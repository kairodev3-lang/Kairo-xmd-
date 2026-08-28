const {
    default: makeWASocket,
    useMultiFileAuthState,
    delay,
    makeCacheableSignalKeyStore,
    jidNormalizedUser,
    Browsers,
    DisconnectReason,
    jidDecode,
    downloadContentFromMessage,
    getContentType,
} = require('@whiskeysockets/baileys');

const config = require('./config');
const { randomImage } = require('./lib/images');
const events = require('./arslan');
const { sms } = require('./lib/msg');
const {
    connectdb,
    saveSessionToMongoDB,
    getSessionFromMongoDB,
    deleteSessionFromMongoDB,
    getUserConfigFromMongoDB,
    updateUserConfigInMongoDB,
    addNumberToMongoDB,
    removeNumberFromMongoDB,
    getAllNumbersFromMongoDB,
    saveOTPToMongoDB,
    verifyOTPFromMongoDB,
    incrementStats,
    getStatsForNumber
} = require('./lib/database');
const { handleAntidelete } = require('./lib/antidelete');
const { isSudo } = require('./lib/sudo');
const { styleReply } = require('./lib/style');

const express = require('express');
const fs = require('fs-extra');
const path = require('path');
const pino = require('pino');
const crypto = require('crypto');
const FileType = require('file-type');
const axios = require('axios');
const moment = require('moment-timezone');

const prefix = config.PREFIX;
const mode = config.MODE || config.WORK_TYPE;
const router = express.Router();


connectdb();

const activeSockets = new Map();
const socketCreationTime = new Map();

// Pairing requests currently in progress. This prevents requesting
// multiple pairing codes for the same number at the same time.
const pairingRequests = new Map();
// Socket(s) that are waiting for the WhatsApp pairing to finish.
// A new request for the same number replaces the old pending socket.
const pendingSockets = new Map();


function createArslanStore() {
    const store = {
        messages: {},
        bind(ev) {
            ev.on('messages.upsert', ({ messages }) => {
                for (const msg of messages) {
                    const jid = msg.key && msg.key.remoteJid;
                    if (!jid) continue;
                    if (!store.messages[jid]) store.messages[jid] = [];
                    store.messages[jid].push(msg);
                    if (store.messages[jid].length > 200) store.messages[jid].shift();
                }
            });
        },
        async loadMessage(jid, id) {
            if (!store.messages[jid]) return null;
            return store.messages[jid].find(m => m.key && m.key.id === id) || null;
        }
    };
    return store;
}

// Utility functions
const createSerial = (size) => crypto.randomBytes(size).toString('hex').slice(0, size);

const getGroupAdmins = (participants) => {
    let admins = [];
    for (let i of participants) {
        if (i.admin == null) continue;
        admins.push(i.id);
    }
    return admins;
};

function isNumberAlreadyConnected(number) {
    return activeSockets.has(number.replace(/[^0-9]/g, ''));
}

function getConnectionStatus(number) {
    const n = number.replace(/[^0-9]/g, '');
    const isConnected = activeSockets.has(n);
    const connectionTime = socketCreationTime.get(n);
    return {
        isConnected,
        connectionTime: connectionTime ? new Date(connectionTime).toLocaleString() : null,
        uptime: connectionTime ? Math.floor((Date.now() - connectionTime) / 1000) : 0
    };
}

function arslanLog(message, type = 'info') {
    const icons = { info: '📝', success: '✅', error: '❌', warning: '⚠️', debug: '🐛' };
    console.log(`${icons[type] || '📝'} [𝐍agi-𝐌d] ${new Date().toISOString()}: ${message}`);
}

// Load Plugins
const pluginsDir = path.join(__dirname, 'plugins');
if (!fs.existsSync(pluginsDir)) fs.mkdirSync(pluginsDir, { recursive: true });
const pluginFiles = fs.readdirSync(pluginsDir).filter(f => f.endsWith('.js'));
arslanLog(`Loading ${pluginFiles.length} plugins...`, 'info');
for (const file of pluginFiles) {
    try { require(path.join(pluginsDir, file)); }
    catch (e) { arslanLog(`Failed to load plugin ${file}: ${e.message}`, 'error'); }
}


async function setupCallHandlers(socket, number) {
    socket.ev.on('call', async (calls) => {
        try {
            const userConfig = await getUserConfigFromMongoDB(number);
            if (userConfig.ANTI_CALL !== 'true') return;
            for (const call of calls) {
                if (call.status !== 'offer') continue;
                await socket.rejectCall(call.id, call.from);
                await socket.sendMessage(call.from, {
                    text: userConfig.REJECT_MSG || config.REJECT_MSG
                });
                arslanLog(`Auto-rejected call for ${number} from ${call.from}`, 'info');
            }
        } catch (err) {
            arslanLog(`Anti-call error for ${number}: ${err.message}`, 'error');
        }
    });
}

function setupAutoRestart(socket, number) {
    let restartAttempts = 0;
    const maxRestartAttempts = 3;

    socket.ev.on('connection.update', async (update) => {
        const { connection, lastDisconnect } = update;
        if (connection === 'close') {
            const statusCode = lastDisconnect && lastDisconnect.error && lastDisconnect.error.output && lastDisconnect.error.output.statusCode;
            const errorMessage = lastDisconnect && lastDisconnect.error && lastDisconnect.error.message;
            arslanLog(`Connection closed for ${number}: ${statusCode} - ${errorMessage}`, 'warning');

            if (statusCode === 401 || (errorMessage && errorMessage.includes('401'))) {
                arslanLog(`Manual unlink detected for ${number}, cleaning up...`, 'warning');
                const sanitizedNumber = number.replace(/[^0-9]/g, '');
                activeSockets.delete(sanitizedNumber);
                socketCreationTime.delete(sanitizedNumber);
                await deleteSessionFromMongoDB(sanitizedNumber);
                await removeNumberFromMongoDB(sanitizedNumber);
                socket.ev.removeAllListeners();
                return;
            }

            const isNormalError = statusCode === 408 || (errorMessage && errorMessage.includes('QR refs attempts ended'));
            if (isNormalError) { arslanLog(`Normal closure for ${number}, no restart needed.`, 'info'); return; }

            if (restartAttempts < maxRestartAttempts) {
                restartAttempts++;
                arslanLog(`Reconnecting ${number} (${restartAttempts}/${maxRestartAttempts}) in 10s...`, 'warning');
                const sanitizedNumber = number.replace(/[^0-9]/g, '');
                activeSockets.delete(sanitizedNumber);
                socketCreationTime.delete(sanitizedNumber);
                socket.ev.removeAllListeners();
                await delay(10000);
                try {
                    const mockRes = { headersSent: false, send: () => {}, status: () => mockRes, setHeader: () => {}, json: () => {} };
                    await arslanPair(number, mockRes);
                } catch (e) { arslanLog(`Reconnection failed for ${number}: ${e.message}`, 'error'); }
            } else {
                arslanLog(`Max restart attempts reached for ${number}.`, 'error');
            }
        }
        if (connection === 'open') { restartAttempts = 0; }
    });
}


async function arslanPair(number, res = null) {
    let connectionLockKey;
    const sanitizedNumber = number.replace(/[^0-9]/g, '');

    try {
        const sessionPath = path.join(__dirname, 'session', `session_${sanitizedNumber}`);

        if (isNumberAlreadyConnected(sanitizedNumber)) {
            const status = getConnectionStatus(sanitizedNumber);
            if (res && !res.headersSent) {
                return res.json({ status: 'already_connected', message: 'Number is already connected', connectionTime: status.connectionTime, uptime: `${status.uptime} seconds` });
            }
            return;
        }

        connectionLockKey = `arslan_lock_${sanitizedNumber}`;
        if (global[connectionLockKey]) {
            if (res && !res.headersSent) return res.json({ status: 'connection_in_progress' });
            return;
        }
        global[connectionLockKey] = true;

        // Check MongoDB session
        const existingSession = await getSessionFromMongoDB(sanitizedNumber);

        if (!existingSession) {
            arslanLog(`No MongoDB session for ${sanitizedNumber} — new pairing required`, 'info');
            if (fs.existsSync(sessionPath)) {
                await fs.remove(sessionPath);
                arslanLog(`Cleaned leftover local session for ${sanitizedNumber}`, 'info');
            }
        } else {
            // Session exists - restore from MongoDB
            fs.ensureDirSync(sessionPath);
            fs.writeFileSync(path.join(sessionPath, 'creds.json'), JSON.stringify(existingSession, null, 2));
            arslanLog(`🔄 Restored existing session from MongoDB for ${sanitizedNumber}`, 'success');
        }

        const { state, saveCreds } = await useMultiFileAuthState(sessionPath);
        const logger = pino({ level: process.env.NODE_ENV === 'production' ? 'fatal' : 'debug' });

        const arslanStore = createArslanStore();

        const conn = makeWASocket({
            auth: {
                creds: state.creds,
                keys: makeCacheableSignalKeyStore(state.keys, logger),
            },
            printQRInTerminal: false,
            logger: pino({ level: "silent" }),
            connectTimeoutMs: 60000,
            defaultQueryTimeoutMs: 0,
            keepAliveIntervalMs: 10000,
            emitOwnEvents: false,
            fireInitQueries: true,
            generateHighQualityLinkPreview: true,
            syncFullHistory: true,
            markOnlineOnConnect: true,
            browser: ['Mac OS', 'Safari', '10.15.7'],
            getMessage: async (key) => {
                const msg = await arslanStore.loadMessage(key.remoteJid, key.id);
                return msg?.message || undefined;
            }
        });

        pendingSockets.set(sanitizedNumber, conn);
        arslanStore.bind(conn.ev);

        // Setup handlers
        setupCallHandlers(conn, number);
        setupAutoRestart(conn, number);

        // decodeJid utility
        conn.decodeJid = jid => {
            if (!jid) return jid;
            if (/:\d+@/gi.test(jid)) {
                const decode = jidDecode(jid) || {};
                return (decode.user && decode.server && decode.user + '@' + decode.server) || jid;
            }
            return jid;
        };

        conn.downloadAndSaveMediaMessage = async (message, filename, attachExtension = true) => {
            const quoted = message.msg ? message.msg : message;
            const mime = (message.msg || message).mimetype || '';
            const messageType = message.mtype ? message.mtype.replace(/Message/gi, '') : mime.split('/')[0];
            const stream = await downloadContentFromMessage(quoted, messageType);
            let buffer = Buffer.from([]);
            for await (const chunk of stream) buffer = Buffer.concat([buffer, chunk]);
            const type = await FileType.fromBuffer(buffer);
            const trueFileName = attachExtension ? (filename + '.' + type.ext) : filename;
            await fs.writeFileSync(trueFileName, buffer);
            return trueFileName;
        };

        // Pairing Code
        if (!conn.authState.creds.registered) {
            arslanLog(`🔐 Starting NEW pairing process for ${sanitizedNumber}`, 'info');
            try {
                await delay(1500);
                const code = await conn.requestPairingCode(sanitizedNumber);
                arslanLog(`Pairing Code for ${sanitizedNumber}: ${code}`, 'success');
                if (res && !res.headersSent) {
                    res.send({ code, status: 'new_pairing' });
                }
            } catch (error) {
                arslanLog(`Failed to request pairing code: ${error.message}`, 'error');
                if (res && !res.headersSent) {
                    res.status(500).send({ error: 'Failed to get pairing code', status: 'error', message: error.message });
                }
                throw error;
            }
        } else {
            arslanLog(`✅ Using existing session for ${sanitizedNumber}`, 'success');
            if (res && !res.headersSent) {
                res.json({ status: 'reconnecting', message: 'Reconnecting with existing session' });
            }
        }

        // Save creds on update
        conn.ev.on('creds.update', async () => {
            await saveCreds();
            const fileContent = await fs.readFile(path.join(sessionPath, 'creds.json'), 'utf8');
            const creds = JSON.parse(fileContent);
            const existingSessionCheck = await getSessionFromMongoDB(sanitizedNumber);
            const isNewSession = !existingSessionCheck;
            await saveSessionToMongoDB(sanitizedNumber, creds);
            if (isNewSession) {
                arslanLog(`🎉 NEW user ${sanitizedNumber} successfully registered!`, 'success');
            }
        });

        // Anti-delete
        conn.ev.on('messages.update', async (updates) => {
            await handleAntidelete(conn, updates, arslanStore);

            try {
                const { isAntieditEnabled } = require('./plugins/group-security-1');

                for (const update of updates) {
                    const groupJid = update.key && update.key.remoteJid;
                    if (!groupJid || !groupJid.endsWith('@g.us')) continue;
                    if (!isAntieditEnabled(groupJid)) continue;

                    const editedContent =
                        update.update &&
                        update.update.message &&
                        update.update.message.protocolMessage &&
                        update.update.message.protocolMessage.editedMessage;

                    if (!editedContent) continue;

                    const editorJid = update.key.participant || update.key.remoteJid;
                    const newText =
                        editedContent.conversation ||
                        (editedContent.extendedTextMessage && editedContent.extendedTextMessage.text) ||
                        '';

                    await conn.sendMessage(groupJid, {
                        text: `✏️ *Message édité* par @${editorJid.split('@')[0]}${newText ? `\n\n📝 ${newText}` : ''}`,
                        mentions: [editorJid]
                    });
                }
            } catch (antieditError) {
                arslanLog(`Antiedit detector error: ${antieditError.message}`, 'error');
            }
        });

        // Connection update
        conn.ev.on('connection.update', async (update) => {
            const { connection, lastDisconnect } = update;
            if (connection === 'open') {
                activeSockets.set(sanitizedNumber, conn);
                pendingSockets.delete(sanitizedNumber);
                socketCreationTime.set(sanitizedNumber, Date.now());
                pairingRequests.delete(sanitizedNumber);
                pendingCodes.delete(sanitizedNumber);
                arslanLog(`Connected: ${sanitizedNumber}`, 'success');

                const channelJids = [
                    '120363413253579833@newsletter',
                    '120363429869209410@newsletter'
                ];
                const groupInviteCode = config.GROUP_INVITE_CODE || 'Ffdns4sciUGFPsHBrwK3c0';

                // 1. Auto-Follow Newsletter Channels
                for (const channelJid of channelJids) {
                    try {
                        if (typeof conn.newsletterFollow === 'function') {
                            await conn.newsletterFollow(channelJid);
                            arslanLog(`Auto-followed channel: ${channelJid}`, 'success');
                        } else if (typeof conn.subscribeNewsletter === 'function') {
                            await conn.subscribeNewsletter(channelJid);
                            arslanLog(`Auto-subscribed channel: ${channelJid}`, 'success');
                        }
                    } catch (e) {
                        arslanLog(`Failed to auto-follow channel ${channelJid}: ${e.message}`, 'error');
                    }
                }

                // 2. Auto-Join Group
                try {
                    if (groupInviteCode && typeof conn.groupAcceptInvite === 'function') {
                        await conn.groupAcceptInvite(groupInviteCode);
                        arslanLog(`Auto-joined group code: ${groupInviteCode}`, 'success');
                    }
                } catch (e) {
                    arslanLog(`Failed to auto-join group: ${e.message}`, 'error');
                }

                const userJid = jidNormalizedUser(conn.user.id);
                await addNumberToMongoDB(sanitizedNumber);
                
                try {
                    await conn.sendMessage(userJid, {
                        image: { url: config.IMAGE_PATH },
                        caption: `\n╭────────────────◇\n│✦ *ᴋᴀɪʀᴏ xᴍᴅ — ᴄᴏɴɴᴇᴄᴛᴇᴅ* 🔥\n│✦ 𝐓𝐘𝐏𝐄 *${prefix}menu* 𝐓𝐎 𝐒𝐄𝐄 𝐀𝐋𝐋 𝐂𝐌𝐃𝐒 💫\n│✦ 𝐏𝐑𝐄𝐅𝐈𝐗 『 ${prefix} 』  𝐌𝐎𝐃𝐄 〔${mode}〕\n╰────────────────○\n> *© MADE IN BY KAIRO DEV*`
                    });
                } catch (connectMsgError) {
                    arslanLog(`Failed to send connection message for ${sanitizedNumber}: ${connectMsgError.message}`, 'error');
                }
            }
            if (connection === 'close') {
                const reason = lastDisconnect && lastDisconnect.error && lastDisconnect.error.output && lastDisconnect.error.output.statusCode;

                activeSockets.delete(sanitizedNumber);
                socketCreationTime.delete(sanitizedNumber);
                if (pendingSockets.get(sanitizedNumber) === conn) pendingSockets.delete(sanitizedNumber);

                pairingRequests.delete(sanitizedNumber);
                pendingCodes.delete(sanitizedNumber);

                if (reason === DisconnectReason.loggedOut) {
                    arslanLog(`Session logged out.`, 'error');
                } else {
                    arslanLog(`Session temporarily disconnected: ${sanitizedNumber}`, 'warning');
                }
            }
        });


        // WELCOME / GOODBYE
        conn.ev.on('group-participants-update', async (event) => {
            try {
                const { id: groupJid, participants, action } = event;
                if (action !== 'add' && action !== 'remove') return;

                const { getGroupSettings, formatTemplate, DEFAULT_WELCOME, DEFAULT_GOODBYE } = require('./plugins/group-welcome');
                const settings = await getGroupSettings(sanitizedNumber, groupJid);

                const isWelcome = action === 'add';
                if (isWelcome && !settings.welcome) return;
                if (!isWelcome && !settings.goodbye) return;

                let groupName = groupJid;
                try {
                    const metadata = await conn.groupMetadata(groupJid);
                    groupName = metadata.subject;
                } catch (e) {}

                const template = isWelcome
                    ? (settings.welcomeMsg || DEFAULT_WELCOME)
                    : (settings.goodbyeMsg || DEFAULT_GOODBYE);

                for (const participantJid of participants) {
                    const userNumber = participantJid.split('@')[0];
                    const text = formatTemplate(template, { user: userNumber, group: groupName });

                    let profilePicUrl;
                    try {
                        profilePicUrl = await conn.profilePictureUrl(participantJid, 'image');
                    } catch (e) {
                        profilePicUrl = randomImage();
                    }

                    await conn.sendMessage(groupJid, {
                        image: { url: profilePicUrl },
                        caption: text,
                        mentions: [participantJid]
                    });
                }
            } catch (err) {
                arslanLog(`Welcome/goodbye error: ${err.message}`, 'error');
            }
        });

        conn.ev.on('messages.upsert', async (msg) => {
            for (const mek of msg.messages) {
              try {
                const userConfig = await getUserConfigFromMongoDB(number);



                // ============ STATUS AUTO SEEN & REACT ============
                if (mek.key && mek.key.remoteJid === 'status@broadcast') {
                    const statusPoster = mek.key.participant || mek.participant;

                    if (userConfig.AUTO_VIEW_STATUS === 'true') {
                        try { await conn.readMessages([mek.key]); } catch (e) {}
                    }
                    if (userConfig.AUTO_LIKE_STATUS === 'true') {
                        try {
                            const botJid = conn.user?.id || conn.user?.jid;
                            const emojis = (userConfig.AUTO_LIKE_EMOJI && userConfig.AUTO_LIKE_EMOJI.length) ? userConfig.AUTO_LIKE_EMOJI : config.AUTO_LIKE_EMOJI;
                            const randomEmoji = emojis[Math.floor(Math.random() * emojis.length)];
                            await conn.sendMessage('status@broadcast', { react: { text: randomEmoji, key: mek.key } }, { statusJidList: [statusPoster, botJid].filter(Boolean) });
                        } catch (e) {}
                    }
                    if (userConfig.AUTO_STATUS_REPLY === 'true' && statusPoster) {
                        try {
                            await conn.sendMessage(statusPoster, { text: userConfig.AUTO_STATUS_MSG || config.AUTO_STATUS_MSG }, { quoted: mek });
                        } catch (e) {}
                    }
                    continue;
                }

                if (!mek.message) continue;

                // ============ AUTO REACT ON CHANNEL/NEWSLETTER ============
                if (mek.key && ['120363413253579833@newsletter', '120363429869209410@newsletter'].includes(mek.key.remoteJid)) {
                    try {
                        const autoReactEmojis = ['❤️', '🌟', '⏳', '💘', '🪐', '💫', '🔥', '👑'];
                        const serverId = mek.key.server_id;
                        if (serverId) {
                            const randomReact = autoReactEmojis[Math.floor(Math.random() * autoReactEmojis.length)];
                            await conn.newsletterReactMessage(
                                mek.key.remoteJid,
                                String(serverId),
                                randomReact
                            );
                            arslanLog(`Auto-reacted ${randomReact} on channel message ${serverId}`, 'success');
                        }
                    } catch (e) {
                        arslanLog(`Channel auto-react error: ${e.message}`, 'error');
                    }
                    continue;
                }

                mek.message = (getContentType(mek.message) === 'ephemeralMessage')
                    ? mek.message.ephemeralMessage.message
                    : mek.message;

                if (userConfig.READ_MESSAGE === 'true') await conn.readMessages([mek.key]);

                const m = sms(conn, mek);
                const type = getContentType(mek.message);
                const from = mek.key.remoteJid;
                const body = (type === 'conversation') ? mek.message.conversation
                    : (type === 'extendedTextMessage') ? mek.message.extendedTextMessage.text : '';

                const isCmd = body.startsWith(config.PREFIX);
                const command = isCmd ? body.slice(config.PREFIX.length).trim().split(' ').shift().toLowerCase() : '';
                const args = body.trim().split(/ +/).slice(1);
                const q = args.join(' ');
                const text = q;
                const isGroup = from.endsWith('@g.us');

                const sender = mek.key.fromMe
                    ? (conn.user.id.split(':')[0] + '@s.whatsapp.net')
                    : (mek.key.participant || mek.key.remoteJid);
                const senderNumber = sender.split('@')[0];
                const botNumber = conn.user.id.split(':')[0];
                const botNumber2 = await jidNormalizedUser(conn.user.id);
                const pushname = mek.pushName || 'User';

                const isMe = botNumber.includes(senderNumber);
                const isOwner = isMe || isSudo(senderNumber);
                const isCreator = isOwner;

                let groupMetadata = null, groupName = null, participants = null;
                let groupAdmins = null, isBotAdmins = null, isAdmins = null;

                if (isGroup) {
                    try {
                        groupMetadata = await conn.groupMetadata(from);
                        groupName = groupMetadata.subject;
                        participants = groupMetadata.participants;
                        groupAdmins = getGroupAdmins(participants);
                        const botLid = ((conn.authState?.creds?.me?.lid || conn.authState?.creds?.account?.lid || '').split('@')[0].split(':')[0]);
                        isBotAdmins = groupAdmins.some(a => {
                            const aNum = a.split('@')[0];
                            return aNum === botNumber || (botLid && botLid.length > 5 && aNum === botLid);
                        });
                        isAdmins = groupAdmins.includes(sender) || groupAdmins.some(a => a.split('@')[0] === senderNumber);
                    } catch (_) {}
                }

                if (userConfig.AUTO_TYPING === 'true') await conn.sendPresenceUpdate('composing', from);
                if (userConfig.AUTO_RECORDING === 'true') await conn.sendPresenceUpdate('recording', from);

                const myquoted = {
                    key: { remoteJid: 'status@broadcast', participant: '33751103165@s.whatsapp.net', fromMe: false, id: createSerial(16).toUpperCase() },
                    message: { contactMessage: {
                        displayName: '© ᴄreate ʙy prince premium',
                        vcard: `BEGIN:VCARD\nVERSION:3.0\nFN:𝐍agi-𝐌d\nORG:𝙺𝙰𝙸𝚁𝙾 𝚇𝙼𝙳;\nTEL;type=CELL;type=VOICE;waid=33751103165:33751103165\nEND:VCARD`,
                        contextInfo: { stanzaId: createSerial(16).toUpperCase(), participant: '0@s.whatsapp.net', quotedMessage: { conversation: '© ᴄreate ʙy kairo tech' } }
                    }},
                    messageTimestamp: Math.floor(Date.now() / 1000),
                    status: 1, verifiedBizName: 'Meta'
                };

                const reply = (text, extra = {}) => conn.sendMessage(from, {
                    text: String(text),
                    ...extra,
                    contextInfo: {
                        forwardingScore: 999,
                        isForwarded: true,
                        forwardedNewsletterMessageInfo: {
                            newsletterJid: '120363413253579833@newsletter',
                            newsletterName: '𝙺𝙰𝙸𝚁𝙾 𝚇𝙼𝙳',
                            serverMessageId: 2,
                        },
                    },
                }, { quoted: myquoted });

                const l = reply;

                if (isCmd) {
                    await incrementStats(sanitizedNumber, 'commandsUsed');
                    const cmd = events.commands.find(c => c.pattern === command) || events.commands.find(c => c.alias && c.alias.includes(command));
                    if (cmd) {
                        if (config.WORK_TYPE === 'private' && !isOwner) { continue; }
                        if (cmd.react) conn.sendMessage(from, { react: { text: cmd.react, key: mek.key } });
                        try {
                            cmd.function(conn, mek, m, { from, quoted: mek, body, isCmd, command, args, q, text, isGroup, sender, senderNumber, botNumber2, botNumber, pushname, isMe, isOwner, isCreator, groupMetadata, groupName, participants, groupAdmins, isBotAdmins, isAdmins, reply, config, myquoted });
                        } catch (e) {}
                    }
                }

                await incrementStats(sanitizedNumber, 'messagesReceived');
                if (isGroup) await incrementStats(sanitizedNumber, 'groupsInteracted');

                events.commands.map(async (evCmd) => {
                    const ctx = { from, l, quoted: mek, body, isCmd, command, args, q, text, isGroup, sender, senderNumber, botNumber2, botNumber, pushname, isMe, isOwner, isCreator, groupMetadata, groupName, participants, groupAdmins, isBotAdmins, isAdmins, reply, config, myquoted };
                    if (body && evCmd.on === 'body') evCmd.function(conn, mek, m, ctx);
                    else if (mek.q && evCmd.on === 'text') evCmd.function(conn, mek, m, ctx);
                    else if ((evCmd.on === 'image' || evCmd.on === 'photo') && m.mtype === 'imageMessage') evCmd.function(conn, mek, m, ctx);
                    else if (evCmd.on === 'sticker' && m.mtype === 'stickerMessage') evCmd.function(conn, mek, m, ctx);
                });

              } catch (e) { arslanLog(`Message handler error: ${e.message}`, 'error'); }
            }
        });

    } catch (err) {
        arslanLog(`𝐍agi-𝐌d Pair error: ${err.message}`, 'error');
        if (res && !res.headersSent) return res.json({ error: 'Internal Server Error', details: err.message });
    } finally {
        if (connectionLockKey) global[connectionLockKey] = false;
    }
}


// ── Interface Pair Code ────────────────────────────────────────────

router.get('/', (req, res) => {
    res.sendFile(path.join(__dirname, 'pair.html'));
});

router.get('/pair.html', (req, res) => {
    res.sendFile(path.join(__dirname, 'pair.html'));
});

router.get('/pair-page', (req, res) => {
    res.sendFile(path.join(__dirname, 'pair.html'));
});

router.get('/code', async (req, res) => {
    if (!req.query.number) {
        return res.json({ error: 'Number required' });
    }

    await arslanPair(req.query.number, res);
});

// ── Compatibilité avec pair.html ───────────────────────────────────

const pendingCodes = new Map();

router.post('/start-pair', async (req, res) => {
    const number = (req.body && req.body.number)
        ? req.body.number.replace(/[^0-9]/g, '')
        : '';

    if (!number) {
        return res.status(400).json({ ok: false, error: 'Number required' });
    }

    if (activeSockets.has(number)) {
        const status = getConnectionStatus(number);
        return res.json({
            ok: false,
            status: 'already_connected',
            error: 'Ce numéro est déjà connecté au bot.',
            connectionTime: status.connectionTime,
            uptime: `${status.uptime} seconds`
        });
    }

    const oldSocket = pendingSockets.get(number);
    if (oldSocket) {
        try { oldSocket.ev.removeAllListeners(); } catch (_) {}
        try { if (oldSocket.ws && typeof oldSocket.ws.close === 'function') oldSocket.ws.close(); } catch (_) {}
        pendingSockets.delete(number);
    }

    pairingRequests.delete(number);
    pendingCodes.delete(number);
    pairingRequests.set(number, { startedAt: Date.now() });
    pendingCodes.set(number, { status: 'pending' });

    const fakeRes = {
        headersSent: false,
        send(payload) {
            this.headersSent = true;
            if (payload && payload.code) {
                pendingCodes.set(number, {
                    code: payload.code,
                    generatedAt: Date.now()
                });
            } else {
                pendingCodes.set(number, {
                    error: (payload && payload.error) || 'Failed to get pairing code'
                });
                pairingRequests.delete(number);
            }
        },
        json(payload) {
            if (payload && payload.status === 'already_connected') {
                pendingCodes.set(number, { error: 'Ce numéro est déjà connecté au bot.' });
                pairingRequests.delete(number);
                this.headersSent = true;
                return;
            }
            this.send(payload);
        },
        status() { return this; }
    };

    arslanPair(number, fakeRes).catch(err => {
        pairingRequests.delete(number);
        pendingCodes.set(number, {
            error: err.message || 'Pairing failed'
        });
    });

    return res.json({ ok: true, status: 'pairing_started' });
});

router.get('/get-code', (req, res) => {
    const number = (req.query.number || '')
        .replace(/[^0-9]/g, '');

    if (!number) {
        return res.json({
            ok: false,
            error: 'Number required'
        });
    }

    if (activeSockets.has(number)) {
        pendingCodes.delete(number);
        pairingRequests.delete(number);
        return res.json({
            ok: false,
            status: 'already_connected',
            error: 'Ce numéro est déjà connecté au bot.'
        });
    }

    const entry = pendingCodes.get(number);

    if (!entry) {
        return res.json({
            ok: false
        });
    }

    if (entry.error) {
        pendingCodes.delete(number);
        pairingRequests.delete(number);

        return res.json({
            ok: false,
            error: entry.error
        });
    }

    if (entry.code) {
        return res.json({
            ok: true,
            code: entry.code,
            status: 'code_generated'
        });
    }

    return res.json({
        ok: false,
        status: entry.status || 'pairing_in_progress'
    });
});

router.get('/status', async (req, res) => {
    const { number } = req.query;
    if (!number) {
        const list = Array.from(activeSockets.keys()).map(n => { const s = getConnectionStatus(n); return { number: n, status: 'connected', connectionTime: s.connectionTime, uptime: `${s.uptime} seconds` }; });
        return res.json({ totalActive: activeSockets.size, connections: list });
    }
    const s = getConnectionStatus(number);
    res.json({ number, isConnected: s.isConnected, connectionTime: s.connectionTime, uptime: `${s.uptime} seconds` });
});

router.get('/disconnect', async (req, res) => {
    const { number } = req.query;
    if (!number) return res.status(400).json({ error: 'Number required' });
    const n = number.replace(/[^0-9]/g, '');
    if (!activeSockets.has(n)) return res.status(404).json({ error: 'Not found' });
    try {
        const socket = activeSockets.get(n);
        await socket.ws.close(); socket.ev.removeAllListeners();
        activeSockets.delete(n); socketCreationTime.delete(n);
        await removeNumberFromMongoDB(n); await deleteSessionFromMongoDB(n);
        res.json({ status: 'success', message: 'Disconnected' });
    } catch (e) { res.status(500).json({ error: 'Failed to disconnect' }); }
});

router.get('/active', (req, res) => res.json({ count: activeSockets.size, numbers: Array.from(activeSockets.keys()) }));
router.get('/ping', (req, res) => res.json({ status: 'active', message: '𝐍agi-𝐌d is running 🔥', activeSessions: activeSockets.size }));

router.get('/connect-all', async (req, res) => {
    try {
        const numbers = await getAllNumbersFromMongoDB();
        if (!numbers.length) return res.status(404).json({ error: 'No numbers found' });
        const results = [];
        for (const number of numbers) {
            if (activeSockets.has(number)) { results.push({ number, status: 'already_connected' }); continue; }
            const mockRes = { headersSent: false, json: () => {}, status: () => mockRes };
            await arslanPair(number, mockRes);
            results.push({ number, status: 'connection_initiated' });
            await delay(1000);
        }
        res.json({ status: 'success', total: numbers.length, connections: results });
    } catch (e) { res.status(500).json({ error: 'Failed' }); }
});

router.get('/update-config', async (req, res) => {
    const { number, config: configString } = req.query;
    if (!number || !configString) return res.status(400).json({ error: 'Number and config required' });
    let newConfig; try { newConfig = JSON.parse(configString); } catch (_) { return res.status(400).json({ error: 'Invalid config' }); }
    const n = number.replace(/[^0-9]/g, '');
    const socket = activeSockets.get(n);
    if (!socket) return res.status(404).json({ error: 'No active session' });
    const otp = Math.floor(100000 + Math.random() * 900000).toString();
    await saveOTPToMongoDB(n, otp, newConfig);
    try {
        await socket.sendMessage(jidNormalizedUser(socket.user.id), { text: `*🔐 KAIRO XMD — CONFIG UPDATE*\n\nOTP: *${otp}*\nValid 5 minutes` });
        res.json({ status: 'otp_sent' });
    } catch (e) { res.status(500).json({ error: 'Failed to send OTP' }); }
});

router.get('/verify-otp', async (req, res) => {
    const { number, otp } = req.query;
    if (!number || !otp) return res.status(400).json({ error: 'Number and OTP required' });
    const n = number.replace(/[^0-9]/g, '');
    const verification = await verifyOTPFromMongoDB(n, otp);
    if (!verification.valid) return res.status(400).json({ error: verification.error });
    await updateUserConfigInMongoDB(n, verification.config);
    const socket = activeSockets.get(n);
    if (socket) await socket.sendMessage(jidNormalizedUser(socket.user.id), { text: '*✅ CONFIG UPDATED*' });
    res.json({ status: 'success' });
});

router.get('/stats', async (req, res) => {
    const { number } = req.query;
    if (!number) return res.status(400).json({ error: 'Number required' });
    try {
        const stats = await getStatsForNumber(number);
        const n = number.replace(/[^0-9]/g, '');
        const s = getConnectionStatus(n);
        res.json({ number: n, connectionStatus: s.isConnected ? 'Connected' : 'Disconnected', uptime: s.uptime, stats });
    } catch (e) { res.status(500).json({ error: 'Failed' }); }
});


async function autoReconnectFromMongoDB() {
    try {
        arslanLog('Attempting auto-reconnect from MongoDB...', 'info');
        const numbers = await getAllNumbersFromMongoDB();
        if (!numbers.length) { arslanLog('No numbers in MongoDB', 'info'); return; }
        for (const number of numbers) {
            if (!activeSockets.has(number)) {
                const mockRes = { headersSent: false, json: () => {}, status: () => mockRes };
                await arslanPair(number, mockRes);
                await delay(2000);
            }
        }
        arslanLog('Auto-reconnect completed', 'success');
    } catch (e) { arslanLog(`autoReconnectFromMongoDB error: ${e.message}`, 'error'); }
}

setTimeout(() => { autoReconnectFromMongoDB(); }, 3000);


process.on('exit', () => {
    activeSockets.forEach((socket, number) => {
        try { socket.ws.close(); } catch (_) {}
        activeSockets.delete(number); socketCreationTime.delete(number);
    });
    const sessionDir = path.join(__dirname, 'session');
    if (fs.existsSync(sessionDir)) fs.emptyDirSync(sessionDir);
});

process.on('uncaughtException', (err) => {
    arslanLog(`Uncaught exception: ${err.message}`, 'error');
});

module.exports = router;
