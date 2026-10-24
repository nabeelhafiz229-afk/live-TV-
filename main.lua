-- LIVE_TV_APP
require "import"
import "android.widget.*"
import "android.view.*"
import "android.graphics.PixelFormat"
import "android.graphics.Typeface"
import "android.graphics.drawable.GradientDrawable"
import "android.graphics.drawable.ColorDrawable"
import "android.text.InputType"
import "android.net.Uri"
import "android.app.AlertDialog"
import "android.content.ClipboardManager"
import "android.content.ClipData"
import "android.content.Context"
import "android.content.Intent"
import "android.content.SharedPreferences"
import "android.os.Handler"
import "android.os.Looper"
import "android.media.MediaPlayer"
import "android.media.AudioManager"
import "java.net.HttpURLConnection"
import "java.net.URL"
import "java.io.BufferedReader"
import "java.io.InputStreamReader"
import "java.lang.Thread"
import "java.nio.CharBuffer"
import "java.lang.StringBuilder"
import "java.lang.Runnable"
import "java.util.HashMap"
import "org.json.JSONObject"
import "org.json.JSONArray"
import "android.os.Build"
import "android.webkit.*"
import "java.io.OutputStreamWriter"
import "android.content.DialogInterface"
import "android.content.IntentFilter"

----------------------------------------------------------------
-- CONFIGURATION  (change the version here for every update)
-- Keep APP_VERSION the same as the number inside version.txt on GitHub
----------------------------------------------------------------
local APP_VERSION = "1.2"
local UPDATE_BASE = "https://raw.githubusercontent.com/nabeelhafiz229-afk/live-TV-/main/"
local DEFAULT_SCRIPT_PATH = "/sdcard/解说/Tools/live TV /main.lua"

----------------------------------------------------------------
-- Basic state
----------------------------------------------------------------
local mainHandler = Handler(Looper.getMainLooper())
local prefs = service.getSharedPreferences("LiveTV_Settings", Context.MODE_PRIVATE)

local countries = {
    { name = "Pakistan", code = "pk", lang = "urd", extraLangs = { "pan", "snd" }, extra = {
        { label = "Verified Pakistan and India List", url = "https://raw.githubusercontent.com/Rayyan98/my-curated-iptv/refs/heads/main/real_data/main_working.m3u", idSuffix = "pk" },
        { label = "Pakistani TV Stations List", url = "https://raw.githubusercontent.com/ASMASAM/iptv/master/99_All_TV_Stations.m3u" }
    } },
    { name = "India", code = "in", lang = "hin", extraLangs = { "tam", "tel", "mal", "kan", "mar", "guj", "pan" }, extra = {
        { label = "Verified Pakistan and India List", url = "https://raw.githubusercontent.com/Rayyan98/my-curated-iptv/refs/heads/main/real_data/main_working.m3u", idSuffix = "in" },
        { label = "India IPTV List", url = "https://raw.githubusercontent.com/Indiblog/india-iptv/main/output/india_iptv.m3u" },
        { label = "India General List", url = "https://raw.githubusercontent.com/Indiblog/india-iptv/main/output/india_general.m3u" },
        { label = "Hindi and Punjabi List", url = "https://raw.githubusercontent.com/deep2772/Hindi_Punjabi-iptv-playlist/refs/heads/main/Hindi_Punjabi_Merged.m3u" },
        { label = "India Channels List", url = "https://raw.githubusercontent.com/udayshankarv/iptv/master/Indiaiptv.m3u" }
    } },
    { name = "Bangladesh", code = "bd", lang = "ben", extra = {
        { label = "Bangladesh and India List", url = "https://raw.githubusercontent.com/Shadmanislam/bdiptv/master/BD%20IPTV.m3u" }
    } },
    { name = "Afghanistan", code = "af", lang = "pus" },
    { name = "Nepal", code = "np", lang = "nep" },
    { name = "Saudi Arabia", code = "sa", lang = "ara" },
    { name = "United Arab Emirates", code = "ae", lang = "ara" },
    { name = "Turkey", code = "tr", lang = "tur" },
    { name = "Egypt", code = "eg", lang = "ara" },
    { name = "Iraq", code = "iq", lang = "ara" },
    { name = "Kuwait", code = "kw", lang = "ara" },
    { name = "Qatar", code = "qa", lang = "ara" },
    { name = "Oman", code = "om", lang = "ara" },
    { name = "Bahrain", code = "bh", lang = "ara" },
    { name = "Jordan", code = "jo", lang = "ara" },
    { name = "Lebanon", code = "lb", lang = "ara" },
    { name = "Syria", code = "sy", lang = "ara" },
    { name = "Palestine", code = "ps", lang = "ara" },
    { name = "Yemen", code = "ye", lang = "ara" },
    { name = "Morocco", code = "ma", lang = "ara" },
    { name = "Algeria", code = "dz", lang = "ara" },
    { name = "Tunisia", code = "tn", lang = "ara" },
    { name = "Libya", code = "ly", lang = "ara" },
    { name = "Sudan", code = "sd", lang = "ara" }
}

local allChannels = {}
local categoryMap = {}
local activeCategoryList = {}
local currentChannels = {}
local currentIndex = 1
local currentUrlIndex = 1
local selectedCountry = countries[1]
local source1Count = 0
local source2Count = 0
local source3Count = 0
local isLoading = false
local urlHeaders = {}
local attempt = {}
local webPlayer = nil
local webPaused = false
local forceLow = {}
-- Links that must be checked by the resolver before playing (set after the direct attempt failed)
local probeFirst = {}
-- true while an automatic link check runs: short timeouts, one request, no retries, small downloads.
-- (A check holds the Lua state while it waits for the network, so it must be short and cancelable.)
local resolveFast = false
-- Plain stream files go straight to the native player: it does its own networking, so nothing
-- holds the Lua state while a channel connects (that was freezing / crashing the screen reader).
local function isDirectStream(u)
    local l = tostring(u):lower():gsub("%?.*$", "")
    if not l:find("^https?://") then return false end
    if l:find("youtube") or l:find("youtu%.be") then return false end
    return (l:find("%.m3u8$") or l:find("%.ts$") or l:find("%.mp3$") or l:find("%.aac$") or l:find("%.mp4$")) and true or false
end
local bufTimes = {}
local urlOrigin = {}
local sourceStats = {}

local favorites = {}
local customChannels = {}

local windowManager = nil
local playerLayout = nil
local videoView = nil
local statusText = nil
local subText = nil
local playPauseBtn = nil
local favBtn = nil
local modeBtn = nil
local sleepBtn = nil
local audioPlayer = nil
local homeDialog = nil
local lastListFn = nil
local currentDialog = nil
local homeReceiver = nil
local exitTool

local sleepOptions = { 0, 15, 30, 45, 60, 90 }
local sleepIdx = 1
local sleepRunnable = nil
local playToken = 0
local failureToken = -1
local streamStarted = false
local watchdog = nil
local videoContainer = nil
local headerLayout = nil
local controlsScroll = nil
local fullBtn = nil
local exitFullBtn = nil
local isFullScreen = false

-- forward declarations
local showHome, showCategoryMenu, showChannelList, showChannelOptions
local showFavorites, showCustomList, showCustomForm, showSearch
local showSettings, showCountryDialog, fetchChannelsForCountry
local playCurrentStream, playStreamByIndex, closePlayer

----------------------------------------------------------------
-- Style
----------------------------------------------------------------
local C = {
    bg = 0xFF121212,
    text = 0xFFFFFFFF,
    sub = 0xFFB0BEC5,
    primary = 0xFF1565C0,
    secondary = 0xFF37474F,
    success = 0xFF2E7D32,
    danger = 0xFFB71C1C,
    gold = 0xFFF9A825
}

local density = service.getResources().getDisplayMetrics().density
local function dp(n)
    return math.floor(n * density + 0.5)
end

local MATCH = LinearLayout.LayoutParams.MATCH_PARENT
local WRAP = LinearLayout.LayoutParams.WRAP_CONTENT

----------------------------------------------------------------
-- Helpers
----------------------------------------------------------------
local function say(msg)
    if prefs.getBoolean("speech", true) then
        service.speak(tostring(msg))
    end
end

local function sayDetail(msg)
    if prefs.getBoolean("speech", true) and prefs.getBoolean("verbose", true) then
        service.speak(tostring(msg))
    end
end

local function runOnMain(fn)
    mainHandler.post(Runnable{
        run = fn
    })
end

local function trim(s)
    return (tostring(s or ""):match("^%s*(.-)%s*$"))
end

----------------------------------------------------------------
-- Time-sliced background work.
-- A Lua callback keeps the Lua state locked while it runs, so one long loading loop
-- freezes everything else (including the screen reader). Loading therefore runs as many
-- tiny steps on a background thread; between steps the lock is free and the UI can respond.
----------------------------------------------------------------
import "android.os.HandlerThread"
import "java.lang.System"
local showErrorDialog
-- stepFn() is called again and again; it returns true when all the work is finished.
local function runSteps(stepFn, onCrash)
    local ht = HandlerThread("livetv-loader", 10)
    ht.start()
    local h = Handler(ht.getLooper())
    local stepper
    stepper = Runnable{
        run = function()
            local ok, res = pcall(stepFn)
            if not ok then
                pcall(function() ht.quit() end)
                if onCrash then
                    local okc, errc = pcall(onCrash, res)
                    if not okc then isLoading = false end
                end
            elseif res == true then
                pcall(function() ht.quit() end)
            else
                h.postDelayed(stepper, 40)
            end
        end
    }
    h.post(stepper)
end

local function chKey(name)
    local k = tostring(name):lower():gsub("%s+", ""):gsub("%p+", "")
    return k
end

local function hasAny(text, words)
    for _, w in ipairs(words) do
        if text:find(w, 1, true) then return true end
    end
    return false
end

-- Looser key: "ARY News HD", "ARY News (1080p)" and "ARY NEWS" all become the same channel
local noiseWords = { hd = true, sd = true, fhd = true, uhd = true, ["4k"] = true, tv = true, channel = true,
    live = true, official = true, ["1080p"] = true, ["720p"] = true, ["576p"] = true, ["480p"] = true,
    ["360p"] = true, ["240p"] = true }

local function looseKey(name)
    local n = tostring(name):lower()
    n = n:gsub("%b()", " "):gsub("%b[]", " ")
    local parts = {}
    for w in n:gmatch("%S+") do
        local ww = w:gsub("^%p+", ""):gsub("%p+$", "")
        if ww ~= "" and not noiseWords[ww] then
            table.insert(parts, ww)
        end
    end
    local k = table.concat(parts, ""):gsub("%p+", "")
    if k == "" then k = chKey(name) end
    return k
end

local function normalizeCategory(grp, name)
    local g = (tostring(grp or "") .. " " .. tostring(name or "")):lower()
    if hasAny(g, { "kids", "cartoon", "children", "animation", "animated", "toon", "disney", "nickelodeon", "pogo", "nick jr", "baby", "junior" }) then
        return "Kids & Cartoons"
    elseif hasAny(g, { "islam", "quran", "koran", "madani", "qtv", "noor", "huda", "deen", "makkah", "makka", "madina", "saudi quran", "sunnah", "hadith", "iqra", "ahlebait", "ahlulbayt", "peace tv", "mecca", "medina", "naat", "dawat" }) then
        return "Islamic"
    elseif hasAny(g, { "relig", "church", "christian", "gospel", "hindu", "bhakti", "sikh", "gurbani", "bible", "temple", "spiritual" }) then
        return "Religious"
    elseif hasAny(g, { "news" }) then
        return "News"
    elseif hasAny(g, { "sport", "cricket", "football", "soccer", "tennis", "hockey", "wrestling" }) then
        return "Sports"
    elseif hasAny(g, { "movie", "film", "cinema", "bollywood", "lollywood", "hollywood" }) then
        return "Movies"
    elseif hasAny(g, { "entertain", "music", "drama", "comedy", "series", "serial", "lifestyle" }) then
        return "Entertainment"
    else
        return "Other"
    end
end

local function presentDialog(builder, dark, backFn)
    if backFn ~= nil then
        pcall(function()
            builder.setOnKeyListener(DialogInterface.OnKeyListener{
                onKey = function(d, keyCode, event)
                    if keyCode == KeyEvent.KEYCODE_BACK then
                        if event.getAction() == KeyEvent.ACTION_UP then
                            pcall(function() d.dismiss() end)
                            backFn()
                        end
                        return true
                    end
                    return false
                end
            })
        end)
    end
    local dlg = builder.create()
    pcall(function()
        dlg.getWindow().setType(WindowManager.LayoutParams.TYPE_ACCESSIBILITY_OVERLAY)
    end)
    if dark then
        pcall(function()
            dlg.getWindow().setBackgroundDrawable(ColorDrawable(C.bg))
        end)
    end
    dlg.show()
    currentDialog = dlg
    return dlg
end

local function makeLabel(text, size, color, bold)
    local tv = TextView(service)
    tv.setText(text)
    tv.setTextSize(size or 16)
    tv.setTextColor(color or C.text)
    if bold then tv.setTypeface(Typeface.DEFAULT_BOLD) end
    return tv
end

local function makeTitle(text)
    local tv = makeLabel(text, 22, C.text, true)
    tv.setBackgroundColor(C.bg)
    tv.setPadding(dp(16), dp(16), dp(16), dp(8))
    pcall(function() tv.setAccessibilityHeading(true) end)
    return tv
end

local function makeButton(text, desc, color, onClick, size)
    local b = Button(service)
    b.setText(text)
    b.setContentDescription(desc or text)
    pcall(function() b.setAllCaps(false) end)
    b.setTextSize(size or 18)
    b.setTextColor(C.text)
    b.setMinHeight(dp(60))
    b.setPadding(dp(10), dp(10), dp(10), dp(10))
    pcall(function()
        local gd = GradientDrawable()
        gd.setColor(color or C.secondary)
        gd.setCornerRadius(dp(14))
        b.setBackground(gd)
    end)
    b.setOnClickListener(View.OnClickListener{
        onClick = function(v)
            onClick(v)
        end
    })
    return b
end

local function makeEdit(hint, text)
    local et = EditText(service)
    et.setHint(hint)
    et.setContentDescription(hint)
    et.setText(text or "")
    et.setTextColor(C.text)
    et.setHintTextColor(C.sub)
    et.setTextSize(18)
    et.setSingleLine(true)
    pcall(function()
        et.setInputType(InputType.TYPE_CLASS_TEXT)
    end)
    return et
end

local function panelContainer()
    local scroll = ScrollView(service)
    scroll.setBackgroundColor(C.bg)
    local col = LinearLayout(service)
    col.setOrientation(LinearLayout.VERTICAL)
    col.setPadding(dp(16), dp(8), dp(16), dp(16))
    scroll.addView(col)
    return scroll, col
end

local function addTo(col, view, topMargin)
    local lp = LinearLayout.LayoutParams(MATCH, WRAP)
    lp.setMargins(0, dp(topMargin or 10), 0, 0)
    col.addView(view, lp)
end

showErrorDialog = function(errorText)
    runOnMain(function()
        local builder = AlertDialog.Builder(service)
        builder.setTitle("Error Details")
        builder.setMessage(tostring(errorText))
        builder.setPositiveButton("Copy", {
            onClick = function(dialog, which)
                local clipboard = service.getSystemService(Context.CLIPBOARD_SERVICE)
                local clip = ClipData.newPlainText("ErrorLog", tostring(errorText))
                clipboard.setPrimaryClip(clip)
                service.speak("Error copied to clipboard")
            end
        })
        builder.setNegativeButton("Close", nil)
        presentDialog(builder)
    end)
end

local function infoDialog(title, message, onOk)
    runOnMain(function()
        local ok, err = pcall(function()
            local builder = AlertDialog.Builder(service)
            builder.setTitle(title)
            builder.setMessage(message)
            builder.setPositiveButton("OK", {
                onClick = function()
                    if onOk then onOk() end
                end
            })
            presentDialog(builder, nil, function()
                if onOk then onOk() end
            end)
        end)
        if not ok then showErrorDialog("Dialog Error: " .. tostring(err)) end
    end)
end

local function confirmDialog(title, message, onYes)
    runOnMain(function()
        local ok, err = pcall(function()
            local builder = AlertDialog.Builder(service)
            builder.setTitle(title)
            builder.setMessage(message)
            builder.setPositiveButton("Yes", {
                onClick = function() onYes() end
            })
            builder.setNegativeButton("No", nil)
            presentDialog(builder)
        end)
        if not ok then showErrorDialog("Dialog Error: " .. tostring(err)) end
    end)
end

----------------------------------------------------------------
-- Saved lists (favorites / custom channels)
----------------------------------------------------------------
local function loadList(key)
    local list = {}
    local raw = prefs.getString(key, "")
    for line in tostring(raw):gmatch("[^\n]+") do
        local name, rest = line:match("^(.-)\t(.+)$")
        if name and rest then
            local urls = {}
            for u in rest:gmatch("%S+") do
                table.insert(urls, u)
            end
            if #urls > 0 then
                table.insert(list, { name = name, url = urls[1], urls = urls })
            end
        end
    end
    return list
end

local function saveList(key, list)
    local lines = {}
    for _, ch in ipairs(list) do
        local nm = tostring(ch.name):gsub("[\t\r\n]", " ")
        table.insert(lines, nm .. "\t" .. table.concat(ch.urls, " "))
    end
    local e = prefs.edit()
    e.putString(key, table.concat(lines, "\n"))
    e.apply()
end

local function isFavorite(ch)
    if not ch then return false end
    local k = chKey(ch.name)
    for _, f in ipairs(favorites) do
        if chKey(f.name) == k then return true end
    end
    return false
end

local function toggleFavorite(ch)
    local k = chKey(ch.name)
    for i, f in ipairs(favorites) do
        if chKey(f.name) == k then
            table.remove(favorites, i)
            saveList("favorites_v1", favorites)
            return false
        end
    end
    local copy = {}
    for _, u in ipairs(ch.urls) do table.insert(copy, u) end
    table.insert(favorites, { name = ch.name, url = copy[1], urls = copy })
    saveList("favorites_v1", favorites)
    return true
end

----------------------------------------------------------------
-- Player
----------------------------------------------------------------
local function refreshFavButton()
    if favBtn == nil then return end
    local ch = currentChannels[currentIndex]
    local label = isFavorite(ch) and "Remove from Favorites" or "Add to Favorites"
    favBtn.setText(label)
    favBtn.setContentDescription(label)
end

local function refreshModeButton()
    if modeBtn == nil then return end
    local label = prefs.getBoolean("audio_only", false) and "Switch to Video" or "Switch to Audio Only"
    modeBtn.setText(label)
    modeBtn.setContentDescription(label)
end

local function refreshSleepButton()
    if sleepBtn == nil then return end
    local m = sleepOptions[sleepIdx]
    local label = (m == 0) and "Sleep Timer: Off" or ("Sleep Timer: " .. m .. " minutes")
    sleepBtn.setText(label)
    sleepBtn.setContentDescription(label)
end

local function cancelSleepTimer()
    if sleepRunnable ~= nil then
        pcall(function() mainHandler.removeCallbacks(sleepRunnable) end)
        sleepRunnable = nil
    end
end

----------------------------------------------------------------
-- Stream resolver (redirects, playlists, YouTube)
----------------------------------------------------------------
local resolveInfo = {}
local UA = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36"

local function isYouTube(l)
    return (l:find("youtube%.com") or l:find("youtu%.be") or l:find("youtube%-nocookie%.com")) and true or false
end

-- Pulls a clean link out of any text (extra words, quotes, punctuation).
-- Returns link, leftoverText
local function extractLink(text)
    text = tostring(text or "")
    local url = text:match("[%a][%w+.-]*://[^%s\"'<>]+")
    if not url then
        for tok in text:gmatch("%S+") do
            local t = tok:gsub("^[%(%[{<\"']+", "")
            local lt = t:lower()
            if lt:find("^www%.") or lt:find("^[%w-]+%.[%a][%a]+[/:?]") or isYouTube(lt) then
                url = t
                break
            end
        end
    end
    if not url then return nil, text end
    -- Two links glued together ("...m3u8https://...") or markdown "[url](url)": keep only the first link
    local glued = url:find("%whttps?://", 8)
    if glued then url = url:sub(1, glued) end
    url = (url:gsub("%]%(.*$", ""))
    local s1, e1 = text:find(url, 1, true)
    local leftover = ""
    if s1 then
        leftover = text:sub(1, s1 - 1) .. " " .. text:sub(e1 + 1)
    end
    url = url:gsub("[%.,;:!%)%]}>\"']+$", "")
    if not url:find("^%a[%w+.-]*://") then
        url = "https://" .. url
    end
    leftover = (leftover:gsub("[%a][%w+.-]*://%S+", " "))
    leftover = (leftover:gsub("[%[%]%(%)]", " "))
    leftover = trim(leftover)
    leftover = leftover:gsub("^[%p%s]+", ""):gsub("[%p%s]+$", "")
    return url, leftover
end

local function readStream(conn, limit)
    -- Fast path: read in big chunks (few Java calls) instead of a Lua loop over thousands of lines,
    -- which keeps the Lua state locked and makes the screen reader stutter. It stops at `limit`,
    -- so endless streams served with a playlist content type cannot block it.
    local sb = nil
    local fastRan = false
    pcall(function()
        local reader = InputStreamReader(conn.getInputStream(), "UTF-8")
        local cb = CharBuffer.allocate(16384)
        sb = StringBuilder()
        local total = 0
        while true do
            cb.clear()
            local n = reader.read(cb)
            if n == nil or n < 0 then break end
            fastRan = true
            cb.flip()
            sb.append(cb.toString())
            total = total + n
            if limit and total >= limit then break end
        end
        pcall(function() reader.close() end)
    end)
    if fastRan or (sb ~= nil and sb.length() > 0) then
        local text = tostring(sb.toString())
        if limit and #text > limit then text = text:sub(1, limit) end
        text = text:gsub("\r", "")
        return text
    end
    local parts = {}
    local total = 0
    pcall(function()
        local is = conn.getInputStream()
        local reader = BufferedReader(InputStreamReader(is, "UTF-8"))
        local line = reader.readLine()
        while line ~= nil do
            local s = tostring(line)
            table.insert(parts, s)
            total = total + #s + 1
            if limit and total >= limit then break end
            line = reader.readLine()
        end
        reader.close()
    end)
    return table.concat(parts, "\n")
end

-- GET with manual redirect handling (also http -> https)
local function openFollow(urlStr, timeoutMs, extraHeaders)
    local target = urlStr
    for i = 1, 6 do
        local conn = URL(target).openConnection()
        conn.setRequestMethod("GET")
        conn.setConnectTimeout(timeoutMs)
        conn.setReadTimeout(timeoutMs)
        conn.setInstanceFollowRedirects(false)
        conn.setRequestProperty("User-Agent", UA)
        conn.setRequestProperty("Accept", "*/*")
        if extraHeaders then
            for k, v in pairs(extraHeaders) do
                conn.setRequestProperty(k, v)
            end
        end
        local code = conn.getResponseCode()
        if code == 301 or code == 302 or code == 303 or code == 307 or code == 308 then
            local loc = conn.getHeaderField("Location")
            conn.disconnect()
            if loc == nil or tostring(loc) == "" then return nil end
            loc = tostring(loc)
            if not loc:find("^https?://") then
                local base = target:match("^(https?://[^/]+)")
                if loc:sub(1, 1) == "/" then
                    loc = base .. loc
                else
                    loc = target:gsub("[^/]*$", "") .. loc
                end
            end
            target = loc
        else
            return conn, target, code
        end
    end
    return nil
end

local function absoluteUrl(u, base)
    if u:find("^https?://") then return u end
    if u:sub(1, 2) == "//" then return "https:" .. u end
    local origin = base:match("^(https?://[^/]+)") or ""
    if u:sub(1, 1) == "/" then return origin .. u end
    return (base:gsub("[?#].*$", ""):gsub("[^/]*$", "")) .. u
end

-- Picks one rendition from an HLS master playlist (smooth playback needs a moderate bitrate).
-- Returns nil when the playlist is not a master playlist or has separate audio tracks.
local function pickVariantFromText(text, baseUrl, forceLowQuality)
    if not text:find("#EXT%-X%-STREAM%-INF") then return nil end
    if text:find("#EXT%-X%-MEDIA:[^\n]*TYPE=AUDIO") then return nil end
    local q = forceLowQuality and "low" or tostring(prefs.getString("quality", "auto"))
    if prefs.getBoolean("audio_only", false) then q = "low" end
    local list = {}
    local pbw, ph = nil, 0
    for line in text:gmatch("[^\r\n]+") do
        if line:find("^#EXT%-X%-STREAM%-INF") then
            pbw = tonumber(line:match("BANDWIDTH=(%d+)")) or 0
            ph = tonumber(line:match("RESOLUTION=%d+x(%d+)")) or 0
        elseif pbw and not line:find("^#") and trim(line) ~= "" then
            table.insert(list, { url = trim(line), bw = pbw, h = ph })
            pbw = nil
        end
    end
    if #list == 0 then return nil end
    local target = (q == "high") and 720 or 480
    local tbw = (q == "high") and 2800000 or 1200000
    local best, bestScore = nil, nil
    for _, v in ipairs(list) do
        local score
        if q == "low" then
            score = -v.bw
        elseif q == "best" then
            score = v.bw
        elseif v.h > 0 then
            score = -math.abs(v.h - target) * 10 - v.bw / 1000000
        else
            score = -math.abs(v.bw - tbw) / 100000
        end
        if bestScore == nil or score > bestScore then
            best = v
            bestScore = score
        end
    end
    return absoluteUrl(best.url, baseUrl)
end

-- Returns the final playable url for http(s) links
local function probeStream(urlStr, timeoutMs, hdrs)
    local conn, finalUrl, code = openFollow(urlStr, timeoutMs, hdrs)
    if conn == nil then
        resolveInfo.note = "Could not open the link (too many redirects or a redirect without a target)"
        return urlStr
    end
    local ctype = tostring(conn.getContentType() or ""):lower()
    resolveInfo.http = code
    resolveInfo.ctype = ctype
    resolveInfo.final = finalUrl
    if code == 200 and (ctype:find("text/html") or ctype:find("xhtml")) then
        local html = readStream(conn, resolveFast and 500000 or 3000000)
        pcall(function() conn.disconnect() end)
        return finalUrl, html, code
    end
    local path = finalUrl:lower():gsub("%?.*$", "")
    local isList = ctype:find("mpegurl") or ctype:find("scpls") or ctype:find("x%-ms%-asx")
        or path:find("%.m3u8?$") or path:find("%.pls$") or path:find("%.asx$")
    local result = finalUrl
    if code == 200 and isList then
        local text = readStream(conn, 60000)
        if text:find("#EXT%-X") then
            result = finalUrl
            local nv = 0
            for _ in text:gmatch("#EXT%-X%-STREAM%-INF") do nv = nv + 1 end
            resolveInfo.variants = nv
            local v = pickVariantFromText(text, finalUrl, forceLow[urlStr])
            if v then
                result = v
                resolveInfo.note = "Picked stream rendition: " .. v:sub(1, 140)
            end
        else
            local first = nil
            for line in text:gmatch("[^\r\n]+") do
                local l = trim(line)
                if l:find("^https?://") or l:find("^rtsp://") then
                    first = l
                    break
                end
                local f = l:match("^[Ff]ile%d*=(.+)$")
                if f then first = trim(f) break end
            end
            if not first then
                first = text:match('[Hh][Rr][Ee][Ff]%s*=%s*"([^"]+)"')
            end
            if first and first:find("^https?://") or (first and first:find("^rtsp://")) then
                result = first
            end
        end
    end
    pcall(function() conn.disconnect() end)
    return result, nil, code
end

-- Removes the "Invalid method call ... at ..." noise and keeps the real Java exception text
local function cleanError(msg)
    local m = tostring(msg)
    local real = nil
    for part in m:gmatch("%->%s*([^\n]+)") do real = part end
    if real then m = real end
    m = m:gsub("[\r\n]+", " ")
    return m
end

local function ytVideoId(url)
    return url:match("[?&]v=([%w_%-]+)") or url:match("youtu%.be/([%w_%-]+)")
        or url:match("/live/([%w_%-]+)") or url:match("/embed/([%w_%-]+)")
        or url:match("/shorts/([%w_%-]+)")
end

-- YouTube channel / @handle links get "/live" added, so they always open the current live stream
-- and never expire. Single video links (watch?v=) are upgraded automatically after they play.
local function addLiveSuffix(url)
    local u = tostring(url)
    local lu = u:lower()
    if not lu:find("youtube%.com") then return u end
    if ytVideoId(u) then return u end
    local base = u:match("^(https?://[^/]+/@[^/?#]+)")
        or u:match("^(https?://[^/]+/channel/[^/?#]+)")
        or u:match("^(https?://[^/]+/c/[^/?#]+)")
        or u:match("^(https?://[^/]+/user/[^/?#]+)")
    if base then return base .. "/live" end
    return u
end

-- Looks for a direct stream link inside a web page
local function findStreamInHtml(html, baseUrl)
    local h = html:gsub("\\/", "/")
    h = h:gsub("\\u0026", "&"):gsub("&amp;", "&")
    local exts = { "m3u8", "mp3", "aac", "m4a", "mp4" }
    for _, ext in ipairs(exts) do
        local abs = h:match('(https?://[^%s"\'<>\\]+%.' .. ext .. '[^%s"\'<>\\]*)')
        if abs then return abs end
        local rel = h:match('["\']([^"\'%s<>]+%.' .. ext .. '[^"\'%s<>]*)["\']')
        if rel and not rel:find("^data:") then return absoluteUrl(rel, baseUrl) end
    end
    local chan = h:match("embed/live_stream%?channel=([%w_%-]+)")
    if chan then return "https://www.youtube.com/channel/" .. chan .. "/live" end
    local yid = h:match("youtube%.com/embed/([%w_%-]+)") or h:match("youtube%-nocookie%.com/embed/([%w_%-]+)")
        or h:match("youtube%.com/watch%?v=([%w_%-]+)") or h:match("youtu%.be/([%w_%-]+)")
    if yid then return "https://www.youtube.com/watch?v=" .. yid end
    return nil
end

local function iframeList(html, baseUrl)
    local list = {}
    local h = html:gsub("\\/", "/")
    for src in h:gmatch('<[Ii][Ff][Rr][Aa][Mm][Ee][^>]-[Ss][Rr][Cc]%s*=%s*["\']([^"\']+)["\']') do
        local l = src:lower()
        if not l:find("^javascript:") and not l:find("^about:") and not l:find("^data:")
            and not l:find("doubleclick") and not l:find("facebook") and not l:find("twitter")
            and not l:find("googletagmanager") then
            table.insert(list, absoluteUrl(src, baseUrl))
            if #list >= 4 then break end
        end
    end
    return list
end

-- Returns playUrl, mode, referer
--   mode "external" = link type that cannot be played, "page" = web page with no stream found
-- When a server answers 401/403 we retry with other Referer / User-Agent combinations
local function headerVariants(hdrs)
    local list = {}
    local ref = hdrs and hdrs["Referer"]
    local origin = ref and ref:match("^(https?://[^/]+)")
    local vlc = "VLC/3.0.20 LibVLC/3.0.20"
    local mobile = "Mozilla/5.0 (Linux; Android 13; SM-A065F) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Mobile Safari/537.36"
    if ref then
        table.insert(list, { ["Referer"] = ref, ["User-Agent"] = vlc })
        table.insert(list, { ["Referer"] = ref, ["Origin"] = origin, ["User-Agent"] = mobile })
    end
    table.insert(list, { ["User-Agent"] = vlc })
    table.insert(list, { ["User-Agent"] = "okhttp/4.12.0" })
    return list
end

local resolveInner
resolveInner = function(url, depth, hdrs)
    local lower = url:lower()
    -- YouTube plays in the web player; direct extraction is blocked by YouTube
    if isYouTube(lower) then return url, "youtube", nil end
    if lower:find("^rtsp://") then return url, nil, nil end
    if not lower:find("^https?://") then return url, "external", nil end
    local final, html, hcode = probeStream(url, resolveFast and 3000 or 7000, hdrs)
    if hcode and (hcode == 401 or hcode == 403) and depth == 0 and not resolveFast then
        local keepHttp, keepCt, keepFinal = resolveInfo.http, resolveInfo.ctype, resolveInfo.final
        local tried = 0
        for _, v in ipairs(headerVariants(hdrs)) do
            tried = tried + 1
            local f2, h2, c2 = probeStream(url, 5000, v)
            if c2 and c2 < 400 then
                resolveInfo.workingHeaders = v
                resolveInfo.note = "Server refused the first headers; worked after trying another Referer/User-Agent combination"
                final, html, hcode = f2, h2, c2
                break
            end
        end
        if hcode >= 400 then
            resolveInfo.http, resolveInfo.ctype, resolveInfo.final = keepHttp, keepCt, keepFinal
            resolveInfo.note = "Tried " .. tried .. " other header combinations, the server still refuses (expired token, or region/IP lock)"
            local ref = hdrs and hdrs["Referer"]
            if ref and ref:find("^https?://") then
                local u2, m2, r2 = resolveInner(ref, 1, nil)
                if m2 == nil and u2 and u2 ~= ref then
                    resolveInfo.note = resolveInfo.note .. "; fresh stream link found on the official page"
                    return u2, nil, ref
                end
                resolveInfo.http, resolveInfo.ctype, resolveInfo.final = keepHttp, keepCt, keepFinal
            end
        end
    end
    if hcode and (hcode == 404 or hcode == 410 or hcode == 451 or hcode >= 500) then
        return url, "httperror", nil
    end
    if html then
        if depth >= 3 then return url, "page", nil end
        local found = findStreamInHtml(html, final)
        if found then
            local u, m, r = resolveInner(found, depth + 1)
            if m == nil and r == nil then r = final end
            if m ~= "page" then return u, m, r end
        end
        for _, src in ipairs(iframeList(html, final)) do
            local u, m, r = resolveInner(src, depth + 1)
            if m == nil then
                return u, m, r or src
            end
        end
        return url, "page", nil
    end
    return final, nil, nil
end

-- Runs on a background thread. Returns playUrl, mode, referer
local function resolveStream(url, hdrs)
    local clean = extractLink(url)
    if clean then url = clean end
    resolveInfo = {}
    local info = resolveInfo
    if not hdrs and url:lower():find("^https?://") and not isYouTube(url:lower()) then
        local origin = url:match("^(https?://[^/]+)")
        if origin then hdrs = { ["Referer"] = origin .. "/" } end
    end
    local ok, playUrl, mode, referer = pcall(resolveInner, url, 0, hdrs)
    if ok and playUrl then return playUrl, mode, referer, info end
    if not ok then
        info.error = cleanError(playUrl)
        local lm = info.error:lower()
        -- server cannot even be reached: the player would fail too, so skip it
        if lm:find("failed to connect") or lm:find("unknownhost") or lm:find("unable to resolve")
            or lm:find("refused") or lm:find("unreachable") or lm:find("no route") then
            return url, "neterror", nil, info
        end
    end
    return url, nil, nil, info
end

----------------------------------------------------------------
-- Auto update (GitHub)
----------------------------------------------------------------
local updating = false
local updateChecked = false

local function getScriptPath()
    local ok, src = pcall(function() return debug.getinfo(1, "S").source end)
    if ok and src and tostring(src):sub(1, 1) == "@" then
        local pth = tostring(src):sub(2)
        if pth:find("%.lua$") then return pth end
    end
    return DEFAULT_SCRIPT_PATH
end

local function parseVersion(v)
    local t = {}
    for n in tostring(v):gmatch("%d+") do
        table.insert(t, tonumber(n))
    end
    return t
end

local function isNewerVersion(a, b)
    local x, y = parseVersion(a), parseVersion(b)
    for i = 1, math.max(#x, #y) do
        local p, q = x[i] or 0, y[i] or 0
        if p ~= q then return p > q end
    end
    return false
end

local function fetchText(url, timeoutMs)
    local conn, finalUrl, code = openFollow(url, timeoutMs, { ["Cache-Control"] = "no-cache" })
    if conn == nil or code ~= 200 then return nil end
    local text = readStream(conn, 3000000)
    pcall(function() conn.disconnect() end)
    return text
end

-- Synchronous (call from a background thread). Returns "updated", "uptodate" or "fail"
local function doUpdateCheck(manual)
    if updating then return "busy" end
    updating = true
    local result, info = "fail", nil
    pcall(function()
        local stamp = "?t=" .. os.time()
        local vtext = fetchText(UPDATE_BASE .. "version.txt" .. stamp, 15000)
        local v = vtext and vtext:match("%d[%d%.]*")
        if not v then return end
        if not isNewerVersion(v, APP_VERSION) or prefs.getString("updated_to", "") == v then
            result = "uptodate"
            return
        end
        local code = fetchText(UPDATE_BASE .. "main.lua" .. stamp, 40000)
        if not code or #code < 5000 or not code:find("LIVE_TV_APP", 1, true) then return end
        local loader = loadstring or load
        local fn = loader(code)
        if not fn then return end
        local path = getScriptPath()
        local old = io.open(path, "rb")
        if old then
            local data = old:read("*a")
            old:close()
            local b = io.open(path .. ".bak", "wb")
            if b then b:write(data) b:close() end
        end
        local tmp = path .. ".new"
        local f = io.open(tmp, "wb")
        if not f then return end
        f:write(code)
        f:close()
        local renamed = os.rename(tmp, path)
        if not renamed then
            local f2 = io.open(path, "wb")
            if not f2 then return end
            f2:write(code)
            f2:close()
            pcall(function() os.remove(tmp) end)
        end
        local e = prefs.edit()
        e.putString("updated_to", v)
        e.apply()
        result = "updated"
        info = v
    end)
    updating = false
    if result == "updated" then
        infoDialog("Update Installed", "Live TV was updated to version " .. tostring(info) .. ". Please close and reopen the tool to use the new version.")
        runOnMain(function() service.speak("Update to version " .. tostring(info) .. " installed. Please restart Live TV.") end)
    elseif manual then
        runOnMain(function()
            if result == "uptodate" then
                service.speak("You already have the latest version, " .. APP_VERSION)
            else
                service.speak("Could not check for updates. Please check your internet connection")
            end
        end)
    end
    return result
end

local function checkForUpdates(manual)
    Thread(Runnable{
        run = function()
            doUpdateCheck(manual)
        end
    }).start()
end

----------------------------------------------------------------
-- Player control
----------------------------------------------------------------
local function setFullScreen(on)
    if playerLayout == nil or videoContainer == nil then return end
    if on and prefs.getBoolean("audio_only", false) then
        say("Full screen is available only in video mode")
        return
    end
    isFullScreen = on
    pcall(function()
        if on then
            headerLayout.setVisibility(View.GONE)
            controlsScroll.setVisibility(View.GONE)
            videoContainer.setLayoutParams(LinearLayout.LayoutParams(MATCH, 0, 1.0))
            exitFullBtn.setVisibility(View.VISIBLE)
        else
            headerLayout.setVisibility(View.VISIBLE)
            controlsScroll.setVisibility(View.VISIBLE)
            videoContainer.setLayoutParams(LinearLayout.LayoutParams(MATCH, dp(220)))
            exitFullBtn.setVisibility(View.GONE)
        end
    end)
    pcall(function()
        -- hide system bars in full screen (fullscreen + hide navigation + immersive sticky)
        playerLayout.setSystemUiVisibility(on and (4 + 2 + 4096) or 0)
    end)
    pcall(function()
        if fullBtn ~= nil then
            local label = on and "Small Screen" or "Full Screen"
            fullBtn.setText(label)
            fullBtn.setContentDescription(label)
        end
    end)
    say(on and "Full screen" or "Small screen")
end

local MOBILE_UA = "Mozilla/5.0 (Linux; Android 13; SM-A065F) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Mobile Safari/537.36"
local JS_PLAY = "(function(){var v=document.querySelector('video');if(v){v.muted=false;v.play();return 'ok';}return 'novideo';})()"
local JS_STATE = "(function(){var v=document.querySelector('video');var t=document.title.substring(0,40);if(!v)return 'novideo|'+t+'|'+location.href.substring(0,70);return ((v.readyState>=3&&!v.paused)?'playing':'notplaying')+'|rs='+v.readyState+'|paused='+v.paused+'|ended='+v.ended+'|hidden='+document.hidden+'|muted='+v.muted+'|vol='+Math.round(v.volume*100)+'|err='+(v.error?v.error.code:0)+'|'+t;})()"
-- makes the page believe it is always visible (mobile YouTube pauses hidden pages)
local JS_KEEP = "(function(){if(window.__ltv)return;window.__ltv=1;try{Object.defineProperty(document,'hidden',{get:function(){return false}});Object.defineProperty(document,'visibilityState',{get:function(){return 'visible'}});['visibilitychange','webkitvisibilitychange','pagehide','blur'].forEach(function(n){window.addEventListener(n,function(e){e.stopImmediatePropagation()},true);document.addEventListener(n,function(e){e.stopImmediatePropagation()},true);});}catch(e){}})()"

-- Asks the YouTube player for a lower resolution so the live stream does not stutter.
-- Returns nil when the quality setting is "best" (leave YouTube in automatic mode).
local function ytQualityJs()
    local q = tostring(prefs.getString("quality", "auto"))
    if prefs.getBoolean("audio_only", false) then q = "low" end
    local map = { low = "tiny", high = "hd720" }
    local level = map[q]
    if not level then return nil end
    return "(function(){var p=document.querySelector('.html5-video-player')||document.getElementById('movie_player');if(!p||!p.setPlaybackQualityRange||!p.getPlaybackQuality)return 'noapi';var cur=p.getPlaybackQuality();if(cur==='" .. level .. "')return 'ok '+cur;try{p.setPlaybackQualityRange('" .. level .. "','" .. level .. "');p.setPlaybackQuality('" .. level .. "');}catch(e){}return 'asked " .. level .. ", was '+cur;})()"
end

-- Channel id of the video being played (only for live content), so a one-off watch?v= link can be
-- upgraded to the channel's permanent /live page.
local JS_CHANNEL = "(function(){try{var r=window.ytInitialPlayerResponse;if(r&&r.videoDetails&&r.videoDetails.isLiveContent&&r.videoDetails.channelId)return r.videoDetails.channelId;}catch(e){}return '';})()"
-- Is the video on screen still a live stream? (YouTube may jump to another video when a live ends)
local JS_LIVECHK = "(function(){try{var p=document.getElementById('movie_player')||document.querySelector('.html5-video-player');if(p&&p.getVideoData){var d=p.getVideoData();if(d&&d.isLive===false)return 'notlive';if(d&&d.isLive===true)return 'live';}}catch(e){}return 'unknown';})()"

-- Installed inside the YouTube page: keeps the sound on every 200 ms (and on every play/volume event),
-- so the stream never starts muted and no silent gap is heard when it begins.
local JS_HOOK = "(function(){if(window.__ltvHook)return 'hooked';window.__ltvHook=1;function fix(){try{var p=document.getElementById('movie_player')||document.querySelector('.html5-video-player');if(p){if(p.isMuted&&p.isMuted())p.unMute();if(p.getVolume&&p.getVolume()==0&&p.setVolume)p.setVolume(100);}var v=document.querySelector('video');if(v){if(v.muted)v.muted=false;if(v.volume===0)v.volume=1;}}catch(e){}}setInterval(fix,200);['play','playing','volumechange','loadeddata'].forEach(function(n){document.addEventListener(n,fix,true);});fix();return 'installed';})()"

-- Ordinary web pages (TV sites that build the player with JavaScript): start the video, or press the
-- big play button / the first "HD 1" or "SD 1" channel button.
local JS_PAGEPLAY = "(function(){var v=document.querySelector('video');if(v){try{v.muted=false;v.play();}catch(e){}if(v.readyState>0)return 'video';}var sels=['.vjs-big-play-button','.jw-icon-display','.plyr__control--overlaid','button[aria-label*=\"lay\" i]','[class*=\"play-btn\"]','[class*=\"playBtn\"]'];for(var i=0;i<sels.length;i++){var e=document.querySelector(sels[i]);if(e){e.click();return 'clicked '+sels[i];}}var els=document.querySelectorAll('a,button,li,div,span');for(var j=0;j<els.length;j++){var t=(els[j].textContent||'').trim();if(/^(hd|sd)\\s*1$/i.test(t)){els[j].click();return 'clicked '+t;}}try{var c=document.elementFromPoint(innerWidth/2,innerHeight/2);if(c){c.click();return 'center';}}catch(e){}return 'none';})()"

-- The n-th usable <iframe> address of the page (the real player is often inside one; scripts cannot
-- reach into another site's frame, but its address can be opened as the page itself).
local function jsIframe(n)
    return "(function(){var f=document.querySelectorAll('iframe');var k=0;for(var i=0;i<f.length;i++){var s=f[i].src||f[i].getAttribute('data-src')||'';if(s.length<12||!/^https?:/i.test(s))continue;if(/doubleclick|googletagmanager|facebook|twitter|recaptcha|adservice|googlesyndication|about:blank/i.test(s))continue;if(k==" .. n .. ")return s;k++;}return '';})()"
end

-- What YouTube itself says about the video on the page: status|channelId|isLiveContent|isLive
local JS_YTSTATUS = "(function(){try{var r=window.ytInitialPlayerResponse;if(!r)return 'none';var ps=r.playabilityStatus||{};var vd=r.videoDetails||{};return (ps.status||'?')+'|'+(vd.channelId||'')+'|'+(vd.isLiveContent?1:0)+'|'+(vd.isLive?1:0);}catch(e){return 'err';}})()"

local function jsEval(js, cb)
    pcall(function() webPlayer.evaluateJavascript(js, cb) end)
end

local function youtubeWebUrl(url)
    local id = ytVideoId(url)
    if id then return "https://m.youtube.com/watch?v=" .. id end
    local u = url:gsub("//www%.youtube%.com", "//m.youtube.com")
    local lu = u:lower()
    if not lu:find("/live") and not lu:find("/streams") and (lu:find("/channel/") or lu:find("/@") or lu:find("/c/") or lu:find("/user/")) then
        u = (u:gsub("/+$", "")) .. "/live"
    end
    return u
end

local function stopWebPlayer()
    if webPlayer ~= nil then
        pcall(function() webPlayer.loadUrl("about:blank") end)
        pcall(function() webPlayer.setVisibility(View.GONE) end)
    end
    webPaused = false
end

local function destroyWebPlayer()
    if webPlayer ~= nil then
        pcall(function() webPlayer.loadUrl("about:blank") end)
        pcall(function() videoContainer.removeView(webPlayer) end)
        pcall(function() webPlayer.destroy() end)
        webPlayer = nil
    end
    webPaused = false
end

-- Plays a YouTube link with YouTube's own web player (best quality and smoothness).
-- onFail(reason) is called when it does not start, so the direct stream method can take over.
local function startWebPlayback(url, myToken, onFail, referer)
    local ok, err = pcall(function()
        if playerLayout == nil or videoContainer == nil then return end
        if webPlayer == nil then
            webPlayer = WebView(service)
            local ws = webPlayer.getSettings()
            ws.setJavaScriptEnabled(true)
            ws.setDomStorageEnabled(true)
            pcall(function() ws.setMediaPlaybackRequiresUserGesture(false) end)
            pcall(function() ws.setUserAgentString(MOBILE_UA) end)
            webPlayer.setWebViewClient(WebViewClient())
            pcall(function() webPlayer.setWebChromeClient(WebChromeClient()) end)
            pcall(function() webPlayer.setImportantForAccessibility(4) end)
            videoContainer.addView(webPlayer, FrameLayout.LayoutParams(FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.MATCH_PARENT))
        end
        if videoView ~= nil then videoView.setVisibility(View.GONE) end
        videoContainer.setVisibility(View.VISIBLE)
        webPlayer.setVisibility(View.VISIBLE)
        -- Audio only: the page keeps playing (it must stay "visible" for YouTube) but nothing is shown
        if prefs.getBoolean("audio_only", false) then
            if isFullScreen then setFullScreen(false) end
            pcall(function() videoContainer.setLayoutParams(LinearLayout.LayoutParams(MATCH, dp(2))) end)
            pcall(function() webPlayer.setAlpha(0) end)
        else
            if not isFullScreen then
                pcall(function() videoContainer.setLayoutParams(LinearLayout.LayoutParams(MATCH, dp(220))) end)
            end
            pcall(function() webPlayer.setAlpha(1) end)
        end
        webPaused = false
        if referer and tostring(referer):find("^https?://") then
            -- embedded players (Dailymotion etc.) refuse to start without the Referer of the site that embeds them
            local hm = HashMap()
            hm.put("Referer", tostring(referer))
            webPlayer.loadUrl(url, hm)
        else
            webPlayer.loadUrl(url)
        end
        attempt.webNote = "YouTube web player started: " .. url
        streamStarted = true
        if playPauseBtn ~= nil then
            playPauseBtn.setText("Pause")
            playPauseBtn.setContentDescription("Pause")
        end
        -- Keep the page playing: YouTube pauses when the screen reader speaks (audio focus) or when it stalls.
        -- Every 2 seconds check the video and resume it unless the user paused it.
        local elapsed = 0
        local everPlayed = false
        -- Fast ticker for the first 30 s: install the unmute hook the moment the page exists
        local fastN = 0
        local qDone = false
        local fastTick
        fastTick = Runnable{
            run = function()
                if myToken ~= playToken or webPlayer == nil then return end
                fastN = fastN + 1
                jsEval(JS_HOOK, nil)
                if fastN < 45 then mainHandler.postDelayed(fastTick, 700) end
            end
        }
        mainHandler.postDelayed(fastTick, 150)
        -- Live streams on YouTube stop and restart under a NEW video id. A channel's /live page always
        -- points at the current broadcast, so we keep that address and reload it when the stream ends.
        local origUrl = attempt.url or ""
        local isYt = isYouTube(origUrl:lower())
        local liveUrl = nil
        if isYt and not ytVideoId(origUrl) then liveUrl = origUrl end
        local chanChecked, lost, notLive, lastReload, tickN = false, 0, 0, -100000, 0
        local noVideo, frameTry = 0, 0
        local lastSaid = -100000
        -- remember the channel's permanent /live address instead of the one-off video link
        local function upgradeSaved(id)
            liveUrl = "https://www.youtube.com/channel/" .. id .. "/live"
            for _, c in ipairs(customChannels) do
                if c.urls and c.urls[1] == origUrl then
                    c.url = liveUrl
                    c.urls = { liveUrl }
                    saveList("custom_v1", customChannels)
                    say("This YouTube link was upgraded to the channel's live page. It will keep working when the stream restarts")
                    break
                end
            end
        end
        local offline, failedFast = 0, false
        local function reloadLive()
            if liveUrl == nil or elapsed - lastReload < 8000 then return end
            lastReload = elapsed
            lost, notLive = 0, 0
            attempt.webNote = "YouTube live restarted, reloaded " .. tostring(liveUrl)
            if elapsed - lastSaid > 60000 then
                lastSaid = elapsed
                say("The live stream stopped. Looking for the new live stream")
            end
            pcall(function() webPlayer.loadUrl(youtubeWebUrl(liveUrl)) end)
        end
        local tick
        tick = Runnable{
            run = function()
                if myToken ~= playToken or webPlayer == nil then return end
                elapsed = elapsed + 2000
                jsEval(JS_KEEP, nil)
                jsEval(JS_HOOK, nil)
                -- Expired video link or channel that is not live: YouTube says so as soon as the page loads, so
                -- find the new live stream (or give up) within seconds instead of waiting for the long timeout
                if isYt and not everPlayed and not failedFast and elapsed >= 4000 then
                    pcall(function()
                        webPlayer.evaluateJavascript(JS_YTSTATUS, ValueCallback{
                            onReceiveValue = function(v)
                                if myToken ~= playToken or everPlayed or failedFast then return end
                                local r = tostring(v):gsub('"', '')
                                local status, chan, liveContent, isLive = r:match("^([^|]*)|([^|]*)|([^|]*)|([^|]*)")
                                if not status then return end
                                attempt.ytStatus = r
                                local dead = (status ~= "OK") or (liveContent == "1" and isLive == "0")
                                if not dead then offline = 0 return end
                                if liveUrl == nil and chan:find("^UC") then
                                    upgradeSaved(chan)
                                    lastReload = -100000
                                    reloadLive()
                                elseif liveUrl ~= nil then
                                    offline = offline + 1
                                    if offline >= 3 then
                                        failedFast = true
                                        onFail("This channel is not live right now (YouTube status: " .. status .. ")")
                                    end
                                end
                            end
                        })
                    end)
                end
                local qjs = ytQualityJs()
                -- Ask for the lower quality as soon as the player API exists, once (changing it later makes
                -- YouTube re-buffer, which was heard as a short stall). Re-check only every 20 seconds.
                -- only after the video really plays: asking earlier left the player stuck with no data
                if qjs and everPlayed and (not qDone or elapsed % 20000 == 0) then
                    pcall(function()
                        webPlayer.evaluateJavascript(qjs, ValueCallback{
                            onReceiveValue = function(v)
                                local r = tostring(v):gsub('"', '')
                                attempt.webQuality = r
                                if not r:find("noapi") and r ~= "null" then qDone = true end
                            end
                        })
                    end)
                end
                pcall(function()
                    webPlayer.evaluateJavascript(JS_STATE, ValueCallback{
                        onReceiveValue = function(v)
                            if myToken ~= playToken or webPlayer == nil then return end
                            local r = tostring(v)
                            local st = r:match('^"?(%a+)') or "?"
                            local key = r:match('^"?(.-|.-|.-|.-|.-|.-|.-|.-)|') or r
                            attempt.webStates = attempt.webStates or {}
                            if attempt.webKey ~= key and #attempt.webStates < 30 then
                                table.insert(attempt.webStates, "t=" .. math.floor(elapsed / 1000) .. "s " .. r:gsub('"', ''):sub(1, 110))
                            end
                            attempt.webKey = key
                            if st == "playing" then
                                everPlayed = true
                                lost = 0
                            elseif everPlayed and not webPaused then
                                if r:find("ended=true") or st == "novideo" then
                                    lost = lost + 1
                                    if lost >= 3 then reloadLive() end
                                end
                            end
                            if isYt and st == "novideo" and not everPlayed and not failedFast and elapsed >= 12000 then
                                -- a /live link that ended up on the channel's home page means: not live now
                                local href = r:match("|([^|]*)$") or ""
                                if href ~= "" and not href:find("watch") and not href:find("/live") and not href:find("about:blank") then
                                    failedFast = true
                                    onFail("This channel is not live right now (YouTube opened " .. href .. ")")
                                end
                            end
                            if st == "novideo" and not isYt and not everPlayed then
                                noVideo = noVideo + 1
                                -- no <video> on the page: the player is probably inside an iframe, open the frame itself
                                if noVideo >= 4 and frameTry < 3 then
                                    noVideo = 0
                                    local n = frameTry
                                    frameTry = frameTry + 1
                                    pcall(function()
                                        webPlayer.evaluateJavascript(jsIframe(n), ValueCallback{
                                            onReceiveValue = function(fv)
                                                if myToken ~= playToken or webPlayer == nil then return end
                                                local u = tostring(fv):gsub('^"', ''):gsub('"$', '')
                                                u = u:gsub("\\/", "/"):gsub("\\u0026", "&")
                                                if u:find("^https?://") then
                                                    attempt.webNote = (attempt.webNote or "") .. " | opened frame: " .. u:sub(1, 100)
                                                    local hm = HashMap()
                                                    hm.put("Referer", origUrl)
                                                    webPlayer.loadUrl(u, hm)
                                                end
                                            end
                                        })
                                    end)
                                end
                            end
                            if st ~= "playing" and not webPaused and not isYt then
                                jsEval(JS_PAGEPLAY, nil)
                            elseif st ~= "playing" and not webPaused then
                                -- only nudge a video that is really paused; one that is buffering must be left alone
                                if r:find("paused=true") or st == "novideo" then jsEval(JS_PLAY, nil) end
                            elseif st == "playing" and webPaused then
                                -- the user paused: keep it paused even if YouTube tries to resume
                                jsEval("(function(){var p=document.getElementById('movie_player');try{if(p&&p.pauseVideo)p.pauseVideo();}catch(e){}var v=document.querySelector('video');if(v)v.pause();return 'p';})()", nil)
                            end
                        end
                    })
                end)
                tickN = tickN + 1
                if everPlayed and not webPaused and tickN % 2 == 0 then
                    if isYt and not chanChecked then
                        pcall(function()
                            webPlayer.evaluateJavascript(JS_CHANNEL, ValueCallback{
                                onReceiveValue = function(v)
                                    local id = tostring(v):match('(UC[%w_%-]+)')
                                    if id == nil or chanChecked or myToken ~= playToken then return end
                                    chanChecked = true
                                    attempt.webChannel = id
                                    if liveUrl == nil then upgradeSaved(id) end
                                end
                            })
                        end)
                    end
                    if tickN % 6 == 0 then
                        pcall(function()
                            webPlayer.evaluateJavascript(JS_LIVECHK, ValueCallback{
                                onReceiveValue = function(v)
                                    if myToken ~= playToken then return end
                                    if tostring(v):find("notlive") then
                                        notLive = notLive + 1
                                        if notLive >= 2 then reloadLive() end
                                    else
                                        notLive = 0
                                    end
                                end
                            })
                        end)
                    end
                end
                if not everPlayed and elapsed >= 45000 then
                    onFail("The page did not start playing within 45 seconds")
                    return
                end
                mainHandler.postDelayed(tick, 2000)
            end
        }
        mainHandler.postDelayed(tick, 2000)
    end)
    if not ok then
        onFail(cleanError(err))
    end
end

local function stopInternalPlayback()
    stopWebPlayer()
    pcall(function()
        if videoView ~= nil then videoView.stopPlayback() end
        if audioPlayer ~= nil then audioPlayer.reset() end
    end)
end

closePlayer = function(afterAction)
    runOnMain(function()
        pcall(function()
            cancelSleepTimer()
            sleepIdx = 1
            playToken = playToken + 1
            destroyWebPlayer()
            if watchdog ~= nil then
                pcall(function() mainHandler.removeCallbacks(watchdog) end)
                watchdog = nil
            end
            if videoView ~= nil then
                videoView.setOnPreparedListener(nil)
                videoView.setOnErrorListener(nil)
                videoView.stopPlayback()
                videoView = nil
            end
            if audioPlayer ~= nil then
                audioPlayer.setOnPreparedListener(nil)
                audioPlayer.setOnErrorListener(nil)
                if audioPlayer.isPlaying() then
                    audioPlayer.stop()
                end
                audioPlayer.release()
                audioPlayer = nil
            end
            if windowManager ~= nil and playerLayout ~= nil then
                windowManager.removeView(playerLayout)
                playerLayout = nil
                isFullScreen = false
                videoContainer = nil
                headerLayout = nil
                controlsScroll = nil
                fullBtn = nil
                exitFullBtn = nil
                statusText = nil
                subText = nil
                playPauseBtn = nil
                favBtn = nil
                modeBtn = nil
                sleepBtn = nil
                say("Player closed")
            end
            if afterAction == "list" then
                if lastListFn ~= nil then lastListFn() else showHome() end
            elseif afterAction == "home" then
                showHome()
            end
        end)
    end)
end

-- Collects stream links of similarly named channels from every source
local function extendMirrors(channel)
    channel.extended = true
    local lk = channel.lk or looseKey(channel.name)
    local have = {}
    for _, u in ipairs(channel.urls) do have[u] = true end
    local added = 0
    for _, other in ipairs(allChannels) do
        if other ~= channel then
            local ok = other.lk == lk
            if not ok and other.lk and #lk >= 5 and #other.lk >= 5 then
                -- only a prefix match with similar length (e.g. "geonews" and "geonewshd")
                local short, long = lk, other.lk
                if #short > #long then short, long = long, short end
                ok = (long:sub(1, #short) == short) and (#short / #long >= 0.75)
            end
            if ok then
                for _, u in ipairs(other.urls) do
                    if not have[u] then
                        have[u] = true
                        table.insert(channel.urls, u)
                        urlOrigin[u] = "Similar-name match with channel '" .. tostring(other.name) .. "' | " .. tostring(urlOrigin[u] or "?")
                        added = added + 1
                    end
                end
            end
        end
    end
    return added
end

----------------------------------------------------------------
-- Failure diagnostics (why a channel does not play)
----------------------------------------------------------------
local failLog = {}
local lastReport = nil

local function explainHttp(code)
    local m = {
        [400] = "Bad request", [401] = "Login required", [403] = "Access forbidden (blocked: wrong Referer or User-Agent, or region/IP lock)",
        [404] = "Stream not found (dead link)", [410] = "Stream was removed", [429] = "Too many requests",
        [451] = "Blocked for legal reasons"
    }
    if m[code] then return m[code] end
    if code >= 500 then return "Server error" end
    return "HTTP error"
end

local function explainException(msg)
    local m = tostring(msg)
    local lm = m:lower()
    if lm:find("failed to connect") or lm:find("connectexception") then
        if lm:find("timeout") or lm:find("timed out") then
            return "Could not connect: the server did not answer in time (offline, blocked, or unreachable from your network)"
        end
        return "Could not connect to the server (offline, blocked, or unreachable from your network)"
    elseif lm:find("unknownhost") or lm:find("unable to resolve") then
        return "Server name not found (dead domain or no internet)"
    elseif lm:find("timeout") or lm:find("timed out") then
        return "Server timed out"
    elseif lm:find("refused") then
        return "Connection refused by the server"
    elseif lm:find("ssl") or lm:find("certificate") or lm:find("handshake") then
        return "SSL or certificate problem"
    elseif lm:find("cleartext") then
        return "Android blocks non-secure http links"
    elseif lm:find("unreachable") or lm:find("no route") then
        return "Network unreachable"
    end
    return "Network error: " .. m:sub(1, 120)
end

local function explainPlayerError(what, extra)
    local names = { [1] = "Unknown player error", [100] = "Media server died", [200] = "Not valid for progressive playback" }
    local w = names[what] or ("Player error " .. tostring(what))
    local details = {
        [-1004] = "IO error: could not read the stream (server refused or blocked it, dead link, or no internet)",
        [-1005] = "Connection lost: the server closed the connection (often a refusal, expired link, or region lock)",
        [-1007] = "Malformed data: not a real media stream or corrupt data",
        [-1010] = "Unsupported format or codec: the built-in player cannot decode this stream",
        [-110] = "Timed out while connecting"
    }
    local e = details[extra]
    if extra == -2147483648 then
        e = "Low-level system error: format not supported or the server rejected the connection"
    end
    local short = "Player error"
    if e then short = "Player error, " .. e:match("^[^:]+") end
    return short, w .. " (what=" .. tostring(what) .. ", extra=" .. tostring(extra) .. ")" .. (e and (": " .. e) or "")
end

local function buildReport(channel, short, detail)
    local lines = {}
    local function add(l) table.insert(lines, l) end
    add("Time: " .. os.date("%Y-%m-%d %H:%M:%S"))
    add("Channel: " .. tostring(channel and channel.name or "?"))
    local a = (attempt.token == playToken) and attempt or {}
    add("Source: " .. tostring(a.idx or currentUrlIndex) .. " of " .. tostring(a.total or (channel and #channel.urls) or "?"))
    add("Link: " .. tostring(a.url or "?"))
    if a.playUrl and a.playUrl ~= a.url then
        add("Resolved link: " .. tostring(a.playUrl))
    end
    if a.url and urlOrigin[a.url] then add("Link came from: " .. urlOrigin[a.url]) end
    add("Mode: " .. tostring(a.mode or (prefs.getBoolean("audio_only", false) and "audio" or "video")))
    local info = a.info or {}
    if info.http then add("Server answer: HTTP " .. tostring(info.http) .. ((tonumber(info.http) or 0) >= 400 and (" " .. explainHttp(tonumber(info.http) or 0)) or " (OK)")) end
    if info.ctype and info.ctype ~= "" then add("Content type: " .. tostring(info.ctype)) end
    if info.final and info.final ~= a.url then add("Redirected to: " .. tostring(info.final)) end
    if info.error then add("Link check error: " .. explainException(info.error) .. " | " .. tostring(info.error):sub(1, 200)) end
    if a.webNote then add(tostring(a.webNote)) end
    if a.bufNote then add(a.bufNote) end
    if a.ytStatus then add("YouTube says: " .. tostring(a.ytStatus)) end
    if a.webQuality then add("YouTube quality: " .. tostring(a.webQuality)) end
    if a.webStates and #a.webStates > 0 then add("Web player states: " .. table.concat(a.webStates, " || ")) end
    if info.note then add("Note: " .. tostring(info.note)) end
    local h = a.hdrs
    if h then
        local parts = {}
        for k, v in pairs(h) do table.insert(parts, k .. "=" .. tostring(v)) end
        add("Headers sent: " .. table.concat(parts, "; "))
    else
        add("Headers sent: default")
    end
    add("Failure: " .. tostring(short))
    if detail and detail ~= "" and detail ~= short then add("Details: " .. tostring(detail)) end
    return table.concat(lines, "\n")
end

local function deviceHeader()
    local d = "Live TV version " .. APP_VERSION
    pcall(function()
        d = d .. " | Android " .. tostring(Build.VERSION.RELEASE) .. " (SDK " .. tostring(Build.VERSION.SDK_INT) .. ") | " .. tostring(Build.MODEL)
    end)
    d = d .. " | Country: " .. tostring(selectedCountry.name)
    return d
end

local function logFailure(channel, short, detail)
    local report = buildReport(channel, short, detail)
    lastReport = report
    table.insert(failLog, 1, report)
    while #failLog > 80 do table.remove(failLog) end
end

local function showReportDialog(title, text, onBack)
    runOnMain(function()
        local ok, err = pcall(function()
            local builder = AlertDialog.Builder(service)
            builder.setTitle(title)
            builder.setMessage(text)
            builder.setPositiveButton("Copy", {
                onClick = function(dialog, which)
                    local clipboard = service.getSystemService(Context.CLIPBOARD_SERVICE)
                    clipboard.setPrimaryClip(ClipData.newPlainText("LiveTV report", text))
                    service.speak("Report copied to clipboard. You can paste and send it now")
                    if onBack then onBack() end
                end
            })
            builder.setNegativeButton("Close", {
                onClick = function() if onBack then onBack() end end
            })
            presentDialog(builder, nil, onBack)
        end)
        if not ok then showErrorDialog("Report Error: " .. tostring(err)) end
    end)
end

local function showLastReport(onBack)
    local channel = currentChannels[currentIndex]
    local function show()
        local current = buildReport(channel, "Current status (not necessarily a failure)", "")
        local text = deviceHeader() .. "\n\nCURRENT ATTEMPT:\n" .. current
        if lastReport then
            text = text .. "\n\nLAST RECORDED FAILURE:\n" .. lastReport
        end
        showReportDialog("Last Failure Report", text, onBack)
    end
    -- Channels start in the native player without a link check (so nothing freezes). The check that
    -- finds the real reason (HTTP code, redirects) runs here, only when the report is requested.
    local a = attempt
    if a and a.token == playToken and a.direct and not a.info and a.url and a.failShort then
        say("Checking the link to find the exact reason, please wait")
        Thread(Runnable{
            run = function()
                pcall(function() Thread.currentThread().setPriority(4) end)
                resolveFast = false
                local ok, pu, mode, ref, info = pcall(resolveStream, a.url, a.hdrs)
                if ok and info then a.info = info end
                runOnMain(function()
                    pcall(function()
                        lastReport = buildReport(channel, a.failShort, a.failDetail or "")
                    end)
                    show()
                end)
            end
        }).start()
    else
        show()
    end
end

local function showFailureLog(onBack)
    if #failLog == 0 then
        showReportDialog("Failure Log", "No playback failures recorded in this session.", onBack)
        return
    end
    local text = deviceHeader() .. "\nTotal failures: " .. #failLog .. " (newest first)\n\n" .. table.concat(failLog, "\n\n-----\n\n")
    showReportDialog("Failure Log (" .. #failLog .. ")", text, onBack)
end

local function handleStreamFailure(short, detail, tok)
    if playerLayout == nil then return end
    -- a late error from a channel the user already left must not touch the current one
    if tok ~= nil and tok ~= playToken then return end
    if failureToken == playToken then return end
    failureToken = playToken
    if attempt and attempt.token == playToken then
        attempt.failShort, attempt.failDetail = short, detail
    end
    -- The native player failed on a plain link: one SHORT link check (redirects such as http -> https,
    -- referer) and a retry before giving up on this source. It is cancelled by any channel change.
    if attempt and attempt.direct and attempt.url and not probeFirst[attempt.url] then
        probeFirst[attempt.url] = true
        playCurrentStream()
        return
    end
    short = short or "Unknown failure"
    local channel = currentChannels[currentIndex]
    logFailure(channel, short, detail)
    if channel and channel.urls and currentUrlIndex < #channel.urls then
        currentUrlIndex = currentUrlIndex + 1
        say("Source failed: " .. short .. ". Trying source " .. currentUrlIndex .. " of " .. #channel.urls)
        playCurrentStream()
        return
    end
    -- A custom channel plays exactly the link the user saved: no "similar name" links from other lists
    -- (they hid the real reason in the report and played unrelated streams)
    local isCustomCh = false
    for _, c in ipairs(customChannels) do
        if c == channel then isCustomCh = true break end
    end
    if channel and not channel.extended and not isCustomCh then
        local added = extendMirrors(channel)
        if added > 0 then
            currentUrlIndex = currentUrlIndex + 1
            say("Source failed: " .. short .. ". Trying " .. added .. " alternative sources")
            playCurrentStream()
            return
        end
    end
    local autoSwitch = prefs.getBoolean("auto_switch", true)
    if autoSwitch and currentIndex < #currentChannels then
        say("All sources failed: " .. short .. ". Switching to next channel")
        currentIndex = currentIndex + 1
        currentUrlIndex = 1
        playCurrentStream()
    else
        say("Channel offline: " .. short .. ". Open Error Report to copy the details")
    end
end

-- After a buffering pause some devices play catch-up at a faster speed (sounds like fast-forward).
-- Force normal speed whenever the player reports buffering started/ended or rendering started.
local function normalSpeed(mp)
    pcall(function()
        if Build.VERSION.SDK_INT >= 23 then
            local pp = mp.getPlaybackParams()
            if pp.getSpeed() ~= 1.0 then
                mp.setPlaybackParams(pp.setSpeed(1.0))
            end
        end
    end)
end

local function onBuffering()
    local now = os.time()
    table.insert(bufTimes, now)
    while #bufTimes > 0 and now - bufTimes[1] > 45 do table.remove(bufTimes, 1) end
    sayDetail("Buffering")
    local url = attempt and attempt.url
    if #bufTimes >= 3 and url and not forceLow[url] then
        forceLow[url] = true
        bufTimes = {}
        local nv = attempt and attempt.info and tonumber(attempt.info.variants) or 0
        if nv > 1 then
            say("This stream is buffering a lot. Switching to a lower quality")
            playCurrentStream()
        else
            -- Only one quality exists: restarting would just add another long buffering pause
            attempt.bufNote = "Buffering often; this stream has only one quality, so the server or your internet is too slow for it"
            say("This channel has only one quality and the server is slow. It will keep buffering")
        end
    end
end

local function armWatchdog(myToken)
    if watchdog ~= nil then
        pcall(function() mainHandler.removeCallbacks(watchdog) end)
    end
    streamStarted = false
    local ms = prefs.getInt("timeout_sec", 15) * 1000 + 6000
    watchdog = Runnable{
        run = function()
            if myToken == playToken and not streamStarted and playerLayout ~= nil then
                handleStreamFailure("Timed out, stream did not start", "No picture or sound started within " .. math.floor(ms / 1000) .. " seconds (server slow, dead, blocked, or format unsupported)")
            end
        end
    }
    mainHandler.postDelayed(watchdog, ms)
end

local function startPlayback(playUrl, channel, myToken, referer, hdrs)
    local ok, err = pcall(function()
        if playerLayout == nil then return end
        local audioOnly = prefs.getBoolean("audio_only", false)
        local headers = HashMap()
        headers.put("User-Agent", UA)
        headers.put("Accept", "*/*")
        headers.put("Connection", "keep-alive")
        local lowerUrl = playUrl:lower()
        local origin = playUrl:match("^(https?://[^/]+)")
        if not lowerUrl:find("googlevideo") and not lowerUrl:find("youtube") then
            if referer then
                headers.put("Referer", referer)
            elseif origin then
                headers.put("Referer", origin .. "/")
            end
        end
        if hdrs then
            for k, v in pairs(hdrs) do
                headers.put(k, v)
            end
        end
        armWatchdog(myToken)

        if audioOnly then
            if isFullScreen then setFullScreen(false) end
            if videoContainer ~= nil then videoContainer.setVisibility(View.GONE) end
            if videoView ~= nil then
                videoView.stopPlayback()
                videoView.setVisibility(View.GONE)
            end
            if audioPlayer ~= nil then
                audioPlayer.reset()
            else
                audioPlayer = MediaPlayer()
                audioPlayer.setAudioStreamType(AudioManager.STREAM_MUSIC)
            end
            audioPlayer.setOnPreparedListener(MediaPlayer.OnPreparedListener{
                onPrepared = function(mp)
                    streamStarted = true
                    mp.start()
                    normalSpeed(mp)
                    if playPauseBtn ~= nil then
                        playPauseBtn.setText("Pause")
                        playPauseBtn.setContentDescription("Pause")
                    end
                    sayDetail("Audio streaming started")
                end
            })
            audioPlayer.setOnInfoListener(MediaPlayer.OnInfoListener{
                onInfo = function(mp, what, extra)
                    if what == 701 and myToken == playToken then onBuffering() end
                    if what == 701 or what == 702 or what == 3 then normalSpeed(mp) end
                    return false
                end
            })
            audioPlayer.setOnErrorListener(MediaPlayer.OnErrorListener{
                onError = function(mp, what, extra)
                    local sh, de = explainPlayerError(tonumber(what) or 0, tonumber(extra) or 0)
                    handleStreamFailure(sh, de, myToken)
                    return true
                end
            })
            audioPlayer.setDataSource(service, Uri.parse(playUrl), headers)
            audioPlayer.prepareAsync()
        else
            if audioPlayer ~= nil then
                audioPlayer.reset()
                audioPlayer.release()
                audioPlayer = nil
            end
            if videoContainer ~= nil then
                videoContainer.setVisibility(View.VISIBLE)
                if not isFullScreen then
                    pcall(function() videoContainer.setLayoutParams(LinearLayout.LayoutParams(MATCH, dp(220))) end)
                end
            end
            if videoView ~= nil then
                videoView.setVisibility(View.VISIBLE)
                videoView.stopPlayback()
                videoView.setVideoURI(Uri.parse(playUrl), headers)
                pcall(function() playerLayout.requestFocus() end)
                videoView.start()
            end
            if playPauseBtn ~= nil then
                playPauseBtn.setText("Pause")
                playPauseBtn.setContentDescription("Pause")
            end
        end
    end)
    if not ok then
        handleStreamFailure("Player could not start", tostring(err))
    end
end

playCurrentStream = function()
    local channel = currentChannels[currentIndex]
    if not channel then return end
    local activeUrl = channel.urls[currentUrlIndex] or channel.url
    local audioOnly = prefs.getBoolean("audio_only", false)
    playToken = playToken + 1
    local myToken = playToken
    attempt = {
        token = myToken,
        url = activeUrl,
        idx = currentUrlIndex,
        total = #channel.urls,
        hdrs = urlHeaders[activeUrl],
        mode = audioOnly and "audio" or "video"
    }
    bufTimes = {}

    pcall(function()
        local e = prefs.edit()
        e.putString("last_name", channel.name)
        e.putString("last_urls", table.concat(channel.urls, " "))
        e.apply()
    end)

    runOnMain(function()
        pcall(function()
            local mirrorInfo = ""
            if #channel.urls > 1 then
                mirrorInfo = string.format(" (Mirror %d/%d)", currentUrlIndex, #channel.urls)
            end
            if statusText ~= nil then
                statusText.setText(channel.name)
            end
            if subText ~= nil then
                local modeLabel = audioOnly and "Audio only" or "Video"
                subText.setText(string.format("Channel %d of %d  |  %s%s", currentIndex, #currentChannels, modeLabel, mirrorInfo))
            end
            refreshFavButton()
            refreshModeButton()
            say("Connecting to " .. channel.name .. mirrorInfo)
            mainHandler.postDelayed(Runnable{
                run = function()
                    if myToken == playToken and not streamStarted and playerLayout ~= nil then
                        say("Still connecting, please wait")
                    end
                end
            }, 6000)
            stopInternalPlayback()
        end)
        local function resolveAndPlay()
        resolveFast = true
        Thread(Runnable{
            run = function()
                pcall(function() Thread.currentThread().setPriority(4) end)
                if myToken ~= playToken then return end
                local activeHeaders = urlHeaders[activeUrl]
                local playUrl, mode, referer, info = resolveStream(activeUrl, activeHeaders)
                if playUrl == nil then playUrl = activeUrl end
                runOnMain(function()
                    if myToken ~= playToken then return end
                    attempt.info = info
                    attempt.playUrl = playUrl
                    if info and info.workingHeaders then
                        activeHeaders = info.workingHeaders
                        urlHeaders[activeUrl] = activeHeaders
                        attempt.hdrs = activeHeaders
                    end
                    if mode == "httperror" then
                        local code = tonumber(info and info.http) or 0
                        handleStreamFailure("Server says HTTP " .. code .. ", " .. explainHttp(code), "The server answered with an error before playing")
                        return
                    end
                    if mode == "youtube" then
                        handleStreamFailure("YouTube stream could not be resolved", "The YouTube page player could not be started")
                        return
                    end
                    if mode == "neterror" then
                        handleStreamFailure(explainException(info.error), "The server could not be reached, so the player was not tried: " .. tostring(info.error):sub(1, 160))
                        return
                    end
                    if mode == "page" then
                        -- the page builds its player with JavaScript: open it in the built-in page player
                        say("Opening the web page player")
                        startWebPlayback(activeUrl, myToken, function(reason)
                            if myToken ~= playToken then return end
                            stopWebPlayer()
                            handleStreamFailure("No live stream found on this web page", "No stream link in the page text, and the page player did not start a video: " .. tostring(reason))
                        end)
                        return
                    end
                    if mode == "external" then
                        local scheme = tostring(activeUrl):match("^(%a[%w+.-]*):") or "?"
                        handleStreamFailure("Link type cannot be played", "Scheme '" .. scheme .. "' is not supported by the built-in player (or the YouTube link could not be resolved)")
                        return
                    end
                    -- the link found inside a web page is itself a web player page (Dailymotion, embed pages):
                    -- the native player cannot play those, the page player can
                    local lp = tostring(playUrl):lower()
                    local isPagePlayer = playUrl ~= activeUrl and (lp:find("player%.html") or lp:find("dailymotion%.com") or lp:find("/embed/") or lp:find("/iframe"))
                    -- the link itself is a web page that refused our request (403 / bot protection): a real
                    -- browser view of it may still work
                    if not isPagePlayer and playUrl == activeUrl and tostring(info and info.ctype or ""):find("html") then
                        isPagePlayer = true
                    end
                    if isPagePlayer then
                        say("Opening the web page player")
                        local pu = playUrl
                        if lp:find("dailymotion%.com") and not lp:find("autoplay") then
                            pu = pu .. (pu:find("?", 1, true) and "&" or "?") .. "autoplay=1&mute=0"
                        end
                        attempt.webNote = "Web player page: " .. pu
                        startWebPlayback(pu, myToken, function(reason)
                            if myToken ~= playToken then return end
                            stopWebPlayer()
                            handleStreamFailure("Web player page did not start", tostring(reason))
                        end, referer or activeUrl)
                        return
                    end
                    startPlayback(playUrl, channel, myToken, referer, activeHeaders)
                end)
            end
        }).start()
        end
        if isYouTube(activeUrl:lower()) and prefs.getBoolean("yt_web", true) then
            startWebPlayback(youtubeWebUrl(activeUrl), myToken, function(reason)
                if myToken ~= playToken then return end
                attempt.webNote = "YouTube web player: " .. tostring(reason)
                stopWebPlayer()
                resolveAndPlay()
            end)
        elseif isDirectStream(activeUrl) and not probeFirst[activeUrl] then
            attempt.direct = true
            local h = urlHeaders[activeUrl]
            if not h then
                local origin = activeUrl:match("^(https?://[^/]+)")
                if origin then h = { ["Referer"] = origin .. "/" } end
            end
            attempt.hdrs = h
            attempt.playUrl = activeUrl
            local okp, errp = pcall(startPlayback, activeUrl, channel, myToken, nil, h)
            if not okp then handleStreamFailure("Could not start the player", cleanError(errp)) end
        else
            resolveAndPlay()
        end
    end)
end

-- Previous / Next are debounced: every press moves the channel number at once, but the stream is
-- started only after 600 ms without another press. Fast tapping used to start a stream for every press,
-- each one holding the Lua state while connecting, which froze the screen and made presses pile up.
local navRunnable = nil
local function startPlayIndex(index, debounce)
    if #currentChannels == 0 then return end
    if index < 1 then
        index = #currentChannels
    elseif index > #currentChannels then
        index = 1
    end
    currentIndex = index
    currentUrlIndex = 1
    if navRunnable ~= nil then
        pcall(function() mainHandler.removeCallbacks(navRunnable) end)
        navRunnable = nil
    end
    if not debounce then
        playCurrentStream()
        return
    end
    playToken = playToken + 1
    local ch = currentChannels[currentIndex]
    pcall(function() stopInternalPlayback() end)
    if ch then
        pcall(function() if statusText ~= nil then statusText.setText(ch.name) end end)
        say(ch.name)
    end
    navRunnable = Runnable{
        run = function()
            navRunnable = nil
            if playerLayout == nil then return end
            playCurrentStream()
        end
    }
    mainHandler.postDelayed(navRunnable, 600)
end

local function togglePlayPause()
    pcall(function()
        -- The button label is the single source of truth: "Pause" means it is playing now.
        local wantPause = (tostring(playPauseBtn.getText()) == "Pause")
        local function setLabel()
            local label = wantPause and "Play" or "Pause"
            playPauseBtn.setText(label)
            playPauseBtn.setContentDescription(label)
            say(wantPause and "Paused" or "Playing")
        end
        if webPlayer ~= nil and webPlayer.getVisibility() == View.VISIBLE then
            webPaused = wantPause
            local act = wantPause and "pause" or "play"
            jsEval("(function(){var p=document.getElementById('movie_player')||document.querySelector('.html5-video-player');var v=document.querySelector('video');try{if(p&&p." .. act .. "Video)p." .. act .. "Video();}catch(e){}try{if(v)v." .. act .. "();}catch(e){}return 'ok';})()", nil)
            setLabel()
            return
        end
        if prefs.getBoolean("audio_only", false) then
            if audioPlayer ~= nil then
                if wantPause then audioPlayer.pause() else audioPlayer.start() end
                setLabel()
            end
        else
            if videoView ~= nil then
                if wantPause then videoView.pause() else videoView.start() end
                setLabel()
            end
        end
    end)
end

local function changeVolume(direction)
    pcall(function()
        local am = service.getSystemService(Context.AUDIO_SERVICE)
        am.adjustStreamVolume(AudioManager.STREAM_MUSIC, direction, 0)
        local cur = am.getStreamVolume(AudioManager.STREAM_MUSIC)
        local max = am.getStreamMaxVolume(AudioManager.STREAM_MUSIC)
        service.speak("Volume " .. math.floor(cur * 100 / max) .. " percent")
    end)
end

local function cycleSleepTimer()
    cancelSleepTimer()
    sleepIdx = sleepIdx % #sleepOptions + 1
    local minutes = sleepOptions[sleepIdx]
    if minutes > 0 then
        sleepRunnable = Runnable{
            run = function()
                sleepRunnable = nil
                say("Sleep timer finished, closing player")
                closePlayer("none")
            end
        }
        mainHandler.postDelayed(sleepRunnable, minutes * 60 * 1000)
        say("Sleep timer set to " .. minutes .. " minutes")
    else
        say("Sleep timer turned off")
    end
    refreshSleepButton()
end

local function makeRow(parent, buttons)
    local row = LinearLayout(service)
    row.setOrientation(LinearLayout.HORIZONTAL)
    for _, b in ipairs(buttons) do
        local lp = LinearLayout.LayoutParams(0, WRAP, 1.0)
        lp.setMargins(dp(4), dp(4), dp(4), dp(4))
        row.addView(b, lp)
    end
    parent.addView(row, LinearLayout.LayoutParams(MATCH, WRAP))
end

local function createPlayerWindow()
    if playerLayout ~= nil then return end
    windowManager = service.getSystemService(Context.WINDOW_SERVICE)
    local wmParams = WindowManager.LayoutParams()
    wmParams.type = WindowManager.LayoutParams.TYPE_ACCESSIBILITY_OVERLAY
    wmParams.format = PixelFormat.TRANSLUCENT
    wmParams.flags = WindowManager.LayoutParams.FLAG_NOT_TOUCH_MODAL
    pcall(function()
        wmParams.flags = WindowManager.LayoutParams.FLAG_NOT_TOUCH_MODAL + WindowManager.LayoutParams.FLAG_HARDWARE_ACCELERATED
    end)
    wmParams.width = WindowManager.LayoutParams.MATCH_PARENT
    wmParams.height = WindowManager.LayoutParams.MATCH_PARENT
    wmParams.gravity = Gravity.CENTER

    local mainLayout = LinearLayout(service)
    mainLayout.setOrientation(LinearLayout.VERTICAL)
    mainLayout.setBackgroundColor(0xFF000000)
    pcall(function() mainLayout.setKeepScreenOn(prefs.getBoolean("keep_screen", true)) end)

    -- Header: channel name + details
    local header = LinearLayout(service)
    headerLayout = header
    header.setOrientation(LinearLayout.VERTICAL)
    header.setPadding(dp(16), dp(14), dp(16), dp(14))
    header.setBackgroundColor(C.bg)
    statusText = makeLabel("Loading stream...", 22, C.text, true)
    pcall(function() statusText.setAccessibilityHeading(true) end)
    subText = makeLabel("", 15, C.sub)
    header.addView(statusText)
    header.addView(subText)
    mainLayout.addView(header)

    -- Video area
    videoContainer = FrameLayout(service)
    -- small screen by default; Full Screen button makes it fill the display
    mainLayout.addView(videoContainer, LinearLayout.LayoutParams(MATCH, dp(220)))
    videoView = VideoView(service)
    videoContainer.addView(videoView, FrameLayout.LayoutParams(FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.MATCH_PARENT, Gravity.CENTER))
    exitFullBtn = makeButton("Exit Full Screen", "Exit full screen", C.danger, function()
        setFullScreen(false)
    end, 16)
    exitFullBtn.setVisibility(View.GONE)
    local exitLp = FrameLayout.LayoutParams(WRAP, WRAP, Gravity.BOTTOM + Gravity.CENTER_HORIZONTAL)
    exitLp.setMargins(0, 0, 0, dp(16))
    videoContainer.addView(exitFullBtn, exitLp)

    -- Controls
    local controls = LinearLayout(service)
    controls.setOrientation(LinearLayout.VERTICAL)
    controls.setPadding(dp(8), dp(6), dp(8), dp(10))
    controls.setBackgroundColor(C.bg)

    local btnPrev = makeButton("Previous Channel", "Previous channel", C.secondary, function()
        startPlayIndex(currentIndex - 1, true)
    end, 14)
    playPauseBtn = makeButton("Pause", "Pause", C.primary, togglePlayPause, 15)
    local btnNext = makeButton("Next Channel", "Next channel", C.secondary, function()
        startPlayIndex(currentIndex + 1, true)
    end, 14)
    fullBtn = makeButton("Full Screen", "Full Screen", C.secondary, function()
        setFullScreen(not isFullScreen)
    end, 14)
    makeRow(controls, { btnPrev, playPauseBtn, btnNext, fullBtn })

    favBtn = makeButton("Add to Favorites", "Add to Favorites", C.gold, function()
        local ch = currentChannels[currentIndex]
        if ch then
            local now = toggleFavorite(ch)
            say(now and (ch.name .. " added to favorites") or (ch.name .. " removed from favorites"))
            refreshFavButton()
        end
    end, 16)
    favBtn.setTextColor(0xFF000000)
    local btnVolDown = makeButton("Volume Down", "Volume down", C.secondary, function()
        changeVolume(AudioManager.ADJUST_LOWER)
    end, 16)
    local btnVolUp = makeButton("Volume Up", "Volume up", C.secondary, function()
        changeVolume(AudioManager.ADJUST_RAISE)
    end, 16)
    makeRow(controls, { favBtn, btnVolDown, btnVolUp })

    sleepBtn = makeButton("Sleep Timer: Off", "Sleep Timer: Off", C.secondary, cycleSleepTimer, 16)
    modeBtn = makeButton("Switch to Audio Only", "Switch to Audio Only", C.secondary, function()
        local newVal = not prefs.getBoolean("audio_only", false)
        local e = prefs.edit()
        e.putBoolean("audio_only", newVal)
        e.apply()
        say(newVal and "Audio only mode" or "Video mode")
        playCurrentStream()
    end, 16)
    local btnInfo = makeButton("Now Playing", "Now playing information", C.secondary, function()
        local ch = currentChannels[currentIndex]
        if ch then
            local msg = ch.name .. ", channel " .. currentIndex .. " of " .. #currentChannels
            if #ch.urls > 1 then
                msg = msg .. ", mirror " .. currentUrlIndex .. " of " .. #ch.urls
            end
            if isFavorite(ch) then msg = msg .. ", in favorites" end
            service.speak(msg)
        end
    end, 16)
    makeRow(controls, { sleepBtn, modeBtn, btnInfo })

    local btnList = makeButton("Channel List", "Back to channel list", C.secondary, function()
        closePlayer("list")
    end, 17)
    local btnClose = makeButton("Close Player", "Close player and go to home", C.danger, function()
        closePlayer("home")
    end, 17)
    local btnReport = makeButton("Error Report", "Error report for channels that do not play, copy to clipboard", C.secondary, function()
        showLastReport(nil)
    end, 16)
    makeRow(controls, { btnList, btnReport, btnClose })

    controlsScroll = ScrollView(service)
    controlsScroll.setBackgroundColor(C.bg)
    controlsScroll.addView(controls)
    mainLayout.addView(controlsScroll, LinearLayout.LayoutParams(MATCH, 0, 1.0))

    videoView.setOnPreparedListener(MediaPlayer.OnPreparedListener{
        onPrepared = function(mp)
            streamStarted = true
            mp.start()
            normalSpeed(mp)
            if playPauseBtn ~= nil then
                playPauseBtn.setText("Pause")
                playPauseBtn.setContentDescription("Pause")
            end
            sayDetail("Streaming started")
        end
    })
    pcall(function()
        videoView.setOnInfoListener(MediaPlayer.OnInfoListener{
            onInfo = function(mp, what, extra)
                if what == 701 and myToken == playToken then onBuffering() end
                if what == 701 or what == 702 or what == 3 then normalSpeed(mp) end
                return false
            end
        })
    end)
    videoView.setOnErrorListener(MediaPlayer.OnErrorListener{
        onError = function(mp, what, extra)
            local sh, de = explainPlayerError(tonumber(what) or 0, tonumber(extra) or 0)
            handleStreamFailure(sh, de, myToken)
            return true
        end
    })

    pcall(function() videoView.setFocusable(false) end)
    pcall(function()
        mainLayout.setFocusable(true)
        mainLayout.setFocusableInTouchMode(true)
        mainLayout.setOnKeyListener(View.OnKeyListener{
            onKey = function(v, keyCode, event)
                if keyCode == KeyEvent.KEYCODE_BACK then
                    if event.getAction() == KeyEvent.ACTION_UP then
                        if isFullScreen then
                            setFullScreen(false)
                        else
                            closePlayer("list")
                        end
                    end
                    return true
                end
                return false
            end
        })
    end)
    playerLayout = mainLayout
    windowManager.addView(playerLayout, wmParams)
    pcall(function() mainLayout.requestFocus() end)
end

playStreamByIndex = function(index)
    runOnMain(function()
        local ok, err = pcall(function()
            createPlayerWindow()
            startPlayIndex(index)
        end)
        if not ok then showErrorDialog("Player Error: " .. tostring(err)) end
    end)
end

----------------------------------------------------------------
-- Channel lists
----------------------------------------------------------------
showChannelOptions = function(channels, idx, opts)
    opts = opts or {}
    local ch = channels[idx]
    if not ch then return end
    local function refresh()
        if opts.refresh then
            opts.refresh()
        elseif lastListFn then
            lastListFn()
        else
            showHome()
        end
    end
    local labels = {}
    local actions = {}
    table.insert(labels, "Play")
    table.insert(actions, function()
        currentChannels = channels
        playStreamByIndex(idx)
    end)
    table.insert(labels, isFavorite(ch) and "Remove from Favorites" or "Add to Favorites")
    table.insert(actions, function()
        local now = toggleFavorite(ch)
        say(now and (ch.name .. " added to favorites") or (ch.name .. " removed from favorites"))
        refresh()
    end)
    if opts.mode == "custom" then
        table.insert(labels, "Edit Channel")
        table.insert(actions, function()
            showCustomForm(idx)
        end)
        table.insert(labels, "Delete Channel")
        table.insert(actions, function()
            confirmDialog("Delete Channel", "Delete " .. ch.name .. " from your custom channels?", function()
                table.remove(customChannels, idx)
                saveList("custom_v1", customChannels)
                say("Channel deleted")
                refresh()
            end)
        end)
    end
    table.insert(labels, "Cancel")
    table.insert(actions, function() refresh() end)

    runOnMain(function()
        local ok, err = pcall(function()
            local builder = AlertDialog.Builder(service)
            builder.setTitle(ch.name)
            builder.setItems(labels, {
                onClick = function(dialog, which)
                    actions[which + 1]()
                end
            })
            presentDialog(builder, nil, refresh)
        end)
        if not ok then showErrorDialog("Options Error: " .. tostring(err)) end
    end)
end

showChannelList = function(title, channels, opts)
    opts = opts or {}
    if #channels == 0 then
        say("No channels in " .. title)
        showHome()
        return
    end
    currentChannels = channels
    lastListFn = function() showChannelList(title, channels, opts) end
    if opts.mode == "custom" then
        say("Tap a channel to play it. Long press a channel to edit, delete or add it to favorites")
    end

    local names = {}
    for i, ch in ipairs(channels) do
        local label = i .. ". " .. ch.name
        if isFavorite(ch) then label = label .. ", Favorite" end
        if #ch.urls > 1 then label = label .. ", " .. #ch.urls .. " mirrors" end
        table.insert(names, label)
    end

    runOnMain(function()
        local ok, err = pcall(function()
            local builder = AlertDialog.Builder(service)
            builder.setTitle(title .. " (" .. #channels .. ")")
            builder.setItems(names, {
                onClick = function(dialog, which)
                    playStreamByIndex(which + 1)
                end
            })
            builder.setPositiveButton("Home", {
                onClick = function() showHome() end
            })
            if opts.neutralLabel then
                builder.setNeutralButton(opts.neutralLabel, {
                    onClick = function() opts.neutralFn() end
                })
            end
            if opts.backFn then
                builder.setNegativeButton("Back", {
                    onClick = function() opts.backFn() end
                })
            else
                builder.setNegativeButton("Close", nil)
            end
            local dlg = presentDialog(builder, nil, opts.backFn or showHome)
            pcall(function()
                dlg.getListView().setOnItemLongClickListener(AdapterView.OnItemLongClickListener{
                    onItemLongClick = function(parent, itemView, position, id)
                        pcall(function() dlg.dismiss() end)
                        showChannelOptions(channels, position + 1, opts)
                        return true
                    end
                })
            end)
        end)
        if not ok then showErrorDialog("List Error: " .. tostring(err)) end
    end)
end

showCategoryMenu = function()
    if #activeCategoryList == 0 then
        say("No channels loaded. Use Change Country to load channels.")
        showHome()
        return
    end
    local labels = {}
    local actions = {}
    table.insert(labels, "All Channels (" .. #allChannels .. ")")
    table.insert(actions, function()
        showChannelList("All Channels", allChannels, { backFn = showCategoryMenu })
    end)
    for _, cat in ipairs(activeCategoryList) do
        local count = #(categoryMap[cat] or {})
        table.insert(labels, cat .. " (" .. count .. ")")
        table.insert(actions, function()
            showChannelList(cat, categoryMap[cat], { backFn = showCategoryMenu })
        end)
    end
    runOnMain(function()
        local ok, err = pcall(function()
            local builder = AlertDialog.Builder(service)
            builder.setTitle(selectedCountry.name .. " Categories")
            builder.setItems(labels, {
                onClick = function(dialog, which)
                    actions[which + 1]()
                end
            })
            builder.setPositiveButton("Home", {
                onClick = function() showHome() end
            })
            builder.setNegativeButton("Close", nil)
            presentDialog(builder, nil, showHome)
        end)
        if not ok then showErrorDialog("UI Error: " .. tostring(err)) end
    end)
end

showFavorites = function()
    if #favorites == 0 then
        infoDialog("Favorites", "You have no favorite channels yet. While a channel is playing, press Add to Favorites. You can also long press any channel in a list.", showHome)
        return
    end
    showChannelList("Favorites", favorites, { mode = "favorites", refresh = showFavorites })
end

showCustomList = function()
    if #customChannels == 0 then
        say("No custom channels yet. Add your first channel.")
        showCustomForm(nil)
        return
    end
    showChannelList("My Custom Channels", customChannels, {
        mode = "custom",
        refresh = showCustomList,
        neutralLabel = "Add Channel",
        neutralFn = function() showCustomForm(nil) end
    })
end

----------------------------------------------------------------
-- Custom channel form
----------------------------------------------------------------
showCustomForm = function(editIndex)
    runOnMain(function()
        local ok, err = pcall(function()
            local existing = editIndex and customChannels[editIndex] or nil
            local scroll, col = panelContainer()

            addTo(col, makeLabel("Channel name (optional)", 16, C.sub), 4)
            local nameEt = makeEdit("Channel name", existing and existing.name or "")
            addTo(col, nameEt, 4)

            addTo(col, makeLabel("Stream link or web page link", 16, C.sub), 14)
            local urlEt = makeEdit("Stream link", existing and existing.url or "")
            addTo(col, urlEt, 4)

            local dlg

            local function closeForm()
                pcall(function() dlg.dismiss() end)
            end

            local function save(playAfter)
                local name = trim(nameEt.getText().toString())
                local rawUrl = trim(urlEt.getText().toString())
                local cleaned, leftover = extractLink(rawUrl)
                local url = cleaned or rawUrl
                if cleaned and cleaned ~= rawUrl then
                    urlEt.setText(cleaned)
                end
                if name == "" and leftover and leftover ~= "" and #leftover <= 60 then
                    name = leftover
                end
                if not url:find("^%a[%w+.-]*://") and url:find("%.") and not url:find("%s") then
                    url = "https://" .. url
                end
                local lu = url:lower()
                local fixedUrl = addLiveSuffix(url)
                if fixedUrl ~= url then
                    url = fixedUrl
                    lu = url:lower()
                    say("YouTube channel link detected, live was added to it")
                end
                local validScheme = lu:find("^https?://") or lu:find("^rtsp://") or lu:find("^rtmps?://")
                    or lu:find("^udp://") or lu:find("^rtp://") or lu:find("^mmsh?://")
                if not validScheme or #url < 10 then
                    say("Invalid link. Please enter a full stream or YouTube link")
                    return
                end
                if name == "" then
                    name = url:match("^%a+://([^/:?]+)") or "Custom Channel"
                end
                name = name:gsub("[\t\r\n]", " ")
                local entry
                if editIndex and customChannels[editIndex] then
                    entry = customChannels[editIndex]
                    entry.name = name
                    entry.url = url
                    entry.urls = { url }
                else
                    for _, c in ipairs(customChannels) do
                        if c.url == url then
                            say("This link is already saved as " .. c.name)
                            return
                        end
                    end
                    entry = { name = name, url = url, urls = { url } }
                    table.insert(customChannels, entry)
                end
                saveList("custom_v1", customChannels)
                say("Channel " .. name .. " saved")
                closeForm()
                if playAfter then
                    currentChannels = { entry }
                    lastListFn = showCustomList
                    playStreamByIndex(1)
                else
                    showCustomList()
                end
            end

            addTo(col, makeButton("Paste Link from Clipboard", "Paste link from clipboard", C.secondary, function()
                local okp, text = pcall(function()
                    local cm = service.getSystemService(Context.CLIPBOARD_SERVICE)
                    local clip = cm.getPrimaryClip()
                    if clip ~= nil and clip.getItemCount() > 0 then
                        return tostring(clip.getItemAt(0).coerceToText(service))
                    end
                    return ""
                end)
                text = trim(okp and text or "")
                if text == "" then
                    say("Clipboard is empty")
                else
                    local cl, left = extractLink(text)
                    if cl then
                        urlEt.setText(cl)
                        if trim(nameEt.getText().toString()) == "" and left and left ~= "" and #left <= 60 then
                            nameEt.setText(left)
                        end
                        say("Link extracted and pasted")
                    else
                        say("No link found in the clipboard text")
                    end
                end
            end), 18)
            addTo(col, makeButton("Save", "Save channel", C.success, function() save(false) end), 12)
            addTo(col, makeButton("Save and Play", "Save channel and play now", C.primary, function() save(true) end), 12)
            addTo(col, makeButton("Cancel", "Cancel", C.danger, function()
                closeForm()
                if #customChannels > 0 then showCustomList() else showHome() end
            end), 12)

            local builder = AlertDialog.Builder(service)
            builder.setCustomTitle(makeTitle(existing and "Edit Custom Channel" or "Add Custom Channel"))
            builder.setView(scroll)
            dlg = presentDialog(builder, true, function()
                if #customChannels > 0 then showCustomList() else showHome() end
            end)
            pcall(function()
                dlg.getWindow().clearFlags(WindowManager.LayoutParams.FLAG_ALT_FOCUSABLE_IM)
                dlg.getWindow().clearFlags(WindowManager.LayoutParams.FLAG_NOT_FOCUSABLE)
                dlg.getWindow().setSoftInputMode(WindowManager.LayoutParams.SOFT_INPUT_ADJUST_RESIZE)
            end)
        end)
        if not ok then showErrorDialog("Form Error: " .. tostring(err)) end
    end)
end

----------------------------------------------------------------
-- Search
----------------------------------------------------------------
showSearch = function()
    runOnMain(function()
        local ok, err = pcall(function()
            local scroll, col = panelContainer()
            addTo(col, makeLabel("Type part of a channel name", 16, C.sub), 4)
            local et = makeEdit("Channel name", "")
            addTo(col, et, 4)
            local dlg
            local function doSearch()
                local q = trim(et.getText().toString()):lower()
                if q == "" then
                    say("Please type a channel name")
                    return
                end
                local results = {}
                local seen = {}
                local function scan(list)
                    for _, ch in ipairs(list) do
                        if ch.name:lower():find(q, 1, true) and not seen[ch] then
                            seen[ch] = true
                            table.insert(results, ch)
                        end
                    end
                end
                scan(customChannels)
                scan(favorites)
                scan(allChannels)
                pcall(function() dlg.dismiss() end)
                if #results == 0 then
                    infoDialog("Search", "No channels found for: " .. q, showSearch)
                else
                    say(#results .. " channels found")
                    showChannelList("Search: " .. q, results, { backFn = showSearch })
                end
            end
            addTo(col, makeButton("Search", "Search channels", C.primary, doSearch), 14)
            addTo(col, makeButton("Cancel", "Cancel", C.danger, function()
                pcall(function() dlg.dismiss() end)
                showHome()
            end), 12)
            local builder = AlertDialog.Builder(service)
            builder.setCustomTitle(makeTitle("Search Channels"))
            builder.setView(scroll)
            dlg = presentDialog(builder, true, showHome)
            pcall(function()
                dlg.getWindow().clearFlags(WindowManager.LayoutParams.FLAG_ALT_FOCUSABLE_IM)
                dlg.getWindow().clearFlags(WindowManager.LayoutParams.FLAG_NOT_FOCUSABLE)
                dlg.getWindow().setSoftInputMode(WindowManager.LayoutParams.SOFT_INPUT_ADJUST_RESIZE)
            end)
        end)
        if not ok then showErrorDialog("Search Error: " .. tostring(err)) end
    end)
end

----------------------------------------------------------------
-- Loading channels
----------------------------------------------------------------
local function addChannelEntry(name, str, rawGroup, existingUrls, channelDict, hdrs, origin)
    if existingUrls[str] then return false end
    existingUrls[str] = true
    urlOrigin[str] = tostring(origin or "?") .. " (listed as: " .. tostring(name) .. ")"
    if hdrs then urlHeaders[str] = hdrs end
    local cleanKey = looseKey(name)
    local unifiedGroup = normalizeCategory(rawGroup, name)
    if channelDict[cleanKey] then
        local existingList = channelDict[cleanKey].urls
        if str:find("^https://") and existingList[1] and existingList[1]:find("^http://") then
            table.insert(existingList, 1, str)
        else
            table.insert(existingList, str)
        end
    else
        local item = {
            name = name,
            url = str,
            urls = { str },
            lk = cleanKey,
            category = unifiedGroup
        }
        channelDict[cleanKey] = item
        table.insert(allChannels, item)
        if not categoryMap[unifiedGroup] then
            categoryMap[unifiedGroup] = {}
        end
        table.insert(categoryMap[unifiedGroup], item)
    end
    return true
end

-- M3U playlists. Understands #EXTVLCOPT referrer / user-agent lines and url|Referer=... suffixes
local function newM3uJob(streamUrl, timeoutMs, defaultGroup, existingUrls, channelDict, targetCountryCode, idSuffix, label, strict)
    local job = { added = 0, seen = 0, done = false }
    local conn, reader, line
    local currentName = nil
    local currentRawGroup = defaultGroup or "General"
    local currentCountry, currentId = nil, nil
    local pendingRef, pendingUA = nil, nil
    local function finish()
        job.done = true
        pcall(function() reader.close() end)
        pcall(function() conn.disconnect() end)
    end
    local function handle(str)
        if str:find("^#EXTINF") then
            local grp = str:match('group%-title="([^"]+)"')
            if grp and grp ~= "" then
                currentRawGroup = grp
            else
                currentRawGroup = defaultGroup or "General"
            end
            currentCountry = str:match('tvg%-country="([^"]+)"')
            currentId = str:match('tvg%-id="([^"]*)"')
            local name = str:match(',%s*(.-)$')
            if not name or name == "" then
                name = str:match('tvg%-name="([^"]+)"')
            end
            currentName = name or "Live Stream"
            pendingRef, pendingUA = nil, nil
        elseif str:find("^#EXTVLCOPT") then
            local r = str:match("[Hh]ttp%-referrer=(.+)$") or str:match("[Hh]ttp%-referer=(.+)$")
            if r then pendingRef = trim(r) end
            local u = str:match("[Hh]ttp%-user%-agent=(.+)$")
            if u then pendingUA = trim(u) end
        elseif str:find("^https?://") and currentName then
            local hdrs = nil
            local base, params = str:match("^([^|]+)|(.+)$")
            if base then
                str = base
                hdrs = {}
                for k, v in params:gmatch("([%w%-]+)=([^&]*)") do
                    local lk = k:lower()
                    if lk == "referer" or lk == "referrer" then
                        hdrs["Referer"] = v
                    elseif lk == "user-agent" then
                        hdrs["User-Agent"] = v
                    elseif lk == "origin" then
                        hdrs["Origin"] = v
                    end
                end
            end
            if pendingRef or pendingUA then
                hdrs = hdrs or {}
                if pendingRef then hdrs["Referer"] = pendingRef end
                if pendingUA then hdrs["User-Agent"] = pendingUA end
            end
            local isAllowed = true
            if targetCountryCode ~= nil then
                if currentCountry == nil or currentCountry:upper() ~= targetCountryCode:upper() then
                    isAllowed = false
                end
            end
            if isAllowed and idSuffix then
                if currentId and currentId ~= "" then
                    local lid = currentId:lower()
                    if not (lid:find("%." .. idSuffix .. "$") or lid:find("%." .. idSuffix .. "@")) then
                        isAllowed = false
                    end
                elseif strict then
                    isAllowed = false
                end
            end
            if isAllowed then
                job.seen = job.seen + 1
                if addChannelEntry(currentName, str, currentRawGroup, existingUrls, channelDict, hdrs, label) then
                    job.added = job.added + 1
                end
            end
            currentName = nil
            currentRawGroup = defaultGroup or "General"
            currentCountry, currentId = nil, nil
            pendingRef, pendingUA = nil, nil
        end
    end
    local opened = false
    -- one call = one slice of work (the connection, or about 25 ms of lines)
    function job.step()
        if job.done then return end
        if not opened then
            opened = true
            local c, finalUrl, code = openFollow(streamUrl, timeoutMs)
            conn = c
            if conn == nil then job.done = true return end
            if code ~= 200 then finish() return end
            reader = BufferedReader(InputStreamReader(conn.getInputStream(), "UTF-8"))
            line = reader.readLine()
            return
        end
        local t0 = System.currentTimeMillis()
        while line ~= nil and (System.currentTimeMillis() - t0) < 25 do
            local str = tostring(line):match("^%s*(.-)%s*$")
            if str and str ~= "" then handle(str) end
            line = reader.readLine()
        end
        if line == nil then finish() end
    end
    return job
end

local function humanizeId(id)
    local n = tostring(id):match("^([^%.@]+)") or tostring(id)
    n = n:gsub("(%l)(%u)", "%1 %2")
    n = n:gsub("(%u)(%u%l)", "%1 %2")
    n = n:gsub("(%a)(%d)", "%1 %2")
    return n
end

-- iptv-org JSON API: every stream with its own referrer / user agent. Filters by country code.
local function newApiJob(apiUrl, timeoutMs, code, existingUrls, channelDict, label)
    local job = { added = 0, seen = 0, done = false }
    local conn, jr
    local opened = false
    local function finish()
        job.done = true
        pcall(function() jr.close() end)
        pcall(function() conn.disconnect() end)
    end
    local function str()
        local t = tostring(jr.peek())
        if t == "STRING" then return tostring(jr.nextString()) end
        jr.skipValue()
        return ""
    end
    local function readOne()
        local ch, u, title, ref, ua = "", "", "", "", ""
        jr.beginObject()
        while jr.hasNext() do
            local name = tostring(jr.nextName())
            if name == "channel" then ch = str()
            elseif name == "url" then u = str()
            elseif name == "title" then title = str()
            elseif name == "referrer" then ref = str()
            elseif name == "user_agent" then ua = str()
            else jr.skipValue() end
        end
        jr.endObject()
        local chl = ch:lower()
        if (chl:find("%." .. code .. "$") or chl:find("%." .. code .. "@")) and u:find("^https?://") then
            job.seen = job.seen + 1
            title = trim(title)
            if title == "" then title = humanizeId(ch) end
            local hdrs = nil
            ref, ua = trim(ref), trim(ua)
            if ref ~= "" or ua ~= "" then
                hdrs = {}
                if ref ~= "" then hdrs["Referer"] = ref end
                if ua ~= "" then hdrs["User-Agent"] = ua end
            end
            if addChannelEntry(title, u, "", existingUrls, channelDict, hdrs, label) then
                job.added = job.added + 1
            end
        end
    end
    function job.step()
        if job.done then return end
        if not opened then
            opened = true
            local c, finalUrl, rc = openFollow(apiUrl, timeoutMs)
            conn = c
            if conn == nil then job.done = true return end
            if rc ~= 200 then finish() return end
            -- Streamed with JsonReader: the file is huge, never hold it in memory as a string.
            jr = luajava.bindClass("android.util.JsonReader")(InputStreamReader(conn.getInputStream(), "UTF-8"))
            jr.beginArray()
            return
        end
        local t0 = System.currentTimeMillis()
        while (System.currentTimeMillis() - t0) < 25 do
            if not jr.hasNext() then finish() return end
            readOne()
        end
    end
    return job
end

fetchChannelsForCountry = function(country)
    if isLoading then
        service.speak("Already loading, please wait")
        return
    end
    isLoading = true
    selectedCountry = country
    service.speak("Loading " .. country.name .. " channels from all sources, please wait")
    -- Short network timeouts while loading: a dead host must not stall the tool for long.
    local timeoutSec = math.min(prefs.getInt("timeout_sec", 15) * 1000, 6000)
    allChannels = {}
    categoryMap = {}
    activeCategoryList = {}
    source1Count = 0
    source2Count = 0
    source3Count = 0
    sourceStats = {}
    urlHeaders = {}
    urlOrigin = {}
    local existingUrls = {}
    local channelDict = {}

    local code = country.code
    local ioBase = "https://iptv-org.github.io/iptv/"
    local gh = "https://raw.githubusercontent.com/iptv-org/iptv/"
    local sources = {}
    local function addSource(label, url, group, filter, bucket, idSuffix, isApi, strict)
        table.insert(sources, { label = label, url = url, group = group, filter = filter, bucket = bucket, idSuffix = idSuffix, isApi = isApi, strict = strict })
    end
    -- bucket 1 = country lists, 2 = language lists, 3 = extra sources
    addSource("iptv-org Country List", ioBase .. "countries/" .. code .. ".m3u", "General", nil, 1)
    addSource("iptv-org Country Backup", gh .. "gh-pages/countries/" .. code .. ".m3u", "General", nil, 1)
    for _, src in ipairs(country.extra or {}) do
        addSource(src.label, src.url, "General", nil, 3, src.idSuffix)
    end
    addSource("iptv-org Streams API", "https://iptv-org.github.io/api/streams.json", "General", nil, 3, nil, true)
    -- Language lists mix many countries (Urdu, Punjabi, Arabic...): keep only this country's channels
    addSource("Language " .. country.lang, ioBase .. "languages/" .. country.lang .. ".m3u", "Regional / Language", nil, 2, code, false, true)
    for _, l in ipairs(country.extraLangs or {}) do
        addSource("Language " .. l, ioBase .. "languages/" .. l .. ".m3u", "Regional / Language", nil, 2, code, false, true)
    end
    addSource("iptv-org Master Streams", gh .. "master/streams/" .. code .. ".m3u", "Master Streams", nil, 3)

    -- go back to the tool's home screen right away; it shows "loading" and refreshes itself when done
    showHome()
    local idx = 1
    local job = nil
    -- "Top Channels": the well known channels of the country, picked by name from the channels that
    -- actually loaded (no fixed links, so a dead link can never end up here). Entertainment first, then sports.
    local topNames = {
        pk = { "hum tv", "ary digital", "geo entertainment", "har pal geo", "hum sitaray", "express entertainment", "aaj entertainment", "ptv home", "urdu 1", "ptv sports", "geo super", "ten sports", "a sports" },
        ["in"] = { "star plus", "zee tv", "sony tv", "colors", "sab tv", "star bharat", "star sports", "sony ten", "dd national" },
    }
    local function buildTopChannels()
        local names = topNames[code]
        if not names then return end
        local list, used = {}, {}
        for _, nm in ipairs(names) do
            local key = chKey(nm)
            local best = nil
            for _, ch in ipairs(allChannels) do
                if not used[ch] and chKey(ch.name):find(key, 1, true) then
                    if best == nil or #ch.urls > #best.urls then best = ch end
                end
            end
            if best then
                used[best] = true
                table.insert(list, best)
            end
        end
        if #list > 0 then categoryMap["Top Channels"] = list end
    end
    local function finishAll(errText)
        isLoading = false
        pcall(buildTopChannels)
        local orderedCategories = { "Top Channels", "News", "Entertainment", "Movies", "Kids & Cartoons", "Islamic", "Religious", "Sports", "Other" }
        for _, cat in ipairs(orderedCategories) do
            if categoryMap[cat] and #categoryMap[cat] > 0 then
                table.insert(activeCategoryList, cat)
            end
        end
        if errText then showErrorDialog("Load Error: " .. tostring(errText)) end
        runOnMain(function()
            local working = 0
            for _, st in ipairs(sourceStats) do
                if st.found > 0 then working = working + 1 end
            end
            if #allChannels == 0 then
                service.speak("No online channels found for " .. country.name .. ". You can still use favorites and custom channels.")
            else
                service.speak(#allChannels .. " channels loaded for " .. country.name .. ". " .. working .. " of " .. #sourceStats .. " sources working")
            end
        end)
        showHome()
        if not updateChecked and prefs.getBoolean("auto_update", true) then
            updateChecked = true
            doUpdateCheck(false)
        end
    end
    local function closeSource(src, j)
        table.insert(sourceStats, { label = src.label, found = j and j.seen or 0, added = j and j.added or 0 })
        local n = j and j.added or 0
        if src.bucket == 1 then
            source1Count = source1Count + n
        elseif src.bucket == 2 then
            source2Count = source2Count + n
        else
            source3Count = source3Count + n
        end
    end
    -- one call = one small slice of work; see runSteps
    runSteps(function()
        local src = sources[idx]
        if src == nil then
            finishAll(nil)
            return true
        end
        if job == nil then
            if src.isApi then
                job = newApiJob(src.url, timeoutSec, code, existingUrls, channelDict, src.label)
            else
                job = newM3uJob(src.url, timeoutSec, src.group, existingUrls, channelDict, src.filter, src.idSuffix, src.label, src.strict)
            end
        end
        local ok = pcall(job.step)
        if not ok then job.done = true end
        if job.done then
            closeSource(src, job)
            job = nil
            idx = idx + 1
        end
        return false
    end, function(err)
        finishAll(err)
    end)
end

showCountryDialog = function()
    local names = {}
    for _, c in ipairs(countries) do
        table.insert(names, c.name)
    end
    runOnMain(function()
        local ok, err = pcall(function()
            local builder = AlertDialog.Builder(service)
            builder.setTitle("Select Country")
            builder.setItems(names, {
                onClick = function(dialog, which)
                    local e = prefs.edit()
                    e.putInt("last_country_index", which)
                    e.apply()
                    local chosen = countries[which + 1]
                    -- start the loading after the dialog has closed, and never let an error escape
                    -- into the screen reader (an uncaught error here closed the whole tool)
                    mainHandler.postDelayed(Runnable{
                        run = function()
                            local okf, errf = pcall(fetchChannelsForCountry, chosen)
                            if not okf then
                                isLoading = false
                                pcall(function() showErrorDialog("Country Error: " .. tostring(errf)) end)
                                pcall(showHome)
                            end
                        end
                    }, 200)
                end
            })
            builder.setNegativeButton("Back", {
                onClick = function() showHome() end
            })
            presentDialog(builder, nil, showHome)
        end)
        if not ok then showErrorDialog("Country Error: " .. tostring(err)) end
    end)
end

----------------------------------------------------------------
-- Settings
----------------------------------------------------------------
showSettings = function()
    runOnMain(function()
        local ok, err = pcall(function()
            local function onOff(v) return v and "ON" or "OFF" end
            local isAudioOnly = prefs.getBoolean("audio_only", false)
            local isAutoSwitch = prefs.getBoolean("auto_switch", true)
            local isSpeech = prefs.getBoolean("speech", true)
            local isVerbose = prefs.getBoolean("verbose", true)
            local isKeepScreen = prefs.getBoolean("keep_screen", true)
            local isAutoUpdate = prefs.getBoolean("auto_update", true)
            local timeout = prefs.getInt("timeout_sec", 15)

            local labels = {}
            local actions = {}
            local function add(label, fn)
                table.insert(labels, label)
                table.insert(actions, fn)
            end
            local function toggle(key, current, spoken)
                return function()
                    local newVal = not current
                    local e = prefs.edit()
                    e.putBoolean(key, newVal)
                    e.apply()
                    service.speak(spoken .. " " .. (newVal and "enabled" or "disabled"))
                    showSettings()
                end
            end

            add("Playback Mode: " .. (isAudioOnly and "Audio Only" or "Video"), function()
                local modeItems = { "Video (picture and sound)", "Audio Only (sound only, uses less data)" }
                runOnMain(function()
                    local mb = AlertDialog.Builder(service)
                    mb.setTitle("Playback Mode")
                    mb.setItems(modeItems, {
                        onClick = function(d, idx)
                            local e = prefs.edit()
                            e.putBoolean("audio_only", idx == 1)
                            e.apply()
                            service.speak(idx == 1 and "Playback mode set to audio only. Channels will play as audio" or "Playback mode set to video. Channels will play with video")
                            showSettings()
                        end
                    })
                    mb.setNegativeButton("Back", {
                        onClick = function() showSettings() end
                    })
                    presentDialog(mb, nil, showSettings)
                end)
            end)
            add("Auto Switch Failed Stream: " .. onOff(isAutoSwitch), toggle("auto_switch", isAutoSwitch, "Auto switch"))
            add("Stream Connection Timeout: " .. timeout .. " seconds", function()
                local timeouts = { 10, 15, 20, 30, 45 }
                local items = {}
                for _, t in ipairs(timeouts) do table.insert(items, t .. " Seconds") end
                runOnMain(function()
                    local subBuilder = AlertDialog.Builder(service)
                    subBuilder.setTitle("Select Timeout")
                    subBuilder.setItems(items, {
                        onClick = function(d, idx)
                            local e = prefs.edit()
                            e.putInt("timeout_sec", timeouts[idx + 1])
                            e.apply()
                            service.speak("Timeout set to " .. timeouts[idx + 1] .. " seconds")
                            showSettings()
                        end
                    })
                    subBuilder.setNegativeButton("Back", {
                        onClick = function() showSettings() end
                    })
                    presentDialog(subBuilder, nil, showSettings)
                end)
            end)
            add("Spoken Feedback: " .. onOff(isSpeech), function()
                local newVal = not isSpeech
                local e = prefs.edit()
                e.putBoolean("speech", newVal)
                e.apply()
                service.speak("Spoken feedback " .. (newVal and "enabled" or "disabled"))
                showSettings()
            end)
            add("Announcement Detail: " .. (isVerbose and "Detailed" or "Minimal"), function()
                local newVal = not isVerbose
                local e = prefs.edit()
                e.putBoolean("verbose", newVal)
                e.apply()
                service.speak("Announcement detail " .. (newVal and "detailed" or "minimal"))
                showSettings()
            end)
            local qualityLabels = { auto = "Auto (about 480p)", low = "Low (smoothest)", high = "High (about 720p)", best = "Best (may buffer)" }
            local curQuality = tostring(prefs.getString("quality", "auto"))
            add("Stream Quality: " .. (qualityLabels[curQuality] or qualityLabels.auto), function()
                local keys = { "auto", "low", "high", "best" }
                local items = {}
                for _, k in ipairs(keys) do table.insert(items, qualityLabels[k]) end
                runOnMain(function()
                    local qb = AlertDialog.Builder(service)
                    qb.setTitle("Stream Quality")
                    qb.setItems(items, {
                        onClick = function(d, idx)
                            local e = prefs.edit()
                            e.putString("quality", keys[idx + 1])
                            e.apply()
                            service.speak("Stream quality set to " .. items[idx + 1])
                            showSettings()
                        end
                    })
                    qb.setNegativeButton("Back", {
                        onClick = function() showSettings() end
                    })
                    presentDialog(qb, nil, showSettings)
                end)
            end)
            local isYtWeb = prefs.getBoolean("yt_web", true)
            add("YouTube Playback: " .. (isYtWeb and "YouTube Player (recommended)" or "Direct Stream"), function()
                local newVal = not isYtWeb
                local e = prefs.edit()
                e.putBoolean("yt_web", newVal)
                e.apply()
                service.speak(newVal and "YouTube links play with the YouTube player" or "YouTube links play as a direct stream")
                showSettings()
            end)
            add("Keep Screen On While Playing: " .. onOff(isKeepScreen), toggle("keep_screen", isKeepScreen, "Keep screen on"))
            add("Country: " .. selectedCountry.name .. " (change)", function()
                showCountryDialog()
            end)
            add("Clear All Favorites (" .. #favorites .. ")", function()
                if #favorites == 0 then
                    service.speak("No favorites to clear")
                    showSettings()
                    return
                end
                confirmDialog("Clear Favorites", "Remove all " .. #favorites .. " favorite channels?", function()
                    while #favorites > 0 do table.remove(favorites) end
                    saveList("favorites_v1", favorites)
                    service.speak("All favorites cleared")
                    showSettings()
                end)
            end)
            add("Delete All Custom Channels (" .. #customChannels .. ")", function()
                if #customChannels == 0 then
                    service.speak("No custom channels to delete")
                    showSettings()
                    return
                end
                confirmDialog("Delete Custom Channels", "Delete all " .. #customChannels .. " custom channels?", function()
                    while #customChannels > 0 do table.remove(customChannels) end
                    saveList("custom_v1", customChannels)
                    service.speak("All custom channels deleted")
                    showSettings()
                end)
            end)
            add("Auto Update: " .. onOff(isAutoUpdate), toggle("auto_update", isAutoUpdate, "Auto update"))
            add("Check for Updates Now (version " .. APP_VERSION .. ")", function()
                service.speak("Checking for updates")
                checkForUpdates(true)
                showSettings()
            end)
            add("Failure Log (" .. #failLog .. "): view and copy", function()
                showFailureLog(showSettings)
            end)
            add("Clear Failure Log", function()
                while #failLog > 0 do table.remove(failLog) end
                lastReport = nil
                service.speak("Failure log cleared")
                showSettings()
            end)
            add("Reset Settings to Default", function()
                confirmDialog("Reset Settings", "Reset all settings to their default values? Favorites and custom channels will be kept.", function()
                    local e = prefs.edit()
                    e.remove("audio_only")
                    e.remove("auto_switch")
                    e.remove("timeout_sec")
                    e.remove("speech")
                    e.remove("verbose")
                    e.remove("keep_screen")
                    e.remove("auto_update")
                    e.remove("quality")
                    e.remove("yt_web")
                    e.apply()
                    service.speak("Settings reset")
                    showSettings()
                end)
            end)
            add("Help and About", function()
                infoDialog("Help and About",
                    "Live TV for Commentary Screen Reader. Version " .. APP_VERSION .. ".\n\n" ..
                    "Home: browse channels by category, open favorites, manage custom channels, search or change country.\n\n" ..
                    "Favorites: while playing press Add to Favorites, or long press a channel in any list.\n\n" ..
                    "Custom channels: add any link (stream, m3u8, radio, YouTube live or a web page that has a live stream), type it or paste it. Extra text around the link is removed automatically. Then save. Open a saved channel to play, edit or delete it.\n\n" ..
                    "If a channel does not play, the next source is tried, then similar channels, then the next channel (if Auto Switch is on).\n\n" ..
                    "Player: previous and next channel, play and pause, volume, sleep timer, audio only mode and now playing information.",
                    showSettings)
            end)

            local builder = AlertDialog.Builder(service)
            builder.setTitle("Settings")
            builder.setItems(labels, {
                onClick = function(dialog, which)
                    actions[which + 1]()
                end
            })
            builder.setNegativeButton("Back to Home", {
                onClick = function() showHome() end
            })
            presentDialog(builder, nil, showHome)
        end)
        if not ok then showErrorDialog("Settings Error: " .. tostring(err)) end
    end)
end

----------------------------------------------------------------
-- Home screen
----------------------------------------------------------------
showHome = function()
    runOnMain(function()
        local ok, err = pcall(function()
            if homeDialog ~= nil then
                pcall(function() homeDialog.dismiss() end)
                homeDialog = nil
            end
            local scroll, col = panelContainer()

            local status
            if isLoading then
                status = selectedCountry.name .. ": loading channels, please wait. Search and Browse open when loading is finished"
            elseif #allChannels > 0 then
                status = selectedCountry.name .. ": " .. #allChannels .. " channels available"
            else
                status = selectedCountry.name .. ": no online channels loaded"
            end
            if #sourceStats > 0 then
                local w = 0
                for _, st in ipairs(sourceStats) do
                    if st.found > 0 then w = w + 1 end
                end
                status = status .. " | Sources working: " .. w .. " of " .. #sourceStats
            end
            status = status .. " | Mode: " .. (prefs.getBoolean("audio_only", false) and "Audio only" or "Video")
            addTo(col, makeLabel(status, 16, C.sub), 4)

            local dlg
            local function go(fn)
                return function()
                    pcall(function() dlg.dismiss() end)
                    homeDialog = nil
                    fn()
                end
            end

            -- Channel lists open only after loading is complete, so all channels appear together
            local function goData(fn)
                return function()
                    if isLoading then
                        say("Channels are still loading, please wait a moment")
                        return
                    end
                    pcall(function() dlg.dismiss() end)
                    homeDialog = nil
                    fn()
                end
            end

            addTo(col, makeButton("Search Channels", "Search channels by name", C.secondary, goData(showSearch)), 14)
            local favHomeBtn = makeButton("Favorites (" .. #favorites .. ")", "Favorites, " .. #favorites .. " channels", C.gold, go(showFavorites))
            favHomeBtn.setTextColor(0xFF000000)
            addTo(col, favHomeBtn, 12)
            addTo(col, makeButton("My Custom Channels (" .. #customChannels .. ")", "My custom channels, " .. #customChannels .. " saved", C.secondary, go(showCustomList)), 12)
            addTo(col, makeButton("Add Custom Channel", "Add a new custom channel link", C.success, go(function() showCustomForm(nil) end)), 12)

            local lastName = tostring(prefs.getString("last_name", ""))
            local lastUrls = tostring(prefs.getString("last_urls", ""))
            if lastName ~= "" and lastUrls ~= "" then
                addTo(col, makeButton("Resume: " .. lastName, "Resume last channel, " .. lastName, C.primary, go(function()
                    local urls = {}
                    for u in lastUrls:gmatch("%S+") do table.insert(urls, u) end
                    if #urls > 0 then
                        currentChannels = { { name = lastName, url = urls[1], urls = urls } }
                        lastListFn = showHome
                        playStreamByIndex(1)
                    end
                end)), 12)
            end

            addTo(col, makeButton("Browse by Category", "Browse channels by category", C.secondary, goData(showCategoryMenu)), 12)
            addTo(col, makeButton("Change Country", "Change country, currently " .. selectedCountry.name, C.secondary, go(showCountryDialog)), 12)
            addTo(col, makeButton("Settings", "Settings", C.secondary, go(showSettings)), 12)
            addTo(col, makeButton("Exit", "Exit Live TV", C.danger, go(function()
                exitTool(false)
            end)), 12)

            if #sourceStats > 0 then
                local working = 0
                for _, st in ipairs(sourceStats) do
                    if st.found > 0 then working = working + 1 end
                end
                addTo(col, makeLabel("Source details (channels found per source):", 15, C.sub, true), 6)
                for _, st in ipairs(sourceStats) do
                    local line
                    if st.found > 0 then
                        line = st.label .. ": " .. st.found .. " channels (" .. st.added .. " new)"
                    else
                        line = st.label .. ": not working (0 channels)"
                    end
                    addTo(col, makeLabel(line, 14, st.found > 0 and C.sub or 0xFFEF9A9A), 2)
                end
            end


            -- the favorites button text is dark on gold
            local builder = AlertDialog.Builder(service)
            builder.setCustomTitle(makeTitle("Live TV"))
            builder.setView(scroll)
            dlg = presentDialog(builder, true, function() exitTool(false) end)
            homeDialog = dlg
        end)
        if not ok then showErrorDialog("Home Error: " .. tostring(err)) end
    end)
end

----------------------------------------------------------------
-- Exit / system navigation (Back, Home, Overview)
----------------------------------------------------------------
exitTool = function(silent)
    pcall(function()
        if homeReceiver ~= nil then
            service.unregisterReceiver(homeReceiver)
        end
    end)
    homeReceiver = nil
    pcall(function() _G.LIVETV_RECEIVER = nil end)
    pcall(function()
        if currentDialog ~= nil then currentDialog.dismiss() end
    end)
    currentDialog = nil
    homeDialog = nil
    if playerLayout ~= nil then
        closePlayer("none")
    end
    if not silent then
        say("Live TV closed")
        -- Exit goes to the phone's home screen (instead of leaving the screen reader's own window open).
        -- 2 = GLOBAL_ACTION_HOME of the accessibility service.
        mainHandler.postDelayed(Runnable{
            run = function()
                pcall(function() service.performGlobalAction(2) end)
            end
        }, 250)
    end
end

-- Home and Overview (recent apps) close the tool, like other tools do
local function registerNavReceiver()
    pcall(function()
        if _G.LIVETV_RECEIVER ~= nil then
            pcall(function() service.unregisterReceiver(_G.LIVETV_RECEIVER) end)
            _G.LIVETV_RECEIVER = nil
        end
        pcall(function() import "com.androlua.LuaBroadcastReceiver" end)
        if LuaBroadcastReceiver == nil then return end
        local receiver = LuaBroadcastReceiver(LuaBroadcastReceiver.OnReceiveListener{
            onReceive = function(ctx, intent)
                local reason = tostring(intent.getStringExtra("reason") or "")
                if reason == "homekey" or reason == "recentapps" then
                    exitTool(true)
                end
            end
        })
        service.registerReceiver(receiver, IntentFilter(Intent.ACTION_CLOSE_SYSTEM_DIALOGS))
        homeReceiver = receiver
        _G.LIVETV_RECEIVER = receiver
    end)
end

----------------------------------------------------------------
-- Start
----------------------------------------------------------------
local function initLiveTV()
    registerNavReceiver()
    favorites = loadList("favorites_v1")
    customChannels = loadList("custom_v1")
    local defaultIndex = prefs.getInt("last_country_index", 0)
    if defaultIndex < 0 or defaultIndex >= #countries then
        defaultIndex = 0
    end
    selectedCountry = countries[defaultIndex + 1]
    showHome()
    fetchChannelsForCountry(countries[defaultIndex + 1])
end

local ok, initErr = pcall(initLiveTV)
if not ok then
    showErrorDialog("Init Error: " .. tostring(initErr))
    pcall(showHome)
end
