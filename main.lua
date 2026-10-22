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
import "java.lang.Runnable"
import "java.util.HashMap"
import "org.json.JSONObject"
import "java.io.OutputStreamWriter"

----------------------------------------------------------------
-- Basic state
----------------------------------------------------------------
local mainHandler = Handler(Looper.getMainLooper())
local prefs = service.getSharedPreferences("LiveTV_Settings", Context.MODE_PRIVATE)

local countries = {
    { name = "Pakistan", code = "pk", lang = "urd", extraLangs = { "pan", "snd" } },
    { name = "India", code = "in", lang = "hin", extraLangs = { "tam", "tel", "mal", "kan", "mar", "guj", "pan" } },
    { name = "Bangladesh", code = "bd", lang = "ben" },
    { name = "Afghanistan", code = "af", lang = "pus" },
    { name = "Nepal", code = "np", lang = "nep" },
    { name = "Saudi Arabia", code = "sa", lang = "ara" },
    { name = "United Arab Emirates", code = "ae", lang = "ara" },
    { name = "Turkey", code = "tr", lang = "tur" },
    { name = "United Kingdom", code = "gb", lang = "eng" },
    { name = "United States", code = "us", lang = "eng" }
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

local sleepOptions = { 0, 15, 30, 45, 60, 90 }
local sleepIdx = 1
local sleepRunnable = nil
local playToken = 0
local failureToken = -1
local streamStarted = false
local watchdog = nil

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

local function presentDialog(builder, dark)
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

local function showErrorDialog(errorText)
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
            presentDialog(builder)
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
    local s1, e1 = text:find(url, 1, true)
    local leftover = ""
    if s1 then
        leftover = text:sub(1, s1 - 1) .. " " .. text:sub(e1 + 1)
    end
    url = url:gsub("[%.,;:!%)%]}>\"']+$", "")
    if not url:find("^%a[%w+.-]*://") then
        url = "https://" .. url
    end
    leftover = trim(leftover)
    leftover = leftover:gsub("^[%p%s]+", ""):gsub("[%p%s]+$", "")
    return url, leftover
end

local function readStream(conn, limit)
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

-- Returns the final playable url for http(s) links
local function probeStream(urlStr, timeoutMs)
    local conn, finalUrl, code = openFollow(urlStr, timeoutMs)
    if conn == nil then return urlStr end
    local ctype = tostring(conn.getContentType() or ""):lower()
    if code == 200 and (ctype:find("text/html") or ctype:find("xhtml")) then
        local html = readStream(conn, 3000000)
        pcall(function() conn.disconnect() end)
        return finalUrl, html
    end
    local path = finalUrl:lower():gsub("%?.*$", "")
    local isList = ctype:find("mpegurl") or ctype:find("scpls") or ctype:find("x%-ms%-asx")
        or path:find("%.m3u8?$") or path:find("%.pls$") or path:find("%.asx$")
    local result = finalUrl
    if code == 200 and isList then
        local text = readStream(conn, 8000)
        if text:find("#EXT%-X") then
            result = finalUrl
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
    return result
end

local function ytVideoId(url)
    return url:match("[?&]v=([%w_%-]+)") or url:match("youtu%.be/([%w_%-]+)")
        or url:match("/live/([%w_%-]+)") or url:match("/embed/([%w_%-]+)")
        or url:match("/shorts/([%w_%-]+)")
end

local function ytFromPage(pageUrl)
    local conn, finalUrl = openFollow(pageUrl, 12000, {
        ["Cookie"] = "CONSENT=YES+1; SOCS=CAI",
        ["Accept-Language"] = "en-US,en;q=0.9"
    })
    if conn == nil then return nil end
    local html = readStream(conn, 4000000)
    pcall(function() conn.disconnect() end)
    local hls = html:match('"hlsManifestUrl":"(.-)"')
    if hls then
        return (hls:gsub("\\u0026", "&"):gsub("\\/", "/"))
    end
    local id = ytVideoId(finalUrl) or html:match('canonical" href="https://www%.youtube%.com/watch%?v=([%w_%-]+)')
    return nil, id
end

local function ytInnertube(id)
    local conn = URL("https://www.youtube.com/youtubei/v1/player?prettyPrint=false").openConnection()
    conn.setRequestMethod("POST")
    conn.setConnectTimeout(12000)
    conn.setReadTimeout(12000)
    conn.setDoOutput(true)
    conn.setRequestProperty("Content-Type", "application/json")
    conn.setRequestProperty("User-Agent", "com.google.android.youtube/19.09.37 (Linux; U; Android 11) gzip")
    conn.setRequestProperty("X-YouTube-Client-Name", "3")
    conn.setRequestProperty("X-YouTube-Client-Version", "19.09.37")
    local body = '{"videoId":"' .. id .. '","contentCheckOk":true,"racyCheckOk":true,"context":{"client":{"clientName":"ANDROID","clientVersion":"19.09.37","androidSdkVersion":30,"hl":"en","gl":"US"}}}'
    local w = OutputStreamWriter(conn.getOutputStream(), "UTF-8")
    w.write(body)
    w.flush()
    w.close()
    if conn.getResponseCode() ~= 200 then return nil end
    local text = readStream(conn, 4000000)
    pcall(function() conn.disconnect() end)
    local obj = JSONObject(text)
    local sd = obj.optJSONObject("streamingData")
    if sd == nil then return nil end
    local hls = tostring(sd.optString("hlsManifestUrl", ""))
    if hls ~= "" then return hls end
    local formats = sd.optJSONArray("formats")
    if formats ~= nil then
        local best = nil
        for i = 0, formats.length() - 1 do
            local f = formats.optJSONObject(i)
            local u = f and tostring(f.optString("url", "")) or ""
            if u ~= "" then best = u end
        end
        if best then return best end
    end
    return nil
end

local function resolveYouTube(url)
    local id = ytVideoId(url)
    if not id then
        local u = url
        local lu = u:lower()
        if not lu:find("/live") and not lu:find("/streams") and (lu:find("/channel/") or lu:find("/@") or lu:find("/c/") or lu:find("/user/")) then
            u = (u:gsub("/+$", "")) .. "/live"
        end
        local ok1, hls, vid = pcall(ytFromPage, u)
        if ok1 and hls then return hls end
        id = ok1 and vid or nil
        if not id then return nil end
    end
    local ok2, r = pcall(ytInnertube, id)
    if ok2 and r then return r end
    local ok3, hls2 = pcall(ytFromPage, "https://www.youtube.com/watch?v=" .. id)
    if ok3 and hls2 then return hls2 end
    return nil
end

local function absoluteUrl(u, base)
    if u:find("^https?://") then return u end
    if u:sub(1, 2) == "//" then return "https:" .. u end
    local origin = base:match("^(https?://[^/]+)") or ""
    if u:sub(1, 1) == "/" then return origin .. u end
    return (base:gsub("[?#].*$", ""):gsub("[^/]*$", "")) .. u
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
--   mode "external" = hand over to another app, "page" = web page with no stream found
local resolveInner
resolveInner = function(url, depth)
    local lower = url:lower()
    if isYouTube(lower) then
        local u = resolveYouTube(url)
        if u then return u, nil, nil end
        return url, "external", nil
    end
    if lower:find("^rtsp://") then return url, nil, nil end
    if not lower:find("^https?://") then return url, "external", nil end
    local final, html = probeStream(url, 12000)
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
local function resolveStream(url)
    local clean = extractLink(url)
    if clean then url = clean end
    local ok, playUrl, mode, referer = pcall(resolveInner, url, 0)
    if ok and playUrl then return playUrl, mode, referer end
    return url, nil, nil
end

----------------------------------------------------------------
-- Player control
----------------------------------------------------------------
local function stopInternalPlayback()
    pcall(function()
        if videoView ~= nil then videoView.stopPlayback() end
        if audioPlayer ~= nil then audioPlayer.reset() end
    end)
end

local function launchExternal(url, title, noType)
    runOnMain(function()
        local ok, err = pcall(function()
            stopInternalPlayback()
            local intent = Intent(Intent.ACTION_VIEW)
            if noType or isYouTube(url:lower()) then
                intent.setData(Uri.parse(url))
            else
                intent.setDataAndType(Uri.parse(url), "video/*")
            end
            intent.putExtra("title", tostring(title or ""))
            intent.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK)
            local chooser = Intent.createChooser(intent, "Open with")
            chooser.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK)
            service.startActivity(chooser)
        end)
        if not ok then
            say("No external player found. Please install VLC or MX Player.")
        end
    end)
end

closePlayer = function(afterAction)
    runOnMain(function()
        pcall(function()
            cancelSleepTimer()
            sleepIdx = 1
            playToken = playToken + 1
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
                statusText = nil
                subText = nil
                playPauseBtn = nil
                favBtn = nil
                modeBtn = nil
                sleepBtn = nil
                say("Player closed")
            end
            if afterAction == "list" and lastListFn ~= nil then
                lastListFn()
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
            if not ok and #lk >= 5 and other.lk and #other.lk >= 5 then
                ok = other.lk:find(lk, 1, true) ~= nil or lk:find(other.lk, 1, true) ~= nil
            end
            if ok then
                for _, u in ipairs(other.urls) do
                    if not have[u] then
                        have[u] = true
                        table.insert(channel.urls, u)
                        added = added + 1
                    end
                end
            end
        end
    end
    return added
end

local function handleStreamFailure()
    if playerLayout == nil then return end
    if failureToken == playToken then return end
    failureToken = playToken
    local channel = currentChannels[currentIndex]
    if channel and channel.urls and currentUrlIndex < #channel.urls then
        currentUrlIndex = currentUrlIndex + 1
        say("Source failed, trying source " .. currentUrlIndex .. " of " .. #channel.urls)
        playCurrentStream()
        return
    end
    if channel and not channel.extended then
        local added = extendMirrors(channel)
        if added > 0 then
            currentUrlIndex = currentUrlIndex + 1
            say("Trying " .. added .. " alternative sources")
            playCurrentStream()
            return
        end
    end
    if channel and prefs.getBoolean("external_fallback", true) then
        say("This channel could not play in the built-in player. Opening external player")
        launchExternal(channel.urls[currentUrlIndex] or channel.url, channel.name)
        return
    end
    local autoSwitch = prefs.getBoolean("auto_switch", true)
    if autoSwitch and currentIndex < #currentChannels then
        say("All mirrors failed, switching to next channel")
        currentIndex = currentIndex + 1
        currentUrlIndex = 1
        playCurrentStream()
    else
        say("This channel is currently offline on all sources")
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
                handleStreamFailure()
            end
        end
    }
    mainHandler.postDelayed(watchdog, ms)
end

local function startPlayback(playUrl, channel, myToken, referer)
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
        armWatchdog(myToken)

        if audioOnly then
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
                    if playPauseBtn ~= nil then
                        playPauseBtn.setText("Pause")
                        playPauseBtn.setContentDescription("Pause")
                    end
                    sayDetail("Audio streaming started")
                end
            })
            audioPlayer.setOnErrorListener(MediaPlayer.OnErrorListener{
                onError = function(mp, what, extra)
                    handleStreamFailure()
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
            if videoView ~= nil then
                videoView.setVisibility(View.VISIBLE)
                videoView.stopPlayback()
                videoView.setVideoURI(Uri.parse(playUrl), headers)
                videoView.requestFocus()
                videoView.start()
            end
            if playPauseBtn ~= nil then
                playPauseBtn.setText("Pause")
                playPauseBtn.setContentDescription("Pause")
            end
        end
    end)
    if not ok then
        handleStreamFailure()
    end
end

playCurrentStream = function()
    local channel = currentChannels[currentIndex]
    if not channel then return end
    local activeUrl = channel.urls[currentUrlIndex] or channel.url
    local audioOnly = prefs.getBoolean("audio_only", false)
    playToken = playToken + 1
    local myToken = playToken

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
            sayDetail("Buffering " .. channel.name .. mirrorInfo)
            stopInternalPlayback()
        end)
        Thread(Runnable{
            run = function()
                local playUrl, mode, referer = resolveStream(activeUrl)
                if playUrl == nil then playUrl = activeUrl end
                runOnMain(function()
                    if myToken ~= playToken then return end
                    if mode == "page" then
                        say("No live stream found on this web page. Opening it in the browser")
                        launchExternal(activeUrl, channel.name, true)
                        return
                    end
                    if mode == "external" then
                        say("Opening in external player")
                        launchExternal(activeUrl, channel.name)
                        return
                    end
                    startPlayback(playUrl, channel, myToken, referer)
                end)
            end
        }).start()
    end)
end

local function startPlayIndex(index)
    if #currentChannels == 0 then return end
    if index < 1 then
        index = #currentChannels
    elseif index > #currentChannels then
        index = 1
    end
    currentIndex = index
    currentUrlIndex = 1
    playCurrentStream()
end

local function togglePlayPause()
    pcall(function()
        if prefs.getBoolean("audio_only", false) then
            if audioPlayer ~= nil then
                if audioPlayer.isPlaying() then
                    audioPlayer.pause()
                    playPauseBtn.setText("Play")
                    playPauseBtn.setContentDescription("Play")
                    say("Paused")
                else
                    audioPlayer.start()
                    playPauseBtn.setText("Pause")
                    playPauseBtn.setContentDescription("Pause")
                    say("Playing")
                end
            end
        else
            if videoView ~= nil then
                if videoView.isPlaying() then
                    videoView.pause()
                    playPauseBtn.setText("Play")
                    playPauseBtn.setContentDescription("Play")
                    say("Paused")
                else
                    videoView.start()
                    playPauseBtn.setText("Pause")
                    playPauseBtn.setContentDescription("Pause")
                    say("Playing")
                end
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
    wmParams.width = WindowManager.LayoutParams.MATCH_PARENT
    wmParams.height = WindowManager.LayoutParams.MATCH_PARENT
    wmParams.gravity = Gravity.CENTER

    local mainLayout = LinearLayout(service)
    mainLayout.setOrientation(LinearLayout.VERTICAL)
    mainLayout.setBackgroundColor(0xFF000000)
    pcall(function() mainLayout.setKeepScreenOn(prefs.getBoolean("keep_screen", true)) end)

    -- Header: channel name + details
    local header = LinearLayout(service)
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
    local videoContainer = FrameLayout(service)
    mainLayout.addView(videoContainer, LinearLayout.LayoutParams(MATCH, 0, 1.0))
    videoView = VideoView(service)
    videoContainer.addView(videoView, FrameLayout.LayoutParams(FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.MATCH_PARENT, Gravity.CENTER))

    -- Controls
    local controls = LinearLayout(service)
    controls.setOrientation(LinearLayout.VERTICAL)
    controls.setPadding(dp(8), dp(6), dp(8), dp(10))
    controls.setBackgroundColor(C.bg)

    local btnPrev = makeButton("Previous Channel", "Previous channel", C.secondary, function()
        startPlayIndex(currentIndex - 1)
    end, 16)
    playPauseBtn = makeButton("Pause", "Pause", C.primary, togglePlayPause, 18)
    local btnNext = makeButton("Next Channel", "Next channel", C.secondary, function()
        startPlayIndex(currentIndex + 1)
    end, 16)
    makeRow(controls, { btnPrev, playPauseBtn, btnNext })

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
    local btnExt = makeButton("External Player", "Open this channel in an external player", C.secondary, function()
        local ch = currentChannels[currentIndex]
        if ch then
            launchExternal(ch.urls[currentUrlIndex] or ch.url, ch.name)
        end
    end, 16)
    makeRow(controls, { btnExt, btnList, btnClose })

    mainLayout.addView(controls)

    videoView.setOnPreparedListener(MediaPlayer.OnPreparedListener{
        onPrepared = function(mp)
            streamStarted = true
            mp.start()
            if playPauseBtn ~= nil then
                playPauseBtn.setText("Pause")
                playPauseBtn.setContentDescription("Pause")
            end
            sayDetail("Streaming started")
        end
    })
    videoView.setOnErrorListener(MediaPlayer.OnErrorListener{
        onError = function(mp, what, extra)
            handleStreamFailure()
            return true
        end
    })

    playerLayout = mainLayout
    windowManager.addView(playerLayout, wmParams)
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
            presentDialog(builder)
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
                    local idx = which + 1
                    if opts.mode == "custom" then
                        showChannelOptions(channels, idx, opts)
                    else
                        playStreamByIndex(idx)
                    end
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
            local dlg = presentDialog(builder)
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
            presentDialog(builder)
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
            dlg = presentDialog(builder, true)
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
            dlg = presentDialog(builder, true)
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
local function parseM3uSource(streamUrl, timeoutSec, defaultGroup, existingUrls, channelDict, targetCountryCode)
    local countAdded = 0
    pcall(function()
        local target = streamUrl
        local redirectCount = 0
        local conn = nil
        while redirectCount < 3 do
            local url = URL(target)
            conn = url.openConnection()
            conn.setRequestMethod("GET")
            conn.setConnectTimeout(timeoutSec)
            conn.setReadTimeout(timeoutSec)
            conn.setRequestProperty("User-Agent", "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36")
            conn.setInstanceFollowRedirects(false)
            local code = conn.getResponseCode()
            if code == 301 or code == 302 or code == 307 or code == 308 then
                local loc = conn.getHeaderField("Location")
                if loc ~= nil and loc ~= "" then
                    target = loc
                    redirectCount = redirectCount + 1
                    conn.disconnect()
                else
                    break
                end
            else
                break
            end
        end
        if conn ~= nil and conn.getResponseCode() == 200 then
            local inputStream = conn.getInputStream()
            local reader = BufferedReader(InputStreamReader(inputStream, "UTF-8"))
            local line = reader.readLine()
            local currentName = nil
            local currentRawGroup = defaultGroup or "General"
            local currentCountry = nil
            while line ~= nil do
                local str = tostring(line):match("^%s*(.-)%s*$")
                if str and str:find("^#EXTINF") then
                    local grp = str:match('group%-title="([^"]+)"')
                    if grp and grp ~= "" then
                        currentRawGroup = grp
                    else
                        currentRawGroup = defaultGroup or "General"
                    end
                    currentCountry = str:match('tvg%-country="([^"]+)"')
                    local name = str:match(',%s*(.-)$')
                    if not name or name == "" then
                        name = str:match('tvg%-name="([^"]+)"')
                    end
                    currentName = name or "Live Stream"
                elseif str and (str:find("^http://") or str:find("^https://")) and currentName then
                    local isAllowed = true
                    if targetCountryCode ~= nil then
                        if currentCountry == nil or currentCountry:upper() ~= targetCountryCode:upper() then
                            isAllowed = false
                        end
                    end
                    if isAllowed and not existingUrls[str] then
                        existingUrls[str] = true
                        local cleanKey = looseKey(currentName)
                        local unifiedGroup = normalizeCategory(currentRawGroup, currentName)
                        if channelDict[cleanKey] then
                            local existingList = channelDict[cleanKey].urls
                            if str:find("^https://") and existingList[1] and existingList[1]:find("^http://") then
                                table.insert(existingList, 1, str)
                            else
                                table.insert(existingList, str)
                            end
                            countAdded = countAdded + 1
                        else
                            countAdded = countAdded + 1
                            local item = {
                                name = currentName,
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
                    end
                    currentName = nil
                    currentRawGroup = defaultGroup or "General"
                    currentCountry = nil
                end
                line = reader.readLine()
            end
            reader.close()
            conn.disconnect()
        end
    end)
    return countAdded
end

fetchChannelsForCountry = function(country)
    if isLoading then
        service.speak("Already loading, please wait")
        return
    end
    isLoading = true
    selectedCountry = country
    service.speak("Loading " .. country.name .. " channels from all sources, please wait")
    local timeoutSec = prefs.getInt("timeout_sec", 15) * 1000
    Thread(Runnable{
        run = function()
            local ok, err = pcall(function()
                allChannels = {}
                categoryMap = {}
                activeCategoryList = {}
                source1Count = 0
                source2Count = 0
                source3Count = 0
                local existingUrls = {}
                local channelDict = {}

                local code = country.code
                local slug = country.name:lower():gsub(" ", "_")
                local gh = "https://raw.githubusercontent.com/iptv-org/iptv/"
                local sources = {}
                local function addSource(url, group, filter, bucket)
                    table.insert(sources, { url = url, group = group, filter = filter, bucket = bucket })
                end
                -- bucket 1 = country lists, 2 = language lists, 3 = extra sources
                addSource(gh .. "gh-pages/countries/" .. code .. ".m3u", "General", nil, 1)
                addSource("https://iptv-org.github.io/iptv/countries/" .. code .. ".m3u", "General", nil, 1)
                addSource(gh .. "gh-pages/languages/" .. country.lang .. ".m3u", "Regional / Language", nil, 2)
                for _, l in ipairs(country.extraLangs or {}) do
                    addSource(gh .. "gh-pages/languages/" .. l .. ".m3u", "Regional / Language", nil, 2)
                end
                addSource("https://raw.githubusercontent.com/Free-TV/IPTV/master/playlists/playlist_" .. slug .. ".m3u8", "Free TV", nil, 3)
                addSource("https://raw.githubusercontent.com/Free-TV/IPTV/master/playlists/playlist_asia.m3u8", "Free TV Asia", code, 3)
                addSource(gh .. "master/streams/" .. code .. ".m3u", "Master Streams", nil, 3)

                for _, src in ipairs(sources) do
                    local n = parseM3uSource(src.url, timeoutSec, src.group, existingUrls, channelDict, src.filter)
                    if src.bucket == 1 then
                        source1Count = source1Count + n
                    elseif src.bucket == 2 then
                        source2Count = source2Count + n
                    else
                        source3Count = source3Count + n
                    end
                end

                local orderedCategories = { "News", "Entertainment", "Movies", "Kids & Cartoons", "Islamic", "Religious", "Sports", "Other" }
                for _, cat in ipairs(orderedCategories) do
                    if categoryMap[cat] and #categoryMap[cat] > 0 then
                        table.insert(activeCategoryList, cat)
                    end
                end
            end)
            isLoading = false
            if not ok then
                showErrorDialog("Load Error: " .. tostring(err))
            end
            runOnMain(function()
                if #allChannels == 0 then
                    service.speak("No online channels found for " .. country.name .. ". You can still use favorites and custom channels.")
                else
                    service.speak(#allChannels .. " channels loaded for " .. country.name)
                end
            end)
            showHome()
        end
    }).start()
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
                    fetchChannelsForCountry(countries[which + 1])
                end
            })
            builder.setNegativeButton("Back", {
                onClick = function() showHome() end
            })
            presentDialog(builder)
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
            local isExternal = prefs.getBoolean("external_fallback", true)
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

            add("Audio Only Mode: " .. onOff(isAudioOnly), toggle("audio_only", isAudioOnly, "Audio only mode"))
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
                    presentDialog(subBuilder)
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
            add("Keep Screen On While Playing: " .. onOff(isKeepScreen), toggle("keep_screen", isKeepScreen, "Keep screen on"))
            add("Open External Player If Channel Fails: " .. onOff(isExternal), toggle("external_fallback", isExternal, "External player fallback"))
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
            add("Reset Settings to Default", function()
                confirmDialog("Reset Settings", "Reset all settings to their default values? Favorites and custom channels will be kept.", function()
                    local e = prefs.edit()
                    e.remove("audio_only")
                    e.remove("auto_switch")
                    e.remove("timeout_sec")
                    e.remove("speech")
                    e.remove("verbose")
                    e.remove("keep_screen")
                    e.remove("external_fallback")
                    e.apply()
                    service.speak("Settings reset")
                    showSettings()
                end)
            end)
            add("Help and About", function()
                infoDialog("Help and About",
                    "Live TV for Commentary Screen Reader.\n\n" ..
                    "Home: browse channels by category, open favorites, manage custom channels, search or change country.\n\n" ..
                    "Favorites: while playing press Add to Favorites, or long press a channel in any list.\n\n" ..
                    "Custom channels: add any link (stream, m3u8, radio, YouTube live or a web page that has a live stream), type it or paste it. Extra text around the link is removed automatically. Then save. Open a saved channel to play, edit or delete it.\n\n" ..
                    "If a channel cannot play in the built-in player, it is resolved (redirects, playlists, YouTube) and then handed to an external player such as VLC if enabled in settings.\n\n" ..
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
            presentDialog(builder)
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
            if #allChannels > 0 then
                status = selectedCountry.name .. ": " .. #allChannels .. " channels available"
            elseif isLoading then
                status = selectedCountry.name .. ": loading channels, please wait"
            else
                status = selectedCountry.name .. ": no online channels loaded"
            end
            addTo(col, makeLabel(status, 16, C.sub), 4)

            local dlg
            local function go(fn)
                return function()
                    pcall(function() dlg.dismiss() end)
                    homeDialog = nil
                    fn()
                end
            end

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

            addTo(col, makeButton("Browse by Category", "Browse channels by category", C.secondary, go(showCategoryMenu)), 12)
            addTo(col, makeButton("Favorites (" .. #favorites .. ")", "Favorites, " .. #favorites .. " channels", C.gold, go(showFavorites)), 12)
            addTo(col, makeButton("My Custom Channels (" .. #customChannels .. ")", "My custom channels, " .. #customChannels .. " saved", C.secondary, go(showCustomList)), 12)
            addTo(col, makeButton("Add Custom Channel", "Add a new custom channel link", C.success, go(function() showCustomForm(nil) end)), 12)
            addTo(col, makeButton("Search Channels", "Search channels by name", C.secondary, go(showSearch)), 12)
            addTo(col, makeButton("Change Country", "Change country, currently " .. selectedCountry.name, C.secondary, go(showCountryDialog)), 12)
            addTo(col, makeButton("Settings", "Settings", C.secondary, go(showSettings)), 12)
            addTo(col, makeButton("Exit", "Exit Live TV", C.danger, go(function()
                say("Live TV closed")
            end)), 12)

            -- the favorites button text is dark on gold
            local builder = AlertDialog.Builder(service)
            builder.setCustomTitle(makeTitle("Live TV"))
            builder.setView(scroll)
            dlg = presentDialog(builder, true)
            homeDialog = dlg
        end)
        if not ok then showErrorDialog("Home Error: " .. tostring(err)) end
    end)
end

----------------------------------------------------------------
-- Start
----------------------------------------------------------------
local function initLiveTV()
    favorites = loadList("favorites_v1")
    customChannels = loadList("custom_v1")
    local defaultIndex = prefs.getInt("last_country_index", 0)
    if defaultIndex < 0 or defaultIndex >= #countries then
        defaultIndex = 0
    end
    fetchChannelsForCountry(countries[defaultIndex + 1])
end

local ok, initErr = pcall(initLiveTV)
if not ok then
    showErrorDialog("Init Error: " .. tostring(initErr))
    pcall(showHome)
end
