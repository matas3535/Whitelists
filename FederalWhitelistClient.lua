local domain = "http://51.89.166.88/wl3/"
local SCRIPT_ID = 3
--[[
        One-time link generation equation function - written by fed
     x ∈ R, 62 ≤ x : f(x-62) = x^2 + 16x + 31313 + [(x % 3)^2 + (x % 7)^2] * x
                        validated on server
]]
local function Equate(x)
	x = x + 62
	return ((x ^ 2) + (16 * x) + 31313 + ((((x % 3) ^ 2) + ((x % 7) ^ 2)) * x)) % 99999999999999
end
local RndClass = {}
RndClass.__index = RndClass

local function mathfloor(n)
	return n - n % 1
end

local function NormalizeNumber(num)
	return num % 0x80000000
end

local function RandomizeSeed(seed, object)
	object[2] = object[4]
	object[5] = NormalizeNumber(seed)

	return object
end

local function CopyTable(Table)
	local clone = {}

	for i, v in pairs(Table) do
		clone[i] = v
	end

	return clone
end

function RndClass:NextNumber(floor, ceil)
	local rand1, rand2 = self[3], self[1] * self[5] + self[2]
	local rand3 = rand2 % rand1 + self[6]
	self[6] = self[6] + 1

	self[5] = rand3
	self[2] = mathfloor(rand2 / rand1)

	if not floor then
		return rand3 / 99999999
	elseif not ceil then
		if floor == 0 then
			return rand3
		else
			return 1 + rand3 % floor
		end
	else
		return floor + rand3 % ceil - floor + 1
	end
end

function RndClass:NextInteger(floor, ceil)
	return mathfloor(self:NextNumber(floor, ceil))
end

local Random = {}

function Random.Generate(seed)
	local object = setmetatable({}, RndClass)

	object[1], object[2], object[3] = 1103515245, 12345, 99999999
	object[4] = object[2]
	object = RandomizeSeed(seed, object)
	object[6] = 1

	return object
end

local rnd_seed = #game:GetService("Workspace"):GetChildren()

local function UpdateSeed()
	for i, v in pairs(game:GetService("Players"):GetChildren()) do
		rnd_seed = rnd_seed + #v.Name + v.UserId
		pcall(
			function()
				rnd_seed =
					rnd_seed +
					(mathfloor((v[CONS1].Head.Position.x * 1000) % 10000 + 2) *
						mathfloor((v[CONS1].HumanoidRootPart.Position.x * 10000 + 2) % 100000))
			end
		)
		rnd_seed = rnd_seed % 10000000
	end
end
UpdateSeed()
local MAIN_RANDOM = Random.Generate(rnd_seed + (os.clock() * 100))

local ActionOpcodes = {
	["Bans"] = {
		["TamperingDetected"] = 0x0A0A,
		["RandomHookingDetected"] = 0x0B0B,
		["HttpLoggingDetected"] = 0x0CC,
		["EQHookDetected"] = 0x0DF,
		["Undefined"] = 0xAAC
	},
	["Auth"] = {
		["SeedHandshake"] = 0xEFE,
		["AuthHandshake"] = 0xEAF
	},
	["Ack"] = {
		["Success"] = 0xB1B,
		["ErrorOccured"] = 0xB0C,
		["Unauthorized"] = 0xBED
	}
}

local function httpget(url)
	local a = {Method = "GET", Url = url}

	local resp = (syn and syn.request(a) or http and http.request(a)).Body
	if string.byte(resp:sub(1,1)) == 239 then
   return resp:sub(4,#resp)
   else
       return resp
       
       end
end
local WLAPI = {}
WLAPI = {
	["GenerateAuthLink"] = function(opcode)
		local maineq, secondeq, thirdeq, opcodeEquator = 1, 2, 3, 4
		for i = 1, 5 do
			maineq = maineq + MAIN_RANDOM:NextInteger(11111, 99999)
			secondeq = secondeq + MAIN_RANDOM:NextInteger(11111, 99999)
			thirdeq = thirdeq + MAIN_RANDOM:NextInteger(11111, 99999)
			opcodeEquator = opcodeEquator + MAIN_RANDOM:NextInteger(11111, 99999)
		end

		local hashedMain, hashedSecond, hashedThird, hashedOpcode =
			Equate(maineq),
			Equate(secondeq),
			Equate(thirdeq),
			Equate(opcodeEquator + opcode)

		local expectedResult = hashedThird .. hashedSecond .. hashedMain

		return domain ..
			"api.php?sid=" ..
				SCRIPT_ID ..
					"&a=" ..
						maineq ..
							"&b=" ..
								expectedResult .. "&c=" .. opcodeEquator .. "&d=" .. secondeq .. "&e=" .. hashedOpcode .. "&f=" .. thirdeq
	end,
	["Ban"] = function(reason)
		if not reason then
			reason = ActionOpcodes.Bans.Undefined
		end
		return httpget(WLAPI.GenerateAuthLink(reason))
	end,
	["PerformHandshake"] = function()
		return httpget(WLAPI.GenerateAuthLink(ActionOpcodes.Auth.SeedHandshake))
	end,
	["Authenticate"] = function(keys, hashvals)
		return httpget(
			WLAPI.GenerateAuthLink(ActionOpcodes.Auth.AuthHandshake) ..
				"&g=" ..
					keys[1] ..
						"&h=" ..
							hashvals[2] ..
								"&i=" .. keys[3] .. "&j=" .. hashvals[1] .. "&k=" .. keys[2] .. "&l=" .. keys[4] .. "&m=" .. hashvals[3]
		)
	end
}

local function CrackAttemptDetected(reason)
	WLAPI.Ban(ActionOpcodes.Bans[reason])
	local sep = (rconsoleprint or print)("Get cummed on nerd ROFL - Federal REASON: ")
	wait(5)
	while true do
	end
end

local charDict = {}
for i = 0, 255 do
	charDict[i] = string.char(i)
	charDict[charDict[i]] = i
end

-- Skid baiter 3000
local combo, prev, rnewidx = 0, 0, 0
for i = 1, 50 do
	local n = math.random(10000, 99999)
	if i == 31 then
		rnewidx = n
	end
	if n == prev then
		combo = combo + 1
	end
	prev = n
end

if combo > 45 then
	CrackAttemptDetected("RandomHookingDetected")
end

local iscclosure =
	islclosure or is_l_closure or debug and debug.islclosure or debug and debug.is_l_closure or function()
		print("EXECUTOR NOT SUPPORTED [0x01]")
		while true do
			wait()
		end
	end
local checks = {
	math.random,
	os.clock,
	string.char,
	string.byte,
	pcall,
	setfenv,
	iscclosure,
	loadstring,
	math.floor,
	string.sub
}
for i = 1, #checks do
	if (iscclosure(checks[i])) or (pcall(setfenv, checks[i], {})) then
		CrackAttemptDetected("TamperingDetected")
	end
end
UpdateSeed()
rnd_seed = rnd_seed + rnewidx
MAIN_RANDOM = Random.Generate(rnd_seed + MAIN_RANDOM:NextInteger(1111, 9999))

-- AUTHENTICATION --
print("Authentication Started")
local RESPONSE_RECEIVED, passed = false, 0
spawn(
	function()
		while RESPONSE_RECEIVED == false do
			wait()
			passed = passed + 1
		end
	end
)

local handshakeResp = WLAPI.PerformHandshake()
RESPONSE_RECEIVED = true
if (passed < 3) then -- responds too fast (never happens unless its autorespond)
--CrackAttemptDetected("HttpLoggingDetected")
end
print(handshakeResp)
if handshakeResp == "USER_AUTHORIZED" then -- just a pre-check, not the main check obviously
	print("Handshake success.. Authenticating..")
elseif handshakeResp == "IP_BANNED" then
	print("You're banned from using this script. Contact the script developer")
	return
else
	print("You're not whitelisted, contact the script developer")
	return
end

combo, prev, rnewidx = 0, 0, 0
for i = 1, 50 do
	local n = math.random(10000, 99999)
	if i == 25 then
		rnewidx = n
	end
	if n == prev then
		combo = combo + 1
	end
	prev = n
end

if combo > 45 then
	CrackAttemptDetected("RandomHookingDetected")
end

UpdateSeed()
rnd_seed = rnd_seed + rnewidx + passed
MAIN_RANDOM = Random.Generate(rnd_seed)

local decryptionKeys = {
	MAIN_RANDOM:NextInteger(11111, 99999),
	MAIN_RANDOM:NextInteger(11111, 99999),
	MAIN_RANDOM:NextInteger(11111, 99999),
	MAIN_RANDOM:NextInteger(11111, 99999)
}
local hashKeys = {
	MAIN_RANDOM:NextInteger(11111, 99999),
	MAIN_RANDOM:NextInteger(11111, 99999),
	MAIN_RANDOM:NextInteger(11111, 99999)
}

local expectedMain = Equate(hashKeys[1]) .. Equate(hashKeys[3]) .. Equate(hashKeys[2])
local serverResp = WLAPI.Authenticate(decryptionKeys, hashKeys)
decryptionKeys = {
	[0] = decryptionKeys[1] % 256,
	[1] = decryptionKeys[2] % 256,
	[2] = decryptionKeys[3] % 256,
	[3] = decryptionKeys[4] % 256
}
local CONS1, CONS2, CONS3 = "", "", ""

local charset = "asdfghjklmnoprty"
local charset_hexified = {}
for i = 0, 15 do
	charset_hexified[charset:sub(i + 1, i + 1)] = i
end

local respHash = ""
local respConstants = ""
local cStat = 0
local cChar = ""
for i = 1, #serverResp do
	cChar = serverResp:sub(i, i)
	if cChar == "/" then
		cStat = cStat + 1
	else
		if cStat == 0 then
			respHash = respHash .. cChar
		end
		if cStat == 1 then
			respConstants = respConstants .. cChar
		end
	end
end

cChar = ""
cStat = 0
for i = 1, #respConstants / 2 do
	local f, s =
		charset_hexified[respConstants:sub(i * 2 - 1, i * 2 - 1)],
		charset_hexified[respConstants:sub(i * 2, i * 2)]
	local byte = f * 16 + s + 2048 - decryptionKeys[(i - 1) % 4]
	byte = charDict[byte % 256]
	if byte == ";" then
		cStat = cStat + 1
	else
		if cStat == 0 then
			CONS1 = CONS1 .. byte
		elseif cStat == 1 then
			CONS2 = CONS2 .. byte
		elseif cStat == 2 then
			CONS3 = CONS3 .. byte
		end
	end
end

local MAINCODE =
	setmetatable(
	{
		[expectedMain] = function(...)
            -- ur code here I think i dont know dont quote me on that luh bro
        end
	},
	{
		__index = function(s, idx)
			if idx ~= expectedMain then
				return (function()
					CrackAttemptDetected("EQHookDetected")
					return function()
						while true do
						end
					end
				end)()
			end
			return s[idx]
		end
	}
)

return MAINCODE[respHash](...)
