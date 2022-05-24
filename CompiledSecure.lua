if rconsolecreate then
	rconsolecreate()
end

local LocalPlayer = game.GetService(game, "Players").LocalPlayer

local scriptKey = scriptKey or ""
getgenv().scriptKey = scriptKey or ""
local websiteKey = websiteKey or ""
getgenv().websiteKey = websiteKey or ""

if scriptKey == "" then
	LocalPlayer:Kick("No ScriptKey Found (stop it kthx)")
	wait(.25)
	while true do end
	return
end

if getgenv().scriptKey == "" then
	LocalPlayer:Kick("No ScriptKey Found (stop it kthx)")
	wait(.25)
	while true do end
	return
end

if websiteKey == "" then
	LocalPlayer:Kick("No websiteKey Found (stop it kthx)")
	wait(.25)
	while true do end
	return
end

if getgenv().websiteKey == "" then
	LocalPlayer:Kick("No websiteKey Found (stop it kthx)")
	wait(.25)
	while true do end
	return
end

if pebc_execute then
	-- why, Linux?
end

if is_synapse_function(type) or is_synapse_function(typeof) then
	return (function()
		while true do end
	end)()
elseif islclosure(type) or islclosure(typeof) then
	return (function()
		while true do end
	end)()
end

local AuthTime = tick()
--// HMAC functions\\--
local hmac

do
    local unpack, table_concat, byte, char, string_rep, sub, string_format, floor, ceil, min, max =
        table.unpack or unpack,
        table.concat,
        string.byte,
        string.char,
        string.rep,
        string.sub,
        string.format,
        math.floor,
        math.ceil,
        math.min,
        math.max
    shared.unpack = unpack
    local AND, OR, XOR, SHL, SHR, ROL, ROR, HEX
    local function SHL(x, n)
        return (x * 2 ^ n) % 4294967296
    end

    local function SHR(x, n)
        x = x % 4294967296 / 2 ^ n
        return x - x % 1
    end

    local function ROL(x, n)
        x = x % 4294967296 * 2 ^ n
        local r = x % 4294967296
        return r + (x - r) / 4294967296
    end

    local function ROR(x, n)
        x = x % 4294967296 / 2 ^ n
        local r = x % 1
        return r * 4294967296 + (x - r)
    end

    local AND_of_two_bytes = {}
    for idx = 0, 65535 do
        local x = idx % 256
        local y = (idx - x) / 256
        local res = 0
        local w = 1
        while x * y ~= 0 do
            local rx = x % 2
            local ry = y % 2
            res = res + rx * ry * w
            x = (x - rx) / 2
            y = (y - ry) / 2
            w = w * 2
        end
        AND_of_two_bytes[idx] = res
    end

    local function and_or_xor(x, y, operation)
        local x0 = x % 4294967296
        local y0 = y % 4294967296
        local rx = x0 % 256
        local ry = y0 % 256
        local res = AND_of_two_bytes[rx + ry * 256]
        x = x0 - rx
        y = (y0 - ry) / 256
        rx = x % 65536
        ry = y % 256
        res = res + AND_of_two_bytes[rx + ry] * 256
        x = (x - rx) / 256
        y = (y - ry) / 256
        rx = x % 65536 + y % 256
        res = res + AND_of_two_bytes[rx] * 65536
        res = res + AND_of_two_bytes[(x + y - rx) / 256] * 16777216
        if operation then
            res = x0 + y0 - operation * res
        end
        return res
    end

    local function AND(x, y)
        return and_or_xor(x, y)
    end

    local function OR(x, y)
        return and_or_xor(x, y, 1)
    end

    local function XOR(x, y, z)
        if z then
            y = and_or_xor(y, z, 2)
        end
        return and_or_xor(x, y, 2)
    end

    local function HEX(x)
        return string_format("%08x", x % 4294967296)
    end
    local sha2_K_lo, sha2_K_hi, sha2_H_lo, sha2_H_hi = {}, {}, {}, {}
    local sha2_H_ext256 = {
        [224] = {},
        [256] = sha2_H_hi
    }
    local sha2_H_ext512_lo, sha2_H_ext512_hi = {
            [384] = {},
            [512] = sha2_H_lo
        },
        {
            [384] = {},
            [512] = sha2_H_hi
        }

    local common_W = {} -- a temporary table shared between all calculations

    local function sha256_feed_64(H, K, str, W, offs, size)
        -- offs >= 0, size >= 0, size is multiple of 64
        for pos = offs, size + offs - 1, 64 do
            for j = 1, 16 do
                pos = pos + 4
                local a, b, c, d = byte(str, pos - 3, pos)
                W[j] = ((a * 256 + b) * 256 + c) * 256 + d
            end
            for j = 17, 64 do
                local a, b = W[j - 15], W[j - 2]
                W[j] =
                    XOR(ROR(a, 7), ROL(a, 14), SHR(a, 3)) + XOR(ROL(b, 15), ROL(b, 13), SHR(b, 10)) + W[j - 7] +
                    W[j - 16]
            end
            local a, b, c, d, e, f, g, h, z = H[1], H[2], H[3], H[4], H[5], H[6], H[7], H[8]
            for j = 1, 64 do
                z = XOR(ROR(e, 6), ROR(e, 11), ROL(e, 7)) + AND(e, f) + AND(-1 - e, g) + h + K[j] + W[j]
                h = g
                g = f
                f = e
                e = z + d
                d = c
                c = b
                b = a
                a = z + AND(d, c) + AND(a, XOR(d, c)) + XOR(ROR(a, 2), ROR(a, 13), ROL(a, 10))
            end
            H[1], H[2], H[3], H[4] =
                (a + H[1]) % 4294967296,
                (b + H[2]) % 4294967296,
                (c + H[3]) % 4294967296,
                (d + H[4]) % 4294967296
            H[5], H[6], H[7], H[8] =
                (e + H[5]) % 4294967296,
                (f + H[6]) % 4294967296,
                (g + H[7]) % 4294967296,
                (h + H[8]) % 4294967296
        end
    end

    local function sha512_feed_128(H_lo, H_hi, K_lo, K_hi, str, W, offs, size)
        -- offs >= 0, size >= 0, size is multiple of 128
        -- W1_hi, W1_lo, W2_hi, W2_lo, ...   Wk_hi = W[2*k-1], Wk_lo = W[2*k]
        for pos = offs, size + offs - 1, 128 do
            for j = 1, 32 do
                pos = pos + 4
                local a, b, c, d = byte(str, pos - 3, pos)
                W[j] = ((a * 256 + b) * 256 + c) * 256 + d
            end
            local tmp1, tmp2
            for jj = 17 * 2, 80 * 2, 2 do
                local a_lo, a_hi, b_lo, b_hi = W[jj - 30], W[jj - 31], W[jj - 4], W[jj - 5]
                tmp1 =
                    XOR(SHR(a_lo, 1) + SHL(a_hi, 31), SHR(a_lo, 8) + SHL(a_hi, 24), SHR(a_lo, 7) + SHL(a_hi, 25)) +
                    XOR(SHR(b_lo, 19) + SHL(b_hi, 13), SHL(b_lo, 3) + SHR(b_hi, 29), SHR(b_lo, 6) + SHL(b_hi, 26)) +
                    W[jj - 14] +
                    W[jj - 32]
                tmp2 = tmp1 % 4294967296
                W[jj - 1] =
                    XOR(SHR(a_hi, 1) + SHL(a_lo, 31), SHR(a_hi, 8) + SHL(a_lo, 24), SHR(a_hi, 7)) +
                    XOR(SHR(b_hi, 19) + SHL(b_lo, 13), SHL(b_hi, 3) + SHR(b_lo, 29), SHR(b_hi, 6)) +
                    W[jj - 15] +
                    W[jj - 33] +
                    (tmp1 - tmp2) / 4294967296
                W[jj] = tmp2
            end
            local a_lo, b_lo, c_lo, d_lo, e_lo, f_lo, g_lo, h_lo, z_lo =
                H_lo[1],
                H_lo[2],
                H_lo[3],
                H_lo[4],
                H_lo[5],
                H_lo[6],
                H_lo[7],
                H_lo[8]
            local a_hi, b_hi, c_hi, d_hi, e_hi, f_hi, g_hi, h_hi, z_hi =
                H_hi[1],
                H_hi[2],
                H_hi[3],
                H_hi[4],
                H_hi[5],
                H_hi[6],
                H_hi[7],
                H_hi[8]
            for j = 1, 80 do
                local jj = 2 * j
                tmp1 =
                    XOR(SHR(e_lo, 14) + SHL(e_hi, 18), SHR(e_lo, 18) + SHL(e_hi, 14), SHL(e_lo, 23) + SHR(e_hi, 9)) +
                    AND(e_lo, f_lo) +
                    AND(-1 - e_lo, g_lo) +
                    h_lo +
                    K_lo[j] +
                    W[jj]
                z_lo = tmp1 % 4294967296
                z_hi =
                    XOR(SHR(e_hi, 14) + SHL(e_lo, 18), SHR(e_hi, 18) + SHL(e_lo, 14), SHL(e_hi, 23) + SHR(e_lo, 9)) +
                    AND(e_hi, f_hi) +
                    AND(-1 - e_hi, g_hi) +
                    h_hi +
                    K_hi[j] +
                    W[jj - 1] +
                    (tmp1 - z_lo) / 4294967296
                h_lo = g_lo
                h_hi = g_hi
                g_lo = f_lo
                g_hi = f_hi
                f_lo = e_lo
                f_hi = e_hi
                tmp1 = z_lo + d_lo
                e_lo = tmp1 % 4294967296
                e_hi = z_hi + d_hi + (tmp1 - e_lo) / 4294967296
                d_lo = c_lo
                d_hi = c_hi
                c_lo = b_lo
                c_hi = b_hi
                b_lo = a_lo
                b_hi = a_hi
                tmp1 =
                    z_lo + AND(d_lo, c_lo) + AND(b_lo, XOR(d_lo, c_lo)) +
                    XOR(SHR(b_lo, 28) + SHL(b_hi, 4), SHL(b_lo, 30) + SHR(b_hi, 2), SHL(b_lo, 25) + SHR(b_hi, 7))
                a_lo = tmp1 % 4294967296
                a_hi =
                    z_hi + (AND(d_hi, c_hi) + AND(b_hi, XOR(d_hi, c_hi))) +
                    XOR(SHR(b_hi, 28) + SHL(b_lo, 4), SHL(b_hi, 30) + SHR(b_lo, 2), SHL(b_hi, 25) + SHR(b_lo, 7)) +
                    (tmp1 - a_lo) / 4294967296
            end
            tmp1 = H_lo[1] + a_lo
            tmp2 = tmp1 % 4294967296
            H_lo[1], H_hi[1] = tmp2, (H_hi[1] + a_hi + (tmp1 - tmp2) / 4294967296) % 4294967296
            tmp1 = H_lo[2] + b_lo
            tmp2 = tmp1 % 4294967296
            H_lo[2], H_hi[2] = tmp2, (H_hi[2] + b_hi + (tmp1 - tmp2) / 4294967296) % 4294967296
            tmp1 = H_lo[3] + c_lo
            tmp2 = tmp1 % 4294967296
            H_lo[3], H_hi[3] = tmp2, (H_hi[3] + c_hi + (tmp1 - tmp2) / 4294967296) % 4294967296
            tmp1 = H_lo[4] + d_lo
            tmp2 = tmp1 % 4294967296
            H_lo[4], H_hi[4] = tmp2, (H_hi[4] + d_hi + (tmp1 - tmp2) / 4294967296) % 4294967296
            tmp1 = H_lo[5] + e_lo
            tmp2 = tmp1 % 4294967296
            H_lo[5], H_hi[5] = tmp2, (H_hi[5] + e_hi + (tmp1 - tmp2) / 4294967296) % 4294967296
            tmp1 = H_lo[6] + f_lo
            tmp2 = tmp1 % 4294967296
            H_lo[6], H_hi[6] = tmp2, (H_hi[6] + f_hi + (tmp1 - tmp2) / 4294967296) % 4294967296
            tmp1 = H_lo[7] + g_lo
            tmp2 = tmp1 % 4294967296
            H_lo[7], H_hi[7] = tmp2, (H_hi[7] + g_hi + (tmp1 - tmp2) / 4294967296) % 4294967296
            tmp1 = H_lo[8] + h_lo
            tmp2 = tmp1 % 4294967296
            H_lo[8], H_hi[8] = tmp2, (H_hi[8] + h_hi + (tmp1 - tmp2) / 4294967296) % 4294967296
        end
    end
    do
        local function mul(src1, src2, factor, result_length)
            -- Long arithmetic multiplication: src1 * src2 * factor
            -- src1, src2 - long integers (arrays of digits in base 2^24)
            -- factor - short integer
            local result = {}
            local carry = 0
            local value = 0.0
            local weight = 1.0
            for j = 1, result_length do
                local prod = 0
                for k = max(1, j + 1 - #src2), min(j, #src1) do
                    prod = prod + src1[k] * src2[j + 1 - k]
                end
                carry = carry + prod * factor
                local digit = carry % 16777216
                result[j] = digit
                carry = floor(carry / 16777216)
                value = value + digit * weight
                weight = weight * 2 ^ 24
            end
            return result, value -- long integer -- and its floating point approximation
        end

        local idx, step, p, one =
            0,
            {
                4,
                1,
                2,
                -2,
                2
            },
            4,
            {
                1
            }
        local sqrt_hi, sqrt_lo, idx_disp = sha2_H_hi, sha2_H_lo, 0
        repeat
            p = p + step[p % 6]
            local d = 1
            repeat
                d = d + step[d % 6]
                if d * d > p then
                    idx = idx + 1
                    local root = p ^ (1 / 3)
                    local R =
                        mul(
                        {
                            floor(root * 2 ^ 40)
                        },
                        one,
                        1,
                        2
                    )
                    local _, delta = mul(R, mul(R, R, 1, 4), -1, 4)
                    local hi = R[2] % 65536 * 65536 + floor(R[1] / 256)
                    local lo = R[1] % 256 * 16777216 + floor(delta * (2 ^ -56 / 3) * root / p)
                    sha2_K_hi[idx], sha2_K_lo[idx] = hi, lo
                    if idx < 17 then
                        root = p ^ (1 / 2)
                        R =
                            mul(
                            {
                                floor(root * 2 ^ 40)
                            },
                            one,
                            1,
                            2
                        )
                        _, delta = mul(R, R, -1, 2)
                        hi = R[2] % 65536 * 65536 + floor(R[1] / 256)
                        lo = R[1] % 256 * 16777216 + floor(delta * 2 ^ -17 / root)
                        sha2_H_ext256[224][idx + idx_disp] = lo
                        sqrt_hi[idx + idx_disp], sqrt_lo[idx + idx_disp] = hi, lo
                        if idx == 8 then
                            sqrt_hi, sqrt_lo, idx_disp = sha2_H_ext512_hi[384], sha2_H_ext512_lo[384], -8
                        end
                    end
                    break
                end
            until p % d == 0
        until idx > 79
    end

    -- Calculating IV for SHA512/224 and SHA512/256
    for width = 224, 256, 32 do
        local H_lo, H_hi = {}, {}
        for j = 1, 8 do
            H_lo[j] = XOR(sha2_H_lo[j], 0xa5a5a5a5)
            H_hi[j] = XOR(sha2_H_hi[j], 0xa5a5a5a5)
        end
        sha512_feed_128(
            H_lo,
            H_hi,
            sha2_K_lo,
            sha2_K_hi,
            "SHA-512/" .. tonumber(width) .. "\128" .. string_rep("\0", 115) .. "\88",
            common_W,
            0,
            128
        )
        sha2_H_ext512_lo[width] = H_lo
        sha2_H_ext512_hi[width] = H_hi
    end

    --------------------------------------------------------------------------------
    -- FINAL FUNCTIONS
    --------------------------------------------------------------------------------

    local function sha512ext(width, text)
        -- Create an instance (private objects for current calculation)
        local length, tail, H_lo, H_hi =
            0,
            "",
            {
                unpack(sha2_H_ext512_lo[width])
            },
            {
                unpack(sha2_H_ext512_hi[width])
            }

        local function partial(text_part)
            if text_part then
                if tail then
                    length = length + #text_part
                    local offs = 0
                    if tail ~= "" and #tail + #text_part >= 128 then
                        offs = 128 - #tail
                        sha512_feed_128(
                            H_lo,
                            H_hi,
                            sha2_K_lo,
                            sha2_K_hi,
                            tail .. sub(text_part, 1, offs),
                            common_W,
                            0,
                            128
                        )
                        tail = ""
                    end
                    local size = #text_part - offs
                    local size_tail = size % 128
                    sha512_feed_128(H_lo, H_hi, sha2_K_lo, sha2_K_hi, text_part, common_W, offs, size - size_tail)
                    tail = tail .. sub(text_part, #text_part + 1 - size_tail)
                    return partial
                else
                    error("Adding more chunks is not allowed after asking for final result", 2)
                end
            else
                if tail then
                    local final_blocks = {
                        tail,
                        "\128",
                        string_rep("\0", (-17 - length) % 128 + 9)
                    }
                    tail = nil
                    -- Assuming user data length is shorter than 2^53 bytes
                    -- 2^53 bytes = 2^56 bits, so "bit-counter" fits in 7 bytes
                    length = length * (8 / 256 ^ 7) -- convert "byte-counter" to "bit-counter" and move floating point to the left
                    for j = 4, 10 do
                        length = length % 1 * 256
                        final_blocks[j] = char(floor(length))
                    end
                    final_blocks = table_concat(final_blocks)
                    sha512_feed_128(H_lo, H_hi, sha2_K_lo, sha2_K_hi, final_blocks, common_W, 0, #final_blocks)
                    local max_reg = ceil(width / 64)
                    for j = 1, max_reg do
                        H_lo[j] = HEX(H_hi[j]) .. HEX(H_lo[j])
                    end
                    H_hi = nil
                    H_lo = table_concat(H_lo, "", 1, max_reg):sub(1, width / 4)
                end
                return H_lo
            end
        end

        if text then
            -- Actually perform calculations and return the SHA256 digest of a message
            return partial(text)()
        else
            -- Return function for partial chunk loading
            -- User should feed every chunks of input data as single argument to this function and receive SHA256 digest by invoking this function without an argument
            return partial
        end
    end

    function hmac(secret, data)
        return sha512ext(512, secret .. data .. secret)
    end -- Init sha library
end

function generate_order()
    math.randomseed(tick() / 4)
    local options = {}
    local new_options = {}
    while #options ~= 3 do
        local num = math.random(1, 3) 
        if not new_options[num] then
            table.insert(options, num)
            new_options[num] = true
        end
    end
    return options
end

function findindex(table, value, multi)
    if not multi then
        for i,v in next, table do 
            if v == value then 
                return i
            end
        end
    else 
        local result = {}
        while true do 
            for i,v in next, table do 
                if v == value and (not findindex(result, i)) then
                    result[i] = i
                else 
                    break
                end
            end
        end
        return result;
    end
    return nil;
end

function eq_check1(v1, v2)
    local start = tick();
    local eq_table = {values = {}, indexes = {}};
    
    local v3 = tostring(v1);
    local v4 = tostring(v2);

    for i = 10, 14 do 
        v3, v4 = v4:reverse():sub(0, v4:len()), v3:reverse():sub(0, v3:len());
        eq_table.values[i*10+math.random(math.random(1,100),math.random(1000,10000))] = v3;
        eq_table.values[i*20+math.random(math.random(1,100),math.random(1000,10000))] = v4;
    end 
    
    local stack = debug.getstack(1);
    for i,v in next, eq_table.values do 
        if not table.find(stack, v) then 
            return false;
        else 
            for i2,v2 in next, findindex(stack,v,true) do 
                eq_table.indexes[i] = v2;
                debug.setstack(1, v2, i)
            end
        end
    end
    local newstack = debug.getstack(1);
    
    return (v1 == v2) and (eq_table.values[v1] == eq_table.values[v2]) and (stack[eq_table.indexes[v1]] == stack[eq_table.indexes[v2]]);
end

local function eq_check2(v1,v2)
    math.randomseed(tick() / 4)
    local charset = "ABCDEFGHIJKLMNOPQRSTUVXYZabcdefghijklmnopqrstuvwxyz1234567890"
    if type(v1) == "string" and type(v2) == "string" then
        local length1,length2,chars_1,chars_2 = #v1,#v2,{},{}
        v1:gsub(".",function(s)chars_1[#chars_1+1]=s end)
        v2:gsub(".",function(s)chars_2[#chars_2+1]=s end)
        if (length1~=length2) then
            return false
        end
        local start = math.random(1,length1)
        local bool = true
        for i,v in pairs(generate_order()) do
            if v == 1 then
                for i=1,start do
                    local operation_type = math.random(1,4)
                    if operation_type == 1 then
                        if not not (chars_1[i] ~= chars_2[i]) then bool = false end
                    elseif operation_type == 2 then
                        if not (chars_1[i] == chars_2[i]) then bool = false end 
                    elseif operation_type == 3 then
                        if not not (chars_2[i] ~= chars_1[i]) then bool = false end
                    elseif operation_type == 4 then
                        if not (chars_2[i] == chars_1[i]) then bool = false end 
                    end
                end  
            elseif v == 2 then
                math.randomseed(tick()/2)
                for i=1,math.random(1,20) do
                    local num_1,num_2 = math.random(1,#charset),math.random(1,#charset)
                    local char_1,char_2 = charset:sub(num_1,num_1),charset:sub(num_2,num_2)
                    local operation_type = math.random(1,4)
                    if operation_type == 1 then
                        if not not (num_1 ~= num_2) then end
                    elseif operation_type == 2 then
                        if not (num_1 == num_2) then end 
                    elseif operation_type == 3 then
                        if not not (num_1 ~= num_2) then end
                    elseif operation_type == 4 then
                        if not (num_1 == num_2) then end 
                    end
                end  
            elseif v == 3 then
                for i=1,length1-start do
                    local operation_type = math.random(1,4)
                    if operation_type == 1 then
                        if not not (chars_1[i] ~= chars_2[i]) then bool = false end
                    elseif operation_type == 2 then
                        if not (chars_1[i] == chars_2[i]) then bool = false end 
                    elseif operation_type == 3 then
                        if not not (chars_2[i] ~= chars_1[i]) then bool = false end
                    elseif operation_type == 4 then
                        if not (chars_2[i] == chars_1[i]) then bool = false end 
                    end
                end
            end
        end
        return bool
    else 
        return false
    end
end

function eq(v1, v2)
    local v3 = tostring(v1);
    local v4 = tostring(v2);
    local c1 = not(v1<v2 or v1>v2);
    local c2 = (#v3 >= #v4) and (#v3 <= #v4);
    local c3 = v3:find(v4);
    --local c4 = eq_check1(v1, v2);
    local c5 = eq_check2(v1, v2);
    return function()
        if c1 and c2 and c3 and v5 then 
            return true 
        else 
            return false 
        end 
    end
end

local tweenInterrupt = false;
function tweenCheck(var)
	coroutine.wrap(function()
		local f = Instance.new("Frame");
		f.Parent = Workspace;
		f:TweenSize(UDim2.new(1 / 0, 1 / 0, 1 / 0, 1 / 0), Enum.EasingDirection.InOut, Enum.EasingStyle.Sine, 100)
		f:TweenSize(UDim2.new(0, 0, 0, 0), Enum.EasingDirection.InOut, Enum.EasingStyle.Sine, 0.1, var)
		wait(0.1)
		if f.Size.X.Scale == 1 / 0 then
			LocalPlayer:Kick("CompiledSecure: Tween Check Failure")
			wait(0.25)
			while true do end
			return
		end
	end)()
end

local chars = {}

for i = ("a"):byte(), ("z"):byte() do
    table.insert(chars, string.char(i))
end

for i = ("A"):byte(), ("Z"):byte() do
    table.insert(chars, string.char(i))
end

for i = ("0"):byte(), ("9"):byte() do
    table.insert(chars, string.char(i))
end

local function randomString(length)
    local str = ""
    for i = 1, length do
        str = str .. chars[math.random(1, #chars)]
    end
    return str
end

local function calculate_server_encryption(length)
    local str = ""
    for i = 1, length do
        str = str .. chars[math.random(1, #chars)]
    end
    return str
end

local function IsHooked(func)
    if islclosure(func) then
        return true 
    end
	local info = debug.getinfo(func)
    if info.source ~= "=[C]" or info.short_src ~= "[C]" or info.what ~= "C" then
        return true
    end
    return false
end

--//http_request for all exploits & jsondecode\\--

local getservice = game.GetService
local timezone = os.date("%Z")
local timehash = os.time()
local httpservice = getservice(game, "HttpService")

local httpreq, exploit = http_request, "N/A"
if identifyexecutor and identifyexecutor() == "ScriptWare" then
	httpreq, exploit = request, "ScriptWare"
elseif syn_decompile then
	httpreq, exploit = syn.request, "Synapse"
elseif SENTINEL_V2 then
	httpreq, exploit = request, "Sentinel"
elseif is_sirhurt_closure then
	httpreq, exploit = http_request, "Sirhurt"
elseif PROTOSMASHER_LOADED then
	httpreq, exploit = http_request, "Protosmasher"
elseif KRNL_LOADED then
	httpreq, exploit = request, "KRNL"
elseif Fluxus_Closure then
	httpreq, exploit = http_request, "Fluxus"
end

local function http_request_get(URL, Headers)
	if not httpreq or IsHooked(islclosure) or IsHooked(debug.getinfo) or IsHooked(httpreq) then
		LocalPlayer:Kick("Anti Http Request Spy")
		local flag = (http_request_get("https://compiledsecure.xyz/Api/Whitelist/flag?scriptKey=" .. scriptKey .. "&htnu=" .. Randomize))
		wait(.25)
		while true do end
	end
    return httpreq({
        Method = "GET",
        Url = URL,
        Headers = {
            Username = LocalPlayer.Name,
            Game = tostring(game.PlaceId),
            Exploit = tostring(exploit),
            timezone = tostring(timezone),
            timehash = tostring(timehash)
        }
    }).Body
end

local function jsondecode(json)
    local jsonTable = {}
    pcall(function()
        jsonTable = httpservice.JSONDecode(httpservice, json)
    end)
    return jsonTable
end

--//Start Checking Whitelist\\--

local secretKey1 = PSU_ENCRYPT_STRING("w=ezj(p{bFZt>3A%<KE2~df9jcK~#sVJn4LkpS!$6juvM^g3B}6]6WbKbEabdhggre")
local secretKey2 = PSU_ENCRYPT_STRING("f57,,PErKcAcNHs2n<T]6,2TT<NJj[/zp8+Y]nvCuuXgD{py396!!*<RQs6'Ja4}")
local secretKey3 = hmac(PSU_ENCRYPT_STRING(os.time() * 45 .. "SAJDGALKJHl7B78byVBy^vvY8VUYkl^y6LvL^&"), PSU_ENCRYPT_STRING("JHgdlGHLFDhgflGFUYGFlgfl78fGV6OFL87gf87gvf6lIHGF7Ol8hlfg7lh8fg7H89LG"))
local Random = hmac(secretKey1, randomString(32))

local serverData = (http_request_get("https://compiledsecure.xyz/Api/Whitelist/checkWhitelist?scriptKey=" .. scriptKey .. "&ghvxz=" .. Random))
local data = (http_request_get("https://compiledsecure.xyz/Api/Whitelist/check?scriptKey=" .. scriptKey .. "&bsrhs=" .. Random))
local sessioncrash = (http_request_get("https://compiledsecure.xyz/Api/Whitelist/checksessioncrash?scriptKey=" .. scriptKey .. "&ndtjz=" .. Random))

if serverData then
	if (eq_check2(serverData, "Adding users Data to database.")) then
		LocalPlayer:Kick("Your HWID Has Been Registered. Rejoin The Game")
		wait(.25)
		while true do end
		return
	elseif serverData:find("HWID Mismatch") then
		LocalPlayer:Kick("HWID Mismatch. Reset your HWID with ;resethwid in the Discord Server")
		wait(.25)
		while true do end
		return
	elseif serverData == "" then
		LocalPlayer:Kick("CompiledSecure: Fuck Off Ye")
		local flag = (http_request_get("https://compiledsecure.xyz/Api/Whitelist/flag?scriptKey=" .. scriptKey .. "&htnu=" .. Randomize))
		wait(.25)
		while true do end
		return
	end
else
    LocalPlayer:Kick("Failed to contact Whitelist Server [Step 2]")
    wait(.25)
    while true do end
    return
end

if not data or data == "" then
    LocalPlayer:Kick("Failed to contact Sanity Server [Step 3]")
    wait(.25)
    while true do end
    return
end

game:GetService("Players").PlayerRemoving:Connect(function(plr)
	if plr == LocalPlayer then
		local deletesession = (http_request_get("https://compiledsecure.xyz/Api/Whitelist/deletesession?scriptKey=" .. scriptKey .. "&ndtjz=" .. Random))
	end
end)

local predictedData = hmac(hmac(secretKey3, scriptKey), scriptKey .. Random)
local whitelisted = false
local server_constants = nil

if(eq_check2(serverData, "Invalid Key")) then
    return LocalPlayer:Kick("Invalid Key")
end

if eq(serverData, predictedData) then
    if serverData ~= predictedData then
		rconsoleprint("\n> Data Mismatch")
        return;
    end
    tweenInterrupt = true;
    whitelisted = true;
    server_constants = eq(serverData, predictedData);
else
    return LocalPlayer:Kick(serverData)
end

local session = (http_request_get("https://compiledsecure.xyz/Api/Whitelist/createession?scriptKey=" .. scriptKey .. "&ndtjz=" .. Random))

if (eq_check2(data, "sanity_failure_ResetHWID/InvalidKey/NoKey/TimezoneMismatch")) then
	LocalPlayer:Kick([[
       Error Code: Sanity
       - Hwid Mismatch
       - Invalid Key
       - No key
       - Timezone Mismatch
       - Hash mismatch

       If this issue persists please contact the Developers Of The Script
    ]])
    wait(.25)
    while true do end
    return
end

local CoreGui = game:GetService("CoreGui")
local ExcludedWords = {
    "dex",
    "remote called",
    "remote invoked",
    "decompiler",
    "remote spy",
    "remotespy",
    "fluxspy",
    "mrspyv2rebug",
    "fluxspy v2",
    "mr.spy v2 - rebug",
    "scripteditor;",
    "newguipart1",
    "contentspy",
    "Content Spy",
    "ContentSpy",
	"dajdhwqoewenfdjkwehweouhdfajsnjbakhfhd"
}
local FalsePositives = {
    "index",
    "backgroundextender",
    "redex"
}

function FalsePositiveCheck(text)
    text = text or "dajdhwqoewenfdjkwehweouhdfajsnjbakhfhd"
    for i, FalsePositive in pairs(FalsePositives) do
        if string.find(text:lower(), FalsePositive) then
            return true
        end
    end
end

function ExclusionCheck(text)   
    text = text or "dajdhwqoewenfdjkwehweouhdfajsnjbakhfhd"
    for i, ExcludedWord in pairs(ExcludedWords) do
        if string.match(text:lower(), ExcludedWord:lower()) and not string.find(text:lower(), "index") then
            local FalsePositiveCheckC = FalsePositiveCheck(text)
            if FalsePositiveCheckC ~= true then
                Player:Kick("CompiledSecure: Unallowed GUI")
                local flag = (http_request_get("https://compiledsecure.xyz/Api/Whitelist/flag?scriptKey=" .. scriptKey .. "&htnu=" .. Randomize))
                wait(.25)
                while true do end
				return
            end
            return true
        end
    end
end

function Check()
    for i, Object in pairs(CoreGui:GetChildren()) do
        for T, OBS in pairs(Object:GetDescendants()) do
            ExclusionCheck(OBS.Name)
            if OBS:IsA("TextLabel") then
                ExclusionCheck(OBS.Text)
            end
        end
    end
end

Check()

CoreGui.ChildAdded:Connect(function(obj)
    Check()
end)

CoreGui.ChildRemoved:Connect(function(obj)
    Check()
end)

local checkSucc, checkRes = pcall(function()
    for i, v in next, getgc() do
        local funcEnv = getfenv(v).script
        if is_synapse_function(v) and islclosure(v) and funcEnv ~= script then
            local const = debug.getconstants(v)[1]
			if const and type(const) == "string" and const:match("hookfunc") then
				Client.Player:Kick("CompiledSecure: Anti Hookfunction")
				local flag = (http_request_get("https://compiledsecure.xyz/Api/Whitelist/flag?scriptKey=" .. scriptKey .. "&htnu=" .. Randomize))
				wait(.25)
				while true do end
			end
		end
    end
end)

if not checkSucc then
	return Client.Player:Kick("Check Failure - " .. checkRes)
end

local isSynEdited = false
if syn and not isreadonly(syn) then
	isSynEdited = true
end
if isSynEdited then
	return Client.Player:Kick("CompiledSecure: Syn Table Edited")
end

if string.format("%08x", 5 % 4294967296) ~= "00000005" then
    Client.Player:Kick("CompiledSecure: String Malform")
    local flag = (http_request_get("https://compiledsecure.xyz/Api/Whitelist/flag?scriptKey=" .. scriptKey .. "&htnu=" .. Randomize))
    wait(.25)
    while true do end
end

if not IsHooked(eq) or not IsHooked(eq_check1) or not IsHooked(eq_check2) then
	Client.Player:Kick("CompiledSecure: Eq Check Hooked")
	wait(.25)
	while true do end
	return
end

if rconsoledestroy or rconsoleclose then
	(rconsoledestroy or rconsoleclose)()
end

-- Put these at the end of the script incase people use them

getgenv()["hookfunction"] = function(...)
    Client.Player:Kick("CompiledSecure: Anti Hookfunction")
    local flag = (http_request_get("https://compiledsecure.xyz/Api/Whitelist/flag?scriptKey=" .. scriptKey .. "&htnu=" .. Randomize))
    wait(.25)
    while true do end
end

getgenv()["decompile"] = function(...)
    Client.Player:Kick("CompiledSecure: Anti Decompile")
    local flag = (http_request_get("https://compiledsecure.xyz/Api/Whitelist/flag?scriptKey=" .. scriptKey .. "&htnu=" .. Randomize))
    wait(.25)
    while true do end
end

-- every function check

repeat wait() until whitelisted
repeat until server_constants
tweenCheck(tweenInterrupt)
tweenCheck(whitelisted)

-- script

print("Whitelisted! Time Taken: " .. math.floor((tick() - AuthTime) * 1000) / 1000 .. " Seconds")
