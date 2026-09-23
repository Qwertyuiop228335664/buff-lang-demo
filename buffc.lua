#!/usr/bin/env lua
-- Buff compiler: lexer -> parser/AST -> semantic analysis -> C99 backend.

local function fail(message, token)
    if token then
        io.stderr:write(string.format("%s:%d:%d: %s\n", token.file or "<input>", token.line, token.column, message))
    else
        io.stderr:write("buffc: " .. message .. "\n")
    end
    os.exit(1)
end

local keywords = {fn=true, struct=true, ["end"]=true, let=true, var=true, ["if"]=true, ["then"]=true,
    ["elseif"]=true, ["else"]=true, ["while"]=true, ["do"]=true, ["for"]=true, match=true, case=true,
    default=true, ["return"]=true, import=true, const=true, spawn=true, ["in"]=true,
    ["and"]=true, ["or"]=true, ["not"]=true, ["true"]=true, ["false"]=true}

local function lex(source, file)
    local tokens, index, line, column = {}, 1, 1, 1
    local function add(kind, value, token_line, token_column)
        tokens[#tokens + 1] = {type=kind, value=value, line=token_line, column=token_column, file=file}
    end
    local function advance(text)
        for char in text:gmatch(".") do
            if char == "\n" then line, column = line + 1, 1 else column = column + 1 end
        end
        index = index + #text
    end
    while index <= #source do
        local rest = source:sub(index)
        local whitespace = rest:match("^%s+")
        if whitespace then
            advance(whitespace)
        elseif rest:match("^//") or rest:match("^%-%-") then
            local comment = rest:match("^.-\n") or rest
            advance(comment)
        elseif rest:match("^%-%-%[") then
            local close = rest:find("]%]", 5, true)
            if not close then fail("unterminated block comment", {file=file, line=line, column=column}) end
            advance(rest:sub(1, close + 1))
        elseif rest:match('^"') or rest:match("^'") then
            local quote, offset = rest:sub(1, 1), 2
            while offset <= #rest and rest:sub(offset, offset) ~= quote do
                if rest:sub(offset, offset) == "\n" then fail("newline in string literal", {file=file, line=line, column=column}) end
                if rest:sub(offset, offset) == "\\" then offset = offset + 1 end
                offset = offset + 1
            end
            if offset > #rest then fail("unterminated string literal", {file=file, line=line, column=column}) end
            local raw = rest:sub(1, offset)
            add("string", raw, line, column); advance(raw)
        elseif rest:match("^%d+%.?%d*") then
            local value = rest:match("^%d+%.?%d*")
            add("number", value, line, column); advance(value)
        elseif rest:match("^[A-Za-z_][A-Za-z0-9_]*") then
            local value = rest:match("^[A-Za-z_][A-Za-z0-9_]*")
            add(keywords[value] and "keyword" or "identifier", value, line, column); advance(value)
        else
            local two = rest:sub(1, 2)
            local multi = { ["->"]=true, ["=="]=true, ["!="]=true, ["<="]=true, [">="]=true, ["&&"]=true, ["||"]=true }
            local symbol = multi[two] and two or rest:sub(1, 1)
            add("symbol", symbol, line, column); advance(symbol)
        end
    end
    add("eof", "<eof>", line, column)
    return tokens
end

local Parser = {}; Parser.__index = Parser
function Parser.new(tokens) return setmetatable({tokens=tokens, position=1}, Parser) end
function Parser:current() return self.tokens[self.position] end
function Parser:at(value) return self:current().value == value end
function Parser:take(value)
    local token = self:current()
    if value and token.value ~= value then fail("expected '" .. value .. "', got '" .. token.value .. "'", token) end
    self.position = self.position + 1
    return token
end
function Parser:accept(value) if self:at(value) then return self:take() end end
function Parser:identifier(message)
    local token = self:current()
    if token.type ~= "identifier" then fail(message or "expected identifier", token) end
    self.position = self.position + 1
    return token
end
function Parser:type_name()
    local token = self:current()
    if token.type ~= "identifier" then fail("expected type name", token) end
    self.position = self.position + 1
    local result = {type="Type", name=token.value, pointer=0, token=token}
    while self:accept("*") do result.pointer = result.pointer + 1 end
    return result
end

local precedence = { ["="]=1, ["or"]=2, ["||"]=2, ["and"]=3, ["&&"]=3, ["=="]=4, ["!="]=4,
    ["<"]=5, [">"]=5, ["<="]=5, [">="]=5, ["+"]=6, ["-"]=6, ["*"]=7, ["/"]=7, ["%"] = 7 }
function Parser:expression(min_precedence)
    min_precedence = min_precedence or 1
    local token, left = self:current()
    if token.value == "(" then self:take(); left = self:expression(); self:take(")")
    elseif token.value == "-" or token.value == "not" then self:take(); left = {type="Unary", operator=token.value, value=self:expression(7), token=token}
    elseif token.type == "number" then self:take(); left = {type="Literal", value=token.value, value_type=token.value:find("%.") and "float" or "int", token=token}
    elseif token.type == "string" then self:take(); left = {type="Literal", value=token.value, value_type="string", token=token}
    elseif token.value == "true" or token.value == "false" then self:take(); left = {type="Literal", value=token.value, value_type="bool", token=token}
    elseif token.value == "spawn" then
        self:take(); local target = self:type_name(); local count
        if self:accept("[") then count = self:expression(); self:take("]") end
        self:take("in"); local arena = self:identifier("expected arena name after 'in'")
        left = {type="Spawn", target=target, count=count, arena=arena.value, token=token}
    elseif token.type == "identifier" then self:take(); left = {type="Name", name=token.value, token=token}
    else fail("expected expression", token) end
    while true do
        local next_token, op_precedence = self:current()
        if next_token.value == "(" then
            self:take(); local args = {}
            if not self:at(")") then repeat args[#args + 1] = self:expression() until not self:accept(",") end
            self:take(")"); left = {type="Call", callee=left, args=args, token=next_token}
        elseif next_token.value == "." then
            self:take(); local member = self:identifier("expected member name")
            left = {type="Member", object=left, member=member.value, token=member}
        elseif next_token.value == "[" then
            self:take(); local index = self:expression(); self:take("]")
            left = {type="Index", object=left, index=index, token=next_token}
        else
            op_precedence = precedence[next_token.value]
            if not op_precedence or op_precedence < min_precedence then break end
            self:take(); local right = self:expression(op_precedence + 1)
            left = {type="Binary", operator=next_token.value, left=left, right=right, token=next_token}
        end
    end
    return left
end
function Parser:block(terminators)
    local statements = {}
    while not terminators[self:current().value] and not self:at("<eof>") do statements[#statements + 1] = self:statement() end
    return statements
end
function Parser:statement()
    local token = self:current()
    if token.value == "let" or token.value == "var" then
        self:take(); local name = self:identifier("expected variable name")
        local declared = self:accept(":") and self:type_name() or nil
        self:take("="); return {type="Variable", name=name.value, declared=declared, value=self:expression(), token=token}
    elseif token.value == "return" then
        self:take(); return {type="Return", value=self:at("end") and nil or self:expression(), token=token}
    elseif token.value == "if" then
        self:take(); local condition = self:expression(); self:accept("then")
        local branches = {{condition=condition, body=self:block({["elseif"]=true, ["else"]=true, ["end"]=true})}}
        while self:accept("elseif") do
            local branch_condition = self:expression(); self:accept("then")
            branches[#branches + 1] = {condition=branch_condition, body=self:block({["elseif"]=true, ["else"]=true, ["end"]=true})}
        end
        local alternative
        if self:accept("else") then alternative = self:block({["end"]=true}) end
        self:take("end"); return {type="If", branches=branches, alternative=alternative, token=token}
    elseif token.value == "while" then
        self:take(); local condition = self:expression(); self:accept("do")
        local body = self:block({["end"]=true}); self:take("end"); return {type="While", condition=condition, body=body, token=token}
    elseif token.value == "for" then
        self:take(); local name = self:identifier(); self:take("=")
        local first = self:expression(); self:take(","); local last = self:expression(); self:accept("do")
        local body = self:block({["end"]=true}); self:take("end")
        return {type="For", name=name.value, first=first, last=last, body=body, token=token}
    elseif token.value == "match" then
        self:take(); local value = self:expression(); local cases = {}
        while self:accept("case") do
            local case_value = self:expression()
            cases[#cases + 1] = {value=case_value, body=self:block({case=true, default=true, ["end"]=true})}
        end
        local default
        if self:accept("default") then default = self:block({["end"]=true}) end
        self:take("end"); return {type="Match", value=value, cases=cases, default=default, token=token}
    else return {type="Expression", value=self:expression(), token=token} end
end
function Parser:parse()
    local program = {type="Program", imports={}, structs={}, functions={}, constants={}}
    while not self:at("<eof>") do
        if self:accept("import") then
            local token = self:current()
            if token.type == "string" then self:take(); program.imports[#program.imports + 1] = token.value:sub(2, -2)
            elseif self:accept("<") then local header = self:take().value; self:take(">"); program.imports[#program.imports + 1] = "<" .. header .. ">"
            else fail("expected quoted Buff file or C header after import", token) end
        elseif self:accept("struct") then
            local name = self:identifier(); local fields = {}
            while not self:at("end") do
                local field = self:identifier(); self:take(":"); local field_type = self:type_name(); local size
                if self:accept("[") then size = self:expression(); self:take("]") end
                fields[#fields + 1] = {name=field.value, field_type=field_type, size=size, token=field}
            end
            self:take("end"); program.structs[#program.structs + 1] = {name=name.value, fields=fields, token=name}
        elseif self:accept("fn") then
            local name = self:identifier(); self:take("("); local params = {}
            if not self:at(")") then repeat local param = self:identifier(); self:take(":"); params[#params + 1] = {name=param.value, param_type=self:type_name(), token=param} until not self:accept(",") end
            self:take(")"); local result = self:accept("->") and self:type_name() or {type="Type", name="void", pointer=0, token=name}
            local body = self:block({["end"]=true}); self:take("end")
            program.functions[#program.functions + 1] = {name=name.value, params=params, result=result, body=body, token=name}
        elseif self:accept("const") then
            local name = self:identifier(); self:take("="); program.constants[#program.constants + 1] = {name=name.value, value=self:expression(), token=name}
        else fail("only import, struct, fn, and const are allowed at top level", self:current()) end
    end
    return program
end

local function type_key(t) return t.name .. string.rep("*", t.pointer or 0) end
local primitive = {int=true, float=true, double=true, char=true, bool=true, string=true, void=true, size_t=true, uint8_t=true}
local Analyzer = {}; Analyzer.__index = Analyzer
function Analyzer.new(program)
    local self = setmetatable({program=program, structs={}, functions={}, scopes={}}, Analyzer)
    for _, item in ipairs(program.structs) do if self.structs[item.name] then fail("duplicate struct '" .. item.name .. "'", item.token) end; self.structs[item.name] = item end
    for _, item in ipairs(program.functions) do if self.functions[item.name] then fail("duplicate function '" .. item.name .. "'", item.token) end; self.functions[item.name] = item end
    return self
end
function Analyzer:valid_type(t) if not primitive[t.name] and not self.structs[t.name] then fail("unknown type '" .. t.name .. "'", t.token) end end
function Analyzer:lookup(name, token)
    for index = #self.scopes, 1, -1 do if self.scopes[index][name] then return self.scopes[index][name] end end
    if name == "game_arena" then return "Arena*" end
    fail("unknown name '" .. name .. "'", token)
end
function Analyzer:compatible(left, right, token)
    if left == "unknown" or right == "unknown" or left == right then return true end
    if (left == "int" and right == "float") or (left == "float" and right == "int") then return true end
    fail("type mismatch: cannot use " .. right .. " where " .. left .. " is expected", token)
end
function Analyzer:expression(node)
    if node.type == "Literal" then node.inferred = node.value_type
    elseif node.type == "Name" then node.inferred = self:lookup(node.name, node.token); node.resolved = node.inferred; node.assignable = true
    elseif node.type == "Spawn" then
        self:valid_type(node.target); self:lookup(node.arena, node.token); if node.count then self:expression(node.count) end
        node.inferred = type_key({name=node.target.name, pointer=1})
    elseif node.type == "Unary" then
        local value_type = self:expression(node.value)
        if node.operator == "-" and value_type ~= "int" and value_type ~= "float" and value_type ~= "double" then fail("unary '-' requires a numeric value", node.token) end
        if node.operator == "not" and value_type ~= "bool" then fail("'not' requires a bool value", node.token) end
        node.inferred = node.operator == "not" and "bool" or value_type
    elseif node.type == "Binary" then
        local left, right = self:expression(node.left), self:expression(node.right)
        if node.operator == "=" then
            if not node.left.assignable then fail("left side of assignment is not assignable", node.token) end
            node.inferred = left
            self:compatible(left, right, node.token)
        else
            if node.operator == "and" or node.operator == "or" or node.operator == "&&" or node.operator == "||" or node.operator == "==" or node.operator == "!=" or node.operator == "<" or node.operator == ">" or node.operator == "<=" or node.operator == ">=" then node.inferred = "bool" else node.inferred = left end
            self:compatible(left, right, node.token)
        end
    elseif node.type == "Member" then
        local object = self:expression(node.object); local name = object:gsub("%*$", ""); local structure = self.structs[name]
        if not structure then fail("'" .. name .. "' has no fields", node.token) end
        for _, field in ipairs(structure.fields) do if field.name == node.member then node.field = field; node.inferred = type_key(field.field_type); node.assignable = true; return node.inferred end end
        fail("struct '" .. name .. "' has no member '" .. node.member .. "'", node.token)
    elseif node.type == "Index" then self:expression(node.object); self:expression(node.index); node.inferred = "unknown"; node.assignable = true
    elseif node.type == "Call" then
        local name = node.callee.name; local callee = name and self.functions[name]
        if name == "print" or name == "println" then
            for _, arg in ipairs(node.args) do
                local arg_type = self:expression(arg)
                if arg_type == "unknown" then fail("cannot print a value with unknown type", arg.token) end
            end
            node.inferred = "void"
        else
            if not callee then fail("unknown function", node.token) end
            if #callee.params ~= #node.args then fail("function '" .. callee.name .. "' expects " .. #callee.params .. " arguments", node.token) end
            for index, arg in ipairs(node.args) do self:compatible(type_key(callee.params[index].param_type), self:expression(arg), arg.token) end
            node.inferred = type_key(callee.result)
        end
    end
    return node.inferred or "unknown"
end
function Analyzer:statements(statements, result_type)
    for _, node in ipairs(statements) do
        if node.type == "Variable" then
            local inferred = self:expression(node.value)
            if node.declared then self:valid_type(node.declared); self:compatible(type_key(node.declared), inferred, node.token); node.final_type = node.declared
            else if inferred == "unknown" then fail("cannot infer variable type", node.token) end; node.final_type = {name=inferred, pointer=0} end
            if self.scopes[#self.scopes][node.name] then fail("duplicate variable '" .. node.name .. "'", node.token) end
            self.scopes[#self.scopes][node.name] = type_key(node.final_type)
        elseif node.type == "Return" then self:compatible(type_key(result_type), node.value and self:expression(node.value) or "void", node.token)
        elseif node.type == "Expression" then self:expression(node.value)
        elseif node.type == "If" then
            for _, branch in ipairs(node.branches) do self:expression(branch.condition); self.scopes[#self.scopes + 1] = {}; self:statements(branch.body, result_type); table.remove(self.scopes) end
            if node.alternative then self.scopes[#self.scopes + 1] = {}; self:statements(node.alternative, result_type); table.remove(self.scopes) end
        elseif node.type == "While" then self:expression(node.condition); self.scopes[#self.scopes + 1] = {}; self:statements(node.body, result_type); table.remove(self.scopes)
        elseif node.type == "For" then self:expression(node.first); self:expression(node.last); self.scopes[#self.scopes + 1] = {[node.name]="int"}; self:statements(node.body, result_type); table.remove(self.scopes)
        elseif node.type == "Match" then
            local matched_type = self:expression(node.value)
            if matched_type ~= "int" and matched_type ~= "char" and matched_type ~= "bool" then fail("match requires an int, char, or bool value", node.token) end
            for _, case in ipairs(node.cases) do self:compatible(matched_type, self:expression(case.value), case.value.token); self.scopes[#self.scopes + 1] = {}; self:statements(case.body, result_type); table.remove(self.scopes) end
            if node.default then self.scopes[#self.scopes + 1] = {}; self:statements(node.default, result_type); table.remove(self.scopes) end
        end
    end
end
function Analyzer:run()
    for _, structure in ipairs(self.program.structs) do for _, field in ipairs(structure.fields) do self:valid_type(field.field_type) end end
    for _, fn in ipairs(self.program.functions) do
        self:valid_type(fn.result); self.scopes = {{}}
        for _, param in ipairs(fn.params) do self:valid_type(param.param_type); self.scopes[1][param.name] = type_key(param.param_type) end
        self:statements(fn.body, fn.result)
    end
end

local function ctype(t)
    if t.name == "string" and (t.pointer or 0) == 0 then return "const char*" end
    return t.name .. string.rep("*", t.pointer or 0)
end
local emit_expression
local function print_format(node)
    if node.inferred == "string" then return "%s", emit_expression(node) end
    if node.inferred == "int" or node.inferred == "size_t" or node.inferred == "uint8_t" then return "%d", emit_expression(node) end
    if node.inferred == "float" or node.inferred == "double" then return "%f", emit_expression(node) end
    if node.inferred == "char" then return "%c", emit_expression(node) end
    if node.inferred == "bool" then return "%s", "(" .. emit_expression(node) .. " ? \"true\" : \"false\")" end
    return "%p", "(void*)" .. emit_expression(node)
end
function emit_expression(node)
    if node.type == "Literal" then return node.value
    elseif node.type == "Name" then return node.name
    elseif node.type == "Spawn" then return "(" .. ctype({name=node.target.name, pointer=1}) .. ")arena_alloc(&" .. node.arena .. ", sizeof(" .. node.target.name .. ")" .. (node.count and " * (" .. emit_expression(node.count) .. ")" or "") .. ")"
    elseif node.type == "Unary" then return (node.operator == "not" and "!" or node.operator) .. "(" .. emit_expression(node.value) .. ")"
    elseif node.type == "Binary" then local op = ({["and"]="&&",["or"]="||"})[node.operator] or node.operator; return "(" .. emit_expression(node.left) .. " " .. op .. " " .. emit_expression(node.right) .. ")"
    elseif node.type == "Member" then return emit_expression(node.object) .. ((node.object.inferred or ""):sub(-1) == "*" and "->" or ".") .. node.member
    elseif node.type == "Index" then return emit_expression(node.object) .. "[" .. emit_expression(node.index) .. "]"
    elseif node.type == "Call" then
        if node.callee.name == "print" or node.callee.name == "println" then
            if #node.args > 1 and node.args[1].type == "Literal" and node.args[1].value_type == "string" then
                local args = {node.args[1].value}
                for index = 2, #node.args do args[#args + 1] = emit_expression(node.args[index]) end
                local result = "printf(" .. table.concat(args, ", ") .. ")"
                if node.callee.name == "println" then result = result .. "; printf(\"\\n\")" end
                return result
            end
            local statements = {}
            for _, arg in ipairs(node.args) do
                local format, value = print_format(arg)
                statements[#statements + 1] = "printf(\"" .. format .. "\", " .. value .. ")"
            end
            if node.callee.name == "println" then statements[#statements + 1] = "printf(\"\\n\")" end
            return table.concat(statements, "; ")
        end
        local args = {}; for _, arg in ipairs(node.args) do args[#args + 1] = emit_expression(arg) end
        return emit_expression(node.callee) .. "(" .. table.concat(args, ", ") .. ")"
    end
    return "0"
end
local Backend = {}; Backend.__index = Backend
function Backend.new(program) return setmetatable({program=program, lines={}, indent=0}, Backend) end
function Backend:write(text) self.lines[#self.lines + 1] = string.rep("    ", self.indent) .. text end
function Backend:block(statements, result_type)
    for _, node in ipairs(statements) do
        if node.type == "Variable" then self:write(ctype(node.final_type) .. " " .. node.name .. " = " .. emit_expression(node.value) .. ";")
        elseif node.type == "Return" then self:write("return" .. (node.value and " " .. emit_expression(node.value) or "") .. ";")
        elseif node.type == "Expression" then self:write(emit_expression(node.value) .. ";")
        elseif node.type == "If" then
            for index, branch in ipairs(node.branches) do self:write((index == 1 and "if" or "else if") .. " (" .. emit_expression(branch.condition) .. ") {"); self.indent = self.indent + 1; self:block(branch.body, result_type); self.indent = self.indent - 1; self:write("}") end
            if node.alternative then self:write("else {"); self.indent = self.indent + 1; self:block(node.alternative, result_type); self.indent = self.indent - 1; self:write("}") end
        elseif node.type == "While" then self:write("while (" .. emit_expression(node.condition) .. ") {"); self.indent = self.indent + 1; self:block(node.body, result_type); self.indent = self.indent - 1; self:write("}")
        elseif node.type == "For" then self:write("for (int " .. node.name .. " = " .. emit_expression(node.first) .. "; " .. node.name .. " <= " .. emit_expression(node.last) .. "; " .. node.name .. "++) {"); self.indent = self.indent + 1; self:block(node.body, result_type); self.indent = self.indent - 1; self:write("}")
        elseif node.type == "Match" then self:write("switch (" .. emit_expression(node.value) .. ") {"); self.indent = self.indent + 1; for _, case in ipairs(node.cases) do self:write("case " .. emit_expression(case.value) .. ":"); self.indent = self.indent + 1; self:block(case.body, result_type); self:write("break;"); self.indent = self.indent - 1 end; if node.default then self:write("default:"); self.indent = self.indent + 1; self:block(node.default, result_type); self.indent = self.indent - 1 end; self.indent = self.indent - 1; self:write("}") end
    end
end
function Backend:generate()
    self:write("/* Generated by buffc.lua - do not edit. */")
    self:write("#include <stdbool.h>"); self:write("#include <stdint.h>"); self:write("#include <stddef.h>"); self:write("#include <stdio.h>"); self:write("#include \"buff_runtime.h\"")
    for _, import in ipairs(self.program.imports) do if import:sub(1, 1) == "<" then self:write("#include " .. import) elseif import:match("%.h$") then self:write("#include \"" .. import .. "\"") end end
    self:write("")
    for _, structure in ipairs(self.program.structs) do self:write("typedef struct " .. structure.name .. " {"); self.indent = self.indent + 1; for _, field in ipairs(structure.fields) do self:write(ctype(field.field_type) .. " " .. field.name .. (field.size and "[" .. emit_expression(field.size) .. "]" or "") .. ";") end; self.indent = self.indent - 1; self:write("} " .. structure.name .. ";"); self:write("") end
    for _, fn in ipairs(self.program.functions) do local params = {}; for _, param in ipairs(fn.params) do params[#params + 1] = ctype(param.param_type) .. " " .. param.name end; self:write(ctype(fn.result) .. " " .. fn.name .. "(" .. (#params > 0 and table.concat(params, ", ") or "void") .. ");") end
    self:write("")
    for _, constant in ipairs(self.program.constants) do self:write("#define " .. constant.name .. " " .. emit_expression(constant.value)) end
    for _, fn in ipairs(self.program.functions) do local params = {}; for _, param in ipairs(fn.params) do params[#params + 1] = ctype(param.param_type) .. " " .. param.name end; self:write(ctype(fn.result) .. " " .. fn.name .. "(" .. (#params > 0 and table.concat(params, ", ") or "void") .. ") {"); self.indent = self.indent + 1; self:block(fn.body, fn.result); self.indent = self.indent - 1; self:write("}"); self:write("") end
    return table.concat(self.lines, "\n") .. "\n"
end

local function read_file(path)
    local file = io.open(path, "r"); if not file then fail("cannot open '" .. path .. "'") end
    local content = file:read("*a"); file:close(); return content
end
local function normalize_path(path)
    local normalized = path:gsub("\\\\", "/")
    local prefix = ""
    if normalized:match("^%a:/") then prefix, normalized = normalized:sub(1, 3), normalized:sub(4)
    elseif normalized:sub(1, 1) == "/" then prefix, normalized = "/", normalized:sub(2) end
    local parts = {}
    for part in normalized:gmatch("[^/]+") do
        if part == ".." then
            if #parts > 0 and parts[#parts] ~= ".." then table.remove(parts) else parts[#parts + 1] = part end
        elseif part ~= "." and part ~= "" then
            parts[#parts + 1] = part
        end
    end
    return prefix .. table.concat(parts, "/")
end

local function load_sources(path, loaded, visiting)
    loaded, visiting = loaded or {}, visiting or {}
    local canonical = normalize_path(path)
    if loaded[canonical] then return "" end
    if visiting[canonical] then fail("cyclic import involving '" .. canonical .. "'") end
    visiting[canonical] = true
    local directory = canonical:match("^(.*)/[^/]+$") or "."
    local source, parts = read_file(canonical), {}
    for imported in source:gmatch('import%s+["(]([^"()]+%.buff)[")]') do
        parts[#parts + 1] = load_sources(directory .. "/" .. imported, loaded, visiting)
    end
    parts[#parts + 1] = source
    visiting[canonical], loaded[canonical] = nil, true
    return table.concat(parts, "\n")
end
local function parse_args(args)
    local config = {input=nil, output="out.c", compile=false, run=false, cc="gcc", cflags="-std=c99 -Wall -Wextra -O2"}
    local index = 1
    while index <= #args do
        local arg = args[index]
        if arg == "-o" then index = index + 1; config.output = args[index]
        elseif arg == "-c" or arg == "--compile" then config.compile = true
        elseif arg == "-r" or arg == "--run" then config.compile, config.run = true, true
        elseif arg == "--cc" then index = index + 1; config.cc = args[index]
        elseif arg == "--no-compile" then config.compile = false
        elseif not config.input and arg:sub(1, 1) ~= "-" then config.input = arg end
        index = index + 1
    end
    if not config.input then fail("usage: lua buffc.lua <input.buff> [-o output.c] [-c] [-r]") end
    return config
end
local function compile(config)
    local parser = Parser.new(lex(load_sources(config.input), config.input))
    local program = parser:parse(); Analyzer.new(program):run()
    local generated = Backend.new(program):generate()
    local output = io.open(config.output, "w"); if not output then fail("cannot write '" .. config.output .. "'") end
    output:write(generated); output:close(); print("[buffc] Transpiled -> " .. config.output)
    if config.compile then
        local executable = config.output:gsub("%.c$", "")
        local command = string.format('%s %s "%s" -o "%s"', config.cc, config.cflags, config.output, executable)
        print("[buffc] Compiling: " .. command)
        local ok = os.execute(command)
        if ok ~= true and ok ~= 0 then fail("C compilation failed") end
        print("[buffc] Build success: " .. executable)
        if config.run then os.execute('"' .. executable .. '"') end
    end
end
compile(parse_args(arg))
