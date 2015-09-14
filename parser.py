#!/usr/bin/python3

"""
RLANG Verification Compiler
Software dedicated to formal verification of programs written in RLANG
programming language.
Copyright (C) 2015 Tomasz Stanislawski

This program is free software; you can redistribute it and/or
modify it under the terms of the GNU General Public License
as published by the Free Software Foundation; either version 2
of the License, or (at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
"""

import sys
if sys.version_info.major != 3:
	raise Exception("Python 3.x required")

def prepare_grammar():
	import pyparsing as pp
	stack = []
	def __push(t):
		print("PUSH(", t[0], ")")
		stack.append(t[0])
		print("post: ", stack)
		return t[0]
	PUSH = lambda p: p.copy().setParseAction(__push) #lambda t: stack.append(t[0]))
	PUSH_NULL = pp.Empty().setParseAction(lambda t: stack.append([]))

	def REDUCE(parser, n, head = None):
		def handler(t):
			print("REDUCE(n={}, head={})".format(n, head))
			print("pre:  {}".format(stack))
			if head is None:
				print("no head")
				item = stack[-n] + stack[-n+1:]
			elif isinstance(head, str):
				print("str head")
				item = [head]
				if n > 0:
					item = item + stack[-n:]
			else:
				print("idx head")
				s = -n + head
				print(s)
				item = [stack[s]] + stack[-n:s] + stack[s+1:]
			print("item: ", item)
			if n > 0:
				del stack[-n:]
			stack.append(item)
			print("post: {}".format(stack))
			return t
		return parser.copy().setParseAction(handler)

	FLAG = lambda p: pp.Optional(p.setParseAction(pp.replaceWith(True)), default = False)

	AND = pp.Literal('&&')
	DIV = pp.Literal('/')
	DOT = pp.Literal('.')
	EQ = pp.Literal("==") + pp.NotAny(pp.Literal('>')) # conflict with ==>
	GE = pp.Literal(">=")
	GT = pp.Literal(">")
	GRAVE = pp.Literal('`')
	IND = pp.Literal("==>")
	LBRA = pp.Literal("{")
	LE = pp.Literal("<=")
	LPAR = pp.Literal('(')
	LSPAR = pp.Literal('[')
	LT = pp.Literal("<")
	MINUS = pp.Literal('-')
	MOD = pp.Literal('%')
	MUL = pp.Literal('*')
	NEQ = pp.Literal("!=")
	NOT = pp.Literal('!')
	OR = pp.Literal('||')
	PLUS = pp.Literal('+')
	RBRA = pp.Literal("}")
	RPAR = pp.Literal(')')
	RSPAR = pp.Literal(']')

	ident = PUSH(pp.Word(pp.alphas + '_', pp.alphanums + '_'))

	dec_digit = pp.Regex(r'0|([1-9]\d*)').setParseAction(lambda toks: int(toks[0]))
	hex_digit = pp.Regex(r'0x[0-9a-fA-F]+').setParseAction(lambda toks: int(toks[0][2:],16))
	bin_digit = pp.Regex(r'0b[01]+').setParseAction(lambda toks: int(toks[0][2:],2))
	digit = PUSH(dec_digit ^ hex_digit ^ bin_digit)

	expr = pp.Forward()

	struct_access = REDUCE(DOT + ident, 2, '.')
	array_access = REDUCE(LSPAR + expr + RSPAR, 2, '[')
	ref_access = pp.ZeroOrMore(struct_access ^ array_access)
	flow_expr = ident ^ REDUCE(GRAVE + ident, 1, '`')
	access_expr = flow_expr + ref_access

	top_expr = access_expr ^ digit ^ (LPAR + expr + RPAR) # add # operator

	unr_expr = pp.Forward()
	pos_expr = PLUS + unr_expr
	neg_expr = REDUCE(MINUS + unr_expr, 1, "-unary")
	not_expr = REDUCE(NOT + unr_expr, 1, "!")
	unr_expr << (pos_expr ^ neg_expr ^ not_expr ^ top_expr)

	mul_expr = unr_expr + pp.ZeroOrMore(\
		REDUCE(PUSH(MUL ^ DIV ^ MOD) + unr_expr, 3, 1))

	sum_expr = mul_expr + pp.ZeroOrMore(\
		REDUCE(PUSH(PLUS ^ MINUS) + mul_expr, 3, 1))

	CMP = LT ^ LE ^ EQ ^ NEQ ^ GE ^ GT
	cmp_tail1 = REDUCE(PUSH(CMP) + sum_expr, 3, '<>')
	cmp_tail2 = REDUCE(PUSH(CMP) + sum_expr, 3)
	cmp_expr = sum_expr + pp.Optional(cmp_tail1 + pp.ZeroOrMore(cmp_tail2))

	and_expr = pp.Forward()
	and_expr << cmp_expr + pp.Optional(REDUCE(AND + and_expr, 2, '&&'))
	orr_expr = pp.Forward()
	orr_expr << and_expr + pp.Optional(REDUCE(OR + orr_expr, 2, '||'))
	ind_expr = pp.Forward()
	ind_expr << orr_expr + pp.Optional(REDUCE(IND + ind_expr, 2, '==>'))

	cond_expr = pp.Forward()
	cond_tail = REDUCE('?' + cond_expr + ':' + cond_expr, 3, '?')
	cond_expr << (ind_expr + pp.Optional(cond_tail))

	expr << cond_expr

	stmt = pp.Forward()
	assign_stmt = REDUCE(access_expr + '=' + expr + ';', 2, '=')
	block_stmt = REDUCE(LBRA, 0, '{') + pp.ZeroOrMore(REDUCE(stmt, 2)) + RBRA
	if_stmt = pp.Forward()
	IF = pp.Keyword('if')
	ELSE = pp.Keyword('else')
	else_tail = ELSE + (block_stmt ^ if_stmt)
	if_stmt = REDUCE(IF + expr + block_stmt + (else_tail ^ REDUCE(pp.Empty(), 0, '{')), 3, 'if')

	bind_atom = REDUCE(REDUCE(ident + '=' + expr, 2, 0) + pp.Empty(), 2)
	bind_list = PUSH_NULL + pp.Optional(bind_atom + pp.ZeroOrMore(',' + bind_atom) + pp.Optional(','))
	instance_stmt = REDUCE(ident + '!' + LPAR + bind_list + RPAR + ';', 2, 'instance')
	return_stmt = REDUCE(pp.Keyword('return') + ';', 0, 'return')
	run_stmt = REDUCE(pp.Keyword('run') + PUSH(ident) + ';', 1, 'run')
	assert_stmt = REDUCE(pp.Keyword('assert') + expr + ';', 1, 'assert')

	stmt << (assign_stmt ^ block_stmt ^ if_stmt ^ instance_stmt ^ return_stmt\
		^ run_stmt ^ assert_stmt)

	grammar = expr.copy() ^ stmt
	grammar.setParseAction(lambda t: stack.pop())

	return grammar

	stack = []
	def pop(id, n, extra = []):
		print("pop(id={}, n={})".format(id, n))
		tail = stack[-n:]
		del stack[-n:]
		stack.append([id] + tail + extra)
		return stack[-1]

	def RIGHT_UNARY(sym, arg):
		parser = pp.Forward()
		body = sym + parser
		body.setParseAction(lambda t: pop(t[0], 1))
		parser << (arg ^ body)
		return parser

	def LEFT_BINARY(sym, arg):
		body = sym + arg
		body.setParseAction(lambda t: pop(t[0], 2))
		return arg + pp.ZeroOrMore(body)

	def RIGHT_BINARY(sym, arg):
		parser = pp.Forward()
		body = sym + parser
		body.setParseAction(lambda t: pop(t[0], 2))
		parser << (arg + pp.Optional(body))
		return parser

	def push(t):
		print('push0')
		print(stack)
		print(t)
		stack.append(t[0])
		print(stack)
		return t[0]
	def push1(t):
		print('push1')
		print(stack)
		print(t)
		b = stack.pop()
		a = stack.pop()
		#print(a)
		r = [t[0], a, b]
		stack.append(r)
		print(stack)
		#print(r)
		return r
	def push_unr(t):
		print('push_unr')
		print(stack)
		print(t)
		a = stack.pop()
		r = [t[0], a]
		stack.append(r)
		print(stack)
		return r;

	import pyparsing as pp

	LBRA, RBRA, SCOLON, LPAR, RPAR, COMMA = [pp.Suppress(c) for c in '{};(),']
	ASSIGN, QUESTION, COLON, PLUS, MINUS = [pp.Suppress(c) for c in '=?:+-']
	MUL, DIV, MOD, NOT = [pp.Suppress(c) for c in '*/%!']

	ident = pp.Word(pp.alphas + '_', pp.alphanums + '_')
	eident = ident.copy()
	eident.setParseAction(push)

	dec_digit = pp.Regex(r'0|([1-9]\d*)').setParseAction(lambda toks: int(toks[0]))
	hex_digit = pp.Regex(r'0x[0-9a-fA-F]+').setParseAction(lambda toks: int(toks[0][2:],16))
	bin_digit = pp.Regex(r'0b[01]+').setParseAction(lambda toks: int(toks[0][2:],2))
	digit = dec_digit ^ hex_digit ^ bin_digit
	#push(digit)
	digit.setParseAction(push)

	expr = pp.Forward()

	DOT = pp.Literal('.')
	struct_access = DOT + eident
	struct_access.setParseAction(push1)

	LSPAR = pp.Literal('[')
	RSPAR = pp.Literal(']')
	array_access = LSPAR + expr + RSPAR
	array_access.setParseAction(push1)
	#array_access.setParseAction(lambda toks: ['[]', toks[0]])
	access_expr = eident + pp.Group(pp.ZeroOrMore(struct_access ^ array_access))
	#access_expr.setParseAction(lambda t: ['.', t[0], list(t[1:])])

	par_expr = LPAR + expr + RPAR
	# TODO: what about casts
	top_expr = digit ^ access_expr ^ par_expr

	PLUS = pp.Literal('+')
	MINUS = pp.Literal('-')
	NOT = pp.Literal('!')
	#unr_expr = pp.ZeroOrMore(PLUS ^ MINUS ^ NOT) + top_expr
	#unr_expr = pp.Forward()
	#unr_expr << (top_expr ^ ((PLUS ^ MINUS ^ NOT) + unr_expr).setParseAction(push_unr))
	unr_expr = RIGHT_UNARY(PLUS ^ MINUS ^ NOT, top_expr)

	MUL = pp.Literal('*')
	DIV = pp.Literal('/')
	MOD = pp.Literal('%')
	mul_expr = LEFT_BINARY(MUL ^ DIV ^ MOD, unr_expr)
	add_expr = LEFT_BINARY(PLUS ^ MINUS, mul_expr)
	#mul_expr = unr_expr + pp.ZeroOrMore(((MUL ^ DIV ^ MOD) + unr_expr).setParseAction(push1))
	#add_expr = mul_expr + pp.ZeroOrMore(((PLUS ^ MINUS) + mul_expr).setParseAction(push1))

	LT = pp.Literal("<")
	LE = pp.Literal("<=")
	EQ = pp.Literal("==")
	NEQ = pp.Literal("!=")
	GE = pp.Literal(">=")
	GT = pp.Literal(">")
	CMP = LT ^ LE ^ EQ ^ NEQ ^ GE ^ GT

	def cmp_tail2_merge(t):
		print('cmp_tail2_merge')
		print(stack)
		print(t)
		z = stack.pop()
		print("z={}".format(z))
		h = stack.pop()
		print("h={}".format(h))
		if h[0] == '<>':
			# stack = ..., [<> ... op1 a], z
			#           -> [<> ... op1 a op2 z]
			ret = h + [t[0], z]
		else:
			# stack = ..., [op1 a b], z
			#           -> [<> a op1 b op2 z]
			ret = ['<>', h[1], h[0], h[2], t[0], z]
		print("ret={}".format(ret))
		stack.append(ret)
		return ret
	cmp_tail2 = CMP + add_expr
	cmp_tail2.setParseAction(cmp_tail2_merge)

	cmp_tail1 = CMP + add_expr
	cmp_tail1.setParseAction(lambda t: pop(t[0], 2))

	# a < b -> ['<', a, b]
	# a < b < c -> ['<>', a, '<', b, '<', c]
	cmp_expr = add_expr + pp.Optional(cmp_tail1 + pp.ZeroOrMore(cmp_tail2))

	#and_expr = pp.Forward()
	#and_expr << (cmp_expr + pp.Optional((pp.Literal('&&') + and_expr).setParseAction(push1)))
	AND = pp.Literal('&&')
	and_expr = RIGHT_BINARY(AND, cmp_expr)
	#and_expr = cmp_expr + pp.ZeroOrMore(pp.Suppress('&&') + cmp_expr)
	#or_expr = and_expr + pp.ZeroOrMore(pp.Suppress('||') + and_expr)
	OR = pp.Literal('||')
	or_expr = RIGHT_BINARY(OR, and_expr)
	#or_expr = pp.Forward()
	#or_expr << (and_expr + pp.Optional((pp.Literal('||') + or_expr).setParseAction(push1)))
	#induc_expr = pp.Forward()
	#induc_expr << (or_expr + pp.Optional((pp.Literal('==>') + induc_expr).setParseAction(push1)))
	IND = pp.Literal("==>")
	induc_expr = RIGHT_BINARY(IND, or_expr)
	equiv_expr = induc_expr + pp.Optional((pp.Literal('<==>') + induc_expr).setParseAction(push1))

	cond_expr = pp.Forward()
	QUEST = pp.Literal('?')
	cond_tail = QUEST + cond_expr + COLON + cond_expr
	cond_tail.setParseAction(lambda t: pop(t[0], 3))
	cond_expr << (equiv_expr + pp.Optional(cond_tail))

	expr << cond_expr

	buildin_type = pp.Keyword('int')

	extern_mod = pp.Optional(pp.Keyword('extern'))
	extern_mod.setParseAction(lambda toks: len(toks) != 0)
	extern_mod.setResultsName('extern')

	var_decl_body = pp.Forward()

	stmt = pp.Forward()
	block_stmt = LBRA + pp.Group(pp.ZeroOrMore(stmt)) + RBRA
	assign_stmt = access_expr + ASSIGN + expr + SCOLON
	RUN = pp.Suppress(pp.Keyword('run'))
	run_stmt = RUN + ident + SCOLON
	IF = pp.Suppress(pp.Keyword('if'))
	ELSE = pp.Suppress(pp.Keyword('else'))
	if_stmt = pp.Forward()
	if_stmt << IF + LPAR + expr + RPAR + block_stmt + pp.Optional(ELSE + (block_stmt ^ if_stmt))

	arg_bind = pp.Group(DOT + ident + ASSIGN + access_expr)
	arg_bind_list = pp.Group(pp.Optional(arg_bind + pp.ZeroOrMore(COMMA + arg_bind) + pp.Optional(COMMA)))
	template_stmt = ident + NOT + LPAR + arg_bind_list + RPAR + SCOLON

	stmt << pp.Group(block_stmt ^ if_stmt ^ run_stmt ^ assign_stmt ^ template_stmt)

	contracts_decl = pp.Empty()
	arg_list = pp.Group(pp.Optional(var_decl_body + pp.ZeroOrMore( \
		COMMA + var_decl_body) + pp.Optional(COMMA)))
	TEMPLATE = pp.Suppress(pp.Keyword('template'))
	template_decl = extern_mod + TEMPLATE + ident + LPAR + \
		arg_list + RPAR + contracts_decl + block_stmt

	SEQUENCE = pp.Suppress(pp.Keyword('sequence'))
	sequence_decl = extern_mod + SEQUENCE + ident + contracts_decl + block_stmt

	STRUCT = pp.Keyword('struct')
	struct_def = LBRA + pp.Group(pp.ZeroOrMore(var_decl_body + SCOLON)) + RBRA
	struct_decl = STRUCT + ident + struct_def + SCOLON

	struct_type = STRUCT + ident
	type_decl = buildin_type ^ struct_type

	var_decl_body << type_decl + ident
	var_decl = extern_mod + var_decl_body + pp.Optional(ASSIGN + expr, default = None) + SCOLON

	decl = pp.Group(var_decl ^ struct_decl ^ template_decl ^ sequence_decl)

	grammar = pp.ZeroOrMore(decl)

	comment = pp.cppStyleComment()
	grammar.ignore(comment)

	def show(t):
		print(stack)
	grammar.setParseAction(show)

	return grammar

def main():
	import sys

	in_file = sys.stdin
	if len(sys.argv) > 1 and sys.argv[1] != '-':
		in_file = open(sys.argv[1], "r")

	grammar = prepare_grammar()
	ast = grammar.parseFile(in_file, True)

	print(ast)

if __name__ == "__main__":
	main()
