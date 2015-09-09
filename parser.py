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
	stack = []
	def pop(id, n, extra = []):
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
	cmp_tail = pp.OneOrMore((LT ^ LE ^ EQ ^ NEQ ^ GE ^ GT) + add_expr)
	def cmp_expr_merge(t):
		print('cmp_expr_merge')
		print(stack)
		print(t)
		L = len(t) // 2
		print(L)
		if L == 1:
			return pop(t[0], 2)
		del stack[-L:]
		return pop('<>', 1, t[:])
##		if len(t) == 1:
##			return t[0]
##		if len(t) == 3:
##			return pop(t[1], 2)
#		r = pop('<>', len(t)+1)
#		print(r)
#		r = r + [t]
#		print(r)
#		print(stack)
#		stack.pop()
#		stack.append(r)
#		print(stack)
#		return stack[-1]
#		r = pop(
#		L = len(t)
#		base = ['<>', stack[L - 1]]
#		r = sum([list(x) for x in zip(t, stack[-L:])], base)
#		del stack[L-1:]
#		stack.append(r)
#		print(stack)
#		return r

	cmp_tail.setParseAction(cmp_expr_merge)
	cmp_expr = add_expr + pp.Optional(cmp_tail)

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
