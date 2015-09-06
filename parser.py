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

	LBRA, RBRA, SCOLON, LPAR, RPAR, COMMA = [pp.Suppress(c) for c in '{};(),']
	ASSIGN, QUESTION, COLON, PLUS, MINUS = [pp.Suppress(c) for c in '=?:+-']
	MUL, DIV, MOD, NOT = [pp.Suppress(c) for c in '*/%!']

	ident = pp.Word(pp.alphas + '_', pp.alphanums + '_')
	dec_digit = pp.Word("123456789", "0123456789")
	hex_digit = pp.Combine(pp.Suppress('0x') + pp.Word(pp.hexnums), adjacent = True)
	bin_digit = pp.Combine(pp.Suppress('0b') + pp.Word('01'), adjacent = True)
	digit = dec_digit ^ hex_digit ^ bin_digit

	expr = pp.Forward()

	DOT, LSPAR, RSPAR = [pp.Suppress(c) for c in '.[]']
	struct_access = DOT + ident
	array_access = LSPAR + expr + RSPAR
	access_expr = ident + pp.ZeroOrMore(struct_access ^ array_access)

	par_expr = LPAR + expr + RPAR
	# TODO: what about casts
	top_expr = digit ^ access_expr ^ par_expr

	unr_expr = pp.ZeroOrMore(PLUS ^ MINUS ^ NOT) + top_expr
	mul_expr = unr_expr + pp.ZeroOrMore((MUL ^ DIV ^ MOD) + unr_expr)
	add_expr = mul_expr + pp.ZeroOrMore((PLUS ^ MINUS) + mul_expr)

	LT = pp.Suppress("<")
	LE = pp.Suppress("<=")
	EQ = pp.Suppress("==")
	GE = pp.Suppress(">=")
	GT = pp.Suppress(">")
	cmp_expr = add_expr + pp.ZeroOrMore((LT ^ LE ^ EQ ^ GE ^ GT) + add_expr)

	and_expr = cmp_expr + pp.ZeroOrMore(pp.Suppress('&&') + cmp_expr)
	or_expr = and_expr + pp.ZeroOrMore(pp.Suppress('||') + and_expr)
	induc_expr = pp.Forward()
	induc_expr << or_expr + pp.Optional(pp.Suppress('==>') + induc_expr)
	equiv_expr = induc_expr + pp.Optional(pp.Suppress('<==>') + induc_expr)
	cond_expr = equiv_expr + pp.Optional(pp.Suppress('?') + equiv_expr + pp.Suppress(':') + equiv_expr)
	expr << cond_expr

	buildin_type = pp.Keyword('int')
	extern_mod = pp.Optional(pp.Keyword('extern'), default = '__noextern')

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
	var_decl = extern_mod + var_decl_body + pp.Optional(ASSIGN + expr) + SCOLON

	decl = pp.Group(var_decl ^ struct_decl ^ template_decl ^ sequence_decl)

	grammar = pp.ZeroOrMore(decl)

	comment = pp.cppStyleComment()
	grammar.ignore(comment)

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
