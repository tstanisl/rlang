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

	LBRA, RBRA, COLON, LPAR, RPAR, COMMA = [pp.Suppress(c) for c in '{};(),']
	ident = pp.Word(pp.alphas + '_', pp.alphanums + '_')

	buildin_type = pp.Keyword('int')
	extern_mod = pp.Optional(pp.Keyword('extern'), default = '__noextern')

	var_decl_body = pp.Forward()

	block_stmt = LBRA + RBRA
	contracts_decl = pp.Empty()
	arg_list = pp.Group(pp.Optional(var_decl_body + pp.ZeroOrMore( \
		COMMA + var_decl_body) + pp.Optional(COMMA)))
	TEMPLATE = pp.Suppress(pp.Keyword('template'))
	template_decl = extern_mod + TEMPLATE + ident + LPAR + \
		arg_list + RPAR + contracts_decl + block_stmt

	STRUCT = pp.Keyword('struct')
	struct_def = LBRA + pp.Group(pp.ZeroOrMore(var_decl_body + COLON)) + RBRA
	struct_decl = STRUCT + ident + struct_def + COLON

	struct_type = STRUCT + ident
	type_decl = buildin_type ^ struct_type

	var_decl_body << type_decl + ident
	var_decl = extern_mod + var_decl_body + COLON

	decl = pp.Group(var_decl ^ struct_decl ^ template_decl)

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
