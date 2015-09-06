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

	LBRA, RBRA, COLON = [pp.Suppress(c) for c in '{};']
	ident = pp.Word(pp.alphas + '_', pp.alphanums + '_')

	buildin_type = pp.Keyword('int')

	var_decl = pp.Forward()

	struct_def = LBRA + pp.Group(pp.ZeroOrMore(var_decl)) + RBRA
	struct_decl = pp.Keyword('struct') + ident + pp.Optional(struct_def)

	type_decl = buildin_type ^ struct_decl
	var_decl << type_decl + pp.Optional(ident) + COLON

	extern_mod = pp.Optional(pp.Keyword('extern'), default = '__noextern')

	decl = pp.Group(extern_mod + var_decl)

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
