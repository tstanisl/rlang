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

def parseExpression():
	import pyparsing as pp
	ident = pp.Word(pp.alphas, pp.alphanums + '_')
	eident = ident.copy()
	dec_digit = pp.Regex(r'0|([1-9]\d*)').setParseAction(lambda t: int(t[0]))
	digit = dec_digit

	expr = pp.Forward()

	top_expr = eident ^ digit

	def make_ast(t):
		t = t[0].asList()
		ret = t[0]
		for i in range(1, len(t), 2):
			ret = [t[i], ret, t[i + 1]]
		return [ret]
	comparison_ast = lambda t: [['<>'] + t[0].asList()]
	arith_expr = pp.infixNotation(top_expr, [ \
		(pp.oneOf('+ - !'), 1, pp.opAssoc.RIGHT,), \
		(pp.oneOf('/ % *'), 2, pp.opAssoc.LEFT, make_ast), \
		(pp.oneOf('+ -'), 2, pp.opAssoc.LEFT, make_ast), \
		(pp.oneOf('< <= == != => >'), 2, pp.opAssoc.LEFT, comparison_ast), \
		(pp.Literal('&&'), 2, pp.opAssoc.RIGHT, make_ast), \
		(pp.Literal('||'), 2, pp.opAssoc.RIGHT, make_ast), \
		(pp.Literal('==>'), 2, pp.opAssoc.RIGHT, make_ast), \
	])

	expr << arith_expr

	return expr

def parseProgram():
	import pyparsing as pp

	program = pp.Empty()

	comment = pp.cppStyleComment()
	program.ignore(comment)

	return program

def main():
	import sys

	in_file = sys.stdin
	if len(sys.argv) > 1 and sys.argv[1] != '-':
		in_file = open(sys.argv[1], "r")

	grammar = parseExpression()
	ast = grammar.parseFile(in_file, True)

	print(ast)

if __name__ == "__main__":
	main()
