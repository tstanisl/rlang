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

	variables = {}

	ident = pp.Word(pp.alphas + '_', pp.alphanums + '_')
	digit = pp.Regex(r'0|([1-9]\d*)').setParseAction(lambda toks: int(toks[0]))

	def check_varname(s,l,t):
		varname = t[0]
		if varname not in variables:
			raise pp.ParseFatalException(s, l,\
				 "undefined variable '{}'".format(varname))
		return varname

	def get_storage(varname):
		return "{}${}".format(varname, variables[varname])

	def get_temporary():
		get_temporary.tmp_count += 1
		return "$" + str(get_temporary.tmp_count - 1)

	get_temporary.tmp_count = 0

	def eident_handle(s,l,t):
		varname = check_varname(s,l,t)
		return get_storage(varname)

	eident = ident.copy()
	eident.setParseAction(eident_handle)

	expr = pp.Forward()
	LPAR = pp.Suppress('(')
	RPAR = pp.Suppress(')')
	top_expr = digit ^ eident ^ (LPAR + expr + RPAR)
	PLUS = pp.Literal('+')
	MINUS = pp.Literal('-')
	add_expr = top_expr + pp.ZeroOrMore((PLUS ^ MINUS) + top_expr)
	def add_expr_handle(s,l,t):
		prev = t[0]
		for i in range(1, len(t), 2):
			if isinstance(prev, int) and isinstance(t[i + 1], int):
				if t[i] == '+':
					prev += t[i + 1]
				else:
					prev -= t[i + 1]
				continue
			result = get_temporary()
			print("(define-fun {} () Int ({} {} {}))".format(result, t[i], prev, t[i + 1]))
			prev = result

		return prev
	add_expr.setParseAction(add_expr_handle)

	expr << add_expr;

	EQ = pp.Suppress('=')
	SCOLON = pp.Suppress(';')

	assign_stmt = ident + EQ + expr + SCOLON
	def assign_stmt_handle(s,l,t):
		varname = check_varname(s,l,t)
		variables[varname] += 1
		t[0] = get_storage(varname)
		print("(define-fun {} () Int {})".format(t[0], t[1]))

	assign_stmt.setParseAction(assign_stmt_handle)

	INT = pp.Keyword('int')
	type_spec = INT

	VAR = pp.Suppress(pp.Keyword('var'))
	var_decl = VAR + type_spec + ident + SCOLON
	def var_decl_check(s,l,t):
		varname = t[1]
		if varname in variables:
			raise pp.ParseFatalException(s, l,\
				 "variable '{}' redefined".format(varname))
		variables[varname] = 0
		print("(declare-fun {} () Int)".format(get_storage(varname)))
	var_decl.setParseAction(var_decl_check)

	stmt = var_decl ^ assign_stmt
	grammar = pp.ZeroOrMore(stmt)

	comment = pp.cppStyleComment()
	grammar.ignore(comment)

	return grammar

def main():
	import sys
	import pyparsing as pp

	in_file = sys.stdin
	if len(sys.argv) > 1 and sys.argv[1] != '-':
		in_file = open(sys.argv[1], "r")

	grammar = prepare_grammar()

	def perror(e):
		print("{}:{}:error: {}\n\t{}".format(e.lineno, e.col, e.msg, e.line),
			file = sys.stderr)
	try:
		print("(set-logic QF_AUFLIA)")
		ast = grammar.parseFile(in_file, True)
	except pp.ParseException as e:
		perror(e)
	except pp.ParseFatalException as e:
		perror(e)

if __name__ == "__main__":
	main()

