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

	var_age = {}
	var_sort = {}
	tmp_sort = []

	ident = pp.Word(pp.alphas + '_', pp.alphanums + '_')
	digit = pp.Regex(r'0|([1-9]\d*)').setParseAction(lambda toks: int(toks[0]))

	def check_varname(s,l,t):
		varname = t[0]
		if varname not in var_age:
			raise pp.ParseFatalException(s, l,\
				 "undefined variable '{}'".format(varname))
		return varname

	def get_storage(varname):
		return "{}${}".format(varname, var_age[varname])

	def get_temporary(sort = 'int'):
		tmp_sort.append(sort)
		return "${}".format(len(tmp_sort) - 1)

	def eident_handle(s,l,t):
		varname = check_varname(s,l,t)
		return get_storage(varname)

	def get_sort(t):
		if isinstance(t, int):
			return 'int'
		assert isinstance(t, str)
		if t[0] == '$':
			return tmp_sort[int(t[1:])]
		varname = t.split('$', maxsplit = 1)[0]
		return var_sort[varname]

	def to_int(t):
		sort = get_sort(t)
		if sort == 'int':
			return t
		assert sort == 'bool'
		tmp = get_temporary('int')
		print("(define-fun {} () Int (ite {} 1 0))".format(tmp, t))
		return tmp

	def to_bool(t):
		sort = get_sort(t)
		if sort == 'bool':
			return t
		assert sort == 'int'
		tmp = get_temporary('bool')
		print("(define-fun {} () Bool (distinct 0 {}))".format(tmp, t))
		return tmp

	def to_smt2_sort(sort):
		if sort == 'bool':
			return 'Bool'
		return 'Int'

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
		op1 = t[0]
		for i in range(1, len(t), 2):
			op1 = to_int(op1)
			op2 = to_int(t[i + 1])
			# constant folding
			if isinstance(op1, int) and isinstance(op2, int):
				if t[i] == '+':
					op1 += op2
				else:
					op1 -= op2
				continue
			result = get_temporary()
			print("(define-fun {} () Int ({} {} {}))".format(result, t[i], op1, op2))
			op1 = result
		return op1
	add_expr.setParseAction(add_expr_handle)

	LT = pp.Literal("<")
	LE = pp.Literal("<=")
	EQ = pp.Literal("==")
	NEQ = pp.Literal("!=")
	GE = pp.Literal(">=")
	GT = pp.Literal(">")
	CMP = LT ^ LE ^ EQ ^ NEQ ^ GE ^ GT

	smt2_cmp = {
		'<' : '<',
		'<=' : '<=',
		'==' : '=',
		'!=' : 'distinct',
		'>' : '>',
		'>=' : '>=',
	}

	cmp_expr = add_expr + pp.ZeroOrMore(CMP + add_expr)
	def cmp_expr_handle(s,l,t):
		if len(t) == 1:
			return
		res = []
		for i in range(1, len(t), 2):
			op1 = t[i - 1]
			op = t[i]
			op2 = t[i + 1]
			if not (op == '==' or op == '!='):
				op1 = to_int(op1)
				op2 = to_int(op2)
			tmp = get_temporary('bool')
			print("(define-fun {} () Bool ({} {} {}))".format(\
				tmp, smt2_cmp[op], op1, op2))
			res.append(tmp)
		if len(res) == 1:
			return res
		tmp = get_temporary('bool')
		print("(define-fun {} () Bool (and {}))".format(\
			tmp, ' '.join(res)))
		return tmp

	cmp_expr.setParseAction(cmp_expr_handle)

	expr << cmp_expr;

	EQ = pp.Suppress('=')
	SCOLON = pp.Suppress(';')

	assign_stmt = ident + EQ + expr + SCOLON
	def assign_stmt_handle(s,l,t):
		varname = check_varname(s,l,t)
		var_age[varname] += 1
		t[0] = get_storage(varname)
		sort = to_smt2_sort(var_sort[varname])
		src = to_int(t[1])
		print("(define-fun {} () Int {})".format(t[0], src))

	assign_stmt.setParseAction(assign_stmt_handle)

	INT = pp.Keyword('int')
	type_spec = INT

	VAR = pp.Suppress(pp.Keyword('var'))
	var_decl = VAR + type_spec + ident + SCOLON
	def var_decl_check(s,l,t):
		varname = t[1]
		if varname in var_age:
			raise pp.ParseFatalException(s, l,\
				 "variable '{}' redefined".format(varname))
		var_age[varname] = 0
		var_sort[varname] = 'int'
		print("(declare-fun {} () Int)".format(get_storage(varname)))
	var_decl.setParseAction(var_decl_check)

	ASSERT = pp.Suppress(pp.Keyword('assert'))
	assert_stmt = ASSERT + expr + SCOLON;
	def assert_stmt_handle(s,l,t):
		print('(echo "assert:{}")'.format(l))
		res = to_bool(t[0])
		print("(push 1)")
		print("(assert (not {}))".format(res))
		print("(check-sat)")
		print("(pop 1)")

	assert_stmt.setParseAction(assert_stmt_handle)

	ASSUME = pp.Suppress(pp.Keyword('assume'))
	assume_stmt = ASSUME + expr + SCOLON
	def assume_stmt_handle(s,l,t):
		res = to_bool(t[0])
		print("(assert {})".format(res))
	assume_stmt.setParseAction(assume_stmt_handle)

	stmt = var_decl ^ assign_stmt ^ assert_stmt ^ assume_stmt
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

