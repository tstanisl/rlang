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

from semantics import *

class Verifier:
	pipe = None
	int_size = 64
	errors = []
	varstack = []
	var_age = dict()
	var_sort = dict()
	tmp_sort = []

	def __init__(self, int_size):
		self.int_size = int_size

	def emit(self, smt2):
		print(smt2 + '\n')

	def verify_sequence(self, seq):
		for stmt in seq:
			verify_statement(stmt)

	def verify_statement(self, stmt):
		op = stmt[0]
		where = str(stmt[1])


def main():
	import sys

	in_file = sys.stdin
	if len(sys.argv) > 1 and sys.argv[1] != '-':
		in_file = open(sys.argv[1], "r")

	#grammar = parseExpression()
	#grammar = parseStatement()
	grammar = parseProgram()
	ast = grammar.parseFile(in_file, True)
	print(ast)

	ctx = semantic_context()
	ctx.check_sequence(ast)
	if len(ctx.errors) > 0:
		for err in ctx.errors:
			print("Error: ", err)
		return
	print("Program semanticaly valid");

if __name__ == "__main__":
	main()