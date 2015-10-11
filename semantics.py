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

from parser import *

class context:
	variables = set()
	errors = []
	varstack = []
	def check_sequence(self, seq):
		frame = len(self.varstack)
		for stmt in seq:
			self.check_statement(stmt)
		# remove variables added in current sequence
		for idx in range(frame, len(self.varstack)):
			var = self.varstack[idx]
			self.variables.remove(var)
		del self.varstack[frame:]

	def check_statement(self, stmt):
		op = stmt[0]
		where = stmt[1]
		if op == 'var':
			name = stmt[3]
			if name in self.variables:
				self.errors.append("{}: '{}' is redefined"\
					.format(where, name))
			else:
				self.variables.add(name)
				self.varstack.append(name)
		elif op == '=':
			name = stmt[2]
			if name not in self.variables:
				self.errors.append("{}: '{}' is undefined"\
					.format(where, name))
		elif op == '{':
			self.check_sequence(stmt[2:])

def main():
	import sys

	in_file = sys.stdin
	if len(sys.argv) > 1 and sys.argv[1] != '-':
		in_file = open(sys.argv[1], "r")

	#grammar = parseExpression()
	#grammar = parseStatement()
	grammar = parseProgram()
	ast = grammar.parseFile(in_file, True)

	ctx = context()
	ctx.check_sequence(ast)
	if len(ctx.errors) == 0:
		print("Program semanticaly valid");
		return
	for err in ctx.errors:
		print("Error: ", err)

if __name__ == "__main__":
	main()
