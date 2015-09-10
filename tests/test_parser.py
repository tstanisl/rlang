from importlib.machinery import SourceFileLoader

parser = SourceFileLoader("module", "parser.py").load_module()

tests = [
	["base0", "var a int;", ['var', 'a', 'int', False, None] ],
	["base1", "var a int = 1;", ['var', 'a', 'int', False, 1] ],
	["base2", "var a [2]int = {0,1};", ['var', 'a', 'int', False, 1] ],
	["template0", "template a() {}", ['template', 'a', [], False, []] ],
	["template1", "template a(b bit) {}", ['template', 'a', [['b', 'bit']], False, []] ],
]

grammar = parser.prepare_grammar()

n_pass = 0
for test in tests:
	name = test[0]
	code = test[1]
	expected_ast = test[2]
	ast = []
	try:
		ast = grammar.parseString(code)
		if ast != expected_ast:
			raise
		print(name + " : passed")
		n_pass = n_pass + 1
	except:
		print(name + " : failed")
		print("\tcode    : {}".format(code))
		print("\texpected: {}".format(expected_ast))
		print("\t     got: {}".format(ast))

print("Passed {}/{} tests".format(n_pass, len(tests)))
