from z3 import *

fun = Function('fun', IntSort(), IntSort(), BoolSort())
err = Bool('err')
fp1 = Fixedpoint()

fp1.register_relation(fun)
fp1.register_relation(err.decl())

x, i = z3.Ints('x i')

fp1.rule(fun(x, i), [x == 1, i == 0])
fp1.rule(fun(x + 2, i + 1), fun(x, i))
fp1.rule(err, [fun(x, i), i >= x])

a, j = z3.Ints('a j')
n = fp1.get_rules()[0]
print(n)
print(substitute(n, (x, a)))
print([substitute(rule, (x, a), (i, j)) for rule in fp1.get_rules()])