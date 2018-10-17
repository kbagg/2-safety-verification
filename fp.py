tr = Relation('transition', IntSort(), IntSort())
err = Relation('error')

# model M
fp1 = Fixedpoint()
fp1.set(generate_explanations=True, engine='pdr')

fp1.register_relation(tr)

x, y = Ints('x, y')

fp1.rule(tr(x, y), [x = 0, y > 1])
fp1.rule(tr(x + 1, y + x), tr(x,y))
fp1.rule(error, [tr(x, y), x >= y])

# model M' (M_d)
fp2 = Fixedpoint()
fp2.set(generate_explanations=True, engine='pdr')

fp2.register_relation(tr)

a, b = Ints('a, b')

fp2.rule(tr(a, b), [a = 0, b > 1])
fp2.rule(tr(a + 1, b + a), tr(a, b))
fp2.rule(error, [tr(a, b), a >= b])

# Self composition of M and M'
trace = Relation('transition', IntSort(), IntSort(), IntSort(), IntSort())

fp3 = Fixedpoint()
fp3.set(generate_explanations=True, engine='pdr')

fp3.register_relation(tr)

X, Y, A, B = Ints('X, Y, A, B')

fp3.rule(trace(X, Y, A, B), [X = 0, Y > 1, A = 0, B > 1])
fp3.rule(trace(X + 1, Y + X, A + 1, B + A), trace(X, Y, A, B))
fp3.rule(error, [trace(X, Y, A, B), X >= Y, A >= B])