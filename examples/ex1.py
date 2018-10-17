fp = Fixedpoint()
fp.set(generate_explanations=True, engine='pdr')

tr = Relation('transition', IntSort(), IntSort())
err = Relation('error')
fp.register_relation(tr)
x, y = Ints('x, y')

fp.rule(tr(x, y), [x = 0, y > 1])
fp.rule(tr(x + 1, y + x), tr(x,y))
fp.rule(error, [tr(x, y), x >= y])


