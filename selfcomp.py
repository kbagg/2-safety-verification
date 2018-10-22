import z3

# M = < {x, y}, Init, Tr >
def vs(suffix = ''):
    s = '' if suffix == '' else '_' + suffix
    return [z3.Int('x'+s), z3.Int('y'+s)]
def sorts():
    return [z3.IntSort(), z3.IntSort()]
# Init(x, y) = (x >= 0) && (x < y)
def init(xs):
    return [xs[0] >= 0, xs[0] < xs[1]]
# Tr(x, y, x', y') = (x' == x + 1 && y' = x + y)
def tr(xs, xsp):
    return [xsp[0] == xs[0] + 1, xsp[1] == xs[0] + xs[1]]
# bad(x, y) = x >= y
def bad(xs):
    return [xs[0] > xs[1]]

def fp(vs, sorts, init, tr, bad):
    fnsorts = sorts() + [z3.BoolSort()]
    inv = z3.Function('inv', *fnsorts)
    err = z3.Function('err', z3.BoolSort())

    fp = z3.Fixedpoint()
    fp.set(engine='pdr')
    fp.register_relation(inv)
    fp.register_relation(err)

    xs = vs()
    xsp = vs('p')

    fp.declare_var(*(xs + xsp))

    inv_xs = inv(*xs)
    inv_xsp = inv(*xsp)

    # init
    fp.rule(inv_xs, init(xs))
    fp.rule(inv_xsp, [inv(xs)] + tr(xs, xsp))
    fp.rule(err(), [inv_xs] + bad(xs))


    print (str(fp))
    print (fp.query(err))


if __name__ == '__main__':
    fp(vs, sorts, init, tr, bad)


