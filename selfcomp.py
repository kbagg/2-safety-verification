import z3

class TransitionSystem(object):
    def variables(self, suffix = ''):
        if suffix != '':
            s = '_' + suffix
        else:
            s = ''
        return [z3.Int('x' + s), z3.Int('y' + s)]

    def sorts(self):
        return [z3.IntSort(), z3.IntSort()]

    def init(self, xs):
        "Init(x, y) = (x == 0 && y == 1)"
        return [xs[0] == 0, xs[1] == 1]

    def tr(self, xs, xsp):
        "Tr(x, y, x', y') = (x' == x + 1 && y' == x + y)"
        return [xsp[0] == xs[0] + 1,
                xsp[1] == xs[0] + xs[1]]

class SelfComposedTransitionSystem(object):
    def __init__(self, M):
        self.M = M
    def variables(self, suffix = ''):
        v1 = self.M.variables('_1' + suffix)
        v2 = self.M.variables('_2' + suffix)
        return v1 + v2
    def sorts(self):
        return self.M.sorts() + self.M.sorts()
    def init(self, xs):
        m = len(xs) // 2
        xs1 = xs[:m]
        xs2 = xs[m:]
        return self.M.init(xs1) + self.M.init(xs2)
    def tr(self, xs, xsp):
        m = len(xs) // 2
        xs1  = xs[:m]
        xs2  = xs[m:]
        xsp1 = xsp[:m]
        xsp2 = xsp[m:]
        return self.M.tr(xs1, xsp1) + self.M.tr(xs2, xsp2)

def fixedpoint(M, bad):
    fp = z3.Fixedpoint()
    options = {'engine':'spacer'}
    fp.set(**options)

    xs = M.variables()
    xsp = M.variables('prime')
    sorts = M.sorts() + [z3.BoolSort()]
    inv = z3.Function('inv', *sorts)
    err = z3.Function('err', z3.BoolSort())

    fp.register_relation(inv)
    fp.register_relation(err)
    for zi in xs + xsp:
        fp.declare_var(zi)

    inv_xs = inv(*xs)
    inv_xsp = inv(*xsp)
    fp.rule(inv_xs, M.init(xs))
    fp.rule(inv_xsp, M.tr(xs, xsp) + [inv_xs])
    fp.rule(err(), bad(xs) + [inv_xs])

    print (str(fp))
    print (fp.query(err))
    # print (fp.get_answer())

if __name__ == '__main__':
    M = TransitionSystem()
    def bad(xs):
        return [xs[0] > xs[1]]
    fixedpoint(M, bad)

    Msc = SelfComposedTransitionSystem(M)
    def bad_sc(xs):
        return [z3.And(xs[0] == xs[2], xs[1] != xs[3])]
    # The following times out.
    fixedpoint(Msc, bad_sc)
