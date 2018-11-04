import z3
import struct

class TransitionSystem(object):

	def __init__(self, suffix = ''):
		
		if suffix != '':
			s = '_' + suffix
		else:
			s = ''
		xs = [z3.Int('x' + s), z3.Int('y' + s)]

		self.suffix = s
		self.variables = xs
		self.sorts = [z3.IntSort(), z3.IntSort()]
		self.init = [xs[0] == 0, xs[1] == 1]
		self.tr = [xs[0] + 1, xs[0] + xs[1]]
		self.bad = [xs[0] > xs[1]]

	def addSuffix(self, suffix = ''):
	    if suffix != '':
	    	s = '_' + suffix
	    else:
	    	s = ''
	    return [z3.Int('x' + s), z3.Int('y' + s)]

	def initialize(self, xs):
	    "Init(x, y) = (x == 0 && y == 1)"
	    return [xs[0] == 0, xs[1] == 1]

	def transition(self, xs):
	    "Tr(x, y, x', y') = (x' == x + 1 && y' == x + y)"
	    return [xs[0] + 1,
	            xs[0] + xs[1]]

class SelfComposedTransitionSystem(object):

	def __init__(self, model, suffix = ''):

		self.suffix = suffix
		self.model = model
		v1 = model.addSuffix('1' + suffix)
		v2 = model.addSuffix('2' + suffix)
		self.variables = v1 + v2
		self.sorts = model.sorts + model.sorts
		self.init = model.initialize(v1) + model.initialize(v2)
		self.tr =  model.transition(v1) + model.transition(v2)
		self.bad = [z3.And(v1[0] == v2[0], v1[1] != v2[1])]

	def addSuffix(self, suffix = ''):
		v1 = self.model.addSuffix('1' + suffix)
		v2 = self.model.addSuffix('2' + suffix)
		return v1 + v2

	def bad_sc(self, xs):
		return [z3.And(xs[0] == xs[2], xs[1] != xs[3])]

def getLength(ans):
	count = 0
	last_and = ans.arg(0).children()[-1]
	trace = last_and.children()[1]
	while trace.num_args() > 0:
		count = count + 1
		trace = trace.children()[-1]
	return count

def addCounter(M):
	M.variables = M.variables + [z3.Int('counter' + M.suffix)]
	M.sorts = M.sorts + [z3.IntSort()]
	M.init = M.init + [M.variables[-1] == 0]
	M.tr = M.tr + [M.variables[-1] + 1]

def relationalInduction():

	M = TransitionSystem()
	Msc = SelfComposedTransitionSystem(M)

	xs = Msc.variables
	xsp = Msc.addSuffix('prime')
	print(xs)
	print(xsp)

	bad = z3.simplify(z3.And(Msc.bad))
	init = z3.simplify(z3.And(Msc.init))
	check = z3.simplify(z3.And(init, bad))

	S = z3.Solver()
	S.push()
	S.add(check)
	rInit = (S.check())
	S.pop()
	assert (rInit == z3.unsat)

	S.push()

	bad_assume = bad
	bad_proofob = z3.simplify(z3.And(Msc.bad_sc(xsp)))
	trx = z3.simplify(z3.And([xsp[i]==Msc.tr[i] for i in range(len(xs))]))

	S.add(bad_assume)
	S.add(bad_proofob)
	S.add(trx)

	n = len(xsp) // 2
	while S.check() == z3.sat:
		m = S.model()
		xm1 = [m.eval(xsi) for xsi in xs[:n]]
		xm2 = [m.eval(xsi) for xsi in xs[n:]]
		bad1 = lambda xs: [z3.And(*[xi == xmi for (xi, xmi) in itertools.izip(xm1, xs)])]
		bad2 = lambda xs: [z3.And(*[xi == xmi for (xi, xmi) in itertools.izip(xm2, xs)])]

		(r1, vs1, inv1) = fixedpoint(M, bad1)
		if r1 == z3.unsat:
			sub1 = zip(vs1, xs[:n])
			sub2 = zip(vs1, xs[n:])
			p1 = z3.substitute(inv1, *sub1)
			p2 = z3.substitute(inv1, *sub2)
			S.add(p1)
			S.add(p2)
			print (p1, p2)
			continue
		(r2, vs2, inv2) = fixedpoint(M, bad2)
		if r2 == z3.unsat:
			sub1 = zip(vs2, xs[:n])
			sub2 = zip(vs2, xs[n:])
			p1 = z3.substitute(inv2, *sub1)
			p2 = z3.substitute(inv2, *sub2)
			S.add(p1)
			S.add(p2)
			print (p1, p2)
	S.pop()

def fixedpoint(M, bad):


if __name__ == '__main__':

	relationalInduction()
