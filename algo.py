import z3
import struct
import itertools

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

	def __init__(self, model):

                self.model = model
		v1 = model.addSuffix('1')
		v2 = model.addSuffix('2')
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

def getLength2(ans):
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
	# print(xs)
	# print(xsp)

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

	bad_assume = bad                                                             #Shouldn't bad be a function defined over xs?
	bad_proofob = z3.simplify(z3.And(Msc.bad_sc(xsp)))
	trx = z3.simplify(z3.And([xsp[i]==Msc.tr[i] for i in range(len(xs))]))

	S.add(bad_assume)
	# print(bad_assume)
	# print(bad_proofob)
	S.add(bad_proofob)
	S.add(trx)

	n = len(xsp) // 2
	while S.check() == z3.sat:
                #print "Msc CounterExample Found"
                m = S.model()
		xm1 = [m.eval(xsi) for xsi in xs[:n]]
		xm2 = [m.eval(xsi) for xsi in xs[n:]]
		bad1 = lambda xs: [z3.And(*[xi == xmi for (xi, xmi) in itertools.izip(xm1, xs)])]
		bad2 = lambda xs: [z3.And(*[xi == xmi for (xi, xmi) in itertools.izip(xm2, xs)])]

		#r1, count1 = getLength(M, bad1)
                #no1 = bad1(M.variables)
                r1, arg1, expr1 = getLength1(M, bad1)
                
                if r1 == z3.unsat:
			#sub1 = zip(M.variables, xs[:n])
                        #sub2 = zip(M.variables, xs[n:])
                        sub1 = zip(arg1, xs[:n])
                        sub2 = zip(arg1, xs[n:])
                        #p1 = z3.substitute(*(no1 + sub1))
			#p2 = z3.substitute(*(no1 + sub2))
                        p1 = z3.substitute(expr1, *sub1)
			p2 = z3.substitute(expr1, *sub2)
                        #S.add(z3.Not(p1))
			#S.add(z3.Not(p2))
                        S.add(p1)
			S.add(p2)
			continue

		#r2, count2 = checkLength(M, bad2, arg1)                         # arg1 stores the value of length when r1 is sat
                no2 = bad2(M.variables)
                #r2, arg2, expr2 = checkLength1(M, bad2, arg1)
                r2, arg2, expr2 = checkLengthBMC(M, bad2, arg1)
                
                if r2 == z3.unsat:
                        #sub1 = zip(M.variables, xs[:n])
                        #sub2 = zip(M.variables, xs[n:])
                        sub1 = zip(arg2[:n], xs[:n])
                        sub2 = zip(arg2[n:], xs[n:])
                        #p1 = z3.substitute(*(no2 + sub1))
			#p2 = z3.substitute(*(no2 + sub2))
                        p1 = z3.substitute(expr2, sub1)
			p2 = z3.substitute(expr2, sub2)
			#S.add(z3.Not(p1))
			#S.add(z3.Not(p2))
                        S.add(p1)
			S.add(p2)
			continue

		print("UNSAFE")
		return

	print("SAFE")
	S.pop()

def getLength(M, bad):

        fp = z3.Fixedpoint()
	options = {'engine':'spacer'}
	fp.set(**options)

	xs = M.variables

	sorts = M.sorts + [z3.BoolSort()]
	inv = z3.Function('inv', *sorts)
	err = z3.Bool('err')

	fp.register_relation(inv)
	fp.register_relation(err.decl())
	fp.declare_var(*xs)

	fp.rule(inv(*xs), M.init)
	fp.rule(inv(*M.tr), inv(*xs))
	fp.rule(err, bad(xs) + [inv(*xs)])

	r = fp.query(err)
	if r == z3.unsat:
		return (z3.unsat, None)
	else:
                return (z3.sat, len(fp.get_answer().children()))

def checkLength(M, bad, count):

        fp = z3.Fixedpoint()
	options = {'engine': 'spacer'}
	fp.set(**options)

	addCounter(M)

	xs = M.variables
	
	sorts = M.sorts + [z3.BoolSort()]
	inv = z3.Function('inv', *sorts)
	err = z3.Bool('err')

	fp.register_relation(inv)
	fp.register_relation(err.decl())
	fp.declare_var(*xs)

	bad_state = [z3.And(bad(xs) + [xs[-1] == count])]

	fp.rule(inv(*xs), M.init)
	fp.rule(inv(*M.tr), inv(*xs))
	fp.rule(err, bad_state + [inv(*xs)])

	r = fp.query(err)
	if r == z3.unsat:
		return (z3.unsat, None)
	else:
                return (z3.sat, len(inv.children()))

def checkLengthBMC(M, bad, count):

        x = []
        for i in range(count):
                x.append(M.addSuffix(str(i)))

	bad = z3.simplify(z3.And(bad(x[-1])))
	init = z3.simplify(z3.And(M.initialize(x[0])))
	trx = True

        for i in range(count-1):
                temp = M.transition(x[i])
                temp = z3.And(*[xi == xpi for (xi, xpi) in itertools.izip(temp, x[i+1])])
                trx = z3.And(trx, temp)

	S = z3.Solver()
	S.add(init)
        S.add(trx)
        S.add(bad)
	rBMC = (S.check())

        if rBMC == z3.unsat:
                # Compute the interpolant
                formula1 = True
                formula2 = True
                xprime = []
                for i in range(count):
                        xprime.append(M.addSuffix(str(i)+"_prime"))
                formula1 = z3.And(init, trx)
                initprime = z3.simplify(z3.And(M.initialize(xprime[0])))
                trxprime = True

                for i in range(count-1):
                        temp = M.transition(xprime[i])
                        temp = z3.And(*[xi == xpi for (xi, xpi) in itertools.izip(temp, xprime[i+1])])
                        trxprime = z3.And(trxprime, temp)

                formula1 = z3.And(formula1, initprime, trxprime)

                # xval are the exact values that consecutive states of M take
                xval = [[0, 1]]                                                   
                temp = True
                
                for i in range(count-1):
                        xval.append(M.transition(x[i]))

                for i in range(1, count):
                        temp = z3.And(temp, *[xi == xvi for (xi, xvi) in itertools.izip(x[i], xval[i])])

                formula1 = z3.And(formula1, temp)
                
                Msc = SelfComposedTransitionSystem(M)
                formula2 = z3.simplify(z3.And(Msc.bad_sc(x[count-1]+xprime[count-1])))

                return z3.unsat, x[count-1]+xprime[count-1], z3.mk_interpolant(formula1, formula2)
                
        return rBMC, None, None
        
def getLength1(M, bad):

        fp = z3.Fixedpoint()
	options = {'engine':'spacer'}
	fp.set(**options)

	Mp = TransitionSystem('prime')
	# addCounter(M)
	# addCounter(Mp)
	xs = M.variables
	xsp = Mp.variables
	trx = [xsp[i]==M.tr[i] for i in range(len(xs))]

	sorts = M.sorts + [z3.BoolSort()]
	inv = z3.Function('inv', *sorts)
	err = z3.Function('err', z3.BoolSort())

	fp.register_relation(inv)
	fp.register_relation(err)
	for x in xs + xsp:
		fp.declare_var(x)

	inv_xs = inv(*xs)
	inv_xsp = inv(*xsp)

	fp.rule(inv_xs, M.init)
	fp.rule(inv_xsp, trx + [inv_xs])
	fp.rule(err(), bad(xs) + [inv_xs])

	r = fp.query(err) == z3.unsat
	if r:
		inv = fp.get_answer()
                print("INV:")
		print(inv)
		assert inv.is_forall()
		body = inv.body()
		assert z3.is_eq(body)
		print("BODY:", body)
		fapp = body.arg(0)
		assert (z3.is_app(fapp))
		args = [fapp.arg(i) for i in range(body.num_args())]
		assert len(args) == len(xs)
		expr = (body.arg(1))
		print(z3.unsat, args, expr)
		return (z3.unsat, args, expr)
	else:
                return (z3.sat, len(fp.get_answer().children()), None)             # Are you sure this is the correct length?

def checkLength1(M, bad, count):

        fp = z3.Fixedpoint()
	options = {'engine': 'spacer'}
	fp.set(**options)

	addCounter(M)

	xs = M.variables
	
	sorts = M.sorts + [z3.BoolSort()]
	inv = z3.Function('inv', *sorts)
	err = z3.Bool('err')

	fp.register_relation(inv)
	fp.register_relation(err.decl())
	fp.declare_var(*xs)

	bad_state = [z3.And(bad(xs) + [xs[-1] == count])]

	fp.rule(inv(*xs), M.init)
	fp.rule(inv(*M.tr), inv(*xs))
	fp.rule(err, bad_state + [inv(*xs)])

	r = fp.query(err)
	if r == z3.unsat:
                inv = fp.get_answer()
                print("INV:")
		print(inv)
		assert inv.is_forall()
		body = inv.body()
		assert z3.is_eq(body)
		print("BODY:", body)
		fapp = body.arg(0)
		assert (z3.is_app(fapp))
		args = [fapp.arg(i) for i in range(body.num_args())]
		assert len(args) == len(xs)
		expr = (body.arg(1))
		print(z3.unsat, args, expr)
		return (z3.unsat, args, expr)
	else:
		return (z3.sat, len(inv.children()), None)
        
if __name__ == '__main__':

	relationalInduction()
