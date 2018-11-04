import z3
import struct

class TransitionSystem(object):

	def __init__(self, suffix = ''):
		
		if suffix != '':
			s = '_' + suffix
		else:
			s = ''
		xs = [z3.Int('x' + s), z3.Int('y' + s)]

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

	# def sorts(self):
	# 	return [z3.IntSort(), z3.IntSort()]

	def initialize(self, xs):
	    "Init(x, y) = (x == 0 && y == 1)"
	    return [xs[0] == 0, xs[1] == 1]

	def transition(self, xs):
	    "Tr(x, y, x', y') = (x' == x + 1 && y' == x + y)"
	    return [xs[0] + 1,
	            xs[0] + xs[1]]

	# def bad(self, xs):
	# 	return [xs[0] > xs[1]]

class SelfComposedTransitionSystem(object):

	def __init__(self, model, suffix = ''):
		self.model = model
		v1 = model.addSuffix('1' + suffix)
		v2 = model.addSuffix('2' + suffix)
		self.variables = v1 + v2
		self.sorts = model.sorts + model.sorts
		self.init = model.initialize(v1) + model.initialize(v2)
		self.tr =  model.transition(v1) + model.transition(v2)
		self.bad = [z3.And(v1[0] == v2[0], v1[1] != v2[1])]

	# def variables(self, suffix = ''):
	#     v1 = self.M.variables('_1' + suffix)
	#     v2 = self.M.variables('_2' + suffix)
	#     return v1 + v2

	# def sorts(self):
	# 	return self.M.sorts() + self.M.sorts()

	# def init(self, xs):
	#     m = len(xs) // 2
	#     xs1 = xs[:m]
	#     xs2 = xs[m:]
	#     return self.M.init(xs1) + self.M.init(xs2)

	# def tr(self, xs):
	#     m = len(xs) // 2
	#     xs1  = xs[:m]
	#     xs2  = xs[m:]
	#     return self.M.tr(xs1) + self.M.tr(xs2)

	# def bad_sc(self, xs):
	# 	return [z3.And(xs[0] == xs[2], xs[1] != xs[3])]

def getLength(ans):
	count = 0
	last_and = ans.arg(0).children()[-1]
	trace = last_and.children()[1]
	while trace.num_args() > 0:
		count = count + 1
		trace = trace.children()[-1]
	return count

def addCounter(M):
	M.variables

if __name__ == '__main__':
	M = TransitionSystem()
	# print(vars(M))
	Msc = SelfComposedTransitionSystem(M)
	# print(vars(Msc))

	
