from z3 import*

def get_length(ans):
	count = 0
	last _and = ans.arg(0).children()[-1]
    trace = last_and.children()[1]
    while trace.num_args() > 0:
		count = count + 1
		trace = trace.children()[-1]
	return count