from ortools.sat.python import cp_model
import sys
import timeit

sets = []
time_limit_seconds = 1000000
def readData():
	global sets
	M = int(sys.stdin.readline())
	for _ in range(M):
		s = [int(x) for x in sys.stdin.readline().split()]
		sets.append(s)

	global time_limit_seconds
	time_limit_seconds = int(sys.stdin.readline())

readData()
n = 0
for s in sets:
	t = max(s)
	n = max(n,t)

res = []

def runCPSAT():
	# print("Solving HS instance using OR-tools and CpSolver with ", len(sets), " sets and n:", n, sep=' ', file=sys.stderr)

	model = cp_model.CpModel()

	node_vars = [ model.new_bool_var(f"{v}") for v in range(n) ]

	for zb in sets:
		cnst = [node_vars[v-1] for v in zb]
		# print("adding constraint", zb)
		model.add_at_least_one(cnst)

	weights = [1] * n
	expr = cp_model.LinearExpr.weighted_sum(node_vars, weights)
	model.minimize(expr)

	# model.minimize(sum(node_vars))


	solver = cp_model.CpSolver()
	solver.parameters.max_time_in_seconds = time_limit_seconds
	solver.parameters.num_workers = 3

	status = solver.solve(model)

	global res
	if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
		res = [i+1 for i in range(n) if solver.value(node_vars[i])]
	# else:
		# print("No solution found.")

# time_taken = timeit.timeit(stmt='runSAT()', globals=globals(), number=1)
time_taken = timeit.timeit(stmt='runCPSAT()', globals=globals(), number=1)


if len(res) != 0:
	print( 1000 * time_taken )
	print(len(res))
	for x in res:
		print( x, end=' ' )
else:
	print(0)
	print(0)