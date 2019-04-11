# Self-Composition-using-z3

Steps to execute in the code -

1. Represent Model M
2. Create copy M' of M
3. Self-compose M to get Msc
4. Find a pair (Xsc, Xsc') in Msc such that Xsc' is a bad state (Normal SMT Query satisfying Bad(Xsc') && Relation(Xsc, Xsc'))
5. From Xsc, find Xm and check if Xm is reachable in M (PDR Query). If it is reachable, let the length of the trace be Lm.
6. From Xsc, find Xm' and check if Xm' is reachable in M' with a length of Lm (Bounded Model Checking). If it is reachable, then we have a counterexample.
7. Otherwise, Add conditions to SMT query to ensure it doesn't appear again.