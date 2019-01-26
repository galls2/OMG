#PASS: (0)
#p must go to 1 for r to go to 1
((~q) & (~r)) -> ~E (~p) U r

#FAIL
AG (~p) & (~q) & (~r)

#FAIL
AG ~p

#FAIL
AG ~q

#FAIL
AG ~r
