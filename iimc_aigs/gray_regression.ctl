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

#FAIL
AG (~p) & (~q) & (~r)

#PASS
AG true

#PASS
# never 1
AG ~((~p) & (~q) & r)

#PASS
# never 2
AG ~((~p) & q & (~r))

#PASS
# never 5
AG ~(p & (~q) & r)

#PASS
# never 6
AG ~(p & q & (~r))
