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

#PASS
AG EX p

