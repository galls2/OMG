#FAIL
AG ((~state<0>) & (~state<1>))

#PASS
AG ~(state<0> & state<1>)

#FAIL
AG state<0> | state<1>
