#FAIL
AX EG ~state<1>

#PASS
EG ((~state<0>) & (~state<1>))

#PASS
EX EG (state<0> ^ state<1>)

#PASS
EF EG ((~state<0>) & state<1>)

