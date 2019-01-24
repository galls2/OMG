#PASS
EX state<0> & ~state<1>

#PASS
EX ~state<0> & ~state<1>

#PASS REDUNDANT
EX state<0> | state<1>

#FAIL
EX state<0> & state<1>

#FAIL
EX (~state<0>) & state<1>

#FAIL
EX state<1>

#PASS
EX EX ((~state<0>) & state<1>)

#PASS
EX ((EX ((~state<0>) & state<1>)) | (EX (state<0> & state<1>)))

#PASS
EX EX ((~state<0>) & state<1>)

#PASS    IF YOU REMOVE THE SECOND CLAUSE THEN THE NEXT TAKES LONGER
EX ((EX ((~state<0>) & state<1>)) | (EX (state<0> & state<1>)))

#FAIL
EX EX (state<0> & state<1>)

#FAIL
EX EX EX (state<0> & state<1>)

