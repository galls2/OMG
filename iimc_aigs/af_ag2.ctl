#PASS
(EX state<0> & ~state<1>)

#PASS
(EX ~state<0> & ~state<1>)

#PASS REDUNDANT
(EX state<0> | state<1>)
