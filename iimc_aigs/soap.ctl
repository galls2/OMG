#PASS: (0-9) Showering only takes one clock cycle.
AG(GA.condition<1> & ~GA.condition<0> -> AX(~GA.condition<1> & ~GA.condition<0>))
AG(GB.condition<1> & ~GB.condition<0> -> AX(~GB.condition<1> & ~GB.condition<0>))
AG(GC.condition<1> & ~GC.condition<0> -> AX(~GC.condition<1> & ~GC.condition<0>))
AG(GD.condition<1> & ~GD.condition<0> -> AX(~GD.condition<1> & ~GD.condition<0>))
AG(GE.condition<1> & ~GE.condition<0> -> AX(~GE.condition<1> & ~GE.condition<0>))
AG(GF.condition<1> & ~GF.condition<0> -> AX(~GF.condition<1> & ~GF.condition<0>))
AG(GG.condition<1> & ~GG.condition<0> -> AX(~GG.condition<1> & ~GG.condition<0>))
AG(GH.condition<1> & ~GH.condition<0> -> AX(~GH.condition<1> & ~GH.condition<0>))
AG(GI.condition<1> & ~GI.condition<0> -> AX(~GI.condition<1> & ~GI.condition<0>))
AG(GJ.condition<1> & ~GJ.condition<0> -> AX(~GJ.condition<1> & ~GJ.condition<0>))

#PASS: (10-19) No showering unless dirty.
~EF((GA.condition<1> | ~GA.condition<0>) & EX(GA.condition<1> & ~GA.condition<0>))
~EF((GB.condition<1> | ~GB.condition<0>) & EX(GB.condition<1> & ~GB.condition<0>))
~EF((GC.condition<1> | ~GC.condition<0>) & EX(GC.condition<1> & ~GC.condition<0>))
~EF((GD.condition<1> | ~GD.condition<0>) & EX(GD.condition<1> & ~GD.condition<0>))
~EF((GE.condition<1> | ~GE.condition<0>) & EX(GE.condition<1> & ~GE.condition<0>))
~EF((GF.condition<1> | ~GF.condition<0>) & EX(GF.condition<1> & ~GF.condition<0>))
~EF((GG.condition<1> | ~GG.condition<0>) & EX(GG.condition<1> & ~GG.condition<0>))
~EF((GH.condition<1> | ~GH.condition<0>) & EX(GH.condition<1> & ~GH.condition<0>))
~EF((GI.condition<1> | ~GI.condition<0>) & EX(GI.condition<1> & ~GI.condition<0>))
~EF((GJ.condition<1> | ~GJ.condition<0>) & EX(GJ.condition<1> & ~GJ.condition<0>))

#PASS: (20-29) It is always possible for a guest to get dirty.
AG EF(~GA.condition<1> & GA.condition<0>)
AG EF(~GB.condition<1> & GB.condition<0>)
AG EF(~GC.condition<1> & GC.condition<0>)
AG EF(~GD.condition<1> & GD.condition<0>)
AG EF(~GE.condition<1> & GE.condition<0>)
AG EF(~GF.condition<1> & GF.condition<0>)
AG EF(~GG.condition<1> & GG.condition<0>)
AG EF(~GH.condition<1> & GH.condition<0>)
AG EF(~GI.condition<1> & GI.condition<0>)
AG EF(~GJ.condition<1> & GJ.condition<0>)

#PASS: (30-39) If a guest ever gets dirty, eventually he/she will return clean.
AG((~GA.condition<1> & GA.condition<0>) -> AF(~GA.condition<1> & ~GA.condition<0>))
AG((~GB.condition<1> & GB.condition<0>) -> AF(~GB.condition<1> & ~GB.condition<0>))
AG((~GC.condition<1> & GC.condition<0>) -> AF(~GC.condition<1> & ~GC.condition<0>))
AG((~GD.condition<1> & GD.condition<0>) -> AF(~GD.condition<1> & ~GD.condition<0>))
AG((~GE.condition<1> & GE.condition<0>) -> AF(~GE.condition<1> & ~GE.condition<0>))
AG((~GF.condition<1> & GF.condition<0>) -> AF(~GF.condition<1> & ~GF.condition<0>))
AG((~GG.condition<1> & GG.condition<0>) -> AF(~GG.condition<1> & ~GG.condition<0>))
AG((~GH.condition<1> & GH.condition<0>) -> AF(~GH.condition<1> & ~GH.condition<0>))
AG((~GI.condition<1> & GI.condition<0>) -> AF(~GI.condition<1> & ~GI.condition<0>))
AG((~GJ.condition<1> & GJ.condition<0>) -> AF(~GJ.condition<1> & ~GJ.condition<0>))
