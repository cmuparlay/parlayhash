 --------------------------- MODULE MCTracking_proofs ---------------------------
(***************************************************************************
 This module contains proofs of _ 
 ***************************************************************************)
EXTENDS MCTracking, Assumptions, 
        SequenceTheorems, FiniteSetTheorems, TLAPS

\* LinInit = Init => (S = {[state |-> [k \in KeyDomain |-> NULL],
\*                          op    |-> [p \in ProcSet   |-> BOT],
\*                          arg   |-> [p \in ProcSet   |-> BOT],
\*                          res   |-> [p \in ProcSet   |-> BOT]]})
THEOREM LinInit
  <1> DEFINE m0 == [state |-> [k \in KeyDomain |-> NULL],
                    op    |-> [p \in ProcSet   |-> BOT],
                    arg   |-> [p \in ProcSet   |-> BOT],
                    res   |-> [p \in ProcSet   |-> BOT]]
  <1> SUFFICES ASSUME Init PROVE /\ m0 \in S
                                 /\ \A c \in S : c = m0
    OBVIOUS
  <1>1. m0 \in S
    <2>1. m0 \in ConfigDomain
      BY DEF ConfigDomain, StateDomain, OpDomain, ArgDomain, ResDomain
    <2>2. m0.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
      <3> SUFFICES ASSUME NEW k \in KeyDomain
                   PROVE  ~KeyInBktAtAddr(k, A[Hash[k]])
        OBVIOUS
      <3> QED
        BY HashDef DEF KeyInBktAtAddr, Init
    <2>3. \A p \in ProcSet : pc[p] = RemainderID
      BY DEF Init
    <2> SUFFICES \A p \in ProcSet : m0.op[p] = BOT /\ m0.arg[p] = BOT /\ m0.res[p] = BOT
      BY <2>1, <2>2, <2>3, RemDef, Zenon DEF S
    <2> QED
      OBVIOUS
  <1>2. ASSUME NEW c \in S PROVE c = m0
    <2> USE <1>2
    <2>1. c.state = [k \in KeyDomain |-> NULL]
      BY HashDef DEF KeyInBktAtAddr, Init, S
    <2>2. c.op = [p \in ProcSet   |-> BOT]
      BY RemDef, Zenon DEF S, Init, ConfigDomain
    <2>3. c.arg = [p \in ProcSet  |-> BOT]
      BY RemDef, Zenon DEF S, Init, ConfigDomain
    <2>4. c.res = [p \in ProcSet  |-> BOT]
      BY RemDef, Zenon DEF S, Init, ConfigDomain
    <2>5. c \in ConfigDomain
      BY DEF S
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF ConfigDomain
  <1> QED  
    BY <1>1, <1>2

\* LinSNE = TypeOK => S # {}
THEOREM LinSNE
  <1> SUFFICES ASSUME TypeOK
               PROVE  \E c \in ConfigDomain : c \in S
    BY Zenon DEF S
  <1> USE DEF TypeOK
  <1> DEFINE op == [p \in ProcSet |-> CASE pc[p] = RemainderID -> BOT
                                        [] pc[p] \in {"F1", "F2", "F3"} -> "Find"
                                        [] pc[p] \in {"I1", "I2", "I3", "I4", "I5"} -> "Insert"
                                        [] pc[p] \in {"U1", "U2", "U3", "U4", "U5"} -> "Upsert"
                                        [] pc[p] \in {"R1", "R2", "R3", "R4", "R5"} -> "Remove"]
  <1>1. op \in [ProcSet -> OpDomain]
    BY DEF OpDomain, LineIDs
  <1> DEFINE carg == [p \in ProcSet |-> IF pc[p] = RemainderID THEN BOT ELSE arg[p]]
  <1>2. carg \in [ProcSet -> ArgDomain]
    BY DEF OpDomain, LineIDs, ArgDomain
  <1> DEFINE state == [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
  <1>3. state \in StateDomain
    <2> SUFFICES ASSUME NEW k \in KeyDomain,
                        KeyInBktAtAddr(k, A[Hash[k]])
                 PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]]) \in ValDomain
      BY DEF StateDomain
    <2>1. A[Hash[k]] \in AllocAddrs
      BY HashDef DEF KeyInBktAtAddr
    <2>2. PICK idx \in 1..Len(MemLocs[A[Hash[k]]]) : MemLocs[A[Hash[k]]][idx].key = k
      BY DEF KeyInBktAtAddr
    <2>3. idx = CHOOSE index \in 1..Len(MemLocs[A[Hash[k]]]) : MemLocs[A[Hash[k]]][index].key = k
      BY <2>2 
    <2>4. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = MemLocs[A[Hash[k]]][idx].val
      BY <2>3, Zenon DEF ValOfKeyInBktAtAddr
    <2>5. MemLocs[A[Hash[k]]] \in Seq([key: KeyDomain, val: ValDomain])
      BY <2>1, Zenon
    <2>6. MemLocs[A[Hash[k]]][idx] \in [key: KeyDomain, val: ValDomain]
      BY <2>2, <2>5, ElementOfSeq, Zenon
    <2>7. MemLocs[A[Hash[k]]][idx].val \in ValDomain
      BY <2>6
    <2> QED
      BY <2>4, <2>7
  <1> DEFINE res == 
        [p \in ProcSet |->
           CASE pc[p] = RemainderID 
                -> BOT
             [] pc[p] = "F1"        
                -> BOT
             [] pc[p] = "F2" /\ KeyInBktAtAddr(arg[p].key, bucket[p])
                -> ValOfKeyInBktAtAddr(arg[p].key, bucket[p])
             [] pc[p] = "F2" /\ ~KeyInBktAtAddr(arg[p].key, bucket[p])
                -> NULL
             [] pc[p] = "F3"
                -> r[p]
             [] pc[p] \in {"I1", "I3", "I4"}   
                -> BOT
             [] pc[p] = "I2" /\ KeyInBktAtAddr(arg[p].key, bucket[p])
                -> ValOfKeyInBktAtAddr(arg[p].key, bucket[p])
             [] pc[p] = "I2" /\ ~KeyInBktAtAddr(arg[p].key, bucket[p])
                -> BOT
             [] pc[p] = "I5"
                -> r[p]
             [] pc[p] \in {"U1", "U2", "U3", "U4"}
                -> BOT
             [] pc[p] = "U5"
                -> r[p]
             [] pc[p] \in {"R1", "R3", "R4"}        
                -> BOT
             [] pc[p] = "R2" /\ KeyInBktAtAddr(arg[p].key, bucket[p])
                -> BOT
             [] pc[p] = "R2" /\ ~KeyInBktAtAddr(arg[p].key, bucket[p])
                -> NULL
             [] pc[p] = "R5"
                -> r[p]]
  <1>4. res \in [ProcSet -> ResDomain]
    <2> SUFFICES ASSUME NEW p \in ProcSet
                 PROVE  res[p] \in ResDomain
      BY Zenon
    <2> USE RemDef
    <2>1. CASE pc[p] = RemainderID
      BY <2>1 DEF ResDomain
    <2>2. CASE pc[p] = "F1"
      BY <2>2 DEF ResDomain
    <2>3. CASE pc[p] = "F2" /\ KeyInBktAtAddr(arg[p].key, bucket[p])
      <3> SUFFICES ValOfKeyInBktAtAddr(arg[p].key, bucket[p]) \in ValDomain
        BY <2>3 DEF ResDomain
      <3>1. PICK idx \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][idx].key = arg[p].key
        BY Zenon, <2>3 DEF KeyInBktAtAddr
      <3>2. ValOfKeyInBktAtAddr(arg[p].key, bucket[p]) = 
            MemLocs[bucket[p]][CHOOSE index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key = arg[p].key].val
        BY Zenon DEF ValOfKeyInBktAtAddr
      <3>3. idx = CHOOSE index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key = arg[p].key
        BY <3>1
      <3>4. ValOfKeyInBktAtAddr(arg[p].key, bucket[p]) = MemLocs[bucket[p]][idx].val
        BY <3>2, <3>3, Zenon
      <3>5. MemLocs[bucket[p]] \in Seq([key: KeyDomain, val: ValDomain])
        BY <2>3, Zenon DEF KeyInBktAtAddr
      <3>6. MemLocs[bucket[p]][idx] \in [key: KeyDomain, val: ValDomain]
        BY <3>1, <3>5, ElementOfSeq, Zenon
      <3>7. MemLocs[bucket[p]][idx].val \in ValDomain
        BY <3>6
      <3>8. ValOfKeyInBktAtAddr(arg[p].key, bucket[p]) \in ValDomain
        BY <3>4, <3>7
      <3> QED
        BY <2>3, <3>8
    <2>4. CASE pc[p] = "F2" /\ ~KeyInBktAtAddr(arg[p].key, bucket[p])
      BY <2>4 DEF ResDomain
    <2>5. CASE pc[p] = "F3"
      BY <2>5 DEF ResDomain
    <2>6. CASE pc[p] \in {"I1", "I3", "I4"}
      BY <2>6 DEF ResDomain
    <2>7. CASE pc[p] = "I2" /\ KeyInBktAtAddr(arg[p].key, bucket[p])
      <3> SUFFICES ValOfKeyInBktAtAddr(arg[p].key, bucket[p]) \in ValDomain
        BY <2>7 DEF ResDomain
      <3>1. PICK idx \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][idx].key = arg[p].key
        BY Zenon, <2>7 DEF KeyInBktAtAddr
      <3>2. ValOfKeyInBktAtAddr(arg[p].key, bucket[p]) = 
            MemLocs[bucket[p]][CHOOSE index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key = arg[p].key].val
        BY Zenon DEF ValOfKeyInBktAtAddr
      <3>3. idx = CHOOSE index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key = arg[p].key
        BY <3>1
      <3>4. ValOfKeyInBktAtAddr(arg[p].key, bucket[p]) = MemLocs[bucket[p]][idx].val
        BY <3>2, <3>3, Zenon
      <3>5. MemLocs[bucket[p]] \in Seq([key: KeyDomain, val: ValDomain])
        BY <2>7, Zenon DEF KeyInBktAtAddr
      <3>6. MemLocs[bucket[p]][idx] \in [key: KeyDomain, val: ValDomain]
        BY <3>1, <3>5, ElementOfSeq, Zenon
      <3>7. MemLocs[bucket[p]][idx].val \in ValDomain
        BY <3>6
      <3>8. ValOfKeyInBktAtAddr(arg[p].key, bucket[p]) \in ValDomain
        BY <3>4, <3>7
      <3> QED
        BY <2>7, <3>8
    <2>8. CASE pc[p] = "I2" /\ ~KeyInBktAtAddr(arg[p].key, bucket[p])
      BY <2>8 DEF ResDomain
    <2>9. CASE pc[p] = "I5"
      BY <2>9 DEF ResDomain
    <2>10. CASE pc[p] \in {"U1", "U2", "U3", "U4"}
      BY <2>10 DEF ResDomain
    <2>11. CASE pc[p] = "U5"
      BY <2>11 DEF ResDomain
    <2>12. CASE pc[p] \in {"R1", "R3", "R4"}
      BY <2>12 DEF ResDomain
    <2>13. CASE pc[p] = "R2" /\ KeyInBktAtAddr(arg[p].key, bucket[p])
      BY <2>13 DEF ResDomain
    <2>14. CASE pc[p] = "R2" /\ ~KeyInBktAtAddr(arg[p].key, bucket[p])
      BY <2>14 DEF ResDomain
    <2>15. CASE pc[p] = "R5"
      BY <2>15 DEF ResDomain
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, 
         <2>10, <2>11, <2>12, <2>13, <2>14, <2>15, Zenon DEF LineIDs
  <1> DEFINE c == [state |-> state, op |-> op, arg |-> carg, res |-> res]
  <1>5. c \in ConfigDomain
    BY <1>1, <1>2, <1>3, <1>4, Zenon DEF ConfigDomain
  <1>6. ASSUME NEW q \in ProcSet
          PROVE
            CASE pc[q] = RemainderID 
                  -> (c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT)
               [] pc[q] = "F1"
                  -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
               [] pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
               [] pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL)
               [] pc[q] = "F3"
                  -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
               [] pc[q] \in {"I1", "I3", "I4"}
                  -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
               [] pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
               [] pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
               [] pc[q] = "I5"
                  -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
               [] pc[q] \in {"U1", "U2", "U3", "U4"}
                  -> (c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
               [] pc[q] = "U5"
                  -> (c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
               [] pc[q] \in {"R1", "R3", "R4"}
                  -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
               [] pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
               [] pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL)
               [] pc[q] = "R5"
                  -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
    <2> USE <1>6, RemDef
    <2>1. CASE pc[q] = RemainderID
      BY <2>1, Zenon
    <2>2. CASE pc[q] = "F1"
      BY <2>2, Zenon
    <2>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
      BY <2>3, Zenon
    <2>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
      BY <2>4, Zenon
    <2>5. CASE pc[q] = "F3"
      BY <2>5, Zenon
    <2>6. CASE pc[q] \in {"I1", "I3", "I4"}
      BY <2>6, Zenon
    <2>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
      BY <2>7, Zenon
    <2>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
      BY <2>8, Zenon
    <2>9. CASE pc[q] = "I5"
      BY <2>9, Zenon
    <2>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
      BY <2>10, Zenon
    <2>11. CASE pc[q] = "U5"
      BY <2>11, Zenon
    <2>12. CASE pc[q] \in {"R1", "R3", "R4"}
      BY <2>12, Zenon
    <2>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
      BY <2>13, Zenon
    <2>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
      BY <2>14, Zenon
    <2>15. CASE pc[q] = "R5"
      BY <2>15, Zenon
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, 
         <2>10, <2>11, <2>12, <2>13, <2>14, <2>15, ZenonT(120) DEF LineIDs
  <1>7. c \in S
    BY <1>5, <1>6, Zenon DEF S
  <1> QED
    BY <1>5, <1>7, Zenon

\* LinSingleton = TypeOK => Cardinality(S) = 1
THEOREM LinSingleton
  <1> SUFFICES ASSUME TypeOK
               PROVE  Cardinality(S) = 1
    OBVIOUS
  <1>1. ASSUME NEW c1 \in S, NEW c2 \in S
        PROVE  c1 = c2
    <2> USE <1>1
    <2> c1 \in ConfigDomain /\ c2 \in ConfigDomain
      BY DEF S
    <2> SUFFICES /\ c1.state = c2.state
                 /\ c1.op = c2.op
                 /\ c1.arg = c2.arg
                 /\ c1.res = c2.res
      BY DEF ConfigDomain
    <2>1. c1.state = c2.state
      BY DEF S
    <2>2. /\ c1.op = c2.op
          /\ c1.arg = c2.arg
          /\ c1.res = c2.res
      <3> SUFFICES ASSUME NEW p \in ProcSet
                   PROVE  /\ c1.op[p] = c2.op[p]
                          /\ c1.arg[p] = c2.arg[p]
                          /\ c1.res[p] = c2.res[p]
        BY DEF ConfigDomain
      <3> USE RemDef
      <3>1. CASE pc[p] = RemainderID
        BY <3>1, Zenon DEF S
      <3>2. CASE pc[p] \in {"F1", "F2", "F3"}
        BY <3>2, Zenon DEF S
      <3>3. CASE pc[p] \in {"I1", "I2", "I3", "I4", "I5"}
        BY <3>3, Zenon DEF S
      <3>4. CASE pc[p] \in {"U1", "U2", "U3", "U4", "U5"}
        BY <3>4, Zenon DEF S
      <3>5. CASE pc[p] \in {"R1", "R2", "R3", "R4", "R5"}
        BY <3>5, Zenon DEF S
      <3> QED
        BY <3>1, <3>2, <3>3, <3>4, <3>5 DEF LineIDs, Inv, TypeOK
    <2> QED
      BY <2>1, <2>2
  <1>2. PICK c \in S : TRUE
    BY LinSNE 
  <1>3. S = {c}
    BY <1>1, <1>2
  <1>4. Cardinality(S) = 1
    BY <1>3, FS_Singleton, Zenon
  <1> QED
    BY <1>4

\* UniqueInvoker = TypeOK => (\A q \in ProcSet : InvokeLine(q) => q = InvokerProc)
LEMMA UniqueInvoker
  <1> SUFFICES ASSUME NEW p1 \in ProcSet, InvokeLine(p1),
                      NEW p2 \in ProcSet, InvokeLine(p2), 
                      TypeOK, p1 # p2
               PROVE  FALSE
    BY DEF InvokerProc
  <1>1. pc[p1] = RemainderID
    BY DEF InvokeLine
  <1>2. pc'[p1] # RemainderID
    BY Zenon, RemDef DEF InvokeLine, TypeOK, OpNames, OpToInvocLine
  <1>3. \A q \in ProcSet : q # p2 => pc[q] = pc'[q]
    BY DEF InvokeLine
  <1> QED
    BY <1>1, <1>2, <1>3 

\* UniqueReturner = TypeOK => (\A q \in ProcSet : (\E LineAction \in RetLines(q) : LineAction) => q = ReturnProc)
LEMMA UniqueReturner
  <1> SUFFICES ASSUME TypeOK,
                      NEW p1 \in ProcSet,
                      NEW LA1 \in RetLines(p1), LA1,
                      NEW p2 \in ProcSet,
                      NEW LA2 \in RetLines(p2), LA2,
                      p1 # p2
               PROVE  FALSE
    BY Zenon DEF ReturnProc
  <1>1. pc[p1] # RemainderID
    BY RemDef DEF RetLines, F3, I5, U5, R5
  <1>2. pc'[p1] = RemainderID
    BY DEF RetLines, F3, I5, U5, R5, TypeOK
  <1>3. \A q \in ProcSet : q # p2 => pc[q] = pc'[q]
    BY DEF RetLines, F3, I5, U5, R5, TypeOK
  <1> QED
    BY <1>1, <1>2, <1>3

\* LinIntermediateLine = Inv /\ IntermAction => S' \in SUBSET Evolve(S)
THEOREM LinIntermediateLine
  <1> SUFFICES ASSUME Inv,
                      NEW p \in ProcSet,
                      NEW LineAction \in IntLines(p),
                      LineAction
               PROVE  S' \in SUBSET Evolve(S)
    BY Zenon DEF IntermAction
  <1>1. CASE LineAction \in {F1(p), F2(p)}
    BY <1>1, Zenon, LinIntermediateLine_Find
  <1>2. CASE LineAction \in {I1(p), I2(p), I3(p), I4(p)}
    BY <1>2, Zenon, LinIntermediateLine_Insert
  <1>3. CASE LineAction \in {U1(p), U2(p), U3(p), U4(p)}
    BY <1>3, Zenon, LinIntermediateLine_Upsert
  <1>4. CASE LineAction \in {R1(p), R2(p), R3(p), R4(p)}
    BY <1>4, Zenon, LinIntermediateLine_Remove
  <1> QED
    BY <1>1, <1>2, <1>3, <1>4, Zenon DEF IntLines
              

\* StrongLinearizability = Spec => [][/\ IntermAction => S' \in SUBSET Evolve(S)
\*                                    /\ InvocnAction => S' \in SUBSET Evolve(Invoke(S, InvokerProc, LineIDtoOp(pc'[InvokerProc]), arg'[InvokerProc]))
\*                                    /\ ReturnAction => S' \in SUBSET Filter(Evolve(S), ReturnProc, ret'[ReturnProc])
\*                                    /\ Cardinality(S) = 1]_vars
THEOREM StrongLinearizability 
  <1>1. Spec => [][Inv]_vars
    BY SpecInv, PTL
  <1>2. Inv => /\ IntermAction => S' \in SUBSET Evolve(S)
               /\ InvocnAction => S' \in SUBSET Evolve(Invoke(S, InvokerProc, LineIDtoOp(pc'[InvokerProc]), arg'[InvokerProc]))
               /\ ReturnAction => S' \in SUBSET Filter(Evolve(S), ReturnProc, ret'[ReturnProc])
               /\ Cardinality(S) = 1
    BY LinIntermediateLine, LinInvocationLine, LinReturnLine, LinSingleton DEF Inv
  <1>3. QED
    BY <1>1, <1>2, PTL

======================================================================================