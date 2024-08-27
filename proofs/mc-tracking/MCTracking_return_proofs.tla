--------------------------- MODULE MCTracking_return_proofs ---------------------------
(***************************************************************************
 This module contains the proof of LinReturnLine from MCTracking.tla
 ***************************************************************************)
EXTENDS MCTracking, Assumptions, 
        SequenceTheorems, FiniteSetTheorems, TLAPS

\* S' - i.e. S in the next configuration
\* Used to define useful rewriting rule           
SPrime == 
     {c \in ConfigDomain :
        /\ c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' 
                                             THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' 
                                             ELSE NULL]
        /\ \A p \in ProcSet :
           CASE pc'[p] = RemainderID
                -> (c.op[p] = BOT /\ c.arg[p] = BOT /\ c.res[p] = BOT)
             [] pc'[p] = "F1"
                -> (c.op[p] = "Find" /\ c.arg[p] = arg'[p] /\ c.res[p] = BOT)
             [] pc'[p] = "F2" /\ KeyInBktAtAddr(arg[p].key, bucket[p])'
                -> (c.op[p] = "Find" /\ c.arg[p] = arg'[p] /\ c.res[p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p])')
             [] pc'[p] = "F2" /\ ~KeyInBktAtAddr(arg[p].key, bucket[p])'
                -> (c.op[p] = "Find" /\ c.arg[p] = arg'[p] /\ c.res[p] = NULL)
             [] pc'[p] = "F3"
                -> (c.op[p] = "Find" /\ c.arg[p] = arg'[p] /\ c.res[p] = r'[p])
             [] pc'[p] \in {"I1", "I3", "I4"}
                -> (c.op[p] = "Insert" /\ c.arg[p] = arg'[p] /\ c.res[p] = BOT)
             [] pc'[p] = "I2" /\ KeyInBktAtAddr(arg[p].key, bucket[p])'
                -> (c.op[p] = "Insert" /\ c.arg[p] = arg'[p] /\ c.res[p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p])')
             [] pc'[p] = "I2" /\ ~KeyInBktAtAddr(arg[p].key, bucket[p])'
                -> (c.op[p] = "Insert" /\ c.arg[p] = arg'[p] /\ c.res[p] = BOT)
             [] pc'[p] = "I5"
                -> (c.op[p] = "Insert" /\ c.arg[p] = arg'[p] /\ c.res[p] = r'[p])
             [] pc'[p] \in {"U1", "U2", "U3", "U4"}
                -> (c.op[p] = "Upsert" /\ c.arg[p] = arg'[p] /\ c.res[p] = BOT)
             [] pc'[p] = "U5"
                -> (c.op[p] = "Upsert" /\ c.arg[p] = arg'[p] /\ c.res[p] = r'[p])
             [] pc'[p] \in {"R1", "R3", "R4"}
                -> (c.op[p] = "Remove" /\ c.arg[p] = arg'[p] /\ c.res[p] = BOT)
             [] pc'[p] = "R2" /\ KeyInBktAtAddr(arg[p].key, bucket[p])'
                -> (c.op[p] = "Remove" /\ c.arg[p] = arg'[p] /\ c.res[p] = BOT)
             [] pc'[p] = "R2" /\ ~KeyInBktAtAddr(arg[p].key, bucket[p])'
                -> (c.op[p] = "Remove" /\ c.arg[p] = arg'[p] /\ c.res[p] = NULL)
             [] pc'[p] = "R5"
                -> (c.op[p] = "Remove" /\ c.arg[p] = arg'[p] /\ c.res[p] = r'[p])}

\* S' rewriting rule
LEMMA SPrimeRewrite == S' = SPrime
  BY ZenonT(120) DEF S, SPrime

\* LinReturnLine = 
\*   Inv /\ ReturnAction => S' \in SUBSET Filter(Evolve(S), ReturnProc, ret'[ReturnProc])
THEOREM LinReturnLine
  <1> SUFFICES ASSUME Inv,
                      NEW p \in ProcSet,
                      NEW LineAction \in RetLines(p),
                      LineAction
               PROVE  S' \in SUBSET Filter(Evolve(S), ReturnProc, ret'[ReturnProc])
    BY Zenon DEF ReturnAction
  <1> SUFFICES S' \in SUBSET Filter(Evolve(S), p, ret'[p])
    BY UniqueReturner, Zenon DEF Inv
  <1> SUFFICES ASSUME NEW c \in ConfigDomain,
                      c \in S'
               PROVE  c \in Filter(Evolve(S), p, ret'[p])
    BY Zenon DEF S
  <1>1. pc'[p] = RemainderID
    BY DEF RetLines, F3, I5, U5, R5, TypeOK, Inv
  <1>2. c.op[p] = BOT /\ c.arg[p] = BOT /\ c.res[p] = BOT
    BY <1>1, RemDef, SPrimeRewrite, Zenon DEF SPrime
  <1>3. CASE LineAction = F3(p)
    <2> USE <1>3 DEF F3, TypeOK, Inv
    <2> DEFINE c_pred == [state |-> c.state,
                          op    |-> [c.op EXCEPT ![p] = "Find"],
                          arg   |-> [c.arg EXCEPT ![p] = arg[p]],
                          res   |-> [c.res EXCEPT ![p] = r[p]]]
    <2>1. c_pred \in ConfigDomain
      <3>1. c_pred.state \in StateDomain
        BY DEF ConfigDomain
      <3>2. c_pred.op \in [ProcSet -> OpDomain]
        BY DEF ConfigDomain, OpDomain
      <3>3. c_pred.arg \in [ProcSet -> ArgDomain]
        BY DEF ConfigDomain, ArgDomain
      <3>4. c_pred.res \in [ProcSet -> ResDomain]
        BY DEF ConfigDomain, ResDomain
      <3> QED
        BY <3>1, <3>2, <3>3, <3>4 DEF ConfigDomain
    <2>2. c_pred \in S
      <3>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
        <4>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
          BY Zenon, SPrimeRewrite DEF SPrime
        <4>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
          BY Zenon DEF KeyInBktAtAddr
        <4>3. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
          <5> SUFFICES ASSUME NEW k \in KeyDomain
                        PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
            OBVIOUS
          <5> bkt_arr == MemLocs'[A'[Hash[k]]]
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
          <5>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
            BY DEF ValOfKeyInBktAtAddr
          <5>2. bkt_arr = MemLocs[A[Hash[k]]]
            BY Zenon
          <5> QED
            BY <5>1, <5>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
        <4> QED
          BY <4>1, <4>2, <4>3
      <3>2. ASSUME NEW q \in ProcSet
            PROVE
                CASE pc[q] = RemainderID 
                    -> (c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT)
                  [] pc[q] = "F1"
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                  [] pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL)
                  [] pc[q] = "F3"
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"I1", "I3", "I4"}
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                  [] pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "I5"
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"U1", "U2", "U3", "U4"}
                    -> (c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "U5"
                    -> (c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"R1", "R3", "R4"}
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL)
                  [] pc[q] = "R5"
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
        <4> USE <3>2
        <4>1. CASE pc[q] = RemainderID
          <5> SUFFICES c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT
            BY <4>1, RemDef, Zenon
          <5>1. q # p
            BY <4>1, RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = RemainderID
            BY <4>1, RemDef, Zenon
          <5>4. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>2. CASE pc[q] = "F1"
          <5> USE <4>2
          <5> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "F1"
            BY RemDef, Zenon
          <5>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>3
          <5> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            <6> DEFINE bkt_arr == MemLocs'[bucket'[q]]
            <6> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
            <6>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
              BY Zenon DEF ValOfKeyInBktAtAddr
            <6>2. bkt_arr = MemLocs[bucket[q]]
              BY Zenon
            <6>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
              BY Zenon
            <6> QED
              BY <6>1, <6>2, <6>3, Isa DEF ValOfKeyInBktAtAddr
          <5> QED
            BY <5>2, <5>4, <5>5
        <4>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>4
          <5> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>5. CASE pc[q] = "F3"
          <5> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY <4>5, RemDef, Zenon
          <5>1. CASE q = p
            BY <5>1 DEF ConfigDomain
          <5> SUFFICES ASSUME q # p
                        PROVE  c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY <5>1
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            OBVIOUS
          <5>3. pc'[q] = "F3"
            BY <4>5, RemDef, Zenon
          <5>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>6. CASE pc[q] \in {"I1", "I3", "I4"}
          <5> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY <4>6, RemDef, Zenon
          <5>1. q # p
            BY <4>6, RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] \in {"I1", "I3", "I4"}
            BY <4>6, RemDef, Zenon
          <5>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>7
          <5> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            <6> DEFINE bkt_arr == MemLocs'[bucket'[q]]
            <6> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
            <6>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
              BY Zenon DEF ValOfKeyInBktAtAddr
            <6>2. bkt_arr = MemLocs[bucket[q]]
              BY Zenon
            <6>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
              BY Zenon
            <6> QED
              BY <6>1, <6>2, <6>3, Isa DEF ValOfKeyInBktAtAddr
          <5> QED
            BY <5>2, <5>4, <5>5
        <4>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>8
          <5> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>9. CASE pc[q] = "I5"
          <5> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY <4>9, RemDef, Zenon
          <5>1. q # p
            BY <4>9, RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "I5"
            BY <4>9, RemDef, Zenon
          <5>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
          <5> USE <4>10
          <5> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] \in {"U1", "U2", "U3", "U4"}
            BY RemDef, Zenon
          <5>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>11. CASE pc[q] = "U5"
          <5> USE <4>11
          <5> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "U5"
            BY RemDef, Zenon
          <5>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>12. CASE pc[q] \in {"R1", "R3", "R4"}
          <5> USE <4>12
          <5> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] \in {"R1", "R3", "R4"}
            BY RemDef, Zenon
          <5>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>13
          <5> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>14
          <5> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>15. CASE pc[q] = "R5"
          <5> USE <4>15
          <5> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "R5"
            BY RemDef, Zenon
          <5>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4> QED
          BY RemDef, ZenonT(120),
              <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, 
              <4>10, <4>11, <4>12, <4>13, <4>14, <4>15
          DEF LineIDs
      <3> QED
        BY <2>1, <3>1, <3>2, Zenon DEF S
    <2>3. c_pred \in Evolve(S)
      BY <2>1, <2>2, EmptySeqEvolve
    <2>4. c.op = [c_pred.op EXCEPT ![p] = BOT]
      BY Zenon, <1>2 DEF ConfigDomain
    <2>5. c.arg = [c_pred.arg EXCEPT ![p] = BOT]
      BY Zenon, <1>2 DEF ConfigDomain
    <2>6. c.res = [c_pred.res EXCEPT ![p] = BOT]
      BY Zenon, <1>2 DEF ConfigDomain
    <2>7. c.state = c_pred.state
      OBVIOUS
    <2>8. c_pred.res[p] = ret'[p]
      BY Zenon DEF ConfigDomain
    <2> QED
      BY <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, Zenon DEF Filter
  <1>4. CASE LineAction = I5(p)
    <2> USE <1>4 DEF I5, TypeOK, Inv
    <2> DEFINE c_pred == [state |-> c.state,
                          op    |-> [c.op EXCEPT ![p] = "Insert"],
                          arg   |-> [c.arg EXCEPT ![p] = arg[p]],
                          res   |-> [c.res EXCEPT ![p] = r[p]]]
    <2>1. c_pred \in ConfigDomain
      <3>1. c_pred.state \in StateDomain
        BY DEF ConfigDomain
      <3>2. c_pred.op \in [ProcSet -> OpDomain]
        BY DEF ConfigDomain, OpDomain
      <3>3. c_pred.arg \in [ProcSet -> ArgDomain]
        BY DEF ConfigDomain, ArgDomain
      <3>4. c_pred.res \in [ProcSet -> ResDomain]
        BY DEF ConfigDomain, ResDomain
      <3> QED
        BY <3>1, <3>2, <3>3, <3>4 DEF ConfigDomain
    <2>2. c_pred \in S
      <3>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
        <4>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
          BY Zenon, SPrimeRewrite DEF SPrime
        <4>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
          BY Zenon DEF KeyInBktAtAddr
        <4>3. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
          <5> SUFFICES ASSUME NEW k \in KeyDomain
                        PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
            OBVIOUS
          <5> bkt_arr == MemLocs'[A'[Hash[k]]]
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
          <5>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
            BY DEF ValOfKeyInBktAtAddr
          <5>2. bkt_arr = MemLocs[A[Hash[k]]]
            BY Zenon
          <5> QED
            BY <5>1, <5>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
        <4> QED
          BY <4>1, <4>2, <4>3
      <3>2. ASSUME NEW q \in ProcSet
            PROVE
                CASE pc[q] = RemainderID 
                    -> (c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT)
                  [] pc[q] = "F1"
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                  [] pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL)
                  [] pc[q] = "F3"
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"I1", "I3", "I4"}
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                  [] pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "I5"
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"U1", "U2", "U3", "U4"}
                    -> (c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "U5"
                    -> (c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"R1", "R3", "R4"}
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL)
                  [] pc[q] = "R5"
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
        <4> USE <3>2
        <4>1. CASE pc[q] = RemainderID
          <5> SUFFICES c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT
            BY <4>1, RemDef, Zenon
          <5>1. q # p
            BY <4>1, RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = RemainderID
            BY <4>1, RemDef, Zenon
          <5>4. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>2. CASE pc[q] = "F1"
          <5> USE <4>2
          <5> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "F1"
            BY RemDef, Zenon
          <5>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>3
          <5> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            <6> DEFINE bkt_arr == MemLocs'[bucket'[q]]
            <6> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
            <6>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
              BY Zenon DEF ValOfKeyInBktAtAddr
            <6>2. bkt_arr = MemLocs[bucket[q]]
              BY Zenon
            <6>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
              BY Zenon
            <6> QED
              BY <6>1, <6>2, <6>3, Isa DEF ValOfKeyInBktAtAddr
          <5> QED
            BY <5>2, <5>4, <5>5
        <4>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>4
          <5> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>5. CASE pc[q] = "F3"
          <5> USE <4>5
          <5> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY <4>5, RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "F3"
            BY <4>5, RemDef, Zenon
          <5>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>6. CASE pc[q] \in {"I1", "I3", "I4"}
          <5> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY <4>6, RemDef, Zenon
          <5>1. q # p
            BY <4>6, RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] \in {"I1", "I3", "I4"}
            BY <4>6, RemDef, Zenon
          <5>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>7
          <5> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            <6> DEFINE bkt_arr == MemLocs'[bucket'[q]]
            <6> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
            <6>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
              BY Zenon DEF ValOfKeyInBktAtAddr
            <6>2. bkt_arr = MemLocs[bucket[q]]
              BY Zenon
            <6>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
              BY Zenon
            <6> QED
              BY <6>1, <6>2, <6>3, Isa DEF ValOfKeyInBktAtAddr
          <5> QED
            BY <5>2, <5>4, <5>5
        <4>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>8
          <5> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>9. CASE pc[q] = "I5"
          <5> USE <4>9
          <5> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY <4>9, RemDef, Zenon
          <5>1. CASE q = p
            BY <5>1 DEF ConfigDomain
          <5> SUFFICES ASSUME q # p
                        PROVE  c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY <5>1
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            OBVIOUS
          <5>3. pc'[q] = "I5"
            BY <4>9, RemDef, Zenon
          <5>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
          <5> USE <4>10
          <5> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] \in {"U1", "U2", "U3", "U4"}
            BY RemDef, Zenon
          <5>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>11. CASE pc[q] = "U5"
          <5> USE <4>11
          <5> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "U5"
            BY RemDef, Zenon
          <5>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>12. CASE pc[q] \in {"R1", "R3", "R4"}
          <5> USE <4>12
          <5> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] \in {"R1", "R3", "R4"}
            BY RemDef, Zenon
          <5>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>13
          <5> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>14
          <5> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>15. CASE pc[q] = "R5"
          <5> USE <4>15
          <5> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "R5"
            BY RemDef, Zenon
          <5>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4> QED
          BY RemDef, ZenonT(120),
              <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, 
              <4>10, <4>11, <4>12, <4>13, <4>14, <4>15
          DEF LineIDs
      <3> QED
        BY <2>1, <3>1, <3>2, Zenon DEF S
    <2>3. c_pred \in Evolve(S)
      BY <2>1, <2>2, EmptySeqEvolve
    <2>4. c.op = [c_pred.op EXCEPT ![p] = BOT]
      BY Zenon, <1>2 DEF ConfigDomain
    <2>5. c.arg = [c_pred.arg EXCEPT ![p] = BOT]
      BY Zenon, <1>2 DEF ConfigDomain
    <2>6. c.res = [c_pred.res EXCEPT ![p] = BOT]
      BY Zenon, <1>2 DEF ConfigDomain
    <2>7. c.state = c_pred.state
      OBVIOUS
    <2>8. c_pred.res[p] = ret'[p]
      BY Zenon DEF ConfigDomain
    <2> QED
      BY <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, Zenon DEF Filter
  <1>5. CASE LineAction = U5(p)
    <2> USE <1>5 DEF U5, TypeOK, Inv
    <2> DEFINE c_pred == [state |-> c.state,
                          op    |-> [c.op EXCEPT ![p] = "Upsert"],
                          arg   |-> [c.arg EXCEPT ![p] = arg[p]],
                          res   |-> [c.res EXCEPT ![p] = r[p]]]
    <2>1. c_pred \in ConfigDomain
      <3>1. c_pred.state \in StateDomain
        BY DEF ConfigDomain
      <3>2. c_pred.op \in [ProcSet -> OpDomain]
        BY DEF ConfigDomain, OpDomain
      <3>3. c_pred.arg \in [ProcSet -> ArgDomain]
        BY DEF ConfigDomain, ArgDomain
      <3>4. c_pred.res \in [ProcSet -> ResDomain]
        BY DEF ConfigDomain, ResDomain
      <3> QED
        BY <3>1, <3>2, <3>3, <3>4 DEF ConfigDomain
    <2>2. c_pred \in S
      <3>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
        <4>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
          BY Zenon, SPrimeRewrite DEF SPrime
        <4>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
          BY Zenon DEF KeyInBktAtAddr
        <4>3. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
          <5> SUFFICES ASSUME NEW k \in KeyDomain
                        PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
            OBVIOUS
          <5> bkt_arr == MemLocs'[A'[Hash[k]]]
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
          <5>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
            BY DEF ValOfKeyInBktAtAddr
          <5>2. bkt_arr = MemLocs[A[Hash[k]]]
            BY Zenon
          <5> QED
            BY <5>1, <5>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
        <4> QED
          BY <4>1, <4>2, <4>3
      <3>2. ASSUME NEW q \in ProcSet
            PROVE
                CASE pc[q] = RemainderID 
                    -> (c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT)
                  [] pc[q] = "F1"
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                  [] pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL)
                  [] pc[q] = "F3"
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"I1", "I3", "I4"}
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                  [] pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "I5"
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"U1", "U2", "U3", "U4"}
                    -> (c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "U5"
                    -> (c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"R1", "R3", "R4"}
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL)
                  [] pc[q] = "R5"
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
        <4> USE <3>2
        <4>1. CASE pc[q] = RemainderID
          <5> SUFFICES c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT
            BY <4>1, RemDef, Zenon
          <5>1. q # p
            BY <4>1, RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = RemainderID
            BY <4>1, RemDef, Zenon
          <5>4. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>2. CASE pc[q] = "F1"
          <5> USE <4>2
          <5> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "F1"
            BY RemDef, Zenon
          <5>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>3
          <5> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            <6> DEFINE bkt_arr == MemLocs'[bucket'[q]]
            <6> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
            <6>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
              BY Zenon DEF ValOfKeyInBktAtAddr
            <6>2. bkt_arr = MemLocs[bucket[q]]
              BY Zenon
            <6>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
              BY Zenon
            <6> QED
              BY <6>1, <6>2, <6>3, Isa DEF ValOfKeyInBktAtAddr
          <5> QED
            BY <5>2, <5>4, <5>5
        <4>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>4
          <5> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>5. CASE pc[q] = "F3"
          <5> USE <4>5
          <5> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY <4>5, RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "F3"
            BY <4>5, RemDef, Zenon
          <5>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>6. CASE pc[q] \in {"I1", "I3", "I4"}
          <5> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY <4>6, RemDef, Zenon
          <5>1. q # p
            BY <4>6, RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] \in {"I1", "I3", "I4"}
            BY <4>6, RemDef, Zenon
          <5>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>7
          <5> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            <6> DEFINE bkt_arr == MemLocs'[bucket'[q]]
            <6> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
            <6>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
              BY Zenon DEF ValOfKeyInBktAtAddr
            <6>2. bkt_arr = MemLocs[bucket[q]]
              BY Zenon
            <6>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
              BY Zenon
            <6> QED
              BY <6>1, <6>2, <6>3, Isa DEF ValOfKeyInBktAtAddr
          <5> QED
            BY <5>2, <5>4, <5>5
        <4>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>8
          <5> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>9. CASE pc[q] = "I5"
          <5> USE <4>9
          <5> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY <4>9, RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "I5"
            BY <4>9, RemDef, Zenon
          <5>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
          <5> USE <4>10
          <5> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] \in {"U1", "U2", "U3", "U4"}
            BY RemDef, Zenon
          <5>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>11. CASE pc[q] = "U5"
          <5> USE <4>11
          <5> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. CASE q = p
            BY <5>1 DEF ConfigDomain
          <5> SUFFICES ASSUME q # p
                        PROVE  c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY <5>1
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            OBVIOUS
          <5>3. pc'[q] = "U5"
            BY RemDef, Zenon
          <5>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>12. CASE pc[q] \in {"R1", "R3", "R4"}
          <5> USE <4>12
          <5> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] \in {"R1", "R3", "R4"}
            BY RemDef, Zenon
          <5>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>13
          <5> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>14
          <5> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>15. CASE pc[q] = "R5"
          <5> USE <4>15
          <5> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "R5"
            BY RemDef, Zenon
          <5>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4> QED
          BY RemDef, ZenonT(120),
              <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, 
              <4>10, <4>11, <4>12, <4>13, <4>14, <4>15
          DEF LineIDs
      <3> QED
        BY <2>1, <3>1, <3>2, Zenon DEF S
    <2>3. c_pred \in Evolve(S)
      BY <2>1, <2>2, EmptySeqEvolve
    <2>4. c.op = [c_pred.op EXCEPT ![p] = BOT]
      BY Zenon, <1>2 DEF ConfigDomain
    <2>5. c.arg = [c_pred.arg EXCEPT ![p] = BOT]
      BY Zenon, <1>2 DEF ConfigDomain
    <2>6. c.res = [c_pred.res EXCEPT ![p] = BOT]
      BY Zenon, <1>2 DEF ConfigDomain
    <2>7. c.state = c_pred.state
      OBVIOUS
    <2>8. c_pred.res[p] = ret'[p]
      BY Zenon DEF ConfigDomain
    <2> QED
      BY <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, Zenon DEF Filter
  <1>6. CASE LineAction = R5(p)
    <2> USE <1>6 DEF R5, TypeOK, Inv
    <2> DEFINE c_pred == [state |-> c.state,
                          op    |-> [c.op EXCEPT ![p] = "Remove"],
                          arg   |-> [c.arg EXCEPT ![p] = arg[p]],
                          res   |-> [c.res EXCEPT ![p] = r[p]]]
    <2>1. c_pred \in ConfigDomain
      <3>1. c_pred.state \in StateDomain
        BY DEF ConfigDomain
      <3>2. c_pred.op \in [ProcSet -> OpDomain]
        BY DEF ConfigDomain, OpDomain
      <3>3. c_pred.arg \in [ProcSet -> ArgDomain]
        BY DEF ConfigDomain, ArgDomain
      <3>4. c_pred.res \in [ProcSet -> ResDomain]
        BY DEF ConfigDomain, ResDomain
      <3> QED
        BY <3>1, <3>2, <3>3, <3>4 DEF ConfigDomain
    <2>2. c_pred \in S
      <3>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
        <4>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
          BY Zenon, SPrimeRewrite DEF SPrime
        <4>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
          BY Zenon DEF KeyInBktAtAddr
        <4>3. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
          <5> SUFFICES ASSUME NEW k \in KeyDomain
                        PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
            OBVIOUS
          <5> bkt_arr == MemLocs'[A'[Hash[k]]]
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
          <5>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
            BY DEF ValOfKeyInBktAtAddr
          <5>2. bkt_arr = MemLocs[A[Hash[k]]]
            BY Zenon
          <5> QED
            BY <5>1, <5>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
        <4> QED
          BY <4>1, <4>2, <4>3
      <3>2. ASSUME NEW q \in ProcSet
            PROVE
                CASE pc[q] = RemainderID 
                    -> (c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT)
                  [] pc[q] = "F1"
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                  [] pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL)
                  [] pc[q] = "F3"
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"I1", "I3", "I4"}
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                  [] pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "I5"
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"U1", "U2", "U3", "U4"}
                    -> (c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "U5"
                    -> (c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"R1", "R3", "R4"}
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL)
                  [] pc[q] = "R5"
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
        <4> USE <3>2
        <4>1. CASE pc[q] = RemainderID
          <5> SUFFICES c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT
            BY <4>1, RemDef, Zenon
          <5>1. q # p
            BY <4>1, RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = RemainderID
            BY <4>1, RemDef, Zenon
          <5>4. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>2. CASE pc[q] = "F1"
          <5> USE <4>2
          <5> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "F1"
            BY RemDef, Zenon
          <5>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>3
          <5> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            <6> DEFINE bkt_arr == MemLocs'[bucket'[q]]
            <6> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
            <6>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
              BY Zenon DEF ValOfKeyInBktAtAddr
            <6>2. bkt_arr = MemLocs[bucket[q]]
              BY Zenon
            <6>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
              BY Zenon
            <6> QED
              BY <6>1, <6>2, <6>3, Isa DEF ValOfKeyInBktAtAddr
          <5> QED
            BY <5>2, <5>4, <5>5
        <4>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>4
          <5> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>5. CASE pc[q] = "F3"
          <5> USE <4>5
          <5> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY <4>5, RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "F3"
            BY <4>5, RemDef, Zenon
          <5>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>6. CASE pc[q] \in {"I1", "I3", "I4"}
          <5> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY <4>6, RemDef, Zenon
          <5>1. q # p
            BY <4>6, RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] \in {"I1", "I3", "I4"}
            BY <4>6, RemDef, Zenon
          <5>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>7
          <5> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            <6> DEFINE bkt_arr == MemLocs'[bucket'[q]]
            <6> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
            <6>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
              BY Zenon DEF ValOfKeyInBktAtAddr
            <6>2. bkt_arr = MemLocs[bucket[q]]
              BY Zenon
            <6>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
              BY Zenon
            <6> QED
              BY <6>1, <6>2, <6>3, Isa DEF ValOfKeyInBktAtAddr
          <5> QED
            BY <5>2, <5>4, <5>5
        <4>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>8
          <5> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>9. CASE pc[q] = "I5"
          <5> USE <4>9
          <5> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY <4>9, RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "I5"
            BY <4>9, RemDef, Zenon
          <5>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
          <5> USE <4>10
          <5> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] \in {"U1", "U2", "U3", "U4"}
            BY RemDef, Zenon
          <5>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>11. CASE pc[q] = "U5"
          <5> USE <4>11
          <5> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. q # p
            BY Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "U5"
            BY RemDef, Zenon
          <5>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>12. CASE pc[q] \in {"R1", "R3", "R4"}
          <5> USE <4>12
          <5> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] \in {"R1", "R3", "R4"}
            BY RemDef, Zenon
          <5>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>13
          <5> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>14
          <5> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>15. CASE pc[q] = "R5"
          <5> USE <4>15
          <5> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. CASE q = p 
            BY <5>1 DEF ConfigDomain
          <5> SUFFICES ASSUME q # p
                        PROVE  c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY <5>1
          <5>2. q # p
            OBVIOUS
          <5>3. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            OBVIOUS
          <5>4. pc'[q] = "R5"
            BY RemDef, Zenon
          <5>5. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>4, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>3, <5>5
        <4> QED
          BY RemDef, ZenonT(120),
              <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, 
              <4>10, <4>11, <4>12, <4>13, <4>14, <4>15
          DEF LineIDs
      <3> QED
        BY <2>1, <3>1, <3>2, Zenon DEF S
    <2>3. c_pred \in Evolve(S)
      BY <2>1, <2>2, EmptySeqEvolve
    <2>4. c.op = [c_pred.op EXCEPT ![p] = BOT]
      BY Zenon, <1>2 DEF ConfigDomain
    <2>5. c.arg = [c_pred.arg EXCEPT ![p] = BOT]
      BY Zenon, <1>2 DEF ConfigDomain
    <2>6. c.res = [c_pred.res EXCEPT ![p] = BOT]
      BY Zenon, <1>2 DEF ConfigDomain
    <2>7. c.state = c_pred.state
      OBVIOUS
    <2>8. c_pred.res[p] = ret'[p]
      BY Zenon DEF ConfigDomain
    <2> QED
      BY <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, Zenon DEF Filter
  <1> QED
    BY <1>3, <1>4, <1>5, <1>6, Zenon DEF RetLines

=================================================================================================