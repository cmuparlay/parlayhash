--------------------------- MODULE MCTracking_find_proofs ----------------------
(***************************************************************************
 This module contains the proof of LinIntermediateLine_Find from IndInv.tla
 ***************************************************************************)
EXTENDS MCTracking, Assumptions, TLAPS,
        SequenceTheorems, FiniteSets

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

\* LinIntermediateLine_Find =
\*     Inv /\ (\E p \in ProcSet : \/ F1(p)
\*                                \/ F2(p)) => S' \in SUBSET Evolve(S)
LEMMA LinIntermediateLine_Find
  <1> SUFFICES ASSUME Inv,
                      NEW p \in ProcSet,
                      \/ F1(p)
                      \/ F2(p)
               PROVE  S' \in SUBSET Evolve(S)
    BY Zenon
  <1>1. CASE F1(p)
    <2> USE <1>1 DEF F1
    <2> SUFFICES ASSUME NEW c \in ConfigDomain,
                        c \in S'
                 PROVE  c \in Evolve(S)
      BY Zenon DEF S
    <2> DEFINE c_pred == [state |-> c.state,
                          op    |-> c.op,
                          arg   |-> c.arg,
                          res   |-> [c.res EXCEPT ![p] = BOT]]
    <2>1. c_pred \in ConfigDomain
      <3>1. c_pred.state \in StateDomain
        BY DEF ConfigDomain
      <3>2. c_pred.op \in [ProcSet -> OpDomain]
        BY DEF ConfigDomain
      <3>3. c_pred.arg \in [ProcSet -> ArgDomain]
        BY DEF ConfigDomain
      <3>4. c_pred.res \in [ProcSet -> ResDomain]
        BY DEF ConfigDomain, ResDomain
      <3> QED
        BY <3>1, <3>2, <3>3, <3>4 DEF ConfigDomain
    <2>2. c_pred \in S
      <3>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) 
                                                    THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) 
                                                    ELSE NULL]
        <4>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])'
                                                      THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])'
                                                      ELSE NULL]
          BY SPrimeRewrite, Zenon DEF SPrime
        <4>2. \A k \in KeyDomain : /\ KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                                    /\ ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
          <5> SUFFICES ASSUME NEW k \in KeyDomain
                        PROVE  /\ KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                              /\ ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
            OBVIOUS
          <5>1. KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
            BY Zenon DEF KeyInBktAtAddr
          <5>2. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
            <6> DEFINE bkt_arr == MemLocs'[A'[Hash[k]]]
            <6> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
            <6>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
              BY Zenon DEF ValOfKeyInBktAtAddr
            <6>2. bkt_arr = MemLocs[A[Hash[k]]]
              BY Zenon
            <6>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              BY Zenon
            <6> QED
              BY <6>1, <6>2, <6>3, Isa DEF ValOfKeyInBktAtAddr
          <5>3. QED
            BY <5>1, <5>2
        <4> QED
          BY <4>1, <4>2   
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
        <4> USE <3>2 DEF TypeOK, Inv
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
          <5>1. CASE q = p
            <6> USE <5>1
            <6>1. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = BOT
              BY Zenon DEF ConfigDomain
            <6>2. pc'[q] = "F2"
              BY Zenon
            <6>3. c.op[q] = "Find" /\ c.arg[q] = arg[q]
              BY <6>2, SPrimeRewrite, ZenonT(30), RemDef DEF SPrime
            <6> QED
              BY <6>1, <6>3
          <5> SUFFICES ASSUME q # p
                        PROVE  c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY <5>1
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            OBVIOUS
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
          <5>1. q # p
            BY <4>5, RemDef, Zenon
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
    <2>3. Delta(c_pred, p, c)
      <3> USE DEF TypeOK, Inv
      <3>1. c_pred.op[p] = "Find" /\ c_pred.arg[p] = arg[p] /\ c_pred.res[p] = BOT
        BY <2>2, RemDef, Zenon DEF S
      <3>2. c_pred.arg[p] \in ArgsOf("Find")
        BY <3>1, RemDef, Zenon DEF ArgsOf, LineIDtoOp
      <3> SUFFICES c.res = [c_pred.res EXCEPT ![p] = c_pred.state[c_pred.arg[p].key]]
        BY <3>1, <3>2 DEF Delta
      <3> SUFFICES c.res[p] = c_pred.state[c_pred.arg[p].key]
        BY <2>1, Zenon DEF ConfigDomain
      <3>3. KeyInBktAtAddr(arg[p].key, bucket[p])' = KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])
        BY Zenon DEF KeyInBktAtAddr
      <3>4. ValOfKeyInBktAtAddr(arg[p].key, bucket[p])' = ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])
        <4> DEFINE bkt_arr == MemLocs'[bucket'[p]]
        <4> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[p].key
        <4>1. ValOfKeyInBktAtAddr(arg[p].key, bucket[p])' = bkt_arr[idx].val
          BY Zenon DEF ValOfKeyInBktAtAddr
        <4> DEFINE bkt_arr2 == MemLocs[A[Hash[arg[p].key]]]
        <4> DEFINE idx2 == CHOOSE index \in 1..Len(bkt_arr2) : bkt_arr2[index].key = arg[p].key
        <4>2. ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) = bkt_arr2[idx2].val
          BY Zenon DEF ValOfKeyInBktAtAddr
        <4>3. bkt_arr = bkt_arr2 /\ idx = idx2
          BY ZenonT(30)
        <4> QED
          BY <4>1, <4>2, <4>3
      <3>5. CASE KeyInBktAtAddr(arg[p].key, bucket[p])'
        <4> USE <3>5
        <4>1. c.res[p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p])'
          BY RemDef, Zenon DEF S
        <4>2. c.res[p] = ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])
          BY <3>4, <4>1
        <4>3. c_pred.arg[p].key \in KeyDomain /\ c_pred.arg[p] = arg[p]
          BY <3>1, <3>2 DEF ArgsOf
        <4>4. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) 
                                                  THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) 
                                                  ELSE NULL]
          BY <2>2, Zenon DEF S
        <4>5. c_pred.state[c_pred.arg[p].key] = IF KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) 
                                                   THEN ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) 
                                                   ELSE NULL
          BY <4>3, <4>4, Zenon
        <4>6. c_pred.state[c_pred.arg[p].key] = ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) 
          BY <3>3, <4>5
        <4> QED
          BY <4>2, <4>6
      <3>6. CASE ~KeyInBktAtAddr(arg[p].key, bucket[p])'
        <4> USE <3>6
        <4>1. c.res[p] = NULL
          BY RemDef, Zenon DEF S
        <4>2. c_pred.arg[p].key \in KeyDomain /\ c_pred.arg[p] = arg[p]
          BY <3>1, <3>2 DEF ArgsOf
        <4>3. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) 
                                         THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) 
                                         ELSE NULL]
          BY <2>2, Zenon DEF S
        <4>4. c_pred.state[c_pred.arg[p].key] = IF KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) 
                                                   THEN ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) 
                                                   ELSE NULL
          BY <4>2, <4>3, Zenon
        <4>5. c_pred.state[c_pred.arg[p].key] = NULL 
          BY <3>3, <4>4
        <4> QED
          BY <4>1, <4>5
      <3> QED 
        BY <3>5, <3>6
    <2>4. c \in Evolve(S)
      BY <2>1, <2>2, <2>3, SingleDeltaEvolve
    <2> QED
      BY <2>4
  <1>2. CASE F2(p)
    <2> USE <1>2 DEF F2
    <2> SUFFICES ASSUME NEW c \in ConfigDomain,
                        c \in S'
                 PROVE  c \in Evolve(S)
      BY Zenon DEF S
    <2> SUFFICES c \in S
      BY EmptySeqEvolve
    <2>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
      <3>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
        BY Zenon, SPrimeRewrite DEF SPrime
      <3>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
        BY Zenon DEF KeyInBktAtAddr
      <3>3. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
        <4> SUFFICES ASSUME NEW k \in KeyDomain
                     PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
          OBVIOUS
        <4> bkt_arr == MemLocs'[A'[Hash[k]]]
        <4> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
        <4>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
          BY DEF ValOfKeyInBktAtAddr
        <4>2. bkt_arr = MemLocs[A[Hash[k]]]
          BY Zenon
        <4> QED
          BY <4>1, <4>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
      <3> QED
        BY <3>1, <3>2, <3>3
    <2>2. ASSUME NEW q \in ProcSet
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
      <3> USE <2>2 DEF TypeOK, Inv
      <3>1. \A k \in KeyDomain : KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
        BY Zenon DEF KeyInBktAtAddr
      <3>2. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, bucket[q])
        <4> SUFFICES ASSUME NEW k \in KeyDomain
                      PROVE  ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, bucket[q])
          OBVIOUS
        <4> bkt_arr == MemLocs'[bucket'[q]]
        <4> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
        <4>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
          BY DEF ValOfKeyInBktAtAddr
        <4>2. bkt_arr = MemLocs[bucket[q]]
          BY Zenon
        <4> QED
          BY <4>1, <4>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
      <3>3. CASE pc[q] = RemainderID
        <4> USE <3>3
        <4> SUFFICES c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] = RemainderID
          BY RemDef, Zenon
        <4>2. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>4. CASE pc[q] = "F1"
        <4> USE <3>4
        <4> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] = "F1"
          BY RemDef, Zenon
        <4>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>5. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>5
        <4> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY RemDef, Zenon
        <4>1. CASE q = p
          <5> USE <4>1
          <5>1. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r'[q]
            BY SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY <5>1, Zenon
          <5> QED
            BY <5>2
        <4> SUFFICES ASSUME q # p
                     PROVE  c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY <4>1
        <4>2. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>3. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
          BY <4>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4>4. arg[q].key = arg'[q].key /\ arg[q].key \in KeyDomain
          BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
        <4>5. c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY <4>3, <4>4, <3>2
        <4> QED
          BY <4>3, <4>5
      <3>6. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>6
        <4> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
          BY RemDef, Zenon
        <4>1. CASE q = p
          <5> USE <4>1
          <5>1. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r'[q]
            BY SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>1, Zenon
          <5> QED
            BY <5>2
        <4> SUFFICES ASSUME q # p
                    PROVE  c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
          BY <4>1
        <4>2. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>3. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
          BY <4>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>3
      <3>7. CASE pc[q] = "F3"
        <4> USE <3>7
        <4> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY RemDef, Zenon
        <4>1. pc'[q] = "F3"
          BY RemDef, Zenon
        <4>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2 
      <3>8. CASE pc[q] \in {"I1", "I3", "I4"}
        <4> USE <3>8
        <4> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] \in {"I1", "I3", "I4"}
          BY RemDef, Zenon
        <4>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2 
      <3>9. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>9
        <4> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY RemDef, Zenon
        <4>2. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
          BY <4>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4>4. arg[q].key = arg'[q].key /\ arg[q].key \in KeyDomain
          BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
        <4>5. c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY <4>3, <4>4, <3>2
        <4> QED
          BY <4>3, <4>5
      <3>10. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>10
        <4> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2 
      <3>11. CASE pc[q] = "I5"
        <4> USE <3>11
        <4> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY RemDef, Zenon
        <4>1. pc'[q] = "I5"
          BY RemDef, Zenon 
        <4>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2 
      <3>12. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
        <4> USE <3>12
        <4> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] \in {"U1", "U2", "U3", "U4"}
          BY RemDef, Zenon
        <4>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>13. CASE pc[q] = "U5" 
        <4> USE <3>13
        <4> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY RemDef, Zenon
        <4>1. pc'[q] = "U5"
          BY RemDef, Zenon
        <4>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>14. CASE pc[q] \in {"R1", "R3", "R4"}
        <4> USE <3>14
        <4> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] \in {"R1", "R3", "R4"}
          BY RemDef, Zenon
        <4>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>15. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>15
        <4> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>16. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>16
        <4> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
          BY RemDef, Zenon
        <4>1. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>17. CASE pc[q] = "R5"
        <4> USE <3>17
        <4> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY RemDef, Zenon
        <4>1. pc'[q] = "R5" 
          BY RemDef, Zenon
        <4>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3> QED
          BY RemDef, ZenonT(120),
              <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11, 
              <3>12, <3>13, <3>14, <3>15, <3>16, <3>17
          DEF LineIDs
    <2> QED
      BY <2>1, <2>2, Zenon DEF S
  <1> QED
    BY <1>1, <1>2

==========================================================================================
\* Modification History
\* Last modified Tue Aug 27 10:59:21 EDT 2024 by uguryavuz
\* Created Mon Jul 08 12:21:04 EDT 2024 by uyavuz
