--------------------------- MODULE MCTracking_insert_proofs ----------------------
(***************************************************************************
 This module contains the proof of LinIntermediateLine_Insert from IndInv.tla
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

\* LinIntermediateLine_Insert
\*     Inv /\ (\E p \in ProcSet : \/ I1(p)
\*                                \/ I2(p)
\*                                \/ I3(p)
\*                                \/ I4(p)) => S' \in SUBSET Evolve(S)
LEMMA LinIntermediateLine_Insert
  <1> SUFFICES ASSUME Inv,
                      NEW p \in ProcSet,
                      \/ I1(p)
                      \/ I2(p)
                      \/ I3(p)
                      \/ I4(p)
               PROVE  S' \in SUBSET Evolve(S)
    BY Zenon
  <1>1. CASE I1(p)
    <2> USE <1>1 DEF I1
    <2> SUFFICES ASSUME NEW c \in ConfigDomain,
                        c \in S'
                 PROVE  c \in Evolve(S)
      BY Zenon DEF S
    <2>1. CASE ~KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])
      <3> USE <2>1 DEF TypeOK, Inv
      <3> SUFFICES c \in S
        BY EmptySeqEvolve
      <3>1. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
        BY Zenon, HashDef DEF KeyInBktAtAddr
      <3>2. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
        <4> SUFFICES ASSUME NEW k \in KeyDomain
                     PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
          OBVIOUS
        <4> DEFINE bkt_arr == MemLocs'[A'[Hash[k]]]
        <4> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
        <4>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
          BY Zenon DEF ValOfKeyInBktAtAddr
        <4>2. bkt_arr = MemLocs[A[Hash[k]]] /\ A'[Hash[k]] = A[Hash[k]]
          BY Zenon
        <4> QED
          BY <4>1, <4>2 DEF ValOfKeyInBktAtAddr
      <3>3. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) 
                                              THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) 
                                              ELSE NULL]
        <4>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
          BY SPrimeRewrite, Zenon DEF SPrime
        <4> QED
          BY <3>1, <3>2, <4>1
      <3>4. ASSUME NEW q \in ProcSet
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
        <4> USE <3>4
        <4>1. CASE pc[q] = RemainderID
          <5> USE <4>1
          <5> SUFFICES c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = RemainderID
            BY RemDef, Zenon
          <5>2. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>2. CASE pc[q] = "F1"
          <5> USE <4>2
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = "F1"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2    
        <4>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>3
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            <6> DEFINE bkt_arr == MemLocs'[bucket'[q]]
            <6> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
            <6>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
              BY Zenon DEF ValOfKeyInBktAtAddr
            <6>2. bkt_arr = MemLocs[bucket[q]]
              BY Zenon
            <6>3. arg'[q].key = arg[q].key
              BY Zenon
            <6> QED
              BY <6>1, <6>2, <6>3, Isa DEF ValOfKeyInBktAtAddr
          <5> QED
            BY <5>2, <5>3
        <4>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>4
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY RemDef, Zenon
          <5>1. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>5. CASE pc[q] = "F3"
          <5> USE <4>5
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "F3"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2 
        <4>6. CASE pc[q] \in {"I1", "I3", "I4"}
          <5> USE <4>6
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. CASE p = q
            <6> USE <5>1
            <6>1. arg[q].key = arg'[q].key /\ bucket'[q] = A[Hash[arg[q].key]]
              BY Zenon
            <6>2. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY <6>1, Zenon DEF KeyInBktAtAddr
            <6>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>2, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>3
          <5> SUFFICES ASSUME p # q
                        PROVE  c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1
          <5>2. pc'[q] \in {"I1", "I3", "I4"}
            BY RemDef, Zenon
          <5>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>2, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>3 
        <4>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>7
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            <6> DEFINE bkt_arr == MemLocs'[bucket'[q]]
            <6> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
            <6>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
              BY Zenon DEF ValOfKeyInBktAtAddr
            <6>2. bkt_arr = MemLocs[bucket[q]]
              BY Zenon
            <6>3. arg'[q].key = arg[q].key
              BY Zenon
            <6> QED
              BY <6>1, <6>2, <6>3, Isa DEF ValOfKeyInBktAtAddr
          <5> QED
            BY <5>2, <5>3
        <4>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>8
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>9. CASE pc[q] = "I5"
          <5> USE <4>9
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "I5"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2 
        <4>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
          <5> USE <4>10
          <5> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] \in {"U1", "U2", "U3", "U4"}
            BY RemDef, Zenon
          <5>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2 
        <4>11. CASE pc[q] = "U5" 
          <5> USE <4>11
          <5> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "U5"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2 
        <4>12. CASE pc[q] \in {"R1", "R3", "R4"}
          <5> USE <4>12
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] \in {"R1", "R3", "R4"}
            BY RemDef, Zenon
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2 
        <4>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>13
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>14
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY RemDef, Zenon
          <5>1. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>15. CASE pc[q] = "R5"
          <5> USE <4>15
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "R5"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2 
        <4> QED
          BY RemDef, ZenonT(120),
              <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, 
              <4>10, <4>11, <4>12, <4>13, <4>14, <4>15
          DEF LineIDs
      <3> QED
        BY <3>3, <3>4, Zenon DEF S
    <2>2. CASE KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])
      <3> USE <2>2 DEF TypeOK, Inv
      <3> DEFINE c_pred == [state |-> c.state,
                            op    |-> c.op,
                            arg   |-> c.arg,
                            res   |-> [c.res EXCEPT ![p] = BOT]]
      <3>1. c_pred \in ConfigDomain
        <4>1. c_pred.state \in StateDomain
          BY DEF ConfigDomain
        <4>2. c_pred.op \in [ProcSet -> OpDomain]
          BY DEF ConfigDomain
        <4>3. c_pred.arg \in [ProcSet -> ArgDomain]
          BY DEF ConfigDomain
        <4>4. c_pred.res \in [ProcSet -> ResDomain]
          BY DEF ConfigDomain, ResDomain
        <4> QED
          BY <4>1, <4>2, <4>3, <4>4 DEF ConfigDomain
      <3>2. c_pred \in S
        <4>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
          <5>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])'
                                                        THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])'
                                                        ELSE NULL]
            BY SPrimeRewrite, Zenon DEF SPrime
          <5>2. \A k \in KeyDomain : /\ KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                                      /\ ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
            <6> SUFFICES ASSUME NEW k \in KeyDomain
                          PROVE  /\ KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                                /\ ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
              OBVIOUS
            <6>1. KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
              BY Zenon DEF KeyInBktAtAddr
            <6>2. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
              <7> DEFINE bkt_arr == MemLocs'[A'[Hash[k]]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[A[Hash[k]]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6>3. QED
              BY <6>1, <6>2
          <5> QED
            BY <5>1, <5>2 
        <4>2. ASSUME NEW q \in ProcSet
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
          <5> USE <4>2
          <5>1. CASE pc[q] = RemainderID
            <6> USE <5>1
            <6> SUFFICES c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = RemainderID
              BY RemDef, Zenon
            <6>4. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>2. CASE pc[q] = "F1"
            <6> USE <5>2
            <6> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "F1"
              BY RemDef, Zenon
            <6>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
            <6> USE <5>3
            <6> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              <7> DEFINE bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
              <7>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>2, <6>4, <6>5
          <5>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
            <6> USE <5>4
            <6> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>5. CASE pc[q] = "F3" 
            <6> USE <5>5
            <6> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "F3"
              BY RemDef, Zenon
            <6>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>6. CASE pc[q] \in {"I1", "I3", "I4"}
            <6> USE <5>6
            <6> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>A. CASE p = q
              <7> USE <6>A
              <7>1. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = BOT
                BY <3>1 DEF ConfigDomain
              <7>2. pc'[q] = "I2"
                BY Zenon
              <7>3. c.op[q] = "Insert" /\ c.arg[p] = arg[q]
                BY <7>2, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>1, <7>3
            <6> SUFFICES ASSUME p # q
                          PROVE  c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY <6>A
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              OBVIOUS
            <6>3. pc'[q] \in {"I1", "I3", "I4"}
              BY RemDef, Zenon
            <6>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
            <6> USE <5>7
            <6> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              <7> DEFINE bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
              <7>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>2, <6>4, <6>5
          <5>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
            <6> USE <5>8
            <6> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>9. CASE pc[q] = "I5"
            <6> USE <5>9
            <6> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "I5"
              BY RemDef, Zenon
            <6>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
            <6> USE <5>10
            <6> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] \in {"U1", "U2", "U3", "U4"}
              BY RemDef, Zenon
            <6>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>11. CASE pc[q] = "U5" 
            <6> USE <5>11
            <6> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "U5"
              BY RemDef, Zenon
            <6>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>12. CASE pc[q] \in {"R1", "R3", "R4"}
            <6> USE <5>12
            <6> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] \in {"R1", "R3", "R4"}
              BY RemDef, Zenon
            <6>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q]) 
            <6> USE <5>13
            <6> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4              
          <5>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
            <6> USE <5>14
            <6> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4    
          <5>15. CASE pc[q] = "R5"
            <6> USE <5>15
            <6> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "R5"
              BY RemDef, Zenon
            <6>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5> QED
              BY RemDef, ZenonT(120),
                  <5>1, <5>2, <5>3, <5>4, <5>5, <5>6, <5>7, <5>8, <5>9, 
                  <5>10, <5>11, <5>12, <5>13, <5>14, <5>15
              DEF LineIDs
        <4> QED
          BY <3>1, <4>1, <4>2, Zenon DEF S
      <3>3. Delta(c_pred, p, c)
        <4>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
          BY <3>1, <3>2, Zenon DEF S
        <4>2. c_pred.op[p] = "Insert" /\ c_pred.arg[p] = arg[p] /\ c_pred.res[p] = BOT
          BY <3>1, <3>2, Zenon, RemDef DEF S
        <4>3. arg[p] \in ArgsOf("Insert") /\ arg[p].key \in KeyDomain
          BY RemDef, Zenon DEF ArgsOf, LineIDtoOp 
        <4>4. c_pred.state[c_pred.arg[p].key] = ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])
          BY <4>1, <4>2, <4>3, Zenon
        <4>5. ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) \in ValDomain
          <5> DEFINE bkt_arr == MemLocs[A[Hash[arg[p].key]]]
          <5>1. A[Hash[arg[p].key]] # NULL
            BY DEF KeyInBktAtAddr
          <5>2. bkt_arr \in Seq([key: KeyDomain, val: ValDomain])
            BY HashDef, <4>3, <5>1, Zenon
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[p].key
          <5>3. idx \in 1..Len(bkt_arr)
            BY Zenon DEF KeyInBktAtAddr
          <5>4. bkt_arr[idx] \in [key: KeyDomain, val: ValDomain]
            BY Zenon, ElementOfSeq, <5>2, <5>3
          <5>5. bkt_arr[idx].val \in ValDomain
            BY Zenon, <5>4
          <5>6. ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) = bkt_arr[idx].val
            BY DEF ValOfKeyInBktAtAddr
          <5> QED
            BY Zenon, <5>5, <5>6
        <4>6. ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) # NULL
          BY <4>5, NULLDef
        <4> SUFFICES c.res = [c_pred.res EXCEPT ![p] = c_pred.state[c_pred.arg[p].key]]
          BY <4>2, <4>3, <4>4, <4>6, Zenon DEF Delta
        <4> SUFFICES c.res[p] = c_pred.state[c_pred.arg[p].key]
          BY <3>2, Zenon DEF ConfigDomain, S
        <4>7. pc'[p] = "I2" /\ KeyInBktAtAddr(arg[p].key, bucket[p])'
          BY Zenon DEF KeyInBktAtAddr
        <4>8. c.res[p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p])'
          BY <4>7, SPrimeRewrite, RemDef, Zenon DEF SPrime
        <4>9. ValOfKeyInBktAtAddr(arg[p].key, bucket[p])' = ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])
          <5> DEFINE bkt_arr == MemLocs'[bucket'[p]]
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[p].key
          <5>1. ValOfKeyInBktAtAddr(arg[p].key, bucket[p])' = bkt_arr[idx].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5> DEFINE bkt_arr2 == MemLocs[A[Hash[arg[p].key]]]
          <5> DEFINE idx2 == CHOOSE index \in 1..Len(bkt_arr2) : bkt_arr2[index].key = arg[p].key
          <5>2. ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) = bkt_arr2[idx2].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>3. bkt_arr = bkt_arr2 /\ idx = idx2
            BY ZenonT(30)
          <5> QED
            BY <5>1, <5>2, <5>3, Zenon
        <4> QED
          BY <4>8, <4>9, <4>4, Zenon
      <3> QED
        BY <3>1, <3>2, <3>3, SingleDeltaEvolve
    <2> QED
      BY <2>1, <2>2
  <1>2. CASE I2(p)
    <2> USE <1>2 DEF I2
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
        <4>1. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
          BY <4>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4>3. arg[q].key = arg'[q].key /\ arg[q].key \in KeyDomain
          BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
        <4>4. c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY <4>2, <4>3, <3>2
        <4> QED
          BY <4>2, <4>4
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
        <4>1. CASE p = q
          <5> USE <4>1
          <5>1. c.op[p] = "Insert" /\ c.arg[p] = arg[p] /\ c.res[p] = r'[p]
            BY SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>2. r'[p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p])
            BY Zenon
          <5> QED
            BY <5>1, <5>2
        <4> SUFFICES ASSUME p # q
                      PROVE  c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY <4>1
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
        <4>1. CASE p = q
          <5> USE <4>1
          <5>1. c.op[p] = "Insert" /\ c.arg[p] = arg[p] /\ c.res[p] = BOT
            BY SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>1
        <4> SUFFICES ASSUME p # q
                      PROVE  c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1
        <4>2. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>2, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>3 
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
  <1>3. CASE I3(p)
    <2> USE <1>3 DEF I3, TypeOK, Inv
    <2> SUFFICES ASSUME NEW c \in ConfigDomain,
                        c \in S'
                 PROVE  c \in Evolve(S)
      BY Zenon DEF S
    <2> SUFFICES c \in S
      BY EmptySeqEvolve
    <2>1. CASE bucket[p] = NULL
      <3> PICK addr \in Addrs : 
                    /\ addr \notin AllocAddrs
                    /\ AllocAddrs' = AllocAddrs \cup {addr}
                    /\ newbkt' = [newbkt EXCEPT ![p] = addr]
                    /\ MemLocs' = [MemLocs EXCEPT ![addr] = <<arg[p]>>]
        BY <2>1, Zenon
      <3>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
        <4>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
          BY Zenon, SPrimeRewrite DEF SPrime
        <4>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
          <5> SUFFICES ASSUME NEW k \in KeyDomain
                        PROVE  KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
            OBVIOUS
          <5>1. A'[Hash[k]] = A[Hash[k]]
            BY Zenon
          <5>2. CASE A[Hash[k]] = NULL
            BY <5>1, <5>2 DEF KeyInBktAtAddr
          <5> SUFFICES ASSUME A[Hash[k]] # NULL
                        PROVE  KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
            BY <5>2
          <5>3. A[Hash[k]] \in AllocAddrs
            BY HashDef, Zenon
          <5>4. A[Hash[k]] # addr
            BY NULLDef, <5>3
          <5>5. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
            BY Zenon
          <5>6. MemLocs'[A'[Hash[k]]] = MemLocs[A[Hash[k]]]
            BY <5>1, <5>4, <5>5
          <5> QED
            BY <5>6, Zenon DEF KeyInBktAtAddr
        <4>3. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) => (ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])')
          <5> SUFFICES ASSUME NEW k \in KeyDomain,
                              NEW bkt_arr,
                              A[Hash[k]] # NULL,
                              bkt_arr = MemLocs[A[Hash[k]]],
                              \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                        PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
            BY Zenon DEF KeyInBktAtAddr
          <5>1. A'[Hash[k]] = A[Hash[k]]
            BY Zenon
          <5>2. A[Hash[k]] \in AllocAddrs
            BY HashDef, Zenon
          <5>3. A[Hash[k]] # addr
            BY NULLDef, <5>2
          <5>4. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
            BY Zenon
          <5>5. MemLocs'[A'[Hash[k]]] = MemLocs[A[Hash[k]]]
            BY <5>1, <5>3, <5>4
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
          <5>6. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = bkt_arr[idx].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>7. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
            BY Isa, <5>5 DEF ValOfKeyInBktAtAddr
          <5> QED
            BY <5>6, <5>7, Zenon
        <4> QED
          BY <4>1, <4>2, <4>3, Zenon
      <3>2. ASSUME NEW q \in ProcSet
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
        <4> USE <3>2
        <4>1. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
          <5>1. bucket[q] = bucket'[q]
            BY Zenon
          <5>2. CASE bucket[q] = NULL
            BY <5>1, <5>2, Zenon DEF KeyInBktAtAddr
          <5> SUFFICES ASSUME bucket[q] # NULL
                        PROVE  KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>2
          <5>3. bucket[q] \in AllocAddrs
            BY NULLDef, Zenon
          <5>4. bucket[q] # addr
            BY <5>3
          <5>5. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
            BY Zenon
          <5>6. MemLocs'[bucket'[q]] = MemLocs[bucket[q]]
            BY <5>1, <5>4, <5>5
          <5> QED
            BY <5>6, Zenon DEF KeyInBktAtAddr
        <4>2. KeyInBktAtAddr(arg[q].key, bucket[q]) => (ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])')
          <5> SUFFICES ASSUME NEW bkt_arr,
                              bkt_arr = MemLocs[bucket[q]],
                              bucket[q] # NULL,
                              \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                        PROVE  ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY Zenon DEF KeyInBktAtAddr
          <5>1. bucket[q] = bucket'[q]
            BY Zenon
          <5>2. bucket[q] \in AllocAddrs
            BY NULLDef, Zenon
          <5>3. bucket[q] # addr
            BY <5>2
          <5>4. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
            BY Zenon
          <5>5. MemLocs'[bucket'[q]] = MemLocs[bucket[q]]
            BY <5>1, <5>3, <5>4 
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
          <5>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = bkt_arr[idx].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
            BY Isa, <5>5 DEF ValOfKeyInBktAtAddr
          <5> QED
            BY <5>6, <5>7, Zenon
        <4>3. CASE pc[q] = RemainderID
          <5> USE <4>3
          <5> SUFFICES c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = RemainderID
            BY RemDef, Zenon
          <5>2. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>4. CASE pc[q] = "F1"
          <5> USE <4>4
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = "F1"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2  
        <4>5. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>5
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>1, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY <4>2, Zenon
          <5> QED
            BY <5>2, <5>3
        <4>6. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>6
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY RemDef, Zenon
          <5>1. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>1, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>7. CASE pc[q] = "F3" 
          <5> USE <4>7
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "F3"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>8. CASE pc[q] \in {"I1", "I3", "I4"}
          <5> USE <4>8
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. CASE p = q
            <6> USE <5>1
            <6>1. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>1
          <5> SUFFICES ASSUME p # q
                        PROVE  c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1
          <5>2. pc'[q] \in {"I1", "I3", "I4"}
            BY RemDef, Zenon
          <5>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>3
        <4>9. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>9
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>1, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY <4>2, Zenon
          <5> QED
            BY <5>2, <5>3
        <4>10. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>10
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>1, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>11. CASE pc[q] = "I5"
          <5> USE <4>11
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "I5"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>12. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
          <5> USE <4>12
          <5> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] \in {"U1", "U2", "U3", "U4"}
            BY RemDef, Zenon
          <5>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>13. CASE pc[q] = "U5" 
          <5> USE <4>13
          <5> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "U5"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>14. CASE pc[q] \in {"R1", "R3", "R4"}
          <5> USE <4>14
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] \in {"R1", "R3", "R4"}
            BY RemDef, Zenon
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>15. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>15
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>1, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>16. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>16
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY RemDef, Zenon
          <5>1. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>1, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>17. CASE pc[q] = "R5"
          <5> USE <4>17
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "R5"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4> QED
            BY RemDef, ZenonT(120),
                <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10, <4>11, 
                <4>12, <4>13, <4>14, <4>15, <4>16, <4>17
            DEF LineIDs
      <3> QED
        BY <3>1, <3>2, Zenon DEF S
    <2>2. CASE bucket[p] # NULL
      <3> PICK addr \in Addrs : 
                    /\ addr \notin AllocAddrs
                    /\ AllocAddrs' = AllocAddrs \cup {addr}
                    /\ newbkt' = [newbkt EXCEPT ![p] = addr]
                    /\ MemLocs' = [MemLocs EXCEPT ![addr] = Append(MemLocs[bucket[p]], arg[p])]
        BY <2>2, Zenon
      <3>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
        <4>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
          BY Zenon, SPrimeRewrite DEF SPrime
        <4>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
          <5> SUFFICES ASSUME NEW k \in KeyDomain
                        PROVE  KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
            OBVIOUS
          <5>1. A'[Hash[k]] = A[Hash[k]]
            BY Zenon
          <5>2. CASE A[Hash[k]] = NULL
            BY <5>1, <5>2 DEF KeyInBktAtAddr
          <5> SUFFICES ASSUME A[Hash[k]] # NULL
                        PROVE  KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
            BY <5>2
          <5>3. A[Hash[k]] \in AllocAddrs
            BY HashDef, Zenon
          <5>4. A[Hash[k]] # addr
            BY NULLDef, <5>3
          <5>5. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
            BY Zenon
          <5>6. MemLocs'[A'[Hash[k]]] = MemLocs[A[Hash[k]]]
            BY <5>1, <5>4, <5>5
          <5> QED
            BY <5>6, Zenon DEF KeyInBktAtAddr
        <4>3. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) => (ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])')
          <5> SUFFICES ASSUME NEW k \in KeyDomain,
                              NEW bkt_arr,
                              A[Hash[k]] # NULL,
                              bkt_arr = MemLocs[A[Hash[k]]],
                              \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                        PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
            BY Zenon DEF KeyInBktAtAddr
          <5>1. A'[Hash[k]] = A[Hash[k]]
            BY Zenon
          <5>2. A[Hash[k]] \in AllocAddrs
            BY HashDef, Zenon
          <5>3. A[Hash[k]] # addr
            BY NULLDef, <5>2
          <5>4. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
            BY Zenon
          <5>5. MemLocs'[A'[Hash[k]]] = MemLocs[A[Hash[k]]]
            BY <5>1, <5>3, <5>4
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
          <5>6. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = bkt_arr[idx].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>7. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
            BY Isa, <5>5 DEF ValOfKeyInBktAtAddr
          <5> QED
            BY <5>6, <5>7, Zenon
        <4> QED
          BY <4>1, <4>2, <4>3, Zenon
      <3>2. ASSUME NEW q \in ProcSet
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
        <4> USE <3>2
        <4>A. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
          <5>1. bucket[q] = bucket'[q]
            BY Zenon
          <5>2. CASE bucket[q] = NULL
            BY <5>1, <5>2, Zenon DEF KeyInBktAtAddr
          <5> SUFFICES ASSUME bucket[q] # NULL
                        PROVE  KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>2
          <5>3. bucket[q] \in AllocAddrs
            BY NULLDef, Zenon
          <5>4. bucket[q] # addr
            BY <5>3
          <5>5. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
            BY Zenon
          <5>6. MemLocs'[bucket'[q]] = MemLocs[bucket[q]]
            BY <5>1, <5>4, <5>5
          <5> QED
            BY <5>6, Zenon DEF KeyInBktAtAddr
        <4>B. KeyInBktAtAddr(arg[q].key, bucket[q]) => (ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])')
          <5> SUFFICES ASSUME NEW bkt_arr,
                              bkt_arr = MemLocs[bucket[q]],
                              bucket[q] # NULL,
                              \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                        PROVE  ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY Zenon DEF KeyInBktAtAddr
          <5>1. bucket[q] = bucket'[q]
            BY Zenon
          <5>2. bucket[q] \in AllocAddrs
            BY NULLDef, Zenon
          <5>3. bucket[q] # addr
            BY <5>2
          <5>4. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
            BY Zenon
          <5>5. MemLocs'[bucket'[q]] = MemLocs[bucket[q]]
            BY <5>1, <5>3, <5>4 
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
          <5>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = bkt_arr[idx].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
            BY Isa, <5>5 DEF ValOfKeyInBktAtAddr
          <5> QED
            BY <5>6, <5>7, Zenon
        <4>1. CASE pc[q] = RemainderID
          <5> USE <4>1
          <5> SUFFICES c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = RemainderID
            BY RemDef, Zenon
          <5>2. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>2. CASE pc[q] = "F1"
          <5> USE <4>2
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = "F1"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2  
        <4>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>3
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>A, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY <4>B, Zenon
          <5> QED
            BY <5>2, <5>3
        <4>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>4
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY RemDef, Zenon
          <5>1. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>A, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>5. CASE pc[q] = "F3" 
          <5> USE <4>5
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "F3"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>6. CASE pc[q] \in {"I1", "I3", "I4"}
          <5> USE <4>6
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. CASE p = q
            <6> USE <5>1
            <6>1. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>1
          <5> SUFFICES ASSUME p # q
                        PROVE  c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1
          <5>2. pc'[q] \in {"I1", "I3", "I4"}
            BY RemDef, Zenon
          <5>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>3
        <4>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>7
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>A, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY <4>B, Zenon
          <5> QED
            BY <5>2, <5>3
        <4>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>8
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>A, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>9. CASE pc[q] = "I5"
          <5> USE <4>9
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "I5"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
          <5> USE <4>10
          <5> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] \in {"U1", "U2", "U3", "U4"}
            BY RemDef, Zenon
          <5>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>11. CASE pc[q] = "U5" 
          <5> USE <4>11
          <5> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "U5"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>12. CASE pc[q] \in {"R1", "R3", "R4"}
          <5> USE <4>12
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] \in {"R1", "R3", "R4"}
            BY RemDef, Zenon
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>13
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>A, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>14
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY RemDef, Zenon
          <5>1. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>A, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>15. CASE pc[q] = "R5"
          <5> USE <4>15
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "R5"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4> QED
            BY RemDef, ZenonT(120),
                <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, 
                <4>10, <4>11, <4>12, <4>13, <4>14, <4>15
            DEF LineIDs
      <3> QED
        BY <3>1, <3>2, Zenon DEF S
    <2> QED
      BY <2>1, <2>2
  <1>4. CASE I4(p)
    <2> USE <1>4 DEF I4, TypeOK, Inv
    <2> SUFFICES ASSUME NEW c \in ConfigDomain,
                        c \in S'
                 PROVE  c \in Evolve(S)
      BY Zenon DEF S
    <2>1. CASE A[Hash[arg[p].key]] = bucket[p]
      <3> USE <2>1
      <3> DEFINE c_pred == [state |-> [c.state EXCEPT ![arg[p].key] = NULL],
                            op    |-> c.op,
                            arg   |-> c.arg,
                            res   |-> [c.res EXCEPT ![p] = BOT]]
      <3>1. c_pred \in ConfigDomain
        <4>1. c_pred.state \in StateDomain
          BY Zenon DEF ConfigDomain, StateDomain
        <4>2. c_pred.op \in [ProcSet -> OpDomain]
          BY DEF ConfigDomain
        <4>3. c_pred.arg \in [ProcSet -> ArgDomain]
          BY DEF ConfigDomain
        <4>4. c_pred.res \in [ProcSet -> ResDomain]
          BY DEF ConfigDomain, ResDomain
        <4> QED
          BY <4>1, <4>2, <4>3, <4>4 DEF ConfigDomain
      <3>2. c_pred \in S
        <4>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
          <5> SUFFICES ASSUME NEW k \in KeyDomain
                        PROVE  c_pred.state[k] = IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL
            BY Zenon, <3>1 DEF StateDomain, ConfigDomain
          <5>1. CASE k = arg[p].key
            <6> USE <5>1
            <6>1. ~KeyInBktAtAddr(k, A[Hash[k]])
              BY Zenon DEF BktInv
            <6>2. c_pred.state[k] = NULL
              BY Zenon DEF ConfigDomain, StateDomain
            <6> QED
              BY <6>1, <6>2
          <5>2. CASE k # arg[p].key /\ Hash[k] # Hash[arg[p].key]
            <6> USE <5>2
            <6>1. c.state = [key \in KeyDomain |-> IF KeyInBktAtAddr(key, A[Hash[key]])' THEN ValOfKeyInBktAtAddr(key, A[Hash[key]])' ELSE NULL]
              BY SPrimeRewrite, Zenon DEF SPrime
            <6>2. A'[Hash[k]] = A[Hash[k]]
              BY HashDef, Zenon
            <6>3. KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
              BY <6>2, Zenon DEF KeyInBktAtAddr
            <6>4. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
              <7> DEFINE bkt_arr == MemLocs'[A'[Hash[k]]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[A[Hash[k]]]
                BY Zenon, <6>2
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7>4. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = MemLocs[A[Hash[k]]][CHOOSE index \in 1..Len(MemLocs[A[Hash[k]]]) : MemLocs[A[Hash[k]]][index].key = k].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>5. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = bkt_arr[idx].val
                BY ZenonT(90), <7>2, <7>3, <7>4
              <7> QED
                BY Zenon, <7>1, <7>5
            <6> QED
              BY <6>1, <6>3, <6>4
          <5>3. CASE k # arg[p].key /\ Hash[k] = Hash[arg[p].key]
            <6> USE <5>3
            <6>1. c.state = [key \in KeyDomain |-> IF KeyInBktAtAddr(key, A[Hash[key]])' 
                                                      THEN ValOfKeyInBktAtAddr(key, A[Hash[key]])' 
                                                      ELSE NULL]
              BY SPrimeRewrite, Zenon DEF SPrime
            <6>2. c_pred.state[k] = IF KeyInBktAtAddr(k, A[Hash[k]])' 
                                        THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' 
                                        ELSE NULL
              BY <6>1
            <6>3. MemLocs' = MemLocs
              BY Zenon
            <6>4. bucket[p] = A[Hash[k]]
              BY Zenon
            <6>5. arg[p].key \in KeyDomain
              BY RemDef, Zenon DEF ArgsOf, LineIDtoOp
            <6>6. newbkt[p] = A'[Hash[k]]
              BY Zenon, <6>5, HashDef
            <6>7. KeyInBktAtAddr(k, A[Hash[k]])' = KeyInBktAtAddr(k, newbkt[p])
              BY <6>6, Zenon DEF KeyInBktAtAddr
            <6>8. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, newbkt[p])
              BY <6>6, Zenon DEF ValOfKeyInBktAtAddr
            <6>9. c_pred.state[k] = IF KeyInBktAtAddr(k, newbkt[p]) THEN ValOfKeyInBktAtAddr(k, newbkt[p]) ELSE NULL
              BY <6>2, <6>7, <6>8, Zenon
            <6>10. /\ KeyInBktAtAddr(k, bucket[p]) = KeyInBktAtAddr(k, newbkt[p])
                   /\ KeyInBktAtAddr(k, bucket[p]) => (ValOfKeyInBktAtAddr(k, bucket[p]) = ValOfKeyInBktAtAddr(k, newbkt[p]))
              BY Zenon DEF NewBktInv
            <6>11. c_pred.state[k] = IF KeyInBktAtAddr(k, bucket[p]) THEN ValOfKeyInBktAtAddr(k, bucket[p]) ELSE NULL
              BY <6>9, <6>10, Zenon
            <6>12. c_pred.state[k] = IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL
              BY <6>11, <6>6, Zenon
            <6> QED
              BY <6>12, Zenon
          <5> QED
            BY <5>1, <5>2, <5>3
        <4>2. ASSUME NEW q \in ProcSet
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
          <5> USE <4>2
          <5>1. CASE pc[q] = RemainderID
            <6> USE <5>1
            <6> SUFFICES c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = RemainderID
              BY RemDef, Zenon
            <6>4. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>2. CASE pc[q] = "F1"
            <6> USE <5>2
            <6> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "F1"
              BY RemDef, Zenon
            <6>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
            <6> USE <5>3
            <6> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              <7> DEFINE bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
              <7>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>2, <6>4, <6>5
          <5>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
            <6> USE <5>4
            <6> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>5. CASE pc[q] = "F3"
            <6> USE <5>5
            <6> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "F3"
              BY RemDef, Zenon
            <6>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4 
          <5>6. CASE pc[q] \in {"I1", "I3", "I4"}
            <6> USE <5>6
            <6> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>A. CASE p = q
              <7> USE <6>A
              <7>1. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = BOT
                BY <3>1 DEF ConfigDomain
              <7>2. pc'[q] = "I5"
                BY Zenon
              <7>3. c.op[q] = "Insert" /\ c.arg[p] = arg[q]
                BY <7>2, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>1, <7>3
            <6> SUFFICES ASSUME p # q
                          PROVE  c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY <6>A
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              OBVIOUS
            <6>3. pc'[q] \in {"I1", "I3", "I4"}
              BY RemDef, Zenon
            <6>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
            <6> USE <5>7
            <6> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              <7> DEFINE bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
              <7>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>2, <6>4, <6>5
          <5>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
            <6> USE <5>8
            <6> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>9. CASE pc[q] = "I5"
            <6> USE <5>9
            <6> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "I5"
              BY RemDef, Zenon
            <6>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
            <6> USE <5>10
            <6> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] \in {"U1", "U2", "U3", "U4"}
              BY RemDef, Zenon
            <6>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>11. CASE pc[q] = "U5" 
            <6> USE <5>11
            <6> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "U5"
              BY RemDef, Zenon
            <6>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>12. CASE pc[q] \in {"R1", "R3", "R4"}
            <6> USE <5>12
            <6> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] \in {"R1", "R3", "R4"}
              BY RemDef, Zenon
            <6>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q]) 
            <6> USE <5>13
            <6> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4              
          <5>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
            <6> USE <5>14
            <6> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4    
          <5>15. CASE pc[q] = "R5"
            <6> USE <5>15
            <6> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "R5"
              BY RemDef, Zenon
            <6>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5> QED
              BY RemDef, ZenonT(120),
                  <5>1, <5>2, <5>3, <5>4, <5>5, <5>6, <5>7, <5>8, <5>9, 
                  <5>10, <5>11, <5>12, <5>13, <5>14, <5>15
              DEF LineIDs 
        <4> QED
          BY <3>1, <4>1, <4>2, Zenon DEF S
      <3>3. Delta(c_pred, p, c)
        <4>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
          BY <3>1, <3>2, Zenon DEF S
        <4>2. c_pred.op[p] = "Insert" /\ c_pred.arg[p] = arg[p] /\ c_pred.res[p] = BOT
          BY <3>1, <3>2, Zenon, RemDef DEF S
        <4>3. arg[p] \in ArgsOf("Insert") /\ arg[p].key \in KeyDomain
          BY RemDef, Zenon DEF ArgsOf, LineIDtoOp 
        <4>4. c_pred.state[c_pred.arg[p].key] = NULL
          BY <4>1, <4>2, <4>3, Zenon DEF BktInv
        <4> SUFFICES /\ c.state = [c_pred.state EXCEPT ![arg[p].key] = arg[p].val]
                     /\ c.res = [c_pred.res EXCEPT ![p] = NULL]
          BY <4>2, <4>3, <4>4, Zenon DEF Delta
        <4> SUFFICES /\ c.state[arg[p].key] = arg[p].val
                     /\ c.res[p] = NULL
          BY <3>2, <4>3, ZenonT(60) DEF ConfigDomain, StateDomain
        <4>5. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
          BY SPrimeRewrite, Zenon DEF SPrime
        <4>6. c.state[arg[p].key] = IF KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])' THEN ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])' ELSE NULL
          BY <4>5, <4>3, Zenon
        <4>7. newbkt[p] = A'[Hash[arg[p].key]]
          BY Zenon, HashDef, <4>3
        <4>8. MemLocs[A'[Hash[arg[p].key]]] = MemLocs[newbkt[p]]
          BY Zenon, <4>7
        <4>9. KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])' = KeyInBktAtAddr(arg[p].key, newbkt[p])
          BY Zenon, <4>7 DEF KeyInBktAtAddr
        <4>10. ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])' = 
          MemLocs[A'[Hash[arg[p].key]]][CHOOSE index \in 1..Len(MemLocs[A'[Hash[arg[p].key]]]) : MemLocs[A'[Hash[arg[p].key]]][index].key = arg[p].key].val
          BY Zenon DEF ValOfKeyInBktAtAddr
        <4>11. ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])' = 
          MemLocs[newbkt[p]][CHOOSE index \in 1..Len(MemLocs[newbkt[p]]) : MemLocs[newbkt[p]][index].key = arg[p].key].val
          BY <4>10, <4>8
        <4>12. ValOfKeyInBktAtAddr(arg[p].key, newbkt[p]) = 
          MemLocs[newbkt[p]][CHOOSE index \in 1..Len(MemLocs[newbkt[p]]) : MemLocs[newbkt[p]][index].key = arg[p].key].val
          BY Zenon DEF ValOfKeyInBktAtAddr
        <4>13. ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])' = ValOfKeyInBktAtAddr(arg[p].key, newbkt[p])
          BY <4>11, <4>12, Zenon
        <4>14. c.state[arg[p].key] = IF KeyInBktAtAddr(arg[p].key, newbkt[p]) THEN ValOfKeyInBktAtAddr(arg[p].key, newbkt[p]) ELSE NULL
          BY <4>6, <4>9, <4>13, Zenon
        <4>15. c.state[arg[p].key] = arg[p].val
          BY <4>14, Zenon DEF NewBktInv
        <4>16. pc'[p] = "I5"
          BY Zenon
        <4>17. c.res[p] = r'[p]
          BY <4>16, SPrimeRewrite, RemDef, Zenon DEF SPrime
        <4>18. c.res[p] = NULL
          BY <4>17, Zenon DEF BktInv
        <4> QED
          BY <4>18, <4>15
      <3> QED
        BY <3>1, <3>2, <3>3, SingleDeltaEvolve
    <2>2. CASE A[Hash[arg[p].key]] # bucket[p]
      <3> USE <2>2
      <3> SUFFICES c \in S
        BY EmptySeqEvolve
      <3>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
        <4>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
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
        <4> USE <3>2
        <4>A. \A k \in KeyDomain : KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
          BY Zenon DEF KeyInBktAtAddr
        <4>B. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, bucket[q])
          <5> SUFFICES ASSUME NEW k \in KeyDomain
                        PROVE  ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, bucket[q])
            OBVIOUS
          <5> bkt_arr == MemLocs'[bucket'[q]]
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
          <5>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
            BY DEF ValOfKeyInBktAtAddr
          <5>2. bkt_arr = MemLocs[bucket[q]]
            BY Zenon
          <5> QED
            BY <5>1, <5>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
        <4>1. CASE pc[q] = RemainderID
          <5> USE <4>1
          <5> SUFFICES c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = RemainderID
            BY RemDef, Zenon
          <5>2. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>2. CASE pc[q] = "F1"
          <5> USE <4>2
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = "F1"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>3
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>3. arg[q].key = arg'[q].key /\ arg[q].key \in KeyDomain
            BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
          <5>4. c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY <5>2, <5>3, <4>B
          <5> QED
            BY <5>2, <5>4
        <4>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>4
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY RemDef, Zenon
          <5>2. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>3. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>3
        <4>5. CASE pc[q] = "F3"
          <5> USE <4>5
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "F3"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2 
        <4>6. CASE pc[q] \in {"I1", "I3", "I4"}
          <5> USE <4>6
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] \in {"I1", "I3", "I4"}
            BY RemDef, Zenon
          <5>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2 
        <4>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>7
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. CASE p = q
            <6> USE <5>1
            <6>1. c.op[p] = "Insert" /\ c.arg[p] = arg[p] /\ c.res[p] = r'[p]
              BY SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6>2. r'[p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p])
              BY Zenon
            <6> QED
              BY <6>1, <6>2
          <5> SUFFICES ASSUME p # q
                        PROVE  c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY <5>1
          <5>2. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>4. arg[q].key = arg'[q].key /\ arg[q].key \in KeyDomain
            BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
          <5>5. c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY <5>3, <5>4, <4>B
          <5> QED
            BY <5>3, <5>5
        <4>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>8
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. CASE p = q
            <6> USE <5>1
            <6>1. c.op[p] = "Insert" /\ c.arg[p] = arg[p] /\ c.res[p] = BOT
              BY SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>1
          <5> SUFFICES ASSUME p # q
                        PROVE  c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1
          <5>2. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>2, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>3 
        <4>9. CASE pc[q] = "I5"
          <5> USE <4>9
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "I5"
            BY RemDef, Zenon 
          <5>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2 
        <4>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
          <5> USE <4>10
          <5> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] \in {"U1", "U2", "U3", "U4"}
            BY RemDef, Zenon
          <5>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>11. CASE pc[q] = "U5" 
          <5> USE <4>11
          <5> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "U5"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>12. CASE pc[q] \in {"R1", "R3", "R4"}
          <5> USE <4>12
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] \in {"R1", "R3", "R4"}
            BY RemDef, Zenon
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>13
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>14
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY RemDef, Zenon
          <5>1. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>15. CASE pc[q] = "R5"
          <5> USE <4>15
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "R5" 
            BY RemDef, Zenon
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4> QED
            BY RemDef, ZenonT(120),
                <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, 
                <4>10, <4>11, <4>12, <4>13, <4>14, <4>15
            DEF LineIDs
      <3> QED
        BY <3>1, <3>2, Zenon DEF S
    <2> QED
      BY <2>1, <2>2
  <1> QED
    BY <1>1, <1>2, <1>3, <1>4

============================================================================================
\* Modification History
\* Last modified Tue Aug 27 13:20:52 EDT 2024 by uguryavuz
\* Created Mon Jul 08 12:21:04 EDT 2024 by uyavuz
