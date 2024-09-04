--------------------------- MODULE MCTracking_invoc_proofs ---------------------------
(***************************************************************************
 This module contains the proof of LinInvocationLine from MCTracking.tla
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

\* LinInvocationLine = 
\*   Inv /\ InvocnAction => S' \in SUBSET Evolve(Invoke(S, InvokerProc, LineIDtoOp(pc'[InvokerProc]), arg'[InvokerProc]))
THEOREM LinInvocationLine
  <1> SUFFICES ASSUME Inv,
                      NEW p \in ProcSet,
                      InvokeLine(p)
               PROVE  S' \in SUBSET Evolve(Invoke(S, p, LineIDtoOp(pc'[p]), arg'[p]))
    BY UniqueInvoker DEF Inv, InvocnAction
  <1> SUFFICES ASSUME pc[p] = RemainderID,
                      NEW op \in OpNames,
                      pc' = [pc EXCEPT ![p] = OpToInvocLine(op)],
                      NEW new_arg \in ArgsOf(op),
                      arg' = [arg EXCEPT ![p] = new_arg],
                      UNCHANGED <<A, MemLocs, AllocAddrs, bucket, newbkt, r, ret>>
               PROVE  S' \in SUBSET Evolve(Invoke(S, p, LineIDtoOp(pc'[p]), arg'[p]))
    BY Zenon DEF InvokeLine
  <1>A. LineIDtoOp(pc'[p]) = op
    BY ZenonT(120) DEF Inv, TypeOK, OpToInvocLine, LineIDtoOp, OpNames
  <1>B. arg'[p] \in ArgsOf(op)
    BY DEF Inv, TypeOK 
  <1> SUFFICES ASSUME NEW c \in ConfigDomain,
                      c \in S'
               PROVE  c \in Evolve(Invoke(S, p, op, arg'[p]))
    BY <1>A, Zenon DEF S
  <1> USE DEF Inv, TypeOK
  <1> DEFINE c_pred == [state |-> c.state,
                        op    |-> [c.op EXCEPT ![p] = BOT],
                        arg   |-> [c.arg EXCEPT ![p] = BOT],
                        res   |-> [c.res EXCEPT ![p] = BOT]]
  <1>1. c_pred \in ConfigDomain
    <2>1. c_pred.state \in StateDomain
      BY DEF ConfigDomain
    <2>2. c_pred.op \in [ProcSet -> OpDomain]
      BY DEF ConfigDomain, OpDomain
    <2>3. c_pred.arg \in [ProcSet -> ArgDomain]
      BY DEF ConfigDomain, ArgDomain
    <2>4. c_pred.res \in [ProcSet -> ResDomain]
      BY DEF ConfigDomain, ResDomain
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4 DEF ConfigDomain
  <1>2. c_pred \in S
    <2>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
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
      <3> QED
        BY <3>1
    <2>2. ASSUME NEW q \in ProcSet
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
      <3> USE <2>2
      <3>1. CASE pc[q] = RemainderID
        <4> SUFFICES c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT
          BY <3>1, RemDef, Zenon
        <4>A. CASE q = p
          BY <4>A DEF ConfigDomain
        <4> SUFFICES ASSUME q # p
                      PROVE  c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT
          BY <4>A
        <4>1. q # p
          BY <3>1, RemDef, Zenon
        <4>X. c_pred.op = [c.op EXCEPT ![p] = BOT]
          OBVIOUS
        <4>Y. \A p1 \in ProcSet : p1 # p => c_pred.op[p1] = c.op[p1]
          OBVIOUS

        <4>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
          BY <4>1
        <4>3. pc'[q] = RemainderID
          BY <3>1, RemDef, Zenon
        <4>4. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
          BY <4>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2, <4>4
      <3>2. CASE pc[q] = "F1"
        <4> USE <3>2
        <4> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
          BY RemDef, Zenon
        <4>1. q # p
          BY RemDef, Zenon
        <4>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
          BY <4>1
        <4>3. pc'[q] = "F1"
          BY RemDef, Zenon
        <4>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2, <4>4
      <3>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>3
        <4> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY RemDef, Zenon
        <4>1. q # p
          BY RemDef, Zenon
        <4>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
          BY <4>1
        <4>3. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
          BY <4>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          <5> DEFINE bkt_arr == MemLocs'[bucket'[q]]
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
          <5>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>2. bkt_arr = MemLocs[bucket[q]]
            BY Zenon
          <5>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
            BY <4>1, Zenon
          <5>4. ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) =
                MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][index].key = arg[q].key].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = bkt_arr[idx].val
            BY <5>2, <5>3, <5>4, Zenon
          <5> QED
            BY <5>1, <5>5
        <4> QED
          BY <4>2, <4>4, <4>5
      <3>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>4
        <4> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
          BY RemDef, Zenon
        <4>1. q # p
          BY RemDef, Zenon
        <4>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
          BY <4>1
        <4>3. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
          BY <4>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2, <4>4
      <3>5. CASE pc[q] = "F3"
        <4> USE <3>5
        <4> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
          BY <3>5, RemDef, Zenon
        <4>1. q # p
          BY RemDef, Zenon
        <4>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
          BY <4>1
        <4>3. pc'[q] = "F3"
          BY <3>5, RemDef, Zenon
        <4>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY <4>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2, <4>4
      <3>6. CASE pc[q] \in {"I1", "I3", "I4"}
        <4> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
          BY <3>6, RemDef, Zenon
        <4>1. q # p
          BY <3>6, RemDef, Zenon
        <4>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
          BY <4>1
        <4>3. pc'[q] \in {"I1", "I3", "I4"}
          BY <3>6, RemDef, Zenon
        <4>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1, <4>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2, <4>4
      <3>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>7
        <4> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY RemDef, Zenon
        <4>1. q # p
          BY RemDef, Zenon
        <4>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
          BY <4>1
        <4>3. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
          BY <4>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          <5> DEFINE bkt_arr == MemLocs'[bucket'[q]]
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
          <5>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>2. bkt_arr = MemLocs[bucket[q]]
            BY Zenon
          <5>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
            BY <4>1, Zenon
          <5>4. ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) =
                MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][index].key = arg[q].key].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = bkt_arr[idx].val
            BY <5>2, <5>3, <5>4, Zenon
          <5> QED
            BY <5>1, <5>5
        <4> QED
          BY <4>2, <4>4, <4>5
      <3>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>8
        <4> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
          BY RemDef, Zenon
        <4>1. q # p
          BY RemDef, Zenon
        <4>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
          BY <4>1
        <4>3. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2, <4>4
      <3>9. CASE pc[q] = "I5"
        <4> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
          BY <3>9, RemDef, Zenon
        <4>1. q # p
          BY <3>9, RemDef, Zenon
        <4>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
          BY <4>1
        <4>3. pc'[q] = "I5"
          BY <3>9, RemDef, Zenon
        <4>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY <4>1, <4>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2, <4>4
      <3>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
        <4> USE <3>10
        <4> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
          BY RemDef, Zenon
        <4>1. q # p
          BY RemDef, Zenon
        <4>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
          BY <4>1
        <4>3. pc'[q] \in {"U1", "U2", "U3", "U4"}
          BY RemDef, Zenon
        <4>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2, <4>4
      <3>11. CASE pc[q] = "U5"
        <4> USE <3>11
        <4> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
          BY RemDef, Zenon
        <4>1. q # p
          BY RemDef, Zenon
        <4>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
          BY <4>1
        <4>3. pc'[q] = "U5"
          BY RemDef, Zenon
        <4>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY <4>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2, <4>4
      <3>12. CASE pc[q] \in {"R1", "R3", "R4"}
        <4> USE <3>12
        <4> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
          BY RemDef, Zenon
        <4>1. q # p
          BY RemDef, Zenon
        <4>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
          BY <4>1
        <4>3. pc'[q] \in {"R1", "R3", "R4"}
          BY RemDef, Zenon
        <4>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2, <4>4
      <3>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>13
        <4> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
          BY RemDef, Zenon
        <4>1. q # p
          BY RemDef, Zenon
        <4>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
          BY <4>1
        <4>3. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2, <4>4
      <3>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>14
        <4> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
          BY RemDef, Zenon
        <4>1. q # p
          BY RemDef, Zenon
        <4>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
          BY <4>1
        <4>3. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
          BY <4>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2, <4>4
      <3>15. CASE pc[q] = "R5"
        <4> USE <3>15
        <4> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
          BY RemDef, Zenon
        <4>1. q # p
          BY RemDef, Zenon
        <4>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
          BY <4>1
        <4>3. pc'[q] = "R5"
          BY RemDef, Zenon
        <4>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY <4>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2, <4>4
      <3> QED
        BY RemDef, ZenonT(120),
            <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, 
            <3>10, <3>11, <3>12, <3>13, <3>14, <3>15
        DEF LineIDs
    <2> QED
      BY <1>1, <2>1, <2>2, Zenon DEF S
  <1>3. c_pred.op[p] = BOT /\ c_pred.arg[p] = BOT /\ c_pred.res[p] = BOT
    BY <1>1 DEF ConfigDomain
  <1>4. c.op[p] = op /\ c.arg[p] = arg'[p] /\ c.res[p] = BOT
    <2>1. CASE op = "Find"   /\ pc'[p] = "F1"
      BY <2>1, Zenon, RemDef, SPrimeRewrite DEF SPrime
    <2>2. CASE op = "Insert" /\ pc'[p] = "I1"
      BY <2>2, Zenon, RemDef, SPrimeRewrite DEF SPrime
    <2>3. CASE op = "Upsert" /\ pc'[p] = "U1"
      BY <2>3, Zenon, RemDef, SPrimeRewrite DEF SPrime
    <2>4. CASE op = "Remove" /\ pc'[p] = "R1"
      BY <2>4, Zenon, RemDef, SPrimeRewrite DEF SPrime
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4, Zenon DEF OpNames, OpToInvocLine
  <1>5. c \in Invoke(S, p, op, new_arg)
    <2>1. c.op = [c_pred.op EXCEPT ![p] = op]
      BY <1>4, Zenon DEF ConfigDomain
    <2>2. c.arg = [c_pred.arg EXCEPT ![p] = new_arg]
      BY <1>4, Zenon DEF ConfigDomain
    <2>3. c.res = [c_pred.res EXCEPT ![p] = BOT]
      BY <1>4, Zenon DEF ConfigDomain
    <2> QED
      BY <1>2, <1>3, <2>1, <2>2, <2>3, Zenon DEF Invoke
  <1> QED
    BY <1>5, EmptySeqEvolve

================================================================================================