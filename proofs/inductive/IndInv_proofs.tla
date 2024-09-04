--------------------------- MODULE IndInv_proofs ---------------------------
(***************************************************************************
 This module contains proofs of InitInv, StutterInv, IntermInv, NextInv, 
 and SpecInv from IndInv.tla.
 ***************************************************************************)
EXTENDS IndInv, Assumptions, TLAPS

\* InitInv = Init => Inv
THEOREM InitInv
  <1> USE RemDef DEF TypeOK, Init, LineIDs, RetDomain, AddrsInv, BktInv, NewBktInv, UniqInv
  <1> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <1>1. TypeOK
    OBVIOUS
  <1>2. AddrsInv
    OBVIOUS
  <1>3. BktInv
    OBVIOUS 
  <1>4. NewBktInv
    OBVIOUS
  <1>5. UniqInv  
    OBVIOUS 
  <1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Inv

\* StutterInv = Inv /\ UNCHANGED vars => Inv'  
LEMMA StutterInv
  <2> SUFFICES ASSUME Inv, UNCHANGED vars
               PROVE  Inv'
    BY DEF StutterInv
  <2> USE DEF Inv, vars, TypeOK
  <2>1. (pc \in [ProcSet -> LineIDs])'
    BY DEF LineIDs
  <2>2. (A \in [1..N -> AllocAddrs \union {NULL}])'
    OBVIOUS
  <2>3. (MemLocs \in [Addrs -> Seq([key: KeyDomain, val: ValDomain])])'
    <3> DEFINE D == Addrs
    <3> DEFINE R == Seq([key: KeyDomain, val: ValDomain])
    <3>0. MemLocs \in [D -> R]
      BY Zenon
    <3> SUFFICES MemLocs' \in [D' -> R']
      BY Zenon
    <3>1. D = D'
      OBVIOUS
    <3>2. R = R'
      OBVIOUS
    <3>3. MemLocs = MemLocs'
      OBVIOUS
    <3> HIDE DEF D, R
    <3> QED
      BY <3>0, <3>1, <3>2, <3>3
  <2>4. (AllocAddrs \in SUBSET Addrs)'
    OBVIOUS
  <2>5. (bucket \in [ProcSet -> AllocAddrs \union {NULL}])'
    OBVIOUS
  <2>6. (newbkt \in [ProcSet -> AllocAddrs \union {NULL}])'
    OBVIOUS
  <2>7. (r \in [ProcSet -> ValDomain \union {NULL}])'
    OBVIOUS
  <2>8. (arg \in [ProcSet -> ArgDomain])'
    OBVIOUS
  <2>9. (ret \in [ProcSet -> RetDomain])'
    BY DEF RetDomain
  <2>10. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
    OBVIOUS
  <2>11. AddrsInv'
    <3> SUFFICES ASSUME NEW p \in ProcSet',
                        (pc[p] \in {"I4", "U4", "R4"})'
                 PROVE  (/\ \A q \in ProcSet : (p # q => /\ newbkt[p] # bucket[q]
                                                         /\ newbkt[p] # newbkt[q])
                         /\ \A idx \in 1..N  : (A[idx] # newbkt[p])
                         /\ newbkt[p] # bucket[p]
                         /\ newbkt[p] \in AllocAddrs)'
      BY DEF AddrsInv
    <3>1. (\A q \in ProcSet : (p # q => /\ newbkt[p] # bucket[q]
                                        /\ newbkt[p] # newbkt[q]))'
      BY DEF AddrsInv
    <3>2. A = A' /\ newbkt = newbkt'
      OBVIOUS
    <3>3. (\A idx \in 1..N  : (A[idx] # newbkt[p]))'
      BY <3>2 DEF AddrsInv
    <3>4. (newbkt[p] # bucket[p])'
      BY DEF AddrsInv
    <3>5. (newbkt[p] \in AllocAddrs)'
      BY DEF AddrsInv
    <3>6. QED
      BY <3>1, <3>3, <3>4, <3>5
  <2>12. BktInv'
    <3> SUFFICES ASSUME NEW q \in ProcSet'
                 PROVE  (/\ pc[q] \in {"I3", "I4"} => (/\ ~KeyInBktAtAddr(arg[q].key, bucket[q]) 
                                                       /\ r[q] = NULL)
                         /\ pc[q] \in {"U3", "U4"} => (IF KeyInBktAtAddr(arg[q].key, bucket[q])
                                                          THEN (/\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) 
                                                                /\ r[q] # NULL)
                                                          ELSE r[q] = NULL)
                         /\ pc[q] \in {"R3", "R4"} => (/\ KeyInBktAtAddr(arg[q].key, bucket[q]) 
                                                       /\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) 
                                                       /\ r[q] # NULL))'
      BY DEF BktInv
    <3>1. CASE pc'[q] \in {"I3", "I4"}
      <4> USE <3>1
      <4> SUFFICES ~KeyInBktAtAddr(arg[q].key, bucket[q])' /\ r'[q] = NULL
        OBVIOUS
      <4> pc[q] \in {"I3", "I4"}
        OBVIOUS
      <4>1. ~KeyInBktAtAddr(arg[q].key, bucket[q]) /\ r[q] = NULL
        BY Zenon DEF BktInv
      <4> QED
        BY <4>1 DEF KeyInBktAtAddr
    <3>2. CASE pc'[q] \in {"U3", "U4"}
      <4> USE <3>2
      <4> SUFFICES IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                          THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                /\ r'[q] # NULL)
                          ELSE r'[q] = NULL
        OBVIOUS
      <4> pc[q] \in {"U3", "U4"}
        OBVIOUS
      <4>1. IF KeyInBktAtAddr(arg[q].key, bucket[q])
                   THEN (/\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                         /\ r[q] # NULL)
                   ELSE r[q] = NULL
        BY Zenon DEF BktInv
      <4>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
        BY DEF KeyInBktAtAddr
      <4>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
        MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                 MemLocs'[bucket'[q]][index].key = arg'[q].key].val
        BY DEF ValOfKeyInBktAtAddr
      <4>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
        OBVIOUS
      <4>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
            MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                MemLocs[bucket'[q]][index].key = arg[q].key].val
        BY Zenon, <4>3, <4>4
      <4>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
            MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                               MemLocs[bucket[q]][index].key = arg[q].key].val
        BY <4>4, <4>5
      <4>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
        BY <4>6, Zenon DEF ValOfKeyInBktAtAddr
      <4> QED
        BY <4>1, <4>2, <4>7
    <3>3. CASE pc'[q] \in {"R3", "R4"}
      <4> USE <3>3
      <4> SUFFICES /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                   /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                   /\ r'[q] # NULL
        OBVIOUS
      <4> pc[q] \in {"R3", "R4"}
        OBVIOUS
      <4>1. /\ KeyInBktAtAddr(arg[q].key, bucket[q])
            /\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            /\ r[q] # NULL
        BY Zenon DEF BktInv
      <4>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
        BY DEF KeyInBktAtAddr
      <4>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
            MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                 MemLocs'[bucket'[q]][index].key = arg'[q].key].val
        BY DEF ValOfKeyInBktAtAddr
      <4>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
        OBVIOUS
      <4>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
            MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                MemLocs[bucket'[q]][index].key = arg[q].key].val
        BY Zenon, <4>3, <4>4
      <4>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
            MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                               MemLocs[bucket[q]][index].key = arg[q].key].val
        BY <4>4, <4>5
      <4>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
        BY <4>6, Zenon DEF ValOfKeyInBktAtAddr
      <4> QED
        BY <4>1, <4>2, <4>7
    <3> QED
      BY <3>1, <3>2, <3>3     
  <2>13. UniqInv'
    <3> SUFFICES ASSUME NEW addr \in AllocAddrs', 
                        NEW bucket_arr, bucket_arr = MemLocs'[addr],
                        NEW j1 \in 1..Len(bucket_arr),
                        NEW j2 \in 1..Len(bucket_arr),
                        bucket_arr[j1].key = bucket_arr[j2].key
                 PROVE  j1 = j2
      BY Zenon DEF UniqInv
    <3> QED
      BY DEF UniqInv
  <2>14. NewBktInv'
    <3> SUFFICES ASSUME NEW q \in ProcSet
                     PROVE  /\ pc'[q] = "I4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                                /\ \A k \in KeyDomain : k # arg'[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                           /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                             (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                            /\ pc'[q] = "U4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                                /\ \A k \in KeyDomain : k # arg'[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                           /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                             (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                            /\ pc'[q] = "R4" => /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                /\ \A k \in KeyDomain : k # arg'[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                           /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                             (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
          BY DEF NewBktInv
    <3>A. arg = arg'
      OBVIOUS
    <3>B. SUFFICES /\ pc'[q] = "I4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                       /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                       /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                 /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                    (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                   /\ pc'[q] = "U4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                       /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                       /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                 /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                    (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                   /\ pc'[q] = "R4" => /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                       /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                 /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                    (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
      BY <3>A
    <3>0. ASSUME NEW k \in KeyDomain
          PROVE  /\ pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
                 /\ KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
                 /\ pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                 /\ ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
      <4> USE <3>0
      <4>1. pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
        BY DEF KeyInBktAtAddr
      <4>2. KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
        BY DEF KeyInBktAtAddr
      <4>3. pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
        <5> SUFFICES ASSUME pc[q] \in {"I4", "U4", "R4"}
                     PROVE  ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
          OBVIOUS
        <5> DEFINE bkt_arr == MemLocs'[bucket'[q]]
        <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
        <5>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
          BY Zenon DEF ValOfKeyInBktAtAddr
        <5>2. bkt_arr = MemLocs[bucket[q]]
          OBVIOUS
        <5>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
          BY Zenon
        <5> QED
          BY <5>1, <5>2, <5>3, Isa DEF ValOfKeyInBktAtAddr
      <4>4. ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
        <5> DEFINE bkt_arr == MemLocs'[newbkt'[q]]
        <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
        <5>1. ValOfKeyInBktAtAddr(k, newbkt[q])' = bkt_arr[idx].val
          BY Zenon DEF ValOfKeyInBktAtAddr
        <5>2. bkt_arr = MemLocs[newbkt[q]]
          OBVIOUS
        <5>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
          BY Zenon
        <5> QED
          BY <5>1, <5>2, <5>3, Isa DEF ValOfKeyInBktAtAddr
      <4> QED
        BY <4>1, <4>2, <4>3, <4>4
    <3>1. CASE pc'[q] = "I4"
      <4> USE <3>1
      <4> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                   /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                   /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                             /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
        OBVIOUS
      <4>1. pc[q] = "I4" /\ arg[q].key \in KeyDomain
        BY RemDef DEF ArgsOf, LineIDtoOp
      <4>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
            /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
            /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                      /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                         (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
        BY <4>1, Zenon DEF NewBktInv
      <4> QED
        BY <3>0, <4>1, <4>2
    <3>2. CASE pc'[q] = "U4"
      <4> USE <3>2
      <4> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                   /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                   /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                             /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
        OBVIOUS
      <4>1. pc[q] = "U4" /\ arg[q].key \in KeyDomain
        BY RemDef DEF ArgsOf, LineIDtoOp
      <4>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
            /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
            /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                      /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                         (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
        BY <4>1, Zenon DEF NewBktInv
      <4> QED
        BY <3>0, <4>1, <4>2
    <3>3. CASE pc'[q] = "R4"
      <4> USE <3>3
      <4> SUFFICES /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                   /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                             /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
        OBVIOUS
      <4>1. pc[q] = "R4" /\ arg[q].key \in KeyDomain
        BY RemDef DEF ArgsOf, LineIDtoOp
      <4>2. /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])
            /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                      /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                         (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
        BY <4>1, Zenon DEF NewBktInv
      <4> QED
        BY <3>0, <4>1, <4>2
    <3> QED
      BY <3>1, <3>2, <3>3
  <2> QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12, <2>13, <2>14 DEF Inv

\* IntermInv = Inv /\ IntermAction => Inv'
LEMMA IntermInv
  <1> USE Zenon
  <1> SUFFICES ASSUME Inv, 
                      NEW p \in ProcSet,
                      NEW LineAction \in IntLines(p),
                      LineAction
               PROVE  Inv'
    BY DEF IntermAction
  <1>1. CASE LineAction \in {F1(p), F2(p)}
    BY <1>1, FindInv
  <1>2. CASE LineAction \in {I1(p), I2(p), I3(p), I4(p)}
    BY <1>2, InsertInv
  <1>3. CASE LineAction \in {U1(p), U2(p), U3(p), U4(p)}
    BY <1>3, UpsertInv
  <1>4. CASE LineAction \in {R1(p), R2(p), R3(p), R4(p)}
    BY <1>4, RemoveInv
  <1> QED
    BY <1>1, <1>2, <1>3, <1>4, Zenon DEF IntLines

\* NextInv = Inv /\ [Next]_vars => Inv'
LEMMA NextInv
  <1> SUFFICES ASSUME Inv, [Next]_vars
               PROVE  Inv'
    BY DEF NextInv
  <1>1. CASE Next
    <2>1. CASE InvocnAction
      BY <2>1, InvocInv
    <2>2. CASE IntermAction
      BY <2>2, IntermInv
    <2>3. CASE ReturnAction
      BY <2>3, ReturnInv
    <2> QED
      BY <1>1, <2>1, <2>2, <2>3 DEF Next
  <1>2. CASE UNCHANGED vars
    BY <1>2, StutterInv
  <1> QED
    BY <1>1, <1>2

\* SpecInv = Spec => []Inv
THEOREM SpecInv
  BY InitInv, NextInv, PTL DEF Spec

======================================================================================
\* Modification History
\* Last modified Mon Aug 26 14:28:37 EDT 2024 by uguryavuz
\* Created Mon Jul 08 12:21:04 EDT 2024 by uyavuz
