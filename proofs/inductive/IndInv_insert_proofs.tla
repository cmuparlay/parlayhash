--------------------------- MODULE IndInv_insert_proofs ----------------------
(***************************************************************************
 This module contains the proof of InsertInv from IndInv.tla
 ***************************************************************************)
EXTENDS IndInv, Assumptions, TLAPS,
        SequenceTheorems, FiniteSets

\* InsertInv = Inv /\ (\E p \in ProcSet : \/ I1(p)
\*                                        \/ I2(p)
\*                                        \/ I3(p)
\*                                        \/ I4(p)) => Inv'
LEMMA InsertInv
  <1> SUFFICES ASSUME Inv,
                      NEW p \in ProcSet,
                      \/ I1(p)
                      \/ I2(p)
                      \/ I3(p)
                      \/ I4(p)
               PROVE  Inv'
    BY DEF InsertInv
  <1>1. CASE I1(p)
    <2> USE <1>1 DEF I1, TypeOK, Inv, vars
    <2>1. (pc \in [ProcSet -> LineIDs])'
      BY Isa DEF LineIDs
    <2>2. (A \in [1..N -> AllocAddrs \union {NULL}])'
      OBVIOUS
    <2>3. (MemLocs \in [Addrs -> Seq([key: KeyDomain, val: ValDomain])])'
      OBVIOUS
    <2>4. (AllocAddrs \in SUBSET Addrs)'
      OBVIOUS
    <2>5. (bucket \in [ProcSet -> AllocAddrs \union {NULL}])'
      <3>1. arg[p].key \in KeyDomain
        BY RemDef, Zenon DEF LineIDtoOp, ArgsOf
      <3> QED
        BY <3>1, HashDef, Zenon
    <2>6. (newbkt \in [ProcSet -> AllocAddrs \union {NULL}])'
      OBVIOUS
    <2>7. (r \in [ProcSet -> ValDomain \union {NULL}])'
      OBVIOUS
    <2>8. (arg \in [ProcSet -> ArgDomain])'
      OBVIOUS
    <2>9. (ret \in [ProcSet -> RetDomain])'
      OBVIOUS
    <2>10. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
      <3> SUFFICES arg[p] \in ArgsOf(LineIDtoOp(pc'[p]))
        BY Zenon
      <3> QED
        BY RemDef, ZenonT(30) DEF LineIDtoOp, ArgsOf
    <2>11. AddrsInv'
      <3> SUFFICES ASSUME NEW p_1 \in ProcSet',
                          (pc[p_1] \in {"I4", "U4", "R4"})'
                    PROVE  (/\ \A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                                              /\ newbkt[p_1] # newbkt[q])
                            /\ \A idx \in 1..N  : (A[idx] # newbkt[p_1])
                            /\ newbkt[p_1] # bucket[p_1]
                            /\ newbkt[p_1] \in AllocAddrs)'
        BY DEF AddrsInv
      <3>1. (\A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                            /\ newbkt[p_1] # newbkt[q]))'
        <4> SUFFICES ASSUME NEW q \in ProcSet,
                            p_1 # q
                      PROVE  newbkt[p_1] # bucket'[q]
          BY ZenonT(30) DEF AddrsInv
        <4>1. CASE p = q
          <5>1. arg[p] \in [key: KeyDomain, val: ValDomain]
            BY RemDef, Zenon DEF ArgsOf, LineIDtoOp
          <5>2. Hash[arg[p].key] \in 1..N
            BY <5>1, HashDef
          <5>3. A[Hash[arg[p].key]] # newbkt[p_1]
            BY <5>2, Zenon DEF AddrsInv
          <5>4. bucket'[q] # newbkt[p_1]
            BY <4>1, <5>3, Zenon
          <5> QED
            BY <5>4
        <4>2. CASE p # q
          BY <4>2, Zenon DEF AddrsInv
        <4> QED
          BY <4>1, <4>2
      <3>2. (\A idx \in 1..N  : (A[idx] # newbkt[p_1]))'
        BY DEF AddrsInv
      <3>3. (newbkt[p_1] # bucket[p_1])'
        BY DEF AddrsInv
      <3>4. (newbkt[p_1] \in AllocAddrs)'
        BY DEF AddrsInv
      <3>5. QED
        BY <3>1, <3>2, <3>3, <3>4
    <2>12. BktInv'
      <3> SUFFICES ASSUME NEW q \in ProcSet
                    PROVE  (/\ pc'[q] \in {"I3", "I4"} => (/\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                          /\ r'[q] = NULL)
                            /\ pc'[q] \in {"U3", "U4"} => (IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                                    /\ r'[q] # NULL)
                                                              ELSE r'[q] = NULL)
                            /\ pc'[q] \in {"R3", "R4"} => (/\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                          /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                          /\ r'[q] # NULL))
        BY DEF BktInv
      <3>1. CASE pc'[q] \in {"I3", "I4"}
        <4> USE <3>1
        <4> SUFFICES ~KeyInBktAtAddr(arg[q].key, bucket[q])' /\ r'[q] = NULL
          OBVIOUS
        <4>1. ~KeyInBktAtAddr(arg[q].key, bucket[q]) /\ r[q] = NULL
          BY Zenon DEF BktInv
        <4> QED
          BY <4>1, Zenon DEF KeyInBktAtAddr
      <3>2. CASE pc'[q] \in {"U3", "U4"}
        <4> USE <3>2
        <4> SUFFICES IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                        THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                              /\ r'[q] # NULL)
                        ELSE r'[q] = NULL
          OBVIOUS
        <4>1. IF KeyInBktAtAddr(arg[q].key, bucket[q])
                  THEN (/\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                        /\ r[q] # NULL)
                  ELSE r[q] = NULL
          BY Zenon DEF BktInv
        <4>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY Zenon DEF KeyInBktAtAddr
        <4>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
          MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                MemLocs'[bucket'[q]][index].key = arg'[q].key].val
          BY DEF ValOfKeyInBktAtAddr
        <4>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
          BY Zenon
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
          BY <4>1, <4>2, <4>7, Zenon
      <3>3. CASE pc'[q] \in {"R3", "R4"}
        <4> USE <3>3
        <4> SUFFICES /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                      /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                      /\ r'[q] # NULL
          OBVIOUS
        <4>1. /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              /\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              /\ r[q] # NULL
          BY Zenon DEF BktInv
        <4>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY Zenon DEF KeyInBktAtAddr
        <4>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
          MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                MemLocs'[bucket'[q]][index].key = arg'[q].key].val
          BY DEF ValOfKeyInBktAtAddr
        <4>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
          BY Zenon
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
          BY <4>1, <4>2, <4>7, Zenon
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
        BY Zenon DEF UniqInv
    <2>14. NewBktInv'
      <3> SUFFICES ASSUME NEW q \in ProcSet
                    PROVE  /\ pc'[q] = "I4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
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
        BY ZenonT(60) DEF NewBktInv
      <3>0. ASSUME NEW k \in KeyDomain
            PROVE  /\ pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
                   /\ KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
                   /\ pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                   /\ ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
        <4> USE <3>0
        <4>1. pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
          BY Zenon DEF KeyInBktAtAddr
        <4>2. KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
          BY Zenon DEF KeyInBktAtAddr
        <4>3. pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
          <5> SUFFICES ASSUME pc[q] \in {"I4", "U4", "R4"}
                        PROVE  ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
            OBVIOUS
          <5> DEFINE bkt_arr == MemLocs'[bucket'[q]]
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
          <5>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>2. bkt_arr = MemLocs[bucket[q]]
            BY Zenon
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
            BY Zenon
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
          BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
        <4>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
              /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
              /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                        /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                            (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
          BY <4>1, Zenon DEF NewBktInv
        <4> QED
          BY <3>0, <4>1, <4>2, ZenonT(30)
      <3>2. CASE pc'[q] = "U4"
        <4> USE <3>2
        <4> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                      /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                      /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                  (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
          OBVIOUS
        <4>1. pc[q] = "U4" /\ arg[q].key \in KeyDomain
          BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
        <4>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
              /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
              /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                        /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                            (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
          BY <4>1, Zenon DEF NewBktInv
        <4> QED
          BY <3>0, <4>1, <4>2, ZenonT(30)
      <3>3. CASE pc'[q] = "R4"
        <4> USE <3>3
        <4> SUFFICES /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                      /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                  (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
          OBVIOUS
        <4>1. pc[q] = "R4" /\ arg[q].key \in KeyDomain
          BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
        <4>2. /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])
              /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                        /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                            (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
          BY <4>1, Zenon DEF NewBktInv
        <4> QED
          BY <3>0, <4>1, <4>2, ZenonT(30)
      <3> QED
        BY <3>1, <3>2, <3>3
    <2> QED
      BY <2>9, <2>10, <2>11, <2>12, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>13, <2>14 DEF Inv
  <1>2. CASE I2(p)
    <2> USE <1>2 DEF I2, TypeOK, Inv, vars
    <2>1. (pc \in [ProcSet -> LineIDs])'
      BY Isa DEF LineIDs
    <2>2. (A \in [1..N -> AllocAddrs \union {NULL}])'
      OBVIOUS
    <2>3. (MemLocs \in [Addrs -> Seq([key: KeyDomain, val: ValDomain])])'
      OBVIOUS
    <2>4. (AllocAddrs \in SUBSET Addrs)'
      OBVIOUS
    <2>5. (bucket \in [ProcSet -> AllocAddrs \union {NULL}])'
      OBVIOUS
    <2>6. (newbkt \in [ProcSet -> AllocAddrs \union {NULL}])'
      OBVIOUS
    <2>7. (r \in [ProcSet -> ValDomain \union {NULL}])'
      <3>1. CASE bucket[p] # NULL /\ KeyInBktAtAddr(arg[p].key, bucket[p])
        <4>1. r' = [r EXCEPT ![p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p])]
          BY <3>1, Zenon
        <4>2. ValOfKeyInBktAtAddr(arg[p].key, bucket[p]) = MemLocs[bucket[p]][CHOOSE index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key = arg[p].key].val
          BY Zenon DEF ValOfKeyInBktAtAddr
        <4>3. \E index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key = arg[p].key
          BY <3>1, Zenon DEF KeyInBktAtAddr
        <4>4. PICK index \in 1..Len(MemLocs[bucket[p]]) : /\ MemLocs[bucket[p]][index].key = arg[p].key
                                                          /\ ValOfKeyInBktAtAddr(arg[p].key, bucket[p]) = MemLocs[bucket[p]][index].val
          BY <4>2, <4>3, Zenon
        <4>5. MemLocs[bucket[p]] \in Seq([key: KeyDomain, val: ValDomain])
          BY <3>1
        <4>6. MemLocs[bucket[p]][index] \in [key: KeyDomain, val: ValDomain]
          BY <4>4, <4>5, ElementOfSeq, Zenon
        <4>7. MemLocs[bucket[p]][index].val \in ValDomain
          BY <4>6
        <4> QED
          BY <4>1, <4>4, <4>7, Zenon
      <3>2. CASE bucket[p] = NULL \/ ~KeyInBktAtAddr(arg[p].key, bucket[p])
        BY <3>2, Zenon DEF KeyInBktAtAddr
      <3> QED
        BY <3>1, <3>2
    <2>8. (arg \in [ProcSet -> ArgDomain])'
      OBVIOUS
    <2>9. (ret \in [ProcSet -> RetDomain])'
      OBVIOUS
    <2>10. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
      <3> SUFFICES arg[p] \in ArgsOf(LineIDtoOp(pc'[p]))
        BY Zenon
      <3> QED
        BY RemDef, ZenonT(30) DEF LineIDtoOp, ArgsOf
    <2>11. AddrsInv'
      <3> SUFFICES ASSUME NEW p_1 \in ProcSet',
                          (pc[p_1] \in {"I4", "U4", "R4"})'
                    PROVE  (/\ \A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                                              /\ newbkt[p_1] # newbkt[q])
                            /\ \A idx \in 1..N  : (A[idx] # newbkt[p_1])
                            /\ newbkt[p_1] # bucket[p_1]
                            /\ newbkt[p_1] \in AllocAddrs)'
        BY DEF AddrsInv
      <3>1. (\A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                            /\ newbkt[p_1] # newbkt[q]))'
        BY DEF AddrsInv
      <3>2. (\A idx \in 1..N  : (A[idx] # newbkt[p_1]))'
        BY DEF AddrsInv
      <3>3. (newbkt[p_1] # bucket[p_1])'
        BY DEF AddrsInv
      <3>4. (newbkt[p_1] \in AllocAddrs)'
        BY DEF AddrsInv
      <3>5. QED
        BY <3>1, <3>2, <3>3, <3>4
    <2>12. BktInv'
      <3> SUFFICES ASSUME NEW q \in ProcSet
                    PROVE  (/\ pc'[q] \in {"I3", "I4"} => (/\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                          /\ r'[q] = NULL)
                            /\ pc'[q] \in {"U3", "U4"} => (IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                                    /\ r'[q] # NULL)
                                                              ELSE r'[q] = NULL)
                            /\ pc'[q] \in {"R3", "R4"} => (/\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                          /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                          /\ r'[q] # NULL))
        BY DEF BktInv
      <3>1. CASE pc'[q] \in {"I3", "I4"}
        <4> USE <3>1
        <4>1. CASE p = q
          <5>1. ~KeyInBktAtAddr(arg[q].key, bucket[q]) /\ r'[q] = NULL
            BY <4>1, Zenon
          <5> QED 
            BY <5>1, Zenon DEF KeyInBktAtAddr
        <4> SUFFICES ASSUME p # q
                      PROVE  ~KeyInBktAtAddr(arg[q].key, bucket[q])' /\ r'[q] = NULL
          BY <4>1
        <4>2. ~KeyInBktAtAddr(arg[q].key, bucket[q]) /\ r[q] = NULL
          BY Zenon DEF BktInv
        <4> QED
          BY <4>2, Zenon DEF KeyInBktAtAddr
      <3>2. CASE pc'[q] \in {"U3", "U4"}
        <4> USE <3>2
        <4> SUFFICES IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                        THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                              /\ r'[q] # NULL)
                        ELSE r'[q] = NULL
          OBVIOUS
        <4>1. IF KeyInBktAtAddr(arg[q].key, bucket[q])
                  THEN (/\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                        /\ r[q] # NULL)
                  ELSE r[q] = NULL
          BY Zenon DEF BktInv
        <4>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY Zenon DEF KeyInBktAtAddr
        <4>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
          MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                MemLocs'[bucket'[q]][index].key = arg'[q].key].val
          BY DEF ValOfKeyInBktAtAddr
        <4>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
          BY Zenon
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
          BY <4>1, <4>2, <4>7, Zenon
      <3>3. CASE pc'[q] \in {"R3", "R4"}
        <4> USE <3>3
        <4> SUFFICES /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                      /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                      /\ r'[q] # NULL
          OBVIOUS
        <4>1. /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              /\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              /\ r[q] # NULL
          BY Zenon DEF BktInv
        <4>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY Zenon DEF KeyInBktAtAddr
        <4>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
          MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                MemLocs'[bucket'[q]][index].key = arg'[q].key].val
          BY DEF ValOfKeyInBktAtAddr
        <4>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
          BY Zenon
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
          BY <4>1, <4>2, <4>7, Zenon
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
        BY Zenon DEF UniqInv
    <2>14. NewBktInv'
      <3> SUFFICES ASSUME NEW q \in ProcSet
                    PROVE  /\ pc'[q] = "I4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
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
        BY ZenonT(60) DEF NewBktInv
      <3>0. ASSUME NEW k \in KeyDomain
            PROVE  /\ pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
                   /\ KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
                   /\ pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                   /\ ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
        <4> USE <3>0
        <4>1. pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
          BY Zenon DEF KeyInBktAtAddr
        <4>2. KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
          BY Zenon DEF KeyInBktAtAddr
        <4>3. pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
          <5> SUFFICES ASSUME pc[q] \in {"I4", "U4", "R4"}
                        PROVE  ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
            OBVIOUS
          <5> DEFINE bkt_arr == MemLocs'[bucket'[q]]
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
          <5>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>2. bkt_arr = MemLocs[bucket[q]]
            BY Zenon
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
            BY Zenon
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
          BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
        <4>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
              /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
              /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                        /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                            (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
          BY <4>1, Zenon DEF NewBktInv
        <4> QED
          BY <3>0, <4>1, <4>2, ZenonT(30)
      <3>2. CASE pc'[q] = "U4"
        <4> USE <3>2
        <4> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                      /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                      /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                  (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
          OBVIOUS
        <4>1. pc[q] = "U4" /\ arg[q].key \in KeyDomain
          BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
        <4>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
              /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
              /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                        /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                            (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
          BY <4>1, Zenon DEF NewBktInv
        <4> QED
          BY <3>0, <4>1, <4>2, ZenonT(30)
      <3>3. CASE pc'[q] = "R4"
        <4> USE <3>3
        <4> SUFFICES /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                      /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                  (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
          OBVIOUS
        <4>1. pc[q] = "R4" /\ arg[q].key \in KeyDomain
          BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
        <4>2. /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])
              /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                        /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                            (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
          BY <4>1, Zenon DEF NewBktInv
        <4> QED
          BY <3>0, <4>1, <4>2, ZenonT(30)
      <3> QED
        BY <3>1, <3>2, <3>3
    <2> QED
      BY <2>9, <2>10, <2>11, <2>12, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>13, <2>14 DEF Inv
  <1>3. CASE I3(p)
    <2> USE <1>3 DEF I3, TypeOK, Inv, vars
    <2>1. (pc \in [ProcSet -> LineIDs])'
      BY Isa DEF LineIDs
    <2>2. (A \in [1..N -> AllocAddrs \union {NULL}])'
      OBVIOUS
    <2>3. (MemLocs \in [Addrs -> Seq([key: KeyDomain, val: ValDomain])])'
      <3>1. CASE bucket[p] = NULL
        <4> USE <3>1
        <4>1. PICK addr \in Addrs : MemLocs' = [MemLocs EXCEPT ![addr] = <<arg[p]>>]
          BY Zenon
        <4>2. MemLocs'[addr] \in Seq([key: KeyDomain, val: ValDomain])
          <5> SUFFICES arg[p] \in [key: KeyDomain, val: ValDomain]
            BY <4>1 DEF Seq
          <5> QED
            BY RemDef, Zenon DEF LineIDtoOp, ArgsOf
        <4> QED
          BY <4>1, <4>2
      <3>2. CASE bucket[p] # NULL
        <4> USE <3>2
        <4>1. PICK addr \in Addrs : MemLocs' = [MemLocs EXCEPT ![addr] = Append(MemLocs[bucket[p]], arg[p])]
          BY Zenon
        <4> SUFFICES Append(MemLocs[bucket[p]], arg[p]) \in Seq([key: KeyDomain, val: ValDomain])
          BY <4>1, Zenon
        <4> SUFFICES /\ MemLocs[bucket[p]] \in Seq([key: KeyDomain, val: ValDomain])
                      /\ arg[p] \in [key: KeyDomain, val: ValDomain]
          BY AppendProperties, Zenon
        <4>2. MemLocs[bucket[p]] \in Seq([key: KeyDomain, val: ValDomain])
          OBVIOUS
        <4>3. arg[p] \in [key: KeyDomain, val: ValDomain]
          BY RemDef, Zenon DEF LineIDtoOp, ArgsOf
        <4> QED
          BY <4>2, <4>3
      <3> QED
        BY <3>1, <3>2
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
      OBVIOUS
    <2>10. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
      <3> SUFFICES arg[p] \in ArgsOf(LineIDtoOp(pc'[p]))
        BY Zenon
      <3> QED
        BY RemDef, ZenonT(30) DEF LineIDtoOp, ArgsOf
    <2>11. AddrsInv'
      <3> SUFFICES ASSUME NEW p_1 \in ProcSet,
                          pc'[p_1] \in {"I4", "U4", "R4"}
                   PROVE  /\ \A q \in ProcSet : (p_1 # q => /\ newbkt'[p_1] # bucket'[q]
                                                            /\ newbkt'[p_1] # newbkt'[q])
                          /\ \A idx \in 1..N  : (A'[idx] # newbkt'[p_1])
                          /\ newbkt'[p_1] # bucket'[p_1]
                          /\ newbkt'[p_1] \in AllocAddrs'
        BY Zenon DEF AddrsInv
      <3>0. PICK addr \in Addrs : /\ addr \notin AllocAddrs
                                  /\ AllocAddrs' = AllocAddrs \cup {addr}
                                  /\ newbkt' = [newbkt EXCEPT ![p] = addr]
        BY Zenon
      <3>1. CASE p_1 = p
        <4>1. newbkt'[p_1] \notin AllocAddrs /\ newbkt'[p_1] # NULL
          BY <3>0, <3>1, NULLDef
        <4>2. \A q \in ProcSet : (p_1 # q => /\ newbkt'[p_1] # bucket'[q]
                                              /\ newbkt'[p_1] # newbkt'[q])
          <5> SUFFICES ASSUME NEW q \in ProcSet,
                              p_1 # q
                        PROVE  /\ newbkt'[p_1] # bucket'[q]
                              /\ newbkt'[p_1] # newbkt'[q]
            OBVIOUS
          <5>1. bucket[q] \in AllocAddrs \/ bucket[q] = NULL
            OBVIOUS
          <5>2. bucket'[q] \in AllocAddrs \/ bucket'[q] = NULL
            BY <5>1, Zenon
          <5>3. newbkt[q] \in AllocAddrs \/ newbkt[q] = NULL
            OBVIOUS
          <5>4. newbkt'[q] \in AllocAddrs \/ newbkt'[q] = NULL
            BY <3>1, <5>3, Zenon
          <5>5. newbkt'[p_1] # bucket'[q]
            BY <3>1, <4>1, <5>2 DEF AddrsInv
          <5>6. newbkt'[p_1] # newbkt'[q]
            BY <3>1, <4>1, <5>4 DEF AddrsInv
          <5>7. QED
            BY <5>5, <5>6
        <4>3. \A idx \in 1..N  : (A'[idx] # newbkt'[p_1])
          <5> SUFFICES ASSUME NEW idx \in 1..N
                        PROVE  A'[idx] # newbkt'[p_1]
            OBVIOUS
          <5>1. A'[idx] \in AllocAddrs \/ A'[idx] = NULL
            BY <2>2, Zenon
          <5> QED
            BY <4>1, <5>1
        <4>4. newbkt'[p_1] # bucket'[p_1]
          <5>1. bucket'[p_1] \in AllocAddrs \/ bucket'[p_1] = NULL
            BY Zenon
          <5> QED
            BY <4>1, <5>1
        <4>5. newbkt'[p_1] \in AllocAddrs'
          BY <3>1 DEF AddrsInv
        <4>6. QED
          BY <4>2, <4>3, <4>4, <4>5
      <3>2. CASE p_1 # p
        <4>1. \A q \in ProcSet : (p_1 # q => /\ newbkt'[p_1] # bucket'[q]
                                              /\ newbkt'[p_1] # newbkt'[q])
          <5> SUFFICES ASSUME NEW q \in ProcSet,
                              p_1 # q
                        PROVE  /\ newbkt'[p_1] # bucket'[q]
                              /\ newbkt'[p_1] # newbkt'[q]
            BY <3>2 DEF AddrsInv
          <5>1. newbkt'[p_1] # bucket'[q]
            BY <3>2 DEF AddrsInv
          <5>2. newbkt'[p_1] # newbkt'[q]
            <6>1. CASE q = p
              <7>1. newbkt'[q] \notin AllocAddrs
                BY <6>1, Zenon
              <7>2. newbkt'[p_1] \in AllocAddrs
                BY <3>2, Zenon DEF AddrsInv
              <7> QED  
                BY <7>1, <7>2
            <6>2. CASE q # p
              BY <3>2, <6>2 DEF AddrsInv
            <6> QED
              BY <6>1, <6>2
          <5>3. QED
            BY <5>1, <5>2
        <4>2. \A idx \in 1..N  : (A'[idx] # newbkt'[p_1])
          BY <3>2 DEF AddrsInv
        <4>3. newbkt'[p_1] # bucket'[p_1]
          BY <3>2 DEF AddrsInv
        <4>4. newbkt'[p_1] \in AllocAddrs'
          BY <3>2 DEF AddrsInv
        <4>5. QED
          BY <4>1, <4>2, <4>3, <4>4
      <3> QED
        BY <3>1, <3>2
    <2>12. BktInv'
      <3> SUFFICES ASSUME NEW q \in ProcSet
                    PROVE  (/\ pc'[q] \in {"I3", "I4"} => (/\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                          /\ r'[q] = NULL)
                            /\ pc'[q] \in {"U3", "U4"} => (IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                                    /\ r'[q] # NULL)
                                                              ELSE r'[q] = NULL)
                            /\ pc'[q] \in {"R3", "R4"} => (/\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                          /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                          /\ r'[q] # NULL))
        BY DEF BktInv
      <3>0. PICK addr \in Addrs : /\ addr \notin AllocAddrs
                                  /\ AllocAddrs' = AllocAddrs \cup {addr}
                                  /\ newbkt' = [newbkt EXCEPT ![p] = addr]
                                  /\ \A a \in Addrs : a # addr => MemLocs[a] = MemLocs'[a]
        BY Zenon
      <3>1. CASE pc'[q] \in {"I3", "I4"}
        <4>1. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
          <5>1. CASE bucket[q] = NULL
            <6> USE <5>1
            <6>1. KeyInBktAtAddr(arg[q].key, bucket[q]) = FALSE
              BY DEF KeyInBktAtAddr
            <6>2. bucket'[q] = NULL
              BY Zenon
            <6>3. KeyInBktAtAddr(arg[q].key, bucket[q])' = FALSE
              BY <6>2 DEF KeyInBktAtAddr
            <6> QED
              BY <6>1, <6>3, Zenon
          <5>2. CASE bucket[q] # NULL
            <6> USE <5>2
            <6>1. KeyInBktAtAddr(arg[q].key, bucket[q]) = \E index \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][index].key = arg[q].key
              BY Zenon DEF KeyInBktAtAddr
            <6>2. bucket'[q] = bucket[q] /\ bucket[q] \in AllocAddrs
              BY Zenon
            <6>3. MemLocs'[bucket[q]] = MemLocs[bucket[q]] /\ arg' = arg
              BY <6>2, Zenon
            <6>4. KeyInBktAtAddr(arg[q].key, bucket[q])' = \E index \in 1..Len(MemLocs'[bucket'[q]]) : MemLocs'[bucket'[q]][index].key = arg'[q].key
              BY Zenon DEF KeyInBktAtAddr
            <6>5. KeyInBktAtAddr(arg[q].key, bucket[q])' = \E index \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][index].key = arg[q].key
              BY <6>2, <6>3, <6>4
            <6> QED
              BY <6>1, <6>5
          <5> QED
            BY <5>1, <5>2
        <4>2. CASE p = q
          BY <4>2, <4>1, Zenon DEF BktInv
        <4> USE <3>1
        <4> SUFFICES ASSUME p # q
                      PROVE  ~KeyInBktAtAddr(arg[q].key, bucket[q])' /\ r'[q] = NULL
          BY <4>2
        <4>3. ~KeyInBktAtAddr(arg[q].key, bucket[q]) /\ r[q] = NULL
          BY Zenon DEF BktInv
        <4> QED
          BY <4>3, <4>1, Zenon DEF KeyInBktAtAddr
      <3>2. CASE pc'[q] \in {"U3", "U4"}
        <4> USE <3>2
        <4> SUFFICES IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                        THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                              /\ r'[q] # NULL)
                        ELSE r'[q] = NULL
          OBVIOUS
        <4>1. IF KeyInBktAtAddr(arg[q].key, bucket[q])
                  THEN (/\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                        /\ r[q] # NULL)
                  ELSE r[q] = NULL
          BY Zenon DEF BktInv
        <4>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
          <5>1. CASE bucket[q] = NULL
            <6> USE <5>1
            <6>1. KeyInBktAtAddr(arg[q].key, bucket[q]) = FALSE
              BY DEF KeyInBktAtAddr
            <6>2. bucket'[q] = NULL
              BY Zenon
            <6>3. KeyInBktAtAddr(arg[q].key, bucket[q])' = FALSE
              BY <6>2 DEF KeyInBktAtAddr
            <6> QED
              BY <6>1, <6>3, Zenon
          <5>2. CASE bucket[q] # NULL
            <6> USE <5>2
            <6>1. KeyInBktAtAddr(arg[q].key, bucket[q]) = \E index \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][index].key = arg[q].key
              BY Zenon DEF KeyInBktAtAddr
            <6>2. bucket'[q] = bucket[q] /\ bucket[q] \in AllocAddrs
              BY Zenon
            <6>3. MemLocs'[bucket[q]] = MemLocs[bucket[q]] /\ arg' = arg
              BY <6>2, Zenon
            <6>4. KeyInBktAtAddr(arg[q].key, bucket[q])' = \E index \in 1..Len(MemLocs'[bucket'[q]]) : MemLocs'[bucket'[q]][index].key = arg'[q].key
              BY Zenon DEF KeyInBktAtAddr
            <6>5. KeyInBktAtAddr(arg[q].key, bucket[q])' = \E index \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][index].key = arg[q].key
              BY <6>2, <6>3, <6>4
            <6> QED
              BY <6>1, <6>5
          <5> QED
            BY <5>1, <5>2
        <4>3. CASE KeyInBktAtAddr(arg[q].key, bucket[q])
          <5>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
            MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                  MemLocs'[bucket'[q]][index].key = arg'[q].key].val
            BY DEF ValOfKeyInBktAtAddr
          <5>2. bucket'[q] = bucket[q] /\ bucket[q] \in AllocAddrs
            BY Zenon, <4>3 DEF KeyInBktAtAddr
          <5>3. MemLocs'[bucket'[q]] = MemLocs[bucket[q]]
            BY <3>0, <5>2, Zenon
          <5>4. arg' = arg
            BY Zenon
          <5>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
            MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                MemLocs[bucket[q]][index].key = arg[q].key].val
            BY <5>1, <5>3, <5>4
          <5>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY <5>5, Zenon DEF ValOfKeyInBktAtAddr
          <5>7. r'[q] = r[q]
            BY Zenon
          <5> QED
            BY <4>1, <4>2, <4>3, <5>6, <5>7
        <4>4. CASE ~KeyInBktAtAddr(arg[q].key, bucket[q])
          BY <4>1, <4>2, <4>4, Zenon
        <4> QED
          BY <4>3, <4>4
      <3>3. CASE pc'[q] \in {"R3", "R4"}
        <4> USE <3>3
        <4> SUFFICES /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                      /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                      /\ r'[q] # NULL
          OBVIOUS
        <4>1. /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              /\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              /\ r[q] # NULL
          BY Zenon DEF BktInv
        <4>2. MemLocs[bucket[q]] = MemLocs'[bucket'[q]]
          <5>1. bucket[q] = bucket'[q]
            BY Zenon
          <5>2. bucket[q] \in AllocAddrs
            BY Zenon, <4>1 DEF KeyInBktAtAddr
          <5>3. bucket[q] # addr
            BY <3>0, <5>2
          <5>4. MemLocs'[bucket[q]] = MemLocs[bucket[q]]
            BY <3>0, <5>2, <5>3, Zenon
          <5> QED
            BY <5>1, <5>4
        <4>3. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY <4>2, Zenon DEF KeyInBktAtAddr
        <4>4. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
          MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                MemLocs'[bucket'[q]][index].key = arg'[q].key].val
          BY DEF ValOfKeyInBktAtAddr
        <4>5. arg = arg'
          BY Zenon
        <4>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
          MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                MemLocs[bucket[q]][index].key = arg'[q].key].val
          BY <4>2, <4>4
        <4>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
          MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                              MemLocs[bucket[q]][index].key = arg[q].key].val
          BY Zenon, <4>6, <4>5
        <4>8. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY <4>7, Zenon DEF ValOfKeyInBktAtAddr
        <4> QED
          BY <4>1, <4>3, <4>8, Zenon
      <3> QED
        BY <3>1, <3>2, <3>3
    <2>13. UniqInv'
      <3> SUFFICES ASSUME NEW a \in AllocAddrs', 
                          NEW bucket_arr, bucket_arr = MemLocs'[a],
                          NEW j1 \in 1..Len(bucket_arr),
                          NEW j2 \in 1..Len(bucket_arr),
                          bucket_arr[j1].key = bucket_arr[j2].key
                    PROVE  j1 = j2
        BY Zenon DEF UniqInv
      <3>1. PICK addr \in Addrs : /\ addr \notin AllocAddrs
                                  /\ AllocAddrs' = AllocAddrs \cup {addr}
                                  /\ IF bucket[p] = NULL
                                        THEN MemLocs' = [MemLocs EXCEPT ![addr] = <<arg[p]>>]
                                        ELSE MemLocs' = [MemLocs EXCEPT ![addr] = Append(MemLocs[bucket[p]], arg[p])]
        BY Zenon
      <3>2. \A ad \in Addrs : ad # addr => MemLocs'[ad] = MemLocs[ad]
        BY <3>1, Zenon
      <3>3. CASE a # addr
        BY <3>1, <3>2, <3>3, Zenon DEF UniqInv
      <3> SUFFICES ASSUME a = addr
                    PROVE  j1 = j2
        BY <3>3
      <3>4. CASE bucket[p] = NULL
        <4>1. Len(bucket_arr) = 1
          BY <3>1, <3>4
        <4> QED
          BY <4>1
      <3>5. CASE bucket[p] # NULL
        <4>1. bucket_arr = Append(MemLocs[bucket[p]], arg[p])
          BY <3>1, <3>5, Zenon
        <4>2. MemLocs[bucket[p]] \in Seq([key: KeyDomain, val: ValDomain])
          BY <3>5, Zenon
        <4>3. arg[p] \in [key: KeyDomain, val: ValDomain]
          BY RemDef, Zenon DEF LineIDtoOp, ArgsOf
        <4>A. Len(bucket_arr) = Len(MemLocs[bucket[p]])+1
          BY <4>1, <4>2, <4>3, AppendProperties
        <4>4. \A index \in 1..Len(MemLocs[bucket[p]]) : Append(MemLocs[bucket[p]], arg[p])[index] = MemLocs[bucket[p]][index]
          BY <4>2, <4>3, AppendProperties
        <4>5. \A index \in 1..Len(MemLocs[bucket[p]]) : bucket_arr[index] = MemLocs[bucket[p]][index]
          BY <4>1, <4>4, Zenon
        <4>6. CASE j1 = Len(bucket_arr)
          <5>1. bucket_arr[j1] = arg[p]
            <6>1. Append(MemLocs[bucket[p]], arg[p])[Len(MemLocs[bucket[p]])+1] = arg[p]
              BY <4>2, <4>3, AppendProperties
            <6>2. bucket_arr[Len(bucket_arr)] = arg[p]
              BY <4>1, <4>A, <6>1, Zenon
            <6> QED
              BY <4>6, <6>2
          <5>2. \A index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key # arg[p].key
            BY Zenon, <3>5 DEF KeyInBktAtAddr, BktInv
          <5>3. \A index \in 1..Len(MemLocs[bucket[p]]) : bucket_arr[index].key # arg[p].key
            BY <4>5, <5>2, Zenon
          <5>4. j2 \notin 1..Len(MemLocs[bucket[p]])
            BY <5>1, <5>3
          <5>5. j2 = Len(bucket_arr)
            BY <4>A, <5>4
          <5> QED
            BY <4>6, <5>5
        <4>7. CASE j2 = Len(bucket_arr)
          <5>1. bucket_arr[j2] = arg[p]
            <6>1. Append(MemLocs[bucket[p]], arg[p])[Len(MemLocs[bucket[p]])+1] = arg[p]
              BY <4>2, <4>3, AppendProperties
            <6>2. bucket_arr[Len(bucket_arr)] = arg[p]
              BY <4>1, <4>A, <6>1, Zenon
            <6> QED
              BY <4>7, <6>2
          <5>2. \A index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key # arg[p].key
            BY Zenon, <3>5 DEF KeyInBktAtAddr, BktInv
          <5>3. \A index \in 1..Len(MemLocs[bucket[p]]) : bucket_arr[index].key # arg[p].key
            BY <4>5, <5>2, Zenon
          <5>4. j1 \notin 1..Len(MemLocs[bucket[p]])
            BY <5>1, <5>3
          <5>5. j1 = Len(bucket_arr)
            BY <4>A, <5>4
          <5> QED
            BY <4>6, <5>5
        <4>8. CASE j1 # Len(bucket_arr) /\ j2 # Len(bucket_arr)
          <5>1. j1 \in 1..Len(MemLocs[bucket[p]]) /\ j2 \in 1..Len(MemLocs[bucket[p]])
            BY <4>A, <4>8
          <5>2. bucket[p] \in AllocAddrs
            BY <3>5
          <5> QED
            BY <4>5, <5>1, <5>2 DEF UniqInv
        <4> QED
          BY <4>6, <4>7, <4>8
      <3> QED
        BY <3>4, <3>5
    <2>14. NewBktInv'
      <3> SUFFICES ASSUME NEW q \in ProcSet
                    PROVE  /\ pc'[q] = "I4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
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
        BY ZenonT(60) DEF NewBktInv
      <3> PICK addr \in Addrs : /\ addr \notin AllocAddrs
                                /\ AllocAddrs' = AllocAddrs \cup {addr}
                                /\ newbkt' = [newbkt EXCEPT ![p] = addr]
                                /\ IF bucket[p] = NULL
                                      THEN MemLocs' = [MemLocs EXCEPT ![addr] = <<arg[p]>>]
                                      ELSE MemLocs' = [MemLocs EXCEPT ![addr] = Append(MemLocs[bucket[p]], arg[p])]
        BY Zenon
      <3>A. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
        BY ZenonT(30)
      <3>B. ASSUME NEW k \in KeyDomain, q # p, pc[q] \in {"I4", "U4", "R4"}
            PROVE  /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
                   /\ KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
                   /\ KeyInBktAtAddr(k, bucket[q]) => (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])')
                   /\ KeyInBktAtAddr(k, newbkt[q]) => (ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])')
        <4> USE <3>B
        <4>1. bucket[q] = bucket'[q] /\ newbkt'[q] = newbkt[q] /\ newbkt[q] \in AllocAddrs
          BY NULLDef, Zenon DEF AddrsInv
        <4>2. MemLocs[newbkt[q]] = MemLocs'[newbkt'[q]]
          BY <3>A, <4>1, Zenon
        <4>3. KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'  
          BY Zenon, <4>1, <4>2 DEF KeyInBktAtAddr
        <4>4. ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
          <5> DEFINE bkt_arr == MemLocs'[newbkt'[q]]
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
          <5>1. ValOfKeyInBktAtAddr(k, newbkt[q])' = bkt_arr[idx].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>2. bkt_arr = MemLocs[newbkt[q]]
            BY Zenon, <4>2
          <5>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
            BY Zenon
          <5> QED
            BY <5>1, <5>2, <5>3, Isa DEF ValOfKeyInBktAtAddr
        <4>5. CASE bucket[q] = NULL
          BY <4>1, <4>3, <4>4, <4>5, Zenon DEF KeyInBktAtAddr
        <4> SUFFICES ASSUME bucket[q] \in AllocAddrs
                      PROVE  /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
                             /\ KeyInBktAtAddr(k, bucket[q]) => (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])')
          BY NULLDef, <4>5, <4>3, <4>4, Zenon
        <4>6. MemLocs[bucket[q]] = MemLocs'[bucket'[q]]
          BY <3>A, <4>1, Zenon
        <4>7. KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'  
          BY Zenon, <4>1, <4>6 DEF KeyInBktAtAddr
        <4> SUFFICES ASSUME KeyInBktAtAddr(k, bucket[q])
                      PROVE  ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
          BY <4>7, Zenon
        <4>8. ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
          <5> DEFINE bkt_arr == MemLocs'[bucket'[q]]
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
          <5>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>2. bkt_arr = MemLocs[bucket[q]]
            BY Zenon, <4>6
          <5>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
            BY Zenon
          <5> QED
            BY <5>1, <5>2, <5>3, Isa DEF ValOfKeyInBktAtAddr
        <4> QED
          BY <4>8
      <3>1. CASE pc'[q] = "I4"
        <4> USE <3>1
        <4> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                     /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                     /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                               /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                  (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
          OBVIOUS
        <4>1. CASE q = p
          <5> USE <4>1
          <5>1. CASE bucket[p] = NULL
            <6> USE <5>1
            <6> DEFINE bkt_arr == MemLocs'[newbkt'[q]]
            <6>1. newbkt'[q] = addr /\ bkt_arr = <<arg[q]>> /\ arg = arg'
              BY Zenon
            <6>2. KeyInBktAtAddr(arg[q].key, newbkt[q])'
              <7> SUFFICES newbkt'[q] # NULL /\ \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
                BY Zenon DEF KeyInBktAtAddr
              <7> SUFFICES newbkt'[q] # NULL /\ \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                BY <6>1 
              <7>1. newbkt'[q] # NULL
                BY <6>1, NULLDef, Zenon
              <7>2. Len(bkt_arr) = 1
                BY <6>1
              <7>3. 1 \in 1..Len(bkt_arr)
                <8>1. 1 \in 1..1
                  OBVIOUS
                <8>2. 1 \in 1..Len(bkt_arr)
                  BY <8>1, Zenon
                <8> QED
                  BY <8>2
              <7>4. bkt_arr[1].key = arg[q].key
                BY <6>1
              <7> QED
                BY <7>1, <7>3, <7>4
            <6>3. ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
              <7>1. ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = bkt_arr[idx].val
                BY <6>1, Zenon DEF ValOfKeyInBktAtAddr
              <7>2. Len(bkt_arr) = 1
                BY <6>1
              <7>3. \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                BY <6>1, <6>2, Zenon DEF KeyInBktAtAddr
              <7>4. idx = 1
                BY <7>2, <7>3
              <7>5. bkt_arr[idx].val = arg[q].val
                <8>1. bkt_arr[1] = arg[q]
                  BY <6>1
                <8> QED
                  BY <8>1, <7>4, Zenon
              <7> QED
                BY <7>1, <7>5
            <6>4. ASSUME NEW k \in KeyDomain, k # arg[q].key
                  PROVE  /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])' 
                         /\ KeyInBktAtAddr(k, bucket[q])' =>
                            (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              <7> USE <6>4
              <7>1. KeyInBktAtAddr(k, bucket[q])' = FALSE
                BY Zenon DEF KeyInBktAtAddr
              <7>2. KeyInBktAtAddr(k, newbkt[q])' = FALSE
                <8>1. Len(bkt_arr) = 1
                  BY <6>1
                <8>2. \A index \in 1..Len(bkt_arr) : index = 1
                  <9>1. \A index \in 1..1 : index = 1
                    OBVIOUS
                  <9> QED
                    BY <8>1, <9>1, Zenon
                <8>3. \A index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                  BY <8>2
                <8> QED
                  BY <8>3, Zenon DEF KeyInBktAtAddr 
              <7> QED
                BY <7>1, <7>2, Zenon
            <6> QED
              BY <6>2, <6>3, <6>4
          <5>2. CASE bucket[p] # NULL
            <6> USE <5>2
            <6> DEFINE bkt_arr == MemLocs'[newbkt'[q]]
            <6>1. newbkt'[q] = addr /\ bkt_arr = Append(MemLocs[bucket[q]], arg[q]) /\ arg = arg'
              BY Zenon
            <6>2. KeyInBktAtAddr(arg[q].key, newbkt[q])'
              <7> SUFFICES newbkt'[q] # NULL /\ \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
                BY Zenon DEF KeyInBktAtAddr
              <7> SUFFICES newbkt'[q] # NULL /\ \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                BY <6>1 
              <7>1. newbkt'[q] # NULL
                BY <6>1, NULLDef, Zenon
              <7>2. MemLocs[bucket[q]] \in Seq([key: KeyDomain, val: ValDomain])
                BY Zenon
              <7>3. arg[q] \in [key: KeyDomain, val: ValDomain]
                BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
              <7>4. bkt_arr[Len(bkt_arr)] = arg[q]
                BY <6>1, <7>2, <7>3, AppendProperties
              <7>5. Len(bkt_arr) \in 1..Len(bkt_arr)
                BY <7>2, <7>3, AppendProperties, LenProperties
              <7> QED
                BY <7>1, <7>4, <7>5
            <6>3. ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
              <7>1. ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = bkt_arr[idx].val
                BY Zenon, <6>1 DEF ValOfKeyInBktAtAddr
              <7> PICK index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                BY Zenon, <6>1, <6>2 DEF KeyInBktAtAddr
              <7> idx = index
                OBVIOUS
              <7>2. MemLocs[bucket[q]] \in Seq([key: KeyDomain, val: ValDomain])
                BY Zenon
              <7>3. arg[q] \in [key: KeyDomain, val: ValDomain]
                BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
              <7>4. bkt_arr[Len(bkt_arr)] = arg[q]
                BY <6>1, <7>2, <7>3, AppendProperties
              <7>5. Len(MemLocs[bucket[q]]) \in Nat /\ Len(bkt_arr) \in 1..Len(bkt_arr) /\ Len(bkt_arr) = Len(MemLocs[bucket[q]])+1
                BY <7>2, <7>3, AppendProperties, LenProperties
              <7>6. \A ind \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][ind].key # arg[q].key
                BY Zenon DEF BktInv, KeyInBktAtAddr
              <7>7. index = Len(bkt_arr)
                BY <7>5, <7>6, Z3T(90)
              <7>8. bkt_arr[index] = arg[q]
                BY <7>4, <7>7, Zenon
              <7> QED
                BY <7>1, <7>8, Zenon
            <6>4. ASSUME NEW k \in KeyDomain, k # arg[q].key
                  PROVE  /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])' 
                         /\ KeyInBktAtAddr(k, bucket[q])' =>
                            (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              <7> USE <6>4
              <7>1. CASE KeyInBktAtAddr(k, bucket[q])' = TRUE
                <8> USE <7>1
                <8> SUFFICES /\ KeyInBktAtAddr(k, newbkt[q])'
                              /\ ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])'
                  BY Zenon 
                <8>1. bucket[q] \in AllocAddrs
                  BY Zenon
                <8>2. bucket[q] # addr /\ bucket[q] = bucket'[q]
                  BY <8>1, Zenon
                <8>3. MemLocs'[bucket'[q]] = MemLocs[bucket[q]]
                  BY Zenon, <3>A, <8>2
                <8>4. \E index \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][index].key = k
                  BY Zenon, <8>3 DEF KeyInBktAtAddr
                <8>5. MemLocs[bucket[q]] \in Seq([key: KeyDomain, val: ValDomain])
                  BY Zenon
                <8>6. arg[q] \in [key: KeyDomain, val: ValDomain]
                  BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
                <8>7. /\ \A index \in 1..Len(MemLocs[bucket[q]]) : bkt_arr[index] = MemLocs[bucket[q]][index]
                        /\ Len(MemLocs[bucket[q]]) \in Nat
                        /\ Len(bkt_arr) = Len(MemLocs[bucket[q]])+1
                        /\ bkt_arr[Len(bkt_arr)] = arg[q]
                  BY <8>5, <8>6, AppendProperties, LenProperties
                <8>8. \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                  BY <8>4, <8>7
                <8>9. newbkt'[q] # NULL
                  BY NULLDef
                <8>10. KeyInBktAtAddr(k, newbkt[q])'
                  BY <6>1, <8>8, <8>9, Zenon DEF KeyInBktAtAddr
                <8> DEFINE idx == CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) : MemLocs'[bucket'[q]][index].key = k
                <8>11. ValOfKeyInBktAtAddr(k, bucket[q])' = MemLocs'[bucket'[q]][idx].val
                    BY Zenon, <8>3 DEF ValOfKeyInBktAtAddr
                <8> PICK index \in 1..Len(MemLocs'[bucket'[q]]) : MemLocs'[bucket'[q]][index].key = k
                  BY Zenon DEF KeyInBktAtAddr
                <8> idx = index
                  OBVIOUS
                <8> index \in 1..Len(MemLocs[bucket[q]]) /\ MemLocs[bucket[q]][index].key = k
                  BY <8>3
                <8>12. ValOfKeyInBktAtAddr(k, bucket[q])' = MemLocs[bucket[q]][index].val
                  BY <8>3, <8>11, Zenon
                <8>13. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[index].val
                  BY <8>12, <8>7, Zenon
                <8>14. bkt_arr[Len(bkt_arr)].key # k
                  BY <8>7
                <8>15. \A ind \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][ind].key = MemLocs[bucket[q]][index].key => ind = index
                  BY Zenon, <8>1 DEF UniqInv
                <8>16. \A ind \in 1..Len(MemLocs[bucket[q]]) : ind # index => MemLocs[bucket[q]][ind].key # k
                  BY <8>15, Zenon
                <8>17. \A ind \in 1..Len(bkt_arr) : ind # index => bkt_arr[ind].key # k
                  BY <8>16, <8>14, <8>7, Z3T(1200)
                <8>18. \E ind \in 1..Len(bkt_arr) : bkt_arr[ind].key = k
                  BY <8>7
                <8>19. ValOfKeyInBktAtAddr(k, newbkt[q])' = bkt_arr[index].val
                  BY <6>1, <8>17, <8>18, Zenon DEF ValOfKeyInBktAtAddr
                <8> QED
                  BY <8>10, <8>13, <8>19, Zenon
              <7>2. CASE KeyInBktAtAddr(k, bucket[q])' = FALSE
                <8> USE <7>2
                <8> SUFFICES KeyInBktAtAddr(k, newbkt[q])' = FALSE
                  BY Zenon
                <8>1. bucket[q] \in AllocAddrs
                  BY Zenon
                <8>2. bucket[q] # addr /\ bucket[q] = bucket'[q]
                  BY <8>1, Zenon
                <8>3. MemLocs'[bucket'[q]] = MemLocs[bucket[q]]
                  BY Zenon, <3>A, <8>2
                <8>4. \A index \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][index].key # k
                  BY Zenon, <8>3 DEF KeyInBktAtAddr
                <8>5. MemLocs[bucket[q]] \in Seq([key: KeyDomain, val: ValDomain])
                  BY Zenon
                <8>6. arg[q] \in [key: KeyDomain, val: ValDomain]
                  BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
                <8>7. bkt_arr[Len(bkt_arr)].key # k
                  BY <6>1, <8>5, <8>6, AppendProperties
                <8>8. /\ \A index \in 1..Len(MemLocs[bucket[q]]) : bkt_arr[index] = MemLocs[bucket[q]][index]
                        /\ Len(MemLocs[bucket[q]]) \in Nat
                        /\ Len(bkt_arr) = Len(MemLocs[bucket[q]])+1
                  BY <8>5, <8>6, AppendProperties, LenProperties
                <8> QED
                  BY <8>4, <8>7, <8>8 DEF KeyInBktAtAddr
              <7> QED
                BY <7>1, <7>2, Zenon DEF KeyInBktAtAddr
            <6> QED
              BY <6>2, <6>3, <6>4
          <5> QED
            BY <5>1, <5>2
        <4>2. CASE q # p
          <5> USE <4>2
          <5>1. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                          /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                              (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
            BY Zenon DEF NewBktInv
          <5>2. arg[q].key \in KeyDomain
            BY RemDef, Zenon DEF ArgsOf, LineIDtoOp
          <5> QED
            BY <3>B, <5>1, <5>2, ZenonT(30)
        <4> QED
          BY <4>1, <4>2
      <3>2. CASE pc'[q] = "U4"
        <4> USE <3>2
        <4>1. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
              /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
              /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                        /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                            (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
          BY Zenon DEF NewBktInv
        <4>2. arg[q].key \in KeyDomain
          BY RemDef, Zenon DEF ArgsOf, LineIDtoOp
        <4> QED
          BY <3>B, <4>1, <4>2, ZenonT(30)
      <3>3. CASE pc'[q] = "R4"
        <4> USE <3>3
        <4>1. /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])
              /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                        /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                            (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
          BY Zenon DEF NewBktInv
        <4>2. arg[q].key \in KeyDomain
          BY RemDef, Zenon DEF ArgsOf, LineIDtoOp
        <4> QED
          BY <3>B, <4>1, <4>2, ZenonT(30)
      <3> QED
        BY <3>1, <3>2, <3>3
    <2> QED
      BY <2>9, <2>10, <2>11, <2>12, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>13, <2>14 DEF Inv
  <1>4. CASE I4(p)
    <2> USE <1>4 DEF I4, TypeOK, Inv, vars
    <2>1. (pc \in [ProcSet -> LineIDs])'
      BY Isa DEF LineIDs
    <2>2. (A \in [1..N -> AllocAddrs \union {NULL}])'
      <3>1. CASE A[Hash[arg[p].key]] = bucket[p]
        <4> SUFFICES newbkt[p] \in AllocAddrs \union {NULL}
          BY <3>1, Isa
        <4> QED
          OBVIOUS
      <3>2. CASE A[Hash[arg[p].key]] # bucket[p] 
        BY <3>2
      <3> QED
        BY <3>1, <3>2
    <2>3. (MemLocs \in [Addrs -> Seq([key: KeyDomain, val: ValDomain])])'
      OBVIOUS
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
      OBVIOUS
    <2>10. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
      <3> SUFFICES arg[p] \in ArgsOf(LineIDtoOp(pc'[p]))
        BY Zenon
      <3> QED
        BY RemDef, ZenonT(30) DEF LineIDtoOp, ArgsOf
    <2>11. AddrsInv'
      <3> SUFFICES ASSUME NEW p_1 \in ProcSet',
                          (pc[p_1] \in {"I4", "U4", "R4"})'
                    PROVE  (/\ \A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                                              /\ newbkt[p_1] # newbkt[q])
                            /\ \A idx \in 1..N  : (A[idx] # newbkt[p_1])
                            /\ newbkt[p_1] # bucket[p_1]
                            /\ newbkt[p_1] \in AllocAddrs)'
        BY DEF AddrsInv
      <3>1. (\A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                            /\ newbkt[p_1] # newbkt[q]))'
        BY DEF AddrsInv
      <3>2. (\A idx \in 1..N  : (A[idx] # newbkt[p_1]))'
        BY DEF AddrsInv
      <3>3. (newbkt[p_1] # bucket[p_1])'
        BY DEF AddrsInv
      <3>4. (newbkt[p_1] \in AllocAddrs)'
        BY DEF AddrsInv
      <3>5. QED
        BY <3>1, <3>2, <3>3, <3>4
    <2>12. BktInv'
      <3> SUFFICES ASSUME NEW q \in ProcSet
                    PROVE  (/\ pc'[q] \in {"I3", "I4"} => (/\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                          /\ r'[q] = NULL)
                            /\ pc'[q] \in {"U3", "U4"} => (IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                                    /\ r'[q] # NULL)
                                                              ELSE r'[q] = NULL)
                            /\ pc'[q] \in {"R3", "R4"} => (/\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                          /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                          /\ r'[q] # NULL))
        BY DEF BktInv
      <3>1. CASE pc'[q] \in {"I3", "I4"}
        <4> USE <3>1
        <4> SUFFICES ~KeyInBktAtAddr(arg[q].key, bucket[q])' /\ r'[q] = NULL
          OBVIOUS
        <4>1. ~KeyInBktAtAddr(arg[q].key, bucket[q]) /\ r[q] = NULL
          BY Zenon DEF BktInv
        <4> QED
          BY <4>1, Zenon DEF KeyInBktAtAddr
      <3>2. CASE pc'[q] \in {"U3", "U4"}
        <4> USE <3>2
        <4> SUFFICES IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                        THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                              /\ r'[q] # NULL)
                        ELSE r'[q] = NULL
          OBVIOUS
        <4>1. IF KeyInBktAtAddr(arg[q].key, bucket[q])
                  THEN (/\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                        /\ r[q] # NULL)
                  ELSE r[q] = NULL
          BY Zenon DEF BktInv
        <4>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY Zenon DEF KeyInBktAtAddr
        <4>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
          MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                MemLocs'[bucket'[q]][index].key = arg'[q].key].val
          BY DEF ValOfKeyInBktAtAddr
        <4>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
          BY Zenon
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
          BY <4>1, <4>2, <4>7, Zenon
      <3>3. CASE pc'[q] \in {"R3", "R4"}
        <4> USE <3>3
        <4> SUFFICES /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                      /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                      /\ r'[q] # NULL
          OBVIOUS
        <4>1. /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              /\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              /\ r[q] # NULL
          BY Zenon DEF BktInv
        <4>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY Zenon DEF KeyInBktAtAddr
        <4>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
          MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                MemLocs'[bucket'[q]][index].key = arg'[q].key].val
          BY DEF ValOfKeyInBktAtAddr
        <4>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
          BY Zenon
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
          BY <4>1, <4>2, <4>7, Zenon
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
        BY Zenon DEF UniqInv
    <2>14. NewBktInv'
      <3> SUFFICES ASSUME NEW q \in ProcSet
                    PROVE  /\ pc'[q] = "I4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
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
        BY ZenonT(60) DEF NewBktInv
      <3>0. ASSUME NEW k \in KeyDomain
            PROVE  /\ pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
                   /\ KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
                   /\ pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                   /\ ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
        <4> USE <3>0
        <4>1. pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
          BY Zenon DEF KeyInBktAtAddr
        <4>2. KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
          BY Zenon DEF KeyInBktAtAddr
        <4>3. pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
          <5> SUFFICES ASSUME pc[q] \in {"I4", "U4", "R4"}
                        PROVE  ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
            OBVIOUS
          <5> DEFINE bkt_arr == MemLocs'[bucket'[q]]
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
          <5>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>2. bkt_arr = MemLocs[bucket[q]]
            BY Zenon
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
            BY Zenon
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
          BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
        <4>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
              /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
              /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                        /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                            (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
          BY <4>1, Zenon DEF NewBktInv
        <4> QED
          BY <3>0, <4>1, <4>2, ZenonT(30)
      <3>2. CASE pc'[q] = "U4"
        <4> USE <3>2
        <4> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                      /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                      /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                  (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
          OBVIOUS
        <4>1. pc[q] = "U4" /\ arg[q].key \in KeyDomain
          BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
        <4>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
              /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
              /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                        /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                            (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
          BY <4>1, Zenon DEF NewBktInv
        <4> QED
          BY <3>0, <4>1, <4>2, ZenonT(30)
      <3>3. CASE pc'[q] = "R4"
        <4> USE <3>3
        <4> SUFFICES /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                      /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                  (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
          OBVIOUS
        <4>1. pc[q] = "R4" /\ arg[q].key \in KeyDomain
          BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
        <4>2. /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])
              /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                        /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                            (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
          BY <4>1, Zenon DEF NewBktInv
        <4> QED
          BY <3>0, <4>1, <4>2, ZenonT(30)
      <3> QED
        BY <3>1, <3>2, <3>3
    <2> QED
      BY <2>9, <2>10, <2>11, <2>12, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>13, <2>14 DEF Inv
  <1> QED
    BY <1>1, <1>2, <1>3, <1>4

======================================================================================
\* Modification History
\* Last modified Mon Aug 26 15:57:06 EDT 2024 by uguryavuz
\* Created Mon Jul 08 12:21:04 EDT 2024 by uyavuz
