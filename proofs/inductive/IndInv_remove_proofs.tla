--------------------------- MODULE IndInv_remove_proofs ----------------------
(***************************************************************************
 This module contains the proof of RemoveInv from IndInv.tla
 ***************************************************************************)
EXTENDS IndInv, Assumptions, TLAPS,
        SequenceTheorems, FiniteSets

\* RemoveInv = Inv /\ (\E p \in ProcSet : \/ R1(p)
\*                                        \/ R2(p)
\*                                        \/ R3(p)
\*                                        \/ R4(p)) => Inv'
LEMMA RemoveInv
  <1> SUFFICES ASSUME Inv,
                      NEW p \in ProcSet,
                      \/ R1(p)
                      \/ R2(p)
                      \/ R3(p)
                      \/ R4(p)
               PROVE  Inv'
    BY DEF RemoveInv
  <1>1. CASE R1(p)
    <2> USE <1>1 DEF R1, TypeOK, Inv, vars
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
          <5>1. arg[p] \in [key: KeyDomain]
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
  <1>2. CASE R2(p)
    <2> USE <1>2 DEF R2, TypeOK, Inv, vars
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
        BY RemDef, ZenonT(45) DEF LineIDtoOp, ArgsOf
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
        <4>A. CASE p = q
          <5> USE <4>A
          <5>1. KeyInBktAtAddr(arg[p].key, bucket[p])
            BY <4>A, Zenon
          <5>B. KeyInBktAtAddr(arg[p].key, bucket[p])'
            BY <5>1, Zenon DEF KeyInBktAtAddr
          <5>2. r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY <5>1, Zenon
          <5>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
            MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                  MemLocs'[bucket'[q]][index].key = arg'[q].key].val
            BY DEF ValOfKeyInBktAtAddr
          <5>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
            BY Zenon
          <5>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
            MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                MemLocs[bucket'[q]][index].key = arg[q].key].val
            BY Zenon, <5>3, <5>4
          <5>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
            MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                MemLocs[bucket[q]][index].key = arg[q].key].val
            BY <5>4, <5>5
          <5>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY <5>6, Zenon DEF ValOfKeyInBktAtAddr
          <5>8. \E index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key = arg[p].key
            BY <5>1, Zenon DEF KeyInBktAtAddr
          <5>9. ValOfKeyInBktAtAddr(arg[p].key, bucket[p]) = MemLocs[bucket[p]][CHOOSE index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key = arg[p].key].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>10. PICK index \in 1..Len(MemLocs[bucket[p]]) : /\ MemLocs[bucket[p]][index].key = arg[p].key
                                                              /\ ValOfKeyInBktAtAddr(arg[p].key, bucket[p]) = MemLocs[bucket[p]][index].val
            BY <5>8, <5>9, Zenon
          <5>11. MemLocs[bucket[p]] \in Seq([key: KeyDomain, val: ValDomain])
            BY <4>A, Zenon DEF KeyInBktAtAddr
          <5>12. MemLocs[bucket[p]][index] \in [key: KeyDomain, val: ValDomain]
            BY <5>10, <5>11, ElementOfSeq, Zenon
          <5>13. MemLocs[bucket[p]][index].val \in ValDomain
            BY <5>12
          <5> SUFFICES r'[q] # NULL
            BY <5>B, <5>2, <5>7
          <5> QED
            BY <5>2, <5>7, <5>10, <5>13, NULLDef
        <4> SUFFICES ASSUME p # q
                      PROVE  /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                            /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                            /\ r'[q] # NULL
          BY <4>A
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
      BY  <2>9, <2>10, <2>11, <2>12, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>13, <2>14 DEF Inv
  <1>3. CASE R3(p)
    <2> USE <1>3 DEF R3, TypeOK, Inv, vars
    <2>1. (pc \in [ProcSet -> LineIDs])'
      BY Isa DEF LineIDs
    <2>2. (A \in [1..N -> AllocAddrs \union {NULL}])'
      BY Zenon
    <2>3. (MemLocs \in [Addrs -> Seq([key: KeyDomain, val: ValDomain])])'
      <3> DEFINE idx == IdxInBktAtAddr(arg[p].key, bucket[p])
      <3> DEFINE bucket_arr == MemLocs[bucket[p]]
      <3>1. PICK addr \in Addrs : 
        /\ addr \notin AllocAddrs
        /\ AllocAddrs' = AllocAddrs \cup {addr}
        /\ newbkt' = [newbkt EXCEPT ![p] = addr]
        /\ MemLocs' = [MemLocs EXCEPT ![addr] = SubSeq(bucket_arr, 1, idx-1) \o SubSeq(bucket_arr, idx+1, Len(bucket_arr))]
        BY Zenon
      <3> SUFFICES MemLocs'[addr] \in Seq([key: KeyDomain, val: ValDomain])
        BY Zenon, <3>1
      <3> SUFFICES /\ SubSeq(bucket_arr, 1, idx-1) \in Seq([key: KeyDomain, val: ValDomain])
                    /\ SubSeq(bucket_arr, idx+1, Len(bucket_arr)) \in Seq([key: KeyDomain, val: ValDomain])
        BY ConcatProperties, Zenon, <3>1
      <3> HIDE DEF R3
      <3> SUFFICES /\ idx \in 1..Len(bucket_arr)
                    /\ \A i \in 1..Len(bucket_arr) : bucket_arr[i] \in [key: KeyDomain, val: ValDomain]
        BY SubSeqProperties
      <3>2. bucket_arr \in Seq([key: KeyDomain, val: ValDomain])
        BY Zenon, NULLDef DEF BktInv, KeyInBktAtAddr, R3
      <3>3. \A i \in 1..Len(bucket_arr) : bucket_arr[i] \in [key: KeyDomain, val: ValDomain]
        BY ElementOfSeq, Zenon, <3>2
      <3>4. idx = CHOOSE index \in 1..Len(bucket_arr) : bucket_arr[index].key = arg[p].key
        BY DEF IdxInBktAtAddr
      <3>5. \E index \in 1..Len(bucket_arr) : bucket_arr[index].key = arg[p].key
        <4>1. KeyInBktAtAddr(arg[p].key, bucket[p])
          BY Zenon DEF BktInv, R3
        <4> QED
          BY <4>1 DEF KeyInBktAtAddr
      <3> QED
        BY <3>3, <3>4, <3>5
    <2>4. (AllocAddrs \in SUBSET Addrs)'
      BY Zenon
    <2>5. (bucket \in [ProcSet -> AllocAddrs \union {NULL}])'
      BY Zenon
    <2>6. (newbkt \in [ProcSet -> AllocAddrs \union {NULL}])'
      BY Zenon
    <2>7. (r \in [ProcSet -> ValDomain \union {NULL}])'
      BY Zenon
    <2>8. (arg \in [ProcSet -> ArgDomain])'
      BY Zenon
    <2>9. (ret \in [ProcSet -> RetDomain])'
      BY Zenon
    <2>10. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
      <3> SUFFICES arg[p] \in ArgsOf(LineIDtoOp(pc'[p]))
        BY Zenon
      <3> QED
        BY RemDef, ZenonT(45) DEF LineIDtoOp, ArgsOf
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
      <3> HIDE DEF R3
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
            BY <5>1, Zenon DEF R3
          <5>3. newbkt[q] \in AllocAddrs \/ newbkt[q] = NULL
            OBVIOUS
          <5>4. newbkt'[q] \in AllocAddrs \/ newbkt'[q] = NULL
            BY <3>1, <5>3, Zenon DEF R3
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
            BY <2>2, Zenon DEF R3
          <5> QED
            BY <4>1, <5>1
        <4>4. newbkt'[p_1] # bucket'[p_1]
          <5>1. bucket'[p_1] \in AllocAddrs \/ bucket'[p_1] = NULL
            BY Zenon DEF R3
          <5> QED
            BY <4>1, <5>1
        <4>5. newbkt'[p_1] \in AllocAddrs'
          BY <3>1, Zenon DEF AddrsInv, R3
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
          <5>1. \A q1 \in ProcSet : (p_1 # q1 => (newbkt[p_1] # bucket[q1] /\ newbkt[p_1] # newbkt[q1]))
            BY <3>2, Zenon DEF AddrsInv, R3
          <5>2. newbkt'[p_1] = newbkt[p_1] /\ bucket'[q] = bucket[q] /\ (q # p => newbkt'[q] = newbkt[q])
            BY <3>2, Zenon DEF R3
          <5>3. newbkt'[p_1] # bucket'[q]
            BY <5>1, <5>2, Zenon
          <5>4. newbkt'[p_1] # newbkt'[q]
            <6>1. CASE q = p
              <7>1. newbkt'[q] \notin AllocAddrs
                BY <6>1, Zenon DEF R3
              <7>2. newbkt'[p_1] \in AllocAddrs
                BY <3>2, Zenon DEF AddrsInv, R3
              <7> QED  
                BY <7>1, <7>2
            <6>2. CASE q # p
              BY <3>2, <6>2, <5>1, <5>2
            <6> QED
              BY <6>1, <6>2
          <5>5. QED
            BY <5>3, <5>4
        <4>2. \A idx \in 1..N  : (A'[idx] # newbkt'[p_1])
          BY <3>2, Zenon DEF AddrsInv, R3
        <4>3. newbkt'[p_1] # bucket'[p_1]
          BY <3>2, Zenon DEF AddrsInv, R3
        <4>4. newbkt'[p_1] \in AllocAddrs'
          BY <3>2, Zenon DEF AddrsInv, R3
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
      <3> HIDE DEF R3
      <3>1. CASE pc'[q] \in {"I3", "I4"}
        <4>1. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
          <5>1. CASE bucket[q] = NULL
            <6> USE <5>1
            <6>1. KeyInBktAtAddr(arg[q].key, bucket[q]) = FALSE
              BY DEF KeyInBktAtAddr
            <6>2. bucket'[q] = NULL
              BY Zenon DEF R3
            <6>3. KeyInBktAtAddr(arg[q].key, bucket[q])' = FALSE
              BY <6>2 DEF KeyInBktAtAddr
            <6> QED
              BY <6>1, <6>3, Zenon
          <5>2. CASE bucket[q] # NULL
            <6> USE <5>2
            <6>1. KeyInBktAtAddr(arg[q].key, bucket[q]) = \E index \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][index].key = arg[q].key
              BY Zenon DEF KeyInBktAtAddr, R3
            <6>2. bucket'[q] = bucket[q] /\ bucket[q] \in AllocAddrs
              BY Zenon DEF R3
            <6>3. MemLocs'[bucket[q]] = MemLocs[bucket[q]] /\ arg' = arg
              BY <6>2, Zenon DEF R3
            <6>4. KeyInBktAtAddr(arg[q].key, bucket[q])' = \E index \in 1..Len(MemLocs'[bucket'[q]]) : MemLocs'[bucket'[q]][index].key = arg'[q].key
              BY Zenon DEF KeyInBktAtAddr, R3
            <6>5. KeyInBktAtAddr(arg[q].key, bucket[q])' = \E index \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][index].key = arg[q].key
              BY <6>2, <6>3, <6>4
            <6> QED
              BY <6>1, <6>5
          <5> QED
            BY <5>1, <5>2
        <4> USE <3>1
        <4> SUFFICES ~KeyInBktAtAddr(arg[q].key, bucket[q])' /\ r'[q] = NULL
          OBVIOUS
        <4>3. ~KeyInBktAtAddr(arg[q].key, bucket[q]) /\ r[q] = NULL
          BY Zenon DEF BktInv, R3
        <4> QED
          BY <4>3, <4>1, Zenon DEF KeyInBktAtAddr, R3
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
          BY Zenon DEF BktInv, R3
        <4>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
          <5>1. CASE bucket[q] = NULL
            <6> USE <5>1
            <6>1. KeyInBktAtAddr(arg[q].key, bucket[q]) = FALSE
              BY DEF KeyInBktAtAddr
            <6>2. bucket'[q] = NULL
              BY Zenon DEF R3
            <6>3. KeyInBktAtAddr(arg[q].key, bucket[q])' = FALSE
              BY <6>2 DEF KeyInBktAtAddr
            <6> QED
              BY <6>1, <6>3, Zenon
          <5>2. CASE bucket[q] # NULL
            <6> USE <5>2
            <6>1. KeyInBktAtAddr(arg[q].key, bucket[q]) = \E index \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][index].key = arg[q].key
              BY Zenon DEF KeyInBktAtAddr
            <6>2. bucket'[q] = bucket[q] /\ bucket[q] \in AllocAddrs
              BY Zenon DEF R3
            <6>3. MemLocs'[bucket[q]] = MemLocs[bucket[q]] /\ arg' = arg
              BY <6>2, Zenon DEF R3
            <6>4. KeyInBktAtAddr(arg[q].key, bucket[q])' = \E index \in 1..Len(MemLocs'[bucket'[q]]) : MemLocs'[bucket'[q]][index].key = arg'[q].key
              BY Zenon DEF KeyInBktAtAddr, R3
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
            BY Zenon, <4>3 DEF KeyInBktAtAddr, R3
          <5>3. MemLocs'[bucket'[q]] = MemLocs[bucket[q]]
            BY <3>0, <5>2, Zenon DEF R3
          <5>4. arg' = arg
            BY Zenon DEF R3
          <5>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
            MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                MemLocs[bucket[q]][index].key = arg[q].key].val
            BY <5>1, <5>3, <5>4
          <5>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY <5>5, Zenon DEF ValOfKeyInBktAtAddr
          <5>7. r'[q] = r[q]
            BY Zenon DEF R3
          <5> QED
            BY <4>1, <4>2, <4>3, <5>6, <5>7
        <4>4. CASE ~KeyInBktAtAddr(arg[q].key, bucket[q])
          BY <4>1, <4>2, <4>4, Zenon DEF R3
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
          BY Zenon DEF BktInv, R3
        <4>2. MemLocs[bucket[q]] = MemLocs'[bucket'[q]]
          <5>1. bucket[q] = bucket'[q]
            BY Zenon DEF R3
          <5>2. bucket[q] \in AllocAddrs
            BY Zenon, <4>1 DEF KeyInBktAtAddr
          <5>3. bucket[q] # addr
            BY <3>0, <5>2
          <5>4. MemLocs'[bucket[q]] = MemLocs[bucket[q]]
            BY <3>0, <5>2, <5>3, Zenon
          <5> QED
            BY <5>1, <5>4
        <4>3. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY <4>2, Zenon DEF KeyInBktAtAddr, R3
        <4>4. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
          MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                MemLocs'[bucket'[q]][index].key = arg'[q].key].val
          BY DEF ValOfKeyInBktAtAddr
        <4>5. arg = arg'
          BY Zenon DEF R3
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
          BY <4>1, <4>3, <4>8, Zenon DEF R3
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
      <3> idx == IdxInBktAtAddr(arg[p].key, bucket[p])
      <3>1. PICK addr \in Addrs : /\ addr \notin AllocAddrs
                                  /\ AllocAddrs' = AllocAddrs \cup {addr}
                                  /\ MemLocs' = [MemLocs EXCEPT ![addr] = SubSeq(MemLocs[bucket[p]], 1, idx-1) \o SubSeq(MemLocs[bucket[p]], idx+1, Len(MemLocs[bucket[p]]))]
        BY Zenon
      <3>2. \A ad \in Addrs : ad # addr => MemLocs'[ad] = MemLocs[ad]
        BY <3>1, Zenon
      <3>3. CASE a # addr
        BY <3>1, <3>2, <3>3, Zenon DEF UniqInv
      <3> SUFFICES ASSUME a = addr
                    PROVE  j1 = j2
        BY <3>3
      <3>4. idx = CHOOSE index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key = arg[p].key
        BY DEF IdxInBktAtAddr
      <3>5. \E index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key = arg[p].key
        <4>1. KeyInBktAtAddr(arg[p].key, bucket[p])
          BY Zenon DEF BktInv, R3
        <4> QED
          BY <4>1 DEF KeyInBktAtAddr
      <3>6. bucket[p] # NULL
        BY Zenon DEF BktInv, KeyInBktAtAddr, R3
      <3>7. MemLocs[bucket[p]] \in Seq([key: KeyDomain, val: ValDomain])
        BY <3>6, Zenon
      <3>8. \A i \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][i] \in [key: KeyDomain, val: ValDomain]
        BY <3>7, ElementOfSeq, Zenon
      <3> HIDE DEF R3
      <3>9. idx \in 1..Len(MemLocs[bucket[p]])
        BY <3>4, <3>5, Zenon
      <3>10. \A i \in 1..idx-1 : MemLocs[bucket[p]][i] \in [key: KeyDomain, val: ValDomain]
        BY <3>8, <3>9
      <3>11. \A i \in idx+1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][i] \in [key: KeyDomain, val: ValDomain]
        BY <3>8, <3>9
      <3>12. idx \in Nat \ {0}
        BY <3>7, <3>9, LenProperties
      <3> DEFINE barr == MemLocs[bucket[p]]
      <3> DEFINE s1 == SubSeq(MemLocs[bucket[p]], 1, idx-1) 
      <3> DEFINE s2 == SubSeq(MemLocs[bucket[p]], idx+1, Len(MemLocs[bucket[p]])) 
      <3>13. /\ s1 \in Seq([key: KeyDomain, val: ValDomain])
             /\ Len(s1) = idx-1
             /\ \A i \in 1..idx-1 : s1[i] = barr[i]
        BY <3>9, <3>10, <3>12, SubSeqProperties, Z3T(90)
      <3>14. /\ s2 \in Seq([key: KeyDomain, val: ValDomain])
             /\ Len(s2) = Len(barr) - idx
             /\ \A i \in 1..Len(barr)-idx : s2[i] = barr[idx+i]
        BY <3>9, <3>11, <3>12, SubSeqProperties
      <3>15. /\ s2 \in Seq([key: KeyDomain, val: ValDomain])
             /\ Len(s2) = Len(barr)-idx
             /\ \A i \in idx..Len(barr)-1 : s2[i-idx+1] = barr[i+1]
        BY <3>9, <3>14, <3>12
      <3>16. /\ s1 \o s2 \in Seq([key: KeyDomain, val: ValDomain])
             /\ Len(s1 \o s2) = Len(s1) + Len(s2)
             /\ \A i \in 1 .. Len(s1) + Len(s2) : /\ i <= Len(s1) => (s1 \o s2)[i] = s1[i] 
                                                  /\ i > Len(s1)  => (s1 \o s2)[i] = s2[i - Len(s1)]
        BY <3>13, <3>14, ConcatProperties
      <3>17. /\ Len(s1) + Len(s2) = Len(barr)-1
             /\ Len(s1) = idx-1
             /\ Len(s2) = Len(barr)-idx
        BY <3>13, <3>14, <3>12, LenProperties
      <3>18. /\ s1 \o s2 \in Seq([key: KeyDomain, val: ValDomain])
             /\ Len(s1 \o s2) = Len(barr)-1
             /\ \A i \in 1 .. Len(barr)-1 : /\ i <= idx-1 => (s1 \o s2)[i] = s1[i] 
                                            /\ i > idx-1  => (s1 \o s2)[i] = s2[i - (idx-1)]
        BY <3>16, <3>17, Zenon
      <3>19. /\ s1 \o s2 \in Seq([key: KeyDomain, val: ValDomain])
             /\ Len(s1 \o s2) = Len(barr)-1
             /\ \A i \in 1 .. Len(barr)-1 : /\ i <= idx-1 => (s1 \o s2)[i] = s1[i] 
                                            /\ i > idx-1  => (s1 \o s2)[i] = s2[i-idx+1]
        BY <3>18, <3>12
      <3>20. \A i \in 1..Len(barr)-1 : i <= idx-1 => (s1 \o s2)[i] = barr[i]
        BY <3>13, <3>19, <3>12
      <3>21. \A i \in 1..Len(barr)-1 : i > idx-1 => i \in idx..Len(barr)-1
        BY <3>12, LenProperties, <3>7
      <3>22. \A i \in 1..Len(barr)-1 : i > idx-1 => s2[i-idx+1] = barr[i+1]
        BY <3>15, <3>21, Zenon
      <3>23. \A i \in 1..Len(barr)-1 : i > idx-1  => (s1 \o s2)[i] = barr[i+1]
        BY <3>19, <3>22, Zenon
      <3>24. bucket_arr = s1 \o s2 /\ Len(bucket_arr) = Len(barr)-1
        BY <3>1, <3>18, Zenon
      <3>25. CASE j1 <= idx-1 /\ j2 <= idx-1
        <4>1. (j1 \in 1..Len(barr) /\ j2 \in 1..Len(barr)) => (barr[j1].key = barr[j2].key => j1 = j2)
          BY <3>6, Zenon DEF UniqInv
        <4>2. barr[j1].key = barr[j2].key => j1 = j2
          BY <4>1, <3>24
        <4>3. barr[j1] = bucket_arr[j1]
          BY <3>25, <3>20, <3>24, Zenon
        <4>4. barr[j2] = bucket_arr[j2]
          BY <3>25, <3>20, <3>24, Zenon
        <4> QED
          BY <4>2, <4>3, <4>4
      <3>26. CASE j1 <= idx-1 /\ j2 > idx-1
        <4> SUFFICES FALSE
          OBVIOUS
        <4>1. barr[j1] = bucket_arr[j1]
          BY <3>26, <3>20, <3>24, Zenon
        <4>2. barr[j2+1] = bucket_arr[j2]
          BY <3>26, <3>23, <3>24, Zenon
        <4>3. (j1 \in 1..Len(barr) /\ j2+1 \in 1..Len(barr)) => (barr[j1].key = barr[j2+1].key => j1 = j2+1)
          BY <3>6, Zenon DEF UniqInv
        <4>4. barr[j1].key = barr[j2+1].key => j1 = j2+1
          BY <4>3, <3>24
        <4>5. j1 = j2+1
          BY <4>1, <4>2, <4>4
        <4> QED
          BY <3>26, <3>12, <4>5
      <3>27. CASE j1 > idx-1 /\ j2 <= idx-1
        <4> SUFFICES FALSE
          OBVIOUS
        <4>1. barr[j1+1] = bucket_arr[j1]
          BY <3>27, <3>23, <3>24, Zenon
        <4>2. barr[j2] = bucket_arr[j2]
          BY <3>27, <3>20, <3>24, Zenon
        <4>3. (j1+1 \in 1..Len(barr) /\ j2 \in 1..Len(barr)) => (barr[j1+1].key = barr[j2].key => j1+1 = j2)
          BY <3>6, Zenon DEF UniqInv
        <4>4. barr[j1+1].key = barr[j2].key => j1+1 = j2
          BY <4>3, <3>24
        <4>5. j1+1 = j2
          BY <4>1, <4>2, <4>4
        <4> QED
          BY <3>27, <3>12, <4>5
      <3>28. CASE j1 > idx-1 /\ j2 > idx-1
        <4>1. (j1+1 \in 1..Len(barr) /\ j2+1 \in 1..Len(barr)) => (barr[j1+1].key = barr[j2+1].key => j1+1 = j2+1)
          BY <3>6, Zenon DEF UniqInv
        <4>2. barr[j1+1].key = barr[j2+1].key => j1+1 = j2+1
          BY <4>1, <3>24
        <4>3. barr[j1+1] = bucket_arr[j1]
          BY <3>28, <3>23, <3>24, Zenon
        <4>4. barr[j2+1] = bucket_arr[j2]
          BY <3>28, <3>23, <3>24, Zenon
        <4> QED
          BY <4>2, <4>3, <4>4
      <3> QED
        BY <3>12, <3>25, <3>26, <3>27, <3>28
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
      <3>1. bucket[p] # NULL
        BY Zenon DEF BktInv, KeyInBktAtAddr
      <3>2. PICK idx \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][idx].key = arg[p].key
        BY Zenon DEF BktInv, KeyInBktAtAddr
      <3> HIDE DEF R3
      <3>3. idx = CHOOSE index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key = arg[p].key
        BY <3>1, <3>2
      <3>4. PICK addr \in Addrs : /\ addr \notin AllocAddrs
                                  /\ AllocAddrs' = AllocAddrs \cup {addr}
                                  /\ newbkt' = [newbkt EXCEPT ![p] = addr]
                                  /\ MemLocs' = [MemLocs EXCEPT ![addr] = SubSeq(MemLocs[bucket[p]], 1, idx-1) 
                                                                          \o SubSeq(MemLocs[bucket[p]], idx+1, Len(MemLocs[bucket[p]]))]
        BY Zenon, <3>2, <3>3 DEF R3, IdxInBktAtAddr
      <3> USE <3>1, <3>2, <3>3, <3>4
      <3>5. /\ pc[p] = "R3"
            /\ pc' = [pc EXCEPT ![p] = "R4"]
            /\ UNCHANGED <<A, bucket, r, arg, ret>>
        BY Zenon DEF R3
      <3> USE <3>5
      <3>6. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
        BY ZenonT(30)
      <3>7. ASSUME NEW k \in KeyDomain, q # p, pc[q] \in {"I4", "U4", "R4"}
            PROVE  /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
                   /\ KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
                   /\ KeyInBktAtAddr(k, bucket[q]) => (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])')
                   /\ KeyInBktAtAddr(k, newbkt[q]) => (ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])')
        <4> USE <3>7
        <4>1. bucket[q] = bucket'[q] /\ newbkt'[q] = newbkt[q] /\ newbkt[q] \in AllocAddrs
          BY NULLDef, Zenon DEF AddrsInv
        <4>2. MemLocs[newbkt[q]] = MemLocs'[newbkt'[q]]
          BY <3>6, <4>1, Zenon
        <4>3. KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'  
          BY Zenon, <4>1, <4>2 DEF KeyInBktAtAddr
        <4>4. ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
          <5> DEFINE bkt_arr == MemLocs'[newbkt'[q]]
          <5> DEFINE id == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
          <5>1. ValOfKeyInBktAtAddr(k, newbkt[q])' = bkt_arr[id].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>2. bkt_arr = MemLocs[newbkt[q]]
            BY Zenon, <4>2
          <5>3. id = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
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
          BY <3>6, <4>1, Zenon
        <4>7. KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'  
          BY Zenon, <4>1, <4>6 DEF KeyInBktAtAddr
        <4> SUFFICES ASSUME KeyInBktAtAddr(k, bucket[q])
                      PROVE  ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
          BY <4>7, Zenon
        <4>8. ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
          <5> DEFINE bkt_arr == MemLocs'[bucket'[q]]
          <5> DEFINE id == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
          <5>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[id].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>2. bkt_arr = MemLocs[bucket[q]]
            BY Zenon, <4>6
          <5>3. id = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
            BY Zenon
          <5> QED
            BY <5>1, <5>2, <5>3, Isa DEF ValOfKeyInBktAtAddr
        <4> QED
          BY <4>8
      <3>8. CASE pc'[q] = "I4"
        <4> USE <3>8
        <4>1. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
              /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
              /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                        /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                            (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
          BY Zenon DEF NewBktInv
        <4>2. arg[q].key \in KeyDomain
          BY RemDef, Zenon DEF ArgsOf, LineIDtoOp
        <4> QED
          BY <3>7, <4>1, <4>2, ZenonT(30)
      <3>9. CASE pc'[q] = "U4"
        <4> USE <3>9
        <4>1. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
              /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
              /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                        /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                            (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
          BY Zenon DEF NewBktInv
        <4>2. arg[q].key \in KeyDomain
          BY RemDef, Zenon DEF ArgsOf, LineIDtoOp
        <4> QED
          BY <3>7, <4>1, <4>2, ZenonT(30)
      <3>10. CASE pc'[q] = "R4"
        <4> USE <3>10
        <4> SUFFICES /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                      /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                  (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
          OBVIOUS
        <4>1. CASE q = p
          <5> USE <4>1
          <5> DEFINE old == MemLocs[bucket[p]]
          <5> DEFINE s1 == SubSeq(old, 1, idx-1)
          <5> DEFINE s2 == SubSeq(old, idx+1, Len(old))
          <5> DEFINE new == MemLocs'[newbkt'[p]]
          <5>1. new = s1 \o s2
            BY Zenon
          <5>2. old \in Seq([key: KeyDomain, val: ValDomain])
            BY Zenon
          <5>3. /\ Len(old) \in Nat
                /\ \A i \in 1..Len(old) : old[i] \in [key: KeyDomain, val: ValDomain]
            BY Zenon, <5>2, ElementOfSeq, LenProperties
          <5>4. idx \in 1..Len(old)
            BY Zenon
          <5>5. \A i \in 1..idx-1 : old[i] \in [key: KeyDomain, val: ValDomain]
            <6> HIDE <3>1, <3>2, <3>3, <3>4
            <6> QED BY Z3T(30), <5>3
          <5>6. 1 \in Int /\ idx-1 \in Int
            <6> HIDE <3>1, <3>2, <3>3, <3>4 
            <6> QED BY Z3T(30)
          <5>7. /\ s1 \in Seq([key: KeyDomain, val: ValDomain])
                /\ Len(s1) = IF 1 <= idx-1 THEN (idx-1)-1+1 ELSE 0
                /\ \A i \in 1..(idx-1)-1+1 : s1[i] = old[1+i-1]
            BY <5>5, <5>6, SubSeqProperties, Isa
          <5>8. /\ s1 \in Seq([key: KeyDomain, val: ValDomain])
                /\ Len(s1) = idx-1
                /\ \A i \in 1..(idx-1) : s1[i] = old[i]
            <6> HIDE <3>1, <3>2, <3>3, <3>4, <3>10, <4>1, RemDef DEF new, old, TypeOK, Inv, RemDef
            <6> QED BY Z3T(30), <5>6, <5>7
          <5>9. \A i \in idx+1..Len(old) : old[i] \in [key: KeyDomain, val: ValDomain]
            <6> HIDE <3>1, <3>2, <3>3, <3>4
            <6> QED BY Z3T(30), <5>3
          <5>10. idx \in Nat \ {0}
            <6> HIDE <3>1, <3>2, <3>3, <3>4
            <6> QED BY Z3T(30), <5>2, LenProperties
          <5>11. /\ s2 \in Seq([key: KeyDomain, val: ValDomain])
                  /\ Len(s2) = Len(old) - idx
                  /\ \A i \in 1..Len(old)-idx : s2[i] = old[idx+i]
            <6> HIDE <3>1, <3>2, <3>3, <3>4
            <6> QED BY <5>9, <5>10, SubSeqProperties
          <5>12. /\ s2 \in Seq([key: KeyDomain, val: ValDomain])
                  /\ Len(s2) = Len(old)-idx
                  /\ \A i \in idx..Len(old)-1 : s2[i-idx+1] = old[i+1]
            <6> HIDE <3>1, <3>2, <3>3, <3>4
            <6> QED BY <5>10, <5>11
          <5>13. \A i \in idx+1..Len(old) : s2[i-idx] = old[i]
            <6> HIDE <3>1, <3>2, <3>3, <3>4
            <6> QED BY <5>10, <5>11, <5>12
          <5>14. /\ s1 \o s2 \in Seq([key: KeyDomain, val: ValDomain])
                 /\ Len(s1 \o s2) = Len(s1) + Len(s2)
                 /\ \A i \in 1 .. Len(s1) + Len(s2) : (s1 \o s2)[i] = IF i <= Len(s1) THEN s1[i] ELSE s2[i - Len(s1)]
            <6> HIDE <3>1, <3>2, <3>3, <3>4, <3>10, <4>1, RemDef DEF new, old, s1, s2, TypeOK, Inv, RemDef
            <6> QED BY <5>8, <5>12, ZenonT(30), ConcatProperties
          <5>15. /\ s1 \o s2 \in Seq([key: KeyDomain, val: ValDomain])
                 /\ Len(s1 \o s2) = Len(s1) + Len(s2)
                 /\ \A i \in 1 .. Len(s1) + Len(s2) : /\ i <= Len(s1) => (s1 \o s2)[i] = s1[i] 
                                                      /\ i > Len(s1)  => (s1 \o s2)[i] = s2[i - Len(s1)]
            <6> HIDE <3>1, <3>2, <3>3, <3>4, <3>10, <4>1, RemDef DEF s1, s2, new, old, TypeOK, Inv, RemDef
            <6> QED BY <5>10, <5>8, <5>12, <5>14, <5>3
          <5>16. /\ Len(s1) + Len(s2) = Len(old)-1
                 /\ Len(s1) = idx-1
                 /\ Len(s2) = Len(old)-idx
            <6> HIDE <3>1, <3>2, <3>3, <3>4, <3>10, <4>1, RemDef DEF s1, s2, new, old, TypeOK, Inv, RemDef
            <6> QED BY <5>10, <5>12, <5>8, LenProperties
          <5>17. /\ s1 \o s2 \in Seq([key: KeyDomain, val: ValDomain])
                 /\ Len(s1 \o s2) = Len(old)-1
                 /\ \A i \in 1 .. Len(old)-1 : /\ i <= idx-1 => (s1 \o s2)[i] = s1[i] 
                                               /\ i > idx-1  => (s1 \o s2)[i] = s2[i - (idx-1)]
            <6> HIDE <3>1, <3>2, <3>3, <3>4, <3>10, <4>1, RemDef DEF s1, s2, new, old, TypeOK, Inv, RemDef
            <6> QED BY <5>15, <5>16, Zenon
          <5>18. /\ s1 \o s2 \in Seq([key: KeyDomain, val: ValDomain])
                  /\ Len(s1 \o s2) = Len(old)-1
                  /\ \A i \in 1 .. Len(old)-1 : /\ i <= idx-1 => (s1 \o s2)[i] = s1[i] 
                                                /\ i > idx-1  => (s1 \o s2)[i] = s2[i-idx+1]
            <6> HIDE <3>1, <3>2, <3>3, <3>4, <3>10, <4>1, RemDef DEF s1, s2, new, old, TypeOK, Inv, RemDef
            <6> QED BY <5>17, <5>10      
          <5>19. \A i \in 1..Len(old)-1 : i <= idx-1 => (s1 \o s2)[i] = old[i]
            <6> HIDE <3>1, <3>2, <3>3, <3>4, <3>10, <4>1, RemDef DEF s1, s2, new, old, TypeOK, Inv, RemDef
            <6> QED BY  <5>8, <5>18, <5>10
          <5>20. \A i \in 1..Len(old)-1 : i > idx-1 => i \in idx..Len(old)-1
            <6> HIDE <3>1, <3>2, <3>3, <3>4, <3>10, <4>1, RemDef DEF s1, s2, new, old, TypeOK, Inv, RemDef
            <6> QED BY  <5>10, LenProperties, <5>2
          <5>21. \A i \in 1..Len(old)-1 : i > idx-1 => s2[i-idx+1] = old[i+1]
            <6> HIDE <3>1, <3>2, <3>3, <3>4, <3>10, <4>1, RemDef DEF s1, s2, new, old, TypeOK, Inv, RemDef
            <6> QED BY  <5>12, <5>20, Zenon
          <5>22. \A i \in 1..Len(old)-1 : i > idx-1  => (s1 \o s2)[i] = old[i+1]
            <6> HIDE <3>1, <3>2, <3>3, <3>4, <3>10, <4>1, RemDef DEF s1, s2, new, old, TypeOK, Inv, RemDef
            <6> QED BY  <5>18, <5>21, Zenon
          <5>23. \A j2 \in 1..Len(old) : old[idx].key = old[j2].key => idx = j2
            BY ZenonT(30) DEF UniqInv
          <5>24. \A j2 \in 1..Len(old) : idx # j2 => arg[p].key # old[j2].key
            BY <5>23, <3>3, Zenon
          <5>25. \A i \in 1..Len(old)-1 : arg[p].key # new[i].key
            <6> SUFFICES ASSUME NEW i \in 1..Len(old)-1
                          PROVE  arg[p].key # new[i].key
              BY Zenon
            <6>1. CASE i <= idx-1
              <7>1. new[i] = old[i]
                BY <5>19, <6>1, Zenon
              <7>2. i # idx
                <8> HIDE <3>1, <3>2, <3>3, <3>4, <3>10, <4>1, RemDef DEF s1, s2, new, old, TypeOK, Inv, RemDef
                <8> QED  BY <5>10, <6>1
              <7>3. arg[p].key # old[i].key
                <8> HIDE <3>1, <3>2, <3>3, <3>4, <3>10, <4>1, RemDef DEF s1, s2, new, old, TypeOK, Inv, RemDef
                <8> QED  BY <5>3, <5>24, <6>1, <7>2
              <7> QED
                BY <7>1, <7>3, Zenon
            <6>2. CASE i > idx-1 
              <7>1. new[i] = old[i+1]
                BY <5>22, <6>2, Zenon
              <7>2. i+1 # idx
                <8> HIDE <3>1, <3>2, <3>3, <3>4, <3>10, <4>1, RemDef DEF s1, s2, new, old, TypeOK, Inv, RemDef
                <8> QED  BY <5>10, <6>2
              <7>3. arg[p].key # old[i+1].key
                <8> HIDE <3>1, <3>2, <3>3, <3>4, <3>10, <4>1, RemDef DEF s1, s2, new, old, TypeOK, Inv, RemDef
                <8> QED  BY <5>3, <5>24, <6>2, <7>2
              <7> QED
                BY <7>1, <7>3, Zenon
            <6> QED
              <7> HIDE <3>1, <3>2, <3>3, <3>4, <3>10, <4>1, RemDef DEF s1, s2, new, old, TypeOK, Inv, RemDef
              <7> QED  BY <6>1, <6>2, <5>10
          <5>26. ~KeyInBktAtAddr(arg[p].key, newbkt[p])' 
            BY ZenonT(30), <5>25, <5>17 DEF KeyInBktAtAddr 
          <5>27. \A k \in KeyDomain : k # arg[p].key => /\ KeyInBktAtAddr(k, bucket[p])' = KeyInBktAtAddr(k, newbkt[p])'
                                                        /\ KeyInBktAtAddr(k, bucket[p])' =>
                                                            (ValOfKeyInBktAtAddr(k, bucket[p])' = ValOfKeyInBktAtAddr(k, newbkt[p])')
            <6> SUFFICES ASSUME NEW k \in KeyDomain,
                                k # arg[p].key
                         PROVE  /\ KeyInBktAtAddr(k, bucket[p])' = KeyInBktAtAddr(k, newbkt[p])'
                                /\ KeyInBktAtAddr(k, bucket[p])' =>
                                   (ValOfKeyInBktAtAddr(k, bucket[p])' = ValOfKeyInBktAtAddr(k, newbkt[p])')
              BY Zenon
            <6>1. CASE KeyInBktAtAddr(k, bucket[p])' = FALSE
              <7> USE <6>1
              <7>1. \A i \in 1..Len(old) : old[i].key # k
                BY Zenon DEF KeyInBktAtAddr
              <7> HIDE <3>1, <3>2, <3>3, <3>4, <3>10, <4>1, RemDef DEF s1, s2, new, old, TypeOK, Inv, RemDef
              <7>2. \A i \in 1..Len(old)-1 : new[i].key # k
                <8> SUFFICES ASSUME NEW i \in 1..Len(old)-1
                              PROVE  new[i].key # k
                  BY Zenon
                <8>1. CASE i > idx-1
                  <9>1. new[i] = old[i+1]
                    BY <5>22, <8>1, <5>1, Zenon
                  <9>2. old[i+1].key # k
                    BY <7>1, <5>22, <5>3, <5>19, <5>10
                  <9> QED
                    BY <9>1, <9>2
                <8>2. CASE i <= idx-1
                  <9>1. new[i] = old[i]
                    BY <5>19, <8>2, <5>1, Zenon
                  <9>2. old[i].key # k
                    BY <7>1, <5>22, <5>3, <5>19, <5>10
                  <9> QED
                    BY <9>1, <9>2
                <8> QED
                  BY <8>1, <8>2, <5>10
              <7>3. \A i \in 1..Len(new) : new[i].key # k
                BY <7>2, <5>1, <5>18
              <7> USE <3>1, <3>2, <3>3, <3>4, <3>10, <4>1, RemDef DEF s1, s2, new, old, TypeOK, Inv, RemDef
              <7>4. KeyInBktAtAddr(k, newbkt[p])' = FALSE
                BY <7>3, <3>4, Zenon DEF KeyInBktAtAddr
              <7> QED
                BY <6>1, <7>4, Zenon
            <6>2. CASE KeyInBktAtAddr(k, bucket[p])' = TRUE
              <7> USE <6>2
              <7>1. PICK i \in 1..Len(old) : old[i].key = k
                BY ZenonT(30) DEF KeyInBktAtAddr
              <7>2. i # idx
                BY <3>2, <7>1, Zenon
              <7> HIDE <3>1, <3>2, <3>3, <3>4, <3>10, <4>1, RemDef DEF s1, s2, new, old, TypeOK, Inv, RemDef
              <7>3. CASE i < idx
                <8> USE <7>3
                <8>1. i <= idx-1
                  BY <5>10, <5>17
                <8>2. i \in 1..Len(old)-1
                  BY <5>3, <5>4, <5>10, <5>17
                <8>3. new[i] = old[i]
                  BY <5>1, <5>19, <8>1, <8>2, Zenon
                <8>4. new[i].key = k
                  BY <7>1, <8>3, Zenon
                <8> USE <3>1, <3>2, <3>3, <3>4, <3>10, <4>1, RemDef DEF s1, s2, new, old, TypeOK, Inv, RemDef
                <8>5. \A j1, j2 \in 1..Len(new) : new[j1].key = new[j2].key => j1 = j2
                  BY <2>13, ZenonT(30) DEF UniqInv
                <8>6. i \in 1..Len(new)
                  BY <8>2, <5>18, Zenon
                <8>7. \A j2 \in 1..Len(new) : new[i].key = new[j2].key => i = j2
                  BY <8>5, <8>6, Zenon
                <8>8. \A j2 \in 1..Len(new) : i # j2 => new[i].key # new[j2].key
                  BY <8>7, Zenon
                <8>9. \A j2 \in 1..Len(new) : i # j2 => new[j2].key # k
                  BY <8>8, <8>4, Zenon
                <8>10. KeyInBktAtAddr(k, newbkt[p])' = TRUE
                  BY Zenon, NULLDef, <8>4, <8>6 DEF KeyInBktAtAddr
                <8>11. \A j1, j2 \in 1..Len(old) : old[j1].key = old[j2].key => j1 = j2
                  BY ZenonT(30) DEF UniqInv
                <8>12. \A j2 \in 1..Len(old) : old[i].key = old[j2].key => i = j2
                  BY <7>1, <8>11, Zenon
                <8>13. \A j2 \in 1..Len(old) : i # j2 => old[j2].key # old[i].key
                  BY <8>12, Zenon
                <8>14. \A j2 \in 1..Len(old) : i # j2 => old[j2].key # k
                  BY <7>1, <8>13, Zenon
                <8> HIDE <3>1, <3>2, <3>3, <3>4, <3>10, <4>1, RemDef DEF s1, s2, new, old, TypeOK, Inv, RemDef
                <8>15. (CHOOSE index \in 1..Len(old) : old[index].key = k) = i
                  BY <7>1, <8>14
                <8>16. (CHOOSE index \in 1..Len(new) : new[index].key = k) = i
                  BY <8>4, <8>9
                <8> USE <3>1, <3>2, <3>3, <3>4, <3>10, <4>1, RemDef DEF s1, s2, new, old, TypeOK, Inv, RemDef
                <8>17. ValOfKeyInBktAtAddr(k, bucket[p]) = old[i].val
                  BY Zenon, <8>15 DEF ValOfKeyInBktAtAddr
                <8>18. MemLocs'[bucket'[p]] = MemLocs[bucket[p]]
                  BY ZenonT(30)
                <8> HIDE <3>1, <3>2, <3>3, <3>4, <3>10, <4>1, RemDef DEF s1, s2, new, old, TypeOK, Inv, RemDef
                <8>19. ValOfKeyInBktAtAddr(k, bucket[p])' = old[i].val
                  BY Zenon, <8>17, <8>18 DEF ValOfKeyInBktAtAddr  
                <8> USE <3>1, <3>2, <3>3, <3>4, <3>10, <4>1, RemDef DEF s1, s2, new, old, TypeOK, Inv, RemDef
                <8>20. ValOfKeyInBktAtAddr(k, newbkt[p])' = new[i].val
                  BY Zenon, <8>16 DEF ValOfKeyInBktAtAddr
                <8>21. ValOfKeyInBktAtAddr(k, bucket[p])' = ValOfKeyInBktAtAddr(k, newbkt[p])'
                  BY Zenon, <8>3, <8>19, <8>20
                <8> HIDE <3>1, <3>2, <3>3, <3>4, <3>10, <4>1, RemDef DEF s1, s2, new, old, TypeOK, Inv, RemDef
                <8> QED
                  BY <8>10, <8>21, Zenon
              <7>4. CASE i > idx
                <8> USE <7>4
                <8>1. i-1 > idx-1
                  BY <5>10, <5>17
                <8>2. i-1 \in 1..Len(old)-1
                  BY <5>3, <5>4, <5>10, <5>17, <7>4
                <8>3A. new[i-1] = old[i-1+1]
                  BY <5>1, <5>22, <8>1, <8>2, Zenon
                <8>3. new[i-1] = old[i]
                  BY <8>3A
                <8>4. new[i-1].key = k
                  BY <7>1, <8>3, Zenon
                <8> USE <3>1, <3>2, <3>3, <3>4, <3>10, <4>1, RemDef DEF s1, s2, new, old, TypeOK, Inv, RemDef
                <8>5. \A j1, j2 \in 1..Len(new) : new[j1].key = new[j2].key => j1 = j2
                  BY <2>13, ZenonT(30) DEF UniqInv
                <8>6. i-1 \in 1..Len(new)
                  BY <8>2, <5>18, Zenon
                <8>7. \A j2 \in 1..Len(new) : new[i-1].key = new[j2].key => i-1 = j2
                  BY <8>5, <8>6, Zenon
                <8>8. \A j2 \in 1..Len(new) : i-1 # j2 => new[i-1].key # new[j2].key
                  BY <8>7, Zenon
                <8>9. \A j2 \in 1..Len(new) : i-1 # j2 => new[j2].key # k
                  BY <8>8, <8>4, Zenon
                <8>10. KeyInBktAtAddr(k, newbkt[p])' = TRUE
                  BY Zenon, NULLDef, <8>4, <8>6 DEF KeyInBktAtAddr
                <8>11. \A j1, j2 \in 1..Len(old) : old[j1].key = old[j2].key => j1 = j2
                  BY ZenonT(30) DEF UniqInv
                <8>12. \A j2 \in 1..Len(old) : old[i].key = old[j2].key => i = j2
                  BY <7>1, <8>11, Zenon
                <8>13. \A j2 \in 1..Len(old) : i # j2 => old[j2].key # old[i].key
                  BY <8>12, Zenon
                <8>14. \A j2 \in 1..Len(old) : i # j2 => old[j2].key # k
                  BY <7>1, <8>13, Zenon
                <8> HIDE <3>1, <3>2, <3>3, <3>4, <3>10, <4>1, RemDef DEF s1, s2, new, old, TypeOK, Inv, RemDef
                <8>15. (CHOOSE index \in 1..Len(old) : old[index].key = k) = i
                  BY <7>1, <8>14
                <8>16. (CHOOSE index \in 1..Len(new) : new[index].key = k) = i-1
                  BY <8>4, <8>9
                <8> USE <3>1, <3>2, <3>3, <3>4, <3>10, <4>1, RemDef DEF s1, s2, new, old, TypeOK, Inv, RemDef
                <8>17. ValOfKeyInBktAtAddr(k, bucket[p]) = old[i].val
                  BY Zenon, <8>15 DEF ValOfKeyInBktAtAddr
                <8>18. MemLocs'[bucket'[p]] = MemLocs[bucket[p]]
                  BY ZenonT(30)
                <8> HIDE <3>1, <3>2, <3>3, <3>4, <3>10, <4>1, RemDef DEF s1, s2, new, old, TypeOK, Inv, RemDef
                <8>19. ValOfKeyInBktAtAddr(k, bucket[p])' = old[i].val
                  BY Zenon, <8>17, <8>18 DEF ValOfKeyInBktAtAddr  
                <8> USE <3>1, <3>2, <3>3, <3>4, <3>10, <4>1, RemDef DEF s1, s2, new, old, TypeOK, Inv, RemDef
                <8>20. ValOfKeyInBktAtAddr(k, newbkt[p])' = new[i-1].val
                  BY Zenon, <8>16 DEF ValOfKeyInBktAtAddr
                <8>21. ValOfKeyInBktAtAddr(k, bucket[p])' = ValOfKeyInBktAtAddr(k, newbkt[p])'
                  BY Zenon, <8>3, <8>19, <8>20
                <8> HIDE <3>1, <3>2, <3>3, <3>4, <3>10, <4>1, RemDef DEF s1, s2, new, old, TypeOK, Inv, RemDef
                <8> QED
                  BY <8>10, <8>21, Zenon
              <7> QED
                BY <7>2, <7>3, <7>4, <5>10
            <6> QED
              BY <6>1, <6>2, Zenon DEF KeyInBktAtAddr
          <5> QED
            BY <5>26, <5>27, Zenon
        <4>2. CASE q # p
          <5> USE <4>2
          <5>1. /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])
                /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                          /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                              (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
            BY Zenon DEF NewBktInv
          <5>2. arg[q].key \in KeyDomain
            BY RemDef, Zenon DEF ArgsOf, LineIDtoOp
          <5> QED
            BY <3>7, <5>1, <5>2, ZenonT(30)
        <4> QED
          BY <4>1, <4>2, Zenon
      <3> QED
        BY <3>8, <3>9, <3>10
    <2> QED
      BY <2>9, <2>10, <2>11, <2>12, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>13, <2>14 DEF Inv
  <1>4. CASE R4(p)
    <2> USE <1>4 DEF R4, TypeOK, Inv, vars
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
\* Last modified Mon Aug 26 17:10:17 EDT 2024 by uguryavuz
\* Created Mon Jul 08 12:21:04 EDT 2024 by uyavuz
