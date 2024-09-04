--------------------------- MODULE IndInv_return_proofs ----------------------
(***************************************************************************
 This module contains the proof of ReturnInv from IndInv.tla
 ***************************************************************************)
EXTENDS IndInv, Assumptions, TLAPS,
        SequenceTheorems, FiniteSets

\* ReturnInv == Inv /\ ReturnAction => Inv'
LEMMA ReturnInv
  <1> SUFFICES ASSUME Inv,
                      NEW p \in ProcSet,
                      NEW LineAction \in RetLines(p),
                      LineAction
               PROVE  Inv'
    BY Zenon DEF ReturnAction
  <1>1. CASE LineAction = F3(p)
    <2> USE <1>1, RemDef DEF F3, TypeOK, Inv, vars
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
      OBVIOUS
    <2>8. (arg \in [ProcSet -> ArgDomain])'
      OBVIOUS
    <2>9. (ret \in [ProcSet -> RetDomain])'
      BY Zenon DEF RetDomain
    <2>10. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
      <3> SUFFICES pc'[p] = RemainderID
        BY Zenon
      <3> QED
        BY Zenon
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
  <1>2. CASE LineAction = I5(p)
    <2> USE <1>2, RemDef DEF I5, TypeOK, Inv, vars
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
      OBVIOUS
    <2>8. (arg \in [ProcSet -> ArgDomain])'
      OBVIOUS
    <2>9. (ret \in [ProcSet -> RetDomain])'
      BY Zenon DEF RetDomain
    <2>10. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
      <3> SUFFICES pc'[p] = RemainderID
        BY Zenon
      <3> QED
        BY Zenon
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
  <1>3. CASE LineAction = U5(p)
    <2> USE <1>3, RemDef DEF U5, TypeOK, Inv, vars
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
      OBVIOUS
    <2>8. (arg \in [ProcSet -> ArgDomain])'
      OBVIOUS
    <2>9. (ret \in [ProcSet -> RetDomain])'
      BY Zenon DEF RetDomain
    <2>10. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
      <3> SUFFICES pc'[p] = RemainderID
        BY Zenon
      <3> QED
        BY Zenon
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
  <1>4. CASE LineAction = R5(p)
    <2> USE <1>4, RemDef DEF R5, TypeOK, Inv, vars
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
      OBVIOUS
    <2>8. (arg \in [ProcSet -> ArgDomain])'
      OBVIOUS
    <2>9. (ret \in [ProcSet -> RetDomain])'
      BY Zenon DEF RetDomain
    <2>10. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
      <3> SUFFICES pc'[p] = RemainderID
        BY Zenon
      <3> QED
        BY Zenon
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
    BY Zenon, <1>1, <1>2, <1>3, <1>4 DEF RetLines

======================================================================================
\* Modification History
\* Last modified Mon Aug 26 17:47:12 EDT 2024 by uguryavuz
\* Created Mon Jul 08 12:21:04 EDT 2024 by uyavuz
