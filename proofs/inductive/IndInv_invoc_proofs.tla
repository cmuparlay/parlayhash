--------------------------- MODULE IndInv_invoc_proofs ----------------------
(***************************************************************************
 This module contains the proof of InvocInv from IndInv.tla
 ***************************************************************************)
EXTENDS IndInv, Assumptions, TLAPS,
        SequenceTheorems, FiniteSets

\* InvocInv == Inv /\ InvocnAction => Inv'
LEMMA InvocInv
  <1> SUFFICES ASSUME Inv,
                      NEW p \in ProcSet,
                      InvokeLine(p)
               PROVE  Inv'
    BY DEF InvocInv, InvocnAction
  <1> USE DEF InvokeLine, Inv, TypeOK, vars
  <1>1. (A       \in [1..N    -> AllocAddrs \union {NULL}])'
      OBVIOUS
  <1>2. (MemLocs \in [Addrs   -> Seq([key: KeyDomain, val: ValDomain])])'
    <2> DEFINE D == Addrs
    <2> DEFINE R == Seq([key: KeyDomain, val: ValDomain])
    <2>0. MemLocs \in [D -> R]
      BY Zenon
    <2> SUFFICES MemLocs' \in [D' -> R']
      BY Zenon
    <2>1. D = D'
      OBVIOUS
    <2>2. R = R'
      OBVIOUS
    <2>3. MemLocs = MemLocs'
      OBVIOUS
    <2> HIDE DEF D, R
    <2> QED
      BY <2>0, <2>1, <2>2, <2>3
  <1>3. (AllocAddrs \in SUBSET Addrs)'
    OBVIOUS
  <1>4. (bucket  \in [ProcSet -> AllocAddrs \union {NULL}])'
    OBVIOUS
  <1>5. (newbkt  \in [ProcSet -> AllocAddrs \union {NULL}])'
    OBVIOUS
  <1>6. (r       \in [ProcSet -> ValDomain \union {NULL}])'
    OBVIOUS
  <1>7. (ret     \in [ProcSet -> RetDomain])'
    BY DEF RetDomain
  <1> SUFFICES /\ pc' \in [ProcSet -> LineIDs]
               /\ arg' \in [ProcSet -> ArgDomain]
               /\ \A q \in ProcSet : (pc'[q] # RemainderID) => arg'[q] \in ArgsOf(LineIDtoOp(pc'[q]))
               /\ AddrsInv'
               /\ BktInv'
               /\ UniqInv'
               /\ NewBktInv'
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, Zenon
  <1> PICK op \in OpNames :
              /\ pc' = [pc EXCEPT ![p] = OpToInvocLine(op)]
              /\ \E new_arg \in ArgsOf(op) : arg' = [arg EXCEPT ![p] = new_arg]
    BY Zenon
  <1> PICK new_arg \in ArgsOf(op) : arg' = [arg EXCEPT ![p] = new_arg]
    BY Zenon
  <1>8. CASE op = "Find"
    <2> USE <1>8
    <2>1. pc' \in [ProcSet -> LineIDs]
      BY Zenon DEF LineIDs, OpToInvocLine
    <2>2. arg' \in [ProcSet -> ArgDomain]
      BY DEF ArgsOf, ArgDomain
    <2>3. \A q \in ProcSet : (pc'[q] # RemainderID) => arg'[q] \in ArgsOf(LineIDtoOp(pc'[q]))
      <3> SUFFICES ASSUME NEW q \in ProcSet,
                          pc'[q] # RemainderID
                    PROVE  arg'[q] \in ArgsOf(LineIDtoOp(pc'[q]))
        OBVIOUS
      <3>1. CASE q = p
        <4> SUFFICES new_arg \in ArgsOf(LineIDtoOp(OpToInvocLine(op)))
          BY <3>1
        <4>1. LineIDtoOp(OpToInvocLine(op)) = "Find"
          BY DEF LineIDtoOp, OpToInvocLine
        <4> QED
          BY <4>1
      <3>2. CASE q # p
        BY <3>2
      <3> QED
        BY <3>1, <3>2
    <2>4. pc'[p] = "F1"
      BY Zenon DEF OpToInvocLine
    <2>5. AddrsInv'
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
        BY <2>4 DEF AddrsInv
      <3>2. (\A idx \in 1..N  : (A[idx] # newbkt[p_1]))'
        BY <2>4 DEF AddrsInv
      <3>3. (newbkt[p_1] # bucket[p_1])'
        BY <2>4 DEF AddrsInv
      <3>4. (newbkt[p_1] \in AllocAddrs)'
        BY <2>4 DEF AddrsInv
      <3>5. QED
        BY <3>1, <3>2, <3>3, <3>4
    <2>6. BktInv'
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
      <3> USE RemDef, <2>4
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
        <4>4. MemLocs = MemLocs' /\ arg[q] = arg'[q] /\ bucket[q] = bucket'[q]
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
        <4>4. MemLocs = MemLocs' /\ arg[q] = arg'[q] /\ bucket[q] = bucket'[q]
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
    <2>7. UniqInv'
      <3> SUFFICES ASSUME NEW addr \in AllocAddrs', 
                          NEW bucket_arr, bucket_arr = MemLocs'[addr],
                          NEW j1 \in 1..Len(bucket_arr),
                          NEW j2 \in 1..Len(bucket_arr),
                          bucket_arr[j1].key = bucket_arr[j2].key
                    PROVE  j1 = j2
        BY Zenon DEF UniqInv
      <3> QED
        BY Zenon DEF UniqInv
    <2>8. NewBktInv'
      <3> SUFFICES ASSUME NEW q \in ProcSet
                    PROVE  /\ pc'[q] = "I4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                               /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg'[q].val
                                               /\ \A k \in KeyDomain : k # arg'[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                          /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                            (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                           /\ pc'[q] = "U4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                               /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg'[q].val
                                               /\ \A k \in KeyDomain : k # arg'[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                          /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                            (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                           /\ pc'[q] = "R4" => /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                               /\ \A k \in KeyDomain : k # arg'[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                          /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                            (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
        BY DEF NewBktInv
      <3>1. ASSUME NEW k \in KeyDomain
            PROVE  /\ pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
                   /\ KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
                   /\ pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                   /\ ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
        <4> USE <3>1
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
          <5>2. bkt_arr = MemLocs[bucket[q]] /\ bucket'[q] = bucket[q]
            BY Zenon
          <5>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
            BY Zenon
          <5>4. ValOfKeyInBktAtAddr(k, bucket[q]) = 
                MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][index].key = k].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>5. ValOfKeyInBktAtAddr(k, bucket[q]) = bkt_arr[idx].val
            BY <5>2, <5>3, <5>4, Zenon
          <5> QED
            BY <5>1, <5>5
        <4>4. ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
          <5> DEFINE bkt_arr == MemLocs'[newbkt'[q]]
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
          <5>1. ValOfKeyInBktAtAddr(k, newbkt[q])' = bkt_arr[idx].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>2. bkt_arr = MemLocs[newbkt[q]]
            BY Zenon
          <5>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
            BY Zenon
          <5>4. ValOfKeyInBktAtAddr(k, newbkt[q]) = 
                MemLocs[newbkt[q]][CHOOSE index \in 1..Len(MemLocs[newbkt[q]]) : MemLocs[newbkt[q]][index].key = k].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>5. ValOfKeyInBktAtAddr(k, newbkt[q]) = bkt_arr[idx].val
            BY <5>2, <5>3, <5>4, Zenon
          <5> QED
            BY <5>1, <5>5
        <4> QED
          BY <4>1, <4>2, <4>3, <4>4
      <3>2. CASE pc'[q] = "I4"
        <4> USE <3>2
        <4> arg[q] = arg'[q] /\ pc[q] = pc'[q]
          BY <2>4, Zenon
        <4> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                      /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                      /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                  (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
          OBVIOUS
        <4>1. pc'[q] = "I4" /\ arg'[q].key \in KeyDomain
          BY <2>3, Zenon, RemDef DEF ArgsOf, LineIDtoOp
        <4>2. pc[q] = "I4" /\ arg[q].key \in KeyDomain
          BY <4>1, Zenon
        <4>3. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
              /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
              /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                        /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                            (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
          BY <4>2, Zenon DEF NewBktInv
        <4> QED
          BY <3>1, <4>2, <4>3, ZenonT(90)
      <3>3. CASE pc'[q] = "U4"
        <4> USE <3>3
        <4> arg[q] = arg'[q] /\ pc[q] = pc'[q]
          BY <2>4, Zenon
        <4> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                      /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                      /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                  (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
          OBVIOUS
        <4>1. pc'[q] = "U4" /\ arg'[q].key \in KeyDomain
          BY <2>3, Zenon, RemDef DEF ArgsOf, LineIDtoOp
        <4>2. pc[q] = "U4" /\ arg[q].key \in KeyDomain
          BY <4>1, Zenon
        <4>3. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
              /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
              /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                        /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                            (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
          BY <4>2, Zenon DEF NewBktInv
        <4> QED
          BY <3>1, <4>2, <4>3, ZenonT(90)
      <3>4. CASE pc'[q] = "R4"
        <4> USE <3>4
        <4> arg[q] = arg'[q] /\ pc[q] = pc'[q]
          BY <2>4, Zenon
        <4> SUFFICES /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                      /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                  (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
          OBVIOUS
        <4>1. pc'[q] = "R4" /\ arg'[q].key \in KeyDomain
          BY <2>3, Zenon, RemDef DEF ArgsOf, LineIDtoOp
        <4>2. pc[q] = "R4" /\ arg[q].key \in KeyDomain
          BY <4>1, Zenon
        <4>3. /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])
              /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                        /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                            (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
          BY <4>2, Zenon DEF NewBktInv
        <4> QED
          BY <3>1, <4>2, <4>3, ZenonT(90)
      <3> QED
        BY <3>2, <3>3, <3>4
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8
  <1>9. CASE op = "Insert"
    <2> USE <1>9
    <2>1. pc' \in [ProcSet -> LineIDs]
      BY Zenon DEF LineIDs, OpToInvocLine
    <2>2. arg' \in [ProcSet -> ArgDomain]
      BY DEF ArgsOf, ArgDomain
    <2>3. \A q \in ProcSet : (pc'[q] # RemainderID) => arg'[q] \in ArgsOf(LineIDtoOp(pc'[q]))
      <3> SUFFICES ASSUME NEW q \in ProcSet,
                          pc'[q] # RemainderID
                    PROVE  arg'[q] \in ArgsOf(LineIDtoOp(pc'[q]))
        OBVIOUS
      <3>1. CASE q = p
        <4> SUFFICES new_arg \in ArgsOf(LineIDtoOp(OpToInvocLine(op)))
          BY <3>1
        <4>1. LineIDtoOp(OpToInvocLine(op)) = "Insert"
          BY DEF LineIDtoOp, OpToInvocLine
        <4> QED
          BY <4>1
      <3>2. CASE q # p
        BY <3>2
      <3> QED
        BY <3>1, <3>2
    <2>4. pc'[p] = "I1"
      BY Zenon DEF OpToInvocLine
    <2>5. AddrsInv'
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
        BY <2>4 DEF AddrsInv
      <3>2. (\A idx \in 1..N  : (A[idx] # newbkt[p_1]))'
        BY <2>4 DEF AddrsInv
      <3>3. (newbkt[p_1] # bucket[p_1])'
        BY <2>4 DEF AddrsInv
      <3>4. (newbkt[p_1] \in AllocAddrs)'
        BY <2>4 DEF AddrsInv
      <3>5. QED
        BY <3>1, <3>2, <3>3, <3>4
    <2>6. BktInv'
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
      <3> USE RemDef, <2>4
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
        <4>4. MemLocs = MemLocs' /\ arg[q] = arg'[q] /\ bucket[q] = bucket'[q]
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
        <4>4. MemLocs = MemLocs' /\ arg[q] = arg'[q] /\ bucket[q] = bucket'[q]
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
    <2>7. UniqInv'
      <3> SUFFICES ASSUME NEW addr \in AllocAddrs', 
                          NEW bucket_arr, bucket_arr = MemLocs'[addr],
                          NEW j1 \in 1..Len(bucket_arr),
                          NEW j2 \in 1..Len(bucket_arr),
                          bucket_arr[j1].key = bucket_arr[j2].key
                    PROVE  j1 = j2
        BY Zenon DEF UniqInv
      <3> QED
        BY Zenon DEF UniqInv
    <2>8. NewBktInv'
      <3> SUFFICES ASSUME NEW q \in ProcSet
                    PROVE  /\ pc'[q] = "I4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                               /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg'[q].val
                                               /\ \A k \in KeyDomain : k # arg'[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                          /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                            (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                           /\ pc'[q] = "U4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                               /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg'[q].val
                                               /\ \A k \in KeyDomain : k # arg'[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                          /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                            (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                           /\ pc'[q] = "R4" => /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                               /\ \A k \in KeyDomain : k # arg'[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                          /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                            (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
        BY DEF NewBktInv
      <3>1. ASSUME NEW k \in KeyDomain
            PROVE  /\ pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
                   /\ KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
                   /\ pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                   /\ ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
        <4> USE <3>1
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
          <5>2. bkt_arr = MemLocs[bucket[q]] /\ bucket'[q] = bucket[q]
            BY Zenon
          <5>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
            BY Zenon
          <5>4. ValOfKeyInBktAtAddr(k, bucket[q]) = 
                MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][index].key = k].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>5. ValOfKeyInBktAtAddr(k, bucket[q]) = bkt_arr[idx].val
            BY <5>2, <5>3, <5>4, Zenon
          <5> QED
            BY <5>1, <5>5
        <4>4. ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
          <5> DEFINE bkt_arr == MemLocs'[newbkt'[q]]
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
          <5>1. ValOfKeyInBktAtAddr(k, newbkt[q])' = bkt_arr[idx].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>2. bkt_arr = MemLocs[newbkt[q]]
            BY Zenon
          <5>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
            BY Zenon
          <5>4. ValOfKeyInBktAtAddr(k, newbkt[q]) = 
                MemLocs[newbkt[q]][CHOOSE index \in 1..Len(MemLocs[newbkt[q]]) : MemLocs[newbkt[q]][index].key = k].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>5. ValOfKeyInBktAtAddr(k, newbkt[q]) = bkt_arr[idx].val
            BY <5>2, <5>3, <5>4, Zenon
          <5> QED
            BY <5>1, <5>5
        <4> QED
          BY <4>1, <4>2, <4>3, <4>4
      <3>2. CASE pc'[q] = "I4"
        <4> USE <3>2
        <4> arg[q] = arg'[q] /\ pc[q] = pc'[q]
          BY <2>4, Zenon
        <4> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                      /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                      /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                  (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
          OBVIOUS
        <4>1. pc'[q] = "I4" /\ arg'[q].key \in KeyDomain
          BY <2>3, Zenon, RemDef DEF ArgsOf, LineIDtoOp
        <4>2. pc[q] = "I4" /\ arg[q].key \in KeyDomain
          BY <4>1, Zenon
        <4>3. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
              /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
              /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                        /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                            (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
          BY <4>2, Zenon DEF NewBktInv
        <4> QED
          BY <3>1, <4>2, <4>3, ZenonT(90)
      <3>3. CASE pc'[q] = "U4"
        <4> USE <3>3
        <4> arg[q] = arg'[q] /\ pc[q] = pc'[q]
          BY <2>4, Zenon
        <4> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                      /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                      /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                  (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
          OBVIOUS
        <4>1. pc'[q] = "U4" /\ arg'[q].key \in KeyDomain
          BY <2>3, Zenon, RemDef DEF ArgsOf, LineIDtoOp
        <4>2. pc[q] = "U4" /\ arg[q].key \in KeyDomain
          BY <4>1, Zenon
        <4>3. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
              /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
              /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                        /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                            (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
          BY <4>2, Zenon DEF NewBktInv
        <4> QED
          BY <3>1, <4>2, <4>3, ZenonT(90)
      <3>4. CASE pc'[q] = "R4"
        <4> USE <3>4
        <4> arg[q] = arg'[q] /\ pc[q] = pc'[q]
          BY <2>4, Zenon
        <4> SUFFICES /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                      /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                  (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
          OBVIOUS
        <4>1. pc'[q] = "R4" /\ arg'[q].key \in KeyDomain
          BY <2>3, Zenon, RemDef DEF ArgsOf, LineIDtoOp
        <4>2. pc[q] = "R4" /\ arg[q].key \in KeyDomain
          BY <4>1, Zenon
        <4>3. /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])
              /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                        /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                            (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
          BY <4>2, Zenon DEF NewBktInv
        <4> QED
          BY <3>1, <4>2, <4>3, ZenonT(90)
      <3> QED
        BY <3>2, <3>3, <3>4
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8
  <1>10. CASE op = "Upsert"
    <2> USE <1>10
    <2>1. pc' \in [ProcSet -> LineIDs]
      BY Zenon DEF LineIDs, OpToInvocLine
    <2>2. arg' \in [ProcSet -> ArgDomain]
      BY DEF ArgsOf, ArgDomain
    <2>3. \A q \in ProcSet : (pc'[q] # RemainderID) => arg'[q] \in ArgsOf(LineIDtoOp(pc'[q]))
      <3> SUFFICES ASSUME NEW q \in ProcSet,
                          pc'[q] # RemainderID
                    PROVE  arg'[q] \in ArgsOf(LineIDtoOp(pc'[q]))
        OBVIOUS
      <3>1. CASE q = p
        <4> SUFFICES new_arg \in ArgsOf(LineIDtoOp(OpToInvocLine(op)))
          BY <3>1
        <4>1. LineIDtoOp(OpToInvocLine(op)) = "Upsert"
          BY DEF LineIDtoOp, OpToInvocLine
        <4> QED
          BY <4>1
      <3>2. CASE q # p
        BY <3>2
      <3> QED
        BY <3>1, <3>2
    <2>4. pc'[p] = "U1"
      BY Zenon DEF OpToInvocLine
    <2>5. AddrsInv'
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
        BY <2>4 DEF AddrsInv
      <3>2. (\A idx \in 1..N  : (A[idx] # newbkt[p_1]))'
        BY <2>4 DEF AddrsInv
      <3>3. (newbkt[p_1] # bucket[p_1])'
        BY <2>4 DEF AddrsInv
      <3>4. (newbkt[p_1] \in AllocAddrs)'
        BY <2>4 DEF AddrsInv
      <3>5. QED
        BY <3>1, <3>2, <3>3, <3>4
    <2>6. BktInv'
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
      <3> USE RemDef, <2>4
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
        <4>4. MemLocs = MemLocs' /\ arg[q] = arg'[q] /\ bucket[q] = bucket'[q]
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
        <4>4. MemLocs = MemLocs' /\ arg[q] = arg'[q] /\ bucket[q] = bucket'[q]
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
    <2>7. UniqInv'
      <3> SUFFICES ASSUME NEW addr \in AllocAddrs', 
                          NEW bucket_arr, bucket_arr = MemLocs'[addr],
                          NEW j1 \in 1..Len(bucket_arr),
                          NEW j2 \in 1..Len(bucket_arr),
                          bucket_arr[j1].key = bucket_arr[j2].key
                    PROVE  j1 = j2
        BY Zenon DEF UniqInv
      <3> QED
        BY Zenon DEF UniqInv
    <2>8. NewBktInv'
      <3> SUFFICES ASSUME NEW q \in ProcSet
                    PROVE  /\ pc'[q] = "I4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                               /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg'[q].val
                                               /\ \A k \in KeyDomain : k # arg'[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                          /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                            (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                           /\ pc'[q] = "U4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                               /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg'[q].val
                                               /\ \A k \in KeyDomain : k # arg'[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                          /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                            (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                           /\ pc'[q] = "R4" => /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                               /\ \A k \in KeyDomain : k # arg'[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                          /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                            (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
        BY DEF NewBktInv
      <3>1. ASSUME NEW k \in KeyDomain
            PROVE  /\ pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
                   /\ KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
                   /\ pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                   /\ ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
        <4> USE <3>1
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
          <5>2. bkt_arr = MemLocs[bucket[q]] /\ bucket'[q] = bucket[q]
            BY Zenon
          <5>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
            BY Zenon
          <5>4. ValOfKeyInBktAtAddr(k, bucket[q]) = 
                MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][index].key = k].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>5. ValOfKeyInBktAtAddr(k, bucket[q]) = bkt_arr[idx].val
            BY <5>2, <5>3, <5>4, Zenon
          <5> QED
            BY <5>1, <5>5
        <4>4. ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
          <5> DEFINE bkt_arr == MemLocs'[newbkt'[q]]
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
          <5>1. ValOfKeyInBktAtAddr(k, newbkt[q])' = bkt_arr[idx].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>2. bkt_arr = MemLocs[newbkt[q]]
            BY Zenon
          <5>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
            BY Zenon
          <5>4. ValOfKeyInBktAtAddr(k, newbkt[q]) = 
                MemLocs[newbkt[q]][CHOOSE index \in 1..Len(MemLocs[newbkt[q]]) : MemLocs[newbkt[q]][index].key = k].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>5. ValOfKeyInBktAtAddr(k, newbkt[q]) = bkt_arr[idx].val
            BY <5>2, <5>3, <5>4, Zenon
          <5> QED
            BY <5>1, <5>5
        <4> QED
          BY <4>1, <4>2, <4>3, <4>4
      <3>2. CASE pc'[q] = "I4"
        <4> USE <3>2
        <4> arg[q] = arg'[q] /\ pc[q] = pc'[q]
          BY <2>4, Zenon
        <4> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                      /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                      /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                  (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
          OBVIOUS
        <4>1. pc'[q] = "I4" /\ arg'[q].key \in KeyDomain
          BY <2>3, Zenon, RemDef DEF ArgsOf, LineIDtoOp
        <4>2. pc[q] = "I4" /\ arg[q].key \in KeyDomain
          BY <4>1, Zenon
        <4>3. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
              /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
              /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                        /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                            (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
          BY <4>2, Zenon DEF NewBktInv
        <4> QED
          BY <3>1, <4>2, <4>3, ZenonT(90)
      <3>3. CASE pc'[q] = "U4"
        <4> USE <3>3
        <4> arg[q] = arg'[q] /\ pc[q] = pc'[q]
          BY <2>4, Zenon
        <4> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                      /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                      /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                  (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
          OBVIOUS
        <4>1. pc'[q] = "U4" /\ arg'[q].key \in KeyDomain
          BY <2>3, Zenon, RemDef DEF ArgsOf, LineIDtoOp
        <4>2. pc[q] = "U4" /\ arg[q].key \in KeyDomain
          BY <4>1, Zenon
        <4>3. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
              /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
              /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                        /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                            (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
          BY <4>2, Zenon DEF NewBktInv
        <4> QED
          BY <3>1, <4>2, <4>3, ZenonT(90)
      <3>4. CASE pc'[q] = "R4"
        <4> USE <3>4
        <4> arg[q] = arg'[q] /\ pc[q] = pc'[q]
          BY <2>4, Zenon
        <4> SUFFICES /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                      /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                  (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
          OBVIOUS
        <4>1. pc'[q] = "R4" /\ arg'[q].key \in KeyDomain
          BY <2>3, Zenon, RemDef DEF ArgsOf, LineIDtoOp
        <4>2. pc[q] = "R4" /\ arg[q].key \in KeyDomain
          BY <4>1, Zenon
        <4>3. /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])
              /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                        /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                            (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
          BY <4>2, Zenon DEF NewBktInv
        <4> QED
          BY <3>1, <4>2, <4>3, ZenonT(90)
      <3> QED
        BY <3>2, <3>3, <3>4
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8
  <1>11. CASE op = "Remove"
    <2> USE <1>11
    <2>1. pc' \in [ProcSet -> LineIDs]
      BY Zenon DEF LineIDs, OpToInvocLine
    <2>2. arg' \in [ProcSet -> ArgDomain]
      BY DEF ArgsOf, ArgDomain
    <2>3. \A q \in ProcSet : (pc'[q] # RemainderID) => arg'[q] \in ArgsOf(LineIDtoOp(pc'[q]))
      <3> SUFFICES ASSUME NEW q \in ProcSet,
                          pc'[q] # RemainderID
                    PROVE  arg'[q] \in ArgsOf(LineIDtoOp(pc'[q]))
        OBVIOUS
      <3>1. CASE q = p
        <4> SUFFICES new_arg \in ArgsOf(LineIDtoOp(OpToInvocLine(op)))
          BY <3>1
        <4>1. LineIDtoOp(OpToInvocLine(op)) = "Remove"
          BY DEF LineIDtoOp, OpToInvocLine
        <4> QED
          BY <4>1
      <3>2. CASE q # p
        BY <3>2
      <3> QED
        BY <3>1, <3>2
    <2>4. pc'[p] = "R1"
      BY Zenon DEF OpToInvocLine
    <2>5. AddrsInv'
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
        BY <2>4 DEF AddrsInv
      <3>2. (\A idx \in 1..N  : (A[idx] # newbkt[p_1]))'
        BY <2>4 DEF AddrsInv
      <3>3. (newbkt[p_1] # bucket[p_1])'
        BY <2>4 DEF AddrsInv
      <3>4. (newbkt[p_1] \in AllocAddrs)'
        BY <2>4 DEF AddrsInv
      <3>5. QED
        BY <3>1, <3>2, <3>3, <3>4
    <2>6. BktInv'
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
      <3> USE RemDef, <2>4
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
        <4>4. MemLocs = MemLocs' /\ arg[q] = arg'[q] /\ bucket[q] = bucket'[q]
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
        <4>4. MemLocs = MemLocs' /\ arg[q] = arg'[q] /\ bucket[q] = bucket'[q]
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
    <2>7. UniqInv'
      <3> SUFFICES ASSUME NEW addr \in AllocAddrs', 
                          NEW bucket_arr, bucket_arr = MemLocs'[addr],
                          NEW j1 \in 1..Len(bucket_arr),
                          NEW j2 \in 1..Len(bucket_arr),
                          bucket_arr[j1].key = bucket_arr[j2].key
                    PROVE  j1 = j2
        BY Zenon DEF UniqInv
      <3> QED
        BY Zenon DEF UniqInv
    <2>8. NewBktInv'
      <3> SUFFICES ASSUME NEW q \in ProcSet
                    PROVE  /\ pc'[q] = "I4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                               /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg'[q].val
                                               /\ \A k \in KeyDomain : k # arg'[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                          /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                            (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                           /\ pc'[q] = "U4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                               /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg'[q].val
                                               /\ \A k \in KeyDomain : k # arg'[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                          /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                            (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                           /\ pc'[q] = "R4" => /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                               /\ \A k \in KeyDomain : k # arg'[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                          /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                            (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
        BY DEF NewBktInv
      <3>1. ASSUME NEW k \in KeyDomain
            PROVE  /\ pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
                   /\ KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
                   /\ pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                   /\ ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
        <4> USE <3>1
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
          <5>2. bkt_arr = MemLocs[bucket[q]] /\ bucket'[q] = bucket[q]
            BY Zenon
          <5>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
            BY Zenon
          <5>4. ValOfKeyInBktAtAddr(k, bucket[q]) = 
                MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][index].key = k].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>5. ValOfKeyInBktAtAddr(k, bucket[q]) = bkt_arr[idx].val
            BY <5>2, <5>3, <5>4, Zenon
          <5> QED
            BY <5>1, <5>5
        <4>4. ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
          <5> DEFINE bkt_arr == MemLocs'[newbkt'[q]]
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
          <5>1. ValOfKeyInBktAtAddr(k, newbkt[q])' = bkt_arr[idx].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>2. bkt_arr = MemLocs[newbkt[q]]
            BY Zenon
          <5>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
            BY Zenon
          <5>4. ValOfKeyInBktAtAddr(k, newbkt[q]) = 
                MemLocs[newbkt[q]][CHOOSE index \in 1..Len(MemLocs[newbkt[q]]) : MemLocs[newbkt[q]][index].key = k].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>5. ValOfKeyInBktAtAddr(k, newbkt[q]) = bkt_arr[idx].val
            BY <5>2, <5>3, <5>4, Zenon
          <5> QED
            BY <5>1, <5>5
        <4> QED
          BY <4>1, <4>2, <4>3, <4>4
      <3>2. CASE pc'[q] = "I4"
        <4> USE <3>2
        <4> arg[q] = arg'[q] /\ pc[q] = pc'[q]
          BY <2>4, Zenon
        <4> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                      /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                      /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                  (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
          OBVIOUS
        <4>1. pc'[q] = "I4" /\ arg'[q].key \in KeyDomain
          BY <2>3, Zenon, RemDef DEF ArgsOf, LineIDtoOp
        <4>2. pc[q] = "I4" /\ arg[q].key \in KeyDomain
          BY <4>1, Zenon
        <4>3. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
              /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
              /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                        /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                            (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
          BY <4>2, Zenon DEF NewBktInv
        <4> QED
          BY <3>1, <4>2, <4>3, ZenonT(90)
      <3>3. CASE pc'[q] = "U4"
        <4> USE <3>3
        <4> arg[q] = arg'[q] /\ pc[q] = pc'[q]
          BY <2>4, Zenon
        <4> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                      /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                      /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                  (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
          OBVIOUS
        <4>1. pc'[q] = "U4" /\ arg'[q].key \in KeyDomain
          BY <2>3, Zenon, RemDef DEF ArgsOf, LineIDtoOp
        <4>2. pc[q] = "U4" /\ arg[q].key \in KeyDomain
          BY <4>1, Zenon
        <4>3. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
              /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
              /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                        /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                            (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
          BY <4>2, Zenon DEF NewBktInv
        <4> QED
          BY <3>1, <4>2, <4>3, ZenonT(90)
      <3>4. CASE pc'[q] = "R4"
        <4> USE <3>4
        <4> arg[q] = arg'[q] /\ pc[q] = pc'[q]
          BY <2>4, Zenon
        <4> SUFFICES /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                      /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                  (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
          OBVIOUS
        <4>1. pc'[q] = "R4" /\ arg'[q].key \in KeyDomain
          BY <2>3, Zenon, RemDef DEF ArgsOf, LineIDtoOp
        <4>2. pc[q] = "R4" /\ arg[q].key \in KeyDomain
          BY <4>1, Zenon
        <4>3. /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])
              /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                        /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                            (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
          BY <4>2, Zenon DEF NewBktInv
        <4> QED
          BY <3>1, <4>2, <4>3, ZenonT(90)
      <3> QED
        BY <3>2, <3>3, <3>4
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8
  <1> QED
    BY <1>8, <1>9, <1>10, <1>11 DEF OpNames

======================================================================================
\* Modification History
\* Last modified Mon Aug 26 17:27:38 EDT 2024 by uguryavuz
\* Created Mon Jul 08 12:21:04 EDT 2024 by uyavuz
