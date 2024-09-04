--------------------------- MODULE IndInv ---------------------------
(***************************************************************************
 This module contains the inductive invariant for ParlayHash, and the 
 declarations of the lemmas and theorems that prove the inductive invariant.
 ***************************************************************************)
EXTENDS Implementation

\* Any process who is attempting a CAS in insert, upsert or remove
\* has a newbkt that is an allocated address, differing from its bucket,
\* any address currently in the table (i.e. A), and also the newbkt or bucket 
\* of any other process.
AddrsInv  == \A p \in ProcSet : pc[p] \in {"I4", "U4", "R4"}
               => /\ \A q \in ProcSet : (p # q => (newbkt[p] # bucket[q] /\ newbkt[p] # newbkt[q]))
                  /\ \A idx \in 1..N  : (A[idx] # newbkt[p])
                  /\ newbkt[p] # bucket[p]
                  /\ newbkt[p] \in AllocAddrs

\* At the third and fourth lines of insert / upsert / remove --
\* insert: the key is not in the bucket and the return value is NULL
\* upsert: if the key is in the bucket, the return value is the value
\*         corresponding to the key in the bucket and it is not NULL;
\*         otherwise the return value is NULL
\* remove: the key is in the bucket and the return value is the value
\*         corresponding to the key in the bucket and it is not NULL.
BktInv    == \A p \in ProcSet : 
                  /\ pc[p] \in {"I3", "I4"} => (~KeyInBktAtAddr(arg[p].key, bucket[p]) /\ r[p] = NULL)
                  /\ pc[p] \in {"U3", "U4"} => (IF KeyInBktAtAddr(arg[p].key, bucket[p])
                                                   THEN (r[p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p]) /\ r[p] # NULL)
                                                   ELSE  r[p] = NULL)
                  /\ pc[p] \in {"R3", "R4"} => (/\ KeyInBktAtAddr(arg[p].key, bucket[p]) 
                                                /\ r[p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p]) 
                                                /\ r[p] # NULL)

\* At the fourth (CAS) line of insert / upsert / remove --
\* insert / upsert: the key is in the new bucket and the corresponding value is the value
\*                  in the argument.
\* remove: the key is not in the new bucket.
\* for all keys other than the key in the argument, whether the key is in the new bucket
\* is the same as whether it is in the bucket, and if it is in the bucket, the values 
\* corresponding to the key in the bucket and the new bucket are the same.  
NewBktInv == \A p \in ProcSet : 
                  /\ pc[p] = "I4" => /\ KeyInBktAtAddr(arg[p].key, newbkt[p])
                                     /\ ValOfKeyInBktAtAddr(arg[p].key, newbkt[p]) = arg[p].val
                                     /\ \A k \in KeyDomain : k # arg[p].key => /\ KeyInBktAtAddr(k, bucket[p]) = KeyInBktAtAddr(k, newbkt[p])
                                                                               /\ KeyInBktAtAddr(k, bucket[p]) =>
                                                                                  (ValOfKeyInBktAtAddr(k, bucket[p]) = ValOfKeyInBktAtAddr(k, newbkt[p]))
                  /\ pc[p] = "U4" => /\ KeyInBktAtAddr(arg[p].key, newbkt[p])
                                     /\ ValOfKeyInBktAtAddr(arg[p].key, newbkt[p]) = arg[p].val
                                     /\ \A k \in KeyDomain : k # arg[p].key => /\ KeyInBktAtAddr(k, bucket[p]) = KeyInBktAtAddr(k, newbkt[p])
                                                                               /\ KeyInBktAtAddr(k, bucket[p]) =>
                                                                                  (ValOfKeyInBktAtAddr(k, bucket[p]) = ValOfKeyInBktAtAddr(k, newbkt[p]))
                  /\ pc[p] = "R4" => /\ ~KeyInBktAtAddr(arg[p].key, newbkt[p])
                                     /\ \A k \in KeyDomain : k # arg[p].key => /\ KeyInBktAtAddr(k, bucket[p]) = KeyInBktAtAddr(k, newbkt[p])
                                                                               /\ KeyInBktAtAddr(k, bucket[p]) =>
                                                                                  (ValOfKeyInBktAtAddr(k, bucket[p]) = ValOfKeyInBktAtAddr(k, newbkt[p]))

\* No key appears in a bucket more than once.
UniqInv   == \A addr \in AllocAddrs : LET bucket_arr == MemLocs[addr] IN
                                      \A j1, j2 \in 1..Len(bucket_arr) : bucket_arr[j1].key = bucket_arr[j2].key => j1 = j2

\* Type correctness
TypeOK    == /\ pc \in [ProcSet -> LineIDs]
             /\ A \in [1..N -> AllocAddrs \union {NULL}]
             /\ MemLocs \in [Addrs -> Seq([key: KeyDomain, val: ValDomain])]
             /\ AllocAddrs \in SUBSET Addrs
             /\ bucket \in [ProcSet -> AllocAddrs \union {NULL}]
             /\ newbkt \in [ProcSet -> AllocAddrs \union {NULL}]
             /\ r \in [ProcSet -> ValDomain \union {NULL}]
             /\ arg \in [ProcSet -> ArgDomain]
             /\ ret \in [ProcSet -> RetDomain]
             /\ \A p \in ProcSet : (pc[p] # RemainderID) => arg[p] \in ArgsOf(LineIDtoOp(pc[p]))

Inv == /\ AddrsInv
       /\ BktInv
       /\ NewBktInv
       /\ UniqInv
       /\ TypeOK

\* Thm: Inductive invariant holds at the initial state
\* Proof in IndInv_proofs
THEOREM InitInv == Init => Inv

\* Lemma: Inductive invariant is preserved by invocation
\* Proof in IndInv_invoc_proofs
LEMMA InvocInv == Inv /\ InvocnAction => Inv'

\* Lemma: Inductive invariant is preserved by Find
\* Proof in IndInv_find_proofs
LEMMA FindInv == Inv /\ (\E p \in ProcSet : \/ F1(p)
                                            \/ F2(p)) => Inv'
                                        
\* Lemma: Inductive invariant is preserved by Insert
\* Proof in IndInv_insert_proofs
LEMMA InsertInv == Inv /\ (\E p \in ProcSet : \/ I1(p)
                                              \/ I2(p)
                                              \/ I3(p)
                                              \/ I4(p)) => Inv'

\* Lemma: Inductive invariant is preserved by Upsert
\* Proof in IndInv_upsert_proofs
LEMMA UpsertInv == Inv /\ (\E p \in ProcSet : \/ U1(p)
                                              \/ U2(p)
                                              \/ U3(p)
                                              \/ U4(p)) => Inv'

\* Lemma: Inductive invariant is preserved by Remove
\* Proof in IndInv_remove_proofs
LEMMA RemoveInv == Inv /\ (\E p \in ProcSet : \/ R1(p)
                                              \/ R2(p)
                                              \/ R3(p)
                                              \/ R4(p)) => Inv'

\* Lemma: Inductive invariant is preserved by intermediate line actions
\* Implied by FindInv, InsertInv, UpsertInv, RemoveInv
\* Proof in IndInv_proofs
LEMMA IntermInv == Inv /\ IntermAction => Inv'

\* Lemma: Inductive invariant is preserved by return
\* Proof in IndInv_return_proofs
LEMMA ReturnInv == Inv /\ ReturnAction => Inv'

\* Lemma: Inductive invariant is preserved by stuttering
\* Proof in IndInv_proofs
LEMMA StutterInv == Inv /\ UNCHANGED vars => Inv'

\* Thm: Inductive invariant is preserved by the next-state relation
\* Implied by InvocInv, IntermedInv, ReturnInv, StutterInv
\* Proof in IndInv_proofs
THEOREM NextInv == Inv /\ [Next]_vars => Inv'

\* Thm: Inductive invariant is an invariant of Spec
\* Implied by InitInv, NextInv
\* Proof in IndInv_proofs
THEOREM SpecInv == Spec => []Inv

===============================================================================
\* Modification History
\* Last modified Mon Aug 26 12:27:18 EDT 2024 by uguryavuz
\* Created Thu Aug 08 09:37:36 EDT 2024 by uguryavuz
