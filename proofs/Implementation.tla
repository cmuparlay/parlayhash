----------------------------- MODULE Implementation -----------------------------
(***************************************************************************
 This module contains the TLA+ specification of ParlayHash.
 ***************************************************************************)
EXTENDS   UnorderedMapType, Integers, Sequences, FiniteSets
CONSTANT  RemainderID, Hash, Addrs, N
VARIABLES pc, A, MemLocs, AllocAddrs, bucket, newbkt, r, arg, ret
vars == <<pc, A, MemLocs, AllocAddrs, bucket, newbkt, r, arg, ret>>

\* Check if a key appears in a bucket at the given address
KeyInBktAtAddr(k, addr) ==
  LET
    bkt_arr == MemLocs[addr]
  IN
    /\ addr # NULL
    /\ \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = k

\* Find the index of a key in a bucket at the given address    
IdxInBktAtAddr(k, addr) ==
  LET
    bkt_arr == MemLocs[addr]
  IN
    CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                
\* Find the value associated with a key in a bucket at the given address
ValOfKeyInBktAtAddr(k, addr) ==
  LET 
    bkt_arr == MemLocs[addr]
    idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
  IN
    bkt_arr[idx].val

\* Line 1 of the Find operation
\* bucket <- A[Hash[arg.key]]
F1(p) == /\ pc[p] = "F1"
         /\ bucket' = [bucket EXCEPT ![p] = A[Hash[arg[p].key]]]
         /\ pc' = [pc EXCEPT ![p] = "F2"]
         /\ UNCHANGED <<A, MemLocs, AllocAddrs, newbkt, r, arg, ret>>

\* Line 2 of the Find operation
\* if KeyInBktAtAddr(arg.key, bucket) 
\*    then r <- ValOfKeyInBktAtAddr(arg.key, bucket)
\*    else r <- NULL
F2(p) == /\ pc[p] = "F2"
         /\ IF KeyInBktAtAddr(arg[p].key, bucket[p]) 
               THEN r' = [r EXCEPT ![p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p])]
               ELSE r' = [r EXCEPT ![p] = NULL]
         /\ pc' = [pc EXCEPT ![p] = "F3"]
         /\ UNCHANGED <<A, MemLocs, AllocAddrs, bucket, newbkt, arg, ret>>

\* Line 3 of the Find operation
\* return r
F3(p) == /\ pc[p] = "F3"
         /\ pc' = [pc EXCEPT ![p] = RemainderID]
         /\ UNCHANGED <<A, MemLocs, AllocAddrs, bucket, newbkt, r, arg>>
         /\ ret' = [ret EXCEPT ![p] = r[p]]

\* Line 1 of the Insert operation
\* bucket <- A[Hash[arg.key]]
I1(p) == /\ pc[p] = "I1"
         /\ bucket' = [bucket EXCEPT ![p] = A[Hash[arg[p].key]]]
         /\ pc' = [pc EXCEPT ![p] = "I2"]
         /\ UNCHANGED <<A, MemLocs, AllocAddrs, newbkt, r, arg, ret>>

\* Line 2 of the Insert operation
\* if KeyInBktAtAddr(arg.key, bucket)
\*    then r <- ValOfKeyInBktAtAddr(arg.key, bucket) && goto I5
\*    else r <- NULL
I2(p) == /\ pc[p] = "I2"
         /\ IF KeyInBktAtAddr(arg[p].key, bucket[p]) 
               THEN /\ r' = [r EXCEPT ![p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p])]
                    /\ pc' = [pc EXCEPT ![p] = "I5"]
               ELSE /\ r' = [r EXCEPT ![p] = NULL]
                    /\ pc' = [pc EXCEPT ![p] = "I3"]
         /\ UNCHANGED <<A, MemLocs, AllocAddrs, bucket, newbkt, arg, ret>>

\* Line 3 of the Insert operation
\* if *bucket = NULL
\*    then *newbkt <- <<arg>>
\*    else *newbkt <- *bucket \o <<arg>>
I3(p) == /\ pc[p] = "I3"
         /\ \E addr \in Addrs : 
            /\ addr \notin AllocAddrs
            /\ AllocAddrs' = AllocAddrs \cup {addr}
            /\ newbkt' = [newbkt EXCEPT ![p] = addr]
            /\ IF bucket[p] = NULL
                  THEN MemLocs' = [MemLocs EXCEPT ![addr] = <<arg[p]>>]
                  ELSE MemLocs' = [MemLocs EXCEPT ![addr] = Append(MemLocs[bucket[p]], arg[p])]
         /\ pc' = [pc EXCEPT ![p] = "I4"]
         /\ UNCHANGED <<A, bucket, r, arg, ret>>

\* Line 4 of the Insert operation
\* if not CAS(A[Hash[arg.key]], bucket, newbkt) goto I1
I4(p) == /\ pc[p] = "I4"
         /\ IF A[Hash[arg[p].key]] = bucket[p]
               THEN /\ A' = [A EXCEPT ![Hash[arg[p].key]] = newbkt[p]]
                    /\ pc' = [pc EXCEPT ![p] = "I5"]
               ELSE /\ A' = A
                    /\ pc' = [pc EXCEPT ![p] = "I1"]
         /\ UNCHANGED <<MemLocs, AllocAddrs, bucket, newbkt, r, arg, ret>>

\* Line 5 of the Insert operation
\* return r
I5(p) == /\ pc[p] = "I5"
         /\ pc' = [pc EXCEPT ![p] = RemainderID]
         /\ UNCHANGED <<A, MemLocs, AllocAddrs, bucket, newbkt, r, arg>>
         /\ ret' = [ret EXCEPT ![p] = r[p]]

\* Line 1 of the Upsert operation
\* bucket <- A[Hash[arg.key]]
U1(p) == /\ pc[p] = "U1"
         /\ bucket' = [bucket EXCEPT ![p] = A[Hash[arg[p].key]]]
         /\ pc' = [pc EXCEPT ![p] = "U2"]
         /\ UNCHANGED <<A, MemLocs, AllocAddrs, newbkt, r, arg, ret>>

\* Line 2 of the Upsert operation
\* if KeyInBktAtAddr(arg.key, bucket)
\*    then r <- ValOfKeyInBktAtAddr(arg.key, bucket)
\*    else r <- NULL
U2(p) == /\ pc[p] = "U2"
         /\ IF KeyInBktAtAddr(arg[p].key, bucket[p]) 
               THEN r' = [r EXCEPT ![p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p])]
               ELSE r' = [r EXCEPT ![p] = NULL]
         /\ pc' = [pc EXCEPT ![p] = "U3"]
         /\ UNCHANGED <<A, MemLocs, AllocAddrs, bucket, newbkt, arg, ret>>

\* Line 3 of the Upsert operation
\* if *bucket = NULL
\*    then *newbkt <- <<arg>>
\* else if r = NULL
\*    then *newbkt <- *bucket \o <<arg>>
\* else 
\*    let idx == IdxInBktAtAddr(arg.key, bucket) in
\*    *newbkt <- *bucket[1..idx-1] \o <<arg>> \o *bucket[idx+1..Len(bucket)]
U3(p) == /\ pc[p] = "U3"
         /\ \E addr \in Addrs : 
            /\ addr \notin AllocAddrs
            /\ AllocAddrs' = AllocAddrs \cup {addr}
            /\ newbkt' = [newbkt EXCEPT ![p] = addr]
            /\ IF bucket[p] = NULL
                  THEN MemLocs' = [MemLocs EXCEPT ![addr] = <<arg[p]>>]
               ELSE
                  IF r[p] = NULL
                  THEN MemLocs' = [MemLocs EXCEPT ![addr] = Append(MemLocs[bucket[p]], arg[p])]
                  ELSE LET idx == IdxInBktAtAddr(arg[p].key, bucket[p]) IN
                       MemLocs' = [MemLocs EXCEPT ![addr] = [MemLocs[bucket[p]] EXCEPT ![idx] = arg[p]]]
         /\ pc' = [pc EXCEPT ![p] = "U4"]
         /\ UNCHANGED <<A, bucket, r, arg, ret>>

\* Line 4 of the Upsert operation
\* if not CAS(A[Hash[arg.key]], bucket, newbkt) goto U1
U4(p) == /\ pc[p] = "U4"
         /\ IF A[Hash[arg[p].key]] = bucket[p]
               THEN /\ A' = [A EXCEPT ![Hash[arg[p].key]] = newbkt[p]]
                    /\ pc' = [pc EXCEPT ![p] = "U5"]
               ELSE /\ A' = A
                    /\ pc' = [pc EXCEPT ![p] = "U1"]
         /\ UNCHANGED <<MemLocs, AllocAddrs, bucket, newbkt, r, arg, ret>>

\* Line 5 of the Upsert operation
\* return r
U5(p) == /\ pc[p] = "U5"
         /\ pc' = [pc EXCEPT ![p] = RemainderID]
         /\ UNCHANGED <<A, MemLocs, AllocAddrs, bucket, newbkt, r, arg>>
         /\ ret' = [ret EXCEPT ![p] = r[p]]

\* Line 1 of the Remove operation
\* bucket <- A[Hash[arg.key]]
R1(p) == /\ pc[p] = "R1"
         /\ bucket' = [bucket EXCEPT ![p] = A[Hash[arg[p].key]]]
         /\ pc' = [pc EXCEPT ![p] = "R2"]
         /\ UNCHANGED <<A, MemLocs, AllocAddrs, newbkt, r, arg, ret>>

\* Line 2 of the Remove operation
\* if KeyInBktAtAddr(arg.key, bucket)
\*    then r <- ValOfKeyInBktAtAddr(arg.key, bucket)
\*    else r <- NULL && goto R5
R2(p) == /\ pc[p] = "R2"
         /\ IF KeyInBktAtAddr(arg[p].key, bucket[p]) 
               THEN /\ r' = [r EXCEPT ![p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p])]
                    /\ pc' = [pc EXCEPT ![p] = "R3"]
               ELSE /\ r' = [r EXCEPT ![p] = NULL]
                    /\ pc' = [pc EXCEPT ![p] = "R5"]
         /\ UNCHANGED <<A, MemLocs, AllocAddrs, bucket, newbkt, arg, ret>>

\* Line 3 of the Remove operation
\* *newbkt <- let idx == IdxInBktAtAddr(arg.key, bucket) in
\*            *bucket[1..idx-1] \o *bucket[idx+1..Len(bucket)]
R3(p) == /\ pc[p] = "R3"
         /\ \E addr \in Addrs : 
            /\ addr \notin AllocAddrs
            /\ AllocAddrs' = AllocAddrs \cup {addr}
            /\ newbkt' = [newbkt EXCEPT ![p] = addr]
            /\ LET idx == IdxInBktAtAddr(arg[p].key, bucket[p])
                   bucket_arr == MemLocs[bucket[p]] IN
               MemLocs' = [MemLocs EXCEPT ![addr] = SubSeq(bucket_arr, 1, idx-1) \o SubSeq(bucket_arr, idx+1, Len(bucket_arr))]
         /\ pc' = [pc EXCEPT ![p] = "R4"]
         /\ UNCHANGED <<A, bucket, r, arg, ret>>

\* Line 4 of the Remove operation
\* if not CAS(A[Hash[arg.key]], bucket, newbkt) goto R1
R4(p) == /\ pc[p] = "R4"
         /\ IF A[Hash[arg[p].key]] = bucket[p]
               THEN /\ A' = [A EXCEPT ![Hash[arg[p].key]] = newbkt[p]]
                    /\ pc' = [pc EXCEPT ![p] = "R5"]
               ELSE /\ A' = A
                    /\ pc' = [pc EXCEPT ![p] = "R1"]
         /\ UNCHANGED <<MemLocs, AllocAddrs, bucket, newbkt, r, arg, ret>>

\* Line 5 of the Remove operation
\* return r
R5(p) == /\ pc[p] = "R5"
         /\ pc' = [pc EXCEPT ![p] = RemainderID]
         /\ UNCHANGED <<A, MemLocs, AllocAddrs, bucket, newbkt, r, arg>>
         /\ ret' = [ret EXCEPT ![p] = r[p]]

\* Initial configuration
\* Initially, every process is at the remainder label.
Init == /\ pc = [p \in ProcSet |-> RemainderID]
        /\ A = [idx \in 1..N |-> NULL]
        /\ MemLocs = [addr \in Addrs |-> <<>>]
        /\ AllocAddrs = {}
        /\ bucket = [p \in ProcSet |-> NULL]
        /\ newbkt = [p \in ProcSet |-> NULL]
        /\ r \in [ProcSet -> ValDomain \cup {NULL}]
        /\ arg \in [ProcSet -> ArgDomain]
        /\ ret = [p \in ProcSet |-> NULL]

\* Map from operation names to the line IDs of their first lines
OpToInvocLine(op) == CASE op = "Find"   -> "F1"
                       [] op = "Insert" -> "I1"
                       [] op = "Upsert" -> "U1"
                       [] op = "Remove" -> "R1"

\* Map from line IDs to operation names
LineIDtoOp(id) == CASE id \in {"F1", "F2", "F3"} -> "Find"
                    [] id \in {"I1", "I2", "I3", "I4", "I5"} -> "Insert"
                    [] id \in {"U1", "U2", "U3", "U4", "U5"} -> "Upsert"
                    [] id \in {"R1", "R2", "R3", "R4", "R5"} -> "Remove"

\* Set of line IDs
LineIDs == {RemainderID,
            "F1", "F2", "F3",
            "I1", "I2", "I3", "I4", "I5",
            "U1", "U2", "U3", "U4", "U5",
            "R1", "R2", "R3", "R4", "R5"}

\* Set of all possible intermediate line actions for a process
IntLines(p) == {F1(p), F2(p), 
                I1(p), I2(p), I3(p), I4(p), 
                U1(p), U2(p), U3(p), U4(p),
                R1(p), R2(p), R3(p), R4(p)}

\* Set of all possible return line actions for a process
RetLines(p) == {F3(p), I5(p), U5(p), R5(p)}

\* Line invocation action: pick an operation and corresponding arguments, 
\* and go to the first line of the operation
InvokeLine(p) == /\ pc[p] = RemainderID
                 /\ \E op \in OpNames :
                       /\ pc' = [pc EXCEPT ![p] = OpToInvocLine(op)]
                       /\ \E new_arg \in ArgsOf(op) : arg' = [arg EXCEPT ![p] = new_arg]
                 /\ UNCHANGED <<A, MemLocs, AllocAddrs, bucket, newbkt, r, ret>>

\* Three types of actions: invoking an operation, intermediate line actions, and return line actions;
\* all existentially quantified over processes
InvocnAction == \E p \in ProcSet : InvokeLine(p)
IntermAction == \E p \in ProcSet : \E LineAction \in IntLines(p) : LineAction
ReturnAction == \E p \in ProcSet : \E LineAction \in RetLines(p) : LineAction

\* Next-state relation: either invoke an operation, execute an intermediate line, or execute a return line
Next == \/ InvocnAction
        \/ IntermAction
        \/ ReturnAction

\* System specification: start from the initial configuration and repeatedly take a step according to Next
Spec == Init /\ [][Next]_vars

===========================================================================================
\* Modification History
\* Last modified Tue Aug 06 09:22:31 EDT 2024 by uguryavuz
\* Created Mon Jul 08 07:31:45 EST 2024 by uyavuz
