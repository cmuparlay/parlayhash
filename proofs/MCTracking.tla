--------------------------- MODULE MCTracking ---------------------------
(***************************************************************************
 This module contains meta-configuration tracking related definitions and
 theorem / lemma declarations for ParlayHash.
 ***************************************************************************)
EXTENDS IndInv
INSTANCE Augmentation

\* Witness S for proof of linearizability by meta-configuration tracking.
S == {c \in ConfigDomain :
        /\ c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) 
                                             THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) 
                                             ELSE NULL]
        /\ \A p \in ProcSet :
           CASE pc[p] = RemainderID 
                -> (c.op[p] = BOT /\ c.arg[p] = BOT /\ c.res[p] = BOT)
             [] pc[p] = "F1"
                -> (c.op[p] = "Find" /\ c.arg[p] = arg[p] /\ c.res[p] = BOT)
             [] pc[p] = "F2" /\ KeyInBktAtAddr(arg[p].key, bucket[p])
                -> (c.op[p] = "Find" /\ c.arg[p] = arg[p] /\ c.res[p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p]))
             [] pc[p] = "F2" /\ ~KeyInBktAtAddr(arg[p].key, bucket[p])
                -> (c.op[p] = "Find" /\ c.arg[p] = arg[p] /\ c.res[p] = NULL)
             [] pc[p] = "F3"
                -> (c.op[p] = "Find" /\ c.arg[p] = arg[p] /\ c.res[p] = r[p])
             [] pc[p] \in {"I1", "I3", "I4"}
                -> (c.op[p] = "Insert" /\ c.arg[p] = arg[p] /\ c.res[p] = BOT)
             [] pc[p] = "I2" /\ KeyInBktAtAddr(arg[p].key, bucket[p])
                -> (c.op[p] = "Insert" /\ c.arg[p] = arg[p] /\ c.res[p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p]))
             [] pc[p] = "I2" /\ ~KeyInBktAtAddr(arg[p].key, bucket[p])
                -> (c.op[p] = "Insert" /\ c.arg[p] = arg[p] /\ c.res[p] = BOT)
             [] pc[p] = "I5"
                -> (c.op[p] = "Insert" /\ c.arg[p] = arg[p] /\ c.res[p] = r[p])
             [] pc[p] \in {"U1", "U2", "U3", "U4"}
                -> (c.op[p] = "Upsert" /\ c.arg[p] = arg[p] /\ c.res[p] = BOT)
             [] pc[p] = "U5"
                -> (c.op[p] = "Upsert" /\ c.arg[p] = arg[p] /\ c.res[p] = r[p])
             [] pc[p] \in {"R1", "R3", "R4"}
                -> (c.op[p] = "Remove" /\ c.arg[p] = arg[p] /\ c.res[p] = BOT)
             [] pc[p] = "R2" /\ KeyInBktAtAddr(arg[p].key, bucket[p])
                -> (c.op[p] = "Remove" /\ c.arg[p] = arg[p] /\ c.res[p] = BOT)
             [] pc[p] = "R2" /\ ~KeyInBktAtAddr(arg[p].key, bucket[p])
                -> (c.op[p] = "Remove" /\ c.arg[p] = arg[p] /\ c.res[p] = NULL)
             [] pc[p] = "R5"
                -> (c.op[p] = "Remove" /\ c.arg[p] = arg[p] /\ c.res[p] = r[p])}

\* Theorem: S = {m_0} in the initial configuration.
THEOREM LinInit == Init => (S = {[state |-> [k \in KeyDomain |-> NULL],
                                  op    |-> [p \in ProcSet   |-> BOT],
                                  arg   |-> [p \in ProcSet   |-> BOT],
                                  res   |-> [p \in ProcSet   |-> BOT]]})

\* Theorem: S # {} in any configuration satisfying TypeOK.
\* Since TypeOK is an invariant of Spec, this automatically implies 
\* that S # {} in any reachable configuration.
THEOREM LinSNE == TypeOK => S # {} 

\* Theorem: S is a singleton in any configuration satisfying TypeOK.
\* The observation above is also applicable here.
THEOREM LinSingleton == TypeOK => Cardinality(S) = 1

\* For the theorems needed to be proven in the case of invocation / return
\* actions; the names of the process executing the action is needed to 
\* specify the set S' should remain a subset of. However, these processes'
\* names are internal to InvocnAction and ReturnAction, respectively;
\* we need to make the following definitions to extract them.
\* And we will also prove their uniqueness. Note that this is trivial,
\* since for any action executed by p, for all q != p, pc[q] = pc'[q].
InvokerProc == CHOOSE p \in ProcSet : InvokeLine(p)
ReturnProc == CHOOSE p \in ProcSet : (\E LineAction \in RetLines(p) : LineAction)
LEMMA UniqueInvoker == TypeOK => (\A q \in ProcSet : InvokeLine(q) => q = InvokerProc)
LEMMA UniqueReturner == TypeOK => (\A q \in ProcSet : (\E LineAction \in RetLines(q) : LineAction) => q = ReturnProc)

\* Theorem: Following invocation actions, 
\* S' is a subset of Evolve(S_invoke) where S_invoke is S with the necessary
\* changes made to reflect the invocation action.
THEOREM LinInvocationLine ==
    Inv /\ InvocnAction => S' \in SUBSET Evolve(Invoke(S, InvokerProc, LineIDtoOp(pc'[InvokerProc]), arg'[InvokerProc]))

\* Theorem: Following return actions
\* S' is a subset of Evolve(S_filter) where S_filter is S with the necessary
\* filtering done to reflect the return action and to eliminate invalid meta-configurations.
THEOREM LinReturnLine == 
    Inv /\ ReturnAction => S' \in SUBSET Filter(Evolve(S), ReturnProc, ret'[ReturnProc])

\* Lemma: Following intermediate line actions pertaining to Find, S' is a subset of Evolve(S).
LEMMA LinIntermediateLine_Find ==
    Inv /\ (\E p \in ProcSet : \/ F1(p)
                               \/ F2(p)) => S' \in SUBSET Evolve(S)

\* Lemma: Following intermediate line actions pertaining to Insert, S' is a subset of Evolve(S).
LEMMA LinIntermediateLine_Insert ==
    Inv /\ (\E p \in ProcSet : \/ I1(p)
                               \/ I2(p)
                               \/ I3(p)
                               \/ I4(p)) => S' \in SUBSET Evolve(S)

\* Lemma: Following intermediate line actions pertaining to Upsert, S' is a subset of Evolve(S).
LEMMA LinIntermediateLine_Upsert ==
    Inv /\ (\E p \in ProcSet : \/ U1(p)
                               \/ U2(p)
                               \/ U3(p)
                               \/ U4(p)) => S' \in SUBSET Evolve(S)

\* Lemma: Following intermediate line actions pertaining to Remove, S' is a subset of Evolve(S).
LEMMA LinIntermediateLine_Remove ==
    Inv /\ (\E p \in ProcSet : \/ R1(p)
                               \/ R2(p)
                               \/ R3(p)
                               \/ R4(p)) => S' \in SUBSET Evolve(S)

\* Theorem: Following intermediate line actions, S' is a subset of Evolve(S).
\* This is implied by LIL_Find, LIL_Insert, LIL_Upsert, LIL_Remove.
THEOREM LinIntermediateLine ==
    Inv /\ IntermAction => S' \in SUBSET Evolve(S)

\* Theorem: strong linearizability by meta-configuration tracking
\* This is implied by LinInit, LinSingleton, LinInvocationLine, LinReturnLine, LinIntermediateLine.
THEOREM StrongLinearizability == 
    Spec => [][/\ IntermAction => S' \in SUBSET Evolve(S)
               /\ InvocnAction => S' \in SUBSET Evolve(Invoke(S, InvokerProc, LineIDtoOp(pc'[InvokerProc]), arg'[InvokerProc]))
               /\ ReturnAction => S' \in SUBSET Filter(Evolve(S), ReturnProc, ret'[ReturnProc])
               /\ Cardinality(S) = 1]_vars

===================================================================================