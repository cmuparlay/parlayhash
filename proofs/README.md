# ParlayHash - proof of strong linearizability via meta-configuration tracking

This directory contains the TLA+ implementation of ParlayHash, 
and a TLAPS proof of its strong linearizability, using the meta-configuration tracking approach
[Jayanti et al. 2024](https://dl.acm.org/doi/abs/10.1145/3632924). 
There are four components of this effort:
- The definition of the domain of meta-configurations and the transition relation between
  meta-configurations of the *unordered map type* which ParlayHash implements.
  This is in the file `UnorderedMapType.tla`.
- The specification of the ParlayHash algorithm itself, in the file `Implementation.tla`.
- The definition of a set of invariants that constitute an inductive invariant, 
  that are later used to prove the strong linearizability of ParlayHash; and its proof.
  The definitions of invariants and declarations of theorems are in `IndInv.tla`.
  The proof is split into 7 files, all starting with `IndInv_`.
  <!-- The theorem stating that the inductive invariant is an invariant of the specificiation is `SpecInv`.  -->
  <!-- The proof is split into 7 files, each containing a part of the proof. 
    - `IndInv_find_proofs.tla`: Ind. inv. preserved by the intermediate steps of the find operation.
    - `IndInv_insert_proofs.tla`: Ind. inv. preserved by the intermediate steps of the insert operation.
    - `IndInv_upsert_proofs.tla`: Ind. inv. preserved by the intermediate steps of the upsert operation.
    - `IndInv_remove_proofs.tla`: Ind. inv. preserved by the intermediate steps of the remove operation.
    - `IndInv_invoc_proofs.tla`: Ind. inv. preserved by the invocation of operations.
    - `IndInv_return_proofs.tla`: Ind. inv. preserved by the return line of operations.
    - `IndInv_proofs.tla`: Ind. inv. holds for the initial configuration, is preserved by a stuttering step, and 
       proof of `SpecInv`. -->
- The definition of the witnessing meta-configuration set for proof of linearizability,
  and the proof of the well-formedness, non-emptiness, and the singleton property of the set.
  Note that the former two are sufficient to prove linearizability, and the singleton property
  proves strong linearizability.
  The definitions of invariants and declarations of theorems are in `MCTracking.tla`.
  <!-- The theorem stating that the properties listed above are an invariant of the specificiation is `StrongLinearizability`. -->
  The proof is split into 7 files, all starting with `MCTracking_`.
    <!-- - `MCTracking_find_proofs.tla`: Well-formedness maintained by the intermediate steps of the find operation.
    - `MCTracking_insert_proofs.tla`: Well-formedness maintained by the intermediate steps of the insert operation.
    - `MCTracking_upsert_proofs.tla`: Well-formedness maintained by the intermediate steps of the upsert operation.
    - `MCTracking_remove_proofs.tla`: Well-formedness maintained by the intermediate steps of the remove operation.
    - `MCTracking_invoc_proofs.tla`: Well-formedness maintained by the invocation of operations.
    - `MCTracking_return_proofs.tla`: Well-formedness maintained by the return line of operations.
    - `MCTracking_proofs.tla`: Proof that the witness matches the initial configuration, is non-empty and a singleton, 
      proofs of miscellaneous lemmas, and proof of `StrongLinearizability`. -->

## Important definitions and theorems
Here is a list of useful definitions and theorems, and where they are defined and proven:
- Pertaining to the inductive invariant - all defined in `IndInv.tla`:
    - `Inv`: The inductive invariant.
    - `InitInv`: Ind. inv. holds for the initial configuration, proven in `IndInv_proofs.tla`.
    - `InvocInv`: Ind. inv. preserved by the invocation of operations, proven in `IndInv_invoc_proofs.tla`.
    - `FindInv`: Ind. inv. preserved by the intermediate steps of the find operation, proven in `IndInv_find_proofs.tla`.
    - `InsertInv`: Ind. inv. preserved by the intermediate steps of the insert operation, proven in `IndInv_insert_proofs.tla`.
    - `UpsertInv`: Ind. inv. preserved by the intermediate steps of the upsert operation, proven in `IndInv_upsert_proofs.tla`.
    - `RemoveInv`: Ind. inv. preserved by the intermediate steps of the remove operation, proven in `IndInv_remove_proofs.tla`.
    - `IntermInv`: Ind. inv. preserved by the intermediate steps of operations, implied directly by the above lemmas; proven in `IndInv_proofs.tla`.
    - `ReturnInv`: Ind. inv. preserved by the return line of operations, proven in `IndInv_return_proofs.tla`.
    - `StutterInv`: Ind. inv. preserved by a stuttering step, proven in `IndInv_proofs.tla`.
    - `SpecInv`: Ind. inv. is an invariant of the specification, implied directly by `InitInv`, `InvocInv`, `IntermInv`, `ReturnInv`, and `StutterInv`; proven in `IndInv_proofs.tla`.
- Pertaining to meta-configuration tracking - all defined in `MCTracking.tla`, 
  and all theorems regarding actions assume `Inv`, which we have proven to be an invariant of the specification:
    - `S`: The witness set.
    - `LinInit`: The witness matches the initial configuration, proven in `MCTracking_proofs.tla`.
    - `LinSNE`: The witness set is non-empty, proven in `MCTracking_proofs.tla`.
    - `LinSingleton`: The witness set is a singleton, proven in `MCTracking_proofs.tla`.
    - `LinInvocationLine`: Witness well-formedness maintained by the invocation of operations, proven in `MCTracking_invoc_proofs.tla`.
    - `LinIntermediateLine_Find`: Witness well-formedness maintained by the intermediate steps of the find operation, proven in `MCTracking_find_proofs.tla`.
    - `LinIntermediateLine_Insert`: Witness well-formedness maintained by the intermediate steps of the insert operation, proven in `MCTracking_insert_proofs.tla`.
    - `LinIntermediateLine_Upsert`: Witness well-formedness maintained by the intermediate steps of the upsert operation, proven in `MCTracking_upsert_proofs.tla`.
    - `LinIntermediateLine_Remove`: Witness well-formedness maintained by the intermediate steps of the remove operation, proven in `MCTracking_remove_proofs.tla`.
    - `LinIntermediateLine`: Witness well-formedness maintained by the intermediate steps of operations; 
    implied directly by the above lemmas, proven in `MCTracking_proofs.tla`.
    - `LinReturnLine`: Witness well-formedness maintained by the return line of operations, proven in `MCTracking_return_proofs.tla`.
    - `StrongLinearizability`: Well-formedness, and the singleton property of the witness set, are invariants of the specification; directly implied by `LinSingleton`, `LinInvocationLine`, `LinIntermediateLine`, and `LinReturnLine`; proven in `MCTracking_proofs.tla`.
