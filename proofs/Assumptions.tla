---------------------------- MODULE Assumptions ----------------------------
EXTENDS Implementation

ASSUME HashDef == Hash \in [KeyDomain -> 1..N]
ASSUME NDef    == N \in Nat \ {0}
ASSUME NULLDef == /\ NULL \notin Addrs
                  /\ NULL \notin ValDomain
ASSUME RemDef  == RemainderID = "Remainder"
=============================================================================
\* Modification History
\* Last modified Tue Aug 06 11:27:13 EDT 2024 by uguryavuz
\* Created Fri Jan 05 20:36:49 EST 2024 by uguryavuz