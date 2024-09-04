---------------------------- MODULE Augmentation ----------------------------
EXTENDS Integers, Sequences, TLAPS
CONSTANTS BOT, ConfigDomain, Delta(_, _, _), ProcSet

(* Update P by invoking idle process p, with given op and arg *)
Invoke(P, p, op, arg) == 
  {c \in ConfigDomain : \E c_prev \in P : 
      /\ c_prev.op[p] = BOT
      /\ c_prev.arg[p] = BOT
      /\ c_prev.res[p] = BOT
      /\ c.op  = [c_prev.op EXCEPT ![p] = op]
      /\ c.arg = [c_prev.arg EXCEPT ![p] = arg]
      /\ c.res = [c_prev.res EXCEPT ![p] = BOT]
      /\ c.state = c_prev.state}
      
(* Evolve P by allowing any sequence processes to linearize,
   as specified in Delta *)
Evolve(P) ==
  {c \in ConfigDomain : \E c_prev \in P : 
    \E n \in Nat : \E alpha \in Seq(ProcSet) : \E beta \in Seq(ConfigDomain) :
      /\ Len(alpha) = n
      /\ Len(beta) = n+1
      /\ beta[1] = c_prev
      /\ \A i \in 1..n : Delta(beta[i], alpha[i], beta[i+1])
      /\ beta[n+1] = c}
      
(* Filter P, given process p and its intended return value *)
Filter(P, p, ret) ==
  {c \in ConfigDomain : \E c_prev \in P :
      /\ c_prev.res[p] = ret
      /\ c.op = [c_prev.op EXCEPT ![p] = BOT]
      /\ c.arg = [c_prev.arg EXCEPT ![p] = BOT]
      /\ c.res = [c_prev.res EXCEPT ![p] = BOT]
      /\ c.state = c_prev.state}
      
\* Simple useful theorem: c \in P => c \in Evolve(P)
THEOREM EmptySeqEvolve == \A P : \A c \in ConfigDomain : c \in P => c \in Evolve(P)
  <1> SUFFICES ASSUME NEW P,
                      NEW c \in ConfigDomain,
                      c \in P
               PROVE  c \in Evolve(P)
      OBVIOUS
  <1> DEFINE n == 0
  <1> DEFINE alpha == <<>>
  <1> DEFINE beta == <<c>>
  <1>1. alpha \in Seq(ProcSet)
    OBVIOUS
  <1>2. beta \in Seq(ConfigDomain)
    OBVIOUS
  <1> SUFFICES /\ Len(alpha) = n
               /\ Len(beta) = n+1
               /\ beta[1] = c
               /\ \A i \in 1..n : Delta(beta[i], alpha[i], beta[i+1])
               /\ beta[n+1] = c
    BY Zenon, <1>1, <1>2 DEF Evolve
  <1> QED
    OBVIOUS 
    
THEOREM SingleDeltaEvolve == \A P : \A c, d \in ConfigDomain : 
    (c \in P /\ (\E p \in ProcSet : Delta(c, p, d))) => d \in Evolve(P)
  <1> SUFFICES ASSUME NEW P,
                      NEW c \in ConfigDomain,
                      NEW d \in ConfigDomain,
                      NEW p \in ProcSet,
                      c \in P,
                      Delta(c, p, d)
               PROVE  d \in Evolve(P)
    OBVIOUS
  <1> SUFFICES \E n \in Nat : \E alpha \in Seq(ProcSet) : \E beta \in Seq(ConfigDomain) :
        /\ Len(alpha) = n
        /\ Len(beta) = n+1
        /\ beta[1] = c
        /\ \A i \in 1..n : Delta(beta[i], alpha[i], beta[i+1])
        /\ beta[n+1] = d
    BY DEF Evolve
  <1> DEFINE n == 1
  <1> DEFINE alpha == <<p>>
  <1> DEFINE beta == <<c, d>>
  <1>1. alpha \in Seq(ProcSet)
    OBVIOUS
  <1>2. beta \in Seq(ConfigDomain)
    OBVIOUS
  <1>3. Len(beta) = n+1
    OBVIOUS
  <1>4. beta[n+1] = d
    OBVIOUS
  <1> SUFFICES \A i \in 1..n : Delta(beta[i], alpha[i], beta[i+1])
    BY Zenon, <1>1, <1>2, <1>3, <1>4
  <1> QED
    OBVIOUS
    
=============================================================================
\* Modification History
\* Last modified Tue Aug 06 11:27:13 EDT 2024 by uguryavuz
\* Created Fri Jan 05 20:36:49 EST 2024 by uguryavuz