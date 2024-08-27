----------------------------- MODULE UnorderedMapType -----------------------------
(***************************************************************************
 This module contains definitions related to the unordered map type;
 specifically meta-configuration domains, and the transition relation.
 ***************************************************************************)
CONSTANTS NULL, BOT, ProcSet, KeyDomain, ValDomain

\* Set of all possible operations
OpNames     == {"Find", "Insert", "Upsert", "Remove"}

\* Domain of the op field of meta-configurations
OpDomain    == {"Find", "Insert", "Upsert", "Remove", BOT}

\* Domain of the state of the reference implementation / meta-configuration
StateDomain == [KeyDomain -> ValDomain \union {NULL}]

\* Domain of the arg field of meta-configurations
ArgDomain   == [key: KeyDomain] \union [key: KeyDomain, val: ValDomain] \union {BOT}

\* Domain of the ret variable
RetDomain   == ValDomain \union {NULL}

\* Domain of the res field of meta-configurations
ResDomain   == ValDomain \union {NULL, BOT}

\* Map from operation names to the set of arguments they can take
ArgsOf(op) == CASE op = "Find"   -> [key: KeyDomain]
                [] op = "Insert" -> [key: KeyDomain, val: ValDomain]
                [] op = "Upsert" -> [key: KeyDomain, val: ValDomain]
                [] op = "Remove" -> [key: KeyDomain]
                [] OTHER         -> {}

\* Meta-configuration domain
ConfigDomain == [state : StateDomain, 
                 op    : [ProcSet -> OpDomain], 
                 arg   : [ProcSet -> ArgDomain], 
                 res   : [ProcSet -> ResDomain]]

\* Transition relation between two meta-configurations, by the linearization
\* of the ongoing operation of process p.
\* Here, we follow the interface provided at:
\* https://github.com/cmuparlay/parlayhash/tree/main?tab=readme-ov-file#interface
Delta(c, p, d) == CASE (c.op[p] = "Find" 
                          /\ c.arg[p] \in ArgsOf("Find") /\ c.res[p] = BOT)
                       -> /\ d.state = c.state
                          /\ d.op    = c.op
                          /\ d.arg   = c.arg
                          /\ d.res   = [c.res EXCEPT ![p] = c.state[c.arg[p].key]]
                    [] (c.op[p] = "Insert" 
                          /\ c.state[c.arg[p].key] # NULL
                          /\ c.arg[p] \in ArgsOf("Insert") /\ c.res[p] = BOT)
                       -> /\ d.state = c.state
                          /\ d.op    = c.op
                          /\ d.arg   = c.arg
                          /\ d.res   = [c.res EXCEPT ![p] = c.state[c.arg[p].key]]
                    [] (c.op[p] = "Insert"
                          /\ c.state[c.arg[p].key] = NULL
                          /\ c.arg[p] \in ArgsOf("Insert") /\ c.res[p] = BOT)
                       -> /\ d.state = [c.state EXCEPT ![c.arg[p].key] = c.arg[p].val]
                          /\ d.op    = c.op
                          /\ d.arg   = c.arg
                          /\ d.res   = [c.res EXCEPT ![p] = NULL]
                    [] (c.op[p] = "Upsert"
                          /\ c.arg[p] \in ArgsOf("Upsert") /\ c.res[p] = BOT)
                       -> /\ d.state = [c.state EXCEPT ![c.arg[p].key] = c.arg[p].val]
                          /\ d.op    = c.op
                          /\ d.arg   = c.arg
                          /\ d.res   = [c.res EXCEPT ![p] = c.state[c.arg[p].key]]
                    [] (c.op[p] = "Remove"
                          /\ c.arg[p] \in ArgsOf("Remove") /\ c.res[p] = BOT)
                       -> /\ d.state = [c.state EXCEPT ![c.arg[p].key] = NULL]
                          /\ d.op    = c.op
                          /\ d.arg   = c.arg
                          /\ d.res   = [c.res EXCEPT ![p] = c.state[c.arg[p].key]]
                    [] OTHER -> FALSE

===================================================================================
\* Modification History
\* Last modified Tue Aug 06 11:27:37 EDT 2024 by uguryavuz
\* Created Mon Jul 08 08:33:49 EST 2024 by uyavuz
