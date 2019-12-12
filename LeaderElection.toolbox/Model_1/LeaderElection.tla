--------------------------- MODULE LeaderElection ---------------------------

EXTENDS Integers

vars == <<>>

Init == TRUE

Next == TRUE

Spec == /\ Init
        /\ [][Next]_vars

=============================================================================
