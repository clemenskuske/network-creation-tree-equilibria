In the network creation game, each player purchases incident undirected edges
at price $\alpha>0$ per edge and pays the sum of its distances to all players.
Disconnected pairs have infinite distance. A pure Nash equilibrium admits no
unilateral strategy change that reduces the changing player's cost.

This submission proves Theorem 3 of Fabrikant, Luthra, Maneva, Papadimitriou,
and Shenker, *On a Network Creation Game* (PODC 2003, p. 350): every tree Nash
equilibrium has social cost strictly less than five times the social optimum.
The optimum ranges over all strategy profiles, and the bound holds for every
positive edge price and every number of players at least two.

The concept package separates strategy profiles, individual cost, Nash
equilibrium, social cost, the inefficiency ratio, and the theorem statement.
The proof compares the distance savings obtained when both endpoints of a
tree path buy a link to its midpoint. The resulting distance bound, together
with unique edge ownership at equilibrium and a lower bound on every
profile's social cost, gives the strict factor-five inequality.
