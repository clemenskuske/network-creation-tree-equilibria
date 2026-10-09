import Lax899194.NashEquilibrium
import Lax899194.InefficiencyRatio
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
---
title: Tree Nash equilibria have inefficiency below five
type: theorem
---
For every positive edge price $\alpha$ and every tree Nash equilibrium $T$,
$\rho(T)<5$: its social cost is strictly less than five times the social
optimum.

# Formalization notes

There are at least two players, making the cost ratio well-defined with a
positive denominator. `SimpleGraph.IsTree` means connected and acyclic.
The equilibrium is a strategy profile whose resulting undirected network is
a tree; the profile retains edge ownership and the costs of deviations.
No non-transience assumption or lower bound such as $\alpha\ge2$ is imposed.

# Reference

Theorem 3, p. 350, in Fabrikant, Luthra, Maneva, Papadimitriou, and Shenker,
[*On a Network Creation Game*](https://people.eecs.berkeley.edu/~kubitron/courses/cs294-4-F03/papers/p347-fabrikant.pdf),
PODC 2003, pp. 347-351, DOI: 10.1145/872035.872088.
-/

namespace Lax899194.TreeNashEfficiency

open Lax899194.NetworkCreationGame Lax899194.NashEquilibrium
open Lax899194.InefficiencyRatio

/-- Theorem 3: every tree Nash equilibrium has inefficiency strictly below five. -/
axiom statement (n : ℕ) (hn : 2 ≤ n) (α : ℝ≥0) (hα : 0 < α)
    (s : Profile n) (hNash : IsNashEquilibrium α s) (hTree : (graph s).IsTree) :
    inefficiencyRatio α s < 5

end Lax899194.TreeNashEfficiency
