import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card

/-!
---
title: Network creation game
type: definition
---
There are $n$ players, indexed by $\{0,\ldots,n-1\}$. A strategy of player
$i$ is a set $s_i$ of other players: player $i$ purchases an edge to each member
of $s_i$. A strategy profile specifies one strategy for every player.

The resulting network $G[s]$ is undirected. Distinct players $i$ and $j$ are
adjacent when $j\in s_i$ or $i\in s_j$. Either endpoint may purchase an edge,
and both endpoints may purchase the same edge.

# Formalization notes

Strategies are subsets of `Fin n`, with self-purchases excluded by their type.
Every such subset is finite. Edge ownership remains part of the profile even
though the resulting graph is a simple graph.
-/

namespace Lax899194.NetworkCreationGame

/-- The other players to which player `i` purchases edges. -/
def Strategy (n : ℕ) (i : Fin n) := { S : Set (Fin n) // i ∉ S }

/-- A choice of strategy for every player. -/
abbrev Profile (n : ℕ) := (i : Fin n) → Strategy n i

/-- The undirected network formed by all purchased edges. -/
def graph {n : ℕ} (s : Profile n) : SimpleGraph (Fin n) where
  Adj i j := j ∈ (s i).val ∨ i ∈ (s j).val
  symm := fun _ _ h => h.elim Or.inr Or.inl
  loopless := fun i h => h.elim (s i).property (s i).property

end Lax899194.NetworkCreationGame
