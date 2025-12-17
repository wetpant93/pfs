import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

variable {V : Type*} {u v w : V} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
variable [DecidableEq V]

#check SimpleGraph.comap

#check G.degree v

open SimpleGraph

def IsKConnected (G : SimpleGraph V) (k : ℕ) : Prop :=
  Fintype.card V > k ∧ ∀ (s : Finset V), s.card < k → (G.induce sᶜ).Connected

abbrev Is3Connected (G : SimpleGraph V) : Prop := IsKConnected G 3


def surpressEdge (v w : V) (G : SimpleGraph V) : SimpleGraph {u : V // u ≠ v} where
  Adj x y := x ≠ y ∧
      ((G.Adj x.val y.val)
      ∨ (G.Adj x.val v ∧
         G.Adj y.val v ∧
         x.val ≠ w ∧
         y.val ≠ w))

  symm x y h := by
    obtain ⟨hne, hadj⟩ := h
    refine ⟨hne.symm, ?_⟩
    rcases hadj with (h|h) <;> simp[h.symm]

  loopless _ := by simp

#check surpressEdge G

lemma t1 (e : G.Adj v w) (h₀ : G.degree v = 3) (h₁ : Is3Connected (surpressEdge v w G)) : Is3Connected G := sorry
