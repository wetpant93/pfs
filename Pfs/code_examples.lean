import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk

/-Listing some variables and types-/
def m : ℕ := 2  -- m is a term of the natural numbers
def t : ℝ := 2.7128  -- t is a term of the real numbers

def distance (x : ℝ) (y : ℝ) := |x - y|

lemma distance_one : 1 = distance 1 0 := by
  rw[distance] -- ⊢ 1 = |1 - 0|
  rw[sub_zero 1]-- ⊢ 1 = |1|
  rw[abs_one] -- ⊢ 1 = 1

theorem distance_eq {x y : ℝ} (h_eq : x = y) : distance x y = 0 := by
  rw[h_eq] -- ⊢ 0 = distance y y
  rw[← abs_zero] -- ⊢ |0| = distance y y
  rw[← sub_self y]  -- ⊢ |y - y| = distance y y
  exact rfl

theorem distance_eq' {x y : ℝ} (h_eq : x = y) : distance x y = 0 := by
  simp[distance, h_eq]

theorem distance_zero_eq {x y : ℝ} (h_dist : distance x y = 0) : x = y := by
  rw[distance] at h_dist
  have h_sub : x - y = 0 := by
    rw[← abs_eq_zero]
    exact h_dist

  rw[← sub_eq_zero]
  exact h_sub



open SimpleGraph

def K3 : SimpleGraph (Fin 3) where
  Adj x y := x ≠ y

def K₃ : SimpleGraph (Fin 3) := SimpleGraph.mk (Adj := fun x y => x ≠ y)

def e01 : K3.Adj 0 1 := by simp[K3]
def e12 : K3.Adj 1 2 := by simp[K3]
def e20 : K3.Adj 2 0 := by simp[K3]


def K3.cycle : K3.Walk 0 0 := Walk.cons e01 (Walk.cons e12 (Walk.cons e20 Walk.nil))

def myGraphFun.{u} {V : Type u} [Fintype V] (G : SimpleGraph V) :=
  2 * Fintype.card V

def myGraphFun'.{u} {V : Type u} {finite : Fintype V} (G : SimpleGraph V) :=
  2 * Fintype.card V

variable {V : Type*} {v : V} {S T : Set V}


#check S -> T
#check v ∈ S
#check Walk.support
