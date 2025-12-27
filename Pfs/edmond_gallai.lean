import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Tutte
import Mathlib.Combinatorics.Hall.Basic


variable {V V' : Type*}
variable {G H : SimpleGraph V}
variable {G' H' : SimpleGraph V'}
variable {S B T : Set V}
variable {S' : Set V'}
variable {C : G.ConnectedComponent}

namespace SimpleGraph

def IsClosed (G : SimpleGraph V) (S : Set V) : Prop :=
    ¬∃ x ∈ S, ∃y ∈ Sᶜ, G.Adj x y

def IsFactorCritical : Prop :=
    ∀ v : V, ∃ M : G.Subgraph, M.IsMatching ∧ M.support = {v}ᶜ


variable [Nonempty S] in
def IsFactorCriticalArea (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ v ∈ S, ∃ M : G.Subgraph, M.IsMatching ∧ M.support = S \ {v}


def IsMatchableToComps (S : Set V) : Prop :=
  ∃ (f : S → (G.induce Sᶜ).ConnectedComponent),
  Function.Injective f ∧ (∀ s : S, ∃ y ∈ (f s), G.Adj ↑s ↑y)

variable [Fintype V] in
open Classical in
open Fintype in
lemma matchable_card_le (h : G.IsMatchableToComps S) :
  card S ≤ card (G.induce Sᶜ).ConnectedComponent := by
  obtain ⟨f, finj, _⟩ := h
  exact Fintype.card_le_of_injective f finj

variable [Fintype V] in
open Classical in
noncomputable
def compNeighbors (s : S) : Finset (G.induce Sᶜ).ConnectedComponent :=
  {C : (G.induce Sᶜ).ConnectedComponent | ∃ y ∈ C.supp, G.Adj s y}

def IsMatchableToComp (s : S) (C : (G.induce Sᶜ).ConnectedComponent) : Prop :=
  ∃ y ∈ C.supp, G.Adj s y


lemma union_closed_closed (h₀ : G.IsClosed S) (h₁ : G.IsClosed T) : G.IsClosed (S ∪ T) := by
  rintro ⟨x, (hx | hx), y, hy, xy⟩
  · rw[Set.mem_compl_iff, Set.mem_union] at hy
    push_neg at hy
    exact h₀ ⟨x, hx, y, hy.1, xy⟩
  · rw[Set.mem_compl_iff, Set.mem_union] at hy
    push_neg at hy
    exact h₁ ⟨x, hx, y, hy.2, xy⟩

lemma biunion_closed_closed {α : Type*} (S : Set α) (f : α → Set V)
 (hS : ∀ s ∈ S, G.IsClosed (f s)) :
  G.IsClosed (⋃ s ∈ S, (f s)) := by
  rintro ⟨x, hx, y, hy, xy⟩
  simp at hx hy
  obtain ⟨s, hs⟩ := hx
  exact (hS s hs.1) ⟨x, hs.2, y, hy s hs.1, xy⟩

lemma iunion_closed_closed {ι : Type*} (s : ι → Set V) (hS : (i : ι) → G.IsClosed (s i))
  : G.IsClosed (⋃ (i : ι), s i) := by
  rintro ⟨x, hx , y, hy, xy⟩
  rw[Set.compl_iUnion, Set.mem_iInter] at hy
  rcases Set.mem_iUnion.1 hx with ⟨w, hw⟩
  exact (hS w) ⟨x, hw, y, hy w, xy⟩


variable [Fintype V] in
open Classical in
open Fintype in
lemma not_matchable_exists_set (h : ¬ G.IsMatchableToComps S) :
  ∃ (A : Finset S),
     A.card > Finset.card {C | ∃ s ∈ A, G.IsMatchableToComp s C} := by
     contrapose! h
     exact (all_card_le_filter_rel_iff_exists_injective _).1 h

variable [Fintype V] in
open Classical in
open Fintype in
lemma from_set_to_comp_neighbors (T : Finset S) :
  T.biUnion G.compNeighbors =
  ({C | ∃ s ∈ T, G.IsMatchableToComp s C} : Finset (G.induce Sᶜ).ConnectedComponent) := by
  ext C; simp[IsMatchableToComp, compNeighbors]


lemma exists_of_disjoint_sets_of_injective {A B : Set V} (f : A → B) (hd : Disjoint A B)
  (hf : ∀ a : A, G.Adj a (f a)) (hinj : Function.Injective f) :
  ∃ M : G.Subgraph, M.verts = A ∪ (↑(Set.range f)) ∧ M.IsMatching := by
  use {
      verts := A ∪ (↑(Set.range f))
      Adj x y := (∃ (ha: x ∈ A), f ⟨x, ha⟩ = y) ∨ (∃ (ha: y ∈ A), f ⟨y, ha⟩ = x)
      adj_sub := by
        rintro v w (⟨ha, rfl⟩ | ⟨ha, rfl⟩)
        · exact hf ⟨v, ha⟩
        · exact (hf ⟨w, ha⟩).symm
      edge_vert := by
        rintro v w (⟨ha, h⟩ | ⟨ha, rfl⟩)
        · left
          exact ha
        · right
          use f ⟨w, ha⟩
          refine ⟨?_, rfl⟩
          use ⟨w, ha⟩
  }
  simp only [Subgraph.IsMatching, Set.mem_union, true_and]
  rintro v (hv | ⟨⟨v', vb'⟩, ⟨⟨⟨w, wa⟩, hw⟩, h⟩⟩ )
  · use f ⟨v, hv⟩
    simp only [hv, exists_const, true_or,
               true_and, exists_true_left]
    rintro y (rfl | ⟨ha, h⟩)
    · rfl
    · have: v ∈ B := by
        rw[← h]
        obtain ⟨_ , hb⟩ := f ⟨y, ha⟩
        exact hb
      exfalso
      exact hd.le_bot ⟨hv, this⟩
  use w
  simp only [wa, exists_true_left, hw, h, or_true, true_and]
  rintro y (⟨va, _⟩ | ⟨hy, hy'⟩)
  · have vb: v ∈ B := by
      rw[← h]
      exact vb'
    exfalso
    exact hd.le_bot ⟨va, vb⟩
  rw[← Subtype.val_inj, h, ← hy', Subtype.val_inj] at hw
  apply hinj at hw
  rw[← Subtype.val_inj] at hw
  exact hw.symm



open Subgraph in
variable [Fintype V] in
lemma factor_area_odd (h : G.IsFactorCriticalArea S) (hn : S.Nonempty) : Odd S.ncard := by
  classical
  obtain ⟨v, vs⟩ := hn
  rcases (h v vs) with ⟨M, hM⟩
  let even := IsMatching.even_card hM.1
  rw[← IsMatching.support_eq_verts hM.1, hM.2, ← Set.ncard_eq_toFinset_card'] at even
  rw[← Set.ncard_diff_singleton_add_one vs]
  exact Even.add_one even



variable [Fintype V] in
open Classical in
open Fintype in
lemma all_odd_factor_area :
  (∀ C : G.ConnectedComponent, G.IsFactorCriticalArea C.supp) →
  card G.ConnectedComponent = G.oddComponents.ncard := by
  intro h
  rw[Fintype.card_eq_nat_card, ← Nat.card_congr (Equiv.Set.univ _)]
  congr
  symm
  rw[Set.eq_univ_iff_forall]
  exact (fun C ↦ factor_area_odd (h C) C.nonempty_supp)


abbrev ι : G.induce S ↪g G := Embedding.induce S

def comp_ι (S) (C : (G.induce S).ConnectedComponent) : G.ConnectedComponent :=
  C.map ι.toHom

theorem comp_ι_mk {v : {x // x ∈ S}} :
  comp_ι S ((G.induce S).connectedComponentMk v) = G.connectedComponentMk (G.ι v) := rfl

lemma cmpl_of_closed_closed (h : G.IsClosed S) : G.IsClosed Sᶜ := by
    rintro ⟨x, hx, y, hy, xy⟩
    have: S = Sᶜᶜ := by simp
    rw[← this] at hy
    exact h ⟨y, hy, x, hx, G.adj_symm xy⟩

lemma exists_crossing_edge {v w : V}
  {X : Set V} (h₀ : v ∈ X) (h₁ : w ∉ X) (h : G.Reachable v w) : ∃ x ∈ X, ∃ y ∈ Xᶜ, G.Adj x y := by
  rcases h with ⟨p⟩
  induction p with
   | nil =>
     contradiction
   | @cons u x _ ux _ ih =>
     by_cases h: x ∈ X
     · exact ih h h₁
     · exact ⟨u, h₀, x, h, ux⟩


lemma closed_mem_of_reachable {v w : V}
  (vs : v ∈ S) (h₀ : G.IsClosed S) (h₁ : G.Reachable v w) : w ∈ S := by
  by_contra! wns
  exact h₀ <| exists_crossing_edge vs wns h₁

lemma closed_reachable_induce {v w : V} {S : Set V}
  (vs : v ∈ S) (h₀ : G.IsClosed S) (h₁ : G.Reachable v w) :
    ∃(ws : w ∈ S),  (G.induce S).Reachable ⟨v, vs⟩ ⟨w, ws⟩ := by
  have ws := closed_mem_of_reachable vs h₀ h₁

  rcases h₁ with ⟨p⟩
  have hw: (x : V) → x ∈ p.support → x ∈ S := by
    intro x h
    induction p with
      | nil =>
        rw[Walk.support_nil, List.mem_singleton] at h
        rwa[h]
      | @cons v u w vu h ih =>
        rw[Walk.mem_support_iff] at h
        rcases h with (h | h)
        · rwa[h]
        by_cases us: u ∈ S
        · exact ih us ws h
        · let nvu := h₀ ⟨v, vs, u, us, vu⟩
          contradiction
  use ws
  use Walk.induce S p hw



lemma closed_comp_dichotomy (h : G.IsClosed S) (C : G.ConnectedComponent) :
  C.supp ⊆ S ∨ C.supp ⊆ Sᶜ := by
  by_contra! h'
  obtain ⟨v, vc, vns⟩ := Set.not_subset.1 h'.1
  obtain ⟨w, wc, wnsc⟩ := Set.not_subset.1 h'.2
  have: w ∈ S := by
    simp at wnsc
    exact wnsc

  exact h <| exists_crossing_edge this vns <| C.reachable_of_mem_supp wc vc


lemma closed_comp_ι_supp_subset_closed (h : G.IsClosed S) (C : (G.induce S).ConnectedComponent) :
  ((G.comp_ι S) C).supp ⊆ S := by
  intro x hx
  obtain ⟨⟨v, vs⟩, rfl⟩ := C.nonempty_supp
  rw[comp_ι_mk, ConnectedComponent.mem_supp_iff, ConnectedComponent.eq] at hx
  exact closed_mem_of_reachable vs h hx.symm


lemma closed_comp_ι_inj (h : G.IsClosed S) : Function.Injective (G.comp_ι S) := by
  intro C C' h'
  obtain ⟨⟨v, vs⟩, rfl⟩ := C.nonempty_supp
  obtain ⟨w, rfl⟩ := C'.nonempty_supp
  rw[comp_ι_mk, comp_ι_mk, ConnectedComponent.eq] at h'
  exact ConnectedComponent.sound (closed_reachable_induce vs h h').2

lemma comp_ι_surj (C : G.ConnectedComponent) (CS : C.supp ⊆ S) :
  ∃ C' : (G.induce S).ConnectedComponent, (G.comp_ι S) C' = C := by
  obtain ⟨v, vs⟩ := C.nonempty_supp
  use (G.induce S).connectedComponentMk ⟨v, CS vs⟩
  simpa


noncomputable
def comp_ι_inv (C : G.ConnectedComponent) (CS : C.supp ⊆ S) :
  (G.induce S).ConnectedComponent := (comp_ι_surj C CS).choose


lemma comp_ι_inv_comp_ι (C : G.ConnectedComponent) (CS : C.supp ⊆ S) :
  (G.comp_ι S) (G.comp_ι_inv C CS) = C := (comp_ι_surj C CS).choose_spec

lemma comp_ι_comp_ι_inv (C : (G.induce S).ConnectedComponent) (h : G.IsClosed S) :
  ∃(CS : (G.comp_ι S C).supp ⊆ S), (G.comp_ι_inv (G.comp_ι S C) CS) = C := by
  use closed_comp_ι_supp_subset_closed h C
  apply closed_comp_ι_inj h
  apply comp_ι_inv_comp_ι


lemma closed_comp_ι_supp (h : G.IsClosed S) (C : (G.induce S).ConnectedComponent) :
  (G.comp_ι S C).supp = G.ι '' C.supp := by
  ext x; constructor
  · intro hx
    use ⟨x, closed_comp_ι_supp_subset_closed h C <| hx⟩
    refine ⟨?_, by rfl⟩
    apply closed_comp_ι_inj h
    rwa[comp_ι_mk, ← ConnectedComponent.mem_supp_iff]
  rintro ⟨_, ⟨hy', hy⟩⟩
  rw[← hy', comp_ι_mk, hy]
  rfl



lemma closed_comp_ι_supp_card (h : G.IsClosed S) (C : (G.induce S).ConnectedComponent) :
  (G.comp_ι S C).supp.ncard = C.supp.ncard := by
  rw[closed_comp_ι_supp, Set.ncard_image_of_injective]
  · exact Subtype.coe_injective
  · assumption


variable [Fintype V] in
lemma odd_comp_eq (h : G.IsClosed S) :
  (G.induce S).oddComponents.ncard + (G.induce Sᶜ).oddComponents.ncard = G.oddComponents.ncard := by
  let hc := cmpl_of_closed_closed h
  let ImS  := (G.induce S).oddComponents.image <| G.comp_ι S
  let ImSc := (G.induce Sᶜ).oddComponents.image <| G.comp_ι Sᶜ

  let ImScard  := Set.ncard_image_of_injective (G.induce S).oddComponents <| closed_comp_ι_inj h
  let ImSccard := Set.ncard_image_of_injective (G.induce Sᶜ).oddComponents <| closed_comp_ι_inj hc

  have ImD: Disjoint ImS ImSc := by
      rw[Set.disjoint_iff]
      rintro x ⟨⟨xs, ⟨_, xim⟩⟩, ⟨xsc, ⟨_, ximsc⟩⟩⟩
      obtain ⟨⟨y,ys⟩, rfl⟩ := xs.nonempty_supp
      obtain ⟨⟨z,zs⟩, rfl⟩ := xsc.nonempty_supp
      rw[← ximsc, comp_ι_mk, comp_ι_mk, ConnectedComponent.eq] at xim
      exact h <| exists_crossing_edge ys zs xim

  have Imss: ImS ∪ ImSc ⊆ G.oddComponents := by
    rintro _ (hx | hx) <;> {
      obtain ⟨w, odd, rfl⟩ := hx
      rw[Set.mem_setOf, closed_comp_ι_supp_card]
      assumption'

    }

  have Gss: G.oddComponents ⊆ ImS ∪ ImSc := by
    intro C _
    rcases closed_comp_dichotomy h C with (h' | h')
    · left
      use comp_ι_inv C h'
      rw[comp_ι_inv_comp_ι, eq_self_iff_true, and_true,
         Set.mem_setOf, ← closed_comp_ι_supp_card, comp_ι_inv_comp_ι]
      assumption'

    · right
      use comp_ι_inv C h'
      rw[comp_ι_inv_comp_ι, eq_self_iff_true, and_true,
         Set.mem_setOf, ← closed_comp_ι_supp_card, comp_ι_inv_comp_ι]
      assumption'


  rwa[← ImScard, ← ImSccard, ← Set.ncard_union_eq, Set.Subset.antisymm Imss Gss]


lemma comp_is_closed (C : G.ConnectedComponent) : G.IsClosed C.supp := by
  rintro ⟨x, hx, y, hy, xy⟩
  apply hy
  rw[← hx]
  exact ConnectedComponent.connectedComponentMk_eq_of_adj xy.symm

lemma pullback_closed_is_closed (B : Set V) (h₁ : G.IsClosed S) :
  (G.induce B).IsClosed ((↑) ⁻¹' S) :=
  fun ⟨⟨x, _⟩, hx, ⟨y, _⟩, hy, xy⟩ ↦ h₁ ⟨x, hx, y, hy, xy⟩



lemma is_closed_induced_something {B : Set {x // x ∈ S}}
  (hc : (G.induce S).IsClosed B) (he : ¬(∃ x ∈ T \ S, ∃ y ∈ B, G.Adj x y)) :
  (G.induce T).IsClosed (Subtype.val ⁻¹' (↑B)) := by
  rintro ⟨⟨x, xt⟩, hx, ⟨y, yt⟩, hy, xy⟩
  simp at hx hy
  rcases hx with ⟨x', hx'⟩
  by_cases hy': y ∈ S
  · exact hc ⟨⟨x, x'⟩, hx', ⟨y, hy'⟩, hy hy', xy⟩
  · exact he ⟨y, ⟨yt, hy'⟩, ⟨x, x'⟩, hx', xy.symm⟩

lemma is_closed_induce_mono {B : Set {x // x ∈ S}} {T : Set V}
  (hc : (G.induce S).IsClosed B) (hs : T ⊆ S) :
  (G.induce T).IsClosed (Subtype.val ⁻¹' (↑B)) :=
  is_closed_induced_something hc (by simp [Set.diff_eq_empty.2 hs])



lemma iso_closed_is_closed (φ : G ≃g G') (h : G.IsClosed S) : G'.IsClosed (φ '' S) := by
  rintro ⟨x', hx, y', hy, x'y'⟩
  simp at hy
  rcases hx with ⟨x, ⟨xs, imx⟩⟩
  let imy := RelIso.apply_symm_apply φ y'
  by_cases h': φ.symm y' ∈ S
  · exact hy (φ.symm y') h' imy
  rw[← imx, ← imy] at x'y'
  exact h ⟨x, xs, φ.symm y', h', (Iso.map_adj_iff φ).1 x'y'⟩

lemma iso_comp_card_eq (φ : G ≃g G') :
  ∀ C : G.ConnectedComponent, C.supp.ncard = (C.map φ.toHom).supp.ncard := by
  intro C
  rw[Set.ncard_congr (fun v _ ↦ φ v)]

  · intro v vc
    obtain ⟨x, rfl⟩ := vc
    rw[ConnectedComponent.map_mk, ConnectedComponent.mem_supp_iff]
    rfl

  · exact fun _ _ _ _ h ↦ φ.injective h

  · intro v vc
    use (φ.symm) v
    simp only [RelIso.apply_symm_apply, exists_prop, and_true,
               ConnectedComponent.mem_supp_iff,
               ConnectedComponent.iso_inv_image_comp_eq_iff_eq_map]
    exact vc



lemma iso_odd_card_eq (φ : G ≃g G') : G.oddComponents.ncard = G'.oddComponents.ncard := by
  let comp_card_eq := iso_comp_card_eq φ
  rw[Set.ncard_congr (fun C _ ↦ C.map φ.toHom)]

  · intro C Codd
    rwa[Set.mem_setOf, ← comp_card_eq C]

  · intro _ _ _ _ h
    let mapped := congr_arg (ConnectedComponent.map φ.symm.toHom) h
    simp only [ConnectedComponent.map_comp, Iso.symm_toHom_comp_toHom,
               ConnectedComponent.map_id] at mapped
    exact mapped

  intro C Codd
  use C.map φ.symm.toHom
  simp only [exists_prop, ConnectedComponent.map_comp, Iso.toHom_comp_symm_toHom,
             ConnectedComponent.map_id, and_true, Set.mem_setOf,
             comp_card_eq <| C.map φ.symm.toHom]
  exact Codd

def induce_induce_iso_set_ss' (G : SimpleGraph V) (h : B ⊆ S) :
  (G.induce S).induce ((↑) ⁻¹' B) ≃g G.induce B where
  toFun := fun ⟨⟨x, _⟩, hx⟩ ↦ ⟨x, hx⟩
  invFun := fun ⟨x, hx⟩ ↦ ⟨⟨x, h hx⟩, hx⟩
  map_rel_iff' := by rfl

def induce_congr (h : B = S) : G.induce B ≃g G.induce S where
  toFun := by subst h; exact id
  invFun := by subst h; exact id
  map_rel_iff' := by
    intro a b
    subst h
    rfl

  left_inv := by intro x; subst h; rfl
  right_inv := by intro x; subst h; rfl



lemma image_induce_induce_iso_preimage
  (G : SimpleGraph V) (h : B ⊆ S) (X : Set {s // s ∈ S}) :
  (G.induce_induce_iso_set_ss' h) '' (Subtype.val ⁻¹' X) = ((Subtype.val ⁻¹' X) : (Set (↑B))) := by
  ext x; constructor
  · rintro ⟨x', ⟨hx', hx''⟩⟩
    use x'; constructor;
    · assumption
    rw[← hx'']
    dsimp[induce_induce_iso_set_ss']

  rintro ⟨x', ⟨hx', hx''⟩⟩
  rw[Set.mem_image]
  dsimp[induce_induce_iso_set_ss']
  obtain ⟨y, hy⟩ := x'
  simp at *
  rw[← hx'']
  exact ⟨hy, hx'⟩


variable [Fintype V] [Fintype V']

def induce_induce_iso (G : SimpleGraph V) (C : Set {x // x ∈ S}) :
  (G.induce S).induce C ≃g (G.induce <| (↑) '' C) where
  toFun := by
    rintro ⟨⟨s, hs⟩, hc⟩
    use s
    use ⟨s, hs⟩

  invFun := by
    rintro ⟨s, hs⟩
    have: s ∈ S := by rcases hs with ⟨⟨_, hs'⟩, ⟨_, rfl⟩⟩; exact hs'
    use ⟨s, this⟩
    have: ⟨s, this⟩ ∈ C := by
      rcases hs with ⟨x, hx, rfl⟩; exact hx
    assumption

  map_rel_iff' := by rfl

lemma odd_comp_eq_zero_induce_even_comp
  (C : G.ConnectedComponent) (h : Even C.supp.ncard) :
  (G.induce C.supp).oddComponents.ncard = 0 := by
  rw[Set.ncard_eq_zero, Set.eq_empty_iff_forall_notMem]
  rintro C'; simp
  obtain ⟨⟨x, xc⟩, rfl⟩ := C'.nonempty_supp
  rwa[← closed_comp_ι_supp_card (comp_is_closed C),
        comp_ι_mk,
        (ConnectedComponent.mem_supp_iff C (G.ι ⟨x, xc⟩)).1 xc]

omit [Fintype V] in
lemma odd_comp_eq_one_induce_odd_comp
  (C : G.ConnectedComponent) (h : Odd C.supp.ncard) :
  (G.induce C.supp).oddComponents.ncard = 1 := by
  rw[Set.ncard_eq_one]
  use comp_ι_inv C (by rfl)
  ext x; constructor
  · rintro hx
    apply closed_comp_ι_inj (comp_is_closed C)
    obtain ⟨⟨_, x'⟩, rfl⟩ := x.nonempty_supp
    rwa[comp_ι_inv_comp_ι, comp_ι_mk, ← ConnectedComponent.mem_supp_iff]

  · intro rfl
    rwa[Set.mem_setOf, ← closed_comp_ι_supp_card (comp_is_closed C), comp_ι_inv_comp_ι]



noncomputable
def d (G : SimpleGraph V) (S : Set V) : ℤ :=
    (G.induce Sᶜ).oddComponents.ncard - S.ncard

noncomputable
def score (G : SimpleGraph V) (B : Set V) : Lex (ℤ × ℕ) :=
  (d G B, B.ncard)

def exists_maximal_score (G : SimpleGraph V) :
  ∃ (B : Set V), ∀ (S : Set V), score G S ≤ score G B := by
  let ps : (Set (Set V)) := Set.univ
  have psnonempty: ps.Nonempty := by simp[ps]
  have psfinite: ps.Finite := by simp[Set.toFinite]
  rcases Set.exists_max_image ps (score G) psfinite psnonempty with ⟨B', _, h⟩
  use B'
  intro S
  exact Set.mem_univ S |> h S

noncomputable
def edmond_gallai_set (G : SimpleGraph V) : Set V := (exists_maximal_score G).choose


lemma edmond_gallai_is_maximal_d (G : SimpleGraph V) :
  ∀ (B : Set V), d G B ≤ d G (edmond_gallai_set G) := by
  intro B
  have h := (exists_maximal_score G).choose_spec B
  apply Prod.Lex.monotone_fst at h
  rw[edmond_gallai_set]; exact h

lemma edmond_gallai_is_maximal_card (G : SimpleGraph V) (h : d G S = d G (edmond_gallai_set G)) :
  S.ncard ≤ (edmond_gallai_set G).ncard := by
  have h' := (exists_maximal_score G).choose_spec S
  rw[score, Prod.Lex.le_iff] at h'
  rcases h' with h_lt | ⟨_ , h'⟩
  · rw[h] at h_lt
    apply lt_irrefl at h_lt
    contradiction
  · exact h'

lemma odd_comp_ineq (Cs : Set G.ConnectedComponent) :
  Cs.ncard ≥ (G.induce (⋃ c ∈ Cs, c.supp)).oddComponents.ncard := by
  set B := (⋃ c ∈ Cs, c.supp)
  have: G.comp_ι B  '' (G.induce B).oddComponents ⊆ Cs := by
    intro x hx
    obtain ⟨y, ⟨hy, rfl⟩⟩ := hx
    obtain ⟨y', rfl⟩ := y.nonempty_supp
    rcases y' with ⟨y'', hy'⟩
    simp[B] at hy'
    exact hy'

  let comp_closed := G.biunion_closed_closed Cs
                     (fun c ↦ c.supp) (fun c _ ↦ comp_is_closed c)

  rw[← Set.ncard_image_of_injective _ (closed_comp_ι_inj comp_closed)]
  exact Set.ncard_le_ncard this

-- (G.induce Sᶜ).oddComponents.ncard - S.ncard
-- (G.induce (S\T)ᶜ).oddComponents.ncard - (S.ncard - T.ncard)
-- variable [Fintype V] in
open Classical in
open Fintype in
lemma temp (S' : Finset S) (h : S'.card > (S'.biUnion G.compNeighbors).card) :
  ∃ T ⊆ S,
  T = SetLike.coe S' ∧
  d G S < d G (S \ T) := by
  let T : Set V := Subtype.val '' SetLike.coe S'
  have TssS: T ⊆ S := fun _ ⟨⟨_, h⟩, ⟨_ , rfl⟩⟩ ↦ h
  have TeqS': T = SetLike.coe S' := rfl
  refine ⟨T, ⟨TssS, rfl, ?_⟩⟩

  let I := SetLike.coe (S'.biUnion G.compNeighbors)

  let comps := ⋃ c ∈ I, c.supp

  let f := (fun c : (G.induce Sᶜ).ConnectedComponent ↦ c.supp)

  let comps_closed := (G.induce Sᶜ).biunion_closed_closed I f (fun c _ ↦ comp_is_closed c)

  let compsST : Set ↑(S \ T)ᶜ := Subtype.val ⁻¹' ↑compsᶜ

  have: Subtype.val '' compsST = Subtype.val '' (compsᶜ) := by
     simp[compsST]
     have hs: Sᶜ ⊆ (S\T)ᶜ := by
        rw[Set.compl_diff]
        exact Set.subset_union_right
     have: (S \ T)ᶜ \ S = Sᶜ := by
      rw[Set.diff_eq, Set.inter_eq_self_of_subset_right hs]
     rw[this, Set.inter_eq_self_of_subset_right]
     trans Sᶜ
     · simp
     · exact hs

  have he: ¬(∃ x ∈ T, ∃ y ∈ compsᶜ, G.Adj x y) := by
    rintro ⟨x, xt, y, hy, xy⟩
    simp only [comps, Set.mem_compl_iff, Set.mem_iUnion,
               exists_prop, I, SetLike.mem_coe,
               Finset.mem_biUnion, compNeighbors, Finset.mem_filter,
               Finset.mem_univ, true_and] at hy
    apply hy
    use (G.induce Sᶜ).connectedComponentMk y
    refine ⟨?_, rfl⟩
    use ⟨x, TssS xt⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨a, ⟨ha, rfl⟩⟩ := TeqS' ▸ xt
      exact ha
    refine ⟨y, ⟨rfl, xy⟩⟩

  have compsST_closed : (G.induce (S\T)ᶜ).IsClosed compsST := by
    have: T = (S \ T)ᶜ \ Sᶜ := by tauto_set
    exact is_closed_induced_something (cmpl_of_closed_closed comps_closed) (this ▸ he)

  have GsTgeq: (G.induce (S \ T)ᶜ).oddComponents.ncard ≥
         ((G.induce Sᶜ).induce compsᶜ).oddComponents.ncard := by

    let ψ := (G.induce_induce_iso compsST).symm.comp <|
             (G.induce_congr this).symm.comp <|
              G.induce_induce_iso compsᶜ

    rw[← odd_comp_eq compsST_closed, iso_odd_card_eq ψ]
    linarith

  have Ilt: I.ncard ≥ ((G.induce Sᶜ).induce comps).oddComponents.ncard :=
    (G.induce Sᶜ).odd_comp_ineq I

  have Tgt: T.ncard > I.ncard := by
    rw[Set.ncard_image_of_injective _ Subtype.val_injective]
    simpa only [I, Set.ncard_coe_finset]


  have : ((S \ T).ncard : ℤ) = (S.ncard : ℤ) - (T.ncard : ℤ) := by
    rw[Set.ncard_diff TssS, Nat.cast_sub (Set.ncard_le_ncard TssS)]

  calc
    d G (S \ T) = (induce (S \ T)ᶜ G).oddComponents.ncard - (S \ T).ncard := rfl
    _ ≥ ((G.induce Sᶜ).induce compsᶜ).oddComponents.ncard - (S \ T).ncard := by linarith[GsTgeq]
    _  = ((G.induce Sᶜ).induce compsᶜ).oddComponents.ncard - (S.ncard - T.ncard) := by rw[this]
    _  > ((G.induce Sᶜ).induce compsᶜ).oddComponents.ncard +
         ((G.induce Sᶜ).induce comps).oddComponents.ncard - S.ncard := by linarith[Tgt, Ilt]
    _  = (G.induce Sᶜ).oddComponents.ncard - S.ncard := by linarith[odd_comp_eq comps_closed]
    _ = d G S := rfl



open Subgraph
open Fintype

open Classical in
lemma one_factor_iff (h₀ : G.IsMatchableToComps S)
  (h₁ : ∀ (C : (G.induce Sᶜ).ConnectedComponent), (G.induce Sᶜ).IsFactorCriticalArea C.supp) :
  card S = card (G.induce Sᶜ).ConnectedComponent ↔ ∃ M : Subgraph G, M.IsPerfectMatching := by
  obtain ⟨f, finj, hf⟩ := h₀
  choose c c_mem c_adj using hf
  choose M hM hM' using fun s ↦ h₁ (f s) (c s) (c_mem s)
  constructor
  · intro card_eq

    have fbij := (Fintype.bijective_iff_injective_and_card f).2 ⟨finj, card_eq⟩

    have hd: Pairwise fun s s' ↦ Disjoint (M s).support (M s').support := by
      intro s s' h
      rw[hM', hM']
      exact Disjoint.mono (by simp) (by simp) <|
            ((G.induce Sᶜ).pairwise_disjoint_supp_connectedComponent (finj.ne h))


    have cinj: Function.Injective c := by
      intro s s' h
      by_contra! ts
      have cinfs': c s ∈ (f s') := by rw[h]; exact c_mem s'
      exact ((G.induce Sᶜ).pairwise_disjoint_supp_connectedComponent (finj.ne ts)).le_bot <|
            ⟨c_mem s, cinfs'⟩

    have dj: Disjoint S Sᶜ := by rw[Set.disjoint_compl_right_iff_subset]


    obtain ⟨P, ⟨hP, hP'⟩⟩ := exists_of_disjoint_sets_of_injective c dj c_adj cinj
    let cM' := ⨆ s : S, (M s)
    let hcM' := Subgraph.IsMatching.iSup hM hd
    let hcM := hcM'.map (G.ι.toHom) (G.ι.injective)
    let cM := cM'.map G.ι.toHom

    have P_D_cM: Disjoint P.support cM.support := by
      rw[IsMatching.support_eq_verts, IsMatching.support_eq_verts, Set.disjoint_iff]
      · rintro x ⟨hl , ⟨⟨v, vc⟩, ⟨hC, hv⟩⟩⟩
        rcases hP ▸ hl with (hs | ⟨⟨y, yc⟩, ⟨⟨w, h⟩, hw⟩ ⟩)
        · rw[← hv] at hs
          exact vc hs
        rw[verts_iSup] at hC
        rcases hC with ⟨C, ⟨⟨s, hs'⟩, vC⟩⟩
        dsimp at hs'
        rw[← IsMatching.support_eq_verts, hM' s] at hs'
        · rw[← hs'] at vC
          have: G.ι.toHom ⟨v, vc⟩ = (⟨v, vc⟩ : ↑(Sᶜ)) := rfl
          rw[← hw, this, Subtype.val_inj] at hv
          rw[hv, ← h] at vC
          rcases vC with ⟨h1, h2⟩
          by_cases ws : w = s
          · rw[ws] at h2
            exact h2 rfl
          · exact ((G.induce Sᶜ).pairwise_disjoint_supp_connectedComponent (finj.ne ws)).le_bot <|
                  ⟨c_mem w, h1⟩
        exact hM s
      · exact hcM
      exact hP'

    let pMatch := P ⊔ cM

    have: pMatch.IsSpanning := by
      intro v
      rw[verts_sup]
      by_cases hv: v ∈ S
      · left
        rw[hP]
        exact Or.inl hv

      · have: ⟨v, hv⟩ ∈ (Set.univ : Set ↑(Sᶜ)) := by trivial
        rw[← (G.induce Sᶜ).iUnion_connectedComponentSupp] at this
        rcases this with ⟨Csupp, ⟨⟨C, rfl⟩, vC⟩⟩
        obtain ⟨s, hs⟩ := fbij.existsUnique C
        by_cases hv' : ⟨v, hv⟩ = (c s)
        · left
          rw[hP]
          right
          refine ⟨c s, ⟨Set.mem_range_self s, Subtype.val_inj.2 hv'.symm⟩⟩
        · right
          rw[map_verts, verts_iSup]
          refine ⟨⟨v, hv⟩, ⟨?_, rfl⟩⟩
          rw[Set.mem_iUnion]
          use s
          rw[← IsMatching.support_eq_verts <| hM s, hM' s, hs.1]
          exact ⟨vC, hv'⟩

    refine ⟨pMatch, ⟨IsMatching.sup hP' hcM P_D_cM, this⟩⟩

  intro h
  let nonviolator := tutte.1 h S

  have iso: G.induce Sᶜ ≃g ((⊤ : G.Subgraph).deleteVerts S).coe := by
    rw[deleteVerts, Subgraph.verts_top, ← Set.compl_eq_univ_diff, G.induce_eq_coe_induce_top Sᶜ]

  have Sleq: S.ncard ≥ (G.induce Sᶜ).oddComponents.ncard := by -- ≤ wg. tutte
    by_contra!
    apply nonviolator
    rwa[IsTutteViolator, ← iso_odd_card_eq iso]

  have oddeq: card (induce Sᶜ G).ConnectedComponent = (induce Sᶜ G).oddComponents.ncard := by
    rw[Fintype.card_eq_nat_card, ← Nat.card_congr (Equiv.Set.univ _)]
    congr
    symm
    rw[Set.eq_univ_iff_forall]
    intro C
    exact factor_area_odd (h₁ C) C.nonempty_supp

  have Seq: card S = S.ncard := by rw[← Nat.card_coe_set_eq, Fintype.card_eq_nat_card]

  have Sgeq: S.ncard ≤ (G.induce Sᶜ).oddComponents.ncard := by -- ≥ wg. h₀
    rw[← Seq, ← oddeq]
    exact Fintype.card_le_of_injective f finj

  rw[Seq, oddeq, le_antisymm Sgeq Sleq]

open Classical in
lemma helper (h₀ : G.IsMatchableToComps S)
  (h₁ : ∀ (C : (G.induce Sᶜ).ConnectedComponent), (G.induce Sᶜ).IsFactorCriticalArea C.supp)
  (h₂ : ¬∃ M : G.Subgraph, M.IsPerfectMatching) : S.ncard < (G.induce Sᶜ).oddComponents.ncard := by
  rw[← one_factor_iff h₀ h₁] at h₂
  rcases ne_iff_lt_or_gt.1 h₂ with h | h
  · have: card S = S.ncard := by
      rw[← Nat.card_coe_set_eq, Fintype.card_eq_nat_card]
    rw[← this]
    have: card (G.induce Sᶜ).ConnectedComponent = (G.induce Sᶜ).oddComponents.ncard := by
        rw[Fintype.card_eq_nat_card, ← Nat.card_congr (Equiv.Set.univ _)]
        congr
        symm
        rw[Set.eq_univ_iff_forall]
        exact fun C ↦ factor_area_odd (h₁ C) C.nonempty_supp

    rw[← this]
    exact h
  · obtain ⟨f, finj, _⟩ := h₀
    linarith[Fintype.card_le_of_injective f finj]


lemma helper₁ (h₀ : Even (Nat.card V)) (h₁ : S.ncard < (G.induce Sᶜ).oddComponents.ncard) :
  (G.induce Sᶜ).oddComponents.ncard - S.ncard ≥ 2 := by

  by_cases hS : Odd (S.ncard)
  · have: Odd (Nat.card ↑Sᶜ) := by
      rw[Nat.card_coe_set_eq, Set.odd_ncard_compl_iff]
      assumption'

    rcases (G.induce Sᶜ).odd_ncard_oddComponents.2 this with ⟨n₀, hn₀⟩
    rcases hS with ⟨n₁, hn₁⟩
    omega
  · have: ¬ Odd (Nat.card ↑Sᶜ) := by
      rw[Nat.not_odd_iff_even] at *
      rw[Nat.card_coe_set_eq, Set.even_ncard_compl_iff]
      assumption'

    rw[← (G.induce Sᶜ).odd_ncard_oddComponents] at this
    rcases Nat.not_odd_iff_even.1 this with ⟨n₀, hn₀⟩
    rcases Nat.not_odd_iff_even.1 hS with ⟨n₁, hn₁⟩
    omega



lemma ncard_oddComponents_induce_compl_eq_add
  {C : G.ConnectedComponent} (h : S ⊆ C.supp) :
  (G.induce Sᶜ).oddComponents.ncard = (G.induce C.suppᶜ).oddComponents.ncard +
                                      (G.induce (C.supp \ S)).oddComponents.ncard := by
  classical
  let C' : Set ↑Sᶜ := Subtype.val ⁻¹' C.supp
  have hc: ↑C' = C.supp \ S := by
    simp only [C', Set.diff_eq, Set.inter_comm, Subtype.image_preimage_coe]
  have hcc: (Subtype.val '' C'ᶜ) = C.suppᶜ := by
    simp only [C', Set.image_compl_preimage, Subtype.range_coe, Set.diff_eq,
    ← Set.compl_union, Set.union_eq_right.2 h]

  let ψ₀ := (G.induce_congr hc).comp <| G.induce_induce_iso C'
  let ψ₁ := (G.induce_congr hcc).comp <| G.induce_induce_iso C'ᶜ
  rw[← odd_comp_eq <| pullback_closed_is_closed Sᶜ (comp_is_closed C),
     iso_odd_card_eq ψ₀, iso_odd_card_eq ψ₁]
  ring



lemma odd_ncard_geq_one_oddComponents (G : SimpleGraph V) (h : Odd (card V)) :
  G.oddComponents.ncard ≥ 1 :=  by
  simp only [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero]
  apply Odd.pos
  rwa[odd_ncard_oddComponents, Nat.card_eq_fintype_card]




set_option maxHeartbeats 400000 in -- horrible needs to be fixed
open Classical in
theorem aux (G : SimpleGraph V) : ∃ (B : Set V),
  (G.IsMatchableToComps B) ∧
  (∀ (C : (G.induce Bᶜ).ConnectedComponent), (G.induce Bᶜ).IsFactorCriticalArea C.supp) := by

  generalize hn : Fintype.card V = n

  induction' n using Nat.strong_induction_on with n ih generalizing V

  rcases n with _ | n
  · use ∅
    have hempty := Fintype.card_eq_zero_iff.1 hn
    constructor <;> simp_all [IsFactorCriticalArea, IsMatchableToComps]
    use fun ⟨_, h⟩ ↦ False.elim h
    intro ⟨_ , hx⟩ _ _
    contradiction

  · use edmond_gallai_set G
    set B := edmond_gallai_set G
    have hnonempty := Fintype.card_pos_iff.1 (by linarith)

    have all_odd: ∀ (C : (G.induce Bᶜ).ConnectedComponent), Odd C.supp.ncard := by
      intro C
      by_contra h -- assume |C| is even
      rw[Nat.not_odd_iff_even] at h
      obtain ⟨c, cinC⟩ := C.nonempty_supp
      let C' := C.supp \ {c}
      let T := B ∪ {c.val} -- consider T := B ∪ {c}
      let funny :=
        (G.induce Bᶜ).ncard_oddComponents_induce_compl_eq_add (Set.singleton_subset_iff.2 cinC)

      have Beq: (G.induce Bᶜ).oddComponents.ncard =
            ((G.induce Bᶜ).induce C.suppᶜ).oddComponents.ncard := by
          rw[← odd_comp_eq <| comp_is_closed C, odd_comp_eq_zero_induce_even_comp C h]
          ring


      have: Tᶜ = Subtype.val '' {c}ᶜ := by
        simp[Set.diff_eq, ← Set.compl_union, T]

      let τ := (G.induce_congr this.symm).comp <| G.induce_induce_iso {c}ᶜ

      have cnotinB: c.val ∉ B := by
        obtain ⟨_, cinBc⟩ := c
        intro h'
        exact cinBc h'

      have T_card_gt_B_card: T.ncard = B.ncard + 1 := by
        simp[T]
        rw[Set.ncard_insert_of_notMem cnotinB]


      have: Odd (card C') := by
        rwa[Fintype.card_eq_nat_card, Nat.card_coe_set_eq,
          ← Nat.not_even_iff_odd, ← Nat.even_add_one,
          Set.ncard_diff_singleton_add_one cinC C.supp.toFinite]

      have one_odd : ((G.induce Bᶜ).induce C').oddComponents.ncard ≥ 1 :=
          ((G.induce Bᶜ).induce C').odd_ncard_geq_one_oddComponents this

      suffices d G T = d G B by linarith [G.edmond_gallai_is_maximal_card this]
      apply le_antisymm
      · exact G.edmond_gallai_is_maximal_d T
      simp only [d, T_card_gt_B_card, Beq, ← iso_odd_card_eq τ, funny,
                Nat.cast_add, Nat.cast_one]
      linarith[one_odd]


    have: ∀ C : (G.induce Bᶜ).ConnectedComponent, (G.induce Bᶜ).IsFactorCriticalArea C.supp := by
      intro C
      rw[IsFactorCriticalArea]
      by_contra! nCrit
      rcases nCrit with ⟨c, hc⟩

      let P' := C.supp \ {c}

      have noP': ¬ ∃ M : ((G.induce Bᶜ).induce P').Subgraph, M.IsPerfectMatching := by
        rintro ⟨M, ⟨hM₀, hM₁⟩⟩
        let M' := M.map (G.induce Bᶜ).ι.toHom
        let hM' := hM₀.map (G.induce Bᶜ).ι.toHom (G.induce Bᶜ).ι.injective
        apply hc.2 M' hM'
        rw[IsMatching.support_eq_verts hM', map_verts, isSpanning_iff.1 hM₁]
        ext x; constructor
        · rintro ⟨⟨_, ha⟩, ⟨_, rfl⟩⟩
          exact ha
        · exact fun hx ↦ ⟨⟨x, hx⟩, ⟨Set.mem_univ (⟨x, hx⟩ : ↑P'), rfl⟩⟩

      have cardP': card P' < n + 1 := by
        have: card P' = card (Subtype.val '' (C.supp \ {c})) := by
          simp only [Fintype.card_eq_nat_card, Nat.card_coe_set_eq, P',
                     Set.ncard_image_of_injective _ Subtype.val_injective]

        rw[this, Fintype.card_subtype, ← hn, Finset.card_lt_iff_ne_univ, ne_eq,
           Finset.eq_univ_iff_forall, not_forall]
        use c
        simp

      have cardEven: Even (Nat.card P') := by
        rw[Nat.card_coe_set_eq, Set.ncard_diff_singleton_of_mem hc.1,
           ← Nat.not_odd_iff_even, ← Nat.odd_add_one, Nat.sub_add_cancel]
        · exact all_odd C
        · have: 0 < C.supp.ncard := by
            rw[Set.ncard_pos]
            exact C.nonempty_supp
          exact Nat.one_le_of_lt this



      obtain ⟨Q, hQ, hQ'⟩ := ih (card P') cardP' ((G.induce Bᶜ).induce P') rfl
      let T := B ∪ ↑((Subtype.val '' Q) ∪ {c})
      let t' := helper₁ cardEven (helper hQ hQ' noP')

      have Qeq: ↑Qᶜ = C.supp \ (↑Q ∪ {c}) := by
        simp only [P', Set.image_compl_eq_range_diff_image Subtype.val_injective,
          Subtype.range_coe, Set.diff_diff, Set.union_comm]

      have Teq:  Subtype.val '' (Subtype.val '' Q ∪ {c})ᶜ = Tᶜ:= by
        rw[Set.image_compl_eq_range_diff_image Subtype.val_injective, Subtype.range_coe,
           Set.compl_union, Set.diff_eq]



      let τ := ((G.induce Bᶜ).induce_congr Qeq).comp <| (G.induce Bᶜ).induce_induce_iso Qᶜ
      let ψ := (G.induce_congr Teq).comp <| G.induce_induce_iso (Subtype.val '' Q ∪ {c})ᶜ

      have Tcard : T.ncard = B.ncard + Q.ncard + 1 := by
        repeat rw[Set.ncard_union_eq, Set.ncard_image_of_injective _ Subtype.val_injective]
        · rw[Set.ncard_singleton, add_assoc]
        · apply Set.disjoint_of_subset_left (Set.image_subset_range _ _)
          rw[Subtype.range_coe]
          exact Set.disjoint_sdiff_left
        · exact Set.disjoint_right.2 fun _ ⟨⟨_, ha⟩ , ⟨_, rfl⟩⟩ ↦ ha


      have Qcss: ↑Q ∪ {c} ⊆ C.supp := by
          rw[Set.union_subset_iff]
          refine ⟨?_, Set.singleton_subset_iff.2 hc.1⟩
          apply Set.Subset.trans (Set.image_subset_range _ _)
          rw[Subtype.range_coe]
          exact Set.diff_subset

      have Bceq: ((G.induce Bᶜ).induce C.suppᶜ).oddComponents.ncard + 1 =
            (G.induce Bᶜ).oddComponents.ncard := by
        rw[← odd_comp_eq (comp_is_closed C),
            odd_comp_eq_one_induce_odd_comp C (all_odd C), add_comm]


      suffices d G T = d G B by linarith [G.edmond_gallai_is_maximal_card this]
      apply le_antisymm
      · exact G.edmond_gallai_is_maximal_d T
      simp only [d, ← iso_odd_card_eq ψ, Tcard, Nat.cast_add, Nat.cast_one, ← Bceq,
       (G.induce Bᶜ).ncard_oddComponents_induce_compl_eq_add Qcss, ← iso_odd_card_eq τ]
      ring_nf; rw[← Nat.cast_sub (helper hQ hQ' noP').le]
      linarith[helper₁ cardEven (helper hQ hQ' noP')]

    refine ⟨?_, this⟩
    by_contra! h
    rcases not_matchable_exists_set h with ⟨A, hA⟩
    obtain ⟨T, TssB , ⟨_, hT⟩⟩ := temp A ((G.from_set_to_comp_neighbors A) ▸ hA)
    linarith[G.edmond_gallai_is_maximal_d (B \ T)]



end SimpleGraph
