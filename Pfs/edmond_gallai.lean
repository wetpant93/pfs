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

#check Set.iUnion

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
lemma factor_critcal_image (h : G.IsFactorCriticalArea S) (f : G ↪g G') :
  G'.IsFactorCriticalArea (f '' S) := by
  rintro s ⟨s', ⟨hs, hs'⟩⟩
  choose M hM hM' using h
  use (M s' hs).map f.toHom
  have img_match := Subgraph.IsMatching.map (f.toHom) (f.injective) (hM s' hs)
  refine ⟨img_match, ?_⟩
  rw[IsMatching.support_eq_verts img_match]
  simp
  rw[← IsMatching.support_eq_verts (hM s' hs),
     hM', Set.image_diff (f.injective), Set.image_singleton, hs']

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
  intro C
  exact factor_area_odd (h C) C.nonempty_supp




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
  (G.comp_ι S) (G.comp_ι_inv C CS) = C := by
  exact (comp_ι_surj C CS).choose_spec

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
    simpa
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
    rintro x (hx | hx) <;> {
      obtain ⟨w, odd, rfl⟩ := hx
      simp
      rw[closed_comp_ι_supp_card]
      assumption'
    }

  have Gss: G.oddComponents ⊆ ImS ∪ ImSc := by
    intro C _
    rcases closed_comp_dichotomy h C with (h' | h')
    · left
      use comp_ι_inv C h'
      simp[comp_ι_inv_comp_ι]
      rw[← closed_comp_ι_supp_card, comp_ι_inv_comp_ι]
      assumption'

    · right
      use comp_ι_inv C h'
      simp[comp_ι_inv_comp_ι]
      rw[← closed_comp_ι_supp_card, comp_ι_inv_comp_ι]
      assumption'

  rwa[← ImScard, ← ImSccard, ← Set.ncard_union_eq, Set.Subset.antisymm Imss Gss]


lemma comp_is_closed (C : G.ConnectedComponent) : G.IsClosed C.supp := by
  rintro ⟨x, hx, y, hy, xy⟩
  simp at hy hx
  apply hy
  rw[← hx]
  exact ConnectedComponent.connectedComponentMk_eq_of_adj xy.symm

lemma pullback_closed_is_closed (B : Set V) (h₁ : G.IsClosed S) :
  (G.induce B).IsClosed ((↑) ⁻¹' S) := by
  rintro ⟨⟨x, xb⟩, hx, ⟨y, yb⟩, hy, xy⟩
  exact h₁ ⟨x, hx, y, hy, xy⟩







#check (Subtype.val ⁻¹' B : Set ↑S)

lemma is_closed_induce_mono {B : Set {x // x ∈ S}} {T : Set V}
  (hc : (G.induce S).IsClosed B) (hs : T ⊆ S) :
  (G.induce T).IsClosed (Subtype.val ⁻¹' (↑B)) := by
  rintro ⟨⟨x, xt⟩, hx, ⟨y, yt⟩, hy, xy⟩
  simp at hx hy
  rcases hx with ⟨x', hx'⟩
  exact hc ⟨⟨x, hs xt⟩, hx', ⟨y, hs yt⟩, hy (hs yt), xy⟩

lemma is_closed_induced_something {B : Set {x // x ∈ S}}
  (hc : (G.induce S).IsClosed B) (he : ¬(∃ x ∈ T \ S, ∃ y ∈ B, G.Adj x y)) :
  (G.induce T).IsClosed (Subtype.val ⁻¹' (↑B)) := by
  rintro ⟨⟨x, xt⟩, hx, ⟨y, yt⟩, hy, xy⟩
  simp at hx hy
  rcases hx with ⟨x', hx'⟩
  by_cases hy': y ∈ S
  · exact hc ⟨⟨x, x'⟩, hx', ⟨y, hy'⟩, hy hy', xy⟩
  · exact he ⟨y, ⟨yt, hy'⟩, ⟨x, x'⟩, hx', xy.symm⟩

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
  rw[Set.ncard_congr]
  · intro v vc
    use (φ v)
  · intro v vc
    simpa
  · intro v w vc wc h
    simp at h
    exact h
  · intro v vc
    use (φ.symm) v
    simp
    rw[← ConnectedComponent.iso_inv_image_comp_eq_iff_eq_map]
    simpa

lemma iso_odd_card_eq (φ : G ≃g G') : G.oddComponents.ncard = G'.oddComponents.ncard := by
  let comp_card_eq := iso_comp_card_eq φ
  rw[Set.ncard_congr]
  · intro C _
    exact C.map φ.toHom
  · intro C Codd
    simp at *
    rwa[← comp_card_eq C]
  · intro C C' _ _ h
    let mapped := congr_arg (ConnectedComponent.map φ.symm.toHom) h
    rw[ConnectedComponent.map_comp] at mapped
    simpa using mapped

  intro C Codd
  use C.map φ.symm.toHom
  let p := comp_card_eq <| C.map φ.symm.toHom
  rw[ConnectedComponent.map_comp] at p
  simp at *
  rwa[p]


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
    rw[comp_ι_inv_comp_ι, comp_ι_mk, ← ConnectedComponent.mem_supp_iff]
    exact x'
  · intro rfl
    simp
    rwa[← closed_comp_ι_supp_card (comp_is_closed C), comp_ι_inv_comp_ι]



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
def edmond_gallai_set (G : SimpleGraph V) : (Set V) := (exists_maximal_score G).choose


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
  sorry


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
  refine ⟨T,⟨TssS, rfl, ?_⟩⟩

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
    have: (S \ T)ᶜ \ Sᶜ = T := by
      rw[Set.diff_eq, Set.diff_eq, Set.compl_inter, Set.union_inter_distrib_right]
      simpa
    rw[← this] at he
    exact is_closed_induced_something (cmpl_of_closed_closed comps_closed) he

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
    _ ≥ ((G.induce Sᶜ).induce compsᶜ).oddComponents.ncard - (S \ T).ncard := by linarith
    _  = ((G.induce Sᶜ).induce compsᶜ).oddComponents.ncard - (S.ncard - T.ncard) := by rw[this]
    _  > ((G.induce Sᶜ).induce compsᶜ).oddComponents.ncard +
         ((G.induce Sᶜ).induce comps).oddComponents.ncard - S.ncard := by linarith
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
        intro C
        exact factor_area_odd (h₁ C) C.nonempty_supp

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
    intro ⟨_,hx⟩ _ _
    contradiction

  · use edmond_gallai_set G
    set B := edmond_gallai_set G
    have hnonempty := Fintype.card_pos_iff.1 (by linarith)

    have all_odd: ∀ (C : (G.induce Bᶜ).ConnectedComponent), Odd C.supp.ncard := by
      intro C
      by_contra! h -- assume |C| is even

      obtain ⟨c, cinC⟩ := C.nonempty_supp

      let C' := C.supp \ {c}

      let C'_val := Subtype.val '' C' -- C \ {c}
      let T := B ∪ {c.val} -- consider T := B ∪ {c}

      have C'ssTc: C'_val ⊆ Tᶜ := by
        intro x h
        simp[C'_val, C'] at h
        rcases h with ⟨⟨h₀, h₁⟩, h⟩
        simp[T]
        exact ⟨h, h₀⟩

      have cnotinB: c.val ∉ B := by
        obtain ⟨_, cinBc⟩ := c
        intro h'
        exact cinBc h'

      have T_card_gt_B_card: T.ncard = B.ncard + 1 := by
        simp[T]
        rw[Set.ncard_insert_of_notMem cnotinB]

      have one_odd: (G.induce C'_val).oddComponents.ncard ≥ 1 := by -- q(C - c) ≥ 1
        have: Odd (G.induce C'_val).oddComponents.ncard := by
          rw[odd_ncard_oddComponents]
          have: C.supp.ncard = C'_val.ncard + 1 := by
            rw[Set.ncard_image_of_injective C' Subtype.coe_injective]
            rw[Set.ncard_diff_singleton_add_one cinC C.supp.toFinite]
          have: C'_val.ncard = C.supp.ncard - 1 := by simp[this]
          rw[Nat.card_coe_set_eq, this, Nat.odd_sub]
          constructor <;> {
            intro
            try simp
            contradiction
          }
          have: 0 < C.supp.ncard := by
            rw[Set.ncard_pos]
            exact C.nonempty_supp
          linarith

        rcases this with ⟨k, hk⟩
        linarith


      let C_pb : Set ↑(Tᶜ) := Subtype.val ⁻¹' C.supp -- = C'
      let GindC := (G.induce Tᶜ).induce C_pb -- G[Tᶜ][C']
      let GindCc := (G.induce Tᶜ).induce C_pbᶜ -- G[Tᶜ][C'ᶜ] ≃ G[Tᶜ ∩ C'ᶜ] ≃ G[(S ∪ C)ᶜ]

      have: Tᶜ ⊆ Bᶜ := by simp[T]

      have pb_eq: C'_val = (↑) '' C_pb := by
        simp[C'_val, C_pb, C', T]
        ext x; constructor
        · rintro ⟨hx, xneqc⟩
          refine ⟨?_, hx⟩
          simp
          refine ⟨xneqc, ?_⟩
          obtain ⟨⟨y, ynb⟩, ⟨yc, rfl⟩⟩ := hx
          exact ynb

        · rintro ⟨xb, xc⟩
          simp at xb
          exact ⟨xc, xb.1⟩

      have pbc_eq: Tᶜ \ C'_val = (↑) '' C_pbᶜ := by
        rw[pb_eq]
        simp


      let ψ := (G.induce_congr pb_eq.symm).comp (G.induce_induce_iso C_pb)  -- G[Tᶜ][C'] ≃ G[C']

      let φ := induce_induce_iso_set_ss' G this
      let C_pb_closed := pullback_closed_is_closed ((↑) ⁻¹' Tᶜ) (comp_is_closed C)
                                        -- π(C) is closed in G[Sᶜ][Tᶜ] ≃g G[Tᶜ]
      let j := iso_closed_is_closed φ C_pb_closed


      have: ¬(∃ x ∈ C_pb, ∃ y ∈ C_pbᶜ, (G.induce Tᶜ).Adj x y) := by
        have: φ '' ((↑) ⁻¹' C.supp) = C_pb := image_induce_induce_iso_preimage G this C.supp
        rwa[this] at j


      have: GindC.oddComponents.ncard + GindCc.oddComponents.ncard =
            (G.induce Tᶜ).oddComponents.ncard := by
        exact odd_comp_eq this

      have GCc_odd_eq_GBc_odd: GindCc.oddComponents.ncard = (G.induce Bᶜ).oddComponents.ncard := by
        let eq1 := odd_comp_eq (comp_is_closed C)
        simp at h
        rw[odd_comp_eq_zero_induce_even_comp C h] at eq1

        have: Subtype.val '' C.suppᶜ = Tᶜ \ C'_val := by
          simp[C'_val, T, C']
          ext x; constructor
          · rintro ⟨xBc, xnC⟩
            by_cases xeqc : x = c
            · rw[xeqc] at xnC
              have: ↑c ∈ Subtype.val '' C.supp := by use c
              contradiction
            · refine ⟨not_or.2 ⟨xeqc, xBc⟩, ?_⟩
              intro ⟨xinC, _⟩
              contradiction
          rintro ⟨xBcc, xnCc⟩
          obtain ⟨xneqc, xinBc⟩ := not_or.1 xBcc
          refine ⟨xinBc, ?_⟩
          intro xinC
          have: x ∈ Subtype.val '' C.supp \ {↑c} := by
            exact ⟨xinC, xneqc⟩
          contradiction

        rw[pbc_eq] at this

        let γ := (G.induce_induce_iso C_pbᶜ).symm.comp <|
                 (G.induce_congr this).comp <|
                  G.induce_induce_iso C.suppᶜ

        rw[← iso_odd_card_eq γ.symm] at eq1
        simp at eq1
        exact eq1

      have eq_odd: (G.induce Tᶜ).oddComponents.ncard =
                    (G.induce Bᶜ).oddComponents.ncard + (G.induce C'_val).oddComponents.ncard := by
        rw[← GCc_odd_eq_GBc_odd, iso_odd_card_eq ψ.symm]
        linarith

      have tutte_eq: d G T = d G B := by
        apply eq_of_le_of_ge
        · exact edmond_gallai_is_maximal_d G T
        calc
          d G B = (G.induce Bᶜ).oddComponents.ncard - B.ncard := rfl
          _ = (G.induce Bᶜ).oddComponents.ncard + 1 - (B.ncard + 1) := by linarith
          _ ≤ (G.induce Bᶜ).oddComponents.ncard +
             (G.induce C'_val).oddComponents.ncard - T.ncard := by linarith

          _ ≤ (G.induce Tᶜ).oddComponents.ncard - T.ncard := by linarith
          _ = d G T := rfl

      linarith[edmond_gallai_is_maximal_card G tutte_eq]

    have: ∀ C : (G.induce Bᶜ).ConnectedComponent, (G.induce Bᶜ).IsFactorCriticalArea C.supp := by
      intro C
      rw[IsFactorCriticalArea]
      by_contra! nCrit
      rcases nCrit with ⟨c, hc⟩
      let C' := Subtype.val '' (C.supp \ {c})
      have noP: ¬ ∃ M : (G.induce C').Subgraph, M.IsPerfectMatching := by
        intro h
        rcases h with ⟨M, ⟨hM, hM'⟩⟩
        have ts: Set.MapsTo id C' Bᶜ := by
          rintro x ⟨⟨y, hy⟩, ⟨_, rfl⟩⟩
          exact hy

        let h' := hM.map (G.induceHom Hom.id ts) (G.induceHom_injective Hom.id ts (by simp))
        let M' := M.map (G.induceHom Hom.id ts)

        have: M'.support = C.supp \ {c} := by
          rw[IsMatching.support_eq_verts h', map_verts, isSpanning_iff.1 hM']
          ext x; constructor
          · rintro ⟨⟨_, hy⟩, ⟨_, rfl⟩⟩
            obtain ⟨_ , ⟨h, rfl⟩⟩ := hy
            exact h
          rintro h
          have: ↑x ∈ C' := by
            rwa[Function.Injective.mem_set_image Subtype.val_injective]
          use ⟨x, this⟩
          refine ⟨by simp, rfl⟩

        exact hc.2 M' h' this

      have : card C' < n + 1 := by
        rw[← hn, Fintype.card_subtype, Finset.card_lt_iff_ne_univ]
        simp
        use c
        simp[C']


      obtain ⟨S, hS, hS'⟩ := ih (card C') this (G.induce C') rfl
      have: Even (Nat.card ↑C') := by
        rw[Nat.card_coe_set_eq]
        rw[Set.ncard_image_of_injective _ Subtype.val_injective,
           Set.ncard_diff_singleton_of_mem hc.1]
        rcases all_odd C with ⟨n , k⟩
        rw[k]
        simp

      let t := helper₁ this (helper hS hS' noP)
      let T := ↑S ∪ B ∪ {↑c}
      let C_pb : Set ↑Tᶜ := (Subtype.val ⁻¹' C.supp)
      let G'  := (G.induce Tᶜ).induce C_pb
      let Gc' := (G.induce Tᶜ).induce C_pbᶜ


      have BsubsetT: B ⊆ T := fun _ xb ↦ Or.inl (Or.inr xb)
      have TcsubsetBc : Tᶜ ⊆ Bᶜ := by simpa

      have SssC: Subtype.val '' S ⊆ Subtype.val '' C.supp := by
          have: Subtype.val '' S ⊆ C' := by simp
          exact Set.Subset.trans this (by simp[C'])


      have: Subtype.val '' Sᶜ = Subtype.val '' C_pb := by
        have eq1: ↑C_pb = Tᶜ ∩ ↑C.supp := by simp[C_pb]
        have eq2: ↑Sᶜ = C' \ ↑S := by simp
        have CssB: Subtype.val '' C.supp ⊆ Bᶜ := by simp
        rw[eq1, eq2, Set.compl_union, Set.compl_union,
            Set.inter_right_comm _ Bᶜ, Set.inter_assoc,
           Set.inter_eq_right.2 CssB, Set.inter_assoc]
        rw[← Set.diff_eq_compl_inter, ← Set.diff_eq_compl_inter]
        rw[← Set.image_singleton, ← Set.image_diff Subtype.val_injective]

      let ψ := (G.induce_induce_iso C_pb).symm.comp <|
               (G.induce_congr this).comp <|
               (G.induce_induce_iso Sᶜ) -- G[C' \ Sᶜ] ≅ G[Tᶜ ∩ C]

      have: (Subtype.val '' C.suppᶜ) = (Subtype.val '' C_pbᶜ) := by
        simp[C_pb]
        have cssC: {c.val} ⊆ Subtype.val '' C.supp:= by
          rw[Set.singleton_subset_iff]
          refine ⟨c, ⟨hc.1, rfl⟩⟩
        have SssC: Subtype.val '' S ⊆ Subtype.val '' C.supp := by
          have: Subtype.val '' S ⊆ C' := by simp
          exact Set.Subset.trans this (by simp[C'])

        rw[Set.diff_eq, Set.diff_eq, Set.compl_union, Set.compl_union,
           Set.inter_assoc, ← (Set.compl_union {c.val} _), Set.union_eq_right.2 cssC,
           Set.inter_comm _ Bᶜ, Set.inter_assoc, ← Set.compl_union (Subtype.val '' S),
           Set.union_eq_right.2 SssC]

      let φ := (G.induce_induce_iso C_pbᶜ).symm.comp <|
               (G.induce_congr this).comp <|
               (G.induce_induce_iso C.suppᶜ) -- G[Bᶜ][Cᶜ] ≅ G[Tᶜ][C'ᶜ]


      have Tcgeq2: ((G.induce Tᶜ).induce C_pb).oddComponents.ncard - S.ncard ≥ 2 := by
        rwa[← iso_odd_card_eq ψ]

      have Bceq: (G.induce Bᶜ).oddComponents.ncard - 1 =
                 ((G.induce Tᶜ).induce C_pbᶜ).oddComponents.ncard := by
        rw[← iso_odd_card_eq φ, ← odd_comp_eq_one_induce_odd_comp C (all_odd C),
           ← odd_comp_eq (comp_is_closed C)]
        simp

      have T_card: T.ncard = S.ncard + 1 + B.ncard := by
        have: Disjoint (Subtype.val '' S) B := by
          apply Set.disjoint_of_subset_left SssC
          rw[Set.disjoint_left]
          rintro _ ⟨⟨_, yb⟩, ⟨_, rfl⟩⟩
          exact yb
        have: Disjoint (Subtype.val '' S ∪ B) {↑c} := by
          rw[Set.disjoint_singleton_right]
          rintro (h | h)
          · have: ↑S ⊆ C' := by simp
            rcases this h with ⟨_ , ⟨⟨_, I'⟩, I⟩⟩
            exact I' <| Subtype.val_inj.1 I
          exact c.2 h

        rw[Set.ncard_union_eq, Set.ncard_union_eq,
           Set.ncard_image_of_injective _ Subtype.val_injective,
           Set.ncard_singleton]
        · omega
        assumption'


      have C_pb_closed: (G.induce Tᶜ).IsClosed C_pb :=
        (is_closed_induce_mono (comp_is_closed C) TcsubsetBc)

      have tutte_eq: d G T = d G B := by
        apply eq_of_le_of_ge
        · exact edmond_gallai_is_maximal_d G T
        calc
          d G T = (G.induce Tᶜ).oddComponents.ncard - T.ncard := rfl
          _ = ((G.induce Tᶜ).induce C_pb).oddComponents.ncard +
              ((G.induce Tᶜ).induce C_pbᶜ).oddComponents.ncard - T.ncard := by
               rw[← odd_comp_eq C_pb_closed]; omega
          _ ≥ (G.induce Bᶜ).oddComponents.ncard - B.ncard := by rw[T_card, ← Bceq]; omega
          _ = d G B := rfl

      linarith[G.edmond_gallai_is_maximal_card tutte_eq]
    refine ⟨?_, this⟩
    by_contra! h
    rcases not_matchable_exists_set h with ⟨A, hA⟩
    obtain ⟨T, TssB , ⟨_, hT⟩⟩ := temp A ((G.from_set_to_comp_neighbors A) ▸ hA)
    linarith[G.edmond_gallai_is_maximal_d (B \ T)]


end SimpleGraph
