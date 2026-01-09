import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Tutte
import Mathlib.Combinatorics.Hall.Basic
import Pfs.IsClosed

variable {V V' : Type*}
variable {G H : SimpleGraph V}
variable {G' H' : SimpleGraph V'}
variable {S B T : Set V}
variable {S' : Set V'}
variable {C : G.ConnectedComponent}

namespace SimpleGraph

variable [Nonempty S] in
def IsFactorCriticalArea (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ v ∈ S, ∃ M : G.Subgraph, M.IsMatching ∧ M.support = S \ {v}


def IsMatchableToComps (S : Set V) : Prop :=
  ∃ (f : S → (G.induce Sᶜ).ConnectedComponent),
  Function.Injective f ∧ (∀ s : S, ∃ y ∈ (f s), G.Adj ↑s ↑y)

variable [Fintype V] in
open Classical in
open Fintype in
lemma IsMatchableToComps.card_le (h : G.IsMatchableToComps S) :
  card S ≤ card (G.induce Sᶜ).ConnectedComponent := by
  obtain ⟨f, finj, _⟩ := h
  exact Fintype.card_le_of_injective f finj

def connectedComponentsNeighbors (s : S) : Set (G.induce Sᶜ).ConnectedComponent :=
  {C : (G.induce Sᶜ).ConnectedComponent | ∃ y ∈ C.supp, G.Adj s y}

variable [Fintype V] in
open Fintype in
lemma not_matchable_exists_hall_violator (h : ¬ G.IsMatchableToComps S) :
  ∃ (A : Set S),
     A.ncard > (⋃ a ∈ A, G.connectedComponentsNeighbors a).ncard  := by
     classical
     let r := fun (s : S) (C : (G.induce Sᶜ).ConnectedComponent) ↦ ∃ y ∈ C.supp, G.Adj s y
     apply (Iff.not (all_card_le_filter_rel_iff_exists_injective r)).2 at h
     push_neg at h
     rcases h with ⟨A, hA⟩
     use A
     rw[Set.ncard_coe_finset, Finset.set_biUnion_coe, gt_iff_lt, Set.ncard_eq_toFinset_card']
     convert hA
     ext
     simp[connectedComponentsNeighbors, r]

lemma IsMatching.exists_of_disjoint_sets_of_injective {A B : Set V} (f : A → B) (hd : Disjoint A B)
  (hf : ∀ a : A, G.Adj a (f a)) (hinj : Function.Injective f) :
  ∃ M : G.Subgraph, M.verts = A ∪ (↑(Set.range f)) ∧ M.IsMatching := by
  have: ↑(Set.range f) ⊆ B := by simp
  let hd' := (Set.disjoint_of_subset_right this hd)
  let f' := (Equiv.ofInjective f hinj).trans (Equiv.Set.image _ (Set.range f) Subtype.val_injective)
  exact Subgraph.IsMatching.exists_of_disjoint_sets_of_equiv hd' f' hf


open Subgraph in
variable [Fintype V] in
lemma IsFactorCriticalArea.odd_ncard
  (h : G.IsFactorCriticalArea S) (hn : S.Nonempty) : Odd S.ncard := by
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
lemma all_odd_factor_area (h : ∀ C : G.ConnectedComponent, G.IsFactorCriticalArea C.supp) :
  card G.ConnectedComponent = G.oddComponents.ncard := by
  rw[Fintype.card_eq_nat_card, ← Nat.card_congr (Equiv.Set.univ _)]
  congr
  symm
  rw[Set.eq_univ_iff_forall]
  exact (fun C ↦ IsFactorCriticalArea.odd_ncard (h C) C.nonempty_supp)

lemma iso_comp_card_eq (φ : G ≃g G') (C : G.ConnectedComponent) :
  C.supp.ncard = (C.map φ.toHom).supp.ncard := by
  rw[Set.ncard, Set.encard_congr (C.isoEquivSupp φ), ← Set.ncard]
  rfl

lemma iso_odd_card_eq (φ : G ≃g G') : G.oddComponents.ncard = G'.oddComponents.ncard := by
  have: G.oddComponents ≃ G'.oddComponents := by
    refine φ.connectedComponentEquiv.subtypeEquiv fun u ↦ ?_
    simp only [oddComponents, Set.mem_setOf, iso_comp_card_eq φ]
    rfl
  rw[Set.ncard, Set.encard_congr this, Set.ncard]

def induce_congr (h : B = S) : G.induce B ≃g G.induce S where
  toFun := by subst h; exact id
  invFun := by subst h; exact id
  map_rel_iff' := by
    intro a b
    subst h
    rfl

  left_inv := by intro x; subst h; rfl
  right_inv := by intro x; subst h; rfl


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
  intro C'
  obtain ⟨⟨x, xc⟩, rfl⟩ := C'.nonempty_supp
  rw[Set.mem_setOf, ← C.isClosed_supp.connectedComponent_ncard_eq,
    ConnectedComponent.map_mk]
  dsimp
  rwa[xc, Nat.not_odd_iff_even]


omit [Fintype V] in
lemma odd_comp_eq_one_induce_odd_comp
  (C : G.ConnectedComponent) (h : Odd C.supp.ncard) :
  (G.induce C.supp).oddComponents.ncard = 1 := by
  rw[Set.ncard_eq_one]
  obtain ⟨u, uc⟩ := C.nonempty_supp
  use (G.induce C.supp).connectedComponentMk ⟨u, uc⟩
  ext x
  refine x.ind fun ⟨v, vc⟩ ↦ ?_
  rw[Set.mem_setOf, Set.mem_singleton_iff, eq_comm,
     ← C.isClosed_supp.connectedComponent_eq_map_induce_iff, uc,
     ConnectedComponent.map_mk, eq_comm, ← C.mem_supp_iff,
     ← C.isClosed_supp.connectedComponent_ncard_eq, ConnectedComponent.map_mk]
  dsimp
  rw[vc]
  exact iff_of_true h vc

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
  exact ⟨B', fun S ↦  Set.mem_univ S |> h S⟩

noncomputable
def edmonds_gallai_set (G : SimpleGraph V) : Set V := (exists_maximal_score G).choose

lemma edmonds_gallai_is_maximal_d (G : SimpleGraph V) :
  ∀ (B : Set V), d G B ≤ d G (edmonds_gallai_set G) := by
  intro B
  have h := (exists_maximal_score G).choose_spec B
  apply Prod.Lex.monotone_fst at h
  rwa[edmonds_gallai_set]

lemma edmonds_gallai_is_maximal_card (G : SimpleGraph V) (h : d G S = d G (edmonds_gallai_set G)) :
  S.ncard ≤ (edmonds_gallai_set G).ncard := by
  have h' := (exists_maximal_score G).choose_spec S
  rw[score, Prod.Lex.le_iff] at h'
  rcases h' with h_lt | ⟨_ , h'⟩
  · rw[h] at h_lt
    apply lt_irrefl at h_lt
    contradiction
  · exact h'


lemma ncard_ge_induce_iUnion_oddComponents (Cs : Set G.ConnectedComponent) :
  Cs.ncard ≥ (G.induce (⋃ c ∈ Cs, c.supp)).oddComponents.ncard := by
  let comps_closed := IsClosed.biUnion Cs (fun c ↦ c.supp) (fun c _ ↦ c.isClosed_supp)
  rw[← Set.ncard_image_of_injective _ comps_closed.connectedComponent_map_induce_injective]
  apply Set.ncard_le_ncard _
  intro _ ⟨c, ⟨_, h⟩⟩
  obtain ⟨⟨v, vc⟩, rfl⟩ := c.nonempty_supp
  simp only [Set.mem_iUnion, exists_prop, ConnectedComponent.mem_supp_iff, exists_eq_right'] at vc
  rwa[← h, ConnectedComponent.map_mk]


lemma deficiency_remove_hall_violator_lt
  (T : Set S) (hT : T.ncard > (⋃ x ∈ T, G.connectedComponentsNeighbors x).ncard) :
  d G S < d G (S \ ↑T) := by
  classical
  let I := ⋃ x ∈ T, G.connectedComponentsNeighbors x
  let comps := ⋃ x ∈ I, x.supp
  let comps_closed := IsClosed.biUnion I (fun c ↦ c.supp) (fun c _ ↦ c.isClosed_supp)
  let compsST : Set ↑(S \ ↑T)ᶜ := Subtype.val ⁻¹' ↑compsᶜ

  have: Subtype.val '' compsST = Subtype.val '' compsᶜ := by
     simp[compsST]
     tauto_set

  have T_subset: ↑T ⊆ S := fun _ ⟨⟨_, xs⟩, ⟨_, hx⟩⟩ ↦ hx ▸ xs

  have he': ¬(∃ x ∈ (Subtype.val '' T), ∃ y ∈ compsᶜ, G.Adj x y) := by
    rintro ⟨x, ⟨x', ⟨hx, hx'⟩⟩, y, hy, xy⟩
    simp only [Set.mem_compl_iff, comps, Set.mem_iUnion, exists_prop, I] at hy
    apply hy
    --refine ⟨(G.induce Sᶜ).connectedComponentMk y, ⟨⟨x, ⟨hx, ⟨y, ⟨rfl, xy⟩⟩⟩⟩, rfl⟩⟩
    use ((G.induce Sᶜ).connectedComponentMk y)
    constructor
    · use x'
      exact ⟨hx, ⟨y, ⟨rfl, hx' ▸ xy⟩⟩⟩
    · rfl

  have compsST_closed : (G.induce (S\T)ᶜ).IsClosed compsST := by
    have: Subtype.val '' T = (S \ T)ᶜ \ Sᶜ := by
      tauto_set

    exact IsClosed.induce_of_not_adj (comps_closed.compl) (this ▸ he')

  have: (G.induce (S \ ↑T)ᶜ).oddComponents.ncard ≥
        ((G.induce Sᶜ).induce compsᶜ).oddComponents.ncard := by
    let ψ := (G.induce_induce_iso compsᶜ).symm.comp <|
             (G.induce_congr this).comp <|
             (G.induce_induce_iso compsST)
    rw[← compsST_closed.oddComponents_ncard_add_compl_eq, iso_odd_card_eq ψ]
    linarith

  have S_diff_T_ncard: - ((S \ ↑T).ncard : ℤ) = -S.ncard + ↑T.ncard := by
    rw[Set.ncard_diff T_subset, Nat.cast_sub (Set.ncard_le_ncard T_subset),
       Set.ncard_image_of_injective _ Subtype.val_injective]
    linarith

  calc
    d G (S \ ↑T) = (G.induce (S \ ↑T)ᶜ).oddComponents.ncard - (S \ ↑T).ncard := rfl
    _ ≥ ((G.induce Sᶜ).induce compsᶜ).oddComponents.ncard - (S \ ↑T).ncard := by linarith[this]
    _ > (G.induce Sᶜ).oddComponents.ncard - S.ncard := by
        linarith[S_diff_T_ncard,
                 lt_of_le_of_lt ((G.induce Sᶜ).ncard_ge_induce_iUnion_oddComponents I) hT,
                 comps_closed.oddComponents_ncard_add_compl_eq]
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


    obtain ⟨P, ⟨hP, hP'⟩⟩ := IsMatching.exists_of_disjoint_sets_of_injective c dj c_adj cinj
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

    exact ⟨pMatch, ⟨IsMatching.sup hP' hcM P_D_cM, this⟩⟩

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
    exact IsFactorCriticalArea.odd_ncard (h₁ C) C.nonempty_supp

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
        exact fun C ↦ IsFactorCriticalArea.odd_ncard (h₁ C) C.nonempty_supp

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

  let ψ₀ := (G.induce_congr hc).comp <| G.induce_induce_iso C' -- G[Sᶜ][C] ≃g G[C \ S]
  let ψ₁ := (G.induce_congr hcc).comp <| G.induce_induce_iso C'ᶜ -- G[Sᶜ][Cᶜ] ≃g G[Cᶜ]
  rw[← IsClosed.oddComponents_ncard_add_compl_eq <|
     IsClosed.val_preimage_closed Sᶜ (ConnectedComponent.isClosed_supp C),
     iso_odd_card_eq ψ₀, iso_odd_card_eq ψ₁]
  ring


lemma ncard_oddComponents_induce_compl_eq_add'
  (h : S ⊆ T) (hT : G.IsClosed T) :
  (G.induce Sᶜ).oddComponents.ncard = (G.induce Tᶜ).oddComponents.ncard +
                                      (G.induce (T \ S)).oddComponents.ncard := by
  classical
  let T' : Set ↑Sᶜ := Subtype.val ⁻¹' T
  have hc: ↑T' = T \ S := by
    simp only [T', Set.diff_eq, Set.inter_comm, Subtype.image_preimage_coe]
  have hcc: (Subtype.val '' T'ᶜ) = Tᶜ := by
    simp only [T', Set.image_compl_preimage, Subtype.range_coe, Set.diff_eq,
    ← Set.compl_union, Set.union_eq_right.2 h]

  let ψ₀ := (G.induce_congr hc).comp <| G.induce_induce_iso T' -- G[Sᶜ][T] ≃g G[T \ S]
  let ψ₁ := (G.induce_congr hcc).comp <| G.induce_induce_iso T'ᶜ -- G[Sᶜ][Tᶜ] ≃g G[Tᶜ]
  rw[← IsClosed.oddComponents_ncard_add_compl_eq <|
     IsClosed.val_preimage_closed Sᶜ hT,
     iso_odd_card_eq ψ₀, iso_odd_card_eq ψ₁]
  ring

lemma odd_ncard_geq_one_oddComponents (G : SimpleGraph V) (h : Odd (card V)) :
  G.oddComponents.ncard ≥ 1 :=  by
  simp only [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero]
  apply Odd.pos
  rwa[odd_ncard_oddComponents, Nat.card_eq_fintype_card]


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

  · use edmonds_gallai_set G
    set B := edmonds_gallai_set G
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
          rw[← IsClosed.oddComponents_ncard_add_compl_eq <| ConnectedComponent.isClosed_supp C,
              odd_comp_eq_zero_induce_even_comp C h]
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

      suffices d G T = d G B by linarith [G.edmonds_gallai_is_maximal_card this]
      apply le_antisymm
      · exact G.edmonds_gallai_is_maximal_d T
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
        rw[← IsClosed.oddComponents_ncard_add_compl_eq (ConnectedComponent.isClosed_supp C),
            odd_comp_eq_one_induce_odd_comp C (all_odd C), add_comm]


      suffices d G T = d G B by linarith [G.edmonds_gallai_is_maximal_card this]
      apply le_antisymm
      · exact G.edmonds_gallai_is_maximal_d T
      simp only [d, ← iso_odd_card_eq ψ, Tcard, Nat.cast_add, Nat.cast_one, ← Bceq,
       (G.induce Bᶜ).ncard_oddComponents_induce_compl_eq_add Qcss, ← iso_odd_card_eq τ]
      ring_nf; rw[← Nat.cast_sub (helper hQ hQ' noP').le]
      linarith[helper₁ cardEven (helper hQ hQ' noP')]

    refine ⟨?_, this⟩
    by_contra! h
    rcases not_matchable_exists_hall_violator h with ⟨T, hT⟩
    linarith[G.deficiency_remove_hall_violator_lt T hT, G.edmonds_gallai_is_maximal_d (B \ T)]


end SimpleGraph
