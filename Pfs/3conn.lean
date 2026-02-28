import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Pfs.IsClosed

variable {V : Type*} {u v w x y : V} {G : SimpleGraph V}
variable {S : Set V}
variable {H H' : (SimpleGraph.completeGraph V).Subgraph}


namespace SimpleGraph

def IsVertexSeparator (G : SimpleGraph V) (S : Set V) (v w : V) : Prop :=
  (∀ p : G.Walk v w, ∃ s ∈ S, s ∈ p.support) ∧ (v ∉ S ∧ w ∉ S)


def IsSeparator (G : SimpleGraph V) (S : Set V) : Prop :=
  ∃ x : V, ∃ y : V, G.IsVertexSeparator S x y

def IsMinimumSeparator (G : SimpleGraph V) (X : Set V) : Prop :=
  X.Finite ∧ G.IsSeparator X ∧ ∀ S, S.Finite ∧ G.IsSeparator S → X.ncard ≤ S.ncard


def IsKConnected (G : SimpleGraph V) (k : ℕ) : Prop :=
  (∃ X : Set V, X.ncard > k) ∧ ¬(∃ S : Set V, S.Finite ∧ S.ncard < k ∧ G.IsSeparator S)

def absorbInto (G : SimpleGraph V) (x y : V) : SimpleGraph {z // z ≠ y} where
  Adj a b := a ≠ b ∧ (G.Adj ↑a ↑b ∨ (x = ↑a ∧ G.Adj ↑b y) ∨ (x = ↑b ∧ G.Adj ↑a y))
  symm a b h := by tauto
  loopless a := by tauto

lemma sub_walker {x z : V} (p : G.Path x z) (h_ne : x ≠ z) (adj_ne : ¬G.Adj x z) :
  ∃ y : V, ∃ p' : G.Walk y z, x ∉ p'.support ∧ p'.support ⊆ p.val.support ∧ G.Adj x y := by
  classical
  rcases p with (_ | ⟨e, p⟩)
  · contradiction
  rename_i y hp
  refine ⟨y, p, ⟨?_, ?_⟩⟩
  · intro hx
    let h' := hp.support_nodup
    rw[Walk.support_cons, List.nodup_cons] at h'
    exact h'.1 hx
  simpa

noncomputable
def proj (v : V) (h : x ≠ y) : {z // z ≠ y} := by
  by_cases hv : v = y
  · exact ⟨x, h⟩
  · exact ⟨v, hv⟩


lemma proj_adj (e : G.Adj v w) (h : x ≠ y) :
  (G.absorbInto x y).Adj (proj v h) (proj w h) ∨ proj v h = proj w h := by
  by_cases hp : proj v h = proj w h
  · exact Or.inr hp
  · simp [absorbInto, proj] at *
    split_ifs at *
    all_goals simp_all
    right
    exact e.symm

lemma proj_prop (h : x ≠ y) (hv : v ≠ y) :
  proj v h = v := by simp[proj, hv]


lemma proj_val (v : {z // z ≠ y}) (h : x ≠ y) : proj (↑v) h = v := by simp[v.property, proj]


noncomputable
def transport (h : x ≠ y) {u v : V} : G.Walk u v → (G.absorbInto x y).Walk (proj u h) (proj v h)
  | Walk.nil => Walk.nil
  | Walk.cons e p' => by
    rename_i w
    let p'_t := transport h p'
    by_cases h₀ : proj u h = proj w h
    · exact p'_t.copy h₀.symm rfl
    · exact Walk.cons (Or.resolve_right (proj_adj e h) h₀) p'_t

lemma transport_prop {u v : V} (h : x ≠ y) (p : G.Walk u v) :
  ∀ z ∈ (transport h p).support, z.val ∈ p.support ∨ z.val = x := by
  induction p with
    | nil =>
      intro z hz
      simp[transport] at *
      by_cases hz' : z = x
      · exact Or.inr hz'
      left
      rw[hz]
      apply proj_prop
      intro hu
      simp[proj, hu] at hz
      exact hz' (Subtype.val_inj.2 hz)
    | cons e p ih =>
      intro z hz
      rename_i u w v
      by_cases heq : proj u h = proj w h
      · simp[transport, heq] at hz
        rcases ih z hz with (h | h)
        · rw[Walk.support_cons, List.mem_cons]
          left; right;
          exact h
        · exact Or.inr h
      simp[transport, heq] at hz
      rw[Walk.support_cons, List.mem_cons] at *
      rcases hz with (h' | h')
      by_cases hu : proj u h = u
      · simp[h', hu]
      · right
        have: u = y := by
          contrapose hu
          push_neg
          apply proj_prop
          exact hu
        simp[h', proj, this]
      rcases ih z h' with (h' | h')
      · left; right; exact h'
      · exact Or.inr h'


lemma transport_y_free_walk {u v : V} (p : G.Walk u v) (h : x ≠ y) (hy : y ∉ p.support) :
  ∀ z ∈ (transport h p).support, z.val ∈ p.support := by
  induction p with
    | nil =>
      intro z hz
      rw[transport, Walk.mem_support_nil_iff] at *
      subst hz
      apply proj_prop
      intro; apply hy; symm; assumption
    | cons e p ih =>
      intro z hz
      rename_i u w v
      rw[transport, Walk.support_cons, List.mem_cons] at *
      split_ifs at hz
      · rw[Walk.support_copy] at hz
        exact Or.inr <| ih (not_or.1 hy).2 z hz
      · rw[Walk.support_cons, List.mem_cons] at hz
        rcases hz with (hz | hz)
        · subst hz
          left
          apply proj_prop
          symm
          exact(not_or.1 hy).1
        · exact Or.inr <| ih (not_or.1 hy).2 z hz


lemma keep_sep_no_x {X : Set {z // z ≠ y}} (h : x ≠ y) (hX : (G.absorbInto x y).IsSeparator X)
  (xne : x ∉ Subtype.val '' X) :
  G.IsSeparator (Subtype.val '' X) := by
  rcases hX with ⟨v, w, h'⟩
  refine ⟨↑v, ↑w, ⟨?_, ?_⟩⟩
  · intro p
    let p_trans := Walk.copy (transport h p) (proj_val v h) (proj_val w h)
    rcases h'.1 p_trans with ⟨s, hs⟩
    use ↑s
    constructor
    · use s
      exact ⟨hs.1, rfl⟩

    rw[Walk.support_copy] at hs
    rcases (transport_prop h p) s hs.2 with (h' | h')
    · assumption
    · subst h'
      exfalso
      apply xne
      use s
      exact ⟨hs.1, rfl⟩
  let := h'.2
  simp only [Set.mem_image, Subtype.val_inj]
  simpa



lemma keep_sep {X : Set {z // z ≠ y}} (h : x ≠ y) (hX : (G.absorbInto x y).IsSeparator X) :
  G.IsSeparator ((Subtype.val '' X) ∪ {y}) := by
  rcases hX with ⟨v, w, h'⟩
  refine ⟨↑v, ↑w, ⟨?_, ?_⟩⟩
  · intro p
    let p_trans := Walk.copy (transport h p) (proj_val v h) (proj_val w h)
    by_cases hy : y ∈ p.support
    · use y
      exact ⟨by simp, hy⟩
    · rcases h'.1 p_trans with ⟨s, hs⟩
      use ↑s
      constructor
      · left
        use s
        exact ⟨hs.1, rfl⟩
      rw[Walk.support_copy] at hs
      exact transport_y_free_walk p h hy s hs.2
  simp[h'.2, Set.mem_image, Subtype.val_inj, v.property, w.property]


lemma IsMinimalSeperator.adj_comp [Fintype V] {X : Set V} (h : G.IsMinimumSeparator X) :
  ∀ C : (G.induce Xᶜ).ConnectedComponent, ∀ x ∈ X, ∃ c ∈ C, G.Adj x c := by
  classical
  by_contra! h'
  rcases h' with ⟨C, x, ⟨hx, hC⟩⟩
  have X_sep : G.IsSeparator (X \ {x}) := by
    obtain ⟨c, hC'⟩ := C.nonempty_supp

    have xneqc : x ≠ ↑c := by
      intro rfl
      exact c.property hx

    have cX : ↑c ∉ X \ {x} := by
      rintro ⟨cinX, _⟩
      exact c.property cinX

    refine ⟨x, c, ⟨?_, ⟨by simp, cX⟩⟩⟩
    intro p
    by_contra! hp
    rcases sub_walker p.toPath xneqc (hC c hC') with ⟨y, p', hp'⟩
    have p'_avoids_X : ∀ v ∈ p'.support, v ∈ Xᶜ := by
      intro v vp' vx
      by_cases hv : v = x
      · apply hp'.1
        rwa[← hv]
      have: v ∈ X \ {x} := by exact ⟨vx, hv⟩
      apply hp v this
      exact Set.Subset.trans hp'.2.1 (Walk.support_toPath_subset p) vp'

    let p'' := p'.induce Xᶜ p'_avoids_X
    have: y ∉ Subtype.val '' C.supp := by
      intro ⟨_ , ⟨hy, hy'⟩⟩
      exact hp'.2.2 |> hy' ▸ hC _ hy

    have: ⟨y, p'_avoids_X _ p'.start_mem_support⟩ ∉ C.supp := by
      rintro hy
      have: y ∈ Subtype.val '' C.supp := by use ⟨y, p'_avoids_X _ p'.start_mem_support⟩
      contradiction
    exact C.isClosed_supp <| exists_crossing_edge hC' this p''.reachable.symm
  sorry
  --linarith[h.2 (X \ {x}) X_sep, Set.ncard_diff_singleton_lt_of_mem hx]


lemma IsKConnected.nonempty {k : ℕ} (h : G.IsKConnected k) : Nonempty V := by
  rcases h.1 with ⟨X, hX⟩
  have: X ≠ ∅ := by
    intro rfl
    rw[Set.ncard_empty] at hX
    contradiction
  obtain ⟨x⟩ := Set.nonempty_iff_empty_ne.2 this.symm
  use x

lemma IsKConnected.Connected {k : ℕ} (h : G.IsKConnected k) (hk : k > 0) : G.Connected := by
  have preconnected: G.Preconnected := by
    intro x y
    by_contra! h'
    apply h.2
    use ∅
    simp[hk, IsSeparator, IsVertexSeparator]
    refine ⟨x, y, ?_⟩
    intro p'
    apply h'
    use p'
  let nonempty := h.nonempty
  constructor
  assumption

lemma aux₀ [Fintype V] (e : G.Adj x y) (h_card : Fintype.card V > 4)
  (h_conn : G.IsKConnected 3)
  (h_sep : ¬((G.absorbInto x y).IsKConnected 3)) :
  ∃ z , G.IsSeparator {x, y, z} := by
  classical
  dsimp[IsKConnected] at h_sep
  push_neg at h_sep
  have absorb_card : ∃ X : Set {x // x ≠ y}, X.ncard > 3 := by
    use Set.univ
    simp; omega

  rcases h_sep absorb_card with ⟨S, hS⟩

  have S_card: S.ncard = 2 := by
    by_cases h' : S.ncard < 2
    · have sep_ncard : ((Subtype.val '' S) ∪ {y}).ncard < 3 := by
        apply lt_of_le_of_lt <| Set.ncard_union_le (Subtype.val '' S) {y}
        rw[Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_singleton]
        omega
      exfalso
      apply h_conn.2
      use (Subtype.val '' S) ∪ {y}
      refine ⟨?_, sep_ncard, keep_sep e.ne hS.2.2⟩
      rw[Set.finite_union]
      exact ⟨Set.Finite.image Subtype.val hS.1, Set.finite_singleton y⟩
    omega

  have xinS: ⟨x, e.ne⟩ ∈ S := by
    by_contra! hx
    have: x ∉ Subtype.val '' S := by simp[hx]
    exfalso
    apply h_conn.2
    use Subtype.val '' S
    refine ⟨Set.Finite.image Subtype.val hS.1, ?_, keep_sep_no_x e.ne hS.2.2 this⟩
    rw[Set.ncard_image_of_injective _ Subtype.val_injective]
    omega

  rcases Set.ncard_eq_two.1 S_card with ⟨a, b, hS'⟩
  wlog ha : a = x with H
  · have wl: b ≠ a ∧ S = {b, a} := by
      constructor
      · symm; exact hS'.1
      · rw[Set.pair_comm]
        exact hS'.2

    have beqx: ↑b = x := by
      rw[hS'.2] at xinS
      rcases xinS with rfl | rfl
      · contradiction
      · rfl

    exact H e h_card h_conn h_sep absorb_card S hS S_card xinS b a wl beqx

  use b
  have: Subtype.val '' S ∪ {y} = {x, y, ↑b} := by grind
  exact this ▸ keep_sep e.ne hS.2.2


lemma exists_edge_of_connected_nontrivial [Nontrivial V]
  (h : G.Connected) : ∃ u v : V, G.Adj u v := by
  obtain ⟨u, v, h_neq⟩ := exists_pair_ne V
  obtain ⟨p⟩ := h.preconnected u v
  cases p with
  | nil => contradiction
  | cons h_adj _ =>
    exact ⟨_, _, h_adj⟩



lemma IsKConnected.exists_edge {k : ℕ} (hk : k ≥ 1) (h : G.IsKConnected k) :
  ∃ x y : V, G.Adj x y := by
  have: Nontrivial V := by
    obtain ⟨X, hX⟩ := h.1
    have: X.ncard > 1 := by omega
    obtain ⟨x⟩ := h.nonempty
    obtain ⟨b, hb⟩ := Set.exists_ne_of_one_lt_ncard this x
    exact ⟨x, b, hb.2.symm⟩
  exact exists_edge_of_connected_nontrivial (h.Connected (by omega))


noncomputable
def score_comp (C : G.ConnectedComponent) : ℕ := C.supp.ncard

lemma exists_min_comp_card [Nonempty V] [Fintype V] :
  ∃ C : G.ConnectedComponent, ∀ C' : G.ConnectedComponent, score_comp C ≤ score_comp C' := by
  apply Finite.exists_min

noncomputable
def score_sep [Fintype V] (x y z : V) (h_card : Fintype.card V > 4) : ℕ := by
  classical
  have c_nonempty: Nonempty ({x,y,z}ᶜ : Set V) := by
     rw[Set.nonempty_coe_sort, Set.nonempty_iff_empty_ne]
     intro h
     have univ: {x,y,z} = (Set.univ : Set V) := Set.compl_empty_iff.1 h.symm
     have univ_card : ({x,y,z} : Set V).ncard ≤ 3:= by
        linarith [Set.ncard_insert_le x {y, z}, Set.ncard_insert_le y {z}, Set.ncard_singleton z]
     rw[Fintype.card_eq_nat_card, ← Set.ncard_univ, ← univ] at h_card
     omega
  let min_comp := ((G.induce {x,y,z}ᶜ).exists_min_comp_card).choose
  exact min_comp.supp.ncard

lemma score_sep_min [Fintype V] (h_card : Fintype.card V > 4)
  (h_exists : ∃ x y z, G.Adj x y ∧ G.IsSeparator {x, y, z}) :
  ∃ (x y z : V), G.Adj x y ∧ G.IsSeparator {x, y, z} ∧
  ∀ (x' y' z' : V), G.Adj x' y' ∧ G.IsSeparator {x', y', z'} →
    G.score_sep x y z h_card ≤ G.score_sep x' y' z' h_card := by
  classical
  let P := fun (n : ℕ) ↦ ∃ (x y z : V)
                            (e : G.Adj x y)
                            (hz : G.IsSeparator {x,y,z}) , G.score_sep x y z h_card = n

  have hP_exists : ∃ n, P n := by
    obtain ⟨x, y, z, ⟨e, hz⟩⟩ := h_exists
    refine ⟨G.score_sep x y z h_card, ⟨x,y,z,e,hz,rfl⟩⟩
  rcases Nat.find_spec hP_exists with ⟨x,y,z, ⟨h₀,h₁,h₂⟩⟩
  refine ⟨x, y, z, h₀, h₁, ?_⟩
  intro x' y' z' h'
  rw[h₂]
  apply Nat.find_min'
  use x', y', z', h'.1, h'.2

open Classical in
lemma aux_main [Fintype V] (h : G.IsKConnected 3) (h_card : Fintype.card V > 4) :
  ∃ x y : V, G.Adj x y ∧ (G.absorbInto x y).IsKConnected 3 := by
  by_contra! no_edge
  obtain ⟨x, y, xy⟩ := h.exists_edge (by decide)
  let not_conn := no_edge x y xy
  obtain ⟨z, hz⟩ := aux₀ xy h_card h not_conn
  obtain ⟨x, y, z, xy, h_sep, h_min⟩ := G.score_sep_min h_card (by refine ⟨x, y, z, xy, hz⟩)
  sorry


end SimpleGraph
