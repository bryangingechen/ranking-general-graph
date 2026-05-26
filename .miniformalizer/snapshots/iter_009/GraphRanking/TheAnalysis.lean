import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Perm.Basic
import GraphRanking.Introduction

open scoped Classical

/-! ## The Analysis section -/

/-- Given matchings $R$ (the output of $\operatorname{Rank}$) and $\operatorname{opt}$
    (a maximum matching of $G$), a subset $I$ of $2k$ vertices is a $k$-wasteful independent set
    iff the vertices in $I$ are end-points of $k$ vertex-disjoint length-three augmenting paths
    in $R\oplus\operatorname{opt}$. Each such path consists of two $\operatorname{opt}$-edges
    connected by an $R$-edge, with the outer endpoints forming $I$.

    Formally, there exists a set $M$ of $2k$ $\operatorname{opt}$-edges paired by an involution
    $f$, such that each pair $(e, f e)$ is connected by an $R$-edge between non-$I$ vertices,
    and $I$ contains exactly one vertex from each $M$-edge.  Vertices in $I$ are unmatched in
    $R$ (they are the "wasted" endpoints of the augmenting paths). -/
def def_ltap {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (R opt : SimpleGraph.Subgraph G) (k : ℕ) (I : Finset V) : Prop :=
  I.card = 2*k ∧ G.IsIndepSet (I : Set V) ∧
  (∀ v ∈ I, ∀ w, s(v, w) ∉ R.edgeSet) ∧
  ∃ (M : Finset (Sym2 V)) (f : Sym2 V → Sym2 V),
    M.card = 2*k ∧ (∀ e ∈ M, e ∈ opt.edgeSet) ∧
    -- f is a fixed-point-free involution on M, pairing edges into k augmenting paths
    (∀ e ∈ M, f e ∈ M) ∧ (∀ e ∈ M, f (f e) = e) ∧ (∀ e ∈ M, f e ≠ e) ∧
    -- Each pair (e, f e) is connected by an R-edge between non-I endpoints
    (∀ e ∈ M, ∃ (v w : V), v ∈ e ∧ w ∈ f e ∧ s(v, w) ∈ R.edgeSet ∧ v ∉ I ∧ w ∉ I) ∧
    -- Every I-vertex belongs to some M-edge, and each M-edge contains exactly one I-vertex
    (∀ v ∈ I, ∃ e ∈ M, v ∈ e) ∧
    (∀ e ∈ M, ∃! v, v ∈ I ∧ v ∈ e)

lemma def_ltap.card_I {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {R opt : SimpleGraph.Subgraph G} {k : ℕ} {I : Finset V} (h : def_ltap G R opt k I) : I.card = 2*k :=
  h.1

lemma def_ltap.isIndepSet {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {R opt : SimpleGraph.Subgraph G} {k : ℕ} {I : Finset V} (h : def_ltap G R opt k I) :
    G.IsIndepSet (I : Set V) :=
  h.2.1

lemma def_ltap.unmatched {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {R opt : SimpleGraph.Subgraph G} {k : ℕ} {I : Finset V} (h : def_ltap G R opt k I)
    {v w : V} (hv : v ∈ I) : s(v, w) ∉ R.edgeSet :=
  h.2.2.1 v hv w

/-- If the approximation ratio of $\operatorname{Rank}$ is at most $1/2 + c$ for
    $0 \leq c \leq 1/6$, then the expected number of $k$-WIS in the output of
    $\operatorname{Rank}$ is at least one, when $k = (1/2 - 3c) \cdot n/2$. -/
theorem lem_kltap_all_perms {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (opt : SimpleGraph.Subgraph G) (c : ℝ) (hc_low : 0 ≤ c) (hc_high : c ≤ 1/6) (k : ℕ)
    (hk : (k : ℝ) = (1/2 - 3*c) * (Fintype.card V : ℝ) / 2)
    (h_ratio : (Finset.sum Finset.univ (fun (σ : Equiv.Perm V) =>
      ((Finset.filter (· ∈ (Ranking_Algorithm G σ).edgeSet) G.edgeFinset).card : ℝ))
      / (Fintype.card (Equiv.Perm V) : ℝ)) ≤ (1/2 + c) * (matchingNumber G : ℝ)) :
    (Finset.sum Finset.univ (fun (σ : Equiv.Perm V) =>
      ((Finset.filter (fun (I : Finset V) =>
        def_ltap G (Ranking_Algorithm G σ) opt k I) (Finset.powerset (Finset.univ : Finset V))).card : ℝ))
      / (Fintype.card (Equiv.Perm V) : ℝ)) ≥ 1 := by
  /- The proof follows the LaTeX structure:
     1. For each σ, let r_σ = |Ranking_Algorithm G σ| and write r_σ = (1/2 + c_σ) * μ(G).
     2. By prop_aug3_path_bound (applied with M = Ranking_Algorithm G σ, which is a maximal matching),
        there are at least (1/4 - 3c_σ/2) * μ(G) disjoint aug-3-paths (edges/2).
     3. Let a_σ be the number of such paths. Then a_σ ≥ (1/4 - 3c_σ/2) * μ(G).
     4. The total number of paths across all σ is Σ a_σ.
     5. From h_ratio: (Σ r_σ)/N ≤ (1/2 + c)*μ(G), which implies Σ c_σ ≤ N*c.
     6. Therefore Σ a_σ ≥ N * (μ(G)/4 - 3c*μ(G)/2) = N * μ(G) * (1/4 - 3c/2).
     7. Number of k-WIS for σ is at least C(a_σ, k) (choose k paths among a_σ, each gives a distinct k-WIS).
     8. By prop_bionomila_minimize, Σ C(a_σ, k) is minimized when all a_σ are equal.
     9. With a_σ ≥ μ(G)*(1/4 - 3c/2) on average, the minimum of Σ C(a_σ, k) occurs at equality.
     10. So Σ C(a_σ, k) ≥ N * C(μ(G)*(1/4 - 3c/2), k).
     11. With k = (1/2 - 3c)*n/2 and μ(G) ≤ n/2, this evaluates to ≥ N.
     12. Therefore expected number ≥ N/N = 1.
     
     Note: There is a factor-of-2 discrepancy between prop_aug3_path_bound (which bounds edges)
     and the LaTeX (which counts paths). We use edges/2 for the path count.
     Also, the proof assumes μ(G) = n/2 (perfect matching) for the final evaluation;
     a more general argument would need to handle μ(G) < n/2. -/
  sorry

/-- There exist at most ${n/2 \choose 2k} \cdot 3^k$ \underline{different} $k$-WIS for all
    possible outputs of $\operatorname{Rank}$ on input graph $G$. -/
theorem clm_kltap_bound {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (opt : SimpleGraph.Subgraph G) (h_opt_matching : opt.IsMatching) (k : ℕ) :
    (Finset.filter (fun (I : Finset V) =>
      ∃ (σ : Equiv.Perm V), def_ltap G (Ranking_Algorithm G σ) opt k I)
      (Finset.powerset (Finset.univ : Finset V))).card ≤
    Nat.choose (Fintype.card V / 2) (2*k) * 3^k := by
  -- Proof strategy (LaTeX):
  -- 1. Select 2k edges from opt that will form k aug-3-paths: C(n/2, 2k) choices.
  -- 2. For each such set of 2k opt-edges, at most 3^k ways to select which endpoints form I.
  --    The key combinatorial fact: for each pair of opt-edges forming an aug-3-path,
  --    the two "inner" (R-adjacent) vertices cannot both be in I because I is independent.
  --    Hence at most 3 valid choices per pair.
  --
  -- The main gap: the pairing of opt-edges into aug-3-paths varies with the permutation σ.
  -- A rigorous proof requires showing that across all possible pairings, the total number
  -- of valid I is still bounded by 3^k per choice of 2k opt-edges.
  -- See issue #clm_kltap_bound_gap for the detailed analysis.
  sorry

/-- If `s(u,v)` is an edge of `G`, then at least one endpoint is matched in the Ranking output.
    This follows from the maximality of the Ranking output: if both endpoints were unmatched,
    we could add the edge and obtain a strictly larger matching, contradicting maximality. -/
private lemma ranking_no_edge_unmatched {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (σ : Equiv.Perm V) (u v : V) (h_edge : s(u, v) ∈ G.edgeFinset) :
    u ∈ (Ranking_Algorithm G σ).verts ∨ v ∈ (Ranking_Algorithm G σ).verts := by
  let R := Ranking_Algorithm G σ
  have hR_match : R.IsMatching := Ranking_Algorithm_isMatching G σ
  have hR_max := Ranking_Algorithm_isMaximal G σ
  by_contra! h
  rcases h with ⟨hu, hv⟩
  -- hu: u ∉ R.verts, hv: v ∉ R.verts
  -- Construct M' = R extended with edge s(u,v)
  let M' : G.Subgraph := {
    verts := R.verts ∪ {u, v}
    Adj := fun x y => R.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u)
    adj_sub := by
      intro x y h_adj
      rcases h_adj with (hR | ⟨hx, hy⟩ | ⟨hx, hy⟩)
      · exact R.adj_sub hR
      · rw [hx, hy]; rw [G.mem_edgeFinset] at h_edge; exact h_edge
      · rw [hx, hy]; rw [G.mem_edgeFinset] at h_edge; exact h_edge.symm
    edge_vert := by
      intro x y h_adj
      rcases h_adj with (hR | ⟨hx, hy⟩ | ⟨hx, hy⟩)
      · apply Or.inl; exact R.edge_vert hR
      · rw [hx]; apply Or.inr; simp
      · rw [hx]; apply Or.inr; simp
    symm := by
      intro x y h_adj
      rcases h_adj with (hR | ⟨hx, hy⟩ | ⟨hx, hy⟩)
      · exact Or.inl (R.symm hR)
      · exact Or.inr (Or.inr ⟨hy, hx⟩)
      · exact Or.inr (Or.inl ⟨hy, hx⟩)
  }
  have hR_le_M' : R ≤ M' := by
    refine ⟨?_, ?_⟩
    · intro x hx; apply Or.inl; exact hx
    · intro x y h_adj; exact Or.inl h_adj
  have hM'_match : M'.IsMatching := by
    have h_ne_uv : u ≠ v := by
      intro h_eq; subst h_eq
      have : s(u,u) ∉ G.edgeFinset := by simp
      exact this h_edge
    intro x hx
    rcases hx with (hxR | hxu | hxv)
    · -- x ∈ R.verts
      rcases hR_match hxR with ⟨y, hy, huniq⟩
      refine ⟨y, Or.inl hy, ?_⟩
      intro z hz
      rcases hz with (hzR | ⟨hz_eq_u, hz_eq_v⟩ | ⟨hz_eq_v, hz_eq_u⟩)
      · -- z is R-neighbor
        exact huniq z hzR
      · -- z is the new edge: x = u, z = v, so u ∈ R.verts, contradiction
        exfalso; apply hu; rw [hz_eq_u] at hxR; exact hxR
      · -- z is the new edge: x = v, z = u, contradiction
        exfalso; apply hv; rw [hz_eq_v] at hxR; exact hxR
    · -- x = u
      subst hxu
      refine ⟨v, Or.inr (Or.inl ⟨rfl, rfl⟩), ?_⟩
      intro z hz
      rcases hz with (hzR | ⟨hz1, hz2⟩ | ⟨hz1, hz2⟩)
      · -- z is R-neighbor of u, but u ∉ R.verts
        exfalso; apply hu; exact R.edge_vert hzR
      · -- (u = u ∧ z = v): so z = v
        exact hz2
      · -- (u = v ∧ z = u): u = v, impossible
        exfalso; exact h_ne_uv hz1
    · -- x = v
      subst hxv
      refine ⟨u, Or.inr (Or.inr ⟨rfl, rfl⟩), ?_⟩
      intro z hz
      rcases hz with (hzR | ⟨hz1, hz2⟩ | ⟨hz1, hz2⟩)
      · -- z is R-neighbor of v, but v ∉ R.verts
        exfalso; apply hv; exact R.edge_vert hzR
      · -- (v = u ∧ z = v): v = u, impossible
        exfalso; exact h_ne_uv (hz1.symm)
      · -- (v = v ∧ z = u): z = u
        exact hz2
  have hM'_ne_R : M' ≠ R := by
    intro h_eq
    have h_uv_adj_M' : M'.Adj u v := Or.inr (Or.inl ⟨rfl, rfl⟩)
    have h_uv_adj_R : R.Adj u v := by
      -- from h_eq, M'.Adj = R.Adj
      rw [h_eq] at h_uv_adj_M'
      exact h_uv_adj_M'
    -- But u ∉ R.verts, contradicting edge_vert of R
    apply hu
    exact R.edge_vert h_uv_adj_R
  exact hM'_ne_R (hR_max M' hR_le_M' hM'_match)

/-- If `def_ltap` holds for `Ranking_Algorithm` output, then there exists a bijection
    between the non-I endpoints of the augmenting paths and I such that each non-I vertex
    appears before its counterpart in the permutation.

    **Proof**: From `def_ltap`, we obtain `M` (2k opt-edges) and an involution `f` pairing them.
    For each `e ∈ M`, let `n_e` be the unique non-`I` vertex and `i_e` the unique
    `I`-vertex in `e`.  Define `N := {n_e | e ∈ M}` and `φ(n_e) := i_{f e}`.

    The order property `π(n_e) < π(i_{f e})` is proved by contradiction.
    Injectivity of `φ` follows from `f` being an involution and each edge having a
    unique `I`-vertex.  Surjectivity follows because every `I`-vertex belongs to
    some `M`-edge. -/
private lemma ranking_order_property {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (opt : SimpleGraph.Subgraph G) (k : ℕ) (I : Finset V) (σ : Equiv.Perm V)
    (h_def : def_ltap G (Ranking_Algorithm G σ) opt k I) :
    ∃ (N : Finset V) (φ : V → V),
      N.card = 2*k ∧
      (∀ v ∈ N, v ∉ I) ∧
      (∀ v ∈ N, φ v ∈ I) ∧
      (∀ v ∈ N, (Fintype.equivFin V) (σ.symm v) < (Fintype.equivFin V) (σ.symm (φ v))) ∧
      (∀ v₁ ∈ N, ∀ v₂ ∈ N, φ v₁ = φ v₂ → v₁ = v₂) ∧
      (∀ u ∈ I, ∃ v ∈ N, φ v = u) := by
  -- Proof sketch:
  -- From def_ltap, we have M (2k opt-edges) and involution f.
  -- For each e ∈ M, let i_e be the unique I-vertex in e, and n_e the other vertex.
  -- Define N = {n_e | e ∈ M} and φ(n_e) = i_{f(e)}.
  -- Then |N| = 2k (injectivity from matching property).
  -- The order property π(n_e) < π(i_{f(e)}) follows from the greedy nature of Ranking.
  -- Injectivity and surjectivity of φ follow from f being an involution.
  sorry

/-- A combinatorial lemma: given two disjoint finsets `A` and `B` of equal size `m`,
    and a bijection `φ : A → B`, the fraction of permutations `σ` of `A ∪ B` such that
    `∀ a ∈ A, σ(a) < σ(φ a)` is exactly `(1/2)^m`.

    Here we use the encoding of the permutation via `Equiv.Perm`.  The condition
    `σ(a) < σ(φ a)` is interpreted as: in the linear order on `A ∪ B` induced by `σ`,
    `a` appears before `φ a`. -/
private lemma order_constraints_prob_noB {α : Type*} [Fintype α] [DecidableEq α]
    (A : Finset α) (φ : α → α)
    (h_inj : ∀ a₁ ∈ A, ∀ a₂ ∈ A, φ a₁ = φ a₂ → a₁ = a₂)
    (h_notin : ∀ a ∈ A, φ a ∉ A) :
    ((Finset.filter (fun (σ : Equiv.Perm α) =>
      ∀ a ∈ A, (Fintype.equivFin α) (σ.symm a) < (Fintype.equivFin α) (σ.symm (φ a)))
      Finset.univ).card : ℝ) / (Fintype.card (Equiv.Perm α) : ℝ) = (1/2 : ℝ)^(A.card) := by
  let e := Fintype.equivFin α
  have ha_ne_φa : ∀ a ∈ A, a ≠ φ a := by
    intro a ha h_eq
    have h_contra := h_notin a ha
    rw [← h_eq] at h_contra
    exact h_contra ha
  have swap_fixes : ∀ (x a' b' : α), x ≠ a' → x ≠ b' → (Equiv.swap a' b') x = x := by
    intro x a' b' hxa hxb
    by_cases h : (Equiv.swap a' b') x = x
    · exact h
    · exfalso
      rcases ((Equiv.swap_apply_ne_self_iff (a := a') (b := b') (x := x)).mp h) with ⟨_, h_or⟩
      rcases h_or with (hx | hx)
      · exact hxa hx
      · exact hxb hx
  let good (S : Finset α) : Finset (Equiv.Perm α) :=
    Finset.filter (fun σ => ∀ x ∈ S, e (σ.symm x) < e (σ.symm (φ x))) Finset.univ
  induction A using Finset.induction with
  | empty =>
    simp
  | insert a A' ha_notin_A' IH =>
    -- Restrict hypotheses to A'
    have h_inj' : ∀ a₁ ∈ A', ∀ a₂ ∈ A', φ a₁ = φ a₂ → a₁ = a₂ := by
      intro a₁ ha₁ a₂ ha₂ heq
      apply h_inj a₁ (Finset.mem_insert_of_mem ha₁) a₂ (Finset.mem_insert_of_mem ha₂) heq
    have h_notin' : ∀ a ∈ A', φ a ∉ A' := by
      intro x hx hφx_A'
      apply h_notin x (Finset.mem_insert_of_mem hx)
      exact Finset.mem_insert_of_mem hφx_A'
    -- Properties needed for the involution step
    have h_φa_notin_A : φ a ∉ insert a A' := h_notin a (Finset.mem_insert_self a A')
    have ha_ne_φa' : a ≠ φ a := ha_ne_φa a (Finset.mem_insert_self a A')
    -- For any x ∈ A': key disjointness properties
    have hx_ne_φa : ∀ x ∈ A', x ≠ φ a := by
      intro x hx h_eq
      apply h_φa_notin_A
      rw [← h_eq]
      exact Finset.mem_insert_of_mem hx
    have hφx_ne_a : ∀ x ∈ A', φ x ≠ a := by
      intro x hx h_eq
      apply h_notin x (Finset.mem_insert_of_mem hx)
      rw [h_eq]
      exact Finset.mem_insert_self a A'
    have hφx_ne_φa : ∀ x ∈ A', φ x ≠ φ a := by
      intro x hx h_eq
      have hx_eq_a : x = a := h_inj x (Finset.mem_insert_of_mem hx) a (Finset.mem_insert_self a A') h_eq
      exact ha_notin_A' (hx_eq_a ▸ hx)
    have ha_ne_φa_A' : ∀ a ∈ A', a ≠ φ a := by
      intro x hx; apply ha_ne_φa x; exact Finset.mem_insert_of_mem hx
    -- From IH
    have h_IH_good : ((good A').card : ℝ) / (Fintype.card (Equiv.Perm α) : ℝ) = (1/2 : ℝ)^(A'.card) := by
      simpa [good] using IH h_inj' h_notin' ha_ne_φa_A'
    -- Subset relation
    have h_sub : good (insert a A') ⊆ good A' := by
      intro σ hσ
      rcases Finset.mem_filter.mp hσ with ⟨hσ_univ, hσ_all⟩
      refine Finset.mem_filter.mpr ⟨hσ_univ, ?_⟩
      intro x hx
      apply hσ_all
      exact Finset.mem_insert_of_mem hx
    have h_good_insert_eq : good (insert a A') =
        Finset.filter (fun σ => e (σ.symm a) < e (σ.symm (φ a))) (good A') := by
      ext σ; simp [good]; tauto
    -- Involution f(σ) = swap(a, φ a) * σ
    let f : Equiv.Perm α → Equiv.Perm α := fun σ => Equiv.swap a (φ a) * σ
    have hf_inj : Function.Injective f := by
      intro σ τ h
      simpa [f, mul_assoc] using congrArg (fun g => Equiv.swap a (φ a) * g) h
    -- f maps good A' to good A'
    have hf_maps : ∀ σ, σ ∈ good A' → f σ ∈ good A' := by
      intro σ hσ
      rcases Finset.mem_filter.mp hσ with ⟨hσ_univ, hσ_A'⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      intro x hx
      -- (f σ).symm x = σ.symm x and similarly for φ x
      have h_fσ_symm_x : (f σ).symm x = σ.symm x := by
        calc
          (f σ).symm x = σ.symm ((Equiv.swap a (φ a)) x) := rfl
          _ = σ.symm x := by rw [swap_fixes x a (φ a) (by intro h; exact ha_notin_A' (h ▸ hx)) (hx_ne_φa x hx)]
      have h_fσ_symm_φx : (f σ).symm (φ x) = σ.symm (φ x) := by
        calc
          (f σ).symm (φ x) = σ.symm ((Equiv.swap a (φ a)) (φ x)) := rfl
          _ = σ.symm (φ x) := by rw [swap_fixes (φ x) a (φ a) (hφx_ne_a x hx) (hφx_ne_φa x hx)]
      rw [h_fσ_symm_x, h_fσ_symm_φx]
      exact hσ_A' x hx
    -- f swaps the condition for (a, φ a)
    have hf_swap_cond : ∀ σ : Equiv.Perm α, (e (σ.symm a) < e (σ.symm (φ a))) ↔
        ¬ (e ((f σ).symm a) < e ((f σ).symm (φ a))) := by
      intro σ
      have h_fσ_symm_a : (f σ).symm a = σ.symm (φ a) := by
        calc
          (f σ).symm a = σ.symm ((Equiv.swap a (φ a)) a) := rfl
          _ = σ.symm (φ a) := by rw [Equiv.swap_apply_left]
      have h_fσ_symm_φa : (f σ).symm (φ a) = σ.symm a := by
        calc
          (f σ).symm (φ a) = σ.symm ((Equiv.swap a (φ a)) (φ a)) := rfl
          _ = σ.symm a := by rw [Equiv.swap_apply_right]
      rw [h_fσ_symm_a, h_fσ_symm_φa]
      have h_ne : σ.symm a ≠ σ.symm (φ a) := by
        intro heq; apply ha_ne_φa'; exact σ.injective (by simpa using heq)
      have h_fin_ne : e (σ.symm a) ≠ e (σ.symm (φ a)) := by
        intro heq; apply h_ne; exact e.injective heq
      constructor
      · intro hlt hlt'; exact lt_irrefl _ (lt_trans hlt hlt')
      · intro h_not
        rcases lt_or_gt_of_ne h_fin_ne with (hlt | hlt)
        · exact hlt
        · exfalso; exact h_not hlt
    -- Cardinality argument via f-images
    have hf_image_sub : Finset.image f (good (insert a A')) ⊆ (good A') \ (good (insert a A')) := by
      intro σ hσ
      rcases Finset.mem_image.mp hσ with ⟨τ, hτ, rfl⟩
      have hτ_goodA' : τ ∈ good A' := h_sub hτ
      have hfτ_maps : f τ ∈ good A' := hf_maps τ hτ_goodA'
      have hfτ_not_good : f τ ∉ good (insert a A') := by
        rw [h_good_insert_eq, Finset.mem_filter]
        intro h; rcases h with ⟨_, hcond_fτ⟩
        rw [h_good_insert_eq] at hτ
        have hcond_τ : e (τ.symm a) < e (τ.symm (φ a)) := (Finset.mem_filter.mp hτ).2
        exact ((hf_swap_cond τ).mp hcond_τ) hcond_fτ
      exact Finset.mem_sdiff.mpr ⟨hfτ_maps, hfτ_not_good⟩
    have hf_image_sub' : Finset.image f ((good A') \ (good (insert a A'))) ⊆ good (insert a A') := by
      intro σ hσ
      rcases Finset.mem_image.mp hσ with ⟨τ, hτ, rfl⟩
      rcases Finset.mem_sdiff.mp hτ with ⟨hτ_goodA', hτ_not_good⟩
      rw [h_good_insert_eq]
      have hfτ_maps : f τ ∈ good A' := hf_maps τ hτ_goodA'
      have h_not_cond_τ : ¬ (e (τ.symm a) < e (τ.symm (φ a))) := by
        rw [h_good_insert_eq] at hτ_not_good
        intro h; apply hτ_not_good; exact Finset.mem_filter.mpr ⟨hτ_goodA', h⟩
      have hcond : e ((f τ).symm a) < e ((f τ).symm (φ a)) := by
        by_contra h_not_right
        have h_left : e (τ.symm a) < e (τ.symm (φ a)) := (hf_swap_cond τ).mpr h_not_right
        exact h_not_cond_τ h_left
      exact Finset.mem_filter.mpr ⟨hfτ_maps, hcond⟩
    -- Cardinality equalities
    have h_card_image : (Finset.image f (good (insert a A'))).card = (good (insert a A')).card :=
      Finset.card_image_of_injective _ hf_inj
    have h_card_image' : (Finset.image f ((good A') \ (good (insert a A')))).card =
        ((good A') \ (good (insert a A'))).card :=
      Finset.card_image_of_injective _ hf_inj
    have h_card_eq : (good (insert a A')).card = ((good A') \ (good (insert a A'))).card := by
      apply le_antisymm
      · calc
          (good (insert a A')).card = (Finset.image f (good (insert a A'))).card := by rw [h_card_image]
          _ ≤ ((good A') \ (good (insert a A'))).card := Finset.card_le_card hf_image_sub
      · calc
          ((good A') \ (good (insert a A'))).card =
              (Finset.image f ((good A') \ (good (insert a A')))).card := by rw [h_card_image']
          _ ≤ (good (insert a A')).card := Finset.card_le_card hf_image_sub'
    have h_card_G : (good A').card =
        (good (insert a A')).card + ((good A') \ (good (insert a A'))).card := by
      rw [add_comm, Finset.card_sdiff_add_card_eq_card h_sub]
    rw [h_card_eq] at h_card_G
    -- Hence (good A').card = 2 * (good (insert a A')).card
    have h_card_double : (good A').card = 2 * (good (insert a A')).card := by omega
    -- Now work in ℝ
    have h_card_half : ((good (insert a A')).card : ℝ) = ((good A').card : ℝ) / 2 := by
      have h := h_card_double
      have h' : ((good A').card : ℝ) = 2 * ((good (insert a A')).card : ℝ) := by exact_mod_cast h
      linarith
    have h_card_insert : (insert a A').card = A'.card + 1 := by
      rw [Finset.card_insert_of_notMem ha_notin_A']
    calc
      ((good (insert a A')).card : ℝ) / (Fintype.card (Equiv.Perm α) : ℝ) =
          (((good A').card : ℝ) / 2) / (Fintype.card (Equiv.Perm α) : ℝ) := by rw [h_card_half]
      _ = (((good A').card : ℝ) / (Fintype.card (Equiv.Perm α) : ℝ)) * (1/2) := by ring
      _ = (1/2 : ℝ)^(A'.card) * (1/2) := by rw [h_IH_good]
      _ = (1/2 : ℝ)^((insert a A').card) := by rw [h_card_insert, pow_succ, mul_comm]

private lemma order_constraints_prob {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) (h_disjoint : A ∩ B = ∅) (_A_card_eq_B_card : A.card = B.card)
    (φ : α → α) (h_φ_maps : ∀ a ∈ A, φ a ∈ B) (h_φ_inj : ∀ a₁ ∈ A, ∀ a₂ ∈ A, φ a₁ = φ a₂ → a₁ = a₂)
    (_h_φ_surj : ∀ b ∈ B, ∃ a ∈ A, φ a = b) :
    ((Finset.filter (fun (σ : Equiv.Perm α) =>
      ∀ a ∈ A, (Fintype.equivFin α) (σ.symm a) < (Fintype.equivFin α) (σ.symm (φ a)))
      Finset.univ).card : ℝ) / (Fintype.card (Equiv.Perm α) : ℝ) = (1/2 : ℝ)^(A.card) := by
  have h_notin : ∀ a ∈ A, φ a ∉ A := by
    intro a ha hφa_A
    have hφa_B : φ a ∈ B := h_φ_maps a ha
    have mem : φ a ∈ A ∩ B := Finset.mem_inter.mpr ⟨hφa_A, hφa_B⟩
    rw [h_disjoint] at mem; simp at mem
  exact order_constraints_prob_noB A φ h_φ_inj h_notin

/-- Let $I = \{v_1, v_2, \ldots, v_{2k}\}$ be a set of independent vertices in $G$. Then, the
    vertices in $I$ form a $k$-WIS with probability at most $1/2^{2k}$ in the output of
    $\operatorname{Rank}$. -/
theorem lem_prob_bound {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (opt : SimpleGraph.Subgraph G) (h_opt_matching : opt.IsMatching) (k : ℕ)
    (I : Finset V) (h_indep : G.IsIndepSet I) (h_card : I.card = 2*k) :
    ((Finset.filter (fun (σ : Equiv.Perm V) => def_ltap G (Ranking_Algorithm G σ) opt k I)
      Finset.univ).card : ℝ) / (Fintype.card (Equiv.Perm V) : ℝ) ≤ (1/2 : ℝ)^(2*k) := by
  by_cases hk0 : k = 0
  · subst hk0
    have hI_empty : I = ∅ := by
      have : I.card = 0 := by simpa using h_card
      exact Finset.card_eq_zero.mp this
    subst hI_empty
    -- For k=0, the fraction is at most 1 (since filter count ≤ total), and (1/2)^0 = 1.
    have h_card_filter_le : (Finset.filter (fun (σ : Equiv.Perm V) => def_ltap G (Ranking_Algorithm G σ) opt 0 ∅) Finset.univ).card ≤ Fintype.card (Equiv.Perm V) :=
      Finset.card_filter_le _ _
    have h_nonneg : 0 ≤ (Fintype.card (Equiv.Perm V) : ℝ) := by exact Nat.cast_nonneg _
    have h_pos : 0 < (Fintype.card (Equiv.Perm V) : ℝ) := by exact_mod_cast Fintype.card_pos
    rw [div_le_iff₀ h_pos]
    -- Goal: ↑(filter.card) ≤ ((1/2)^(2*0)) * ↑(total)
    have h_pow_zero : ((1 : ℝ)/2)^(2*(0 : ℕ)) = 1 := by norm_num
    rw [h_pow_zero, one_mul]
    -- Goal: ↑(filter.card) ≤ ↑(total)
    exact_mod_cast h_card_filter_le
  have hpos : 0 < 2*k := by omega
  let good := Finset.filter (fun (σ : Equiv.Perm V) => def_ltap G (Ranking_Algorithm G σ) opt k I) Finset.univ
  have h_good_subset : good ⊆ Finset.filter (fun (σ : Equiv.Perm V) =>
      ∃ (N : Finset V) (φ : V → V),
        N.card = 2*k ∧ (∀ v ∈ N, v ∉ I) ∧ (∀ v ∈ N, φ v ∈ I) ∧
        (∀ v ∈ N, (Fintype.equivFin V) (σ.symm v) < (Fintype.equivFin V) (σ.symm (φ v))) ∧
        (∀ v₁ ∈ N, ∀ v₂ ∈ N, φ v₁ = φ v₂ → v₁ = v₂) ∧ (∀ u ∈ I, ∃ v ∈ N, φ v = u))
      Finset.univ := by
    intro σ hσ
    rcases Finset.mem_filter.mp hσ with ⟨_, h_def⟩
    rcases ranking_order_property G opt k I σ h_def with ⟨N, φ, hN_card, hN_notin, hφ_inI, h_order, h_inj, h_surj⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact ⟨N, φ, hN_card, hN_notin, hφ_inI, h_order, h_inj, h_surj⟩
  have h_card_le : (good.card : ℝ) ≤
      ((Finset.filter (fun (σ : Equiv.Perm V) =>
        ∃ (N : Finset V) (φ : V → V),
          N.card = 2*k ∧ (∀ v ∈ N, v ∉ I) ∧ (∀ v ∈ N, φ v ∈ I) ∧
          (∀ v ∈ N, (Fintype.equivFin V) (σ.symm v) < (Fintype.equivFin V) (σ.symm (φ v))) ∧
          (∀ v₁ ∈ N, ∀ v₂ ∈ N, φ v₁ = φ v₂ → v₁ = v₂) ∧ (∀ u ∈ I, ∃ v ∈ N, φ v = u))
        Finset.univ).card : ℝ) := by
    have h_card_nat : good.card ≤
        (Finset.filter (fun (σ : Equiv.Perm V) =>
        ∃ (N : Finset V) (φ : V → V),
          N.card = 2*k ∧ (∀ v ∈ N, v ∉ I) ∧ (∀ v ∈ N, φ v ∈ I) ∧
          (∀ v ∈ N, (Fintype.equivFin V) (σ.symm v) < (Fintype.equivFin V) (σ.symm (φ v))) ∧
          (∀ v₁ ∈ N, ∀ v₂ ∈ N, φ v₁ = φ v₂ → v₁ = v₂) ∧ (∀ u ∈ I, ∃ v ∈ N, φ v = u))
        Finset.univ).card :=
      Finset.card_le_card h_good_subset
    exact_mod_cast h_card_nat
  -- Now we need to bound the right-hand side by |Π| * (1/2)^(2k).
  -- The LaTeX proof uses a sequential insertion argument:
  --   Process the 2k non-I vertices (N) in reverse order of π.
  --   For each non-I vertex v, its counterpart φ(v) ∈ I must appear after v.
  --   The probability that all constraints are satisfied telescopes to (1/2)^(2k).
  --
  -- The difficulty in formalizing this: φ depends on σ (the permutation itself).
  -- `order_constraints_prob` gives the bound (1/2)^(2k) for a FIXED φ.
  -- Summing over all possible φ gives a union bound of (2k)!·(1/2)^(2k) which is
  -- too large.  The sequential insertion argument avoids this by directly analyzing
  -- the relative order without enumerating φ, but its formalization requires
  -- connecting the σ-dependent φ to the probability space.
  -- See issue #lem_prob_bound_structure.
  sorry

/-- The expected number of $k$-\wis{} in the output of $\operatorname{Rank}$ is at most
    ${n/2 \choose 2k} \cdot (3/4)^k$. -/
theorem lem_upperbound_kwis {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (opt : SimpleGraph.Subgraph G) (h_opt_matching : opt.IsMatching) (k : ℕ) :
    (Finset.sum Finset.univ (fun (σ : Equiv.Perm V) =>
      ((Finset.filter (fun (I : Finset V) =>
        def_ltap G (Ranking_Algorithm G σ) opt k I) (Finset.powerset (Finset.univ : Finset V))).card : ℝ))
      / (Fintype.card (Equiv.Perm V) : ℝ)) ≤
    (Nat.choose (Fintype.card V / 2) (2*k) : ℝ) * ((3/4 : ℝ)^k) := by
  set N := (Fintype.card (Equiv.Perm V) : ℝ) with hN
  set C := (Nat.choose (Fintype.card V / 2) (2*k) : ℝ) with hC
  have hN_pos : 0 < N := by
    rw [hN]
    exact_mod_cast Fintype.card_pos
  -- Using div_le_iff₀ to clear denominator
  rw [div_le_iff₀ hN_pos]
  -- Goal becomes: Σ ≤ (C * (3/4)^k) * N = N * C * (3/4)^k
  -- (commutative ring, we'll rearrange at the end)
  -- Let's define abbreviations
  let A := Finset.univ (α := Equiv.Perm V)
  let B := Finset.powerset (Finset.univ : Finset V)
  set P : Equiv.Perm V → Finset V → Prop := fun σ I => def_ltap G (Ranking_Algorithm G σ) opt k I
    with hP_def
  -- Helper: card of filter as sum of indicators
  have h_card_as_sum (σ : Equiv.Perm V) : ((Finset.filter (P σ) B).card : ℝ) =
      (Finset.sum B (fun I => if P σ I then (1 : ℝ) else 0)) := by
    rw [Finset.natCast_card_filter]
  have h_card_as_sum' (I : Finset V) : ((Finset.filter (fun σ => P σ I) A).card : ℝ) =
      (Finset.sum A (fun σ => if P σ I then (1 : ℝ) else 0)) := by
    rw [Finset.natCast_card_filter]
  -- Double counting: Σ_σ |{I}| = Σ_I |{σ}|
  have h_double_count :
      (Finset.sum A (fun σ => ((Finset.filter (P σ) B).card : ℝ))) =
      (Finset.sum B (fun I => ((Finset.filter (fun σ => P σ I) A).card : ℝ))) := by
    rw [Finset.sum_congr rfl (fun σ _ => h_card_as_sum σ),
      Finset.sum_congr rfl (fun I _ => h_card_as_sum' I)]
    exact Finset.sum_comm
  -- Restrict the B-sum to S = {I | ∃ σ, P σ I}
  let S : Finset (Finset V) := Finset.filter (fun I => ∃ σ, P σ I) B
  have h_restrict : (Finset.sum B (fun I => ((Finset.filter (fun σ => P σ I) A).card : ℝ))) =
      (Finset.sum S (fun I => ((Finset.filter (fun σ => P σ I) A).card : ℝ))) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun I hI => ?_)
    by_cases h : ∃ σ, P σ I
    · simp [h]
    · have h_empty : (Finset.filter (fun σ => P σ I) A) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro σ hσA
        intro hPσ
        exact h ⟨σ, hPσ⟩
      simp [h_empty, h]
  have h_LHS : (Finset.sum A (fun σ => ((Finset.filter (P σ) B).card : ℝ))) =
      (Finset.sum S (fun I => ((Finset.filter (fun σ => P σ I) A).card : ℝ))) := by
    rw [h_double_count, h_restrict]
  rw [h_LHS]
  -- Now bound each term using lem_prob_bound
  have h_prob : ∀ I ∈ S,
      ((Finset.filter (fun σ => P σ I) A).card : ℝ) ≤ N * (((1 : ℝ)/2)^(2*k)) := by
    intro I hI
    rcases Finset.mem_filter.mp hI with ⟨_, hI_ex⟩
    rcases hI_ex with ⟨σ₀, h_def⟩
    have h_card : I.card = 2*k := def_ltap.card_I h_def
    have h_indep : G.IsIndepSet (I : Set V) := def_ltap.isIndepSet h_def
    -- lem_prob_bound gives: count/N ≤ (1/2)^{2k}
    have h_bound := lem_prob_bound G opt h_opt_matching k I h_indep h_card
    -- h_bound: (filter count) / N ≤ (1/2)^{2k}
    -- We want: count ≤ N * (1/2)^{2k}
    -- Using div_le_iff₀ hN_pos on h_bound gives: count ≤ (1/2)^{2k} * N
    rcases (div_le_iff₀ hN_pos).mp h_bound with h_mul
    -- h_mul: count ≤ ((1/2)^{2k}) * N = N * ((1/2)^{2k})
    -- But h_bound is about def_ltap, not P. We need to relate them.
    simpa [hP_def, hN, A, mul_comm] using h_mul
  -- Bound on |S|
  have hS_card_nat : S.card ≤ Nat.choose (Fintype.card V / 2) (2*k) * 3^k :=
    clm_kltap_bound G opt h_opt_matching k
  have hS_card : (S.card : ℝ) ≤ C * ((3 : ℝ)^k) := by
    rw [hC]
    exact_mod_cast hS_card_nat
  -- Sum bound
  calc
    (Finset.sum S (fun I => ((Finset.filter (fun σ => P σ I) A).card : ℝ))) ≤
        (Finset.sum S (fun _ => N * (((1 : ℝ)/2)^(2*k)))) :=
      Finset.sum_le_sum (fun I hI => h_prob I hI)
    _ = (S.card : ℝ) * (N * (((1 : ℝ)/2)^(2*k))) := by simp
    _ = N * ((S.card : ℝ) * (((1 : ℝ)/2)^(2*k))) := by ring
    _ ≤ N * ((C * ((3 : ℝ)^k)) * (((1 : ℝ)/2)^(2*k))) := by
      refine mul_le_mul_of_nonneg_left ?_ (by rw [hN]; exact Nat.cast_nonneg _)
      have h_nonneg_pow : 0 ≤ ((1 : ℝ)/2)^(2*k) := by positivity
      exact mul_le_mul_of_nonneg_right hS_card h_nonneg_pow
    _ = N * C * (((3 : ℝ)^k * (((1 : ℝ)/2)^(2*k)))) := by ring
    _ = N * C * ((3/4 : ℝ)^k) := by
      have h_pow_eq : ((3 : ℝ)^k) * (((1 : ℝ)/2)^(2*k)) = ((3/4 : ℝ)^k) := by
        calc
          ((3 : ℝ)^k) * (((1 : ℝ)/2)^(2*k)) = ((3 : ℝ)^k) * ((((1 : ℝ)/2)^2)^k) := by simp [pow_mul]
          _ = ((3 : ℝ)^k) * (((1 : ℝ)/4)^k) := by norm_num
          _ = ((3/4 : ℝ)^k) := by rw [← mul_pow, mul_div, mul_one]
      rw [h_pow_eq]
    -- Adjust to match goal: N*C*(3/4)^k = (C*(3/4)^k)*N
    _ = (C * ((3/4 : ℝ)^k)) * N := by ring

/-- Numerical inequality: for 0 ≤ c ≤ 0.005,
    `binEntropy(6c) + (1/2 - 3c) * log(3/4) < 0`.
    This is the key numerical fact used in the final theorem. -/
private lemma num_ineq (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 0.005) :
    Real.binEntropy (6*c) + (1/2 - 3*c) * Real.log (3/4) < 0 := by
  have h6c_low : 0 ≤ 6*c := by nlinarith
  have h6c_high : 6*c ≤ 2⁻¹ := by nlinarith
  have hlog_neg : Real.log (3/4) < 0 := by
    refine Real.log_neg ?_ ?_
    · positivity
    · norm_num
  -- f(c) = binEntropy(6c) + (1/2 - 3c)*log(3/4) is strictly increasing on [0, 0.005]
  have h_mono : StrictMonoOn (fun x : ℝ => Real.binEntropy (6*x) + (1/2 - 3*x) * Real.log (3/4))
      (Set.Icc (0 : ℝ) 0.005) := by
    have h1 : StrictMonoOn (fun x : ℝ => Real.binEntropy (6*x)) (Set.Icc (0 : ℝ) 0.005) := by
      intro a ha b hb hlt
      have ha_low : 0 ≤ a := ha.1
      have ha_high : a ≤ 0.005 := ha.2
      have hb_low : 0 ≤ b := hb.1
      have hb_high : b ≤ 0.005 := hb.2
      have ha6 : 6*a ∈ Set.Icc (0 : ℝ) 2⁻¹ := by
        constructor <;> nlinarith
      have hb6 : 6*b ∈ Set.Icc (0 : ℝ) 2⁻¹ := by
        constructor <;> nlinarith
      have hlt6 : 6*a < 6*b := by nlinarith
      exact Real.binEntropy_strictMonoOn ha6 hb6 hlt6
    have h2 : StrictMonoOn (fun x : ℝ => (1/2 - 3*x) * Real.log (3/4)) (Set.Icc (0 : ℝ) 0.005) := by
      intro a ha b hb hlt
      have ha_low : 0 ≤ a := ha.1
      have ha_high : a ≤ 0.005 := ha.2
      have hb_low : 0 ≤ b := hb.1
      have hb_high : b ≤ 0.005 := hb.2
      -- For a < b, we have 1/2 - 3a > 1/2 - 3b
      -- Since log(3/4) < 0, (1/2 - 3a)*log(3/4) < (1/2 - 3b)*log(3/4)
      have hcoeff : 1/2 - 3*b < 1/2 - 3*a := by nlinarith
      nlinarith
    exact h1.add h2
  have hc_mem : c ∈ Set.Icc (0 : ℝ) 0.005 := ⟨hc0, hc1⟩
  have h_max : Real.binEntropy (6*c) + (1/2 - 3*c) * Real.log (3/4) ≤
      Real.binEntropy (6*(0.005 : ℝ)) + (1/2 - 3*(0.005 : ℝ)) * Real.log (3/4) := by
    rcases lt_or_eq_of_le hc1 with (hlt | heq)
    · have h_mem : (0.005 : ℝ) ∈ Set.Icc (0 : ℝ) 0.005 := ⟨by norm_num, by norm_num⟩
      have h_lt := h_mono hc_mem h_mem hlt
      exact h_lt.le
    · subst heq
      rfl
  -- Now compute f(0.005) = binEntropy(0.03) + 0.485*log(3/4)
  have h_bound : Real.binEntropy (0.03 : ℝ) ≤ -(0.03 : ℝ) * Real.log (0.03 : ℝ) + (0.03 : ℝ) := by
    have hpos : 0 < (0.03 : ℝ) := by norm_num
    have hlt1 : (0.03 : ℝ) < 1 := by norm_num
    have h_aux : Real.binEntropy (0.03 : ℝ) = -(0.03 : ℝ) * Real.log (0.03 : ℝ) - (0.97 : ℝ) * Real.log (0.97 : ℝ) := by
      rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
      simp [Real.negMulLog_def]
      ring_nf
    rw [h_aux]
    have h_log_bound : -(0.97 : ℝ) * Real.log (0.97 : ℝ) ≤ (0.03 : ℝ) := by
      have hx : 0 < (0.97 : ℝ) := by norm_num
      have h_log_ineq := Real.one_sub_inv_le_log_of_pos hx
      -- h_log_ineq : 1 - (0.97)⁻¹ ≤ log(0.97)
      -- So log(0.97) ≥ 1 - 1/0.97 = (0.97-1)/0.97 = -0.03/0.97
      -- Hence -log(0.97) ≤ 0.03/0.97
      -- Multiply by 0.97: -0.97*log(0.97) ≤ 0.03
      nlinarith
    nlinarith
  have h_total : Real.binEntropy (0.03 : ℝ) + (0.485 : ℝ) * Real.log (3/4) < 0 := by
    -- Using h_bound, it suffices to show -(0.03)*log(0.03) + 0.03 + 0.485*log(3/4) < 0
    -- Algebraically: = 0.455*log(3/2) + 0.06*log(5/4) + 0.03 - 0.335*log(2) < 0
    have h_goal : -(0.03 : ℝ) * Real.log (0.03 : ℝ) + (0.03 : ℝ) + (0.485 : ℝ) * Real.log (3/4) < 0 := by
      have h_eq : -(0.03 : ℝ) * Real.log (0.03 : ℝ) + (0.03 : ℝ) + (0.485 : ℝ) * Real.log (3/4) =
          (0.455 : ℝ) * Real.log (3/2) + (0.06 : ℝ) * Real.log (5/4) + (0.03 : ℝ) - (0.335 : ℝ) * Real.log 2 := by
        have hlog3 : Real.log (3 : ℝ) = Real.log 2 + Real.log (3/2) := by
          calc
            Real.log (3 : ℝ) = Real.log (2 * (3/2 : ℝ)) := by norm_num
            _ = Real.log 2 + Real.log (3/2 : ℝ) := by rw [Real.log_mul (by norm_num) (by norm_num)]
        have hlog10 : Real.log (10 : ℝ) = 3 * Real.log 2 + Real.log (5/4) := by
          calc
            Real.log (10 : ℝ) = Real.log ((8 : ℝ) * (5/4 : ℝ)) := by norm_num
            _ = Real.log (8 : ℝ) + Real.log (5/4 : ℝ) := by rw [Real.log_mul (by norm_num) (by norm_num)]
            _ = Real.log ((2:ℝ)^3) + Real.log (5/4 : ℝ) := by norm_num
            _ = 3 * Real.log 2 + Real.log (5/4 : ℝ) := by rw [Real.log_pow, Nat.cast_ofNat]
        have hlog003 : Real.log (0.03 : ℝ) = Real.log (3 : ℝ) - 2 * Real.log (10 : ℝ) := by
          calc
            Real.log (0.03 : ℝ) = Real.log ((3 : ℝ) / (100 : ℝ)) := by norm_num
            _ = Real.log (3 : ℝ) - Real.log (100 : ℝ) := by rw [Real.log_div (by norm_num) (by norm_num)]
            _ = Real.log (3 : ℝ) - Real.log ((10 : ℝ)^2) := by norm_num
            _ = Real.log (3 : ℝ) - 2 * Real.log (10 : ℝ) := by rw [Real.log_pow, Nat.cast_ofNat]
        have hlog34 : Real.log (3/4 : ℝ) = Real.log (3 : ℝ) - 2 * Real.log 2 := by
          calc
            Real.log (3/4 : ℝ) = Real.log (3 : ℝ) - Real.log (4 : ℝ) := by rw [Real.log_div (by norm_num) (by norm_num)]
            _ = Real.log (3 : ℝ) - Real.log ((2:ℝ)^2) := by norm_num
            _ = Real.log (3 : ℝ) - 2 * Real.log 2 := by rw [Real.log_pow, Nat.cast_ofNat]
        rw [hlog003, hlog34, hlog3, hlog10]
        ring
      rw [h_eq]
      -- Now we need: 0.455*log(3/2) + 0.06*log(5/4) + 0.03 < 0.335*log(2)
      -- Upper bounds for log(3/2) and log(5/4) via Real.log_div_le_sum_range_add
      have hlog15 : Real.log (3/2 : ℝ) ≤ 2*(1/5 : ℝ) + 2*(1/375 : ℝ) + 2*(1/15625 : ℝ) + 2*(1/75000 : ℝ) := by
        have hx0 : (0 : ℝ) ≤ 1/5 := by norm_num
        have hx1 : (1/5 : ℝ) < 1 := by norm_num
        have h := Real.log_div_le_sum_range_add hx0 hx1 3
        have h_eq15 : ((1 + (1/5 : ℝ)) / (1 - (1/5 : ℝ))) = (3/2 : ℝ) := by norm_num
        rw [h_eq15] at h
        have h_sum : (∑ i ∈ Finset.range 3, ((1/5 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) +
          ((1/5 : ℝ) ^ (2 * 3 + 1) / (1 - ((1/5 : ℝ)^2)))) ≤
          (1/5 : ℝ) + (1/375 : ℝ) + (1/15625 : ℝ) + (1/75000 : ℝ) := by
          norm_num [Finset.sum_range_succ]
        linarith
      have hlog125 : Real.log (5/4 : ℝ) ≤ 2*(1/9 : ℝ) + 2*(1/2187 : ℝ) + 2*(1/295245 : ℝ) + 2*(1/531441 : ℝ) := by
        have hx0 : (0 : ℝ) ≤ 1/9 := by norm_num
        have hx1 : (1/9 : ℝ) < 1 := by norm_num
        have h := Real.log_div_le_sum_range_add hx0 hx1 3
        have h_eq125 : ((1 + (1/9 : ℝ)) / (1 - (1/9 : ℝ))) = (5/4 : ℝ) := by norm_num
        rw [h_eq125] at h
        have h_sum : (∑ i ∈ Finset.range 3, ((1/9 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) +
          ((1/9 : ℝ) ^ (2 * 3 + 1) / (1 - ((1/9 : ℝ)^2)))) ≤
          (1/9 : ℝ) + (1/2187 : ℝ) + (1/295245 : ℝ) + (1/531441 : ℝ) := by
          norm_num [Finset.sum_range_succ]
        linarith
      -- Lower bound for log(2) via Real.sum_range_le_log_div
      have hlog2lb : (0.69 : ℝ) < Real.log 2 := by
        have hx0 : (0 : ℝ) ≤ 1/3 := by norm_num
        have hx1 : (1/3 : ℝ) < 1 := by norm_num
        have h := Real.sum_range_le_log_div hx0 hx1 10
        have h_eq2 : ((1 + (1/3 : ℝ)) / (1 - (1/3 : ℝ))) = (2 : ℝ) := by norm_num
        rw [h_eq2] at h
        -- h: sum ≤ 1/2*log(2), so log(2) ≥ 2*sum
        have h_sum : (0.69 : ℝ) < 2 * (∑ i ∈ Finset.range 10, ((1/3 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1))) := by
          norm_num [Finset.sum_range_succ]
        linarith
      -- Now combine the bounds
      have h_main : (0.455 : ℝ) * Real.log (3/2) + (0.06 : ℝ) * Real.log (5/4) + (0.03 : ℝ) - (0.335 : ℝ) * Real.log 2 < 0 := by
        have h1 : (0.455 : ℝ) * Real.log (3/2) ≤
            (0.455 : ℝ) * (2*(1/5 : ℝ) + 2*(1/375 : ℝ) + 2*(1/15625 : ℝ) + 2*(1/75000 : ℝ)) :=
          mul_le_mul_of_nonneg_left hlog15 (by norm_num)
        have h2 : (0.06 : ℝ) * Real.log (5/4) ≤
            (0.06 : ℝ) * (2*(1/9 : ℝ) + 2*(1/2187 : ℝ) + 2*(1/295245 : ℝ) + 2*(1/531441 : ℝ)) :=
          mul_le_mul_of_nonneg_left hlog125 (by norm_num)
        have h_bound : (0.455 : ℝ) * (2*(1/5 : ℝ) + 2*(1/375 : ℝ) + 2*(1/15625 : ℝ) + 2*(1/75000 : ℝ)) +
            (0.06 : ℝ) * (2*(1/9 : ℝ) + 2*(1/2187 : ℝ) + 2*(1/295245 : ℝ) + 2*(1/531441 : ℝ)) +
            (0.03 : ℝ) - (0.335 : ℝ) * (0.69 : ℝ) < 0 := by
          norm_num
        linarith
      exact h_main
    nlinarith
  have h_final : Real.binEntropy (6*c) + (1/2 - 3*c) * Real.log (3/4) < 0 := by
    have h_val : Real.binEntropy (6*(0.005 : ℝ)) + (1/2 - 3*(0.005 : ℝ)) * Real.log (3/4) =
        Real.binEntropy (0.03 : ℝ) + (0.485 : ℝ) * Real.log (3/4) := by norm_num
    rw [h_val] at h_max
    linarith
  exact h_final

/-- For a matching subgraph `M`, each vertex in `M.verts` is incident to exactly one edge,
    and each edge in `M.edgeSet` has exactly two endpoints. Therefore the number of vertices
    equals twice the number of edges. -/
private lemma matching_card_verts_eq_two_mul_card_edges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (M : SimpleGraph.Subgraph G) (h_match : M.IsMatching) :
    (G.edgeFinset.filter (· ∈ M.edgeSet)).card * 2 = (Finset.filter (· ∈ M.verts) Finset.univ).card := by
  -- Use double-counting via the degree sum argument from even_card.
  -- Key steps:
  -- 1. Each edge in a matching has exactly two distinct endpoints (both in M.verts)
  -- 2. Each vertex in M.verts is incident to exactly one edge (matching property)
  -- 3. Therefore |M.verts| = 2 * |M.edgeSet|
  -- Formalization requires Fintype instances for M.verts, M.edgeSet and relating
  -- M.coe.edgeFinset to G.edgeFinset.filter.
  sorry

/-- The expected approximation ratio of $\operatorname{Rank}$ is at least $0.505$ in general
    graphs. -/
theorem thm_final {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (opt : SimpleGraph.Subgraph G) (h_opt_matching : opt.IsMatching) :
    (Finset.sum Finset.univ (fun (σ : Equiv.Perm V) =>
      (((Finset.filter (· ∈ (Ranking_Algorithm G σ).edgeSet) G.edgeFinset).card : ℝ) /
       (matchingNumber G : ℝ))) / (Fintype.card (Equiv.Perm V) : ℝ)) ≥ 0.505 := by
  -- Proof by contradiction.  Assume the expected ratio is < 0.505.
  by_contra! h_lt
  -- h_lt : expected ratio < 0.505
  -- Let E denote the expected ratio, and set c := E - 1/2 (so c < 0.005).
  set E := (Finset.sum Finset.univ (fun (σ : Equiv.Perm V) =>
    (((Finset.filter (· ∈ (Ranking_Algorithm G σ).edgeSet) G.edgeFinset).card : ℝ) /
     (matchingNumber G : ℝ))) / (Fintype.card (Equiv.Perm V) : ℝ)) with hE_def
  have hE_pos : 1/2 ≤ E := by
    -- For each σ, the Ranking output R_σ is a maximal matching, so |R_σ| ≥ μ(G)/2.
    -- Hence the ratio |R_σ|/μ(G) ≥ 1/2 pointwise, and the average is also ≥ 1/2.
    -- Formal proof: R.verts is a vertex cover (ranking_no_edge_unmatched).
    -- For any matching M, each edge of M intersects R.verts (vertex cover property).
    -- Since M is a matching, distinct edges intersect R.verts at distinct vertices.
    -- Therefore |M.edgeFinset| ≤ |R.verts| = 2*|R.edgeFinset|, so |R| ≥ |M|/2.
    -- Taking M to be a maximum matching (size μ(G)) gives the result.
    have h_one_div_two : (1/2 : ℝ) = (1/2 : ℝ) := rfl
    -- For each σ, let r_σ = |R_σ| / μ(G)
    -- We show r_σ ≥ 1/2 for all σ
    have h_pointwise (σ : Equiv.Perm V) : (1/2 : ℝ) ≤
        (((Finset.filter (· ∈ (Ranking_Algorithm G σ).edgeSet) G.edgeFinset).card : ℝ) /
         (matchingNumber G : ℝ)) := by
      let R := Ranking_Algorithm G σ
      have hR_match : R.IsMatching := Ranking_Algorithm_isMatching G σ
      have hR_cover (u v : V) (h_edge : s(u, v) ∈ G.edgeFinset) : u ∈ R.verts ∨ v ∈ R.verts :=
        ranking_no_edge_unmatched G σ u v h_edge
      -- Get a maximum matching M* with |M*| = μ(G)
      -- Use the definition of matchingNumber as supremum
      -- For simplicity, use the fact that there exists a matching achieving the matching number
      -- (by definition of sSup for ℕ, there is a matching of size matchingNumber)
      sorry
    -- Use the pointwise bound to get the bound on the average
    have h_sum : (Finset.sum Finset.univ (fun (σ : Equiv.Perm V) => (1/2 : ℝ))) ≤
        Finset.sum Finset.univ (fun (σ : Equiv.Perm V) =>
          (((Finset.filter (· ∈ (Ranking_Algorithm G σ).edgeSet) G.edgeFinset).card : ℝ) /
           (matchingNumber G : ℝ))) :=
      Finset.sum_le_sum (fun σ _ => h_pointwise σ)
    have h_sum_left : (Finset.sum Finset.univ (fun (σ : Equiv.Perm V) => (1/2 : ℝ))) =
        (Fintype.card (Equiv.Perm V) : ℝ) * (1/2) := by simp
    have hN_pos : 0 < (Fintype.card (Equiv.Perm V) : ℝ) := by exact_mod_cast Fintype.card_pos
    rw [h_sum_left] at h_sum
    -- h_sum: N*(1/2) ≤ S
    -- Goal: 1/2 ≤ S/N = E
    rw [hE_def]
    -- Need: 1/2 ≤ S/N
    -- Equivalent to: (1/2)*N ≤ S  (multiplying by N>0)
    -- But h_sum is N*(1/2) ≤ S, same thing
    -- Use (div_le_div_right hN_pos).mp? No, we have the opposite direction
    -- Actually: h_sum : N*(1/2) ≤ S, so (1/2) ≤ S/N
    -- This is: (div_le_div_right hN_pos).mpr ?_ gives (N*(1/2))/N ≤ S/N, but that's not what we want
    -- Better: apply (one_le_div ?_).? No.
    -- Use field algebra:
    have h_div : (1/2 : ℝ) ≤ (Finset.sum Finset.univ (fun (σ : Equiv.Perm V) =>
        (((Finset.filter (· ∈ (Ranking_Algorithm G σ).edgeSet) G.edgeFinset).card : ℝ) /
         (matchingNumber G : ℝ)))) / (Fintype.card (Equiv.Perm V) : ℝ) := by
      calc
        (1/2 : ℝ) = ((Fintype.card (Equiv.Perm V) : ℝ) * (1/2 : ℝ)) / (Fintype.card (Equiv.Perm V) : ℝ) := by
          field_simp [hN_pos.ne.symm]
        _ ≤ (Finset.sum Finset.univ (fun (σ : Equiv.Perm V) =>
            (((Finset.filter (· ∈ (Ranking_Algorithm G σ).edgeSet) G.edgeFinset).card : ℝ) /
             (matchingNumber G : ℝ)))) / (Fintype.card (Equiv.Perm V) : ℝ) :=
          div_le_div_of_nonneg_right h_sum (by positivity)
    exact h_div
  set c := E - 1/2 with hc_def
  have hc_low : 0 ≤ c := by
    rw [hc_def]
    linarith [hE_pos]
  have hc_high : c < 0.005 := by
    rw [hc_def]
    linarith
  -- Let n := |V| and define k := ⌊(1/2 - 3c)·n/2⌋ (integrality issue — see below).
  set n := Fintype.card V with hn_def
  -- The LaTeX sets k = (1/2 - 3c)·n/2, but k must be a natural number.
  -- We work with the real value kr := (1/2 - 3c)·n/2 and note that
  -- we can choose c' slightly smaller than c to make k integral while preserving c' ≤ 0.005.
  -- For the formal proof, we assume such a k exists (see issue #integrality).
  set kr := (1/2 - 3*c) * (n : ℝ) / 2 with hkr_def
  have hkr_nonneg : 0 ≤ kr := by
    rw [hkr_def]
    have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    nlinarith
  -- We need a natural k such that (k:ℝ) = kr.  This is the integrality gap.
  -- For now, we assume such a k exists.
  -- Obtain k : ℕ with (k:ℝ) = kr (or at least kr ≤ k ≤ kr+1 with error bounds).
  -- See issue #thm_final_integrality.
  --
  -- After obtaining k, apply the lemmas:
  --   lem_kltap_all_perms → expected number of k-WIS ≥ 1
  --   lem_upperbound_kwis → expected number ≤ C(n/2, 2k)·(3/4)^k
  -- Hence C(n/2, 2k)·(3/4)^k ≥ 1.
  -- Then derive contradiction via binomial coefficient identity, entropy bound, and num_ineq:
  --   C(n/2, 2k) = C(n/2, 6c·n/2) ≤ exp((n/2)·binEntropy(6c))
  --   (3/4)^k = exp(k·log(3/4)) = exp(((1/2-3c)·n/2)·log(3/4))
  -- So 1 ≤ exp((n/2)·[binEntropy(6c) + (1/2-3c)·log(3/4)])
  -- Hence binEntropy(6c) + (1/2-3c)·log(3/4) ≥ 0, contradicting num_ineq.
  sorry
