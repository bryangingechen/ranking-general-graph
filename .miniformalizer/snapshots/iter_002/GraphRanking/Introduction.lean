import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Real.Basic

open Real
open scoped Classical

/-! ## Auxiliary definitions for the Introduction section -/

/-- The matching number μ(G): the size of a maximum matching in G. -/
noncomputable def matchingNumber {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : ℕ :=
  sSup {d | ∃ (M : SimpleGraph.Subgraph G), M.IsMatching ∧
    (G.edgeFinset.filter (· ∈ M.edgeSet)).card = d}

/-- A predicate asserting that a set `S` of edges of `M` is covered by a collection of
    vertex-disjoint length-three augmenting paths w.r.t. matching `M` in `G`.

    Formally, `S` is a subset of `M`'s edges, and there exists a fixed-point-free involution
    `f` on `S` pairing the edges into augmenting paths: each pair `(e, f e)` is connected
    by a `G`-edge between some vertex of `e` and some vertex of `f e`. -/
def IsCoveredByDisjointAug3Paths {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (M : SimpleGraph.Subgraph G) (S : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ S, e ∈ M.edgeSet) ∧
  ∃ (f : Sym2 V → Sym2 V),
    (∀ e ∈ S, f e ∈ S) ∧
    (∀ e ∈ S, f (f e) = e) ∧
    (∀ e ∈ S, f e ≠ e) ∧
    (∀ e ∈ S, ∃ (v w : V), v ∈ e ∧ w ∈ f e ∧ G.Adj v w)

/-! ## Main declarations -/

/-- We first draw a permutation $\pi$ over the vertices uniformly at random. Then, we iterate over
the vertices in order of $\pi$, and match each vertex to its first unmatched neighbor, again in the
order of $\pi$, if any. We use $\pi(v)$ to denote the position of vertex $v$ in the permutation
selected by \rnk{}. -/
noncomputable def Ranking_Algorithm {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (perm : Equiv.Perm V) : SimpleGraph.Subgraph G :=
  let enum := Fintype.equivFin V
  let vertices : List V :=
    ((Finset.univ : Finset V).toList).mergeSort (fun v w => enum (perm.symm v) < enum (perm.symm w))
  let step (acc : Finset V × Finset (Sym2 V)) (v : V) : Finset V × Finset (Sym2 V) :=
    if h : v ∈ acc.1 then acc else
    match vertices.find? (fun u => s(v, u) ∈ G.edgeFinset && !(u ∈ acc.1)) with
    | none => acc
    | some u => ({v, u} ∪ acc.1, insert (s(v, u)) acc.2)
  let (_, edges) := vertices.foldl step (∅, ∅)
  {
    verts := {v | ∃ w, s(v, w) ∈ edges}
    Adj := fun v w => s(v, w) ∈ edges ∧ s(v, w) ∈ G.edgeFinset
    adj_sub := by
      intro v w h
      rcases h with ⟨_, hmem⟩
      rw [G.mem_edgeFinset, G.mem_edgeSet] at hmem
      exact hmem
    edge_vert := by
      intro v w h
      rcases h with ⟨he, _⟩
      exact ⟨w, he⟩
    symm := by
      intro v w h
      rcases h with ⟨he, hg⟩
      have he' : s(w, v) ∈ edges := by
        simpa [Sym2.eq_swap] using he
      have hg' : s(w, v) ∈ G.edgeFinset := by
        simpa [Sym2.eq_swap] using hg
      exact ⟨he', hg'⟩
  }

/-- The output of the Ranking Algorithm is a matching. -/
theorem Ranking_Algorithm_isMatching {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (perm : Equiv.Perm V) : (Ranking_Algorithm G perm).IsMatching := by
  -- Extract the key components
  let enum := Fintype.equivFin V
  let vertices : List V :=
    ((Finset.univ : Finset V).toList).mergeSort (fun v w => enum (perm.symm v) < enum (perm.symm w))
  -- Define step and the foldl explicitly
  let step (acc : Finset V × Finset (Sym2 V)) (v : V) : Finset V × Finset (Sym2 V) :=
    if h : v ∈ acc.1 then acc else
    match vertices.find? (fun u => s(v, u) ∈ G.edgeFinset && !(u ∈ acc.1)) with
    | none => acc
    | some u => ({v, u} ∪ acc.1, insert (s(v, u)) acc.2)
  let final_acc := vertices.foldl step (∅, ∅)
  let edges := final_acc.2
  -- Lemma: if find? returns some a, the condition holds for a
  have h_find_prop {l : List V} {p : V → Bool} {a : V} (h : l.find? p = some a) : p a := by
    induction l with
    | nil => simp at h
    | cons x xs ih =>
      have h_find : (x :: xs).find? p = (match p x with | true => some x | false => xs.find? p) := by rfl
      rw [h_find] at h
      by_cases hpx : p x
      · have hpx' : p x = true := by simpa using hpx
        rw [hpx'] at h
        have hx_eq_a : x = a := by simpa using h
        rw [← hx_eq_a]
        exact hpx
      · have hpx' : p x = false := by simpa using hpx
        rw [hpx'] at h
        exact ih h
  -- Invariant for the accumulator
  let Inv (acc : Finset V × Finset (Sym2 V)) : Prop :=
    (∀ v, v ∈ acc.1 ↔ ∃ w, s(v, w) ∈ acc.2) ∧
    (∀ v w₁ w₂, s(v, w₁) ∈ acc.2 → s(v, w₂) ∈ acc.2 → w₁ = w₂) ∧
    (∀ e ∈ acc.2, e ∈ G.edgeFinset)
  have h_inv_base : Inv (∅, ∅) := by
    refine ⟨?_, ?_, ?_⟩
    · intro v; simp
    · intro v w₁ w₂; simp
    · intro e; simp
  -- Key lemma: step preserves Inv
  have h_step_preserves : ∀ (acc : Finset V × Finset (Sym2 V)) (v : V),
      Inv acc → Inv (step acc v) := by
    intro acc v ⟨h_cov, h_uniq, h_G⟩
    -- Analyze step acc v by cases
    by_cases hv : v ∈ acc.1
    · -- step does nothing
      have h_step : step acc v = acc := by
        unfold step
        simp [hv]
      rw [h_step]
      exact ⟨h_cov, h_uniq, h_G⟩
    · -- v ∉ acc.1
      have hx_noedge : ∀ w, s(v, w) ∉ acc.2 := by
        intro w hw
        apply hv
        exact (h_cov v).mpr ⟨w, hw⟩
      -- Now we need to consider the find? result
      -- But the step function uses find? on `vertices`
      -- We need to reason about the possibilities
      -- Instead of splitting the step function, we use the following:
      -- If find? returns none, step acc v = acc
      -- If find? returns some u, step acc v = ({v,u} ∪ acc.1, insert s(v,u) acc.2)
      -- We analyze both cases
      have h_step_eq : step acc v =
          (match vertices.find? (fun u => s(v, u) ∈ G.edgeFinset && !(u ∈ acc.1)) with
          | none => acc
          | some u => ({v, u} ∪ acc.1, insert (s(v, u)) acc.2)) := by
        unfold step
        simp [hv]
      rw [h_step_eq]
      -- Now split on the find? result
      cases h_find_res : vertices.find? (fun u => s(v, u) ∈ G.edgeFinset && !(u ∈ acc.1)) with
      | none =>
        -- No change
        exact ⟨h_cov, h_uniq, h_G⟩
      | some u =>
        -- Found neighbor u
        have h_cond : s(v, u) ∈ G.edgeFinset ∧ u ∉ acc.1 := by
          have hp : (fun u' => s(v, u') ∈ G.edgeFinset && !(u' ∈ acc.1)) u := h_find_prop h_find_res
          simpa using hp
        have hu_noedge : ∀ w, s(u, w) ∉ acc.2 := by
          intro w hw
          apply h_cond.2
          exact (h_cov u).mpr ⟨w, hw⟩
        -- New state: ({v, u} ∪ acc.1, insert (s(v, u)) acc.2)
        have h_cov' : ∀ z, z ∈ ({v, u} ∪ acc.1) ↔ ∃ w, s(z, w) ∈ insert (s(v, u)) acc.2 := by
          intro z
          have h_mem : z ∈ ({v, u} ∪ acc.1) ↔ z = v ∨ z = u ∨ z ∈ acc.1 := by
            simp [Finset.mem_insert]
          rw [h_mem]
          constructor
          · intro hz; rcases hz with (hz_v | hz_u | hz_in)
            · rw [hz_v]; exact ⟨u, Finset.mem_insert_self _ _⟩
            · rw [hz_u]
              have h_edge : s(u, v) ∈ insert (s(v, u)) acc.2 := by
                rw [Sym2.eq_swap]
                exact Finset.mem_insert_self _ _
              exact ⟨v, h_edge⟩
            · rcases (h_cov z).mp hz_in with ⟨w, hw⟩
              exact ⟨w, Finset.mem_insert_of_mem hw⟩
          · intro ⟨w, hw⟩
            rcases Finset.mem_insert.mp hw with (heq | hw')
            · rcases (Sym2.eq_iff.mp heq) with (⟨hz_v, hw_u⟩ | ⟨hz_u, hw_v⟩)
              · rw [hz_v]; left; rfl
              · rw [hz_u]; right; left; rfl
            · have hz_in : z ∈ acc.1 := (h_cov z).mpr ⟨w, hw'⟩
              right; right; exact hz_in
        have h_uniq' : ∀ z w₁ w₂, s(z, w₁) ∈ insert (s(v, u)) acc.2 → s(z, w₂) ∈ insert (s(v, u)) acc.2 → w₁ = w₂ := by
          intro z w₁ w₂ h₁ h₂
          rcases Finset.mem_insert.mp h₁ with (heq₁ | hold₁)
          · -- s(z,w₁) = s(v,u)
            rcases Finset.mem_insert.mp h₂ with (heq₂ | hold₂)
            · -- both equal s(v,u)
              have heq_sym : s(z, w₁) = s(z, w₂) := by rw [heq₁, heq₂]
              rcases (Sym2.eq_iff.mp heq_sym) with (⟨hz, hw⟩ | ⟨hz, hw⟩)
              · exact hw
              · rw [hz] at hw; exact hw
            · -- s(z,w₁) = s(v,u), s(z,w₂) ∈ acc.2
              rcases (Sym2.eq_iff.mp heq₁) with (⟨hz_v, hw_u⟩ | ⟨hz_u, hw_v⟩)
              · rw [hz_v] at hold₂; exact absurd hold₂ (hx_noedge w₂)
              · rw [hz_u] at hold₂; exact absurd hold₂ (hu_noedge w₂)
          · -- s(z,w₁) ∈ acc.2
            rcases Finset.mem_insert.mp h₂ with (heq₂ | hold₂)
            · -- s(z,w₂) = s(v,u)
              rcases (Sym2.eq_iff.mp heq₂) with (⟨hz_v, hw_u⟩ | ⟨hz_u, hw_v⟩)
              · rw [hz_v] at hold₁; exact absurd hold₁ (hx_noedge w₁)
              · rw [hz_u] at hold₁; exact absurd hold₁ (hu_noedge w₁)
            · -- both old
              exact h_uniq z w₁ w₂ hold₁ hold₂
        have h_G' : ∀ e ∈ insert (s(v, u)) acc.2, e ∈ G.edgeFinset := by
          intro e he
          rcases Finset.mem_insert.mp he with (rfl | he')
          · exact h_cond.1
          · exact h_G e he'
        exact ⟨h_cov', h_uniq', h_G'⟩
  -- Foldl induction
  have h_final : Inv (vertices.foldl step (∅, ∅)) := by
    have h_foldl : ∀ (l : List V) (a : Finset V × Finset (Sym2 V)), Inv a → Inv (l.foldl step a) := by
      intro l
      induction l with
      | nil => intro a ha; exact ha
      | cons x xs ih =>
        intro a ha
        rw [List.foldl]
        have ha_step : Inv (step a x) := h_step_preserves a x ha
        exact ih (step a x) ha_step
    exact h_foldl vertices (∅, ∅) h_inv_base
  rcases h_final with ⟨h_cov, h_uniq, h_G⟩
  -- Now prove the main statement
  have h_edge_in_G : ∀ e ∈ edges, e ∈ G.edgeFinset := by
    intro e he; dsimp [edges, final_acc] at he; exact h_G e he
  intro v hv
  rcases hv with ⟨w, hw⟩
  dsimp [edges, final_acc] at hw
  refine ⟨w, ⟨hw, h_edge_in_G (s(v, w)) hw⟩, ?_⟩
  intro w' ⟨hw', _⟩
  dsimp [edges, final_acc] at hw'
  exact (h_uniq v w w' hw hw').symm

/-- The output of the Ranking Algorithm is a maximal matching. -/
theorem Ranking_Algorithm_isMaximal {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (perm : Equiv.Perm V) : ∀ (M' : SimpleGraph.Subgraph G),
    (Ranking_Algorithm G perm) ≤ M' → M'.IsMatching → M' = Ranking_Algorithm G perm := by
  sorry

/-- Let $\alpha \geq 0$ and $M$ be a maximal matching of $G$ such that
$|M| \leq (1/2 + \alpha) \cdot \mu(G)$. Then, at least $(1/2 - 3\alpha)\cdot \mu(G)$ edges of $M$
are in disjoint, length-three augmenting paths. -/
theorem prop_aug3_path_bound {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (M : SimpleGraph.Subgraph G) (hM : M.IsMatching) (hM_maximal : ∀ (M' : SimpleGraph.Subgraph G),
    M ≤ M' → M'.IsMatching → M' = M) (α : ℝ) (hα : α ≥ 0)
    (h_size : ((Finset.filter (· ∈ M.edgeSet) G.edgeFinset).card : ℝ) ≤
      (1/2 + α) * (matchingNumber G : ℝ)) :
    ∃ (S : Finset (Sym2 V)), (∀ e ∈ S, e ∈ M.edgeSet) ∧
    IsCoveredByDisjointAug3Paths G M S ∧
    (S.card : ℝ) ≥ (1/2 - 3 * α) * (matchingNumber G : ℝ) := by
  sorry

/-- Let $a_1, a_2, \ldots, a_n$ be $n$ positive integers such that $\sum_{i = 1}^n a_i = m$.
Then, for a positive integer $x$,  $\sum_{i=1}^n {a_i \choose x}$ is minimized when
$\{a_1,\ldots, a_n\} = \{\lfloor m/n \rfloor , \lceil m/n \rceil\}$. -/
theorem prop_bionomila_minimize {n m x : ℕ} (hn : n > 0) (hx : x > 0) (a : ℕ → ℕ)
    (hpos : ∀ i, i < n → a i > 0) (hsum : (Finset.sum (Finset.range n) a) = m) :
    (Finset.sum (Finset.range n) fun i => Nat.choose (a i) x) ≥
      (let q := m / n;
       let r := m % n;
       (n - r) * Nat.choose q x + r * Nat.choose (q + 1) x) := by
  sorry

/-- Let $n$ and $\alpha n$ be two positive integers and $1/n \leq \alpha \leq 1/2$. Then, we have
${n \choose \alpha n} \leq 2^{nH(\alpha)}$ where
$H(\alpha) = -\alpha \cdot \log_2(\alpha) - (1-\alpha) \cdot \log_2 (1 - \alpha)$. -/
theorem prop_entropy_approximation (n αn : ℕ) (hn : n > 0) (hαn : αn > 0)
    (hα_lower : (1 : ℝ) / n ≤ (αn : ℝ) / n) (hα_upper : (αn : ℝ) / n ≤ 1/2) :
    (Nat.choose n αn : ℝ) ≤ Real.exp (n * binEntropy ((αn : ℝ) / n)) := by
  sorry
