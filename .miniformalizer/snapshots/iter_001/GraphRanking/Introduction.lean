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
  let R := Ranking_Algorithm G perm
  let enum := Fintype.equivFin V
  let vertices : List V :=
    ((Finset.univ : Finset V).toList).mergeSort (fun v w => enum (perm.symm v) < enum (perm.symm w))
  let step (acc : Finset V × Finset (Sym2 V)) (v : V) : Finset V × Finset (Sym2 V) :=
    if h : v ∈ acc.1 then acc else
    match vertices.find? (fun u => s(v, u) ∈ G.edgeFinset && !(u ∈ acc.1)) with
    | none => acc
    | some u => ({v, u} ∪ acc.1, insert (s(v, u)) acc.2)
  let final_acc := vertices.foldl step (∅, ∅)
  have hR_verts_eq : R.verts = {v | ∃ w, s(v, w) ∈ final_acc.2} := rfl
  have hR_adj_eq : R.Adj = fun v w => s(v, w) ∈ final_acc.2 ∧ s(v, w) ∈ G.edgeFinset := rfl
  have h_mem : ∀ v, v ∈ vertices := by
    intro v; simpa [vertices] using (Finset.mem_sort (Finset.univ : Finset V)
      (fun v w => enum (perm.symm v) < enum (perm.symm w))).mpr (Finset.mem_univ v)
  -- 1. Monotonicity: step only adds
  have h_step_mono (a : Finset V × Finset (Sym2 V)) (v : V) : a.1 ⊆ (step a v).1 := by
    unfold step
    by_cases hv : v ∈ a.1
    · simp [hv]
    · simp [hv]
      split
      · exact Finset.Subset.refl _
      · intro x hx; simp [hx]
  have h_foldl_mono (l : List V) (a : Finset V × Finset (Sym2 V)) : a.1 ⊆ (l.foldl step a).1 := by
    induction l generalizing a with
    | nil => exact Finset.Subset.refl _
    | cons x xs ih =>
      rw [List.foldl]; exact Finset.Subset.trans (h_step_mono a x) (ih _)
  -- 2. Covering invariant by induction on foldl
  let cov (acc : Finset V × Finset (Sym2 V)) : Prop := ∀ v, v ∈ acc.1 ↔ ∃ w, s(v, w) ∈ acc.2
  have h_cov_base : cov (∅, ∅) := by intro v; simp
  have h_cov_step : ∀ (acc : Finset V × Finset (Sym2 V)) (x : V), cov acc → cov (step acc x) := by
    intro acc x h_cov
    by_cases hx : x ∈ acc.1
    · -- x already matched, step does nothing
      have h_step : step acc x = acc := by
        dsimp [step]; simp [hx]
      rw [h_step]; exact h_cov
    · -- x not matched, step may add x and its match
      have h_step : step acc x =
          (match vertices.find? (fun u => s(x, u) ∈ G.edgeFinset && !(u ∈ acc.1)) with
          | none => acc
          | some u => ({x, u} ∪ acc.1, insert (s(x, u)) acc.2)) := by
        dsimp [step]; simp [hx]
      rw [h_step]
      cases h_find : vertices.find? (fun u => s(x, u) ∈ G.edgeFinset && !(u ∈ acc.1)) with
      | none => simpa using h_cov
      | some u0 =>
        -- Goal: cov ({x, u0} ∪ acc.1, insert (s(x, u0)) acc.2)
        intro v
        have h_cov_v := h_cov v
        have h_left : v ∈ ({x, u0} ∪ acc.1) ↔ v = x ∨ v = u0 ∨ v ∈ acc.1 := by simp
        rw [h_left]
        constructor
        · rintro (rfl | rfl | hv)
          · exact ⟨u0, Finset.mem_insert_self _ _⟩
          · exact ⟨x, by simp⟩
          · rcases h_cov_v.mp hv with ⟨w, hw⟩; exact ⟨w, Finset.mem_insert_of_mem hw⟩
        · rintro ⟨w, hw⟩
          rcases Finset.mem_insert.mp hw with (heq | hw')
          · rcases Sym2.eq_iff.mp heq with (⟨h1, h2⟩ | ⟨h1, h2⟩)
            · rw [h1]; left; rfl
            · rw [h1]; right; left; rfl
          · have hv := h_cov_v.mpr ⟨w, hw'⟩; right; right; exact hv
  have h_cov_foldl : ∀ (l : List V) (a : Finset V × Finset (Sym2 V)), cov a → cov (l.foldl step a) := by
    intro l; induction l with
    | nil => intro a ha; exact ha
    | cons x xs ih => intro a ha; rw [List.foldl]; exact ih (step a x) (h_cov_step a x ha)
  have h_cov_final : cov final_acc := h_cov_foldl vertices (∅, ∅) h_cov_base
  have h_equiv : ∀ v, v ∈ final_acc.1 ↔ v ∈ R.verts := by
    intro v; rw [hR_verts_eq, Set.mem_setOf_eq]; exact h_cov_final v
  -- 3. Key lemma: unmatched → all G-neighbors matched
  have h_unmatched_neighbors (v : V) (hv : v ∉ final_acc.1) (u : V) (h_edge : s(v, u) ∈ G.edgeFinset) :
      u ∈ final_acc.1 := by
    rcases List.append_of_mem (h_mem v) with ⟨pre, suf, h_eq⟩
    let acc_pre := pre.foldl step (∅, ∅)
    have h_final_unfold : final_acc = suf.foldl step (step acc_pre v) := by
      dsimp [final_acc]
      rw [h_eq]
      simp [List.foldl_append, acc_pre, List.foldl]
    have hv_not_step : v ∉ (step acc_pre v).1 := by
      intro h; apply hv; rw [h_final_unfold]; exact h_foldl_mono suf (step acc_pre v) h
    by_cases hv'_acc : v ∈ acc_pre.1
    · -- If v ∈ acc_pre.1, then v ∈ final_acc.1 by monotonicity, contradiction with hv
      have h_v_final : v ∈ final_acc.1 := by
        rw [h_final_unfold]
        have h : (step acc_pre v).1 ⊆ (suf.foldl step (step acc_pre v)).1 :=
          h_foldl_mono suf (step acc_pre v)
        -- Actually we need v ∈ acc_pre.1 → v ∈ (step acc_pre v).1 → v ∈ final_acc.1
        have h_step_acc : acc_pre.1 ⊆ (step acc_pre v).1 := h_step_mono acc_pre v
        exact h (h_step_acc hv'_acc)
      exact absurd h_v_final hv
    · -- v ∉ acc_pre.1, so step acc_pre v expands to the match
      have h_step_eq : step acc_pre v =
          (match vertices.find? (fun w => s(v, w) ∈ G.edgeFinset && !(w ∈ acc_pre.1)) with
          | none => acc_pre
          | some w => ({v, w} ∪ acc_pre.1, insert (s(v, w)) acc_pre.2)) := by
        dsimp [step]; simp [hv'_acc]
      rw [h_step_eq] at hv_not_step
      cases h_find : vertices.find? (fun w => s(v, w) ∈ G.edgeFinset && !(w ∈ acc_pre.1)) with
      | none =>
        rw [h_find] at hv_not_step
        -- hv_not_step: v ∉ acc_pre.1 (contradicts hv'_acc, but we know hv'_acc)
        have h_all := (List.find?_eq_none.mp h_find)
        have h_no_unmatched_neighbor : ∀ w ∈ vertices, w ∉ acc_pre.1 → s(v, w) ∉ G.edgeFinset := by
          intro w hw hw_not
          have h := h_all w hw
          by_contra! h_edge'
          have h_true : (s(v, w) ∈ G.edgeFinset && !(w ∈ acc_pre.1)) = true := by
            simp [h_edge', hw_not]
          exact h h_true
        by_cases hu_in_acc : u ∈ acc_pre.1
        · rw [h_final_unfold]
          apply h_foldl_mono suf (step acc_pre v)
          apply h_step_mono acc_pre v
          exact hu_in_acc
        · exact absurd h_edge (h_no_unmatched_neighbor u (h_mem u) hu_in_acc)
      | some u0 =>
        rw [h_find] at hv_not_step
        simp at hv_not_step
  -- 4. No edge between two vertices outside R.verts
  have h_no_edge_unmatched : ∀ u v, s(u, v) ∈ G.edgeFinset → u ∈ R.verts ∨ v ∈ R.verts := by
    intro u v h_edge
    by_cases hu : u ∈ final_acc.1
    · exact Or.inl ((h_equiv u).mp hu)
    · exact Or.inr ((h_equiv v).mp (h_unmatched_neighbors u hu v h_edge))
  -- 5. Main proof: M' = R
  intro M' h_le h_match
  have h_verts_eq : M'.verts = R.verts := by
    apply Set.Subset.antisymm
    · intro v hvM
      by_contra! hv_notR
      rcases h_match hvM with ⟨w, h_adj, huniq⟩
      have h_edgeG : s(v, w) ∈ G.edgeFinset := by
        rw [G.mem_edgeFinset]; exact M'.adj_sub h_adj
      have hwR : w ∈ R.verts := (h_no_edge_unmatched v w h_edgeG).resolve_left hv_notR
      -- w has unique R-neighbor w'
      rcases (Ranking_Algorithm_isMatching G perm) hwR with ⟨w', h_adjR, huniqR⟩
      -- R.Adj w w' → M'.Adj w w'
      have h_adjM'_w' : M'.Adj w w' := h_le.2 h_adjR
      -- In M', w also has neighbor v
      have h_adjM'_sw : M'.Adj w v := M'.symm h_adj
      -- M' is a matching, so v and w' must be the same
      rcases h_match (M'.edge_vert h_adjM'_sw) with ⟨x, hxM, huniqM⟩
      -- huniqM: ∀ y, M'.Adj w y → y = x
      have hv_eq_x : v = x := huniqM v h_adjM'_sw
      have hw'_eq_x : w' = x := huniqM w' h_adjM'_w'
      -- Therefore v = w'
      have h_v_eq_w' : v = w' := by rw [hv_eq_x, hw'_eq_x]
      -- w' ∈ R.verts (by R.Adj w w')
      have hw'_in_R : w' ∈ R.verts := by
        rw [hR_adj_eq] at h_adjR; rcases h_adjR with ⟨he, _⟩
        rw [hR_verts_eq, Set.mem_setOf_eq]
        rw [Sym2.eq_swap] at he
        exact ⟨w, he⟩
      rw [h_v_eq_w'] at hv_notR
      exact hv_notR hw'_in_R
    · exact h_le.1
  have h_adj_eq : M'.Adj = R.Adj := by
    ext v w; constructor
    · intro h_adjM
      have hvR : v ∈ R.verts := by rw [← h_verts_eq]; exact M'.edge_vert h_adjM
      have hwR : w ∈ R.verts := by
        rw [← h_verts_eq]; apply M'.edge_vert; exact M'.symm h_adjM
      -- v has unique R-neighbor v'
      rcases (Ranking_Algorithm_isMatching G perm) hvR with ⟨v', h_adjR, huniqR⟩
      -- R.Adj v v' → M'.Adj v v'
      have h_adjM'_v' : M'.Adj v v' := h_le.2 h_adjR
      -- In M', v also has neighbor w
      rcases h_match (M'.edge_vert h_adjM'_v') with ⟨x, hxM, huniqM⟩
      have hw_eq_x : w = x := huniqM w h_adjM
      have hv'_eq_x : v' = x := huniqM v' h_adjM'_v'
      -- Therefore w = v'
      have h_w_eq_v' : w = v' := by rw [hw_eq_x, hv'_eq_x]
      rw [h_w_eq_v']
      exact h_adjR
    · simpa [R] using h_le.2 (v := v) (w := w)
  -- M' = R follows from equalities on verts and Adj
  have h_ext : M' = R := by
    ext x
    · -- verts equality: M'.verts x ↔ R.verts x
      rw [h_verts_eq]
    · -- Adj equality: M'.Adj x = R.Adj x
      -- The goal is M'.Adj x y ↔ R.Adj x y for all y (already introduced by ext)
      rw [h_adj_eq]
  exact h_ext

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
