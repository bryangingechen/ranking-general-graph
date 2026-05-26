# Stage 2b issue tracker

Cumulative across iterations. Each entry has a status header (`[open]` / `[closed: reason]`).

[open] **Prover iteration 2026-05-26 (~07:45): summary**
No proofs closed. Deep analysis of all 5 remaining sorries confirmed they are blocked by structural/mathematical issues that require Reviewer intervention. Key findings:

1. **`ranking_order_property` (line 307)**: The vertex extraction from Sym2 is doable via `Mem.other'` / `Sym2.mem_iff`. The order property π(n_e) < π(i_{f e}) has a clean mathematical proof via contradiction using the greedy nature of Ranking (see detailed proof sketch in docstring). However, formalization requires duplicating the ~200-line foldl infrastructure from `Ranking_Algorithm_isMaximal`. Adding `h_opt_matching` to the lemma signature would simplify the vertex-disjointness argument (since M-edges ⊆ opt.edgeSet and opt is a matching, M-edges are vertex-disjoint).

2. **`clm_kltap_bound` (line 140)**: The "at most 3 per pair" argument is valid for a FIXED involution pairing, but the pairing varies with σ. Across all pairings, the naive union bound gives (2k-1)!!·3^k, not 3^k. The sets {I consistent with pairing H} are DISJOINT for different H (since I determines H via the R-edges). Thus the LaTeX proof is genuinely incomplete — a different combinatorial argument is needed. Possible approaches: (a) show that not all perfect matchings on the non-I vertices are "greedy-realizable" by Ranking, (b) use extremal set theory on {0,1}^{2k} with constraints.

3. **`lem_prob_bound` (line 534)**: The current approach (bound good by ∃N,φ union) is structurally flawed because the union over all (N,φ) pairs gives a bound of C(n-2k,2k)·(2k)!·(1/2)^{2k} which is much too large. The LaTeX sequential insertion argument avoids this but requires the counterpart mapping C to be fixed (σ-independent). Since C depends on σ through the R-edge pairing, a correct formalization must either (a) prove C is σ-independent, or (b) find a direct probability argument that doesn't fix C.

4. **`lem_kltap_all_perms` (line 55)**: The algebraic proof depends on `prop_aug3_path_bound` (edges vs paths factor-of-2), `prop_bionomila_minimize` (integer-valued), and `Ranking_Algorithm_isMaximal` (for the augmenting path bound). The μ(G)=|V|/2 assumption in the LaTeX proof also needs addressing.

5. **`thm_final` (line 1049)**: The h_mu_zero case (μ(G)=0) makes the theorem false as stated, since 0 ≥ 0.505 is false for edgeless graphs. Requires either adding `0 < matchingNumber G` hypothesis or excluding the trivial case.

**File state**: Compiles cleanly (0 errors, 5 `sorry` warnings). All private lemmas except `ranking_order_property` are fully proved.

[open] **Reviewer audit (2026-05-26, iteration ~07:45)**
Manifest coverage: ✅ all 10 items present. Build: 0 errors, 5 `sorry` warnings in TheAnalysis.lean, 3 `sorry` warnings in Introduction.lean (prior, OK). No `axiom` usage. Signatures match LaTeX.

Novel declarations (6 total):
- `def_ltap` — ✅ fully implemented (definition)
- `lem_kltap_all_perms` — ❌ sorry (k=0 done, k>0 blocked)
- `clm_kltap_bound` — ❌ sorry (k=0 done, k>0 blocked)
- `lem_prob_bound` — ❌ sorry (k=0 done, k>0 blocked)
- `lem_upperbound_kwis` — ✅ fully proved
- `thm_final` — ❌ sorry (hE_pos done except h_mu_zero; final algebraic part blocked)

Prior declarations (4 total): all present, sorry OK.

Private lemmas: `ranking_order_property` still sorry. All others (`ranking_no_edge_unmatched`, `order_constraints_prob`, `order_constraints_prob_noB`, `matching_card_verts_eq_two_mul_card_edges`, `card_edgeSet_le_card_verts_of_vertexCover`, `num_ineq`) are fully proved.

No progress this iteration — the Prover analyzed all remaining blockers but couldn't close any proofs. The blockers are:
1. `thm_final`: false for μ(G)=0 (needs signature change)
2. `clm_kltap_bound`: LaTeX proof incomplete (union over pairings)
3. `lem_prob_bound`: current proof structure invalid (∃N,φ union)
4. `ranking_order_property`: needs ~200-line foldl analysis
5. `lem_kltap_all_perms`: factor-of-2 discrepancy, μ(G)=|V|/2 assumption

Decision: **Keep changes, more work needed.**

[closed: Prover2b k=0 case] **lem_kltap_all_perms: k=0 case proved**
File: `GraphRanking/TheAnalysis.lean` line 55
When k=0 (which occurs when c=1/6 or |V|=0), the only 0-WIS is ∅, and def_ltap holds for ∅ vacuously for any σ. Hence expected number = 1 ≥ 1. The k>0 case remains blocked by the issues below.

[closed: Prover2b k=0 case] **clm_kltap_bound: k=0 case proved**
File: `GraphRanking/TheAnalysis.lean` line 140
When k=0, the only valid I is ∅, so the filter has size 1 ≤ C(n/2,0)*3^0 = 1. The k>0 case remains blocked by the 3^k combinatorial gap.

[closed: Prover2b k=0 case] **lem_kltap_all_perms: k=0 case proved**
File: `GraphRanking/TheAnalysis.lean` line 55
When k=0 (which occurs when c=1/6 or |V|=0), the only 0-WIS is ∅, and def_ltap holds for ∅ vacuously for any σ. Hence expected number = 1 ≥ 1. The k>0 case remains blocked by the issues below.

[closed: Prover2b k=0 case] **clm_kltap_bound: k=0 case proved**
File: `GraphRanking/TheAnalysis.lean` line 140
When k=0, the only valid I is ∅, so the filter has size 1 ≤ C(n/2,0)*3^0 = 1. The k>0 case remains blocked by the 3^k combinatorial gap.


[open] **thm_final: h_pointwise μ(G)=0 case needs hypothesis change (CONFIRMED FALSE)**
File: `GraphRanking/TheAnalysis.lean` line 1114-1118
The proof that |R|/μ(G) ≥ 1/2 for each Ranking output R requires μ(G) > 0. If μ(G) = 0 (empty graph), then |R| = 0 and |R|/μ(G) = 0/0 = 0 (in ℝ), making the goal 1/2 ≤ 0 false. **The theorem as stated is mathematically false for edgeless graphs**: E = 0 and 0 ≥ 0.505 is false. Solution: add explicit hypothesis `h_mu_pos : 0 < matchingNumber G` to `thm_final`. This is a signature-level change requiring Reviewer action.

[open] **thm_final: new lemma card_edgeSet_le_card_verts_of_vertexCover proved**
File: `GraphRanking/TheAnalysis.lean` line ~848
Private lemma proved: for any matching M and any R whose verts form a vertex cover, |M.edgeFinset| ≤ |R.verts|. Proof by double-counting pairs (v,e) where v ∈ R.verts, e ∈ M.edgeSet, v ∈ e. Used in h_pointwise to show μ(G) ≤ 2|R|.

[open] **thm_final: h_pointwise proved for μ(G) > 0**
File: `GraphRanking/TheAnalysis.lean` line 968
The proof that 1/2 ≤ |R|/μ(G) is complete for μ(G) > 0. Uses:
1. `card_edgeSet_le_card_verts_of_vertexCover` (new) + `matching_card_verts_eq_two_mul_card_edges` to show μ(G) ≤ 2|R|
2. `csSup_le` on `matchingNumber` definition
3. Algebraic manipulation to get 1/2 ≤ |R|/μ(G)

Remaining gap: μ(G)=0 case (needs hypothesis change, see above).


[closed: fixed in prior iteration] **def_ltap/opt signature mismatch (blocking all novel proofs)**
The signature now has 4 arguments `(G, R, k, I)` with `opt` existentially quantified inside, matching all call sites.

[closed: Reviewer fixed in current iteration] **def_ltap structural flaws (was blocking clm_kltap_bound, lem_prob_bound, lem_kltap_all_perms)**
Fixed by:
1. Made `opt` an explicit parameter (signature: `(G, R, opt, k, I)`)
2. Replaced the involution-on-vertices `ι` with an involution-on-edges `f : Sym2 V → Sym2 V` that pairs opt-edges into k augmenting paths
3. Changed the last condition to use `R.edgeSet` instead of `G.Adj` and to only require R-edges between paired edges (not all pairs)
4. Added the condition that each M-edge contains exactly one I-vertex (`∃! v, v ∈ I ∧ v ∈ e`)
5. The `R` parameter is now properly used in the body
6. Added condition that I-vertices are unmatched in R (`∀ v ∈ I, ∀ w, s(v,w) ∉ R.edgeSet`)

[closed: Prover2b fixed] **num_ineq: need alternating series bounds for log(1+x)**
Proof completed using `Real.log_div_le_sum_range_add` and `Real.sum_range_le_log_div` from Mathlib.

[closed: Prover2b fixed] **IsCoveredByDisjointAug3Paths not implemented**
Implemented as: S ⊆ M.edgeSet, with a fixed-point-free involution f on S pairing edges into augmenting paths.

[closed: Reviewer fixed signatures] **clm_kltap_bound, lem_prob_bound, lem_upperbound_kwis, thm_final — missing opt.IsMatching hypothesis**
Added `(h_opt_matching : opt.IsMatching)` parameter to all four theorems.

[closed: Reviewer fixed signature] **lem_kltap_all_perms — pointwise vs average hypothesis**
Changed `h_ratio` from pointwise to average (expected value ≤ (1/2+c)·μ(G)), matching the LaTeX theorem statement.

[closed: Reviewer cleanup] **TheAnalysis.lean: unterminated comment and 350 lines of garbage code**
Removed duplicate/leftover code from a prior partial rewrite of `order_constraints_prob` that had an unterminated doc-comment (`/--`) breaking compilation. File now compiles cleanly.

[closed: Reviewer cleanup] **order_constraints_prob and order_constraints_prob_noB fully proved**
The involution-based induction proof (using `Equiv.swap`) is complete. Base case and inductive step both compile.

**Reviewer iteration summary (2026-05-25, current iteration)**
Audit: all 10 manifest items present.  Project builds cleanly (no errors).
No `axiom` usage.  Signature fidelity maintained.

Closed this iteration:
- `Ranking_Algorithm_isMatching` fully proved (foldl induction with custom List.find? lemma)

5 of 6 novel declarations still need proofs:
- `lem_kltap_all_perms` (line 55) — algebraic, depends on Ranking lemmas + prior theorems
- `clm_kltap_bound` (line 69) — combinatorial counting, pairing-dependence gap
- `lem_prob_bound` (line 306) — σ-dependent φ remains central blocker
- `thm_final` (line 625) — blocked by all above
- `ranking_order_property` (line 93, private) — reverted to sorry, needs Sym2 API + foldl

Plus: `Ranking_Algorithm_isMaximal` stub added (still sorry).

Next iteration priorities:
1. Prove `Ranking_Algorithm_isMaximal` in Introduction.lean (maximal matching property)
2. Prove `ranking_order_property` via foldl induction (now that IsMatching pattern is established)
3. Address σ-dependent φ in `lem_prob_bound`  
4. Prove `clm_kltap_bound` via induction on k (canonical edge selection)
5. Prove `lem_kltap_all_perms` (algebraic)
6. Assemble `thm_final`

[open] **Prover iteration 2026-05-26 (current): summary**
No proofs closed this iteration. Key findings and new issues filed below.
- Attempted `ranking_order_property`: Sym2 API (`Mem.other'`, `other_spec'`, `mem_toFinset`) is workable for extracting vertices. The order property π(n_e) < π(i_{f(e)}) is mathematically true and provable, but formalization requires: (a) getting Fintype instances for Subgraph components, (b) accessing Ranking_Algorithm foldl internals.
- Attempted `clm_kltap_bound`: The 3^k bound remains unresolved. The "at most 2 per pair" argument is confirmed valid (complementary constraints). However, the union across all possible pairings f gives a (2k-1)!! factor that breaks the LaTeX proof. A global combinatorial proof is needed.
- Attempted `hE_pos` (`thm_final`): The standard proof that |R| ≥ μ(G)/2 for maximal matching R requires: (1) |R.verts| = 2 * |R.edgeFinset| (matching cardinality equality), (2) |M| ≤ |R.verts| for any matching M (vertex cover injection). Both are standard but require nontrivial Finset/Subgraph API work.
- Added `two_mul_card_ge_matchingNumber` lemma stub (reverted to sorry) — needs Fintype instances for Subgraph.verts and edgeSet.
File compiles cleanly with 5 sorry-bearing declarations.

[open] **two_mul_card_ge_matchingNumber: matching cardinality lemmas needed**
File: `GraphRanking/TheAnalysis.lean` (was added then reverted)
The proof that |R| ≥ μ(G)/2 for a maximal matching R requires:
1. Lemma: For a matching M, `(Finset.filter (· ∈ M.verts) Finset.univ).card = 2 * (G.edgeFinset.filter (· ∈ M.edgeSet)).card`
   - Proof via double-counting pairs (v,e) with v ∈ M.verts, e ∈ M.edgeSet, v ∈ e.
   - Each v belongs to exactly 1 e (matching), each e contains exactly 2 v's.
   - Formalization requires `Fintype` instances for `M.verts` and `M.edgeSet` (these are subsets of Fintype V and Fintype G.edgeSet respectively).
2. Lemma: For matchings M,R with `hR_cover` (every edge has endpoint in R.verts), we have |M| ≤ 2|R|.
   - Proof: each M-edge has an endpoint in R.verts; distinct M-edges have distinct endpoints; hence |M| ≤ |R.verts| = 2|R|.
   - Formalization requires constructing the injection from M-edges to R-vertices.

Both lemmas are standard but their formalization involves significant Finset/Sym2/Subgraph API work.

[open] **lem_kltap_all_perms needs proof**
File: `GraphRanking/TheAnalysis.lean` line 55
Blocked by:
1. Need lemmas that `Ranking_Algorithm G σ` is a matching and is maximal (see #Ranking_Algorithm_lemmas)
2. Factor-of-2 ambiguity: `prop_aug3_path_bound` gives a bound on edges, but the LaTeX proof expects a bound on augmenting paths (which is half)
3. `prop_aug3_path_bound` and `prop_bionomila_minimize` are prior theorems (sorry OK)

[open] **clm_kltap_bound needs proof**
File: `GraphRanking/TheAnalysis.lean` line 78
The 3^k factor needs a rigorous combinatorial proof. The LaTeX argument (3 choices per augmenting path) assumes a fixed involution f pairing the opt-edges, but f depends on the Ranking output R which varies with σ. The union over all possible f gives a (2k-1)!! factor, which is too large. A direct combinatorial proof or a more sophisticated counting argument is needed. Also needs a lemma that `|opt.edgeSet| ≤ |V|/2` from `opt.IsMatching`.

[open] **ranking_order_property needs proof**
File: `GraphRanking/TheAnalysis.lean` line 93
**Update 2026-05-25 (most recent Prover2b)**: Reverted to `sorry` — the previous partial proof
was broken (Sym2 API issues, `Finset.choose` misuse, wrong `mem_insert` patterns).
The proof sketch remains: from `def_ltap`, extract M (2k opt-edges) and involution f,
define N = non-I vertices and φ: N → I via φ(n_e) = i_{f(e)}. The order property
π(n_e) < π(i_{f(e)}) requires Ranking Algorithm analysis (see #Ranking_Algorithm_lemmas).
Key blockers: Sym2.Mem API for extracting the "other" vertex, injectivity of n_vertex
(needs opt.IsMatching in context), and the order property (needs foldl trace reasoning).
See #Ranking_Algorithm_lemmas.

[open] **Prover iteration 2026-05-26 (Prover2b, current): summary**
No proofs closed this iteration. File compiles cleanly (0 errors, 6 sorry-bearing declarations).
Major findings:

1. **`ranking_order_property` proof analysis**: Developed a rigorous proof sketch for the order property π(n_e) < π(i_{f(e)}). The core contradiction argument: assume π(i_{f(e)}) < π(n_e). Then i_{f(e)} processes before n_e. When i_{f(e)} processes, n_{f(e)} (its G-neighbor via opt-edge) must be matched, so min(π(n_e), π(n_{f(e)})) < π(i_{f(e)}). Combined with π(i_{f(e)}) < π(n_e), we get π(n_{f(e)}) < π(i_{f(e)}) < π(n_e). Now n_{f(e)} processes first; both i_{f(e)} and n_e are unmatched G-neighbors; since π(i_{f(e)}) < π(n_e), n_{f(e)} would match with i_{f(e)} instead of n_e. Contradiction. Formalization blocked by: (a) extracting vertices from Sym2 edges, (b) proving the greedy choice property (algorithm picks π-smallest unmatched neighbor).

2. **`clm_kltap_bound` combinatorial analysis**: Discovered that for a fixed pair of opt-edges, at most 2 of 4 I-choices are valid (contradictory G-edge requirements: one choice requires edge present, the other requires it absent). This gives a 2^k bound per fixed pairing, but the union across pairings is not yet bounded.

3. **`hE_pos` (`thm_final`)**: Added private lemma `matching_card_verts_eq_two_mul_card_edges` (still sorry) for the cardinality relationship |R.verts| = 2*|R.edgeFinset|. The remaining step: using `ranking_no_edge_unmatched` (R.verts is a vertex cover) to prove |R| ≥ μ(G)/2 via injection from max-matching edges to R-vertices.

4. Cleaned up broken code from previous iteration: removed `ranking_order_core` (incomplete), restored `ranking_order_property` to simple sorry, fixed `Subgraph.IsMatching.toEdge.surjective` naming.

File state: 6 sorry-bearing declarations (lem_kltap_all_perms, clm_kltap_bound, ranking_order_property, lem_prob_bound, matching_card_verts_eq_two_mul_card_edges, thm_final). lem_upperbound_kwis and num_ineq are fully proved.

[open] **matching_card_verts_eq_two_mul_card_edges needs proof**
File: `GraphRanking/TheAnalysis.lean` line 743
Private lemma: for a matching M, |M.verts| = 2 * |M.edgeFinset|.
Added stub with `IsMatching.toEdge.surjective`. Needs double-counting proof: each vertex in M.verts has exactly 1 incident edge in M.edgeSet; each edge has exactly 2 incident vertices. Blocked by Fintype/Subtype API for M.verts and M.edgeSet.

[open] **Reviewer audit (2026-05-26, current iteration)**
Audit: all 10 manifest items present. Project builds cleanly (0 errors, 6 `sorry` warnings).
No `axiom` usage. Signature fidelity maintained.

Novel declarations (6 total):
- `def_ltap` — ✅ fully implemented (definition)
- `lem_kltap_all_perms` — ❌ sorry (line 55)
- `clm_kltap_bound` — ❌ sorry (line 88)
- `lem_prob_bound` — ❌ sorry (line 430), k=0 case done
- `lem_upperbound_kwis` — ✅ fully proved
- `thm_final` — ❌ sorry (line 764), `hE_pos` average bound completed this iteration

Prior declarations (4 total):
- `Ranking_Algorithm` — ✅ fully implemented
- `prop_aug3_path_bound` — sorry (prior, OK)
- `prop_bionomila_minimize` — sorry (prior, OK)
- `prop_entropy_approximation` — sorry (prior, OK)

Private lemmas still sorry:
- `ranking_order_property` (line 210)
- `matching_card_verts_eq_two_mul_card_edges` (line 750)

Changes this iteration:
- `thm_final`: Filled in the proof that pointwise bound implies average bound (the `hE_pos` subproof now has only the `h_pointwise` part remaining).
- Attempted `matching_card_verts_eq_two_mul_card_edges` with several approaches (double-counting, even_card, Fintype.ofFinite); all reverted. Key blockers remain Fintype instances for `M.verts`/`M.edgeSet` and lemmas linking `M.degree` to `M.coe.degree`.
- Attempted `ranking_order_property` construction (N and φ); reverted. Key blocker is defining a total φ: V → V.

Decision: **Keep changes, more work needed.** Minor progress (thm_final average bound). No regressions.

Next iteration priorities:
1. Prove `matching_card_verts_eq_two_mul_card_edges` — this unblocks `thm_final`'s `h_pointwise`. Approach: use `Fintype.ofFinite` for instances, then use `sum_degrees_eq_twice_card_edges` on `M.coe` to get `M.verts.toFinset.card = 2 * M.coe.edgeFinset.card`, then relate `M.coe.edgeFinset.card` to `(G.edgeFinset.filter (· ∈ M.edgeSet)).card` via `Sym2.map Subtype.val`.
2. Prove `ranking_order_property` — construct N via `Finset.attach` and i_vertex/n_vertex, define φ on N using Finset pairs, extend arbitrarily for V → V.
3. Prove `lem_prob_bound` using `ranking_order_property` — the k>0 case is the only remaining gap.
4. Prove `clm_kltap_bound` — combinatorial bound (3^k factor).
5. Prove `lem_kltap_all_perms` — algebraic proof using prior lemmas.
6. Assemble remaining pieces of `thm_final`.

[open] **lem_prob_bound needs proof**probability product) or using `order_constraints_prob` with a fixed φ — but φ varies with σ. This is a central proof-theoretic gap.

[open] **thm_final needs proof**
File: `GraphRanking/TheAnalysis.lean` line 661
Blocked by: `lem_kltap_all_perms`, `lem_prob_bound`, `clm_kltap_bound`, `prop_entropy_approximation` (prior, sorry OK). Additional issues:
- Integrality of k = (1/2 - 3c)·n/2 (k must be ℕ)
- Need `Ranking_Algorithm_isMaximal` for the E ≥ 1/2 case
- Algebraic manipulation with binomial coefficient, entropy, and the `num_ineq` lemma (which is proved)

[closed: Prover2b fixed in iteration 2026-05-25] **Ranking_Algorithm_isMatching proved**
File: `GraphRanking/Introduction.lean` line 75
Proof completed via foldl induction with a three-part invariant:
1. `v ∈ acc.1 ↔ ∃ w, s(v,w) ∈ acc.2` (cover property)
2. `∀ v w₁ w₂, s(v,w₁) ∈ acc.2 → s(v,w₂) ∈ acc.2 → w₁ = w₂` (matching property)
3. `∀ e ∈ acc.2, e ∈ G.edgeFinset` (edges are from G)
A custom lemma `h_find_prop` was proved: `List.find? p l = some a → p a`.
The step preservation argument avoids `split`/`rename_i` by using `cases` with an explicit equation.
The remaining lemmas needed from Ranking_Algorithm are `Ranking_Algorithm_isMaximal` and
`Ranking_Algorithm_unmatched_neighbors`.

[open] **Ranking_Algorithm needs lemmas: is maximal, unmatched_neighbors**
File: `GraphRanking/Introduction.lean`
- `Ranking_Algorithm_isMatching` — DONE (see above)
- `Ranking_Algorithm_isMaximal (G) (σ) : ...` (maximal matching property) — STILL NEEDED
- `Ranking_Algorithm_unmatched_neighbors` (if v unmatched, all neighbors have smaller π and are matched) — STILL NEEDED
These are needed by `prop_aug3_path_bound`, `lem_kltap_all_perms`, `ranking_order_property`, and `thm_final`.

[open] **thm_final: integrality of k**
File: `GraphRanking/TheAnalysis.lean` line 661
The proof requires k:ℕ with (k:ℝ) = (1/2 - 3c)·|V|/2. This is only possible when the RHS is an integer, which the LaTeX assumes without comment. Solutions: (1) round k and adjust bounds with error terms, or (2) use real k with Gamma function (much harder).

[closed: Prover proved in iteration 2026-05-26] **ranking_no_edge_unmatched lemma proved**
File: `GraphRanking/TheAnalysis.lean` line 110
Private lemma proving: `s(u,v) ∈ G.edgeFinset → u ∈ R.verts ∨ v ∈ R.verts`
Proof: by contradiction using `Ranking_Algorithm_isMaximal`. Constructs extended subgraph M' = R ∪ {s(u,v)} via `Subgraph.mk`. The matching property of M' is verified by case analysis.

[open] **thm_final: hE_pos — cardinality lemmas needed**
File: `GraphRanking/TheAnalysis.lean` line 761
Now that `ranking_no_edge_unmatched` is proved (R.verts is a vertex cover), the remaining step for `hE_pos` (1/2 ≤ E) is:
1. For any matching M and vertex cover C, |M.edgeFinset ∩ G.edgeFinset| ≤ |C.toFinset| (injective map from M-edges to C-vertices).
2. For the Ranking output R (which is a matching), |R.verts.toFinset| = 2 * |(G.edgeFinset.filter (· ∈ R.edgeSet))|.
These are standard cardinality facts about matchings and vertex covers.

[open] **Prover iteration 2026-05-26: summary**
No proofs closed. Key findings:
1. **`ranking_order_property` is mathematically true**: The order property π(n_e) < π(i_{f(e)}) can be proved by case analysis on which of n_e, n_{f(e)} processes first. In both cases, the greedy algorithm's "first unmatched neighbor" property forces the ordering.
   - If n_{f(e)} processes first: must prefer n_e over i_{f(e)} → π(n_e) < π(i_{f(e)})
   - If n_e processes first: n_e matches n_{f(e)} at π(n_e); later i_{f(e)} must find n_{f(e)} already matched → π(n_e) < π(i_{f(e)})
   - Formalization requires accessing the foldl internals of Ranking_Algorithm, which are locked behind `let` bindings.

2. **`hE_pos` in `thm_final`**: The standard lemma "maximal matching size ≥ μ(G)/2" is needed. The proof via vertex cover is clean: no edge can have both endpoints outside R.verts (by maximality). This is already proved as `h_no_edge_unmatched` inside `Ranking_Algorithm_isMaximal` but not exported.

3. **Missing exported lemma**: `Ranking_Algorithm_no_edge_unmatched (G) (σ) (u v) : s(u,v) ∈ G.edgeFinset → u ∈ R.verts ∨ v ∈ R.verts` would unblock both `ranking_order_property` and `hE_pos`. This is already proved internally in `Ranking_Algorithm_isMaximal` (line 361-365 of Introduction.lean) but needs to be extracted as a public theorem.

4. **Sym2 API gap**: `ranking_order_property` needs to extract the unique non-I vertex from a Sym2 edge. `simp [v ∈ s(a,b)]` works but the injectivity of e↦n_e relies on `opt.IsMatching` which is not available in the lemma's current signature (could be added).

Next iteration recommendation: Export `Ranking_Algorithm_no_edge_unmatched` lemma from Introduction.lean, then use it to prove `hE_pos` and `ranking_order_property`.y maximal matching has size ≥ μ(G)/2. Needs `Ranking_Algorithm_isMaximal`.

[open] **clm_kltap_bound: the 3^k factor — combinatorial gap**
File: `GraphRanking/TheAnalysis.lean` line 78
Detailed analysis: For a fixed set M of 2k opt-edges, we need to bound the number of I (picking one endpoint per edge) that can be valid k-WIS for SOME σ. The LaTeX argument claims 3^k by noting that in each augmenting path, the two R-adjacent vertices can't both be in I. But which vertices are R-adjacent depends on f (the involution), which depends on σ. Different σ produce different f, hence different forbidden choices. The union over f gives (2k-1)!! · 3^k, which is too large. A rigorous proof must show the bound holds across all possible pairings simultaneously.

**Update 2026-05-25 (Prover2b)**: Additional combinatorial analysis reveals the constraint
structure more precisely.  For a fixed pair of opt-edges {e1, e2} forming one augmenting
path, let the four vertices be a,b (from e1) and c,d (from e2).  The valid I-choices are
exactly those where:
- The non-I endpoints are adjacent in G (R-edge constraint)
- The I-vertices are NOT adjacent in G (independence constraint)
These two constraints are complementary: each possible I requires one specific cross-edge
to exist and its "partner" cross-edge (connecting the I-vertices) to NOT exist.  Hence at
most 2 of 4 choices are valid for k=1, confirming the 3^k upper bound is not tight but valid.

The fundamental gap remains: for k>1, different σ produce different pairings of the 2k
opt-edges into k augmenting paths, leading to different sets of forbidden I-choices.  A
direct union bound over all possible pairings gives a (2k-1)!! factor, invalidating the
proof.  A different argument is needed — perhaps using the fact that the I-vertices are
unmatched in R and the structure of the Ranking Algorithm forces additional constraints.

[open] **lem_prob_bound: probability bound structure**
File: `GraphRanking/TheAnalysis.lean` line 333
The LaTeX proof uses sequential insertion: process N in reverse order, inserting counterparts into I∪N. The probability that each counterpart lands after its N-vertex telescopes to 1/2^(2k). This argument does NOT sum over bijections φ; it directly computes the probability for the specific φ determined by the augmenting paths (which depends on σ). To formalize: after `ranking_order_property` extracts φ (which depends on σ), we need to bound Pr_σ[∀v∈N, σ⁻¹(v) < σ⁻¹(φ_σ(v))] without summing over all possible φ. The event is σ-dependent in a complex way. The `order_constraints_prob` lemma gives the bound for a FIXED φ; bridging to σ-dependent φ is the gap.

[closed: Reviewer fixed verts] **Ranking_Algorithm.verts = Set.univ conflicts with IsMatching**
File: `GraphRanking/Introduction.lean` line 53
Changed `verts := Set.univ` to `verts := {v | ∃ w, s(v, w) ∈ edges}`. Now `verts` only contains vertices incident to at least one output edge, matching the definition of `IsMatching` (every vertex in `verts` is incident to exactly one edge). The `edge_vert` proof is now trivial. This unblocks proving `Ranking_Algorithm_isMatching`.

[open] **clm_kltap_bound: potential counterexample to 3^k bound — RESOLVED**
File: `GraphRanking/TheAnalysis.lean` line 99
**Update 2026-05-25 (Prover2b)**: The alleged counterexample (all 4 choices of I valid when all 4 cross-edges exist) is impossible.  Analysis:
- For I={a,c} to be valid: need R-edge (b,d) ∈ G AND independence (a,c) ∉ G.
- For I={b,d} to be valid: need R-edge (a,c) ∈ G AND independence (b,d) ∉ G.
- These two conditions are complementary: they require (b,d) ∈ G and (b,d) ∉ G simultaneously.
- Similarly I={a,d} and I={b,c} conflict.
- Therefore at most 2 (not 4, not even 3) of the 4 choices can be valid for k=1.
- The LaTeX's 3^k bound (which gives 3 for k=1) is a valid upper bound (2 ≤ 3).
- **However**, the deeper issue of varying pairings for k>1 remains unresolved.

[open] **lem_kltap_all_perms: μ(G) vs |V|/2 mismatch**
File: `GraphRanking/TheAnalysis.lean` line 55
The theorem uses hk: k = (1/2 - 3c)·|V|/2 but the proof relies on prop_aug3_path_bound which gives bounds in terms of μ(G). The LaTeX proof implicitly assumes μ(G) = |V|/2 (perfect matching). In general μ(G) ≤ |V|/2, so the derived inequality may not hold. This needs either an additional hypothesis that G has a perfect matching, or a more careful bounding argument.

[open] **lem_prob_bound: ∃φ event has probability > 1/2^{2k} — subset argument insufficient**
File: `GraphRanking/TheAnalysis.lean` line 385
For k=1, the event "∃ φ: N → I bijection such that ∀v∈N, π(v) < π(φ(v))" has probability 1/3 (8/24 permutations), which exceeds the target bound 1/2²=1/4. This means the simple approach of bounding k-WIS probability via the ∃φ superset does NOT work — it gives a strictly larger upper bound. The LaTeX sequential insertion argument computes the probability for the SPECIFIC counterpart mapping C determined by the augmenting path structure, not the ∃φ event. The gap is: C depends on σ (through the R-edge pairing), so we cannot directly apply the fixed-φ probability bound. A correct formalization must either (a) prove that C is σ-independent, or (b) use a more refined argument that avoids fixing C.

[open] **ranking_order_property: detailed proof sketch and Sym2 API issues**
File: `GraphRanking/TheAnalysis.lean` line 158
A complete proof requires:
1. **Construction of N and φ from def_ltap**: N = non-I vertices of M-edges, φ(n_e) = I-vertex of f(e). This needs Sym2.Mem.other to extract the non-I vertex, and proof that the mapping e↦n_e is injective (since opt is a matching, M-edges are vertex-disjoint).
2. **Order property via greedy choice**: The key lemma is `ranking_greedy_choice`: if s(v,w) ∈ R.edgeSet and u is a G-neighbor of v with u unmatched in R, then π(w) < π(u). Proof requires unfolding the `foldl` definition of Ranking_Algorithm and analyzing the step function. An alternative: use the property "if v is unmatched, all G-neighbors were already matched when v was processed" (provable by induction on foldl).
3. **Injectivity and surjectivity of φ**: Follows from the involution property of f and the unique-I-vertex condition.

[open] **Reviewer iteration summary (2026-05-25, iteration 2)**
Audit: all 10 manifest items present.  Project builds cleanly (no errors).
No `axiom` usage.  Signature fidelity maintained.

4 of 6 novel declarations still need proofs:
- `lem_kltap_all_perms` (line 55) — algebraic, depends on Ranking lemmas + prior theorems
- `clm_kltap_bound` (line 69) — combinatorial counting, induction-on-k strategy identified
- `lem_prob_bound` (line 308) — σ-dependent φ is central blocker
- `thm_final` (line 627) — blocked by all above

Plus private helper `ranking_order_property` (line 93).

This iteration was neutral: the Prover attempted `Ranking_Algorithm_isMatching` but hit API
limitations (`List.find?` Bool/Prop, missing `List.foldl_induction`) and reverted all changes.
No files were modified; the project state is unchanged from the previous iteration.

Next iteration priorities (same as before):
1. Prove `Ranking_Algorithm_isMatching` and `Ranking_Algorithm_isMaximal` in Introduction.lean
   (requires custom list induction + Sym2 API)
2. Prove `ranking_order_property` via foldl induction
3. Address σ-dependent φ in `lem_prob_bound`
4. Prove `clm_kltap_bound` via induction on k (canonical edge selection)
5. Prove `lem_kltap_all_perms` (algebraic)
6. Assemble `thm_final`

Note: `lem_upperbound_kwis`, `num_ineq`, `order_constraints_prob`, `order_constraints_prob_noB`,
and `def_ltap` with its helper lemmas are all fully proved.

[open] **thm_final: algebraic derivation outline**
File: `GraphRanking/TheAnalysis.lean` line 709
The algebraic part (binomial identity → entropy bound → num_ineq contradiction) is well-understood and `num_ineq` is proved. The remaining blockers are:
1. Integrality of k (see above).
2. `Ranking_Algorithm_isMaximal` for E ≥ 1/2 (see Ranking_Algorithm_lemmas).
3. `lem_kltap_all_perms` (provides lower bound ≥ 1).
4. `clm_kltap_bound` and `lem_prob_bound` (used by `lem_upperbound_kwis`, which is proved assuming they hold).
Once items 1-4 are resolved, the algebraic derivation is a straightforward calculation using `prop_entropy_approximation` (prior, sorry OK) and `num_ineq` (proved).

[closed: Reviewer proved in iteration 2026-05-26] **Ranking_Algorithm_isMaximal proved**
File: `GraphRanking/Introduction.lean` line 236
Proof completed using:
1. Covering invariant (`v ∈ final_acc.1 ↔ ∃ w, s(v,w) ∈ final_acc.2`) via foldl induction
2. Monotonicity lemma (foldl only grows)
3. "Unmatched neighbors" lemma (`v ∉ final_acc.1 → s(v,u) ∈ G → u ∈ final_acc.1`)
4. Standard matching maximality via uniqueness of neighbors

[open] **Reviewer iteration summary (2026-05-26)**
Key achievement: `Ranking_Algorithm_isMaximal` is fully proved, unblocking the critical dependency chain.

Remaining novel proofs (4 of 6):
- `lem_kltap_all_perms` (line 55) — algebraic, now unblocked since Rank maximality is proved
- `clm_kltap_bound` (line 69) — combinatorial counting (3^k bound)
- `lem_prob_bound` (line 316) — k=0 done, k>0 blocked by ranking_order_property
- `thm_final` (line 635) — blocked by all above
- `ranking_order_property` (line 93, private) — needs Sym2 API + foldl analysis

`lem_upperbound_kwis`, `num_ineq`, `order_constraints_prob`, `order_constraints_prob_noB`,
`def_ltap`, `Ranking_Algorithm_isMatching`, `Ranking_Algorithm_isMaximal` are all fully proved.

Next iteration priorities:
1. Prove `ranking_order_property` (now that IsMatching and IsMaximal are available)
2. Prove `lem_prob_bound` using ranking_order_property
3. Prove `clm_kltap_bound` (combinatorial, 3^k bound)
4. Prove `lem_kltap_all_perms` (algebraic, using prop_aug3_path_bound which now can use IsMaximal)
5. Assemble `thm_final`

[open] **lem_prob_bound: LaTeX order property proof is flawed (critical)**
File: `GraphRanking/TheAnalysis.lean` line 316
**Finding (Prover2b, 2026-05-26)**: The LaTeX proof that π(v₁) < π(u₂) (where v₁ is a non-I vertex and u₂ is the I-vertex of the paired opt-edge) is incorrect. The LaTeX attempts a proof by contradiction: assume π(v₁) > π(u₂), then when u₂ is processed, u₁ (matched to v₁) must already be matched, and the match time < π(u₂). The LaTeX then claims this implies π(v₁) < π(u₂), which is a non-sequitur: the match time is min(π(v₁), π(u₁)), not π(v₁). A concrete counterexample with |V|=4 demonstrates that π(v₁) > π(u₂) is possible while all def_ltap conditions hold:
- Vertices: u₁(rank 1), u₂(rank 2), v₁(rank 3), v₂(rank 4)
- opt-edges: (v₁,v₂), (u₁,u₂); cross-edge: (v₁,u₁)
- Ranking output: R = {(u₁,v₁)}; I = {u₂,v₂}; def_ltap holds with f swapping the two opt-edges
- But π(v₁)=3 > π(u₂)=2, contradicting the claimed order property.
Therefore the ranking_order_property as currently stated (∀v∈N, π(v) < π(φ(v)) with φ(n_e)=i_{f(e)}) is FALSE in general. The lem_prob_bound theorem may still be true, but a different proof is needed. The sequential insertion argument from the LaTeX cannot be used as-is because the mapping C depends on σ in a way that doesn't satisfy the order property.

[open] **clm_kltap_bound: rigorous combinatorial proof needed**
File: `GraphRanking/TheAnalysis.lean` line 88
**Update (Prover2b, 2026-05-26)**: Further analysis shows that for any fixed pair of opt-edges {a,b} and {c,d}, at most 2 of the 4 possible I-choices (one vertex per edge) can be valid for ANY σ. The proof: choices (0,0) and (1,1) are mutually exclusive (one requires cross-edge (b,d)∈G and independence (a,c)∉G, the other requires (a,c)∈G and independence (b,d)∉G). Similarly (0,1) and (1,0) conflict. This gives a 2^k bound per fixed involution f. However, the involution f varies with σ, and the number of possible f is (2k-1)!!. The product (2k-1)!!·2^k exceeds 3^k for k≥2, so the naive union over f does not yield the claimed 3^k bound. A global combinatorial argument that avoids summing over f is needed. The bound 2^k per pair is a necessary condition but not sufficient to prove the final 3^k.

[open] **lem_kltap_all_perms: factor-of-2 discrepancy with prop_aug3_path_bound**
File: `GraphRanking/TheAnalysis.lean` line 55
**Update (Prover2b, 2026-05-26)**: The LaTeX proof expects the number of aug-3-paths to be at least (1/2-3c)·μ(G), but `prop_aug3_path_bound` gives a bound on |S| (edges in augmenting paths), not the number of paths. Since each path uses 2 edges from S, the number of paths is |S|/2 ≥ (1/4-3c/2)·μ(G). This factor-of-2 discrepancy needs resolution. Additionally, the LaTeX proof assumes μ(G)=|V|/2 (perfect matching), but only μ(G)≤|V|/2 is guaranteed. The theorem statement uses |V| for k = (1/2-3c)·|V|/2 but the proof expects bounds in terms of μ(G).

[closed: Reviewer proved in iteration 2026-05-26] **matching_card_verts_eq_two_mul_card_edges proved**
File: `GraphRanking/TheAnalysis.lean` line ~750
Proof via Finset.sum_comm double-counting: each matched vertex has exactly 1 incident edge;
each matching edge has exactly 2 endpoints; therefore |M.verts| = 2*|M.edgeSet|.
Uses Sym2.inductionOn, M.mem_edgeSet, G.loopless.irrefl, Finset.sum_comm.

[open] **Reviewer iteration summary (2026-05-26, current iteration)**
1 lemma proved: `matching_card_verts_eq_two_mul_card_edges` (unblocks h_pointwise in thm_final).
5 sorries remain:
- `lem_kltap_all_perms` (line 55) — algebraic
- `clm_kltap_bound` (line 88) — combinatorial (3^k factor)
- `ranking_order_property` (line 210) — Sym2 + foldl
- `lem_prob_bound` (line 430) — k>0 case
- `thm_final` (line 847) — h_pointwise still sorry

Next iteration priorities:
1. Prove `h_pointwise` in thm_final (now unblocked by matching_card_verts_eq_two_mul_card_edges)
2. Prove `ranking_order_property`
3. Prove `lem_prob_bound` using ranking_order_property
4. Prove `clm_kltap_bound`
5. Prove `lem_kltap_all_perms`

`lem_upperbound_kwis`, `num_ineq`, `order_constraints_prob`, `order_constraints_prob_noB`,
`def_ltap`, `Ranking_Algorithm_isMatching`, `Ranking_Algorithm_isMaximal` are fully proved.

Critical blockers for next iteration:
1. **Reformulate `ranking_order_property`**: The current statement (π(v) < π(φ(v))) is false in general. Need to find the correct condition that holds for all k-WIS and still yields the 1/2^{2k} probability bound. Possible approaches: (a) use a different mapping φ, (b) prove a weaker order property that's still sufficient, (c) abandon the order-property approach and find a direct probability argument.
2. **Prove `clm_kltap_bound`**: Need a global combinatorial argument that avoids the (2k-1)!! factor from summing over involution pairings.
3. **Resolve factor-of-2 in `lem_kltap_all_perms`**: Either adjust the proof to work with edges/2, or modify `prop_aug3_path_bound`'s interpretation.

[open] **Prover iteration summary (2026-05-26 iteration 4)**
No proofs closed. Key findings:

1. **`ranking_order_property` counterexample is INVALID**: The alleged counterexample in the issue tracker (π(v₁)=3 > π(u₂)=2) does not correspond to any valid Ranking Algorithm output. For R={(u₁,v₁)} to be the output with π(u₁)=1, π(v₁)=2, π(u₂)=3, π(v₂)=4, the order property holds: π(v₁)=2 < π(u₂)=3. The proof that π(n_e) < π(i_{f(e)}) can be established using: (a) i_{f(e)} is unmatched, so by the greedy nature of Rank, all its G-neighbors (including n_{f(e)}) are matched before it; (b) the match (n_e, n_{f(e)}) is formed when the earlier of n_e, n_{f(e)} is processed, and must occur before i_{f(e)} is processed to prevent i_{f(e)} from matching with n_{f(e)}. The statement is LIKELY TRUE and PROVABLE with the right Ranking Algorithm lemmas.

2. **`IsCoveredByDisjointAug3Paths` formalization is inconsistent with LaTeX**: The definition pairs M-edges (from the suboptimal matching) connected by G-edges, representing paths of form M-edge, G-edge, M-edge. However, the LaTeX augmenting paths are of form opt-edge, R-edge, opt-edge (two edges from one matching, one from the other). The formalization should have S contain the R-edges (middle edges of augmenting paths), each path contributing exactly one edge to S, with |S| = number of paths. The current definition with an involution f pairing S-edges gives 2 edges per "pair," which doesn't match the augmenting path structure. This affects `prop_aug3_path_bound` and everything downstream.

3. **`clm_kltap_bound` 3^k factor**: Further analysis confirms the LaTeX proof is incomplete. The "at most 3 choices per pair" argument works for a fixed involution f, but f varies with σ. The union over all possible f gives a (2k-1)!!·2^k bound, which exceeds 3^k for k≥2. A rigorous proof requires showing that the union across all f is still bounded by 3^k per choice of 2k opt-edges, which is a nontrivial extremal set theory problem (maximum size of a subset of {0,1}^{2k} with pairwise projections of size ≤2).

4. **`lem_kltap_all_perms` factor-of-2 confirmed**: The formalization's `prop_aug3_path_bound` gives S.card (counting edges in IsCoveredByDisjointAug3Paths), but the LaTeX expects a bound on the number of augmenting paths directly. If S.card counts edges paired by f, then the number of "paths" is S.card/2, giving only half the needed paths, which makes the average number of paths k/2 instead of k, breaking the C(average, k) ≥ 1 calculation.

Next iteration priorities (unchanged, with additional notes):
1. **Fix `IsCoveredByDisjointAug3Paths`** — this is a reviewer-level signature change that's blocking all downstream proofs.
2. **Prove `ranking_order_property`** — now understood to be true and provable, needs Sym2 API and a lemma about Ranking Algorithm unmatched-neighbor ordering.
3. **Prove `clm_kltap_bound`** — may require a different combinatorial argument than the LaTeX provides.
4. **Prove `lem_kltap_all_perms`** — blocked by #1.
5. **Assemble `thm_final`** — blocked by all above.

[closed: Prover 2026-05-26] **ranking_no_edge_unmatched proved**
File: `GraphRanking/TheAnalysis.lean` line 110
Private lemma: `s(u,v) ∈ G.edgeFinset → u ∈ R.verts ∨ v ∈ R.verts`.
Proof via Subgraph.mk construction of R ∪ {s(u,v)}, contradicting maximality.

[open] **Prover iteration 2026-05-26 (iteration 5) summary**
One lemma closed: `ranking_no_edge_unmatched`. This proves R.verts is a vertex cover, which is the key ingredient for both `hE_pos` (μ(G) ≤ 2|R|) and `ranking_order_property` (the order argument).

Remaining work for `hE_pos`: cardinality lemmas linking vertex cover size to matching size:
- |R.verts.toFinset| = 2 * |(G.edgeFinset.filter (· ∈ R.edgeSet))| (matching property)
- For any matching M and vertex cover C, |M| ≤ |C| (injective map from edges to vertices)

Remaining work for `ranking_order_property`: Sym2 vertex extraction, injectivity via opt.IsMatching, and the order argument (now has ranking_no_edge_unmatched available).

## [reverted] iteration 9 rolled back (2026-05-26T06:21:39)
- kind: revert
- detail: The TheAnalysis.lean file became corrupted from incomplete edits during the proof of matching_card_verts_eq_two_mul_card_edges and thm_final.h_pointwise. The matching_card_verts_eq_two_mul_card_edges proof was successfully completed but subsequent attempts broke the file structure with orphaned code fragments.
