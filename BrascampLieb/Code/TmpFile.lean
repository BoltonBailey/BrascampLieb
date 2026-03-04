-- import BrascampLieb.Code.Defs
-- import BrascampLieb.Code.BackgroundLemmas

-- namespace LinearMap

-- /- (by claude) Test proving EssentialRank_comp_linearIsometryEquiv -/

-- -- Key insight: The singular values of l ∘ U equal those of l because:
-- -- 1. singularValues are sqrt(eigenvalues of (adjoint_comp_self))
-- -- 2. (l ∘ U)^* ∘ (l ∘ U) = U^* ∘ l^* ∘ l ∘ U
-- -- 3. For a LinearIsometryEquiv, U^* = U.symm
-- -- 4. So we get U.symm.conj (l^* ∘ l)
-- -- 5. Eigenvalues are preserved under conjugation by unitary

-- -- Let's first establish that adjoint of (l ∘ U) = adjoint(U) ∘ adjoint(l)
-- -- and for LinearIsometryEquiv, adjoint(U) = U.symm

-- lemma test_adjoint_comp {E F G : Type*}
--     [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
--     [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
--     [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
--     (l : F →ₗ[ℝ] G) (U : E ≃ₗᵢ[ℝ] F) :
--     (l.comp U.toLinearMap).adjoint = U.symm.toLinearMap.comp l.adjoint := by
--   ext v
--   apply ext_inner_left ℝ
--   intro w
--   simp only [LinearMap.adjoint_inner_right, LinearMap.coe_comp, Function.comp_apply]
--   /- (by claude) Goal: inner (l (U w)) v = inner w (U.symm (l.adjoint v))
--      Step 1: inner (l (U w)) v = inner (U w) (l.adjoint v) (by adjoint_inner_right)
--      Step 2: inner (U w) (l.adjoint v) = inner w (U.symm (l.adjoint v)) (by isometry) -/
--   calc @inner ℝ _ _ (l (U.toLinearEquiv w)) v
--       = @inner ℝ _ _ (U.toLinearEquiv w) (l.adjoint v) := by
--           rw [← LinearMap.adjoint_inner_right l (U.toLinearEquiv w) v]
--     _ = @inner ℝ _ _ w (U.symm.toLinearEquiv (l.adjoint v)) := by
--         rw [← LinearIsometryEquiv.inner_map_map U.symm]; simp

-- -- Now let's show that the adjoint_comp_self of (l ∘ U) equals U^{-1} (l^* l) U
-- lemma test_adjoint_comp_self_comp {E F G : Type*}
--     [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
--     [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
--     [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
--     (l : F →ₗ[ℝ] G) (U : E ≃ₗᵢ[ℝ] F) :
--     (l.comp U.toLinearMap).adjoint.comp (l.comp U.toLinearMap) =
--     U.symm.toLinearMap.comp ((l.adjoint.comp l).comp U.toLinearMap) := by
--   rw [test_adjoint_comp]
--   /- (by claude) After rewrite: (U.symm ∘ l.adjoint) ∘ (l ∘ U) = U.symm ∘ ((l.adjoint ∘ l) ∘ U)
--      This is associativity of composition. -/
--   ext x
--   simp only [LinearMap.coe_comp, Function.comp_apply]

-- /- (by claude) Now we need to show the adjoint_comp_self is a conjugation -/
-- lemma test_adjoint_comp_self_eq_conj {E F G : Type*}
--     [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
--     [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
--     [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
--     (l : F →ₗ[ℝ] G) (U : E ≃ₗᵢ[ℝ] F) :
--     (l.comp U.toLinearMap).adjoint.comp (l.comp U.toLinearMap) =
--     U.toLinearEquiv.symm.conj (l.adjoint.comp l) := by
--   rw [test_adjoint_comp_self_comp, LinearEquiv.conj_apply]
--   rfl

-- /- (by claude) Show charpoly is preserved -/
-- lemma test_charpoly_adjoint_comp_self_eq {E F G : Type*}
--     [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
--     [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
--     [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
--     (l : F →ₗ[ℝ] G) (U : E ≃ₗᵢ[ℝ] F) :
--     ((l.comp U.toLinearMap).adjoint.comp (l.comp U.toLinearMap)).charpoly =
--     (l.adjoint.comp l).charpoly := by
--   rw [test_adjoint_comp_self_eq_conj]
--   exact LinearEquiv.charpoly_conj U.toLinearEquiv.symm (l.adjoint.comp l)

-- end LinearMap

-- namespace BrascampLiebHelper

-- /- (by claude) Testing the negative sum bound proof approach -/

-- /- (by claude) The key insight: For i ∈ Fin d, define:
--    - p_i = ∑_j q_j * 1_{i ∈ I_j}
--    - deficit_i = max(0, 1 - p_i)

--    By perceptivity: ∑_{i ∈ Ici k} p_i ≥ d - k - β for all k

--    We want to show: ∑_i deficit_i ≤ β

--    The argument: partition indices into S = {i : p_i ≤ 1} and its complement.
--    For S: deficit_i = 1 - p_i
--    For S^c: deficit_i = 0

--    The total deficit = |S| - ∑_{i∈S} p_i

--    We use perceptivity on the smallest k where all i ≥ k are in S.
--    Actually, let's try: at k = smallest index in S,
--    ∑_{i ≥ k} p_i ≥ d - k - β

--    But S might not be a tail (i.e., {k, k+1, ..., d-1} for some k).

--    A cleaner approach: induction from the end.
-- -/

-- /- (by claude) Alternative approach: direct use of perceptivity

--    Claim: ∑_{i ≥ k} deficit_i ≤ β for all k.

--    Proof by reverse induction on k (from d-1 to 0):

--    Base (k = d-1): deficit_{d-1} = max(0, 1 - p_{d-1})
--    By perceptivity: p_{d-1} ≥ 1 - β, so deficit_{d-1} ≤ β.

--    Step (k → k-1): Assume ∑_{i ≥ k} deficit_i ≤ β.
--    Show ∑_{i ≥ k-1} deficit_i ≤ β.

--    Case 1: p_{k-1} ≥ 1. Then deficit_{k-1} = 0, done by IH.
--    Case 2: p_{k-1} < 1. Then deficit_{k-1} = 1 - p_{k-1}.

--    By perceptivity at k-1: ∑_{i ≥ k-1} p_i ≥ d - (k-1) - β
--    So: p_{k-1} + ∑_{i ≥ k} p_i ≥ d - k + 1 - β

--    Now I need to relate ∑_{i ≥ k} p_i to ∑_{i ≥ k} deficit_i.

--    For any i: p_i + deficit_i ≥ 1 (with equality when p_i ≤ 1)
--    So: p_i ≥ 1 - deficit_i
--    Thus: ∑_{i ≥ k} p_i ≥ (d - k) - ∑_{i ≥ k} deficit_i

--    Using IH: ∑_{i ≥ k} deficit_i ≤ β
--    So: ∑_{i ≥ k} p_i ≥ (d - k) - β

--    Then: p_{k-1} ≥ d - k + 1 - β - ∑_{i ≥ k} p_i
--                  ≥ d - k + 1 - β - (something)

--    Hmm, this direction doesn't directly give what we need.

--    Let me try: Use perceptivity to get lower bound on p_{k-1},
--    then use the fact that excess at later indices helps.

--    Alternative: Think about cumulative sums.
--    Let S_k = ∑_{i < k} (1 - p_i) = cumulative deficit minus cumulative excess

--    We have S_d = ∑_i (1 - p_i) = d - Ac

--    At each step: S_{k+1} = S_k + (1 - p_k)

--    The deficit up to k is: D_k = ∑_{i < k} max(0, 1 - p_i)
--    The excess up to k is: E_k = ∑_{i < k} max(0, p_i - 1)

--    We have: D_k - E_k = S_k

--    Tail versions: TD_k = ∑_{i ≥ k} deficit_i, TE_k = ∑_{i ≥ k} excess_i
--    We have: TD_k - TE_k = d - k - ∑_{i ≥ k} p_i

--    By perceptivity: ∑_{i ≥ k} p_i ≥ d - k - β
--    So: TD_k - TE_k ≤ d - k - (d - k - β) = β
--    Hence: TD_k ≤ β + TE_k

--    We need: TD_k ≤ β, which requires TE_k ≤ 0, but TE_k ≥ 0!

--    Hmm wait. We have TD_k ≤ β + TE_k.
--    We want to show TD_0 = ∑_i deficit_i ≤ β.
--    This would require TE_0 = 0, meaning no excess anywhere.
--    But that's not necessarily true!

--    Let me reconsider. The goal is: pos_sum ≤ Ac - d + β
--    where pos_sum = ∑_k max(0, w_k) = ∑_k max(0, p_k - 1) = TE_0 (total excess)

--    From TD_0 - TE_0 = d - Ac and TD_0 ≤ β + TE_0:
--    d - Ac ≤ β (which is just Ac ≥ d - β, true by perceptivity at k=0)

--    This doesn't directly give TE_0 ≤ Ac - d + β.

--    Wait, let me re-read the goal. The goal after rw is:
--    (Ac - d - pos_sum) ≥ -β
--    i.e., Ac - d - TE_0 ≥ -β
--    i.e., TE_0 ≤ Ac - d + β

--    We have: TE_0 - TD_0 = Ac - d (from w_k = p_k - 1)
--    So: TE_0 = Ac - d + TD_0

--    We want: TE_0 ≤ Ac - d + β
--    i.e.: Ac - d + TD_0 ≤ Ac - d + β
--    i.e.: TD_0 ≤ β

--    So we DO need to show TD_0 = ∑_i deficit_i ≤ β.

--    But from the analysis above, we get TD_k ≤ β + TE_k, which at k=0 gives
--    TD_0 ≤ β + TE_0.

--    This is consistent since TE_0 ≥ 0, but doesn't prove TD_0 ≤ β directly.

--    The key insight I'm missing:
--    By perceptivity: for ANY k, ∑_{i ≥ k} p_i ≥ (d - k) - β

--    Consider the indices where p_i < 1. These contribute to deficit.
--    Consider the indices where p_i ≥ 1. These contribute to excess or nothing.

--    For any tail {k, k+1, ..., d-1}:
--    - The number of elements is d - k
--    - If ALL had p_i = 1, the sum would be d - k
--    - Perceptivity says sum ≥ (d-k) - β
--    - So the "total shortfall" in the tail is at most β

--    The "total shortfall" = ∑_{i ≥ k} (1 - p_i)^+ = TD_k
--    But also includes excess! ∑_{i ≥ k} (p_i - 1)^+ = TE_k

--    Actually: ∑_{i ≥ k} (1 - p_i) = (d-k) - ∑_{i ≥ k} p_i ≤ β

--    Now: (1 - p_i) = (1 - p_i)^+ - (p_i - 1)^+ for all p_i
--    So: ∑_{i ≥ k} (1 - p_i) = TD_k - TE_k ≤ β
--    Hence: TD_k ≤ β + TE_k ≤ β + (something ≥ 0)

--    This only gives TD_k ≤ β when TE_k = 0 (no excess in tail).

--    But for k = 0, we need TD_0 ≤ β even if TE_0 > 0.

--    Hmm, I think there might be a subtlety I'm missing in the proof sketch.

--    Let me re-read the tex file approach...

--    Actually, looking at the code comments again:
--    "For the last index k = d-1: if w_{d-1} < 0, then p_{d-1} < 1.
--     But by perceptivity at i = d-1: ∑_j q_j |I_j ∩ {d-1}| ≥ 1 - β.
--     This means p_{d-1} ≥ 1 - β, so w_{d-1} ≥ -β."

--    This only bounds ONE term. The claim is that using telescoping,
--    the CUMULATIVE underrepresentation is bounded.

--    I think the key is the tail sum structure. Let me think again...

--    Define R_k = ∑_{i ≥ k} w_i = ∑_{i ≥ k} (p_i - 1)

--    We have:
--    - R_0 = Ac - d (from h_sum_w)
--    - R_k = R_{k-1} - w_{k-1} for k > 0
--    - Also R_k = ∑_{i ≥ k} p_i - (d - k)
--    - By perceptivity: ∑_{i ≥ k} p_i ≥ (d - k) - β
--    - So R_k ≥ -β for all k!

--    Now: R_k = (sum of positive w_i for i ≥ k) + (sum of negative w_i for i ≥ k)
--           = TE_k - TD_k (where I'm reusing notation: TD_k for neg parts)

--    Wait no, w_k = p_k - 1, so:
--    - positive part of w_k = max(0, p_k - 1) = excess_k
--    - negative part of w_k = min(0, p_k - 1) = -deficit_k

--    So: R_k = ∑_{i ≥ k} excess_i - ∑_{i ≥ k} deficit_i

--    We have R_k ≥ -β (by perceptivity), so:
--    ∑_{i ≥ k} excess_i - ∑_{i ≥ k} deficit_i ≥ -β
--    ∑_{i ≥ k} deficit_i ≤ ∑_{i ≥ k} excess_i + β

--    At k = 0: TD_0 ≤ TE_0 + β

--    But we want TD_0 ≤ β, which would require TE_0 ≤ 0. That's not true in general!

--    WAIT. I think I've been confusing myself.

--    Let me re-read the goal:
--    "h_neg_sum_bound : (∑ k, if 0 ≤ w k then 0 else w k) ≥ -β"

--    This is ∑_k min(0, w_k) ≥ -β, i.e., the sum of negative parts of w is ≥ -β.

--    The negative parts of w_k are when w_k < 0, i.e., p_k < 1.
--    min(0, w_k) = min(0, p_k - 1) = -(1 - p_k) when p_k < 1, else 0.

--    So: ∑_k min(0, w_k) = -∑_k max(0, 1 - p_k) = -TD_0

--    Goal: -TD_0 ≥ -β, i.e., TD_0 ≤ β. YES this is what we need!

--    OK so the analysis shows: TD_k ≤ β + TE_k.

--    At k=0: TD_0 ≤ β + TE_0.

--    But we need TD_0 ≤ β. This seems to require TE_0 ≤ 0, which is false.

--    UNLESS... there's something special about the structure.

--    Let me look at this differently. Perhaps the perceptivity gives a STRONGER bound
--    that I'm not using.

--    Actually, wait. The goal after rewriting (line 1131-1132) is:
--    (↑Ac - ↑d - ∑ k, if 0 ≤ w k then w k else 0) ≥ -↑β

--    i.e., Ac - d - pos_sum ≥ -β
--    i.e., pos_sum ≤ Ac - d + β

--    where pos_sum = ∑_k max(0, w_k) = ∑_k max(0, p_k - 1) = TE_0 (total excess)

--    Goal: TE_0 ≤ Ac - d + β

--    Now: TE_0 - TD_0 = ∑_k w_k = Ac - d
--    So: TE_0 = Ac - d + TD_0

--    Goal becomes: Ac - d + TD_0 ≤ Ac - d + β
--    i.e.: TD_0 ≤ β. ✓

--    And we showed: TD_0 ≤ β + TE_0 = β + (Ac - d + TD_0)
--    i.e.: 0 ≤ β + Ac - d
--    i.e.: Ac ≥ d - β ✓ (true by perceptivity)

--    This is consistent but doesn't prove TD_0 ≤ β!

--    I think I need to use the perceptivity condition MORE DIRECTLY.

--    Let me look at specific indices. Define S = {i : p_i < 1} (deficit set).

--    For any i ∈ S: deficit_i = 1 - p_i > 0
--    For any i ∉ S: deficit_i = 0

--    TD_0 = ∑_{i ∈ S} (1 - p_i) = |S| - ∑_{i ∈ S} p_i

--    Now, if S = {k, k+1, ..., d-1} for some k (i.e., S is a tail):
--    By perceptivity: ∑_{i ≥ k} p_i ≥ (d-k) - β = |S| - β
--    So: TD_0 = |S| - ∑_{i ∈ S} p_i ≤ |S| - (|S| - β) = β ✓

--    But S might NOT be a tail! It could be {0, 2, 5} for example.

--    However, the MINIMUM of p over any tail is constrained by perceptivity.
--    If S is not a tail, some indices in S have smaller indices than others.
--    The smallest index in S... let's call it k_min.

--    Indices {k_min, k_min+1, ..., d-1} include S (since S has smallest element k_min).
--    Wait no, S could be non-contiguous.

--    Hmm, this is tricky. Let me think about what perceptivity really says.

--    Perceptivity says: for EVERY k, the weighted sum of indicators over i ≥ k is at least (d-k) - β.

--    Consider the tightest constraint. The perceptivity at each k gives:
--    ∑_{i ≥ k} p_i ≥ (d-k) - β

--    For k = 0: ∑_i p_i ≥ d - β
--    For k = 1: ∑_{i ≥ 1} p_i ≥ d - 1 - β
--    ...
--    For k = d-1: p_{d-1} ≥ 1 - β

--    The constraints at different k are related:
--    ∑_{i ≥ k} p_i = p_k + ∑_{i ≥ k+1} p_i

--    Constraint at k: p_k + ∑_{i ≥ k+1} p_i ≥ (d-k) - β
--    Constraint at k+1: ∑_{i ≥ k+1} p_i ≥ (d-k-1) - β

--    So: p_k ≥ (d-k) - β - ∑_{i ≥ k+1} p_i

--    If the tail sum exactly meets its bound (tight):
--    p_k ≥ (d-k) - β - ((d-k-1) - β) = 1

--    So if ALL tail constraints are tight, each p_k ≥ 1, meaning no deficits!

--    Deficits happen when tail sums EXCEED their bounds (slack in perceptivity).

--    Key insight: Any slack in the tail goes toward reducing deficits.

--    Let me define slack: δ_k = ∑_{i ≥ k} p_i - ((d-k) - β) ≥ 0

--    Then:
--    δ_k = p_k + ∑_{i ≥ k+1} p_i - (d-k) + β
--       = p_k + δ_{k+1} + (d-k-1) - β - (d-k) + β
--       = p_k + δ_{k+1} - 1

--    So: δ_{k} = p_k + δ_{k+1} - 1, i.e., p_k = 1 + δ_k - δ_{k+1}

--    Now: deficit_k = max(0, 1 - p_k) = max(0, δ_{k+1} - δ_k)

--    Since δ_{k+1} ≥ 0 and this recurrence:
--    - If δ_k ≥ δ_{k+1}: deficit_k = 0
--    - If δ_k < δ_{k+1}: deficit_k = δ_{k+1} - δ_k

--    Total deficit:
--    TD_0 = ∑_k max(0, δ_{k+1} - δ_k)

--    This is a telescoping sum of positive increments!
--    Since we're summing all k from 0 to d-1, and δ_d = 0 (empty tail):

--    TD_0 = ∑_k max(0, δ_{k+1} - δ_k)

--    Now, the sum of (δ_{k+1} - δ_k) over k = 0 to d-1 is δ_d - δ_0 = -δ_0.

--    But we're summing max(0, δ_{k+1} - δ_k), not (δ_{k+1} - δ_k).

--    The positive parts sum to: (sum of increments where δ increases)

--    Since the sum telescopes to -δ_0:
--    (sum of positive increments) - (sum of negative increments) = -δ_0
--    (sum of positive increments) = (sum of |negative increments|) - δ_0

--    The negative increments happen when δ_k > δ_{k+1}, contributing |δ_k - δ_{k+1}|.

--    Actually let me be more careful. At the end, δ_d = 0 (the tail {i : i ≥ d} is empty).
--    Actually δ_d is undefined. Let me use k from 0 to d-1, and define δ_d = 0.

--    Then: δ_{d-1} = ∑_{i = d-1} p_i - (1 - β) = p_{d-1} - 1 + β
--    And: δ_d = 0 (by convention, empty sum is 0, and d - d = 0)

--    So: deficit_{d-1} = max(0, δ_d - δ_{d-1}) = max(0, 0 - (p_{d-1} - 1 + β))
--                      = max(0, 1 - p_{d-1} - β)

--    Hmm, this doesn't match the usual deficit formula...

--    Let me reconsider. deficit_k = max(0, 1 - p_k) = max(0, 1 - (1 + δ_k - δ_{k+1}))
--                                 = max(0, δ_{k+1} - δ_k)

--    This is correct!

--    Now: TD_0 = ∑_{k=0}^{d-1} max(0, δ_{k+1} - δ_k)

--    The key: δ_{k+1} ≤ δ_0 + β for all k (roughly speaking).
--    Actually, δ_k ≥ 0 for all k (by perceptivity).

--    Consider the maximum of δ over all k. Let M = max_k δ_k.

--    The positive increments bring us from δ_0 up to M at some point,
--    then negative increments bring us down to δ_d = 0.

--    Total positive increments = M - δ_0 + (any extra ups after the max)

--    But actually, since we're doing max(0, increment), we're just counting
--    the total "upward motion" in the sequence δ_0, δ_1, ..., δ_d = 0.

--    The sequence starts at δ_0, ends at 0, and we count all positive jumps.

--    If the sequence is monotone decreasing: all increments are negative,
--    so TD_0 = 0. This happens when p_k ≥ 1 for all k.

--    If there are ups and downs:
--    Total ups = sum of positive increments
--    Total downs = sum of |negative increments| = total ups + δ_0 (since net = -δ_0)

--    Actually: sum of increments = δ_d - δ_0 = -δ_0
--    So: (sum of positive) - (sum of |negative|) = -δ_0
--    Hence: (sum of positive) = (sum of |negative|) - δ_0

--    Since sum of |negative| ≥ max δ_k (to get back to 0 from the max):

--    Hmm this is getting complicated. Let me try a different approach.

--    Since δ_k ≥ 0 for all k (perceptivity), and δ_d = 0:

--    TD_0 = ∑_k max(0, δ_{k+1} - δ_k)

--    For any k, max(0, δ_{k+1} - δ_k) ≤ δ_{k+1} (since δ_k ≥ 0)

--    But this doesn't give a good bound.

--    Alternative: since the increments sum to -δ_0:
--    ∑_k (δ_{k+1} - δ_k) = -δ_0

--    Split into positive and negative:
--    (pos sum) - (neg sum) = -δ_0
--    (pos sum) = (neg sum) - δ_0

--    The neg sum is the total decrease in δ, which must be at least max(δ)
--    (to get from max down to 0).

--    But max(δ) = δ_0 at k = 0 (if sequence is decreasing) or some k > 0.

--    If all δ_k ≤ β + some_constant:

--    Actually, let's compute δ_0:
--    δ_0 = ∑_{i=0}^{d-1} p_i - (d - β) = Ac - d + β

--    And δ_d = 0.

--    So the sequence goes from δ_0 = Ac - d + β down to 0.

--    If the sequence is monotone: TD_0 = 0.

--    If not monotone, there are ups and downs.

--    The key constraint: δ_k ≥ 0 for all k (perceptivity).

--    This means the sequence can't go below 0.

--    Total ups: TD_0
--    Total downs: TD_0 + δ_0 (since net = -δ_0)

--    The sequence starts at δ_0 ≥ 0, can't go below 0, ends at 0.
--    The maximum it can reach is... unconstrained from above by perceptivity.

--    But wait: δ_k = ∑_{i ≥ k} p_i - (d-k) + β

--    Each p_i ≥ 0 (being a sum of non-negative terms).
--    So δ_k ≤ ∑_{i ≥ k} p_i + β ≤ ∑_{all i} p_i + β = Ac + β

--    This is a weak upper bound.

--    Hmm, I don't immediately see how to get TD_0 ≤ β.

--    Let me think about small examples.

--    Example 1: d = 2, Ac = 2, β = 0.
--    Perceptivity: p_0 + p_1 ≥ 2, p_1 ≥ 1.
--    If p_0 = 1, p_1 = 1: TD_0 = 0 ✓
--    If p_0 = 0.5, p_1 = 1.5: TD_0 = 0.5. But perceptivity requires p_0 + p_1 ≥ 2, ✓.
--       Also p_1 ≥ 1, ✓. deficit_0 = 0.5, deficit_1 = 0. TD_0 = 0.5.
--       But β = 0, so we need TD_0 ≤ 0. Contradiction!

--    Wait, let me recalculate. If β = 0:
--    Perceptivity: p_0 + p_1 ≥ 2, p_1 ≥ 1.

--    With p_0 = 0.5, p_1 = 1.5: p_0 + p_1 = 2 ≥ 2 ✓, p_1 = 1.5 ≥ 1 ✓.
--    TD_0 = max(0, 1 - 0.5) + max(0, 1 - 1.5) = 0.5 + 0 = 0.5.
--    We'd need TD_0 ≤ β = 0. But 0.5 > 0. Contradiction!

--    This suggests the claim TD_0 ≤ β is FALSE in general!

--    Let me re-examine the goal. Maybe I misread.

--    The goal after rewrites at line 1154 is:
--    ⊢ (↑Ac - ↑d - ∑ k : Fin d, if (0 : ℝ) ≤ w k then w k else (0 : ℝ)) ≥ -↑β

--    This is: Ac - d - pos_sum ≥ -β
--    i.e., pos_sum ≤ Ac - d + β

--    In my example: Ac = 2, d = 2, β = 0.
--    pos_sum = max(0, 0.5-1) + max(0, 1.5-1) = 0 + 0.5 = 0.5
--    Ac - d + β = 2 - 2 + 0 = 0
--    Is 0.5 ≤ 0? NO!

--    So the claim fails in this example!

--    But wait, maybe my understanding of perceptivity is wrong.

--    Let me re-read h_percep:
--    h_percep : ∀ (i : Fin d), ↑(∑ j : J, q j * ↑(I j ∩ Finset.Ici i).card) ≥ ↑d - ↑↑i - ↑β

--    For d = 2:
--    At i = 0: ∑_j q_j |I_j ∩ {0,1}| ≥ 2 - 0 - β = 2 - β
--    At i = 1: ∑_j q_j |I_j ∩ {1}| ≥ 2 - 1 - β = 1 - β

--    With β = 0:
--    ∑_j q_j |I_j ∩ {0,1}| ≥ 2
--    ∑_j q_j |I_j ∩ {1}| ≥ 1

--    Now p_k = ∑_j q_j * 1_{k ∈ I_j} = contribution from index k.

--    We have:
--    p_0 + p_1 = ∑_j q_j (|I_j ∩ {0}| + |I_j ∩ {1}|) = ∑_j q_j |I_j ∩ {0,1}| ≥ 2
--    p_1 = ∑_j q_j |I_j ∩ {1}| ≥ 1

--    So my example with p_0 = 0.5, p_1 = 1.5 satisfies p_0 + p_1 = 2 ≥ 2 ✓ and p_1 = 1.5 ≥ 1 ✓.

--    But pos_sum = 0.5 and Ac - d + β = 0, so 0.5 > 0.

--    Hmm, this is a counterexample!

--    Unless... there's a constraint I'm missing. Let me check h_card:
--    h_card : ∑ j : J, q j * ↑(I j).card = Ac

--    So Ac = ∑_j q_j |I_j|.

--    In the example, I need to define I_j and q_j such that:
--    - ∑_j q_j |I_j| = 2 (Ac = 2)
--    - p_k = ∑_j q_j 1_{k ∈ I_j}

--    For p_0 = 0.5, p_1 = 1.5:

--    One way: J = {a}, q_a = 1, I_a = {1}.
--    Then: p_0 = 0, p_1 = 1. Not matching.

--    Another: J = {a, b}, q_a = 0.5, q_b = 0.5, I_a = {0, 1}, I_b = {1}.
--    Then: p_0 = 0.5, p_1 = 0.5 + 0.5 = 1. Not matching (p_1 = 1, not 1.5).

--    Another: J = {a, b}, q_a = 0.5, q_b = 1.5, I_a = {0}, I_b = {1}.
--    Then: p_0 = 0.5, p_1 = 1.5. ✓
--    Also: Ac = q_a |I_a| + q_b |I_b| = 0.5 * 1 + 1.5 * 1 = 2. ✓
--    Perceptivity:
--    At i = 0: ∑_j q_j |I_j ∩ {0,1}| = 0.5 * 1 + 1.5 * 1 = 2 ≥ 2 ✓
--    At i = 1: ∑_j q_j |I_j ∩ {1}| = 0 + 1.5 = 1.5 ≥ 1 ✓

--    So this is a valid configuration with β = 0.
--    But pos_sum = 0.5, Ac - d + β = 0. Goal fails!

--    This means the lemma as stated is FALSE, or I'm misunderstanding something.

--    Let me re-read the original goal more carefully...

--    Oh wait! I think I misread the indices in Ici. Let me check.

--    Finset.Ici i for i : Fin d is {i, i+1, ..., d-1}, which has d - i elements.

--    So h_percep says: ∑_j q_j |I_j ∩ Ici i| ≥ d - i - β

--    For i = ⟨0, _⟩: |Ici 0| = d, and ∑ ≥ d - 0 - β = d - β
--    For i = ⟨1, _⟩: |Ici 1| = d - 1, and ∑ ≥ d - 1 - β
--    ...
--    For i = ⟨d-1, _⟩: |Ici (d-1)| = 1, and ∑ ≥ 1 - β

--    This is what I had. So my example should work.

--    Hmm, but the code says this lemma compiles (just has sorry). Let me look at the overall structure again.

--    Actually wait. The h_percep in the goal state:
--    h_percep : ∀ (i : Fin d), ↑(∑ j : J, q j * ↑(I j ∩ Finset.Ici i).card) ≥ ↑d - ↑↑i - ↑β

--    Here ↑↑i is Fin.val i coerced to ℝ.

--    Let me trace through my example again:
--    d = 2, J = {a, b}, q_a = 0.5, q_b = 1.5, I_a = {0}, I_b = {1}, β = 0.

--    At i = ⟨0, _⟩:
--    LHS = ∑_j q_j |I_j ∩ Ici 0| = q_a |{0} ∩ {0,1}| + q_b |{1} ∩ {0,1}|
--        = 0.5 * 1 + 1.5 * 1 = 2
--    RHS = d - i.val - β = 2 - 0 - 0 = 2
--    2 ≥ 2 ✓

--    At i = ⟨1, _⟩:
--    LHS = 0.5 * |{0} ∩ {1}| + 1.5 * |{1} ∩ {1}| = 0.5 * 0 + 1.5 * 1 = 1.5
--    RHS = 2 - 1 - 0 = 1
--    1.5 ≥ 1 ✓

--    So the perceptivity is satisfied.

--    Now: w_0 = p_0 - 1 = 0.5 - 1 = -0.5 < 0
--         w_1 = p_1 - 1 = 1.5 - 1 = 0.5 > 0

--    pos_sum = if (0 ≤ w_0) then w_0 else 0 + if (0 ≤ w_1) then w_1 else 0
--            = 0 + 0.5 = 0.5

--    Goal: Ac - d - pos_sum ≥ -β
--          2 - 2 - 0.5 ≥ -0
--          -0.5 ≥ 0
--    FALSE!

--    So the statement is FALSE in this example, unless there's an additional constraint.

--    Let me check if there's a constraint on q_j. In the original theorem:
--    (q : J → NNReal)

--    So q_j ≥ 0. ✓

--    And β : NNReal, so β ≥ 0. ✓

--    There's also h_card : ∑_j q_j * |I_j| = Ac.
--    In my example: 0.5 * 1 + 1.5 * 1 = 2 = Ac ✓

--    Hmm, the statement seems to be incorrect, OR there's a hidden assumption I'm missing.

--    Let me look at the .tex file description again...

--    From the tex (lem:telescoping_eigenvalues):
--    "Let $\lambda_1 \ge \dots \ge \lambda_d > 0$ be a non-increasing sequence.
--     Let $c_{j,k} \in \{0, 1\}$ be indicators such that for each $k$,
--     $\sum_{j \in J} q_j \sum_{m=k+1}^d c_{j,m} \ge d - k - \beta$."

--    Note: The tex uses k+1 to d, i.e., STRICTLY greater than k.
--    But in the Lean code, Ici i includes i itself!

--    Let me check: In Lean, Finset.Ici i = {j : j ≥ i}, which includes i.
--    But the tex says "for each k, sum over m = k+1 to d", which excludes k!

--    This is a mismatch! The Lean h_percep uses Ici (includes i), but tex uses (k+1, d].

--    If we use the tex definition with STRICT inequality:
--    At k = 0: ∑_j q_j |I_j ∩ (0, d]| ≥ d - 0 - β = d - β
--    This is |I_j ∩ {1, 2, ..., d-1}|, excluding index 0.

--    In my example with d = 2:
--    At k = 0: ∑_j q_j |I_j ∩ {1}| = 0 + 1.5 = 1.5 ≥ 2 - 0 = 2? NO! 1.5 < 2.

--    So with the STRICT inequality version, my example violates perceptivity!

--    Let me re-read the Lean code carefully...

--    Actually looking at the goal state again:
--    h_percep : ∀ (i : Fin d), ↑(∑ j : J, q j * ↑(I j ∩ Finset.Ici i).card) ≥ ↑d - ↑↑i - ↑β

--    It uses Ici, which INCLUDES i. So the statement is:
--    ∑_j q_j |I_j ∩ {i, i+1, ..., d-1}| ≥ d - i - β

--    At i = 0: ∑_j q_j |I_j| ≥ d - β (using full sets I_j)

--    In my example: 0.5 + 1.5 = 2 ≥ 2 - 0 = 2 ✓

--    At i = 1: ∑_j q_j |I_j ∩ {1}| ≥ 2 - 1 - 0 = 1
--    In my example: 0 + 1.5 = 1.5 ≥ 1 ✓

--    So my example DOES satisfy h_percep as stated in the Lean code!

--    This suggests the lemma statement itself might be wrong, or there's additional
--    context I'm missing.

--    Let me look at what the lemma is actually trying to prove...

--    The main theorem statement is:
--    ∏ j, (∏ i ∈ I j, lam i) ^ (q j : ℝ) ≤
--      lam ⟨0, hd⟩ ^ (Ac - d + β : ℝ) * (lam ⟨d - 1, _⟩) ^ (-(β : ℝ)) * ∏ i, lam i

--    In my example with lam_0 = lam_1 = 1 (constant sequence):
--    LHS = (1^1)^0.5 * (1^1)^1.5 = 1 * 1 = 1
--    RHS = 1^(2-2+0) * 1^(-0) * (1*1) = 1 * 1 * 1 = 1
--    1 ≤ 1 ✓

--    What about lam_0 = 2, lam_1 = 1 (antitone)?
--    LHS = (2^1)^0.5 * (1^1)^1.5 = 2^0.5 * 1 = √2 ≈ 1.414
--    RHS = 2^0 * 1^0 * (2*1) = 1 * 1 * 2 = 2
--    1.414 ≤ 2 ✓

--    Hmm, the main theorem might still be true even if the intermediate step fails!

--    The proof approach in the code might be flawed. The sorry at h_neg_sum_bound
--    might need a different approach or the proof structure needs revision.

--    For now, let me try to see if there's an alternative proof that works.

--    Actually, looking more carefully at the proof structure: maybe h_neg_sum_bound
--    isn't actually needed as stated. Maybe there's a different inequality that works.

--    Or perhaps the mistake is that the direct splitting approach doesn't work,
--    and we need to use the full Abel summation identity.

--    Let me look at what happens after h_neg_sum_bound in the proof...
-- -/

-- end BrascampLiebHelper

-- /- (by claude) Helper lemma for the NNReal inequality.
--    With positivity hypotheses, the proof is complete without sorry.
--    The approach: Use NNReal.rpow_le_rpow combined with algebraic rearrangement.
--    From h: c^s * a * (e^2/b)^s ≤ f, we get a ≤ f * b^s / (c^s * e^(2s)) = f * b^s * c^(-s) * e^(-2s)
--    Taking g-th power: a^g ≤ f^g * b^(gs) * c^(-gs) * e^(-2gs) -/
-- lemma nnreal_pow_inequality_helper' {a b c e f : NNReal} {g s : ℝ}
--     (t : 0 ≤ g) (hb : 0 < b) (hc : 0 < c) (he : 0 < e)
--     (h : c ^ s * (a * (e ^ 2 / b) ^ s) ≤ f) :
--     a ^ g ≤ b ^ (g * s) * c ^ (-(g * s)) * e ^ (-(g * s * 2)) * f ^ g := by

--   /- (by claude) Handle the case when g = 0 first -/
--   by_cases hg : g = 0
--   · simp [hg]

--   have hg_pos : 0 < g := lt_of_le_of_ne t (ne_comm.mpr hg)

--   /- (by claude) Case on whether s = 0 -/
--   by_cases hs : s = 0
--   · /- (by claude) s = 0: All rpow with exponent 0 become 1 -/
--     subst hs
--     simp only [mul_zero, zero_mul, neg_zero, NNReal.rpow_zero, one_mul, mul_one] at h ⊢
--     exact NNReal.rpow_le_rpow h t

--   /- (by claude) Now s ≠ 0 -/

--   /- (by claude) Case on whether a = 0 -/
--   by_cases ha : a = 0
--   · subst ha
--     simp only [NNReal.zero_rpow hg_pos.ne']
--     exact zero_le _

--   have ha_pos : 0 < a := pos_iff_ne_zero.mpr ha

--   /- (by claude) Case on f = 0 -/
--   by_cases hf : f = 0
--   · /- (by claude) f = 0: h gives c^s * a * (e^2/b)^s ≤ 0.
--        Since c, a, e, b all > 0, the LHS is positive. Contradiction. -/
--     subst hf
--     have h_lhs_pos : 0 < c ^ s * (a * (e ^ 2 / b) ^ s) := by
--       apply mul_pos
--       · exact NNReal.rpow_pos hc
--       · apply mul_pos ha_pos
--         apply NNReal.rpow_pos
--         apply div_pos
--         · exact sq_pos_of_pos he
--         · exact hb
--     exact absurd h (not_le.mpr h_lhs_pos)

--   have hf_pos : 0 < f := pos_iff_ne_zero.mpr hf

--   /- (by claude) Main case: all quantities positive.
--      We can do algebraic manipulation freely. -/

--   /- (by claude) Expand the hypothesis using rpow properties -/
--   have h_expand : c ^ s * (a * (e ^ 2 / b) ^ s) = a * c ^ s * e ^ (2 * s) / b ^ s := by
--     rw [NNReal.div_rpow, sq, NNReal.mul_rpow]
--     have he_sq : e ^ s * e ^ s = e ^ (2 * s) := by
--       rw [← NNReal.rpow_add he.ne', ← two_mul]
--     rw [he_sq]
--     ring

--   have h' : a * c ^ s * e ^ (2 * s) / b ^ s ≤ f := by
--     rw [← h_expand]; exact h

--   /- (by claude) Since b^s > 0, we can multiply both sides -/
--   have hbs_pos : 0 < b ^ s := NNReal.rpow_pos hb
--   have h_rearr : a * c ^ s * e ^ (2 * s) ≤ f * b ^ s := by
--     rw [div_le_iff₀ hbs_pos] at h'
--     ring_nf at h' ⊢
--     exact h'

--   /- (by claude) Divide both sides by c^s and e^(2s) -/
--   have hcs_pos : 0 < c ^ s := NNReal.rpow_pos hc
--   have hes_pos : 0 < e ^ (2 * s) := NNReal.rpow_pos he

--   have h_a_le : a ≤ f * b ^ s / (c ^ s * e ^ (2 * s)) := by
--     rw [le_div_iff₀ (mul_pos hcs_pos hes_pos)]
--     ring_nf at h_rearr ⊢
--     exact h_rearr

--   /- (by claude) Rewrite RHS using division and inverse -/
--   have h_a_bound : a ≤ f * b ^ s * (c ^ s)⁻¹ * (e ^ (2 * s))⁻¹ := by
--     calc a ≤ f * b ^ s / (c ^ s * e ^ (2 * s)) := h_a_le
--       _ = f * b ^ s * (c ^ s * e ^ (2 * s))⁻¹ := div_eq_mul_inv _ _
--       _ = f * b ^ s * ((c ^ s)⁻¹ * (e ^ (2 * s))⁻¹) := by rw [mul_inv]
--       _ = f * b ^ s * (c ^ s)⁻¹ * (e ^ (2 * s))⁻¹ := by ring

--   /- (by claude) Rewrite using rpow_neg -/
--   have h_a_bound' : a ≤ f * b ^ s * c ^ (-s) * e ^ (-(2 * s)) := by
--     convert h_a_bound using 2 <;> rw [NNReal.rpow_neg]

--   /- (by claude) Take g-th power of both sides -/
--   have h_pow : a ^ g ≤ (f * b ^ s * c ^ (-s) * e ^ (-(2 * s))) ^ g :=
--     NNReal.rpow_le_rpow h_a_bound' t

--   /- (by claude) Expand RHS -/
--   calc a ^ g ≤ (f * b ^ s * c ^ (-s) * e ^ (-(2 * s))) ^ g := h_pow
--     _ = f ^ g * (b ^ s) ^ g * (c ^ (-s)) ^ g * (e ^ (-(2 * s))) ^ g := by
--         rw [NNReal.mul_rpow, NNReal.mul_rpow, NNReal.mul_rpow]
--     _ = f ^ g * b ^ (s * g) * c ^ ((-s) * g) * e ^ ((-(2 * s)) * g) := by
--         rw [← NNReal.rpow_mul, ← NNReal.rpow_mul, ← NNReal.rpow_mul]
--     _ = b ^ (g * s) * c ^ (-(g * s)) * e ^ (-(g * s * 2)) * f ^ g := by
--         ring_nf
