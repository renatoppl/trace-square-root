import TraceSqrt.Defs
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Analysis.Convex.PathConnected

set_option maxHeartbeats 2000000

/-!
# Sion's Minimax Theorem and Affine Payoffs Corollary (`thm:sion-minimax`, `cor:sion-affine`)

From *Contextual Search and Bilateral Trade with a Trace-Square-Root Potential*
(Appendix D.2, Theorem D.6 `thm:sion-minimax` and Corollary D.7 `cor:sion-affine`).

We formalize:
* **Theorem D.6 (`thm_sion_minimax`)**: Sion's minimax theorem in its general semicontinuous
  quasiconcave/quasiconvex form on nonempty convex subsets `M, N` of real topological vector
  spaces when at least one of `M` and `N` is compact, proved from first principles via Komiya's
  elementary connectedness argument (1988). Values are taken in `EReal` (`[-∞, +∞]`) so that
  potentially unbounded suprema/infima are represented faithfully without `ℝ`'s junk `0`.
* **Corollary D.7 (`cor_sion_affine`)**: Separately continuous affine payoffs on `G × P(K)`,
  where `G ⊆ C(K, ℝ)` is nonempty and convex (equipped with the uniform norm) and `P(K)` is the
  space of Borel probability measures on a nonempty compact metric space `K` (equipped with the
  topology of weak convergence).
-/

namespace TraceSqrt

/-! ## Elementary `EReal` helpers -/

private lemma ereal_iSup_neg {α : Type*} (f : α → EReal) :
    (⨆ a, -f a) = -(⨅ a, f a) := by
  apply le_antisymm
  · refine iSup_le fun a => ?_
    rw [EReal.neg_le_neg_iff]
    exact iInf_le f a
  · rw [← EReal.neg_le_neg_iff, neg_neg]
    refine le_iInf fun a => ?_
    have h : -f a ≤ ⨆ b, -f b := le_iSup (fun b => -f b) a
    rwa [← EReal.neg_le_neg_iff, neg_neg] at h

private lemma ereal_iInf_neg {α : Type*} (f : α → EReal) :
    (⨅ a, -f a) = -(⨆ a, f a) := by
  have h := ereal_iSup_neg (fun a => -f a)
  simp only [neg_neg] at h
  have h2 := congr_arg Neg.neg h
  simpa [neg_neg] using h2.symm

private lemma exists_two_reals_between_ereal {A B : EReal} (h : A < B) :
    ∃ c α : ℝ, c < α ∧ A < (c : EReal) ∧ (α : EReal) < B := by
  induction A using EReal.rec with
  | bot =>
    induction B using EReal.rec with
    | bot => exact absurd h (lt_irrefl _)
    | coe b =>
      refine ⟨b - 2, b - 1, by linarith, EReal.bot_lt_coe _, ?_⟩
      exact EReal.coe_lt_coe_iff.mpr (by linarith)
    | top =>
      exact ⟨0, 1, by norm_num, EReal.bot_lt_coe _, EReal.coe_lt_top _⟩
  | coe a =>
    induction B using EReal.rec with
    | bot => exact absurd h (not_lt_of_ge bot_le)
    | coe b =>
      have hab : a < b := EReal.coe_lt_coe_iff.mp h
      refine ⟨(2 * a + b) / 3, (a + 2 * b) / 3, by linarith, ?_, ?_⟩
      · exact EReal.coe_lt_coe_iff.mpr (by linarith)
      · exact EReal.coe_lt_coe_iff.mpr (by linarith)
    | top =>
      refine ⟨a + 1, a + 2, by linarith, ?_, EReal.coe_lt_top _⟩
      exact EReal.coe_lt_coe_iff.mpr (by linarith)
  | top =>
    exact absurd h (not_lt_of_ge le_top)

/-! ## Komiya's Connectedness Proof of Sion's Minimax Theorem -/

/-- Komiya's two-point lemma: on any convex subset `X ⊆ M`, if for every `n ∈ N` there exists
`x ∈ X` with `F(x, n) > α`, then for any `c < α` and any two points `n₁, n₂ ∈ N` there exists a
single `x₀ ∈ X` with `F(x₀, n₁) ≥ c` and `F(x₀, n₂) ≥ c`. -/
private lemma komiya_two_point
    {E₁ E₂ : Type*}
    [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁] [ContinuousAdd E₁] [ContinuousSMul ℝ E₁]
    [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂] [ContinuousAdd E₂] [ContinuousSMul ℝ E₂]
    {M : Set E₁} {N : Set E₂}
    (hN_conv : Convex ℝ N)
    {F : M → N → ℝ}
    (hF_usc : ∀ n : N, UpperSemicontinuous (fun m : M => F m n))
    (hF_qconc : ∀ (n : N) (r : ℝ), Convex ℝ (Subtype.val '' {m : M | r ≤ F m n}))
    (hF_lsc : ∀ m : M, LowerSemicontinuous (fun n : N => F m n))
    (hF_qconv : ∀ (m : M) (r : ℝ), Convex ℝ (Subtype.val '' {n : N | F m n ≤ r}))
    {X : Set E₁} (hXM : X ⊆ M) (hX_conv : Convex ℝ X)
    {c α : ℝ} (hcα : c < α)
    (h_all : ∀ n : N, ∃ x ∈ X, ∃ hx : x ∈ M, α < F ⟨x, hx⟩ n)
    (n₁ n₂ : N) :
    ∃ x₀ ∈ X, ∃ hx₀ : x₀ ∈ M, c ≤ F ⟨x₀, hx₀⟩ n₁ ∧ c ≤ F ⟨x₀, hx₀⟩ n₂ := by
  by_contra h_none
  push_neg at h_none
  set c' : ℝ := (c + α) / 2
  have hc'₁ : c < c' := by dsimp [c']; linarith
  have hc'₂ : c' < α := by dsimp [c']; linarith
  set S₁ : Set M := {m : M | m.1 ∈ X ∧ c ≤ F m n₁}
  set S₂ : Set M := {m : M | m.1 ∈ X ∧ c ≤ F m n₂}
  have hS_disj' : ∀ m : M, m.1 ∈ X → F m n₁ < c ∨ F m n₂ < c := by
    intro m hmX
    by_cases h1 : c ≤ F m n₁
    · right
      exact h_none m.1 hmX m.2 h1
    · left
      exact lt_of_not_ge h1

  -- Segment γ : [0, 1] → N joining n₁ and n₂
  let I := Set.Icc (0 : ℝ) 1
  let γ : I → N := fun t =>
    ⟨(1 - t.1) • n₁.1 + t.1 • n₂.1,
      hN_conv n₁.2 n₂.2 (sub_nonneg.mpr t.2.2) t.2.1 (sub_add_cancel 1 t.1)⟩
  have hγ_cont : Continuous γ := by
    refine Continuous.subtype_mk ?_ _
    exact ((continuous_const.sub continuous_subtype_val).smul continuous_const).add
      (continuous_subtype_val.smul continuous_const)

  set J₁ : Set I := {t : I | ∀ m ∈ S₁, F m (γ t) ≤ c'}
  set J₂ : Set I := {t : I | ∀ m ∈ S₂, F m (γ t) ≤ c'}

  have hJ₁_closed : IsClosed J₁ := by
    have h_eq : J₁ = ⋂ m ∈ S₁, (fun t : I => F m (γ t)) ⁻¹' Set.Iic c' := by
      ext t; simp [J₁]
    rw [h_eq]
    exact isClosed_biInter fun m _ => ((hF_lsc m).comp hγ_cont).isClosed_preimage c'

  have hJ₂_closed : IsClosed J₂ := by
    have h_eq : J₂ = ⋂ m ∈ S₂, (fun t : I => F m (γ t)) ⁻¹' Set.Iic c' := by
      ext t; simp [J₂]
    rw [h_eq]
    exact isClosed_biInter fun m _ => ((hF_lsc m).comp hγ_cont).isClosed_preimage c'

  -- J₁ ∩ J₂ = ∅ by quasiconvexity of n ↦ F m n
  have hJ_disj : ∀ t : I, ¬(t ∈ J₁ ∧ t ∈ J₂) := by
    rintro t ⟨ht1, ht2⟩
    obtain ⟨x, hxX, hxM, hα⟩ := h_all (γ t)
    let m : M := ⟨x, hxM⟩
    have hm_not1 : m ∉ S₁ := fun hm1 => not_le_of_gt (hc'₂.trans hα) (ht1 m hm1)
    have hm_not2 : m ∉ S₂ := fun hm2 => not_le_of_gt (hc'₂.trans hα) (ht2 m hm2)
    have h1_lt : F m n₁ ≤ c := by
      by_contra h_nle
      exact hm_not1 ⟨hxX, le_of_lt (not_le.mp h_nle)⟩
    have h2_lt : F m n₂ ≤ c := by
      by_contra h_nle
      exact hm_not2 ⟨hxX, le_of_lt (not_le.mp h_nle)⟩
    have hn₁_mem : n₁.1 ∈ Subtype.val '' {n : N | F m n ≤ c} := ⟨n₁, h1_lt, rfl⟩
    have hn₂_mem : n₂.1 ∈ Subtype.val '' {n : N | F m n ≤ c} := ⟨n₂, h2_lt, rfl⟩
    have hγ_mem : (γ t).1 ∈ Subtype.val '' {n : N | F m n ≤ c} :=
      (hF_qconv m c) hn₁_mem hn₂_mem (sub_nonneg.mpr t.2.2) t.2.1 (sub_add_cancel 1 t.1)
    rcases hγ_mem with ⟨n', hn'_le, hn'_eq⟩
    have hn'_eq' : n' = γ t := Subtype.ext hn'_eq
    rw [hn'_eq'] at hn'_le
    have hn'_le' : F m (γ t) ≤ c := hn'_le
    linarith

  -- Endpoints: 0 ∉ J₁ and 1 ∉ J₂
  let t₀ : I := ⟨0, ⟨le_rfl, zero_le_one⟩⟩
  let t₁ : I := ⟨1, ⟨zero_le_one, le_rfl⟩⟩
  have hγ0 : γ t₀ = n₁ := by
    apply Subtype.ext
    simp [γ, t₀]
  have hγ1 : γ t₁ = n₂ := by
    apply Subtype.ext
    simp [γ, t₁]
  have ht₀_not : t₀ ∉ J₁ := by
    intro ht₀
    obtain ⟨x, hxX, hxM, hα⟩ := h_all n₁
    let m : M := ⟨x, hxM⟩
    have hmS₁ : m ∈ S₁ := ⟨hxX, le_of_lt (hcα.trans hα)⟩
    have hle := ht₀ m hmS₁
    rw [hγ0] at hle
    linarith
  have ht₁_not : t₁ ∉ J₂ := by
    intro ht₁
    obtain ⟨x, hxX, hxM, hα⟩ := h_all n₂
    let m : M := ⟨x, hxM⟩
    have hmS₂ : m ∈ S₂ := ⟨hxX, le_of_lt (hcα.trans hα)⟩
    have hle := ht₁ m hmS₂
    rw [hγ1] at hle
    linarith

  -- Every t ∈ I belongs to J₁ ∪ J₂ by connectedness of C_t = X ∩ {m ∈ M | c' ≤ F m (γ t)}
  have hJ_cover : ∀ t : I, t ∈ J₁ ∨ t ∈ J₂ := by
    intro t
    by_contra h_neither
    push_neg at h_neither
    rcases h_neither with ⟨ht1, ht2⟩
    simp only [J₁, Set.mem_setOf_eq, not_forall, not_le] at ht1
    simp only [J₂, Set.mem_setOf_eq, not_forall, not_le] at ht2
    rcases ht1 with ⟨m₁, hm₁S, hm₁_gt⟩
    rcases ht2 with ⟨m₂, hm₂S, hm₂_gt⟩
    let C_t : Set E₁ := X ∩ (Subtype.val '' {m : M | c' ≤ F m (γ t)})
    have hC_conv : Convex ℝ C_t := hX_conv.inter (hF_qconc (γ t) c')
    have hC_preconn : IsPreconnected C_t := hC_conv.isPreconnected
    -- Open sets V₁, V₂ in M lifted to open sets W₁, W₂ in E₁
    have hV₁_open : IsOpen ((fun m : M => F m n₁) ⁻¹' Set.Iio c) :=
      (hF_usc n₁).isOpen_preimage c
    have hV₂_open : IsOpen ((fun m : M => F m n₂) ⁻¹' Set.Iio c) :=
      (hF_usc n₂).isOpen_preimage c
    rw [isOpen_induced_iff] at hV₁_open hV₂_open
    rcases hV₁_open with ⟨W₁, hW₁_open, hW₁_pre⟩
    rcases hV₂_open with ⟨W₂, hW₂_open, hW₂_pre⟩
    have h_mem_W₁ : ∀ m : M, m.1 ∈ W₁ ↔ F m n₁ < c := by
      intro m
      have := Set.ext_iff.mp hW₁_pre m
      simpa using this
    have h_mem_W₂ : ∀ m : M, m.1 ∈ W₂ ↔ F m n₂ < c := by
      intro m
      have := Set.ext_iff.mp hW₂_pre m
      simpa using this
    have hC_sub : C_t ⊆ W₁ ∪ W₂ := by
      rintro x ⟨hxX, m, _, rfl⟩
      rcases hS_disj' m hxX with h1 | h2
      · exact Or.inl ((h_mem_W₁ m).mpr h1)
      · exact Or.inr ((h_mem_W₂ m).mpr h2)
    have hm₁_C : m₁.1 ∈ C_t := ⟨hm₁S.1, ⟨m₁, le_of_lt hm₁_gt, rfl⟩⟩
    have hm₂_C : m₂.1 ∈ C_t := ⟨hm₂S.1, ⟨m₂, le_of_lt hm₂_gt, rfl⟩⟩
    have hm₁_W₂ : m₁.1 ∈ W₂ := (h_mem_W₂ m₁).mpr (h_none m₁.1 hm₁S.1 m₁.2 hm₁S.2)
    have hm₂_W₁ : m₂.1 ∈ W₁ := by
      rcases hS_disj' m₂ hm₂S.1 with h1 | h2
      · exact (h_mem_W₁ m₂).mpr h1
      · exact absurd h2 (not_lt_of_ge hm₂S.2)
    obtain ⟨z, ⟨hzX, mz, hmz_ge, rfl⟩, hzW₁, hzW₂⟩ :=
      hC_preconn W₁ W₂ hW₁_open hW₂_open hC_sub ⟨m₂.1, hm₂_C, hm₂_W₁⟩ ⟨m₁.1, hm₁_C, hm₁_W₂⟩
    have hmz1 : F mz n₁ ≤ c := le_of_lt ((h_mem_W₁ mz).mp hzW₁)
    have hmz2 : F mz n₂ ≤ c := le_of_lt ((h_mem_W₂ mz).mp hzW₂)
    have hγ_mem : (γ t).1 ∈ Subtype.val '' {n : N | F mz n ≤ c} :=
      (hF_qconv mz c) ⟨n₁, hmz1, rfl⟩ ⟨n₂, hmz2, rfl⟩
        (sub_nonneg.mpr t.2.2) t.2.1 (sub_add_cancel 1 t.1)
    rcases hγ_mem with ⟨n', hn'_le, hn'_eq⟩
    have hn'_eq' : n' = γ t := Subtype.ext hn'_eq
    rw [hn'_eq'] at hn'_le
    have hmz_ge' : c' ≤ F mz (γ t) := hmz_ge
    have hn'_le' : F mz (γ t) ≤ c := hn'_le
    linarith

  -- Lift open complements J₁ᶜ, J₂ᶜ in I to open sets O₁, O₂ in ℝ and contradict connectedness of [0, 1]
  have hJc₁_open : IsOpen (J₁ᶜ : Set I) := hJ₁_closed.isOpen_compl
  have hJc₂_open : IsOpen (J₂ᶜ : Set I) := hJ₂_closed.isOpen_compl
  rw [isOpen_induced_iff] at hJc₁_open hJc₂_open
  rcases hJc₁_open with ⟨O₁, hO₁_open, hO₁_pre⟩
  rcases hJc₂_open with ⟨O₂, hO₂_open, hO₂_pre⟩
  have h_mem_O₁ : ∀ t : I, t.1 ∈ O₁ ↔ t ∉ J₁ := by
    intro t
    have := Set.ext_iff.mp hO₁_pre t
    simpa using this
  have h_mem_O₂ : ∀ t : I, t.1 ∈ O₂ ↔ t ∉ J₂ := by
    intro t
    have := Set.ext_iff.mp hO₂_pre t
    simpa using this
  have hI_sub : Set.Icc (0 : ℝ) 1 ⊆ O₁ ∪ O₂ := by
    intro r hr
    let t : I := ⟨r, hr⟩
    by_cases ht1 : t ∈ J₁
    · right
      exact (h_mem_O₂ t).mpr fun ht2 => hJ_disj t ⟨ht1, ht2⟩
    · left
      exact (h_mem_O₁ t).mpr ht1
  have h0_in : ((Set.Icc (0 : ℝ) 1) ∩ O₁).Nonempty :=
    ⟨0, t₀.2, (h_mem_O₁ t₀).mpr ht₀_not⟩
  have h1_in : ((Set.Icc (0 : ℝ) 1) ∩ O₂).Nonempty :=
    ⟨1, t₁.2, (h_mem_O₂ t₁).mpr ht₁_not⟩
  obtain ⟨r, hrI, hrO₁, hrO₂⟩ :=
    isPreconnected_Icc O₁ O₂ hO₁_open hO₂_open hI_sub h0_in h1_in
  let t : I := ⟨r, hrI⟩
  have ht1 : t ∉ J₁ := (h_mem_O₁ t).mp hrO₁
  have ht2 : t ∉ J₂ := (h_mem_O₂ t).mp hrO₂
  rcases hJ_cover t with h1 | h2
  · exact ht1 h1
  · exact ht2 h2

/-- Finite-family induction for Komiya's proof: for every nonempty finite family `ns : Fin (k + 1) → N`
and `c < α`, if `∀ n, ∃ x ∈ X, F(x, n) > α` on a convex `X ⊆ M`, then there is a single `x₀ ∈ X`
with `F(x₀, ns i) ≥ c` for all `i`. -/
private lemma komiya_fin_inter
    {E₁ E₂ : Type*}
    [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁] [ContinuousAdd E₁] [ContinuousSMul ℝ E₁]
    [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂] [ContinuousAdd E₂] [ContinuousSMul ℝ E₂]
    {M : Set E₁} {N : Set E₂}
    (hN_conv : Convex ℝ N)
    {F : M → N → ℝ}
    (hF_usc : ∀ n : N, UpperSemicontinuous (fun m : M => F m n))
    (hF_qconc : ∀ (n : N) (r : ℝ), Convex ℝ (Subtype.val '' {m : M | r ≤ F m n}))
    (hF_lsc : ∀ m : M, LowerSemicontinuous (fun n : N => F m n))
    (hF_qconv : ∀ (m : M) (r : ℝ), Convex ℝ (Subtype.val '' {n : N | F m n ≤ r})) :
    ∀ (k : ℕ) {X : Set E₁} (_hXM : X ⊆ M) (_hX_conv : Convex ℝ X)
      {c α : ℝ} (_hcα : c < α)
      (_h_all : ∀ n : N, ∃ x ∈ X, ∃ hx : x ∈ M, α < F ⟨x, hx⟩ n)
      (ns : Fin (k + 1) → N),
      ∃ x₀ ∈ X, ∃ hx₀ : x₀ ∈ M, ∀ i : Fin (k + 1), c ≤ F ⟨x₀, hx₀⟩ (ns i)
  | 0, X, _, _, c, α, hcα, h_all, ns => by
      obtain ⟨x, hxX, hxM, hα⟩ := h_all (ns 0)
      refine ⟨x, hxX, hxM, fun i => ?_⟩
      fin_cases i
      exact le_of_lt (hcα.trans hα)
  | k + 1, X, hXM, hX_conv, c, α, hcα, h_all, ns => by
      set β : ℝ := (c + α) / 2
      have hcβ : c < β := by dsimp [β]; linarith
      have hβα : β < α := by dsimp [β]; linarith
      set β' : ℝ := (β + α) / 2
      have hββ' : β < β' := by dsimp [β']; linarith
      have hβ'α : β' < α := by dsimp [β']; linarith
      let n_last : N := ns (Fin.last (k + 1))
      let X' : Set E₁ := X ∩ (Subtype.val '' {m : M | β ≤ F m n_last})
      have hX'M : X' ⊆ M := fun x hx => hXM hx.1
      have hX'_conv : Convex ℝ X' := hX_conv.inter (hF_qconc n_last β)
      have h_all' : ∀ n : N, ∃ x ∈ X', ∃ hx : x ∈ M, β < F ⟨x, hx⟩ n := by
        intro n
        obtain ⟨x₀, hx₀X, hx₀M, h1, h2⟩ :=
          komiya_two_point hN_conv hF_usc hF_qconc hF_lsc hF_qconv hXM hX_conv hβ'α h_all n n_last
        refine ⟨x₀, ⟨hx₀X, ⟨⟨x₀, hx₀M⟩, le_of_lt (hββ'.trans_le h2), rfl⟩⟩, hx₀M, ?_⟩
        exact hββ'.trans_le h1
      obtain ⟨x₀, hx₀X', hx₀M, h_ih⟩ :=
        komiya_fin_inter hN_conv hF_usc hF_qconc hF_lsc hF_qconv k hX'M hX'_conv hcβ h_all'
          (fun i : Fin (k + 1) => ns i.castSucc)
      rcases hx₀X' with ⟨hx₀X, m', hm'_ge, hm'_eq⟩
      have hm'_eq' : m' = ⟨x₀, hx₀M⟩ := Subtype.ext hm'_eq
      rw [hm'_eq'] at hm'_ge
      refine ⟨x₀, hx₀X, hx₀M, fun i => ?_⟩
      refine Fin.lastCases ?_ ?_ i
      · exact le_of_lt (hcβ.trans_le hm'_ge)
      · intro j
        exact h_ih j

/-- Compact-left case of Sion's minimax theorem (`IsCompact M`). -/
private lemma sion_minimax_of_compact_left
    {E₁ E₂ : Type*}
    [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁] [ContinuousAdd E₁] [ContinuousSMul ℝ E₁]
    [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂] [ContinuousAdd E₂] [ContinuousSMul ℝ E₂]
    {M : Set E₁} {N : Set E₂}
    (_hM_ne : M.Nonempty) (hN_ne : N.Nonempty)
    (hM_conv : Convex ℝ M) (hN_conv : Convex ℝ N)
    (hM_cpt : IsCompact M)
    (F : M → N → ℝ)
    (hF_usc : ∀ n : N, UpperSemicontinuous (fun m : M => F m n))
    (hF_qconc : ∀ (n : N) (r : ℝ), Convex ℝ (Subtype.val '' {m : M | r ≤ F m n}))
    (hF_lsc : ∀ m : M, LowerSemicontinuous (fun n : N => F m n))
    (hF_qconv : ∀ (m : M) (r : ℝ), Convex ℝ (Subtype.val '' {n : N | F m n ≤ r})) :
    (⨆ m : M, ⨅ n : N, (F m n : EReal)) = (⨅ n : N, ⨆ m : M, (F m n : EReal)) := by
  apply le_antisymm
  · -- Weak minimax inequality: sup_m inf_n F(m, n) ≤ inf_n sup_m F(m, n)
    refine iSup_le fun m => le_iInf fun n => ?_
    exact le_trans (iInf_le (fun n' : N => (F m n' : EReal)) n)
      (le_iSup (fun m' : M => (F m' n : EReal)) m)
  · -- Strong minimax inequality: suppose LHS < RHS and derive a contradiction via compactness of M
    by_contra h_not_le
    have h_lt : (⨆ m : M, ⨅ n : N, (F m n : EReal)) <
        (⨅ n : N, ⨆ m : M, (F m n : EReal)) := lt_of_not_ge h_not_le
    obtain ⟨c, α, hcα, h_lhs_lt, h_lt_rhs⟩ := exists_two_reals_between_ereal h_lt
    have h_all : ∀ n : N, ∃ x ∈ M, ∃ hx : x ∈ M, α < F ⟨x, hx⟩ n := by
      intro n
      have h_lt_sup : (α : EReal) < ⨆ m : M, (F m n : EReal) :=
        h_lt_rhs.trans_le (iInf_le (fun n' : N => ⨆ m : M, (F m n' : EReal)) n)
      rw [lt_iSup_iff] at h_lt_sup
      rcases h_lt_sup with ⟨m, hm_gt⟩
      exact ⟨m.1, m.2, m.2, EReal.coe_lt_coe_iff.mp hm_gt⟩
    -- For every m ∈ M, some n ∈ N has F m n < c (otherwise inf_n F m n ≥ c > LHS)
    have h_cover : (Set.univ : Set M) ⊆ ⋃ n : N, {m : M | F m n < c} := by
      intro m _
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      by_contra h_ge_all
      push_neg at h_ge_all
      have h_le_inf : (c : EReal) ≤ ⨅ n : N, (F m n : EReal) :=
        le_iInf fun n => EReal.coe_le_coe_iff.mpr (h_ge_all n)
      have h_le_lhs : (c : EReal) ≤ ⨆ m' : M, ⨅ n : N, (F m' n : EReal) :=
        h_le_inf.trans (le_iSup (fun m' : M => ⨅ n : N, (F m' n : EReal)) m)
      exact not_lt_of_ge h_le_lhs h_lhs_lt
    haveI : CompactSpace M := isCompact_iff_compactSpace.mp hM_cpt
    have h_open : ∀ n : N, IsOpen {m : M | F m n < c} :=
      fun n => (hF_usc n).isOpen_preimage c
    obtain ⟨S, hS_sub⟩ := isCompact_univ.elim_finite_subcover (fun n : N => {m : M | F m n < c})
      h_open h_cover
    -- Ensure the finite index set is nonempty by inserting an element of N
    rcases hN_ne with ⟨n₀_val, hn₀_mem⟩
    let n₀ : N := ⟨n₀_val, hn₀_mem⟩
    classical
    let S' : Finset N := insert n₀ S
    have hS'_ne : S'.Nonempty := Finset.insert_nonempty n₀ S
    set k : ℕ := S'.card - 1
    have hk : S'.card = k + 1 := Nat.eq_add_of_sub_eq (Finset.Nonempty.card_pos hS'_ne) rfl
    let e_fin : Fin (k + 1) ≃ S' := (S'.equivFinOfCardEq hk).symm
    let ns : Fin (k + 1) → N := fun i => (e_fin i).1
    obtain ⟨x₀, _, hx₀M, hx₀_ge⟩ :=
      komiya_fin_inter hN_conv hF_usc hF_qconc hF_lsc hF_qconv k
        (subset_refl M) hM_conv hcα h_all ns
    let m₀ : M := ⟨x₀, hx₀M⟩
    have hm₀_cov := hS_sub (Set.mem_univ m₀)
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hm₀_cov
    rcases hm₀_cov with ⟨n_bad, hn_bad_S, hn_bad_lt⟩
    have hn_bad_S' : n_bad ∈ S' := Finset.mem_insert_of_mem hn_bad_S
    let i_bad : Fin (k + 1) := e_fin.symm ⟨n_bad, hn_bad_S'⟩
    have hns_ibad : ns i_bad = n_bad := by
      simp [ns, i_bad]
    have h_ge := hx₀_ge i_bad
    rw [hns_ibad] at h_ge
    exact not_lt_of_ge h_ge hn_bad_lt

/-- **Theorem D.6 (Sion's minimax theorem, `thm:sion-minimax`)**:
Let `M` and `N` be nonempty convex subsets of real topological vector spaces, and suppose that
at least one of `M` and `N` is compact. If `F : M → N → ℝ` is upper semicontinuous and
quasiconcave in its first argument (`M`), and lower semicontinuous and quasiconvex in its second
argument (`N`), then
`sup_{m ∈ M} inf_{n ∈ N} F(m, n) = inf_{n ∈ N} sup_{m ∈ M} F(m, n)` in `EReal`. -/
theorem thm_sion_minimax
    {E₁ E₂ : Type*}
    [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁] [ContinuousAdd E₁] [ContinuousSMul ℝ E₁]
    [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂] [ContinuousAdd E₂] [ContinuousSMul ℝ E₂]
    (M : Set E₁) (N : Set E₂)
    (hM_ne : M.Nonempty) (hN_ne : N.Nonempty)
    (hM_conv : Convex ℝ M) (hN_conv : Convex ℝ N)
    (h_compact : IsCompact M ∨ IsCompact N)
    (F : M → N → ℝ)
    (hF_usc : ∀ n : N, UpperSemicontinuous (fun m : M => F m n))
    (hF_qconc : ∀ (n : N) (r : ℝ), Convex ℝ (Subtype.val '' {m : M | r ≤ F m n}))
    (hF_lsc : ∀ m : M, LowerSemicontinuous (fun n : N => F m n))
    (hF_qconv : ∀ (m : M) (r : ℝ), Convex ℝ (Subtype.val '' {n : N | F m n ≤ r})) :
    (⨆ m : M, ⨅ n : N, (F m n : EReal)) = (⨅ n : N, ⨆ m : M, (F m n : EReal)) := by
  rcases h_compact with hM_cpt | hN_cpt
  · exact sion_minimax_of_compact_left hM_ne hN_ne hM_conv hN_conv hM_cpt
      F hF_usc hF_qconc hF_lsc hF_qconv
  · -- Symmetric case `IsCompact N`: apply compact-left version to `(N, M)` and `(n, m) ↦ -F m n`
    let F' : N → M → ℝ := fun n m => -F m n
    have hF'_usc : ∀ m : M, UpperSemicontinuous (fun n : N => F' n m) := by
      intro m
      rw [upperSemicontinuous_iff_isOpen_preimage]
      intro y
      have h_eq : ((fun n : N => -F m n) ⁻¹' Set.Iio y) =
          (fun n : N => F m n) ⁻¹' Set.Ioi (-y) := by
        ext n; simp [neg_lt]
      rw [h_eq]
      exact (hF_lsc m).isOpen_preimage (-y)
    have hF'_qconc : ∀ (m : M) (r : ℝ), Convex ℝ (Subtype.val '' {n : N | r ≤ F' n m}) := by
      intro m r
      have h_eq : {n : N | r ≤ -F m n} = {n : N | F m n ≤ -r} := by
        ext n; simp [le_neg]
      rw [h_eq]
      exact hF_qconv m (-r)
    have hF'_lsc : ∀ n : N, LowerSemicontinuous (fun m : M => F' n m) := by
      intro n
      rw [lowerSemicontinuous_iff_isOpen_preimage]
      intro y
      have h_eq : ((fun m : M => -F m n) ⁻¹' Set.Ioi y) =
          (fun m : M => F m n) ⁻¹' Set.Iio (-y) := by
        ext m; simp [lt_neg]
      rw [h_eq]
      exact (hF_usc n).isOpen_preimage (-y)
    have hF'_qconv : ∀ (n : N) (r : ℝ), Convex ℝ (Subtype.val '' {m : M | F' n m ≤ r}) := by
      intro n r
      have h_eq : {m : M | -F m n ≤ r} = {m : M | -r ≤ F m n} := by
        ext m; simp [neg_le]
      rw [h_eq]
      exact hF_qconc n (-r)
    have h_dual := sion_minimax_of_compact_left hN_ne hM_ne hN_conv hM_conv hN_cpt
      F' hF'_usc hF'_qconc hF'_lsc hF'_qconv
    simp only [F', EReal.coe_neg] at h_dual
    have h_lhs : (⨆ n : N, ⨅ m : M, -(F m n : EReal)) =
        -(⨅ n : N, ⨆ m : M, (F m n : EReal)) := by
      simp_rw [ereal_iInf_neg]
      exact ereal_iSup_neg _
    have h_rhs : (⨅ m : M, ⨆ n : N, -(F m n : EReal)) =
        -(⨆ m : M, ⨅ n : N, (F m n : EReal)) := by
      simp_rw [ereal_iSup_neg]
      exact ereal_iInf_neg _
    rw [h_lhs, h_rhs] at h_dual
    have h_neg := congr_arg Neg.neg h_dual
    simpa [neg_neg] using h_neg.symm

/-! ## Corollary D.7: Separately Continuous Affine Payoffs on `G × P(K)` -/

/-- Convex combination `t ρ₁ + (1 - t) ρ₂` of two Borel probability measures on `K`
for `t ∈ [0, 1]`. -/
noncomputable def probMeasureConvexComb {K : Type*} [MeasurableSpace K]
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ρ₁ ρ₂ : MeasureTheory.ProbabilityMeasure K) :
    MeasureTheory.ProbabilityMeasure K :=
  ⟨ENNReal.ofReal t • (ρ₁ : MeasureTheory.Measure K) +
      ENNReal.ofReal (1 - t) • (ρ₂ : MeasureTheory.Measure K), by
    constructor
    simp only [MeasureTheory.Measure.add_apply, MeasureTheory.Measure.smul_apply,
      MeasureTheory.measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add ht0 (sub_nonneg.mpr ht1), add_sub_cancel, ENNReal.ofReal_one]⟩

/-- Integration of a continuous real-valued function on a compact space against
`probMeasureConvexComb` is the corresponding convex combination of integrals. -/
lemma integral_probMeasureConvexComb
    {K : Type*} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ρ₁ ρ₂ : MeasureTheory.ProbabilityMeasure K) (f : C(K, ℝ)) :
    (∫ ω, f ω ∂(probMeasureConvexComb t ht0 ht1 ρ₁ ρ₂ : MeasureTheory.Measure K)) =
      t * (∫ ω, f ω ∂(ρ₁ : MeasureTheory.Measure K)) +
      (1 - t) * (∫ ω, f ω ∂(ρ₂ : MeasureTheory.Measure K)) := by
  have hf1 : MeasureTheory.Integrable f (ρ₁ : MeasureTheory.Measure K) :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have hf2 : MeasureTheory.Integrable f (ρ₂ : MeasureTheory.Measure K) :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  change ∫ ω, f ω ∂(ENNReal.ofReal t • (ρ₁ : MeasureTheory.Measure K) +
      ENNReal.ofReal (1 - t) • (ρ₂ : MeasureTheory.Measure K)) = _
  rw [MeasureTheory.integral_add_measure (hf1.smul_measure ENNReal.ofReal_ne_top)
        (hf2.smul_measure ENNReal.ofReal_ne_top),
      MeasureTheory.integral_smul_measure, MeasureTheory.integral_smul_measure,
      ENNReal.toReal_ofReal ht0, ENNReal.toReal_ofReal (sub_nonneg.mpr ht1)]
  simp [smul_eq_mul]

/-- **Corollary D.7 (Separately continuous affine payoffs, `cor:sion-affine`)**:
Let `K` be a nonempty compact metric space, `G ⊆ C(K, ℝ)` be nonempty and convex (equipped with
the uniform norm on `C(K, ℝ)`), and `ProbabilityMeasure K` be the space of Borel probability
measures on `K` equipped with the weak topology. If `F : G → ProbabilityMeasure K → ℝ` is
separately continuous and affine in each variable, then
`inf_{g ∈ G} sup_{ρ ∈ P(K)} F(g, ρ) = sup_{ρ ∈ P(K)} inf_{g ∈ G} F(g, ρ)`. -/
theorem cor_sion_affine
    {K : Type*} [MetricSpace K] [CompactSpace K] [Nonempty K] [MeasurableSpace K] [BorelSpace K]
    (G : Set C(K, ℝ)) (hG_ne : G.Nonempty) (hG_conv : Convex ℝ G)
    (F : G → MeasureTheory.ProbabilityMeasure K → ℝ)
    (hF_cont_left : ∀ ρ : MeasureTheory.ProbabilityMeasure K, Continuous (fun g : G => F g ρ))
    (hF_cont_right : ∀ g : G, Continuous (fun ρ : MeasureTheory.ProbabilityMeasure K => F g ρ))
    (hF_aff_left : ∀ (g₁ g₂ : G) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
      (ρ : MeasureTheory.ProbabilityMeasure K),
      F ⟨t • g₁.1 + (1 - t) • g₂.1,
          hG_conv g₁.2 g₂.2 ht0 (sub_nonneg.mpr ht1) (add_sub_cancel t 1)⟩ ρ =
        t * F g₁ ρ + (1 - t) * F g₂ ρ)
    (hF_aff_right : ∀ (g : G) (ρ₁ ρ₂ : MeasureTheory.ProbabilityMeasure K)
      (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1),
      F g (probMeasureConvexComb t ht0 ht1 ρ₁ ρ₂) =
        t * F g ρ₁ + (1 - t) * F g ρ₂) :
    (⨅ g : G, ⨆ ρ : MeasureTheory.ProbabilityMeasure K, (F g ρ : EReal)) =
      (⨆ ρ : MeasureTheory.ProbabilityMeasure K, ⨅ g : G, (F g ρ : EReal)) := by
  -- Embed ProbabilityMeasure K affinely and homeomorphically into the locally convex space C(K, ℝ) → ℝ
  let ι : MeasureTheory.ProbabilityMeasure K → (C(K, ℝ) → ℝ) :=
    fun ρ f => ∫ ω, f ω ∂(ρ : MeasureTheory.Measure K)
  have hι_cont : Continuous ι :=
    continuous_pi fun f => MeasureTheory.ProbabilityMeasure.continuous_integral_continuousMap f
  have hι_inj : Function.Injective ι := by
    intro ρ₁ ρ₂ h_eq
    have h_tend1 : Filter.Tendsto (fun _ : ℕ => ρ₁) Filter.atTop (nhds ρ₁) := tendsto_const_nhds
    have h_tend2 : Filter.Tendsto (fun _ : ℕ => ρ₁) Filter.atTop (nhds ρ₂) := by
      rw [MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
      intro f
      have hf_eq : (∫ ω, f ω ∂(ρ₁ : MeasureTheory.Measure K)) =
          (∫ ω, f ω ∂(ρ₂ : MeasureTheory.Measure K)) :=
        congr_fun h_eq ⟨f, f.continuous⟩
      simp_rw [hf_eq]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique h_tend1 h_tend2
  let M : Set (C(K, ℝ) → ℝ) := Set.range ι
  have hM_ne : M.Nonempty := by
    let k₀ : K := Classical.arbitrary K
    let ρ₀ : MeasureTheory.ProbabilityMeasure K := ⟨MeasureTheory.Measure.dirac k₀, inferInstance⟩
    exact ⟨ι ρ₀, ρ₀, rfl⟩
  have hM_cpt : IsCompact M := isCompact_range hι_cont
  have hM_conv : Convex ℝ M := by
    rintro _ ⟨ρ₁, rfl⟩ _ ⟨ρ₂, rfl⟩ a b ha hb hab
    have hb_eq : b = 1 - a := by linarith
    have ha1 : a ≤ 1 := by linarith
    refine ⟨probMeasureConvexComb a ha ha1 ρ₁ ρ₂, ?_⟩
    ext f
    simp only [ι, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hb_eq]
    exact integral_probMeasureConvexComb a ha ha1 ρ₁ ρ₂ f

  -- Homeomorphism e : ProbabilityMeasure K ≃ₜ M
  let e₀ : MeasureTheory.ProbabilityMeasure K ≃ M := Equiv.ofInjective ι hι_inj
  have he₀_cont : Continuous e₀ := hι_cont.rangeFactorization
  let e : MeasureTheory.ProbabilityMeasure K ≃ₜ M :=
    e₀.toHomeomorphOfContinuousClosed he₀_cont he₀_cont.isClosedMap
  have he_val : ∀ ρ : MeasureTheory.ProbabilityMeasure K, (e ρ).1 = ι ρ := fun _ => rfl
  have he_symm_ι : ∀ m : M, ι (e.symm m) = m.1 := by
    intro m
    have := he_val (e.symm m)
    simpa using this.symm
  have he_symm_aff : ∀ (m₁ m₂ : M) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1),
      e.symm ⟨t • m₁.1 + (1 - t) • m₂.1,
          hM_conv m₁.2 m₂.2 ht0 (sub_nonneg.mpr ht1) (add_sub_cancel t 1)⟩ =
        probMeasureConvexComb t ht0 ht1 (e.symm m₁) (e.symm m₂) := by
    intro m₁ m₂ t ht0 ht1
    apply hι_inj
    rw [he_symm_ι]
    ext f
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ι]
    rw [integral_probMeasureConvexComb t ht0 ht1 (e.symm m₁) (e.symm m₂) f]
    have h1 : (∫ ω, f ω ∂((e.symm m₁ : MeasureTheory.ProbabilityMeasure K) : MeasureTheory.Measure K)) =
        m₁.1 f := congr_fun (he_symm_ι m₁) f
    have h2 : (∫ ω, f ω ∂((e.symm m₂ : MeasureTheory.ProbabilityMeasure K) : MeasureTheory.Measure K)) =
        m₂.1 f := congr_fun (he_symm_ι m₂) f
    rw [h1, h2]

  -- Apply Theorem D.6 (`thm_sion_minimax`) to `F_tilde (m, g) := F g (e.symm m)` on `M × G`
  let F_tilde : M → G → ℝ := fun m g => F g (e.symm m)
  have hFt_usc : ∀ g : G, UpperSemicontinuous (fun m : M => F_tilde m g) :=
    fun g => ((hF_cont_right g).comp e.symm.continuous).upperSemicontinuous
  have hFt_qconc : ∀ (g : G) (r : ℝ), Convex ℝ (Subtype.val '' {m : M | r ≤ F_tilde m g}) := by
    rintro g r _ ⟨m₁, hm₁, rfl⟩ _ ⟨m₂, hm₂, rfl⟩ a b ha hb hab
    have hb_eq : b = 1 - a := by linarith
    have ha1 : a ≤ 1 := by linarith
    let m : M := ⟨a • m₁.1 + (1 - a) • m₂.1,
      hM_conv m₁.2 m₂.2 ha (sub_nonneg.mpr ha1) (add_sub_cancel a 1)⟩
    refine ⟨m, ?_, by simp [m, hb_eq]⟩
    change r ≤ F g (e.symm m)
    rw [he_symm_aff m₁ m₂ a ha ha1, hF_aff_right g (e.symm m₁) (e.symm m₂) a ha ha1]
    have hm₁' : r ≤ F g (e.symm m₁) := hm₁
    have hm₂' : r ≤ F g (e.symm m₂) := hm₂
    nlinarith
  have hFt_lsc : ∀ m : M, LowerSemicontinuous (fun g : G => F_tilde m g) :=
    fun m => (hF_cont_left (e.symm m)).lowerSemicontinuous
  have hFt_qconv : ∀ (m : M) (r : ℝ), Convex ℝ (Subtype.val '' {g : G | F_tilde m g ≤ r}) := by
    rintro m r _ ⟨g₁, hg₁, rfl⟩ _ ⟨g₂, hg₂, rfl⟩ a b ha hb hab
    have hb_eq : b = 1 - a := by linarith
    have ha1 : a ≤ 1 := by linarith
    let g : G := ⟨a • g₁.1 + (1 - a) • g₂.1,
      hG_conv g₁.2 g₂.2 ha (sub_nonneg.mpr ha1) (add_sub_cancel a 1)⟩
    refine ⟨g, ?_, by simp [g, hb_eq]⟩
    change F g (e.symm m) ≤ r
    rw [hF_aff_left g₁ g₂ a ha ha1 (e.symm m)]
    have hg₁' : F g₁ (e.symm m) ≤ r := hg₁
    have hg₂' : F g₂ (e.symm m) ≤ r := hg₂
    nlinarith

  have h_sion := thm_sion_minimax M G hM_ne hG_ne hM_conv hG_conv (Or.inl hM_cpt)
    F_tilde hFt_usc hFt_qconc hFt_lsc hFt_qconv
  -- Reindex `M` back to `ProbabilityMeasure K` via the equivalence `e`
  have h_lhs_eq : (⨆ ρ : MeasureTheory.ProbabilityMeasure K, ⨅ g : G, (F g ρ : EReal)) =
      (⨆ m : M, ⨅ g : G, (F_tilde m g : EReal)) := by
    rw [← e.toEquiv.iSup_comp]
    congr 1; ext ρ; congr 1; ext g
    simp [F_tilde]
  have h_rhs_eq : (⨅ g : G, ⨆ ρ : MeasureTheory.ProbabilityMeasure K, (F g ρ : EReal)) =
      (⨅ g : G, ⨆ m : M, (F_tilde m g : EReal)) := by
    congr 1; ext g
    rw [← e.toEquiv.iSup_comp]
    congr 1; ext ρ
    simp [F_tilde]
  rw [h_rhs_eq, h_lhs_eq]
  exact h_sion.symm

end TraceSqrt
