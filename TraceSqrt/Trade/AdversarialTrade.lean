import TraceSqrt.Defs
import TraceSqrt.Trade.TradeLottery

set_option maxHeartbeats 4000000

/-!
# Theorem 3.4: Adversarial Contextual Bilateral Trade (`thm:trade-direct`)

From *Contextual Search and Bilateral Trade with a Trace-Square-Root Potential*
(Section 3.2, Algorithm 4 and Theorem 3.4 `thm:trade-direct`).
-/

namespace TraceSqrt

/-- **Theorem 3.4 (Adversarial Bilateral Trade, `thm:trade-direct`)**:
For every `d ≥ 1`, hidden pair `(s, b) ∈ K = B_2^d × B_2^d`, full-history adaptive unit-ball
context strategy `ctxPolicy` (`𝓕_{t-1}`), and horizon `T`:
1. `0 ≤ E[Reg_T]` and `0 ≤ E[Φ(m_{T+1}, R_{T+1}, w)]`,
2. `E[Reg_T] + 2^{10} E[Φ(m_{T+1}, R_{T+1}, w)] ≤ 2^{10} Φ(m_1, R_1, w) + 1 ≤ 2^{12} √d + 1`, and
3. `E[Reg_T] ≤ 2^{12} √d + 1` (Eq. (22)). -/
theorem thm_adversarial_bilateral_trade (d : ℕ) (hd : 0 < d)
    (s b : Fin d → ℝ) (hs : vecL2Norm s ≤ 1) (hb : vecL2Norm b ≤ 1)
    (ctxPolicy : List (AdvTradeObs d) → (Fin d → ℝ))
    (hCtx : ∀ hist : List (AdvTradeObs d), vecL2Norm (ctxPolicy hist) ≤ 1)
    (T : ℕ) :
    let initR := alg4InitScale d
    let out := alg4RunExpected s b ctxPolicy T 0 0 0 initR initR []
    0 ≤ out.1 ∧
    0 ≤ out.2 ∧
    out.1 + (2 ^ 10 : ℝ) * out.2 ≤
      (2 ^ 10 : ℝ) * tradeQuadPotential 0 0 initR initR s b + 1 ∧
    (2 ^ 10 : ℝ) * tradeQuadPotential 0 0 initR initR s b + 1 ≤
      (2 ^ 12 : ℝ) * Real.sqrt d + 1 ∧
    out.1 ≤ (2 ^ 12 : ℝ) * Real.sqrt d + 1 :=
by
  have h_norm_nonneg : ∀ v : Fin d → ℝ, 0 ≤ vecL2Norm v :=
    fun _ => Real.sqrt_nonneg _

  have h_norm_sq : ∀ v : Fin d → ℝ, vecL2Norm v ^ 2 = ∑ i, (v i) ^ 2 :=
    fun v => Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (v i))

  have h_agent_nonneg :
      ∀ (mVec zVec : Fin d → ℝ) (R : Matrix (Fin d) (Fin d) ℝ),
        R.PosDef → 0 ≤ agentQuadPotential mVec R zVec := by
    intro mVec zVec R hR
    unfold agentQuadPotential
    have h1 : 0 ≤ Matrix.trace R := hR.posSemidef.trace_nonneg
    have h2 : 0 ≤ dotProduct (zVec - mVec) (R⁻¹.mulVec (zVec - mVec)) := by
      simpa using hR.inv.posSemidef.dotProduct_mulVec_nonneg (zVec - mVec)
    exact add_nonneg h1 h2

  have h_pot_nonneg :
      ∀ (mS mB : Fin d → ℝ) (RS RB : Matrix (Fin d) (Fin d) ℝ),
        RS.PosDef → RB.PosDef → 0 ≤ tradeQuadPotential mS mB RS RB s b := by
    intro mS mB RS RB hRS hRB
    unfold tradeQuadPotential
    exact add_nonneg (h_agent_nonneg mS s RS hRS) (h_agent_nonneg mB b RB hRB)

  have h_lottery_exist :
      ∀ (mS mB : Fin d → ℝ) (RS RB : Matrix (Fin d) (Fin d) ℝ),
        RS.PosDef → RB.PosDef →
        ∀ x : Fin d → ℝ, vecL2Norm x ≤ 1 →
        ∀ γ : ℝ, 0 < γ → γ ≤ 1 →
          ∃ lottery : List (ℝ × TradePlan d), IsValidTradeLottery mS mB RS RB x γ lottery := by
    intro mS mB RS RB hRS hRB x hx γ hγ_pos hγ_le
    obtain ⟨lottery, _, _, hnn, hsum, _, hcost⟩ :=
      lem_trade_lottery mS mB RS RB hRS hRB x hx γ hγ_pos hγ_le
    exact ⟨lottery, hnn, hsum, hcost⟩

  have h_init :
      (alg4InitScale d).PosDef ∧
      (2 ^ 10 : ℝ) * tradeQuadPotential 0 0 (alg4InitScale d) (alg4InitScale d) s b + 1 ≤
        (2 ^ 12 : ℝ) * Real.sqrt d + 1 := by
    have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
    have hsqrt_pos : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd_pos
    have hsqrt_ne : Real.sqrt d ≠ 0 := hsqrt_pos.ne'
    have hinv_pos : 0 < (Real.sqrt d)⁻¹ := inv_pos.mpr hsqrt_pos
    have hR_pd : (alg4InitScale d).PosDef := by
      unfold alg4InitScale
      exact Matrix.PosDef.one.smul hinv_pos
    have hR_inv : (alg4InitScale d)⁻¹ = Real.sqrt d • (1 : Matrix (Fin d) (Fin d) ℝ) := by
      apply Matrix.inv_eq_right_inv
      unfold alg4InitScale
      rw [Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul, inv_mul_cancel₀ hsqrt_ne, one_smul]
    have h_trace : Matrix.trace (alg4InitScale d) = Real.sqrt d := by
      unfold alg4InitScale
      rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
      have hsq : Real.sqrt d ^ 2 = (d : ℝ) := Real.sq_sqrt (Nat.cast_nonneg d)
      calc (Real.sqrt d)⁻¹ * (d : ℝ)
          = (Real.sqrt d)⁻¹ * (Real.sqrt d ^ 2) := by rw [hsq]
        _ = Real.sqrt d := by field_simp
    have h_agent_bound :
        ∀ z : Fin d → ℝ, vecL2Norm z ≤ 1 →
          agentQuadPotential 0 (alg4InitScale d) z ≤ 2 * Real.sqrt d := by
      intro z hz
      have h_quad :
          dotProduct (z - 0) ((alg4InitScale d)⁻¹.mulVec (z - 0)) ≤ Real.sqrt d := by
        rw [sub_zero, hR_inv, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
        have h_dot_eq : dotProduct z z = vecL2Norm z ^ 2 := by
          rw [h_norm_sq z]
          simp [dotProduct, sq]
        have hz_nn : 0 ≤ vecL2Norm z := h_norm_nonneg z
        have hz_sq : vecL2Norm z ^ 2 ≤ 1 := by nlinarith
        rw [h_dot_eq]
        nlinarith [hsqrt_pos]
      unfold agentQuadPotential
      linarith [h_trace, h_quad]
    refine ⟨hR_pd, ?_⟩
    have hs_pot := h_agent_bound s hs
    have hb_pot := h_agent_bound b hb
    unfold tradeQuadPotential
    linarith [hs_pot, hb_pot]

  have h_telescoping :
      ∀ (n roundIdx : ℕ) (mS mB : Fin d → ℝ) (RS RB : Matrix (Fin d) (Fin d) ℝ)
        (hist : List (AdvTradeObs d)),
        RS.PosDef → RB.PosDef →
        0 ≤ (alg4RunExpected s b ctxPolicy n roundIdx mS mB RS RB hist).1 ∧
        0 ≤ (alg4RunExpected s b ctxPolicy n roundIdx mS mB RS RB hist).2 ∧
        (alg4RunExpected s b ctxPolicy n roundIdx mS mB RS RB hist).1 +
          (2 ^ 10 : ℝ) * (alg4RunExpected s b ctxPolicy n roundIdx mS mB RS RB hist).2 ≤
          (2 ^ 10 : ℝ) * tradeQuadPotential mS mB RS RB s b +
            (1 / ((roundIdx : ℝ) + 1) - 1 / ((roundIdx : ℝ) + (n : ℝ) + 1)) := by
    intro n
    induction n with
    | zero =>
      intro roundIdx mS mB RS RB hist hRS hRB
      dsimp only [alg4RunExpected]
      simp only [Nat.cast_zero, add_zero, sub_self]
      exact ⟨le_rfl, h_pot_nonneg mS mB RS RB hRS hRB, by linarith⟩
    | succ n ih =>
      intro roundIdx mS mB RS RB hist hRS hRB
      dsimp only [alg4RunExpected]
      set x := ctxPolicy hist
      have hx : vecL2Norm x ≤ 1 := hCtx hist
      set t : ℝ := (roundIdx : ℝ) + 1
      have hr_nn : (0 : ℝ) ≤ (roundIdx : ℝ) := Nat.cast_nonneg roundIdx
      have ht_ge_one : 1 ≤ t := by linarith
      have ht_pos : 0 < t := by linarith
      have ht1_pos : 0 < t + 1 := by linarith
      set γ : ℝ := 1 / (t * (t + 1))
      have htt1_pos : 0 < t * (t + 1) := mul_pos ht_pos ht1_pos
      have hγ_pos : 0 < γ := div_pos one_pos htt1_pos
      have hγ_le : γ ≤ 1 := by
        rw [div_le_iff₀ htt1_pos]
        nlinarith
      have h_ex : ∃ lottery : List (ℝ × TradePlan d),
          IsValidTradeLottery mS mB RS RB x γ lottery :=
        h_lottery_exist mS mB RS RB hRS hRB x hx γ hγ_pos hγ_le
      set lottery := alg4SelectLottery mS mB RS RB x roundIdx
      have h_lot_valid : IsValidTradeLottery mS mB RS RB x γ lottery := by
        change IsValidTradeLottery mS mB RS RB x γ (alg4SelectLottery mS mB RS RB x roundIdx)
        unfold alg4SelectLottery
        dsimp only
        split_ifs with h_if
        · exact Classical.choose_spec h_if
        · exact False.elim (h_if h_ex)
      obtain ⟨hlot_nn, hlot_sum, hlot_cost⟩ := h_lot_valid
      let evalAtom (entry : (ℝ × TradePlan d) × ℕ) : ℝ × ℝ :=
        let w := entry.1.1
        let plan := entry.1.2
        let idx := entry.2
        let p : ℝ := plan.price
        let S := dotProduct x s
        let B := dotProduct x b
        if S ≤ p ∧ p ≤ B then
          let sub := alg4RunExpected s b ctxPolicy n (roundIdx + 1)
            plan.mS1 plan.mB1 plan.RS1 plan.RB1 (hist ++ [⟨x, idx, plan, p, 1⟩])
          (w * sub.1, w * sub.2)
        else
          let ell := max (B - S) 0
          let sub := alg4RunExpected s b ctxPolicy n (roundIdx + 1)
            plan.mS0 plan.mB0 plan.RS0 plan.RB0 (hist ++ [⟨x, idx, plan, p, 0⟩])
          (w * (ell + sub.1), w * sub.2)
      let Δ_rem : ℝ :=
        1 / (((roundIdx + 1 : ℕ) : ℝ) + 1) -
          1 / (((roundIdx + 1 : ℕ) : ℝ) + (n : ℝ) + 1)
      have h_entry_bound :
          ∀ (wp : ℝ × TradePlan d) (idx : ℕ), wp ∈ lottery →
            0 ≤ (evalAtom (wp, idx)).1 ∧
            0 ≤ (evalAtom (wp, idx)).2 ∧
            (evalAtom (wp, idx)).1 + (2 ^ 10 : ℝ) * (evalAtom (wp, idx)).2 ≤
              wp.1 * planRoundCost x wp.2 s b + wp.1 * Δ_rem := by
        intro wp idx hwp
        have hw : 0 ≤ wp.1 := hlot_nn wp hwp
        set w := wp.1
        set plan := wp.2
        set p : ℝ := (plan.price : ℝ)
        by_cases htr : dotProduct x s ≤ p ∧ p ≤ dotProduct x b
        · have h_eval : evalAtom (wp, idx) =
              (w * (alg4RunExpected s b ctxPolicy n (roundIdx + 1)
                plan.mS1 plan.mB1 plan.RS1 plan.RB1 (hist ++ [⟨x, idx, plan, p, 1⟩])).1,
               w * (alg4RunExpected s b ctxPolicy n (roundIdx + 1)
                plan.mS1 plan.mB1 plan.RS1 plan.RB1 (hist ++ [⟨x, idx, plan, p, 1⟩])).2) := by
            simp [evalAtom, w, plan, p, htr]
          have h_cost_eq : planRoundCost x plan s b =
              (2 ^ 10 : ℝ) * tradeQuadPotential plan.mS1 plan.mB1 plan.RS1 plan.RB1 s b := by
            simp [planRoundCost, p, htr]
          obtain ⟨h_ih1_nn1, h_ih1_nn2, h_ih1⟩ :=
            ih (roundIdx + 1) plan.mS1 plan.mB1 plan.RS1 plan.RB1
              (hist ++ [⟨x, idx, plan, p, 1⟩]) plan.posDef_RS1 plan.posDef_RB1
          have h_mul := mul_le_mul_of_nonneg_left h_ih1 hw
          rw [h_eval, h_cost_eq]
          dsimp only
          refine ⟨mul_nonneg hw h_ih1_nn1, mul_nonneg hw h_ih1_nn2, ?_⟩
          change w * (alg4RunExpected s b ctxPolicy n (roundIdx + 1)
              plan.mS1 plan.mB1 plan.RS1 plan.RB1 (hist ++ [⟨x, idx, plan, p, 1⟩])).1 +
            (2 ^ 10 : ℝ) * (w * (alg4RunExpected s b ctxPolicy n (roundIdx + 1)
              plan.mS1 plan.mB1 plan.RS1 plan.RB1 (hist ++ [⟨x, idx, plan, p, 1⟩])).2) ≤
            w * ((2 ^ 10 : ℝ) * tradeQuadPotential plan.mS1 plan.mB1 plan.RS1 plan.RB1 s b) +
              w * Δ_rem
          linarith [h_mul]
        · have h_eval : evalAtom (wp, idx) =
              (w * (max (dotProduct x b - dotProduct x s) 0 +
                (alg4RunExpected s b ctxPolicy n (roundIdx + 1)
                  plan.mS0 plan.mB0 plan.RS0 plan.RB0 (hist ++ [⟨x, idx, plan, p, 0⟩])).1),
               w * (alg4RunExpected s b ctxPolicy n (roundIdx + 1)
                plan.mS0 plan.mB0 plan.RS0 plan.RB0 (hist ++ [⟨x, idx, plan, p, 0⟩])).2) := by
            simp [evalAtom, w, plan, p, htr]
          have h_cost_eq : planRoundCost x plan s b =
              max (dotProduct x b - dotProduct x s) 0 +
                (2 ^ 10 : ℝ) * tradeQuadPotential plan.mS0 plan.mB0 plan.RS0 plan.RB0 s b := by
            simp [planRoundCost, p, htr]
          obtain ⟨h_ih0_nn1, h_ih0_nn2, h_ih0⟩ :=
            ih (roundIdx + 1) plan.mS0 plan.mB0 plan.RS0 plan.RB0
              (hist ++ [⟨x, idx, plan, p, 0⟩]) plan.posDef_RS0 plan.posDef_RB0
          have h_ell_nn : 0 ≤ max (dotProduct x b - dotProduct x s) 0 := le_max_right _ _
          have h_ih0' :
              max (dotProduct x b - dotProduct x s) 0 +
                (alg4RunExpected s b ctxPolicy n (roundIdx + 1)
                  plan.mS0 plan.mB0 plan.RS0 plan.RB0 (hist ++ [⟨x, idx, plan, p, 0⟩])).1 +
                (2 ^ 10 : ℝ) * (alg4RunExpected s b ctxPolicy n (roundIdx + 1)
                  plan.mS0 plan.mB0 plan.RS0 plan.RB0 (hist ++ [⟨x, idx, plan, p, 0⟩])).2 ≤
              (max (dotProduct x b - dotProduct x s) 0 +
                (2 ^ 10 : ℝ) * tradeQuadPotential plan.mS0 plan.mB0 plan.RS0 plan.RB0 s b) +
                Δ_rem := by
            linarith [h_ih0]
          have h_mul := mul_le_mul_of_nonneg_left h_ih0' hw
          rw [h_eval, h_cost_eq]
          dsimp only
          exact ⟨mul_nonneg hw (add_nonneg h_ell_nn h_ih0_nn1), mul_nonneg hw h_ih0_nn2,
            by linarith [h_mul]⟩
      have h_list_sum :
          ∀ (L : List (ℝ × TradePlan d)) (k : ℕ),
            (∀ (wp : ℝ × TradePlan d) (idx : ℕ), wp ∈ L →
              0 ≤ (evalAtom (wp, idx)).1 ∧
              0 ≤ (evalAtom (wp, idx)).2 ∧
              (evalAtom (wp, idx)).1 + (2 ^ 10 : ℝ) * (evalAtom (wp, idx)).2 ≤
                wp.1 * planRoundCost x wp.2 s b + wp.1 * Δ_rem) →
            0 ≤ (((L.zipIdx k).map evalAtom).map Prod.fst).sum ∧
            0 ≤ (((L.zipIdx k).map evalAtom).map Prod.snd).sum ∧
            (((L.zipIdx k).map evalAtom).map Prod.fst).sum +
              (2 ^ 10 : ℝ) * (((L.zipIdx k).map evalAtom).map Prod.snd).sum ≤
            (L.map (fun wp => wp.1 * planRoundCost x wp.2 s b)).sum +
              (L.map Prod.fst).sum * Δ_rem := by
        intro L
        induction L with
        | nil =>
          intro k _
          simp
        | cons hd_wp tl ihL =>
          intro k hL
          obtain ⟨h_hd1, h_hd2, h_hd3⟩ := hL hd_wp k (List.mem_cons.mpr (Or.inl rfl))
          obtain ⟨h_tl1, h_tl2, h_tl3⟩ :=
            ihL (k + 1) (fun wp idx hwp => hL wp idx (List.mem_cons.mpr (Or.inr hwp)))
          simp only [List.zipIdx_cons, List.map_cons, List.sum_cons]
          exact ⟨by linarith, by linarith, by linarith⟩
      obtain ⟨h_sum_nn1, h_sum_nn2, h_sum_step⟩ := h_list_sum lottery 0 h_entry_bound
      have h_cost_step := hlot_cost s b hs hb
      rw [hlot_sum, one_mul] at h_sum_step
      have h_tele_eq :
          γ + Δ_rem =
            1 / ((roundIdx : ℝ) + 1) - 1 / ((roundIdx : ℝ) + ((n + 1 : ℕ) : ℝ) + 1) := by
        have h_cast1 : (((roundIdx + 1 : ℕ) : ℝ) + 1) = t + 1 := by
          simp [t]
        have h_cast2 :
            (((roundIdx + 1 : ℕ) : ℝ) + (n : ℝ) + 1) =
              (roundIdx : ℝ) + ((n + 1 : ℕ) : ℝ) + 1 := by
          push_cast
          ring
        have h_frac : 1 / (t * (t + 1)) + 1 / (t + 1) = 1 / t := by
          field_simp
          ring
        change 1 / (t * (t + 1)) +
            (1 / (((roundIdx + 1 : ℕ) : ℝ) + 1) -
              1 / (((roundIdx + 1 : ℕ) : ℝ) + (n : ℝ) + 1)) =
          1 / t - 1 / ((roundIdx : ℝ) + ((n + 1 : ℕ) : ℝ) + 1)
        rw [h_cast1, h_cast2]
        linarith [h_frac]
      refine ⟨h_sum_nn1, h_sum_nn2, ?_⟩
      change (((lottery.zipIdx 0).map evalAtom).map Prod.fst).sum +
          (2 ^ 10 : ℝ) * (((lottery.zipIdx 0).map evalAtom).map Prod.snd).sum ≤
        (2 ^ 10 : ℝ) * tradeQuadPotential mS mB RS RB s b +
          (1 / ((roundIdx : ℝ) + 1) - 1 / ((roundIdx : ℝ) + ((n + 1 : ℕ) : ℝ) + 1))
      linarith [h_sum_step, h_cost_step, h_tele_eq]

  dsimp only
  obtain ⟨hR_pd, h_init_bound⟩ := h_init
  obtain ⟨h_reg_nn, h_pot_nn, h_run⟩ :=
    h_telescoping T 0 0 0 (alg4InitScale d) (alg4InitScale d) [] hR_pd hR_pd
  have hT_nn : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
  have h_inv_nn : 0 ≤ 1 / ((0 : ℝ) + (T : ℝ) + 1) := by positivity
  have h_one_div : (1 : ℝ) / ((0 : ℝ) + 1) = 1 := by norm_num
  have h_amortized :
      (alg4RunExpected s b ctxPolicy T 0 0 0 (alg4InitScale d) (alg4InitScale d) []).1 +
        (2 ^ 10 : ℝ) *
          (alg4RunExpected s b ctxPolicy T 0 0 0 (alg4InitScale d) (alg4InitScale d) []).2 ≤
        (2 ^ 10 : ℝ) * tradeQuadPotential 0 0 (alg4InitScale d) (alg4InitScale d) s b + 1 := by
    linarith [h_run, h_inv_nn, h_one_div]
  refine ⟨h_reg_nn, h_pot_nn, h_amortized, h_init_bound, ?_⟩
  linarith [h_amortized, h_init_bound, h_pot_nn]

/-- **Pure-regret statement of Theorem 3.4 (Eq. (22))**:
For every `d ≥ 1`, hidden pair `(s, b) ∈ K = B_2^d × B_2^d`, full-history adaptive unit-ball
context strategy `ctxPolicy` (`𝓕_{t-1}`), and horizon `T`, Algorithm 4's expected cumulative
regret satisfies `E[∑_{t=1}^T ℓ_t] ≤ 2^{12} √d + 1`. -/
theorem cor_adversarial_bilateral_trade_regret (d : ℕ) (hd : 0 < d)
    (s b : Fin d → ℝ) (hs : vecL2Norm s ≤ 1) (hb : vecL2Norm b ≤ 1)
    (ctxPolicy : List (AdvTradeObs d) → (Fin d → ℝ))
    (hCtx : ∀ hist : List (AdvTradeObs d), vecL2Norm (ctxPolicy hist) ≤ 1)
    (T : ℕ) :
    (alg4RunExpected s b ctxPolicy T 0 0 0 (alg4InitScale d) (alg4InitScale d) []).1 ≤
      (2 ^ 12 : ℝ) * Real.sqrt d + 1 :=
  (thm_adversarial_bilateral_trade d hd s b hs hb ctxPolicy hCtx T).2.2.2.2

/-- **Theorem 3.4 for randomized adaptive context strategies**:
For any probability space `(Ξ, ν_ctx)` driving the context adversary's randomization and any
full-history context policy `ctxPolicy : Ξ → List (AdvTradeObs d) → (Fin d → ℝ)` with
`‖ctxPolicy ξ hist‖₂ ≤ 1`, Algorithm 4 satisfies `E[∑_{t=1}^T ℓ_t] ≤ 2^{12} √d + 1` both as an
unconditional extended Lebesgue integral and (when `AEStronglyMeasurable`) as a Bochner integral. -/
theorem thm_adversarial_bilateral_trade_rand_ctx (d : ℕ) (hd : 0 < d)
    (s b : Fin d → ℝ) (hs : vecL2Norm s ≤ 1) (hb : vecL2Norm b ≤ 1)
    {Ξ : Type*} [MeasurableSpace Ξ]
    (ν_ctx : MeasureTheory.Measure Ξ) [MeasureTheory.IsProbabilityMeasure ν_ctx]
    (ctxPolicy : Ξ → List (AdvTradeObs d) → (Fin d → ℝ))
    (hCtx : ∀ (ξ : Ξ) (hist : List (AdvTradeObs d)), vecL2Norm (ctxPolicy ξ hist) ≤ 1)
    (T : ℕ) :
    let L : Ξ → ℝ :=
      fun ξ => (alg4RunExpected s b (ctxPolicy ξ) T 0 0 0 (alg4InitScale d) (alg4InitScale d) []).1
    let B : ℝ := (2 ^ 12 : ℝ) * Real.sqrt d + 1
    (∀ ξ : Ξ, 0 ≤ L ξ ∧ L ξ ≤ B) ∧
    (∫⁻ ξ, ENNReal.ofReal (L ξ) ∂ν_ctx ≤ ENNReal.ofReal B) ∧
    (MeasureTheory.AEStronglyMeasurable L ν_ctx →
      MeasureTheory.Integrable L ν_ctx ∧
      0 ≤ (∫ ξ, L ξ ∂ν_ctx) ∧
      (∫ ξ, L ξ ∂ν_ctx) ≤ B) := by
  dsimp only
  have h_pw : ∀ ξ : Ξ,
      0 ≤ (alg4RunExpected s b (ctxPolicy ξ) T 0 0 0 (alg4InitScale d) (alg4InitScale d) []).1 ∧
      (alg4RunExpected s b (ctxPolicy ξ) T 0 0 0 (alg4InitScale d) (alg4InitScale d) []).1 ≤
        (2 ^ 12 : ℝ) * Real.sqrt d + 1 := by
    intro ξ
    have h := thm_adversarial_bilateral_trade d hd s b hs hb (ctxPolicy ξ) (hCtx ξ) T
    exact ⟨h.1, h.2.2.2.2⟩
  have h_exp := prob_expectation_le_of_pointwise ν_ctx _ ((2 ^ 12 : ℝ) * Real.sqrt d + 1) h_pw
  exact ⟨h_pw, h_exp.1, h_exp.2⟩

end TraceSqrt
