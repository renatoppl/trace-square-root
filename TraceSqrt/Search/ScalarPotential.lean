import TraceSqrt.Defs

set_option maxHeartbeats 4000000

/-!
# Lemma C.1: One-Dimensional Potential Decrease (`lem:scalar-potential`)

From *Contextual Search and Bilateral Trade with a Trace-Square-Root Potential*
(Appendix C.1, Lemma C.1).
-/

namespace TraceSqrt

/-- **Lemma C.1 (One-dimensional potential decrease, `lem:scalar-potential`)**:
For any `m, z ∈ ℝ` and `r > 0`, under uniform `ε ∈ {-1, 1}`:
1. `E_ε |z - P| = max(|z - m|, r / 2)`,
2. `φ(m, r, z) - E_ε φ(m⁺, r⁺, z) ≥ (1 / 6) E_ε |z - P|`, and
3. `E_ε φ(m⁺, r⁺, z) ≤ φ(m, r, z) - r / 12`. -/
theorem lem_scalar_potential (m r z : ℝ) (hr : 0 < r) :
    rademacherExpect (fun eps => |z - scalarPostedPrice m r eps|) = max |z - m| (r / 2) ∧
    scalarPotential m r z -
        rademacherExpect (fun eps =>
          scalarPotential (scalarUpdatedCenter m r z eps) (scalarUpdatedScale m r z eps) z) ≥
      (1 / 6 : ℝ) * rademacherExpect (fun eps => |z - scalarPostedPrice m r eps|) ∧
    rademacherExpect (fun eps =>
        scalarPotential (scalarUpdatedCenter m r z eps) (scalarUpdatedScale m r z eps) z) ≤
      scalarPotential m r z - r / 12 :=
by
  have hr_ne : r ≠ 0 := hr.ne'
  have ⟨h_loss, h_drift⟩ :
      rademacherExpect (fun eps => |z - scalarPostedPrice m r eps|) = max |z - m| (r / 2) ∧
      scalarPotential m r z -
          rademacherExpect (fun eps =>
            scalarPotential (scalarUpdatedCenter m r z eps) (scalarUpdatedScale m r z eps) z) ≥
        (1 / 6 : ℝ) * rademacherExpect (fun eps => |z - scalarPostedPrice m r eps|) := by
    rcases lt_or_ge z (m - r / 2) with hzL | hzM
    · have h_abs_neg : |z - scalarPostedPrice m r (-1)| = -(z - (m + (r / 2) * (-1))) := by
        unfold scalarPostedPrice
        exact abs_of_neg (by linarith)
      have h_abs_pos : |z - scalarPostedPrice m r 1| = -(z - (m + (r / 2) * 1)) := by
        unfold scalarPostedPrice
        exact abs_of_neg (by linarith)
      have h_abs_mid : |z - m| = m - z := by
        rw [abs_of_neg (by linarith)]
        ring
      have h_max : max |z - m| (r / 2) = m - z := by
        rw [h_abs_mid]
        exact max_eq_left (by linarith)
      have h1 : rademacherExpect (fun eps => |z - scalarPostedPrice m r eps|) =
          max |z - m| (r / 2) := by
        unfold rademacherExpect
        dsimp only
        rw [h_abs_neg, h_abs_pos, h_max]
        ring
      have hY_neg : scalarFeedback m r z (-1) = -1 := by
        unfold scalarFeedback paperSign scalarPostedPrice
        exact if_neg (by linarith)
      have hY_pos : scalarFeedback m r z 1 = -1 := by
        unfold scalarFeedback paperSign scalarPostedPrice
        exact if_neg (by linarith)
      have h_eq : scalarPotential m r z -
          rademacherExpect (fun eps =>
            scalarPotential (scalarUpdatedCenter m r z eps) (scalarUpdatedScale m r z eps) z) =
          (2 / 3 : ℝ) * (m - z) - r / 4 := by
        unfold rademacherExpect scalarUpdatedCenter scalarUpdatedScale
        dsimp only
        rw [hY_neg, hY_pos]
        unfold scalarPotential
        norm_num
        field_simp
        ring
      refine ⟨h1, ?_⟩
      rw [h_eq, h1, h_max]
      linarith
    · rcases lt_or_ge z (m + r / 2) with hzM2 | hzR
      · have h_abs_neg : |z - scalarPostedPrice m r (-1)| = z - (m + (r / 2) * (-1)) := by
          unfold scalarPostedPrice
          exact abs_of_nonneg (by linarith)
        have h_abs_pos : |z - scalarPostedPrice m r 1| = -(z - (m + (r / 2) * 1)) := by
          unfold scalarPostedPrice
          exact abs_of_neg (by linarith)
        have h_abs_mid : |z - m| ≤ r / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
        have h_max : max |z - m| (r / 2) = r / 2 := max_eq_right h_abs_mid
        have h1 : rademacherExpect (fun eps => |z - scalarPostedPrice m r eps|) =
            max |z - m| (r / 2) := by
          unfold rademacherExpect
          dsimp only
          rw [h_abs_neg, h_abs_pos, h_max]
          ring
        have hY_neg : scalarFeedback m r z (-1) = 1 := by
          unfold scalarFeedback paperSign scalarPostedPrice
          exact if_pos (by linarith)
        have hY_pos : scalarFeedback m r z 1 = -1 := by
          unfold scalarFeedback paperSign scalarPostedPrice
          exact if_neg (by linarith)
        have h_eq : scalarPotential m r z -
            rademacherExpect (fun eps =>
              scalarPotential (scalarUpdatedCenter m r z eps) (scalarUpdatedScale m r z eps) z) =
            r / 6 - (m - z) ^ 2 / (3 * r) := by
          unfold rademacherExpect scalarUpdatedCenter scalarUpdatedScale
          dsimp only
          rw [hY_neg, hY_pos]
          unfold scalarPotential
          norm_num
          field_simp
          ring
        have h_sq_div : (m - z) ^ 2 / (3 * r) ≤ r / 12 := by
          rw [div_le_iff₀ (by linarith : 0 < 3 * r)]
          nlinarith
        refine ⟨h1, ?_⟩
        rw [h_eq, h1, h_max]
        linarith
      · have h_abs_neg : |z - scalarPostedPrice m r (-1)| = z - (m + (r / 2) * (-1)) := by
          unfold scalarPostedPrice
          exact abs_of_nonneg (by linarith)
        have h_abs_pos : |z - scalarPostedPrice m r 1| = z - (m + (r / 2) * 1) := by
          unfold scalarPostedPrice
          exact abs_of_nonneg (by linarith)
        have h_abs_mid : |z - m| = z - m := abs_of_nonneg (by linarith)
        have h_max : max |z - m| (r / 2) = z - m := by
          rw [h_abs_mid]
          exact max_eq_left (by linarith)
        have h1 : rademacherExpect (fun eps => |z - scalarPostedPrice m r eps|) =
            max |z - m| (r / 2) := by
          unfold rademacherExpect
          dsimp only
          rw [h_abs_neg, h_abs_pos, h_max]
          ring
        have hY_neg : scalarFeedback m r z (-1) = 1 := by
          unfold scalarFeedback paperSign scalarPostedPrice
          exact if_pos (by linarith)
        have hY_pos : scalarFeedback m r z 1 = 1 := by
          unfold scalarFeedback paperSign scalarPostedPrice
          exact if_pos (by linarith)
        have h_eq : scalarPotential m r z -
            rademacherExpect (fun eps =>
              scalarPotential (scalarUpdatedCenter m r z eps) (scalarUpdatedScale m r z eps) z) =
            (2 / 3 : ℝ) * (z - m) - r / 4 := by
          unfold rademacherExpect scalarUpdatedCenter scalarUpdatedScale
          dsimp only
          rw [hY_neg, hY_pos]
          unfold scalarPotential
          norm_num
          field_simp
          ring
        refine ⟨h1, ?_⟩
        rw [h_eq, h1, h_max]
        linarith
  have h_max_ge : r / 2 ≤ max |z - m| (r / 2) := le_max_right |z - m| (r / 2)
  refine ⟨h_loss, h_drift, ?_⟩
  linarith

end TraceSqrt
