import LNS.Definitions
import LNS.BasicIxRx
import LNS.BasicRounding
import LNS.Lemma51
import LNS.Lemma52

namespace LNS

private lemma theorem53_bound (fix : FixedPoint) (hr1 : 0 ≤ r) (hr2 : r ≤ Δ):
    |x - fix.rnd y + fix.rnd (r * fix.rnd z)| ≤ |x - y + r * z| + Δ * fix.ε + |(y - fix.rnd y) - (r * fix.rnd z - fix.rnd (r * fix.rnd z))| := by
  set s1 := y - fix.rnd y
  set s2 := r * (fix.rnd z - z)
  set s3 := r * fix.rnd  z - fix.rnd (r * fix.rnd z)
  rw [(by ring : x - fix.rnd y + fix.rnd (r * fix.rnd z) = (x - y + r * z) + s2 + (s1 - s3))]
  apply le_trans (abs_add _ _)
  apply add_le_add_right
  apply le_trans (abs_add _ _)
  apply add_le_add_left
  rw [abs_mul, abs_of_nonneg hr1]
  exact mul_le_mul hr2 (fix.hrnd_sym _) (abs_nonneg _) (by linarith)

private lemma theorem53_bound' (fix : FixedPoint) (hr1 : 0 ≤ r) (hr2 : r ≤ Δ):
    |x - fix.rnd y + fix.rnd (r * fix.rnd z)| ≤ |x - y + r * z| + (2 + Δ) * fix.ε := by
  apply le_trans (theorem53_bound fix hr1 hr2)
  have : |y - fix.rnd y - (r * fix.rnd z - fix.rnd (r * fix.rnd z))| ≤ fix.ε + fix.ε := by
    apply le_trans (abs_sub _ _)
    exact add_le_add (fix.hrnd _) (fix.hrnd _)
  linarith

private lemma theorem53_bound_dir (fix : FixedPointDir) (hr1 : 0 ≤ r) (hr2 : r ≤ Δ):
    |x - fix.rnd y + fix.rnd (r * fix.rnd z)| ≤ |x - y + r * z| + (1 + Δ) * fix.ε := by
  apply le_trans (theorem53_bound fix hr1 hr2)
  have : |y - fix.rnd y - (r * fix.rnd z - fix.rnd (r * fix.rnd z))| ≤ fix.ε := fix.abs_rnd_sub_rnd _ _
  linarith

theorem Theorem53_Ep (fix : FixedPoint) {i r Δ : ℝ} (hi : i ≤ 0) (hr1 : 0 ≤ r) (hr2 : r < Δ) :
    |Ep_fix fix i r| < (Ep 0 Δ) + (2 + Δ) * fix.ε := by
  apply lt_of_le_of_lt (theorem53_bound' fix hr1 (le_of_lt hr2))
  apply add_lt_add_right
  exact Lemma51 hi hr1 hr2

theorem Theorem53_Ep_dir (fix : FixedPointDir) {i r Δ : ℝ} (hi : i ≤ 0) (hr1 : 0 ≤ r) (hr2 : r < Δ) :
    |Ep_fix fix i r| < (Ep 0 Δ) + (1 + Δ) * fix.ε := by
  apply lt_of_le_of_lt (theorem53_bound_dir fix hr1 (le_of_lt hr2))
  apply add_lt_add_right
  exact Lemma51 hi hr1 hr2

theorem Theorem53_Em (fix : FixedPoint) {i₀ i r Δ : ℝ} (hi₀ : i₀ < 0) (hi : i ≤ i₀) (hr1 : 0 ≤ r) (hr2 : r < Δ) :
    |Em_fix fix i r| < (Em i₀ Δ) + (2 + Δ) * fix.ε := by
  apply lt_of_le_of_lt (theorem53_bound' fix hr1 (le_of_lt hr2))
  apply add_lt_add_right
  have : |Φm (i - r) - Φm i + r * deriv Φm i| = |Em i r| := by
    unfold Em; rw [← abs_neg]; congr; ring
  rw [this]
  exact Lemma52 hi₀ hi hr1 hr2

theorem Theorem53_Em_dir (fix : FixedPointDir) {i₀ i r Δ : ℝ} (hi₀ : i₀ < 0) (hi : i ≤ i₀) (hr1 : 0 ≤ r) (hr2 : r < Δ) :
    |Em_fix fix i r| < (Em i₀ Δ) + (1 + Δ) * fix.ε := by
  apply lt_of_le_of_lt (theorem53_bound_dir fix hr1 (le_of_lt hr2))
  apply add_lt_add_right
  have : |Φm (i - r) - Φm i + r * deriv Φm i| = |Em i r| := by
    unfold Em; rw [← abs_neg]; congr; ring
  rw [this]
  exact Lemma52 hi₀ hi hr1 hr2

/- A first order Taylor approximation error bound for Φ⁺ -/

theorem Theorem53_ΦTp (fix : FixedPoint) {x Δ : ℝ} (hd : 0 < Δ) (hx : x ≤ 0) :
    |Φp x - ΦTp_fix fix Δ x| < Ep 0 Δ + (2 + Δ) * fix.ε := by
  have eq : Φp x - ΦTp_fix fix Δ x = Ep_fix fix (Iₓ Δ x) (Rₓ Δ x) := by
    unfold ΦTp_fix Ep_fix; rw [i_sub_r_eq_x]; ring_nf
  rw [eq]
  apply Theorem53_Ep fix _ (rx_nonneg hd x) (rx_lt_delta hd x)
  rw [← x_neg_iff_ix_neg hd]; exact hx

theorem Theorem53_ΦTp_dir (fix : FixedPointDir) {x Δ : ℝ} (hd : 0 < Δ) (hx : x ≤ 0) :
    |Φp x - ΦTp_fix fix Δ x| < Ep 0 Δ + (1 + Δ) * fix.ε := by
  have eq : Φp x - ΦTp_fix fix Δ x = Ep_fix fix (Iₓ Δ x) (Rₓ Δ x) := by
    unfold ΦTp_fix Ep_fix; rw [i_sub_r_eq_x]; ring_nf
  rw [eq]
  apply Theorem53_Ep_dir fix _ (rx_nonneg hd x) (rx_lt_delta hd x)
  rw [← x_neg_iff_ix_neg hd]; exact hx

/- A first order Taylor approximation error bound for Φ⁻ -/

theorem Theorem53_ΦTm (fix : FixedPoint) {x₀ x Δ : ℝ} (hd : 0 < Δ) (hx₀ : x₀ ≤ -Δ) (hx : x ≤ x₀) :
    |Φm x - ΦTm_fix fix Δ x| < Em (Iₓ Δ x₀) Δ + (2 + Δ) * fix.ε := by
  have eq : Φm x - ΦTm_fix fix Δ x = Em_fix fix (Iₓ Δ x) (Rₓ Δ x) := by
    unfold ΦTm_fix Em_fix; rw [i_sub_r_eq_x]; ring_nf
  rw [eq]
  exact Theorem53_Em fix (ix_lt_zero hd hx₀) (ix_monotone hd hx) (rx_nonneg hd x) (rx_lt_delta hd x)

theorem Theorem53_ΦTm_dir (fix : FixedPointDir) {x₀ x Δ : ℝ} (hd : 0 < Δ) (hx₀ : x₀ ≤ -Δ) (hx : x ≤ x₀) :
    |Φm x - ΦTm_fix fix Δ x| < Em (Iₓ Δ x₀) Δ + (1 + Δ) * fix.ε := by
  have eq : Φm x - ΦTm_fix fix Δ x = Em_fix fix (Iₓ Δ x) (Rₓ Δ x) := by
    unfold ΦTm_fix Em_fix; rw [i_sub_r_eq_x]; ring_nf
  rw [eq]
  exact Theorem53_Em_dir fix (ix_lt_zero hd hx₀) (ix_monotone hd hx) (rx_nonneg hd x) (rx_lt_delta hd x)

/- A first order Taylor approximation of Φ⁻ for x ≤ -1 -/

theorem Theorem53_ΦTm' (fix : FixedPoint) {x Δ : ℝ}
    (hdn : ∃ n : ℕ, 1 = n * Δ) (hx : x ≤ -1) :
    |Φm x - ΦTm_fix fix Δ x| < Em (-1) Δ + (2 + Δ) * fix.ε := by
  have hx₀ : -1 ≤ -Δ := by rw [neg_le_neg_iff]; exact div_one_imp_le_one hdn
  rw [← ix_eq_neg_one hdn]
  exact Theorem53_ΦTm fix (div_one_imp_pos hdn) hx₀ hx

theorem Theorem53_ΦTm_dir' (fix : FixedPointDir) {x Δ : ℝ}
    (hdn : ∃ n : ℕ, 1 = n * Δ) (hx : x ≤ -1) :
    |Φm x - ΦTm_fix fix Δ x| < Em (-1) Δ + (1 + Δ) * fix.ε := by
  have hx₀ : -1 ≤ -Δ := by rw [neg_le_neg_iff]; exact div_one_imp_le_one hdn
  rw [← ix_eq_neg_one hdn]
  exact Theorem53_ΦTm_dir fix (div_one_imp_pos hdn) hx₀ hx

/- Taylor approximations of Φ⁺ and Φ⁻ -/

noncomputable def ΦTp_approx (fix : FixedPoint) {Δ : ℝ} (hd : 0 < Δ) : FunApprox Φp (Set.Iic 0) := {
  fe := ΦTp_fix fix Δ
  err := Ep 0 Δ + (2 + Δ) * fix.ε
  herr := fun _ => le_of_lt ∘ Theorem53_ΦTp fix hd
}

noncomputable def ΦTp_dir_approx (fix : FixedPointDir) {Δ : ℝ} (hd : 0 < Δ) : FunApprox Φp (Set.Iic 0) := {
  fe := ΦTp_fix fix Δ
  err := Ep 0 Δ + (1 + Δ) * fix.ε
  herr := fun _ => le_of_lt ∘ Theorem53_ΦTp_dir fix hd
}

noncomputable def ΦTm_approx (fix : FixedPoint) {Δ : ℝ} (hdn : ∃ n : ℕ, 1 = n * Δ) : FunApprox Φm (Set.Iic (-1)) := {
  fe := ΦTm_fix fix Δ
  err := Em (-1) Δ + (2 + Δ) * fix.ε
  herr := fun _ => le_of_lt ∘ Theorem53_ΦTm' fix hdn
}

noncomputable def ΦTm_dir_approx (fix : FixedPointDir) {Δ : ℝ} (hdn : ∃ n : ℕ, 1 = n * Δ) : FunApprox Φm (Set.Iic (-1)) := {
  fe := ΦTm_fix fix Δ
  err := Em (-1) Δ + (1 + Δ) * fix.ε
  herr := fun _ => le_of_lt ∘ Theorem53_ΦTm_dir' fix hdn
}
