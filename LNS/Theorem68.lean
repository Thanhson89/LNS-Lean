import LNS.Definitions
import LNS.BasicIxRx
import LNS.BasicRounding
import LNS.Lemma63
import LNS.Lemma64
import LNS.Lemma67
import LNS.Lemma51
import LNS.Lemma52

namespace LNS

open Real

variable (fix : FixedPoint)

lemma Φp_eq_EC (hr1 : 0 ≤ r) (hr2 : r < Δ) :
    Φp (i - r) = Φp i - r * (deriv Φp i) + (Ep i Δ) * (Qp Δ i r) := by
  have ep : Ep i Δ > 0 := by apply Ep_r_pos; linarith
  unfold Qp; field_simp; unfold Ep; ring_nf

lemma Φm_eq_EC (hi: i ≤ -1) (hr1 : 0 ≤ r) (hr2 : r < Δ) :
    Φm (i - r) = Φm i - r * (deriv Φm i) - (Em i Δ) * (Qm Δ i r) := by
  have ep : Em i Δ > 0 := by apply Em_r_pos; linarith; linarith
  unfold Qm; field_simp; unfold Em; ring_nf

lemma Qp_lt_1 (hr1 : 0 ≤ r) (hr2 : r < Δ) : |fix.rnd (Qp Δ c r)| ≤ 1 := by
  have i1 : Qp Δ c r ≥ 0 := by
    unfold Qp; apply div_nonneg; apply Ep_r_nonneg; linarith; apply Ep_r_nonneg; linarith
  have i2 : fix.rnd (Qp Δ c r) ≥ 0 := by
    rw [← fix.rnd_0]; apply fix.rnd_mono; assumption
  have e1 : |fix.rnd (Qp Δ c r)| = fix.rnd (Qp Δ c r) := by apply abs_of_nonneg; assumption
  rw [e1, ← fix.rnd_1]; apply fix.rnd_mono
  unfold Qp; apply le_of_lt
  have i3 : Ep c Δ >0 := by apply Ep_r_pos; linarith
  apply (div_lt_one i3).mpr
  apply Ep_r_strictMonoOn
  any_goals simp
  any_goals linarith

lemma Qm_lt_1 (hc: c ≤ -1) (hr1 : 0 ≤ r) (hr2 : r < Δ) : |fix.rnd (Qm Δ c r)| ≤ 1 := by
  have i1 : Qm Δ c r ≥ 0 := by
    unfold Qm; apply div_nonneg
    apply Em_r_nonneg; linarith; assumption
    apply Em_r_nonneg; linarith; linarith
  have i2 : fix.rnd (Qm Δ c r) ≥ 0 := by
    rw [← fix.rnd_0]; apply fix.rnd_mono; assumption
  have e1 : |fix.rnd (Qm Δ c r)| = fix.rnd (Qm Δ c r) := by apply abs_of_nonneg; assumption
  rw [e1, ← fix.rnd_1]; apply fix.rnd_mono
  unfold Qm; apply le_of_lt
  have i3 : Em c Δ >0 := by apply Em_r_pos; linarith; linarith
  apply (div_lt_one i3).mpr
  apply Em_r_strictMonoOn
  any_goals simp
  any_goals linarith

lemma sum_8_abs1 (a1 a2 a3 a4 a5 a6 a7 a8 : ℝ) :
    |a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8| ≤ |a1| + |a2| + |a3| + |a4| + |a5| + |a6| + |a7| + |a8| := by
  have i1 : |a1+a2+a3+a4+a5+a6+a7+a8| ≤ |a1+a2+a3+a4+a5+a6+a7|+|a8| := by apply abs_add
  have i2 : |a1+a2+a3+a4+a5+a6+a7| ≤ |a1+a2+a3+a4+a5+a6|+|a7| := by apply abs_add
  have i3 : |a1+a2+a3+a4+a5+a6| ≤ |a1+a2+a3+a4+a5|+|a6| := by apply abs_add
  have i4 : |a1+a2+a3+a4+a5| ≤ |a1+a2+a3+a4|+|a5| := by apply abs_add
  have i5 : |a1+a2+a3+a4| ≤ |a1+a2+a3|+|a4| := by apply abs_add
  have i6 : |a1+a2+a3| ≤ |a1+a2|+|a3| := by apply abs_add
  have i7 : |a1+a2| ≤ |a1|+|a2| := by apply abs_add
  linarith

lemma sum_8_abs2 (a1 a2 a3 a4 a5 a6 a7 a8 : ℝ) :
    |a1 + a2 + a3 - (a4 + a5 + a6 + a7 + a8)| ≤ |a1| + |a2| + |a3| + |a4| + |a5| + |a6| + |a7| + |a8| := by
  have i1 : |a1+a2+a3-(a4 + a5 + a6 + a7 + a8)| ≤ |a1+a2+a3| + |a4+a5+a6+a7+a8| := by apply abs_sub
  have i2 : |a1+a2+a3| ≤ |a1+a2|+|a3| := by apply abs_add
  have i3 : |a1+a2| ≤ |a1|+|a2| := by apply abs_add
  have i4 : |a4+a5+a6+a7+a8| ≤ |a4+a5+a6+a7|+|a8| := by apply abs_add
  have i5 : |a4+a5+a6+a7| ≤ |a4+a5+a6|+|a7| := by apply abs_add
  have i6 : |a4+a5+a6| ≤ |a4+a5|+|a6| := by apply abs_add
  have i7 : |a4+a5| ≤ |a4|+|a5| := by apply abs_add
  linarith

theorem Theorem68p (hi : i ≤ 0)(hc : c ≤ 0) (hr1 : 0 ≤ r) (hr2 : r < Δ) (hΔ : ΔP < Δ) (hΔP : 0 < ΔP) :
    |EECp_fix fix Δ ΔP c i r| ≤ (4 + Δ) * fix.ε + Ep 0 Δ * (QRp Δ + QIp Δ ΔP + fix.ε) := by
  set rr := (Int.floor (r / ΔP) * ΔP)
  set a1 := Φp i - fix.rnd (Φp i)
  set a2 := fix.rnd (r * fix.rnd (deriv Φp i) ) - r * fix.rnd (deriv Φp i)
  set a3 := r * (fix.rnd (deriv Φp i) -  (deriv Φp i))
  set a4 := (Ep i Δ)*((Qp Δ i r) - (Qp Δ c r))
  set a5 := (Ep i Δ)*((Qp Δ c r) - (Qp Δ c rr))
  set a6 := (Ep i Δ)*((Qp Δ c rr) - (fix.rnd (Qp Δ c rr)))
  set a7 := (fix.rnd (Qp Δ c rr)) * ((Ep i Δ) - (fix.rnd (Ep i Δ) ) )
  set a8 := (fix.rnd (Ep i Δ) ) * (fix.rnd (Qp Δ c rr)) - fix.rnd (fix.rnd (Ep i Δ) * fix.rnd (Qp Δ c rr))
  have irr0 : rr ≥ 0 := by
    apply mul_nonneg; simp; apply Int.floor_nonneg.mpr
    apply div_nonneg
    any_goals linarith
  have irr1 : r - rr ≥ 0 := by
    simp only [ge_iff_le, sub_nonneg]
    have i2 : Int.floor (r / ΔP) * ΔP ≤ r / ΔP * ΔP := by
      apply mul_le_mul; apply Int.floor_le; simp only [le_refl]; linarith
      apply div_nonneg
      any_goals linarith
    have e0 : r / ΔP * ΔP = r := by field_simp
    rw [e0] at i2; exact i2
  have eq0 : Φp (i - r) - EECp fix Δ ΔP c i r = a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 := by
    rw [Φp_eq_EC hr1 hr2]; unfold EECp; ring_nf
  have i0 : |Ep i Δ| ≤ (Ep 0 Δ) := by apply Lemma51' hi; linarith; linarith
  have i01 :  Ep 0 Δ ≥ 0 := by
    have : |Ep i Δ| ≥ 0 := by simp
    linarith
  have i1 : |a1| ≤ fix.ε := by apply fix.hrnd
  have i2 : |a2| ≤ fix.ε := by apply fix.hrnd_sym
  have i3 : |a3| ≤ Δ * fix.ε := by
    have e1 : |a3| = |r| * |fix.rnd (deriv Φp i) -  (deriv Φp i)| := by apply abs_mul
    have e2 : |r| = r := by apply abs_of_nonneg hr1
    rw [e1,e2]; apply mul_le_mul; linarith; apply fix.hrnd_sym; simp only [abs_nonneg]; linarith
  have i4 : |a4| ≤ (Ep 0 Δ) * (QRp Δ) := by
    have e1 : |a4| = |Ep i Δ| * |(Qp Δ i r) - (Qp Δ c r)| := by apply abs_mul
    have i1 : |(Qp Δ i r) - (Qp Δ c r)| ≤ (QRp Δ) := by apply Lemma63; any_goals linarith
    rw [e1] ; apply mul_le_mul; assumption; assumption; simp; assumption
  have i5 : |a5| ≤ (Ep 0 Δ) * (QIp Δ ΔP) := by
    have e1 : |a5| = |Ep i Δ| * |(Qp Δ c r) - (Qp Δ c rr)| := by apply abs_mul
    have i1 : |(Qp Δ c r) - (Qp Δ c rr)| ≤ QIp Δ ΔP := by apply Lemma64; any_goals linarith
    rw [e1] ; apply mul_le_mul; assumption; assumption; simp; assumption
  have i6 : |a6| ≤ (Ep 0 Δ) * fix.ε := by
    have e1 : |a6| = |Ep i Δ| * |(Qp Δ c rr) - (fix.rnd (Qp Δ c rr))| := by apply abs_mul
    have i1 : |(Qp Δ c rr) - (fix.rnd (Qp Δ c rr))| ≤ fix.ε := by apply fix.hrnd
    rw [e1] ; apply mul_le_mul; assumption; assumption; simp; assumption
  have i7 : |a7| ≤ fix.ε := by
    have e1 : |a7| = |fix.rnd (Qp Δ c rr)| * |(Ep i Δ) - (fix.rnd (Ep i Δ) )| := by apply abs_mul
    have i1 : |(Ep i Δ) - (fix.rnd (Ep i Δ) )| ≤ fix.ε := by apply fix.hrnd
    have i2 : |fix.rnd (Qp Δ c rr)| ≤ (1:ℝ) := by
      apply Qp_lt_1 fix irr0 (by linarith)
    have e2 : fix.ε = (1:ℝ) * fix.ε := by simp
    rw [e1, e2] ; apply mul_le_mul; assumption; assumption; simp; linarith
  have i8 : |a8| ≤  fix.ε := by apply fix.hrnd
  have isum : |EECp_fix fix Δ ΔP c i r| ≤ |a1|+|a2|+|a3|+|a4|+|a5|+|a6|+|a7|+|a8| := by
    unfold EECp_fix; rw [eq0]; apply sum_8_abs1
  linarith

theorem Theorem68m (hi : i ≤ -1)(hc : c ≤ -1) (hr1 : 0 ≤ r) (hr2 : r < Δ) (hΔ: ΔP < Δ) (hΔP: 0 < ΔP) :
    |EECm_fix fix Δ ΔP c i r| ≤ (4 + Δ) * fix.ε + Em (-1) Δ * (QRm Δ + QIm Δ ΔP + fix.ε) := by
  set rr := (Int.floor (r / ΔP) * ΔP)
  set a1 := Φm i - fix.rnd (Φm i)
  set a2 := fix.rnd (r * fix.rnd (deriv Φm i) ) - r * fix.rnd (deriv Φm i)
  set a3 := r * (fix.rnd (deriv Φm i) -  (deriv Φm i))
  set a4 := (Em i Δ)*((Qm Δ i r) - (Qm Δ c r))
  set a5 := (Em i Δ)*((Qm Δ c r) - (Qm Δ c rr))
  set a6 := (Em i Δ)*((Qm Δ c rr) - (fix.rnd (Qm Δ c rr)))
  set a7 := (fix.rnd (Qm Δ c rr)) * ((Em i Δ) - (fix.rnd (Em i Δ) ) )
  set a8 := (fix.rnd (Em i Δ) ) * (fix.rnd (Qm Δ c rr)) - fix.rnd (fix.rnd (Em i Δ) * fix.rnd (Qm Δ c rr))
  have irr0 : rr ≥ 0 := by
    apply mul_nonneg; simp; apply Int.floor_nonneg.mpr
    apply div_nonneg
    any_goals linarith
  have irr1 : r - rr ≥ 0 := by
    simp only [ge_iff_le, sub_nonneg]
    have i2 : Int.floor (r / ΔP) * ΔP ≤ r / ΔP * ΔP := by
      apply mul_le_mul; apply Int.floor_le; simp only [le_refl]; linarith
      apply div_nonneg
      any_goals linarith
    have e0 : r / ΔP * ΔP = r := by field_simp
    rw [e0] at i2; exact i2
  have eq0 : Φm (i - r) - EECm fix Δ ΔP c i r = a1 + a2 + a3 - (a4 + a5 + a6 + a7 + a8) := by
    rw [Φm_eq_EC hi hr1 hr2]; unfold EECm; ring_nf
  have i0 : |Em i Δ| ≤ Em (-1) Δ := by apply Lemma52' (by norm_num : -1 < (0 : ℝ)) hi ; linarith; linarith
  have i01 : Em (-1) Δ ≥ 0 := by
    have : |Em i Δ| ≥ 0 := by simp only [ge_iff_le, abs_nonneg]
    linarith
  have i1 : |a1| ≤ fix.ε := by apply fix.hrnd
  have i2 : |a2| ≤ fix.ε := by apply fix.hrnd_sym
  have i3 : |a3| ≤ Δ * fix.ε := by
    have e1 : |a3| = |r| * |fix.rnd (deriv Φm i) -  (deriv Φm i)| := by apply abs_mul
    have e2 : |r| = r := by apply abs_of_nonneg hr1
    rw [e1,e2]; apply mul_le_mul; linarith; apply fix.hrnd_sym; simp only [abs_nonneg]; linarith
  have i4 : |a4| ≤ (Em (-1) Δ) * (QRm Δ) := by
    have e1 : |a4| = |Em i Δ| * |(Qm Δ i r) - (Qm Δ c r)| := by apply abs_mul
    have i1 : |(Qm Δ i r) - (Qm Δ c r)| ≤ (QRm Δ) := by apply Lemma66; any_goals linarith
    rw [e1] ; apply mul_le_mul; assumption; assumption; simp; assumption
  have i5 : |a5| ≤ (Em (-1) Δ) * (QIm Δ ΔP) := by
    have e1 : |a5| = |Em i Δ| * |(Qm Δ c r) - (Qm Δ c rr)| := by apply abs_mul
    have i1 : |(Qm Δ c r) - (Qm Δ c rr)| ≤ QIm Δ ΔP := by apply Lemma67; any_goals linarith
    rw [e1] ; apply mul_le_mul; assumption; assumption; simp; assumption
  have i6 : |a6| ≤ (Em (-1) Δ) * fix.ε := by
    have e1 : |a6| = |Em i Δ| * |(Qm Δ c rr) - (fix.rnd (Qm Δ c rr))| := by apply abs_mul
    have i1 : |(Qm Δ c rr) - (fix.rnd (Qm Δ c rr))| ≤ fix.ε := by apply fix.hrnd
    rw [e1] ; apply mul_le_mul; assumption; assumption; simp; assumption
  have i7 : |a7| ≤ fix.ε := by
    have e1 : |a7| = |fix.rnd (Qm Δ c rr)| * |(Em i Δ) - (fix.rnd (Em i Δ) )| := by apply abs_mul
    have i1 : |(Em i Δ) - (fix.rnd (Em i Δ) )| ≤ fix.ε := by apply fix.hrnd
    have i2 : |fix.rnd (Qm Δ c rr)| ≤ (1:ℝ) := by
      apply Qm_lt_1 fix hc irr0 (by linarith)
    have e2 : fix.ε = (1:ℝ) * fix.ε := by simp
    rw [e1, e2] ; apply mul_le_mul; assumption; assumption; simp; linarith
  have i8 : |a8| ≤ fix.ε := by apply fix.hrnd
  have isum : |EECm_fix fix Δ ΔP c i r| ≤ |a1|+|a2|+|a3|+|a4|+|a5|+|a6|+|a7|+|a8| := by
    unfold EECm_fix; rw [eq0]; apply sum_8_abs2
  linarith

theorem Theorem68_ΦECp (hc : c ≤ 0) (hΔ : ΔP < Δ) (hΔP : 0 < ΔP) (hx : x ≤ 0) :
    |Φp x - ΦECp_fix fix Δ ΔP c x| ≤ (4 + Δ) * fix.ε + Ep 0 Δ * (QRp Δ + QIp Δ ΔP + fix.ε) := by
  have hd : 0 < Δ := by linarith
  have eq : Φp x - ΦECp_fix fix Δ ΔP c x = EECp_fix fix Δ ΔP c (Iₓ Δ x) (Rₓ Δ x) := by
    unfold ΦECp_fix EECp_fix; rw [i_sub_r_eq_x]
  rw [eq]
  apply Theorem68p fix _ hc _ _ hΔ hΔP
  · rw [← x_neg_iff_ix_neg] <;> assumption
  · exact rx_nonneg hd x
  · exact rx_lt_delta hd x

theorem Theorem68_ΦECm {Δ ΔP : ℝ} (hc : c ≤ -1) (hΔ : ΔP < Δ) (hΔP : 0 < ΔP)
    (hdn : ∃ n : ℕ, 1 = n * Δ) (hx : x ≤ -1) :
    |Φm x - ΦECm_fix fix Δ ΔP c x| ≤ (4 + Δ) * fix.ε + Em (-1) Δ * (QRm Δ + QIm Δ ΔP + fix.ε) := by
  have hd : 0 < Δ := by linarith
  have eq : Φm x - ΦECm_fix fix Δ ΔP c x = EECm_fix fix Δ ΔP c (Iₓ Δ x) (Rₓ Δ x) := by
    unfold ΦECm_fix EECm_fix; rw [i_sub_r_eq_x]
  rw [eq]
  apply Theorem68m fix _ hc (rx_nonneg hd x) (rx_lt_delta hd x) hΔ hΔP
  rw [← ix_eq_neg_one hdn]
  apply ix_monotone hd hx


/- Error correction approximations of Φ⁺ and Φ⁻ -/

noncomputable def ΦECp_approx (fix : FixedPoint) {c Δ ΔP : ℝ} (hc : c ≤ 0) (hΔ : ΔP < Δ) (hΔP : 0 < ΔP) : FunApprox Φp (Set.Iic 0) := {
  fe := ΦECp_fix fix Δ ΔP c
  err := (4 + Δ) * fix.ε + Ep 0 Δ * (QRp Δ + QIp Δ ΔP + fix.ε)
  herr := fun _ => Theorem68_ΦECp fix hc hΔ hΔP
}

noncomputable def ΦECm_approx (fix : FixedPoint) {c Δ ΔP : ℝ} (hc : c ≤ -1) (hΔ : ΔP < Δ)
    (hΔP : 0 < ΔP) (hdn : ∃ n : ℕ, 1 = n * Δ) : FunApprox Φm (Set.Iic (-1)) := {
  fe := ΦECm_fix fix Δ ΔP c
  err := (4 + Δ) * fix.ε + Em (-1) Δ * (QRm Δ + QIm Δ ΔP + fix.ε)
  herr := fun _ => Theorem68_ΦECm fix hc hΔ hΔP hdn
}
