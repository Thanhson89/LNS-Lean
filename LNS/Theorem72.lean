import LNS.Definitions
import LNS.BasicIxRx
import LNS.BasicRounding
import LNS.Lemma71

namespace LNS

noncomputable section

open Real

private lemma phi_sub_phi_nonneg (hx : 0 ≤ x) : 0 ≤ Φm (-1 - x) - Φm (-1) := by
  apply sub_nonneg_of_le
  exact Φm_antitoneOn (by simp; linarith) (by simp) (by linarith)

lemma phi_sub_phi_bound (he : 0 < e) : Φm (-1 - e) - Φm (-1) < e := by
  set f := fun x => x - Φm (-1 - x)
  suffices h : f 0 < f e by simp [f] at h; linarith
  have : ∀ x ∈ Set.Ici (0 : ℝ), -1 - x < 0 := by simp only [Set.mem_Ici]; intro x hx; linarith
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) _ _ (le_refl 0) (le_of_lt he) he
  · unfold f; fun_prop (disch := assumption)
  simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi, f]
  intro x hx
  rw [deriv_sub (by fun_prop) (by fun_prop (disch := linarith))]
  have eq : (fun x => Φm (-1 - x)) = (fun x => Φm ((-1) * x + (-1))) := by
    ext x; congr 1; linarith
  rw [eq, deriv_comp_linear, deriv_Φm (by simp; linarith)]
  have : 1 - (2 : ℝ) ^ (-x + -1) > 0 := by
    simp only [gt_iff_lt, sub_pos]
    apply rpow_lt_one_of_one_lt_of_neg one_lt_two
    linarith
  field_simp
  apply lt_sub_left_of_add_lt
  rw [← mul_two]
  nth_rewrite 2 [(by norm_num : 2 = (2 : ℝ) ^ (1 : ℝ))]
  rw [← rpow_add zero_lt_two]
  apply rpow_lt_one_of_one_lt_of_neg one_lt_two
  linarith

lemma phi_sub_phi_bound' (he : 0 ≤ e) : Φm (-1 - e) - Φm (-1) ≤ e := by
  cases le_iff_eq_or_lt.mp he with
  | inl h => rw [← h, Φm, Φm]; norm_num
  | inr h => exact le_of_lt (phi_sub_phi_bound h)

lemma k_neg (hd : 0 < Δ) (hx : x < 0) : kval Δ x < 0 := by
  have i1 : ind Δ x < x := ind_lt_x hd
  have : Φm (rem Δ x) < Φm (ind Δ x) := by
    apply Φm_strictAntiOn (by linarith : ind Δ x < 0) (rem_lt_zero hd)
    apply lt_of_sub_neg
    rw [ind_sub_rem]; exact hx
  unfold kval; linarith

lemma cotransformation (hd : 0 < Δ) (hx : x < 0) : Φm x = Φm (ind Δ x) + Φm (kval Δ x) := by
  unfold Φm
  have ineq : ∀ {y : ℝ}, y < 0 → (2:ℝ) ^ y < 1 := by
    intro y hy; exact rpow_lt_one_of_one_lt_of_neg one_lt_two hy
  have i0 : (2:ℝ) ^ x < 1 := ineq hx
  have i1 : (2:ℝ) ^ ind Δ x < 1 := ineq (ind_lt_zero hd hx)
  have i2 : (2:ℝ) ^ kval Δ x < 1 := ineq (k_neg hd hx)
  have i3 : (2:ℝ) ^ rem Δ x < 1 := ineq (rem_lt_zero hd)
  unfold logb; field_simp
  apply Real.exp_eq_exp.mp
  rw [exp_log (by linarith), exp_add, exp_log (by linarith), exp_log (by linarith)]
  set a := (2:ℝ) ^ rem Δ x
  set b := (2:ℝ) ^ ind Δ x
  have eq : 2 ^ kval Δ x = 2 ^ x * (1 - a) / (1 - b) := by
    unfold kval Φm; rw [rpow_add, rpow_sub, rpow_logb, rpow_logb]; field_simp
    any_goals linarith
  rw [eq]; field_simp [(by linarith : 1 - b ≠ 0)]; ring_nf
  have eq : (2:ℝ) ^ x * a = b := by rw [← rpow_add zero_lt_two]; unfold rem; simp
  rw [eq]; ring

private def f_aux (x : ℝ) := x - Φm x

private lemma f_aux_strictMono : StrictMonoOn f_aux (Set.Iio 0) := by
  unfold f_aux
  apply strictMonoOn_of_deriv_pos (convex_Iio _) (by fun_prop)
  · simp only [interior_Iio, Set.mem_Iio, differentiableAt_id']
    intro x hx
    rw [deriv_sub differentiableAt_id' (differentiable_Φm.differentiableAt (Iio_mem_nhds hx))]
    rw [deriv_id'', deriv_Φm hx]
    simp only [sub_pos]
    have : 1 - (2 : ℝ) ^ x > 0 := by
      simp only [gt_iff_lt, sub_pos]
      exact rpow_lt_one_of_one_lt_of_neg one_lt_two hx
    rw [div_lt_one this]
    linarith

private lemma k_bound_eq (hd : 0 < d) : Φm (-2 * d) - Φm (-d) = Φp (-d) := by
  unfold Φm Φp
  have neg_d : -d < 0 ∧ -2 * d < 0 := by constructor <;> linarith
  have ineq_d := one_minus_two_pow_ne_zero2 _ neg_d.1
  rw [← logb_div (one_minus_two_pow_ne_zero2 _ neg_d.2) ineq_d]
  have : 1 - (2 : ℝ) ^ (-2 * d) = (1 - (2 : ℝ) ^ (-d)) * (1 + (2 : ℝ) ^ (-d)) := by
    rw [(by linarith : -2 * d = (-d) * 2), rpow_mul]
    ring_nf; simp only [rpow_two]
    norm_num
  rw [this]
  field_simp

private lemma k_bound_ineq (hd : 0 < d) : -d - Φp (-d) ≤ -d / 2 - 1 := by
  apply (by intros; linarith : forall a b : ℝ, 1 ≤ b + a / 2 → -a - b ≤ -a / 2 - 1)
  set f := fun x => Φp (-x) + x / 2
  suffices h : 1 ≤ f d from h
  rw [(by norm_num [f, Φp] : 1 = f 0)]
  suffices h : MonotoneOn f (Set.Ici 0) from h (le_refl (0 : ℝ)) (le_of_lt hd) (le_of_lt hd)
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
  simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi, f]
  intro x hx
  rw [deriv_add (by fun_prop) (by fun_prop), deriv_comp_neg, deriv_Φp]
  simp only [deriv_div_const, deriv_id'', le_neg_add_iff_add_le, add_zero]
  rw [div_le_div_iff (one_plus_two_pow_pos (-x)) (by norm_num)]
  apply (by intros; linarith : forall a : ℝ, a ≤ 1 → a * 2 ≤ 1 * (1 + a))
  exact rpow_le_one_of_one_le_of_nonpos one_le_two (by linarith)

lemma k_bound (hd : 0 < Δ) (hx : x ≤ -Δ) : kval Δ x ≤ -Δ - Φp (-Δ) := by
  unfold kval
  nth_rewrite 1 [← ind_sub_rem Δ x]
  set a := rem _ _
  set b := ind _ _
  have bx : b < x := ind_lt_x hd
  have b0 : b < 0 := by linarith
  have a0 : a < 0 := rem_lt_zero hd
  have eq : forall c d, b - a - c + d = (b - c) - (a - d) := by intros; ring
  rw [eq, ← f_aux, ← f_aux]
  have ineq1 : f_aux b ≤ f_aux (-2 * Δ) := by
    apply f_aux_strictMono.monotoneOn b0 (by linarith : -2 * Δ < 0)
    exact ind_le_two_delta hd hx
  have ineq2 : f_aux (-Δ) ≤ f_aux a := by
    apply f_aux_strictMono.monotoneOn (by linarith : -Δ < 0) a0
    exact rem_ge_neg_delta hd
  apply le_trans (by linarith : f_aux b - f_aux a ≤ f_aux (-2 * Δ) - f_aux (-Δ))
  unfold f_aux
  have eq : forall a b c : ℝ, -2 * a - b - (-a - c) = -a - (b - c) := by intros; ring
  rw [eq, k_bound_eq hd]

lemma k_bound' (hd : 0 < Δ) (hx : x ≤ -Δ) : kval Δ x ≤ -Δ / 2 - 1 :=
  le_trans (k_bound hd hx) (k_bound_ineq hd)

lemma k_bound'' (hd : 0 < Δ) (hx : x ≤ -Δ) : kval Δ x ≤ -1 := by
  apply le_trans (k_bound' hd hx); linarith

lemma krnd_fix_bound (fix : FixedPoint) (Δ x : ℝ) : |kval Δ x - krnd fix Δ x| ≤ 2 * fix.ε := by
  set a1 := fix.rnd (Φm (ind Δ x)) - Φm (ind Δ x)
  set a2 := Φm (rem Δ x) - fix.rnd (Φm (rem Δ x))
  have eq : kval Δ x - krnd fix Δ x = a1 + a2 := by unfold kval krnd; ring_nf
  rw [eq]
  apply le_trans (abs_add _ _)
  have i1 : |a1| ≤ fix.ε := by apply fix.hrnd_sym
  have i2 : |a2| ≤ fix.ε := by apply fix.hrnd
  linarith

lemma krnd_bound (fix : FixedPoint) {Δ x : ℝ} (hd : 0 < Δ) (hx : x ≤ -Δ) :
    krnd fix Δ x ≤ -Δ / 2 - 1 + 2 * fix.ε := by
  have ineq1 := (abs_le.mp (krnd_fix_bound fix Δ x)).1
  have ineq2 := k_bound' hd hx
  linarith

lemma krnd_fix_bound_dir (fix : FixedPointDir) (Δ x : ℝ) : |kval Δ x - krnd fix Δ x| ≤ fix.ε := by
  set a1 := Φm (ind Δ x) - fix.rnd (Φm (ind Δ x))
  set a2 := Φm (rem Δ x) - fix.rnd (Φm (rem Δ x))
  have eq : kval Δ x - krnd fix Δ x = a2 - a1 := by unfold kval krnd; ring_nf
  rw [eq]
  apply fix.abs_rnd_sub_rnd

lemma krnd_bound_dir (fix : FixedPointDir) {Δ x : ℝ} (hd : 0 < Δ) (hx : x ≤ -Δ) :
    krnd fix Δ x ≤ -Δ / 2 - 1 + fix.ε := by
  have ineq1 := (abs_le.mp (krnd_fix_bound_dir fix Δ x)).1
  have ineq2 := k_bound' hd hx
  linarith

/- Case 2 -/

section Cotrans2

lemma bound_case2 (fix : FixedPoint)
    (hc : c < 0) (Φe : FunApprox Φm (Set.Iic c))
    (ha : 0 < Δa) (hx : x < 0) (hk : kval Δa x ≤ c)
    (hkr : krnd fix Δa x ≤ c) (hkr2 : |kval Δa x - krnd fix Δa x| ≤ kε):
    |Φm x - Cotrans₂ fix Φe Δa x| ≤ fix.ε + Φm (c - kε) - Φm c + Φe.err := by
  rw [cotransformation ha hx]
  set s1 := Φm (ind Δa x) - fix.rnd (Φm (ind Δa x) )
  set s2 := Φm (kval Δa x) - Φm (krnd fix Δa x)
  set s3 := Φm (krnd fix Δa x) - Φe (krnd fix Δa x)
  have eq : Φm (ind Δa x) + Φm (kval Δa x) - Cotrans₂ fix Φe Δa x = s1 + s2 + s3 := by
    unfold Cotrans₂; ring_nf
  rw [eq]
  have i01 : |s1 + s2 + s3| ≤ |s1 + s2| + |s3| := by apply abs_add
  have i02 : |s1 + s2| ≤ |s1| + |s2| := by apply abs_add
  have i1 : |s1| ≤ fix.ε := by apply fix.hrnd
  have i3 : |s3| ≤ Φe.err := by apply Φe.herr; apply hkr
  have i2 : |s2| ≤ Φm (c - kε) - Φm c := Lemma71 hc hk hkr hkr2
  linarith

theorem Theorem72_case2 (fix : FixedPoint)
    (Φe : FunApprox Φm (Set.Iic (-1))) /- An approximation of Φm on (-∞, -1] -/
    (ha : 0 < Δa)
    (hΔa : 4 * fix.ε ≤ Δa)             /- Δa should be large enough -/
    (hx : x ≤ -Δa) :                   /- The result is valid for all x ∈ (-∞, -Δa] -/
    |Φm x - Cotrans₂ fix Φe Δa x| ≤ fix.ε + Φm (-1 - 2 * fix.ε) - Φm (-1) + Φe.err := by
  apply bound_case2 fix neg_one_lt_zero Φe ha (by linarith : x < 0)
  · exact k_bound'' ha hx
  · linarith [krnd_bound fix ha hx]
  · exact krnd_fix_bound fix _ _

/- A simplified error bound -/
theorem Theorem72_case2' (fix : FixedPoint)
    (Φe : FunApprox Φm (Set.Iic (-1))) /- An approximation of Φm on (-∞, -1] -/
    (ha : 0 < Δa)
    (hΔa : 4 * fix.ε ≤ Δa)             /- Δa should be large enough -/
    (hx : x ≤ -Δa) :                   /- The result is valid for all x ∈ (-∞, -Δa] -/
    |Φm x - Cotrans₂ fix Φe Δa x| ≤ 3 * fix.ε + Φe.err := by
  apply le_trans (Theorem72_case2 fix Φe ha hΔa hx)
  have ineq := phi_sub_phi_bound' (by linarith [fix.eps_nonneg] : 0 ≤ 2 * fix.ε)
  linarith

theorem Theorem72_case2_dir (fix : FixedPointDir)
    (Φe : FunApprox Φm (Set.Iic (-1))) /- An approximation of Φm on (-∞, -1] -/
    (ha : 0 < Δa)
    (hΔa : 2 * fix.ε ≤ Δa)             /- Δa should be large enough -/
    (hx : x ≤ -Δa) :                   /- The result is valid for all x ∈ (-∞, -Δa] -/
    |Φm x - Cotrans₂ fix Φe Δa x| ≤ fix.ε + Φm (-1 - fix.ε) - Φm (-1) + Φe.err := by
  apply bound_case2 fix neg_one_lt_zero Φe ha (by linarith : x < 0)
  · exact k_bound'' ha hx
  · linarith [krnd_bound_dir fix ha hx]
  · exact krnd_fix_bound_dir fix _ _

/- A simplified error bound (directed rounding) -/
theorem Theorem72_case2_dir' (fix : FixedPointDir)
    (Φe : FunApprox Φm (Set.Iic (-1))) /- An approximation of Φm on (-∞, -1] -/
    (ha : 0 < Δa)
    (hΔa : 2 * fix.ε ≤ Δa)             /- Δa should be large enough -/
    (hx : x ≤ -Δa) :                   /- The result is valid for all x ∈ (-∞, -Δa] -/
    |Φm x - Cotrans₂ fix Φe Δa x| ≤ 2 * fix.ε + Φe.err := by
  apply le_trans (Theorem72_case2_dir fix Φe ha hΔa hx)
  have ineq := phi_sub_phi_bound' fix.eps_nonneg
  linarith

end Cotrans2

/- Case 3 -/

section Contrans3

lemma k2_alt (ha : 0 < Δa) (hb : 0 < Δb) : k₂ Δb x = x + Φm (rb Δa Δb x) + Φm (k₁ Δa Δb x) - Φm (ind Δb x) := by
  have e2 : Φm (rem Δb x) = Φm (rb Δa Δb x) + Φm (k₁ Δa Δb x) := by
    rw [cotransformation ha (rem_lt_zero hb), rb, k₁, kval]
  unfold k₂ kval
  rw [e2]; ring

lemma cotrans3 (hb : 0 < Δb) (hx : x < 0) : Φm x = Φm (ind Δb x) + Φm (k₂ Δb x) :=
  by rw [cotransformation hb hx, k₂]

lemma k2rnd_fix_bound (fix : FixedPoint) (hc : c < 0) (Φe : FunApprox Φm (Set.Iic c))
    (ha : 0 < Δa) (hb : 0 < Δb)
    (hk1 : k₁ Δa Δb x ≤ c) (hk1r : k1rnd fix Δa Δb x ≤ c) :
    |k₂ Δb x - k2rnd fix Φe Δa Δb x| ≤ 2 * fix.ε +  Φm (c - 2 * fix.ε) - Φm c + Φe.err := by
  set a1 := Φm (rb Δa Δb x) - fix.rnd (Φm (rb Δa Δb x))
  set a2 := fix.rnd (Φm (ind Δb x)) - Φm (ind Δb x)
  set a3 := Φm (k₁ Δa Δb x) - Φm (k1rnd fix Δa Δb x)
  set a4 := Φm (k1rnd fix Δa Δb x) - Φe (k1rnd fix Δa Δb x)
  have e : k₂ Δb x - k2rnd fix Φe Δa Δb x = a1 + a2 + a3 + a4 := by
    unfold k2rnd; rw [k2_alt ha hb]; ring
  rw [e]
  have i00 : |a1 + a2 + a3 + a4| ≤ |a1 + a2 + a3| + |a4| := by apply abs_add
  have i01 : |a1 + a2 + a3| ≤ |a1 + a2| + |a3| := by apply abs_add
  have i02 : |a1 + a2| ≤ |a1| + |a2| := by apply abs_add
  have i1 : |a1| ≤ fix.ε := by apply fix.hrnd
  have i2 : |a2| ≤ fix.ε := by apply fix.hrnd_sym
  have i4 : |a4| ≤ Φe.err := by apply Φe.herr; apply hk1r
  have i3 : |a3| ≤  Φm (c - 2 * fix.ε) - Φm c := by
    apply Lemma71 hc hk1 hk1r
    apply krnd_fix_bound
  linarith

lemma k2rnd_fix_bound_dir (fix : FixedPointDir) (hc : c < 0) (Φe : FunApprox Φm (Set.Iic c))
    (ha : 0 < Δa) (hb : 0 < Δb)
    (hk1 : k₁ Δa Δb x ≤ c) (hk1r : k1rnd fix Δa Δb x ≤ c) :
    |k₂ Δb x - k2rnd fix Φe Δa Δb x| ≤ fix.ε +  Φm (c - fix.ε) - Φm c + Φe.err := by
  set a1 := Φm (rb Δa Δb x) - fix.rnd (Φm (rb Δa Δb x))
  set a2 := Φm (ind Δb x) - fix.rnd (Φm (ind Δb x))
  set a3 := Φm (k₁ Δa Δb x) - Φm (k1rnd fix Δa Δb x)
  set a4 := Φm (k1rnd fix Δa Δb x) - Φe (k1rnd fix Δa Δb x)
  have e : k₂ Δb x - k2rnd fix Φe Δa Δb x = (a1 - a2) + a3 + a4 := by
    unfold k2rnd; rw [k2_alt ha hb]; ring
  rw [e]
  have i00 : |(a1 - a2) + a3 + a4| ≤ |(a1 - a2) + a3| + |a4| := by apply abs_add
  have i01 : |(a1 - a2) + a3| ≤ |a1 - a2| + |a3| := by apply abs_add
  have i12 : |a1 - a2| ≤ fix.ε := fix.abs_rnd_sub_rnd _ _
  have i4 : |a4| ≤ Φe.err := by apply Φe.herr; apply hk1r
  have i3 : |a3| ≤  Φm (c - fix.ε) - Φm c := by
    apply Lemma71 hc hk1 hk1r
    apply krnd_fix_bound_dir
  linarith

lemma bound_case3 (fix : FixedPoint) (hc : c < 0) (Φe : FunApprox Φm (Set.Iic c))
    (hb : 0 < Δb) (hx : x < 0)
    (hk2 : k₂ Δb x ≤ c) (hk2r : k2rnd fix Φe Δa Δb x ≤ c)
    (hk2rnd : |k₂ Δb x - k2rnd fix Φe Δa Δb x| ≤ Ek2) :
    |Φm x - Cotrans₃ fix Φe Δa Δb x| ≤ fix.ε + Φm (c - Ek2) - Φm c + Φe.err := by
  rw [cotrans3 hb hx]
  set s1 := Φm (ind Δb x) - fix.rnd (Φm (ind Δb x))
  set s2 := Φm (k₂ Δb x) - Φm (k2rnd fix Φe Δa Δb x)
  set s3 := Φm (k2rnd fix Φe Δa Δb x) - Φe (k2rnd fix Φe Δa Δb x)
  have e : Φm (ind Δb x) +  Φm (k₂ Δb x) - Cotrans₃ fix Φe Δa Δb x = s1 + s2 + s3 := by
    unfold Cotrans₃; ring_nf
  rw [e]
  have i01 : |s1 + s2 + s3| ≤ |s1 + s2| + |s3| := by apply abs_add
  have i02 : |s1 + s2| ≤ |s1| + |s2| := by apply abs_add
  have i1 : |s1| ≤ fix.ε := by apply fix.hrnd
  have i3 : |s3| ≤ Φe.err := by apply Φe.herr; apply hk2r
  have i2 : |s2| ≤ Φm (c - Ek2) - Φm c := by apply Lemma71 hc hk2 hk2r hk2rnd
  linarith

/- Note: If rem Δb x ∈ (-Δa, 0) then use Contrans₂ fix Δb x
   since Φm (rem Δb x) can be computed directly from
   a table defined for all values in (-Δa, 0) -/

theorem Theorem72_case3 (fix : FixedPoint)
    (Φe : FunApprox Φm (Set.Iic (-1)))  /- An approximation of Φm on (-∞, -1] -/
    (ha : 0 < Δa) (hb : 0 < Δb) (hrem : rem Δb x ≤ -Δa)
    (hΔa : 4 * fix.ε ≤ Δa)              /- Δa should be large enough -/
    (hΔb : 8 * fix.ε + 2 * Φe.err ≤ Δb) /- Δb should be large enough -/
    (hx : x ≤ -Δb) :                    /- The result is valid for all x ∈ (-∞, -Δb] -/
    let Ek2 := 2 * fix.ε + Φm (-1 - 2 * fix.ε) - Φm (-1) + Φe.err
    |Φm x - Cotrans₃ fix Φe Δa Δb x| ≤ fix.ε + Φm (-1 - Ek2) - Φm (-1) + Φe.err := by
  have hk1 : k₁ Δa Δb x ≤ -1 := by apply k_bound'' ha hrem
  have hk1r : k1rnd fix Δa Δb x ≤ -1 := by unfold k1rnd; linarith [krnd_bound fix ha hrem]
  have hk2 : k₂ Δb x ≤ -1 := by unfold k₂; exact k_bound'' hb hx
  have hk2rnd := k2rnd_fix_bound fix neg_one_lt_zero Φe ha hb hk1 hk1r
  apply bound_case3 fix neg_one_lt_zero Φe hb (by linarith) hk2 _ hk2rnd
  have ineq1 := (abs_le.mp $ k2rnd_fix_bound fix neg_one_lt_zero Φe ha hb hk1 hk1r).1
  have ineq2 := k_bound' hb hx
  have ineq3 := phi_sub_phi_bound' (by linarith [fix.eps_nonneg] : 0 ≤ 2 * fix.ε)
  unfold k₂ at ineq1
  linarith

theorem Theorem72_case3_dir (fix : FixedPointDir)
    (Φe : FunApprox Φm (Set.Iic (-1)))  /- An approximation of Φm on (-∞, -1] -/
    (ha : 0 < Δa) (hb : 0 < Δb) (hrem : rem Δb x ≤ -Δa)
    (hΔa : 2 * fix.ε ≤ Δa)              /- Δa should be large enough -/
    (hΔb : 4 * fix.ε + 2 * Φe.err ≤ Δb) /- Δb should be large enough -/
    (hx : x ≤ -Δb) :                    /- The result is valid for all x ∈ (-∞, -Δb] -/
    let Ek2 := fix.ε + Φm (-1 - fix.ε) - Φm (-1) + Φe.err
    |Φm x - Cotrans₃ fix Φe Δa Δb x| ≤ fix.ε + Φm (-1 - Ek2) - Φm (-1) + Φe.err := by
  have hk1 : k₁ Δa Δb x ≤ -1 := by apply k_bound'' ha hrem
  have hk1r : k1rnd fix Δa Δb x ≤ -1 := by unfold k1rnd; linarith [krnd_bound_dir fix ha hrem]
  have hk2 : k₂ Δb x ≤ -1 := by unfold k₂; exact k_bound'' hb hx
  have hk2rnd := k2rnd_fix_bound_dir fix neg_one_lt_zero Φe ha hb hk1 hk1r
  apply bound_case3 fix neg_one_lt_zero Φe hb (by linarith) hk2 _ hk2rnd
  have ineq1 := (abs_le.mp $ k2rnd_fix_bound_dir fix neg_one_lt_zero Φe ha hb hk1 hk1r).1
  have ineq2 := k_bound' hb hx
  have ineq3 := phi_sub_phi_bound' fix.eps_nonneg
  unfold k₂ at ineq1
  linarith

/- A simplified error bound -/
theorem Theorem72_case3' (fix : FixedPoint)
    (Φe : FunApprox Φm (Set.Iic (-1)))  /- An approximation of Φm on (-∞, -1] -/
    (ha : 0 < Δa) (hb : 0 < Δb) (hrem : rem Δb x ≤ -Δa)
    (hΔa : 4 * fix.ε ≤ Δa)              /- Δa should be large enough -/
    (hΔb : 8 * fix.ε + 2 * Φe.err ≤ Δb) /- Δb should be large enough -/
    (hx : x ≤ -Δb) :                    /- The result is valid for all x ∈ (-∞, -Δb] -/
    |Φm x - Cotrans₃ fix Φe Δa Δb x| ≤ 5 * fix.ε + 2 * Φe.err := by
  have hk1 : k₁ Δa Δb x ≤ -1 := by apply k_bound'' ha hrem
  have hk1r : k1rnd fix Δa Δb x ≤ -1 := by unfold k1rnd; linarith [krnd_bound fix ha hrem]
  apply le_trans (Theorem72_case3 fix Φe ha hb hrem hΔa hΔb hx)
  have ineq1 : 0 ≤ 2 * fix.ε + Φm (-1 - 2 * fix.ε) - Φm (-1) + Φe.err := by
    apply (le_trans (abs_nonneg $ k₂ Δb x - k2rnd fix Φe Δa Δb x))
    exact k2rnd_fix_bound fix neg_one_lt_zero Φe ha hb hk1 hk1r
  have ineq2 := phi_sub_phi_bound' ineq1
  have ineq3 := phi_sub_phi_bound' (by linarith [fix.eps_nonneg] : 0 ≤ 2 * fix.ε)
  linarith

theorem Theorem72_case3_dir' (fix : FixedPointDir)
    (Φe : FunApprox Φm (Set.Iic (-1)))  /- An approximation of Φm on (-∞, -1] -/
    (ha : 0 < Δa) (hb : 0 < Δb) (hrem : rem Δb x ≤ -Δa)
    (hΔa : 2 * fix.ε ≤ Δa)              /- Δa should be large enough -/
    (hΔb : 4 * fix.ε + 2 * Φe.err ≤ Δb) /- Δb should be large enough -/
    (hx : x ≤ -Δb) :                    /- The result is valid for all x ∈ (-∞, -Δb] -/
    |Φm x - Cotrans₃ fix Φe Δa Δb x| ≤ 3 * fix.ε + 2 * Φe.err := by
  have hk1 : k₁ Δa Δb x ≤ -1 := by apply k_bound'' ha hrem
  have hk1r : k1rnd fix Δa Δb x ≤ -1 := by unfold k1rnd; linarith [krnd_bound_dir fix ha hrem]
  apply le_trans (Theorem72_case3_dir fix Φe ha hb hrem hΔa hΔb hx)
  have ineq1 : 0 ≤ fix.ε + Φm (-1 - fix.ε) - Φm (-1) + Φe.err := by
    apply (le_trans (abs_nonneg $ k₂ Δb x - k2rnd fix Φe Δa Δb x))
    exact k2rnd_fix_bound_dir fix neg_one_lt_zero Φe ha hb hk1 hk1r
  have ineq2 := phi_sub_phi_bound' ineq1
  have ineq3 := phi_sub_phi_bound' fix.eps_nonneg
  linarith

end Contrans3

/- A general result -/

section Cotrans

private lemma contrans2_bound_le_cotrans3_bound (he : 0 ≤ e) (herr : 0 ≤ err) :
    let Ek2 := e + Φm (-1 - e) - Φm (-1) + err
    eps + Φm (-1 - e) - Φm (-1) + err ≤ eps + Φm (-1 - Ek2) - Φm (-1) + err := by
  apply add_le_add_right
  apply add_le_add_right
  apply add_le_add_left
  apply Φm_antitoneOn
  · simp; linarith [phi_sub_phi_nonneg he]
  · simp; linarith
  · linarith [phi_sub_phi_nonneg he]

theorem Theorem72 (fix : FixedPoint)
    (Φe : FunApprox Φm (Set.Iic (-1)))
    (ha : 0 < Δa) (hb : 0 < Δb)
    (hΔa : 4 * fix.ε ≤ Δa)                /- Δa should be large enough -/
    (hΔb : 8 * fix.ε + 2 * Φe.err ≤ Δb) : /- Δb should be large enough -/
    let Ek2 := 2 * fix.ε + Φm (-1 - 2 * fix.ε) - Φm (-1) + Φe.err
    |Φm x - Cotrans fix Φe Δa Δb x| ≤ fix.ε + Φm (-1 - Ek2) - Φm (-1) + Φe.err := by
  intro Ek2
  have hε := fix.eps_nonneg
  have herr : 0 ≤ Φe.err := by
    apply le_trans (abs_nonneg _) (Φe.herr (-1) _)
    simp only [Set.mem_Iic, le_refl]
  have ek2_nonneg : 0 ≤ Ek2 := by
    have := phi_sub_phi_nonneg (by linarith : 0 ≤ 2 * fix.ε)
    unfold Ek2; rw [add_sub_assoc]
    positivity
  unfold Cotrans
  split_ifs with hax hbx hrem
  · linarith [fix.hrnd (Φm x), phi_sub_phi_nonneg ek2_nonneg]
  · apply le_trans (Theorem72_case2 fix Φe ha hΔa (by linarith : x ≤ -Δa))
    exact contrans2_bound_le_cotrans3_bound (by positivity) herr
  · have ineq : 4 * fix.ε ≤ Δb := by linarith
    apply le_trans (Theorem72_case2 fix Φe hb ineq (by linarith : x ≤ -Δb))
    exact contrans2_bound_le_cotrans3_bound (by positivity) herr
  · exact Theorem72_case3 fix Φe ha hb (by linarith) hΔa hΔb (by linarith)

theorem Theorem72_dir (fix : FixedPointDir)
    (Φe : FunApprox Φm (Set.Iic (-1)))
    (ha : 0 < Δa) (hb : 0 < Δb)
    (hΔa : 2 * fix.ε ≤ Δa)                /- Δa should be large enough -/
    (hΔb : 4 * fix.ε + 2 * Φe.err ≤ Δb) : /- Δb should be large enough -/
    let Ek2 := fix.ε + Φm (-1 - fix.ε) - Φm (-1) + Φe.err
    |Φm x - Cotrans fix Φe Δa Δb x| ≤ fix.ε + Φm (-1 - Ek2) - Φm (-1) + Φe.err := by
  intro Ek2
  have hε := fix.eps_nonneg
  have herr : 0 ≤ Φe.err := by
    apply le_trans (abs_nonneg _) (Φe.herr (-1) _)
    simp only [Set.mem_Iic, le_refl]
  have ek2_nonneg : 0 ≤ Ek2 := by
    have := phi_sub_phi_nonneg hε
    unfold Ek2; rw [add_sub_assoc]
    positivity
  unfold Cotrans
  split_ifs with hax hbx hrem
  · linarith [fix.hrnd (Φm x), phi_sub_phi_nonneg ek2_nonneg]
  · apply le_trans (Theorem72_case2_dir fix Φe ha hΔa (by linarith : x ≤ -Δa))
    exact contrans2_bound_le_cotrans3_bound (by positivity) herr
  · have ineq : 2 * fix.ε ≤ Δb := by linarith
    apply le_trans (Theorem72_case2_dir fix Φe hb ineq (by linarith : x ≤ -Δb))
    exact contrans2_bound_le_cotrans3_bound (by positivity) herr
  · exact Theorem72_case3_dir fix Φe ha hb (by linarith) hΔa hΔb (by linarith)

/- Simplified bounds -/

theorem Theorem72' (fix : FixedPoint)
    (Φe : FunApprox Φm (Set.Iic (-1)))
    (ha : 0 < Δa) (hb : 0 < Δb)
    (hΔa : 4 * fix.ε ≤ Δa)                /- Δa should be large enough -/
    (hΔb : 8 * fix.ε + 2 * Φe.err ≤ Δb) : /- Δb should be large enough -/
    |Φm x - Cotrans fix Φe Δa Δb x| ≤ 5 * fix.ε + 2 * Φe.err := by
  have hε := fix.eps_nonneg
  have herr : 0 ≤ Φe.err := by
    apply le_trans (abs_nonneg _) (Φe.herr (-1) _)
    simp only [Set.mem_Iic, le_refl]
  unfold Cotrans
  split_ifs with hax hbx hrem
  · linarith [fix.hrnd (Φm x)]
  · linarith [Theorem72_case2' fix Φe ha hΔa (by linarith : x ≤ -Δa)]
  · have ineq : 4 * fix.ε ≤ Δb := by linarith
    have := Theorem72_case2' fix Φe hb ineq (by linarith : x ≤ -Δb)
    linarith
  · apply Theorem72_case3' fix Φe ha hb (by linarith) hΔa hΔb (by linarith)

theorem Theorem72_dir' (fix : FixedPointDir)
    (Φe : FunApprox Φm (Set.Iic (-1)))
    (ha : 0 < Δa) (hb : 0 < Δb)
    (hΔa : 2 * fix.ε ≤ Δa)                /- Δa should be large enough -/
    (hΔb : 4 * fix.ε + 2 * Φe.err ≤ Δb) : /- Δb should be large enough -/
    |Φm x - Cotrans fix Φe Δa Δb x| ≤ 3 * fix.ε + 2 * Φe.err := by
  have hε := fix.eps_nonneg
  have herr : 0 ≤ Φe.err := by
    apply le_trans (abs_nonneg _) (Φe.herr (-1) _)
    simp only [Set.mem_Iic, le_refl]
  unfold Cotrans
  split_ifs with hax hbx hrem
  · linarith [fix.hrnd (Φm x)]
  · linarith [Theorem72_case2_dir' fix Φe ha hΔa (by linarith : x ≤ -Δa)]
  · have ineq : 2 * fix.ε ≤ Δb := by linarith
    have := Theorem72_case2_dir' fix Φe hb ineq (by linarith : x ≤ -Δb)
    linarith
  · apply Theorem72_case3_dir' fix Φe ha hb (by linarith) hΔa hΔb (by linarith)

end Cotrans
