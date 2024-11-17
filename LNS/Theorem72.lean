import LNS.Definitions
import LNS.BasicIxRx
import LNS.Lemma71

namespace LNS

noncomputable section

open Real

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

def ind (Δ : ℝ) (x : ℝ) := (⌈x / Δ⌉ - 1) * Δ

def rem (Δ : ℝ) (x : ℝ) := ind Δ x - x

lemma ind_sub_rem (Δ x : ℝ) : ind Δ x - rem Δ x = x := by unfold rem; linarith

lemma ind_alt : ind Δ x = Iₓ Δ x - Δ := by unfold ind Iₓ; linarith

lemma rem_alt : rem Δ x = Rₓ Δ x - Δ := by unfold rem Rₓ; rw [ind_alt, sub_right_comm]

lemma rem_lt_zero (hd : 0 < Δ) : rem Δ x < 0 := by
  rw [rem_alt]; linarith [rx_lt_delta hd x]

lemma rem_ge_neg_delta (hd : 0 < Δ) : -Δ ≤ rem Δ x := by
  rw [rem_alt]; linarith [rx_nonneg hd x]

lemma ind_lt_x (hd : 0 < Δ) : ind Δ x < x := by
  rw [ind_alt]
  nth_rewrite 2 [←i_sub_r_eq_x Δ x]
  rw [sub_lt_sub_iff_left]
  exact rx_lt_delta hd x

lemma ind_lt_zero (hd : 0 < Δ) (hx : x < 0) : ind Δ x < 0 := lt_trans (ind_lt_x hd) hx

lemma ind_le_two_delta (hd : 0 < Δ) (hx : x ≤ -Δ) : ind Δ x ≤ -2 * Δ := by
  rw [ind_alt, sub_le_iff_le_add]; ring_nf
  have : -Δ = ((-1) : ℤ) * Δ := by
    simp only [Int.reduceNeg, Int.cast_neg, Int.cast_one, neg_mul, one_mul]
  rw [this, ←ix_eq_n_delta, ←this]
  exact ix_monotone hd hx

lemma k_bound (hd : 0 < Δ) (hx : x ≤ -Δ) :
    x - Φm (ind Δ x) + Φm (rem Δ x) ≤ -Δ - Φp (-Δ) := by
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

lemma k_bound' (hd : 0 < Δ) (hx : x ≤ -Δ) :
    x - Φm (ind Δ x) + Φm (rem Δ x) ≤ -Δ / 2 - 1 :=
  le_trans (k_bound hd hx) (k_bound_ineq hd)

/- Case 2 -/

section Cotrans2

variable (fix : FixedPoint)
variable (Δa : ℝ)

def k (x : ℝ) := x - Φm (ind Δa x) + Φm (rem Δa x)

def krnd (x : ℝ) := x - fix.rnd (Φm (ind Δa x)) + fix.rnd (Φm (rem Δa x))

def Prnd2 (Φe : FunApprox Φm s) (x : ℝ) := fix.rnd (Φm (ind Δa x)) + Φe (krnd fix Δa x)

lemma krnd_bound (Δa x : ℝ) : |k Δa x - krnd fix Δa x| ≤ 2 * fix.ε := by
  set a1 := fix.rnd (Φm (ind Δa x)) - Φm (ind Δa x)
  set a2 := Φm (rem Δa x) - fix.rnd (Φm (rem Δa x))
  have eq : k Δa x - krnd fix Δa x = a1 + a2 := by unfold k krnd; ring_nf
  rw [eq]
  apply le_trans (abs_add _ _)
  have i1 : |a1| ≤ fix.ε := by apply fix.hrnd_sym
  have i2 : |a2| ≤ fix.ε := by apply fix.hrnd
  linarith

variable {Δa}
variable (ha : 0 < Δa)
include ha

lemma k_neg (hx : x < 0) : k Δa x < 0 := by
  have i1 : ind Δa x < x := ind_lt_x ha
  have : Φm (rem Δa x) < Φm (ind Δa x) := by
    apply Φm_strictAntiOn (by linarith : ind Δa x < 0) (rem_lt_zero ha)
    apply lt_of_sub_neg
    rw [ind_sub_rem]; exact hx
  unfold k; linarith

lemma cotrans2 (hx : x < 0) : Φm x = Φm (ind Δa x) + Φm (k Δa x) := by
  unfold Φm
  have ineq : ∀ {y : ℝ}, y < 0 → (2:ℝ) ^ y < 1 := by
    intro y hy; exact rpow_lt_one_of_one_lt_of_neg one_lt_two hy
  have i0 : (2:ℝ) ^ x < 1 := ineq hx
  have i1 : (2:ℝ) ^ ind Δa x < 1 := ineq (ind_lt_zero ha hx)
  have i2 : (2:ℝ) ^ k Δa x < 1 := ineq (k_neg ha hx)
  have i3 : (2:ℝ) ^ rem Δa x < 1 := ineq (rem_lt_zero ha)
  unfold logb; field_simp
  apply Real.exp_eq_exp.mp
  rw [exp_log (by linarith), exp_add, exp_log (by linarith), exp_log (by linarith)]
  set a := (2:ℝ) ^ rem Δa x
  set b := (2:ℝ) ^ ind Δa x
  have eq : 2 ^ k Δa x = 2 ^ x * (1 - a) / (1 - b) := by
    unfold k Φm; rw [rpow_add, rpow_sub, rpow_logb, rpow_logb]; field_simp
    any_goals linarith
  rw [eq]; field_simp [(by linarith : 1 - b ≠ 0)]; ring_nf
  have eq : (2:ℝ) ^ x * a = b := by rw [← rpow_add zero_lt_two]; unfold rem; simp
  rw [eq]; ring

lemma bound_case2 (Φe : FunApprox Φm (Set.Iic (-1))) (hx : x < 0) (hk : k Δa x ≤ -1) (hkr : krnd fix Δa x ≤ -1) :
    |Φm x - Prnd2 fix Δa Φe x| ≤ fix.ε + Φm (-1 - 2 * fix.ε) - Φm (-1) + Φe.err := by
  rw [cotrans2 ha hx]
  set s1 := Φm (ind Δa x) - fix.rnd (Φm (ind Δa x) )
  set s2 := Φm (k Δa x) - Φm (krnd fix Δa x)
  set s3 := Φm (krnd fix Δa x) - Φe (krnd fix Δa x)
  have eq : Φm (ind Δa x) + Φm (k Δa x) - Prnd2 fix Δa Φe x = s1 + s2 + s3 := by
    unfold Prnd2; ring_nf
  rw [eq]
  have i01 : |s1 + s2 + s3| ≤ |s1 + s2| + |s3| := by apply abs_add
  have i02 : |s1 + s2| ≤ |s1| + |s2| := by apply abs_add
  have i1 : |s1| ≤ fix.ε := by apply fix.hrnd
  have i3 : |s3| ≤ Φe.err := by apply Φe.herr; apply hkr
  have i2 : |s2| ≤ Φm (-1-2*fix.ε) - Φm (-1) := by
    apply Lemma71 (by norm_num : -1 < (0 : ℝ)) hk hkr
    exact krnd_bound fix _ _
  linarith

theorem Theorem72_case2
      (Φe : FunApprox Φm (Set.Iic (-1))) /- An approximation of Φm on (-oo, -1] -/
      (hΔa : Δa ≥ 4 * fix.ε)             /- Δa should be large enough -/
      (hx : x ≤ -Δa) :                   /- The result is valid for all x ∈ (-oo, -Δa] -/
    |Φm x - Prnd2 fix Δa Φe x| ≤ fix.ε + Φm (-1 - 2 * fix.ε) - Φm (-1) + Φe.err := by
  apply bound_case2 fix ha Φe (by linarith : x < 0)
  · unfold k; linarith [k_bound' ha hx]
  · have ineq1 := (abs_le.mp (krnd_bound fix Δa x)).1
    have ineq2 := k_bound' ha hx
    unfold krnd k at *; linarith

end Cotrans2

/- Case 3 -/

section Contrans3

variable (fix : FixedPoint)
variable (Φe : FunApprox Φm (Set.Iic (-1)))
variable (Δa Δb : ℝ)

def rc x := ind Δb x

def rab x := rem Δb x

def rb x := ind Δa (rab Δb x)

def ra x := rem Δa (rab Δb x)

def k1 x := rab Δb x  - Φm (rb Δa Δb x)  + Φm (ra Δa Δb x)

def k2 x := x + Φm (rb Δa Δb x) + Φm (k1 Δa Δb x) - Φm (rc Δb x)

def Pest3 x := Φm (rc Δb x) +  Φm (k2 Δa Δb x)

def k1rnd x := rab Δb x - fix.rnd (Φm (rb Δa Δb x))  + fix.rnd (Φm (ra Δa Δb x))

def k2rnd x := x + fix.rnd (Φm (rb Δa Δb x)) + Φe (k1rnd fix Δa Δb x) - fix.rnd (Φm (rc Δb x))

def Prnd3 x := fix.rnd (Φm (rc Δb x)) +  Φe (k2rnd fix Φe Δa Δb x)

lemma cotrans3 (ha : 0 < Δa) (hb : 0 < Δb) (hx : x < 0) :
    Φm x = Pest3 Δa Δb x := by
  have e1 : Φm x = Φm (ind Δb x) + Φm (k Δb x) := cotrans2 hb hx
  rw [e1]; unfold Pest3 rc
  have e2 : Φm (rem Δb x) = Φm (rb Δa Δb x) + Φm (k1 Δa Δb x) := by
    rw [cotrans2 ha (rem_lt_zero hb), rb, k1, k, rb, ra, rab]
  have e : k Δb x = k2 Δa Δb x := by
    unfold k k2
    rw [e2, rc]; ring
  rw [e]

lemma bound_case3 (ha : 0 < Δa) (hb : 0 < Δb) (hx : x < 0)
    (hk1 : k1 Δa Δb x ≤ -1) (hk1r : k1rnd fix Δa Δb x ≤ -1)
    (hk2 : k2 Δa Δb x ≤ -1) (hk2r : k2rnd fix Φe Δa Δb x ≤ -1) :
    let Ek2 := 2 * fix.ε +  Φm (-1 - 2 * fix.ε) - Φm (-1) + Φe.err
    |Φm x - Prnd3 fix Φe Δa Δb x| ≤ fix.ε + Φm (-1 - Ek2) - Φm (-1) + Φe.err := by
  intro Ek2
  rw [cotrans3 _ _ ha hb hx]
  set s1 := Φm (rc Δb x) - fix.rnd (Φm (rc Δb x))
  set s2 := Φm (k2 Δa Δb x) - Φm (k2rnd fix Φe Δa Δb x)
  set s3 := Φm (k2rnd fix Φe Δa Δb x) - Φe (k2rnd fix Φe Δa Δb x)
  have e : Pest3 Δa Δb x - Prnd3 fix Φe Δa Δb x = s1 + s2 + s3 := by unfold Pest3 Prnd3; ring_nf
  rw [e]
  have i01 : |s1 + s2 + s3| ≤ |s1 + s2| + |s3| := by apply abs_add
  have i02 : |s1 + s2| ≤ |s1| + |s2| := by apply abs_add
  have i1 : |s1| ≤ fix.ε := by apply fix.hrnd
  have i3 : |s3| ≤ Φe.err := by apply Φe.herr; apply hk2r
  have i2 : |s2| ≤ Φm (-1 - Ek2) - Φm (-1) := by
    apply Lemma71 (by norm_num) hk2 hk2r
    set a1 := Φm (rb Δa Δb x) - fix.rnd (Φm (rb Δa Δb x))
    set a2 := fix.rnd (Φm (rc Δb x)) - Φm (rc Δb x)
    set a3 := Φm (k1 Δa Δb x) - Φm (k1rnd fix Δa Δb x)
    set a4 := Φm (k1rnd fix Δa Δb x) - Φe (k1rnd fix Δa Δb x)
    have e : k2 Δa Δb x - k2rnd fix Φe Δa Δb x = a1 + a2 + a3 + a4 := by unfold k2 k2rnd; ring_nf
    rw [e]
    have i00 : |a1 + a2 + a3 + a4| ≤ |a1 + a2 + a3| + |a4| := by apply abs_add
    have i01 : |a1 + a2 + a3| ≤ |a1 + a2| + |a3| := by apply abs_add
    have i02 : |a1 + a2| ≤ |a1| + |a2| := by apply abs_add
    have i1 : |a1| ≤ fix.ε := by apply fix.hrnd
    have i2 : |a2| ≤ fix.ε := by apply fix.hrnd_sym
    have i4 : |a4| ≤ Φe.err := by apply Φe.herr; apply hk1r
    have i3 : |a3| ≤  Φm (-1-2*fix.ε) - Φm (-1) := by
      apply Lemma71 (by norm_num) hk1 hk1r
      set b1 := fix.rnd (Φm (rb Δa Δb x)) - Φm (rb Δa Δb x)
      set b2 := Φm (ra Δa Δb x) - fix.rnd (Φm (ra Δa Δb x))
      have e : k1 Δa Δb x - k1rnd fix Δa Δb x = b1 + b2 := by unfold k1 k1rnd; ring_nf
      rw [e]
      have i0 : |b1 + b2| ≤ |b1| + |b2| := by apply abs_add
      have i1 : |b1| ≤ fix.ε := by apply fix.hrnd_sym
      have i2 : |b2| ≤ fix.ε := by apply fix.hrnd
      linarith
    unfold Ek2; linarith
  linarith

end Contrans3
