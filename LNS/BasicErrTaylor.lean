import LNS.Common
import LNS.Tactic
import LNS.Definitions
import LNS.BasicPhi

namespace LNS

noncomputable section

open Real

private lemma one_minus_two_pow_ne_zero3 (hi : i < (0:ℝ)) (hr : r > 0) :
    1 - (2:ℝ) ^ (i - r) ≠ 0 := by
  apply one_minus_two_pow_ne_zero2; linarith

private lemma one_minus_two_pow_ne_zero4 (hi : i < (0:ℝ)) (hr : r ≥ 0) :
    1 - (2:ℝ) ^ (i - r) ≠ 0 := by
  apply one_minus_two_pow_ne_zero2; linarith

private lemma aux_inq1 (hi : i ∈ (Set.Iio (0:ℝ))) :
    ∀ x ∈ Set.Ioi 0, ¬1 - (2:ℝ) ^ (i - x) = 0 ∧ ¬1 - (2:ℝ) ^ i = 0 := by
  simp_all only [Set.mem_Iio, Set.mem_Ioi, one_minus_two_pow_ne_zero2, not_false_eq_true, and_true]
  intro x hx
  exact one_minus_two_pow_ne_zero3 hi hx

private lemma aux_inq1' (hi : i ∈  (Set.Iio (0:ℝ))) :
    ∀ x ∈ Set.Ici 0, ¬1 - (2:ℝ) ^ (i - x) = 0 ∧ ¬1 - (2:ℝ) ^ i = 0 := by
  simp_all only [Set.mem_Iio, Set.mem_Ici, one_minus_two_pow_ne_zero2, not_false_eq_true, and_true]
  intro x hx
  have : (2:ℝ) ^ (i - x) < 1 := by apply rpow_lt_one_of_one_lt_of_neg; simp only [Nat.one_lt_ofNat]; linarith
  linarith

private lemma aux_inq2 (hi : i ∈  (Set.Iio (0:ℝ))) :
    ∀ x ∈ Set.Ici 0, ¬1 - (2:ℝ) ^ (i - x) = 0 := by
  simp_all only [Set.mem_Iio, Set.mem_Ioi, one_minus_two_pow_ne_zero2, not_false_eq_true, and_true]
  intro x hx; simp only [Set.mem_Ici] at hx
  apply one_minus_two_pow_ne_zero2; linarith

private lemma aux_eq1 : rexp (-(log 2 * r)) = 1/ 2 ^ r := by
  rw [exp_neg, exp_mul, exp_log]; field_simp; simp only [Nat.ofNat_pos]

private lemma aux_eq2 : (2:ℝ) ^ ((x:ℝ) - r) = 2^x / 2^r := by
  simp only [Nat.ofNat_pos, rpow_sub]

/-
  Basic properties of Ep and Em
-/

lemma Ep_eq_zero (i : ℝ) : Ep i 0 = 0 := by simp only [Ep, sub_zero, sub_self, zero_mul, add_zero]

lemma Em_eq_zero (i : ℝ) : Em i 0 = 0 := by simp only [Em, sub_zero, neg_add_cancel, zero_mul, sub_self]

/-
  Continuity and differentiability of Ep(i, r) and Em(i, r) with respect to r
-/

lemma deriv_Ep_r : deriv (Ep i) = fun (r : ℝ) => ((2:ℝ)^i - (2:ℝ)^(i-r)) / ((1+(2:ℝ)^i) * (1+(2:ℝ)^(i-r))) := by
  unfold Ep; rw [deriv_Φp]; simp only [Φp, logb]
  deriv_EQ fun r ↦ log (1 + 2 ^ (i - r)) / log 2 - log (1 + 2 ^ i) / log 2 + r * (2 ^ i / (1 + 2 ^ i))

lemma deriv_Em_r (hi : i < 0) :
    Set.EqOn (deriv (Em i)) (fun (r : ℝ) => ((2:ℝ)^i - (2:ℝ)^(i-r)) / ((1-(2:ℝ)^i) * (1-(2:ℝ)^(i-r)) )) (Set.Ioi 0) := by
  unfold Em Set.EqOn
  intro r hr
  rw [deriv_Φm hi]; simp only [Φm, logb]
  get_deriv (fun r ↦ -(log (1 - 2 ^ (i - r)) / log 2) + log (1 - 2 ^ i) / log 2 - r * (-2 ^ i / (1 - 2 ^ i))) within (Set.Ioi 0)
  simp only [Set.mem_Ici, List.Forall, toFun, ne_eq, log_eq_zero, OfNat.ofNat_ne_zero,
    OfNat.ofNat_ne_one, or_self, not_false_eq_true, id_eq, gt_iff_lt, Nat.ofNat_pos,
    and_self, and_true, true_and, (by norm_num : (2 : ℝ) ≠ -1)]
  exact aux_inq1 hi
  simp only [toFun, zero_mul, zero_sub, neg_mul, one_mul, zero_add, sub_neg_eq_add,
    zero_div, mul_zero, sub_zero, Nat.cast_ofNat, rpow_two, add_zero, sub_self, neg_zero] at h
  rw [h.right r hr]
  simp only [Set.mem_Iio, Set.mem_Ioi] at hi hr
  have ie := one_minus_two_pow_ne_zero3 hi hr
  field_simp; simp only [aux_eq2]; field_simp; ring_nf

@[fun_prop]
lemma differentiable_Ep_r : Differentiable ℝ (Ep i) := by
  unfold Ep; rw [deriv_Φp]
  fun_prop (disch := simp)

@[fun_prop]
lemma continuous_Ep_r : Continuous (Ep i) := differentiable_Ep_r.continuous

@[fun_prop]
lemma differentiableAt_Em_r (hi : i < 0) (hr : 0 < r) : DifferentiableAt ℝ (Em i) r := by
  unfold Em; rw [deriv_Φm hi]; fun_prop (disch := linarith)

@[fun_prop]
lemma differentiableOn_Em_r (hi : i < 0) : DifferentiableOn ℝ (Em i) (Set.Ioi 0) := by
  intro r hr
  exact (differentiableAt_Em_r hi hr).differentiableWithinAt

@[fun_prop]
lemma continuousOn_Em_r (hi : i < 0) : ContinuousOn (Em i) (Set.Ici 0) := by
  unfold Em; rw [deriv_Φm hi]; simp only [Φm, logb]
  have e := aux_inq2 hi
  have u : ∀ x ∈ Set.Ici 0, (2:ℝ) ≠ 0 ∨ 0 < i - x := by simp only [Set.mem_Ici, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, sub_pos, true_or, implies_true]
  fun_prop (disch := assumption)

/-
  Monotonicity properties of Ep(i, r) and Em(i, r) and their derivatives
  with respect to r
-/

lemma deriv_Ep_r_pos (hr : 0 < r) : 0 < deriv (Ep i) r := by
  simp only [deriv_Ep_r, ge_iff_le]
  have i3 : (2:ℝ) ^ i > 2 ^ (i - r) := by
    apply rpow_lt_rpow_of_exponent_lt; simp only [Nat.one_lt_ofNat]; linarith
  have i3 : (2:ℝ) ^ i - 2 ^ (i - r) > 0 := by linarith
  positivity

lemma deriv_Em_r_pos (hi : i < 0) (hr : 0 < r) : 0 < deriv (Em i) r := by
  simp only [deriv_Em_r hi hr, gt_iff_lt]
  have i1 : (2:ℝ) ^ i < 1 := by
    apply rpow_lt_one_of_one_lt_of_neg _ hi; simp only [Nat.one_lt_ofNat]
  have _ : (2:ℝ) ^ (i-r) < 1 := by
    apply rpow_lt_one_of_one_lt_of_neg; simp only [Nat.one_lt_ofNat]; linarith
  have i3 : (2:ℝ) ^ i > 2 ^ (i - r) := by
    apply rpow_lt_rpow_of_exponent_lt; simp only [Nat.one_lt_ofNat]; linarith
  apply div_pos; linarith; apply mul_pos; linarith; linarith

lemma Ep_r_strictMonoOn : StrictMonoOn (Ep i) (Set.Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) (by fun_prop)
  simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi]
  exact fun x => deriv_Ep_r_pos

lemma Ep_r_monotoneOn : MonotoneOn (Ep i) (Set.Ici 0) :=
  StrictMonoOn.monotoneOn Ep_r_strictMonoOn

lemma Em_r_strictMonoOn (hi : i < 0) : StrictMonoOn (Em i) (Set.Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) (by fun_prop (disch := assumption))
  simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi]
  exact fun x => deriv_Em_r_pos hi

lemma Em_r_monotoneOn (hi : i < 0) : MonotoneOn (Em i) (Set.Ici 0) :=
  StrictMonoOn.monotoneOn (Em_r_strictMonoOn hi)

lemma Ep_r_nonneg (hr : 0 ≤ r) : 0 ≤ (Ep i) r := by
  rw [← Ep_eq_zero i]
  apply Ep_r_monotoneOn _ hr hr
  simp only [Set.mem_Ici, le_refl]

lemma Ep_r_pos (hr : 0 < r) : 0 < (Ep i) r := by
  rw [← Ep_eq_zero i]
  apply Ep_r_strictMonoOn _ (le_of_lt hr) hr
  simp only [Set.mem_Ici, le_refl]

lemma Em_r_nonneg (hi : i < 0) (hr : 0 ≤ r) : 0 ≤ (Em i) r := by
  rw [← Em_eq_zero i]
  apply Em_r_monotoneOn hi _ hr hr
  simp only [Set.mem_Ici, le_refl]

lemma Em_r_pos (hi : i < 0) (hr : 0 < r) : 0 < (Em i) r := by
  rw [← Em_eq_zero i]
  apply Em_r_strictMonoOn hi _ (le_of_lt hr) hr
  simp only [Set.mem_Ici, le_refl]

lemma deriv_Ep_r_strictMono : StrictMonoOn (deriv (Ep r)) (Set.Ici 0) := by
  rw [deriv_Ep_r]
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) (by fun_prop (disch := simp))
  simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi]
  intro x hx
  get_deriv (fun r_1 ↦ (2 ^ r - 2 ^ (r - r_1)) / ((1 + 2 ^ r) * (1 + 2 ^ (r - r_1)))) at x
  simp only [List.Forall, toFun, ne_eq, mul_eq_zero, one_plus_two_pow_ne_zero, or_self,
    not_false_eq_true, id_eq, gt_iff_lt, Nat.ofNat_pos, and_self]
  simp only [toFun] at h
  rw [HasDerivAt.deriv h]; simp only [zero_mul, add_zero, zero_sub, neg_mul, one_mul, zero_add,
    sub_neg_eq_add, mul_neg, Nat.cast_ofNat, rpow_two, gt_iff_lt]
  have : (2 ^ (r - x) * log 2 * ((1 + 2 ^ r) * (1 + 2 ^ (r - x))) +
      (2 ^ r - 2 ^ (r - x)) * ((1 + 2 ^ r) * (2 ^ (r - x) * log 2))) /
    ((1 + 2 ^ r) * (1 + 2 ^ (r - x))) ^ 2 = 2 ^ (r - x) * log 2/ (1 + 2 ^ (r - x))^2 := by
    field_simp; ring_nf
  rw [this]; positivity

lemma deriv_Em_r_strictMono (hi : i < 0) : StrictMonoOn (deriv (Em i)) (Set.Ioi (0:ℝ)) := by
  have : ∀ x ∈ Set.Ioi 0, (2:ℝ) ≠ 0 ∨ 0 < i - x := by simp only [Set.mem_Ioi, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, sub_pos, true_or, implies_true]
  have : ∀ x ∈ Set.Ioi 0, (1 - (2:ℝ) ^ i) * (1 - 2 ^ (i - x)) ≠ 0 := by
    intro x hx; simp only [Set.mem_Ioi, Set.mem_Iio] at hx hi
    have _ : (2:ℝ) ^ i < 1 := by apply rpow_lt_one_of_one_lt_of_neg _ hi; simp only [Nat.one_lt_ofNat]
    have _ : (2:ℝ) ^ (i-x) < 1 := by apply rpow_lt_one_of_one_lt_of_neg; simp only [Nat.one_lt_ofNat]; linarith
    norm_num; constructor <;> linarith
  apply StrictMonoOn.congr _ (Set.EqOn.symm (deriv_Em_r hi))
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0) (by fun_prop (disch := assumption))
  intro x hx; simp only [interior_Ioi, Set.mem_Ioi, Set.mem_Iio] at hx hi
  have i1 : (2:ℝ) ^ i < 1 := by apply rpow_lt_one_of_one_lt_of_neg _ hi; simp only [Nat.one_lt_ofNat]
  have i1 : 1 - (2:ℝ) ^ i ≠ 0 := by linarith
  have _ : (2:ℝ) ^ (i-x) < 1 := by apply rpow_lt_one_of_one_lt_of_neg; simp only [Nat.one_lt_ofNat]; linarith
  have _ : 1 - (2:ℝ) ^ (i-x) > 0 := by linarith
  have i3 : (2:ℝ) ^ i > 2 ^ (i - x) := by apply rpow_lt_rpow_of_exponent_lt; simp only [Nat.one_lt_ofNat]; linarith
  get_deriv (fun r ↦ (2 ^ i - 2 ^ (i - r)) / ((1 - 2 ^ i) * (1 - 2 ^ (i - r)))) at x
  simp only [List.Forall, toFun, ne_eq, mul_eq_zero, not_or, id_eq, gt_iff_lt, Nat.ofNat_pos,
    and_self, and_true]
  constructor <;> linarith
  simp only [toFun] at h; rw [HasDerivAt.deriv h]
  simp only [zero_mul, add_zero, zero_sub, neg_mul, one_mul, zero_add, sub_neg_eq_add, sub_self,
    Nat.cast_ofNat, rpow_two]
  have : (2 ^ (i - x) * log 2 * ((1 - 2 ^ i) * (1 - 2 ^ (i - x))) -
      (2 ^ i - 2 ^ (i - x)) * ((1 - 2 ^ i) * (2 ^ (i - x) * log 2))) /
    ((1 - 2 ^ i) * (1 - 2 ^ (i - x))) ^ 2 = 2 ^ (i - x) * log 2/(1 - 2 ^ (i - x))^2 := by
    field_simp; ring_nf
  rw [this]; positivity

/-
  Continuity and differentiability of Ep(i, r) and Em(i, r) with respect to i
-/

private def fp (a : ℝ) := a * exp (-a) + exp (-a) - 1

private def gp a := exp (-a) + a - 1

@[fun_prop]
lemma differentiable_Ep_i: Differentiable ℝ (fun i => Ep i r) := by
  unfold Ep; rw [deriv_Φp]; fun_prop (disch := simp)

@[fun_prop]
lemma differentiableOn_Em_i (hr : 0 ≤ r) : DifferentiableOn ℝ (fun i => Em i r) (Set.Iio 0) := by
  unfold Em
  have : ∀ i ∈ (Set.Iio 0), (fun i ↦ -Φm (i - r) + Φm i - r * deriv Φm i) i =
            (fun i ↦ -Φm (i - r) + Φm i - r * (-(2 : ℝ) ^ i / (1 - (2 : ℝ) ^ i))) i := by
    intro i hi ; simp only [sub_right_inj, mul_eq_mul_left_iff]
    simp only [deriv_Φm hi, true_or]
  apply DifferentiableOn.congr _ this
  have : ∀ x ∈ Set.Iio 0, x - r < 0 := by
    simp only [Set.mem_Iio, sub_neg]; intro x x0; linarith
  have := one_minus_two_pow_ne_zero
  fun_prop (disch := first | assumption | simp)

private lemma deriv_Ep_i : deriv (fun i => Ep i r) =
    fun (i : ℝ) => 2 ^ i / ((1 + 2 ^ i) ^ 2 * (1 + 2 ^ (i - r))) * (2 ^ i * fp (log 2 * r) + gp (log 2 * r)) := by
  unfold Ep; rw [deriv_Φp]; simp only [Φp, logb, fp, gp]
  get_deriv fun i ↦ log (1 + 2 ^ (i - r)) / log 2 - log (1 + 2 ^ i) / log 2 + r * (2 ^ i / (1 + 2 ^ i))
  simp only [List.Forall, toFun, ne_eq, log_eq_zero, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one,
    or_self, not_false_eq_true, id_eq, one_plus_two_pow_ne_zero, gt_iff_lt, Nat.ofNat_pos,
    and_self, implies_true, (by norm_num : (2 : ℝ) ≠ -1)]
  simp only [toFun, zero_mul, sub_zero, one_mul, zero_add, zero_div, mul_zero, Nat.cast_ofNat,
    rpow_two] at h
  simp only [h.right]; ext x; simp [aux_eq1, aux_eq2]; field_simp; ring_nf

private lemma deriv_Em_i (hr : 0 ≤ r) : Set.EqOn (deriv (fun i => Em i r))
    (fun (i : ℝ) => 2 ^ i / ((1 - 2 ^ i) ^ 2 * (1 - 2 ^ (i - r))) * (-(2 ^ i * fp (log 2 * r)) + gp (log 2 * r))) (Set.Iio 0) := by
  unfold Em Set.EqOn; intro i hi
  have : deriv (fun i ↦ -Φm (i - r) + Φm i - r * deriv Φm i) i =
        deriv (fun i ↦ -Φm (i - r) + Φm i - r * -(2 : ℝ) ^ i / (1 - (2 : ℝ) ^ i)) i := by
    apply deriv_EqOn_Iio _ hi; intro y hy; simp only [mul_neg, sub_right_inj]
    simp only [deriv_Φm hy]; field_simp
  rw [this]; simp only [Φm, logb, mul_neg, fp, neg_mul, gp]
  get_deriv (fun i ↦ -(log (1 - 2 ^ (i - r)) / log 2) + log (1 - 2 ^ i) / log 2 - -(r * 2 ^ i) / (1 - 2 ^ i)) within (Set.Iio 0)
  simp only [Set.mem_Iio, List.Forall, toFun, ne_eq, log_eq_zero, OfNat.ofNat_ne_zero,
    OfNat.ofNat_ne_one, or_self, not_false_eq_true, id_eq, gt_iff_lt, Nat.ofNat_pos,
    and_self, and_true, true_and, (by norm_num : (2 : ℝ) ≠ -1)]
  intro x hx; exact aux_inq1' hx r hr
  simp only [toFun, zero_mul, sub_zero, one_mul, zero_add, zero_sub, zero_div,
    mul_zero, Nat.cast_ofNat, rpow_two, neg_mul, mul_neg, neg_neg] at h
  rw [h.right i hi]
  have ie := one_minus_two_pow_ne_zero4 hi hr
  have ie2 := one_minus_two_pow_ne_zero2 i hi
  field_simp
  simp [aux_eq1, aux_eq2]; field_simp; ring_nf

/-
  Monotonicity properties of Ep(i, r) and Em(i, r) with respect to i
-/

private lemma differentiable_fp : Differentiable ℝ fp := by
  unfold fp; fun_prop

private lemma deriv_fp : deriv fp = fun (a : ℝ) => -a * exp (-a) := by
  unfold fp
  get_deriv fun a ↦ a * rexp (-a) + rexp (-a) - 1
  simp only [List.Forall, implies_true]
  simp_all only [toFun, differentiable_const, Differentiable.sub_iff_left, one_mul, mul_neg,
    mul_one, add_neg_cancel_comm, sub_zero, neg_mul]

private lemma fp_nonpos (hx : 0 ≤ x) : fp x ≤ 0 := by
  have eq : fp 0 = 0 := by
    simp only [fp, neg_zero, exp_zero, mul_one, zero_add, sub_self]
  rw [← eq]
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0) (by unfold fp; fun_prop) _ _ (le_refl 0) hx hx
  · apply Differentiable.differentiableOn differentiable_fp
  · simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi]
    intro x hx
    simp only [deriv_fp, neg_mul, Left.neg_nonpos_iff]
    positivity

private def N a (i:ℝ) := 2 ^ i * fp a + gp a

private def N0 a := N a 0

private lemma differentiable_N0 : Differentiable ℝ N0 := by unfold N0 N gp fp; fun_prop

private lemma deriv_N0 : deriv N0 = fun x => -fp x := by
  unfold N0 N fp gp
  deriv_EQ fun a ↦ 2 ^ 0 * (a * rexp (-a) + rexp (-a) - 1) + (rexp (-a) + a - 1)
  ring_nf

private lemma N0_eq_zero : N0 0 = 0 := by
  simp only [N0, N, pow_zero, fp, neg_zero, exp_zero, mul_one, zero_add, sub_self, mul_zero, gp, add_zero]

private lemma N0_nonneg (ha : 0 ≤ a) : 0 ≤ N0 a := by
  rw [← N0_eq_zero]
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0) _ _ _ (le_refl 0) ha ha
  · exact differentiable_N0.continuous.continuousOn
  · apply differentiable_N0.differentiableOn
  · simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi]
    intro x hx
    simp only [deriv_N0, ge_iff_le, Left.nonneg_neg_iff]
    exact fp_nonpos (le_of_lt hx)

private lemma differentiable_N : Differentiable ℝ (N a) := by
  unfold N fp gp; fun_prop (disch := simp)

private lemma deriv_N : deriv (N a) = fun i => 2 ^ i * log 2 * fp a := by
  unfold N fp gp
  get_deriv fun i ↦ 2 ^ i * (a * rexp (-a) + rexp (-a) - 1) + (rexp (-a) + a - 1)
  simp only [List.Forall, toFun, gt_iff_lt, Nat.ofNat_pos, id_eq, implies_true]
  simp_all only [toFun, differentiable_add_const_iff, deriv_add_const', deriv_mul_const_field',
    zero_mul, one_mul, zero_add, neg_zero, mul_zero, add_zero, sub_self]

private lemma N_nonneg (hi : i ≤ 0) (ha : 0 ≤ a) : 0 ≤ N a i := by
  apply le_trans (N0_nonneg ha); unfold N0
  apply antitoneOn_of_deriv_nonpos (convex_Iic 0) _ _ _ hi (by norm_num) hi
  · exact differentiable_N.continuous.continuousOn
  · exact differentiable_N.differentiableOn
  simp only [Set.nonempty_Ioi, interior_Iic', Set.mem_Iio]
  intro x hx; simp only [deriv_N]
  apply mul_nonpos_of_nonneg_of_nonpos _ (fp_nonpos ha)
  positivity

lemma deriv_Ep_i_nonneg (hi : i ≤ 0) (hr : 0 ≤ r) : 0 ≤ (deriv (fun i => Ep i r)) i := by
  simp only [deriv_Ep_i, ge_iff_le]
  apply mul_nonneg (by positivity)
  rw [← N]; apply N_nonneg hi
  positivity

lemma Ep_i_monotoneOn (hr : 0 ≤ r) : MonotoneOn (fun i => Ep i r) (Set.Iic 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Iic 0)
  · exact differentiable_Ep_i.continuous.continuousOn
  · fun_prop
  simp only [Set.nonempty_Ioi, interior_Iic', Set.mem_Iio]
  intro i hi; exact deriv_Ep_i_nonneg (le_of_lt hi) hr

private lemma differentiable_gp : Differentiable ℝ gp := by
  unfold gp; fun_prop

private lemma gp_nonneg (ha : 0 ≤ a) : 0 ≤ gp a := by
  have eq : gp 0 = 0 := by
    simp only [gp, neg_zero, exp_zero, add_zero, sub_self]
  rw [← eq]
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0) _ _ _ (le_refl 0) ha ha
  · exact differentiable_gp.continuous.continuousOn
  · exact differentiable_gp.differentiableOn
  simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi]
  intro x hx; unfold gp
  get_deriv (fun a ↦ rexp (-a) + a - 1)
  simp only [List.Forall, implies_true]
  simp only [toFun, differentiable_const, Differentiable.sub_iff_left, differentiable_id',
    Differentiable.add_iff_left, mul_neg, mul_one, sub_zero] at h
  simp only [h.right, ge_iff_le, le_neg_add_iff_add_le, add_zero, exp_le_one_iff,
    Left.neg_nonpos_iff, le_of_lt hx]

lemma deriv_Em_i_nonneg (hi : i < 0) (hr : 0 ≤ r) : 0 ≤ (deriv (fun i => Em i r)) i := by
  simp only [deriv_Em_i hr hi, ge_iff_le]
  have i2 : (2:ℝ) ^ (i-r) < 1 := by apply rpow_lt_one_of_one_lt_of_neg; simp only [Nat.one_lt_ofNat]; linarith
  have i2 : 1 - (2:ℝ) ^ (i-r) > 0 := by linarith
  have i0 : (2:ℝ) ^ i > 0 := by positivity
  have ie : (-(2 ^ i * LNS.fp (log 2 * r)) + LNS.gp (log 2 * r)) ≥ 0 := by
    have : 2 ^ i * (- LNS.fp (log 2 * r)) ≥ 0 := by
      apply mul_nonneg; linarith; simp only [Left.nonneg_neg_iff]; apply fp_nonpos; positivity
    have : LNS.gp (log 2 * r) ≥ 0 := by apply gp_nonneg; positivity
    linarith
  positivity

lemma Em_i_monotoneOn (hr : 0 ≤ r) : MonotoneOn (fun i => Em i r) (Set.Iio 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Iio 0)
  · exact (differentiableOn_Em_i hr).continuousOn
  · simp only [interior_Iio]; exact differentiableOn_Em_i hr
  simp only [interior_Iio, Set.mem_Iio]
  exact fun i hi => deriv_Em_i_nonneg hi hr

/- Simplified expressions for error bounds -/

lemma Ep_bound (hd : 0 < Δ) : Ep 0 Δ < log 2 / 8 * Δ ^ 2 := by
  set f := fun (x : ℝ) => log 2 / 8 * x ^ 2 - Ep 0 x
  suffices h : f 0 < f Δ by simp_all [f, Ep_eq_zero]
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) (by fun_prop) _ (le_refl 0) (le_of_lt hd) hd
  simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi]
  intro x hx
  rw [deriv_sub (by fun_prop) (by fun_prop), deriv_Ep_r]; simp; norm_num
  set g := fun (x : ℝ) => log 2 / 8 * (2 * x) - (1 - 2 ^ (-x)) / (2 * (1 + 2 ^ (-x)))
  suffices h : g 0 < g x by simp_all [g]
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) (by fun_prop (disch := simp)) _ (le_refl 0) (le_of_lt hx) hx
  simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi]
  intro x hx; clear * - hx
  get_deriv (fun x ↦ log 2 / 8 * (2 * x) - (1 - 2 ^ (-x)) / (2 * (1 + 2 ^ (-x)))) at x; simp
  simp at h; rw [h.deriv]; clear h g
  field_simp; apply lt_of_sub_pos
  set y := (2 : ℝ) ^ (-x)
  ring_nf
  rw [(by ring : log 2 * 8 - log 2 * y * 16 + log 2 * y ^ 2 * 8 = log 2 * 8 * (1 - y) ^ 2)]
  refine mul_pos (by norm_num [log_pos]) (pow_pos ?_ 2)
  simp [y]
  apply rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)

lemma Em_bound (hd : 0 < Δ) : Em (-1) Δ < log 2 * Δ ^ 2 := by
  set f := fun (x : ℝ) => log 2 * x ^ 2 - Em (-1) x
  suffices h : f 0 < f Δ by simp_all [f, Em_eq_zero]
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) (by fun_prop (disch := norm_num)) _ (le_refl 0) (le_of_lt hd) hd
  simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi]
  intro x hx
  rw [deriv_sub (by fun_prop) (by fun_prop (disch := simp_all)), deriv_Em_r (by norm_num) hx]; simp; norm_num
  set g := fun (x : ℝ) => log 2 * (2 * x) - (1 / 2 - 2 ^ (-1 - x)) / (1 / 2 * (1 - 2 ^ (-1 - x)))
  suffices h : g 0 < g x by unfold g at h; norm_num at h; exact h
  have ineq : ∀ x : ℝ, 0 ≤ x → 1 - (2 : ℝ) ^ (-1 - x) ≠ 0 := by
    intro x hx; apply one_minus_two_pow_ne_zero2; linarith
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) _ _ (le_refl 0) (le_of_lt hx) hx
  · have ineq : ∀ x ∈ Set.Ici (0 : ℝ), 1 / 2 * (1 - (2 : ℝ) ^ (-1 - x)) ≠ 0 := by
      simp; exact ineq
    fun_prop (disch := first | assumption | simp)
  simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi]
  intro x hx; clear * - hx ineq
  get_deriv (fun x ↦ log 2 * (2 * x) - (1 / 2 - 2 ^ (-1 - x)) / (1 / 2 * (1 - 2 ^ (-1 - x)))) at x; simp [ineq x (le_of_lt hx)]
  simp [g] at *; rw [h.deriv]; clear h g
  have ineq2 : 2 * (2 * 2) * (1 - (2 : ℝ) ^ (-1 - x)) ^ 2 ≠ 0 := by
    norm_num; apply ineq; exact le_of_lt hx
  field_simp; norm_num; apply lt_of_sub_pos
  set y := (2 : ℝ) ^ (-1 - x)
  ring_nf
  rw [(by ring : log 2 * 16 - log 2 * y * 40 + log 2 * y ^ 2 * 16 = (log 2 * 8) * ((2 * y - 1) * (y - 2)))]
  apply mul_pos (by norm_num [log_pos])
  suffices y < 1 / 2 by exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
  simp [y]; rw [← rpow_neg_one 2]
  exact rpow_lt_rpow_of_exponent_lt one_lt_two (by linarith)
