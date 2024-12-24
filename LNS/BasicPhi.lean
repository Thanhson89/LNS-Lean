import LNS.Common
import LNS.Tactic
import LNS.Definitions

namespace LNS

noncomputable section

open Real

/-
  Inequalities for fun_prop
-/

@[simp]
lemma one_plus_two_pow_pos (x : ℝ) : 0 < 1 + (2 : ℝ) ^ x := by
  linarith [rpow_pos_of_pos two_pos x]

@[simp]
lemma one_plus_two_pow_ne_zero (x : ℝ) : 1 + (2 : ℝ) ^ x ≠ 0 := by
  linarith [rpow_pos_of_pos two_pos x]

@[simp]
lemma one_minus_two_pow_ne_zero2 : ∀ x < (0:ℝ), 1 - (2:ℝ) ^ x ≠ 0 := by
  intro x hx
  have ieq : (2:ℝ) ^ x < 1 := by refine rpow_lt_one_of_one_lt_of_neg ?hx hx; linarith
  linarith

@[simp]
lemma one_minus_two_pow_ne_zero : ∀ x ∈ Set.Iio 0, 1 - (2 : ℝ) ^ (x : ℝ) ≠ 0 := by
  simp only [Set.mem_Iio, ne_eq]; exact one_minus_two_pow_ne_zero2

/-
  Properties of Φp
-/

@[fun_prop]
lemma differentiable_Φp : Differentiable ℝ Φp := by
  unfold Φp logb
  fun_prop (disch := simp)

@[fun_prop]
lemma Differentiable.Φp {f : ℝ → ℝ} (hf : Differentiable ℝ f) :
    Differentiable ℝ (fun x => Φp (f x)) := by fun_prop

@[fun_prop]
lemma continuous_Φp : Continuous Φp := differentiable_Φp.continuous

lemma deriv_Φp : deriv Φp = fun (x : ℝ) => (2 : ℝ) ^ x / (1 + (2 : ℝ) ^ x) := by
  unfold Φp logb
  deriv_EQ fun x ↦ log (1 + 2 ^ x) / log 2

lemma deriv2_Φp : deriv (deriv Φp) = fun x => (2 : ℝ) ^ x * log 2 / (1 + (2 : ℝ) ^ x) ^ 2 := by
  simp only [deriv_Φp]
  deriv_EQ (fun x ↦ 2 ^ x / (1 + 2 ^ x))

lemma deriv_Φp_pos : (deriv Φp) x > 0 := by
  simp only [deriv_Φp]; positivity

lemma deriv2_Φp_pos :  deriv (deriv Φp) x > 0 := by
  simp only [deriv2_Φp]; positivity

/-
  Properties of Φm
-/

@[fun_prop]
lemma DifferentiableAt.Φm {f : ℝ → ℝ} (hf : DifferentiableAt ℝ f x) (hx : f x < 0) :
    DifferentiableAt ℝ (fun x => Φm (f x)) x := by
  apply DifferentiableAt.comp
  · have := one_minus_two_pow_ne_zero2 _ hx
    fun_prop (disch := assumption)
  · fun_prop (disch := simp)

@[fun_prop]
lemma DifferentiableOn.Φm {s : Set ℝ} {f : ℝ → ℝ} (hf : DifferentiableOn ℝ f s) (hx : ∀ x ∈ s, f x < 0) :
    DifferentiableOn ℝ (fun x => Φm (f x)) s := by
  apply DifferentiableOn.logb
  · fun_prop (disch := simp)
  intro x xs
  exact one_minus_two_pow_ne_zero (f x) (hx x xs)

@[fun_prop]
lemma differentiableAt_Φm (hx : x < 0) : DifferentiableAt ℝ Φm x := by
  fun_prop (disch := assumption)

@[fun_prop]
lemma differentiable_Φm : DifferentiableOn ℝ Φm (Set.Iio (0:ℝ)) := by
  fun_prop (disch := simp)

@[fun_prop]
lemma ContinuousOn.Φm {s : Set ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f s) (hx : ∀ x ∈ s, f x < 0) :
    ContinuousOn (fun x => Φm (f x)) s := by
  apply ContinuousOn.div_const
  have : ∀ x ∈ s, 1 - (2 : ℝ) ^ f x ≠ 0 := by
    intro x xs; apply one_minus_two_pow_ne_zero2; exact hx x xs
  apply ContinuousOn.log _ this
  fun_prop (disch := first | simp | assumption)

@[fun_prop]
lemma continuous_Φm : ContinuousOn Φm (Set.Iio 0) := differentiable_Φm.continuousOn

lemma deriv_Φm : Set.EqOn (deriv Φm) (fun x=> -(2 : ℝ) ^ x / (1 - (2 : ℝ) ^ x)) (Set.Iio (0 : ℝ)) := by
  unfold Φm logb
  get_deriv (fun x ↦ log (1 - 2 ^ x) / log 2) within (Set.Iio (0:ℝ))
  · simp only [Set.mem_Iio, List.Forall, toFun, ne_eq, log_eq_zero, OfNat.ofNat_ne_zero,
      OfNat.ofNat_ne_one, or_self, not_false_eq_true, id_eq, gt_iff_lt, Nat.ofNat_pos,
      and_self, and_true, true_and, (by norm_num : (2 : ℝ) ≠ -1)]
    exact one_minus_two_pow_ne_zero2
  simp only [toFun, Set.mem_Iio, deriv_div_const, zero_mul, one_mul, zero_add, zero_sub, zero_div,
    mul_zero, sub_zero, Nat.cast_ofNat, rpow_two] at h
  simp only [Set.EqOn, Set.mem_Iio, deriv_div_const]
  intro x hx
  simp only [h.right x hx]; field_simp; ring_nf

lemma deriv2_Φm : Set.EqOn (deriv (deriv Φm)) (fun x => -(log 2 * (2 : ℝ) ^ x ) / (1 - (2 : ℝ) ^ x) ^ 2) (Set.Iio (0 : ℝ)) := by
  unfold Set.EqOn
  intro x hx
  rw [deriv_EqOn_Iio deriv_Φm hx]
  get_deriv (fun x ↦ -2 ^ x / (1 - 2 ^ x)) within (Set.Iio (0:ℝ))
  simp only [Set.mem_Iio, List.Forall, toFun, ne_eq, id_eq, gt_iff_lt, Nat.ofNat_pos, and_self, and_true]
  exact one_minus_two_pow_ne_zero2
  simp only [toFun, zero_mul, one_mul, zero_add, neg_mul, zero_sub, mul_neg, neg_neg,
    Nat.cast_ofNat, rpow_two] at h
  simp only [h.right x hx]; field_simp; ring_nf

lemma Φm_strictAntiOn : StrictAntiOn Φm (Set.Iio 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Iio 0) (by fun_prop)
  simp only [interior_Iio]; intro t ht; simp only [deriv_Φm ht]
  simp only [Set.mem_Iio] at ht
  apply div_neg_of_neg_of_pos; simp only [Left.neg_neg_iff, Nat.ofNat_pos, rpow_pos_of_pos]
  simp only [gt_iff_lt, sub_pos]; apply rpow_lt_one_of_one_lt_of_neg (by simp only [Nat.one_lt_ofNat]) (by linarith)

lemma Φm_antitoneOn : AntitoneOn Φm (Set.Iio 0) := Φm_strictAntiOn.antitoneOn
