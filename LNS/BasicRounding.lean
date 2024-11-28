import LNS.Definitions

namespace LNS

/- Basic properties of fixed-point rounding -/

lemma FixedPoint.hrnd_sym (fix : FixedPoint) : ∀ x : ℝ, |fix.rnd x - x| ≤ fix.ε := by
  intro x; rw [abs_sub_comm]; exact fix.hrnd x

lemma FixedPoint.eps_nonneg (fix : FixedPoint) : 0 ≤ fix.ε := le_trans (abs_nonneg _) (fix.hrnd 0)

lemma FixedPointDir.self_sub_rnd (fix : FixedPointDir) :
    (∀ x, 0 ≤ x - fix.rnd x ∧ x - fix.rnd x ≤ fix.ε) ∨ (∀ x, -fix.ε ≤ x - fix.rnd x ∧ x - fix.rnd x ≤ 0) := by
  cases fix.rnd_dir with
  | inl h => left; intro x; specialize h x; split_ands <;> linarith [(abs_le.mp (fix.hrnd x)).2]
  | inr h => right; intro x; specialize h x; split_ands <;> linarith [(abs_le.mp (fix.hrnd x)).1]

lemma FixedPointDir.abs_rnd_sub_rnd (fix : FixedPointDir) (x y : ℝ) :
    |(x - fix.rnd x) - (y - fix.rnd y)| ≤ fix.ε := by
  rw [abs_sub_le_iff]
  cases fix.self_sub_rnd with
  | inl h =>
    have ⟨hx1, hx2⟩ := h x
    have ⟨hy1, hy2⟩ := h y
    split_ands <;> linarith
  | inr h =>
    have ⟨hx1, hx2⟩ := h x
    have ⟨hy1, hy2⟩ := h y
    split_ands <;> linarith

/- Basic properties of function approximations -/

lemma FunApprox.err_sym (g : FunApprox f s) :
    ∀ x ∈ s, |g x - f x| ≤ g.err := by
  intro x xs; rw [abs_sub_comm]; exact g.herr x xs
