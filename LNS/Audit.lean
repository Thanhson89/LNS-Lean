/- This file contains all main results -/

import LNS.Definitions
import LNS.Theorem53
import LNS.Theorem68
import LNS.Theorem72

open LNS

/- First order Taylor approximations -/

theorem TaylorApprox_Φp (fix : FixedPoint) {x Δ : ℝ} (hd : 0 < Δ) (hx : x ≤ 0) :
    |Φp x - ΦTp_fix fix Δ x| < Ep 0 Δ + (2 + Δ) * fix.ε := Theorem53_ΦTp fix hd hx

theorem TaylorApprox_Φm (fix : FixedPoint) {x Δ : ℝ}
    (hdn : ∃ n : ℕ, 1 = n * Δ) (hx : x ≤ -1) :
    |Φm x - ΦTm_fix fix Δ x| < Em (-1) Δ + (2 + Δ) * fix.ε := Theorem53_ΦTm' fix hdn hx

theorem TaylorApprox_Φp_dir (fix : FixedPointDir) {x Δ : ℝ} (hd : 0 < Δ) (hx : x ≤ 0) :
    |Φp x - ΦTp_fix fix Δ x| < Ep 0 Δ + (1 + Δ) * fix.ε := Theorem53_ΦTp_dir fix hd hx

theorem TaylorApprox_Φm_dir (fix : FixedPointDir) {x Δ : ℝ}
    (hdn : ∃ n : ℕ, 1 = n * Δ) (hx : x ≤ -1) :
    |Φm x - ΦTm_fix fix Δ x| < Em (-1) Δ + (1 + Δ) * fix.ε := Theorem53_ΦTm_dir' fix hdn hx

theorem TaylorApprox_Φp' (fix : FixedPoint) {x Δ : ℝ} (hd : 0 < Δ) (hx : x ≤ 0) :
    |Φp x - ΦTp_fix fix Δ x| < (Real.log 2 / 8) * Δ ^ 2 + (2 + Δ) * fix.ε := by
  linarith [Theorem53_ΦTp fix hd hx, Ep_bound hd]

theorem TaylorApprox_Φm' (fix : FixedPoint) {x Δ : ℝ}
    (hdn : ∃ n : ℕ, 1 = n * Δ) (hx : x ≤ -1) :
    |Φm x - ΦTm_fix fix Δ x| < Real.log 2 * Δ ^ 2 + (2 + Δ) * fix.ε := by
  linarith [Theorem53_ΦTm' fix hdn hx, Em_bound (div_one_imp_pos hdn)]

theorem TaylorApprox_Φp_dir' (fix : FixedPointDir) {x Δ : ℝ} (hd : 0 < Δ) (hx : x ≤ 0) :
    |Φp x - ΦTp_fix fix Δ x| < (Real.log 2 / 8) * Δ ^ 2 + (1 + Δ) * fix.ε := by
  linarith [Theorem53_ΦTp_dir fix hd hx, Ep_bound hd]

theorem TaylorApprox_Φm_dir' (fix : FixedPointDir) {x Δ : ℝ}
    (hdn : ∃ n : ℕ, 1 = n * Δ) (hx : x ≤ -1) :
    |Φm x - ΦTm_fix fix Δ x| < Real.log 2 * Δ ^ 2 + (1 + Δ) * fix.ε := by
  linarith [Theorem53_ΦTm_dir' fix hdn hx, Em_bound (div_one_imp_pos hdn)]

/- Error correction approximations -/

theorem ErrorCorrection_Φp (fix : FixedPoint) (hc : c ≤ 0) (hΔ : ΔP < Δ)
    (hΔP : 0 < ΔP) (hx : x ≤ 0) :
    |Φp x - ΦECp_fix fix Δ ΔP c x| ≤ (4 + Δ) * fix.ε + (Ep 0 Δ) * (QRp Δ + QIp Δ ΔP + fix.ε) :=
  Theorem68_ΦECp fix hc hΔ hΔP hx

theorem ErrorCorrection_Φm (fix : FixedPoint) {Δ ΔP : ℝ} (hc : c ≤ -1) (hΔ : ΔP < Δ)
    (hΔP : 0 < ΔP) (hdn : ∃ n : ℕ, 1 = n * Δ) (hx : x ≤ -1) :
    |Φm x - ΦECm_fix fix Δ ΔP c x| ≤ (4 + Δ) * fix.ε + (Em (-1) Δ) * (QRm Δ + QIm Δ ΔP + fix.ε) :=
  Theorem68_ΦECm fix hc hΔ hΔP hdn hx

/- Cotransformations -/

theorem Cotrans_case2 (fix : FixedPoint)
    (Φe : FunApprox Φm (Set.Iic (-1))) /- An approximation of Φm on (-∞, -1] -/
    (ha : 0 < Δa)
    (hΔa : 4 * fix.ε ≤ Δa)             /- Δa should be large enough -/
    (hx : x ≤ -Δa) :                   /- The result is valid for all x ∈ (-∞, -Δa] -/
    |Φm x - Cotrans₂ fix Φe Δa x| ≤ fix.ε + Φm (-1 - 2 * fix.ε) - Φm (-1) + Φe.err :=
  Theorem72_case2 fix Φe ha hΔa hx

theorem Cotrans_case3 (fix : FixedPoint)
    (Φe : FunApprox Φm (Set.Iic (-1)))  /- An approximation of Φm on (-∞, -1] -/
    (ha : 0 < Δa) (hb : 0 < Δb) (hrem : rem Δb x ≤ -Δa)
    (hΔa : 4 * fix.ε ≤ Δa)              /- Δa should be large enough -/
    (hΔb : 8 * fix.ε + 2 * Φe.err ≤ Δb) /- Δb should be large enough -/
    (hx : x ≤ -Δb) :                    /- The result is valid for all x ∈ (-∞, -Δb] -/
    let Ek2 := 2 * fix.ε + Φm (-1 - 2 * fix.ε) - Φm (-1) + Φe.err
    |Φm x - Cotrans₃ fix Φe Δa Δb x| ≤ fix.ε + Φm (-1 - Ek2) - Φm (-1) + Φe.err :=
  Theorem72_case3 fix Φe ha hb hrem hΔa hΔb hx

theorem Cotransformation (fix : FixedPoint)
    (Φe : FunApprox Φm (Set.Iic (-1)))
    (ha : 0 < Δa) (hb : 0 < Δb)
    (hΔa : 4 * fix.ε ≤ Δa)                /- Δa should be large enough -/
    (hΔb : 8 * fix.ε + 2 * Φe.err ≤ Δb) : /- Δb should be large enough -/
    let Ek2 := 2 * fix.ε + Φm (-1 - 2 * fix.ε) - Φm (-1) + Φe.err
    |Φm x - Cotrans fix Φe Δa Δb x| ≤ fix.ε + Φm (-1 - Ek2) - Φm (-1) + Φe.err :=
  Theorem72 fix Φe ha hb hΔa hΔb

theorem Cotransformation_dir (fix : FixedPointDir)
    (Φe : FunApprox Φm (Set.Iic (-1)))
    (ha : 0 < Δa) (hb : 0 < Δb)
    (hΔa : 2 * fix.ε ≤ Δa)                /- Δa should be large enough -/
    (hΔb : 4 * fix.ε + 2 * Φe.err ≤ Δb) : /- Δb should be large enough -/
    let Ek2 := fix.ε + Φm (-1 - fix.ε) - Φm (-1) + Φe.err
    |Φm x - Cotrans fix Φe Δa Δb x| ≤ fix.ε + Φm (-1 - Ek2) - Φm (-1) + Φe.err :=
  Theorem72_dir fix Φe ha hb hΔa hΔb

theorem Cotransformation' (fix : FixedPoint)
    (Φe : FunApprox Φm (Set.Iic (-1)))
    (ha : 0 < Δa) (hb : 0 < Δb)
    (hΔa : 4 * fix.ε ≤ Δa)                /- Δa should be large enough -/
    (hΔb : 8 * fix.ε + 2 * Φe.err ≤ Δb) : /- Δb should be large enough -/
    |Φm x - Cotrans fix Φe Δa Δb x| ≤ 5 * fix.ε + 2 * Φe.err :=
  Theorem72' fix Φe ha hb hΔa hΔb

theorem Cotransformation_dir' (fix : FixedPointDir)
    (Φe : FunApprox Φm (Set.Iic (-1)))
    (ha : 0 < Δa) (hb : 0 < Δb)
    (hΔa : 2 * fix.ε ≤ Δa)                /- Δa should be large enough -/
    (hΔb : 4 * fix.ε + 2 * Φe.err ≤ Δb) : /- Δb should be large enough -/
    |Φm x - Cotrans fix Φe Δa Δb x| ≤ 3 * fix.ε + 2 * Φe.err :=
  Theorem72_dir' fix Φe ha hb hΔa hΔb

/- All theorems depend on standard axioms only: [propext, Classical.choice, Quot.sound]-/

#print axioms TaylorApprox_Φp
#print axioms TaylorApprox_Φm
#print axioms TaylorApprox_Φp_dir
#print axioms TaylorApprox_Φm_dir
#print axioms TaylorApprox_Φp'
#print axioms TaylorApprox_Φm'
#print axioms TaylorApprox_Φp_dir'
#print axioms TaylorApprox_Φm_dir'
#print axioms ErrorCorrection_Φp
#print axioms ErrorCorrection_Φm
#print axioms Cotrans_case2
#print axioms Cotrans_case3
#print axioms Cotransformation
#print axioms Cotransformation_dir
#print axioms Cotransformation'
#print axioms Cotransformation_dir'
