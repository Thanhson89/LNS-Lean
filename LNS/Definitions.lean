import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace LNS

noncomputable section

/- A model of fixed-point arithmetic -/
structure FixedPoint where
  ε : ℝ
  rnd : ℝ → ℝ
  hrnd : ∀ x, |x - rnd x| ≤ ε
  rnd_mono : Monotone rnd
  rnd_1 : rnd 1 = 1
  rnd_0 : rnd 0 = 0

/- Fixed-point arithmetic with directed rounding (down or up) -/
structure FixedPointDir extends FixedPoint where
  rnd_dir : (∀ x, rnd x ≤ x) ∨ (∀ x, x ≤ rnd x)

instance : Coe FixedPointDir FixedPoint where
  coe := FixedPointDir.toFixedPoint

/- FunApprox f s models an approximation of a function f on s -/
structure FunApprox (f : ℝ → ℝ) (s : Set ℝ) where
  fe : ℝ → ℝ
  err : ℝ
  herr : ∀ x ∈ s, |f x - fe x| ≤ err

instance : CoeFun (FunApprox f s) (fun _ => ℝ → ℝ) where
  coe fapprox := fapprox.fe

open Real

/- Φ⁺ and Φ⁻ from Introduction -/

def Φp (x : ℝ) := logb 2 (1 + (2 : ℝ) ^ x)

def Φm (x : ℝ) := logb 2 (1 - (2 : ℝ) ^ x)

/- Iₓ and Rₓ correspond to iₓ and rₓ from Eq (1) -/

def Iₓ (Δ x : ℝ) := ⌈x / Δ⌉ * Δ

def Rₓ (Δ x : ℝ) := Iₓ Δ x - x

/-
  First order Taylor approximation
-/

section Taylor

/- E i r is the error of the first order Taylor approximation
   defined for all real i and r -/

def Ep (i r : ℝ) := Φp (i - r) - Φp i + r * deriv Φp i

def Em (i r : ℝ) := -Φm (i - r) + Φm i - r * deriv Φm i

/- Fixed-point approximations of Ep and Em -/

variable (fix : FixedPoint)

def Ep_fix (i r : ℝ) := Φp (i - r) - fix.rnd (Φp i) + fix.rnd (r * fix.rnd (deriv Φp i))

def Em_fix (i r : ℝ) := Φm (i - r) - fix.rnd (Φm i) + fix.rnd (r * fix.rnd (deriv Φm i))

/- Fixed-point first order Taylor approximations of Φ⁺ and Φ⁻ -/

def ΦTp_fix (Δ x : ℝ) := fix.rnd (Φp (Iₓ Δ x)) - fix.rnd (Rₓ Δ x * fix.rnd (deriv Φp (Iₓ Δ x)))

def ΦTm_fix (Δ x : ℝ) := fix.rnd (Φm (Iₓ Δ x)) - fix.rnd (Rₓ Δ x * fix.rnd (deriv Φm (Iₓ Δ x)))

end Taylor

/-
  Error correction technique
-/

section ErrorCorrection

def Qp (Δ i r : ℝ) := Ep i r / Ep i Δ

def Qp_lo (Δ r : ℝ) := Qp Δ 0 r

def Qp_hi (Δ r : ℝ) := (2 ^ (-r) + r * log 2 - 1) / (2 ^ (-Δ) + Δ * log 2 - 1)

def Rp_opt (Δ : ℝ) :=
  let x := 2 ^ Δ
  let A (y : ℝ) := -2 * y * (log (y + 1) - log y - log 2) - y + 1
  let B (y : ℝ) := y * (2 * log (y + 1) - log y - 2 * log 2)
  logb 2 (B x / A x)

def QRp Δ := Qp_hi Δ (Rp_opt Δ) - Qp_lo Δ (Rp_opt Δ)

def QIp Δ ΔP := 1 - Qp_lo Δ (Δ - ΔP)

def Qm (Δ i r : ℝ) := Em i r / Em i Δ

def Qm_hi (Δ r : ℝ) := Qm Δ (-1) r

def Qm_lo (Δ r : ℝ) := (2 ^ (-r) + r * log 2 - 1) / (2 ^ (-Δ) + Δ * log 2 - 1)

def Rm_opt (Δ : ℝ) :=
  let x := 2 ^ Δ
  let Vm (x : ℝ) := 2 * log x - log (2 * x - 1)
  let Am (y : ℝ) := 2 * y * log y - 2 * y * log (2 * y - 1) + 2 * y - 2
  let Bm (y : ℝ) := y * Vm y
  logb 2 (Bm x / Am x)

def QRm Δ := Qm_hi Δ (Rm_opt Δ) - Qm_lo Δ (Rm_opt Δ)

def QIm Δ ΔP := 1 - Qm_lo Δ (Δ - ΔP)

variable (fix : FixedPoint)

def EECp (Δ ΔP c i r : ℝ) :=
  fix.rnd (Φp i) - fix.rnd (r * fix.rnd (deriv Φp i))
                 + fix.rnd (fix.rnd (Ep i Δ) * fix.rnd (Qp Δ c (⌊r / ΔP⌋ * ΔP)))

def EECp_fix (Δ ΔP c i r : ℝ) := Φp (i - r) - EECp fix Δ ΔP c i r

def EECm (Δ ΔP c i r : ℝ) :=
  fix.rnd (Φm i) - fix.rnd (r * fix.rnd (deriv Φm i))
                 - fix.rnd (fix.rnd (Em i Δ) * fix.rnd (Qm Δ c (⌊r / ΔP⌋ * ΔP)))

def EECm_fix (Δ ΔP c i r  : ℝ) := Φm (i - r) - EECm fix Δ ΔP c i r

/- Fixed-point error correction approximations of Φ⁺ and Φ⁻ -/

def ΦECp_fix (Δ ΔP c : ℝ) (x : ℝ) := EECp fix Δ ΔP c (Iₓ Δ x) (Rₓ Δ x)

def ΦECm_fix (Δ ΔP c : ℝ) (x : ℝ) := EECm fix Δ ΔP c (Iₓ Δ x) (Rₓ Δ x)

end ErrorCorrection

/-
  Cotransformations
-/

section Contrasformation

variable (fix : FixedPoint)
variable {s : Set ℝ}
/- An approximation of Φm on a set s (all main results are proved for s = (-∞, -1]) -/
variable (Φe : FunApprox Φm s)

def ind (Δ : ℝ) (x : ℝ) := (⌈x / Δ⌉ - 1) * Δ

def rem (Δ : ℝ) (x : ℝ) := ind Δ x - x

def kval (Δ : ℝ) (x : ℝ) := x - Φm (ind Δ x) + Φm (rem Δ x)

def krnd (Δ : ℝ) (x : ℝ) := x - fix.rnd (Φm (ind Δ x)) + fix.rnd (Φm (rem Δ x))

/- Case 2: x ∈ [-Δb, -Δa) -/

def Cotrans₂ (Δa : ℝ) (x : ℝ) := fix.rnd (Φm (ind Δa x)) + Φe (krnd fix Δa x)

/- Case 3: x ∈ (-1, -Δb) -/

def rb (Δa Δb : ℝ) (x : ℝ) := ind Δa (rem Δb x)

def ra (Δa Δb : ℝ) (x : ℝ) := rem Δa (rem Δb x)

def k₁ (Δa Δb : ℝ) (x : ℝ) := kval Δa (rem Δb x)

def k₂ (Δb : ℝ) (x : ℝ) := kval Δb x

def k1rnd (Δa Δb : ℝ) (x : ℝ) := krnd fix Δa (rem Δb x)

def k2rnd (Δa Δb : ℝ) (x : ℝ) := x + fix.rnd (Φm (rb Δa Δb x)) + Φe (k1rnd fix Δa Δb x) - fix.rnd (Φm (ind Δb x))

def Cotrans₃ (Δa Δb : ℝ) (x : ℝ) := fix.rnd (Φm (ind Δb x)) + Φe (k2rnd fix Φe Δa Δb x)

/- A general definition -/

def Cotrans (Δa Δb : ℝ) (x : ℝ) :=
  if -Δa ≤ x then fix.rnd (Φm x)
  else if -Δb ≤ x then Cotrans₂ fix Φe Δa x
  else if -Δa ≤ rem Δb x then Cotrans₂ fix Φe Δb x
  else Cotrans₃ fix Φe Δa Δb x

end Contrasformation
