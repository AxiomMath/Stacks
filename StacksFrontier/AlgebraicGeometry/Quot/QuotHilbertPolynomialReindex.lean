/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotHilbertPolynomial
public import StacksFrontier.AlgebraicGeometry.Quot.TwistedEulerSchemeTheoreticSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedEulerNumericalPolynomialProper
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedTwistedCohomology
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Replacing `L` by `L^{⊗ d}` in `Quot^P_{F/X/B}`

Let `(T, 𝒬)` be an object of `Coh_{X/B}`, `L` an invertible `𝒪_X`-module and `t ∈ T`.  The
twisted Euler characteristic `n ↦ χ(X_t, 𝒬_t ⊗ L_t^{⊗ n})` is the twisted Euler characteristic of
a coherent module and an invertible module on a proper algebraic space over `κ(t)`
(`AlgebraicGeometry.Space.CoherentObject.exists_twistedEuler_eq_eulerCharacteristic`), so by
Stacks 0DN4 it is a numerical polynomial.

With this, Stacks 0DP8 holds for the subfunctors themselves: for a numerical polynomial `P` and
`d ≠ 0`,

`Quot^{P, L}_{F/X/B} = Quot^{P', L^{⊗ d}}_{F/X/B}`,  `P'(t) = P(d t)`.

This is the step "changing `L` into `L^{⊗ d}` and `P(t)` into `P(dt)` leaves
`Quot^P_{F/X/B}` unaffected; some details omitted" of the proof of Stacks 0DPC.

## Main results

* `AlgebraicGeometry.Space.CoherentObject.exists_polynomial_eval_eq_twistedEuler`: the twisted
  Euler characteristics at a point are the values of a rational polynomial.
* `AlgebraicGeometry.Space.QuotSituation.hilbertPolynomialQuot_invertibleTensorPower`: Stacks
  0DP8 on `Quot^P`.
* `AlgebraicGeometry.Space.QuotSituation.hilbertPolynomialQuot_congr`: `Quot^{P, L}` depends only
  on the isomorphism class of `L`.

## References

* [Stacks Project, Tag 0DN4](https://stacks.math.columbia.edu/tag/0DN4)
* [Stacks Project, Tag 0DP8](https://stacks.math.columbia.edu/tag/0DP8)
* [Stacks Project, Tag 0DPC](https://stacks.math.columbia.edu/tag/0DPC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A multivariate polynomial in one variable, read as a polynomial: its value at `x` is the
value of the multivariate polynomial at the constant tuple `x`. -/
private theorem eval_eval₂_X_fin_one (P : MvPolynomial (Fin 1) ℚ) (x : ℚ) :
    (MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X) P).eval x =
      MvPolynomial.eval (fun _ => x) P := by
  have h := MvPolynomial.eval₂_comp_left (Polynomial.evalRingHom x) Polynomial.C
    (fun _ : Fin 1 => (Polynomial.X : Polynomial ℚ)) P
  simp only [Polynomial.coe_evalRingHom] at h
  rw [h]
  congr 1
  · ext a
    simp
  · funext j
    simp

namespace CoherentObject

/-- **The twisted Euler characteristics at a point are a numerical polynomial** (Stacks 0DN4):
for an object `(T, 𝒬)` of `Coh_{X/B}`, an invertible `𝒪_X`-module `L` and `t ∈ T`, there is a
rational polynomial `q` with `q(n) = χ(X_t, 𝒬_t ⊗ L_t^{⊗ n})` for every `n ∈ ℤ`. -/
@[ega "III 7.9.11" "partial"]
theorem exists_polynomial_eval_eq_twistedEuler {D : CoherentSituation B S hS}
    (L : Modules.{u, u} B S hS D.X.1 D.X.2)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]
    (A : CoherentObject D) (t : A.testScheme) :
    ∃ q : Polynomial ℚ, ∀ n : ℤ, q.eval (n : ℚ) = (twistedEuler L A t n : ℚ) := by
  obtain ⟨Z, hf, G, ℒ, hG, hℒ, hcoh, h⟩ := A.exists_twistedEuler_eq_eulerCharacteristic L t
  obtain ⟨P, hP, -⟩ :=
    @hasTwistedEulerPolynomialOfDegreeLE_coherentSchemeTheoreticSupport.{u, u}
      (A.testScheme.residueField t) _ B _ Z 1 (toYonedaId B _ _ Z.1) hf G hG (fun _ => ℒ)
      (fun _ => hℒ)
  refine ⟨MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X) P, fun n => ?_⟩
  rw [eval_eval₂_X_fin_one, h n]
  exact hP (fun _ => n)

/-- **The twisted Euler characteristics depend only on the isomorphism class of `L`.** -/
theorem twistedEuler_congr {D : CoherentSituation B S hS}
    {L L' : Modules.{u, u} B S hS D.X.1 D.X.2}
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L']
    (e : L ≅ L') (A : CoherentObject D) (t : A.testScheme) (n : ℤ) :
    twistedEuler L A t n = twistedEuler L' A t n :=
  eulerCharacteristicAlong_congr _ _ _ _ _ _ _
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      (smallEtaleRingedSite B S hS (A.fibreSpace t).1 (A.fibreSpace t).2).O).obj
        (A.fibreModule t)).mapIso
      ((modulePullback B S hS (baseChangeProjection D.f (A.pointTest t))).mapIso
        (invertibleTensorPowerCongr B S hS D.X.1 D.X.2 e n)))

end CoherentObject

namespace QuotSituation

variable (D : QuotSituation B S hS) (L : Modules.{u, u} B S hS D.X.1 D.X.2)
  [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]

/-- **Stacks 0DP8 on `Quot^P`**: for a numerical polynomial `P` and `d ≠ 0`,
`Quot^{P, L}_{F/X/B} = Quot^{P', L^{⊗ d}}_{F/X/B}` with `P'(t) = P(d t)`.  The twisted Euler
characteristics with respect to `L^{⊗ d}` are those with respect to `L` at the multiples of `d`
(`AlgebraicGeometry.Space.CoherentObject.twistedEuler_invertibleTensorPower`), and both sides
are numerical polynomials
(`AlgebraicGeometry.Space.CoherentObject.exists_polynomial_eval_eq_twistedEuler`), so agreeing
at the multiples of `d` is agreeing everywhere
(`AlgebraicGeometry.Space.isPrescribedTwistedEuler_iff_reindexMul`). -/
theorem hilbertPolynomialQuot_invertibleTensorPower {P : ℤ → ℤ} {p : Polynomial ℚ}
    (hP : ∀ m : ℤ, p.eval (m : ℚ) = (P m : ℚ)) {d : ℤ} (hd : d ≠ 0) :
    D.hilbertPolynomialQuot (invertibleTensorPower B S hS D.X.1 D.X.2 L d)
        (hL := isInvertible_invertibleTensorPower B S hS D.X.1 D.X.2 L d)
        (fun m => P (d * m)) = D.hilbertPolynomialQuot L P := by
  let : Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B S hS D.toCoherentSituation.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        D.toCoherentSituation.X.1 D.toCoherentSituation.X.2).O)).property L := hL
  ext T x
  have hq := fun t => Classical.choose_spec
    (@CoherentObject.exists_polynomial_eval_eq_twistedEuler B S hS D.toCoherentSituation L this
      x.cohObject t)
  exact (isPrescribedTwistedEuler_iff_reindexMul hP hq hd
    (fun t m => @CoherentObject.twistedEuler_invertibleTensorPower B S hS D.toCoherentSituation
      L this x.cohObject t d m)).symm

/-- **`Quot^{P, L}_{F/X/B}` depends only on the isomorphism class of `L`.** -/
theorem hilbertPolynomialQuot_congr {L' : Modules.{u, u} B S hS D.X.1 D.X.2}
    [hL' : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L']
    (e : L ≅ L') (P : ℤ → ℤ) :
    D.hilbertPolynomialQuot L P = D.hilbertPolynomialQuot L' P := by
  let : Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B S hS D.toCoherentSituation.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        D.toCoherentSituation.X.1 D.toCoherentSituation.X.2).O)).property L := hL
  let : Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B S hS D.toCoherentSituation.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        D.toCoherentSituation.X.1 D.toCoherentSituation.X.2).O)).property L' := hL'
  ext T x
  exact forall_congr' fun t => forall_congr' fun n => Iff.of_eq (congrArg (fun z => P n = z)
    (@CoherentObject.twistedEuler_congr B S hS D.toCoherentSituation L L' _ _ e x.cohObject t n))

end QuotSituation

end AlgebraicGeometry.Space
