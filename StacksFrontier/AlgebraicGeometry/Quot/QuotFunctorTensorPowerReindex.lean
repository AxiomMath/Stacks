module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotCoherentCondition
public import StacksFrontier.AlgebraicGeometry.Quot.QuotHilbertPolynomialReindex
public import StacksFrontier.AlgebraicGeometry.Quot.TwistedEulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.Quot.TwistedEulerSchemeTheoreticSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedEulerNumericalPolynomialProper

/-!
# Replacing the polarisation by a tensor power

Let `f : X ⟶ B` be a morphism of algebraic spaces of finite presentation, `F` a quasi-coherent
`𝒪_X`-module and `L` an invertible `𝒪_X`-module.  For a numerical polynomial `P`, the
subfunctor `Quot^{P, L}_{F/X/B}` of the Quot functor consists of the quotients `F_T ⟶ Q` with
`P(m) = χ(X_t, Q_t ⊗ L_t^{⊗ m})` for every point `t ∈ T` and every `m ∈ ℤ`.  For an integer
`n ≠ 0`,

`Quot^{P, L}_{F/X/B} = Quot^{P', L^{⊗ n}}_{F/X/B}`,  where `P'(t) = P(n t)`.

## Main results

* `AlgebraicGeometry.Space.CoherentObject.hasHilbertPolynomial_invertibleTensorPower_iff`: an
  object of `Coh_{X/B}` has Hilbert polynomial `P'` with respect to `L^{⊗ n}` exactly when it has
  Hilbert polynomial `P` with respect to `L`, that is `Coh^{P, L}_{X/B} = Coh^{P', L^{⊗ n}}_{X/B}`.
* `AlgebraicGeometry.Space.QuotSituation.setOf_hasHilbertPolynomial_invertibleTensorPower_eq`:
  `Quot^{P, L}_{F/X/B} = Quot^{P', L^{⊗ n}}_{F/X/B}` for `n ≠ 0`.

## Implementation notes

A *numerical polynomial* `P : ℤ → ℤ` is taken to be the function of a rational polynomial at
*every* integer: the hypothesis is `∃ p : Polynomial ℚ, ∀ m : ℤ, p.eval m = P m`, and such a `p`
is automatically numerical in the sense of `Polynomial.IsNumerical`.  The weaker notion asking for
agreement only at `m ≫ 0` (`IsNumericalPolynomial`) would make the statement false for `|n| ≥ 2`:
changing `P` at one small integer not divisible by `n` changes `Quot^{P, L}` (to the empty
functor) but not `Quot^{P', L^{⊗ n}}`.

The integer `n` is required to be nonzero: for `n = 0` the statement is false, since
`L^{⊗ 0} = 𝒪_X` and `P'` is the constant `P(0)`, so the right-hand side only prescribes
`χ(X_t, Q_t)`.

The subfunctors are compared at each scheme `T` of the site, on their sets of sections.
Membership is read on the object of `Coh_{X/B}` a quotient gives, through
`AlgebraicGeometry.Space.CoherentObject.HasHilbertPolynomial`.

## References

* [Stacks Project, Tag 0DP8](https://stacks.math.columbia.edu/tag/0DP8)
* [Stacks Project, Tag 0DNF](https://stacks.math.columbia.edu/tag/0DNF)
* [Stacks Project, Tag 0DN4](https://stacks.math.columbia.edu/tag/0DN4)
* [Stacks Project, Tag 027X](https://stacks.math.columbia.edu/tag/027X)
-/
@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

namespace CoherentObject

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}

/-- **`Coh^{P, L}_{X/B} = Coh^{P', L^{⊗ n}}_{X/B}` with `P'(t) = P(n t)`.**  Let `L` be an
invertible `𝒪_X`-module, `P : ℤ → ℤ` a numerical polynomial and `n ≠ 0`.  An object
`(T, 𝓕)` of `Coh_{X/B}` has Hilbert polynomial `m ↦ P(n m)` with respect to `L^{⊗ n}` exactly
when it has Hilbert polynomial `P` with respect to `L`. -/
theorem hasHilbertPolynomial_invertibleTensorPower_iff (L : Modules.{u, u} B S hS D.X.1 D.X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]
    {P : ℤ → ℤ} (hP : ∃ p : Polynomial ℚ, ∀ m : ℤ, p.eval (m : ℚ) = (P m : ℚ))
    {n : ℤ} (hn : n ≠ 0) (A : CoherentObject D) :
    HasHilbertPolynomial (invertibleTensorPower B S hS D.X.1 D.X.2 L n) (fun m => P (n * m)) A ↔
      HasHilbertPolynomial L P A := by
  obtain ⟨p, hp⟩ := hP
  choose q hq using exists_polynomial_eval_eq_twistedEuler L A
  exact (isPrescribedTwistedEuler_iff_reindexMul hp hq hn
    (fun t m => twistedEuler_invertibleTensorPower L A t n m)).symm

end CoherentObject

namespace QuotSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : QuotSituation B S hS) (L : Modules.{u, u} B S hS D.X.1 D.X.2)
  [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]

include hL in
/-- Let `f : X ⟶ B` be a morphism of algebraic spaces of finite presentation, `F` a
quasi-coherent `𝒪_X`-module, `L` an invertible `𝒪_X`-module, `P : ℤ → ℤ` a numerical polynomial
(at every integer, the value of a rational polynomial) and `n` a nonzero integer.  Then

`Quot^{P, L}_{F/X/B} = Quot^{P', L^{⊗ n}}_{F/X/B}`,  where `P'(t) = P(n t)`:

over every scheme `T` of the site, a quotient `F_T ⟶ Q` in `Quot_{F/X/B}(T)` satisfies
`P(m) = χ(X_t, Q_t ⊗ L_t^{⊗ m})` for all `t ∈ T` and `m ∈ ℤ` exactly when it satisfies
`P(n m) = χ(X_t, Q_t ⊗ (L^{⊗ n})_t^{⊗ m})` for all `t ∈ T` and `m ∈ ℤ`, these being the twisted
Euler characteristics `AlgebraicGeometry.Space.CoherentObject.twistedEuler` of the object of
`Coh_{X/B}` the quotient gives. -/
@[stacks 0DP8 "the equality `Quot^{P,L} = Quot^{P',L^{⊗ n}}` with `P'(t) = P(n t)`, for `n ≠ 0` and
`P` a numerical polynomial, compared on the sections over every scheme of the site, membership
read on the actual twisted Euler characteristics `χ(X_t, Q_t ⊗ L_t^{⊗ m})`"]
theorem setOf_hasHilbertPolynomial_invertibleTensorPower_eq {P : ℤ → ℤ}
    (hP : ∃ p : Polynomial ℚ, ∀ m : ℤ, p.eval (m : ℚ) = (P m : ℚ)) {n : ℤ} (hn : n ≠ 0)
    (T : (BigFppfOver B S hS)ᵒᵖ) :
    letI : Stacks.SheafOfModules.IsInvertible
        (structurePresheaf B S hS D.toCoherentSituation.X.1)
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
          D.toCoherentSituation.X.1 D.toCoherentSituation.X.2).O)).property L := hL
    letI := isInvertible_invertibleTensorPower B S hS D.toCoherentSituation.X.1
      D.toCoherentSituation.X.2 L n
    {x : D.quotSitePresheaf.obj T | x.cohObject.HasHilbertPolynomial L P} =
      {x : D.quotSitePresheaf.obj T | x.cohObject.HasHilbertPolynomial
        (invertibleTensorPower B S hS D.toCoherentSituation.X.1 D.toCoherentSituation.X.2 L n)
        (fun m => P (n * m))} :=
  Set.ext fun x => (CoherentObject.hasHilbertPolynomial_invertibleTensorPower_iff
    (D := D.toCoherentSituation) (hL := hL) L hP hn x.cohObject).symm

end QuotSituation

end AlgebraicGeometry.Space

end
