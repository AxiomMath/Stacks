module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberPrincipal
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorPicardClass
import StacksCore.Tactic.StacksAttribute

/-!
# The reduced special fibre of a regular proper model

Let `X ⟶ Spec(R)` be a regular proper model of a smooth projective curve over the fraction
field of a discrete valuation ring, and write the special fibre as a sum of effective Cartier
divisors `X_k = Σ mᵢ Cᵢ`. Put `d = gcd(m₁, …, mₙ)` and let `D = Σ (mᵢ/d) Cᵢ` be the *reduced
special fibre*. Then `D` is an effective Cartier divisor, `𝒪_X(D)` has order dividing `d` in
`Pic(X)`, and the conormal module `𝒞_{D/X}` is an invertible `𝒪_D`-module of order dividing `d`
in `Pic(D)`.

The proof is the chain `𝒪_X(D)^{⊗d} = 𝒪_X(dD) = 𝒪_X(X_k) = 𝒪_X`, whose only arithmetic input is
that `d` divides each `mᵢ`, together with the fact that `𝒞_{D/X}` is the restriction of
`𝒪_X(-D)` to `D` and so has the pullback class.

**Beware the notation.** On `AlgebraicGeometry.Scheme.IdealSheafData` the sum of divisors is the
product `*` of ideal sheaves and the `n`-fold sum `nD` is the power `^`; Mathlib's `Add` is `⊔`,
which is scheme-theoretic intersection and is *not* divisor addition. So `Σ mᵢ Cᵢ` is written
`∏ i ∈ s, C i ^ m i` throughout.

## Main definitions

* `Stacks.Models.reducedSpecialFibre`: the divisor `D = Σ (mᵢ/d) Cᵢ` obtained from a
  decomposition `Σ mᵢ Cᵢ` by dividing every multiplicity by their greatest common divisor.

## Main results

* `Stacks.Models.reducedSpecialFibre_pow_gcd`: `dD = Σ mᵢ Cᵢ`, the exact-division identity that
  makes `D` the reduced fibre.
* `Stacks.Models.isEffectiveCartierDivisor_reducedSpecialFibre`: `D` is an effective Cartier
  divisor.
* `Stacks.Models.picardClass_specialFiberIdeal`: the special fibre has Picard class `0`.
* `Stacks.Models.zsmul_picardClass_reducedSpecialFibre`: `d • [𝒪_X(D)] = 0` in `Pic(X)`.
* `Stacks.Models.isInvertible_immersionConormalSheaf_reducedSpecialFibre`: `𝒞_{D/X}` is an
  invertible `𝒪_D`-module.
* `Stacks.Models.zsmul_picardClass_immersionConormalSheaf_reducedSpecialFibre`:
  `d • [𝒞_{D/X}] = 0` in `Pic(D)`.
* `Stacks.Models.reducedSpecialFibre_order_dvd_gcd`: the four conclusions together.
* `Stacks.Models.addOrderOf_picardClass_reducedSpecialFibre_dvd` and
  `Stacks.Models.addOrderOf_picardClass_immersionConormalSheaf_reducedSpecialFibre_dvd`: the same
  two torsion statements phrased as divisibility of the additive order by `d`.

## Implementation notes

**Relative to a decomposition.** The components `C₁, …, Cₙ` of the special fibre and their
multiplicities are not constructed here; they enter as hypotheses, namely a finite index set
`s`, a family `C` of effective Cartier divisors and multiplicities `m` with
`X_k = ∏ i ∈ s, C i ^ m i`. This is exactly the phrase "write `X_k = Σ mᵢ Cᵢ`" with which the
standing situation of [Stacks, Tag 0C61](https://stacks.math.columbia.edu/tag/0C61) opens, so
nothing is assumed that the source does not already have in hand, and no canonical indexing of
the components by `irreducibleComponents` is needed. The hypotheses are used only through
`Stacks.Divisors.isEffectiveCartierDivisor_prod` and the identity
`Stacks.Models.reducedSpecialFibre_pow_gcd`.

**The exact division.** Dividing a multiplicity by the greatest common divisor is genuine exact
division: `Stacks.Models.reducedSpecialFibre_pow_gcd` pushes the outer `d`-th power inside the
product with `Finset.prod_pow`, and on each factor `Nat.div_mul_cancel` consumes
`Finset.gcd_dvd`, the proof that `d ∣ mᵢ` for `i ∈ s`. No divisibility hypothesis is assumed.
The degenerate case `d = 0`, which happens exactly when every `mᵢ` with `i ∈ s` vanishes, needs
no separate treatment.

**Reconciling the spellings.** The triviality `𝒪_X(X_k) ≅ 𝒪_X` of
`Stacks.Models.invertibleSheafIso_specialFiberIdeal` is stated over the sheaf of rings
`S.X.ringCatSheaf`, while `Stacks.SheafOfModules.picardClass_zero` is stated over
`Stacks.SheafOfModules.TensorSheafification.structureSheaf S.X.presheaf (structureIsSheaf …)`.
These are definitionally equal but neither `rw` nor instance search crosses between them, so the
move of `StacksFrontier/AlgebraicGeometry/Divisors/DivisorPicardClass.lean` is used: the imported
isomorphism is rebound with a declared type at the spelling the Picard API wants, and the two
Picard classes are then identified with `Stacks.SheafOfModules.picardClass_eq_iff` through
`refine Eq.trans ?_ (… ).symm` rather than by rewriting.

**Transporting along an equality of divisors.** `d • [𝒪_X(D)] = [𝒪_X(dD)]` and
`[𝒪_X(dD)] = [𝒪_X(X_k)]` are composed with `Stacks.Divisors.picardClass_congr`, which transports
a Picard class along an equality of ideal sheaves. A `rw` with
`Stacks.Models.reducedSpecialFibre_pow_gcd` is not available here, since it would have to
rewrite underneath the effective-Cartier instance argument of the Picard class.

**Pushing `d •` through the pullback.** The conormal statement uses
`Stacks.Picard.schemePullbackClassHom`, the pullback as a homomorphism of abelian groups, so
that `d • f^*x = f^*(d • x)` is `map_zsmul` and `f^*0 = 0` is `map_zero`; the non-bundled
`Stacks.Picard.schemePullbackClass` agrees with it by definition.

## References

* [Stacks Project, Tag 0C67](https://stacks.math.columbia.edu/tag/0C67)
* [Stacks Project, Tag 0C61](https://stacks.math.columbia.edu/tag/0C61)
* [Stacks Project, Tag 0C5Z](https://stacks.math.columbia.edu/tag/0C5Z)
* [Stacks Project, Tag 01WT](https://stacks.math.columbia.edu/tag/01WT)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.Divisors
open Stacks.Picard (ofScheme schemePullbackClass schemePullbackClassHom)
open Stacks.RingedSpace (structureIsSheaf)
open Stacks.SheafOfModules (IsInvertible picardClass)

universe u

namespace Stacks.Models

/-! ### The reduced fibre of a decomposition, and the exact division by the gcd -/

section Arithmetic

variable {X : Scheme.{u}} {ι : Type*} (s : Finset ι) (C : ι → X.IdealSheafData) (m : ι → ℕ)

/-- **The reduced fibre of a decomposition `Σ mᵢ Cᵢ`**: the divisor `Σ (mᵢ/d) Cᵢ` obtained by
dividing every multiplicity by the greatest common divisor `d = gcd(mᵢ)` of all of them. -/
abbrev reducedSpecialFibre : X.IdealSheafData := ∏ i ∈ s, C i ^ (m i / s.gcd m)

/-- **The reduced fibre recovers the original divisor after multiplication by the gcd**,
`dD = Σ mᵢ Cᵢ`: the greatest common divisor divides each multiplicity, so `(mᵢ/d)d = mᵢ`. -/
theorem reducedSpecialFibre_pow_gcd :
    reducedSpecialFibre s C m ^ s.gcd m = ∏ i ∈ s, C i ^ m i := by
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [← pow_mul, Nat.div_mul_cancel (Finset.gcd_dvd hi)]

/-- **The reduced fibre of a decomposition into effective Cartier divisors is an effective
Cartier divisor**, being a sum of nonnegative multiples of effective Cartier divisors. -/
@[stacks 0C67 "D is an effective Cartier divisor, given a decomposition of X_k"]
theorem isEffectiveCartierDivisor_reducedSpecialFibre
    (hC : ∀ i ∈ s, IsEffectiveCartierDivisor (C i)) :
    IsEffectiveCartierDivisor (reducedSpecialFibre s C m) :=
  isEffectiveCartierDivisor_prod s C _ hC

end Arithmetic

/-! ### The special fibre is principal, hence trivial in the Picard group -/

/-- **The special fibre of a regular proper model has Picard class `0`.** Its invertible sheaf
`𝒪_X(X_k)` is trivial, because the special fibre is cut out by the single global function
determined by a uniformizer. -/
theorem picardClass_specialFiberIdeal (S : RegularProperModelSituation.{u}) :
    picardClass S.specialFiberIdeal = 0 := by
  have e : invertibleSheaf' S.specialFiberIdeal ≅
      _root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        S.X.presheaf (structureIsSheaf S.X.toRingedSpace)) :=
    invertibleSheafIso_specialFiberIdeal S
  refine Eq.trans ?_ (Stacks.SheafOfModules.picardClass_zero S.X.presheaf
    (structureIsSheaf S.X.toRingedSpace))
  exact (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2 ⟨e⟩

/-! ### Tag 0C67: the reduced special fibre is `d`-torsion in the Picard group -/

section Model

variable (S : RegularProperModelSituation.{u}) {ι : Type*} (s : Finset ι)
  (C : ι → S.X.IdealSheafData) (m : ι → ℕ)
  [IsEffectiveCartierDivisor (reducedSpecialFibre s C m)]

/-- **Stacks Project, Tag 0C67.** The invertible sheaf `𝒪_X(D)` of the reduced special fibre
`D = Σ (mᵢ/d) Cᵢ` of a regular proper model has order dividing `d` in `Pic(X)`:
`𝒪_X(D)^{⊗d} = 𝒪_X(dD) = 𝒪_X(X_k) = 𝒪_X`. -/
@[stacks 0C67 "O_X(D) has order dividing d in Pic(X), given a decomposition of X_k"]
theorem zsmul_picardClass_reducedSpecialFibre
    (hdec : S.specialFiberIdeal = ∏ i ∈ s, C i ^ m i) :
    ((s.gcd m : ℕ) : ℤ) • picardClass (reducedSpecialFibre s C m) = 0 := by
  have hD : reducedSpecialFibre s C m ^ s.gcd m = S.specialFiberIdeal :=
    (reducedSpecialFibre_pow_gcd s C m).trans hdec.symm
  refine Eq.trans (picardClass_pow (reducedSpecialFibre s C m) (s.gcd m)).symm ?_
  exact (picardClass_congr hD).trans (picardClass_specialFiberIdeal S)

/-- **Stacks Project, Tag 0C67.** The conormal module `𝒞_{D/X}` of the reduced special fibre
`D = Σ (mᵢ/d) Cᵢ` is an invertible `𝒪_D`-module: it is the restriction `ℐ_D|_D` of the ideal
sheaf of an effective Cartier divisor. -/
@[stacks 0C67 "the conormal sheaf of D is an invertible O_D-module"]
theorem isInvertible_immersionConormalSheaf_reducedSpecialFibre :
    IsInvertible (reducedSpecialFibre s C m).subscheme.presheaf
      (structureIsSheaf (reducedSpecialFibre s C m).subscheme.toRingedSpace)
      (Stacks.Thickenings.immersionConormalSheaf (reducedSpecialFibre s C m).subschemeι) :=
  isInvertible_immersionConormalSheaf (reducedSpecialFibre s C m)

/-- **Stacks Project, Tag 0C67.** The conormal module `𝒞_{D/X}` of the reduced special fibre
`D = Σ (mᵢ/d) Cᵢ` has order dividing `d` in `Pic(D)`: it is the pullback to `D` of
`𝒪_X(-D) = -[𝒪_X(D)]`, and pullback is a homomorphism of Picard groups. -/
@[stacks 0C67 "the conormal class has order dividing d in Pic(D)"]
theorem zsmul_picardClass_immersionConormalSheaf_reducedSpecialFibre
    (hdec : S.specialFiberIdeal = ∏ i ∈ s, C i ^ m i) :
    ((s.gcd m : ℕ) : ℤ) • picardClass (reducedSpecialFibre s C m).subscheme.presheaf
        (structureIsSheaf (reducedSpecialFibre s C m).subscheme.toRingedSpace)
        (Stacks.Thickenings.immersionConormalSheaf (reducedSpecialFibre s C m).subschemeι)
        (isInvertible_immersionConormalSheaf (reducedSpecialFibre s C m)) = 0 := by
  have hpull : ∀ x : ofScheme S.X,
      schemePullbackClass (reducedSpecialFibre s C m).subschemeι x =
        schemePullbackClassHom (reducedSpecialFibre s C m).subschemeι x := fun _ => rfl
  rw [picardClass_immersionConormalSheaf (reducedSpecialFibre s C m),
    negativeTwistPicardClass_eq_neg (reducedSpecialFibre s C m), hpull,
    ← map_zsmul (schemePullbackClassHom (reducedSpecialFibre s C m).subschemeι),
    smul_neg, zsmul_picardClass_reducedSpecialFibre S s C m hdec, neg_zero, map_zero]

/-- **Stacks Project, Tag 0C67.** All four conclusions at once: the reduced special fibre
`D = Σ (mᵢ/d) Cᵢ` of a regular proper model is an effective Cartier divisor, `𝒪_X(D)` has order
dividing `d = gcd(mᵢ)` in `Pic(X)`, and `𝒞_{D/X}` is an invertible `𝒪_D`-module of order
dividing `d` in `Pic(D)`. -/
@[stacks 0C67 "all four conclusions, given a decomposition of X_k rather than a canonical one"]
theorem reducedSpecialFibre_order_dvd_gcd
    (hC : ∀ i ∈ s, IsEffectiveCartierDivisor (C i))
    (hdec : S.specialFiberIdeal = ∏ i ∈ s, C i ^ m i) :
    IsEffectiveCartierDivisor (reducedSpecialFibre s C m) ∧
      ((s.gcd m : ℕ) : ℤ) • picardClass (reducedSpecialFibre s C m) = 0 ∧
      IsInvertible (reducedSpecialFibre s C m).subscheme.presheaf
        (structureIsSheaf (reducedSpecialFibre s C m).subscheme.toRingedSpace)
        (Stacks.Thickenings.immersionConormalSheaf (reducedSpecialFibre s C m).subschemeι) ∧
      ((s.gcd m : ℕ) : ℤ) • picardClass (reducedSpecialFibre s C m).subscheme.presheaf
        (structureIsSheaf (reducedSpecialFibre s C m).subscheme.toRingedSpace)
        (Stacks.Thickenings.immersionConormalSheaf (reducedSpecialFibre s C m).subschemeι)
        (isInvertible_immersionConormalSheaf (reducedSpecialFibre s C m)) = 0 :=
  ⟨isEffectiveCartierDivisor_reducedSpecialFibre s C m hC,
    zsmul_picardClass_reducedSpecialFibre S s C m hdec,
    isInvertible_immersionConormalSheaf_reducedSpecialFibre S s C m,
    zsmul_picardClass_immersionConormalSheaf_reducedSpecialFibre S s C m hdec⟩

/-- **Stacks Project, Tag 0C67**, as a statement about additive orders: the class of `𝒪_X(D)`
in `Pic(X)` has order dividing `d = gcd(mᵢ)`. -/
theorem addOrderOf_picardClass_reducedSpecialFibre_dvd
    (hdec : S.specialFiberIdeal = ∏ i ∈ s, C i ^ m i) :
    addOrderOf (picardClass (reducedSpecialFibre s C m)) ∣ s.gcd m := by
  refine addOrderOf_dvd_iff_nsmul_eq_zero.2 ?_
  rw [← natCast_zsmul]
  exact zsmul_picardClass_reducedSpecialFibre S s C m hdec

/-- **Stacks Project, Tag 0C67**, as a statement about additive orders: the class of `𝒞_{D/X}`
in `Pic(D)` has order dividing `d = gcd(mᵢ)`. -/
theorem addOrderOf_picardClass_immersionConormalSheaf_reducedSpecialFibre_dvd
    (hdec : S.specialFiberIdeal = ∏ i ∈ s, C i ^ m i) :
    addOrderOf (picardClass (reducedSpecialFibre s C m).subscheme.presheaf
        (structureIsSheaf (reducedSpecialFibre s C m).subscheme.toRingedSpace)
        (Stacks.Thickenings.immersionConormalSheaf (reducedSpecialFibre s C m).subschemeι)
        (isInvertible_immersionConormalSheaf (reducedSpecialFibre s C m))) ∣ s.gcd m := by
  refine addOrderOf_dvd_iff_nsmul_eq_zero.2 ?_
  rw [← natCast_zsmul]
  exact zsmul_picardClass_immersionConormalSheaf_reducedSpecialFibre S s C m hdec

end Model

end Stacks.Models

end
