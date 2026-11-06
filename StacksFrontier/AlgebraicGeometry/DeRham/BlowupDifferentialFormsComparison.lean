module

public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialForms
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorCanonicalSection
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalCartier
public import StacksFrontier.AlgebraicGeometry.DivisorSum.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CoordinateBlowupSmooth
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.Blowup.CartierCentre

/-!
# Differential forms on the blowup of a coordinate subspace

Fix a ring `R`, put `S = Spec(R)`, and fix `0 ≤ m` and `1 ≤ n`. Let

`Z = 𝐀^m_S ⟶ 𝐀^{m+n}_S = X`

be the coordinate closed immersion, let `b : L ⟶ X` be the blowing up of `X` along `Z` and let
`E ⊆ L` be its exceptional divisor. This file sets up that situation in the vocabulary of the
library and records the first of the two canonical maps on differential forms attached to it,

`b^*Ω^a_{X/S} ⟶ Ω^a_{L/S}`,

which is the canonical map of a commutative square of schemes.

## Main definitions

* `Stacks.DeRham.coordinateAmbient`, `Stacks.DeRham.coordinateAmbientToBase`: the affine space
  `X = 𝐀^{m+n}_S = Spec R[x₁, …, x_m, y₁, …, y_n]` and its structure morphism to `S`.
* `Stacks.DeRham.coordinateBlowup`, `Stacks.DeRham.coordinateBlowupToAmbient`: the blowup `L` of
  `X` along the coordinate subspace and the blowing-up morphism `b : L ⟶ X`.
* `Stacks.DeRham.coordinateBlowupToBase`: the structure morphism `L ⟶ S`.
* `Stacks.DeRham.coordinateExceptional`: the exceptional divisor `E ⊆ L`, as an ideal sheaf.
* `Stacks.DeRham.blowupFormsPullbackMap`: the first canonical map `b^*Ω^a_{X/S} ⟶ Ω^a_{L/S}`.
* `Stacks.DeRham.blowupFormsExceptionalTwist`: the twisted module
  `b^*Ω^a_{X/S} ⊗_{𝒪_L} 𝒪_L((n-1)E)`, the target of the second canonical map.
* `Stacks.DeRham.blowupFormsCanonicalSection`: the map
  `b^*Ω^a_{X/S} ⟶ b^*Ω^a_{X/S} ⊗_{𝒪_L} 𝒪_L((n-1)E)` induced by the inclusion
  `𝒪_L ⊆ 𝒪_L((n-1)E)`, the composite the two canonical maps have to produce.

## Main results

* `Stacks.DeRham.coordinateSection_mem_nonZeroDivisors`: each of the last `n` coordinates is a
  nonzerodivisor on `X`.
* `Stacks.DeRham.isEffectiveCartierDivisor_coordinateIdeal_one`: for `n = 1` the centre
  `Z ⊆ X` is an effective Cartier divisor.
* `Stacks.DeRham.isIso_coordinateBlowupToAmbient_one`: for `n = 1` the blowing-up morphism
  `b : L ⟶ X` is an isomorphism. This is the case `n = 1` that the source's calculations in this
  situation dispose of separately.

## Implementation notes

The source works with the graded ring `A = R[x₁, …, x_m, y₁, …, y_n]`, `deg xᵢ = 0`,
`deg yⱼ = 1`, and the ideal `A₊` cutting out `Z`; `Stacks.MoreMorphisms.coordinateIdeal` is that
ideal as an ideal sheaf on `X = Spec(A)`, obtained as the kernel of the coordinate projection
`A ⟶ R[x₁, …, x_m]`. The blowup is then `AlgebraicGeometry.blowUp` of that ideal sheaf, the
relative `Proj` of its Rees algebra, which is how the source presents `L`.

The divisor `(n-1)E` is the `(n-1)`-st power of the exceptional ideal sheaf — powers of ideal
sheaves are multiplication in `AlgebraicGeometry.Scheme.IdealSheafData`, and the `(n-1)`-st
power of an effective Cartier divisor is the divisor `(n-1)E`.

The degree of a form is an integer, as in `relativeDifferentialForms`, while the source's `a` is
a natural number; the statements below are indexed by a natural number cast into `ℤ`, so that
`a ≥ 0` is automatic.

## References

* [Stacks Project, Tag 0G5G](https://stacks.math.columbia.edu/tag/0G5G)
* [Stacks Project, Tag 0FUA](https://stacks.math.columbia.edu/tag/0FUA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.DeRham

variable (R : Type u) [CommRing R] (m n : ℕ)

/-- The base scheme `S = Spec(R)` of the standard coordinate blowup. -/
abbrev coordinateBase : Scheme.{u} := Spec (.of R)

/-- The ambient affine space `X = 𝐀^{m+n}_S = Spec R[x₁, …, x_m, y₁, …, y_n]`. -/
abbrev coordinateAmbient : Scheme.{u} := Spec (.of (MvPolynomial (Fin m ⊕ Fin n) R))

/-- The structure morphism `X ⟶ S` of the ambient affine space. -/
noncomputable abbrev coordinateAmbientToBase :
    coordinateAmbient R m n ⟶ coordinateBase R :=
  Spec.map (CommRingCat.ofHom
    (MvPolynomial.C : R →+* MvPolynomial (Fin m ⊕ Fin n) R))

/-- The blowup `L` of `X = 𝐀^{m+n}_S` along the coordinate subspace `Z = 𝐀^m_S`. -/
noncomputable abbrev coordinateBlowup : Scheme.{u} :=
  blowUp (Stacks.MoreMorphisms.coordinateIdeal R m n)

/-- The blowing-up morphism `b : L ⟶ X`. -/
noncomputable abbrev coordinateBlowupToAmbient :
    coordinateBlowup R m n ⟶ coordinateAmbient R m n :=
  blowUpToBase (Stacks.MoreMorphisms.coordinateIdeal R m n)

/-- The structure morphism `L ⟶ S` of the blowup. -/
noncomputable abbrev coordinateBlowupToBase : coordinateBlowup R m n ⟶ coordinateBase R :=
  coordinateBlowupToAmbient R m n ≫ coordinateAmbientToBase R m n

/-- The exceptional divisor `E ⊆ L` of the coordinate blowup, as an ideal sheaf. -/
noncomputable abbrev coordinateExceptional : (coordinateBlowup R m n).IdealSheafData :=
  exceptionalIdeal (Stacks.MoreMorphisms.coordinateIdeal R m n)

/-- **Stacks Project, Tag 0G5G, the first canonical map.** The canonical map
`b^*Ω^a_{X/S} ⟶ Ω^a_{L/S}` of the commutative square

```
L → X
↓   ↓
S = S
```

attached to the coordinate blowup; this is the general construction of
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsMap`, that is, of Section 50.2 of the
source.

This is the **first** of the two canonical maps asserted by Stacks 0G5G, in that tag's own
Situation: `coordinateAmbient` is the tag's `X`, `coordinateBlowup` is the tag's global `L`,
and the affine blowup charts `A[I/yᵢ]` enter only in the proof of the second map. The second
map and the identification of the composite are not available yet, so only this clause of the
tag is claimed here. -/
@[stacks 0G5G "the first canonical map b^*Ω^a_{X/S} ⟶ Ω^a_{L/S}"]
noncomputable def blowupFormsPullbackMap (a : ℕ) :
    (Scheme.Modules.pullback (coordinateBlowupToAmbient R m n)).obj
        (Scheme.Hom.relativeDifferentialForms (coordinateAmbientToBase R m n) a) ⟶
      Scheme.Hom.relativeDifferentialForms (coordinateBlowupToBase R m n) a :=
  Scheme.Hom.relativeDifferentialFormsMap (coordinateBlowupToAmbient R m n)
    (coordinateAmbientToBase R m n) (coordinateBlowupToBase R m n)
    (𝟙 (coordinateBase R)) (by simp) a

/-- The exceptional divisor of the coordinate blowup is an effective Cartier divisor, hence so
is its `(n-1)`-st power `(n-1)E`; this is what makes `𝒪_L((n-1)E)` invertible. -/
instance isEffectiveCartierDivisor_coordinateExceptional :
    Stacks.Divisors.IsEffectiveCartierDivisor (coordinateExceptional R m n) :=
  Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal _

/-- **The `k`-fold exceptional divisor `kE` is an effective Cartier divisor**, so `𝒪_L(kE)` is
invertible. Powers of an effective Cartier divisor are effective Cartier
([Stacks, Tag 01WU] and the remark following Tag 01WT). -/
instance isEffectiveCartierDivisor_coordinateExceptional_pow (k : ℕ) :
    Stacks.Divisors.IsEffectiveCartierDivisor (coordinateExceptional R m n ^ k) :=
  Stacks.Divisors.isEffectiveCartierDivisor_pow
    (isEffectiveCartierDivisor_coordinateExceptional R m n) k

/-- The twist `b^*Ω^a_{X/S} ⊗_{𝒪_L} 𝒪_L((n-1)E)` of the pulled-back forms by the
`(n-1)`-fold exceptional divisor. -/
noncomputable abbrev blowupFormsExceptionalTwist (a : ℕ) : (coordinateBlowup R m n).Modules :=
  Scheme.Modules.tensorObj
    ((Scheme.Modules.pullback (coordinateBlowupToAmbient R m n)).obj
      (Scheme.Hom.relativeDifferentialForms (coordinateAmbientToBase R m n) a))
    (Stacks.Divisors.invertibleSheaf' (coordinateExceptional R m n ^ (n - 1)))

/-- The map `b^*Ω^a_{X/S} ⟶ b^*Ω^a_{X/S} ⊗_{𝒪_L} 𝒪_L((n-1)E)` induced by the inclusion
`𝒪_L ⊆ 𝒪_L((n-1)E)`: multiplication by the canonical section of `𝒪_L((n-1)E)`. This is the
composite that the two canonical maps of [Stacks, Tag 0G5G] have to produce. -/
noncomputable abbrev blowupFormsCanonicalSection (a : ℕ) :
    (Scheme.Modules.pullback (coordinateBlowupToAmbient R m n)).obj
        (Scheme.Hom.relativeDifferentialForms (coordinateAmbientToBase R m n) a) ⟶
      blowupFormsExceptionalTwist R m n a :=
  Stacks.Divisors.tensorCanonicalSection (coordinateExceptional R m n ^ (n - 1)) _

/-! ### The case `n = 1` -/

section OneCoordinate

open MvPolynomial Stacks.MoreMorphisms

/-- The `i`-th of the last `n` coordinates is a nonzerodivisor in the ring of global functions of
affine `(m + n)`-space: multiplying by it shifts the exponent of `yᵢ` in every monomial, so it is
injective on coefficients, and the global functions are the polynomial ring. -/
theorem coordinateSection_mem_nonZeroDivisors (i : Fin n) :
    coordinateSection R m n i ∈ nonZeroDivisors Γ(coordinateAmbient R m n, ⊤) := by
  rw [mem_nonZeroDivisors_iff_left]
  intro z hz
  have h0 : (X (Sum.inr i) : MvPolynomial (Fin m ⊕ Fin n) R) * (gammaEquiv R m n).symm z = 0 := by
    simpa using congrArg (gammaEquiv R m n).symm hz
  have h1 : (gammaEquiv R m n).symm z = 0 := by
    refine MvPolynomial.ext _ _ fun d => ?_
    have h := congrArg (fun p : MvPolynomial (Fin m ⊕ Fin n) R =>
      p.coeff (Finsupp.single (Sum.inr i) 1 + d)) h0
    simp only [MvPolynomial.coeff_X_mul, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h
    rw [h, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  simpa using congrArg (gammaEquiv R m n) h1

/-- **For `n = 1` the centre of the blowup is an effective Cartier divisor.** The coordinate
subspace `Z = 𝐀^m_S ⊆ 𝐀^{m+1}_S = X` is cut out on the whole of the affine scheme `X` by the
single coordinate `y₁`, which is a nonzerodivisor. -/
theorem isEffectiveCartierDivisor_coordinateIdeal_one :
    Stacks.Divisors.IsEffectiveCartierDivisor (coordinateIdeal R m 1) := by
  refine Stacks.Divisors.isEffectiveCartierDivisor_of_forall_exists_affineOpen _ fun x =>
    ⟨⊤, isAffineOpen_top _, trivial, coordinateSection R m 1 0,
      isRegular_iff_mem_nonZeroDivisors.2 (coordinateSection_mem_nonZeroDivisors R m 1 0), ?_⟩
  rw [coordinateIdeal_ideal_top, coordinateRingIdeal, Ideal.map_span]
  congr 1
  rw [Set.range_unique, Set.image_singleton]
  rfl

/-- **For `n = 1` the blowing-up morphism `b : L ⟶ X` is an isomorphism.** This is the case
`n = 1` of the source's calculations: the centre is then an effective Cartier divisor, and
blowing up an effective Cartier divisor changes nothing ([Stacks, Tag 0807]). -/
instance isIso_coordinateBlowupToAmbient_one : IsIso (coordinateBlowupToAmbient R m 1) :=
  Stacks.Blowup.isIso_blowUpToBase_of_isEffectiveCartierDivisor _
    (isEffectiveCartierDivisor_coordinateIdeal_one R m)

end OneCoordinate

end Stacks.DeRham

end
