module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardOfDivisor

/-!
# Pushforward of a principal divisor along a dominant proper morphism

In Situation 0EDT let `X/B` and `Y/B` be good, let `X` and `Y` be integral with
`dim_δ(X) = dim_δ(Y) = n`, let `p : X ⟶ Y` be a dominant proper morphism and let
`f ∈ R(X)^*`. Writing `g = Nm_{R(X)/R(Y)}(f)`, **Stacks 0EQ4** is the identity

`p_* div(f) = div(g)` in `Z_{n-1}(Y)`.

This module states that identity in the vocabulary of this chapter — in particular it
constructs the norm `Nm_{R(X)/R(Y)}` of a rational function — and proves its reduction to the
coefficients at the prime divisors of `Y`.

## Main definitions

* `AlgebraicGeometry.Space.rationalFunctionNorm`: the norm `Nm_{R(X)/R(Y)} : R(X) → R(Y)` of a
  rational function along a morphism of integral algebraic spaces carrying the generic point to
  the generic point. This is the `g` of Stacks 0EQ4.

## Main results

* `AlgebraicGeometry.Space.properPushforwardCoeff_principalDivisorCycleCoefficients_eq_zero`: at
  an integral closed subspace of `Y` which is not a prime divisor the coefficient of
  `p_* div(f)` vanishes. This is where `dim_δ(X) = dim_δ(Y)` enters.
* `AlgebraicGeometry.Space.properPushforward_principalDivisorCycle_eq_iff`: **Stacks 0EQ4
  reduced to its coefficients.** The identity `p_* div(f) = div(g)` holds in `Z_{n-1}(Y)` if and
  only if it holds coefficientwise at every prime divisor of `Y`, that is when
  `∑_Z ord_Z(f) · deg(Z/Z') = ord_{Z'}(g)` for every prime divisor `Z' ⊆ Y`.

## Implementation notes

### The norm of a rational function

The function field of an integral good algebraic space is its residue field at the generic
point, by Stacks 0END — `AlgebraicGeometry.Space.rationalFunctionsRingEquiv` — and a morphism
`p : X ⟶ Y` induces a homomorphism of residue fields at a point,
`AlgebraicGeometry.Space.residueFieldHom`. When `p` carries the generic point of `X` to the
generic point of `Y`, which is one of the conclusions of the dominant disjunct of Stacks 0ENY,
these two compose to the extension `R(Y) ⟶ R(X)` of function fields, and
`AlgebraicGeometry.Space.rationalFunctionNorm` is Mathlib's `Algebra.norm` of that extension,
read back through the two identifications. The transport along the equality of points is
`AlgebraicGeometry.Space.residueFieldCongr`.

No finiteness hypothesis is imposed. `Algebra.norm` is `1` on an extension which is not finite
free, exactly as `AlgebraicGeometry.Space.functionFieldDegree` is `0` there, so the definition
makes sense unconditionally; finiteness of `R(X)/R(Y)` under the hypotheses of the source is the
dominant disjunct of Stacks 0ENY, in
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.EqualDeltaDimension`, which is also where the
hypothesis `hgen` below comes from.

### What is proved, and what Stacks 0EQ4 still needs

Proved here: the two sides of `p_* div(f) = div(g)` are coefficient families on the integral
closed subspaces of `Y` which agree away from the prime divisors of `Y`, so the identity is
equivalent to the coefficient identity

`∑_Z ord_Z(f) · deg(Z/Z') = ord_{Z'}(g)`

at every prime divisor `Z' ⊆ Y`, the sum being over the integral closed subspaces `Z ⊆ X`. This
is the same reduction that
`AlgebraicGeometry.Space.properPushforward_divisorCycleOfSection_eq_iff` performs for
Stacks 0EQS, and it is where the hypothesis `dim_δ(X) = dim_δ(Y)` is used: an integral closed
subspace `Z ⊆ X` with a nonzero `div(f)`-coefficient is a prime divisor of `X`, hence has
δ-dimension `n - 1` by Stacks 0EPZ; a nonzero degree forces its image closure to have the same
δ-dimension by Stacks 0EP1, part (1); and `dim_δ(Y) = n` then makes that image closure a prime
divisor of `Y`, again by Stacks 0EPZ.

Not proved here: the coefficient identity itself, which is the whole mathematical content of
Stacks 0EQ4 and is **not** stated as a hypothesis anywhere below — stating it would be assuming
the conclusion. The source's proof of it is étale-local descent of the scheme case: shrink `Y`
so that `p` is finite (Stacks 0AD2), pass to an affine étale neighbourhood of the generic point
of `Z'`, apply the scheme case Stacks 02RT on the components of `V ×_Y X`, and chain the
resulting identities with Stacks 0EPY, Stacks 0EPD, Stacks 0EQ2 and Stacks 0EP2. Of those,
Stacks 0EQ2 and Stacks 0EP2 are absent from this repository; of Stacks 0EPY only the
well-definedness of the right-hand side of its cycle identity is proved — see the
implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackComponents` — and the comparison
statement "a cycle identity on `Y` holds if and only if it holds after étale pullback to `V`"
that step two needs is absent; and Stacks 0AD2 is not on this branch. The scheme case itself
*is* available, as `Stacks.Chow.properPushforward_principalDivisorCycle`.

The final step of the source's proof, the field-theoretic compatibility of the norm with the
decomposition `M ⊗_K L = ∏ Mᵢ`, is the one step for which the source says "we omit the proof".
That step is proved in this repository, as
`Stacks.Norm.norm_baseChange_eq_prod_quotient` of
`StacksFrontier.RingTheory.Norm.BaseChangeProduct`.

The direct route, through the ring-theoretic Stacks 02MJ rather than through the source's
étale-local descent, is blocked for the reasons recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.OrderOfVanishingDomain`: Stacks 02MJ needs the
henselian local rings to be domains, which is not derivable here, and there is no geometric
presentation of `X` over `Y` at the generic point of a prime divisor to apply it to — the
morphism `Spec(𝒪^h_{X,ξ}) ⟶ X` is not constructed, so there is not even an induced homomorphism
`𝒪^h_{Y,ξ'} ⟶ 𝒪^h_{X,ξ}`.

## References

* [Stacks Project, Tag 02MJ](https://stacks.math.columbia.edu/tag/02MJ)
* [Stacks Project, Tag 02RT](https://stacks.math.columbia.edu/tag/02RT)
* [Stacks Project, Tag 0AD2](https://stacks.math.columbia.edu/tag/0AD2)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0END](https://stacks.math.columbia.edu/tag/0END)
* [Stacks Project, Tag 0ENN](https://stacks.math.columbia.edu/tag/0ENN)
* [Stacks Project, Tag 0ENP](https://stacks.math.columbia.edu/tag/0ENP)
* [Stacks Project, Tag 0ENX](https://stacks.math.columbia.edu/tag/0ENX)
* [Stacks Project, Tag 0ENY](https://stacks.math.columbia.edu/tag/0ENY)
* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
* [Stacks Project, Tag 0EP2](https://stacks.math.columbia.edu/tag/0EP2)
* [Stacks Project, Tag 0EPD](https://stacks.math.columbia.edu/tag/0EPD)
* [Stacks Project, Tag 0EPY](https://stacks.math.columbia.edu/tag/0EPY)
* [Stacks Project, Tag 0EPZ](https://stacks.math.columbia.edu/tag/0EPZ)
* [Stacks Project, Tag 0EQ1](https://stacks.math.columbia.edu/tag/0EQ1)
* [Stacks Project, Tag 0EQ2](https://stacks.math.columbia.edu/tag/0EQ2)
* [Stacks Project, Tag 0EQ4](https://stacks.math.columbia.edu/tag/0EQ4)
* [Stacks Project, Tag 0EQS](https://stacks.math.columbia.edu/tag/0EQS)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The norm of a rational function along a morphism -/

section Norm

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The norm `Nm_{R(X)/R(Y)} : R(X) → R(Y)` of a rational function along a morphism
`p : X ⟶ Y` of integral algebraic spaces which carries the generic point of `X` to the generic
point of `Y`. This is the `g = Nm_{R(X)/R(Y)}(f)` of Stacks 0EQ4.

The function field of an integral algebraic space is its residue field at the generic point by
Stacks 0END, and `p` induces a homomorphism of residue fields there, so `R(X)` is an `R(Y)`-
algebra; this is Mathlib's `Algebra.norm` of that algebra, read back through the two
identifications. No finiteness hypothesis is needed: `Algebra.norm` is `1` where the extension
is not finite free, just as `AlgebraicGeometry.Space.functionFieldDegree` is `0` there. -/
def rationalFunctionNorm (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hintX : IsIntegralSpace B S hS X) (hintY : IsIntegralSpace B S hS Y) (p : X ⟶ Y)
    (hgen : pointsMap B S hS X p (genericPoint B S hS hX hintX) =
      genericPoint B S hS hY hintY)
    (f : rationalFunctions B S hS hX) : rationalFunctions B S hS hY :=
  letI := (residueFieldHom B S hS X Y hY hintX.2.1 hintY.2.1 p
    (genericPoint B S hS hX hintX)).toAlgebra
  (rationalFunctionsRingEquiv B S hS hY hintY).symm
    (residueFieldCongr B S hS hintY.2.1 hgen
      (Algebra.norm (residueField B S hS Y hintY.2.1
          (pointsMap B S hS X p (genericPoint B S hS hX hintX)))
        (rationalFunctionsRingEquiv B S hS hX hintX f)))

/-- The extension `R(Y) ⟶ R(X)` of function fields induced by a morphism `p : X ⟶ Y` of
integral algebraic spaces which carries the generic point of `X` to the generic point of `Y`.

The function fields are the residue fields at the generic points by Stacks 0END, and this is the
homomorphism of residue fields that `p` induces there, read through those identifications. It is
the extension whose degree is `[R(X) : R(Y)]` and along which
`AlgebraicGeometry.Space.rationalFunctionNorm` takes the norm. -/
def rationalFunctionMap (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hintX : IsIntegralSpace B S hS X) (hintY : IsIntegralSpace B S hS Y) (p : X ⟶ Y)
    (hgen : pointsMap B S hS X p (genericPoint B S hS hX hintX) =
      genericPoint B S hS hY hintY) :
    rationalFunctions B S hS hY →+* rationalFunctions B S hS hX :=
  (rationalFunctionsRingEquiv B S hS hX hintX).symm.toRingHom.comp
    (((residueFieldHom B S hS X Y hY hintX.2.1 hintY.2.1 p
          (genericPoint B S hS hX hintX)).comp
        (residueFieldCongr B S hS hintY.2.1 hgen).symm.toRingHom).comp
      (rationalFunctionsRingEquiv B S hS hY hintY).toRingHom)

/-- **The norm of a rational function coming from the target is its `[R(X) : R(Y)]`-th power.**
For `g ∈ R(Y)^*` the norm along `p` of the image of `g` in `R(X)` is `g ^ [R(X) : R(Y)]`.

This is the step by which Stacks 0EQ4 gives the degree `[R(X) : R(Y)]` in the first conclusion
of Stacks 0EQS: the rational function attached to `p^*s` is the image of the one attached to
`s`, so its norm is a power. The degree is the parameter `d`, pinned by `hd` as the rank of the
extension of residue fields at the generic point of `X`, so that the statement does not depend
on how that degree is spelled; `Mathlib`'s `Algebra.norm_algebraMap` needs no finiteness
hypothesis, both sides being trivial when the extension is not finite free. -/
theorem rationalFunctionNorm_rationalFunctionMap (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hintX : IsIntegralSpace B S hS X)
    (hintY : IsIntegralSpace B S hS Y) (p : X ⟶ Y)
    (hgen : pointsMap B S hS X p (genericPoint B S hS hX hintX) =
      genericPoint B S hS hY hintY) (d : ℕ)
    (hd : letI := (residueFieldHom B S hS X Y hY hintX.2.1 hintY.2.1 p
        (genericPoint B S hS hX hintX)).toAlgebra
      Module.finrank (residueField B S hS Y hintY.2.1
          (pointsMap B S hS X p (genericPoint B S hS hX hintX)))
        (residueField B S hS X hintX.2.1 (genericPoint B S hS hX hintX)) = d)
    (g : rationalFunctions B S hS hY) :
    rationalFunctionNorm B S hS hX hY hintX hintY p hgen
        (rationalFunctionMap B S hS hX hY hintX hintY p hgen g) = g ^ d := by
  let : Algebra (residueField B S hS Y hintY.2.1
      (pointsMap B S hS X p (genericPoint B S hS hX hintX)))
      (residueField B S hS X hintX.2.1 (genericPoint B S hS hX hintX)) :=
    (residueFieldHom B S hS X Y hY hintX.2.1 hintY.2.1 p
      (genericPoint B S hS hX hintX)).toAlgebra
  subst hd
  set eX := rationalFunctionsRingEquiv B S hS hX hintX
  set eY := rationalFunctionsRingEquiv B S hS hY hintY
  set c := residueFieldCongr B S hS hintY.2.1 hgen
  have key : ∀ y : residueField B S hS Y hintY.2.1
      (pointsMap B S hS X p (genericPoint B S hS hX hintX)),
      Algebra.norm _ (residueFieldHom B S hS X Y hY hintX.2.1 hintY.2.1 p
          (genericPoint B S hS hX hintX) y) =
        y ^ Module.finrank (residueField B S hS Y hintY.2.1
          (pointsMap B S hS X p (genericPoint B S hS hX hintX)))
          (residueField B S hS X hintX.2.1 (genericPoint B S hS hX hintX)) :=
    fun y => Algebra.norm_algebraMap y
  change eY.symm (c (Algebra.norm _ (eX (eX.symm (residueFieldHom B S hS X Y hY hintX.2.1
    hintY.2.1 p (genericPoint B S hS hX hintX) (c.symm (eY g))))))) = g ^ _
  rw [eX.apply_symm_apply, key, map_pow, c.apply_symm_apply, ← map_pow, eY.symm_apply_apply]

end Norm

/-! ### The degree `[R(X) : R(Y)]` as a rank of residue fields -/

section Degree

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)

/-- The degree of Stacks 0EP1, part (1), at an integral closed subspace whose ambient generic
point is `ξ` is the rank of the extension of residue fields at `ξ`. This is the definition of
`AlgebraicGeometry.Space.functionFieldDegree` with the generic point named. -/
theorem functionFieldDegree_eq_finrank_of_ambientGenericPoint_eq (p : X ⟶ Y)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    {ξ : points D.site D.base D.base_mem X}
    (hξ : Z.ambientGenericPoint D.site D.base D.base_mem = ξ) :
    functionFieldDegree D sX hX sY hY p Z =
      letI := (residueFieldHom D.site D.base D.base_mem X Y hY.1
        (D.isDecentSpace_of_isGood sX hX) (D.isDecentSpace_of_isGood sY hY) p ξ).toAlgebra
      Module.finrank (residueField D.site D.base D.base_mem Y
          (D.isDecentSpace_of_isGood sY hY) (pointsMap D.site D.base D.base_mem X p ξ))
        (residueField D.site D.base D.base_mem X (D.isDecentSpace_of_isGood sX hX) ξ) := by
  subst hξ
  rfl

/-- **The degree `[R(X) : R(Y)]` is the rank of the extension of residue fields at the generic
point of `X`.** This identifies the degree that Stacks 0EP1 and Stacks 0EQS use,
`AlgebraicGeometry.Space.functionFieldDegreeAtGenericPoint`, with the rank appearing in
`AlgebraicGeometry.Space.rationalFunctionNorm_rationalFunctionMap`, so that the exponent there
is the development's own `[R(X) : R(Y)]` and not a second spelling of it. -/
theorem functionFieldDegreeAtGenericPoint_eq_finrank
    (hintX : IsIntegralSpace D.site D.base D.base_mem X) (p : X ⟶ Y) :
    functionFieldDegreeAtGenericPoint D sX hX sY hY hintX p =
      letI := (residueFieldHom D.site D.base D.base_mem X Y hY.1
        (D.isDecentSpace_of_isGood sX hX) (D.isDecentSpace_of_isGood sY hY) p
        (genericPoint D.site D.base D.base_mem hX.1 hintX)).toAlgebra
      Module.finrank (residueField D.site D.base D.base_mem Y
          (D.isDecentSpace_of_isGood sY hY) (pointsMap D.site D.base D.base_mem X p
            (genericPoint D.site D.base D.base_mem hX.1 hintX)))
        (residueField D.site D.base D.base_mem X (D.isDecentSpace_of_isGood sX hX)
          (genericPoint D.site D.base D.base_mem hX.1 hintX)) :=
  functionFieldDegree_eq_finrank_of_ambientGenericPoint_eq D sX hX sY hY p _
    (pointsMap_genericPoint_integralClosedSubspaceOfPoint D.site D.base D.base_mem hX.1
      (D.isDecentSpace_of_isGood sX hX) (genericPoint D.site D.base D.base_mem hX.1 hintX))

end Degree

/-! ### Away from the prime divisors of the target -/

section Reduction

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (hdecX : IsDecentSpace D.site D.base D.base_mem X)

variable [∀ W : PrimeDivisor D.site D.base D.base_mem X,
    Nontrivial ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdecX)]
  [∀ W : PrimeDivisor D.site D.base D.base_mem X,
    IsNoetherianRing ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdecX)]
  [∀ W : PrimeDivisor D.site D.base D.base_mem X,
    Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdecX)]

variable (embX : ∀ W : PrimeDivisor D.site D.base D.base_mem X,
    rationalFunctions D.site D.base D.base_mem hX.1 →+*
      W.genericTotalFractionRing D.site D.base D.base_mem hX.1 hdecX)
  (f : rationalFunctions D.site D.base D.base_mem hX.1)
  (hf : ∀ W : PrimeDivisor D.site D.base D.base_mem X, IsUnit (embX W f))

/-- **The content of the reduction of Stacks 0EQ4.** At an integral closed subspace `Z' ⊆ Y`
which is not a prime divisor the coefficient of `p_* div(f)` is zero.

An integral closed subspace `Z ⊆ X` contributing to that coefficient has a nonzero
`div(f)`-coefficient, hence is a prime divisor of `X` and so has δ-dimension `n - 1` by
Stacks 0EPZ, and has a nonzero degree, which forces its image closure `Z'` to have the same
δ-dimension by Stacks 0EP1, part (1). Since `dim_δ(Y) = n` as well, Stacks 0EPZ on `Y` makes
`Z'` a prime divisor of `Y`. -/
theorem properPushforwardCoeff_principalDivisorCycleCoefficients_eq_zero
    (hintX : IsIntegralSpace D.site D.base D.base_mem X)
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y)
    (dX : DimensionFunction (points D.site D.base D.base_mem X))
    (hdX : ∀ x, dX x = D.deltaValue sX x)
    (dY : DimensionFunction (points D.site D.base D.base_mem Y))
    (hdY : ∀ y, dY y = D.deltaValue sY y) {n : ℤ}
    (hnX : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (hnY : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (n : EInt)) (p : X ⟶ Y)
    {Z' : IntegralClosedSubspace D.site D.base D.base_mem Y}
    (hZ' : codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hY.1 Z') ≠ 1) :
    properCyclePushforwardCoeff D sX hX sY hY p
      (principalDivisorCycleCoefficients D sX hX hdecX embX f hf) Z' = 0 := by
  refine finsum_eq_zero_of_forall_eq_zero fun Z => ?_
  by_cases hα : principalDivisorCycleCoefficients D sX hX hdecX embX f hf Z = 0
  · rw [hα, zero_mul]
  by_cases hm : properCycleMult D sX hX sY hY p Z Z' = 0
  · rw [hm, mul_zero]
  obtain ⟨him, hdeg⟩ := (properCycleMult_ne_zero_iff D sX hX sY hY p Z Z').1 hm
  have hcodX :
      codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hX.1 Z) = 1 :=
    of_not_not fun hc =>
      hα (principalDivisorCycleCoefficients_of_codimension_ne_one D sX hX hdecX embX f hf hc)
  have hδX : deltaDimension D sX Z = n - 1 :=
    ((isPrimeDivisor_tfae_of_isIntegralSpace D sX hX hintX dX hdX hnX Z).out 2 3).mp hcodX
  have hδY := deltaDimension_closureImage_of_properCycleDegree_ne_zero D sX hX sY hY p hdeg
  rw [him, hδX] at hδY
  exact (hZ' (((isPrimeDivisor_tfae_of_isIntegralSpace D sY hY hintY dY hdY hnY Z').out 3 2).mp
    hδY)).elim

end Reduction

/-! ### Stacks 0EQ4 reduced to its coefficients -/

section Identity

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (hdecX : IsDecentSpace D.site D.base D.base_mem X)
    (hdecY : IsDecentSpace D.site D.base D.base_mem Y)

variable [∀ W : PrimeDivisor D.site D.base D.base_mem X,
    Nontrivial ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdecX)]
  [∀ W : PrimeDivisor D.site D.base D.base_mem X,
    IsNoetherianRing ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdecX)]
  [∀ W : PrimeDivisor D.site D.base D.base_mem X,
    Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdecX)]
  [∀ W : PrimeDivisor D.site D.base D.base_mem Y,
    Nontrivial ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hY.1 hdecY)]
  [∀ W : PrimeDivisor D.site D.base D.base_mem Y,
    IsNoetherianRing ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hY.1 hdecY)]
  [∀ W : PrimeDivisor D.site D.base D.base_mem Y,
    Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hY.1 hdecY)]

variable (embX : ∀ W : PrimeDivisor D.site D.base D.base_mem X,
    rationalFunctions D.site D.base D.base_mem hX.1 →+*
      W.genericTotalFractionRing D.site D.base D.base_mem hX.1 hdecX)
  (f : rationalFunctions D.site D.base D.base_mem hX.1)
  (hf : ∀ W : PrimeDivisor D.site D.base D.base_mem X, IsUnit (embX W f))
  (embY : ∀ W : PrimeDivisor D.site D.base D.base_mem Y,
    rationalFunctions D.site D.base D.base_mem hY.1 →+*
      W.genericTotalFractionRing D.site D.base D.base_mem hY.1 hdecY)
  (g : rationalFunctions D.site D.base D.base_mem hY.1)
  (hg : ∀ W : PrimeDivisor D.site D.base D.base_mem Y, IsUnit (embY W g))

variable (hintX : IsIntegralSpace D.site D.base D.base_mem X)
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y)
    (dX : DimensionFunction (points D.site D.base D.base_mem X))
    (hdX : ∀ x, dX x = D.deltaValue sX x)
    (dY : DimensionFunction (points D.site D.base D.base_mem Y))
    (hdY : ∀ y, dY y = D.deltaValue sY y) {n : ℤ}
    (hnX : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (hnY : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (n : EInt))

/-- **Stacks 0EQ4, reduced to its coefficients at the prime divisors of `Y`.** In Situation
0EDT let `X/B` and `Y/B` be good, let `p : X ⟶ Y` be quasi-compact over `B`, let `X` and `Y` be
integral with `dim_δ(X) = dim_δ(Y) = n`, and let `f ∈ R(X)^*` and `g ∈ R(Y)^*`. Then

`p_* div(f) = div(g)` in `Z_{n-1}(Y)`

holds exactly when it holds coefficientwise at every prime divisor of `Y`, that is when

`∑_Z ord_Z(f) · deg(Z/Z') = ord_{Z'}(g)`

for every prime divisor `Z' ⊆ Y`, the sum being over the integral closed subspaces `Z ⊆ X`.

Both sides are coefficient families on the integral closed subspaces of `Y`, and away from the
prime divisors of `Y` both vanish: the coefficient of `div(g)` at an integral closed subspace
whose point set does not have codimension one is zero by Stacks 0ENP, and the pushforward has no
contribution there by
`AlgebraicGeometry.Space.properPushforwardCoeff_principalDivisorCycleCoefficients_eq_zero`,
which is where the equality of the δ-dimensions is used. That is the whole content of the
reduction; the coefficient identity at a prime divisor of `Y` — which is the mathematical
content of Stacks 0EQ4 — is *not* proved here, and is not assumed either. Taking
`g = Nm_{R(X)/R(Y)}(f)`, that is
`AlgebraicGeometry.Space.rationalFunctionNorm D.site D.base D.base_mem … p hgen f`, gives the
source's statement. -/
@[stacks 0EQ4 "REDUCED, not proved: p_*div(f) = div(g) in Z_{n-1}(Y) IF AND ONLY IF it holds at
every prime divisor of Y; proved away from them, using dim_δ(X) = dim_δ(Y). Take g to be
rationalFunctionNorm, the norm Nm_{R(X)/R(Y)} constructed here, for the source's statement"]
theorem properPushforward_principalDivisorCycle_eq_iff
    (hfinX : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem X =>
      if principalDivisorCoefficients D.site D.base D.base_mem hX.1 hdecX embX f hf W = 0 then ∅
      else W.support D.site D.base D.base_mem X)
    (hfinY : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem Y =>
      if principalDivisorCoefficients D.site D.base D.base_mem hY.1 hdecY embY g hg W = 0 then ∅
      else W.support D.site D.base D.base_mem Y)
    {p : X ⟶ Y} (hpB : p ≫ sY = sX) (hp : IsQuasiCompact D.site D.base D.base_mem p) :
    properCyclePushforward D sX hX sY hY hpB hp (n - 1)
          (principalDivisorCycle D sX hX hdecX embX f hf hfinX hintX dX hdX hnX) =
        principalDivisorCycle D sY hY hdecY embY g hg hfinY hintY dY hdY hnY ↔
      ∀ W : PrimeDivisor D.site D.base D.base_mem Y,
        (∑ᶠ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
            principalDivisorCycleCoefficients D sX hX hdecX embX f hf Z *
              properCycleMult D sX hX sY hY p Z
                (W.toIntegralClosedSubspace D.site D.base D.base_mem)) =
          principalDivisorCoefficients D.site D.base D.base_mem hY.1 hdecY embY g hg W := by
  rw [Subtype.ext_iff, funext_iff]
  simp only [properPushforward_apply, principalDivisorCycle_coe]
  refine ⟨fun h W => ?_, fun hW Z' => ?_⟩
  · have h := h (W.toIntegralClosedSubspace D.site D.base D.base_mem)
    rwa [principalDivisorCycleCoefficients_toIntegralClosedSubspace] at h
  · by_cases hcod :
        codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hY.1 Z') = 1
    · have h := hW (Z'.toPrimeDivisor D.site D.base D.base_mem hY.1 hcod)
      rw [IntegralClosedSubspace.toIntegralClosedSubspace_toPrimeDivisor] at h
      rw [h, show principalDivisorCycleCoefficients D sY hY hdecY embY g hg Z' =
        principalDivisorCoefficients D.site D.base D.base_mem hY.1 hdecY embY g hg
          (Z'.toPrimeDivisor D.site D.base D.base_mem hY.1 hcod) from dite_eq_left hcod]
    · rw [principalDivisorCycleCoefficients_of_codimension_ne_one D sY hY hdecY embY g hg hcod,
        ← properCyclePushforwardCoeff]
      exact properPushforwardCoeff_principalDivisorCycleCoefficients_eq_zero D sX hX sY hY hdecX
        embX f hf hintX hintY dX hdX dY hdY hnX hnY p hcod

end Identity

end AlgebraicGeometry.Space

end
