module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectFromFibresCharts
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology

/-!
# Relative perfectness from boundedness below of the derived fibres

Let `f : X ⟶ S` be flat and locally of finite presentation and let `E` be a pseudo-coherent object
of `D(𝒪_X)`. If `E` is locally bounded below and, for every point `s` of `S`, the derived
restriction `L(X_s ⟶ X)^*E` of `E` to the scheme-theoretic fibre is locally bounded below, then
`E` is `S`-perfect. This is the implication (2) ⟹ (1) of Stacks 0GEH; the converse implication is
`AlgebraicGeometry.isLocallyBoundedBelow_of_isPerfectRelativeTo` and
`AlgebraicGeometry.isLocallyBoundedBelow_derivedPullback_fibre_of_hasTorAmplitudeOver`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isRelativelyPerfect_of_isLocallyBoundedBelow_of_fibres`:
  **Stacks 0GEH, (2) ⟹ (1).**

## Implementation notes

The proof is the source's. The cohomology of a pseudo-coherent object is quasi-coherent
(Stacks 08E5). Everything is local, so by Stacks 0DI2 it suffices to show that `RΓ(U, E)` is
`Γ(S, V)`-perfect on every affine chart `U ⊆ f⁻¹(V)`, and by the ring-level criterion Stacks 0GHJ
that reduces to boundedness below of `RΓ(U, E)` and of its derived fibres — this composition is
`AlgebraicGeometry.Scheme.Hom.isRelativelyPerfect_of_forall_chart_isBoundedBelow_and_fibres`. The
two chart conditions come from condition (2) by
`AlgebraicGeometry.exists_isGE_derivedSections_of_isLocallyBoundedBelow` and
`AlgebraicGeometry.exists_isGE_derivedFibre_derivedSections`, the latter being the affine case of
Stacks 08IB for the flat morphism `f`.

## References

* [Stacks Project, Lemma 36.35.13 (Tag 0GEH)](https://stacks.math.columbia.edu/tag/0GEH)
* [Stacks Project, Lemma 36.35.3 (Tag 0DI2)](https://stacks.math.columbia.edu/tag/0DI2)
* [Stacks Project, Lemma 15.85.10 (Tag 0GHJ)](https://stacks.math.columbia.edu/tag/0GHJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Stacks 0GEH, condition (2) implies condition (1).** Let `f : X ⟶ S` be flat and locally of
finite presentation and let `E` be a pseudo-coherent object of `D(𝒪_X)`. If `E` is locally
bounded below and for every point `s` of `S` the derived pullback `L(X_s ⟶ X)^*E` of `E` to the
fibre `X_s = X ×_S Spec κ(s)` is locally bounded below, then `E` is `S`-perfect. -/
@[stacks 0GEH "condition (2) implies condition (1): for f flat and locally of finite \
presentation and E pseudo-coherent, if E is locally bounded below and every derived fibre \
L(X_s ⟶ X)^*E is locally bounded below, then E is S-perfect"]
public theorem isRelativelyPerfect_of_isLocallyBoundedBelow_of_fibres
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (E : DerivedCategory X.Modules)
    (hpc : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E)
    (hE : RingedSpace.IsLocallyBoundedBelow X.toRingedSpace E)
    (hfib : ∀ s : S, RingedSpace.IsLocallyBoundedBelow
      (Limits.pullback f (S.fromSpecResidueField s)).toRingedSpace
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (Limits.pullback.fst f (S.fromSpecResidueField s)).toLRSHom.toShHom).obj E)) :
    f.IsRelativelyPerfect E := by
  have hqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent :=
    isQuasicoherentDerived_of_isPseudoCoherent X E hpc
  exact isRelativelyPerfect_of_forall_chart_isBoundedBelow_and_fibres f E hqc hpc
    fun U hU V hV e => ⟨exists_isGE_derivedSections_of_isLocallyBoundedBelow E hqc hE hU,
      fun p => exists_isGE_derivedFibre_derivedSections f E hqc hfib hU hV e p⟩

end AlgebraicGeometry.Scheme.Hom
