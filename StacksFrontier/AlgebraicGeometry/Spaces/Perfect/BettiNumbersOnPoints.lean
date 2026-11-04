module

public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreBettiBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ConstructiblePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique

/-!
# Betti-number functions on the points of an algebraic space

A function `β : |X| → ℕ` on the points of a presheaf `X` on the big fppf site of `S` is an
`i`-th *Betti-number function* when on every étale chart `φ : h_U → X` from an object of the
site it agrees, under the homeomorphism `|h_U| ≅ U` of Stacks 03BX, with the `i`-th
derived-fibre Betti function of a pseudo-coherent complex on the scheme `U`. Every level set
of such a `β` is étale locally constructible, and `β` is upper semicontinuous.

## Main definitions

* `AlgebraicGeometry.Space.IsEtaleLocallyDerivedFibreBetti` is the property above.

## Main results

* `AlgebraicGeometry.Space.isEtaleLocallyConstructible_setOf_eq`: the level sets of an `i`-th
  Betti-number function are étale locally constructible.
* `AlgebraicGeometry.Space.upperSemicontinuous_of_isEtaleLocallyDerivedFibreBetti`: an `i`-th
  Betti-number function is upper semicontinuous.

## Implementation notes

*Why `β` is data.* Not because it cannot be built. The Betti-number function of a
pseudo-coherent object of the derived category of modules on the small étale site of `X` is
`AlgebraicGeometry.Space.geometricFibreBettiFunction`, its Betti number at a geometric
representative of the point, and clause (1) of Stacks 0D1Y holds for it
(`AlgebraicGeometry.Space.geometricFibreBettiFunction_derivedPullback`). What is missing is the
*comparison*: no declaration identifies that function, on a scheme chart, with the
derived-fibre Betti function of a complex on the chart, which is what
`IsEtaleLocallyDerivedFibreBetti` below demands. So `β` is taken as data together with that
property, and the two results below are the clauses of Stacks 0D1Y for such a `β`.

Clause (2) of Stacks 03OJ is
available: it is clause (2) of Stacks 03DX at `τ = étale`, proved unconditionally as
`AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule` and
`AlgebraicGeometry.SmallEtale.isEquivalence_associatedModuleQcohOnSite'`.

*What the comparison still needs.* The route is assembled but for its last step. A chart
`φ : h_U ⟶ X` carries a pseudo-coherent `E` to a pseudo-coherent `Lφ^*E` on the small étale
site of `h_U`, which `AlgebraicGeometry.Space.representedSmallEtaleEquivalence` reads on the
small étale site of the scheme `U`; the cohomology of that object is quasi-coherent by
Stacks 08JL (`AlgebraicGeometry.Space.derivedCategoryB_of_isPseudoCoherent_unconditional`), so
Stacks 071Q (`AlgebraicGeometry.SmallEtale.derivedAssociatedModule_isEquivalence`, for every
scheme) yields a complex on `U` of which it is the associated étale complex, and Stacks 08HE,
clause (2) ⇒ (1) (`AlgebraicGeometry.SmallEtale.associatedModuleToPseudoCoherent`) makes that
complex pseudo-coherent. The step with nothing to supply it is the agreement of the two Betti
numbers at corresponding points: the étale-site dimension of
`AlgebraicGeometry.Space.geometricFibreBetti_eq_finrank_idChart` against the residue-field
dimension of `AlgebraicGeometry.DerivedFibreOverField.derivedFiberBetti_specField`.

*The cited hypotheses.* Both results reduce to the corresponding statement for the
derived-fibre Betti function of a pseudo-coherent complex on a scheme, which is parts (2) and
(3) of Stacks 0BDI. Those parts are proved for an arbitrary scheme under pseudo-coherence
alone — `AlgebraicGeometry.DerivedFibreBetti.upperSemicontinuous_derivedFiberBetti` and
`AlgebraicGeometry.DerivedFibreBetti.isLocallyConstructible_derivedFiberBetti_preimage` — and
are fed to the two results below in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/BettiNumbersOnPointsUnconditional.lean`. They
are named hypotheses here only so that this module rests on the space-level material alone.

*What the proofs contribute.* The descent from a scheme chart to the space: for
constructibility the definition of Stacks 0ECU quantifies over all étale charts, so the chart
hypothesis is used at the given chart and transported along the homeomorphism of Stacks 03BX;
for upper semicontinuity a surjective étale chart is chosen, its map on points is open and
surjective, and the level sets descend along it.

## References

* [Stacks Project, Tag 0D1Y](https://stacks.math.columbia.edu/tag/0D1Y)
* [Stacks Project, Tag 0BDI](https://stacks.math.columbia.edu/tag/0BDI)
* [Stacks Project, Tag 0ECU](https://stacks.math.columbia.edu/tag/0ECU)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
* [Stacks Project, Tag 08JL](https://stacks.math.columbia.edu/tag/08JL)
-/

@[expose] public noncomputable section

open CategoryTheory Topology

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A function on the points of a presheaf on the big fppf site of `S` is an `i`-th
*Betti-number function* when on every étale chart from an object of the site it agrees, under
the homeomorphism of Stacks 03BX between the points of a represented presheaf and the points
of the representing scheme, with the `i`-th derived-fibre Betti function of a pseudo-coherent
complex on that scheme. -/
def IsEtaleLocallyDerivedFibreBetti (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (β : points B S hS X → ℕ) (i : ℤ) : Prop :=
  ∀ (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X), IsEtale B S hS φ →
    ∃ (F : DerivedCategory ((BigFppfOver.toScheme B S hS).obj U).Modules)
      (hF : RingedSpace.IsPseudoCoherent
        (X := ((BigFppfOver.toScheme B S hS).obj U).toRingedSpace) F),
      DerivedFibreBetti.derivedFiberBetti ((BigFppfOver.toScheme B S hS).obj U) F hF i =
        β ∘ pointsMap B S hS (yoneda.obj U) φ ∘ (schemePointsHomeomorph B S hS U).symm

variable (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (β : points B S hS X → ℕ) (i : ℤ)

/-- **Stacks 0D1Y, the level sets of a Betti-number function are étale locally
constructible.** The Betti-number function is data, characterised by `hβ`: the function of
Stacks 0D1Y is built, but nothing identifies it with a derived-fibre Betti function on a
scheme chart. `constructibleLevels` is part (3) of Stacks 0BDI, the same statement for a
scheme, which holds for every scheme and is supplied in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/BettiNumbersOnPointsUnconditional.lean`. -/
@[stacks 0D1Y "constructible levels, for a Betti-number function given as data"]
theorem isEtaleLocallyConstructible_setOf_eq
    (hβ : IsEtaleLocallyDerivedFibreBetti B S hS X β i)
    (constructibleLevels : ∀ (Z : Scheme.{u}) (F : DerivedCategory Z.Modules)
      (hF : RingedSpace.IsPseudoCoherent (X := Z.toRingedSpace) F) (m : ℕ),
      IsLocallyConstructible {z : Z | DerivedFibreBetti.derivedFiberBetti Z F hF i z = m})
    (n : ℕ) :
    IsEtaleLocallyConstructible B S hS X {x | β x = n} := by
  intro U φ hφ
  obtain ⟨F, hF, hval⟩ := hβ U φ hφ
  refine ((schemePointsHomeomorph B S hS U).symm.isLocallyConstructible_preimage_iff
    (pointsMap B S hS (yoneda.obj U) φ ⁻¹' {x | β x = n})).mp ?_
  have hset : {z : (BigFppfOver.toScheme B S hS).obj U |
        DerivedFibreBetti.derivedFiberBetti ((BigFppfOver.toScheme B S hS).obj U) F hF i z
          = n} =
      (schemePointsHomeomorph B S hS U).symm ⁻¹'
        (pointsMap B S hS (yoneda.obj U) φ ⁻¹' {x | β x = n}) := by
    rw [hval]
    rfl
  rw [← hset]
  exact constructibleLevels _ F hF n

/-- **Stacks 0D1Y, upper semicontinuity of a Betti-number function.** The Betti-number
function is data, characterised by `hβ`: the function of Stacks 0D1Y is built, but nothing
identifies it with a derived-fibre Betti function on a scheme chart.
`upperSemicontinuousBetti` is part (2) of Stacks 0BDI, the same statement for a scheme, which
holds for every scheme and is supplied in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/BettiNumbersOnPointsUnconditional.lean`. -/
@[stacks 0D1Y "upper semicontinuity, for a Betti-number function given as data"]
theorem upperSemicontinuous_of_isEtaleLocallyDerivedFibreBetti
    (hX : IsAlgebraicSpace B S hS X)
    (hβ : IsEtaleLocallyDerivedFibreBetti B S hS X β i)
    (upperSemicontinuousBetti : ∀ (Z : Scheme.{u}) (F : DerivedCategory Z.Modules)
      (hF : RingedSpace.IsPseudoCoherent (X := Z.toRingedSpace) F),
      UpperSemicontinuous (DerivedFibreBetti.derivedFiberBetti Z F hF i)) :
    UpperSemicontinuous β := by
  obtain ⟨U, φ, hsurj, het⟩ := hX.exists_atlas
  obtain ⟨F, hF, hval⟩ := hβ U φ (isEtale_of_presheaf_etale B S hS het)
  have hopen : IsOpenMap (pointsMap B S hS (yoneda.obj U) φ) :=
    isOpenMap_pointsMap_of_etale B S hS hX U φ het
  have hsurjPts : Function.Surjective (pointsMap B S hS (yoneda.obj U) φ) :=
    (surjective_iff_surjective_pointsMap B S hS X hX U φ).mp hsurj
  rw [upperSemicontinuous_iff_isOpen_preimage]
  intro a
  have hscheme : IsOpen (DerivedFibreBetti.derivedFiberBetti
      ((BigFppfOver.toScheme B S hS).obj U) F hF i ⁻¹' Set.Iio a) :=
    (upperSemicontinuousBetti _ F hF).isOpen_preimage a
  rw [hval] at hscheme
  have hpre : IsOpen (pointsMap B S hS (yoneda.obj U) φ ⁻¹' (β ⁻¹' Set.Iio a)) :=
    ((schemePointsHomeomorph B S hS U).symm.isOpen_preimage).mp hscheme
  rw [← Set.image_preimage_eq (β ⁻¹' Set.Iio a) hsurjPts]
  exact hopen _ hpre

end AlgebraicGeometry.Space

end
