module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreEulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.BettiNumbersOnPoints

/-!
# The Euler characteristic of the derived fibres on the points of an algebraic space

For a perfect object `E` of `D(𝒪_X)` on an algebraic space `X`, Stacks 0D1Z says that the
alternating sum `χ_E(x) = ∑ (-1)^i β_i(x)` of the derived-fibre Betti numbers is a locally
constant function on `|X|`.

## Main definitions

* `AlgebraicGeometry.Space.IsEtaleLocallyDerivedFibreChi`: a function on the points of a
  presheaf on the big fppf site is the derived-fibre Euler characteristic of a perfect object
  étale locally.

## Main results

* `AlgebraicGeometry.Space.isLocallyConstant_of_isEtaleLocallyDerivedFibreChi`:
  **Stacks 0D1Z**, such a function is locally constant.

## Implementation notes

*Why `χ` is data.*  As for the Betti-number functions in
`AlgebraicGeometry.Space.IsEtaleLocallyDerivedFibreBetti`, not because the function cannot be
built: the derived-fibre Betti numbers of an object of `D(𝒪_X)` on an algebraic space are
`AlgebraicGeometry.Space.geometricFibreBettiFunction`, and their alternating sum is
`AlgebraicGeometry.Space.geometricFibreChiFunction`.  What no declaration provides is the
comparison identifying that function with the derived-fibre Euler characteristic of a complex
on a scheme chart.  The function is therefore taken as data together with the property that
characterises it étale locally, and that property is stated with a *perfect* object on each
chart, which is the hypothesis of the source.

*A single object per chart.*  The property asks for one object `E` on the chart computing `χ`,
not one object per degree.  That is what the source's hypothesis says, and it is what the
conclusion needs: the alternating sum of the Betti numbers of unrelated objects, one per
degree, is not locally constant.

*What the proof contributes.*  The étale localization, which is all the source's proof claims
("Follows from the case of schemes by étale localization").  The case of schemes is
`AlgebraicGeometry.DerivedFibreBetti.isLocallyConstant_chiDerivedFibre`, which carries
`@[stacks 0BDJ]` and is unconditional, so nothing is deferred here.  A surjective étale chart
is chosen, its map on points is open and surjective, and the preimages of sets under `χ` are
open because their preimages on the chart are.

## References

* [Stacks Project, Tag 0D1Z](https://stacks.math.columbia.edu/tag/0D1Z)
* [Stacks Project, Tag 0BDJ](https://stacks.math.columbia.edu/tag/0BDJ)
* [Stacks Project, Tag 0D1Y](https://stacks.math.columbia.edu/tag/0D1Y)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
-/

@[expose] public noncomputable section

open CategoryTheory Topology

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A function on the points of a presheaf on the big fppf site of `S` is the *derived-fibre
Euler characteristic of a perfect object* étale locally when on every étale chart from an
object of the site it agrees, under the homeomorphism of Stacks 03BX between the points of a
represented presheaf and the points of the representing scheme, with the derived-fibre Euler
characteristic of a perfect object of the derived category of modules on that scheme. -/
def IsEtaleLocallyDerivedFibreChi (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (χ : points B S hS X → ℤ) : Prop :=
  ∀ (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X), IsEtale B S hS φ →
    ∃ (E : DerivedCategory ((BigFppfOver.toScheme B S hS).obj U).Modules)
      (hE : RingedSpace.IsPerfect.{u, u + 1}
        (X := ((BigFppfOver.toScheme B S hS).obj U).toRingedSpace) E),
      DerivedFibreBetti.chiDerivedFibre ((BigFppfOver.toScheme B S hS).obj U) E
          (DerivedFibreBetti.isPseudoCoherent_of_isPerfect E hE) =
        χ ∘ pointsMap B S hS (yoneda.obj U) φ ∘ (schemePointsHomeomorph B S hS U).symm

variable (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (χ : points B S hS X → ℤ)

/-- **Stacks 0D1Z.**  The derived-fibre Euler characteristic of a perfect object of `D(𝒪_X)`
on an algebraic space `X` is locally constant on `|X|`.

The function is data, characterised by `hχ` (see the implementation notes); the proof
reduces to the case of schemes, Stacks 0BDJ, by étale localization. -/
@[stacks 0D1Z "for a derived-fibre Euler characteristic given as data"]
theorem isLocallyConstant_of_isEtaleLocallyDerivedFibreChi
    (hX : IsAlgebraicSpace B S hS X)
    (hχ : IsEtaleLocallyDerivedFibreChi B S hS X χ) :
    IsLocallyConstant χ := by
  obtain ⟨U, φ, hsurj, het⟩ := hX.exists_atlas
  obtain ⟨E, hE, hval⟩ := hχ U φ (isEtale_of_presheaf_etale B S hS het)
  have hopen : IsOpenMap (pointsMap B S hS (yoneda.obj U) φ) :=
    isOpenMap_pointsMap_of_etale B S hS hX U φ het
  have hsurjPts : Function.Surjective (pointsMap B S hS (yoneda.obj U) φ) :=
    (surjective_iff_surjective_pointsMap B S hS X hX U φ).mp hsurj
  intro s
  have hscheme : IsOpen (DerivedFibreBetti.chiDerivedFibre
      ((BigFppfOver.toScheme B S hS).obj U) E
      (DerivedFibreBetti.isPseudoCoherent_of_isPerfect E hE) ⁻¹' s) :=
    DerivedFibreBetti.isLocallyConstant_chiDerivedFibre _ E hE s
  rw [hval] at hscheme
  have hpre : IsOpen (pointsMap B S hS (yoneda.obj U) φ ⁻¹' (χ ⁻¹' s)) :=
    ((schemePointsHomeomorph B S hS U).symm.isOpen_preimage).mp hscheme
  rw [← Set.image_preimage_eq (χ ⁻¹' s) hsurjPts]
  exact hopen _ hpre

end AlgebraicGeometry.Space

end
