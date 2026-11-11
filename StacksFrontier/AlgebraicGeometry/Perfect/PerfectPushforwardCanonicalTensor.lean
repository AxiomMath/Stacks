module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.Flat
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.MayerVietorisTorDimension
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectPushforwardDerivedTensor
import StacksCore.Tactic.StacksAttribute

/-!
# Producing perfect complexes: the derived direct image of `E ⊗^L 𝒢` and of `E`

Let `S` be a Noetherian scheme and `f : X ⟶ S` a morphism of schemes. This file states the two
results of the section *Producing perfect complexes* of the chapter on perfect complexes that
conclude perfectness of a derived direct image, at the derived tensor product of
[Stacks, Tag 06YU] (`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`) and the derived
direct image of the morphism of ringed spaces underlying `f`.

## Main results

* `Stacks.Cohomology.PerfectPushforward.isPerfect_derivedPushforward_derivedTensorProductFunctor`:
  [Stacks, Tag 0DJQ]. For `f` locally of finite type, `E` perfect and `𝒢` a bounded complex of
  coherent `𝒪_X`-modules flat over `S` with support proper over `S`, `Rf_*(E ⊗^L_{𝒪_X} 𝒢)` is
  perfect.
* `Stacks.Cohomology.PerfectPushforward.isPerfect_derivedPushforward_of_flat_of_isProper`:
  [Stacks, Tag 0B6F]. For `f` flat and proper and `E` perfect, `Rf_*E` is perfect.

## Implementation notes

[Stacks, Tag 0DJQ] is read here at the canonical derived tensor product; it holds for every derived
tensor product of [Stacks, Tag 06YU], as
`Stacks.Cohomology.PerfectPushforward.isPerfect_derivedPushforward_derivedTensor_of_isPerfect`.

The tag is registered here and not on
`Stacks.Cohomology.PerfectPushforward.isPerfect_derivedPushforward_derivedTensor`
(`StacksFrontier/AlgebraicGeometry/Perfect/PerfectPushforward.lean`), an untagged conditional form
which takes two residues of [Stacks, Tag 08EV] and its Tor-dimension clause as hypotheses; the
statement here takes none of them.

A flat proper morphism to a Noetherian scheme is of finite presentation, hence perfect
(`AlgebraicGeometry.perfect_of_flat_of_locallyOfFinitePresentation`), so [Stacks, Tag 0B6F] is the
case of [Stacks, Tag 0B6G],
`Stacks.AlgebraicGeometry.PerfectProperDirectImage.isPerfect_derivedPushforward_of_isPerfect`.

Both statements are read in the standard model `HasDerivedCategory.standard` of the derived
categories, the model [Stacks, Tag 08EV] and [Stacks, Tag 0B6G] are stated in; it is bound by
`letI` in the statements.

## References

* [Stacks Project, Tag 0DJQ](https://stacks.math.columbia.edu/tag/0DJQ)
* [Stacks Project, Tag 0B6F](https://stacks.math.columbia.edu/tag/0B6F)
* [Stacks Project, Tag 08EV](https://stacks.math.columbia.edu/tag/08EV)
* [Stacks Project, Tag 0B6G](https://stacks.math.columbia.edu/tag/0B6G)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry StrictlyPerfect
open Stacks.Cohomology.ProperSupportPerfection (derivedPushforwardOX)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)

namespace Stacks.Cohomology.PerfectPushforward

universe u

attribute [local implicit_reducible] structureSheafRing
  StrictlyPerfect.structureSheafOfRings StrictlyPerfect.structureModule

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **[Stacks, Tag 0DJQ].** Let `S` be a Noetherian scheme and `f : X ⟶ S` a morphism of schemes
which is locally of finite type. Let `E` be a perfect object of `D(𝒪_X)` and let `𝒢` be a bounded
complex of coherent `𝒪_X`-modules, flat over `S`, with support proper over `S`
(`Stacks.Cohomology.PerfectPushforward.FlatProperSupportComplex`). Then
`Rf_*(E ⊗^L_{𝒪_X} 𝒢)` is a perfect object of `D(𝒪_S)`. -/
@[stacks 0DJQ]
theorem isPerfect_derivedPushforward_derivedTensorProductFunctor [IsNoetherian S]
    [LocallyOfFiniteType f] (G : CochainComplex (OXMod.{u, u} X.toRingedSpace) ℤ)
    (hG : FlatProperSupportComplex f G) :
    letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
    letI := HasDerivedCategory.standard
      (Stacks.DerivedTensor.RingedSite.Modules X.toRingedSpace.sheaf)
    letI := HasDerivedCategory.standard (OXMod.{u, u} S.toRingedSpace)
    ∀ E : DerivedCategory (OXMod.{u, u} X.toRingedSpace),
      RingedSpace.IsPerfect (X := X.toRingedSpace) E →
        RingedSpace.IsPerfect (X := S.toRingedSpace)
          ((derivedPushforwardOX f).obj
            (((derivedTensorProductFunctor X.toRingedSpace.sheaf).obj E).obj
              (DerivedCategory.Q.obj G))) :=
  let := HasDerivedCategory.standard
    (Stacks.DerivedTensor.RingedSite.Modules X.toRingedSpace.sheaf)
  fun E hE => isPerfect_derivedPushforward_derivedTensor_of_isPerfect f
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.toRingedSpace.sheaf) E G hE hG

/-- **[Stacks, Tag 0B6F].** Let `S` be a Noetherian scheme and `f : X ⟶ S` a flat proper morphism
of schemes. Let `E` be a perfect object of `D(𝒪_X)`. Then `Rf_*E` is a perfect object of
`D(𝒪_S)`. -/
@[stacks 0B6F]
theorem isPerfect_derivedPushforward_of_flat_of_isProper [IsNoetherian S] [Flat f] [IsProper f] :
    letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
    letI := HasDerivedCategory.standard (OXMod.{u, u} S.toRingedSpace)
    ∀ E : DerivedCategory (OXMod.{u, u} X.toRingedSpace),
      RingedSpace.IsPerfect (X := X.toRingedSpace) E →
        RingedSpace.IsPerfect (X := S.toRingedSpace) ((derivedPushforwardOX f).obj E) :=
  fun E hE =>
    Stacks.AlgebraicGeometry.PerfectProperDirectImage.isPerfect_derivedPushforward_of_isPerfect
      f E hE

end Stacks.Cohomology.PerfectPushforward

end
