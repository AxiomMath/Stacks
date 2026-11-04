module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedStalk
public import StacksFrontier.Homology.Tor.BaseChangeTensorIso
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.Tor.BaseChangeTensorIsoSupplement

/-!
# The derived stalk at a point of an affine open, read degree by degree

`AlgebraicGeometry.derivedStalkAffineSectionsIsoToStalk` identifies two *objects* of a derived
category: for `i : Spec A ⟶ X` and a point `y` of `Spec A`,

```
RΓ(U,K) ⊗ᴸ_A 𝒪_{Spec A,y}  ≅  K_{i y} ⊗ᴸ_{𝒪_{X, i y}} 𝒪_{Spec A,y}.
```

Condition (2) of Stacks 0DJ8 is read in
`StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartCohomologyComparison`
not object by object but *degree by degree*, as a family of maps of localized modules, so what a
consumer of that reading needs is the same identification with `Hⁿ` applied and the left-hand
side recognized as a localization of `Hⁿ(RΓ(U,K))`.  That is what this module records:

```
(Hⁿ RΓ(U,K))_y  ≅  Hⁿ(K_{i y} ⊗ᴸ_{𝒪_{X, i y}} 𝒪_{Spec A,y}),
```

an isomorphism of `A`-modules.

## Main results

* `AlgebraicGeometry.localizedHomologyAffineSectionsStalkIso`: the displayed identification.

## The proof

The germ map `A ⟶ 𝒪_{Spec A,y}` is a localization, hence flat, so derived extension of scalars
along it commutes with each cohomology functor and turns cohomology into localized cohomology:
that is `CochainComplex.DerivedTensor.derivedExtensionScalarsLocalizationHomologyIsoAtModel`.
Applying it at `RΓ(U,K)` and composing with `Hⁿ` of
`AlgebraicGeometry.derivedStalkAffineSectionsIsoToStalk` is the whole proof.

## Implementation notes

*The model of the derived category.*  The locally small one throughout, as in
`AlgebraicGeometry.derivedStalkAffineSectionsIsoToStalk` and in
`AlgebraicGeometry.BaseChangeChart.comparison`.  This is the one point at which this module could
not simply be written: the file
`StacksFrontier.Homology.Tor.BaseChangeTensorIso` carries
`attribute [local instance] HasDerivedCategory.standard` over the whole of its namespace, so
`CochainComplex.DerivedTensor.derivedExtensionScalarsLocalizationHomologyIsoAtModel` and
`CochainComplex.DerivedTensor.derivedExtensionScalarsHomologyIsoAtModel` had their statements
pinned to the standard model, with morphisms in `Type (u+1)`, and nothing stated at the locally
small model could consume them.  Both now take the model as an instance binder and so say
something about every model; the standard model is still the one their existing consumers get,
from the ambient local instance of their own files.

*Two spellings of the localized module.*  The localization functor here is
`CochainComplex.DerivedTensor.localizedModuleFunctor`, an endofunctor of `ModuleCat A` with the
literal `LocalizedModule` carrier, which is the spelling
`derivedExtensionScalarsLocalizationHomologyIsoAtModel` is stated in.  The degreewise reading of
condition (2),
`AlgebraicGeometry.BaseChangeChart.isIso_comparison_iff_forall_localized`, is stated in Mathlib's
`ModuleCat.localizedModuleFunctor` instead, which lands in `ModuleCat (Localization S)` and whose
carrier is `Shrink (LocalizedModule S M)`.  The two are identified over the base ring by
`StacksDraft.localizedModuleFunctorRestrictIso`, and they invert the same morphisms by
`StacksDraft.isIso_localizedModuleFunctor_map_iff`; neither is needed for the statement above,
which is why the spelling here is the one the derived statements come in.

*The point of `Spec A` is typed `↥(Spec A)`.*  As in
`StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedStalk`: the exactness instances for the
stalk functor are keyed at a point of a scheme and are not found when the point is presented as a
prime of the coordinate ring, while `Ideal.primeCompl` needs the primality of `y.asIdeal`, which
is supplied by reading `y` back as a prime.

## References

* [Stacks Project, Tag 01HV](https://stacks.math.columbia.edu/tag/01HV)
* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars)

universe u

namespace AlgebraicGeometry

attribute [local instance] hasDerivedCategory_ringedSpaceModules

/-- **The derived stalk at a point of an affine open, read degree by degree.**  For
`i : Spec A ⟶ X`, a point `y` of `Spec A` and `K ∈ D(𝒪_X)` with quasi-coherent cohomology
sheaves, the localization at `y` of the degree-`n` cohomology of `RΓ(U,K)` is the degree-`n`
cohomology of the derived stalk of `K` at `i y`, base changed to `𝒪_{Spec A,y}`:

`(Hⁿ RΓ(U,K))_y ≅ Hⁿ(K_{i y} ⊗ᴸ_{𝒪_{X, i y}} 𝒪_{Spec A,y})`.

When `i` is an open immersion `𝒪_{X, i y} ⟶ 𝒪_{Spec A,y}` is invertible and the right-hand side
is the degree-`n` cohomology of the derived stalk itself; the statement asks nothing of `i`.

This is `AlgebraicGeometry.derivedStalkAffineSectionsIsoToStalk` with `Hⁿ` applied, the left-hand
side being recognized as a localization because the germ map is one. -/
@[stacks 0DJ8 "the degreewise reading of the first of the two inputs needed to turn condition \
(1) into condition (2): the localization at a prime of the degree-n cohomology of RGamma(U,K) \
is the degree-n cohomology of the derived stalk there. The identification of this localized \
module with the localization of the degree-n chart map of condition (2), which needs the \
compatibility of the base-change comparison of Tag 065Z with localizing ALL FOUR rings of the \
chart's square and not only its right-hand column, is not proved anywhere, so condition (1) \
implies condition (2) is NOT formalized"]
public def localizedHomologyAffineSectionsStalkIso {X : Scheme.{u}} {A : CommRingCat.{u}}
    (i : Spec A ⟶ X) (y : Spec A) (K : DerivedCategory X.Modules)
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent)
    (n : ℤ) :
    (CochainComplex.DerivedTensor.localizedModuleFunctor.{u, u}
        (show PrimeSpectrum (A : Type u) from y).asIdeal.primeCompl).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A : Type u)) n).obj
          ((affineDerivedSections i).obj K)) ≅
      (ModuleCat.restrictScalars.{u, u, u} (StructureSheaf.toStalk A y).hom).obj
        ((DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((Spec A).presheaf.stalk y : Type u)) n).obj
          ((totalDerivedExtensionScalars.{u, u, u} (i.stalkMap y).hom).functor.obj
            ((derivedStalkFunctor (i y)).obj K))) := by
  have : (show PrimeSpectrum (A : Type u) from y).asIdeal.IsPrime :=
    (show PrimeSpectrum (A : Type u) from y).isPrime
  let : Algebra (A : Type u) (((Spec A).presheaf.stalk y : CommRingCat.{u}) : Type u) :=
    (StructureSheaf.toStalk A y).hom.toAlgebra
  have : IsLocalization.AtPrime (((Spec A).presheaf.stalk y : CommRingCat.{u}) : Type u)
      (show PrimeSpectrum (A : Type u) from y).asIdeal :=
    AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk (R := (A : Type u)) y
  exact
    ((CochainComplex.DerivedTensor.derivedExtensionScalarsLocalizationHomologyIsoAtModel.{u, u, u}
          (A := ((Spec A).presheaf.stalk y : Type u))
          (show PrimeSpectrum (A : Type u) from y).asIdeal.primeCompl n).app
        ((affineDerivedSections i).obj K)).symm ≪≫
    (ModuleCat.restrictScalars.{u, u, u} (StructureSheaf.toStalk A y).hom).mapIso
      ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((Spec A).presheaf.stalk y : Type u)) n).mapIso
        (derivedStalkAffineSectionsIsoToStalk i y K hK))

end AlgebraicGeometry

end
