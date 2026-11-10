module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.StructureSheafAsADerivedUnit
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AugmentationInvertedByDerivedFunctor
public import StacksFrontier.AlgebraicGeometry.Perfect.TensorFinitelyPresentedPerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.VanishingHigherDirectImages
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleComparison
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleKGroup
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FinitePresentationDegreeMinusOne
public import StacksFrontier.AlgebraicGeometry.UnboundedDerivedDirectImage.QuasiCoherence
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PseudoCoherentAndFiniteTorDimension

/-!
# Perfectness and finite presentation of the single direct image

`Stacks.AlgebraicGeometry.VanishingHigherDirectImages.FlatFinitePresentationOfSingleDirectImage`,
the first of the two inputs named by
`StacksFrontier/AlgebraicGeometry/Perfect/VanishingHigherDirectImages.lean`, says this: for
`f : X ⟶ S` of finite presentation and `ℱ` an `𝒪_X`-module of finite presentation, flat over `S`,
with support proper over `S`, a module `N` on `S` carrying an isomorphism `Rf_* ℱ ≅ N[0]` in
`D⁺(𝒪_S)` is flat and of finite presentation. It is the perfection half of [Stacks, Tag 0A1H]
composed with the algebraic half of [More on Algebra, Tag 0658].

**Two of its three components are proved here**, under exactly the hypotheses that predicate
quantifies over: that `N[0]` is a perfect object of `D(𝒪_S)`, and that `N` is of finite
presentation. The third, flatness of `N`, is
`…VanishingHigherDirectImages.isFlat_of_nonempty_iso` of
`StacksFrontier/AlgebraicGeometry/Perfect/VanishingHigherDirectImagesFlatness.lean`, which also
assembles the three into `flatFinitePresentationOfSingleDirectImage` and states the first
conclusion of [Stacks, Tag 0D4E] with nothing granted.

## Main results

* `…VanishingHigherDirectImages.isPerfect_singleFunctor_of_nonempty_iso`: **the perfection half
  of [Stacks, Tag 0A1H] at the object the proof of [Stacks, Tag 0D4E] applies it to**,
  unconditional.
* `…VanishingHigherDirectImages.isFinitePresentation_of_nonempty_iso`: **the
  finite-presentation clause of [More on Algebra, Tag 0658] at that object**, unconditional.

## Implementation notes

**Perfectness.** [Stacks, Tag 0A1H] is applied as
`AlgebraicGeometry.isPerfect_derivedPushforward_tensor` with `E` the structure sheaf in degree
`0` — perfect because `𝒪_X` is finite locally free, by
`AlgebraicGeometry.isPerfect_singleFunctor_of_isFiniteLocallyFree` — and with `𝒢^•` the complex
`ℱ` in degree `0`, which satisfies that tag's hypothesis on `𝒢^•` by
`AlgebraicGeometry.flatProperSupportFinitelyPresented_singleDegreeComplex'`. Three
identifications then carry the conclusion to `N[0]`: the left unit constraint of the derived
tensor product cancels the tensor factor
(`Stacks.RingedSpace.derivedTensorLeftUnitIso`, [Stacks, Tag 0FPT]), the unbounded derived direct
image agrees on a bounded below object with the one computed on `D⁺`
(`Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus`,
[Stacks, Tag 05TC]), and `DerivedCategory.Plus.singleFunctorιIso` crosses between the two single
functors.

**Finite presentation.** A perfect object is pseudo-coherent, which is
`Stacks.Cohomology.TorAmplitude.isPseudoCoherent_of_isPerfect`, one half of [Stacks, Tag 08CQ];
pseudo-coherence of an object of the derived category is a representative that is
`m`-pseudo-coherent for every `m`, so reading it at `m = -1` and applying [Stacks, Tag 09V9] (2),
`isFinitePresentation_of_isPseudoCoherentFrom_singleFunctor_zero_neg_one` of the namespace
`AlgebraicGeometry.RingedSpace`, gives finite presentation of the module.

**Why this is a separate file.** The results quoted above live in subtrees that install global
`HasDerivedCategory` instances of their own —
`AlgebraicGeometry.hasDerivedCategorySchemeModules` and the locally-small model
`StacksFrontier.Homology.DerivedCategory.LocallySmall` among them — and importing them into
`VanishingHigherDirectImages.lean` moves the derived category's hom universe in the statements
that file owns, including the `@[stacks 0D4E]` registration of the second conclusion. Those
statements are the tag's registration, so they are left alone and the two theorems below are
stated in the same namespace from here.

**Spellings.** `AlgebraicGeometry.Scheme.Modules` and
`Stacks.DerivedTensor.RingedSite.Modules X.sheaf` are the same category by `rfl`, and so are
`AlgebraicGeometry.Scheme.ringCatSheaf` and `Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf`, but
instance search does not cross between them; likewise
`AlgebraicGeometry.RingedSpace.IsPerfect` and
`Stacks.Cohomology.PerfectComplexes.IsPerfect` are the same predicate unfolded. Each crossing
below is made by a `have` carrying the explicit type, which typechecks its term at default
transparency, where the spellings are interchangeable.

## References

* [Stacks Project, Tag 0D4E](https://stacks.math.columbia.edu/tag/0D4E)
* [Stacks Project, Tag 0A1H](https://stacks.math.columbia.edu/tag/0A1H)
* [Stacks Project, Tag 0658](https://stacks.math.columbia.edu/tag/0658)
* [Stacks Project, Tag 08CQ](https://stacks.math.columbia.edu/tag/08CQ)
* [Stacks Project, Tag 09V9](https://stacks.math.columbia.edu/tag/09V9)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 05TC](https://stacks.math.columbia.edu/tag/05TC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)

universe u

namespace Stacks.AlgebraicGeometry.VanishingHigherDirectImages

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The perfection half of [Stacks, Tag 0A1H], at the object the proof of [Stacks, Tag 0D4E]
applies it to.** Let `f : X ⟶ S` be a morphism of finite presentation and let `ℱ` be an
`𝒪_X`-module of finite presentation, flat over `S`, with support proper over `S`. If `Rf_* ℱ` is
isomorphic in `D⁺(𝒪_S)` to a module `N` placed in degree `0`, then `N[0]` is a perfect object of
`D(𝒪_S)`.

Unconditional. This is the first of the three components of
`FlatFinitePresentationOfSingleDirectImage`; the module documentation of this file describes the
proof. -/
public theorem isPerfect_singleFunctor_of_nonempty_iso {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : FinitePresentation f) (F : X.Modules) [F.IsFinitePresentation]
    (hflat : IsFlatOver f.toLRSHom.toShHom F)
    (hsupp : letI : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
      ∃ Z : Closeds X, IsProperOver f Z ∧ SheafOfModules.supp F ⊆ (Z : Set X))
    (N : S.Modules)
    (hN : Nonempty ((Scheme.Modules.pushforward f).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj F) ≅
      (DerivedCategory.Plus.singleFunctor S.Modules 0).obj N)) :
    RingedSpace.IsPerfect (X := S.toRingedSpace)
      ((DerivedCategory.singleFunctor S.Modules 0).obj N) := by
  let : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
  have : QuasiCompact f := hf.quasiCompact
  have : QuasiSeparated f := hf.quasiSeparated
  obtain ⟨eN⟩ := hN
  have hE : RingedSpace.IsPerfect.{u, u + 1} (X := X.toRingedSpace)
      ((DerivedCategory.singleFunctor X.Modules 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))) :=
    isPerfect_singleFunctor_of_isFiniteLocallyFree.{u, u + 1} X _ (isFiniteLocallyFree_unit X)
  have hG : FlatProperSupportFinitelyPresented f (ProperFlatBaseChange.singleDegreeComplex F) :=
    flatProperSupportFinitelyPresented_singleDegreeComplex' f F inferInstance hflat hsupp
  have hperfect := isPerfect_derivedPushforward_tensor f hf _ hE _ hG
  obtain ⟨eb⟩ := Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus
    (Scheme.Modules.pushforward f) (derivedPushforwardModules f)
    (derivedPushforwardModulesUnit f)
    (fun I hI => RingedSpace.isIso_derivedPushforwardUnit_app_of_isKInjective _ I hI)
    ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj F) 0 (by
      change ((DerivedCategory.singleFunctor X.Modules 0).obj F).IsGE 0
      infer_instance)
  have etensor : (((derivedTensorProductFunctor X.sheaf).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)))).obj
      (DerivedCategory.Q.obj (ProperFlatBaseChange.singleDegreeComplex F))) ≅
      (DerivedCategory.singleFunctor X.Modules 0).obj F :=
    Stacks.RingedSpace.derivedTensorLeftUnitIso X.toRingedSpace _ ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app F).symm
  have estep : (derivedPushforward f.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj F) ≅
      (DerivedCategory.singleFunctor S.Modules 0).obj N :=
    eb ≪≫ DerivedCategory.Plus.ι.mapIso eN ≪≫
      (DerivedCategory.Plus.singleFunctorιIso S.Modules 0).app N
  exact isPerfect_of_iso_scheme
    ((derivedPushforward f.toLRSHom.toShHom).mapIso etensor ≪≫ estep) hperfect

/-- **The finite-presentation clause of [More on Algebra, Tag 0658], at the object the proof of
[Stacks, Tag 0D4E] applies it to.** Under the hypotheses of
`isPerfect_singleFunctor_of_nonempty_iso`, the module `N` is of finite presentation.

Unconditional. This is the second of the three components of
`FlatFinitePresentationOfSingleDirectImage`. -/
public theorem isFinitePresentation_of_nonempty_iso {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : FinitePresentation f) (F : X.Modules) [F.IsFinitePresentation]
    (hflat : IsFlatOver f.toLRSHom.toShHom F)
    (hsupp : letI : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
      ∃ Z : Closeds X, IsProperOver f Z ∧ SheafOfModules.supp F ⊆ (Z : Set X))
    (N : S.Modules)
    (hN : Nonempty ((Scheme.Modules.pushforward f).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj F) ≅
      (DerivedCategory.Plus.singleFunctor S.Modules 0).obj N)) :
    N.IsFinitePresentation := by
  have hperf : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.toRingedSpace)
      ((DerivedCategory.singleFunctor S.Modules 0).obj N) :=
    isPerfect_singleFunctor_of_nonempty_iso f hf F hflat hsupp N hN
  obtain ⟨K, hK, hKN⟩ := Stacks.Cohomology.TorAmplitude.isPseudoCoherent_of_isPerfect _ hperf
  exact RingedSpace.isFinitePresentation_of_isPseudoCoherentFrom_singleFunctor_zero_neg_one
    (X := S.toRingedSpace) N ⟨K, hK (-1), hKN⟩

end Stacks.AlgebraicGeometry.VanishingHigherDirectImages

end
