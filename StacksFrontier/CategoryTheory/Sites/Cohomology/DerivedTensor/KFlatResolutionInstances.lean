module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.KFlatInBothVariables
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOfSize
public import StacksFrontier.Homology.KFlat.BifunctorLocalization

/-!
# K-flat resolutions on a ringed site, as instances

Every complex of `O`-modules on a ringed site receives a quasi-isomorphism from a complex which
is K-flat for the tensor product `⊗_O`, in either variable (Stacks 06YS). This file registers
both facts as instances of Mathlib's `CategoryTheory.LocalizerMorphism.HasLeftResolutions`, for
the inclusions `CochainComplex.KFlatBifunctor.kFlatLocalizer` and `kFlatLocalizerLeft` of the
K-flat complexes into the homotopy category. The generic instances
`CochainComplex.KFlatBifunctor.kFlatQ_isLocalization_of_hasLeftResolutions` and
`kFlatQLeft_isLocalization_of_hasLeftResolutions` then make `D(Mod(O))` the localization of the
K-flat complexes in each variable.

## Main results

* `Stacks.DerivedTensor.RingedSite.kFlatLocalizer_hasLeftResolutions`: the K-flat resolutions.
* `Stacks.DerivedTensor.RingedSite.kFlatLocalizerLeft_hasLeftResolutions`: the left K-flat
  resolutions.

## Universes

The object universe `u` and the morphism universe `v` of the site and the universe `w` of the
sections of the structure sheaf are independent, and the site is not assumed small. The modules
have their sections in `w`, which the flat cover behind the resolution forces. The two inputs are
stated at these universes: `Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution_ofSize`
resolves by flat modules, and `Stacks.DerivedTensor.RingedSite.kFlatLeft_of_kFlat` turns a K-flat
complex into a left K-flat one by the symmetry of `⊗_O`.

## References

* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public section

open CategoryTheory

universe w v u

namespace Stacks.DerivedTensor.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (R : Sheaf J CommRingCat.{w})
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).obj M).Additive]
  [∀ (K L : CochainComplex
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} R)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R) (ComplexShape.up ℤ)]

/-- **The K-flat resolutions of [Stacks, Tag 06YS], as an instance.** Every complex of
`O`-modules receives a quasi-isomorphism from a K-flat one: the resolution of
`Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution_ofSize`, with its flatness and
surjectivity clauses forgotten. -/
instance kFlatLocalizer_hasLeftResolutions :
    (CochainComplex.KFlatBifunctor.kFlatLocalizer
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R)).HasLeftResolutions :=
  CochainComplex.KFlatBifunctor.kFlatLocalizer_hasLeftResolutions _ fun G ↦ by
    obtain ⟨P, f, hP, -, hf, -⟩ :=
      Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution_ofSize R G
    exact ⟨P, f, hP, hf⟩

/-- **The left K-flat resolutions, as an instance.** The K-flat resolution of
`kFlatLocalizer_hasLeftResolutions` is also K-flat in the left variable of `⊗_O`, by
`Stacks.DerivedTensor.RingedSite.kFlatLeft_of_kFlat`. -/
instance kFlatLocalizerLeft_hasLeftResolutions :
    (CochainComplex.KFlatBifunctor.kFlatLocalizerLeft
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R)).HasLeftResolutions :=
  CochainComplex.KFlatBifunctor.kFlatLocalizerLeft_hasLeftResolutions _ fun G ↦ by
    obtain ⟨P, f, hP, -, hf, -⟩ :=
      Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution_ofSize R G
    exact ⟨P, f, kFlatLeft_of_kFlat R hP, hf⟩

end Stacks.DerivedTensor.RingedSite

end
