module

public import StacksFrontier.Cotangent.SheavesOfRings.CotangentDerivedTensorModule
public import StacksFrontier.Cotangent.Triangle.DerivedFirstVertex
public import StacksFrontier.Homology.TensorComplex.BifunctorSingleRightComplex
import StacksCore.Tactic.StacksAttribute

/-!
# `L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ` is the complex of the base-changed relative differentials

Let `C` be a site, let `f : 𝒜 ⟶ ℬ` be a morphism of sheaves of commutative rings on `C` and let
`ℱ` be a sheaf of `ℬ`-modules. The first term of the Atiyah triangle of [Stacks, Tag 09DH] is
`L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ`, and the source identifies it with the associated chain complex of the
simplicial sheaf of `ℬ`-modules

`n ↦ Ω_{P_n/𝒜} ⊗_{P_n} ℱ`,

for `P_•` the standard resolution of `ℬ` over `𝒜`. This file proves that identification.

## Main definitions

* `CategoryTheory.Sheaf.cotangentSimplicialModuleTensor`: the simplicial sheaf of `ℬ`-modules
  `Ω_{P_•/𝒜} ⊗_{P_•} ℱ`, written as `Ω_{P_•/𝒜} ⊗_{P_•} ℬ` tensored degreewise with `ℱ` over `ℬ`.

## Main results

* `CategoryTheory.Sheaf.cotangentComplexTensorIso`: the total tensor complex
  `L_{ℬ/𝒜} ⊗_ℬ ℱ[0]` is the alternating-face-map complex of `Ω_{P_•/𝒜} ⊗_{P_•} ℱ`.
* `CategoryTheory.Sheaf.cotangentComplexDerivedTensorSimplicialIso`: **`L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ` is the
  associated chain complex of `Ω_{P_•/𝒜} ⊗_{P_•} ℱ`**, in `D(ℬ)`.

## Implementation notes

**The derived tensor product does not have to be derived here, and that is the point.** The
statement this file proves is the one [Stacks, Tag 09DH] needs about its first term, and it looks
like a *derived* base change along `ℬ`: `s(Ω_{P_•/𝒜} ⊗_{P_•} ℬ) ⊗^𝐋_ℬ ℱ ≅ s(Ω_{P_•/𝒜} ⊗_{P_•} ℱ)`.
It is not one. The cotangent complex of a morphism of sheaves of rings is K-flat
(`CategoryTheory.Sheaf.isKFlat_cotangentComplex`, which is the "flatness of the terms of
`L_{B/A}`" the source invokes), so `L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ` *is* the ordinary total tensor complex
`L_{ℬ/𝒜} ⊗_ℬ ℱ[0]` — that is
`CategoryTheory.Sheaf.cotangentComplexDerivedTensorIso` — and from there the whole statement is
an isomorphism of complexes with no homological algebra left in it:

* `ℱ` sits in a single degree, so the total complex of the tensor double complex collapses onto
  the row of the first factor: `HomologicalComplex.mapBifunctorSingleRightIso` gives
  `Tot(L_{ℬ/𝒜} ⊗_ℬ ℱ[0]) ≅ (- ⊗_ℬ ℱ)` applied to `L_{ℬ/𝒜}` degreewise;
* `- ⊗_ℬ ℱ` is additive, so it commutes with the formation of the (reindexed)
  alternating-face-map complex:
  `AlgebraicTopology.alternatingFaceMapCochainComplexCompMapHomologicalComplexIso`.

So no flat base change over the simplicial sheaf of rings `P_•` is involved, and in particular
none of the machinery of [Stacks, Tag 09D2] is needed for this step.

**What the degreewise term is.** `cotangentSimplicialModuleTensor` is spelled as
`(Ω_{P_n/𝒜} ⊗_{P_n} ℬ) ⊗_ℬ ℱ`, the base-changed differentials of
`CategoryTheory.Sheaf.cotangentSimplicialModule` tensored with `ℱ` over `ℬ`. That is the shape
the source's own computation produces — it computes `L_{ℬ/𝒜} ⊗_ℬ ℱ` termwise — and it is
`Ω_{P_n/𝒜} ⊗_{P_n} ℱ` by transitivity of extension of scalars along `P_n ⟶ ℬ`.

**Universes.** As in `StacksFrontier/Cotangent/SheavesOfRings/CotangentDerivedTensorModule.lean`,
the site is small and its morphisms, the sections of the sheaves of rings and the sections of the
modules lie in one universe; that is what the ringed-site derived tensor product of
[Stacks, Tag 06YU] is stated at.

## References

* [Stacks Project, Tag 09DH](https://stacks.math.columbia.edu/tag/09DH), the Atiyah triangle,
  whose first term this is.
* [Stacks Project, Tag 08SS](https://stacks.math.columbia.edu/tag/08SS), the cotangent complex of
  a morphism of sheaves of rings.
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU), the derived tensor
  product on a ringed site.
* [Stacks Project, Tag 0662](https://stacks.math.columbia.edu/tag/0662), the total complex of a
  tensor double complex.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)

universe u

namespace CategoryTheory.Sheaf

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  {A B : Sheaf J CommRingCat.{u}} (f : A ⟶ B)

/-- **The simplicial sheaf of `ℬ`-modules `Ω_{P_•/𝒜} ⊗_{P_•} ℱ`**, written as the base-changed
relative differentials `Ω_{P_•/𝒜} ⊗_{P_•} ℬ` of `CategoryTheory.Sheaf.cotangentSimplicialModule`
tensored degreewise with `ℱ` over `ℬ`. -/
def cotangentSimplicialModuleTensor (F : Stacks.DerivedTensor.RingedSite.Modules B) :
    SimplicialObject (Stacks.DerivedTensor.RingedSite.Modules B) :=
  (cotangentSimplicialModule.{u, u, u} J f).object ⋙
    (Stacks.SheafOfModules.Tensor.sheafTensor B).flip.obj F

/-- **The degree-`n` term of `Ω_{P_•/𝒜} ⊗_{P_•} ℱ` is `(Ω_{P_n/𝒜} ⊗_{P_n} ℬ) ⊗_ℬ ℱ`**, for
`Ω_{P_n/𝒜}` the sheaf of relative differentials of the degree-`n` term of the standard resolution
and the first extension of scalars taken along its augmentation `P_n ⟶ ℬ`. This is
`CategoryTheory.Sheaf.cotangentSimplicialModuleObjIso` tensored with `ℱ`, and it is the
transitivity of extension of scalars along `P_n ⟶ ℬ` that makes this term `Ω_{P_n/𝒜} ⊗_{P_n} ℱ`. -/
def cotangentSimplicialModuleTensorObjIso (F : Stacks.DerivedTensor.RingedSite.Modules B)
    (n : SimplexCategoryᵒᵖ) :
    (cotangentSimplicialModuleTensor J f F).obj n ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor B).flip.obj F).obj
        ((Stacks.FlatChangeOfRings.extendScalars (resolutionAugmentation J f n)).obj
          (resolutionDifferentials J f n)) :=
  Functor.mapIso ((Stacks.SheafOfModules.Tensor.sheafTensor B).flip.obj F)
    (X := (cotangentSimplicialModule.{u, u, u} J f).object.obj n)
    (Y := (Stacks.FlatChangeOfRings.extendScalars (resolutionAugmentation J f n)).obj
      (resolutionDifferentials J f n))
    (cotangentSimplicialModuleObjIso J f n)

/-- **The total tensor complex `L_{ℬ/𝒜} ⊗_ℬ ℱ[0]` is the alternating-face-map complex of
`Ω_{P_•/𝒜} ⊗_{P_•} ℱ`.** Since `ℱ` sits in a single cohomological degree the total complex
collapses onto the degreewise tensor product with `ℱ`, and that commutes with the formation of
the alternating-face-map complex because `- ⊗_ℬ ℱ` is additive. -/
def cotangentComplexTensorIso (F : Stacks.DerivedTensor.RingedSite.Modules B) :
    ((Stacks.SheafOfModules.Tensor.tensorComplex B).obj (cotangentComplex.{u, u, u} J f)).obj
        ((HomologicalComplex.single (Stacks.DerivedTensor.RingedSite.Modules B)
          (ComplexShape.up ℤ) 0).obj F) ≅
      (alternatingFaceMapCochainComplex (Stacks.DerivedTensor.RingedSite.Modules B)).obj
        (cotangentSimplicialModuleTensor J f F) :=
  HomologicalComplex.mapBifunctorSingleRightIso
      (Stacks.SheafOfModules.Tensor.sheafTensor B) (cotangentComplex.{u, u, u} J f) F ≪≫
    (alternatingFaceMapCochainComplexCompMapHomologicalComplexIso
      ((Stacks.SheafOfModules.Tensor.sheafTensor B).flip.obj F)).app
      (cotangentSimplicialModule.{u, u, u} J f).object

/-- **`L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ` is the associated chain complex of the simplicial sheaf of `ℬ`-modules
`Ω_{P_•/𝒜} ⊗_{P_•} ℱ`.** This is the identification of the first term of the Atiyah triangle of
[Stacks, Tag 09DH] with an explicit complex: the derived tensor product is the ordinary one
because `L_{ℬ/𝒜}` is K-flat, and the ordinary one is the degreewise tensor product with `ℱ` of
the alternating-face-map complex defining `L_{ℬ/𝒜}`. -/
def cotangentComplexDerivedTensorSimplicialIso
    (F : Stacks.DerivedTensor.RingedSite.Modules B) :
    ((derivedTensorProductFunctor B).obj
          (DerivedCategory.Q.obj (cotangentComplex.{u, u, u} J f))).obj
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single (Stacks.DerivedTensor.RingedSite.Modules B)
            (ComplexShape.up ℤ) 0).obj F)) ≅
      DerivedCategory.Q.obj
        ((alternatingFaceMapCochainComplex (Stacks.DerivedTensor.RingedSite.Modules B)).obj
          (cotangentSimplicialModuleTensor J f F)) :=
  cotangentComplexDerivedTensorIso J f F ≪≫
    DerivedCategory.Q.mapIso (cotangentComplexTensorIso J f F)

end CategoryTheory.Sheaf

end
