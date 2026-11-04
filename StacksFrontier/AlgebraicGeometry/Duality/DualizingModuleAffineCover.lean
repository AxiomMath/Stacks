module

public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Local
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexCoverCriterion

/-!
# A module whose sections are dualizing over an affine cover is a dualizing complex

Let `Y` be a locally Noetherian scheme, `F` a quasi-coherent `𝒪_Y`-module and `n : ℤ`. This file
proves the converse of `Stacks.Duality.isDualizingComplex_single_specModule`: if over an affine
open `V` the `Γ(Y, V)`-module of sections `Stacks.AlgebraicGeometry.CoherentTFAE.specModule F hV`
placed in degree `n` is a dualizing complex over `Γ(Y, V)` in the sense of
[Stacks, Tag 0A7B], then `F[n]` carries a dualizing model at `V`; and if this holds at one affine
open through every point, then `F[n]` is a dualizing complex on `Y` in the sense of
[Stacks, Tag 0A87]. Both statements also hold for an arbitrary `𝒪_Y`-module `F` presented over
`V` by some `Γ(Y, V)`-module.

## Main definitions

* `Stacks.Duality.restrictSpecTildeModuleIso` — the module-level comparison
  `F|_V ≅ (specModule F hV)^~`, read on `V` through `V ≅ Spec Γ(Y, V)`.
* `Stacks.Duality.singleModelIsoOfModuleIso` — a presentation `F|_V ≅ N^~` by a `Γ(Y, V)`-module
  `N`, read in the derived category on the complexes concentrated in degree `n`: the presenting
  object of `F[n]` over `V` is `N[n]`.
* `Stacks.Duality.singleRestrictSpecTildeModelIso` — the previous comparison at the canonical
  presentation of a quasi-coherent module, so with `N = specModule F hV`.

## Main results

* `Stacks.Duality.hasDualizingModelOn_single_of_module_iso` — `F[n]` carries a dualizing model at
  an affine open `V` as soon as some `Γ(Y, V)`-module `N` presents `F|_V` and `N[n]` is a
  dualizing complex over `Γ(Y, V)`.
* `Stacks.Duality.isDualizingComplex_single_of_forall_exists_module_iso` — the same hypothesis at
  an affine open through every point makes `F[n]` a dualizing complex on `Y`.
* `Stacks.Duality.hasDualizingModelOn_single_of_isDualizingComplex_specModule` and
  `Stacks.Duality.isDualizingComplex_single_of_forall_isDualizingComplex_specModule` — the two
  previous results for quasi-coherent `F` at `N = specModule F hV`, which is the converse of
  `Stacks.Duality.isDualizingComplex_single_specModule`.

## References

* [Stacks Project, Tag 0A7B](https://stacks.math.columbia.edu/tag/0A7B)
* [Stacks Project, Tag 0A86](https://stacks.math.columbia.edu/tag/0A86)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.CoherentTFAE

universe u w

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.Duality

/-- **The module-level comparison at an affine open, in the shape of
`Stacks.Duality.HasDualizingModelOn`.** For quasi-coherent `F` and an affine open `V`, the
restriction `F|_V` is the associated sheaf of the `Γ(Y, V)`-module of sections
`Stacks.AlgebraicGeometry.CoherentTFAE.specModule F hV`, restricted along `V ≅ Spec Γ(Y, V)`. -/
def restrictSpecTildeModuleIso {Y : Scheme.{u}} (F : Y.Modules) [F.IsQuasicoherent]
    {V : Y.Opens} (hV : IsAffineOpen V) :
    (Scheme.Modules.restrictFunctor V.ι).obj F ≅
      (tilde.functor Γ(Y, V) ⋙ Scheme.Modules.restrictFunctor hV.isoSpec.hom).obj
        (specModule F hV) :=
  restrictIsoSpecTilde F hV ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback hV.isoSpec.hom).app
      (tilde (specModule F hV))).symm

/-- **A presentation of `F|_V` by a module propagates to the complexes in a single degree.**
If `F|_V` is the associated sheaf of the `Γ(Y, V)`-module `N`, read on `V` through
`V ≅ Spec Γ(Y, V)`, then the restriction of `F[n]` to `V` is the complex of sheaves associated
to the complex `N[n]` concentrated in degree `n`. -/
def singleModelIsoOfModuleIso {Y : Scheme.{u}} [HasDerivedCategory.{w} Y.Modules]
    (F : Y.Modules) (n : ℤ) {V : Y.Opens} (hV : IsAffineOpen V) (N : ModuleCat.{u} Γ(Y, V))
    (e : (Scheme.Modules.restrictFunctor V.ι).obj F ≅
      (tilde.functor Γ(Y, V) ⋙ Scheme.Modules.restrictFunctor hV.isoSpec.hom).obj N) :
    (Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor Y.Modules n).obj F) ≅
      (tilde.functor Γ(Y, V) ⋙
        Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(Y, V)) n).obj N) :=
  ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategorySingleFunctor n).app F ≪≫
    (DerivedCategory.singleFunctor V.toScheme.Modules n).mapIso e ≪≫
    ((Functor.mapDerivedCategorySingleFunctor
      (tilde.functor Γ(Y, V) ⋙ Scheme.Modules.restrictFunctor hV.isoSpec.hom) n).app N).symm

/-- **The comparison of presenting objects for a quasi-coherent module placed in a single
degree.** Over an affine open `V`, the restriction of `F[n]` to `V` is the complex of sheaves
associated to the complex `(specModule F hV)[n]` of `Γ(Y, V)`-modules concentrated in degree
`n`. -/
def singleRestrictSpecTildeModelIso {Y : Scheme.{u}} [HasDerivedCategory.{w} Y.Modules]
    (F : Y.Modules) [F.IsQuasicoherent] (n : ℤ) {V : Y.Opens} (hV : IsAffineOpen V) :
    (Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor Y.Modules n).obj F) ≅
      (tilde.functor Γ(Y, V) ⋙
        Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(Y, V)) n).obj (specModule F hV)) :=
  singleModelIsoOfModuleIso F n hV (specModule F hV) (restrictSpecTildeModuleIso F hV)

variable {Y : Scheme.{u}} [IsLocallyNoetherian Y] [HasDerivedCategory.{w} Y.Modules]

/-- **A presented module whose presenting module is dualizing over an affine open carries a
dualizing model at that open.** If `e` presents `F|_V` as the associated sheaf of a
`Γ(Y, V)`-module `N` and `N[n]` is a dualizing complex over `Γ(Y, V)`, then `F[n]` satisfies the
local condition of [Stacks, Tag 0A87] at `V`. -/
theorem hasDualizingModelOn_single_of_module_iso (F : Y.Modules) (n : ℤ) {V : Y.Opens}
    (hV : IsAffineOpen V) (N : ModuleCat.{u} Γ(Y, V))
    (e : (Scheme.Modules.restrictFunctor V.ι).obj F ≅
      (tilde.functor Γ(Y, V) ⋙ Scheme.Modules.restrictFunctor hV.isoSpec.hom).obj N)
    (h : letI : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
      letI := HasDerivedCategory.standard (ModuleCat.{u} Γ(Y, V))
      Dualizing.IsDualizingComplex
        ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(Y, V)) n).obj N)) :
    HasDualizingModelOn ((DerivedCategory.singleFunctor Y.Modules n).obj F) V hV :=
  ⟨(DerivedCategory.singleFunctor (ModuleCat.{u} Γ(Y, V)) n).obj N, h,
    ⟨singleModelIsoOfModuleIso F n hV N e⟩⟩

/-- **A module whose sections over an affine open are dualizing there carries a dualizing model
at that open.** This is the converse of `Stacks.Duality.isDualizingComplex_single_specModule` at
one affine open: the hypothesis is the ring-level condition of [Stacks, Tag 0A7B] on the
`Γ(Y, V)`-module `Stacks.AlgebraicGeometry.CoherentTFAE.specModule F hV` placed in degree `n`,
and the conclusion is the local condition of [Stacks, Tag 0A87] at `V` for `F[n]`. -/
theorem hasDualizingModelOn_single_of_isDualizingComplex_specModule
    (F : Y.Modules) [F.IsQuasicoherent] (n : ℤ) {V : Y.Opens} (hV : IsAffineOpen V)
    (h : letI : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
      letI := HasDerivedCategory.standard (ModuleCat.{u} Γ(Y, V))
      Dualizing.IsDualizingComplex
        ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(Y, V)) n).obj
          (specModule F hV))) :
    HasDualizingModelOn ((DerivedCategory.singleFunctor Y.Modules n).obj F) V hV :=
  hasDualizingModelOn_single_of_module_iso F n hV (specModule F hV)
    (restrictSpecTildeModuleIso F hV) h

/-- **A module presented at an affine open through every point by a dualizing module is a
dualizing complex.** If every point of `Y` lies in an affine open `V` over which `F|_V` is the
associated sheaf of a `Γ(Y, V)`-module `N` with `N[n]` a dualizing complex over `Γ(Y, V)`, then
`F[n]` is a dualizing complex on `Y`. -/
theorem isDualizingComplex_single_of_forall_exists_module_iso (F : Y.Modules) (n : ℤ)
    (h : ∀ y : Y, ∃ (V : Y.Opens) (hV : IsAffineOpen V), y ∈ V ∧
      ∃ (N : ModuleCat.{u} Γ(Y, V))
        (_ : (Scheme.Modules.restrictFunctor V.ι).obj F ≅
          (tilde.functor Γ(Y, V) ⋙ Scheme.Modules.restrictFunctor hV.isoSpec.hom).obj N),
        (letI : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
         letI := HasDerivedCategory.standard (ModuleCat.{u} Γ(Y, V))
         Dualizing.IsDualizingComplex
           ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(Y, V)) n).obj N))) :
    IsDualizingComplex ((DerivedCategory.singleFunctor Y.Modules n).obj F) := by
  choose V hV hmem N e hdual using h
  exact isDualizingComplex_of_hasDualizingModelOn_cover V hV
    (top_unique fun y _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hmem y⟩)
    fun y ↦ hasDualizingModelOn_single_of_module_iso F n (hV y) (N y) (e y) (hdual y)

/-- **A module whose sections are dualizing over an affine open through every point is a
dualizing complex.** If every point of `Y` lies in an affine open `V` such that
`(specModule F hV)[n]` is a dualizing complex over `Γ(Y, V)`, then `F[n]` is a dualizing complex
on `Y`. -/
theorem isDualizingComplex_single_of_forall_isDualizingComplex_specModule
    (F : Y.Modules) [F.IsQuasicoherent] (n : ℤ)
    (h : ∀ y : Y, ∃ (V : Y.Opens) (hV : IsAffineOpen V), y ∈ V ∧
      (letI : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
       letI := HasDerivedCategory.standard (ModuleCat.{u} Γ(Y, V))
       Dualizing.IsDualizingComplex
         ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(Y, V)) n).obj
           (specModule F hV)))) :
    IsDualizingComplex ((DerivedCategory.singleFunctor Y.Modules n).obj F) := by
  refine isDualizingComplex_single_of_forall_exists_module_iso F n fun y ↦ ?_
  obtain ⟨V, hV, hmem, hdual⟩ := h y
  exact ⟨V, hV, hmem, specModule F hV, restrictSpecTildeModuleIso F hV, hdual⟩

end Stacks.Duality

end
