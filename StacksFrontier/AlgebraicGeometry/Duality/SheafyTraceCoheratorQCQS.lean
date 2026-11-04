module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.ProjectionFormulaInterchanged
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.StandardModel
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedTensorAnyModel
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModule
public import StacksFrontier.AlgebraicGeometry.Duality.SheafyTraceCoherator
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorHomBijectionNatural

/-!
# The sheafy trace map after the coherator, for quasi-compact quasi-separated morphisms

`Stacks.Duality.bijective_comp_sheafyTrace` and `Stacks.Duality.isIso_coherator_map_of_bijective`
prove [Stacks, Tag 0A9Q] granted the projection formula of [Stacks, Tag 08EU] for
`Stacks.Duality.pullbackProjectionFormulaMap` and the quasi-coherence of `Lf^*M ⊗^L L` of
[Stacks, Tags 08DW and 08DX]. For a morphism `f : X ⟶ Y` of quasi-compact quasi-separated schemes
both inputs are theorems, and this file discharges them.

## Main results

* `Stacks.Duality.isIso_pullbackProjectionFormulaMap` — the projection formula of
  [Stacks, Tag 08EU] for `pullbackProjectionFormulaMap`.
* `Stacks.Duality.isQuasicoherent_homology_derivedTensor_derivedPullback` — `Lf^*M ⊗^L L` has
  quasi-coherent cohomology.
* `Stacks.Duality.bijective_comp_sheafyTrace_of_qcqs` — precomposition with the trace map is a
  bijection on morphisms out of every object of `D_QCoh(𝒪_Y)`.
* `Stacks.Duality.isIso_coherator_map_sheafyTrace_of_qcqs` — **[Stacks, Tag 0A9Q]**.

## References

* [Stacks Project, Tag 0A9Q](https://stacks.math.columbia.edu/tag/0A9Q)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
  Opposite TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces renaming derivedPullback → derivedPullbackRS,
  derivedAdjunction → derivedAdjunctionRS
open Stacks.Cohomology.DerivedRelativeCupProduct
open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.DerivedKunneth (adjunctionTensorMapRight)
open Stacks.Cohomology.DerivedProjectionFormula (pullbackTensorComparison)
open scoped CategoryTheory.Prod

namespace Stacks.Duality

universe u

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The right adjoint of pushforward, read in the ambient derived categories -/

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

section General

variable (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
  {a : quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X}
  (adj : quasiCoherentDerivedPushforward f hpush ⊣ a)

/-! ### The unit in the first factor followed by the doubled counit -/

/-- **The doubled-counit map preceded by the unit in the first factor is the one-counit map.**
For an adjunction `L ⊣ R`, bifunctors `A` on the source and `B` on the target and a morphism
`α : A ⋙ L ⟶ (L × L) ⋙ B`, the doubled-counit map at `(L H, G)` preceded by `A(η_H, 1)` is the
one-counit map at `(H, G)`: the triangle identity `L η_H ≫ ε_{L H} = 1` cancels the first
counit. -/
private theorem unit_comp_adjunctionBitensorMap {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (A : C × C ⥤ C) (B : D × D ⥤ D)
    (α : A ⋙ L ⟶ L.prod L ⋙ B) (H : C) (G : D) :
    A.map (adj.unit.app H ×ₘ 𝟙 (R.obj G)) ≫ adjunctionBitensorMap adj A B α (L.obj H) G =
      adjunctionTensorMapRight adj A B α H G := by
  unfold adjunctionBitensorMap adjunctionTensorMapRight
  simp only [Adjunction.homEquiv_unit]
  have hu := adj.unit.naturality (A.map (adj.unit.app H ×ₘ 𝟙 (R.obj G)))
  simp only [Functor.id_map, Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hu
  rw [← Category.assoc, hu, Category.assoc, ← R.map_comp]
  congr 2
  have ha := α.naturality (adj.unit.app H ×ₘ 𝟙 (R.obj G))
  simp only [Functor.comp_map, Functor.prod_map, Functor.comp_obj, Functor.id_obj] at ha
  rw [← Category.assoc, ha, Category.assoc, ← Functor.map_comp]
  congr 2
  apply Prod.hom_ext <;> simp

/-! ### The projection-formula map with the pullback in the first factor -/

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- `Stacks.Duality.pullbackProjectionFormulaMap` is the interchanged-order projection-formula
map `Stacks.Cohomology.DerivedKunneth.adjunctionTensorMapRight` of `Lf^* ⊣ Rf_*`. -/
theorem pullbackProjectionFormulaMap_eq (M : DerivedCategory Y.Modules)
    (L : DerivedCategory X.Modules) :
    pullbackProjectionFormulaMap f M L =
      adjunctionTensorMapRight
        (derivedAdjunctionRS f.toLRSHom.toShHom)
        (Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf))
        (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf))
        (pullbackTensorComparison f.toLRSHom.toShHom) M L := by
  have h₁ : (Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf)).map
      ((derivedAdjunctionRS
        f.toLRSHom.toShHom).unit.app M ×ₘ 𝟙 ((derivedPushforward f).obj L)) =
      ((derivedTensorProductFunctor Y.sheaf).map
        ((derivedAdjunctionRS
          f.toLRSHom.toShHom).unit.app M)).app ((derivedPushforward f).obj L) :=
    (congrArg (fun t => ((derivedTensorProductFunctor Y.sheaf).map
        ((derivedAdjunctionRS
          f.toLRSHom.toShHom).unit.app M)).app ((derivedPushforward f).obj L) ≫ t)
      (((derivedTensorProductFunctor Y.sheaf).obj _).map_id _)).trans (Category.comp_id _)
  exact (congrArg (· ≫ relativeCupProduct f.toLRSHom.toShHom
      ((derivedPullbackRS
        f.toLRSHom.toShHom).obj M) L) h₁).symm.trans
    (unit_comp_adjunctionBitensorMap
      (derivedAdjunctionRS f.toLRSHom.toShHom)
      (Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf))
      (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf))
      (pullbackTensorComparison f.toLRSHom.toShHom) M L)

/-- **[Stacks, Tag 08EU] for `Stacks.Duality.pullbackProjectionFormulaMap`.** For a quasi-compact
quasi-separated morphism of schemes `f : X ⟶ Y`, an object `M` of `D(𝒪_Y)` and an object `L` of
`D(𝒪_X)`, both with quasi-coherent cohomology, the projection-formula map
`M ⊗^L_{𝒪_Y} Rf_*L ⟶ Rf_*(Lf^*M ⊗^L_{𝒪_X} L)` is an isomorphism. This is
`AlgebraicGeometry.isIso_adjunctionTensorMapRight_of_quasicoherent`. -/
theorem isIso_pullbackProjectionFormulaMap [QuasiCompact f] [QuasiSeparated f]
    (M : DerivedCategory Y.Modules) (L : DerivedCategory X.Modules)
    (hM : ∀ j : ℤ, ((DerivedCategory.homologyFunctor Y.Modules j).obj M).IsQuasicoherent)
    (hL : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj L).IsQuasicoherent) :
    IsIso (pullbackProjectionFormulaMap f M L) :=
  (pullbackProjectionFormulaMap_eq f M L).symm ▸
    AlgebraicGeometry.isIso_adjunctionTensorMapRight_of_quasicoherent f inferInstance
      inferInstance L M hL hM

omit [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The derived pullback of an object of `D_QCoh(𝒪_Y)` tensored with an object of `D_QCoh(𝒪_X)`
has quasi-coherent cohomology: [Stacks, Tag 08DW] part (1) for the pullback and
[Stacks, Tag 08DX] part (1) for the tensor product. -/
theorem isQuasicoherent_homology_derivedTensor_derivedPullback
    (M : quasiCoherentDerivedCategory Y) (L : quasiCoherentDerivedCategory X) (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      (((derivedTensorProductFunctor X.sheaf).obj
        ((derivedPullbackRS f.toLRSHom.toShHom).obj M.obj)).obj L.obj)).IsQuasicoherent :=
  isQuasicoherent_homology_derivedTensor_anyModel X
    ((derivedPullbackRS f.toLRSHom.toShHom).obj M.obj) L.obj
    (fun j => isQuasicoherent_homology_derivedPullback_anyModel f M.obj M.2 j) L.2 i

/-! ### The trace map on groups of morphisms -/

variable
  (DX : TensorHomAdjunction (derivedTensorProductFunctor X.sheaf)
    (Stacks.SheafOfModules.derivedSheafHom X.sheaf))
  (DY : TensorHomAdjunction (derivedTensorProductFunctor Y.sheaf)
    (Stacks.SheafOfModules.derivedSheafHom Y.sheaf))

/-! ### [Stacks, Tag 0A9Q] -/

/-- **The chain of five bijections.** Let `f : X ⟶ Y` be a quasi-compact quasi-separated
morphism of schemes, `a` any right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`, and `L`, `K`
objects of `D_QCoh(𝒪_X)` and `D_QCoh(𝒪_Y)`. Then precomposition with the sheafy trace map of
[Stacks, Tag 0B6H] is a bijection

`Hom_Y(ι M, Rf_*R𝓗om_{𝒪_X}(L, a K)) ⟶ Hom_Y(ι M, R𝓗om_{𝒪_Y}(Rf_*L, K))`

for every `M` in `D_QCoh(𝒪_Y)`: `Lf^*M ⊗^L_{𝒪_X} L` has quasi-coherent cohomology by
`Stacks.Duality.isQuasicoherent_homology_derivedTensor_derivedPullback`, and the
projection-formula map is invertible by `Stacks.Duality.isIso_pullbackProjectionFormulaMap`. -/
theorem bijective_comp_sheafyTrace_of_qcqs [QuasiCompact f] [QuasiSeparated f]
    (L : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y)
    (M : quasiCoherentDerivedCategory Y) :
    Function.Bijective fun g : (ι _).obj M ⟶ (derivedPushforward f).obj
        (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L.obj)).obj
          (a.obj K).obj) => g ≫ sheafyTrace f DX DY hpush adj L K :=
  bijective_comp_sheafyTrace f hpush adj DX DY L K
    (isQuasicoherent_homology_derivedTensor_derivedPullback f · L)
    (fun M => isIso_pullbackProjectionFormulaMap f M.obj L.obj M.2 L.2) M

end General

section Coherator

attribute [local instance] Stacks.AssociatedSheaf.hasModuleSheafify
  Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective

variable [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]

/-- **[Stacks, Tag 0A9Q].** Let `f : X ⟶ Y` be a morphism of quasi-compact quasi-separated
schemes, let `a = f^×` be the right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`
([Stacks, Tag 0A9E]), and let `DQ_Y : D(𝒪_Y) ⥤ D_QCoh(𝒪_Y)` be the coherator, the right adjoint
of the inclusion ([Stacks, Tag 0CR0]). For `L` in `D_QCoh(𝒪_X)` and `K` in `D_QCoh(𝒪_Y)` the map
of [Stacks, Tag 0B6H]

`Rf_*R𝓗om_{𝒪_X}(L, a(K)) ⟶ R𝓗om_{𝒪_Y}(Rf_*L, K)`

becomes an isomorphism after applying `DQ_Y`. The trace map is built, as in the source, from the
tensor–internal-Hom adjunctions of [Stacks, Tag 08J8] on `X` and on `Y`,
`Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.derivedTensorHomAdjunction`.

The source's argument: the reduction to morphisms out of the quasi-coherent objects,
`Stacks.Duality.isIso_coherator_map_of_bijective`, and the chain of five bijections,
`Stacks.Duality.bijective_comp_sheafyTrace`. -/
@[stacks 0A9Q]
theorem isIso_coherator_map_sheafyTrace_of_qcqs
    (L : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y) :
    IsIso ((DerivedCategoryB.derivedCategoryB (A := Y.Modules)
        (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).ι.rightAdjoint.map
      (sheafyTrace f
        (derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite X.sheaf))
        (derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite Y.sheaf))
        (StandardModel.isQuasicoherent_homology_derivedPushforward f)
        (twistedInverseImageAdjunction f
          (StandardModel.isQuasicoherent_homology_derivedPushforward f)) L K)) :=
  isIso_coherator_map_of_bijective _ (Adjunction.ofIsLeftAdjoint _) _
    (bijective_comp_sheafyTrace_of_qcqs f _ _ _ _ L K)

end Coherator

end Stacks.Duality

end
