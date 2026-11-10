module

public import StacksFrontier.AlgebraicGeometry.Varieties.KunnethDegreeZeroUnitClasses
public import StacksFrontier.CategoryTheory.Monoidal.InternalHomUnitHomothety
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.UnitComparison
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeSubobjects

/-!
# The unit of the degree-zero Künneth map on classes is an isomorphism

`AlgebraicGeometry.degreeZeroKunnethMap_classes` computes the degree-zero Künneth map on the
classes of two morphisms out of the structure sheaf through one fixed morphism
`u = AlgebraicGeometry.degreeZeroKunnethUnit k X Y : 𝒪_W ⟶ Lp^*𝒪_X ⊗^𝐋 Lq^*𝒪_Y` on
`W = X ×_k Y`. This file proves that `u` is an isomorphism when `X` and `Y` are quasi-compact
and quasi-separated over the field `k`.

## The argument

The degree-zero Künneth map is bijective at `(𝒪_X, 𝒪_Y)` (`isIso_degreeZeroKunnethMap`), every
class is the class of a morphism (Stacks 08JA at source the structure sheaf), and the classes of
morphisms out of `𝒪_X` and `𝒪_Y` multiply to classes of morphisms factoring through `u`. Hence
every morphism `𝒪_W ⟶ Lp^*𝒪_X ⊗^𝐋 Lq^*𝒪_Y` factors through `u`
(`AlgebraicGeometry.exists_eq_degreeZeroKunnethUnit_comp`). The target is isomorphic to `𝒪_W`
(`AlgebraicGeometry.boxDerivedStructureSheafIso`), so `u` composed with that isomorphism is an
endomorphism of `𝒪_W` with a right inverse; endomorphisms of the unit object of a monoidal
category commute (Eckmann–Hilton, `CategoryTheory.MonoidalCategory.comp_comm_tensorUnit`, for the
monoidal structure of [Stacks, Tag 0FPT]), so the right inverse is two-sided.

## Main results

* `AlgebraicGeometry.exists_eq_degreeZeroKunnethUnit_comp`: every morphism
  `𝒪_W ⟶ Lp^*𝒪_X ⊗^𝐋 Lq^*𝒪_Y` is `u ≫ m` for some `m`.
* `AlgebraicGeometry.structureSheafObj_endo_comm`: endomorphisms of `𝒪_W` commute.
* `AlgebraicGeometry.isIso_degreeZeroKunnethUnit`: **`u` is an isomorphism**.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 0FLQ](https://stacks.math.columbia.edu/tag/0FLQ)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace MonoidalCategory
open scoped TensorProduct

attribute [local instance 100000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

open Stacks.Cohomology.GlobalKunneth (baseRing sectionsOverBase)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)

section OneScheme

variable (k : Type u) [Field k] (V : Over (Spec (.of k)))

/-- `𝒪_V` in degree zero has quasi-coherent cohomology sheaves. -/
theorem isQCohAll_structureSheafObj : IsQCohAll (structureSheafObj k V) := by
  intro j
  have hM : (SheafOfModules.unit V.left.ringCatSheaf).IsQuasicoherent :=
    unit_isQuasicoherent_and_isFiniteType.1
  have es := (DerivedCategory.singleFunctorIsoCompQ V.left.Modules 0).app
    (SheafOfModules.unit V.left.ringCatSheaf)
  have ef := (DerivedCategory.homologyFunctorFactors V.left.Modules j).app
    ((HomologicalComplex.single V.left.Modules (ComplexShape.up ℤ) 0).obj
      (SheafOfModules.unit V.left.ringCatSheaf))
  have e : (DerivedCategory.homologyFunctor V.left.Modules j).obj (structureSheafObj k V) ≅
      ((HomologicalComplex.single V.left.Modules (ComplexShape.up ℤ) 0).obj
        (SheafOfModules.unit V.left.ringCatSheaf)).homology j :=
    (DerivedCategory.homologyFunctor V.left.Modules j).mapIso es ≪≫ ef
  by_cases h0 : j = 0
  · subst h0
    exact (SheafOfModules.isQuasicoherent V.left.ringCatSheaf).prop_of_iso
      (e ≪≫ HomologicalComplex.singleObjHomologySelfIso _ _ _).symm hM
  · exact (SheafOfModules.isQuasicoherent V.left.ringCatSheaf).prop_of_iso e.symm
      ((SheafOfModules.isQuasicoherent V.left.ringCatSheaf).prop_of_isZero
        (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0
          (SheafOfModules.unit V.left.ringCatSheaf) j h0))

/-- `RΓ(V, 𝒪_V)` has no cohomology in negative degrees. -/
theorem isZero_homology_structureSheafObj (i : ℤ) (hi : i < 0) :
    IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) i).obj
        ((sectionsOverBase V.hom.toLRSHom.toShHom).obj (structureSheafObj k V))) :=
  isZero_homology_sectionsOverBase V.hom i hi (SheafOfModules.unit V.left.ringCatSheaf)

/-- **Endomorphisms of the structure sheaf commute.** `𝒪_V[0]` is the unit object of the
monoidal structure of [Stacks, Tag 0FPT] on `D(𝒪_V)`, and endomorphisms of the unit object of a
monoidal category commute. -/
theorem structureSheafObj_endo_comm (f g : structureSheafObj k V ⟶ structureSheafObj k V) :
    f ≫ g = g ≫ f := by
  let := Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal V.left.sheaf
  exact comp_comm_tensorUnit
    (C := Stacks.SheafOfModules.DerivedMonoidal.DerivedModules V.left.sheaf) f g

end OneScheme

section TwoSchemes

variable (k : Type u) [Field k] (X Y : Over (Spec (.of k)))

/-- **Every morphism `𝒪_W ⟶ Lp^*𝒪_X ⊗^𝐋 Lq^*𝒪_Y` factors through the unit `u` of the
degree-zero Künneth map on classes.** -/
theorem exists_eq_degreeZeroKunnethUnit_comp
    [QuasiCompact X.hom] [QuasiSeparated X.hom] [QuasiCompact Y.hom] [QuasiSeparated Y.hom]
    (z : structureSheafObj k (fibreProductOver k X Y) ⟶
      boxDerived k X.hom Y.hom (structureSheafObj k X) (structureSheafObj k Y)) :
    ∃ m : boxDerived k X.hom Y.hom (structureSheafObj k X) (structureSheafObj k Y) ⟶
        boxDerived k X.hom Y.hom (structureSheafObj k X) (structureSheafObj k Y),
      z = degreeZeroKunnethUnit k X Y ≫ m := by
  have hiso := isIso_degreeZeroKunnethMap k X.hom Y.hom (structureSheafObj k X)
    (structureSheafObj k Y) (isQCohAll_structureSheafObj k X) (isQCohAll_structureSheafObj k Y)
    (isZero_homology_structureSheafObj k X) (isZero_homology_structureSheafObj k Y)
  set μ := degreeZeroKunnethMap k X.hom Y.hom (structureSheafObj k X) (structureSheafObj k Y)
  set cW := degreeZeroClassAddEquiv k (fibreProductOver k X Y)
    (boxDerived k X.hom Y.hom (structureSheafObj k X) (structureSheafObj k Y))
  have hall : ∀ w, ∃ m, μ.hom w = cW (degreeZeroKunnethUnit k X Y ≫ m) := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul a b =>
      refine ⟨boxDerivedMap k X Y ((degreeZeroClassAddEquiv k X _).symm a)
        ((degreeZeroClassAddEquiv k Y _).symm b), ?_⟩
      have h := degreeZeroKunnethMap_classes k X Y ((degreeZeroClassAddEquiv k X _).symm a)
        ((degreeZeroClassAddEquiv k Y _).symm b)
      have ha : (show degreeZeroSections k X.hom (structureSheafObj k X) from
          degreeZeroClassAddEquiv k X _ ((degreeZeroClassAddEquiv k X _).symm a)) = a :=
        AddEquiv.apply_symm_apply _ a
      have hb : (show degreeZeroSections k Y.hom (structureSheafObj k Y) from
          degreeZeroClassAddEquiv k Y _ ((degreeZeroClassAddEquiv k Y _).symm b)) = b :=
        AddEquiv.apply_symm_apply _ b
      refine Eq.trans ?_ h
      exact congrArg (fun w => μ.hom w)
        (congrArg₂ (fun (x : degreeZeroSections k X.hom (structureSheafObj k X))
          (y : degreeZeroSections k Y.hom (structureSheafObj k Y)) =>
            x ⊗ₜ[baseRing (Spec (.of k)).toRingedSpace] y) ha hb).symm
    | add x y hx hy =>
      obtain ⟨m₁, h₁⟩ := hx
      obtain ⟨m₂, h₂⟩ := hy
      refine ⟨m₁ + m₂, ?_⟩
      rw [map_add, h₁, h₂, Preadditive.comp_add, map_add]
      rfl
  obtain ⟨m, hm⟩ := hall ((inv μ).hom (cW z))
  refine ⟨m, cW.injective ?_⟩
  rw [← hm]
  exact (CategoryTheory.IsIso.inv_hom_id_apply μ (cW z)).symm

/-- **`Lp^*𝒪_X ⊗^𝐋 Lq^*𝒪_Y ≅ 𝒪_W`**: the unit comparisons `Lp^*𝒪_X ≅ 𝒪_W` and
`Lq^*𝒪_Y ≅ 𝒪_W` of the derived pullbacks, followed by the left unitor of the monoidal structure
of [Stacks, Tag 0FPT] on `D(𝒪_W)`. -/
def boxDerivedStructureSheafIso :
    boxDerived k X.hom Y.hom (structureSheafObj k X) (structureSheafObj k Y) ≅
      structureSheafObj k (fibreProductOver k X Y) :=
  letI := Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal
    (Limits.pullback X.hom Y.hom).toRingedSpace.sheaf
  let W := (Limits.pullback X.hom Y.hom).toRingedSpace
  let OW : DerivedCategory (SheafOfModules.{u} (structureSheafRing W)) :=
    (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing W)) 0).obj
      (SheafOfModules.unit (structureSheafRing W))
  let νp := Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso
    (Limits.pullback.fst X.hom Y.hom).toLRSHom.toShHom
  let νq := Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso
    (Limits.pullback.snd X.hom Y.hom).toLRSHom.toShHom
  let e₁ : boxDerived k X.hom Y.hom (structureSheafObj k X) (structureSheafObj k Y) ≅
      ((derivedTensorProductFunctor W.sheaf).obj OW).obj OW :=
    ((derivedTensorProductFunctor W.sheaf).mapIso νp).app _ ≪≫
      ((derivedTensorProductFunctor W.sheaf).obj _).mapIso νq
  let e₂ : ((derivedTensorProductFunctor W.sheaf).obj OW).obj OW ≅
      𝟙_ (Stacks.SheafOfModules.DerivedMonoidal.DerivedModules W.sheaf) ⊗
        𝟙_ (Stacks.SheafOfModules.DerivedMonoidal.DerivedModules W.sheaf) :=
    Iso.refl _
  let e₃ : 𝟙_ (Stacks.SheafOfModules.DerivedMonoidal.DerivedModules W.sheaf) ≅
      structureSheafObj k (fibreProductOver k X Y) :=
    Iso.refl _
  e₁.trans ((e₂.trans
    (λ_ (𝟙_ (Stacks.SheafOfModules.DerivedMonoidal.DerivedModules W.sheaf)))).trans e₃)

/-- **The unit of the degree-zero Künneth map on classes is an isomorphism**, for `X` and `Y`
quasi-compact and quasi-separated over the field `k`:
`AlgebraicGeometry.degreeZeroKunnethUnit k X Y : 𝒪_W ⟶ Lp^*𝒪_X ⊗^𝐋 Lq^*𝒪_Y` is invertible. -/
theorem isIso_degreeZeroKunnethUnit
    [QuasiCompact X.hom] [QuasiSeparated X.hom] [QuasiCompact Y.hom] [QuasiSeparated Y.hom] :
    IsIso (degreeZeroKunnethUnit k X Y) := by
  set c := boxDerivedStructureSheafIso k X Y
  set u := degreeZeroKunnethUnit k X Y
  obtain ⟨m, hm⟩ := exists_eq_degreeZeroKunnethUnit_comp k X Y c.inv
  set e := u ≫ c.hom
  set r := c.inv ≫ m ≫ c.hom
  have her : e ≫ r = 𝟙 _ := by
    simp only [e, r, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc, ← hm, Iso.inv_hom_id]
  have hre : r ≫ e = 𝟙 _ := by
    rw [structureSheafObj_endo_comm k (fibreProductOver k X Y) r e, her]
  have hu : u = e ≫ c.inv := by simp only [e, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine ⟨c.hom ≫ r, ?_, ?_⟩
  · rw [← Category.assoc]
    exact her
  · rw [hu, Category.assoc, ← Category.assoc r, hre, Category.id_comp, Iso.hom_inv_id]

end TwoSchemes

end AlgebraicGeometry

end
