module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteSectionsSliceTesting
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteSlicedSituation
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteWeakSerre
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.SliceTestingFamily
public import StacksFrontier.Homology.DerivedComplete.AdicWeakSerreClass
public import StacksFrontier.Homology.DerivedComplete.NakayamaModule

/-!
# Derived-complete sheaves form a weak Serre subcategory, on a slice testing family

`StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteWeakSerre` proves that on a small site with
enough weakly contractible objects the sheaves of modules, in the universe `max u v` of the site,
that are derived complete along a sheaf of ideals form a weak Serre subcategory of all sheaves of
modules. This file proves the same on a site that is not assumed small, for sheaves of modules
in an arbitrary universe `max u v w` containing the site, with the weakly contractible objects a
`Stacks.WeaklyContractible.SliceTestingFamily` at that universe.

The criterion for a property to be a weak Serre class asks that it hold for the middle term of
a five-term exact sequence whose other four terms have it, and that it hold of some object.
Both are checked on sections over a weakly contractible object, where evaluation is exact and
derived completeness of a sheaf of modules is derived completeness of the module of sections
along the ideal of sections; for modules over a ring the weak Serre property is already known.

## Main results

* `AlgebraicGeometry.RingedSite.derivedCompleteSheaves_isWeakSerreClass_of_sliceTestingFamily`:
  the weak Serre property.

## Implementation notes

The weakly contractible objects are a
`Stacks.WeaklyContractible.SliceTestingFamily` at the universe of the module
sections, and the site is not assumed small: the sections of the modules live in an arbitrary
universe `max u v w` containing the site. On a small site a covering collection of weakly
contractible objects is such a family by
`Stacks.WeaklyContractible.SliceTestingFamily.ofIsWeaklyContractible`; the small
pro-étale site of a scheme, which is not essentially small, carries one in every universe.

The result is stated for an arbitrary ringed site and sheaf of ideals. The constant sheaf of a
Noetherian ring together with the sheaf of ideals induced by an ideal gives the situation of the
source; Noetherianity is not needed for the weak Serre property itself.

## References

* [Stacks Project, Tag 099Q](https://stacks.math.columbia.edu/tag/099Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.RingedSite
open CategoryTheory.GrothendieckTopology
open scoped ZeroObject
open scoped IsMulCommutative

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace AlgebraicGeometry.RingedSite

/-- Derived-complete sheaves of modules form a weak Serre subcategory on a site
with enough weakly contractible objects. -/
@[stacks 099Q "weak_serre"]
theorem derivedCompleteSheaves_isWeakSerreClass_of_sliceTestingFamily
    (X : RingedSite.{u, v, max u v w})
    [HasSheafify X.J AddCommGrpCat.{max u v w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (B : Stacks.WeaklyContractible.SliceTestingFamily.{max u v w} X.C X.J)
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ObjectProperty.IsWeakSerreClass
      (fun F : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) =>
        AlgebraicGeometry.RingedSite.IsDerivedComplete.{u, v, max u v w, max u v w} X I
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
              F)) := by
  let P : ObjectProperty
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) := fun F =>
    AlgebraicGeometry.RingedSite.IsDerivedComplete.{u, v, max u v w, max u v w} X I
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj F)
  let : Abelian (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    inferInstance
  rw [ObjectProperty.isWeakSerreClass_iff_prop_obj₂_of_exact]
  refine ⟨⟨(0 : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)),
    (isDerivedComplete_iff_derivedSections_of_sliceTestingFamily X B I
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj 0)).2
      fun U hU => ?_⟩, fun T hT h₀ h₁ h₃ h₄ => ?_⟩
  · let R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)
    let : IsMulCommutative R := inferInstanceAs (IsMulCommutative (X.O.obj.obj (op U)))
    let : CommRing R := inferInstance
    let G := SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)
    let : HasProductsOfShape ℕ (ModuleCat.{max u v w} R) := inferInstance
    let : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{max u v w} R) :=
      moduleCat_hasExactLimitsOfShape_discrete.{max u v w} R ℕ
    let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max u v w} R)) :=
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    let : G.Additive := ⟨fun {_ _} _ _ => rfl⟩
    let : PreservesFiniteLimits G := inferInstance
    let : G.PreservesZeroMorphisms := inferInstance
    let : G.PreservesHomology :=
      Functor.preservesHomology_of_map_exact G (evaluation_map_exact_of_sliceTestingFamily X B U hU)
    let : ∀ {A B : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
        (f : A ⟶ B), PreservesColimit (parallelPair f 0) G := fun f =>
      Functor.PreservesHomology.preservesCokernel G f
    let : PreservesFiniteColimits G := Functor.preservesFiniteColimits_of_preservesCokernels G
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, fun f _ =>
      isDerivedCompleteAt_of_isNilpotent ⟨1, by
        ext
        exact IsZero.eq_of_src (G.mapDerivedCategory.map_isZero
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).map_isZero
              (isZero_zero _))) _ _⟩⟩
  · refine (isDerivedComplete_iff_derivedSections_of_sliceTestingFamily X B I
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
          (T.obj' 2))).2 fun U hU => ?_
    obtain ⟨hAdd, hLim, hColim, hProd, -⟩ :=
      (isDerivedComplete_iff_derivedSections_of_sliceTestingFamily X B I _).mp h₀ U hU
    let R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)
    let : IsMulCommutative R := inferInstanceAs (IsMulCommutative (X.O.obj.obj (op U)))
    let : CommRing R := inferInstance
    let J : Ideal R := I.toSubmodule.obj (op U)
    let G := SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)
    let : G.Additive := hAdd
    let : PreservesFiniteLimits G := hLim
    let : PreservesFiniteColimits G := hColim
    let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat R)) := hProd
    let Q : ObjectProperty (ModuleCat R) := fun M => IsDerivedCompleteModule J M
    let : Q.IsWeakSerreClass :=
      (AdicWeakSerre.derivedCompleteModules_isWeakSerreClass_and_homology_iff R J).1
    have hQ (i : Fin 5) (hi : P (T.obj' i)) : Q (G.obj (T.obj' i)) := fun f hf =>
      (isIso_oneSubSmulShift_congr ((G.mapDerivedCategorySingleFunctor 0).app (T.obj' i)) f).mp
        (((isDerivedComplete_iff_derivedSections_of_sliceTestingFamily X B I _).mp hi U hU).2.2.2.2
          f hf)
    let T' : ComposableArrows
        (ModuleCat.{max u v w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))) 4 :=
      (G.mapComposableArrows 4).obj T
    have hExact : T'.Exact := ⟨⟨fun i hi => by
        change G.map _ ≫ G.map _ = 0
        rw [← Functor.map_comp, hT.toIsComplex.zero i hi, Functor.map_zero]⟩,
      fun i hi => evaluation_map_exact_of_sliceTestingFamily X B U hU
        (T.sc' hT.toIsComplex i (i + 1) (i + 2)) (hT.exact i hi)⟩
    have hmod : IsDerivedCompleteModule J (G.obj (T.obj' 2)) :=
      Q.prop_obj₂_of_exact T' hExact (hQ 0 h₀) (hQ 1 h₁) (hQ 3 h₃) (hQ 4 h₄)
    exact ⟨hAdd, hLim, hColim, hProd, fun f hf => (isIso_oneSubSmulShift_congr
      ((G.mapDerivedCategorySingleFunctor 0).app (T.obj' 2)) f).mpr (hmod f hf)⟩

end AlgebraicGeometry.RingedSite

end
