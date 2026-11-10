module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteSections
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteSlicedSituation
public import StacksFrontier.Homology.DerivedComplete.AdicWeakSerreClass
public import StacksFrontier.Homology.DerivedComplete.NakayamaModule

/-!
# Derived-complete sheaves form a weak Serre subcategory

On a site every object of which has a covering by weakly contractible objects, the sheaves of
modules that are derived complete along a sheaf of ideals form a weak Serre subcategory of all
sheaves of modules.

The criterion for a property to be a weak Serre class asks that it hold for the middle term of
a five-term exact sequence whose other four terms have it, and that it hold of some object.
Both are checked on sections over a weakly contractible object, where evaluation is exact and
derived completeness of a sheaf of modules is derived completeness of the module of sections
along the ideal of sections; for modules over a ring the weak Serre property is already known.

## Main results

* `AlgebraicGeometry.RingedSite.derivedCompleteSheaves_isWeakSerreClass`: the weak Serre
  property.

## Implementation notes

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
theorem derivedCompleteSheaves_isWeakSerreClass_of_slicedObjectsSituation
    (X : RingedSite.{u, v, max u v})
    [HasSheafify X.J AddCommGrpCat.{max u v}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (hX : Stacks.WeaklyContractible.SlicedObjectsSituation.{w, v, u, max u v} X.C X.J)
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ObjectProperty.IsWeakSerreClass
      (fun F : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) =>
        AlgebraicGeometry.RingedSite.IsDerivedComplete X I
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj F)) := by
  let P : ObjectProperty (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    fun F => AlgebraicGeometry.RingedSite.IsDerivedComplete X I
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj F)
  let B := hX
  let B' := hX.toWeaklyContractibleObjectsSituation
  let : Abelian (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    inferInstance
  rw [ObjectProperty.isWeakSerreClass_iff_prop_obj₂_of_exact]
  constructor
  · refine ⟨(0 : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)), ?_⟩
    apply (isDerivedComplete_iff_derivedSections_of_slicedObjectsSituation X B I
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj 0)).2
    intro U hU
    let R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)
    let : IsMulCommutative R := by
      change IsMulCommutative (X.O.obj.obj (op U))
      infer_instance
    let : CommRing R := inferInstance
    let G := SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)
    let : HasProductsOfShape ℕ (ModuleCat.{max u v} R) := inferInstance
    let : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{max u v} R) :=
      moduleCat_hasExactLimitsOfShape_discrete.{max u v} R ℕ
    let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max u v} R)) :=
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    let : G.Additive := ⟨fun {_ _} _ _ => rfl⟩
    let : PreservesFiniteLimits G := inferInstance
    let : G.PreservesZeroMorphisms := inferInstance
    let : G.PreservesHomology := Functor.preservesHomology_of_map_exact G fun S hS =>
      evaluation_map_exact_of_weaklyContractibleObjectsSituation X B' U hU S hS
    let : ∀ {A B : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
        (f : A ⟶ B), PreservesColimit (parallelPair f 0) G := fun f =>
      Functor.PreservesHomology.preservesCokernel G f
    let : PreservesFiniteColimits G := Functor.preservesFiniteColimits_of_preservesCokernels G
    refine ⟨inferInstance, inferInstance, inferInstance,
      inferInstance, ?_⟩
    intro f hf
    let E := (G.mapDerivedCategory).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj 0)
    apply isDerivedCompleteAt_of_isNilpotent
    refine ⟨1, ?_⟩
    have hE : IsZero E := (G.mapDerivedCategory).map_isZero
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).map_isZero
          (isZero_zero _))
    rw [show (1 : End E) = 0 from End.ext ((IsZero.iff_id_eq_zero E).mp hE)]
    simp
  · intro T hT h₀ h₁ h₃ h₄
    apply (isDerivedComplete_iff_derivedSections_of_slicedObjectsSituation X B I
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
          (T.obj' 2))).2
    intro U hU
    let R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)
    let : IsMulCommutative R := by
      change IsMulCommutative (X.O.obj.obj (op U))
      infer_instance
    let : CommRing R := inferInstance
    let J : Ideal R := by
      change Submodule R R
      exact I.toSubmodule.obj (op U)
    let G := SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)
    have h0 := (isDerivedComplete_iff_derivedSections_of_slicedObjectsSituation X B I
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
          (T.obj' 0))).mp h₀ U hU
    rcases h0 with ⟨hAdd, hLim, hColim, hProd, _⟩
    let : G.Additive := hAdd
    let : PreservesFiniteLimits G := hLim
    let : PreservesFiniteColimits G := hColim
    let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat R)) := hProd
    let Q : ObjectProperty (ModuleCat R) := fun M => IsDerivedCompleteModule J M
    have hQ := (AdicWeakSerre.derivedCompleteModules_isWeakSerreClass_and_homology_iff
      R J).1
    let : Q.IsWeakSerreClass := hQ
    have hQ (i : Fin 5) (hi : P (T.obj' i)) : Q (G.obj (T.obj' i)) := by
      change ∀ f ∈ J, IsDerivedCompleteAt
        ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (G.obj (T.obj' i))) f
      intro f hf
      rw [isDerivedCompleteAt_iff_isIso]
      exact (isIso_oneSubSmulShift_congr
        ((G.mapDerivedCategorySingleFunctor 0).app (T.obj' i)) f).mp
          (((isDerivedComplete_iff_derivedSections_of_slicedObjectsSituation X B I _).mp
            hi U hU).2.2.2.2 f hf)
    let T' : ComposableArrows
        (ModuleCat.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))) 4 :=
      (G.mapComposableArrows 4).obj T
    let f₀ := T'.map' 0 1
    let f₁ := T'.map' 1 2
    let f₂ := T'.map' 2 3
    let f₃ := T'.map' 3 4
    have w₀ : f₀ ≫ f₁ = 0 := by
      change G.map (T.map' 0 1) ≫ G.map (T.map' 1 2) = 0
      rw [← Functor.map_comp, hT.toIsComplex.zero' 0 1 2, Functor.map_zero]
    have w₁ : f₁ ≫ f₂ = 0 := by
      change G.map (T.map' 1 2) ≫ G.map (T.map' 2 3) = 0
      rw [← Functor.map_comp, hT.toIsComplex.zero' 1 2 3, Functor.map_zero]
    have w₂ : f₂ ≫ f₃ = 0 := by
      change G.map (T.map' 2 3) ≫ G.map (T.map' 3 4) = 0
      rw [← Functor.map_comp, hT.toIsComplex.zero' 2 3 4, Functor.map_zero]
    let S012 := T.sc' hT.toIsComplex 0 1 2
    let S123 := T.sc' hT.toIsComplex 1 2 3
    let S234 := T.sc' hT.toIsComplex 2 3 4
    have e₀ : (ShortComplex.mk f₀ f₁ w₀).Exact := by
      have hs := evaluation_map_exact_of_weaklyContractibleObjectsSituation X B' U hU S012
        (hT.exact' 0 1 2)
      convert hs using 1
      rfl
    have e₁ : (ShortComplex.mk f₁ f₂ w₁).Exact := by
      have hs := evaluation_map_exact_of_weaklyContractibleObjectsSituation X B' U hU S123
        (hT.exact' 1 2 3)
      convert hs using 1
      rfl
    have e₂ : (ShortComplex.mk f₂ f₃ w₂).Exact := by
      have hs := evaluation_map_exact_of_weaklyContractibleObjectsSituation X B' U hU S234
        (hT.exact' 2 3 4)
      convert hs using 1
      rfl
    have hExact : T'.Exact := ComposableArrows.exact_of_δ₀
      (ComposableArrows.exact₂_mk _ w₀ e₀)
      (ComposableArrows.exact_of_δ₀
        (ComposableArrows.exact₂_mk _ w₁ e₁)
        (ComposableArrows.exact₂_mk _ w₂ e₂))
    have hQ2 : Q (G.obj (T.obj' 2)) := by
      have hQ2' : Q (T'.obj' 2) :=
        Q.prop_obj₂_of_exact T' hExact (hQ 0 h₀) (hQ 1 h₁) (hQ 3 h₃) (hQ 4 h₄)
      simpa [T'] using hQ2'
    refine ⟨hAdd, hLim, hColim, hProd, ?_⟩
    intro f hf
    change IsDerivedCompleteAt ((G.mapDerivedCategory).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
          (T.obj' 2))) f
    rw [isDerivedCompleteAt_iff_isIso]
    have hmod : IsDerivedCompleteModule J (G.obj (T.obj' 2)) := hQ2
    have hsingle : IsDerivedCompleteAt
        ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (G.obj (T.obj' 2))) f :=
      hmod f hf
    rw [isDerivedCompleteAt_iff_isIso] at hsingle
    exact (isIso_oneSubSmulShift_congr
      ((G.mapDerivedCategorySingleFunctor 0).app (T.obj' 2)) f).mpr hsingle

/-- Derived-complete sheaves of modules form a weak Serre subcategory on a site
with enough weakly contractible objects. -/
@[stacks 099Q "weak_serre"]
theorem derivedCompleteSheaves_isWeakSerreClass
    (X : RingedSite.{u, v, max u v})
    [Small.{v} X.C]
    [HasSheafify X.J (Type v)]
    [HasSheafify X.J AddCommGrpCat.{max u v}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (hX : X.J.HasEnoughWeaklyContractibleObjects)
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ObjectProperty.IsWeakSerreClass
      (fun F : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) =>
        AlgebraicGeometry.RingedSite.IsDerivedComplete X I
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            0).obj F)) :=
  derivedCompleteSheaves_isWeakSerreClass_of_slicedObjectsSituation X
    (Stacks.WeaklyContractible.SlicedObjectsSituation.of
      ⟨fun U => X.J.IsWeaklyContractible U, fun {_} hU => hU, hX⟩
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) I

end AlgebraicGeometry.RingedSite

end
