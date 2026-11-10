module

public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.LinkOneModuleNaturality

/-!
# The explicit cohomology of the complex `M X`, functorially in `M`

`DGCategory.RightModule.gradedCohomologyIso` identifies the homology of the complex `M X` with
the explicit cohomology — degree-`n` cocycles modulo coboundaries — object by object, and
`DGCategory.RightModule.gradedCohomologyMapOf` is the map that a closed degree-zero morphism
`M ⟶ N` induces on the explicit cohomology. The two are not yet related: nothing says that the
identification carries Mathlib's `HomologicalComplex.homologyMap` to the elementary map.

This file relates them, and uses the relation to produce the map induced on the explicit
cohomology by a morphism of the *homotopy* category `K(Mod^dg(C))` — which is the form the
comparison `β` of [Stacks, Tag 09LK] delivers, its unit being a homotopy class.

## How the identification is pinned down

`DGCategory.RightModule.homologyπ_gradedCohomologyIso_hom` already says what the identification
does on the image of `HomologicalComplex.homologyπ`, and that morphism is epi, so the
identification is determined by its cycles-level counterpart
`DGCategory.RightModule.gradedCyclesIso`. That counterpart is in turn determined by the
inclusion of the cocycles: composing it with the inclusion gives
`HomologicalComplex.iCycles`, by
`CategoryTheory.ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i` and
`HomologicalComplex.cyclesIsoSc'_hom_iCycles`. Since `HomologicalComplex.cyclesMap` is compatible
with `iCycles`, the cycles-level square commutes, and the homology-level square follows by
cancelling the epimorphism.

## Main definitions

* `DGCategory.RightModule.gradedCyclesIso`: the cycles of `M X` in degree `n` are the explicit
  degree-`n` cocycles.
* `DGCategory.RightModule.gradedCohomologyIsoK`: the degree-`n` homology of `M X`, taken in the
  homotopy category of complexes of `R`-modules, is the explicit cohomology.
* `DGCategory.RightModule.gradedCohomologyMapK`: **the map induced on the explicit cohomology by
  a morphism of `K(Mod^dg(C))`**, defined by conjugating the homology functor of the homotopy
  category.

## Main results

* `DGCategory.RightModule.homologyMap_cochainMap_gradedCohomologyIso_hom`: **the identification
  carries `HomologicalComplex.homologyMap` to
  `DGCategory.RightModule.gradedCohomologyMapOf`.**
* `DGCategory.RightModule.gradedCohomologyMapK_mk`: the map induced by a homotopy class is the
  elementary map of any representative — so `DGCategory.RightModule.gradedCohomologyMapK` is
  computed by `DGCategory.RightModule.gradedCohomologyMapOf_mk`, on the class of a cocycle.

## Implementation notes

`CategoryTheory.HomotopyCategory.homologyFunctorFactors` is `irreducible` in Mathlib, so
`DGCategory.RightModule.gradedCohomologyMapK` cannot be computed by unfolding it; what is used is
its naturality, which is the only thing that holds of it anyway.

The identity `(DGCategory.RightModule.gradedLeftHomologyData M X n).i` is the inclusion of the
cocycles only after the isomorphism of short complexes
`DGCategory.RightModule.gradedScIso` has been seen to be the identity in the middle degree, which
is `DGCategory.RightModule.gradedScIso_inv_τ₂`; that isomorphism carries a substituted degree
equation, so the statement is made elementwise, where the two sides are elements of one module
and no transport is visible.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK)
-/

@[expose] public noncomputable section

namespace DGCategory

universe v u r

open CategoryTheory CategoryTheory.Limits

namespace RightModule

variable {R : Type r} [CommRing R] {C : DGCategory.{v, u} R}

attribute [local implicit_reducible] DGCategory.K

/-! ### The cycles of `M X` are the explicit cocycles -/

/-- In the middle degree the comparison of three consecutive terms of `M X` with the short
complex `DGCategory.RightModule.gradedSc` is the identity: the comparison is built from three
identity isomorphisms once its degree equation is substituted. -/
theorem gradedScIso_inv_τ₂ (M : RightModule.{v} C) (X : C.Obj) {i n : ℤ} (h : i + 1 = n) :
    (gradedScIso M X h).inv.τ₂ = 𝟙 _ := by subst h; rfl

/-- The cycles map of the explicit left homology datum of `M X` is the inclusion of the
degree-`n` cocycles. -/
theorem gradedLeftHomologyData_i_apply (M : RightModule.{v} C) (X : C.Obj) (n : ℤ)
    (a : gradedCocycles M X n) :
    ((gradedLeftHomologyData M X n).i).hom a = (a : M.obj X n) := by
  have h2 := gradedScIso_inv_τ₂ M X (show n - 1 + 1 = n by omega)
  change ((gradedScIso M X (show n - 1 + 1 = n by omega)).symm.hom.τ₂).hom
      (a : M.obj X n) = _
  rw [Iso.symm_hom, h2]
  rfl

/-- **The cycles of `M X` in degree `n` are the explicit degree-`n` cocycles.** This is the
cycles-level half of `DGCategory.RightModule.gradedCohomologyIso`, whose own value on the image
of `HomologicalComplex.homologyπ` is this isomorphism followed by the quotient by the
coboundaries. -/
def gradedCyclesIso (M : RightModule.{v} C) (X : C.Obj) (n : ℤ) :
    (M.cochainComplex X).cycles n ≅ ModuleCat.of R (gradedCocycles M X n) :=
  (M.cochainComplex X).cyclesIsoSc' (n - 1) n (n + 1)
      (CochainComplex.prev ℤ n) (CochainComplex.next ℤ n) ≪≫
    (gradedLeftHomologyData M X n).cyclesIso

/-- The identification of the cycles with the cocycles is the canonical one: a cycle and the
cocycle it becomes have the same underlying element of `M X` in degree `n`. -/
theorem gradedCyclesIso_hom_val (M : RightModule.{v} C) (X : C.Obj) (n : ℤ)
    (z : (M.cochainComplex X).cycles n) :
    (((gradedCyclesIso M X n).hom.hom z : gradedCocycles M X n) : M.obj X n) =
      ((M.cochainComplex X).iCycles n).hom z := by
  have key : ((M.cochainComplex X).cyclesIsoSc' (n - 1) n (n + 1)
          (CochainComplex.prev ℤ n) (CochainComplex.next ℤ n)).hom ≫
        (gradedLeftHomologyData M X n).cyclesIso.hom ≫
          (gradedLeftHomologyData M X n).i =
      (M.cochainComplex X).iCycles n := by
    rw [ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i,
      HomologicalComplex.cyclesIsoSc'_hom_iCycles]
  exact (gradedLeftHomologyData_i_apply M X n _).symm.trans
    (ConcreteCategory.congr_hom key z)

/-- The identification of the homology of `M X` with the explicit cohomology, read through the
cycles: the homology class of a cycle goes to the class of the cocycle it is. -/
theorem homologyπ_gradedCohomologyIso_hom' (M : RightModule.{v} C) (X : C.Obj) (n : ℤ) :
    (M.cochainComplex X).homologyπ n ≫ (gradedCohomologyIso M X n).hom =
      (gradedCyclesIso M X n).hom ≫ ModuleCat.ofHom (gradedBoundaries M X n).mkQ :=
  (homologyπ_gradedCohomologyIso_hom M X n).trans (Category.assoc _ _ _).symm

/-! ### The identification is natural in the module -/

variable {M N : (rightModuleCategory.{v} C).K}

/-- **The identification of the cycles with the cocycles is natural in the module.** Both sides
are the morphism applied to the underlying element of a cycle, by
`HomologicalComplex.cyclesMap_i`. -/
theorem cyclesMap_gradedCyclesIso_hom (ψ : (rightModuleCategory.{v} C).Cocycle M N) (X : C.Obj)
    (n : ℤ) :
    HomologicalComplex.cyclesMap (cochainMap ψ X) n ≫ (gradedCyclesIso N X n).hom =
      (gradedCyclesIso M X n).hom ≫ ModuleCat.ofHom (gradedCocyclesMapOf ψ X n) := by
  have h := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i (cochainMap ψ X) n)
  ext z
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h ⊢
  exact (gradedCyclesIso_hom_val N X n _).trans ((h z).trans
    (congrArg (fun a : M.obj X n => app ψ.1 (add_zero n) a)
      (gradedCyclesIso_hom_val M X n z)).symm)

/-- **The identification of the homology with the explicit cohomology is natural in the
module.** `HomologicalComplex.homologyMap` of the map of complexes attached to a closed
degree-zero morphism corresponds to the elementary map
`DGCategory.RightModule.gradedCohomologyMapOf`.

`HomologicalComplex.homologyπ` is epi, so this follows from the cycles-level statement
`DGCategory.RightModule.cyclesMap_gradedCyclesIso_hom`. -/
theorem homologyMap_cochainMap_gradedCohomologyIso_hom
    (ψ : (rightModuleCategory.{v} C).Cocycle M N) (X : C.Obj) (n : ℤ) :
    HomologicalComplex.homologyMap (cochainMap ψ X) n ≫ (gradedCohomologyIso N X n).hom =
      (gradedCohomologyIso M X n).hom ≫ ModuleCat.ofHom (gradedCohomologyMapOf ψ X n) := by
  refine (cancel_epi ((cochainComplex (C := C) M X).homologyπ n)).1 ?_
  rw [← Category.assoc, HomologicalComplex.homologyπ_naturality, Category.assoc,
    homologyπ_gradedCohomologyIso_hom']
  erw [← Category.assoc, cyclesMap_gradedCyclesIso_hom]
  erw [Category.assoc, ← Category.assoc _ (gradedCohomologyIso M X n).hom,
    homologyπ_gradedCohomologyIso_hom', Category.assoc]

/-! ### The map induced by a morphism of the homotopy category -/

/-- **The degree-`n` homology of `M X`, taken in the homotopy category of complexes of
`R`-modules, is the explicit cohomology.** This is the tail of
`DGCategory.RightModule.derivedForgetGradedCohomologyIso`, isolated so that the map a morphism of
`K(Mod^dg(C))` induces on the explicit cohomology can be defined by conjugating it. -/
def gradedCohomologyIsoK (M : (rightModuleCategory.{v} C).K) (X : C.Obj) (n : ℤ) :
    (HomotopyCategory.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) n).obj
        ((cochainComplexOnK.{v} X).obj M) ≅ ModuleCat.of R (gradedCohomology M X n) :=
  (HomotopyCategory.homologyFunctorFactors (ModuleCat.{v} R) (ComplexShape.up ℤ) n).app
      (cochainComplex (C := C) M X) ≪≫ gradedCohomologyIso M X n

/-- **The map induced on the explicit cohomology of `M X` by a morphism of `K(Mod^dg(C))`.** It
is the map induced on the degree-`n` homology of the complex `M X` by the functoriality of
evaluation on homotopy categories, read through
`DGCategory.RightModule.gradedCohomologyIsoK`.

Unlike `DGCategory.RightModule.gradedCohomologyMapOf` this takes a homotopy class, which is the
form in which the unit of the reflector of steps 1 and 2 of [Stacks, Tag 09LK] arrives. -/
def gradedCohomologyMapK (u : M ⟶ N) (X : C.Obj) (n : ℤ) :
    ModuleCat.of R (gradedCohomology M X n) ⟶ ModuleCat.of R (gradedCohomology N X n) :=
  (gradedCohomologyIsoK M X n).inv ≫
    (HomotopyCategory.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) n).map
        ((cochainComplexOnK.{v} X).map u) ≫
      (gradedCohomologyIsoK N X n).hom

/-- The forward direction of `DGCategory.RightModule.gradedCohomologyIsoK`, written out. -/
theorem gradedCohomologyIsoK_hom (M : (rightModuleCategory.{v} C).K) (X : C.Obj) (n : ℤ) :
    (gradedCohomologyIsoK M X n).hom =
      (HomotopyCategory.homologyFunctorFactors (ModuleCat.{v} R) (ComplexShape.up ℤ) n).hom.app
          (cochainComplex (C := C) M X) ≫
        (gradedCohomologyIso M X n).hom := rfl

/-- The defining square of `DGCategory.RightModule.gradedCohomologyMapK`: it is the map on
homology of the homotopy category, conjugated. -/
theorem gradedCohomologyIsoK_hom_naturality (u : M ⟶ N) (X : C.Obj) (n : ℤ) :
    (HomotopyCategory.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) n).map
          ((cochainComplexOnK.{v} X).map u) ≫ (gradedCohomologyIsoK N X n).hom =
      (gradedCohomologyIsoK M X n).hom ≫ gradedCohomologyMapK u X n := by
  rw [gradedCohomologyMapK, Iso.hom_inv_id_assoc]

/-- **The map induced by a homotopy class is the elementary map of a representative.** So
`DGCategory.RightModule.gradedCohomologyMapK` is computed on the class of a cocycle by
`DGCategory.RightModule.gradedCohomologyMapOf_mk`, and in particular the elementary map does not
depend on the representative. -/
@[simp] theorem gradedCohomologyMapK_mk (ψ : (rightModuleCategory.{v} C).Cocycle M N) (X : C.Obj)
    (n : ℤ) :
    gradedCohomologyMapK (Quotient.mk _ ψ : M ⟶ N) X n =
      ModuleCat.ofHom (gradedCohomologyMapOf ψ X n) := by
  have hnat : (HomotopyCategory.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) n).map
          ((cochainComplexOnK.{v} X).map (Quotient.mk _ ψ : M ⟶ N)) ≫
        (HomotopyCategory.homologyFunctorFactors (ModuleCat.{v} R)
            (ComplexShape.up ℤ) n).hom.app (cochainComplex (C := C) N X) =
      (HomotopyCategory.homologyFunctorFactors (ModuleCat.{v} R)
            (ComplexShape.up ℤ) n).hom.app (cochainComplex (C := C) M X) ≫
        HomologicalComplex.homologyMap (cochainMap ψ X) n :=
    (HomotopyCategory.homologyFunctorFactors (ModuleCat.{v} R)
      (ComplexShape.up ℤ) n).hom.naturality (cochainMap ψ X)
  refine (Iso.cancel_iso_hom_left (gradedCohomologyIsoK M X n) _ _).1 ?_
  refine (gradedCohomologyIsoK_hom_naturality (Quotient.mk _ ψ : M ⟶ N) X n).symm.trans ?_
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ (gradedCohomologyIso N X n).hom) hnat).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun z => (HomotopyCategory.homologyFunctorFactors (ModuleCat.{v} R)
              (ComplexShape.up ℤ) n).hom.app (cochainComplex (C := C) M X) ≫ z)
            (homologyMap_cochainMap_gradedCohomologyIso_hom ψ X n)).trans
          (Category.assoc _ _ _).symm)))

/-! ### The first link, with the induced map of a homotopy class -/

/-- **The first link of [Stacks, Tag 09LK] is natural in the module variable**, with the
naturality expressed by the map that a morphism of `K(Mod^dg(C))` induces on the explicit
cohomology. This is `DGCategory.RightModule.homShiftEquivGradedCohomology_comp` with no
representative chosen. -/
theorem homShiftEquivGradedCohomology_compK (u : M ⟶ N) (X : C.Obj) (n : ℤ)
    (g : yonedaObjK X ⟶ M⟦n⟧) :
    homShiftEquivGradedCohomology N X n
        (g ≫ (shiftFunctor (rightModuleCategory.{v} C).K n).map u) =
      gradedCohomologyMapK u X n (homShiftEquivGradedCohomology M X n g) := by
  refine Quotient.inductionOn u fun ψ => ?_
  rw [gradedCohomologyMapK_mk]
  exact homShiftEquivGradedCohomology_comp ψ X n g

/-- **The first link in the form the chain uses is natural in the module variable**, with the
induced map of a homotopy class. -/
theorem homShiftEquivEvaluationGradedCohomology_compK (u : M ⟶ N) (K : C.Obj)
    (e : (endDGCategory C K).Obj) (n : ℤ) (g : yonedaObjK K ⟶ M⟦n⟧) :
    homShiftEquivEvaluationGradedCohomology N K e n
        (g ≫ (shiftFunctor (rightModuleCategory.{v} C).K n).map u) =
      gradedCohomologyMapK u K n (homShiftEquivEvaluationGradedCohomology M K e n g) :=
  homShiftEquivGradedCohomology_compK u K n g

end RightModule

end DGCategory

end
