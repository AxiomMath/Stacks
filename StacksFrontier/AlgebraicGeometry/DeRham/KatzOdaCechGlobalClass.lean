module

public import StacksFrontier.AlgebraicGeometry.DeRham.KatzOdaCechCup
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.PullbackGlobalClass

/-!
# The elementwise Čech cochain of a global form

Let `p : X ⟶ S` be a morphism of schemes and `U` an open covering of `X`. A global section `s` of
`Ω^n_{X/S}` gives the Čech `0`-cochain `t ↦ s|_{U_t}` of the elementwise total Čech complex
`Tot(Č(U, Ω^•_{X/S}))`. Under the comparison with the library's total Čech complex it is the
augmentation of [Stacks, Tag 07M9] applied to `s`.

## Main definitions

* `AlgebraicGeometry.DeRhamKatzOdaCech.restrictTot`: the cochain `t ↦ s|_{U_t}` in Čech degree `0`.

## Main results

* `AlgebraicGeometry.DeRhamKatzOdaCech.cechIso_hom_restrictTot`: the comparison with the
  augmentation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.CategoryTheory.CechComplex
open Stacks.Cohomology.CechSheaf (SectionRing coverObject sectionsPresheafFunctor)
open Stacks.Cech.Hypercohomology (cocycleClass toMor)
open Stacks.Cohomology.Leray (sectionsFunctor)

universe u

namespace AlgebraicGeometry.DeRhamKatzOdaCech

variable {X S : Scheme.{u}} (p : X ⟶ S) {ι : Type u} (U : ι → X.Opens) (hU : ⊤ = ⨆ i, U i)

/-- The Čech `0`-cochain `t ↦ s|_{U_t}` of a section `s` over `X` of a presheaf on the opens. -/
def restrictCochain {R : Type u} [Ring R] (F : (X.Opens)ᵒᵖ ⥤ ModuleCat.{u} R) (s : F.obj (op ⊤)) :
    Cochain U F 0 :=
  fun t => (F.map (homOfLE (le_top : inter U t ≤ ⊤)).op).hom s

/-- **The elementwise total Čech cochain of a global form** `s` of degree `n`: the cochain
`t ↦ s|_{U_t}` placed in Čech degree `0`. -/
def restrictTot (n : ℕ) (s : (p.sectionsDeRhamComplex.X n).obj (op ⊤)) :
    TotX U p.sectionsDeRhamComplex (n : ℤ) :=
  totSingle U p.sectionsDeRhamComplex (n : ℤ) 0 n (by simp)
    (restrictCochain U (p.sectionsDeRhamComplex.X n) s)

/-- A global form, read as a global section of the term of degree `n` of the `ℤ`-indexed de Rham
complex. -/
def globalExtend (n : ℕ) (s : (p.sectionsDeRhamComplex.X n).obj (op ⊤)) :
    (SheafOfModules.evaluation.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (baseSheaf p))
      (op ⊤)).obj ((deRhamPlus p).obj.X (n : ℤ)) :=
  ((SheafOfModules.evaluation.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (baseSheaf p)) (op ⊤)).map
    ((SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p))).extendXIso
        ComplexShape.embeddingUpNat rfl).inv).hom s

attribute [local instance high] baseSectionCommRing in
/-- **The elementwise cochain of a global form is the augmentation** ([Stacks, Tag 07M9]): under
the comparison `cechIso` of the elementwise total Čech complex with the library's, the cochain
`t ↦ s|_{U_t}` is the image of `s` under `Γ(X, Ω^•_{X/S}) ⟶ Tot(Č(U, Ω^•_{X/S}))`. -/
theorem cechIso_hom_restrictTot (n : ℕ) (s : (p.sectionsDeRhamComplex.X n).obj (op ⊤)) :
    ((cechIso p U hU).hom.f n).hom (restrictTot p U n s) =
      (((Stacks.Cech.Linear.sectionsToTotalCech X.carrier
        (Stacks.SheafOfModules.Tensor.ringSheaf (baseSheaf p)) ⊤ U hU).app
          (deRhamPlus p).obj).f n).hom (globalExtend p n s) := by
  refine (cechIso_hom_f_apply p U hU (n : ℤ) _).trans ?_
  rw [restrictTot, sliceTot_totSingle, totalFrom_totSingle]
  have key : (Stacks.Cech.LinearCupProduct.cechCochainsMap (coverObject U hU)
      (SectionRing (Stacks.SheafOfModules.Tensor.ringSheaf (baseSheaf p)) ⊤)
      (sliceExtendXIso p n).inv 0).hom
      ((cochainsIso (coverObject U hU) ((sliceDeRhamComplex p).X n) 0).inv.hom
        (sliceCochain p U hU n 0 (restrictCochain U (p.sectionsDeRhamComplex.X n) s))) =
      (Stacks.Cohomology.CechDerived.cechDegreeZeroRestriction
        (Stacks.SheafOfModules.Tensor.ringSheaf (baseSheaf p)) ⊤ U hU
        ((deRhamPlus p).obj.X n)).hom (globalExtend p n s) := by
    have hinj : Function.Injective (cochainsIso (coverObject U hU)
        ((sliceDeRhamComplexInt p).X n) 0).hom :=
      (ModuleCat.mono_iff_injective _).1 inferInstance
    refine hinj (funext fun t => ?_)
    refine (cochainsIso_hom_apply _ _ 0 _ t).trans
      (Eq.trans ?_ (cochainsIso_hom_apply _ _ 0 _ t).symm)
    refine (ConcreteCategory.congr_hom (Stacks.Cech.LinearCupProduct.cechCochainsMap_comp_π
      (coverObject U hU) (SectionRing (Stacks.SheafOfModules.Tensor.ringSheaf (baseSheaf p)) ⊤)
      (sliceExtendXIso p n).inv 0 t)
      _).trans ?_
    refine Eq.trans ?_ (ConcreteCategory.congr_hom
      (Stacks.Cohomology.CechDerived.cechDegreeZeroRestriction_comp_π
        (Stacks.SheafOfModules.Tensor.ringSheaf (baseSheaf p))
        ⊤ U hU ((deRhamPlus p).obj.X n) t) (globalExtend p n s)).symm
    rw [ConcreteCategory.comp_apply, π_cochainsIso_inv_apply]
    have hn := ConcreteCategory.congr_hom
      (((SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p))).extendXIso
          ComplexShape.embeddingUpNat (rfl : ((n : ℕ) : ℤ) = n)).inv.val.naturality
        (Over.mkIdTerminal.from (inter (coverObject U hU) t)).left.op) s
    refine Eq.trans (congrArg _ ?_) hn
    exact (ConcreteCategory.congr_hom ((p.sectionsDeRhamComplex.X n).map_comp
      (homOfLE (le_top : inter U t ≤ ⊤)).op
      (homOfLE (le_of_eq (interOver_left_eq U (fun _ => le_top) t))).op).symm s).trans rfl
  rw [key]
  rfl

/-- The complex of global sections of the `ℤ`-indexed de Rham complex. -/
abbrev globalSectionsComplex :=
  (Stacks.Cech.Linear.sectionsComplexFunctor X.carrier
    (Stacks.SheafOfModules.Tensor.ringSheaf (baseSheaf p)) ⊤).obj
    (deRhamPlus p).obj

/-- The augmentation `Γ(X, Ω^•_{X/S}) ⟶ Tot(Č(U, Ω^•_{X/S}))`. -/
abbrev augmentation :=
  (Stacks.Cech.Linear.sectionsToTotalCech X.carrier
    (Stacks.SheafOfModules.Tensor.ringSheaf (baseSheaf p)) ⊤ U hU).app
    (deRhamPlus p).obj

include hU in
/-- **The elementwise cochain of a closed global form is a cocycle.** -/
theorem restrictTot_cocycle (n : ℕ) (s : (p.sectionsDeRhamComplex.X n).obj (op ⊤))
    (hs : ((globalSectionsComplex p).d n (n + 1)).hom (globalExtend p n s) = 0) :
    ((cechTot U p.sectionsDeRhamComplex).d n (n + 1)).hom (restrictTot p U n s) = 0 := by
  have hinj : Function.Injective ((cechIso p U hU).hom.f (n + 1)).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  refine hinj ((Θ_d p U hU n _).symm.trans ?_)
  rw [map_zero]
  refine (congrArg _ (cechIso_hom_restrictTot p U hU n s)).trans ?_
  have hc := ConcreteCategory.congr_hom ((augmentation p U hU).comm n (n + 1)) (globalExtend p n s)
  refine (restrictScalars_d_apply (baseRingHom p) (cechDeRham p U hU) n (n + 1) _).trans
    (hc.trans ?_)
  change ((augmentation p U hU).f (n + 1)).hom (((globalSectionsComplex p).d n (n + 1)).hom
    (globalExtend p n s)) = 0
  rw [hs, map_zero]

/-- The cocycle of global sections of the `ℤ`-indexed de Rham complex given by a closed global
form. -/
def globalCycle (n : ℕ) (s : (p.sectionsDeRhamComplex.X n).obj (op ⊤))
    (hs : ((globalSectionsComplex p).d n (n + 1)).hom (globalExtend p n s) = 0) :
    (globalSectionsComplex p).cycles n :=
  ((globalSectionsComplex p).liftCycles (toMor (globalExtend p n s)) (n + 1) (by simp)
    (toMor_comp_d_eq_zero _ hs)).hom 1

/-- The inclusion of cycles sends `globalCycle p n s hs` to the global form
`globalExtend p n s`. -/
theorem iCycles_globalCycle (n : ℕ) (s : (p.sectionsDeRhamComplex.X n).obj (op ⊤))
    (hs : ((globalSectionsComplex p).d n (n + 1)).hom (globalExtend p n s) = 0) :
    ((globalSectionsComplex p).iCycles n).hom (globalCycle p n s hs) = globalExtend p n s :=
  (ConcreteCategory.congr_hom ((globalSectionsComplex p).liftCycles_i _ _ _ _) 1).trans
    (Stacks.Cech.Hypercohomology.toMor_apply_one _)

/-- **The class of the elementwise cochain of a closed global form**: in `H^n_{dR}(X/S)` it is,
through the comparison of the two realizations ([Stacks, Tag 01F1]), the class of the form in the
hypercohomology of the underlying complex of abelian sheaves. -/
theorem classMap_restrictTot (n : ℕ) (s : (p.sectionsDeRhamComplex.X n).obj (op ⊤))
    (hs : ((globalSectionsComplex p).d n (n + 1)).hom (globalExtend p n s) = 0)
    (sA : ((sectionsFunctor X.carrier ⊤).mapCochainComplexPlus.obj
      ((_root_.SheafOfModules.toSheaf (structureSheafRing
        (SheafOfModules.baseRingedSpace (baseSheaf p)))).mapCochainComplexPlus.obj
          (deRhamPlus p))).obj.cycles n)
    (h : (((sectionsFunctor X.carrier ⊤).mapCochainComplexPlus.obj
      ((_root_.SheafOfModules.toSheaf (structureSheafRing
        (SheafOfModules.baseRingedSpace (baseSheaf p)))).mapCochainComplexPlus.obj
          (deRhamPlus p))).obj.iCycles n).hom sA = globalExtend p n s) :
    (classMap p U hU n).hom ((cocycleClass n (toMor (restrictTot p U n s))
        (toMor_comp_d_eq_zero _ (restrictTot_cocycle p U hU n s hs))).hom 1) =
      (Stacks.Cech.Hypercohomology.realizationUnbounded
        (SheafOfModules.baseRingedSpace (baseSheaf p)) (deRhamPlus p) n).hom.hom
        (Stacks.Cech.Hypercohomology.abelianGlobalClass _ n sA) := by
  refine Eq.trans ?_
    (Stacks.Cech.Hypercohomology.realizationUnbounded_abelianGlobalClass_eq_cechClass
      (SheafOfModules.baseRingedSpace (baseSheaf p)) U hU (deRhamPlus p) n sA
      (globalCycle p n s hs) (h.trans (iCycles_globalCycle p n s hs).symm)).symm
  rw [classMap_cocycleClass p U hU n _ (restrictTot_cocycle p U hU n s hs)]
  have e := Stacks.Cech.Hypercohomology.cocycleClass_comp_homologyMap (augmentation p U hU) n
    (toMor (globalExtend p n s)) (toMor_comp_d_eq_zero _ hs)
  have hxeq : toMor (Θ p U hU n (restrictTot p U n s)) =
      toMor (globalExtend p n s) ≫ (augmentation p U hU).f n :=
    (congrArg (toMor (M := (cechDeRham p U hU).X n)) (cechIso_hom_restrictTot p U hU n s)).trans
      (Stacks.Cech.Hypercohomology.toMor_comp (globalExtend p n s)
        ((augmentation p U hU).f n)).symm
  have e2 : ∀ hx, cocycleClass n (toMor (Θ p U hU n (restrictTot p U n s))) hx =
      cocycleClass n (toMor (globalExtend p n s)) (toMor_comp_d_eq_zero _ hs) ≫
        HomologicalComplex.homologyMap (augmentation p U hU) n :=
    fun hx => (Stacks.Cech.Hypercohomology.cocycleClass_congr n hxeq hx _).trans e.symm
  rw [e2]
  rfl

/-- **The class of the elementwise cochain of a closed global form, in the abelian realization**:
`classMap` of the cochain `t ↦ s|_{U_t}` is the comparison of the two realizations
([Stacks, Tag 01F1]) applied to the class of the global cocycle `s` of the de Rham complex of
abelian sheaves. -/
theorem classMap_restrictTot_eq (n : ℕ) (s : (p.sectionsDeRhamComplex.X n).obj (op ⊤))
    (hs : ((globalSectionsComplex p).d n (n + 1)).hom (globalExtend p n s) = 0)
    (sA : ((sectionsFunctor X.carrier ⊤).mapCochainComplexPlus.obj
      (SheafOfModules.deRhamAbelianComplexPlus (Scheme.Hom.deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)))).obj.cycles n)
    (h : (((sectionsFunctor X.carrier ⊤).mapCochainComplexPlus.obj
      ((_root_.SheafOfModules.toSheaf (structureSheafRing
        (SheafOfModules.baseRingedSpace (baseSheaf p)))).mapCochainComplexPlus.obj
          (deRhamPlus p))).obj.iCycles n).hom (HomologicalComplex.cyclesMap
        ((sectionsFunctor X.carrier ⊤).mapCochainComplexPlus.map
          (SheafOfModules.deRhamAbelianComplexPlusIso (Scheme.Hom.deRhamAlgebras p)
            (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p))).hom).hom n sA) =
        globalExtend p n s) :
    (classMap p U hU n).hom ((cocycleClass n (toMor (restrictTot p U n s))
        (toMor_comp_d_eq_zero _ (restrictTot_cocycle p U hU n s hs))).hom 1) =
      (SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology (Scheme.Hom.deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)) n).hom.hom
        (Stacks.Cech.Hypercohomology.abelianGlobalClass _ n sA) :=
  (classMap_restrictTot p U hU n s hs _ h).trans
    (SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology_abelianGlobalClass _ _ n sA).symm

end AlgebraicGeometry.DeRhamKatzOdaCech

end
