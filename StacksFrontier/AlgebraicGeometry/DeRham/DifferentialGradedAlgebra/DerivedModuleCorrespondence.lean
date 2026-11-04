module

public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.ClassToDerivedMorphism
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedCohomologyDerivedHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedQuasiIsomorphisms
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.RealizationShift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.FromTheStructureSheaf
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedGlobalCupProduct.UnitEvaluation
import StacksCore.Tactic.StacksAttribute

/-!
# The morphism `Ω^• ⟶ Ω^•[n]` attached to a de Rham class

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a ringed space `X` (for a
morphism of schemes `f : X ⟶ S`, `A = f^{-1}𝒪_S`), and let `Ω^•` be the relative de Rham complex,
a sheaf of differential graded `A`-algebras (Tag 0FU6). Differential Graded Sheaves, Section 0FU3
attaches to `ξ ∈ H^n_{dR}` a morphism

`ξ' : Ω^• ⟶ Ω^•[n]`

of `D(A)`, characterized by (1) it lifts to the derived category `D(Ω^•, d)` of right
differential graded `Ω^•`-modules, and (2) `ξ'(1) = ξ` in `H^0(X, Ω^•[n]) = H^n_{dR}`
(Remark 0FU7). This file constructs that correspondence, with no parameter: the derived category
`D(Ω^•, d)`, the forgetful functor to `D(A)`, the evaluation at the unit, and the identification
`H^n_{dR} ≃ Hom_{D(Ω^•, d)}(Ω^•, Ω^•[n])`, which comes from Tag 0FTX.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.derivedForgetShiftedHom`: a morphism `M ⟶ M[n]` of
  `D(A, d)` with its action forgotten, through
  `SheafOfModules.DifferentialGradedModule.derivedForget`.
* `AlgebraicGeometry.SheafOfModules.structureSheafOneClass`: the unit `1 ∈ H^0(X, A)`.
* `AlgebraicGeometry.SheafOfModules.deRhamForgetHom`: forgetting the differential graded
  structure of a morphism `Ω^• ⟶ Ω^•[n]` of `D(Ω^•, d)`.
* `AlgebraicGeometry.SheafOfModules.deRhamOneClass`: the unit `1 ∈ H^0_{dR}`.
* `AlgebraicGeometry.SheafOfModules.deRhamShiftHomologyIso`: `H^m(X, Ω^•[n]) ≅ H^{n + m}_{dR}`.
* `AlgebraicGeometry.SheafOfModules.deRhamEvalOne`: the value `f(1) ∈ H^n_{dR}` of a morphism
  `f : Ω^• ⟶ Ω^•[n]` of `D(A)`.
* `AlgebraicGeometry.SheafOfModules.deRhamClassDerivedEquiv`: **the identification
  `H^n_{dR} ≃ Hom_{D(Ω^•, d)}(Ω^•, Ω^•[n])` of Section 0FU3.**
* `AlgebraicGeometry.SheafOfModules.deRhamClassMorphism`: **the morphism `ξ'` of Tag 0FU7.**

## Main results

* `SheafOfModules.DifferentialGradedModule.forgetUnitHom_cohomologyAddEquivDerivedHom`: the
  normalization of Section 0FU3 for an arbitrary sheaf of differential graded algebras on a ringed
  site and an arbitrary right differential graded module: Tag 0FTX followed by forgetting and
  precomposing with the unit is the identification `H^n(C, M) = Hom_{D(O)}(O, M[n])`.
* `AlgebraicGeometry.SheafOfModules.deRhamEvalOne_deRhamForgetHom_bijective`: forgetting and
  evaluating at the unit is a bijection `Hom_{D(Ω^•, d)}(Ω^•, Ω^•[n]) ⟶ H^n_{dR}`.
* `AlgebraicGeometry.SheafOfModules.exists_lift_deRhamClassMorphism`,
  `AlgebraicGeometry.SheafOfModules.deRhamEvalOne_deRhamClassMorphism`,
  `AlgebraicGeometry.SheafOfModules.existsUnique_deRhamClassMorphism`: properties (1) and (2) of
  Tag 0FU7, and that they characterize `ξ'`.

## Implementation notes

The value at the unit is the literal one: `f(1)` is the image of `1 ∈ H^0_{dR}` under the map
`H^0(X, Ω^•) ⟶ H^0(X, Ω^•[n])` which `f` induces on `RΓ(X, -) = derivedSectionsBase A`, read in
`H^n_{dR}` through the commutation of `RΓ` and of cohomology with the translations. The unit
`1 ∈ H^0(X, A)` is the class of the global section `1`
(`Stacks.Cohomology.DerivedGlobalCupProduct.unitCycleClass`), and `1 ∈ H^0_{dR}` is its image
under the unit `A ⟶ Ω^•`, the class of the global section `1` of `Ω^0`
(`AlgebraicGeometry.SheafOfModules.deRhamOneClass_eq_globalClass_one`).

The source reads `ξ'(1) = ξ` off Tag 0FTX. Here the bijectivity of `g ↦ g(1)` is proved, and the
identification of Section 0FU3 is its inverse: forgetting and precomposing with the unit inverts
Tag 0FTX up to the identification `H^n(C, M) = Hom_{D(O)}(O, M[n])`
(`forgetUnitHom_cohomologyAddEquivDerivedHom`), and evaluation at `1` is a bijection
(`Stacks.Cohomology.DerivedGlobalCupProduct.evalUnit_bijective`). Both `ξ'` and the uniqueness
follow.

The translation functors of the homotopy category and of the derived category of right
differential graded modules are available over a ringed *site*; the ringed space `X` with the base
ring sheaf `A` is read as one through `Stacks.SheafOfModules.opensRingedSite`, here
`AlgebraicGeometry.SheafOfModules.baseSite`.

## References

* [Stacks Project, Tag 0FU7](https://stacks.math.columbia.edu/tag/0FU7)
* [Stacks Project, Section 0FU3](https://stacks.math.columbia.edu/tag/0FU3)
* [Stacks Project, Tag 0FTX](https://stacks.math.columbia.edu/tag/0FTX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf Opposite TopologicalSpace

universe u

namespace SheafOfModules.DifferentialGradedModule

open DifferentialGradedAlgebra

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  (A : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  (M : DifferentialGradedModule.{u, u, u} A)

/-- The unit `O ⟶ A` of a sheaf of differential graded algebras, as a morphism of complexes of
modules over the ring sheaf of the ringed site. -/
noncomputable def unitComplexRingHom :
    AlgebraicGeometry.RingedSite.structureSheafComplex X ⟶ A.complex :=
  unitAlgebraComplexHom (A := (A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)))

/-- A morphism `A ⟶ M[n]` of `D(A, d)`, with its differential graded structure forgotten and
precomposed with the unit `O ⟶ A`: a morphism `O ⟶ M[n]` of `D(O)`. -/
noncomputable def forgetUnitHom (n : ℤ)
    (g : (toDerivedCategory.{u, u, u} A).obj ((HomotopyCategory.quotient A).obj (regularModule A)) ⟶
        ((toDerivedCategory.{u, u, u} A).obj ((HomotopyCategory.quotient A).obj M))⟦n⟧) :
    DerivedCategory.Q.obj (AlgebraicGeometry.RingedSite.structureSheafComplex X) ⟶
      DerivedCategory.Q.obj (M.complex⟦n⟧) :=
  DerivedCategory.Q.map (unitComplexRingHom A) ≫
    (derivedForget A).map
      (g ≫ ((toDerivedCategory.{u, u, u} A).commShiftIso n).inv.app
        ((HomotopyCategory.quotient A).obj M)) ≫
    eqToHom (congrArg DerivedCategory.Q.obj (HomotopyCategory.shiftFunctor_obj_complex A n M))

/-- Forgetting the action on the image in `D(A, d)` of a morphism of the homotopy category is
forgetting it on the homotopy category. -/
theorem derivedForget_map_toDerivedCategory_map {N N' : DifferentialGradedModule.{u, u, u} A}
    (f : (HomotopyCategory.quotient A).obj N ⟶ (HomotopyCategory.quotient A).obj N') :
    (derivedForget A).map ((toDerivedCategory.{u, u, u} A).map f) =
      (homotopyForget A).map f := by
  refine (Functor.congr_hom (toDerivedCategory_comp_derivedForget A) f).trans ?_
  show 𝟙 _ ≫ (homotopyForget A).map f ≫ 𝟙 _ = (homotopyForget A).map f
  rw [Category.id_comp, Category.comp_id]

private theorem Q_map_eq_of_Qh_map_quotient_map {C : Type*} [Category C]
    [Abelian C] [HasDerivedCategory C] {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (y : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L)
    (h : DerivedCategory.Qh.map ((_root_.HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f) =
      (((DerivedCategory.quotientCompQhIso C).app K).hom ≫ y) ≫
        ((DerivedCategory.quotientCompQhIso C).app L).inv) :
    DerivedCategory.Q.map f = y := by
  have key := DerivedCategory.quotientCompQhIso_hom_naturality f
  rw [h] at key
  simpa using key.symm

private theorem forgetUnitHom_aux {I : DifferentialGradedModule.{u, u, u} A} (n : ℤ)
    (b : shiftedModule A M n ⟶ I) (hb : QuasiIso b.toHomologicalComplex)
    (y : DerivedCategory.Q.obj (AlgebraicGeometry.RingedSite.structureSheafComplex X) ⟶
      DerivedCategory.Q.obj (M.complex⟦n⟧))
    (v : (HomotopyCategory.quotient A).obj (regularModule A) ⟶ (HomotopyCategory.quotient A).obj I)
    (hv : DerivedCategory.Qh.map (regularHomotopyHomAddEquiv
        (A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)) I v) =
      (((DerivedCategory.quotientCompQhIso _).app _).symm.symm.hom ≫
        (((Iso.refl _).symm.hom ≫ y) ≫ (eqToIso (congrArg DerivedCategory.Q.obj
          (HomotopyCategory.shiftFunctor_obj_complex A n M).symm) ≪≫
          asIso (DerivedCategory.Q.map b.toHomologicalComplex)).hom)) ≫
        ((DerivedCategory.quotientCompQhIso _).app _).symm.hom) :
    forgetUnitHom A M n (((Iso.refl _).symm.hom ≫
      ((toDerivedCategory.{u, u, u} A).map v ≫ (toDerivedCategoryIso b hb).inv)) ≫
      (((toDerivedCategory.{u, u, u} A).commShiftIso n).app
        ((HomotopyCategory.quotient A).obj M)).hom) = y := by
  show forgetUnitHom A M n ((𝟙 _ ≫
      ((toDerivedCategory.{u, u, u} A).map v ≫ (toDerivedCategoryIso b hb).inv)) ≫
      (((toDerivedCategory.{u, u, u} A).commShiftIso n).app
        ((HomotopyCategory.quotient A).obj M)).hom) = y
  rw [Category.id_comp]
  have : IsIso (DerivedCategory.Q.map b.toHomologicalComplex) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hb
  obtain ⟨G, rfl⟩ := (HomotopyCategory.quotient A).map_surjective v
  replace hv := (congrArg DerivedCategory.Qh.map (regularHomotopyHomAddEquiv_quotient_map
    (A := (A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O))) G).symm).trans hv
  let e := eqToHom (congrArg DerivedCategory.Q.obj
    (HomotopyCategory.shiftFunctor_obj_complex A n M).symm)
  change DerivedCategory.Qh.map ((_root_.HomotopyCategory.quotient
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)).map
      (unitComplexRingHom A ≫ G.toHomologicalComplex)) =
    (((DerivedCategory.quotientCompQhIso _).app
      (AlgebraicGeometry.RingedSite.structureSheafComplex X)).hom ≫
      ((𝟙 _ ≫ y) ≫ (e ≫ DerivedCategory.Q.map b.toHomologicalComplex))) ≫
      ((DerivedCategory.quotientCompQhIso _).app I.complex).inv at hv
  have hQ := Q_map_eq_of_Qh_map_quotient_map _ _ hv
  rw [Category.id_comp] at hQ
  have hhom : ((derivedForget A).mapIso (toDerivedCategoryIso b hb)).hom =
      DerivedCategory.Q.map b.toHomologicalComplex :=
    derivedForget_map_toDerivedCategory_map A _
  rw [← hhom] at hQ
  have hQ' := (DerivedCategory.Q.map_comp _ _).symm.trans hQ
  have h1 : (((toDerivedCategory.{u, u, u} A).map ((HomotopyCategory.quotient A).map G) ≫
        (toDerivedCategoryIso b hb).inv) ≫
      (((toDerivedCategory.{u, u, u} A).commShiftIso n).app
        ((HomotopyCategory.quotient A).obj M)).hom) ≫
      ((toDerivedCategory.{u, u, u} A).commShiftIso n).inv.app
        ((HomotopyCategory.quotient A).obj M) =
      (toDerivedCategory.{u, u, u} A).map ((HomotopyCategory.quotient A).map G) ≫
        (toDerivedCategoryIso b hb).inv := by
    rw [Category.assoc, Iso.app_hom, Iso.hom_inv_id_app]
    exact Category.comp_id _
  unfold forgetUnitHom
  rw [h1, Functor.map_comp, derivedForget_map_toDerivedCategory_map, homotopyForget_quotient_map]
  show _ ≫ (_ ≫ ((derivedForget A).mapIso (toDerivedCategoryIso b hb)).inv) ≫ _ = _
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) (Category.assoc _ _ _).symm).trans ?_
  refine (congrArg (fun t => (t ≫ _) ≫ _) hQ').trans ?_
  refine (congrArg (· ≫ _) ((Category.assoc _ _ _).trans (congrArg (y ≫ ·)
    ((Category.assoc _ _ _).trans ((congrArg (e ≫ ·) (Iso.hom_inv_id _)).trans
      (Category.comp_id _)))))).trans ?_
  exact (Category.assoc _ _ _).trans ((congrArg (y ≫ ·) (eqToHom_trans _ _)).trans
    (Category.comp_id _))

private theorem Qh_map_regularHomotopyHomAddEquiv_symm
    (A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O))
    (I : DifferentialGradedModule.{u, u, u} A)
    (h : Function.Bijective (DerivedCategory.Qh.mapAddHom :
      ((_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (unitComplex X.O) ⟶
        (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I.complex) →+ _))
    (z : DerivedCategory.Qh.obj ((_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (unitComplex X.O)) ⟶
      DerivedCategory.Qh.obj ((_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        I.complex)) :
    DerivedCategory.Qh.map (regularHomotopyHomAddEquiv A I
      ((regularHomotopyHomAddEquiv A I).symm ((AddEquiv.ofBijective _ h).symm z))) = z := by
  rw [AddEquiv.apply_symm_apply]
  exact AddEquiv.ofBijective_apply_symm_apply (f := DerivedCategory.Qh.mapAddHom) h

/-- **The normalization of Section 0FU3.** The morphism `A ⟶ M[n]` of `D(A, d)` which Tag 0FTX
attaches to `ξ ∈ H^n(C, M)`, with its differential graded structure forgotten and precomposed with
the unit `O ⟶ A`, is the morphism `O ⟶ M[n]` of `D(O)` which the cohomology class `ξ` is: in the
words of the source, `ξ` is the image of `1` under it. -/
theorem forgetUnitHom_cohomologyAddEquivDerivedHom (n : ℤ) (x : cohomology M n) :
    forgetUnitHom A M n (cohomologyAddEquivDerivedHom A M n x) =
      complexCohomologyAddEquiv M.complex n x := by
  unfold cohomologyAddEquivDerivedHom
  dsimp only
  apply forgetUnitHom_aux
  exact Qh_map_regularHomotopyHomAddEquiv_symm _ _ _ _

/-- Forgetting the action of `A`, on a morphism `M ⟶ M[n]` of `D(A, d)`: the morphism
`M ⟶ M[n]` of `D(O)` between the underlying complexes. -/
noncomputable def derivedForgetShiftedHom (n : ℤ)
    (g : (toDerivedCategory.{u, u, u} A).obj ((HomotopyCategory.quotient A).obj M) ⟶
        ((toDerivedCategory.{u, u, u} A).obj ((HomotopyCategory.quotient A).obj M))⟦n⟧) :
    DerivedCategory.Q.obj M.complex ⟶ (DerivedCategory.Q.obj M.complex)⟦n⟧ :=
  (derivedForget A).map
      (g ≫ ((toDerivedCategory.{u, u, u} A).commShiftIso n).inv.app
        ((HomotopyCategory.quotient A).obj M)) ≫
    eqToHom (congrArg DerivedCategory.Q.obj (HomotopyCategory.shiftFunctor_obj_complex A n M)) ≫
    (DerivedCategory.Q.commShiftIso n).hom.app M.complex

/-- Precomposing the forgotten morphism `A ⟶ A[n]` with the unit `O ⟶ A`. -/
theorem unitComplexRingHom_derivedForgetShiftedHom (n : ℤ)
    (g : (toDerivedCategory.{u, u, u} A).obj ((HomotopyCategory.quotient A).obj (regularModule A)) ⟶
        ((toDerivedCategory.{u, u, u} A).obj ((HomotopyCategory.quotient A).obj
          (regularModule A)))⟦n⟧) :
    DerivedCategory.Q.map (unitComplexRingHom A) ≫ derivedForgetShiftedHom A (regularModule A) n g =
      forgetUnitHom A (regularModule A) n g ≫
        (DerivedCategory.Q.commShiftIso n).hom.app (regularModule A).complex := by
  unfold derivedForgetShiftedHom forgetUnitHom
  exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))).symm

/-- **Forgetting the action and precomposing with the unit is a bijection** from the morphisms
`A ⟶ M[n]` of `D(A, d)` onto the morphisms `O ⟶ M[n]` of `D(O)`: by
`forgetUnitHom_cohomologyAddEquivDerivedHom`, it inverts the identification of Tag 0FTX up to the
identification of `H^n(C, M)` with morphisms `O ⟶ M[n]` of `D(O)`. -/
theorem forgetUnitHom_bijective (n : ℤ) : Function.Bijective (forgetUnitHom A M n) := by
  refine ⟨fun g g' h => ?_, fun y => ⟨cohomologyAddEquivDerivedHom A M n
    ((complexCohomologyAddEquiv M.complex n).symm y), ?_⟩⟩
  · obtain ⟨x, rfl⟩ := (cohomologyAddEquivDerivedHom A M n).surjective g
    obtain ⟨x', rfl⟩ := (cohomologyAddEquivDerivedHom A M n).surjective g'
    simp only [forgetUnitHom_cohomologyAddEquivDerivedHom] at h
    rw [(complexCohomologyAddEquiv M.complex n).injective h]
  · rw [forgetUnitHom_cohomologyAddEquivDerivedHom]
    exact AddEquiv.apply_symm_apply _ _

/-- **Forgetting the action of `A` on a morphism `A ⟶ A[n]` and precomposing with the unit
`O ⟶ A` is a bijection** onto the morphisms `O ⟶ A[n]` of `D(O)`. -/
theorem unitComplexRingHom_derivedForgetShiftedHom_bijective (n : ℤ) :
    Function.Bijective (fun g => DerivedCategory.Q.map (unitComplexRingHom A) ≫
      derivedForgetShiftedHom A (regularModule A) n g) := by
  have h₂ : Function.Bijective (fun t : DerivedCategory.Q.obj
      (AlgebraicGeometry.RingedSite.structureSheafComplex X) ⟶
        DerivedCategory.Q.obj ((regularModule A).complex⟦n⟧) =>
        t ≫ (DerivedCategory.Q.commShiftIso n).hom.app (regularModule A).complex) :=
    ⟨fun a b h => by simpa using congrArg (· ≫ (DerivedCategory.Q.commShiftIso n).inv.app
        (regularModule A).complex) h,
      fun y => ⟨y ≫ (DerivedCategory.Q.commShiftIso n).inv.app (regularModule A).complex,
        by simp⟩⟩
  convert h₂.comp (forgetUnitHom_bijective A (regularModule A) n) using 1
  exact funext (unitComplexRingHom_derivedForgetShiftedHom A n)

/-- The translation functors of `D(A, d)`, named so that they can be supplied for a sheaf of
differential graded algebras whose ringed site is not found by unification. -/
noncomputable abbrev derivedCategoryHasShift : HasShift (derivedCategory.{u, u, u} A) ℤ :=
  inferInstance

end SheafOfModules.DifferentialGradedModule

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-- The open subsets of `X`, with the base ring sheaf `A` as structure sheaf, as a ringed site. -/
noncomputable abbrev baseSite (A : TopCat.Sheaf CommRingCat.{u} X.carrier) :
    AlgebraicGeometry.RingedSite.{u, u, u} :=
  Stacks.SheafOfModules.opensRingedSite A

/-- **The class of the unit** `1 ∈ H^0(X, A)`: the class of the global section `1` of `A`, a
degree-zero global cocycle of `A[0]`. -/
noncomputable def structureSheafOneClass (A : TopCat.Sheaf CommRingCat.{u} X.carrier) :
    ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} ((underlyingRingSheaf A).obj.obj (op ⊤))) 0).obj
      ((derivedSectionsBase A).obj
        (AlgebraicGeometry.RingedSite.derivedStructureSheaf (baseSite A))) : Type u) :=
  Stacks.Cohomology.DerivedGlobalCupProduct.unitCycleClass (baseRingedSpace A) 0

/-- **The unit class is the class of the global section `1`.** -/
theorem structureSheafOneClass_eq_globalClass_one (A : TopCat.Sheaf CommRingCat.{u} X.carrier) :
    structureSheafOneClass A =
      Stacks.Cohomology.DerivedGlobalCupProduct.globalClass
        (Stacks.Cohomology.DerivedGlobalCupProduct.unitComplex (baseRingedSpace A) 0) 0
        (Stacks.Cohomology.DerivedGlobalCupProduct.unitCycle (baseRingedSpace A) 0) :=
  rfl

/-- The value `φ(1) ∈ H^0(X, Z)` at the unit of a morphism `φ : A ⟶ Z` of `D(A)`. -/
noncomputable def structureSheafEval (A : TopCat.Sheaf CommRingCat.{u} X.carrier)
    (Z : DerivedCategory (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (baseSite A).O)))
    (φ : AlgebraicGeometry.RingedSite.derivedStructureSheaf (baseSite A) ⟶ Z) :
    ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} ((underlyingRingSheaf A).obj.obj (op ⊤))) 0).obj
      ((derivedSectionsBase A).obj Z) : Type u) :=
  (DerivedCategory.homologyFunctor _ 0).map ((derivedSectionsBase A).map φ)
    (structureSheafOneClass A)

/-- `φ ↦ φ(1)` is a bijection from the morphisms `A ⟶ Z` of `D(A)` onto `H^0(X, Z)`: this is
`Stacks.Cohomology.DerivedGlobalCupProduct.evalUnit_bijective`. -/
theorem structureSheafEval_bijective (A : TopCat.Sheaf CommRingCat.{u} X.carrier)
    (Z : DerivedCategory (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (baseSite A).O))) :
    Function.Bijective (structureSheafEval A Z) :=
  Stacks.Cohomology.DerivedGlobalCupProduct.evalUnit_bijective (X := baseRingedSpace A) Z 0

/-! ### A sheaf of differential graded algebras over `(X, A)` -/

section Algebra

variable (𝒜 : _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u} (underlyingRingSheaf A))

/-- The complex underlying a sheaf of differential graded `A`-algebras, as an object of `D(A)`. -/
noncomputable abbrev dgaDerivedObject :
    DerivedCategory (_root_.SheafOfModules.{u} (underlyingRingSheaf A)) :=
  DerivedCategory.Q.obj 𝒜.complex

/-- A sheaf of differential graded `A`-algebras, as the regular right differential graded module
over itself, in the derived category `D(𝒜, d)`. -/
noncomputable abbrev dgaDerivedRegular :
    _root_.SheafOfModules.DifferentialGradedModule.derivedCategory.{u, u, u} 𝒜 :=
  (_root_.SheafOfModules.DifferentialGradedModule.toDerivedCategory _).obj
    ((_root_.SheafOfModules.DifferentialGradedModule.HomotopyCategory.quotient _).obj
      (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜))

/-- The cohomology `H^n(X, 𝒜)` of the complex underlying `𝒜`, as a module over `A(X)`. -/
noncomputable abbrev dgaCohomology (n : ℤ) :
    ModuleCat.{u} ((underlyingRingSheaf A).obj.obj (op ⊤)) :=
  (DerivedCategory.homologyFunctor _ n).obj ((derivedSectionsBase A).obj (dgaDerivedObject 𝒜))

/-- The translation functors of the derived category `D(𝒜, d)` of right differential graded
modules over `𝒜`. -/
noncomputable instance dgaDerivedHasShift :
    HasShift (_root_.SheafOfModules.DifferentialGradedModule.derivedCategory.{u, u, u}
      (𝒜)) ℤ :=
  _root_.SheafOfModules.DifferentialGradedModule.derivedCategoryHasShift (X := baseSite A)
    (𝒜)

/-- **Forgetting the differential graded module structure**: a morphism `𝒜 ⟶ 𝒜[n]` of the
derived category `D(𝒜, d)` of right differential graded `𝒜`-modules, read as a morphism
`𝒜 ⟶ 𝒜[n]` of `D(A)` through the forgetful functor
`SheafOfModules.DifferentialGradedModule.derivedForget` and its compatibility with the
translations. -/
noncomputable def dgaForgetHom (n : ℤ)
    (g : dgaDerivedRegular 𝒜 ⟶ (dgaDerivedRegular 𝒜)⟦n⟧) :
    dgaDerivedObject 𝒜 ⟶ (dgaDerivedObject 𝒜)⟦n⟧ :=
  _root_.SheafOfModules.DifferentialGradedModule.derivedForgetShiftedHom (X := baseSite A)
    (𝒜) ((_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜)) n g

/-- The unit `A ⟶ 𝒜`, `1 ↦ 1 ∈ Ω^0`, as a morphism of `D(A)`. -/
noncomputable def dgaUnitHom :
    AlgebraicGeometry.RingedSite.derivedStructureSheaf (baseSite A) ⟶ dgaDerivedObject 𝒜 :=
  DerivedCategory.Q.map (_root_.SheafOfModules.DifferentialGradedModule.unitComplexRingHom
    (X := baseSite A) (𝒜))

/-- **The unit `1 ∈ H^0(X, 𝒜)`**: the image of the unit class `1 ∈ H^0(X, A)` under the unit
`A ⟶ 𝒜`. -/
noncomputable def dgaOneClass : dgaCohomology 𝒜 0 :=
  (DerivedCategory.homologyFunctor _ 0).map ((derivedSectionsBase A).map (dgaUnitHom 𝒜))
    (structureSheafOneClass A)

/-- **The identification `H^m(X, 𝒜[n]) = H^{n + m}(X, 𝒜)`**, for `n + m = k`: the commutation of
`RΓ(X, -)` with the translations followed by that of cohomology. -/
noncomputable def dgaShiftHomologyIso (n m k : ℤ) (h : n + m = k) :
    (DerivedCategory.homologyFunctor _ m).obj
        ((derivedSectionsBase A).obj ((dgaDerivedObject 𝒜)⟦n⟧)) ≅
      dgaCohomology 𝒜 k :=
  Stacks.Cohomology.RealizationShift.shiftHomologyIsoU
    (Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen (baseRingedSpace A) ⊤)
    (dgaDerivedObject (X := X) (A := A) 𝒜) n m k h

/-- **The value at the unit** `f(1) ∈ H^0(X, 𝒜[n]) = H^n(X, 𝒜)` of a morphism
`f : 𝒜 ⟶ 𝒜[n]` of `D(A)`: the map `f` induces on `H^0(X, -)`, applied to `1 ∈ H^0(X, 𝒜)`. -/
noncomputable def dgaEvalOne (n : ℤ)
    (f : dgaDerivedObject 𝒜 ⟶ (dgaDerivedObject 𝒜)⟦n⟧) : dgaCohomology 𝒜 n :=
  (dgaShiftHomologyIso 𝒜 n 0 n (add_zero n)).hom
    ((DerivedCategory.homologyFunctor _ 0).map ((derivedSectionsBase A).map f)
      (dgaOneClass 𝒜))

/-- The global section `1` of `𝒜^0`, as a degree-zero global cocycle of `𝒜`: the image of the
cocycle `1` of `A[0]` under the unit `A[0] ⟶ 𝒜`. -/
noncomputable def dgaOneCycle :
    (Stacks.Cohomology.DerivedGlobalCupProduct.sectionsComplex (baseRingedSpace A)
      𝒜.complex).cycles 0 :=
  ConcreteCategory.hom (HomologicalComplex.cyclesMap
    (((Stacks.Cohomology.DerivedGlobalCupProduct.globalSections
      (baseRingedSpace A)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map
        (_root_.SheafOfModules.DifferentialGradedModule.unitComplexRingHom (X := baseSite A) 𝒜))
      0) (Stacks.Cohomology.DerivedGlobalCupProduct.unitCycle (baseRingedSpace A) 0)

/-- The cocycle `dgaOneCycle 𝒜` is the global section `1` of `𝒜^0`. -/
theorem iCycles_dgaOneCycle :
    ConcreteCategory.hom
        ((Stacks.Cohomology.DerivedGlobalCupProduct.sectionsComplex (baseRingedSpace A)
          𝒜.complex).iCycles 0) (dgaOneCycle 𝒜) = 𝒜.one.eval (op ⊤) := by
  refine (ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i
    (((Stacks.Cohomology.DerivedGlobalCupProduct.globalSections
      (baseRingedSpace A)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map
        (_root_.SheafOfModules.DifferentialGradedModule.unitComplexRingHom (X := baseSite A) 𝒜)) 0)
    (Stacks.Cohomology.DerivedGlobalCupProduct.unitCycle (baseRingedSpace A) 0)).trans ?_
  refine (ConcreteCategory.comp_apply _ _ _).trans ?_
  have hu := Stacks.Cohomology.DerivedGlobalCupProduct.iCycles_unitCycle (baseRingedSpace A) 0
  refine (congrArg (fun z => ConcreteCategory.hom
    ((((Stacks.Cohomology.DerivedGlobalCupProduct.globalSections
    (baseRingedSpace A)).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (_root_.SheafOfModules.DifferentialGradedModule.unitComplexRingHom
        (X := baseSite A) 𝒜)).f 0) z)
    hu).trans ?_
  refine (_root_.SheafOfModules.DifferentialGradedAlgebra.unitAlgebraHomF_app_zero
    (𝒜 : _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u}
      (CategoryTheory.Sheaf.toRingCat (Opens.grothendieckTopology X.carrier) A)) (op ⊤)
    (Stacks.Cohomology.DerivedGlobalCupProduct.unitSection (baseRingedSpace A) 0)).trans ?_
  have h1 : _root_.SheafOfModules.unitDGAlgebra.toScalar (Osharp := A) rfl (op ⊤)
      (Stacks.Cohomology.DerivedGlobalCupProduct.unitSection (baseRingedSpace A) 0) = 1 :=
    _root_.SheafOfModules.unitDGAlgebra.toScalar_ofScalar (Osharp := A) rfl (op ⊤) 1
  rw [h1, one_smul]

/-- **The unit `1 ∈ H^0(X, 𝒜)` is the class of the global section `1` of `𝒜^0`.** -/
theorem dgaOneClass_eq_globalClass_one :
    (dgaOneClass 𝒜 : _) = Stacks.Cohomology.DerivedGlobalCupProduct.globalClass
      (X := baseRingedSpace A) 𝒜.complex 0 (dgaOneCycle 𝒜) :=
  Stacks.Cohomology.DerivedGlobalCupProduct.globalClass_map (baseRingedSpace A)
    (_root_.SheafOfModules.DifferentialGradedModule.unitComplexRingHom (X := baseSite A) 𝒜) 0
    (Stacks.Cohomology.DerivedGlobalCupProduct.unitCycle (baseRingedSpace A) 0)

/-- The value at the unit of `f : 𝒜 ⟶ 𝒜[n]` is the value at the unit `1 ∈ H^0(X, A)` of the
composite `A ⟶ 𝒜 ⟶ 𝒜[n]`. -/
theorem dgaEvalOne_eq (n : ℤ)
    (f : dgaDerivedObject 𝒜 ⟶ (dgaDerivedObject 𝒜)⟦n⟧) :
    dgaEvalOne 𝒜 n f = (dgaShiftHomologyIso 𝒜 n 0 n (add_zero n)).hom
      (structureSheafEval A _ (dgaUnitHom 𝒜 ≫ f)) := by
  unfold dgaEvalOne dgaOneClass structureSheafEval
  refine congrArg _ ?_
  refine (ConcreteCategory.comp_apply _ _ _).symm.trans ?_
  exact ConcreteCategory.congr_hom ((Functor.map_comp _ _ _).symm.trans
      (congrArg (DerivedCategory.homologyFunctor _ 0).map
        ((derivedSectionsBase A).map_comp _ _).symm)) (structureSheafOneClass A)

/-- **Forgetting the differential graded structure and evaluating at the unit is a bijection**
`Hom_{D(𝒜, d)}(𝒜, 𝒜[n]) ⟶ H^n(X, 𝒜)`. It is the composite of the bijection of
`SheafOfModules.DifferentialGradedModule.unitComplexRingHom_derivedForgetShiftedHom_bijective`,
which rests on Tag 0FTX, with the identification
`Hom_{D(A)}(A, 𝒜[n]) = H^0(X, 𝒜[n]) = H^n(X, 𝒜)` of Stacks 08JA. -/
theorem dgaEvalOne_dgaForgetHom_bijective (n : ℤ) :
    Function.Bijective (fun g => dgaEvalOne 𝒜 n (dgaForgetHom 𝒜 n g)) := by
  have h₁ : Function.Bijective (fun g => dgaUnitHom 𝒜 ≫ dgaForgetHom 𝒜 n g) :=
    SheafOfModules.DifferentialGradedModule.unitComplexRingHom_derivedForgetShiftedHom_bijective
      (X := baseSite A) (𝒜) n
  have e : (fun g => dgaEvalOne 𝒜 n (dgaForgetHom 𝒜 n g)) =
      (ConcreteCategory.hom (dgaShiftHomologyIso 𝒜 n 0 n (add_zero n)).hom) ∘
        (structureSheafEval A ((dgaDerivedObject 𝒜)⟦n⟧)) ∘
          (fun g => dgaUnitHom 𝒜 ≫ dgaForgetHom 𝒜 n g) :=
    funext fun g => dgaEvalOne_eq 𝒜 n _
  rw [e]
  exact (ConcreteCategory.bijective_of_isIso (dgaShiftHomologyIso 𝒜 n 0 n (add_zero n)).hom).comp
    ((structureSheafEval_bijective A _).comp h₁)

/-- **The identification of Differential Graded Sheaves, Section 0FU3, for `𝒜`**:
`H^n(X, 𝒜) ≃ Hom_{D(𝒜, d)}(𝒜, 𝒜[n])`, inverse to forgetting the differential graded structure
and evaluating at the unit. -/
noncomputable def dgaClassDerivedEquiv (n : ℤ) :
    dgaCohomology 𝒜 n ≃ (dgaDerivedRegular 𝒜 ⟶ (dgaDerivedRegular 𝒜)⟦n⟧) :=
  (Equiv.ofBijective _ (dgaEvalOne_dgaForgetHom_bijective 𝒜 n)).symm

/-- The identification of Section 0FU3 is inverse to forgetting and evaluating at the unit. -/
theorem dgaEvalOne_dgaForgetHom_dgaClassDerivedEquiv (n : ℤ)
    (ξ : dgaCohomology 𝒜 n) :
    dgaEvalOne 𝒜 n (dgaForgetHom 𝒜 n (dgaClassDerivedEquiv 𝒜 n ξ)) = ξ :=
  Equiv.ofBijective_apply_symm_apply _ (dgaEvalOne_dgaForgetHom_bijective 𝒜 n) ξ

/-- **Section 0FU3.** The morphism

`ξ' : 𝒜 ⟶ 𝒜[n]`

in `D(A)` attached to a class `ξ ∈ H^n(X, 𝒜)`: the
morphism of `D(𝒜, d)` which Section 0FU3 attaches to `ξ`, with its differential graded
structure forgotten. -/
noncomputable def dgaClassMorphism (n : ℤ) (ξ : dgaCohomology 𝒜 n) :
    dgaDerivedObject 𝒜 ⟶ (dgaDerivedObject 𝒜)⟦n⟧ :=
  dgaForgetHom 𝒜 n (dgaClassDerivedEquiv 𝒜 n ξ)

/-- **Section 0FU3, property (1).** `ξ'` lifts to a morphism of the derived category
of right differential graded `𝒜`-modules. -/
theorem exists_lift_dgaClassMorphism (n : ℤ) (ξ : dgaCohomology 𝒜 n) :
    ∃ g : dgaDerivedRegular 𝒜 ⟶ (dgaDerivedRegular 𝒜)⟦n⟧,
      dgaForgetHom 𝒜 n g = dgaClassMorphism 𝒜 n ξ :=
  ⟨_, rfl⟩

/-- **Section 0FU3, property (2).** `ξ'(1) = ξ` in
`H^0(X, 𝒜[n]) = H^n(X, 𝒜)`. -/
theorem dgaEvalOne_dgaClassMorphism (n : ℤ) (ξ : dgaCohomology 𝒜 n) :
    dgaEvalOne 𝒜 n (dgaClassMorphism 𝒜 n ξ) = ξ :=
  dgaEvalOne_dgaForgetHom_dgaClassDerivedEquiv 𝒜 n ξ

/-- **Section 0FU3, uniqueness.** A morphism `𝒜 ⟶ 𝒜[n]` of
`D(A)` which lifts to the derived category of right differential graded
`𝒜`-modules and whose value at the unit is `ξ` is `ξ'`. -/
theorem eq_dgaClassMorphism (n : ℤ) (ξ : dgaCohomology 𝒜 n)
    {f : dgaDerivedObject 𝒜 ⟶ (dgaDerivedObject 𝒜)⟦n⟧}
    (hlift : ∃ g : dgaDerivedRegular 𝒜 ⟶ (dgaDerivedRegular 𝒜)⟦n⟧,
      dgaForgetHom 𝒜 n g = f)
    (hev : dgaEvalOne 𝒜 n f = ξ) :
    f = dgaClassMorphism 𝒜 n ξ := by
  obtain ⟨g, rfl⟩ := hlift
  refine congrArg (dgaForgetHom 𝒜 n) ((dgaEvalOne_dgaForgetHom_bijective 𝒜 n).1 ?_)
  exact hev.trans (dgaEvalOne_dgaClassMorphism 𝒜 n ξ).symm

/-- **Section 0FU3.** A class `ξ ∈ H^n(X, 𝒜)` determines a unique morphism
`ξ' : 𝒜 ⟶ 𝒜[n]` of `D(A)` with properties (1) and (2). -/
theorem existsUnique_dgaClassMorphism (n : ℤ) (ξ : dgaCohomology 𝒜 n) :
    ∃! f : dgaDerivedObject 𝒜 ⟶ (dgaDerivedObject 𝒜)⟦n⟧,
      (∃ g : dgaDerivedRegular 𝒜 ⟶ (dgaDerivedRegular 𝒜)⟦n⟧,
        dgaForgetHom 𝒜 n g = f) ∧ dgaEvalOne 𝒜 n f = ξ :=
  ⟨dgaClassMorphism 𝒜 n ξ,
    ⟨exists_lift_dgaClassMorphism 𝒜 n ξ, dgaEvalOne_dgaClassMorphism 𝒜 n ξ⟩,
    fun _ hf => eq_dgaClassMorphism 𝒜 n ξ hf.1 hf.2⟩

end Algebra

/-! ### The relative de Rham complex -/

/-- The translation functors of the derived category `D(Ω^•, d)` of right differential graded
modules over the relative de Rham complex. -/
noncomputable instance deRhamDerivedHasShift :
    HasShift (_root_.SheafOfModules.DifferentialGradedModule.derivedCategory.{u, u, u}
      (deRhamDifferentialGradedAlgebra B D)) ℤ :=
  dgaDerivedHasShift (deRhamDifferentialGradedAlgebra B D)

/-- **Forgetting the differential graded module structure**: a morphism `Ω^• ⟶ Ω^•[n]` of the
derived category `D(Ω^•, d)` of right differential graded `Ω^•`-modules, read as a morphism of
`D(f^{-1}𝒪_S)` through `SheafOfModules.DifferentialGradedModule.derivedForget`. -/
noncomputable abbrev deRhamForgetHom (n : ℤ)
    (g : deRhamDerivedRegular B D ⟶ (deRhamDerivedRegular B D)⟦n⟧) :
    deRhamDerivedObject B D ⟶ (deRhamDerivedObject B D)⟦n⟧ :=
  dgaForgetHom (deRhamDifferentialGradedAlgebra B D) n g

/-- The unit `f^{-1}𝒪_S ⟶ Ω^•`, as a morphism of `D(f^{-1}𝒪_S)`. -/
noncomputable abbrev deRhamUnitHom :
    AlgebraicGeometry.RingedSite.derivedStructureSheaf (baseSite A) ⟶ deRhamDerivedObject B D :=
  dgaUnitHom (deRhamDifferentialGradedAlgebra B D)

/-- **The unit `1 ∈ H^0_{dR}(X/S)`**: the image of `1 ∈ H^0(X, f^{-1}𝒪_S)` under the unit
`f^{-1}𝒪_S ⟶ Ω^•`. -/
noncomputable abbrev deRhamOneClass : deRhamCohomology B D 0 :=
  dgaOneClass (deRhamDifferentialGradedAlgebra B D)

/-- **The identification `H^m(X, Ω^•[n]) = H^{n + m}_{dR}(X/S)`**, for `n + m = k`. -/
noncomputable abbrev deRhamShiftHomologyIso (n m k : ℤ) (h : n + m = k) :
    (DerivedCategory.homologyFunctor _ m).obj
        ((derivedSectionsBase A).obj ((deRhamDerivedObject B D)⟦n⟧)) ≅
      deRhamCohomology B D k :=
  dgaShiftHomologyIso (deRhamDifferentialGradedAlgebra B D) n m k h

/-- **The value at the unit** `f(1) ∈ H^0(X, Ω^•[n]) = H^n_{dR}(X/S)` of a morphism
`f : Ω^• ⟶ Ω^•[n]` of `D(f^{-1}𝒪_S)`: the map `f` induces on `H^0(X, -)`, applied to
`1 ∈ H^0_{dR}(X/S)`. -/
noncomputable abbrev deRhamEvalOne (n : ℤ)
    (f : deRhamDerivedObject B D ⟶ (deRhamDerivedObject B D)⟦n⟧) : deRhamCohomology B D n :=
  dgaEvalOne (deRhamDifferentialGradedAlgebra B D) n f

/-- **The identification of Differential Graded Sheaves, Section 0FU3, for the relative de Rham
complex**: `H^n_{dR}(X/S) ≃ Hom_{D(Ω^•, d)}(Ω^•, Ω^•[n])`. -/
noncomputable abbrev deRhamClassDerivedEquiv (n : ℤ) :
    deRhamCohomology B D n ≃ (deRhamDerivedRegular B D ⟶ (deRhamDerivedRegular B D)⟦n⟧) :=
  dgaClassDerivedEquiv (deRhamDifferentialGradedAlgebra B D) n

/-- **Stacks Project, Tag 0FU7.** The morphism

`ξ' : Ω^•_{X/S} ⟶ Ω^•_{X/S}[n]`

in `D(f^{-1}𝒪_S)` attached to a relative de Rham cohomology class `ξ ∈ H^n_{dR}(X/S)`: the
morphism of `D(Ω^•, d)` which Section 0FU3 attaches to `ξ`, with its differential graded
structure forgotten. -/
noncomputable abbrev deRhamClassMorphism (n : ℤ) (ξ : deRhamCohomology B D n) :
    deRhamDerivedObject B D ⟶ (deRhamDerivedObject B D)⟦n⟧ :=
  dgaClassMorphism (deRhamDifferentialGradedAlgebra B D) n ξ

/-- **Stacks Project, Tag 0FU7, property (1).** `ξ'` lifts to a morphism of the derived category
of right differential graded `Ω^•_{X/S}`-modules. -/
@[stacks 0FU7 "property (1): the morphism lifts to the derived category of right differential
  graded modules"]
theorem exists_lift_deRhamClassMorphism (n : ℤ) (ξ : deRhamCohomology B D n) :
    ∃ g : deRhamDerivedRegular B D ⟶ (deRhamDerivedRegular B D)⟦n⟧,
      deRhamForgetHom B D n g = deRhamClassMorphism B D n ξ :=
  exists_lift_dgaClassMorphism (deRhamDifferentialGradedAlgebra B D) n ξ

/-- **Stacks Project, Tag 0FU7, property (2).** `ξ'(1) = ξ` in
`H^0(X, Ω^•_{X/S}[n]) = H^n_{dR}(X/S)`. -/
@[stacks 0FU7 "property (2): the value of the morphism at the unit is the class"]
theorem deRhamEvalOne_deRhamClassMorphism (n : ℤ) (ξ : deRhamCohomology B D n) :
    deRhamEvalOne B D n (deRhamClassMorphism B D n ξ) = ξ :=
  dgaEvalOne_dgaClassMorphism (deRhamDifferentialGradedAlgebra B D) n ξ

/-- **Stacks Project, Tag 0FU7, uniqueness.** A morphism `Ω^•_{X/S} ⟶ Ω^•_{X/S}[n]` of
`D(f^{-1}𝒪_S)` which lifts to the derived category of right differential graded
`Ω^•_{X/S}`-modules and whose value at the unit is `ξ` is `ξ'`. -/
theorem eq_deRhamClassMorphism (n : ℤ) (ξ : deRhamCohomology B D n)
    {f : deRhamDerivedObject B D ⟶ (deRhamDerivedObject B D)⟦n⟧}
    (hlift : ∃ g : deRhamDerivedRegular B D ⟶ (deRhamDerivedRegular B D)⟦n⟧,
      deRhamForgetHom B D n g = f)
    (hev : deRhamEvalOne B D n f = ξ) :
    f = deRhamClassMorphism B D n ξ :=
  eq_dgaClassMorphism (deRhamDifferentialGradedAlgebra B D) n ξ hlift hev

/-- **Stacks Project, Tag 0FU7.** A class `ξ ∈ H^n_{dR}(X/S)` determines a unique morphism
`ξ' : Ω^•_{X/S} ⟶ Ω^•_{X/S}[n]` of `D(f^{-1}𝒪_S)` with properties (1) and (2). -/
@[stacks 0FU7 "existence and uniqueness: a class determines a unique morphism with properties (1)
  and (2)"]
theorem existsUnique_deRhamClassMorphism (n : ℤ) (ξ : deRhamCohomology B D n) :
    ∃! f : deRhamDerivedObject B D ⟶ (deRhamDerivedObject B D)⟦n⟧,
      (∃ g : deRhamDerivedRegular B D ⟶ (deRhamDerivedRegular B D)⟦n⟧,
        deRhamForgetHom B D n g = f) ∧ deRhamEvalOne B D n f = ξ :=
  existsUnique_dgaClassMorphism (deRhamDifferentialGradedAlgebra B D) n ξ

/-- The value at the unit of `f : Ω^• ⟶ Ω^•[n]` is the value at `1 ∈ H^0(X, f^{-1}𝒪_S)` of the
composite `f^{-1}𝒪_S ⟶ Ω^• ⟶ Ω^•[n]`. -/
theorem deRhamEvalOne_eq (n : ℤ)
    (f : deRhamDerivedObject B D ⟶ (deRhamDerivedObject B D)⟦n⟧) :
    deRhamEvalOne B D n f = (deRhamShiftHomologyIso B D n 0 n (add_zero n)).hom
      (structureSheafEval A _ (deRhamUnitHom B D ≫ f)) :=
  dgaEvalOne_eq (deRhamDifferentialGradedAlgebra B D) n f

/-- The global section `1` of `Ω^0`, as a degree-zero global cocycle of the relative de Rham
complex. -/
noncomputable abbrev deRhamOneCycle :
    (Stacks.Cohomology.DerivedGlobalCupProduct.sectionsComplex (baseRingedSpace A)
      (deRhamComplexInt (X := X) (A := A) (φ := φ) B D)).cycles 0 :=
  dgaOneCycle (deRhamDifferentialGradedAlgebra B D)

/-- The cocycle `deRhamOneCycle B D` is the global section `1` of `Ω^0`, the unit of the exterior
algebra. -/
theorem iCycles_deRhamOneCycle :
    ConcreteCategory.hom
        ((Stacks.Cohomology.DerivedGlobalCupProduct.sectionsComplex (baseRingedSpace A)
          (deRhamComplexInt (X := X) (A := A) (φ := φ) B D)).iCycles 0) (deRhamOneCycle B D) =
      (deRhamDifferentialGradedAlgebra B D).one.eval (op ⊤) :=
  iCycles_dgaOneCycle (deRhamDifferentialGradedAlgebra B D)

/-- **The unit `1 ∈ H^0_{dR}(X/S)` is the class of the global section `1` of `Ω^0`.** -/
theorem deRhamOneClass_eq_globalClass_one :
    (deRhamOneClass B D : _) = Stacks.Cohomology.DerivedGlobalCupProduct.globalClass
      (X := baseRingedSpace A) (deRhamComplexInt (X := X) (A := A) (φ := φ) B D) 0
      (deRhamOneCycle B D) :=
  dgaOneClass_eq_globalClass_one (deRhamDifferentialGradedAlgebra B D)

end AlgebraicGeometry.SheafOfModules
