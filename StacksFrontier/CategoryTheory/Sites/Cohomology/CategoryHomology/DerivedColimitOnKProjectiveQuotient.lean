module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.DerivedColimitOnKProjective
-- `leftDerivedObjIsoOfIsKProjective`, `leftDerivedObjSingleIso` and their two instances for
-- `Lπ_!` are defined in a section that is not exposed; the equations below unfold them.
import all StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.DerivedColimitOnKProjective

/-!
# Derived lower shriek on a K-projective complex, read from the homotopy category

`Stacks.CategoryHomology.leftDerivedObjIsoOfIsKProjective` computes a total left derived functor
`LF` of `F` at a K-projective complex `P` as `F` applied degreewise.  Its first factor is the
image under `LF` of the comparison `Q ≅ Q_h ∘ quotient` read backwards.  This file records the
computation with that factor cancelled, which is the form in which a chase meeting the
isomorphism at an object coming from the homotopy category -- for instance a computation of the
unit of the derived adjunction `Lπ_! ⊣ π^{-1}` -- uses it.

The definitions are not exposed outside the module that defines them, so these equations are the
handle a downstream computation has on them.

## Main results

* `Stacks.CategoryHomology.map_quotientCompQhIso_hom_comp_leftDerivedObjIsoOfIsKProjective_hom`
  and `map_quotientCompQhIso_hom_comp_totalDerivedColimitObjIsoOfIsKProjective_hom`:
  the computation at a K-projective complex with its first factor cancelled.
* `Stacks.CategoryHomology.map_quotientCompQhIso_hom_comp_leftDerivedObjSingleIso_hom` and
  `Stacks.CategoryHomology.map_quotientCompQhIso_hom_comp_totalDerivedColimitObjSingleIso_hom`:
  the same at a projective object placed in degree zero.

## References

* [Stacks Project, Tag 08Q6](https://stacks.math.columbia.edu/tag/08Q6)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe uD vD u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.CategoryHomology

section General

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  (F : A ⥤ B) [F.Additive]
  [(F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  (LF : DerivedCategory A ⥤ DerivedCategory B)
  (α : DerivedCategory.Qh ⋙ LF ⟶
    F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
  [LF.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]

/-- **The computation at a K-projective complex, with its first factor cancelled.**
`Stacks.CategoryHomology.leftDerivedObjIsoOfIsKProjective` begins with the derived functor of the
comparison `Q ≅ Q_h ∘ quotient`, read backwards; preceded by the derived functor of that
comparison itself, what is left is the derived-functor comparison `α` followed by the comparison
of the homotopy category with the derived category on the target side.

This is what a computation meeting the isomorphism at an object coming from the homotopy category
consumes, and it is stated here because the body of
`Stacks.CategoryHomology.leftDerivedObjIsoOfIsKProjective` is not exposed outside this module.

The middle factor of that body, the comparison of `quotient ⋙ F_*` with `F_* ⋙ quotient` on
homotopy categories, does not appear: its components are identities, so the composite above is
well typed, and `h₂` is where that is used.  It is used as a *term*, because the composite of
`α` with the comparison on the target side is well typed only up to definitional
unfolding — `F_*(quotient P)` and `quotient (F_* P)` being two spellings of one object — and a
tactic that had to build it would report the target as not type-correct at `implicit`
transparency. -/
lemma map_quotientCompQhIso_hom_comp_leftDerivedObjIsoOfIsKProjective_hom
    (P : CochainComplex A ℤ) [P.IsKProjective] :
    LF.map ((DerivedCategory.quotientCompQhIso A).hom.app P) ≫
        (leftDerivedObjIsoOfIsKProjective F LF α P).hom =
      α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P) ≫
        (DerivedCategory.quotientCompQhIso B).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) := by
  have := Stacks.Homology.isIso_leftDerivedCounit_app_of_isKProjective LF α P
  have h₁ : DerivedCategory.Qh.map
        ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app P) =
      𝟙 (DerivedCategory.Qh.obj ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) :=
    DerivedCategory.Qh.map_id _
  have h₂ : DerivedCategory.Qh.map
          ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app P) ≫
        (DerivedCategory.quotientCompQhIso B).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
      (DerivedCategory.quotientCompQhIso B).hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
    (congrArg (fun x => x ≫ (DerivedCategory.quotientCompQhIso B).hom.app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) h₁).trans (Category.id_comp _)
  dsimp only [leftDerivedObjIsoOfIsKProjective, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    asIso_hom, Iso.app_hom, Iso.app_inv]
  rw [← Category.assoc, ← LF.map_comp, Iso.hom_inv_id_app, LF.map_id, Category.id_comp]
  exact congrArg
    (fun x => α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P) ≫ x) h₂

/-- **The computation at a projective object placed in degree zero, with its first factor
cancelled.** `Stacks.CategoryHomology.leftDerivedObjSingleIso` is
`Stacks.CategoryHomology.leftDerivedObjIsoOfIsKProjective` at the single complex followed by the
degreewise comparison commuting `F` past `single`; cancelling the first factor of the former with
`Stacks.CategoryHomology.map_quotientCompQhIso_hom_comp_leftDerivedObjIsoOfIsKProjective_hom`
leaves the derived-functor comparison `α`, the comparison of the homotopy category with the
derived category on the target side, and that degreewise comparison, which nothing here
cancels. -/
@[reassoc]
lemma map_quotientCompQhIso_hom_comp_leftDerivedObjSingleIso_hom (X : A) [Projective X] :
    LF.map ((DerivedCategory.quotientCompQhIso A).hom.app
          ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj X)) ≫
        (leftDerivedObjSingleIso F LF α X).hom =
      α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
            ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj X)) ≫
        (DerivedCategory.quotientCompQhIso B).hom.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj X)) ≫
          DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex F
            (ComplexShape.up ℤ) 0).app X).hom := by
  have := Stacks.Homology.isKProjective_single (A := A) X
  dsimp only [leftDerivedObjSingleIso, Iso.trans_hom, Functor.mapIso_hom]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun x => x ≫ DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app X).hom)
      (map_quotientCompQhIso_hom_comp_leftDerivedObjIsoOfIsKProjective_hom F LF α
        ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj X))).trans
      (Category.assoc _ _ _))

end General

section LowerShriek

variable (C : Type u) [SmallCategory C] (D : Type uD) [Category.{vD} D] [Abelian D]
  [EnoughProjectives (Cᵒᵖ ⥤ D)] [HasColimitsOfShape ℕ D] [HasExactColimitsOfShape ℕ D]
  [HasColimitsOfShape Cᵒᵖ D]

/-- **The computation of derived lower shriek on a K-projective complex, with its first factor
cancelled**: `map_quotientCompQhIso_hom_comp_leftDerivedObjIsoOfIsKProjective_hom` read for
`Lπ_!`. -/
lemma map_quotientCompQhIso_hom_comp_totalDerivedColimitObjIsoOfIsKProjective_hom
    (P : CochainComplex (Cᵒᵖ ⥤ D) ℤ) [P.IsKProjective] :
    (totalDerivedColimit C D).map ((DerivedCategory.quotientCompQhIso (Cᵒᵖ ⥤ D)).hom.app P) ≫
        (totalDerivedColimitObjIsoOfIsKProjective C D P).hom =
      (totalDerivedColimitCounit C D).app
          ((HomotopyCategory.quotient (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ)).obj P) ≫
        (DerivedCategory.quotientCompQhIso D).hom.app
          (((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  have := colim_hasPointwiseLeftDerivedFunctor C D
  have := totalDerivedColimit_isLeftDerivedFunctor C D
  map_quotientCompQhIso_hom_comp_leftDerivedObjIsoOfIsKProjective_hom
    (colim : (Cᵒᵖ ⥤ D) ⥤ D) (totalDerivedColimit C D) (totalDerivedColimitCounit C D) P

/-- **Derived lower shriek at a projective abelian presheaf in degree zero, with its first factor
cancelled**: `Stacks.CategoryHomology.map_quotientCompQhIso_hom_comp_leftDerivedObjSingleIso_hom`
read for `Lπ_!`.

`Stacks.CategoryHomology.totalDerivedColimitObjSingleIso` is defined in a plain
`public noncomputable section` rather than an exposed one, so a consumer outside this module
cannot unfold it: Lean reports *"The following definitions were not unfolded because their
definition is not exposed: totalDerivedColimitObjSingleIso"*. This equation is therefore the
handle a downstream computation has on it, in the form a chase meeting the identification at an
object coming from the homotopy category uses. -/
@[reassoc]
lemma map_quotientCompQhIso_hom_comp_totalDerivedColimitObjSingleIso_hom (P : Cᵒᵖ ⥤ D)
    [Projective P] :
    (totalDerivedColimit C D).map ((DerivedCategory.quotientCompQhIso (Cᵒᵖ ⥤ D)).hom.app
          ((HomologicalComplex.single (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ) 0).obj P)) ≫
        (totalDerivedColimitObjSingleIso C D P).hom =
      (totalDerivedColimitCounit C D).app
          ((HomotopyCategory.quotient (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ)).obj
            ((HomologicalComplex.single (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ) 0).obj P)) ≫
        (DerivedCategory.quotientCompQhIso D).hom.app
            (((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((HomologicalComplex.single (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ) 0).obj P)) ≫
          DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex
            (colim : (Cᵒᵖ ⥤ D) ⥤ D) (ComplexShape.up ℤ) 0).app P).hom :=
  have := colim_hasPointwiseLeftDerivedFunctor C D
  have := totalDerivedColimit_isLeftDerivedFunctor C D
  map_quotientCompQhIso_hom_comp_leftDerivedObjSingleIso_hom (colim : (Cᵒᵖ ⥤ D) ⥤ D)
    (totalDerivedColimit C D) (totalDerivedColimitCounit C D) P

end LowerShriek

end Stacks.CategoryHomology

end
