module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardCocontinuousSquare

/-!
# The base change of right Kan extensions of abelian groups, on underlying sets

Let `w` be a 2-square of functors `T : C₁ ⥤ C₂`, `L : C₁ ⥤ C₃`, `R : C₂ ⥤ C₄`, `B : C₃ ⥤ C₄`, and
let `F : C₃ ⥤ AddCommGrpCat` admit pointwise right Kan extensions along `B` and, after
precomposition with `L`, along `T`. The forgetful functor to sets preserves limits, so it carries
the pointwise right Kan extensions of `F` to those of the underlying presheaf of sets of `F`, and
it carries the base-change transformation of `w` at `F` to the base-change transformation of `w`
at that underlying presheaf. In particular the first is bijective at an object exactly when the
second is.

This is what lets an identity of Stacks 07AT proved for sheaves of sets be read for abelian
sheaves.

## Main results

* `Stacks.SheafOfModules.bijective_ranBaseChange_app_app_forget_iff`: bijectivity of the base
  change of right Kan extensions of abelian groups, at an object, is bijectivity of the base
  change of the underlying right Kan extensions of sets.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe t v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

namespace Stacks.SheafOfModules

section Underlying

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (L : C ⥤ D)
  [∀ F : C ⥤ AddCommGrpCat.{t}, L.HasRightKanExtension F]
  [∀ F : C ⥤ Type t, L.HasRightKanExtension F]

/-- **The underlying set of a pointwise right Kan extension of abelian groups is the pointwise
right Kan extension of the underlying sets.** Both are limit cones over the same diagram, the
first after applying the forgetful functor, which preserves limits. -/
def ranObjForgetIso (N : C ⥤ AddCommGrpCat.{t}) [L.HasPointwiseRightKanExtension N]
    [L.HasPointwiseRightKanExtension (N ⋙ forget AddCommGrpCat.{t})] (d : D) :
    (forget AddCommGrpCat.{t}).obj ((L.ran.obj N).obj d) ≅
      (L.ran.obj (N ⋙ forget AddCommGrpCat.{t})).obj d :=
  IsLimit.conePointUniqueUpToIso (isLimitOfPreserves (forget AddCommGrpCat.{t}) (ranIsLimit L N d))
    (ranIsLimit L (N ⋙ forget AddCommGrpCat.{t}) d)

/-- The comparison `ranObjForgetIso` is compatible with the legs of the two limit cones. -/
lemma ranObjForgetIso_hom_ranπ (N : C ⥤ AddCommGrpCat.{t}) [L.HasPointwiseRightKanExtension N]
    [L.HasPointwiseRightKanExtension (N ⋙ forget AddCommGrpCat.{t})] (d : D)
    (j : StructuredArrow d L) (s : (forget AddCommGrpCat.{t}).obj ((L.ran.obj N).obj d)) :
    ranπ L (N ⋙ forget AddCommGrpCat.{t}) d j ((ranObjForgetIso L N d).hom s) =
      (forget AddCommGrpCat.{t}).map (ranπ L N d j) s :=
  ConcreteCategory.congr_hom (IsLimit.conePointUniqueUpToIso_hom_comp
    (isLimitOfPreserves (forget AddCommGrpCat.{t}) (ranIsLimit L N d))
    (ranIsLimit L (N ⋙ forget AddCommGrpCat.{t}) d) j) s

end Underlying

section BaseChange

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
  {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄} (w : TwoSquare T L R B)
  [∀ F : C₁ ⥤ AddCommGrpCat.{t}, T.HasPointwiseRightKanExtension F]
  [∀ F : C₃ ⥤ AddCommGrpCat.{t}, B.HasPointwiseRightKanExtension F]
  [∀ F : C₁ ⥤ Type t, T.HasPointwiseRightKanExtension F]
  [∀ F : C₃ ⥤ Type t, B.HasPointwiseRightKanExtension F]

/-- The forgetful functor carries the base change of right Kan extensions of abelian groups to
the base change of the underlying right Kan extensions of sets, through `ranObjForgetIso`. -/
lemma ranObjForgetIso_ranBaseChange (F : C₃ ⥤ AddCommGrpCat.{t}) (x : C₂)
    (s : (forget AddCommGrpCat.{t}).obj ((B.ran.obj F).obj (R.obj x))) :
    (ranObjForgetIso T (L ⋙ F) x).hom
        ((forget AddCommGrpCat.{t}).map ((w.ranBaseChange.app F).app x) s) =
      (w.ranBaseChange.app (F ⋙ forget AddCommGrpCat.{t})).app x
        ((ranObjForgetIso B F (R.obj x)).hom s) := by
  refine Concrete.isLimit_ext _ (ranIsLimit T (L ⋙ F ⋙ forget AddCommGrpCat.{t}) x) _ _
    (fun j => ?_)
  have e1 := ranObjForgetIso_hom_ranπ T (L ⋙ F) x j
    ((forget AddCommGrpCat.{t}).map ((w.ranBaseChange.app F).app x) s)
  have e2 := ranObjForgetIso_hom_ranπ B F (R.obj x)
    (StructuredArrow.mk (R.map j.hom ≫ w.app j.right)) s
  have hA := ConcreteCategory.congr_hom
    (congrArg (forget AddCommGrpCat.{t}).map (ranBaseChange_π w F x j)) s
  have hT := ConcreteCategory.congr_hom (ranBaseChange_π w (F ⋙ forget AddCommGrpCat.{t}) x j)
    ((ranObjForgetIso B F (R.obj x)).hom s)
  simp only [ConcreteCategory.comp_apply] at hA hT
  exact e1.trans (hA.trans (e2.symm.trans hT.symm))

/-- **Bijectivity of the base change of right Kan extensions of abelian groups is bijectivity of
the base change of the underlying right Kan extensions of sets.** -/
theorem bijective_ranBaseChange_app_app_forget_iff (F : C₃ ⥤ AddCommGrpCat.{t}) (x : C₂) :
    Function.Bijective ((forget AddCommGrpCat.{t}).map ((w.ranBaseChange.app F).app x)) ↔
      Function.Bijective ((w.ranBaseChange.app (F ⋙ forget AddCommGrpCat.{t})).app x) := by
  rw [← (ranObjForgetIso T (L ⋙ F) x).toEquiv.bijective.of_comp_iff',
    ← Function.Bijective.of_comp_iff _ (ranObjForgetIso B F (R.obj x)).toEquiv.bijective]
  exact iff_of_eq (congrArg _ (funext (ranObjForgetIso_ranBaseChange w F x)))

end BaseChange

end Stacks.SheafOfModules
