module
public import StacksFrontier.CategoryTheory.Monoidal.FunctorCategoryTensorColimits

public import Mathlib.CategoryTheory.Sites.Limits
public import StacksFrontier.CategoryTheory.Sites.MonoidalPreadditive

/-!
# The tensor product of sheaves commutes with colimits in each variable

Let `A` be a monoidal category and `J` a Grothendieck topology for which the localizing class of
sheafification is monoidal, so that sheaves carry the localized monoidal structure
`CategoryTheory.Sheaf.monoidalCategory`. If tensoring by a fixed object of `A` commutes with
colimits of shape `K`, and `A` has such colimits, then tensoring by a fixed sheaf commutes with
colimits of shape `K` of sheaves.

## Main results

* `CategoryTheory.Sheaf.presheafToSheafCompTensorLeftIso`: sheafifying and then tensoring by a
  sheaf `F` is tensoring by the underlying presheaf of `F` and then sheafifying.
* `CategoryTheory.Sheaf.preservesColimitsOfShape_tensorLeft`,
  `CategoryTheory.Sheaf.preservesColimitsOfShape_tensorRight` and their `PreservesColimitsOfSize`
  forms `preservesColimitsOfSize_tensorLeft`, `preservesColimitsOfSize_tensorRight`.

## Implementation notes

A diagram `D` of sheaves is the sheafification of the diagram `D ⋙ sheafToPresheaf J A` of its
underlying presheaves, whose colimit sheafifies to a colimit of `D` because sheafification is a
left adjoint. Tensoring by `F` after sheafifying is a composite of two colimit-preserving
functors (`presheafToSheafCompTensorLeftIso`), so it carries that colimit cocone to a colimit
cocone; this is `CategoryTheory.Limits.preservesColimit_of_preserves_colimit_cocone`. No closed
structure on sheaves is used.
-/

@[expose] public section

universe w w' v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory.Sheaf

variable {C : Type u₁} [Category.{v₁} C] {A : Type u₂} [Category.{v₂} A] [MonoidalCategory A]
  (J : GrothendieckTopology C) [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]

attribute [local instance] Sheaf.monoidalCategory

/-- Sheafifying and then tensoring on the left by a sheaf `F` is tensoring on the left by the
underlying presheaf of `F` and then sheafifying. -/
noncomputable def presheafToSheafCompTensorLeftIso (F : Sheaf J A) :
    presheafToSheaf J A ⋙ tensorLeft F ≅ tensorLeft F.obj ⋙ presheafToSheaf J A :=
  Functor.isoWhiskerLeft _
      ((tensoringLeft _).mapIso (asIso ((sheafificationAdjunction J A).counit.app F)).symm) ≪≫
    Functor.Monoidal.commTensorLeft (presheafToSheaf J A) F.obj

/-- Sheafifying and then tensoring on the right by a sheaf `F` is tensoring on the right by the
underlying presheaf of `F` and then sheafifying. -/
noncomputable def presheafToSheafCompTensorRightIso (F : Sheaf J A) :
    presheafToSheaf J A ⋙ tensorRight F ≅ tensorRight F.obj ⋙ presheafToSheaf J A :=
  Functor.isoWhiskerLeft _
      ((tensoringRight _).mapIso (asIso ((sheafificationAdjunction J A).counit.app F)).symm) ≪≫
    Functor.Monoidal.commTensorRight (presheafToSheaf J A) F.obj

omit [MonoidalCategory A] [(J.W (A := A)).IsMonoidal] in
/-- A functor out of sheaves preserves the colimits of shape `K` as soon as its composite with
sheafification does and presheaves have colimits of shape `K`: every diagram of sheaves is the
sheafification of the diagram of its underlying presheaves. -/
lemma preservesColimitsOfShape_of_presheafToSheaf_comp {D : Type*} [Category D]
    (K : Type w) [Category.{w'} K] [HasColimitsOfShape K (Cᵒᵖ ⥤ A)] (T : Sheaf J A ⥤ D)
    [PreservesColimitsOfShape K (presheafToSheaf J A ⋙ T)] :
    PreservesColimitsOfShape K T where
  preservesColimit {E} := by
    have : HasColimit (E ⋙ sheafToPresheaf J A) := HasColimitsOfShape.has_colimit _
    let eE : (E ⋙ sheafToPresheaf J A) ⋙ presheafToSheaf J A ≅ E :=
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft E (asIso (sheafificationAdjunction J A).counit) ≪≫
        E.rightUnitor
    have : PreservesColimit ((E ⋙ sheafToPresheaf J A) ⋙ presheafToSheaf J A) T :=
      preservesColimit_of_preserves_colimit_cocone
        (isColimitOfPreserves (presheafToSheaf J A) (colimit.isColimit _))
        (isColimitOfPreserves (presheafToSheaf J A ⋙ T) (colimit.isColimit _))
    exact preservesColimit_of_iso_diagram T eE

variable (K : Type w) [Category.{w'} K] [HasColimitsOfShape K A]

/-- **Tensoring on the left by a fixed sheaf commutes with colimits of shape `K`**, as soon as
tensoring on the left by a fixed object of `A` does. -/
lemma preservesColimitsOfShape_tensorLeft [∀ X : A, PreservesColimitsOfShape K (tensorLeft X)]
    (F : Sheaf J A) : PreservesColimitsOfShape K (tensorLeft F) := by
  have : PreservesColimitsOfShape K (presheafToSheaf J A ⋙ tensorLeft F) :=
    preservesColimitsOfShape_of_natIso (presheafToSheafCompTensorLeftIso J F).symm
  exact preservesColimitsOfShape_of_presheafToSheaf_comp J K _

/-- **Tensoring on the right by a fixed sheaf commutes with colimits of shape `K`**, as soon as
tensoring on the right by a fixed object of `A` does. -/
lemma preservesColimitsOfShape_tensorRight [∀ X : A, PreservesColimitsOfShape K (tensorRight X)]
    (F : Sheaf J A) : PreservesColimitsOfShape K (tensorRight F) := by
  have : PreservesColimitsOfShape K (presheafToSheaf J A ⋙ tensorRight F) :=
    preservesColimitsOfShape_of_natIso (presheafToSheafCompTensorRightIso J F).symm
  exact preservesColimitsOfShape_of_presheafToSheaf_comp J K _

end CategoryTheory.Sheaf

namespace CategoryTheory.Sheaf

variable {C : Type u₁} [Category.{v₁} C] {A : Type u₂} [Category.{v₂} A] [MonoidalCategory A]
  (J : GrothendieckTopology C) [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
  [HasColimitsOfSize.{w, w'} A]

attribute [local instance] Sheaf.monoidalCategory

/-- **Tensoring on the left by a fixed sheaf commutes with colimits**, as soon as tensoring on
the left by a fixed object of `A` does. -/
lemma preservesColimitsOfSize_tensorLeft
    [∀ X : A, PreservesColimitsOfSize.{w, w'} (tensorLeft X)] (F : Sheaf J A) :
    PreservesColimitsOfSize.{w, w'} (tensorLeft F) where
  preservesColimitsOfShape {K} _ := preservesColimitsOfShape_tensorLeft J K F

/-- **Tensoring on the right by a fixed sheaf commutes with colimits**, as soon as tensoring on
the right by a fixed object of `A` does. -/
lemma preservesColimitsOfSize_tensorRight
    [∀ X : A, PreservesColimitsOfSize.{w, w'} (tensorRight X)] (F : Sheaf J A) :
    PreservesColimitsOfSize.{w, w'} (tensorRight F) where
  preservesColimitsOfShape {K} _ := preservesColimitsOfShape_tensorRight J K F

end CategoryTheory.Sheaf

end
