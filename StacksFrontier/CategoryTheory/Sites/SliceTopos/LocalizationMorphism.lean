module

public import Mathlib.CategoryTheory.LocallyCartesianClosed.Sections
public import StacksFrontier.CategoryTheory.Sites.CartesianClosed
public import StacksFrontier.CategoryTheory.Sites.SliceTopos.ToposLocalizationMorphism
public import StacksFrontier.CategoryTheory.Sites.ToposLocalization

/-! # The localization morphism of a topos at a sheaf

Given a site `(C, J)` and a sheaf `F` on `C`, the localization morphism is the morphism of topoi
`j_F : Sh(C)/F ⟶ Sh(C)` of Stacks 04GZ, whose inverse image is `j_F⁻¹ = (H ↦ (H × F ⟶ F))` and
whose pushforward `j_{F,*}` is right adjoint to it.

## Main definitions

* `localizationMorphism`: the localization morphism `j_F : Sh(C, J)/F ⟶ Sh(C, J)`, as a
  `MorphismOfTopoi` (Stacks 04IP (2)).
* `localizationMorphism_inverseImage`: its inverse image is `toOver F : H ↦ (H × F ⟶ F)`.

## Implementation notes

`MorphismOfTopoi.overLocalization` (Stacks 04GZ) builds `j_F` from any right adjoint of
`j_F⁻¹ = toOver F`. On `Sh(C, J)` such a right adjoint exists: the category of sheaves of sets is
cartesian closed (`Sheaf.monoidalClosed_sheaf_type`) and has pullbacks, so `toOver F` has the
right adjoint `CategoryTheory.Over.sections F`, by `CategoryTheory.Over.toOverSectionsAdj`. Any
two right adjoints of a functor are canonically isomorphic, so this is the pushforward `j_{F,*}`
of Stacks 04GZ up to unique isomorphism.

Tags covered: 04IP.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

universe u v

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- **Stacks 04IP (2).** The *localization morphism* of the topos `Sh(C, J)` at a sheaf `F` is the
morphism of topoi `j_F : Sh(C, J)/F ⟶ Sh(C, J)` of Stacks 04GZ: its inverse image `j_F⁻¹` is
`H ↦ (H × F ⟶ F)`, which is left exact, and its pushforward `j_{F,*}` is the right adjoint of
`j_F⁻¹` given by sections over `F`. Its source is `toposLocalization J F`, the localization of the
topos `Sh(C, J)` at `F` (Stacks 04IP (1)). -/
@[stacks 04IP "(2): the localization morphism j_F : Sh(C)/F → Sh(C)"]
noncomputable def localizationMorphism (F : Sheaf J (Type (max u v))) :
    MorphismOfTopoi (toposLocalization J F) (Sheaf J (Type (max u v))) :=
  letI : @Closed _ _ (SemiCartesianMonoidalCategory.toMonoidalCategory
      (self := CartesianMonoidalCategory.toSemiCartesianMonoidalCategory)) F :=
    (Sheaf.monoidalClosed_sheaf_type J).closed F
  letI := ChosenPullbacksAlong.ofHasPullbacksAlong (curryRightUnitorHom F)
  letI := BraidedCategory.ofCartesianMonoidalCategory (C := Sheaf J (Type (max u v)))
  MorphismOfTopoi.overLocalization F (Over.toOverSectionsAdj F)

/-- The inverse image of the localization morphism `j_F` is `H ↦ (H × F ⟶ F)`. -/
lemma localizationMorphism_inverseImage (F : Sheaf J (Type (max u v))) :
    (localizationMorphism J F).inverseImage = toOver F :=
  rfl
