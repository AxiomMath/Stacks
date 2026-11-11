module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Sites.Sheaf
import StacksCore.Tactic.EgaSgaAttribute

/-! # Localization of a topos at a sheaf

Given a site `(C, J)` and a sheaf `F` on `C`, the localization of the topos `Sh(C)` at `F` is the
slice category `Sh(C)/F`. The localization morphism `j_F : Sh(C)/F ⟶ Sh(C)`, the morphism of topoi
`j_F⁻¹ ⊣ j_{F,*}`, is `localizationMorphism` in
`StacksFrontier.CategoryTheory.Sites.SliceTopos.LocalizationMorphism`. This file also packages the
lower-shriek adjunction `j_{F!} ⊣ j_F⁻¹`, i.e. `Over.forget F ⊣ Over.star F`, which Mathlib
provides as `Over.forgetAdjStar`.

## Main results

* `toposLocalization`: the localization `Sh(C, J)/F` of a topos at a sheaf (Stacks 04IP (1)).
* `ToposAdjointPair`: an adjoint pair of functors.
* `toposLocalizationMorphism`: the lower-shriek adjunction `j_{F!} ⊣ j_F⁻¹` of the
  localization, as such an adjoint pair (Stacks 04GZ (2)).

Tags covered: 04IP.
-/

@[expose] public section

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The localization of the topos of sheaves `Sh(C, J)` at a sheaf `F` is the
slice (over) category `Sh(C, J) / F`. Objects are pairs `(G, φ)` where `G` is a
sheaf on `C` and `φ : G ⟶ F` is a morphism of sheaves, and morphisms are
commuting triangles over `F`. -/
@[stacks 04IP "(1): the localization Sh(C)/F of the topos Sh(C) at F", sga "4 IV 5.1"]
abbrev toposLocalization (F : Sheaf J (Type (max u v))) :=
  Over F

/-- An adjoint pair of functors between `E` and `D`, used below for the lower-shriek
adjunction `j_{F!} ⊣ j_F⁻¹` of a localization; the library's morphism of topoi, with a left
exact inverse image, is `MorphismOfTopoi`. We record the left adjoint `leftAdj` and the
right adjoint `rightAdj`. No exactness condition is imposed. -/
@[sga "4 IV 3.1" "partial"]
structure ToposAdjointPair (E D : Type*) [Category E] [Category D] where
  /-- The left adjoint functor `E ⥤ D`. -/
  leftAdj : E ⥤ D
  /-- The right adjoint functor `D ⥤ E`. -/
  rightAdj : D ⥤ E
  /-- The adjunction `leftAdj ⊣ rightAdj`. -/
  adj : leftAdj ⊣ rightAdj

/-- The lower-shriek adjunction `j_{F!} ⊣ j_F⁻¹` of the localization of the topos `Sh(C, J)` at
the sheaf `F` (Stacks Project Tag 04GZ (2)), packaged as a `ToposAdjointPair`.

This is *not* the localization morphism `j_F` itself: that is the morphism of topoi
`j_F⁻¹ ⊣ j_{F,*}`, the declaration `localizationMorphism` (Stacks 04IP (2)). What is packaged
here is the adjunction one step lower in the triple `j_{F!} ⊣ j_F⁻¹ ⊣ j_{F,*}`, namely the
canonical Mathlib adjunction `Over.forget F ⊣ Over.star F`:
- `Over.forget F : Sh(C)/F ⥤ Sh(C)` sends `(G, φ : G ⟶ F)` to `G`. This is
  `j_{F!}`, the left adjoint.
- `Over.star F : Sh(C) ⥤ Sh(C)/F` sends `H` to the second projection
  `(H × F, pr_F) : H × F ⟶ F`. This is the inverse image `j_F⁻¹`, here in the right-adjoint
  slot.

The adjunction `Over.forget F ⊣ Over.star F` is exactly `Over.forgetAdjStar`
in Mathlib, and it requires `Sh(C, J)` to have binary products. -/
@[sga "4 IV 5.2" "(5.2.1)", sga "3 I 1.6" "p_S clause: i_S ⊣ p_S", sga "4 IV 8.5"]
noncomputable def toposLocalizationMorphism (F : Sheaf J (Type (max u v)))
    [Limits.HasBinaryProducts (Sheaf J (Type (max u v)))] :
    ToposAdjointPair (toposLocalization J F) (Sheaf J (Type (max u v))) where
  leftAdj := Over.forget F
  rightAdj := Over.star F
  adj := Over.forgetAdjStar F
