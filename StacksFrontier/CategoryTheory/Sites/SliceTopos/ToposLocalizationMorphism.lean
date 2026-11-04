module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Sites.Sheaf
import StacksCore.Tactic.EgaSgaAttribute

/-! # Localization of a topos at a sheaf

Given a site `(C, J)` and a sheaf `F` on `C`, the localization of the topos `Sh(C)` at `F` is the
slice category `Sh(C)/F`, and the localization morphism `j_F : Sh(C)/F ⟶ Sh(C)` is carried by the
canonical adjunction `Over.forget F ⊣ Over.star F`, which Mathlib provides as
`Over.forgetAdjStar`.

## Main results

* `toposLocalization`: the localization `Sh(C, J)/F` of a topos at a sheaf (Stacks 04IP).
* `ToposAdjointPair`: a morphism of topoi packaged as an adjoint pair of functors.
* `toposLocalizationMorphism`: the localization morphism `j_F`, as such an adjoint pair
  (Stacks 04IP).

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
@[stacks 04IP, sga "4 IV 5.1"]
abbrev toposLocalization (F : Sheaf J (Type (max u v))) :=
  Over F

/-- A morphism of topoi `f : E → D` (in the sense of Stacks Tag 04IN/Tag 04IP)
is packaged here as the data of an adjoint pair of functors between `E` and
`D`. We record the left adjoint (called `leftAdj`, often denoted `f_!` in the
étale case or `f^*` in the standard geometric-morphism convention) and the
right adjoint (called `rightAdj`, the corresponding direct image / star).

In topos theory one additionally requires the inverse image functor to be
left exact (preserve finite limits); we omit this requirement here since the
construction below is purely structural. -/
@[sga "4 IV 3.1" "partial"]
structure ToposAdjointPair (E D : Type*) [Category E] [Category D] where
  /-- The left adjoint functor `E ⥤ D`. -/
  leftAdj : E ⥤ D
  /-- The right adjoint functor `D ⥤ E`. -/
  rightAdj : D ⥤ E
  /-- The adjunction `leftAdj ⊣ rightAdj`. -/
  adj : leftAdj ⊣ rightAdj

/-- The localization morphism `j_F` associated to the localization of the
topos `Sh(C, J)` at the sheaf `F` (Stacks Project Tag 04IN).

We package the canonical Mathlib adjunction `Over.forget F ⊣ Over.star F`,
which is the structural content of the morphism:
- `Over.forget F : Sh(C)/F ⥤ Sh(C)` sends `(G, φ : G ⟶ F)` to `G`. This is
  the left adjoint (the "shriek" / étale-extension functor in the slice
  topos picture).
- `Over.star F : Sh(C) ⥤ Sh(C)/F` sends `G` to the second projection
  `(G × F, pr_F) : G × F ⟶ F`. This is the right adjoint (the base-change
  / star functor).

The adjunction `Over.forget F ⊣ Over.star F` is exactly `Over.forgetAdjStar`
in Mathlib, and it requires `Sh(C, J)` to have binary products. -/
@[stacks 04IP, sga "4 IV 5.2" "(5.2.1)", sga "3 I 1.6" "p_S clause: i_S ⊣ p_S", sga "4 IV 8.5"]
noncomputable def toposLocalizationMorphism (F : Sheaf J (Type (max u v)))
    [Limits.HasBinaryProducts (Sheaf J (Type (max u v)))] :
    ToposAdjointPair (toposLocalization J F) (Sheaf J (Type (max u v))) where
  leftAdj := Over.forget F
  rightAdj := Over.star F
  adj := Over.forgetAdjStar F
