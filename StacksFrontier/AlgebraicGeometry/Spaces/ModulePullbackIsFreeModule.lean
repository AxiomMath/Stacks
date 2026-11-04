module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalTypesOfModules
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModulePullbackSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleFreeLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesCompare

/-!
# Free modules under the inverse image of modules of algebraic spaces

Three small facts about the inverse image of Stacks 03LU along a morphism of algebraic spaces,
used by the clause (3) and clause (4) developments of Stacks 0CZS:

* `SheafOfModules.IsFree.of_iso`: freeness of a sheaf of modules, Stacks 03DE (1), is invariant
  under isomorphism;
* `AlgebraicGeometry.Space.isFreeModule_modulePullback`: the inverse image of a free module is
  free, which is Stacks 03DF (1) for the inverse image of Stacks 03LU, read off the ringed-topos
  statement `AlgebraicGeometry.RingedToposHom.pullbackModules_isFree`;
* `AlgebraicGeometry.Space.modulePullbackCommSquareObjIso`: the two iterated inverse images along
  the sides of a commuting square, at one module.

The base-change clause of Stacks 0CZT itself, both inclusions, is
`AlgebraicGeometry.Space.etaleFreeLocus_modulePullback_eq` of
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleFreeLocusBaseChange.lean`, and the inclusion
`|g'|⁻¹(W(F)) ⊆ W((g')^*F)` for an arbitrary morphism is
`AlgebraicGeometry.Space.preimage_etaleFreeLocus_subset` of
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleFreeLocusPullback.lean`.

## References

* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DF](https://stacks.math.columbia.edu/tag/03DF)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace SheafOfModules

/-- **Freeness of a sheaf of modules, Stacks 03DE (1), is invariant under isomorphism.**  A
family of global sections exhibiting `F` as a coproduct of copies of the structure sheaf is
carried by an isomorphism `F ≅ G` to such a family for `G`. -/
theorem IsFree.of_iso {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} {F G : SheafOfModules.{w} R} (e : F ≅ G) (h : F.IsFree) :
    G.IsFree := by
  obtain ⟨B, ι, ⟨hc⟩⟩ := h
  exact ⟨B, fun b ↦ ι b ≫ e.hom, ⟨hc.ofIsoColimit (Cocone.ext e (by intro i; rfl))⟩⟩

end SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The two inverse images of modules attached to a morphism of algebraic spaces -/

/-- **Stacks 03DF (1) for the inverse image of Stacks 03LU.**  The inverse image along a morphism
`f : X ⟶ Y` of algebraic spaces of a free `𝒪_Y`-module is a free `𝒪_X`-module.

This is `AlgebraicGeometry.RingedToposHom.pullbackModules_isFree` — the pullback carries the
structure sheaf to the structure sheaf and commutes with coproducts.  The two readings of the
inverse image are now one term: `AlgebraicGeometry.Space.modulePullback` is *defined* as
`pullbackModules` of the morphism of small étale ringed topoi
(`AlgebraicGeometry.Space.modulePullback_eq`, by `rfl`), and the four-field morphism that
definition goes through is the one the ringed-topos statement uses
(`AlgebraicGeometry.RingedToposHom.toModulesHom_eq_toRingedToposModulesHom`).  So the two
rewrites below carry the statement onto the ringed-topos one with no transport.  No
`@[stacks 03DF]` attribute is attached: the tag is already registered on the ringed-topos
statement, `AlgebraicGeometry.RingedToposHom.pullbackModules_isFree`. -/
theorem isFreeModule_modulePullback {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (h : IsFreeModule B S hS Y G) :
    IsFreeModule B S hS X ((modulePullback B S hS f).obj G) := by
  have hb : (smallEtaleRingedToposHom B S hS f).toModulesHom =
      smallEtaleRingedToposModulesHom B S hS f :=
    (smallEtaleRingedToposHom B S hS f).toModulesHom_eq_toRingedToposModulesHom
  have hpull := AlgebraicGeometry.RingedToposHom.pullbackModules_isFree
    (smallEtaleRingedToposHom B S hS f) h
  rw [hb] at hpull
  exact hpull

/-- **The inverse image of a module along the two sides of a commuting square of algebraic
spaces.**  For `a' ≫ g' = p ≫ a` and an `𝒪_Z`-module `F`, the two iterated inverse images
`(a')^*(g')^*F` and `p^*(a^*F)` are canonically isomorphic.

This is the object-level reading of the functor-level
`AlgebraicGeometry.Space.modulePullbackCommSquareIso` of
`StacksFrontier.AlgebraicGeometry.Spaces.ChartModulePullbackSquare`, evaluated at `F`; it is given a
separate name only because the functor-level one already occupies that name. -/
def modulePullbackCommSquareObjIso {W X X' Z : AlgebraicSpaces B S hS} {a' : W ⟶ X'} {g' : X' ⟶ Z}
    {p : W ⟶ X} {a : X ⟶ Z} (hw : a' ≫ g' = p ≫ a) (F : Modules.{u, u} B S hS Z.1 Z.2) :
    (modulePullback B S hS a').obj ((modulePullback B S hS g').obj F) ≅
      (modulePullback B S hS p).obj ((modulePullback B S hS a).obj F) :=
  (modulePullbackCommSquareIso B S hS hw).app F

end AlgebraicGeometry.Space

end
