module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.SmallSections

/-!
# Restriction of the sections of a sheaf of groups and of a pseudo-torsor

Let `(C, J)` be a site, let `𝒢` be a sheaf of groups on it and let `F` be a pseudo-torsor under
`𝒢`, the sections of both living in arbitrary universes. Over an object `V` carrying sections
`s` and `s'` of `F`, the unique section of `𝒢` carrying `s` to `s'` is
`(F.sectionEquivGroup V s).symm s'`. This file records that these sections are compatible with
restriction and compose, and packages the restriction maps of `𝒢` as group homomorphisms.

## Main definitions

* `SheafOfGroups.presheafMapHom`: a restriction map of a sheaf of groups, as a group
  homomorphism.

## Main results

* `PseudoTorsor.map_sectionEquivGroup_symm`: the section of `𝒢` carrying one section of `F` to
  another is compatible with restriction.
* `PseudoTorsor.sectionEquivGroup_symm_mul`: these sections compose.

## References

* [Stacks Project, Tag 03AH](https://stacks.math.columbia.edu/tag/03AH)
-/

@[expose] public section

open CategoryTheory Opposite

universe t w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace SheafOfGroups

/-- A restriction map of a sheaf of groups, as a group homomorphism. -/
def presheafMapHom (𝒢 : SheafOfGroups.{w} J) {V W : Cᵒᵖ} (f : V ⟶ W) :
    𝒢.presheaf.obj V →* 𝒢.presheaf.obj W where
  toFun := 𝒢.presheaf.map f
  map_one' := SheafOfGroups.map_one (G := 𝒢) f
  map_mul' := 𝒢.map_mul f

/-- The homomorphism `presheafMapHom 𝒢 f` sends a section `g` to its restriction
`𝒢.presheaf.map f g`. -/
@[simp]
theorem presheafMapHom_apply (𝒢 : SheafOfGroups.{w} J) {V W : Cᵒᵖ} (f : V ⟶ W)
    (g : 𝒢.presheaf.obj V) : 𝒢.presheafMapHom f g = 𝒢.presheaf.map f g :=
  rfl

end SheafOfGroups

namespace PseudoTorsor

variable {𝒢 : SheafOfGroups.{w} J}

/-- The section of the sheaf of groups carrying one section of a pseudo-torsor to another is
compatible with restriction. -/
theorem map_sectionEquivGroup_symm (F : PseudoTorsor.{t} 𝒢) {V W : Cᵒᵖ} (f : V ⟶ W)
    (s s' : F.presheaf.obj V) :
    𝒢.presheaf.map f ((F.sectionEquivGroup V s).symm s') =
      (F.sectionEquivGroup W (F.presheaf.map f s)).symm (F.presheaf.map f s') := by
  rw [Equiv.eq_symm_apply, sectionEquivGroup_apply, ← F.naturality]
  exact congrArg (F.presheaf.map f) ((F.sectionEquivGroup V s).apply_symm_apply s')

/-- The sections of the sheaf of groups carrying one section of a pseudo-torsor to another
compose. -/
theorem sectionEquivGroup_symm_mul (F : PseudoTorsor.{t} 𝒢) (V : Cᵒᵖ)
    (a b c : F.presheaf.obj V) :
    (F.sectionEquivGroup V b).symm c * (F.sectionEquivGroup V a).symm b =
      (F.sectionEquivGroup V a).symm c := by
  rw [Equiv.eq_symm_apply, sectionEquivGroup_apply, F.mul_act]
  exact (congrArg (F.act V _) ((F.sectionEquivGroup V a).apply_symm_apply b)).trans
    ((F.sectionEquivGroup V b).apply_symm_apply c)

end PseudoTorsor
