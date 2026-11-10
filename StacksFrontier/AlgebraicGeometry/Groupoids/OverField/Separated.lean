module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.Separated
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Separation

/-!
# Separatedness of a groupoid scheme over a field

If the object scheme of a groupoid scheme is the spectrum of a field, then its arrow scheme is
separated.  The stabilizer is then a group scheme over that field, hence separated; separatedness
of the stabilizer over the object scheme is equivalent to separatedness of the source-target
morphism, and the object scheme is affine, so the arrow scheme is separated absolutely.

## Main results

* `AlgebraicGeometry.isSeparated_arrows_of_objects_isSpec_field` proves separatedness of the
  arrow scheme.

## Implementation notes

The identification of the object scheme with the spectrum of a field is expressed by an
isomorphism. The conclusion is absolute separatedness of the underlying arrow scheme, not
merely separatedness over the object scheme or the base.

## References

* [Stacks Project, Tag 04LN](https://stacks.math.columbia.edu/tag/04LN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids

namespace AlgebraicGeometry

universe u

/-- A morphism out of a scheme isomorphic to the spectrum of a field is affine. -/
private theorem isAffineHom_of_isSpec_field {X S : Scheme.{u}} {k : Type u} [Field k]
    (f : X ⟶ S) (e : X ≅ Spec (.of k)) : IsAffineHom f := by
  have : Subsingleton X := (Scheme.homeoOfIso e).injective.subsingleton
  exact ⟨fun U _ => IsAffineOpen.of_subsingleton (fun _ _ _ _ => Subsingleton.elim _ _)⟩

/-- **Stacks Project, Tag 04LN.** The arrow scheme of a groupoid scheme with object scheme the
spectrum of a field is separated. -/
@[stacks 04LN]
public theorem isSeparated_arrows_of_objects_isSpec_field
    {S : Scheme.{u}} (G : GroupoidScheme S) {k : Type u} [Field k]
    (_ : G.objects.left ≅ Spec (.of k)) : G.arrows.left.IsSeparated := by
  rename_i h
  have : IsAffine G.objects.left := .of_isIso h.hom
  have : IsAffineHom G.objects.hom := isAffineHom_of_isSpec_field G.objects.hom h
  have : IsAffine (MonoidalCategory.tensorObj G.objects G.objects).left := by
    change IsAffine (pullback G.objects.hom G.objects.hom)
    exact isAffine_of_isAffineHom (pullback.snd G.objects.hom G.objects.hom)
  have hstabAbs : (stabilizer G).left.IsSeparated := by
    let F := (Over.mapIso h).functor
    let : F.Monoidal := Functor.Monoidal.ofChosenFiniteProducts F
    let : GrpObj (F.obj (stabilizer G)) := Functor.grpObjObj
    exact isSeparated_of_groupScheme_over_field (Grp.mk (F.obj (stabilizer G)))
  have : IsSeparated ((stabilizer G).hom ≫ terminal.from G.objects.left) := by
    simpa using hstabAbs.isSeparated_terminal_from
  have : IsSeparated (stabilizer G).hom := .of_comp _ (terminal.from G.objects.left)
  have := (sourceTarget_isSeparated_iff_stabilizer_isSeparated G).mpr this
  exact ⟨by simpa using (inferInstance : IsSeparated
    ((sourceTarget G).left ≫ terminal.from (MonoidalCategory.tensorObj G.objects G.objects).left))⟩

end AlgebraicGeometry
