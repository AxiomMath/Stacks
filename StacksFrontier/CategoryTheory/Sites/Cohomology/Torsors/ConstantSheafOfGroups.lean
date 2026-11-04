module

public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Over
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TrivialityAndGlobalSections

/-!
# The constant sheaf of groups on a site

For a group `G` and a site `(C, J)` on which sheaves of groups can be sheafified, the
constant sheaf with value `G` is a sheaf of groups in the sense of
`SheafOfGroups`: its underlying presheaf of types is the sheafification of the constant
presheaf, read through the forgetful functor, and the group structure on its sections is
the one it carries as a sheaf of groups.

Restricting it along `CategoryTheory.Over.forget U` gives the constant sheaf of groups on
the localized site `C/U`. This model of the localized constant sheaf is chosen so that the
sections of the constant sheaf over an object `V ⟶ U` of `C/U` are *by definition* its
sections over `V`, which lets one and the same group act on torsors over all the localized
sites at once.

## Main definitions

* `CategoryTheory.constantSheafOfGroups`: the constant sheaf with value `G`, as a sheaf of
  groups.
* `CategoryTheory.constantSheafOfGroupsUnit`: the canonical group homomorphism from `G` to
  its sections, the unit of sheafification.
* `CategoryTheory.constantSheafOfGroupsOver`: the same sheaf of groups on the localized
  site `C/U`.

## Implementation notes

The group structure of `SheafOfGroups` is recorded section-wise, so it is read off from the
group object `(constantSheaf J GrpCat).obj (GrpCat.of G)` by `dsimp`-ing through the
forgetful functor; multiplicativity of the restriction maps then holds because those are
the underlying maps of morphisms in `GrpCat`. That the composite with the forgetful functor
is still a sheaf is `CategoryTheory.sheafCompose`, available because the forgetful functor
of `GrpCat` creates the limits that the sheaf condition is about.

The universe `w` of the group is independent of the universes of the site, as it is for
Mathlib's `CategoryTheory.constantSheaf`.

## References

* [Stacks Project, Tag 03AH](https://stacks.math.columbia.edu/tag/03AH)
-/

@[expose] public noncomputable section

namespace CategoryTheory

universe w v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (G : Type w) [Group G]
  [HasWeakSheafify J GrpCat.{w}]

/-- The constant sheaf of groups with value `G`: the sheafification of the constant presheaf
`G` in `GrpCat`, regarded as a sheaf of groups through the forgetful functor. -/
def constantSheafOfGroups : SheafOfGroups.{w} (C := C) J where
  presheaf := ((constantSheaf J GrpCat.{w}).obj (GrpCat.of G)).obj ⋙ forget GrpCat.{w}
  isSheaf := ((sheafCompose J (forget GrpCat.{w})).obj
    ((constantSheaf J GrpCat.{w}).obj (GrpCat.of G))).property
  group := fun _ => by dsimp; infer_instance
  map_mul := fun _ _ _ => by simp

/-- The canonical group homomorphism from `G` to the sections of the constant sheaf of
groups with value `G` over an object, given by the unit of sheafification. -/
def constantSheafOfGroupsUnit (V : Cᵒᵖ) :
    G →* (constantSheafOfGroups J G).presheaf.obj V :=
  ((toSheafify J ((Functor.const Cᵒᵖ).obj (GrpCat.of G))).app V).hom

/-- The constant sheaf of groups with value `G` on the localized site `C/U`, namely the
restriction of `CategoryTheory.constantSheafOfGroups` along `CategoryTheory.Over.forget`. -/
def constantSheafOfGroupsOver (U : C) :
    SheafOfGroups.{w} (C := Over U) (J.over U) where
  presheaf := (Over.forget U).op ⋙ (constantSheafOfGroups J G).presheaf
  isSheaf := ((J.overPullback (Type w) U).obj
    ⟨(constantSheafOfGroups J G).presheaf, (constantSheafOfGroups J G).isSheaf⟩).property
  group := fun _ => (constantSheafOfGroups J G).group _
  map_mul := fun f a b => (constantSheafOfGroups J G).map_mul ((Over.forget U).op.map f) a b

end CategoryTheory

end
