module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.Topology.Category.TopCat.Monoidal

/-!
# Limits of topological groups (Stacks 0B20)

A topological group is a group object internal to the cartesian monoidal category `TopCat`,
so the category of topological groups is Mathlib's `CategoryTheory.Grp TopCat`, and the
category of ordinary groups is `CategoryTheory.Grp (Type _)`. With that reading the tag has
three parts, all stated below: `Grp TopCat` has all small limits, and the two forgetful
functors — to topological spaces and to groups — preserve them.

Parts (1) and (a) come straight from Mathlib: `Grp.forget TopCat` creates limits of every
shape that `TopCat` has, hence `Grp TopCat` has them and the functor preserves them. Part
(b) is the genuinely new content. The forgetful functor to groups is `Functor.mapGrp`
applied to `CategoryTheory.forget TopCat`, which is monoidal because it preserves finite
products; it then preserves limits because its composite with `Grp.forget (Type _)` is the
composite `Grp.forget TopCat ⋙ forget TopCat`, and `Grp.forget (Type _)` reflects limits.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace TopCat

/-- The forgetful functor `TopCat ⥤ Type` is (strong) monoidal for the cartesian monoidal
structures on both sides, since it preserves finite products. -/
noncomputable instance forgetMonoidal : (CategoryTheory.forget TopCat.{u}).Monoidal :=
  Functor.Monoidal.ofChosenFiniteProducts _

/-- The forgetful functor from topological groups to groups, sending a group object in
`TopCat` to the group object in `Type` on its underlying set. -/
noncomputable abbrev forgetGrp : Grp TopCat.{u} ⥤ Grp (Type u) :=
  (CategoryTheory.forget TopCat.{u}).mapGrp

/-- **Stacks 0B20**, part (1). The category of topological groups has all small limits.
This is Mathlib's `HasLimitsOfShape J (Grp C)`, obtained from the fact that
`Grp.forget TopCat` creates limits. -/
@[stacks 0B20 "part (1): existence of limits"]
theorem hasLimits_grp : HasLimits (Grp TopCat.{u}) :=
  ⟨fun _ => inferInstance⟩

/-- **Stacks 0B20**, part (a). The forgetful functor from topological groups to topological
spaces preserves all small limits; indeed Mathlib shows it creates them. -/
@[stacks 0B20 "part (a): commutes with forgetful to TopCat"]
theorem preservesLimits_grpForget : PreservesLimits (Grp.forget TopCat.{u}) :=
  PreservesLimitsOfSize.mk

/-- **Stacks 0B20**, part (b). The forgetful functor from topological groups to groups
preserves all small limits. -/
@[stacks 0B20 "part (b): commutes with forgetful to Grp"]
theorem preservesLimits_forgetGrp : PreservesLimits (forgetGrp.{u}) where
  preservesLimitsOfShape {J} _ :=
    have : PreservesLimitsOfShape J (forgetGrp.{u} ⋙ Grp.forget (Type u)) :=
      preservesLimitsOfShape_of_natIso (G := forgetGrp.{u} ⋙ Grp.forget (Type u))
        (F := Grp.forget TopCat.{u} ⋙ CategoryTheory.forget TopCat.{u})
        (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl))
    preservesLimitsOfShape_of_reflects_of_preserves forgetGrp (Grp.forget (Type u))

end TopCat
