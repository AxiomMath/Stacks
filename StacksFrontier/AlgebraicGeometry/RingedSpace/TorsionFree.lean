module

public import Mathlib.RingTheory.Flat.TorsionFree
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat

/-!
# Torsion free modules over the target of a morphism of ringed spaces

For a morphism of ringed spaces `f : X ⟶ Y`, an `𝒪_X`-module `F` is *torsion free over `Y` at*
a point `x` of `X` when its stalk `F_x`, an `𝒪_{Y, f(x)}`-module through the stalk map of `f`,
is a torsion free `𝒪_{Y, f(x)}`-module; it is torsion free over `Y` when this holds at every
point of `X`.  This is the torsion analogue of flatness over `Y` in the sense of Stacks 08KT,
with the same module structure on the stalk.

A flat module over any ring is torsion free, and over a Bézout domain, in particular over a
valuation ring, a torsion free module is flat (Stacks 0539).  Pointwise this says that flatness
over `Y` at `x` implies torsion freeness over `Y` at `x`, and that the two agree whenever the
local ring `𝒪_{Y, f(x)}` is a Bézout domain, for example a valuation ring.

## Main definitions

* `AlgebraicGeometry.IsTorsionFreeOverAt`: the stalk at `x` is a torsion free module over the
  local ring of the target at `f(x)`.
* `AlgebraicGeometry.IsTorsionFreeOver`: torsion freeness over the target at every point.

## Main results

* `AlgebraicGeometry.IsFlatOverAt.isTorsionFreeOverAt`: flatness over the target at a point
  implies torsion freeness there.
* `AlgebraicGeometry.isFlatOverAt_iff_isTorsionFreeOverAt`: when the local ring of the target is
  a Bézout domain the two conditions agree; this is Stacks 0539 on the stalk.
* `AlgebraicGeometry.isFlatOver_iff_isTorsionFreeOver`: the same at every point.

## References

* [Stacks Project, Tag 0539](https://stacks.math.columbia.edu/tag/0539)
* [Stacks Project, Tag 08KT](https://stacks.math.columbia.edu/tag/08KT)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- An `𝒪_X`-module is *torsion free over `Y` at* `x : X` if its stalk at `x`, regarded as an
`𝒪_{Y, f(x)}`-module through the stalk map of `f`, is torsion free: the regular elements of
`𝒪_{Y, f(x)}` act injectively on it. -/
public noncomputable abbrev IsTorsionFreeOverAt {X Y : AlgebraicGeometry.RingedSpace.{u}}
    (f : X ⟶ Y)
    (F : SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf))
    (x : X) : Prop :=
  let M : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) := F.val
  letI : Module (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x) := inferInstance
  letI : Module (Y.presheaf.stalk (f.hom.base x))
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x) :=
    Module.compHom _ (f.hom.stalkMap x).hom
  Module.IsTorsionFree (Y.presheaf.stalk (f.hom.base x))
    (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x)

/-- An `𝒪_X`-module is *torsion free over `Y`* if it is torsion free over `Y` at every point
of `X`. -/
public abbrev IsTorsionFreeOver {X Y : AlgebraicGeometry.RingedSpace.{u}} (f : X ⟶ Y)
    (F : SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)) : Prop :=
  ∀ x : X, IsTorsionFreeOverAt f F x

variable {X Y : AlgebraicGeometry.RingedSpace.{u}} (f : X ⟶ Y)
  (F : SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf))

/-- Over a Bézout domain, a module is flat if and only if it is torsion free. -/
private theorem flat_iff_isTorsionFree_of_isBezout (R N : Type u) [CommRing R] [IsDomain R]
    [IsBezout R] [AddCommGroup N] [Module R N] : Module.Flat R N ↔ Module.IsTorsionFree R N := by
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, ← Submodule.isTorsionFree_iff_torsion_eq_bot]

/-- A module flat over the target at a point is torsion free over the target there: a flat
module over any ring is torsion free. -/
theorem IsFlatOverAt.isTorsionFreeOverAt {x : X} (h : IsFlatOverAt f F x) :
    IsTorsionFreeOverAt f F x :=
  let M : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) := F.val
  let : Module (Y.presheaf.stalk (f.hom.base x))
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x) :=
    Module.compHom _ (f.hom.stalkMap x).hom
  have : Module.Flat _ (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x) := h
  Module.Flat.isTorsionFree

/-- **Stacks 0539 on a stalk.**  If the local ring of the target at `f(x)` is a Bézout domain —
for example a valuation ring — then a module on the source is flat over the target at `x`
exactly when it is torsion free over the target at `x`. -/
theorem isFlatOverAt_iff_isTorsionFreeOverAt (x : X)
    [IsDomain (Y.presheaf.stalk (f.hom.base x))] [IsBezout (Y.presheaf.stalk (f.hom.base x))] :
    IsFlatOverAt f F x ↔ IsTorsionFreeOverAt f F x :=
  let M : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) := F.val
  let : Module (Y.presheaf.stalk (f.hom.base x))
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x) :=
    Module.compHom _ (f.hom.stalkMap x).hom
  flat_iff_isTorsionFree_of_isBezout _ _

/-- **Stacks 0539 on every stalk.**  If every local ring of the target at a point in the image
is a Bézout domain — for example a valuation ring — then a module on the source is flat over
the target exactly when it is torsion free over the target. -/
theorem isFlatOver_iff_isTorsionFreeOver
    [∀ x : X, IsDomain (Y.presheaf.stalk (f.hom.base x))]
    [∀ x : X, IsBezout (Y.presheaf.stalk (f.hom.base x))] :
    IsFlatOver f F ↔ IsTorsionFreeOver f F :=
  forall_congr' fun x => isFlatOverAt_iff_isTorsionFreeOverAt f F x

end AlgebraicGeometry

end
