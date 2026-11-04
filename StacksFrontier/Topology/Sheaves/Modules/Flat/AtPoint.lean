module

public import StacksFrontier.Topology.Sheaves.Modules.Flat.Stalk
import StacksCore.Tactic.StacksAttribute

/-!
# Modules flat at a point of a ringed space

Let `(X, 𝒪_X)` be a ringed space and `x ∈ X`. An `𝒪_X`-module `F` is *flat at `x`* if its stalk
`F_x` is a flat `𝒪_{X,x}`-module. A module is flat exactly when it is flat at every point.

The stalk carries the `𝒪_{X,x}`-module structure of `Mathlib.Algebra.Category.ModuleCat.Stalk`,
the one over which Stacks 05NE (`AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat`) is
stated.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.IsFlatAt`: flatness of an `𝒪_X`-module at a point.

## Main results

* `AlgebraicGeometry.SheafOfModules.isFlat_iff_forall_isFlatAt`: an `𝒪_X`-module is flat if and
  only if it is flat at every point.

## References

* [Stacks Project, Tag 05NF](https://stacks.math.columbia.edu/tag/05NF)
* [Stacks Project, Tag 05NE](https://stacks.math.columbia.edu/tag/05NE)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.SheafOfModules

/-- An `𝒪_X`-module `F` on a ringed space `X` is *flat at* `x : X` if its stalk `F_x` is a flat
`𝒪_{X,x}`-module. -/
@[stacks 05NF]
noncomputable def IsFlatAt {X : RingedSpace.{u}}
    (F : _root_.SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf))
    (x : X) : Prop :=
  letI : Module (TopCat.Presheaf.stalk (C := CommRingCat.{u}) X.sheaf.obj x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x) :=
    inferInstanceAs (Module (TopCat.Presheaf.stalk (C := CommRingCat.{u}) X.sheaf.obj x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (id F.val : PresheafOfModules.{u}
          (X.sheaf.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})).presheaf x))
  Module.Flat (TopCat.Presheaf.stalk (C := CommRingCat.{u}) X.sheaf.obj x)
    (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x)

noncomputable local instance hasSheafify_opens_isFlatAt (X : TopCat.{u}) :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite _ _

noncomputable local instance wEqualsLocallyBijective_opens_isFlatAt (X : TopCat.{u}) :
    (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- An `𝒪_X`-module on a ringed space is flat if and only if it is flat at every point. -/
theorem isFlat_iff_forall_isFlatAt {X : RingedSpace.{u}}
    (F : _root_.SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)) :
    IsFlat (O := X.sheaf) F ↔ ∀ x : X, IsFlatAt F x :=
  isFlat_iff_stalk_flat X.sheaf F

end AlgebraicGeometry.SheafOfModules
