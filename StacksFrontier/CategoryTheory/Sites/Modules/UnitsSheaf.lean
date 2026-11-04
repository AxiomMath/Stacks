module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Ring.Adjunctions
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Topology.Sheaves.Modules.Invertible
import StacksCore.Tactic.StacksAttribute

/-!
# Invertible modules and the sheaf of units on a ringed site

Let `X` be a ringed site. The unit groups of the rings of sections of the structure sheaf form
a sheaf of abelian groups `O_X^*`. Forgetting the group structure exhibits it as a subsheaf of
the underlying sheaf of sets of the structure sheaf, cut out by the condition that a section
has a right inverse, and its group law is multiplication.

## Main definitions

* `AlgebraicGeometry.RingedSite.unitsSheaf`: the sheaf of abelian groups of units of the
  structure sheaf.
* `AlgebraicGeometry.RingedSite.unitsSheafι`: its canonical inclusion into the underlying
  sheaf of sets of the structure sheaf.

## Main results

* `AlgebraicGeometry.RingedSite.unitsSheafι_mono`: the canonical inclusion is a
  monomorphism.
* `AlgebraicGeometry.RingedSite.isUnit_iff_exists_unitsSheaf`: the sections lifting through
  the units subsheaf are exactly the units.
* `AlgebraicGeometry.RingedSite.exists_unitsSheaf_iff_exists_mul_eq_one`: a section lifts
  through the units subsheaf exactly when it has a right inverse.
* `AlgebraicGeometry.RingedSite.unitsSheafι_hom_app_mul`: the inclusion `O_X^* ⟶ O_X` carries
  the group law of `O_X^*` to multiplication in `O_X`.

## References

* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry.RingedSite

/-- The sheaf of units `O_X^*` of the structure sheaf of a ringed site. -/
@[stacks 0409 "units sheaf", implicit_reducible]
noncomputable def unitsSheaf (X : RingedSite.{u, v, w}) : Sheaf X.J CommGrpCat.{w} :=
  (sheafCompose X.J CommMonCat.units.{w}).obj
    ((sheafCompose X.J (forget₂ CommRingCat.{w} CommMonCat.{w})).obj X.O)

/-- The canonical inclusion of the units sheaf into the underlying sheaf of sets of the
structure sheaf. -/
noncomputable def unitsSheafι (X : RingedSite.{u, v, w}) :
    (sheafCompose X.J (forget CommGrpCat.{w})).obj (unitsSheaf X) ⟶
      (sheafCompose X.J (forget CommRingCat.{w})).obj X.O where
  hom.app U := ↾(fun x : (X.O.obj.obj U)ˣ ↦ (x : X.O.obj.obj U))
  hom.naturality _ _ _ := rfl

/-- The canonical inclusion of the units sheaf into the structure sheaf is a monomorphism. -/
@[stacks 0409 "subsheaf"]
instance unitsSheafι_mono (X : RingedSite.{u, v, w}) : Mono (unitsSheafι X) := by
  have : Mono (unitsSheafι X).hom := by
    rw [NatTrans.mono_iff_mono_app]
    intro U; apply ConcreteCategory.mono_of_injective
    intro x y h; exact Units.ext h
  exact Sheaf.Hom.mono_of_presheaf_mono _ _ _

/-- Sections of the structure sheaf which lift through the units subsheaf are exactly the
units. -/
theorem isUnit_iff_exists_unitsSheaf (X : RingedSite.{u, v, w}) (U : X.Cᵒᵖ)
    (f : X.O.obj.obj U) :
    IsUnit f ↔
      ∃ u : ((unitsSheaf X).obj.obj U : Type w), (unitsSheafι X).hom.app U u = f := by
  constructor
  · rintro ⟨u, rfl⟩; exact ⟨u, rfl⟩
  · rintro ⟨u, rfl⟩; exact u.isUnit

/-- A section belongs to the units subsheaf exactly when it has a right inverse: the units
subsheaf is `U ↦ {f ∈ O(U) | ∃ g ∈ O(U), fg = 1}`. -/
@[stacks 0409 "defining rule"]
theorem exists_unitsSheaf_iff_exists_mul_eq_one (X : RingedSite.{u, v, w}) (U : X.Cᵒᵖ)
    (f : X.O.obj.obj U) :
    (∃ x : ((unitsSheaf X).obj.obj U : Type w), (unitsSheafι X).hom.app U x = f) ↔
      ∃ g : X.O.obj.obj U, f * g = 1 := by
  simpa only [← isUnit_iff_exists_unitsSheaf] using (isUnit_iff_exists_inv (a := f))

end AlgebraicGeometry.RingedSite

/-! ### The group law on the sheaf of units -/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.RingedSite

/-- The group law on the sheaf of units is multiplication: the subsheaf inclusion
`O_X^* ⟶ O_X` is multiplicative. -/
@[stacks 0409 "group law"]
theorem unitsSheafι_hom_app_mul (X : RingedSite.{u, v, w}) (U : X.Cᵒᵖ)
    (x y : (X.O.obj.obj U)ˣ) :
    (unitsSheafι X).hom.app U (x * y) =
      (x : X.O.obj.obj U) * (y : X.O.obj.obj U) :=
  rfl

end AlgebraicGeometry.RingedSite
