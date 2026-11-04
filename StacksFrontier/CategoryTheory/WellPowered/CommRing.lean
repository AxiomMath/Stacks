module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Subobject.WellPowered

/-!
# The category of commutative rings is well-powered

A subobject of `R : CommRingCat.{u}` determines the subring of `R` which is the range of its
arrow, and this assignment is an order embedding `Subobject R ↪o Subring ↥R`. Since
`Subring ↥R : Type u`, this makes `Subobject R` a `u`-small type and `CommRingCat.{u}` a
`CategoryTheory.WellPowered.{u}` category.

## Main definitions

* `Stacks.CommRingWellPowered.toSubring`: the subring of `R` underlying a subobject of `R`.
* `Stacks.CommRingWellPowered.subringOrderEmbedding`: `Subobject R ↪o Subring ↥R`.

## Main results

* `Stacks.CommRingWellPowered.le_of_toSubring_le`: a subobject of a commutative ring is
  determined, as an element of the subobject lattice, by its underlying subring.
* `Stacks.CommRingWellPowered.wellPowered`: `CommRingCat.{u}` is `WellPowered.{u}`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.CommRingWellPowered

variable {R : CommRingCat.{u}}

/-- The subring of `R` underlying a subobject of `R`: the range of its monomorphism. -/
noncomputable def toSubring (S : Subobject R) : Subring ↥R := S.arrow.hom.range

/-- The underlying subring is monotone in the subobject. -/
theorem toSubring_le_toSubring {S T : Subobject R} (h : S ≤ T) : toSubring S ≤ toSubring T := by
  rintro x ⟨a, rfl⟩
  exact ⟨(Subobject.ofLE S T h).hom a, congr($(Subobject.ofLE_arrow h).hom a)⟩

/-- A subobject of a commutative ring is determined by its underlying subring: if the subring
underlying `S` is contained in the one underlying `T`, then `S ≤ T`. -/
theorem le_of_toSubring_le {S T : Subobject R} (h : toSubring S ≤ toSubring T) : S ≤ T := by
  have hT : Function.Injective T.arrow.hom :=
    ConcreteCategory.injective_of_mono_of_preservesPullback T.arrow
  let e : ↥(T : CommRingCat.{u}) ≃+* ↥(toSubring T) :=
    RingEquiv.ofBijective T.arrow.hom.rangeRestrict
      ⟨fun _ _ hab => hT (congrArg Subtype.val hab), T.arrow.hom.rangeRestrict_surjective⟩
  let s : ↥(S : CommRingCat.{u}) →+* ↥(toSubring T) :=
    RingHom.codRestrict S.arrow.hom (toSubring T) fun x => h ⟨x, rfl⟩
  refine Subobject.le_of_comm (CommRingCat.ofHom (e.symm.toRingHom.comp s)) ?_
  ext x
  exact congrArg Subtype.val (e.apply_symm_apply (s x))

/-- The order embedding of the subobjects of a commutative ring `R` into the subrings of `R`,
sending a subobject to the range of its arrow. -/
noncomputable def subringOrderEmbedding (R : CommRingCat.{u}) : Subobject R ↪o Subring ↥R :=
  OrderEmbedding.ofMapLEIff toSubring fun _ _ => ⟨le_of_toSubring_le, toSubring_le_toSubring⟩

/-- The category of commutative rings is well-powered. -/
instance wellPowered : WellPowered.{u} CommRingCat.{u} where
  subobject_small R := small_of_injective (subringOrderEmbedding R).injective

end Stacks.CommRingWellPowered
