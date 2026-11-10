module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.Order.Category.Preord

/-!
# The sections of a constant tower

A *tower* in a category is a functor out of `ℕ`, and the sections of a presheaf `F` along a
tower `T` are the limit `lim_e F(T_e)` of the inverse system `e ↦ F(T_e)`. Such a limit is in
general a genuine inverse limit — for the towers `Spec(D/p^e D)` of [Stacks, Tag 07MM] it is
`p`-adic completion — but when the tower is *constant* it collapses: the index category `ℕᵒᵖ` is
connected and nonempty, so a compatible family of sections at every level is one section.

## Main definitions

* `CategoryTheory.Limits.limitNatConstIso`: the isomorphism between the limit over `ℕᵒᵖ` of a
  constant functor and its value.
* `CategoryTheory.Limits.constLimitIso`: the isomorphism between the sections of a presheaf along
  a constant tower and its sections at the object the tower sits at.

## Main results

* `CategoryTheory.Limits.limitNatConstIso_hom`: `limitNatConstIso` is the projection at level
  zero.
* `CategoryTheory.Limits.constLimitIso_hom`: `constLimitIso` is the projection at level zero.
* `CategoryTheory.Limits.constLimitIso_naturality`: the isomorphism carries the map on sections
  induced by a morphism of constant towers to the restriction map of the presheaf.

## Implementation notes

`ℕᵒᵖ` has a terminal object, `op 0`, and not an initial one, so the collapse is *not* an instance
of `CategoryTheory.Limits.limitOfInitial`. It is close to `CategoryTheory.Limits.limitOfTerminal`,
which asks every transition map of the diagram to be an isomorphism; the isomorphism here is built
from the explicit limit cone `natConstCone`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ v₂ u₁ u₂

noncomputable section

namespace CategoryTheory.Limits

variable {D : Type u₂} [Category.{v₂} D]

/-! ### The limit of a constant functor on `ℕᵒᵖ` -/

/-- **The cone over a constant functor on `ℕᵒᵖ` whose vertex is the constant value**, with the
identity at every level. -/
def natConstCone (Y : D) : Cone ((Functor.const ℕᵒᵖ).obj Y) where
  pt := Y
  π := { app := fun _ => 𝟙 Y, naturality := fun _ _ _ => by simp }

/-- **The constant cone is a limit cone.** A compatible family of maps into the levels of a
constant tower is determined by its level-zero component, because every level receives a morphism
from level zero and the transition maps are identities. -/
def isLimitNatConstCone (Y : D) : IsLimit (natConstCone Y) where
  lift s := s.π.app (op 0)
  fac s j := by
    have h := s.w ((homOfLE (Nat.zero_le j.unop)).op : j ⟶ op 0)
    simp only [Functor.const_obj_map] at h
    simpa [natConstCone] using h.symm
  uniq s m h := (Category.comp_id m).symm.trans (h (op 0))

variable [HasLimitsOfShape ℕᵒᵖ D]

/-- **The limit over `ℕᵒᵖ` of a constant functor is its value.** -/
def limitNatConstIso (Y : D) : limit ((Functor.const ℕᵒᵖ).obj Y) ≅ Y :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _) (isLimitNatConstCone Y)

/-- The isomorphism `limitNatConstIso Y` is the projection of the limit at level zero. -/
@[simp]
theorem limitNatConstIso_hom (Y : D) :
    (limitNatConstIso Y).hom = limit.π ((Functor.const ℕᵒᵖ).obj Y) (op 0) :=
  rfl

/-! ### The sections of a presheaf along a constant tower -/

variable {C : Type u₁} [Category.{v₁} C] (X : C) (F : Cᵒᵖ ⥤ D)

omit [HasLimitsOfShape ℕᵒᵖ D] in
/-- Every transition map of the inverse system of sections along a constant tower is the identity
of the group of sections, the tower's own transition maps being identities. -/
theorem constOp_comp_map {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (((Functor.const ℕ).obj X).op ⋙ F).map f = 𝟙 (F.obj (op X)) :=
  F.map_id (op X)

/-- The inverse system of sections of `F` along a constant tower is the constant functor at the
group of sections. -/
def constOpIso : ((Functor.const ℕ).obj X).op ⋙ F ≅ (Functor.const ℕᵒᵖ).obj (F.obj (op X)) :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun f => by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp, Functor.const_obj_map]
    exact constOp_comp_map X F f

/-- **The sections of a presheaf along a constant tower are its sections at the object the tower
sits at.** -/
def constLimitIso : limit (((Functor.const ℕ).obj X).op ⋙ F) ≅ F.obj (op X) :=
  HasLimit.isoOfNatIso (constOpIso X F) ≪≫ limitNatConstIso (F.obj (op X))

/-- The isomorphism `constLimitIso X F` is the projection of the limit at level zero. -/
@[simp]
theorem constLimitIso_hom :
    (constLimitIso X F).hom = limit.π (((Functor.const ℕ).obj X).op ⋙ F) (op 0) := by
  simp only [constLimitIso, Iso.trans_hom, limitNatConstIso_hom,
    HasLimit.isoOfNatIso_hom_π]
  exact Category.comp_id _

/-- **The identification of the sections along a constant tower is natural**: the map on sections
induced by a morphism of constant towers is the restriction map of the presheaf. -/
theorem constLimitIso_naturality {X Y : C} (g : X ⟶ Y) :
    limMap (Functor.whiskerRight (NatTrans.op ((Functor.const ℕ).map g)) F) ≫
        (constLimitIso X F).hom =
      (constLimitIso Y F).hom ≫ F.map g.op := by
  rw [constLimitIso_hom, constLimitIso_hom, limMap_π]
  rfl

end CategoryTheory.Limits

end
