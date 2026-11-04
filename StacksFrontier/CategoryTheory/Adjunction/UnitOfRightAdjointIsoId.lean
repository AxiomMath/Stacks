module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# The unit of an adjunction whose right adjoint is the identity functor

Let `adj : F ⊣ G` be an adjunction between endofunctors of a category `C` and let
`e : G ≅ 𝟭 C` identify the right adjoint with the identity functor. Then `F` is identified
with the identity functor too, by Mathlib's `CategoryTheory.Adjunction.leftAdjointIdIso`, and
the unit of `adj` read through `e` is a natural transformation `𝟭 C ⟶ F`, namely
`X ↦ adj.unit.app X ≫ e.hom.app (F.obj X)`.

The two are mutually inverse: the composite `X ⟶ F X ⟶ X` is the identity. So the canonical
map `X ⟶ F X` carried by the adjunction is not merely some isomorphism, it is the inverse of
the comparison of `F` with the identity functor.

The comparison itself is available in two shapes, as the mate `leftAdjointIdIso adj e` and as
the comparison of `F` and `𝟭 C` as two left adjoints of `G`; they agree.

## Main definitions

* `CategoryTheory.Adjunction.unitToLeftAdjoint` — the unit of `adj : F ⊣ G`, read through an
  identification `e : G ≅ 𝟭 C`, as a natural transformation `𝟭 C ⟶ F`.

## Main results

* `CategoryTheory.Adjunction.unit_comp_map_leftAdjointIdIso_hom_app` — the adjunct of the
  comparison `leftAdjointIdIso adj e : F ≅ 𝟭 C` is `e.inv`.
* `CategoryTheory.Adjunction.unitToLeftAdjoint_comp_leftAdjointIdIso_hom` — the composite of
  `unitToLeftAdjoint adj e` with that comparison is the identity.
* `CategoryTheory.Adjunction.leftAdjointIdIso_inv_eq_unitToLeftAdjoint` — equivalently, that
  comparison has the unit as its inverse.
* `CategoryTheory.Adjunction.leftAdjointUniq_id_ofNatIsoRight` — the comparison of `F` and
  `𝟭 C` as left adjoints of `G` is that same mate.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

universe v u

variable {C : Type u} [Category.{v} C] {F G : C ⥤ C}

/-- The adjunct of the comparison `leftAdjointIdIso adj e : F ≅ 𝟭 C` of the left adjoint with
the identity functor is the inverse of the identification `e : G ≅ 𝟭 C` of the right adjoint
with the identity functor. -/
@[reassoc]
theorem unit_comp_map_leftAdjointIdIso_hom_app (adj : F ⊣ G) (e : G ≅ 𝟭 C) (X : C) :
    adj.unit.app X ≫ G.map ((leftAdjointIdIso adj e).hom.app X) = e.inv.app X := by
  have h := adj.unit.naturality (e.inv.app X)
  dsimp at h
  rw [leftAdjointIdIso_hom_app, Functor.map_comp]
  simp only [← Category.assoc, ← h]
  simp

/-- The unit of an adjunction `adj : F ⊣ G` whose right adjoint is identified with the identity
functor by `e : G ≅ 𝟭 C`, as a natural transformation `𝟭 C ⟶ F`. -/
@[simps]
def unitToLeftAdjoint (adj : F ⊣ G) (e : G ≅ 𝟭 C) : 𝟭 C ⟶ F where
  app X := adj.unit.app X ≫ e.hom.app (F.obj X)
  naturality X Y f := by
    have h₁ := adj.unit.naturality f
    have h₂ := e.hom.naturality (F.map f)
    dsimp at h₁ h₂ ⊢
    rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

/-- The composite `X ⟶ F X ⟶ X` of the unit of `adj : F ⊣ G`, read through an identification
`e : G ≅ 𝟭 C` of the right adjoint with the identity functor, with the induced comparison of
the left adjoint with the identity functor, is the identity. -/
@[reassoc (attr := simp)]
theorem unitToLeftAdjoint_comp_leftAdjointIdIso_hom_app (adj : F ⊣ G) (e : G ≅ 𝟭 C) (X : C) :
    (unitToLeftAdjoint adj e).app X ≫ (leftAdjointIdIso adj e).hom.app X = 𝟙 X := by
  have h := e.hom.naturality ((leftAdjointIdIso adj e).hom.app X)
  dsimp at h
  rw [unitToLeftAdjoint_app, Category.assoc, ← h, ← Category.assoc,
    unit_comp_map_leftAdjointIdIso_hom_app]
  simp

/-- `CategoryTheory.Adjunction.unitToLeftAdjoint` is a section of the comparison
`CategoryTheory.Adjunction.leftAdjointIdIso` of the left adjoint with the identity functor. -/
theorem unitToLeftAdjoint_comp_leftAdjointIdIso_hom (adj : F ⊣ G) (e : G ≅ 𝟭 C) :
    unitToLeftAdjoint adj e ≫ (leftAdjointIdIso adj e).hom = 𝟙 (𝟭 C) := by
  ext X
  simpa using unitToLeftAdjoint_comp_leftAdjointIdIso_hom_app adj e X

/-- The comparison of the left adjoint with the identity functor has the unit of the adjunction
as its inverse. -/
theorem leftAdjointIdIso_inv_eq_unitToLeftAdjoint (adj : F ⊣ G) (e : G ≅ 𝟭 C) :
    (leftAdjointIdIso adj e).inv = unitToLeftAdjoint adj e := by
  rw [← Category.id_comp (leftAdjointIdIso adj e).inv,
    ← unitToLeftAdjoint_comp_leftAdjointIdIso_hom adj e, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- The comparison of `F` with `𝟭 C` as two left adjoints of `G`, for the adjunction
`𝟭 C ⊣ G` transported from the identity adjunction along `e : 𝟭 C ≅ G`, is the mate of `e`. -/
theorem leftAdjointUniq_id_ofNatIsoRight (adj : F ⊣ G) (e : 𝟭 C ≅ G) :
    leftAdjointUniq adj (Adjunction.id.ofNatIsoRight e) = leftAdjointIdIso adj e.symm := by
  refine Iso.ext (NatTrans.ext (funext fun X ↦ ?_))
  refine (adj.homEquiv X X).injective ?_
  rw [homEquiv_unit, homEquiv_unit, unit_leftAdjointUniq_hom_app,
    unit_comp_map_leftAdjointIdIso_hom_app]
  simp

end CategoryTheory.Adjunction

end
