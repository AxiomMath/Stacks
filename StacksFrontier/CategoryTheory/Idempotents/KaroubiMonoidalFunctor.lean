module

public import StacksFrontier.CategoryTheory.Idempotents.KaroubiMonoidal

/-!
# `toKaroubi` is a symmetric monoidal functor

`CategoryTheory.Idempotents.Karoubi.monoidalCategory` makes the Karoubi envelope of a monoidal
category `C` monoidal, with `(X, p) ⊗ (Y, q) = (X ⊗ Y, p ⊗ q)` and unit `(𝟙_ C, 𝟙)`. This file
records that the canonical functor `toKaroubi C : C ⥤ Karoubi C`, `X ↦ (X, 𝟙)`, is compatible
with that structure: it is monoidal, braided and symmetric, its unit and tensor comparison
morphisms being the identities of `C`, because `(X, 𝟙) ⊗ (Y, 𝟙) = (X ⊗ Y, 𝟙 ⊗ 𝟙)` and
`𝟙 ⊗ 𝟙 = 𝟙`.

The consequence recorded at the end is that for an idempotent complete monoidal category `C`
both halves of the equivalence `toKaroubiEquivalence C : C ≌ Karoubi C` are monoidal: Karoubi
completion does not change a category that is already idempotent complete, monoidal structure
included.

## Main definitions

* `CategoryTheory.Idempotents.toKaroubiCoreMonoidal`: the monoidal structure on `toKaroubi C`,
  as a `Functor.CoreMonoidal`.

## Main results

* `CategoryTheory.Idempotents.toKaroubiMonoidal`: `toKaroubi C` is monoidal.
* `CategoryTheory.Idempotents.toKaroubiBraided`: `toKaroubi C` is braided, hence symmetric
  monoidal when `C` is symmetric.
* `CategoryTheory.Idempotents.toKaroubiEquivalenceFunctorMonoidal` and
  `CategoryTheory.Idempotents.toKaroubiInverseMonoidal`: for `C` idempotent complete both the
  functor and the inverse of `toKaroubiEquivalence C` are monoidal.

## Implementation notes

Mathlib has no monoidal structure on `Karoubi C` at all, so neither of these statements can be
made there; the monoidal structure used is the one in
`StacksFrontier.CategoryTheory.Idempotents.KaroubiMonoidal`.

Each coherence identity reduces by `Karoubi.hom_ext` to an identity in `C`, the idempotents
involved all being identities. `Functor.CoreMonoidal` is used rather than
`Functor.LaxMonoidal`, because the comparison morphisms are isomorphisms and the braided
structure needs them to be.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Category Functor

universe v u

namespace CategoryTheory.Idempotents

section OfComm

variable {C : Type u} [Category.{v} C]

/-- Every morphism of a Karoubi envelope is an `ofComm`: the idempotent of its source is
absorbed into it. -/
theorem Karoubi.eq_ofComm {P Q : Karoubi C} (f : P ⟶ Q) :
    f = Karoubi.ofComm f.f (by rw [Karoubi.p_comp, Karoubi.comp_p]) := by
  apply Karoubi.hom_ext
  rw [Karoubi.ofComm_f, Karoubi.p_comp]

end OfComm

section Monoidal

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

/-- The monoidal structure of `toKaroubi C : C ⥤ Karoubi C`: the unit and tensor comparison
morphisms are the identities of `C`, because `(X, 𝟙) ⊗ (Y, 𝟙) = (X ⊗ Y, 𝟙 ⊗ 𝟙)` and
`𝟙 ⊗ 𝟙 = 𝟙`. -/
def toKaroubiCoreMonoidal : (toKaroubi C).CoreMonoidal where
  εIso := Iso.refl _
  μIso X Y := Karoubi.isoOfIso (Iso.refl (X ⊗ Y)) (by simp)
  μIso_hom_natural_left f X' := by apply Karoubi.hom_ext; simp [Karoubi.ofComm_f]
  μIso_hom_natural_right X' f := by apply Karoubi.hom_ext; simp [Karoubi.ofComm_f]
  associativity X Y Z := by
    apply Karoubi.hom_ext
    simp [Karoubi.ofComm_f, Karoubi.associator_hom]
  left_unitality X := by
    apply Karoubi.hom_ext
    simp [Karoubi.ofComm_f, Karoubi.leftUnitor_hom]
  right_unitality X := by
    apply Karoubi.hom_ext
    simp [Karoubi.ofComm_f, Karoubi.rightUnitor_hom]

/-- `toKaroubi C : C ⥤ Karoubi C` is a monoidal functor, for the monoidal structure
`(X, p) ⊗ (Y, q) = (X ⊗ Y, p ⊗ q)` on the Karoubi envelope. -/
instance toKaroubiMonoidal : (toKaroubi C).Monoidal :=
  (toKaroubiCoreMonoidal C).toMonoidal

/-- The unit comparison morphism of `toKaroubi C` is an identity. -/
@[simp] theorem toKaroubi_ε_f : (LaxMonoidal.ε (toKaroubi C)).f = 𝟙 (𝟙_ C) := rfl

/-- The tensor comparison morphism of `toKaroubi C` is an identity. -/
@[simp] theorem toKaroubi_μ_f (X Y : C) :
    (LaxMonoidal.μ (toKaroubi C) X Y).f = 𝟙 (X ⊗ Y) := by
  show (𝟙 X ⊗ₘ 𝟙 Y) ≫ 𝟙 (X ⊗ Y) = 𝟙 (X ⊗ Y)
  rw [MonoidalCategory.id_tensorHom_id, comp_id]

end Monoidal

section Braided

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- `toKaroubi C : C ⥤ Karoubi C` is a lax braided functor: the commutativity constraint of
`Karoubi C` is that of `C` cut down by the idempotents, which here are identities. -/
instance toKaroubiLaxBraided : (toKaroubi C).LaxBraided where
  braided X Y := by
    apply Karoubi.hom_ext
    simp [Karoubi.braiding_hom, Karoubi.ofComm_f]

/-- `toKaroubi C : C ⥤ Karoubi C` is a braided functor; for `C` symmetric monoidal this says it
is a symmetric monoidal functor. -/
instance toKaroubiBraided : (toKaroubi C).Braided where

end Braided

section IdempotentComplete

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [IsIdempotentComplete C]

/-- The functor of `toKaroubiEquivalence C` is `toKaroubi C`, hence monoidal. -/
instance toKaroubiEquivalenceFunctorMonoidal :
    (toKaroubiEquivalence C).functor.Monoidal :=
  inferInstanceAs (toKaroubi C).Monoidal

/-- For `C` idempotent complete the inverse of `toKaroubiEquivalence C : C ≌ Karoubi C` is
monoidal, `toKaroubi C` being monoidal. -/
noncomputable instance toKaroubiInverseMonoidal :
    (toKaroubiEquivalence C).inverse.Monoidal :=
  (toKaroubiEquivalence C).inverseMonoidal

end IdempotentComplete

end CategoryTheory.Idempotents

end
