module

public import Mathlib.CategoryTheory.Shift.CommShiftTwo

/-!
# Transporting a two-variable shift commutation along an isomorphism of bifunctors

Let `G, G' : C₁ ⥤ C₂ ⥤ D` be bifunctors and `e : G ≅ G'` an isomorphism between them.  This file
transports `CategoryTheory.Functor.CommShift₂` from `G` to `G'`, which is the two-variable
analogue of Mathlib's one-variable `CategoryTheory.Functor.CommShift.ofIso`.

## Main results

* `CategoryTheory.Functor.CommShift₂.ofIso`: **a bifunctor isomorphic to one which commutes with
  the shifts in both variables commutes with them too.**
* `CategoryTheory.Functor.CommShift₂.ofIsoInt`: the same for the standard `ℤ` setup
  `CategoryTheory.CommShift₂Setup.int`, i.e. `CategoryTheory.Functor.CommShift₂Int`.

## Implementation notes

**Why this is needed at all.**  `CategoryTheory.Functor.CommShift₂` is a class carrying *data* —
a `CategoryTheory.Functor.CommShift` structure on `G.obj X₁` for each `X₁` and on `G.flip.obj X₂`
for each `X₂` — so it does not transport along an isomorphism for free.  Mathlib provides the
one-variable transport `CategoryTheory.Functor.CommShift.ofIso` and the two closure properties
`CategoryTheory.Functor.CommShift₂.precomp₁`, `precomp₂`, but no transport along an isomorphism of
bifunctors.  The motivating use is the derived tensor product of [Stacks, Tag 06YU].
Its canonical structure carries its shift datum as the field
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.commShift₂`; transporting the datum of
`CochainComplex.KFlatBifunctor.derivedBifunctor` along the comparison isomorphism gives a second
description of it, `Stacks.SheafOfModules.DerivedMonoidal.canonicalTensor_commShift₂Int` (equal to
the field by `Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedTensorProduct_commShift₂_eq`),
for which the comparison is shift-compatible by construction.  That is what moving a statement
between the two bifunctors needs.

**Where the content is.**  Four of the five fields are the one-variable transport, twice, and the
observation that `G'.map f` is the `e`-conjugate of `G.map f`, whose two outer factors commute
with the shift by `CategoryTheory.Functor.CommShift.ofIso_compatibility` — exactly because the
transported structure is *defined* to make `e` shift-compatible.

All of the work is in the sign coherence `comm`.  Expanding the four occurrences of
`commShiftIso` by `CategoryTheory.Functor.CommShift.ofIso_commShiftIso_hom_app` puts an
`e`-conjugate around each; two adjacent pairs cancel outright, and what remains is `G`'s own
`comm` with the component `(e.hom.app X₁).app X₂` of `e` pushed from the left of
`shiftFunctorComm` and of the sign to its right.  That push is the naturality of
`CategoryTheory.shiftFunctorComm` together with the naturality of `h.ε m n`, which is a morphism
of the identity functor — the two facts the one-variable transport does not have to confront.
-/

@[expose] public section

namespace CategoryTheory

open Category CategoryTheory.Functor

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]

namespace Functor.CommShift₂

variable {M : Type*} [AddCommMonoid M] [HasShift C₁ M] [HasShift C₂ M] [HasShift D M]
  {G G' : C₁ ⥤ C₂ ⥤ D} (e : G ≅ G') (h : CommShift₂Setup D M) [G.CommShift₂ h]

/-- The isomorphism `e` read in the flipped variables: `G.flip ≅ G'.flip`, with components
`(e.hom.app X₁).app X₂` in the other order. -/
abbrev flipIso : G.flip ≅ G'.flip := (flipFunctor C₁ C₂ D).mapIso e

/-- A functor isomorphic to another acts on a morphism by the conjugate of its action.  This is
the form in which the two naturality fields of `CategoryTheory.Functor.CommShift₂` are reduced to
the shift compatibility of the isomorphism. -/
private theorem map_eq_conj {A B : Type*} [Category* A] [Category* B] {F F' : A ⥤ B} (ee : F ≅ F')
    {X Y : A} (f : X ⟶ Y) : F'.map f = (ee.app X).inv ≫ F.map f ≫ (ee.app Y).hom := by
  rw [Iso.app_inv, Iso.app_hom, ee.hom.naturality f, ← Category.assoc, ee.inv_hom_id_app,
    Category.id_comp]

/-- **A bifunctor isomorphic to one which commutes with the shifts in both variables commutes
with them too.**  The two families of `CategoryTheory.Functor.CommShift` structures are the
one-variable `CategoryTheory.Functor.CommShift.ofIso` at the components of `e` and of its flip;
the two naturality fields hold because `G'.map f` is the `e`-conjugate of `G.map f` and `e` is
shift-compatible for the transported structure; and the sign coherence is `G`'s, conjugated. -/
@[instance_reducible]
def ofIso : G'.CommShift₂ h where
  commShiftObj X₁ := CommShift.ofIso (e.app X₁) M
  commShiftFlipObj X₂ := CommShift.ofIso ((flipIso e).app X₂) M
  commShift_map {X₁ Y₁} f := by
    have h₁ := CommShift.ofIso_compatibility (e.app X₁) M
    have h₂ := CommShift.ofIso_compatibility (e.app Y₁) M
    rw [map_eq_conj e f]
    infer_instance
  commShift_flip_map {X₂ Y₂} g := by
    have h₁ := CommShift.ofIso_compatibility ((flipIso e).app X₂) M
    have h₂ := CommShift.ofIso_compatibility ((flipIso e).app Y₂) M
    rw [map_eq_conj (flipIso e) g]
    infer_instance
  comm X₁ X₂ m n := by
    -- the components of `e`, and the fact that they cancel after being shifted
    have key : ∀ (Y : C₁) (Z : C₂), (e.hom.app Y).app Z ≫ (e.inv.app Y).app Z = 𝟙 _ := fun Y Z => by
      simp
    have cancel : ∀ (k : M) (Y : C₁) (Z : C₂) {W : D}
        (g : ((shiftFunctor D k).obj ((G.obj Y).obj Z)) ⟶ W),
        (shiftFunctor D k).map ((e.hom.app Y).app Z) ≫
            (shiftFunctor D k).map ((e.inv.app Y).app Z) ≫ g = g := by
      intro k Y Z W g
      rw [← Category.assoc, ← Functor.map_comp, key, Functor.map_id, Category.id_comp]
    -- the two facts the one-variable transport does not meet: `shiftFunctorComm` and the sign
    -- are natural in the object
    have hsc := ((shiftFunctorComm D m n).inv.naturality ((e.hom.app X₁).app X₂)).symm
    have hε := ((h.ε m n).val.naturality
      ((shiftFunctor D n).map ((shiftFunctor D m).map ((e.hom.app X₁).app X₂)))).symm
    simp only [CommShift.ofIso_commShiftIso_hom_app, flipIso, flipFunctor_map_app_app,
      Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv, Functor.map_comp,
      Category.assoc, cancel]
    rw [G.commShift₂_comm_assoc h X₁ X₂ m n]
    simp only [Iso.app_inv, Functor.comp_map] at hsc hε ⊢
    rw [hε, reassoc_of% hsc]

/-- **The isomorphism is itself compatible with the shifts in both variables**, for the
transported structure.  Each half is Mathlib's one-variable
`CategoryTheory.Functor.CommShift.ofIso_compatibility`, in the second variable at the components
of `e` and in the first at the components of its flip. -/
theorem ofIso_commShift₂ :
    letI := ofIso e h
    NatTrans.CommShift₂ e.hom h :=
  let := ofIso e h
  { commShift_app X₁ := CommShift.ofIso_compatibility (e.app X₁) M
    commShift_flipApp X₂ := CommShift.ofIso_compatibility ((flipIso e).app X₂) M }

section Int

variable [Preadditive D] [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] {G G' : C₁ ⥤ C₂ ⥤ D} (e : G ≅ G') [G.CommShift₂Int]

/-- **A bifunctor isomorphic to one which commutes with the shifts by `ℤ` in both variables
commutes with them too**, with Mathlib's sign `(-1) ^ (p * q)`.  This is
`CategoryTheory.Functor.CommShift₂.ofIso` at the standard setup
`CategoryTheory.CommShift₂Setup.int`. -/
@[instance_reducible]
noncomputable def ofIsoInt : G'.CommShift₂Int := ofIso e CommShift₂Setup.int

/-- `CategoryTheory.Functor.CommShift₂.ofIso_commShift₂` at the standard `ℤ` setup. -/
theorem ofIsoInt_commShift₂ :
    letI := ofIsoInt e
    NatTrans.CommShift₂Int e.hom :=
  ofIso_commShift₂ e CommShift₂Setup.int

end Int

end Functor.CommShift₂

end CategoryTheory

end
