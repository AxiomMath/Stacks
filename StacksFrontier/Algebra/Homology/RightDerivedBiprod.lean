module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Biproducts
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Right derived functors commute with binary biproducts

A natural transformation between additive functors is sent to a natural transformation of right
derived functors by `CategoryTheory.NatTrans.rightDerived`.  This file records that this
operation is *additive*, and deduces that right derivation commutes with binary biproducts of
functors: `(G₁ ⊞ G₂).rightDerived n ≅ G₁.rightDerived n ⊞ G₂.rightDerived n`.  The companion
fact that a right derived functor vanishes on a zero object, in every degree, is here too: it is
the same missing additivity of `CategoryTheory.Functor.rightDerived` that makes it unavailable
from `CategoryTheory.Functor.map_isZero`.

## Main results

* `CategoryTheory.NatTrans.rightDerived_zero` and
  `CategoryTheory.NatTrans.rightDerived_add`: `NatTrans.rightDerived · n` is additive.
* `CategoryTheory.Functor.isZero_rightDerived_obj`: the right derived functors of an
  additive functor send a zero object to a zero object, in every degree.
* `CategoryTheory.Functor.rightDerivedBiprodIso`: the right derived functors of a binary
  biproduct of additive functors are the binary biproduct of their right derived functors.

## Implementation notes

The additivity statements are proved by computing both sides against a chosen injective
resolution with `CategoryTheory.InjectiveResolution.rightDerived_app_eq`; the only inputs are
that `CategoryTheory.NatTrans.mapHomologicalComplex` is degreewise given by the components of
the natural transformation, and that the homology functor is additive.

The biproduct isomorphism is obtained from `CategoryTheory.Limits.biprod.uniqueUpToIso` applied
to the binary bicone whose maps are the right derived functors of the four structure maps of
`G₁ ⊞ G₂`; its `total` condition is exactly additivity.  This route gives the isomorphism the
expected definitional description, `biprod.lift (NatTrans.rightDerived biprod.fst n)
(NatTrans.rightDerived biprod.snd n)` and dually.

Additivity of `G₁ ⊞ G₂` is not available in Mathlib, because the biproduct of functors is
built by the general limit machinery and so its action on morphisms is not literally the
pointwise biproduct map.  It is supplied here by `CategoryTheory.Functor.biprod_map_eq`, which
expands `(G₁ ⊞ G₂).map h` into its matrix entries using `Limits.biprod.total` in the functor
category and naturality of the projections.
-/

@[expose] public noncomputable section

namespace CategoryTheory

open Category Limits

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

section Preadditive

variable [Preadditive D]

/-- The action of a binary biproduct of functors on a morphism, expanded into its matrix
entries.  This is `Limits.biprod.total` in the functor category combined with naturality of the
two projections. -/
lemma Functor.biprod_map_eq {G₁ G₂ : C ⥤ D} [HasBinaryBiproduct G₁ G₂] {X Y : C} (h : X ⟶ Y) :
    (G₁ ⊞ G₂).map h =
      (biprod.fst : G₁ ⊞ G₂ ⟶ G₁).app X ≫ G₁.map h ≫ (biprod.inl : G₁ ⟶ G₁ ⊞ G₂).app Y +
        (biprod.snd : G₁ ⊞ G₂ ⟶ G₂).app X ≫ G₂.map h ≫
          (biprod.inr : G₂ ⟶ G₁ ⊞ G₂).app Y := by
  have ht : (𝟙 ((G₁ ⊞ G₂).obj Y)) =
      (biprod.fst : G₁ ⊞ G₂ ⟶ G₁).app Y ≫ (biprod.inl : G₁ ⟶ G₁ ⊞ G₂).app Y +
        (biprod.snd : G₁ ⊞ G₂ ⟶ G₂).app Y ≫ (biprod.inr : G₂ ⟶ G₁ ⊞ G₂).app Y := by
    have h0 := congrArg (fun t : (G₁ ⊞ G₂) ⟶ (G₁ ⊞ G₂) => t.app Y)
      (biprod.total (X := G₁) (Y := G₂))
    simp only [NatTrans.comp_app, NatTrans.app_add, NatTrans.id_app] at h0
    exact h0.symm
  rw [← comp_id ((G₁ ⊞ G₂).map h), ht, Preadditive.comp_add]
  rw [← assoc ((G₁ ⊞ G₂).map h) ((biprod.fst : G₁ ⊞ G₂ ⟶ G₁).app Y),
    ← assoc ((G₁ ⊞ G₂).map h) ((biprod.snd : G₁ ⊞ G₂ ⟶ G₂).app Y),
    (biprod.fst : G₁ ⊞ G₂ ⟶ G₁).naturality h,
    (biprod.snd : G₁ ⊞ G₂ ⟶ G₂).naturality h, assoc, assoc]

variable [Preadditive C]

/-- A binary biproduct of additive functors is additive. -/
instance Functor.additive_biprod {G₁ G₂ : C ⥤ D} [G₁.Additive] [G₂.Additive]
    [HasBinaryBiproduct G₁ G₂] : (G₁ ⊞ G₂).Additive where
  map_add {X Y} f g := by
    simp only [Functor.biprod_map_eq, Functor.map_add, Preadditive.comp_add,
      Preadditive.add_comp]
    abel

end Preadditive

variable [Abelian C] [HasInjectiveResolutions C] [Abelian D]

/-- **The right derived functors of an additive functor vanish on a zero object**, in every
degree including degree zero.

Mathlib's `CategoryTheory.Functor.isZero_rightDerived_obj_injective_succ` gives this for an
injective object in positive degrees, where the chosen resolution `InjectiveResolution.self` is
the zero object. A zero object is injective and its own resolution is zero in degree `0` too, so
the same argument reaches degree `0`. This is what `CategoryTheory.Functor.map_isZero` cannot
supply: `CategoryTheory.Functor.rightDerived` has no `Additive` instance in Mathlib. -/
@[ega "0 13.7.7.4" "partial"]
theorem Functor.isZero_rightDerived_obj (F : C ⥤ D) [F.Additive] (n : ℕ) {Z : C}
    (hZ : IsZero Z) : IsZero ((F.rightDerived n).obj Z) := by
  have : Injective Z := Injective.of_iso hZ.isoZero.symm inferInstance
  have h0 : IsZero (InjectiveResolution.self Z).cocomplex := by
    rw [InjectiveResolution.self_cocomplex]
    exact Functor.map_isZero _ hZ
  exact IsZero.of_iso (Functor.map_isZero _ (Functor.map_isZero _ h0))
    ((InjectiveResolution.self Z).isoRightDerivedObj F n)

/-- Right derivation of natural transformations is additive; proved first so that it also
gives the zero case. -/
private theorem NatTrans.rightDerived_add_aux {F G : C ⥤ D} [F.Additive] [G.Additive]
    (α β : F ⟶ G) (n : ℕ) :
    NatTrans.rightDerived (α + β) n =
      NatTrans.rightDerived α n + NatTrans.rightDerived β n := by
  ext X
  simp only [NatTrans.app_add]
  rw [InjectiveResolution.rightDerived_app_eq (α + β) (injectiveResolution X) n,
    InjectiveResolution.rightDerived_app_eq α (injectiveResolution X) n,
    InjectiveResolution.rightDerived_app_eq β (injectiveResolution X) n]
  have h : (NatTrans.mapHomologicalComplex (α + β) (ComplexShape.up ℕ)).app
      (injectiveResolution X).cocomplex =
      (NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app
        (injectiveResolution X).cocomplex +
      (NatTrans.mapHomologicalComplex β (ComplexShape.up ℕ)).app
        (injectiveResolution X).cocomplex := by ext n; simp
  rw [h, Functor.map_add]
  simp only [Preadditive.add_comp, Preadditive.comp_add]

/-- Right derivation of natural transformations kills the zero transformation. -/
theorem NatTrans.rightDerived_zero {F G : C ⥤ D} [F.Additive] [G.Additive] (n : ℕ) :
    NatTrans.rightDerived (0 : F ⟶ G) n = 0 := by
  simpa using NatTrans.rightDerived_add_aux (0 : F ⟶ G) 0 n

/-- Right derivation of natural transformations is additive. -/
theorem NatTrans.rightDerived_add {F G : C ⥤ D} [F.Additive] [G.Additive] (α β : F ⟶ G)
    (n : ℕ) :
    NatTrans.rightDerived (α + β) n =
      NatTrans.rightDerived α n + NatTrans.rightDerived β n :=
  NatTrans.rightDerived_add_aux α β n

variable (G₁ G₂ : C ⥤ D) [G₁.Additive] [G₂.Additive] [HasBinaryBiproduct G₁ G₂] (n : ℕ)

/-- The `n`-th right derived functor of `G₁ ⊞ G₂`, with the right derived functors of the four
structure maps of the biproduct, as a binary bicone on the right derived functors of `G₁` and
`G₂`. -/
def Functor.rightDerivedBinaryBicone : BinaryBicone (G₁.rightDerived n) (G₂.rightDerived n) where
  pt := (G₁ ⊞ G₂).rightDerived n
  fst := NatTrans.rightDerived (biprod.fst : G₁ ⊞ G₂ ⟶ G₁) n
  snd := NatTrans.rightDerived (biprod.snd : G₁ ⊞ G₂ ⟶ G₂) n
  inl := NatTrans.rightDerived (biprod.inl : G₁ ⟶ G₁ ⊞ G₂) n
  inr := NatTrans.rightDerived (biprod.inr : G₂ ⟶ G₁ ⊞ G₂) n
  inl_fst := by
    rw [← NatTrans.rightDerived_comp, biprod.inl_fst, NatTrans.rightDerived_id]
  inl_snd := by
    rw [← NatTrans.rightDerived_comp, biprod.inl_snd, NatTrans.rightDerived_zero]
  inr_fst := by
    rw [← NatTrans.rightDerived_comp, biprod.inr_fst, NatTrans.rightDerived_zero]
  inr_snd := by
    rw [← NatTrans.rightDerived_comp, biprod.inr_snd, NatTrans.rightDerived_id]

/-- The `total` condition for `Functor.rightDerivedBinaryBicone`: additivity of right
derivation applied to `Limits.biprod.total`. -/
lemma Functor.rightDerived_biprod_total :
    NatTrans.rightDerived (biprod.fst : G₁ ⊞ G₂ ⟶ G₁) n ≫
        NatTrans.rightDerived (biprod.inl : G₁ ⟶ G₁ ⊞ G₂) n +
      NatTrans.rightDerived (biprod.snd : G₁ ⊞ G₂ ⟶ G₂) n ≫
        NatTrans.rightDerived (biprod.inr : G₂ ⟶ G₁ ⊞ G₂) n =
      𝟙 ((G₁ ⊞ G₂).rightDerived n) := by
  rw [← NatTrans.rightDerived_comp, ← NatTrans.rightDerived_comp,
    ← NatTrans.rightDerived_add, biprod.total, NatTrans.rightDerived_id]

/-- `Functor.rightDerivedBinaryBicone` is a bilimit: its `total` condition is additivity of
right derivation applied to `Limits.biprod.total`. -/
def Functor.rightDerivedBinaryBicone_isBilimit :
    (Functor.rightDerivedBinaryBicone G₁ G₂ n).IsBilimit :=
  isBinaryBilimitOfTotal _ (Functor.rightDerived_biprod_total G₁ G₂ n)

variable [HasBinaryBiproduct (G₁.rightDerived n) (G₂.rightDerived n)]

/-- **Right derived functors commute with binary biproducts.**  The isomorphism takes the
right derived functor of `G₁ ⊞ G₂` to the biproduct of the right derived functors, by the right
derived functors of the two projections. -/
def Functor.rightDerivedBiprodIso :
    (G₁ ⊞ G₂).rightDerived n ≅ G₁.rightDerived n ⊞ G₂.rightDerived n :=
  biprod.uniqueUpToIso _ _ (Functor.rightDerivedBinaryBicone_isBilimit G₁ G₂ n)

/-- The isomorphism of `Functor.rightDerivedBiprodIso` is the lift of the right derived
projections. -/
lemma Functor.rightDerivedBiprodIso_hom :
    (Functor.rightDerivedBiprodIso G₁ G₂ n).hom =
      biprod.lift (NatTrans.rightDerived (biprod.fst : G₁ ⊞ G₂ ⟶ G₁) n)
        (NatTrans.rightDerived (biprod.snd : G₁ ⊞ G₂ ⟶ G₂) n) :=
  rfl

/-- The inverse of `Functor.rightDerivedBiprodIso` is the description by the right derived
inclusions. -/
lemma Functor.rightDerivedBiprodIso_inv :
    (Functor.rightDerivedBiprodIso G₁ G₂ n).inv =
      biprod.desc (NatTrans.rightDerived (biprod.inl : G₁ ⟶ G₁ ⊞ G₂) n)
        (NatTrans.rightDerived (biprod.inr : G₂ ⟶ G₁ ⊞ G₂) n) :=
  rfl

end CategoryTheory

end
