module

public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-! # The componentwise biproduct of two short complexes

This file adds to `Mathlib.Algebra.Homology.ShortComplex.Preadditive` the componentwise binary
biproduct of two short complexes and its homology.

For short complexes `S₁` and `S₂` in a category with zero morphisms and binary biproducts,
`ShortComplex.biprodMk S₁ S₂` is the short complex
`S₁.X₁ ⊞ S₂.X₁ ⟶ S₁.X₂ ⊞ S₂.X₂ ⟶ S₁.X₃ ⊞ S₂.X₃` with differentials `biprod.map S₁.f S₂.f` and
`biprod.map S₁.g S₂.g`. It comes with the projections `biprodFst`, `biprodSnd` and the
inclusions `biprodInl`, `biprodInr`, which satisfy the biproduct identities, and also
`biprod_total` in a preadditive category. In a preadditive category with homology:

* `ShortComplex.homologyBiprodIso S₁ S₂ : (biprodMk S₁ S₂).homology ≅ S₁.homology ⊞ S₂.homology`:
  homology commutes with the componentwise biproduct; `homologyBiprodIso_hom_fst`,
  `homologyBiprodIso_hom_snd`, `inl_homologyBiprodIso_inv` and `inr_homologyBiprodIso_inv`
  identify it on the projections and the inclusions;
* `ShortComplex.exact_biprodMk_iff`: the componentwise biproduct of two short complexes is exact
  if and only if both of them are; `ShortComplex.exact_biprodMk` is the "if" direction.

They are used in the proof of Stacks 02MX (2), where `ℤ/2`-graded complexes `X₀ ⇄ X₁` are added
by taking componentwise biproducts: `exact_biprodMk` shows that a sum of two exact ones is exact,
and `homologyBiprodIso` computes the homology of a sum summand by summand.

## Implementation notes

* `biprodMk` is an `abbrev`, so its differentials are `biprod.map S₁.f S₂.f` and
  `biprod.map S₁.g S₂.g` at reducible transparency: its `zero` field and `exact_biprodMk` apply
  directly to a short complex written with these differentials.
* The name `biprodMk`, rather than `biprod`, leaves `biprod` to `Limits.biprod` inside the
  namespace `ShortComplex`.
* The lemmas `homologyBiprodIso_hom` and `homologyBiprodIso_inv`, which unfold
  `homologyBiprodIso`, are not simp lemmas; the simp lemmas are its components, as for
  `HomologicalComplex.biprodXIso`. This way `simp` still proves
  `(homologyBiprodIso S₁ S₂).hom ≫ (homologyBiprodIso S₁ S₂).inv = 𝟙 _`.
* For products indexed by a type, see `ShortComplex.pi` in
  `StacksCore.Algebra.Homology.ShortComplex.Products`; there the comparison of homologies,
  `ShortComplex.piHomologyIso`, needs an abelian category with exact products.
-/

@[expose] public section

namespace CategoryTheory.ShortComplex

open Limits

variable {C : Type*} [Category* C]

section HasZeroMorphisms

variable [HasZeroMorphisms C] [HasBinaryBiproducts C] (S₁ S₂ : ShortComplex C)

/-- The componentwise biproduct `S₁.X₁ ⊞ S₂.X₁ ⟶ S₁.X₂ ⊞ S₂.X₂ ⟶ S₁.X₃ ⊞ S₂.X₃` of two short
complexes, with differentials `biprod.map S₁.f S₂.f` and `biprod.map S₁.g S₂.g`. -/
noncomputable abbrev biprodMk : ShortComplex C :=
  ShortComplex.mk (biprod.map S₁.f S₂.f) (biprod.map S₁.g S₂.g) (by ext <;> simp)

/-- The projection `biprodMk S₁ S₂ ⟶ S₁`, given componentwise by `biprod.fst`. -/
@[simps]
noncomputable def biprodFst : biprodMk S₁ S₂ ⟶ S₁ where
  τ₁ := biprod.fst
  τ₂ := biprod.fst
  τ₃ := biprod.fst

/-- The projection `biprodMk S₁ S₂ ⟶ S₂`, given componentwise by `biprod.snd`. -/
@[simps]
noncomputable def biprodSnd : biprodMk S₁ S₂ ⟶ S₂ where
  τ₁ := biprod.snd
  τ₂ := biprod.snd
  τ₃ := biprod.snd

/-- The inclusion `S₁ ⟶ biprodMk S₁ S₂`, given componentwise by `biprod.inl`. -/
@[simps]
noncomputable def biprodInl : S₁ ⟶ biprodMk S₁ S₂ where
  τ₁ := biprod.inl
  τ₂ := biprod.inl
  τ₃ := biprod.inl

/-- The inclusion `S₂ ⟶ biprodMk S₁ S₂`, given componentwise by `biprod.inr`. -/
@[simps]
noncomputable def biprodInr : S₂ ⟶ biprodMk S₁ S₂ where
  τ₁ := biprod.inr
  τ₂ := biprod.inr
  τ₃ := biprod.inr

/-- The first inclusion followed by the first projection is the identity. -/
@[reassoc (attr := simp)]
lemma biprodInl_biprodFst : biprodInl S₁ S₂ ≫ biprodFst S₁ S₂ = 𝟙 _ := by
  ext <;> simp

/-- The second inclusion followed by the second projection is the identity. -/
@[reassoc (attr := simp)]
lemma biprodInr_biprodSnd : biprodInr S₁ S₂ ≫ biprodSnd S₁ S₂ = 𝟙 _ := by
  ext <;> simp

/-- The first inclusion followed by the second projection is zero. -/
@[reassoc (attr := simp)]
lemma biprodInl_biprodSnd : biprodInl S₁ S₂ ≫ biprodSnd S₁ S₂ = 0 := by
  ext <;> simp

/-- The second inclusion followed by the first projection is zero. -/
@[reassoc (attr := simp)]
lemma biprodInr_biprodFst : biprodInr S₁ S₂ ≫ biprodFst S₁ S₂ = 0 := by
  ext <;> simp

end HasZeroMorphisms

section Preadditive

variable [Preadditive C] [HasBinaryBiproducts C] (S₁ S₂ : ShortComplex C)

/-- The projections and inclusions of `biprodMk S₁ S₂` satisfy
`biprodFst ≫ biprodInl + biprodSnd ≫ biprodInr = 𝟙 _`, as for `Limits.biprod.total`. -/
@[simp]
lemma biprod_total :
    biprodFst S₁ S₂ ≫ biprodInl S₁ S₂ + biprodSnd S₁ S₂ ≫ biprodInr S₁ S₂ = 𝟙 _ := by
  ext <;> simp

variable [CategoryWithHomology C]

/-- Homology commutes with the componentwise biproduct: the homology of `biprodMk S₁ S₂` is the
biproduct of the homologies of `S₁` and `S₂`, through the maps induced by the projections and
the inclusions. -/
@[simps -isSimp]
noncomputable def homologyBiprodIso : (biprodMk S₁ S₂).homology ≅ S₁.homology ⊞ S₂.homology where
  hom := biprod.lift (homologyMap (biprodFst S₁ S₂)) (homologyMap (biprodSnd S₁ S₂))
  inv := biprod.desc (homologyMap (biprodInl S₁ S₂)) (homologyMap (biprodInr S₁ S₂))
  hom_inv_id := by
    rw [biprod.lift_desc, ← homologyMap_comp, ← homologyMap_comp, ← homologyMap_add,
      biprod_total, homologyMap_id]
  inv_hom_id := by
    ext <;> simp [← homologyMap_comp]

/-- `homologyBiprodIso` followed by the first projection is the map on homology induced by
`biprodFst`. -/
@[reassoc (attr := simp)]
lemma homologyBiprodIso_hom_fst :
    (homologyBiprodIso S₁ S₂).hom ≫ biprod.fst = homologyMap (biprodFst S₁ S₂) := by
  rw [homologyBiprodIso_hom, biprod.lift_fst]

/-- `homologyBiprodIso` followed by the second projection is the map on homology induced by
`biprodSnd`. -/
@[reassoc (attr := simp)]
lemma homologyBiprodIso_hom_snd :
    (homologyBiprodIso S₁ S₂).hom ≫ biprod.snd = homologyMap (biprodSnd S₁ S₂) := by
  rw [homologyBiprodIso_hom, biprod.lift_snd]

/-- The first inclusion followed by the inverse of `homologyBiprodIso` is the map on homology
induced by `biprodInl`. -/
@[reassoc (attr := simp)]
lemma inl_homologyBiprodIso_inv :
    biprod.inl ≫ (homologyBiprodIso S₁ S₂).inv = homologyMap (biprodInl S₁ S₂) := by
  rw [homologyBiprodIso_inv, biprod.inl_desc]

/-- The second inclusion followed by the inverse of `homologyBiprodIso` is the map on homology
induced by `biprodInr`. -/
@[reassoc (attr := simp)]
lemma inr_homologyBiprodIso_inv :
    biprod.inr ≫ (homologyBiprodIso S₁ S₂).inv = homologyMap (biprodInr S₁ S₂) := by
  rw [homologyBiprodIso_inv, biprod.inr_desc]

/-- The inverse of `homologyBiprodIso` followed by the map on homology induced by `biprodFst` is
the first projection. -/
@[reassoc (attr := simp)]
lemma homologyBiprodIso_inv_homologyMap_biprodFst :
    (homologyBiprodIso S₁ S₂).inv ≫ homologyMap (biprodFst S₁ S₂) = biprod.fst := by
  rw [← homologyBiprodIso_hom_fst, Iso.inv_hom_id_assoc]

/-- The inverse of `homologyBiprodIso` followed by the map on homology induced by `biprodSnd` is
the second projection. -/
@[reassoc (attr := simp)]
lemma homologyBiprodIso_inv_homologyMap_biprodSnd :
    (homologyBiprodIso S₁ S₂).inv ≫ homologyMap (biprodSnd S₁ S₂) = biprod.snd := by
  rw [← homologyBiprodIso_hom_snd, Iso.inv_hom_id_assoc]

/-- The map on homology induced by `biprodInl` followed by `homologyBiprodIso` is the first
inclusion. -/
@[reassoc (attr := simp)]
lemma homologyMap_biprodInl_homologyBiprodIso_hom :
    homologyMap (biprodInl S₁ S₂) ≫ (homologyBiprodIso S₁ S₂).hom = biprod.inl := by
  rw [← inl_homologyBiprodIso_inv, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The map on homology induced by `biprodInr` followed by `homologyBiprodIso` is the second
inclusion. -/
@[reassoc (attr := simp)]
lemma homologyMap_biprodInr_homologyBiprodIso_hom :
    homologyMap (biprodInr S₁ S₂) ≫ (homologyBiprodIso S₁ S₂).hom = biprod.inr := by
  rw [← inr_homologyBiprodIso_inv, Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable {S₁ S₂}

/-- The componentwise biproduct of two short complexes is exact if and only if both of them
are exact. -/
lemma exact_biprodMk_iff : (biprodMk S₁ S₂).Exact ↔ S₁.Exact ∧ S₂.Exact := by
  rw [exact_iff_isZero_homology, exact_iff_isZero_homology, exact_iff_isZero_homology,
    (homologyBiprodIso S₁ S₂).isZero_iff, biprod_isZero_iff]

/-- The componentwise biproduct of two exact short complexes is exact. -/
lemma exact_biprodMk (h₁ : S₁.Exact) (h₂ : S₂.Exact) : (biprodMk S₁ S₂).Exact :=
  exact_biprodMk_iff.2 ⟨h₁, h₂⟩

end Preadditive

end CategoryTheory.ShortComplex
