module

public import StacksCore.CategoryTheory.Preadditive.AdditiveFunctor

import StacksCore.Tactic.StacksAttribute

/-!
# Characterisations of additive functors

Stacks, Homological Algebra, Lemma 12.7.1 (0DLP): for a functor `G` between preadditive
categories with zero objects and binary biproducts, `G` is additive if and only if the comparison
maps `G.obj X ⊞ G.obj Y ⟶ G.obj (X ⊞ Y)` are isomorphisms, if and only if the comparison maps
`G.obj (X ⊞ Y) ⟶ G.obj X ⊞ G.obj Y` are isomorphisms. No assumption that `G` preserves zero
morphisms is made: this is deduced from the case `X = Y = 0`.

## Main results

* `CategoryTheory.Functor.additive_of_isIso_biprodComparison`: (3) ⇒ (1).
* `CategoryTheory.Functor.additive_of_isIso_biprodComparison'`: (2) ⇒ (1).
* `CategoryTheory.Functor.tfae_additive`: the three conditions are equivalent.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

open ZeroObject

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D] (G : C ⥤ D)

/-- For an additive functor, the composite of the comparison maps
`G.obj (X ⊞ Y) ⟶ G.obj X ⊞ G.obj Y ⟶ G.obj (X ⊞ Y)` is the identity. -/
lemma biprodComparison_comp_biprodComparison' [G.Additive] (X Y : C) :
    G.biprodComparison X Y ≫ G.biprodComparison' X Y = 𝟙 (G.obj (X ⊞ Y)) := by
  rw [biprodComparison', biprod.desc_eq, Preadditive.comp_add, biprodComparison_fst_assoc,
    biprodComparison_snd_assoc, ← G.map_comp, ← G.map_comp, ← G.map_add, biprod.total, G.map_id]

variable [HasZeroObject C]

/-- If the comparison map `G.obj (0 ⊞ 0) ⟶ G.obj 0 ⊞ G.obj 0` is an isomorphism, then `G` maps
the zero object to a zero object. -/
lemma isZero_obj_zero_of_isIso_biprodComparison [IsIso (G.biprodComparison 0 0)] :
    IsZero (G.obj 0) := by
  have h : (biprod.fst : G.obj 0 ⊞ G.obj 0 ⟶ G.obj 0) = biprod.snd := by
    rw [← cancel_epi (G.biprodComparison 0 0), biprodComparison_fst, biprodComparison_snd,
      (isZero_zero C).eq_of_tgt (biprod.fst : (0 : C) ⊞ 0 ⟶ 0) biprod.snd]
  rw [IsZero.iff_id_eq_zero, ← biprod.inl_fst (X := G.obj 0) (Y := G.obj 0), h, biprod.inl_snd]

/-- If the comparison map `G.obj 0 ⊞ G.obj 0 ⟶ G.obj (0 ⊞ 0)` is an isomorphism, then `G` maps
the zero object to a zero object. -/
lemma isZero_obj_zero_of_isIso_biprodComparison' [IsIso (G.biprodComparison' 0 0)] :
    IsZero (G.obj 0) := by
  have h : (biprod.inl : G.obj 0 ⟶ G.obj 0 ⊞ G.obj 0) = biprod.inr := by
    rw [← cancel_mono (G.biprodComparison' 0 0), inl_biprodComparison', inr_biprodComparison',
      (isZero_zero C).eq_of_src (biprod.inl : (0 : C) ⟶ 0 ⊞ 0) biprod.inr]
  rw [IsZero.iff_id_eq_zero, ← biprod.inl_fst (X := G.obj 0) (Y := G.obj 0), h, biprod.inr_fst]

variable [HasZeroObject D]

/-- Stacks 0DLP (3) ⇒ (1): a functor between preadditive categories with zero objects and binary
biproducts is additive if the comparison maps `G.obj (X ⊞ Y) ⟶ G.obj X ⊞ G.obj Y` are
isomorphisms. That `G` preserves zero morphisms is deduced from the case `X = Y = 0`. -/
@[stacks 0DLP "(3) => (1)"]
lemma additive_of_isIso_biprodComparison
    (h : ∀ X Y : C, IsIso (G.biprodComparison X Y)) : G.Additive :=
  have : G.PreservesZeroMorphisms := preservesZeroMorphisms_of_map_zero_object
    (G.isZero_obj_zero_of_isIso_biprodComparison).isoZero
  _root_.Functor.additive_of_mono_biprodComparison G fun _ _ ↦ inferInstance

/-- Stacks 0DLP (2) ⇒ (1): a functor between preadditive categories with zero objects and binary
biproducts is additive if the comparison maps `G.obj X ⊞ G.obj Y ⟶ G.obj (X ⊞ Y)` are
isomorphisms. That `G` preserves zero morphisms is deduced from the case `X = Y = 0`. -/
@[stacks 0DLP "(2) => (1)"]
lemma additive_of_isIso_biprodComparison'
    (h : ∀ X Y : C, IsIso (G.biprodComparison' X Y)) : G.Additive :=
  have : G.PreservesZeroMorphisms := preservesZeroMorphisms_of_map_zero_object
    (G.isZero_obj_zero_of_isIso_biprodComparison').isoZero
  _root_.Functor.additive_of_epi_biprodComparison' G fun _ _ ↦ inferInstance

/-- Stacks 0DLP: for a functor `G` between preadditive categories with zero objects and binary
biproducts (e.g. additive categories), the following are equivalent:
1. `G` is additive;
2. the comparison maps `G.obj X ⊞ G.obj Y ⟶ G.obj (X ⊞ Y)` are isomorphisms;
3. the comparison maps `G.obj (X ⊞ Y) ⟶ G.obj X ⊞ G.obj Y` are isomorphisms. -/
@[stacks 0DLP]
theorem tfae_additive :
    List.TFAE [G.Additive, ∀ X Y : C, IsIso (G.biprodComparison' X Y),
      ∀ X Y : C, IsIso (G.biprodComparison X Y)] := by
  tfae_have 1 → 2 := fun _ X Y ↦ ⟨_, G.biprodComparison'_comp_biprodComparison X Y,
    G.biprodComparison_comp_biprodComparison' X Y⟩
  tfae_have 1 → 3 := fun _ X Y ↦ ⟨_, G.biprodComparison_comp_biprodComparison' X Y,
    G.biprodComparison'_comp_biprodComparison X Y⟩
  tfae_have 2 → 1 := G.additive_of_isIso_biprodComparison'
  tfae_have 3 → 1 := G.additive_of_isIso_biprodComparison
  tfae_finish

end CategoryTheory.Functor
