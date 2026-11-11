module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import StacksFrontier.Algebra.Homology.HomotopyCategory.DegreewiseSplit

/-!
# Termwise split injections and surjections when idempotents split

A termwise split injection (resp. surjection) of complexes in the sense of [Stacks, Tag 014G],
`HomologicalComplex.Hom.IsDegreewiseSummandInclusion` (resp.
`HomologicalComplex.Hom.IsDegreewiseSummandProjection`), is always a degreewise split
monomorphism (resp. epimorphism). This file proves the converse when the category is idempotent
complete: a split monomorphism `f : X ⟶ Y` is then the inclusion of a direct summand, the
complement being the image of the idempotent `𝟙 Y - retraction f ≫ f`.

## Main results

* `HomologicalComplex.Hom.isDegreewiseSummandInclusion_iff_isDegreewiseSplitMono`
* `HomologicalComplex.Hom.isDegreewiseSummandProjection_iff_isDegreewiseSplitEpi`
-/

@[expose] public section

namespace CategoryTheory.Limits

variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]

/-- In an idempotent complete preadditive category with binary biproducts, a split
monomorphism `f : X ⟶ Y` is the inclusion of a direct summand: the idempotent
`𝟙 Y - retraction f ≫ f` splits through an object `Z`, and `Y ≅ X ⊞ Z` with `f` the first
inclusion. -/
public lemma exists_iso_biprod_inl_of_isSplitMono [IsIdempotentComplete C] {X Y : C}
    (f : X ⟶ Y) [IsSplitMono f] :
    ∃ (Z : C) (e : Y ≅ X ⊞ Z), f ≫ e.hom = biprod.inl := by
  obtain ⟨Z, i, q, hiq, hqi⟩ := IsIdempotentComplete.idempotents_split Y
    (𝟙 Y - retraction f ≫ f) (by simp [Preadditive.sub_comp, Preadditive.comp_sub])
  have hfq : f ≫ q = 0 := by
    have : f ≫ q = f ≫ (q ≫ i) ≫ q := by simp [hiq]
    rw [this, hqi]
    simp [Preadditive.sub_comp, Preadditive.comp_sub]
  have hir : i ≫ retraction f = 0 := by
    have : i ≫ retraction f = i ≫ (q ≫ i) ≫ retraction f := by
      rw [← Category.assoc, ← Category.assoc, hiq, Category.id_comp]
    rw [this, hqi]
    simp [Preadditive.sub_comp]
  let b : BinaryBicone X Z :=
    { pt := Y, fst := retraction f, snd := q, inl := f, inr := i
      inl_fst := IsSplitMono.id f, inl_snd := hfq, inr_fst := hir, inr_snd := hiq }
  have hb : b.IsBilimit := isBinaryBilimitOfTotal b (by simp [b, hqi])
  refine ⟨Z, biprod.uniqueUpToIso X Z hb, ?_⟩
  apply biprod.hom_ext <;> simp [b, hfq]

/-- In an idempotent complete preadditive category with binary biproducts, a split
epimorphism `f : Y ⟶ X` is the projection onto a direct summand: the idempotent
`𝟙 Y - f ≫ section_ f` splits through an object `Z`, and `Y ≅ X ⊞ Z` with `f` the first
projection. -/
public lemma exists_iso_biprod_fst_of_isSplitEpi [IsIdempotentComplete C] {X Y : C}
    (f : Y ⟶ X) [IsSplitEpi f] :
    ∃ (Z : C) (e : Y ≅ X ⊞ Z), e.hom ≫ biprod.fst = f := by
  obtain ⟨Z, i, q, hiq, hqi⟩ := IsIdempotentComplete.idempotents_split Y
    (𝟙 Y - f ≫ section_ f) (by simp [Preadditive.sub_comp, Preadditive.comp_sub])
  have hsq : section_ f ≫ q = 0 := by
    have : section_ f ≫ q = section_ f ≫ (q ≫ i) ≫ q := by simp [hiq]
    rw [this, hqi]
    simp [Preadditive.sub_comp, Preadditive.comp_sub]
  have hif : i ≫ f = 0 := by
    have : i ≫ f = i ≫ (q ≫ i) ≫ f := by
      rw [← Category.assoc, ← Category.assoc, hiq, Category.id_comp]
    rw [this, hqi]
    simp [Preadditive.sub_comp]
  let b : BinaryBicone X Z :=
    { pt := Y, fst := f, snd := q, inl := section_ f, inr := i
      inl_fst := IsSplitEpi.id f, inl_snd := hsq, inr_fst := hif, inr_snd := hiq }
  have hb : b.IsBilimit := isBinaryBilimitOfTotal b (by simp [b, hqi])
  exact ⟨Z, biprod.uniqueUpToIso X Z hb, by simp [b]⟩

end CategoryTheory.Limits

namespace HomologicalComplex.Hom

open CategoryTheory Limits

variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C] {ι : Type*}
  {c : ComplexShape ι} {K L : HomologicalComplex C c}

/-- In an idempotent complete category, a degreewise split monomorphism is a termwise split
injection. -/
public lemma IsDegreewiseSplitMono.isDegreewiseSummandInclusion [IsIdempotentComplete C]
    {α : K ⟶ L} (hα : α.IsDegreewiseSplitMono) : α.IsDegreewiseSummandInclusion :=
  (isDegreewiseSummandInclusion_iff α).2 fun n =>
    haveI := hα n
    exists_iso_biprod_inl_of_isSplitMono (α.f n)

/-- In an idempotent complete category, a degreewise split epimorphism is a termwise split
surjection. -/
public lemma IsDegreewiseSplitEpi.isDegreewiseSummandProjection [IsIdempotentComplete C]
    {β : K ⟶ L} (hβ : β.IsDegreewiseSplitEpi) : β.IsDegreewiseSummandProjection :=
  (isDegreewiseSummandProjection_iff β).2 fun n =>
    haveI := hβ n
    exists_iso_biprod_fst_of_isSplitEpi (β.f n)

/-- In an idempotent complete category, termwise split injections are exactly the degreewise
split monomorphisms. -/
public lemma isDegreewiseSummandInclusion_iff_isDegreewiseSplitMono [IsIdempotentComplete C]
    (α : K ⟶ L) : α.IsDegreewiseSummandInclusion ↔ α.IsDegreewiseSplitMono :=
  ⟨IsDegreewiseSummandInclusion.isDegreewiseSplitMono,
    IsDegreewiseSplitMono.isDegreewiseSummandInclusion⟩

/-- In an idempotent complete category, termwise split surjections are exactly the degreewise
split epimorphisms. -/
public lemma isDegreewiseSummandProjection_iff_isDegreewiseSplitEpi [IsIdempotentComplete C]
    (β : K ⟶ L) : β.IsDegreewiseSummandProjection ↔ β.IsDegreewiseSplitEpi :=
  ⟨IsDegreewiseSummandProjection.isDegreewiseSplitEpi,
    IsDegreewiseSplitEpi.isDegreewiseSummandProjection⟩

end HomologicalComplex.Hom
