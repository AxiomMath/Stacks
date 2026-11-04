module

public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import StacksFrontier.Algebra.Homology.SpectralSequence.NatRestrict

/-!
# First quadrant cohomological spectral sequences indexed by `ℕ × ℕ`

Mathlib has two flavours of cohomological spectral sequence presented from the second page:
`E₂CohomologicalSpectralSequence 𝒜`, whose pages are homological complexes indexed by `ℤ × ℤ`
with differentials of bidegree `(r, 1 - r)`, and `E₂CohomologicalSpectralSequenceNat 𝒜`, whose
pages are indexed by `ℕ × ℕ`. Every construction of a spectral sequence from a filtered complex
or from a double complex produces the first flavour — for instance
`Stacks.Cohomology.CechSpectral.totalE₂SpectralSequence₂Functor` — while the statements about
first quadrant spectral sequences, their edge maps and their abutment (for instance
`Stacks.Cohomology.Leray.FirstQuadrantAbutment`) are phrased in the second.

This file bridges the two, *functorially*: a spectral sequence indexed by `ℤ × ℤ` whose pages
vanish outside the first quadrant yields one indexed by `ℕ × ℕ`, and the construction is a
functor on the full subcategory of such spectral sequences.

The mathematical content is the comparison of homology. Each page of the `ℕ × ℕ`-indexed
spectral sequence is the restriction of the corresponding `ℤ × ℤ`-indexed page along the
inclusion `ℕ × ℕ → ℤ × ℤ` of complex shapes, so the objects and the differentials are literally
the same. What is *not* automatic is that the homology agrees: at a bidegree `(p, q)` of the
first quadrant the predecessor `(p - r, q + r - 1)` or the successor `(p + r, q + 1 - r)` of
`(p, q)` for the `r`-th differential may fall outside the first quadrant, in which case the
restricted complex has no differential there while the original one does. The first quadrant
vanishing is exactly what makes those extra differentials zero. The comparison is set up so that
it is a *single* morphism of short complexes, natural in the complex, whose components are the
canonical isomorphisms of the terms where the indices correspond and zero where they do not; it
is then an isomorphism on homology by the epi/iso/mono criterion
`ShortComplex.isIso_homologyMap_of_isIso_cyclesMap_of_epi`.

## Main definitions

* `ComplexShape.embeddingSpectralSequenceNat`: the embedding of complex shapes
  `ComplexShape.spectralSequenceNat u → ComplexShape.up' u`, i.e. the inclusion of the first
  quadrant `ℕ × ℕ → ℤ × ℤ`.
* `HomologicalComplex.restrictionNatHom`: the comparison, at a bidegree of the first quadrant, of
  the short complex computing the homology of the first quadrant restriction of a complex with
  the short complex computing the homology of the complex itself.
* `HomologicalComplex.restrictionNatHomologyIso`: the resulting identification of the homology of
  the restriction with the homology of the complex.
* `CategoryTheory.SpectralSequence.firstQuadrantNat`: the `ℕ × ℕ`-indexed cohomological spectral
  sequence attached to a first quadrant `ℤ × ℤ`-indexed one.
* `CategoryTheory.SpectralSequence.firstQuadrantNatFunctor`: the same construction as a functor
  `ObjectProperty.FullSubcategory IsFirstQuadrant ⥤ E₂CohomologicalSpectralSequenceNat 𝒜`, and
  `firstQuadrantNatFunctorComp`, its composition with a functor taking first quadrant values.

## Main results

* `HomologicalComplex.restrictionNatHomologyIso_hom_naturality`: the identification of the
  homology of the first quadrant restriction with the homology of the complex is natural in the
  complex. This is what makes the repackaging functorial.

## Implementation notes

* The hypothesis on the shape vector `u` is `0 < u.1` and `u.2 ≤ 0`, which the vector `(r, 1 - r)`
  of the `r`-th page of a cohomological spectral sequence satisfies for `1 ≤ r`, hence in
  particular for `2 ≤ r`. These two inequalities are what make "the predecessor of `(p, q)` falls
  outside the first quadrant" equivalent to `p < u.1` (a negative first coordinate) and "the
  successor falls outside" equivalent to `p.2 + u.2 < 0` (a negative second coordinate); without
  them a missing predecessor could come from either coordinate and the comparison would need a
  stronger vanishing hypothesis.
* The first quadrant hypothesis is `CategoryTheory.SpectralSequence.IsFirstQuadrant` from
  `StacksFrontier.Algebra.Homology.SpectralSequence.NatRestrict`, which asks that the terms of
  *every* page vanish outside the first quadrant. Only the vanishing of the second page has to be
  checked in practice: `CategoryTheory.SpectralSequence.isFirstQuadrant_of_isZero_page` propagates
  it to all later pages, each page being the homology of the previous one and hence a subquotient
  of it.
* The functor is defined on the full subcategory cut out by `IsFirstQuadrant` rather than on all
  of `E₂CohomologicalSpectralSequence 𝒜`: the first quadrant vanishing is genuinely needed, since
  without it the restriction of the pages is not a spectral sequence at all. The morphisms of the
  full subcategory are all the morphisms of spectral sequences, so nothing is lost.
* The comparison of short complexes `restrictionNatHom` takes its middle component to be
  `(K.restrictionXIso e rfl).hom` rather than the identity. That morphism *is* the identity, but
  writing it this way keeps every statement in the spelling `(K.restriction e).X pq` of the
  restricted complex, which `rw` and `simp` require: the identity at `K.X (e.f pq)` is accepted by
  defeq and then blocks every subsequent rewrite.
* Nothing in this file carries a `@[stacks]` attribute. The content is a comparison of two of
  Mathlib's presentations of a spectral sequence, not a statement of the Stacks project; it is the
  item (c) that the implementation notes of `StacksDraft.Ch20.Sec13.Tag01ES` record as missing for
  [Stacks, Tag 01ES], and it is also what [Stacks, Tag 01F2] and [Stacks, Tag 09VX] need in order
  to feed a spectral sequence of a double complex into a first quadrant abutment.

## References

* [Stacks Project, Tag 0130](https://stacks.math.columbia.edu/tag/0130)
* [Stacks Project, Tag 0132](https://stacks.math.columbia.edu/tag/0132)
* [Stacks Project, Tag 01ES](https://stacks.math.columbia.edu/tag/01ES)
-/

@[expose] public section

open CategoryTheory Category Limits ComplexShape HomologicalComplex

namespace ComplexShape

/-- The predecessor of `x` for the shape `up' u` is `x - u`. -/
lemma up'_prev {α : Type*} [AddGroup α] (u x : α) : (up' u).prev x = x - u :=
  (up' u).prev_eq' (by simp [up'])

/-- The successor of `x` for the shape `up' u` is `x + u`. -/
lemma up'_next {α : Type*} [AddGroup α] (u x : α) : (up' u).next x = x + u :=
  (up' u).next_eq' rfl

/-- The embedding of complex shapes `ℕ × ℕ → ℤ × ℤ` which identifies the `r`-th page of a first
quadrant cohomological spectral sequence with the part of the `r`-th page of a cohomological
spectral sequence indexed by `ℤ × ℤ` that lies in the first quadrant. -/
def embeddingSpectralSequenceNat (u : ℤ × ℤ) :
    Embedding (spectralSequenceNat u) (up' u) where
  f pq := ((pq.1 : ℤ), (pq.2 : ℤ))
  injective_f a b h := by
    simp only [Prod.mk.injEq, Nat.cast_inj] at h
    exact Prod.ext h.1 h.2
  rel h := (spectralSequenceNat_rel_iff_up' _ _ _).1 h

/-- The embedding `embeddingSpectralSequenceNat u` reflects the relation of complex shapes. -/
instance (u : ℤ × ℤ) : (embeddingSpectralSequenceNat u).IsRelIff where
  rel' _ _ h := (spectralSequenceNat_rel_iff_up' u _ _).2 h

/-- The embedding `embeddingSpectralSequenceNat u` sends `pq : ℕ × ℕ` to its image in `ℤ × ℤ`. -/
@[simp]
lemma embeddingSpectralSequenceNat_f (u : ℤ × ℤ) (pq : ℕ × ℕ) :
    (embeddingSpectralSequenceNat u).f pq = ((pq.1 : ℤ), (pq.2 : ℤ)) := rfl

section

variable {u : ℤ × ℤ} (pq : ℕ × ℕ)

/-- In the first quadrant shape there is no differential into `pq` when `pq.1 < u.1`. -/
lemma spectralSequenceNat_not_rel_of_lt (hp : (pq.1 : ℤ) < u.1) (i : ℕ × ℕ) :
    ¬ (spectralSequenceNat u).Rel i pq := by
  rintro ⟨h, -⟩
  have : (0 : ℤ) ≤ (i.1 : ℤ) := Int.natCast_nonneg _
  omega

/-- In the first quadrant shape there is no differential out of `pq` when `pq.2 + u.2 < 0`. -/
lemma spectralSequenceNat_not_rel_of_add_neg (hq : (pq.2 : ℤ) + u.2 < 0) (k : ℕ × ℕ) :
    ¬ (spectralSequenceNat u).Rel pq k := by
  rintro ⟨-, h⟩
  have : (0 : ℤ) ≤ (k.2 : ℤ) := Int.natCast_nonneg _
  omega

/-- When `pq` has a predecessor in the first quadrant shape, it is the predecessor of the image
of `pq` in `ℤ × ℤ`. -/
lemma embeddingSpectralSequenceNat_prev (hu : u.2 ≤ 0) (hp : u.1 ≤ (pq.1 : ℤ)) :
    (embeddingSpectralSequenceNat u).f ((spectralSequenceNat u).prev pq) =
      (up' u).prev ((embeddingSpectralSequenceNat u).f pq) := by
  have h2 : (0 : ℤ) ≤ (pq.2 : ℤ) := Int.natCast_nonneg _
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (a : ℤ) = (pq.1 : ℤ) - u.1 :=
    ⟨((pq.1 : ℤ) - u.1).toNat, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ, (b : ℤ) = (pq.2 : ℤ) - u.2 :=
    ⟨((pq.2 : ℤ) - u.2).toNat, by omega⟩
  have hrel : (spectralSequenceNat u).Rel (a, b) pq := by
    rw [spectralSequenceNat_rel_iff]
    exact ⟨by omega, by omega⟩
  rw [(spectralSequenceNat u).prev_eq' hrel,
    (up' u).prev_eq' ((embeddingSpectralSequenceNat u).rel hrel)]

/-- When `pq` has a successor in the first quadrant shape, it is the successor of the image of
`pq` in `ℤ × ℤ`. -/
lemma embeddingSpectralSequenceNat_next (hu : 0 ≤ u.1) (hq : 0 ≤ (pq.2 : ℤ) + u.2) :
    (embeddingSpectralSequenceNat u).f ((spectralSequenceNat u).next pq) =
      (up' u).next ((embeddingSpectralSequenceNat u).f pq) := by
  have h1 : (0 : ℤ) ≤ (pq.1 : ℤ) := Int.natCast_nonneg _
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (a : ℤ) = (pq.1 : ℤ) + u.1 :=
    ⟨((pq.1 : ℤ) + u.1).toNat, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ, (b : ℤ) = (pq.2 : ℤ) + u.2 :=
    ⟨((pq.2 : ℤ) + u.2).toNat, by omega⟩
  have hrel : (spectralSequenceNat u).Rel pq (a, b) := by
    rw [spectralSequenceNat_rel_iff]
    exact ⟨by omega, by omega⟩
  rw [(spectralSequenceNat u).next_eq' hrel,
    (up' u).next_eq' ((embeddingSpectralSequenceNat u).rel hrel)]

/-- If the predecessor of `pq` does not map to the predecessor of its image, then `pq.1 < u.1`. -/
private lemma lt_fst_of_prev_ne (hu : u.2 ≤ 0)
    (h : ¬ (embeddingSpectralSequenceNat u).f ((spectralSequenceNat u).prev pq) =
      (up' u).prev ((embeddingSpectralSequenceNat u).f pq)) : (pq.1 : ℤ) < u.1 := by
  by_contra hc
  exact h (embeddingSpectralSequenceNat_prev pq hu (by omega))

/-- If the successor of `pq` does not map to the successor of its image, then `pq.2 + u.2 < 0`. -/
private lemma add_neg_of_next_ne (hu : 0 ≤ u.1)
    (h : ¬ (embeddingSpectralSequenceNat u).f ((spectralSequenceNat u).next pq) =
      (up' u).next ((embeddingSpectralSequenceNat u).f pq)) : (pq.2 : ℤ) + u.2 < 0 := by
  by_contra hc
  exact h (embeddingSpectralSequenceNat_next pq hu (by omega))

end

end ComplexShape

/-- Local abbreviation for the inclusion `ℕ × ℕ → ℤ × ℤ` of complex shapes, which occurs in
almost every statement below. -/
local notation "εNat" => ComplexShape.embeddingSpectralSequenceNat

namespace HomologicalComplex

variable {C : Type*} [Category C] [Abelian C]

/-- A morphism of complexes commutes with the comparison isomorphisms of the terms of a
restriction. -/
lemma restrictionMap_f_comp_restrictionXIso {ι ι' : Type*} {c : ComplexShape ι}
    {c' : ComplexShape ι'} {K L : HomologicalComplex C c'} (ψ : K ⟶ L) (e : c.Embedding c')
    [e.IsRelIff] {i : ι} {i' : ι'} (h : e.f i = i') :
    (restrictionMap ψ e).f i ≫ (L.restrictionXIso e h).hom =
      (K.restrictionXIso e h).hom ≫ ψ.f i' := by
  subst h
  exact (comp_id _).trans (id_comp _).symm

section

variable {u : ℤ × ℤ} (K L : HomologicalComplex C (ComplexShape.up' u))
  (hu₁ : 0 < u.1) (hu₂ : u.2 ≤ 0)
  (hK : ∀ ab : ℤ × ℤ, ab.1 < 0 ∨ ab.2 < 0 → IsZero (K.X ab))
  (hL : ∀ ab : ℤ × ℤ, ab.1 < 0 ∨ ab.2 < 0 → IsZero (L.X ab))

include hu₂ hK in
/-- If the predecessor of `pq` in the first quadrant does not map to the predecessor of the image
of `pq`, then the term of `K` at the latter is zero. -/
lemma restrictionNat_isZero_X_prev (pq : ℕ × ℕ)
    (h : ¬ (εNat u).f ((spectralSequenceNat u).prev pq) =
      (up' u).prev ((εNat u).f pq)) :
    IsZero (K.X ((up' u).prev ((εNat u).f pq))) := by
  have hp := lt_fst_of_prev_ne pq hu₂ h
  exact hK _ (Or.inl (by rw [up'_prev]; simpa using hp))

include hu₁ hK in
/-- If the successor of `pq` in the first quadrant does not map to the successor of the image of
`pq`, then the term of `K` at the latter is zero. -/
lemma restrictionNat_isZero_X_next (pq : ℕ × ℕ)
    (h : ¬ (εNat u).f ((spectralSequenceNat u).next pq) =
      (up' u).next ((εNat u).f pq)) :
    IsZero (K.X ((up' u).next ((εNat u).f pq))) := by
  have hq := add_neg_of_next_ne pq hu₁.le h
  exact hK _ (Or.inr (by rw [up'_next]; simpa using hq))

include hu₂ in
/-- If the predecessor of `pq` in the first quadrant does not map to the predecessor of the image
of `pq`, then there is no differential into `pq` in the first quadrant shape. -/
lemma restrictionNat_not_rel_prev (pq : ℕ × ℕ)
    (h : ¬ (εNat u).f ((spectralSequenceNat u).prev pq) =
      (up' u).prev ((εNat u).f pq)) :
    ¬ (spectralSequenceNat u).Rel ((spectralSequenceNat u).prev pq) pq := by
  have hp := lt_fst_of_prev_ne pq hu₂ h
  exact spectralSequenceNat_not_rel_of_lt pq hp _

include hu₁ in
/-- If the successor of `pq` in the first quadrant does not map to the successor of the image of
`pq`, then there is no differential out of `pq` in the first quadrant shape. -/
lemma restrictionNat_not_rel_next (pq : ℕ × ℕ)
    (h : ¬ (εNat u).f ((spectralSequenceNat u).next pq) =
      (up' u).next ((εNat u).f pq)) :
    ¬ (spectralSequenceNat u).Rel pq ((spectralSequenceNat u).next pq) := by
  have hq := add_neg_of_next_ne pq hu₁.le h
  exact spectralSequenceNat_not_rel_of_add_neg pq hq _

open scoped Classical in
/-- The left component of `restrictionNatHom`: the canonical isomorphism of the terms if the
predecessor of `pq` in the first quadrant maps to the predecessor of the image of `pq`, and zero
otherwise. -/
noncomputable def restrictionNatτ₁ (pq : ℕ × ℕ) :
    (K.restriction (εNat u)).X ((spectralSequenceNat u).prev pq) ⟶
      K.X ((up' u).prev ((εNat u).f pq)) :=
  if h : (εNat u).f ((spectralSequenceNat u).prev pq) = (up' u).prev ((εNat u).f pq)
    then (K.restrictionXIso _ h).hom else 0

open scoped Classical in
/-- The right component of `restrictionNatHom`: the canonical isomorphism of the terms if the
successor of `pq` in the first quadrant maps to the successor of the image of `pq`, and zero
otherwise. -/
noncomputable def restrictionNatτ₃ (pq : ℕ × ℕ) :
    (K.restriction (εNat u)).X ((spectralSequenceNat u).next pq) ⟶
      K.X ((up' u).next ((εNat u).f pq)) :=
  if h : (εNat u).f ((spectralSequenceNat u).next pq) = (up' u).next ((εNat u).f pq)
    then (K.restrictionXIso _ h).hom else 0

/-- When the predecessors correspond, `restrictionNatτ₁` is the canonical isomorphism of terms. -/
lemma restrictionNatτ₁_eq (pq : ℕ × ℕ)
    (h : (εNat u).f ((spectralSequenceNat u).prev pq) = (up' u).prev ((εNat u).f pq)) :
    restrictionNatτ₁ K pq = (K.restrictionXIso _ h).hom := by
  classical exact dite_eq_left h

/-- When the predecessors do not correspond, `restrictionNatτ₁` is zero. -/
lemma restrictionNatτ₁_eq_zero (pq : ℕ × ℕ)
    (h : ¬ (εNat u).f ((spectralSequenceNat u).prev pq) = (up' u).prev ((εNat u).f pq)) :
    restrictionNatτ₁ K pq = 0 := by
  classical exact dite_eq_right h

/-- When the successors correspond, `restrictionNatτ₃` is the canonical isomorphism of terms. -/
lemma restrictionNatτ₃_eq (pq : ℕ × ℕ)
    (h : (εNat u).f ((spectralSequenceNat u).next pq) = (up' u).next ((εNat u).f pq)) :
    restrictionNatτ₃ K pq = (K.restrictionXIso _ h).hom := by
  classical exact dite_eq_left h

/-- When the successors do not correspond, `restrictionNatτ₃` is zero. -/
lemma restrictionNatτ₃_eq_zero (pq : ℕ × ℕ)
    (h : ¬ (εNat u).f ((spectralSequenceNat u).next pq) = (up' u).next ((εNat u).f pq)) :
    restrictionNatτ₃ K pq = 0 := by
  classical exact dite_eq_right h

include hu₂ in
/-- The left square of `restrictionNatHom` commutes. -/
lemma restrictionNatτ₁_comm (pq : ℕ × ℕ) :
    restrictionNatτ₁ K pq ≫ K.d ((up' u).prev ((εNat u).f pq)) ((εNat u).f pq) =
      (K.restriction (εNat u)).d ((spectralSequenceNat u).prev pq) pq ≫
        (K.restrictionXIso (εNat u) (rfl : (εNat u).f pq = (εNat u).f pq)).hom := by
  by_cases h : (εNat u).f ((spectralSequenceNat u).prev pq) = (up' u).prev ((εNat u).f pq)
  · rw [restrictionNatτ₁_eq K pq h, K.restriction_d_eq _ h rfl]
    simp only [assoc, Iso.inv_hom_id, comp_id]
  · rw [restrictionNatτ₁_eq_zero K pq h,
      (K.restriction _).shape _ _ (restrictionNat_not_rel_prev hu₂ pq h), zero_comp, zero_comp]

include hu₁ hK in
/-- The right square of `restrictionNatHom` commutes. -/
lemma restrictionNatτ₃_comm (pq : ℕ × ℕ) :
    (K.restrictionXIso (εNat u) (rfl : (εNat u).f pq = (εNat u).f pq)).hom ≫
        K.d ((εNat u).f pq) ((up' u).next ((εNat u).f pq)) =
      (K.restriction (εNat u)).d pq ((spectralSequenceNat u).next pq) ≫
        restrictionNatτ₃ K pq := by
  by_cases h : (εNat u).f ((spectralSequenceNat u).next pq) = (up' u).next ((εNat u).f pq)
  · rw [restrictionNatτ₃_eq K pq h, K.restriction_d_eq _ rfl h]
    simp only [assoc, Iso.inv_hom_id, comp_id]
  · rw [restrictionNatτ₃_eq_zero K pq h, comp_zero,
      (restrictionNat_isZero_X_next K hu₁ hK pq h).eq_of_tgt
        (K.d ((εNat u).f pq) ((up' u).next ((εNat u).f pq))) 0, comp_zero]

include hu₁ hu₂ hK in
/-- The comparison, at a point `pq` of the first quadrant, of the short complex computing the
homology of the first-quadrant restriction of `K` at `pq` with the short complex computing the
homology of `K` at the image of `pq`. -/
noncomputable def restrictionNatHom (pq : ℕ × ℕ) :
    (K.restriction (εNat u)).sc pq ⟶ K.sc ((εNat u).f pq) where
  τ₁ := restrictionNatτ₁ K pq
  τ₂ := (K.restrictionXIso (εNat u) (rfl : (εNat u).f pq = (εNat u).f pq)).hom
  τ₃ := restrictionNatτ₃ K pq
  comm₁₂ := restrictionNatτ₁_comm K hu₂ pq
  comm₂₃ := restrictionNatτ₃_comm K hu₁ hK pq


include hu₂ hK in
/-- The left component of `restrictionNatHom` is an epimorphism: it is an isomorphism when the
predecessors correspond, and otherwise the target is a zero object. -/
lemma epi_restrictionNatHom_τ₁ (pq : ℕ × ℕ) :
    Epi (restrictionNatHom K hu₁ hu₂ hK pq).τ₁ := by
  show Epi (restrictionNatτ₁ K pq)
  by_cases h : (εNat u).f ((spectralSequenceNat u).prev pq) = (up' u).prev ((εNat u).f pq)
  · rw [restrictionNatτ₁_eq K pq h]
    infer_instance
  · rw [restrictionNatτ₁_eq_zero K pq h]
    exact ⟨fun g₁ g₂ _ => (restrictionNat_isZero_X_prev K hu₂ hK pq h).eq_of_src g₁ g₂⟩

include hu₁ hu₂ hK in
/-- `restrictionNatHom` induces an isomorphism on cycles: either the successors correspond, and
then its middle component is an isomorphism and its right component a monomorphism, or both
short complexes have a vanishing second map and the cycles are the middle terms. -/
lemma isIso_cyclesMap_restrictionNatHom (pq : ℕ × ℕ) :
    IsIso (ShortComplex.cyclesMap (restrictionNatHom K hu₁ hu₂ hK pq)) := by
  have h₂ : IsIso (restrictionNatHom K hu₁ hu₂ hK pq).τ₂ := by
    show IsIso (K.restrictionXIso (εNat u) (rfl : (εNat u).f pq = (εNat u).f pq)).hom
    infer_instance
  by_cases h : (εNat u).f ((spectralSequenceNat u).next pq) = (up' u).next ((εNat u).f pq)
  · have h₃ : Mono (restrictionNatHom K hu₁ hu₂ hK pq).τ₃ := by
      show Mono (restrictionNatτ₃ K pq)
      rw [restrictionNatτ₃_eq K pq h]
      infer_instance
    exact ShortComplex.isIso_cyclesMap_of_isIso_of_mono' _ h₂ h₃
  · have i₁ := ShortComplex.isIso_iCycles ((K.restriction (εNat u)).sc pq)
      ((K.restriction _).shape _ _ (restrictionNat_not_rel_next hu₁ pq h))
    have i₂ := ShortComplex.isIso_iCycles (K.sc ((εNat u).f pq))
      ((restrictionNat_isZero_X_next K hu₁ hK pq h).eq_of_tgt _ _)
    have : IsIso (ShortComplex.cyclesMap (restrictionNatHom K hu₁ hu₂ hK pq) ≫
        (K.sc ((εNat u).f pq)).iCycles) := by
      rw [ShortComplex.cyclesMap_i]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (K.sc ((εNat u).f pq)).iCycles

include hu₁ hu₂ hK in
/-- `restrictionNatHom` induces an isomorphism on homology. -/
lemma isIso_homologyMap_restrictionNatHom (pq : ℕ × ℕ) :
    IsIso (ShortComplex.homologyMap (restrictionNatHom K hu₁ hu₂ hK pq)) :=
  ShortComplex.isIso_homologyMap_of_isIso_cyclesMap_of_epi
    (isIso_cyclesMap_restrictionNatHom K hu₁ hu₂ hK pq)
    (epi_restrictionNatHom_τ₁ K hu₁ hu₂ hK pq)

include hu₁ hu₂ hK in
/-- For a complex `K` indexed by `ℤ × ℤ` which vanishes outside the first quadrant, the homology
of its restriction to the first quadrant at `pq : ℕ × ℕ` is the homology of `K` at the image of
`pq`. -/
noncomputable def restrictionNatHomologyIso (pq : ℕ × ℕ) :
    (K.restriction (εNat u)).homology pq ≅ K.homology ((εNat u).f pq) :=
  haveI := isIso_homologyMap_restrictionNatHom K hu₁ hu₂ hK pq
  (asIso (ShortComplex.homologyMap (restrictionNatHom K hu₁ hu₂ hK pq)) :
    ((K.restriction (εNat u)).sc pq).homology ≅ (K.sc ((εNat u).f pq)).homology)

/-- `restrictionNatτ₁` is natural in the complex. -/
lemma restrictionNatτ₁_naturality (ψ : K ⟶ L) (pq : ℕ × ℕ) :
    (restrictionMap ψ (εNat u)).f ((spectralSequenceNat u).prev pq) ≫ restrictionNatτ₁ L pq =
      restrictionNatτ₁ K pq ≫ ψ.f ((up' u).prev ((εNat u).f pq)) := by
  by_cases h : (εNat u).f ((spectralSequenceNat u).prev pq) = (up' u).prev ((εNat u).f pq)
  · rw [restrictionNatτ₁_eq K pq h, restrictionNatτ₁_eq L pq h]
    exact restrictionMap_f_comp_restrictionXIso ψ _ h
  · rw [restrictionNatτ₁_eq_zero K pq h, restrictionNatτ₁_eq_zero L pq h, comp_zero, zero_comp]

/-- `restrictionNatτ₃` is natural in the complex. -/
lemma restrictionNatτ₃_naturality (ψ : K ⟶ L) (pq : ℕ × ℕ) :
    (restrictionMap ψ (εNat u)).f ((spectralSequenceNat u).next pq) ≫ restrictionNatτ₃ L pq =
      restrictionNatτ₃ K pq ≫ ψ.f ((up' u).next ((εNat u).f pq)) := by
  by_cases h : (εNat u).f ((spectralSequenceNat u).next pq) = (up' u).next ((εNat u).f pq)
  · rw [restrictionNatτ₃_eq K pq h, restrictionNatτ₃_eq L pq h]
    exact restrictionMap_f_comp_restrictionXIso ψ _ h
  · rw [restrictionNatτ₃_eq_zero K pq h, restrictionNatτ₃_eq_zero L pq h, comp_zero, zero_comp]

include hu₁ hu₂ hK hL in
/-- `restrictionNatHom` is natural in the complex. -/
lemma restrictionNatHom_naturality (ψ : K ⟶ L) (pq : ℕ × ℕ) :
    (shortComplexFunctor C (spectralSequenceNat u) pq).map (restrictionMap ψ (εNat u)) ≫
        restrictionNatHom L hu₁ hu₂ hL pq =
      restrictionNatHom K hu₁ hu₂ hK pq ≫
        (shortComplexFunctor C (up' u) ((εNat u).f pq)).map ψ :=
  ShortComplex.hom_ext _ _ (restrictionNatτ₁_naturality K L ψ pq)
    (restrictionMap_f_comp_restrictionXIso ψ (εNat u) (rfl : (εNat u).f pq = (εNat u).f pq))
    (restrictionNatτ₃_naturality K L ψ pq)

include hu₁ hu₂ hK hL in
/-- The identification of the homology of the first-quadrant restriction with the homology of the
complex is natural in the complex. -/
@[reassoc]
lemma restrictionNatHomologyIso_hom_naturality (ψ : K ⟶ L) (pq : ℕ × ℕ) :
    homologyMap (restrictionMap ψ (εNat u)) pq ≫
        (restrictionNatHomologyIso L hu₁ hu₂ hL pq).hom =
      (restrictionNatHomologyIso K hu₁ hu₂ hK pq).hom ≫ homologyMap ψ ((εNat u).f pq) := by
  have := isIso_homologyMap_restrictionNatHom K hu₁ hu₂ hK pq
  have := isIso_homologyMap_restrictionNatHom L hu₁ hu₂ hL pq
  show ShortComplex.homologyMap _ ≫ ShortComplex.homologyMap _ =
    ShortComplex.homologyMap _ ≫ ShortComplex.homologyMap _
  rw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp,
    restrictionNatHom_naturality K L hu₁ hu₂ hK hL ψ pq]

end

end HomologicalComplex

namespace CategoryTheory.SpectralSequence

variable {C : Type*} [Category C] [Abelian C]

/-- The vector of the differentials of the `r`-th page has positive first coordinate. -/
lemma zero_lt_fst_pageVector {r : ℤ} (hr : 2 ≤ r) : (0 : ℤ) < ((r, 1 - r) : ℤ × ℤ).1 := by omega

/-- The vector of the differentials of the `r`-th page has nonpositive second coordinate. -/
lemma snd_pageVector_nonpos {r : ℤ} (hr : 2 ≤ r) : ((r, 1 - r) : ℤ × ℤ).2 ≤ 0 := by omega

/-- The first quadrant part of a first quadrant cohomological spectral sequence indexed by
`ℤ × ℤ`, as a cohomological spectral sequence indexed by `ℕ × ℕ`. Each page is the restriction of
the corresponding page along the inclusion of the first quadrant, and the identification of the
homology of a page with the next page is the one of `E` transported through
`HomologicalComplex.restrictionNatHomologyIso`. -/
noncomputable def firstQuadrantNat (E : E₂CohomologicalSpectralSequence C)
    (hE : IsFirstQuadrant E) :
    E₂CohomologicalSpectralSequenceNat C where
  page r hr := (E.page r hr).restriction (εNat (r, 1 - r))
  iso r r' pq hrr' hr :=
    restrictionNatHomologyIso (E.page r hr) (zero_lt_fst_pageVector hr)
        (snd_pageVector_nonpos hr) (fun _ h => hE r hr _ h) pq ≪≫
      E.iso r r' ((εNat ((r : ℤ), 1 - r)).f pq) hrr' hr

/-- The square expressing that the restriction to the first quadrant of a morphism of first
quadrant cohomological spectral sequences is compatible with the identifications of the homology
of a page with the next page. -/
lemma firstQuadrantNatMap_comm {E E' : E₂CohomologicalSpectralSequence C} (hE : IsFirstQuadrant E)
    (hE' : IsFirstQuadrant E') (φ : E ⟶ E') (r r' : ℤ) (pq : ℕ × ℕ) (hrr' : r + 1 = r')
    (hr : 2 ≤ r) (hr' : 2 ≤ r') :
    HomologicalComplex.homologyMap
          (restrictionMap (φ.hom r hr) (εNat ((r : ℤ), 1 - r))) pq ≫
        (restrictionNatHomologyIso (E'.page r hr) (zero_lt_fst_pageVector hr)
            (snd_pageVector_nonpos hr) (fun _ h => hE' r hr _ h) pq ≪≫
          E'.iso r r' ((εNat ((r : ℤ), 1 - r)).f pq) hrr' hr).hom =
      (restrictionNatHomologyIso (E.page r hr) (zero_lt_fst_pageVector hr)
            (snd_pageVector_nonpos hr) (fun _ h => hE r hr _ h) pq ≪≫
          E.iso r r' ((εNat ((r : ℤ), 1 - r)).f pq) hrr' hr).hom ≫
        (φ.hom r' hr').f ((εNat ((r : ℤ), 1 - r)).f pq) := by
  simp only [Iso.trans_hom, assoc]
  rw [restrictionNatHomologyIso_hom_naturality_assoc (E.page r hr) (E'.page r hr)
    (zero_lt_fst_pageVector hr) (snd_pageVector_nonpos hr)
    (fun _ h => hE r hr _ h) (fun _ h => hE' r hr _ h)
    (φ.hom r hr) pq, φ.comm r r' ((εNat ((r : ℤ), 1 - r)).f pq) hrr' hr]

/-- A morphism of first quadrant cohomological spectral sequences, restricted to the first
quadrant. -/
noncomputable def firstQuadrantNatMap {E E' : E₂CohomologicalSpectralSequence C}
    (hE : IsFirstQuadrant E) (hE' : IsFirstQuadrant E') (φ : E ⟶ E') :
    firstQuadrantNat E hE ⟶ firstQuadrantNat E' hE' where
  hom r hr := restrictionMap (φ.hom r hr) (εNat ((r : ℤ), 1 - r))
  comm r r' pq hrr' hr := firstQuadrantNatMap_comm hE hE' φ r r' pq hrr' hr (by omega)


/-- `firstQuadrantNatMap` sends the identity to the identity. -/
@[simp]
lemma firstQuadrantNatMap_id (E : E₂CohomologicalSpectralSequence C) (hE : IsFirstQuadrant E) :
    firstQuadrantNatMap hE hE (𝟙 E) = 𝟙 (firstQuadrantNat E hE) :=
  SpectralSequence.hom_ext (fun _ _ => rfl)

/-- `firstQuadrantNatMap` is compatible with composition. -/
@[simp]
lemma firstQuadrantNatMap_comp {E E' E'' : E₂CohomologicalSpectralSequence C}
    (hE : IsFirstQuadrant E) (hE' : IsFirstQuadrant E') (hE'' : IsFirstQuadrant E'')
    (φ : E ⟶ E') (ψ : E' ⟶ E'') :
    firstQuadrantNatMap hE hE'' (φ ≫ ψ) =
      firstQuadrantNatMap hE hE' φ ≫ firstQuadrantNatMap hE' hE'' ψ :=
  SpectralSequence.hom_ext (fun _ _ => rfl)

/-- **The functorial first quadrant repackaging of a cohomological spectral sequence.** The
first quadrant part of a first quadrant cohomological spectral sequence indexed by `ℤ × ℤ`,
presented from its second page, is a cohomological spectral sequence indexed by `ℕ × ℕ`,
functorially in the spectral sequence. -/
noncomputable def firstQuadrantNatFunctor :
    ObjectProperty.FullSubcategory
        (IsFirstQuadrant (C := C) (r₀ := 2) (u := fun r => ((r, 1 - r) : ℤ × ℤ))) ⥤
      E₂CohomologicalSpectralSequenceNat C where
  obj E := firstQuadrantNat E.obj E.property
  map φ := firstQuadrantNatMap _ _ φ.hom
  map_id E := firstQuadrantNatMap_id E.obj E.property
  map_comp φ ψ := firstQuadrantNatMap_comp _ _ _ φ.hom ψ.hom

/-- A functor with values in first quadrant cohomological spectral sequences indexed by `ℤ × ℤ`,
presented from their second page, gives a functor with values in cohomological spectral sequences
indexed by `ℕ × ℕ`. -/
noncomputable def firstQuadrantNatFunctorComp {D : Type*} [Category D]
    (G : D ⥤ E₂CohomologicalSpectralSequence C) (hG : ∀ X, IsFirstQuadrant (G.obj X)) :
    D ⥤ E₂CohomologicalSpectralSequenceNat C :=
  ObjectProperty.lift _ G hG ⋙ firstQuadrantNatFunctor

/-- The value of `firstQuadrantNatFunctorComp G hG` at `X` is
`firstQuadrantNat (G.obj X) (hG X)`. -/
@[simp]
lemma firstQuadrantNatFunctorComp_obj {D : Type*} [Category D]
    (G : D ⥤ E₂CohomologicalSpectralSequence C) (hG : ∀ X, IsFirstQuadrant (G.obj X)) (X : D) :
    (firstQuadrantNatFunctorComp G hG).obj X = firstQuadrantNat (G.obj X) (hG X) := rfl

/-- The `r`-th page of `firstQuadrantNat E hE` is the restriction of the `r`-th page of `E` to the
first quadrant. -/
@[simp]
lemma firstQuadrantNat_page (E : E₂CohomologicalSpectralSequence C) (hE : IsFirstQuadrant E) (r : ℤ)
    (hr : 2 ≤ r) :
    (firstQuadrantNat E hE).page r hr = (E.page r hr).restriction (εNat ((r : ℤ), 1 - r)) := rfl

/-- The term of the `r`-th page of `firstQuadrantNat E hE` at `pq` is the term of the `r`-th page
of `E` at the image of `pq` in `ℤ × ℤ`. -/
@[simp]
lemma firstQuadrantNat_page_X (E : E₂CohomologicalSpectralSequence C)
    (hE : IsFirstQuadrant E) (r : ℤ) (hr : 2 ≤ r) (pq : ℕ × ℕ) :
    ((firstQuadrantNat E hE).page r hr).X pq = (E.page r hr).X ((pq.1 : ℤ), (pq.2 : ℤ)) := rfl

end CategoryTheory.SpectralSequence

end
