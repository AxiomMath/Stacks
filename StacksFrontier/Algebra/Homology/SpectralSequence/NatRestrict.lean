module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restricting a spectral sequence from `ℤ × ℤ` to the first quadrant

Mathlib carries two families of cohomological spectral sequences: those indexed by `ℤ × ℤ`, with
pages shaped by `ComplexShape.up' (r, 1 - r)`, and the *first quadrant* ones indexed by `ℕ × ℕ`,
with pages shaped by `ComplexShape.spectralSequenceNat (r, 1 - r)`. A spectral sequence of the
first kind all of whose pages vanish outside the first quadrant ought to be the same thing as one
of the second kind; this file constructs that restriction, together with its functoriality.

The two complex shapes do agree under the index embedding `ComplexShape.natEmb : ℕ × ℕ → ℤ × ℤ`
(`ComplexShape.spectralSequenceNat_rel_iff_up'`), so the objects, the differentials, the `shape`
condition and `d_comp_d` transfer with no hypothesis at all: this is
`HomologicalComplex.natRestrict`. The content is entirely in the `iso` field of a spectral
sequence, which compares the *homology* of the `r`-th page with the `(r+1)`-st page. Homology of a
homological complex is computed from the short complex `X (prev i) ⟶ X i ⟶ X (next i)`, and where
`ℕ × ℕ` has no predecessor `ComplexShape.prev` returns the index itself with a zero differential.
So at such an index the two short complexes are
```
K.X pq --0--> K.X pq ⟶ K.X (next pq)        versus        0 ⟶ K.X pq ⟶ K.X (next pq),
```
which are *not* isomorphic, even though their homology agrees. The same happens on the other side
where `ℕ × ℕ` has no successor.

The comparison is therefore made through a third short complex `HomologicalComplex.natMid`, which
takes its `X₁` from `ℤ × ℤ` and its `X₃` from `ℕ × ℕ`. Both short complexes map to it by a
morphism which is an isomorphism on `X₂`, an epimorphism on `X₁` and a monomorphism on `X₃` — the
degenerate cases being covered because a morphism *into* a zero object is an epimorphism and a
morphism *out of* one is a monomorphism — and such a morphism induces an isomorphism on homology
by `ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono'`. Choosing `natMid` with its `X₁`
on the `ℤ × ℤ` side and its `X₃` on the `ℕ × ℕ` side is what makes *both* comparisons point the
same way; the naive comparison `K.sc pq ⟶ (natRestrict K).sc pq` has the wrong variance on one
of the two ends.

## Main definitions

* `ComplexShape.natEmb`: the index embedding `ℕ × ℕ → ℤ × ℤ`.
* `HomologicalComplex.natRestrict`, `HomologicalComplex.natRestrictFunctor`: the restriction of a
  homological complex shaped by `ComplexShape.up' u` to one shaped by
  `ComplexShape.spectralSequenceNat u`, and its functoriality.
* `HomologicalComplex.natRestrictHomologyIso`: the comparison of the homology of the restriction
  with the ambient homology, for a complex vanishing outside the first quadrant.
* `CategoryTheory.SpectralSequence.IsFirstQuadrant`: the vanishing hypothesis on a spectral
  sequence indexed by `ℤ × ℤ`.
* `CategoryTheory.SpectralSequence.natRestrict`: the restriction of such a spectral sequence to
  `ℕ × ℕ`.
* `CategoryTheory.SpectralSequence.natRestrictMap`, and
  `CategoryTheory.SpectralSequence.natRestrictComp` which restricts a *functor* into spectral
  sequences indexed by `ℤ × ℤ` to one into spectral sequences indexed by `ℕ × ℕ`. The latter is
  the form in which a functorial first-quadrant spectral sequence is obtained from a functorial
  one on `ℤ × ℤ`.
* `CategoryTheory.SpectralSequence.natRestrictE₂`: the specialization to `E₂`-cohomological
  spectral sequences, turning a `E₂CohomologicalSpectralSequence` which vanishes outside the
  first quadrant into an `E₂CohomologicalSpectralSequenceNat`.

## Main results

* `HomologicalComplex.natRestrictHomologyIso_hom_naturality`: the comparison isomorphism on
  homology is natural in the complex. This is what makes `natRestrict` functorial on spectral
  sequences, since the `comm` axiom of a morphism of spectral sequences is a naturality square
  for the `iso` fields.

## Implementation notes

The vanishing hypothesis is stated for *every* page, not only for the first one: the restriction
has to produce a homological complex in every degree `r`, and the vanishing of a later page does
not follow from that of an earlier one without knowing that the pages are the homology of the
previous ones in the sense of a subquotient, which the bare `SpectralSequence` structure does not
record.

Everything is stated for an arbitrary family of differential vectors `u : ℤ → ℤ × ℤ`, of which
the cohomological family `fun r ↦ (r, 1 - r)` is the case of interest. No non-degeneracy
hypothesis on `u` is needed: at an index with no predecessor in `ℕ × ℕ`, the relation
`spectralSequenceNat u |>.Rel pq pq` in particular fails, so the differential
`K.d (natEmb pq) (natEmb pq)` produced by `ComplexShape.prev` returning `pq` is zero by `shape`.

No `set_option` is used.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe v u

namespace ComplexShape

/-- The index embedding `ℕ × ℕ → ℤ × ℤ` along which a first-quadrant spectral sequence sits
inside one indexed by `ℤ × ℤ`. -/
def natEmb (pq : ℕ × ℕ) : ℤ × ℤ := ((pq.1 : ℤ), (pq.2 : ℤ))

/-- The first coordinate of `ComplexShape.natEmb pq` is the first coordinate of `pq`. -/
@[simp]
lemma natEmb_fst (pq : ℕ × ℕ) : (natEmb pq).1 = (pq.1 : ℤ) := rfl

/-- The second coordinate of `ComplexShape.natEmb pq` is the second coordinate of `pq`. -/
@[simp]
lemma natEmb_snd (pq : ℕ × ℕ) : (natEmb pq).2 = (pq.2 : ℤ) := rfl

/-- The predecessor of `x` for the shape `ComplexShape.up' u` is `x - u`. -/
lemma prev_up' (u x : ℤ × ℤ) : (up' u).prev x = x - u :=
  (up' u).prev_eq' (show x - u + u = x by simp)

/-- The successor of `x` for the shape `ComplexShape.up' u` is `x + u`. -/
lemma next_up' (u x : ℤ × ℤ) : (up' u).next x = x + u :=
  (up' u).next_eq' (show x + u = x + u from rfl)

/-- **The two complex shapes agree under the index embedding.** The shape
`ComplexShape.spectralSequenceNat u` on `ℕ × ℕ` is the restriction of `ComplexShape.up' u` on
`ℤ × ℤ` along `ComplexShape.natEmb`. -/
lemma spectralSequenceNat_rel_iff_up' (u : ℤ × ℤ) (a b : ℕ × ℕ) :
    (spectralSequenceNat u).Rel a b ↔ (up' u).Rel (natEmb a) (natEmb b) := by
  rw [spectralSequenceNat_rel_iff]
  constructor
  · intro h
    exact Prod.ext h.1 h.2
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-- An integer pair outside the negative region is the image of a natural pair. -/
private lemma exists_natEmb_eq (x : ℤ × ℤ) (hx : ¬ (x.1 < 0 ∨ x.2 < 0)) :
    ∃ a : ℕ × ℕ, natEmb a = x :=
  ⟨(x.1.toNat, x.2.toNat), Prod.ext (Int.toNat_of_nonneg (not_lt.1 (not_or.1 hx).1))
    (Int.toNat_of_nonneg (not_lt.1 (not_or.1 hx).2))⟩

/-- An index of `ℕ × ℕ` with no predecessor there has its predecessor in `ℤ × ℤ` outside the
first quadrant. -/
lemma prev_up'_natEmb_lt_zero (u : ℤ × ℤ) (pq : ℕ × ℕ)
    (h : ∀ a : ℕ × ℕ, ¬ (spectralSequenceNat u).Rel a pq) :
    ((up' u).prev (natEmb pq)).1 < 0 ∨ ((up' u).prev (natEmb pq)).2 < 0 := by
  by_contra hc
  obtain ⟨a, ha⟩ := exists_natEmb_eq _ hc
  refine h a ((spectralSequenceNat_rel_iff_up' u a pq).2 ?_)
  change natEmb a + u = natEmb pq
  rw [ha, prev_up', sub_add_cancel]

/-- An index of `ℕ × ℕ` with no successor there has its successor in `ℤ × ℤ` outside the
first quadrant. -/
lemma next_up'_natEmb_lt_zero (u : ℤ × ℤ) (pq : ℕ × ℕ)
    (h : ∀ b : ℕ × ℕ, ¬ (spectralSequenceNat u).Rel pq b) :
    ((up' u).next (natEmb pq)).1 < 0 ∨ ((up' u).next (natEmb pq)).2 < 0 := by
  by_contra hc
  obtain ⟨b, hb⟩ := exists_natEmb_eq _ hc
  refine h b ((spectralSequenceNat_rel_iff_up' u pq b).2 ?_)
  change natEmb pq + u = natEmb b
  rw [hb, next_up']

/-- Where `pq : ℕ × ℕ` does have a predecessor there, the two notions of predecessor agree
under the index embedding. -/
lemma natEmb_prev (u : ℤ × ℤ) (pq : ℕ × ℕ)
    (h : ∃ a : ℕ × ℕ, (spectralSequenceNat u).Rel a pq) :
    natEmb ((spectralSequenceNat u).prev pq) = (up' u).prev (natEmb pq) := by
  obtain ⟨a, ha⟩ := h
  rw [(spectralSequenceNat u).prev_eq' ha,
    (up' u).prev_eq' ((spectralSequenceNat_rel_iff_up' u a pq).1 ha)]

/-- Where `pq : ℕ × ℕ` does have a successor there, the two notions of successor agree
under the index embedding. -/
lemma natEmb_next (u : ℤ × ℤ) (pq : ℕ × ℕ)
    (h : ∃ b : ℕ × ℕ, (spectralSequenceNat u).Rel pq b) :
    natEmb ((spectralSequenceNat u).next pq) = (up' u).next (natEmb pq) := by
  obtain ⟨b, hb⟩ := h
  rw [(spectralSequenceNat u).next_eq' hb,
    (up' u).next_eq' ((spectralSequenceNat_rel_iff_up' u pq b).1 hb)]

end ComplexShape

namespace HomologicalComplex

open ComplexShape

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The naturality of `eqToHom` along an equality of indices: a morphism of homological complexes
commutes with the identifications of the objects at equal indices. -/
lemma eqToHom_X_naturality {ι : Type*} {c : ComplexShape ι} {K L : HomologicalComplex C c}
    (f : K ⟶ L) {i j : ι} (h : i = j) :
    f.f i ≫ eqToHom (congrArg L.X h) = eqToHom (congrArg K.X h) ≫ f.f j := by
  subst h
  simp

section Restrict

variable (u : ℤ × ℤ)

/-- **The restriction of a homological complex from `ℤ × ℤ` to the first quadrant.** The objects
and the differentials are those of the ambient complex at the embedded indices; the `shape`
condition and `d_comp_d` transfer because the two complex shapes agree under the embedding. -/
@[simps]
def natRestrict (K : HomologicalComplex C (up' u)) :
    HomologicalComplex C (spectralSequenceNat u) where
  X pq := K.X (natEmb pq)
  d a b := K.d (natEmb a) (natEmb b)
  shape a b h := K.shape _ _ fun h' => h ((spectralSequenceNat_rel_iff_up' u a b).2 h')
  d_comp_d' _ _ _ _ _ := K.d_comp_d _ _ _

/-- **The restriction to the first quadrant of a morphism of homological complexes.** It is
given by the components of the morphism at the embedded indices. -/
@[simps]
def natRestrictHom {K L : HomologicalComplex C (up' u)} (f : K ⟶ L) :
    natRestrict u K ⟶ natRestrict u L where
  f pq := f.f (natEmb pq)
  comm' _ _ _ := f.comm _ _

/-- **The restriction to the first quadrant is a functor.** -/
@[simps]
def natRestrictFunctor :
    HomologicalComplex C (up' u) ⥤ HomologicalComplex C (spectralSequenceNat u) where
  obj K := natRestrict u K
  map f := natRestrictHom u f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The restriction to the first quadrant of the identity is the identity. -/
@[simp]
lemma natRestrictHom_id (K : HomologicalComplex C (up' u)) :
    natRestrictHom u (𝟙 K) = 𝟙 _ :=
  rfl

/-- The restriction to the first quadrant of a composite is the composite of the restrictions. -/
@[simp]
lemma natRestrictHom_comp {K L M : HomologicalComplex C (up' u)} (f : K ⟶ L) (g : L ⟶ M) :
    natRestrictHom u (f ≫ g) = natRestrictHom u f ≫ natRestrictHom u g :=
  rfl

/-- The value of `HomologicalComplex.homologyMap` is the homology map of the short complex, by
definition. This is the spelling in which the naturality of the first-quadrant comparison is
available. -/
lemma homologyMap_eq {ι : Type*} {c : ComplexShape ι} {K L : HomologicalComplex C c}
    (f : K ⟶ L) (i : ι) :
    homologyMap f i = ShortComplex.homologyMap ((shortComplexFunctor C c i).map f) :=
  rfl

end Restrict

section Comparison

variable {u : ℤ × ℤ} (K : HomologicalComplex C (up' u)) (pq : ℕ × ℕ)

open scoped Classical in
/-- The comparison of the first entry of the first-quadrant short complex at `pq` with the first
entry of the ambient one: the canonical identification where `pq` has a predecessor in `ℕ × ℕ`,
and the zero morphism where it does not. -/
def natPrevMap :
    K.X (natEmb ((spectralSequenceNat u).prev pq)) ⟶ K.X ((up' u).prev (natEmb pq)) :=
  if h : ∃ a : ℕ × ℕ, (spectralSequenceNat u).Rel a pq then
    eqToHom (congrArg K.X (natEmb_prev u pq h))
  else 0

open scoped Classical in
/-- The comparison of the third entry of the ambient short complex at `natEmb pq` with the third
entry of the first-quadrant one: the canonical identification where `pq` has a successor in
`ℕ × ℕ`, and the zero morphism where it does not. -/
def natNextMap :
    K.X ((up' u).next (natEmb pq)) ⟶ K.X (natEmb ((spectralSequenceNat u).next pq)) :=
  if h : ∃ b : ℕ × ℕ, (spectralSequenceNat u).Rel pq b then
    eqToHom (congrArg K.X (natEmb_next u pq h).symm)
  else 0

open scoped Classical in
/-- Where `pq` has a predecessor in `ℕ × ℕ`, the comparison of first entries is the canonical
identification. -/
lemma natPrevMap_eq_eqToHom (h : ∃ a : ℕ × ℕ, (spectralSequenceNat u).Rel a pq) :
    K.natPrevMap pq = eqToHom (congrArg K.X (natEmb_prev u pq h)) :=
  dite_eq_left h

open scoped Classical in
/-- Where `pq` has no predecessor in `ℕ × ℕ`, the comparison of first entries is zero. -/
lemma natPrevMap_eq_zero (h : ¬ ∃ a : ℕ × ℕ, (spectralSequenceNat u).Rel a pq) :
    K.natPrevMap pq = 0 :=
  dite_eq_right h

open scoped Classical in
/-- Where `pq` has a successor in `ℕ × ℕ`, the comparison of third entries is the canonical
identification. -/
lemma natNextMap_eq_eqToHom (h : ∃ b : ℕ × ℕ, (spectralSequenceNat u).Rel pq b) :
    K.natNextMap pq = eqToHom (congrArg K.X (natEmb_next u pq h).symm) :=
  dite_eq_left h

open scoped Classical in
/-- Where `pq` has no successor in `ℕ × ℕ`, the comparison of third entries is zero. -/
lemma natNextMap_eq_zero (h : ¬ ∃ b : ℕ × ℕ, (spectralSequenceNat u).Rel pq b) :
    K.natNextMap pq = 0 :=
  dite_eq_right h

/-- The comparison of first entries is compatible with the differentials into `natEmb pq`. -/
lemma natPrevMap_comp_d :
    K.natPrevMap pq ≫ K.d ((up' u).prev (natEmb pq)) (natEmb pq) =
      K.d (natEmb ((spectralSequenceNat u).prev pq)) (natEmb pq) := by
  by_cases h : ∃ a : ℕ × ℕ, (spectralSequenceNat u).Rel a pq
  · rw [K.natPrevMap_eq_eqToHom pq h]
    exact K.XIsoOfEq_hom_comp_d (natEmb_prev u pq h) (natEmb pq)
  · rw [K.natPrevMap_eq_zero pq h, zero_comp,
      (spectralSequenceNat u).prev_eq_self' pq fun k hk => h ⟨k, hk⟩]
    exact (K.shape _ _ fun h' =>
      h ⟨pq, (spectralSequenceNat_rel_iff_up' u pq pq).2 h'⟩).symm

/-- The comparison of third entries is compatible with the differentials out of `natEmb pq`. -/
lemma d_comp_natNextMap :
    K.d (natEmb pq) ((up' u).next (natEmb pq)) ≫ K.natNextMap pq =
      K.d (natEmb pq) (natEmb ((spectralSequenceNat u).next pq)) := by
  by_cases h : ∃ b : ℕ × ℕ, (spectralSequenceNat u).Rel pq b
  · rw [K.natNextMap_eq_eqToHom pq h]
    exact K.d_comp_XIsoOfEq_hom (natEmb_next u pq h).symm (natEmb pq)
  · rw [K.natNextMap_eq_zero pq h, comp_zero,
      (spectralSequenceNat u).next_eq_self' pq fun k hk => h ⟨k, hk⟩]
    exact (K.shape _ _ fun h' =>
      h ⟨pq, (spectralSequenceNat_rel_iff_up' u pq pq).2 h'⟩).symm

/-- The comparison of first entries is natural in the complex. -/
lemma natPrevMap_naturality {K L : HomologicalComplex C (up' u)} (f : K ⟶ L) (pq : ℕ × ℕ) :
    f.f (natEmb ((spectralSequenceNat u).prev pq)) ≫ L.natPrevMap pq =
      K.natPrevMap pq ≫ f.f ((up' u).prev (natEmb pq)) := by
  by_cases h : ∃ a : ℕ × ℕ, (spectralSequenceNat u).Rel a pq
  · rw [K.natPrevMap_eq_eqToHom pq h, L.natPrevMap_eq_eqToHom pq h]
    exact eqToHom_X_naturality f (natEmb_prev u pq h)
  · rw [K.natPrevMap_eq_zero pq h, L.natPrevMap_eq_zero pq h, zero_comp, comp_zero]

/-- The comparison of third entries is natural in the complex. -/
lemma natNextMap_naturality {K L : HomologicalComplex C (up' u)} (f : K ⟶ L) (pq : ℕ × ℕ) :
    f.f ((up' u).next (natEmb pq)) ≫ L.natNextMap pq =
      K.natNextMap pq ≫ f.f (natEmb ((spectralSequenceNat u).next pq)) := by
  by_cases h : ∃ b : ℕ × ℕ, (spectralSequenceNat u).Rel pq b
  · rw [K.natNextMap_eq_eqToHom pq h, L.natNextMap_eq_eqToHom pq h]
    exact eqToHom_X_naturality f (natEmb_next u pq h).symm
  · rw [K.natNextMap_eq_zero pq h, L.natNextMap_eq_zero pq h, zero_comp, comp_zero]

/-- The comparison of first entries is an epimorphism, for a complex vanishing outside the first
quadrant: either it is an isomorphism, or its target is a zero object. -/
lemma epi_natPrevMap
    (hK : ∀ x : ℤ × ℤ, x.1 < 0 ∨ x.2 < 0 → IsZero (K.X x)) :
    Epi (K.natPrevMap pq) := by
  by_cases h : ∃ a : ℕ × ℕ, (spectralSequenceNat u).Rel a pq
  · rw [K.natPrevMap_eq_eqToHom pq h]
    infer_instance
  · rw [K.natPrevMap_eq_zero pq h]
    exact epi_of_target_iso_zero _
      (hK _ (prev_up'_natEmb_lt_zero u pq fun k hk => h ⟨k, hk⟩)).isoZero

/-- The comparison of third entries is a monomorphism, for a complex vanishing outside the first
quadrant: either it is an isomorphism, or its source is a zero object. -/
lemma mono_natNextMap
    (hK : ∀ x : ℤ × ℤ, x.1 < 0 ∨ x.2 < 0 → IsZero (K.X x)) :
    Mono (K.natNextMap pq) := by
  by_cases h : ∃ b : ℕ × ℕ, (spectralSequenceNat u).Rel pq b
  · rw [K.natNextMap_eq_eqToHom pq h]
    infer_instance
  · rw [K.natNextMap_eq_zero pq h]
    exact mono_of_source_iso_zero _
      (hK _ (next_up'_natEmb_lt_zero u pq fun k hk => h ⟨k, hk⟩)).isoZero

/-- The short complex through which the homology of the restriction is compared with the ambient
homology: its first entry is the ambient one and its third entry the first-quadrant one. -/
abbrev natMid : ShortComplex C :=
  K.sc' ((up' u).prev (natEmb pq)) (natEmb pq) (natEmb ((spectralSequenceNat u).next pq))

/-- The comparison of the short complex computing the homology of the restriction at `pq` with
`HomologicalComplex.natMid`. It is the identity on the middle and the last entry. -/
def natScFromNat : (natRestrict u K).sc pq ⟶ K.natMid pq where
  τ₁ := K.natPrevMap pq
  τ₂ := 𝟙 _
  τ₃ := 𝟙 _
  comm₁₂ := by
    change K.natPrevMap pq ≫ K.d ((up' u).prev (natEmb pq)) (natEmb pq) =
      K.d (natEmb ((spectralSequenceNat u).prev pq)) (natEmb pq) ≫ 𝟙 _
    rw [comp_id]
    exact K.natPrevMap_comp_d pq
  comm₂₃ := by
    change 𝟙 _ ≫ K.d (natEmb pq) (natEmb ((spectralSequenceNat u).next pq)) =
      K.d (natEmb pq) (natEmb ((spectralSequenceNat u).next pq)) ≫ 𝟙 _
    rw [id_comp, comp_id]

/-- The first component of `HomologicalComplex.natScFromNat` is
`HomologicalComplex.natPrevMap`. -/
@[simp]
lemma natScFromNat_τ₁ : (K.natScFromNat pq).τ₁ = K.natPrevMap pq := rfl

/-- The middle component of `HomologicalComplex.natScFromNat` is the identity. -/
@[simp]
lemma natScFromNat_τ₂ : (K.natScFromNat pq).τ₂ = 𝟙 _ := rfl

/-- The third component of `HomologicalComplex.natScFromNat` is the identity. -/
@[simp]
lemma natScFromNat_τ₃ : (K.natScFromNat pq).τ₃ = 𝟙 _ := rfl

/-- The comparison of the short complex computing the ambient homology at `natEmb pq` with
`HomologicalComplex.natMid`. It is the identity on the first and the middle entry. -/
def natScFromInt : K.sc (natEmb pq) ⟶ K.natMid pq where
  τ₁ := 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := K.natNextMap pq
  comm₁₂ := by
    change 𝟙 _ ≫ K.d ((up' u).prev (natEmb pq)) (natEmb pq) =
      K.d ((up' u).prev (natEmb pq)) (natEmb pq) ≫ 𝟙 _
    rw [id_comp, comp_id]
  comm₂₃ := by
    change 𝟙 _ ≫ K.d (natEmb pq) (natEmb ((spectralSequenceNat u).next pq)) =
      K.d (natEmb pq) ((up' u).next (natEmb pq)) ≫ K.natNextMap pq
    rw [id_comp]
    exact (K.d_comp_natNextMap pq).symm

/-- The first component of `HomologicalComplex.natScFromInt` is the identity. -/
@[simp]
lemma natScFromInt_τ₁ : (K.natScFromInt pq).τ₁ = 𝟙 _ := rfl

/-- The middle component of `HomologicalComplex.natScFromInt` is the identity. -/
@[simp]
lemma natScFromInt_τ₂ : (K.natScFromInt pq).τ₂ = 𝟙 _ := rfl

/-- The third component of `HomologicalComplex.natScFromInt` is
`HomologicalComplex.natNextMap`. -/
@[simp]
lemma natScFromInt_τ₃ : (K.natScFromInt pq).τ₃ = K.natNextMap pq := rfl

variable (hK : ∀ x : ℤ × ℤ, x.1 < 0 ∨ x.2 < 0 → IsZero (K.X x))

include hK in
/-- The comparison from the first-quadrant side is an isomorphism on homology. -/
lemma isIso_homologyMap_natScFromNat :
    IsIso (ShortComplex.homologyMap (K.natScFromNat pq)) := by
  exact ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono' _ (K.epi_natPrevMap pq hK)
    (inferInstanceAs (IsIso (𝟙 _))) (inferInstanceAs (Mono (𝟙 _)))

include hK in
/-- The comparison from the ambient side is an isomorphism on homology. -/
lemma isIso_homologyMap_natScFromInt :
    IsIso (ShortComplex.homologyMap (K.natScFromInt pq)) := by
  exact ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono' _
    (inferInstanceAs (Epi (𝟙 _))) (inferInstanceAs (IsIso (𝟙 _)))
    (K.mono_natNextMap pq hK)

/-- **The homology of the first-quadrant restriction is the ambient homology.** Both short
complexes map to `HomologicalComplex.natMid` by a morphism which is epi, iso, mono on the three
entries, hence an isomorphism on homology. -/
def natRestrictHomologyIso :
    ((natRestrict u K).sc pq).homology ≅ (K.sc (natEmb pq)).homology :=
  @asIso _ _ _ _ _ (K.isIso_homologyMap_natScFromNat pq hK) ≪≫
    (@asIso _ _ _ _ _ (K.isIso_homologyMap_natScFromInt pq hK)).symm

include hK in
/-- The characterizing property of the comparison isomorphism: composed with the comparison from
the ambient side it is the comparison from the first-quadrant side. -/
lemma natRestrictHomologyIso_hom_comp :
    (natRestrictHomologyIso K pq hK).hom ≫ ShortComplex.homologyMap (K.natScFromInt pq) =
      ShortComplex.homologyMap (K.natScFromNat pq) := by
  have := K.isIso_homologyMap_natScFromInt pq hK
  rw [natRestrictHomologyIso, Iso.trans_hom, Iso.symm_hom, assoc, asIso_inv, asIso_hom,
    IsIso.inv_hom_id, comp_id]

end Comparison

section Naturality

variable {u : ℤ × ℤ} {K L : HomologicalComplex C (up' u)} (f : K ⟶ L) (pq : ℕ × ℕ)

/-- The comparison from the first-quadrant side is natural in the complex. -/
lemma natScFromNat_naturality :
    (shortComplexFunctor C (spectralSequenceNat u) pq).map (natRestrictHom u f) ≫
        L.natScFromNat pq =
      K.natScFromNat pq ≫
        (shortComplexFunctor' C (up' u) ((up' u).prev (natEmb pq)) (natEmb pq)
          (natEmb ((spectralSequenceNat u).next pq))).map f := by
  refine ShortComplex.hom_ext _ _ ?_ ?_ ?_
  · exact natPrevMap_naturality f pq
  · exact (comp_id _).trans (id_comp _).symm
  · exact (comp_id _).trans (id_comp _).symm

/-- The comparison from the ambient side is natural in the complex. -/
lemma natScFromInt_naturality :
    (shortComplexFunctor C (up' u) (natEmb pq)).map f ≫ L.natScFromInt pq =
      K.natScFromInt pq ≫
        (shortComplexFunctor' C (up' u) ((up' u).prev (natEmb pq)) (natEmb pq)
          (natEmb ((spectralSequenceNat u).next pq))).map f := by
  refine ShortComplex.hom_ext _ _ ?_ ?_ ?_
  · exact (comp_id _).trans (id_comp _).symm
  · exact (comp_id _).trans (id_comp _).symm
  · exact natNextMap_naturality f pq

variable (hK : ∀ x : ℤ × ℤ, x.1 < 0 ∨ x.2 < 0 → IsZero (K.X x))
  (hL : ∀ x : ℤ × ℤ, x.1 < 0 ∨ x.2 < 0 → IsZero (L.X x))

include hK hL in
/-- **The comparison isomorphism on homology is natural in the complex.** This is what makes the
restriction of a spectral sequence to the first quadrant functorial: the `comm` axiom of a
morphism of spectral sequences is exactly this naturality square composed with the naturality of
the `iso` fields of the ambient spectral sequences. -/
lemma natRestrictHomologyIso_hom_naturality :
    ShortComplex.homologyMap
          ((shortComplexFunctor C (spectralSequenceNat u) pq).map (natRestrictHom u f)) ≫
        (natRestrictHomologyIso L pq hL).hom =
      (natRestrictHomologyIso K pq hK).hom ≫
        ShortComplex.homologyMap ((shortComplexFunctor C (up' u) (natEmb pq)).map f) := by
  have := L.isIso_homologyMap_natScFromInt pq hL
  have h₁ : ShortComplex.homologyMap
        ((shortComplexFunctor C (spectralSequenceNat u) pq).map (natRestrictHom u f)) ≫
          ShortComplex.homologyMap (L.natScFromNat pq) =
      ShortComplex.homologyMap (K.natScFromNat pq) ≫
        ShortComplex.homologyMap
          ((shortComplexFunctor' C (up' u) ((up' u).prev (natEmb pq)) (natEmb pq)
            (natEmb ((spectralSequenceNat u).next pq))).map f) := by
    rw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp,
      natScFromNat_naturality f pq]
  have h₂ : ShortComplex.homologyMap ((shortComplexFunctor C (up' u) (natEmb pq)).map f) ≫
        ShortComplex.homologyMap (L.natScFromInt pq) =
      ShortComplex.homologyMap (K.natScFromInt pq) ≫
        ShortComplex.homologyMap
          ((shortComplexFunctor' C (up' u) ((up' u).prev (natEmb pq)) (natEmb pq)
            (natEmb ((spectralSequenceNat u).next pq))).map f) := by
    rw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp,
      natScFromInt_naturality f pq]
  rw [← cancel_mono (ShortComplex.homologyMap (L.natScFromInt pq)), assoc,
    natRestrictHomologyIso_hom_comp L pq hL, assoc, h₂, ← assoc,
    natRestrictHomologyIso_hom_comp K pq hK, h₁]

include hK hL in
/-- The naturality of the comparison isomorphism, in the `HomologicalComplex.homologyMap`
spelling. This is the same statement as `natRestrictHomologyIso_hom_naturality`, restated so
that it applies to the `comm` axiom of a morphism of spectral sequences. -/
lemma natRestrictHomologyIso_hom_naturality' :
    homologyMap (natRestrictHom u f) pq ≫ (natRestrictHomologyIso L pq hL).hom =
      (natRestrictHomologyIso K pq hK).hom ≫ homologyMap f (natEmb pq) :=
  natRestrictHomologyIso_hom_naturality f pq hK hL

end Naturality

end HomologicalComplex

namespace CategoryTheory

namespace SpectralSequence

open ComplexShape HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C] {r₀ : ℤ} {u : ℤ → ℤ × ℤ}

/-- A spectral sequence indexed by `ℤ × ℤ` **lies in the first quadrant** if every object of
every page outside the first quadrant is zero. -/
def IsFirstQuadrant (E : SpectralSequence C (fun r => up' (u r)) r₀) : Prop :=
  ∀ (r : ℤ) (hr : r₀ ≤ r) (x : ℤ × ℤ), x.1 < 0 ∨ x.2 < 0 → IsZero ((E.page r hr).X x)

/-- **First-quadrant vanishing propagates from the starting page.** It is enough to check that
the objects of the page `r₀` outside the first quadrant are zero: each later page is, at every
index, the homology of the previous one at that index, and the homology of a short complex whose
middle term is zero is zero. -/
@[ega "0 11.1.6" "special case"]
lemma isFirstQuadrant_of_isZero_page (E : SpectralSequence C (fun r => up' (u r)) r₀)
    (h : ∀ x : ℤ × ℤ, x.1 < 0 ∨ x.2 < 0 → IsZero ((E.page r₀ le_rfl).X x)) :
    IsFirstQuadrant E := by
  intro r hr x hx
  induction r, hr using Int.leInduction with
  | base => exact h x hx
  | succ n hn ih =>
    exact (Iso.isZero_iff (E.iso n (n + 1) x rfl hn)).1
      (ShortComplex.isZero_homology_of_isZero_X₂ ((E.page n hn).sc x) ih)

variable {E E' : SpectralSequence C (fun r => up' (u r)) r₀}

/-- **The restriction of a first-quadrant spectral sequence to `ℕ × ℕ`.** The pages are the
first-quadrant restrictions of the pages, and the identification of the homology of a page with
the next page is the ambient one, transported by
`HomologicalComplex.natRestrictHomologyIso`. -/
def natRestrict (E : SpectralSequence C (fun r => up' (u r)) r₀) (hE : IsFirstQuadrant E) :
    SpectralSequence C (fun r => spectralSequenceNat (u r)) r₀ where
  page r hr := HomologicalComplex.natRestrict (u r) (E.page r hr)
  iso r r' pq hrr' hr :=
    natRestrictHomologyIso (E.page r hr) pq (hE r hr) ≪≫ E.iso r r' (natEmb pq) hrr' hr

/-- The pages of the first-quadrant restriction of a spectral sequence are the first-quadrant
restrictions of its pages. -/
@[simp]
lemma natRestrict_page (E : SpectralSequence C (fun r => up' (u r)) r₀) (hE : IsFirstQuadrant E)
    (r : ℤ) (hr : r₀ ≤ r) :
    (natRestrict E hE).page r hr = HomologicalComplex.natRestrict (u r) (E.page r hr) :=
  rfl

/-- **The restriction to the first quadrant of a morphism of spectral sequences.** -/
def natRestrictMap (f : E ⟶ E') (hE : IsFirstQuadrant E) (hE' : IsFirstQuadrant E') :
    natRestrict E hE ⟶ natRestrict E' hE' where
  hom r hr := natRestrictHom (u r) (f.hom r hr)
  comm r r' pq hrr' hr := by
    have hr' : r₀ ≤ r' := by omega
    change homologyMap (natRestrictHom (u r) (f.hom r hr)) pq ≫
        ((natRestrictHomologyIso (E'.page r hr) pq (hE' r hr)).hom ≫
          (E'.iso r r' (natEmb pq) hrr' hr).hom) =
      ((natRestrictHomologyIso (E.page r hr) pq (hE r hr)).hom ≫
          (E.iso r r' (natEmb pq) hrr' hr).hom) ≫ (f.hom r' hr').f (natEmb pq)
    have h₁ := natRestrictHomologyIso_hom_naturality' (f.hom r hr) pq (hE r hr) (hE' r hr)
    have h₂ := f.comm r r' (natEmb pq) hrr' hr
    exact (assoc _ _ _).symm.trans
      ((congrArg (· ≫ (E'.iso r r' (natEmb pq) hrr' hr).hom) h₁).trans
        ((assoc _ _ _).trans
          ((congrArg ((natRestrictHomologyIso (E.page r hr) pq (hE r hr)).hom ≫ ·) h₂).trans
            (assoc _ _ _).symm)))

/-- The components of the first-quadrant restriction of a morphism of spectral sequences are the
first-quadrant restrictions of its components. -/
@[simp]
lemma natRestrictMap_hom (f : E ⟶ E') (hE : IsFirstQuadrant E) (hE' : IsFirstQuadrant E')
    (r : ℤ) (hr : r₀ ≤ r) :
    (natRestrictMap f hE hE').hom r hr = natRestrictHom (u r) (f.hom r hr) :=
  rfl

/-- The restriction to the first quadrant preserves identities. -/
lemma natRestrictMap_id (hE : IsFirstQuadrant E) :
    natRestrictMap (𝟙 E) hE hE = 𝟙 _ :=
  SpectralSequence.hom_ext fun _ _ => rfl

/-- The restriction to the first quadrant preserves composition. -/
lemma natRestrictMap_comp {E'' : SpectralSequence C (fun r => up' (u r)) r₀} (f : E ⟶ E')
    (g : E' ⟶ E'') (hE : IsFirstQuadrant E) (hE' : IsFirstQuadrant E')
    (hE'' : IsFirstQuadrant E'') :
    natRestrictMap (f ≫ g) hE hE'' = natRestrictMap f hE hE' ≫ natRestrictMap g hE' hE'' :=
  SpectralSequence.hom_ext fun _ _ => rfl

/-- **A functor into spectral sequences indexed by `ℤ × ℤ` whose values all lie in the first
quadrant restricts to a functor into first-quadrant spectral sequences.** This is the form in
which a functorial first-quadrant spectral sequence is obtained. -/
def natRestrictComp {D : Type*} [Category D]
    (F : D ⥤ SpectralSequence C (fun r => up' (u r)) r₀)
    (hF : ∀ X : D, IsFirstQuadrant (F.obj X)) :
    D ⥤ SpectralSequence C (fun r => spectralSequenceNat (u r)) r₀ where
  obj X := natRestrict (F.obj X) (hF X)
  map {X Y} φ := natRestrictMap (F.map φ) (hF X) (hF Y)
  map_id X := by rw [F.map_id, natRestrictMap_id]
  map_comp φ ψ := by rw [F.map_comp, natRestrictMap_comp]

/-- **An `E₂`-cohomological spectral sequence which vanishes outside the first quadrant is a
first-quadrant `E₂`-cohomological spectral sequence.** -/
abbrev natRestrictE₂ (E : E₂CohomologicalSpectralSequence C)
    (hE : IsFirstQuadrant (u := fun r => (r, 1 - r)) E) :
    E₂CohomologicalSpectralSequenceNat C :=
  natRestrict E hE

/-- **A functor into `E₂`-cohomological spectral sequences all of whose values vanish outside
the first quadrant restricts to a functor into first-quadrant ones.** -/
abbrev natRestrictE₂Comp {D : Type*} [Category D] (F : D ⥤ E₂CohomologicalSpectralSequence C)
    (hF : ∀ X : D, IsFirstQuadrant (u := fun r => (r, 1 - r)) (F.obj X)) :
    D ⥤ E₂CohomologicalSpectralSequenceNat C :=
  natRestrictComp F hF

end SpectralSequence

end CategoryTheory

end
