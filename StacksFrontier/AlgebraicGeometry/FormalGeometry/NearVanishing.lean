module

public import StacksFrontier.RingTheory.LocalCohomology.LowDegree
public import Mathlib.Order.KrullDimension

/-!
# Opens near the formal locus, and their sections

Let `I ⊆ 𝔞` be ideals of a commutative ring `A` and let `U = Spec(A) \ V(𝔞)`. The
algebraization statements of Stacks chapter 52 compare sections of a coherent module on
*arbitrarily small* open neighbourhoods of `U ∩ V(I)` inside `U` with compatible families of
sections of the quotients `F / Iⁿ F` on all of `U`.

This file sets up the left-hand side of that comparison: the index category of such
neighbourhoods, ordered by reverse inclusion so that the comparison is a *colimit*, and the
diagram of sections over them. It also records the local dimension invariant which the
dimension hypotheses of those statements are phrased with.

## Main definitions

* `Stacks.Algebraization.closureLocalDimension` — for a specialization `x ⤳ z` of points of
  `Spec A`, the Krull dimension of the local ring of `closure {x}` at `z`, realized as the
  Krull dimension of the interval of primes between `x` and `z`.
* `Stacks.Algebraization.OpensNearVanishing` — the opens `V ⊆ U` containing `U ∩ V(I)`,
  a category under reverse inclusion.
* `Stacks.Algebraization.opensNearVanishingFunctor` — that index category viewed inside the
  opposite of the opens of `U`.
* `Stacks.Algebraization.sectionsNearVanishing` — the diagram `V ↦ Γ(V, F)` of abelian groups.
* `Stacks.Algebraization.OpensNearVanishing.ofIdealOfLeRadical` — the neighbourhood cut out by an
  ideal `J` of `A`, and `Stacks.Algebraization.OpensNearVanishing.ofZeroLocusInter` the same for an
  ideal of a local ring meeting `V(I)` in the closed point only.

## Main results

* `Stacks.Algebraization.OpensNearVanishing.ι_image_openSet_ofIdeal` — the image in `Spec(A)`
  of the neighbourhood cut out by `J` is the affine complement `Spec(A) ∖ V(J)`, and
  `Stacks.Algebraization.OpensNearVanishing.ι_image_openSet_ofZeroLocusInter` the same over a
  local ring.
* `Stacks.Algebraization.OpensNearVanishing.exists_ideal_ι_image_openSet_eq` — conversely,
  every neighbourhood of the formal locus is cut out by an ideal of `A`.

## References

* [Stacks Project, Tag 0EG2](https://stacks.math.columbia.edu/tag/0EG2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

/-- The dimension of the local ring of the closure of `x` at `z`, for a specialization
`x ⤳ z` of points of `Spec A`. It is computed as the Krull dimension of the poset of primes
lying between `x` and `z`, which is the spectrum of that local ring. -/
def closureLocalDimension (A : Type u) [CommRing A] (x z : PrimeSpectrum A) : WithBot ℕ∞ :=
  Order.krullDim {p : PrimeSpectrum A // x.asIdeal ≤ p.asIdeal ∧ p.asIdeal ≤ z.asIdeal}

/-- An open subset of `U = Spec(A) \ V(𝔞)` containing `U ∩ V(I)`. These are the
neighbourhoods of the formal locus over which the sections of the algebraization statements
are taken. -/
structure OpensNearVanishing (A : Type u) [CommRing A] (I a : Ideal A) where
  /-- The underlying open of `U`. -/
  openSet : (complementZeroLocus A a : Scheme).Opens
  /-- The open contains every point of `U` lying in `V(I)`. -/
  contains_vanishing : ∀ x : (complementZeroLocus A a : Scheme),
    I ≤ x.1.asIdeal → x ∈ openSet

/-- `OpensNearVanishing` is ordered by **reverse** inclusion: a morphism `V ⟶ W` is the
assertion `W ≤ V`. With this convention shrinking the neighbourhood moves forward, so the
sections of the algebraization statements form a colimit. -/
instance (A : Type u) [CommRing A] (I a : Ideal A) :
    Category.{0} (OpensNearVanishing A I a) where
  Hom V W := PLift (W.openSet ≤ V.openSet)
  id V := ⟨le_rfl⟩
  comp g h := ⟨h.down.trans g.down⟩
  assoc := by intros; rfl
  id_comp := by intros; rfl
  comp_id := by intros; rfl

/-- The index category of neighbourhoods of the formal locus, viewed inside the opposite
category of opens of `U`. Reverse inclusion on the source becomes the opposite of inclusion
on the target, so this functor is covariant. -/
def opensNearVanishingFunctor (A : Type u) [CommRing A] (I a : Ideal A) :
    OpensNearVanishing A I a ⥤ (complementZeroLocus A a : Scheme).Opensᵒᵖ where
  obj V := .op V.openSet
  map g := (homOfLE g.down).op
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The diagram of sections of `F` over the shrinking neighbourhoods of the formal locus. Its
colimit is the group of sections of `F` defined near `U ∩ V(I)`. -/
def sectionsNearVanishing (A : Type u) [CommRing A] (I a : Ideal A)
    (F : (complementZeroLocus A a : Scheme).Modules) :
    OpensNearVanishing A I a ⥤ Ab.{u} :=
  opensNearVanishingFunctor A I a ⋙ F.val.presheaf

end Stacks.Algebraization

/-! ## Neighbourhoods of the formal locus cut out by an ideal

The algebraization statements of Stacks chapter 52 take their neighbourhoods `V` of `U ∩ V(I)`
inside `U = Spec(A) ∖ V(𝔞)`, while the finiteness and comparison statements they are proved from
are stated on the affine complement `Spec(A) ∖ V(J)` of the zero locus of an ideal of `A`. The
two vocabularies meet here: every `V` is the trace on `U` of some `Spec(A) ∖ V(J)`, and
conversely.
-/

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A]

/-- **`Spec(A) ∖ V(J)` sits inside `Spec(A) ∖ V(𝔞)` exactly when `J ⊆ √𝔞`.** Taking complements
turns the inclusion of opens into `V(𝔞) ⊆ V(J)`, which is the Galois correspondence between
ideals and closed subsets of the spectrum. -/
theorem complementZeroLocus_le_complementZeroLocus_iff (a J : Ideal A) :
    complementZeroLocus A J ≤ complementZeroLocus A a ↔ J ≤ a.radical := by
  rw [IsConcreteLE.le_iff, ← PrimeSpectrum.zeroLocus_subset_zeroLocus_iff]
  constructor
  · intro h p hp
    exact not_not.1 fun hp' ↦ h hp' hp
  · intro h p hp hp'
    exact hp (h hp')

/-- A prime lies in `Spec(A) ∖ V(J)` exactly when it does not contain `J`. -/
theorem mem_complementZeroLocus_iff_not_le (J : Ideal A) (p : PrimeSpectrum A) :
    p ∈ complementZeroLocus A J ↔ ¬ J ≤ p.asIdeal :=
  not_congr ((PrimeSpectrum.mem_zeroLocus _ _).trans SetLike.coe_subset_coe)

end Stacks.LocalCohomology

namespace Stacks.Algebraization

open Stacks.LocalCohomology

namespace OpensNearVanishing

variable {A : Type u} [CommRing A]

/-- **The neighbourhood of the formal locus cut out by an ideal `J` of `A`:** the trace on
`U = Spec(A) ∖ V(𝔞)` of the affine complement `Spec(A) ∖ V(J)`.

The hypothesis `J ⊆ √𝔞` says `V(𝔞) ⊆ V(J)`, so `Spec(A) ∖ V(J)` is already contained in `U` and
the trace loses nothing — this is what
`Stacks.Algebraization.OpensNearVanishing.ι_image_openSet_ofIdeal` records. The hypothesis
`𝔞 ⊆ √(I + J)` says `V(I) ∩ V(J) ⊆ V(𝔞)`, which is exactly the requirement that the trace
contain `U ∩ V(I)`. -/
def ofIdealOfLeRadical (I a J : Ideal A) (_hJa : J ≤ a.radical) (haIJ : a ≤ (I ⊔ J).radical) :
    OpensNearVanishing A I a where
  openSet := (complementZeroLocus A a).ι ⁻¹ᵁ complementZeroLocus A J
  contains_vanishing x hx := by
    refine (mem_complementZeroLocus_iff_not_le J x.1).2 fun hJx ↦ ?_
    refine (mem_complementZeroLocus_iff_not_le a x.1).1 x.2 ?_
    exact haIJ.trans (x.1.isPrime.radical_le_iff.2 (sup_le hx hJx))

/-- **The image in `Spec(A)` of the neighbourhood cut out by `J` is `Spec(A) ∖ V(J)`.** This is
the bridge between the two vocabularies: a statement about the sections of a module on the
affine complement of a zero locus becomes a statement about its sections on a neighbourhood of
the formal locus, and conversely.

The image of a preimage along an open immersion is the intersection with the range, which for
the inclusion of an open subscheme is that open itself; and `J ⊆ √𝔞` makes the intersection of
`Spec(A) ∖ V(J)` with `Spec(A) ∖ V(𝔞)` the first of the two. -/
theorem ι_image_openSet_ofIdeal (I a J : Ideal A) (hJa : J ≤ a.radical)
    (haIJ : a ≤ (I ⊔ J).radical) :
    (complementZeroLocus A a).ι ''ᵁ (ofIdealOfLeRadical I a J hJa haIJ).openSet =
      complementZeroLocus A J := by
  change (complementZeroLocus A a).ι ''ᵁ (complementZeroLocus A a).ι ⁻¹ᵁ
      complementZeroLocus A J = _
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right]
  exact (complementZeroLocus_le_complementZeroLocus_iff a J).2 hJa

/-- **Every neighbourhood of the formal locus is cut out by an ideal of `A`**, with the two
inclusions of `Stacks.Algebraization.OpensNearVanishing.ofIdealOfLeRadical` holding for it: the
image of `V` in `Spec(A)` is the affine complement `Spec(A) ∖ V(J)` of the zero locus of the
ideal `J` of functions vanishing on the complement of that image. -/
theorem exists_ideal_ι_image_openSet_eq (I a : Ideal A) (V : OpensNearVanishing A I a) :
    ∃ J : Ideal A, J ≤ a.radical ∧ a ≤ (I ⊔ J).radical ∧
      (complementZeroLocus A a).ι ''ᵁ V.openSet = complementZeroLocus A J := by
  set W : (Spec (CommRingCat.of A)).Opens := (complementZeroLocus A a).ι ''ᵁ V.openSet
  -- The complement of the image is closed, so it is the zero locus of the ideal of functions
  -- vanishing on it.
  have hWopen : IsOpen {p : PrimeSpectrum A | p ∈ W} := W.2
  have hTclosed : IsClosed {p : PrimeSpectrum A | p ∉ W} := hWopen.isClosed_compl
  have hJzero : PrimeSpectrum.zeroLocus
      ((PrimeSpectrum.vanishingIdeal {p : PrimeSpectrum A | p ∉ W} : Ideal A) : Set A) =
      {p : PrimeSpectrum A | p ∉ W} := by
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hTclosed.closure_eq]
  -- Hence `Spec(A) ∖ V(J)` is the image itself.
  have hmem : ∀ p : PrimeSpectrum A,
      p ∈ complementZeroLocus A
          (PrimeSpectrum.vanishingIdeal {q : PrimeSpectrum A | q ∉ W}) ↔ p ∈ W := by
    intro p
    have key : PrimeSpectrum.vanishingIdeal {q : PrimeSpectrum A | q ∉ W} ≤ p.asIdeal ↔
        p ∉ W := by
      rw [← SetLike.coe_subset_coe, ← PrimeSpectrum.mem_zeroLocus, hJzero]
      exact Iff.rfl
    rw [mem_complementZeroLocus_iff_not_le, key, not_not]
  -- The image lies in `U`, and it contains every point of `U ∩ V(I)`.
  have hWU : ∀ p : PrimeSpectrum A, p ∈ W → ¬ a ≤ p.asIdeal := fun p hp ↦
    (mem_complementZeroLocus_iff_not_le a p).1
      (IsConcreteLE.le_iff.1 ((complementZeroLocus A a).ι_image_le V.openSet) hp)
  have hVW : ∀ p : PrimeSpectrum A, ¬ a ≤ p.asIdeal → I ≤ p.asIdeal → p ∈ W := fun p hpa hpI ↦
    (Scheme.Opens.mem_ι_image_iff _).2
      (V.contains_vanishing ⟨p, (mem_complementZeroLocus_iff_not_le a p).2 hpa⟩ hpI)
  have himage : W = complementZeroLocus A
      (PrimeSpectrum.vanishingIdeal {q : PrimeSpectrum A | q ∉ W}) :=
    le_antisymm (IsConcreteLE.le_iff.2 fun p hp ↦ (hmem p).2 hp)
      (IsConcreteLE.le_iff.2 fun p hp ↦ (hmem p).1 hp)
  refine ⟨PrimeSpectrum.vanishingIdeal {q : PrimeSpectrum A | q ∉ W}, ?_, ?_, himage⟩
  · -- `V(𝔞) ⊆ V(J)`: the open `Spec(A) ∖ V(J)` is the image, which lies in `U`.
    refine (complementZeroLocus_le_complementZeroLocus_iff a _).1 ?_
    exact IsConcreteLE.le_iff.2 fun p hp ↦
      (mem_complementZeroLocus_iff_not_le a p).2 (hWU p ((hmem p).1 hp))
  · -- `V(I) ∩ V(J) ⊆ V(𝔞)`: such a prime is a point of `U ∩ V(I)`, hence of the image, and so
    -- does not lie on `V(J)`.
    refine (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff (I ⊔ _) a).1 fun p hp ↦ ?_
    rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe] at hp ⊢
    by_contra hpa
    exact (mem_complementZeroLocus_iff_not_le _ p).1
      ((hmem p).2 (hVW p hpa (le_sup_left.trans hp))) (le_sup_right.trans hp)

/-! ### The punctured spectrum of a local ring -/

section IsLocalRing

open IsLocalRing

variable [IsLocalRing A]

/-- An ideal meeting `V(I)` in the closed point only is contained in the maximal ideal, the
closed point being a point of its zero locus. -/
theorem le_radical_maximalIdeal_of_zeroLocus_inter {I J : Ideal A}
    (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      {closedPoint A}) :
    J ≤ (maximalIdeal A).radical :=
  le_trans (hV.ge rfl).1 Ideal.le_radical

/-- An ideal meeting `V(I)` in the closed point only has `𝔪 ⊆ √(I + J)`: a prime containing
both `I` and `J` lies in `V(J) ∩ V(I)`, hence is the closed point. -/
theorem maximalIdeal_le_radical_sup_of_zeroLocus_inter {I J : Ideal A}
    (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      {closedPoint A}) :
    maximalIdeal A ≤ (I ⊔ J).radical := by
  refine (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff (I ⊔ J) (maximalIdeal A)).1 fun p hp ↦ ?_
  have hsup : I ⊔ J ≤ p.asIdeal := hp
  have hpc : p = closedPoint A :=
    hV.subset ⟨le_sup_right.trans hsup, le_sup_left.trans hsup⟩
  exact (PrimeSpectrum.mem_zeroLocus p _).2 (hpc ▸ subset_rfl)

/-- **The neighbourhood of the formal locus cut out by an ideal `J` with `V(J) ∩ V(I) = {𝔪}`.**
This is the shape in which the ideals of Stacks 0DXP and Stacks 0DXQ arrive: the two inclusions
of `Stacks.Algebraization.OpensNearVanishing.ofIdealOfLeRadical` hold for such a `J` at `𝔞 = 𝔪`. -/
def ofZeroLocusInter (I J : Ideal A)
    (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      {closedPoint A}) :
    OpensNearVanishing A I (maximalIdeal A) :=
  ofIdealOfLeRadical I (maximalIdeal A) J (le_radical_maximalIdeal_of_zeroLocus_inter hV)
    (maximalIdeal_le_radical_sup_of_zeroLocus_inter hV)

/-- **The image in `Spec(A)` of the neighbourhood cut out by `J` is `Spec(A) ∖ V(J)`**, for an
ideal `J` of a local ring meeting `V(I)` in the closed point only. This is the identification
that carries a statement about the sections of a module on `Spec(A) ∖ V(J)` over to the
neighbourhoods of the formal locus inside the punctured spectrum. -/
theorem ι_image_openSet_ofZeroLocusInter (I J : Ideal A)
    (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      {closedPoint A}) :
    (complementZeroLocus A (maximalIdeal A)).ι ''ᵁ (ofZeroLocusInter I J hV).openSet =
      complementZeroLocus A J :=
  ι_image_openSet_ofIdeal I (maximalIdeal A) J _ _

end IsLocalRing

end OpensNearVanishing

end Stacks.Algebraization

end
