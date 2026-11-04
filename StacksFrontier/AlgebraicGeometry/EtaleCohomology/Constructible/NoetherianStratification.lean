module

public import Mathlib.Topology.NoetherianSpace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible
public import StacksFrontier.AlgebraicGeometry.Schemes.ZariskiAndSeparation.ReducedInducedLocallyClosed
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Building a constructible stratification by Noetherian induction

`AlgebraicGeometry.ConstructibleStratification B X U` is the datum a constructible sheaf is tested
against on each affine open `U`: a finite family of objects of the big étale site, immersed in `X`,
with pairwise disjoint constructible images covering `U`. Every statement about constructible
sheaves that produces a new stratification — rather than refining or restricting given ones — has
to build such a datum from scratch, and the two halves of that construction are what this file
supplies.

The first half is topological and is the Noetherian induction of Stacks 09BH: on a Noetherian
space, a property `P` of subsets which holds on *some* nonempty relatively open part of every
closed set gives a finite partition of an open set into locally closed parts each satisfying `P`.
The induction is the standard one on closed subsets, which are well founded under `⊆` exactly
because the space is Noetherian.

The second half turns a set-level partition into a `AlgebraicGeometry.ConstructibleStratification`.
A part is realised as a scheme by the reduced induced structure on a locally closed subset,
`Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed.reducedInducedScheme`, whose canonical
morphism to the ambient scheme is an immersion with the prescribed image. That morphism is a
monomorphism, so `AlgebraicGeometry.Scheme.size_lt_of_mono_of_isStrongPrelimit` places the part
below the site's cardinal cutoff — which is the one point where the construction uses that the
cutoff of a `AlgebraicGeometry.BigEtaleSite` is closed under powersets.

## Main results

* `Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed.isImmersion_reducedInducedInclusion` and
  `.range_reducedInducedInclusion`: the reduced induced scheme on a locally closed subset is
  immersed in the ambient scheme with image that subset.
* `AlgebraicGeometry.ConstructibleStratification.ofPartition`: a finite partition of an open
  subscheme into locally closed parts, constructible inside it, is a constructible stratification.
* `AlgebraicGeometry.exists_locallyClosed_partition_of_noetherianSpace`: the Noetherian induction,
  as a statement about topological spaces.
* `AlgebraicGeometry.exists_constructibleStratification_of_noetherianSpace`: the two combined — on a
  scheme with Noetherian underlying space, a property which can always be achieved on a nonempty
  relatively open part of a closed set is achieved on every part of some constructible
  stratification of a given open subscheme.

## Implementation notes

The Noetherian induction is stated for a property of *subsets of the ambient space*, not of
subschemes or of sheaves, and it is the shape the source argument uses: in Stacks 09BH the property
of an open `U` is that the restriction `𝒢|_U` is locally constant, and the input to the induction is
that such a `U` exists around the generic point of every irreducible component. Nothing in this file
knows about sheaves, so the same induction serves the three parts of 09BH and the Zariski-local
criterion of 095E.

What this file does **not** do is supply that input. For 09BH the input is the geometric heart of
the source's proof — passing to an étale neighbourhood of a geometric point of the generic point,
where the ambient constructible sheaf becomes constant, and descending sections of the subsheaf
from that neighbourhood. **No `@[stacks 09BH]` attribute appears here**: this is the induction
scheme of the source's proof, not the proof. Parts (1) and (2) of 09BH are proved by a different
route, by presentation of a constructible sheaf of sets by representables, in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Constructible/StrongSerreSets.lean` and
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Constructible/StrongSerreAbelian.lean`, which carry
the tag and do not use this induction.

`ofPartition` asks separately that each part be constructible as a subset of the open subscheme,
rather than deriving it from local closedness, because that is the field
`AlgebraicGeometry.ConstructibleStratification.constructible` asks for and the derivation needs the
space to be Noetherian. The derivation is done once, inside
`exists_constructibleStratification_of_noetherianSpace`, where that hypothesis is present.

## References

* [Stacks Project, Tag 09BH](https://stacks.math.columbia.edu/tag/09BH)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
* [Stacks Project, Tag 0F2L](https://stacks.math.columbia.edu/tag/0F2L)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Topology

universe u

namespace Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed

open AlgebraicGeometry

variable {X : Scheme.{u}} (T : Set X) (hT : IsLocallyClosed T)

/-- The reduced induced scheme on a locally closed subset is immersed in the ambient scheme: its
structure morphism is a closed immersion into the complement of the boundary followed by the open
immersion of that complement. -/
@[ega "I 4.2.1" "special case"]
public instance isImmersion_reducedInducedInclusion :
    IsImmersion (reducedInducedInclusion T hT) :=
  inferInstanceAs (IsImmersion
    ((reducedInducedIdealSheaf T hT).subschemeι ≫ (reducedInducedOpen T hT).ι))

/-- The image of the reduced induced scheme on a locally closed subset is that subset. -/
public theorem range_reducedInducedInclusion :
    Set.range (reducedInducedInclusion T hT).base = T := by
  have hcomp : Set.range (reducedInducedInclusion T hT).base =
      (reducedInducedOpen T hT).ι.base ''
        Set.range (reducedInducedIdealSheaf T hT).subschemeι.base := by
    rw [← Set.range_comp]; rfl
  have hsupp : (reducedInducedIdealSheaf T hT).support = reducedInducedClosed T hT :=
    Closeds.ext_iff.mpr rfl
  have hpre : (reducedInducedClosed T hT : Set (reducedInducedOpen T hT).toScheme) =
      (reducedInducedOpen T hT).ι.base ⁻¹' T := rfl
  rw [hcomp, Scheme.IdealSheafData.range_subschemeι, hsupp, hpre,
    Set.image_preimage_eq_inter_range, (reducedInducedOpen T hT).range_ι]
  exact Set.inter_eq_left.mpr subset_coborder

end Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed

namespace AlgebraicGeometry

open Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed

namespace ConstructibleStratification

/-- A part of a set-level partition, as an object of the big étale site: the reduced induced scheme
on the part. It lies below the cutoff because its structure morphism to `X` is a monomorphism and
the cutoff is closed under powersets. -/
public def partitionPiece (B : BigEtaleSite.{u}) (X : B.Scheme) (T : Set X.obj)
    (hT : IsLocallyClosed T) : B.Scheme :=
  ⟨reducedInducedScheme T hT, Scheme.size_lt_of_mono_of_isStrongPrelimit
    B.cutoff_isStrongPrelimit (reducedInducedInclusion T hT) X.property⟩

/-- The structure morphism of a part of a set-level partition. -/
public def partitionInclusion (B : BigEtaleSite.{u}) (X : B.Scheme) (T : Set X.obj)
    (hT : IsLocallyClosed T) : partitionPiece B X T hT ⟶ X :=
  B.inclusion.preimage (reducedInducedInclusion T hT)

public theorem map_partitionInclusion (B : BigEtaleSite.{u}) (X : B.Scheme) (T : Set X.obj)
    (hT : IsLocallyClosed T) :
    B.inclusion.map (partitionInclusion B X T hT) = reducedInducedInclusion T hT :=
  B.inclusion.map_preimage _

public theorem range_partitionInclusion (B : BigEtaleSite.{u}) (X : B.Scheme) (T : Set X.obj)
    (hT : IsLocallyClosed T) :
    Set.range (B.inclusion.map (partitionInclusion B X T hT)).base = T := by
  rw [map_partitionInclusion]
  exact range_reducedInducedInclusion T hT

/-- **A set-level partition is a constructible stratification.** Given a finite family of locally
closed subsets of `X`, pairwise disjoint, constructible inside the open subscheme `U` and covering
it, the reduced induced schemes on them form a `AlgebraicGeometry.ConstructibleStratification` of
`U`.

This is the step which turns the topological output of a Noetherian induction into the datum a
constructible sheaf is tested against. -/
public def ofPartition (B : BigEtaleSite.{u}) (X : B.Scheme) (U : X.obj.Opens) {n : ℕ}
    (A : Fin n → Set X.obj) (hlc : ∀ i, IsLocallyClosed (A i))
    (hsub : ∀ i, A i ⊆ (U : Set X.obj))
    (hcon : ∀ i, Topology.IsConstructible (U.ι.base ⁻¹' A i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (hcov : (U : Set X.obj) = ⋃ i, A i) :
    ConstructibleStratification B X U where
  n := n
  piece i := partitionPiece B X (A i) (hlc i)
  inclusion i := partitionInclusion B X (A i) (hlc i)
  isImmersion i := by
    rw [map_partitionInclusion]
    exact isImmersion_reducedInducedInclusion (A i) (hlc i)
  contained i := by rw [range_partitionInclusion]; exact hsub i
  constructible i := by rw [range_partitionInclusion]; exact hcon i
  pairwise_disjoint i j hij := by
    rw [range_partitionInclusion, range_partitionInclusion]; exact hdisj i j hij
  covers := by
    refine hcov.trans (Set.iUnion_congr fun i => ?_)
    rw [range_partitionInclusion]

/-- The image of the `i`-th stratum of `AlgebraicGeometry.ConstructibleStratification.ofPartition`
is the `i`-th part of the given partition. -/
public theorem range_inclusion_ofPartition (B : BigEtaleSite.{u}) (X : B.Scheme)
    (U : X.obj.Opens) {n : ℕ} (A : Fin n → Set X.obj) (hlc : ∀ i, IsLocallyClosed (A i))
    (hsub : ∀ i, A i ⊆ (U : Set X.obj))
    (hcon : ∀ i, Topology.IsConstructible (U.ι.base ⁻¹' A i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (hcov : (U : Set X.obj) = ⋃ i, A i) (i : Fin n) :
    Set.range (B.inclusion.map
        ((ofPartition B X U A hlc hsub hcon hdisj hcov).inclusion i)).base = A i :=
  range_partitionInclusion B X (A i) (hlc i)

/-- **The one-stratum stratification of an open subscheme, with reduced stratum.** Its single
stratum is the reduced induced scheme on the whole of `U`, through
`AlgebraicGeometry.ConstructibleStratification.ofPartition`. The stratification whose stratum is
`U` itself, with its own structure sheaf, is
`AlgebraicGeometry.ConstructibleStratification.single`.

This is the stratification every "a finite locally constant sheaf is constructible" argument starts
from, and it is unconditional: an open subset is locally closed, and it is constructible inside
itself because its preimage along its own inclusion is everything. -/
public def singleReduced (B : BigEtaleSite.{u}) (X : B.Scheme) (U : X.obj.Opens) :
    ConstructibleStratification B X U :=
  ofPartition B X U (fun _ : Fin 1 => (U : Set X.obj)) (fun _ => U.2.isLocallyClosed)
    (fun _ => subset_rfl)
    (fun _ => by
      rw [show U.ι.base ⁻¹' (U : Set X.obj) = Set.univ from
        Set.eq_univ_of_forall fun x => x.2]
      exact Topology.IsConstructible.univ)
    (fun i j hij => absurd (Subsingleton.elim i j) hij)
    (Set.iUnion_const _).symm

public theorem singleReduced_n (B : BigEtaleSite.{u}) (X : B.Scheme) (U : X.obj.Opens) :
    (singleReduced B X U).n = 1 := rfl

/-- The single stratum of `AlgebraicGeometry.ConstructibleStratification.singleReduced` has
image `U`. -/
public theorem range_inclusion_singleReduced (B : BigEtaleSite.{u}) (X : B.Scheme)
    (U : X.obj.Opens) (i : Fin 1) :
    Set.range (B.inclusion.map ((singleReduced B X U).inclusion i)).base = (U : Set X.obj) :=
  range_partitionInclusion B X (U : Set X.obj) U.2.isLocallyClosed

end ConstructibleStratification

section Noetherian

variable {α : Type*} [TopologicalSpace α]

/-- The Noetherian induction, carried out on closed subsets. -/
private theorem exists_partition_aux [NoetherianSpace α] (W : Set α) (hW : IsOpen W)
    (P : Set α → Prop)
    (hP : ∀ Z : Set α, IsClosed Z → (W ∩ Z).Nonempty →
      ∃ V : Set α, IsOpen V ∧ (V ∩ W ∩ Z).Nonempty ∧ P (V ∩ W ∩ Z))
    (Z : Closeds α) :
    ∃ (n : ℕ) (A : Fin n → Set α), (∀ i, IsLocallyClosed (A i)) ∧ (∀ i, A i ⊆ W ∩ Z) ∧
      (∀ i, P (A i)) ∧ (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧ W ∩ (Z : Set α) = ⋃ i, A i := by
  classical
  apply wellFounded_lt.induction Z
  clear Z
  intro Z H
  rcases Set.eq_empty_or_nonempty (W ∩ (Z : Set α)) with hempty | hne
  · exact ⟨0, Fin.elim0, by simp, by simp, by simp, by simp, by simpa using hempty⟩
  obtain ⟨V, hV, hVne, hVP⟩ := hP Z Z.isClosed hne
  -- the closed set `Z \ V` is strictly smaller than `Z`
  let Z' : Closeds α := ⟨(Z : Set α) \ V, Z.isClosed.sdiff hV⟩
  have hZ'lt : Z' < Z := by
    refine lt_of_le_of_ne (fun x hx => hx.1) fun hcontra => ?_
    obtain ⟨x, ⟨hxV, _⟩, hxZ⟩ := hVne
    have : x ∈ (Z' : Set α) := by rw [hcontra]; exact hxZ
    exact this.2 hxV
  obtain ⟨m, A', hlc', hsub', hP', hdisj', hcov'⟩ := H Z' hZ'lt
  refine ⟨m + 1, Fin.cons (V ∩ W ∩ Z) A', ?_, ?_, ?_, ?_, ?_⟩
  · refine Fin.cases ?_ ?_
    · simpa only [Fin.cons_zero] using
        ((hV.inter hW).isLocallyClosed).inter Z.isClosed.isLocallyClosed
    · intro i; simpa only [Fin.cons_succ] using hlc' i
  · refine Fin.cases ?_ ?_
    · simp only [Fin.cons_zero]
      exact fun x hx => ⟨hx.1.2, hx.2⟩
    · intro i
      simp only [Fin.cons_succ]
      exact fun x hx => ⟨(hsub' i hx).1, (hsub' i hx).2.1⟩
  · refine Fin.cases ?_ ?_
    · simpa only [Fin.cons_zero] using hVP
    · intro i; simpa only [Fin.cons_succ] using hP' i
  · have hdisj₀ : ∀ i : Fin m, Disjoint (V ∩ W ∩ (Z : Set α)) (A' i) := by
      intro i
      refine Set.disjoint_left.mpr fun x hx hx' => ?_
      exact ((hsub' i hx').2).2 hx.1.1
    intro i j
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact fun h => absurd rfl h
      | succ j =>
        exact fun _ => by simpa only [Fin.cons_zero, Fin.cons_succ] using hdisj₀ j
    | succ i =>
      induction j using Fin.cases with
      | zero =>
        exact fun _ => by simpa only [Fin.cons_zero, Fin.cons_succ] using (hdisj₀ i).symm
      | succ j =>
        refine fun hij => ?_
        simp only [Fin.cons_succ]
        exact hdisj' i j fun h => hij (by rw [h])
  · have hunion : ⋃ i : Fin (m + 1),
        (Fin.cons (V ∩ W ∩ (Z : Set α)) A' : Fin (m + 1) → Set α) i =
        (V ∩ W ∩ (Z : Set α)) ∪ ⋃ i : Fin m, A' i := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_union]
      refine ⟨fun ⟨i, hi⟩ => ?_, fun h => ?_⟩
      · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
        · exact Or.inl (by simpa only [Fin.cons_zero] using hi)
        · exact Or.inr ⟨j, by simpa only [Fin.cons_succ] using hi⟩
      · rcases h with h | ⟨j, hj⟩
        · exact ⟨0, by simpa only [Fin.cons_zero] using h⟩
        · exact ⟨j.succ, by simpa only [Fin.cons_succ] using hj⟩
    rw [hunion, ← hcov']
    refine Set.Subset.antisymm (fun x hx => ?_) (Set.union_subset (fun x hx => ?_) fun x hx => ?_)
    · by_cases hxV : x ∈ V
      · exact Or.inl ⟨⟨hxV, hx.1⟩, hx.2⟩
      · exact Or.inr ⟨hx.1, hx.2, hxV⟩
    · exact ⟨hx.1.2, hx.2⟩
    · exact ⟨hx.1, hx.2.1⟩

/-- **The Noetherian induction of Stacks 09BH, as a statement about spaces.** Let `P` be a property
of subsets of a Noetherian space. Suppose that for every closed set `Z` meeting the open set `W`
there is an open `V` such that `V ∩ W ∩ Z` is nonempty and satisfies `P`. Then `W` is a finite
disjoint union of locally closed sets each satisfying `P`.

In Stacks 09BH the property of a subset is that the restriction of the given subsheaf to it is
locally constant, and the hypothesis is supplied by working at the generic points of the irreducible
components of `Z`. -/
public theorem exists_locallyClosed_partition_of_noetherianSpace [NoetherianSpace α] (W : Set α)
    (hW : IsOpen W) (P : Set α → Prop)
    (hP : ∀ Z : Set α, IsClosed Z → (W ∩ Z).Nonempty →
      ∃ V : Set α, IsOpen V ∧ (V ∩ W ∩ Z).Nonempty ∧ P (V ∩ W ∩ Z)) :
    ∃ (n : ℕ) (A : Fin n → Set α), (∀ i, IsLocallyClosed (A i)) ∧ (∀ i, A i ⊆ W) ∧
      (∀ i, P (A i)) ∧ (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧ W = ⋃ i, A i := by
  obtain ⟨n, A, hlc, hsub, hP', hdisj, hcov⟩ := exists_partition_aux W hW P hP ⊤
  exact ⟨n, A, hlc, fun i x hx => (hsub i hx).1, hP', hdisj, by
    simpa only [Closeds.coe_top, Set.inter_univ] using hcov⟩

/-- In a Noetherian space every locally closed subset is constructible: the open part is compact,
hence retrocompact, and the closed part is the complement of such an open. -/
@[ega "0 9.1.5" "special case",
  ega "0 9.1.7" "sufficiency",
  ega "0 9.2.1" "partial",
  ega "IV 1.8.1" "special case",
  ega "IV 1.9.5" "(v), special case",
  ega "IV 10.1.1" "special case"]
public theorem isConstructible_of_isLocallyClosed [NoetherianSpace α] {s : Set α}
    (hs : IsLocallyClosed s) : Topology.IsConstructible s := by
  obtain ⟨V, Z, hV, hZ, rfl⟩ := hs
  exact ((NoetherianSpace.isCompact V).isConstructible hV).inter
    (((NoetherianSpace.isCompact Zᶜ).isConstructible hZ.isOpen_compl).of_compl)

end Noetherian

/-- **A constructible stratification by Noetherian induction.** On a scheme with Noetherian
underlying space, a property of subsets which can always be achieved on a nonempty relatively open
part of a closed set is achieved on every stratum of some constructible stratification of a given
open subscheme.

This is the two halves of the Noetherian induction step of Stacks 09BH put together: the
set-theoretic induction `AlgebraicGeometry.exists_locallyClosed_partition_of_noetherianSpace`, and
the realisation of a locally closed part as an object of the big étale site immersed in `X`,
`AlgebraicGeometry.ConstructibleStratification.ofPartition`. The hypothesis `hP` is what a proof of
09BH has to supply, and what this library does not have. -/
public theorem exists_constructibleStratification_of_noetherianSpace (B : BigEtaleSite.{u})
    (X : B.Scheme) [NoetherianSpace X.obj] (U : X.obj.Opens) (P : Set X.obj → Prop)
    (hP : ∀ Z : Set X.obj, IsClosed Z → ((U : Set X.obj) ∩ Z).Nonempty →
      ∃ V : Set X.obj, IsOpen V ∧ (V ∩ (U : Set X.obj) ∩ Z).Nonempty ∧
        P (V ∩ (U : Set X.obj) ∩ Z)) :
    ∃ s : ConstructibleStratification B X U,
      ∀ i, P (Set.range (B.inclusion.map (s.inclusion i)).base) := by
  obtain ⟨n, A, hlc, hsub, hPA, hdisj, hcov⟩ :=
    exists_locallyClosed_partition_of_noetherianSpace (U : Set X.obj) U.2 P hP
  have hUnoeth : NoetherianSpace U.toScheme :=
    U.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  have hcon : ∀ i, Topology.IsConstructible (U.ι.base ⁻¹' A i) := fun i =>
    isConstructible_of_isLocallyClosed ((hlc i).preimage U.ι.base.hom.continuous)
  refine ⟨ConstructibleStratification.ofPartition B X U A hlc hsub hcon hdisj hcov, fun i => ?_⟩
  have hrange := ConstructibleStratification.range_inclusion_ofPartition B X U A hlc hsub hcon
    hdisj hcov i
  rw [hrange]
  exact hPA i

end AlgebraicGeometry

end
