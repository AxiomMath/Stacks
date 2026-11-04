module

public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Extensive
public import Mathlib.Topology.Constructible
public import Mathlib.Topology.Sober
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AffineStratification.FiniteExistence
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Stability
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Approximation
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.FiniteCover
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Misc.FiniteCoproduct
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.GenericallyFinite
public import StacksFrontier.AlgebraicGeometry.Scheme.Reduction
public import StacksFrontier.AlgebraicGeometry.Scheme.ReductionMap
public import StacksFrontier.AlgebraicGeometry.Schemes.ZariskiAndSeparation.ReducedInducedLocallyClosed
public import StacksFrontier.Topology.Stratification.RefineConstructible
public import StacksFrontier.AlgebraicGeometry.AffineClosedUnion.Reduction

/-!
# Decomposition of a quasi-finite morphism after base change

A quasi-finite, finitely presented morphism of affine schemes admits a surjective affine base
change under which a thickening of the pullback is finite étale. More precisely, the base admits
a finite partition into constructible locally closed affine strata, and finite locally free
covers of the strata split the reduced pullback into finitely many copies of the reduced cover.

The two statements are proved in the opposite order to the one in which they are stated above:
taking the coproduct of the covers of the strata turns the partition of the second into the
single affine base change of the first.

## Main results

* `AlgebraicGeometry.exists_surjective_affine_baseChange_thickening_finiteEtale`: a surjective
  affine base change after which the pullback contains a finite étale thickening.
* `AlgebraicGeometry.exists_finite_affine_stratification_split_reduction`: a finite partition of
  the base into constructible locally closed affine strata, with finite locally free covers
  splitting the reduced pullback.

## Implementation notes

The partition is indexed by `Fin n`; its strata are affine schemes immersed in the base, with
pairwise disjoint locally closed constructible images covering the underlying space. The
splitting is an isomorphism of reduced schemes over the reduced cover; the displayed equality
pins down the induced morphism on reductions.

The reduction of a scheme enters through Mathlib's nilradical ideal sheaf and its closed
subscheme, so that the statements speak of `X.nilradical.subscheme` rather than of a wrapper;
`AlgebraicGeometry.Scheme.reduction` is that subscheme and supplies its reducedness,
surjectivity and thickening facts.

## References

* [Stacks Project, Tag 095K](https://stacks.math.columbia.edu/tag/095K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed

universe u

namespace AlgebraicGeometry

private instance isZariskiLocalAtTarget_isFinite : IsZariskiLocalAtTarget
    (@IsFinite : MorphismProperty Scheme.{u}) :=
  Stacks.Morphisms.isFinite_isZariskiLocalAtTarget

private instance : MorphismProperty.RespectsIso
    (@IsFinite : MorphismProperty Scheme.{u}) :=
  isZariskiLocalAtTarget_isFinite.toRespects

private instance {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@Surjective) f :=
  ⟨fun pb hf => (show MorphismProperty.IsStableUnderBaseChange (@Surjective) from
    inferInstance).of_isPullback pb hf⟩

private instance {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@Stacks.Thickenings.IsThickening) f :=
  ⟨fun pb hf => Stacks.Thickenings.isThickening_isStableUnderBaseChange.of_isPullback pb hf⟩

private instance {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@Stacks.Morphisms.IsFiniteLocallyFree) f :=
  ⟨fun pb hf => Stacks.Morphisms.isFiniteLocallyFree_isStableUnderBaseChange.of_isPullback pb hf⟩

private instance : IsZariskiLocalAtTarget
    (@Etale : MorphismProperty Scheme.{u}) :=
  HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := RingHom.Etale)

private instance : IsZariskiLocalAtSource
    (@Etale : MorphismProperty Scheme.{u}) :=
  HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)

private instance : IsZariskiLocalAtSource
    (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) :=
  HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FiniteType)

private instance : IsZariskiLocalAtSource
    (@LocallyQuasiFinite : MorphismProperty Scheme.{u}) :=
  HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.QuasiFinite)

private theorem finiteStratification_stratum_isLocallyClosed
    {X : Type*} [TopologicalSpace X] (𝒮 : FiniteStratification X)
    (j : 𝒮.ι) : IsLocallyClosed (𝒮.S j) := by
  classical
  let lower : Set X := ⋃ i : {i : 𝒮.ι // i < j}, 𝒮.S i.1
  have hlower_closed : IsClosed lower := by
    apply closure_subset_iff_isClosed.mp
    intro x hx
    change x ∈ closure (⋃ i : {i : 𝒮.ι // i < j}, 𝒮.S i.1) at hx
    rw [closure_iUnion_of_finite] at hx
    obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
    have hx' := 𝒮.closure_subset i.1 hx
    obtain ⟨k, hx'⟩ := Set.mem_iUnion.mp hx'
    obtain ⟨hki, hx'⟩ := Set.mem_iUnion.mp hx'
    exact Set.mem_iUnion.mpr ⟨⟨k, lt_of_le_of_lt hki i.2⟩, hx'⟩
  have hEq : 𝒮.S j = closure (𝒮.S j) \ lower := by
    ext x
    constructor
    · intro hx
      refine ⟨subset_closure hx, ?_⟩
      intro hxlower
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxlower
      exact (Set.disjoint_left.mp (𝒮.disjoint (ne_of_lt i.2))) hxi hx
    · intro hx
      have hx' := 𝒮.closure_subset j hx.1
      obtain ⟨i, hx'⟩ := Set.mem_iUnion.mp hx'
      obtain ⟨hij, hxi⟩ := Set.mem_iUnion.mp hx'
      by_cases hEq : i = j
      · simpa [hEq] using hxi
      · have hji : ¬ j ≤ i := by
          intro hji
          exact hEq (le_antisymm hij hji)
        exact False.elim (hx.2 (Set.mem_iUnion.mpr
          ⟨⟨i, lt_iff_le_not_ge.mpr ⟨hij, hji⟩⟩, hxi⟩))
  refine ⟨lowerᶜ, closure (𝒮.S j), hlower_closed.isOpen_compl, isClosed_closure, ?_⟩
  simpa only [Set.sdiff_eq_compl_inter] using hEq

private theorem finiteStratification_strata_locallyClosed_constructible
    {X : Type*} [TopologicalSpace X] {n : ℕ} (T : Fin n → Set X)
    (hT : ∀ k, Topology.IsConstructible (T k))
    (hcover : ⋃ k, T k = Set.univ) :
    ∃ (m : ℕ) (S : Fin m → Set X),
      (∀ i, IsLocallyClosed (S i) ∧ Topology.IsConstructible (S i)) ∧
      Pairwise (Function.onFun Disjoint S) ∧ (⋃ i, S i) = Set.univ ∧
      ∀ k, ∃ J : Set (Fin m), T k = ⋃ i ∈ J, S i := by
  obtain ⟨𝒮, hconstructible, hTrefines⟩ :=
    exists_finiteStratification_refining_constructible T hT hcover
  let e : 𝒮.ι ≃ Fin (Fintype.card 𝒮.ι) := Fintype.equivFin 𝒮.ι
  refine ⟨Fintype.card 𝒮.ι, fun i => 𝒮.S (e.symm i), ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨finiteStratification_stratum_isLocallyClosed 𝒮 (e.symm i), hconstructible _⟩
  · exact 𝒮.disjoint.comp_of_injective e.symm.injective
  · rw [e.symm.surjective.iUnion_comp]
    exact 𝒮.iUnion_eq_univ
  · intro k
    obtain ⟨J, hJ⟩ := hTrefines k
    refine ⟨e '' J, ?_⟩
    rw [hJ, Set.biUnion_image]
    simp

/-- A finite constructible family can be refined even when it is not a cover: adjoining the
whole space as an extra member lets the constructible-partition theorem apply.  In applications
the family consists of the loci where a section lies in a closed subscheme and where two sections
agree. -/
private theorem finiteConstructibleFamily_refined
    {X : Type*} [TopologicalSpace X] {n : ℕ} (T : Fin n → Set X)
    (hT : ∀ k, Topology.IsConstructible (T k)) :
    ∃ (m : ℕ) (S : Fin m → Set X),
      (∀ i, IsLocallyClosed (S i) ∧ Topology.IsConstructible (S i)) ∧
      Pairwise (Function.onFun Disjoint S) ∧ (⋃ i, S i) = Set.univ ∧
      ∀ k, ∃ J : Set (Fin m), T k = ⋃ i ∈ J, S i := by
  let T' : Fin (n + 1) → Set X := Fin.cases Set.univ T
  have hT' : ∀ k, Topology.IsConstructible (T' k) := by
    intro k
    cases k using Fin.cases with
    | zero => simp [T']
    | succ i => simpa [T'] using hT i
  have hcover : (⋃ k, T' k) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨0, by simp [T']⟩
  obtain ⟨m, S, hS, hdisj, hcoverS, hrefines⟩ :=
    finiteStratification_strata_locallyClosed_constructible T' hT' hcover
  refine ⟨m, S, hS, hdisj, hcoverS, ?_⟩
  intro k
  exact hrefines k.succ

/-- Refine a finite family of membership and equality loci together.  This is the set-level
bridge used for a finite family of sections: on each resulting stratum, both whether a section
lies in a chosen closed subscheme and whether two sections coincide are constant. -/
private theorem finiteSectionLoci_refined
    {X : Type*} [TopologicalSpace X] {n : ℕ}
    (member : Fin n → Set X) (agree : Fin n → Fin n → Set X)
    (hmember : ∀ i, Topology.IsConstructible (member i))
    (hagree : ∀ i j, Topology.IsConstructible (agree i j)) :
    ∃ (m : ℕ) (S : Fin m → Set X),
      (∀ i, IsLocallyClosed (S i) ∧ Topology.IsConstructible (S i)) ∧
      Pairwise (Function.onFun Disjoint S) ∧ (⋃ i, S i) = Set.univ ∧
      (∀ i, ∃ J : Set (Fin m), member i = ⋃ j ∈ J, S j) ∧
      ∀ i j, ∃ J : Set (Fin m), agree i j = ⋃ k ∈ J, S k := by
  let ι := Fin n ⊕ (Fin n × Fin n)
  let U : ι → Set X := Sum.elim member (fun ij => agree ij.1 ij.2)
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have hU : ∀ i, Topology.IsConstructible (U (e.symm i)) := by
    intro i
    cases e.symm i with
    | inl j => exact hmember j
    | inr ij => exact hagree ij.1 ij.2
  obtain ⟨m, S, hS, hdisj, hcover, hrefines⟩ :=
    finiteConstructibleFamily_refined (fun i => U (e.symm i)) hU
  refine ⟨m, S, hS, hdisj, hcover, ?_, ?_⟩
  · intro i
    simpa [U] using hrefines (e (Sum.inl i))
  · intro i j
    simpa [U] using hrefines (e (Sum.inr (i, j)))

private lemma constant_on_disjoint_partition
    {X I : Type*} [TopologicalSpace X] (S : I → Set X)
    (hdisjoint : Pairwise (Function.onFun Disjoint S)) (J : Set I) (i : I)
    {x y : X} (hx : x ∈ S i) (hy : y ∈ S i) :
    (x ∈ ⋃ j ∈ J, S j ↔ y ∈ ⋃ j ∈ J, S j) := by
  have mem_iff (z : X) (hz : z ∈ S i) : z ∈ ⋃ j ∈ J, S j ↔ i ∈ J := by
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨j, hj, hzj⟩
      rcases eq_or_ne j i with rfl | hne
      · exact hj
      · exact False.elim ((Set.disjoint_left.mp (hdisjoint hne)) hzj hz)
    · intro hi
      exact ⟨i, hi, hz⟩
  exact (mem_iff x hx).trans (mem_iff y hy).symm

/-- The refinement supplied by `finiteSectionLoci_refined` makes all section predicates
constant on each stratum. This is the pointwise form needed when turning the set-level
partition into a decomposition of the reduced finite scheme. -/
private theorem finiteSectionLoci_refined_constancy
    {X : Type*} [TopologicalSpace X] {n : ℕ}
    (member : Fin n → Set X) (agree : Fin n → Fin n → Set X)
    (hmember : ∀ i, Topology.IsConstructible (member i))
    (hagree : ∀ i j, Topology.IsConstructible (agree i j)) :
    ∃ (m : ℕ) (S : Fin m → Set X),
      (∀ i, IsLocallyClosed (S i) ∧ Topology.IsConstructible (S i)) ∧
      Pairwise (Function.onFun Disjoint S) ∧ (⋃ i, S i) = Set.univ ∧
      (∀ k i x y, x ∈ S i → y ∈ S i →
        (x ∈ member k ↔ y ∈ member k)) ∧
      ∀ k l i x y, x ∈ S i → y ∈ S i →
        (x ∈ agree k l ↔ y ∈ agree k l) := by
  obtain ⟨m, S, hS, hdisjoint, hcover, hmemberRefined, hagreeRefined⟩ :=
    finiteSectionLoci_refined member agree hmember hagree
  refine ⟨m, S, hS, hdisjoint, hcover, ?_, ?_⟩
  · intro k i x y hxi hyi
    obtain ⟨J, hJ⟩ := hmemberRefined k
    rw [hJ]
    exact constant_on_disjoint_partition S hdisjoint J i hxi hyi
  · intro k l i x y hxi hyi
    obtain ⟨J, hJ⟩ := hagreeRefined k l
    rw [hJ]
    exact constant_on_disjoint_partition S hdisjoint J i hxi hyi

/-- A predicate which is constant between points of a stratum either holds everywhere on the
stratum or nowhere on it. The latter alternative includes empty strata. -/
private theorem subset_or_disjoint_of_constant
    {X : Type*} {S T : Set X}
    (hconstant : ∀ x y, x ∈ S → y ∈ S → (x ∈ T ↔ y ∈ T)) :
    S ⊆ T ∨ Disjoint S T := by
  by_cases h : ∃ x, x ∈ S ∧ x ∈ T
  · obtain ⟨y, hy, hyt⟩ := h
    exact Or.inl fun x hx => (hconstant y x hy hx).mp hyt
  · exact Or.inr (Set.disjoint_left.mpr fun x hx hxt => h ⟨x, hx, hxt⟩)

/-- If `a ≫ b` is a closed immersion and `b` is separated, then `a` is a closed immersion. -/
private lemma isClosedImmersion_of_comp_eq {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    {c : X ⟶ Z} [IsClosedImmersion c] [IsSeparated b] (h : a ≫ b = c) :
    IsClosedImmersion a := by
  have : IsClosedImmersion (a ≫ b) := by rw [h]; infer_instance
  exact IsClosedImmersion.of_comp a b

private lemma exists_thickening_onto_open_range {Y X : Scheme.{u}}
    (f : Y ⟶ X) [IsClosedImmersion f] (hf : IsOpen (Set.range f)) :
    ∃ h : Y ⟶ Scheme.Opens.toScheme (X := X) ⟨Set.range f, hf⟩,
      Stacks.Thickenings.IsThickening h ∧ h ≫ Scheme.Opens.ι (X := X) ⟨Set.range f, hf⟩ = f := by
  let U : X.Opens := ⟨Set.range f, hf⟩
  let h := IsOpenImmersion.lift U.ι f (by simp [U])
  have hh : h ≫ U.ι = f := IsOpenImmersion.lift_fac _ _ _
  have : IsClosedImmersion h := isClosedImmersion_of_comp_eq h U.ι hh
  refine ⟨h, ⟨inferInstance, ?_⟩, hh⟩
  intro x
  obtain ⟨y, hy⟩ := x.2
  refine ⟨y, U.ι.isOpenEmbedding.injective ?_⟩
  show (h ≫ U.ι) y = x.1
  rw [hh]
  exact hy

private lemma isOpenImmersion_of_isClosedImmersion_of_isOpen_range
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] [IsReduced Y]
    (ho : IsOpen (Set.range f.base)) : IsOpenImmersion f := by
  obtain ⟨a, ⟨_, ha'⟩, ha⟩ := exists_thickening_onto_open_range f ho
  have : Surjective a := ⟨ha'⟩
  have : IsIso a := isIso_of_isClosedImmersion_of_surjective a
  rw [← ha]
  infer_instance

private lemma isClopen_of_finite_closed_partition {A : Type*} [TopologicalSpace A]
    {J : Type*} [Finite J] (S : J → Set A) (hclosed : ∀ j, IsClosed (S j))
    (hdisj : Pairwise fun j k => Disjoint (S j) (S k))
    (hcover : (⋃ j, S j) = Set.univ) (j : J) : IsClopen (S j) := by
  classical
  refine ⟨hclosed j, ?_⟩
  rw [← isClosed_compl_iff]
  have hc : (S j)ᶜ = ⋃ k : {k : J // k ≠ j}, S k.1 := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := Set.iUnion_eq_univ_iff.mp hcover x
      exact Set.mem_iUnion.mpr ⟨⟨k, fun h => hx (h ▸ hk)⟩, hk⟩
    · intro hx hj
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
      exact Set.disjoint_left.mp (hdisj k.2) hk hj
  rw [hc]
  exact isClosed_iUnion_of_finite (fun k => hclosed k.1)

private lemma exists_iso_coproduct_of_disjoint_closed_sections
    {X Y : Scheme.{u}} [IsReduced Y] (f : Y ⟶ X) {n : ℕ}
    (s : Fin n → (X ⟶ Y)) [∀ i, IsClosedImmersion (s i)]
    (hs : ∀ i, s i ≫ f = 𝟙 X)
    (hdisj : Pairwise (fun i j => Disjoint (Set.range (s i).base) (Set.range (s j).base)))
    (hcover : (⋃ i, Set.range (s i).base) = Set.univ) :
    ∃ e : Y ≅ ∐ fun _ : Fin n => X,
      e.hom ≫ Sigma.desc (fun _ : Fin n => 𝟙 X) = f := by
  have hopen (i) : IsOpen (Set.range (s i).base) :=
    (isClopen_of_finite_closed_partition _ (fun j => (s j).isClosedEmbedding.isClosed_range)
      hdisj hcover i).isOpen
  have : ∀ i, IsOpenImmersion (s i) := fun i =>
    isOpenImmersion_of_isClosedImmersion_of_isOpen_range (s i) (hopen i)
  have : IsOpenImmersion (Sigma.desc s) := isOpenImmersion_sigmaDesc _ s hdisj
  have : Surjective (Sigma.desc s) := Surjective.sigmaDesc_of_union_range_eq_univ hcover
  have : Epi (Sigma.desc s).base := (TopCat.epi_iff_surjective _).mpr
    (show Surjective (Sigma.desc s) from inferInstance).surj
  have : IsIso (Sigma.desc s) := IsOpenImmersion.isIso _
  refine ⟨(asIso (Sigma.desc s)).symm, ?_⟩
  apply (cancel_epi (Sigma.desc s)).mp
  simp only [Iso.symm_hom, asIso_inv, IsIso.hom_inv_id_assoc]
  apply Sigma.hom_ext
  intro i
  simp only [Sigma.ι_desc, Sigma.ι_desc_assoc, hs]

private lemma exists_iso_coproduct_of_closed_sections_eq_or_disjoint
    {X Y : Scheme.{u}} [IsReduced Y] (f : Y ⟶ X) {n : ℕ}
    (s : Fin n → (X ⟶ Y)) [∀ i, IsClosedImmersion (s i)]
    (hs : ∀ i, s i ≫ f = 𝟙 X)
    (hdisj : ∀ i j, s i = s j ∨
      Disjoint (Set.range (s i).base) (Set.range (s j).base))
    (hcover : (⋃ i, Set.range (s i).base) = Set.univ) :
    ∃ (m : ℕ) (e : Y ≅ ∐ fun _ : Fin m => X),
      e.hom ≫ Sigma.desc (fun _ : Fin m => 𝟙 X) = f := by
  classical
  let E := Set.range s
  let : Fintype E := (Set.finite_range s).fintype
  let a : E ≃ Fin (Fintype.card E) := Fintype.equivFin E
  let t : Fin (Fintype.card E) → (X ⟶ Y) := fun i => (a.symm i).1
  have ht (i) : ∃ j, s j = t i := (a.symm i).2
  have : ∀ i, IsClosedImmersion (t i) := by
    intro i
    obtain ⟨j, hj⟩ := ht i
    rw [← hj]
    infer_instance
  have hts (i) : t i ≫ f = 𝟙 X := by
    obtain ⟨j, hj⟩ := ht i
    rw [← hj]
    exact hs j
  have htd : Pairwise (fun i j => Disjoint (Set.range (t i).base)
      (Set.range (t j).base)) := by
    intro i j hij
    obtain ⟨i', hi'⟩ := ht i
    obtain ⟨j', hj'⟩ := ht j
    rcases hdisj i' j' with heq | hd
    · have heq' : t i = t j := hi'.symm.trans (heq.trans hj')
      exact (hij (a.symm.injective (Subtype.ext heq'))).elim
    · simpa only [hi', hj'] using hd
  have htc : (⋃ i, Set.range (t i).base) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨i, x, hx⟩ := Set.iUnion_eq_univ_iff.mp hcover y
    refine Set.mem_iUnion.mpr ⟨a ⟨s i, ⟨i, rfl⟩⟩, x, ?_⟩
    simpa only [t, Equiv.symm_apply_apply] using hx
  obtain ⟨e, he⟩ := exists_iso_coproduct_of_disjoint_closed_sections f t hts htd htc
  exact ⟨Fintype.card E, e, he⟩

private lemma surjective_pullback_snd_of_range_subset
    {X Y S : Scheme.{u}} (f : Y ⟶ X) (s : S ⟶ X)
    (hs : Set.range s ⊆ Set.range f) : Surjective (pullback.snd f s) := by
  constructor
  intro x
  obtain ⟨y, hy⟩ := hs ⟨x, rfl⟩
  obtain ⟨z, _, hz⟩ := Scheme.Pullback.exists_preimage_pullback y x hy
  exact ⟨z, hz⟩

private lemma exists_lift_of_range_subset_of_isReduced
    {T Y Z : Scheme.{u}} [IsReduced T] (i : Y ⟶ Z) [IsClosedImmersion i]
    (f : T ⟶ Z) (hf : Set.range f ⊆ Set.range i) :
    ∃ g : T ⟶ Y, g ≫ i = f := by
  have : Surjective (pullback.snd i f) := surjective_pullback_snd_of_range_subset i f hf
  have : IsIso (pullback.snd i f) := isIso_of_isClosedImmersion_of_surjective _
  refine ⟨inv (pullback.snd i f) ≫ pullback.fst i f, ?_⟩
  rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]

private lemma sections_eq_of_range_subset_of_isReduced
    {X Z : Scheme.{u}} [IsReduced X] (p : Z ⟶ X)
    (s t : X ⟶ Z) [IsClosedImmersion t]
    (hs : s ≫ p = 𝟙 X) (ht : t ≫ p = 𝟙 X)
    (h : Set.range s ⊆ Set.range t) : s = t := by
  obtain ⟨a, ha⟩ := exists_lift_of_range_subset_of_isReduced t s h
  have : a = 𝟙 X := by
    calc
      a = a ≫ (t ≫ p) := by rw [ht, Category.comp_id]
      _ = 𝟙 X := by rw [← Category.assoc, ha, hs]
  simpa only [this, Category.id_comp] using ha.symm

private lemma exists_iso_coproduct_of_selected_closed_sections
    {X Y Z : Scheme.{u}} [IsReduced X] [IsReduced Y]
    (i : Y ⟶ Z) [IsClosedImmersion i] (p : Z ⟶ X) {n : ℕ}
    (s : Fin n → (X ⟶ Z)) [∀ j, IsClosedImmersion (s j)]
    (hs : ∀ j, s j ≫ p = 𝟙 X)
    (hmember : ∀ j, Set.range (s j) ⊆ Set.range i ∨
      Disjoint (Set.range (s j)) (Set.range i))
    (hdisj : ∀ j k, Set.range (s j) = Set.range (s k) ∨
      Disjoint (Set.range (s j)) (Set.range (s k)))
    (hcover : (⋃ j, Set.range (s j)) = Set.univ) :
    ∃ (m : ℕ) (e : Y ≅ ∐ fun _ : Fin m => X),
      e.hom ≫ Sigma.desc (fun _ : Fin m => 𝟙 X) = i ≫ p := by
  classical
  let J := {j : Fin n // Set.range (s j) ⊆ Set.range i}
  have hlift (j : J) : ∃ t : X ⟶ Y, t ≫ i = s j.1 :=
    exists_lift_of_range_subset_of_isReduced i (s j.1) j.2
  choose t ht using hlift
  have htclosed (j : J) : IsClosedImmersion (t j) := isClosedImmersion_of_comp_eq (t j) i (ht j)
  let a : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let t' (j : Fin (Fintype.card J)) := t (a.symm j)
  have : ∀ j, IsClosedImmersion (t' j) := fun j => htclosed _
  apply exists_iso_coproduct_of_closed_sections_eq_or_disjoint (i ≫ p) t'
  · intro j
    dsimp [t']
    rw [← Category.assoc, ht, hs]
  · intro j k
    rcases hdisj (a.symm j).1 (a.symm k).1 with h | h
    · left
      apply (cancel_mono i).mp
      dsimp [t']
      rw [ht, ht]
      exact sections_eq_of_range_subset_of_isReduced p _ _ (hs _) (hs _) h.subset
    · right
      have hmem (j : J) (x : X) : i (t j x) ∈ Set.range (s j.1) := ⟨x, by rw [← ht]; rfl⟩
      apply Set.disjoint_left.mpr
      rintro y ⟨x, rfl⟩ ⟨z, hz⟩
      exact Set.disjoint_left.mp h (hmem _ x) (hz ▸ hmem _ z)
  · apply Set.eq_univ_of_forall
    intro y
    obtain ⟨j, x, hx⟩ := Set.iUnion_eq_univ_iff.mp hcover (i y)
    have hj : Set.range (s j) ⊆ Set.range i := by
      rcases hmember j with h | h
      · exact h
      · exact (Set.disjoint_left.mp h ⟨x, hx⟩ ⟨y, rfl⟩).elim
    refine Set.mem_iUnion.mpr ⟨a ⟨j, hj⟩, x, ?_⟩
    apply i.isClosedEmbedding.injective
    show (t (a.symm (a ⟨j, hj⟩)) ≫ i) x = i y
    rw [Equiv.symm_apply_apply, ht]
    exact hx

private def sectionBaseChange {X Z T : Scheme.{u}} (p : Z ⟶ X)
    (s : X ⟶ Z) (hs : s ≫ p = 𝟙 X) (h : T ⟶ X) : T ⟶ pullback p h :=
  pullback.lift (h ≫ s) (𝟙 T) (by simp [Category.assoc, hs])

private lemma sectionBaseChange_fst {X Z T : Scheme.{u}} (p : Z ⟶ X)
    (s : X ⟶ Z) (hs : s ≫ p = 𝟙 X) (h : T ⟶ X) :
    sectionBaseChange p s hs h ≫ pullback.fst p h = h ≫ s :=
  pullback.lift_fst _ _ _

private lemma sectionBaseChange_snd {X Z T : Scheme.{u}} (p : Z ⟶ X)
    (s : X ⟶ Z) (hs : s ≫ p = 𝟙 X) (h : T ⟶ X) :
    sectionBaseChange p s hs h ≫ pullback.snd p h = 𝟙 T :=
  pullback.lift_snd _ _ _

private lemma isPullback_sectionBaseChange {X Z T : Scheme.{u}} (p : Z ⟶ X)
    (s : X ⟶ Z) (hs : s ≫ p = 𝟙 X) (h : T ⟶ X) :
    IsPullback (sectionBaseChange p s hs h) h (pullback.fst p h) s := by
  apply IsPullback.of_right (h₁₂ := pullback.snd p h) (h₂₂ := p)
  · rw [sectionBaseChange_snd, hs]
    exact IsPullback.of_id_fst
  · exact sectionBaseChange_fst p s hs h
  · exact (IsPullback.of_hasPullback p h).flip

private lemma isClosedImmersion_sectionBaseChange {X Z T : Scheme.{u}} (p : Z ⟶ X)
    (s : X ⟶ Z) [IsClosedImmersion s] (hs : s ≫ p = 𝟙 X) (h : T ⟶ X) :
    IsClosedImmersion (sectionBaseChange p s hs h) :=
  MorphismProperty.of_isPullback (isPullback_sectionBaseChange p s hs h).flip
    (show IsClosedImmersion s from inferInstance)

private lemma range_sectionBaseChange {X Z T : Scheme.{u}} (p : Z ⟶ X)
    (s : X ⟶ Z) (hs : s ≫ p = 𝟙 X) (h : T ⟶ X) :
    Set.range (sectionBaseChange p s hs h) = (pullback.fst p h) ⁻¹' Set.range s := by
  simpa using Scheme.image_preimage_eq_of_isPullback
    (isPullback_sectionBaseChange p s hs h).flip Set.univ

private lemma exists_iso_coproduct_of_baseChange_sections
    {X Y Z T : Scheme.{u}} [IsReduced T] [IsReduced Y]
    (p : Z ⟶ X) (h : T ⟶ X)
    (i : Y ⟶ pullback p h) [IsClosedImmersion i] {n : ℕ}
    (s : Fin n → (X ⟶ Z)) [∀ j, IsClosedImmersion (s j)]
    (hs : ∀ j, s j ≫ p = 𝟙 X)
    (hmember : ∀ j, Set.range (sectionBaseChange p (s j) (hs j) h) ⊆ Set.range i ∨
      Disjoint (Set.range (sectionBaseChange p (s j) (hs j) h)) (Set.range i))
    (hagree : ∀ j k, (∀ t, s j (h t) = s k (h t)) ∨
      (∀ t, s j (h t) ≠ s k (h t)))
    (hcover : (⋃ j, Set.range (s j)) = Set.univ) :
    ∃ (m : ℕ) (e : Y ≅ ∐ fun _ : Fin m => T),
      e.hom ≫ Sigma.desc (fun _ : Fin m => 𝟙 T) = i ≫ pullback.snd p h := by
  let t j := sectionBaseChange p (s j) (hs j) h
  have : ∀ j, IsClosedImmersion (t j) := fun j =>
    isClosedImmersion_sectionBaseChange p (s j) (hs j) h
  apply exists_iso_coproduct_of_selected_closed_sections i (pullback.snd p h) t
    (fun j => sectionBaseChange_snd p (s j) (hs j) h) hmember
  · intro j k
    rcases hagree j k with heq | hne
    · left
      have hsub (j k : Fin n) (heq : ∀ x, s j (h x) = s k (h x)) :
          Set.range (t j) ⊆ Set.range (t k) := by
        rintro _ ⟨x, rfl⟩
        dsimp only [t]
        rw [range_sectionBaseChange]
        refine ⟨h x, ?_⟩
        show s k (h x) = (sectionBaseChange p (s j) (hs j) h ≫ pullback.fst p h) x
        rw [sectionBaseChange_fst]
        exact (heq x).symm
      exact Set.Subset.antisymm (hsub j k heq) (hsub k j (fun x => (heq x).symm))
    · right
      apply Set.disjoint_left.mpr
      rintro z ⟨x, hx⟩ ⟨y, hy⟩
      have hxy : x = y := by
        have := congrArg (pullback.snd p h) (hx.trans hy.symm)
        simpa [← Scheme.Hom.comp_apply, t, sectionBaseChange_snd] using this
      subst y
      apply hne x
      have := congrArg (pullback.fst p h) (hx.trans hy.symm)
      simpa only [← Scheme.Hom.comp_apply, t, sectionBaseChange_fst] using this
  · apply Set.eq_univ_of_forall
    intro z
    obtain ⟨j, hj⟩ := Set.iUnion_eq_univ_iff.mp hcover (pullback.fst p h z)
    exact Set.mem_iUnion.mpr ⟨j, by
      simpa only [t, range_sectionBaseChange, Set.mem_preimage] using hj⟩

private def closedImmersionBaseChange {X Y Z T : Scheme.{u}}
    (i : Y ⟶ Z) (p : Z ⟶ X) (h : T ⟶ X) :
    pullback (i ≫ p) h ⟶ pullback p h :=
  pullback.lift (pullback.fst (i ≫ p) h ≫ i) (pullback.snd (i ≫ p) h)
    (by simp only [Category.assoc, pullback.condition])

private lemma closedImmersionBaseChange_fst {X Y Z T : Scheme.{u}}
    (i : Y ⟶ Z) (p : Z ⟶ X) (h : T ⟶ X) :
    closedImmersionBaseChange i p h ≫ pullback.fst p h = pullback.fst (i ≫ p) h ≫ i :=
  pullback.lift_fst _ _ _

private lemma closedImmersionBaseChange_snd {X Y Z T : Scheme.{u}}
    (i : Y ⟶ Z) (p : Z ⟶ X) (h : T ⟶ X) :
    closedImmersionBaseChange i p h ≫ pullback.snd p h = pullback.snd (i ≫ p) h :=
  pullback.lift_snd _ _ _

private lemma isPullback_closedImmersionBaseChange {X Y Z T : Scheme.{u}}
    (i : Y ⟶ Z) (p : Z ⟶ X) (h : T ⟶ X) :
    IsPullback (closedImmersionBaseChange i p h) (pullback.fst (i ≫ p) h)
      (pullback.fst p h) i := by
  apply IsPullback.of_right (h₁₂ := pullback.snd p h) (h₂₂ := p)
  · rw [closedImmersionBaseChange_snd]
    exact (IsPullback.of_hasPullback (i ≫ p) h).flip
  · exact closedImmersionBaseChange_fst i p h
  · exact (IsPullback.of_hasPullback p h).flip

private lemma range_closedImmersionBaseChange {X Y Z T : Scheme.{u}}
    (i : Y ⟶ Z) (p : Z ⟶ X) (h : T ⟶ X) :
    Set.range (closedImmersionBaseChange i p h) = (pullback.fst p h) ⁻¹' Set.range i := by
  simpa using Scheme.image_preimage_eq_of_isPullback
    (isPullback_closedImmersionBaseChange i p h).flip Set.univ

private lemma exists_split_of_constant_section_loci
    {X Y Z T : Scheme.{u}} [IsReduced T]
    (i : Y ⟶ Z) [IsClosedImmersion i] (p : Z ⟶ X) (h : T ⟶ X) {n : ℕ}
    (s : Fin n → (X ⟶ Z)) [∀ j, IsClosedImmersion (s j)]
    (hs : ∀ j, s j ≫ p = 𝟙 X)
    (hmember : ∀ j, (∀ t, s j (h t) ∈ Set.range i) ∨
      (∀ t, s j (h t) ∉ Set.range i))
    (hagree : ∀ j k, (∀ t, s j (h t) = s k (h t)) ∨
      (∀ t, s j (h t) ≠ s k (h t)))
    (hcover : (⋃ j, Set.range (s j)) = Set.univ) :
    ∃ (m : ℕ) (e : (pullback (i ≫ p) h).nilradical.subscheme ≅ ∐ fun _ : Fin m => T),
      e.hom ≫ Sigma.desc (fun _ : Fin m => 𝟙 T) =
        (pullback (i ≫ p) h).nilradical.subschemeι ≫ pullback.snd (i ≫ p) h := by
  let P := pullback (i ≫ p) h
  let r : P.nilradical.subscheme ⟶ pullback p h :=
    P.nilradical.subschemeι ≫ closedImmersionBaseChange i p h
  have : IsReduced P.nilradical.subscheme := P.isReduced_reduction
  have : IsClosedImmersion (closedImmersionBaseChange i p h) :=
    MorphismProperty.of_isPullback (isPullback_closedImmersionBaseChange i p h).flip
      (show IsClosedImmersion i from inferInstance)
  have : IsClosedImmersion r := by dsimp [r]; infer_instance
  have hsur : Function.Surjective P.nilradical.subschemeι := by
    rw [← Set.range_eq_univ, Scheme.IdealSheafData.range_subschemeι]
    simp
  have hr : Set.range r = (pullback.fst p h) ⁻¹' Set.range i := by
    show Set.range ((closedImmersionBaseChange i p h) ∘ P.nilradical.subschemeι) = _
    rw [Set.range_comp, hsur.range_eq, Set.image_univ, range_closedImmersionBaseChange]
  have hm (j) : Set.range (sectionBaseChange p (s j) (hs j) h) ⊆ Set.range r ∨
      Disjoint (Set.range (sectionBaseChange p (s j) (hs j) h)) (Set.range r) := by
    rcases hmember j with hj | hj
    · left
      rintro _ ⟨x, rfl⟩
      rw [hr]
      show (sectionBaseChange p (s j) (hs j) h ≫ pullback.fst p h) x ∈ Set.range i
      rw [sectionBaseChange_fst]
      exact hj x
    · right
      apply Set.disjoint_left.mpr
      rintro z ⟨x, rfl⟩ hx
      rw [hr] at hx
      change (sectionBaseChange p (s j) (hs j) h ≫ pullback.fst p h) x ∈ Set.range i at hx
      rw [sectionBaseChange_fst] at hx
      exact hj x hx
  obtain ⟨m, e, he⟩ := exists_iso_coproduct_of_baseChange_sections p h r s hs hm hagree hcover
  refine ⟨m, e, ?_⟩
  simpa only [r, Category.assoc, closedImmersionBaseChange_snd] using he

private lemma isConstructible_of_isLocallyClosed_of_noetherian
    {T : Type*} [TopologicalSpace T] [TopologicalSpace.NoetherianSpace T]
    {S : Set T} (hS : IsLocallyClosed S) : Topology.IsConstructible S := by
  obtain ⟨U, C, hU, hC, rfl⟩ := hS
  exact ((TopologicalSpace.NoetherianSpace.isCompact U).isConstructible hU).inter
    ((TopologicalSpace.NoetherianSpace.isCompact Cᶜ).isConstructible hC.isOpen_compl).of_compl

private lemma exists_finite_affine_partition_of_noetherian (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X] :
    ∃ (J : Type) (_ : Fintype J) (T : J → Scheme.{u}) (t : ∀ j, T j ⟶ X),
      (∀ j, IsAffine (T j) ∧ IsReduced (T j) ∧ IsImmersion (t j) ∧
        IsLocallyClosed (Set.range (t j)) ∧ Topology.IsConstructible (Set.range (t j))) ∧
      (Pairwise fun j k => Disjoint (Set.range (t j)) (Set.range (t k))) ∧
      (⋃ j, Set.range (t j)) = Set.univ := by
  classical
  obtain ⟨J, hJ, order, ⟨a⟩⟩ := (hasFiniteAffineStratification_iff X).mpr
    ⟨inferInstance, inferInstance⟩
  let := hJ
  let := Fintype.ofFinite J
  let := order
  let h := a.isLocallyFiniteStratification.isStratification.isPartition
  let T j := reducedInducedScheme (a.strata j) (h.locallyClosed j)
  let t j : T j ⟶ X := reducedInducedInclusion (a.strata j) (h.locallyClosed j)
  have hr (j) : Set.range (t j) = a.strata j := range_reducedInducedInclusion _ (h.locallyClosed j)
  refine ⟨J, inferInstance, T, t, ?_, ?_, ?_⟩
  · intro j
    have ht : IsImmersion (t j) := by dsimp [t]; infer_instance
    refine ⟨a.isAffine j, ?_, ht, ?_, ?_⟩
    · exact Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
    · rw [hr]; exact h.locallyClosed j
    · rw [hr]; exact isConstructible_of_isLocallyClosed_of_noetherian (h.locallyClosed j)
  · intro j k hjk
    rw [hr, hr]
    exact h.disjoint j k hjk
  · simp only [hr]
    exact h.cover

/-- Partitioning each stratum of a partition into affine locally closed constructible pieces
partitions the whole space. -/
private lemma partition_comp_of_partitions {X : Scheme.{u}} [TopologicalSpace.NoetherianSpace X]
    {K : Type} {L : K → Type} {S : K → Scheme.{u}} (s : ∀ k, S k ⟶ X)
    [∀ k, IsImmersion (s k)] {V : ∀ k, L k → Scheme.{u}} (v : ∀ k l, V k l ⟶ S k)
    (hv : ∀ k l, IsAffine (V k l) ∧ IsReduced (V k l) ∧ IsImmersion (v k l) ∧
      IsLocallyClosed (Set.range (v k l)) ∧ Topology.IsConstructible (Set.range (v k l)))
    (hdS : Pairwise fun j k => Disjoint (Set.range (s j)) (Set.range (s k)))
    (hcS : (⋃ k, Set.range (s k)) = Set.univ)
    (hdV : ∀ k, Pairwise fun l l' => Disjoint (Set.range (v k l)) (Set.range (v k l')))
    (hcV : ∀ k, (⋃ l, Set.range (v k l)) = Set.univ) :
    (∀ j : Σ k, L k, IsAffine (V j.1 j.2) ∧ IsReduced (V j.1 j.2) ∧
      IsImmersion (v j.1 j.2 ≫ s j.1) ∧ IsLocallyClosed (Set.range (v j.1 j.2 ≫ s j.1)) ∧
      Topology.IsConstructible (Set.range (v j.1 j.2 ≫ s j.1))) ∧
    (Pairwise fun j j' : Σ k, L k =>
      Disjoint (Set.range (v j.1 j.2 ≫ s j.1)) (Set.range (v j'.1 j'.2 ≫ s j'.1))) ∧
    (⋃ j : Σ k, L k, Set.range (v j.1 j.2 ≫ s j.1)) = Set.univ := by
  refine ⟨fun j => ?_, ?_, ?_⟩
  · have : IsImmersion (v j.1 j.2) := (hv j.1 j.2).2.2.1
    exact ⟨(hv j.1 j.2).1, (hv j.1 j.2).2.1, inferInstance,
      (v j.1 j.2 ≫ s j.1).isLocallyClosed_range,
      isConstructible_of_isLocallyClosed_of_noetherian (v j.1 j.2 ≫ s j.1).isLocallyClosed_range⟩
  · have hsub (j : Σ k, L k) : Set.range (v j.1 j.2 ≫ s j.1) ⊆ Set.range (s j.1) := by
      rintro _ ⟨x, rfl⟩
      exact ⟨v j.1 j.2 x, rfl⟩
    rintro ⟨k, l⟩ ⟨k', l'⟩ hne
    by_cases hk : k = k'
    · subst k'
      have hl : l ≠ l' := fun h => hne (by subst l'; rfl)
      apply Set.disjoint_left.mpr
      rintro x ⟨y, hy⟩ ⟨z, hz⟩
      have hyz : v k l y = v k l' z := (s k).isEmbedding.injective (hy.trans hz.symm)
      exact Set.disjoint_left.mp (hdV k hl) ⟨y, hyz⟩ ⟨z, rfl⟩
    · exact (hdS hk).mono (hsub ⟨k, l⟩) (hsub ⟨k', l'⟩)
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨k, y, hy⟩ := Set.iUnion_eq_univ_iff.mp hcS x
    obtain ⟨l, z, hz⟩ := Set.iUnion_eq_univ_iff.mp (hcV k) y
    exact Set.mem_iUnion.mpr ⟨⟨k, l⟩, z, by change s k (v k l z) = x; rw [hz, hy]⟩

private lemma exists_finite_affine_refinement_of_noetherian
    {X : Scheme.{u}} [TopologicalSpace.NoetherianSpace X]
    {n : ℕ} (S : Fin n → Set X) (hS : ∀ j, IsLocallyClosed (S j))
    (hdisj : Pairwise fun j k => Disjoint (S j) (S k))
    (hcover : (⋃ j, S j) = Set.univ) :
    ∃ (J : Type) (_ : Fintype J) (T : J → Scheme.{u}) (t : ∀ j, T j ⟶ X),
      (∀ j, IsAffine (T j) ∧ IsReduced (T j) ∧ IsImmersion (t j) ∧
        IsLocallyClosed (Set.range (t j)) ∧ Topology.IsConstructible (Set.range (t j))) ∧
      (Pairwise fun j k => Disjoint (Set.range (t j)) (Set.range (t k))) ∧
      (⋃ j, Set.range (t j)) = Set.univ ∧
      ∀ j, ∃ k, Set.range (t j) ⊆ S k := by
  classical
  let V j := reducedInducedScheme (S j) (hS j)
  let v j : V j ⟶ X := reducedInducedInclusion (S j) (hS j)
  have vi (j) : IsImmersion (v j) := by dsimp [v]; infer_instance
  have vr (j) : Set.range (v j) = S j := range_reducedInducedInclusion _ (hS j)
  have : ∀ j, TopologicalSpace.NoetherianSpace (V j) := fun j =>
    (v j).isEmbedding.isInducing.noetherianSpace
  choose J hJ T t ht hd hc using fun j => exists_finite_affine_partition_of_noetherian (V j)
  let : ∀ j, Fintype (J j) := hJ
  let U (j : Σ i, J i) := T j.1 j.2
  let r (j : Σ i, J i) : U j ⟶ X := t j.1 j.2 ≫ v j.1
  have hrsub (j : Σ i, J i) : Set.range (r j) ⊆ S j.1 := by
    rw [← vr]
    rintro _ ⟨x, rfl⟩
    exact ⟨t j.1 j.2 x, rfl⟩
  have : ∀ j, IsImmersion (v j) := vi
  obtain ⟨h₁, h₂, h₃⟩ := partition_comp_of_partitions v t ht
    (fun j k hjk => by simp only [vr]; exact hdisj hjk) (by simp only [vr]; exact hcover) hd hc
  exact ⟨Σ i, J i, inferInstance, U, r, h₁, h₂, h₃, fun j => ⟨j.1, hrsub j⟩⟩

private lemma isClosed_section_agreement {X Z : Scheme.{u}} (p : Z ⟶ X)
    (s t : X ⟶ Z) [IsClosedImmersion s] (hs : s ≫ p = 𝟙 X)
    (ht : t ≫ p = 𝟙 X) : IsClosed {x | s x = t x} := by
  have heq : {x | s x = t x} = t ⁻¹' Set.range s := by
    ext x
    constructor
    · exact fun hx => ⟨x, hx⟩
    · rintro ⟨y, hy⟩
      have hyx : y = x := by
        have h := congrArg p hy
        simpa [← Scheme.Hom.comp_apply, hs, ht] using h
      simpa only [hyx, Set.mem_ofPred_eq] using hy
  rw [heq]
  exact s.isClosedEmbedding.isClosed_range.preimage t.continuous

private lemma exists_affine_stratification_of_closed_sections
    {X Y Z : Scheme.{u}} [TopologicalSpace.NoetherianSpace X]
    (i : Y ⟶ Z) [IsClosedImmersion i] (p : Z ⟶ X) {n : ℕ}
    (s : Fin n → (X ⟶ Z)) [∀ j, IsClosedImmersion (s j)]
    (hs : ∀ j, s j ≫ p = 𝟙 X)
    (hcover : (⋃ j, Set.range (s j)) = Set.univ) :
    ∃ (J : Type) (_ : Fintype J) (T : J → Scheme.{u}) (t : ∀ j, T j ⟶ X),
      (∀ j, IsAffine (T j) ∧ IsReduced (T j) ∧ IsImmersion (t j) ∧
        IsLocallyClosed (Set.range (t j)) ∧ Topology.IsConstructible (Set.range (t j))) ∧
      (Pairwise fun j k => Disjoint (Set.range (t j)) (Set.range (t k))) ∧
      (⋃ j, Set.range (t j)) = Set.univ ∧
      ∀ j, ∃ (m : ℕ)
        (e : (pullback (i ≫ p) (t j)).nilradical.subscheme ≅ ∐ fun _ : Fin m => T j),
        e.hom ≫ Sigma.desc (fun _ : Fin m => 𝟙 (T j)) =
          (pullback (i ≫ p) (t j)).nilradical.subschemeι ≫ pullback.snd (i ≫ p) (t j) := by
  classical
  let member j : Set X := (s j) ⁻¹' Set.range i
  let agree j k : Set X := {x | s j x = s k x}
  have hm (j) : Topology.IsConstructible (member j) :=
    isConstructible_of_isLocallyClosed_of_noetherian
      (i.isClosedEmbedding.isClosed_range.preimage (s j).continuous).isLocallyClosed
  have ha (j k) : Topology.IsConstructible (agree j k) :=
    isConstructible_of_isLocallyClosed_of_noetherian
      (isClosed_section_agreement p (s j) (s k) (hs j) (hs k)).isLocallyClosed
  obtain ⟨l, S, hS, hd, hc, hm, ha⟩ := finiteSectionLoci_refined_constancy member agree hm ha
  obtain ⟨J, hJ, T, t, ht, htd, htc, href⟩ :=
    exists_finite_affine_refinement_of_noetherian S (fun j => (hS j).1) hd hc
  let := hJ
  refine ⟨J, hJ, T, t, ht, htd, htc, ?_⟩
  intro j
  have : IsReduced (T j) := (ht j).2.1
  obtain ⟨k, hk⟩ := href j
  have htk (x : T j) : t j x ∈ S k := hk ⟨x, rfl⟩
  apply exists_split_of_constant_section_loci i p (t j) s hs _ _ hcover
  · intro a
    rcases subset_or_disjoint_of_constant (hm a k) with h | h
    · exact Or.inl (fun x => h (htk x))
    · exact Or.inr (fun x hx => Set.disjoint_left.mp h (htk x) hx)
  · intro a b
    rcases subset_or_disjoint_of_constant (ha a b k) with h | h
    · exact Or.inl (fun x => h (htk x))
    · exact Or.inr (fun x hx => Set.disjoint_left.mp h (htk x) hx)

private lemma isIso_reductionMap_of_isThickening {X Y : Scheme.{u}}
    (i : X ⟶ Y) (hi : Stacks.Thickenings.IsThickening i) : IsIso (reductionMap i) := by
  have : IsClosedImmersion i := hi.1
  have : IsClosedImmersion (reductionMap i) := isClosedImmersion_reductionMap i
  have : IsReduced Y.nilradical.subscheme := Y.isReduced_reduction
  have : Surjective (reductionMap i) := by
    constructor
    intro y
    obtain ⟨x, hx⟩ := hi.2 (Y.nilradical.subschemeι y)
    obtain ⟨z, hz⟩ := (Stacks.AffineClosedUnion.isThickening_subschemeι_nilradical X).2 x
    refine ⟨z, Y.nilradical.subschemeι.isClosedEmbedding.injective ?_⟩
    show (reductionMap i ≫ Y.nilradical.subschemeι) z = Y.nilradical.subschemeι y
    rw [reductionMap_comp_subschemeι]
    show i (X.nilradical.subschemeι z) = _
    rw [hz, hx]
  exact isIso_of_isClosedImmersion_of_surjective _

/-- A splitting of the source of `s` into copies of its target transports along isomorphisms of
the source and the target of a commuting square. -/
private lemma exists_split_of_iso_square {Y P X T : Scheme.{u}} (α : Y ≅ P) (β : X ≅ T)
    (r : P ⟶ T) (s : Y ⟶ X) (hsq : α.hom ≫ r = s ≫ β.hom) {n : ℕ}
    (e : Y ≅ ∐ fun _ : Fin n => X) (he : e.hom ≫ Sigma.desc (fun _ : Fin n => 𝟙 X) = s) :
    ∃ a : P ≅ ∐ fun _ : Fin n => T, a.hom ≫ Sigma.desc (fun _ : Fin n => 𝟙 T) = r := by
  have hcodiagonal : (Sigma.mapIso fun _ : Fin n => β).hom ≫ Sigma.desc (fun _ => 𝟙 T) =
      Sigma.desc (fun _ => 𝟙 X) ≫ β.hom := by
    apply Sigma.hom_ext
    intro j
    simp
  refine ⟨α.symm ≪≫ e ≪≫ Sigma.mapIso fun _ => β, ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, hcodiagonal]
  rw [← Category.assoc e.hom, he, ← hsq, Iso.inv_hom_id_assoc]

private lemma exists_split_reduction_of_thickening_baseChange
    {Y X T : Scheme.{u}} (f : Y ⟶ X) (h : T ⟶ X)
    (hh : Stacks.Thickenings.IsThickening h) {n : ℕ}
    (e : (pullback f h).nilradical.subscheme ≅ ∐ fun _ : Fin n => T.nilradical.subscheme)
    (he : e.hom ≫ Sigma.desc (fun _ : Fin n => 𝟙 T.nilradical.subscheme) =
      reductionMap (pullback.snd f h)) :
    ∃ a : Y.nilradical.subscheme ≅ ∐ fun _ : Fin n => X.nilradical.subscheme,
      a.hom ≫ Sigma.desc (fun _ : Fin n => 𝟙 X.nilradical.subscheme) = reductionMap f := by
  have hf : Stacks.Thickenings.IsThickening (pullback.fst f h) :=
    MorphismProperty.pullback_fst _ _ hh
  have : IsIso (reductionMap h) := isIso_reductionMap_of_isThickening h hh
  have : IsIso (reductionMap (pullback.fst f h)) :=
    isIso_reductionMap_of_isThickening _ hf
  exact exists_split_of_iso_square (asIso (reductionMap (pullback.fst f h)))
    (asIso (reductionMap h)) _ _
    (by simp only [asIso_hom, reductionMap_comp, pullback.condition]) e he

private lemma exists_split_after_baseChange_of_reduced_base
    {Y X T : Scheme.{u}} [IsReduced X] [IsReduced T]
    (f : Y ⟶ X) (h : T ⟶ X) {n : ℕ}
    (e : Y.nilradical.subscheme ≅ ∐ fun _ : Fin n => X)
    (he : e.hom ≫ Sigma.desc (fun _ : Fin n => 𝟙 X) = Y.nilradical.subschemeι ≫ f) :
    ∃ (m : ℕ) (a : (pullback f h).nilradical.subscheme ≅ ∐ fun _ : Fin m => T),
      a.hom ≫ Sigma.desc (fun _ : Fin m => 𝟙 T) =
        (pullback f h).nilradical.subschemeι ≫ pullback.snd f h := by
  let S : Fin n → Scheme.{u} := fun _ => X
  let codiagonal := Sigma.desc (fun _ : Fin n => 𝟙 X)
  have : IsFinite codiagonal := inferInstance
  have hc (j) : IsClosedImmersion (Sigma.ι S j) :=
    isClosedImmersion_of_comp_eq (Sigma.ι S j) codiagonal (c := 𝟙 X) (Sigma.ι_desc _ _)
  let s (j : Fin n) : X ⟶ Y := Sigma.ι S j ≫ e.inv ≫ Y.nilradical.subschemeι
  have : ∀ j, IsClosedImmersion (s j) := by
    intro j
    dsimp [s]
    infer_instance
  have hs (j) : s j ≫ f = 𝟙 X := by
    simp only [s, Category.assoc, ← he, Iso.inv_hom_id_assoc, Sigma.ι_desc]
  have hcover : (⋃ j, Set.range (s j)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨z, hz⟩ := (Stacks.AffineClosedUnion.isThickening_subschemeι_nilradical Y).2 y
    obtain ⟨j, x, hx⟩ := (sigmaOpenCover S).exists_eq (e.hom z)
    refine Set.mem_iUnion.mpr ⟨j, x, ?_⟩
    show Y.nilradical.subschemeι (e.inv (Sigma.ι S j x)) = y
    rw [show Sigma.ι S j x = e.hom z from hx]
    simpa using hz
  have hsplit := exists_split_of_constant_section_loci (𝟙 Y) f h s hs
    (fun j => Or.inl (fun x => ⟨s j (h x), by simp⟩))
    (fun j k => ?_) hcover
  · rw [Category.id_comp] at hsplit
    exact hsplit
  · by_cases hjk : j = k
    · exact Or.inl (fun x => by rw [hjk])
    · refine Or.inr (fun x hx => hjk ?_)
      have hx' := Y.nilradical.subschemeι.isClosedEmbedding.injective hx
      have hx'' := e.inv.homeomorph.injective hx'
      exact congrArg Sigma.fst ((sigmaι_eq_iff S j k (h x) (h x)).mp hx'')

private lemma exists_split_reduction_of_reduced_base {Y X : Scheme.{u}}
    [IsReduced X] (f : Y ⟶ X) {m : ℕ}
    (e : Y.nilradical.subscheme ≅ ∐ fun _ : Fin m => X)
    (he : e.hom ≫ Sigma.desc (fun _ : Fin m => 𝟙 X) = Y.nilradical.subschemeι ≫ f) :
    ∃ (q : Y.nilradical.subscheme ⟶ X.nilradical.subscheme)
      (e' : Y.nilradical.subscheme ≅ ∐ fun _ : Fin m => X.nilradical.subscheme),
      q ≫ X.nilradical.subschemeι = Y.nilradical.subschemeι ≫ f ∧
      e'.hom ≫ Sigma.desc (fun _ : Fin m => 𝟙 X.nilradical.subscheme) = q := by
  have : Surjective X.nilradical.subschemeι :=
    ⟨(Stacks.AffineClosedUnion.isThickening_subschemeι_nilradical X).2⟩
  have : IsIso X.nilradical.subschemeι := isIso_of_isClosedImmersion_of_surjective _
  obtain ⟨e', he'⟩ := exists_split_of_iso_square (Iso.refl _) (asIso X.nilradical.subschemeι).symm
    (reductionMap f) _ (by simp [← reductionMap_comp_subschemeι f]) e he
  exact ⟨reductionMap f, e', reductionMap_comp_subschemeι f, he'⟩

/-- A morphism of reductions compatible with the inclusions is the induced `reductionMap`. -/
private lemma eq_reductionMap_of_comp_subschemeι {Y X : Scheme.{u}} (f : Y ⟶ X)
    (q : Y.nilradical.subscheme ⟶ X.nilradical.subscheme)
    (hq : q ≫ X.nilradical.subschemeι = Y.nilradical.subschemeι ≫ f) :
    q = reductionMap f := by
  apply (cancel_mono X.nilradical.subschemeι).mp
  rw [hq, reductionMap_comp_subschemeι]

private lemma exists_split_reduction_after_baseChange
    {Y X T : Scheme.{u}} [IsReduced X] (f : Y ⟶ X) (h : T ⟶ X) {n : ℕ}
    (e : Y.nilradical.subscheme ≅ ∐ fun _ : Fin n => X)
    (he : e.hom ≫ Sigma.desc (fun _ : Fin n => 𝟙 X) = Y.nilradical.subschemeι ≫ f) :
    ∃ (m : ℕ)
      (a : (pullback f h).nilradical.subscheme ≅ ∐ fun _ : Fin m => T.nilradical.subscheme),
      a.hom ≫ Sigma.desc (fun _ : Fin m => 𝟙 T.nilradical.subscheme) =
        reductionMap (pullback.snd f h) := by
  have : IsReduced T.nilradical.subscheme := T.isReduced_reduction
  obtain ⟨m, a, ha⟩ := exists_split_after_baseChange_of_reduced_base
    f (T.nilradical.subschemeι ≫ h) e he
  obtain ⟨a', ha'⟩ := exists_split_of_iso_square
    (reductionIso (pullbackLeftPullbackSndIso f h T.nilradical.subschemeι)).symm (Iso.refl _)
    ((pullback (pullback.snd f h) T.nilradical.subschemeι).nilradical.subschemeι ≫
      pullback.snd (pullback.snd f h) T.nilradical.subschemeι) _
    (by
      rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, reductionIso_inv, ← Category.assoc,
        reductionMap_comp_subschemeι, Category.assoc, pullbackLeftPullbackSndIso_inv_snd_snd])
    a ha
  obtain ⟨q, a'', hq, ha''⟩ := exists_split_reduction_of_reduced_base
    (pullback.snd (pullback.snd f h) T.nilradical.subschemeι) a' ha'
  have hq' := eq_reductionMap_of_comp_subschemeι _ q hq
  obtain ⟨a''', ha'''⟩ := exists_split_reduction_of_thickening_baseChange
    (pullback.snd f h) T.nilradical.subschemeι
    (Stacks.AffineClosedUnion.isThickening_subschemeι_nilradical T) a'' (ha''.trans hq')
  exact ⟨m, a''', ha'''⟩

private lemma split_reduction_pullback_composite
    {Y X T V : Scheme.{u}} (f : Y ⟶ X) (g : T ⟶ X) (h : V ⟶ T) {n : ℕ}
    (q : (pullback (pullback.snd f g) h).nilradical.subscheme ⟶
      V.nilradical.subscheme)
    (e : (pullback (pullback.snd f g) h).nilradical.subscheme ≅
      ∐ fun _ : Fin n => V.nilradical.subscheme)
    (hq : q ≫ V.nilradical.subschemeι =
      (pullback (pullback.snd f g) h).nilradical.subschemeι ≫
        pullback.snd (pullback.snd f g) h)
    (he : e.hom ≫ Sigma.desc (fun _ : Fin n => 𝟙 V.nilradical.subscheme) = q) :
    ∃ (q' : (pullback f (h ≫ g)).nilradical.subscheme ⟶ V.nilradical.subscheme)
      (e' : (pullback f (h ≫ g)).nilradical.subscheme ≅
        ∐ fun _ : Fin n => V.nilradical.subscheme),
      q' ≫ V.nilradical.subschemeι =
        (pullback f (h ≫ g)).nilradical.subschemeι ≫ pullback.snd f (h ≫ g) ∧
      e'.hom ≫ Sigma.desc (fun _ : Fin n => 𝟙 V.nilradical.subscheme) = q' := by
  obtain ⟨b, hb⟩ := exists_split_of_iso_square
    (reductionIso (pullbackLeftPullbackSndIso f g h)) (Iso.refl _)
    (reductionMap (pullback.snd f (h ≫ g))) q
    (by
      rw [Iso.refl_hom, Category.comp_id, eq_reductionMap_of_comp_subschemeι _ q hq,
        reductionIso_hom, reductionMap_comp, pullbackLeftPullbackSndIso_hom_snd]) e he
  exact ⟨_, b, reductionMap_comp_subschemeι _, hb⟩

private lemma exists_split_reduction_after_baseChange_of_pullback
    {Y X T V : Scheme.{u}} [IsReduced T] (f : Y ⟶ X) (g : T ⟶ X)
    (h : V ⟶ T) {n : ℕ}
    (e : (pullback f g).nilradical.subscheme ≅ ∐ fun _ : Fin n => T)
    (he : e.hom ≫ Sigma.desc (fun _ : Fin n => 𝟙 T) =
      (pullback f g).nilradical.subschemeι ≫ pullback.snd f g) :
    ∃ (m : ℕ) (a : (pullback f (h ≫ g)).nilradical.subscheme ≅
        ∐ fun _ : Fin m => V.nilradical.subscheme),
      a.hom ≫ Sigma.desc (fun _ : Fin m => 𝟙 V.nilradical.subscheme) =
        reductionMap (pullback.snd f (h ≫ g)) := by
  obtain ⟨m, a, ha⟩ :=
    exists_split_reduction_after_baseChange (pullback.snd f g) h e he
  obtain ⟨q, c, hq, hc⟩ := split_reduction_pullback_composite f g h _ a
    (reductionMap_comp_subschemeι _) ha
  exact ⟨m, c, hc.trans (eq_reductionMap_of_comp_subschemeι _ q hq)⟩

private lemma split_reduction_over_reduced_base
    {Y T : Scheme.{u}} [IsReduced T] (f : Y ⟶ T) {n : ℕ}
    (q : Y.nilradical.subscheme ⟶ T.nilradical.subscheme)
    (e : Y.nilradical.subscheme ≅ ∐ fun _ : Fin n => T.nilradical.subscheme)
    (hq : q ≫ T.nilradical.subschemeι = Y.nilradical.subschemeι ≫ f)
    (he : e.hom ≫ Sigma.desc (fun _ : Fin n => 𝟙 T.nilradical.subscheme) = q) :
    ∃ a : Y.nilradical.subscheme ≅ ∐ fun _ : Fin n => T,
      a.hom ≫ Sigma.desc (fun _ : Fin n => 𝟙 T) = Y.nilradical.subschemeι ≫ f := by
  have : IsIso T.nilradical.subschemeι := by
    rw [Scheme.nilradical_eq_bot]
    infer_instance
  exact exists_split_of_iso_square (Iso.refl _) (asIso T.nilradical.subschemeι) _ _
    ((Category.id_comp _).trans hq.symm) e he

private lemma exists_split_reduction_of_thickening
    {Y X T : Scheme.{u}} (f : Y ⟶ X) (h : T ⟶ X)
    (hh : Stacks.Thickenings.IsThickening h) {n : ℕ}
    (q : (pullback f h).nilradical.subscheme ⟶ T.nilradical.subscheme)
    (e : (pullback f h).nilradical.subscheme ≅
      ∐ fun _ : Fin n => T.nilradical.subscheme)
    (hq : q ≫ T.nilradical.subschemeι =
      (pullback f h).nilradical.subschemeι ≫ pullback.snd f h)
    (he : e.hom ≫ Sigma.desc (fun _ : Fin n => 𝟙 T.nilradical.subscheme) = q) :
    ∃ (q' : Y.nilradical.subscheme ⟶ X.nilradical.subscheme)
      (e' : Y.nilradical.subscheme ≅ ∐ fun _ : Fin n => X.nilradical.subscheme),
      q' ≫ X.nilradical.subschemeι = Y.nilradical.subschemeι ≫ f ∧
      e'.hom ≫ Sigma.desc (fun _ : Fin n => 𝟙 X.nilradical.subscheme) = q' := by
  have hq' := eq_reductionMap_of_comp_subschemeι _ q hq
  obtain ⟨a, ha⟩ := exists_split_reduction_of_thickening_baseChange f h hh e
    (he.trans hq')
  exact ⟨reductionMap f, a, reductionMap_comp_subschemeι _, ha⟩

private lemma exists_split_reduction_of_thickening_after_pullback
    {Y X W P : Scheme.{u}} (f : Y ⟶ X) (g : W ⟶ X) (a : P ⟶ W)
    (ha : Stacks.Thickenings.IsThickening a) {n : ℕ}
    (q : (pullback f (a ≫ g)).nilradical.subscheme ⟶ P.nilradical.subscheme)
    (e : (pullback f (a ≫ g)).nilradical.subscheme ≅
      ∐ fun _ : Fin n => P.nilradical.subscheme)
    (hq : q ≫ P.nilradical.subschemeι =
      (pullback f (a ≫ g)).nilradical.subschemeι ≫ pullback.snd f (a ≫ g))
    (he : e.hom ≫ Sigma.desc (fun _ : Fin n => 𝟙 P.nilradical.subscheme) = q) :
    ∃ (q' : (pullback f g).nilradical.subscheme ⟶ W.nilradical.subscheme)
      (e' : (pullback f g).nilradical.subscheme ≅
        ∐ fun _ : Fin n => W.nilradical.subscheme),
      q' ≫ W.nilradical.subschemeι =
        (pullback f g).nilradical.subschemeι ≫ pullback.snd f g ∧
      e'.hom ≫ Sigma.desc (fun _ : Fin n => 𝟙 W.nilradical.subscheme) = q' := by
  let b := pullbackLeftPullbackSndIso f g a
  have hb : (reductionIso b).hom ≫ q ≫ P.nilradical.subschemeι =
      (pullback (pullback.snd f g) a).nilradical.subschemeι ≫
        pullback.snd (pullback.snd f g) a := by
    rw [hq, ← Category.assoc]
    dsimp only [reductionIso_hom]
    rw [reductionMap_comp_subschemeι, Category.assoc]
    exact congrArg ((pullback (pullback.snd f g) a).nilradical.subschemeι ≫ ·)
      (pullbackLeftPullbackSndIso_hom_snd f g a)
  obtain ⟨q', e', hq', he'⟩ := exists_split_reduction_of_thickening
    (pullback.snd f g) a ha ((reductionIso b).hom ≫ q)
    (reductionIso b ≪≫ e) hb (by
      dsimp only [Iso.trans_hom]
      rw [Category.assoc, he])
  exact ⟨q', e', hq', he'⟩

private lemma thickening_over_reduction {Y X : Scheme.{u}} (f : Y ⟶ X)
    (q : Y.nilradical.subscheme ⟶ X.nilradical.subscheme)
    (hq : q ≫ X.nilradical.subschemeι = Y.nilradical.subschemeι ≫ f) :
    ∃ i : Y.nilradical.subscheme ⟶ pullback f X.nilradical.subschemeι,
      (IsClosedImmersion i ∧ Function.Surjective i) ∧
      i ≫ pullback.snd f X.nilradical.subschemeι = q := by
  let i := pullback.lift Y.nilradical.subschemeι q hq.symm
  have hi : i ≫ pullback.fst f X.nilradical.subschemeι = Y.nilradical.subschemeι := by
    simp only [i, pullback.lift_fst]
  have : IsClosedImmersion i :=
    isClosedImmersion_of_comp_eq i (pullback.fst f X.nilradical.subschemeι) hi
  refine ⟨i, ⟨inferInstance, ?_⟩, by simp only [i, pullback.lift_snd]⟩
  intro x
  obtain ⟨z, hz⟩ := (Stacks.AffineClosedUnion.isThickening_subschemeι_nilradical Y).2
    ((pullback.fst f X.nilradical.subschemeι) x)
  refine ⟨z, (pullback.fst f X.nilradical.subschemeι).isClosedEmbedding.injective ?_⟩
  simpa only [← Scheme.Hom.comp_apply, hi] using hz

private lemma isPullback_sigmaMap {n : ℕ} {X Y : Fin n → Scheme.{u}}
    (f : ∀ i, X i ⟶ Y i) (i : Fin n) :
    IsPullback (Sigma.ι X i) (f i) ((Sigma.desc fun i => f i ≫ Sigma.ι Y i)) (Sigma.ι Y i) := by
  let a := Cofan.mk (∐ Y) (Sigma.ι Y)
  let b := Cofan.mk (∐ X) (Sigma.ι X)
  let α : Discrete.functor X ⟶ Discrete.functor Y := Discrete.natTrans (fun i => f i.as)
  have h := FinitaryExtensive.isVanKampen_finiteCoproducts (coproductIsCoproduct Y)
  exact ((h b α ((Sigma.desc fun i => f i ≫ Sigma.ι Y i)) (by ext j; simp [α, b])
    (NatTrans.Equifibered.of_discrete α)).mp ⟨coproductIsCoproduct X⟩) ⟨i⟩

private lemma property_sigmaMap (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P] {n : ℕ} {X Y : Fin n → Scheme.{u}}
    (f : ∀ i, X i ⟶ Y i) (hf : ∀ i, P (f i)) : P ((Sigma.desc fun i => f i ≫ Sigma.ι Y i)) := by
  apply IsZariskiLocalAtTarget.of_openCover (sigmaOpenCover Y)
  intro i
  let h := isPullback_sigmaMap f i
  exact (P.arrow_mk_iso_iff (Arrow.isoMk h.isoPullback (Iso.refl _)
    h.isoPullback_hom_snd)).mp (hf i)

private lemma isPullback_sigmaDesc_left {Y X : Scheme.{u}} (f : Y ⟶ X)
    {n : ℕ} {S : Fin n → Scheme.{u}} (g : ∀ i, S i ⟶ X) :
    IsPullback (Sigma.desc fun i => pullback.fst f (g i))
      (Sigma.desc fun i => pullback.snd f (g i) ≫ Sigma.ι S i) f (Sigma.desc g) := by
  have h := FinitaryPreExtensive.isUniversal_finiteCoproducts (coproductIsCoproduct S)
  exact h.isPullback_of_isColimit_left g (Sigma.desc g) f
    (fun i => pullback.fst f (g i)) (fun i => pullback.snd f (g i))
    (fun i => IsPullback.of_hasPullback f (g i)) (coproductIsCoproduct _) (by simp)

private lemma exists_thickening_finiteEtale_over_reduction
    {Y X : Scheme.{u}} (f : Y ⟶ X) {n : ℕ}
    (q : Y.nilradical.subscheme ⟶ X.nilradical.subscheme)
    (hq : q ≫ X.nilradical.subschemeι = Y.nilradical.subschemeι ≫ f)
    (e : Y.nilradical.subscheme ≅ ∐ fun _ : Fin n => X.nilradical.subscheme)
    (he : e.hom ≫ Sigma.desc (fun _ : Fin n => 𝟙 X.nilradical.subscheme) = q) :
    ∃ i : Y.nilradical.subscheme ⟶ pullback f X.nilradical.subschemeι,
      (IsClosedImmersion i ∧ Function.Surjective i) ∧
      IsFinite (i ≫ pullback.snd f X.nilradical.subschemeι) ∧
      Etale (i ≫ pullback.snd f X.nilradical.subschemeι) := by
  obtain ⟨i, hi, hiq⟩ := thickening_over_reduction f q hq
  refine ⟨i, hi, ?_, ?_⟩ <;> rw [hiq, ← he]
  · have : IsFinite (Sigma.desc (fun _ : Fin n => 𝟙 X.nilradical.subscheme)) :=
      inferInstance
    infer_instance
  · have : Etale (Sigma.desc (fun _ : Fin n => 𝟙 X.nilradical.subscheme)) :=
      IsZariskiLocalAtSource.sigmaDesc (P := @Etale.{u}) (fun _ => inferInstance)
    infer_instance

private lemma exists_thickening_finiteEtale_of_finite_family
    {Y X : Scheme.{u}} (f : Y ⟶ X) {n : ℕ}
    (S : Fin n → Scheme.{u}) [∀ i, IsAffine (S i)]
    (g : ∀ i, S i ⟶ X)
    (hg : (⋃ i, Set.range (g i).base) = Set.univ)
    (Z : Fin n → Scheme.{u}) (j : ∀ i, Z i ⟶ pullback f (g i))
    (hj : ∀ i, IsClosedImmersion (j i) ∧ Function.Surjective (j i))
    (hfin : ∀ i, IsFinite (j i ≫ pullback.snd f (g i)))
    (het : ∀ i, Etale (j i ≫ pullback.snd f (g i))) :
    ∃ (X' : Scheme.{u}) (_ : IsAffine X') (g : X' ⟶ X),
      Surjective g ∧ ∃ (Z' : Scheme.{u}) (i : Z' ⟶ pullback f g),
        (IsClosedImmersion i ∧ Function.Surjective i) ∧
        IsFinite (i ≫ pullback.snd f g) ∧ Etale (i ≫ pullback.snd f g) := by
  let hp := isPullback_sigmaDesc_left f g
  let e := hp.isoPullback
  let j' := (Sigma.desc fun i => j i ≫ Sigma.ι (fun i => pullback f (g i)) i) ≫ e.hom
  have hj' : IsClosedImmersion
      (Sigma.desc fun i => j i ≫ Sigma.ι (fun i => pullback f (g i)) i) :=
    property_sigmaMap _ j (fun i => (hj i).1)
  have hj's : Surjective ((Sigma.desc fun i => j i ≫ Sigma.ι (fun i => pullback f (g i)) i)) :=
    property_sigmaMap _ j (fun i => ⟨(hj i).2⟩)
  have hq : j' ≫ pullback.snd f (Sigma.desc g) =
      Sigma.desc (fun i => (j i ≫ pullback.snd f (g i)) ≫ Sigma.ι S i) := by
    dsimp [j', e]
    rw [Category.assoc, hp.isoPullback_hom_snd]
    apply Sigma.hom_ext
    intro i
    simp
  refine ⟨∐ S, inferInstance, Sigma.desc g,
    Surjective.sigmaDesc_of_union_range_eq_univ hg, ∐ Z, j', ?_, ?_, ?_⟩
  · exact ⟨inferInstance, (show Surjective j' from inferInstance).surj⟩
  · rw [hq]
    exact property_sigmaMap _ _ hfin
  · rw [hq]
    exact property_sigmaMap _ _ het

private lemma exists_thickening_finiteEtale_of_split_reductions
    {Y X : Scheme.{u}} (f : Y ⟶ X) {n : ℕ}
    (S : Fin n → Scheme.{u}) (s : ∀ i, S i ⟶ X) [∀ i, IsAffine (S i)]
    (hcover : (⋃ i, Set.range (s i).base) = Set.univ)
    (hsplit : ∀ i, ∃ (S' : Scheme.{u}) (g : S' ⟶ S i),
        Surjective g ∧ IsAffineHom g ∧
        ∃ (m : ℕ)
          (q : (pullback f (g ≫ s i)).nilradical.subscheme ⟶
            S'.nilradical.subscheme)
          (e : (pullback f (g ≫ s i)).nilradical.subscheme ≅
            ∐ (fun _ : Fin m ↦ S'.nilradical.subscheme)),
          q ≫ S'.nilradical.subschemeι =
              (pullback f (g ≫ s i)).nilradical.subschemeι ≫
                pullback.snd f (g ≫ s i) ∧
          e.hom ≫ Sigma.desc (fun _ : Fin m ↦ 𝟙 S'.nilradical.subscheme) = q) :
    ∃ (X' : Scheme.{u}) (_ : IsAffine X') (g : X' ⟶ X),
      Surjective g ∧ ∃ (Z' : Scheme.{u}) (i : Z' ⟶ pullback f g),
        (IsClosedImmersion i ∧ Function.Surjective i) ∧
        IsFinite (i ≫ pullback.snd f g) ∧ Etale (i ≫ pullback.snd f g) := by
  classical
  choose T g hg ha m q e hq he using hsplit
  let : ∀ i, IsAffineHom (g i) := ha
  let : ∀ i, IsAffine (T i) := fun i => isAffine_of_isAffineHom (g i)
  let A (i) := (T i).nilradical.subscheme
  have : ∀ i, IsAffine (A i) := fun i => isAffine_of_isAffineHom (T i).nilradical.subschemeι
  let h (i) : A i ⟶ X := (T i).nilradical.subschemeι ≫ (g i ≫ s i)
  let Z (i) := (pullback f (g i ≫ s i)).nilradical.subscheme
  have hlocal (i) : ∃ j : Z i ⟶ pullback f (h i),
      (IsClosedImmersion j ∧ Function.Surjective j) ∧
        IsFinite (j ≫ pullback.snd f (h i)) ∧ Etale (j ≫ pullback.snd f (h i)) := by
    obtain ⟨j, hj, hfin, het⟩ := exists_thickening_finiteEtale_over_reduction
      (pullback.snd f (g i ≫ s i)) (q i) (hq i) (e i) (he i)
    let a := pullbackLeftPullbackSndIso f (g i ≫ s i) (T i).nilradical.subschemeι
    have : IsClosedImmersion j := hj.1
    have : Surjective j := ⟨hj.2⟩
    refine ⟨j ≫ a.hom, ⟨inferInstance, (show Surjective (j ≫ a.hom) from inferInstance).surj⟩,
      ?_, ?_⟩
    · simpa only [a, h, Category.assoc, pullbackLeftPullbackSndIso_hom_snd] using hfin
    · simpa only [a, h, Category.assoc, pullbackLeftPullbackSndIso_hom_snd] using het
  choose j hj hfin het using hlocal
  apply exists_thickening_finiteEtale_of_finite_family f A h _ Z j hj hfin het
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨i, y, hy⟩ := Set.iUnion_eq_univ_iff.mp hcover x
  obtain ⟨z, hz⟩ := (hg i).surj y
  obtain ⟨w, hw⟩ := (Stacks.AffineClosedUnion.isThickening_subschemeι_nilradical (T i)).2 z
  refine Set.mem_iUnion.mpr ⟨i, w, ?_⟩
  show (s i) ((g i) ((T i).nilradical.subschemeι w)) = x
  rw [hw, hz]
  exact hy

private lemma isFinite_pullback_snd_of_isFinite_restrict
    {Y X : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) [IsFinite (f ∣_ U)] :
    IsFinite (pullback.snd f U.ι) := by
  let e := (isPullback_morphismRestrict f U).flip.isoPullback
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite) e.hom]
  show IsFinite ((isPullback_morphismRestrict f U).flip.isoPullback.hom ≫ _)
  rw [IsPullback.isoPullback_hom_snd]
  infer_instance

private lemma exists_affine_partition_isFinite_over_closed
    {Y X : Scheme.{u}} [IsAffine Y] [IsAffine X] [IsNoetherian X]
    (f : Y ⟶ X) [LocallyOfFiniteType f] [QuasiCompact f] [LocallyQuasiFinite f]
    (C : TopologicalSpace.Closeds X) :
    ∃ (J : Type) (_ : Fintype J) (T : J → Scheme.{u}) (t : ∀ j, T j ⟶ X),
      (∀ j, IsAffine (T j) ∧ IsReduced (T j) ∧ IsImmersion (t j) ∧
        IsLocallyClosed (Set.range (t j)) ∧ Topology.IsConstructible (Set.range (t j)) ∧
        IsFinite (pullback.snd f (t j))) ∧
      (Pairwise fun j k => Disjoint (Set.range (t j)) (Set.range (t k))) ∧
      (⋃ j, Set.range (t j)) = C := by
  classical
  induction C using WellFoundedLT.induction with
  | ind C ih =>
    by_cases hC : (C : Set X) = ∅
    · refine ⟨PEmpty, inferInstance, PEmpty.elim, fun j => j.elim, ?_, ?_, ?_⟩
      · exact fun j => j.elim
      · exact fun j => j.elim
      · simp [hC]
    let I := Scheme.IdealSheafData.vanishingIdeal C
    let Z := I.subscheme
    let i : Z ⟶ X := I.subschemeι
    have : IsAffine Z := isAffine_of_isAffineHom i
    have : IsReduced Z := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal C
    have hi : Set.range i = C := by
      rw [Scheme.IdealSheafData.range_subschemeι]
      exact Scheme.IdealSheafData.coe_support_vanishingIdeal C
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hC
    obtain ⟨z, hz⟩ := hi.symm ▸ hx
    let η := genericPoints.ofComponent
      ⟨irreducibleComponent z, irreducibleComponent_mem_irreducibleComponents z⟩
    let fZ := pullback.snd f i
    obtain ⟨V, hη, hV⟩ :=
      (finite_preimage_singleton_iff_exists_affine_open_isFinite_restrict
        fZ η.1 η.2).mp (fZ.finite_preimage_singleton η.1)
    let W : Scheme.{u} := V.1.toScheme
    let w : W ⟶ X := V.1.ι ≫ i
    have : IsAffine W := V.2
    have : IsReduced W := isReduced_of_isOpenImmersion V.1.ι
    have : IsImmersion w := by dsimp [w, i]; infer_instance
    have hw : IsFinite (pullback.snd f w) := by
      have : IsFinite (fZ ∣_ V.1) := hV
      have : IsFinite (pullback.snd fZ V.1.ι) :=
        isFinite_pullback_snd_of_isFinite_restrict fZ V.1
      let e := pullbackLeftPullbackSndIso f i V.1.ι
      rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite) e.hom]
      show IsFinite ((pullbackLeftPullbackSndIso f i V.1.ι).hom ≫ _)
      rw [pullbackLeftPullbackSndIso_hom_snd]
      infer_instance
    let D : TopologicalSpace.Closeds X :=
      ⟨i '' (V.1 : Set Z)ᶜ, i.isClosedEmbedding.isClosedMap _ V.1.isOpen.isClosed_compl⟩
    have hDC : D ≤ C := by
      rintro _ ⟨z, hz, rfl⟩
      show i z ∈ (C : Set X)
      rw [← hi]
      exact ⟨z, rfl⟩
    have hDi : i η.1 ∉ D := by
      rintro ⟨z, hz, heq⟩
      have heq' : z = η.1 := i.isClosedEmbedding.injective heq
      exact hz (heq' ▸ hη)
    have hlt : D < C := lt_of_le_of_ne hDC (by
      intro h
      apply hDi
      rw [h]
      show i η.1 ∈ (C : Set X)
      rw [← hi]
      exact ⟨η.1, rfl⟩)
    obtain ⟨J, hJ, T, t, ht, hd, hc⟩ := ih D hlt
    let := hJ
    have hdisj : ∀ j, Disjoint (Set.range w) (Set.range (t j)) := by
      intro j
      apply Set.disjoint_left.mpr
      rintro y ⟨a, ha⟩ ⟨b, hb⟩
      have hyD : y ∈ (D : Set X) := by
        rw [← hc]
        exact Set.mem_iUnion.mpr ⟨j, b, hb⟩
      obtain ⟨c, hcV, hcy⟩ := hyD
      have hac : (V.1.ι a : Z) = c := i.isClosedEmbedding.injective (ha.trans hcy.symm)
      exact hcV (hac ▸ a.2)
    let T' : Option J → Scheme.{u} := fun j => j.elim W T
    let t' : ∀ j, T' j ⟶ X := fun j => Option.rec w t j
    refine ⟨Option J, inferInstance, T', t', ?_, ?_, ?_⟩
    · intro j
      cases j with
      | none =>
        exact ⟨(show IsAffine W from inferInstance), (show IsReduced W from inferInstance),
          (show IsImmersion w from inferInstance), w.isLocallyClosed_range,
          isConstructible_of_isLocallyClosed_of_noetherian w.isLocallyClosed_range, hw⟩
      | some j => exact ht j
    · intro j k hjk
      cases j with
      | none =>
        cases k with
        | none => exact (hjk rfl).elim
        | some k => exact hdisj k
      | some j =>
        cases k with
        | none => exact (hdisj j).symm
        | some k => exact hd (fun h => hjk (congrArg some h))
    · ext y
      constructor
      · intro hy
        obtain ⟨j, z, hz⟩ := Set.mem_iUnion.mp hy
        cases j with
        | none =>
          rw [← hi]
          exact ⟨V.1.ι z, hz⟩
        | some j =>
          apply hDC
          show y ∈ (D : Set X)
          rw [← hc]
          exact Set.mem_iUnion.mpr ⟨j, z, hz⟩
      · intro hy
        rw [← hi] at hy
        obtain ⟨z, hz⟩ := hy
        by_cases hzV : z ∈ V.1
        · exact Set.mem_iUnion.mpr ⟨none, ⟨z, hzV⟩, hz⟩
        · have hyD : y ∈ (D : Set X) := ⟨z, hzV, hz⟩
          rw [← hc] at hyD
          obtain ⟨j, a, ha⟩ := Set.mem_iUnion.mp hyD
          exact Set.mem_iUnion.mpr ⟨some j, a, ha⟩

private lemma isClosedImmersion_sigmaι {J : Type} (T : J → Scheme.{u}) (j : J) :
    IsClosedImmersion (Sigma.ι T j) := by
  apply IsClosedImmersion.of_isPreimmersion
  rw [← isOpen_compl_iff]
  have hc : (Set.range (Sigma.ι T j))ᶜ =
      ⋃ k : {k : J // k ≠ j}, Set.range (Sigma.ι T k.1) := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, y, hy⟩ := (sigmaOpenCover T).exists_eq x
      have hkj : k ≠ j := by
        intro h
        subst k
        exact hx ⟨y, hy⟩
      exact Set.mem_iUnion.mpr ⟨⟨k, hkj⟩, y, hy⟩
    · rintro hx ⟨y, hy⟩
      obtain ⟨k, z, hz⟩ := Set.mem_iUnion.mp hx
      have h := (sigmaι_eq_iff T k.1 j z y).mp (hz.trans hy.symm)
      exact k.2 (congrArg Sigma.fst h)
  rw [hc]
  exact isOpen_iUnion (fun k => (Sigma.ι T k.1).isOpenEmbedding.isOpen_range)

private lemma exists_affine_partition_isFinite_family
    {X : Scheme.{u}} [IsAffine X] [IsNoetherian X]
    {I : Type} [Finite I] (Y : I → Scheme.{u}) [∀ i, IsAffine (Y i)]
    (f : ∀ i, Y i ⟶ X) [∀ i, LocallyOfFiniteType (f i)]
    [∀ i, LocallyQuasiFinite (f i)] :
    ∃ (J : Type) (_ : Fintype J) (T : J → Scheme.{u}) (t : ∀ j, T j ⟶ X),
      (∀ j, IsAffine (T j) ∧ IsReduced (T j) ∧ IsImmersion (t j) ∧
        IsLocallyClosed (Set.range (t j)) ∧ Topology.IsConstructible (Set.range (t j))) ∧
      (Pairwise fun j k => Disjoint (Set.range (t j)) (Set.range (t k))) ∧
      (⋃ j, Set.range (t j)) = Set.univ ∧
      ∀ i j, IsFinite (pullback.snd (f i) (t j)) := by
  let r := Sigma.desc f
  have : IsAffine (∐ Y) := inferInstance
  have : LocallyOfFiniteType r :=
    IsZariskiLocalAtSource.sigmaDesc (P := @LocallyOfFiniteType) (fun i => inferInstance)
  have : LocallyQuasiFinite r :=
    IsZariskiLocalAtSource.sigmaDesc (P := @LocallyQuasiFinite) (fun i => inferInstance)
  obtain ⟨J, hJ, T, t, ht, hd, hc⟩ := exists_affine_partition_isFinite_over_closed r ⊤
  refine ⟨J, hJ, T, t, fun j => ⟨(ht j).1, (ht j).2.1, (ht j).2.2.1,
    (ht j).2.2.2.1, (ht j).2.2.2.2.1⟩, hd, hc, ?_⟩
  intro i j
  have : IsFinite (pullback.snd r (t j)) := (ht j).2.2.2.2.2
  have : IsClosedImmersion (Sigma.ι Y i) := isClosedImmersion_sigmaι Y i
  have : IsClosedImmersion (closedImmersionBaseChange (Sigma.ι Y i) r (t j)) :=
    MorphismProperty.of_isPullback
      (isPullback_closedImmersionBaseChange (Sigma.ι Y i) r (t j)).flip
      (show IsClosedImmersion (Sigma.ι Y i) from inferInstance)
  have hfin : IsFinite (closedImmersionBaseChange (Sigma.ι Y i) r (t j) ≫
      pullback.snd r (t j)) := inferInstance
  rw [closedImmersionBaseChange_snd] at hfin
  change IsFinite (pullback.snd (Sigma.ι Y i ≫ Sigma.desc f) (t j)) at hfin
  rw [Sigma.ι_desc] at hfin
  exact hfin

private lemma isClopen_range_baseChange_of_finite_partition
    {X U S : Scheme.{u}} (g : U ⟶ X) [IsSeparated g] (h : S ⟶ X)
    {J : Type} [Finite J] (T : J → Scheme.{u}) (t : ∀ j, T j ⟶ U)
    [∀ j, IsImmersion (t j)]
    (hdisj : Pairwise fun j k => Disjoint (Set.range (t j)) (Set.range (t k)))
    (hcover : (⋃ j, Set.range (t j)) = Set.univ)
    (hfin : ∀ j, IsFinite (pullback.snd (t j ≫ g) h)) :
    ∀ j, IsClosedImmersion (closedImmersionBaseChange (t j) g h) ∧
      IsClopen (Set.range (closedImmersionBaseChange (t j) g h)) := by
  let r j := closedImmersionBaseChange (t j) g h
  have hri (j) : IsImmersion (r j) :=
    MorphismProperty.of_isPullback (isPullback_closedImmersionBaseChange (t j) g h).flip
      (show IsImmersion (t j) from inferInstance)
  have hrf (j) : IsFinite (r j) := by
    have : IsFinite (r j ≫ pullback.snd g h) := by
      rw [closedImmersionBaseChange_snd]
      exact hfin j
    exact IsFinite.of_comp (r j) (pullback.snd g h)
  have hrc (j) : IsClosed (Set.range (r j)) := (r j).isClosedMap.isClosed_range
  have hrd : Pairwise fun j k => Disjoint (Set.range (r j)) (Set.range (r k)) := by
    intro j k hjk
    simp only [r, range_closedImmersionBaseChange]
    exact (hdisj hjk).preimage _
  have hru : (⋃ j, Set.range (r j)) = Set.univ := by
    simp only [r, range_closedImmersionBaseChange, ← Set.preimage_iUnion, hcover,
      Set.preimage_univ]
  exact fun j => ⟨IsClosedImmersion.of_isPreimmersion (r j) (hrc j),
    isClopen_of_finite_closed_partition _ hrc hrd hru j⟩

private lemma ranges_closedImmersionBaseChange_cover_base
    {X U S : Scheme.{u}} (g : U ⟶ X) [Surjective g] (h : S ⟶ X)
    {J : Type} (T : J → Scheme.{u}) (t : ∀ j, T j ⟶ U)
    (hcover : (⋃ j, Set.range (t j)) = Set.univ) :
    (⋃ j, Set.range (closedImmersionBaseChange (t j) g h ≫ pullback.snd g h)) =
      Set.univ := by
  have hpb : Surjective (pullback.snd g h) :=
    MorphismProperty.pullback_snd _ _ (show Surjective g from inferInstance)
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨y, hy⟩ := hpb.surj x
  have hy' : y ∈ ⋃ j, Set.range (closedImmersionBaseChange (t j) g h) := by
    simpa only [range_closedImmersionBaseChange, ← Set.preimage_iUnion, hcover,
      Set.preimage_univ] using (Set.mem_univ y)
  obtain ⟨j, z, hz⟩ := Set.mem_iUnion.mp hy'
  refine Set.mem_iUnion.mpr ⟨j, z, ?_⟩
  show (pullback.snd g h) (closedImmersionBaseChange (t j) g h z) = x
  rw [hz]
  exact hy

private lemma finiteLocallyFree_restrictSource_of_isClosed
    {Y X : Scheme.{u}} (f : Y ⟶ X) [hf : Stacks.Morphisms.IsFiniteLocallyFree f]
    (U : Y.Opens) (hU : IsClosed (U : Set Y)) : Stacks.Morphisms.IsFiniteLocallyFree (U.ι ≫ f) := by
  obtain ⟨hfin, hflat, hfp⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation f).mp hf
  have : IsFinite f := hfin
  have : Flat f := hflat
  have : LocallyOfFinitePresentation f := hfp
  have : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion U.ι (by simpa using hU)
  exact (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mpr
    ⟨inferInstance, inferInstance, inferInstance⟩

private lemma exists_finiteLocallyFree_open_of_clopen_pullback_stratum
    {X U S V : Scheme.{u}} (g : U ⟶ X) [Stacks.Morphisms.IsFiniteLocallyFree g]
    (h : S ⟶ X) (t : V ⟶ U)
    (ht : IsClosedImmersion (closedImmersionBaseChange t g h))
    (ho : IsClopen (Set.range (closedImmersionBaseChange t g h))) :
    ∃ (W : (pullback g h).Opens)
      (a : pullback (t ≫ g) h ⟶ W.toScheme),
      Stacks.Thickenings.IsThickening a ∧ a ≫ W.ι = closedImmersionBaseChange t g h ∧
      Stacks.Morphisms.IsFiniteLocallyFree (W.ι ≫ pullback.snd g h) := by
  have : IsClosedImmersion (closedImmersionBaseChange t g h) := ht
  let W : (pullback g h).Opens := ⟨Set.range (closedImmersionBaseChange t g h), ho.2⟩
  obtain ⟨a, ha, hfac⟩ := exists_thickening_onto_open_range (closedImmersionBaseChange t g h) ho.2
  have : Stacks.Morphisms.IsFiniteLocallyFree (pullback.snd g h) :=
    MorphismProperty.pullback_snd _ _
      (show Stacks.Morphisms.IsFiniteLocallyFree g from inferInstance)
  exact ⟨W, a, ha, hfac, finiteLocallyFree_restrictSource_of_isClosed (pullback.snd g h) W ho.1⟩

private lemma exists_finiteLocallyFree_open_cover_of_partition
    {X U S : Scheme.{u}} (g : U ⟶ X)
    [Stacks.Morphisms.IsFiniteLocallyFree g] [Surjective g] (h : S ⟶ X)
    {J : Type} [Finite J] (T : J → Scheme.{u}) (t : ∀ j, T j ⟶ U)
    [∀ j, IsImmersion (t j)]
    (hdisj : Pairwise fun i j => Disjoint (Set.range (t i)) (Set.range (t j)))
    (hcover : (⋃ j, Set.range (t j)) = Set.univ)
    (hfin : ∀ j, IsFinite (pullback.snd (t j ≫ g) h)) :
    ∃ W : J → (pullback g h).Opens,
      (∀ j, ∃ a : pullback (t j ≫ g) h ⟶ (W j).toScheme,
        Stacks.Thickenings.IsThickening a ∧
        a ≫ (W j).ι = closedImmersionBaseChange (t j) g h ∧
        Stacks.Morphisms.IsFiniteLocallyFree ((W j).ι ≫ pullback.snd g h)) ∧
      (⋃ j, Set.range ((W j).ι ≫ pullback.snd g h)) = Set.univ := by
  have : IsFinite g :=
    ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation g).mp
      (show Stacks.Morphisms.IsFiniteLocallyFree g from inferInstance)).1
  have hcl := isClopen_range_baseChange_of_finite_partition g h T t hdisj hcover hfin
  choose W a ha hfac hfree using fun j =>
    exists_finiteLocallyFree_open_of_clopen_pullback_stratum g h (t j) (hcl j).1 (hcl j).2
  refine ⟨W, fun j => ⟨a j, ha j, hfac j, hfree j⟩, ?_⟩
  apply Set.eq_univ_of_forall
  intro x
  have hx : x ∈ ⋃ j, Set.range
      (closedImmersionBaseChange (t j) g h ≫ pullback.snd g h) := by
    rw [ranges_closedImmersionBaseChange_cover_base g h T t hcover]
    trivial
  obtain ⟨j, y, hy⟩ := Set.mem_iUnion.mp hx
  refine Set.mem_iUnion.mpr ⟨j, a j y, ?_⟩
  show ((a j ≫ (W j).ι) ≫ pullback.snd g h) y = x
  rw [hfac j]
  exact hy

private lemma exists_affine_partition_subordinate_to_finite_cover
    {X : Scheme.{u}} [TopologicalSpace.NoetherianSpace X] {n : ℕ} [Nonempty (Fin n)]
    (C : Fin n → Set X) (hC : ∀ i, Topology.IsConstructible (C i))
    (hcover : (⋃ i, C i) = Set.univ) :
    ∃ (J : Type) (_ : Fintype J) (S : J → Scheme.{u}) (s : ∀ j, S j ⟶ X),
      (∀ j, IsAffine (S j) ∧ IsReduced (S j) ∧ IsImmersion (s j) ∧
        IsLocallyClosed (Set.range (s j)) ∧ Topology.IsConstructible (Set.range (s j))) ∧
      (Pairwise fun j k => Disjoint (Set.range (s j)) (Set.range (s k))) ∧
      (⋃ j, Set.range (s j)) = Set.univ ∧ ∀ j, ∃ i, Set.range (s j) ⊆ C i := by
  classical
  obtain ⟨m, T, hT, hd, hc, hm, _⟩ := finiteSectionLoci_refined_constancy C
    (fun _ _ => Set.univ) hC (fun _ _ => Topology.IsConstructible.univ)
  obtain ⟨J, hJ, S, s, hs, hsd, hsc, href⟩ :=
    exists_finite_affine_refinement_of_noetherian T (fun j => (hT j).1) hd hc
  refine ⟨J, hJ, S, s, hs, hsd, hsc, ?_⟩
  intro j
  obtain ⟨k, hk⟩ := href j
  by_cases hj : (Set.range (s j)).Nonempty
  · obtain ⟨x, hx⟩ := hj
    obtain ⟨i, hi⟩ := Set.iUnion_eq_univ_iff.mp hcover x
    exact ⟨i, fun y hy => (hm i k x y (hk hx) (hk hy)).mp hi⟩
  · exact ⟨Classical.arbitrary _, fun x hx => (hj ⟨x, hx⟩).elim⟩

private lemma exists_affine_partition_with_surjective_finiteLocallyFree_pullbacks
    {X : Scheme.{u}} [TopologicalSpace.NoetherianSpace X]
    {n : ℕ} [Nonempty (Fin n)] (U : Fin n → Scheme.{u}) (g : ∀ i, U i ⟶ X)
    [∀ i, Stacks.Morphisms.IsFiniteLocallyFree (g i)]
    (hcover : (⋃ i, Set.range (g i)) = Set.univ) :
    ∃ (J : Type) (_ : Fintype J) (S : J → Scheme.{u}) (s : ∀ j, S j ⟶ X),
      (∀ j, IsAffine (S j) ∧ IsReduced (S j) ∧ IsImmersion (s j) ∧
        IsLocallyClosed (Set.range (s j)) ∧ Topology.IsConstructible (Set.range (s j))) ∧
      (Pairwise fun j k => Disjoint (Set.range (s j)) (Set.range (s k))) ∧
      (⋃ j, Set.range (s j)) = Set.univ ∧
      ∀ j, ∃ i, Surjective (pullback.snd (g i) (s j)) ∧
        Stacks.Morphisms.IsFiniteLocallyFree (pullback.snd (g i) (s j)) := by
  have hfin (i) : IsFinite (g i) :=
    ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mp
      (show Stacks.Morphisms.IsFiniteLocallyFree (g i) from inferInstance)).1
  have hC (i) : Topology.IsConstructible (Set.range (g i)) :=
    isConstructible_of_isLocallyClosed_of_noetherian
      (g i).isClosedMap.isClosed_range.isLocallyClosed
  obtain ⟨J, hJ, S, s, hs, hd, hc, href⟩ :=
    exists_affine_partition_subordinate_to_finite_cover (fun i => Set.range (g i)) hC hcover
  refine ⟨J, hJ, S, s, hs, hd, hc, ?_⟩
  intro j
  obtain ⟨i, hi⟩ := href j
  exact ⟨i, surjective_pullback_snd_of_range_subset (g i) (s j) hi,
    MorphismProperty.pullback_snd _ _
      (show Stacks.Morphisms.IsFiniteLocallyFree (g i) from inferInstance)⟩

private lemma exists_affine_stratification_after_finiteLocallyFree_cover
    {Y X : Scheme.{u}} [IsAffine X] [IsNoetherian X] (f : Y ⟶ X) [IsFinite f] :
    ∃ (X' : Scheme.{u}) (g : X' ⟶ X),
      IsAffine X' ∧ Surjective g ∧ Stacks.Morphisms.IsFiniteLocallyFree g ∧
      ∃ (J : Type) (_ : Fintype J) (T : J → Scheme.{u}) (t : ∀ j, T j ⟶ X'),
        (∀ j, IsAffine (T j) ∧ IsReduced (T j) ∧ IsImmersion (t j) ∧
          IsLocallyClosed (Set.range (t j)) ∧ Topology.IsConstructible (Set.range (t j))) ∧
        (Pairwise fun j k => Disjoint (Set.range (t j)) (Set.range (t k))) ∧
        (⋃ j, Set.range (t j)) = Set.univ ∧
        ∀ j, ∃ (m : ℕ)
          (q : (pullback f (t j ≫ g)).nilradical.subscheme ⟶ (T j).nilradical.subscheme)
          (e : (pullback f (t j ≫ g)).nilradical.subscheme ≅
            ∐ fun _ : Fin m => (T j).nilradical.subscheme),
          q ≫ (T j).nilradical.subschemeι =
            (pullback f (t j ≫ g)).nilradical.subschemeι ≫ pullback.snd f (t j ≫ g) ∧
          e.hom ≫ Sigma.desc (fun _ : Fin m => 𝟙 (T j).nilradical.subscheme) = q := by
  obtain ⟨X', g, hg, hfree, _, _, Z, p, i, hi, hip, hp, n, s, hs, hcover⟩ :=
    Stacks.Morphisms.exists_finiteLocallyFree_cover_closedImmersion f
  have : Stacks.Morphisms.IsFiniteLocallyFree g := hfree
  have : IsAffine X' := isAffine_of_isAffineHom g
  have : IsFinite g :=
    ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation g).mp
      hfree).1
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian g
  have : IsNoetherian X' := ⟨⟩
  have : IsClosedImmersion i := hi
  have : ∀ j, IsClosedImmersion (s j) := fun j => (hs j).1
  have hc : (⋃ j, Set.range (s j)) = Set.univ :=
    Set.eq_univ_of_forall fun z => Set.mem_iUnion.mpr (hcover z)
  obtain ⟨J, hJ, T, t, ht, hd, hc, he⟩ :=
    exists_affine_stratification_of_closed_sections i p s (fun j => (hs j).2) hc
  refine ⟨X', g, inferInstance, hg, hfree, J, hJ, T, t, ht, hd, hc, ?_⟩
  intro j
  have : IsReduced (T j) := (ht j).2.1
  have he := he j
  rw [hip] at he
  obtain ⟨m, e, he⟩ := he
  obtain ⟨e', he'⟩ := exists_split_of_iso_square
    (reductionIso (pullbackLeftPullbackSndIso f g (t j))) (Iso.refl _)
    ((pullback f (t j ≫ g)).nilradical.subschemeι ≫ pullback.snd f (t j ≫ g)) _
    (by
      rw [Iso.refl_hom, Category.comp_id, reductionIso_hom, ← Category.assoc,
        reductionMap_comp_subschemeι, Category.assoc, pullbackLeftPullbackSndIso_hom_snd])
    e he
  obtain ⟨q, e'', hq, he''⟩ := exists_split_reduction_of_reduced_base
    (pullback.snd f (t j ≫ g)) e' he'
  exact ⟨m, q, e'', hq, he''⟩

private lemma exists_split_reduction_after_thickening
    {Y X T : Scheme.{u}} (f : Y ⟶ X) (h : T ⟶ X)
    (hh : Stacks.Thickenings.IsThickening h) {n : ℕ}
    (e : Y.nilradical.subscheme ≅ ∐ fun _ : Fin n => X.nilradical.subscheme)
    (he : e.hom ≫ Sigma.desc (fun _ : Fin n => 𝟙 X.nilradical.subscheme) =
      reductionMap f) :
    ∃ a : (pullback f h).nilradical.subscheme ≅
        ∐ fun _ : Fin n => T.nilradical.subscheme,
      a.hom ≫ Sigma.desc (fun _ : Fin n => 𝟙 T.nilradical.subscheme) =
        reductionMap (pullback.snd f h) := by
  have hf : Stacks.Thickenings.IsThickening (pullback.fst f h) :=
    MorphismProperty.pullback_fst _ _ hh
  have : IsIso (reductionMap h) := isIso_reductionMap_of_isThickening h hh
  have : IsIso (reductionMap (pullback.fst f h)) :=
    isIso_reductionMap_of_isThickening _ hf
  exact exists_split_of_iso_square (asIso (reductionMap (pullback.fst f h))).symm
    (asIso (reductionMap h)).symm _ _
    (by simp [IsIso.inv_comp_eq, reductionMap_comp, pullback.condition]) e he

private lemma exists_split_reduction_after_baseChange_general
    {Y X T : Scheme.{u}} (f : Y ⟶ X) (h : T ⟶ X) {n : ℕ}
    (q : Y.nilradical.subscheme ⟶ X.nilradical.subscheme)
    (e : Y.nilradical.subscheme ≅ ∐ fun _ : Fin n => X.nilradical.subscheme)
    (hq : q ≫ X.nilradical.subschemeι = Y.nilradical.subschemeι ≫ f)
    (he : e.hom ≫ Sigma.desc (fun _ : Fin n => 𝟙 X.nilradical.subscheme) = q) :
    ∃ (m : ℕ)
      (q' : (pullback f h).nilradical.subscheme ⟶ T.nilradical.subscheme)
      (e' : (pullback f h).nilradical.subscheme ≅
        ∐ fun _ : Fin m => T.nilradical.subscheme),
      q' ≫ T.nilradical.subschemeι =
        (pullback f h).nilradical.subschemeι ≫ pullback.snd f h ∧
      e'.hom ≫ Sigma.desc (fun _ : Fin m => 𝟙 T.nilradical.subscheme) = q' := by
  have hq' := eq_reductionMap_of_comp_subschemeι _ q hq
  obtain ⟨a, ha⟩ := exists_split_reduction_after_thickening f
    X.nilradical.subschemeι (Stacks.AffineClosedUnion.isThickening_subschemeι_nilradical X)
    e (he.trans hq')
  have : IsReduced X.nilradical.subscheme := X.isReduced_reduction
  obtain ⟨b, hb⟩ := split_reduction_over_reduced_base
    (pullback.snd f X.nilradical.subschemeι) _ a (reductionMap_comp_subschemeι _) ha
  obtain ⟨m, c, hc⟩ := exists_split_reduction_after_baseChange_of_pullback
    f X.nilradical.subschemeι (reductionMap h) b hb
  have hcomp : reductionMap h ≫ X.nilradical.subschemeι =
      T.nilradical.subschemeι ≫ h := reductionMap_comp_subschemeι h
  have hd : ∃ (k : ℕ)
      (d : (pullback f (T.nilradical.subschemeι ≫ h)).nilradical.subscheme ≅
        ∐ fun _ : Fin k => T.nilradical.subscheme.nilradical.subscheme),
      d.hom ≫ Sigma.desc (fun _ : Fin k =>
        𝟙 T.nilradical.subscheme.nilradical.subscheme) =
        reductionMap (pullback.snd f (T.nilradical.subschemeι ≫ h)) := by
    rw [← hcomp]
    exact ⟨m, c, hc⟩
  obtain ⟨m, c, hc⟩ := hd
  obtain ⟨q', e', hq', he'⟩ :=
    exists_split_reduction_of_thickening_after_pullback f h
      T.nilradical.subschemeι (Stacks.AffineClosedUnion.isThickening_subschemeι_nilradical T)
      (reductionMap (pullback.snd f (T.nilradical.subschemeι ≫ h))) c
      (reductionMap_comp_subschemeι _) hc
  exact ⟨m, q', e', hq', he'⟩

private lemma exists_split_reduction_after_baseChange_of_split_pullback_general
    {Y X T V : Scheme.{u}} (f : Y ⟶ X) (g : T ⟶ X)
    (h : V ⟶ T) {n : ℕ}
    (q : (pullback f g).nilradical.subscheme ⟶ T.nilradical.subscheme)
    (e : (pullback f g).nilradical.subscheme ≅
      ∐ fun _ : Fin n => T.nilradical.subscheme)
    (hq : q ≫ T.nilradical.subschemeι =
      (pullback f g).nilradical.subschemeι ≫ pullback.snd f g)
    (he : e.hom ≫ Sigma.desc (fun _ : Fin n => 𝟙 T.nilradical.subscheme) = q) :
    ∃ (m : ℕ)
      (q' : (pullback f (h ≫ g)).nilradical.subscheme ⟶ V.nilradical.subscheme)
      (e' : (pullback f (h ≫ g)).nilradical.subscheme ≅
        ∐ fun _ : Fin m => V.nilradical.subscheme),
      q' ≫ V.nilradical.subschemeι =
        (pullback f (h ≫ g)).nilradical.subschemeι ≫ pullback.snd f (h ≫ g) ∧
      e'.hom ≫ Sigma.desc (fun _ : Fin m => 𝟙 V.nilradical.subscheme) = q' := by
  obtain ⟨m, q', e', hq', he'⟩ :=
    exists_split_reduction_after_baseChange_general (pullback.snd f g) h q e hq he
  obtain ⟨q'', e'', hq'', he''⟩ := split_reduction_pullback_composite f g h q' e' hq' he'
  exact ⟨m, q'', e'', hq'', he''⟩

private lemma exists_affine_partition_with_surjective_finiteLocallyFree_pullbacks_finite
    {X : Scheme.{u}} [TopologicalSpace.NoetherianSpace X]
    {I : Type} [Finite I] [Nonempty I]
    (U : I → Scheme.{u}) (g : ∀ i, U i ⟶ X)
    [∀ i, Stacks.Morphisms.IsFiniteLocallyFree (g i)]
    (hcover : (⋃ i, Set.range (g i)) = Set.univ) :
    ∃ (J : Type) (_ : Fintype J) (S : J → Scheme.{u}) (s : ∀ j, S j ⟶ X),
      (∀ j, IsAffine (S j) ∧ IsReduced (S j) ∧ IsImmersion (s j) ∧
        IsLocallyClosed (Set.range (s j)) ∧ Topology.IsConstructible (Set.range (s j))) ∧
      (Pairwise fun j k => Disjoint (Set.range (s j)) (Set.range (s k))) ∧
      (⋃ j, Set.range (s j)) = Set.univ ∧
      ∀ j, ∃ i, Surjective (pullback.snd (g i) (s j)) ∧
        Stacks.Morphisms.IsFiniteLocallyFree (pullback.snd (g i) (s j)) := by
  let _ : Fintype I := Fintype.ofFinite I
  let e := Fintype.equivFin I
  have hn : Nonempty (Fin (Fintype.card I)) := Equiv.nonempty_congr e |>.mp inferInstance
  let V : Fin (Fintype.card I) → Scheme.{u} := fun k => U (e.symm k)
  let v : ∀ k, V k ⟶ X := fun k => g (e.symm k)
  have : ∀ k, Stacks.Morphisms.IsFiniteLocallyFree (v k) := fun _ => inferInstance
  have hc : (⋃ k, Set.range (v k)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, hi⟩ := Set.iUnion_eq_univ_iff.mp hcover x
    have hei : e.symm (e i) = i := e.symm_apply_apply i
    refine Set.mem_iUnion.mpr ⟨e i, ?_⟩
    show x ∈ Set.range (g (e.symm (e i)))
    rw [hei]
    exact hi
  obtain ⟨J, hJ, S, s, hs, hd, hsc, hg⟩ :=
    exists_affine_partition_with_surjective_finiteLocallyFree_pullbacks V v hc
  refine ⟨J, hJ, S, s, hs, hd, hsc, ?_⟩
  intro j
  obtain ⟨k, hk⟩ := hg j
  exact ⟨e.symm k, hk⟩

private lemma exists_split_reduction_on_clopen_piece
    {Y X U T S : Scheme.{u}}
    (f : Y ⟶ X) (g : U ⟶ X) (t : T ⟶ U) (h : S ⟶ X)
    (W : (pullback g h).Opens)
    (a : pullback (t ≫ g) h ⟶ W.toScheme)
    (ha : Stacks.Thickenings.IsThickening a)
    (hfac : a ≫ W.ι = closedImmersionBaseChange t g h)
    {n : ℕ}
    (q : (pullback f (t ≫ g)).nilradical.subscheme ⟶ T.nilradical.subscheme)
    (e : (pullback f (t ≫ g)).nilradical.subscheme ≅
      ∐ fun _ : Fin n => T.nilradical.subscheme)
    (hq : q ≫ T.nilradical.subschemeι =
      (pullback f (t ≫ g)).nilradical.subschemeι ≫ pullback.snd f (t ≫ g))
    (he : e.hom ≫ Sigma.desc (fun _ : Fin n => 𝟙 T.nilradical.subscheme) = q) :
    ∃ (m : ℕ)
      (q' : (pullback f (W.ι ≫ pullback.snd g h ≫ h)).nilradical.subscheme ⟶
        W.toScheme.nilradical.subscheme)
      (e' : (pullback f (W.ι ≫ pullback.snd g h ≫ h)).nilradical.subscheme ≅
        ∐ fun _ : Fin m => W.toScheme.nilradical.subscheme),
      q' ≫ W.toScheme.nilradical.subschemeι =
        (pullback f (W.ι ≫ pullback.snd g h ≫ h)).nilradical.subschemeι ≫
          pullback.snd f (W.ι ≫ pullback.snd g h ≫ h) ∧
      e'.hom ≫ Sigma.desc (fun _ : Fin m => 𝟙 W.toScheme.nilradical.subscheme) = q' := by
  let b := pullback.fst (t ≫ g) h
  obtain ⟨m, qP, eP, hqP, heP⟩ :=
    exists_split_reduction_after_baseChange_of_split_pullback_general f (t ≫ g) b
      q e hq he
  have hb : b ≫ (t ≫ g) = a ≫ (W.ι ≫ pullback.snd g h ≫ h) := by
    rw [pullback.condition, ← Category.assoc a, hfac, ← Category.assoc,
      closedImmersionBaseChange_snd]
  have hsplit : ∃ (m : ℕ)
      (q' : (pullback f (a ≫ (W.ι ≫ pullback.snd g h ≫ h))).nilradical.subscheme ⟶
        (pullback (t ≫ g) h).nilradical.subscheme)
      (e' : (pullback f (a ≫ (W.ι ≫ pullback.snd g h ≫ h))).nilradical.subscheme ≅
        ∐ fun _ : Fin m => (pullback (t ≫ g) h).nilradical.subscheme),
      q' ≫ (pullback (t ≫ g) h).nilradical.subschemeι =
        (pullback f (a ≫ (W.ι ≫ pullback.snd g h ≫ h))).nilradical.subschemeι ≫
          pullback.snd f (a ≫ (W.ι ≫ pullback.snd g h ≫ h)) ∧
      e'.hom ≫ Sigma.desc (fun _ : Fin m =>
        𝟙 (pullback (t ≫ g) h).nilradical.subscheme) = q' := by
    rw [← hb]
    exact ⟨m, qP, eP, hqP, heP⟩
  obtain ⟨m, qP', eP', hqP', heP'⟩ := hsplit
  obtain ⟨q', e', hq', he'⟩ := exists_split_reduction_of_thickening_after_pullback f
    (W.ι ≫ pullback.snd g h ≫ h) a ha qP' eP' hqP' heP'
  exact ⟨m, q', e', hq', he'⟩

private lemma exists_split_stratification_below_finite_cover
    {Y X U S : Scheme.{u}} (f : Y ⟶ X) (g : U ⟶ X)
    [Stacks.Morphisms.IsFiniteLocallyFree g] [Surjective g] [IsFinite g]
    (h : S ⟶ X) [TopologicalSpace.NoetherianSpace S]
    {I : Type} [Finite I] [Nonempty I]
    (T : I → Scheme.{u}) (t : ∀ i, T i ⟶ U)
    [∀ i, IsImmersion (t i)] [∀ i, IsReduced (T i)]
    (hd : Pairwise fun i j => Disjoint (Set.range (t i)) (Set.range (t j)))
    (hc : (⋃ i, Set.range (t i)) = Set.univ)
    (hfin : ∀ i, IsFinite (pullback.snd (t i ≫ g) h))
    (hsplit : ∀ i, ∃ (m : ℕ)
      (q : (pullback f (t i ≫ g)).nilradical.subscheme ⟶ (T i).nilradical.subscheme)
      (e : (pullback f (t i ≫ g)).nilradical.subscheme ≅
        ∐ fun _ : Fin m => (T i).nilradical.subscheme),
      q ≫ (T i).nilradical.subschemeι =
        (pullback f (t i ≫ g)).nilradical.subschemeι ≫ pullback.snd f (t i ≫ g) ∧
      e.hom ≫ Sigma.desc (fun _ : Fin m => 𝟙 (T i).nilradical.subscheme) = q) :
    ∃ (J : Type) (_ : Fintype J) (V : J → Scheme.{u}) (v : ∀ j, V j ⟶ S),
      (∀ j, IsAffine (V j) ∧ IsReduced (V j) ∧ IsImmersion (v j) ∧
        IsLocallyClosed (Set.range (v j)) ∧ Topology.IsConstructible (Set.range (v j))) ∧
      (Pairwise fun j k => Disjoint (Set.range (v j)) (Set.range (v k))) ∧
      (⋃ j, Set.range (v j)) = Set.univ ∧
      ∀ j, ∃ (V' : Scheme.{u}) (a : V' ⟶ V j),
        Surjective a ∧ Stacks.Morphisms.IsFiniteLocallyFree a ∧
        ∃ (m : ℕ)
          (q : (pullback f (a ≫ v j ≫ h)).nilradical.subscheme ⟶
            V'.nilradical.subscheme)
          (e : (pullback f (a ≫ v j ≫ h)).nilradical.subscheme ≅
            ∐ fun _ : Fin m => V'.nilradical.subscheme),
          q ≫ V'.nilradical.subschemeι =
            (pullback f (a ≫ v j ≫ h)).nilradical.subschemeι ≫
              pullback.snd f (a ≫ v j ≫ h) ∧
          e.hom ≫ Sigma.desc (fun _ : Fin m => 𝟙 V'.nilradical.subscheme) = q := by
  obtain ⟨W, hW, hcover⟩ :=
    exists_finiteLocallyFree_open_cover_of_partition g h T t hd hc hfin
  let a (i : I) : (W i).toScheme ⟶ S := (W i).ι ≫ pullback.snd g h
  have : ∀ i, Stacks.Morphisms.IsFiniteLocallyFree (a i) := by
    intro i
    obtain ⟨_, _, _, hfree⟩ := hW i
    exact hfree
  have hcW : (⋃ i, Set.range (a i)) = Set.univ := hcover
  obtain ⟨J, hJ, V, v, hv, hdV, hcV, hchoice⟩ :=
    exists_affine_partition_with_surjective_finiteLocallyFree_pullbacks_finite
      (fun i => (W i).toScheme) a hcW
  refine ⟨J, hJ, V, v, hv, hdV, hcV, ?_⟩
  intro j
  obtain ⟨i, hsurj, hfree⟩ := hchoice j
  obtain ⟨b, hb, hfac, _⟩ := hW i
  obtain ⟨m, q, e, hq, he⟩ := hsplit i
  obtain ⟨mW, qW, eW, hqW, heW⟩ :=
    exists_split_reduction_on_clopen_piece f g (t i) h (W i) b hb hfac q e hq he
  have hdata : ∃ (k : ℕ)
      (r : (pullback f (a i ≫ h)).nilradical.subscheme ⟶
        (W i).toScheme.nilradical.subscheme)
      (d : (pullback f (a i ≫ h)).nilradical.subscheme ≅
        ∐ fun _ : Fin k => (W i).toScheme.nilradical.subscheme),
      r ≫ (W i).toScheme.nilradical.subschemeι =
        (pullback f (a i ≫ h)).nilradical.subschemeι ≫ pullback.snd f (a i ≫ h) ∧
      d.hom ≫ Sigma.desc (fun _ : Fin k => 𝟙 (W i).toScheme.nilradical.subscheme) = r := by
    simpa only [a, Category.assoc] using ⟨mW, qW, eW, hqW, heW⟩
  obtain ⟨mW, qW, eW, hqW, heW⟩ := hdata
  let r := pullback.fst (a i) (v j)
  obtain ⟨m', q', e', hq', he'⟩ :=
    exists_split_reduction_after_baseChange_of_split_pullback_general f
      (a i ≫ h) r qW eW hqW heW
  have hmap : r ≫ (a i ≫ h) = pullback.snd (a i) (v j) ≫ v j ≫ h := by
    exact pullback.condition_assoc h
  refine ⟨pullback (a i) (v j), pullback.snd (a i) (v j), hsurj, hfree, ?_⟩
  rw [← hmap]
  exact ⟨m', q', e', hq', he'⟩

private lemma exists_split_stratification_of_finite
    {Y X : Scheme.{u}} [IsAffine X] [IsNoetherian X]
    (f : Y ⟶ X) [IsFinite f] :
    ∃ (J : Type) (_ : Fintype J) (V : J → Scheme.{u}) (v : ∀ j, V j ⟶ X),
      (∀ j, IsAffine (V j) ∧ IsReduced (V j) ∧ IsImmersion (v j) ∧
        IsLocallyClosed (Set.range (v j)) ∧ Topology.IsConstructible (Set.range (v j))) ∧
      (Pairwise fun j k => Disjoint (Set.range (v j)) (Set.range (v k))) ∧
      (⋃ j, Set.range (v j)) = Set.univ ∧
      ∀ j, ∃ (V' : Scheme.{u}) (a : V' ⟶ V j),
        Surjective a ∧ Stacks.Morphisms.IsFiniteLocallyFree a ∧
        ∃ (m : ℕ)
          (q : (pullback f (a ≫ v j)).nilradical.subscheme ⟶
            V'.nilradical.subscheme)
          (e : (pullback f (a ≫ v j)).nilradical.subscheme ≅
            ∐ fun _ : Fin m => V'.nilradical.subscheme),
          q ≫ V'.nilradical.subschemeι =
            (pullback f (a ≫ v j)).nilradical.subschemeι ≫
              pullback.snd f (a ≫ v j) ∧
          e.hom ≫ Sigma.desc (fun _ : Fin m => 𝟙 V'.nilradical.subscheme) = q := by
  classical
  obtain ⟨U, g, hU, hg, hfree, I, hI, T, t, hT, hd, hc, hsplit⟩ :=
    exists_affine_stratification_after_finiteLocallyFree_cover f
  by_cases hnonempty : Nonempty I
  · let := hI
    have : Nonempty I := hnonempty
    have : Stacks.Morphisms.IsFiniteLocallyFree g := hfree
    have : Surjective g := hg
    have : IsFinite g :=
      ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation g).mp
        hfree).1
    have : ∀ i, IsImmersion (t i) := fun i => (hT i).2.2.1
    have : ∀ i, IsReduced (T i) := fun i => (hT i).2.1
    have : ∀ i, IsAffine (T i) := fun i => (hT i).1
    have : ∀ i, LocallyOfFiniteType (t i ≫ g) := fun _ => inferInstance
    have : ∀ i, LocallyQuasiFinite (t i ≫ g) := fun _ => inferInstance
    obtain ⟨K, hK, S, s, hS, hdS, hcS, hfin⟩ :=
      exists_affine_partition_isFinite_family T (fun i => t i ≫ g)
    let := hK
    have : ∀ k, IsImmersion (s k) := fun k => (hS k).2.2.1
    have hbelow (k : K) := by
      let : TopologicalSpace.NoetherianSpace (S k) :=
        (s k).isEmbedding.isInducing.noetherianSpace
      exact exists_split_stratification_below_finite_cover f g (s k) T t hd hc
        (fun i => hfin i k) hsplit
    choose L hL V v hV hdV hcV hchoice using hbelow
    let : ∀ k, Fintype (L k) := hL
    let W (j : Σ k, L k) := V j.1 j.2
    let w (j : Σ k, L k) : W j ⟶ X := v j.1 j.2 ≫ s j.1
    have hp := partition_comp_of_partitions s v hV hdS hcS hdV hcV
    refine ⟨Σ k, L k, inferInstance, W, w, hp.1, hp.2.1, hp.2.2, ?_⟩
    intro j
    obtain ⟨A, a, ha, hfreeA, m, q, e, hq, he⟩ := hchoice j.1 j.2
    refine ⟨A, a, ha, hfreeA, ?_⟩
    have hmap : a ≫ w j = a ≫ v j.1 j.2 ≫ s j.1 := by
      rfl
    rw [hmap]
    exact ⟨m, q, e, hq, he⟩
  · let : IsEmpty I := not_nonempty_iff.mp hnonempty
    have : IsEmpty U := ⟨fun x => by
      obtain ⟨i, _⟩ := Set.iUnion_eq_univ_iff.mp hc x
      exact isEmptyElim i⟩
    have : IsEmpty X := ⟨fun x => by
      obtain ⟨u, _⟩ := hg.surj x
      exact isEmptyElim u⟩
    refine ⟨PEmpty, inferInstance, PEmpty.elim, fun j => j.elim,
      fun j => j.elim, fun j => j.elim, ?_, fun j => j.elim⟩
    exact Set.eq_univ_of_forall fun x => isEmptyElim x

private lemma exists_split_stratification_of_noetherian
    {Y X : Scheme.{u}} [IsAffine Y] [IsAffine X] [IsNoetherian X]
    (f : Y ⟶ X) [LocallyOfFiniteType f] [LocallyQuasiFinite f] :
    ∃ (J : Type) (_ : Fintype J) (V : J → Scheme.{u}) (v : ∀ j, V j ⟶ X),
      (∀ j, IsAffine (V j) ∧ IsReduced (V j) ∧ IsImmersion (v j) ∧
        IsLocallyClosed (Set.range (v j)) ∧ Topology.IsConstructible (Set.range (v j))) ∧
      (Pairwise fun j k => Disjoint (Set.range (v j)) (Set.range (v k))) ∧
      (⋃ j, Set.range (v j)) = Set.univ ∧
      ∀ j, ∃ (V' : Scheme.{u}) (a : V' ⟶ V j),
        Surjective a ∧ Stacks.Morphisms.IsFiniteLocallyFree a ∧
        ∃ (m : ℕ)
          (q : (pullback f (a ≫ v j)).nilradical.subscheme ⟶
            V'.nilradical.subscheme)
          (e : (pullback f (a ≫ v j)).nilradical.subscheme ≅
            ∐ fun _ : Fin m => V'.nilradical.subscheme),
          q ≫ V'.nilradical.subschemeι =
            (pullback f (a ≫ v j)).nilradical.subschemeι ≫
              pullback.snd f (a ≫ v j) ∧
          e.hom ≫ Sigma.desc (fun _ : Fin m => 𝟙 V'.nilradical.subscheme) = q := by
  classical
  obtain ⟨I, hI, T, t, hT, hdT, hcT, hfin⟩ :=
    exists_affine_partition_isFinite_family (fun _ : PUnit => Y) (fun _ => f)
  let := hI
  have : ∀ i, IsImmersion (t i) := fun i => (hT i).2.2.1
  have hsplit (i : I) := by
    let : IsAffine (T i) := (hT i).1
    let : IsLocallyNoetherian (T i) := LocallyOfFiniteType.isLocallyNoetherian (t i)
    let : IsNoetherian (T i) := ⟨⟩
    let : IsFinite (pullback.snd f (t i)) := hfin PUnit.unit i
    exact exists_split_stratification_of_finite (pullback.snd f (t i))
  choose J hJ V v hV hdV hcV hchoice using hsplit
  let : ∀ i, Fintype (J i) := hJ
  let W (k : Σ i, J i) := V k.1 k.2
  let w (k : Σ i, J i) : W k ⟶ X := v k.1 k.2 ≫ t k.1
  have hp := partition_comp_of_partitions t v hV hdT hcT hdV hcV
  refine ⟨Σ i, J i, inferInstance, W, w, hp.1, hp.2.1, hp.2.2, ?_⟩
  · intro k
    obtain ⟨A, a, ha, hfreeA, m, q, e, hq, he⟩ := hchoice k.1 k.2
    obtain ⟨q', e', hq', he'⟩ :=
      split_reduction_pullback_composite f (t k.1) (a ≫ v k.1 k.2) q e hq he
    refine ⟨A, a, ha, hfreeA, ?_⟩
    have hmap : a ≫ w k = (a ≫ v k.1 k.2) ≫ t k.1 := by rfl
    rw [hmap]
    exact ⟨m, q', e', hq', he'⟩

private lemma split_reduction_of_isPullback
    {Y X Y₀ X₀ T : Scheme.{u}} (f : Y ⟶ X) (f₀ : Y₀ ⟶ X₀)
    (a : Y ⟶ Y₀) (b : X ⟶ X₀) (h : IsPullback a f f₀ b)
    (g : T ⟶ X) {n : ℕ}
    (e : (pullback f₀ (g ≫ b)).nilradical.subscheme ≅
      ∐ fun _ : Fin n => T.nilradical.subscheme)
    (he : e.hom ≫ Sigma.desc (fun _ : Fin n => 𝟙 T.nilradical.subscheme) =
      reductionMap (pullback.snd f₀ (g ≫ b))) :
    ∃ e' : (pullback f g).nilradical.subscheme ≅
        ∐ fun _ : Fin n => T.nilradical.subscheme,
      e'.hom ≫ Sigma.desc (fun _ : Fin n => 𝟙 T.nilradical.subscheme) =
        reductionMap (pullback.snd f g) := by
  let hp := (IsPullback.of_hasPullback f g).paste_horiz h
  let t := hp.isoPullback
  let e' := reductionIso t ≪≫ e
  refine ⟨e', ?_⟩
  dsimp only [e', Iso.trans_hom, reductionIso_hom]
  rw [Category.assoc, he, reductionMap_comp]
  simp only [t, IsPullback.isoPullback_hom_snd]

private lemma exists_split_stratification_of_isPullback
    {Y X Y₀ X₀ : Scheme.{u}} (f : Y ⟶ X) (f₀ : Y₀ ⟶ X₀)
    (a : Y ⟶ Y₀) (b : X ⟶ X₀) (h : IsPullback a f f₀ b)
    [IsAffine X] [IsAffine X₀]
    {J : Type} [Finite J] (V : J → Scheme.{u}) (v : ∀ j, V j ⟶ X₀)
    (hV : ∀ j, IsAffine (V j) ∧ IsImmersion (v j) ∧
      Topology.IsConstructible (Set.range (v j)))
    (hd : Pairwise fun j k => Disjoint (Set.range (v j)) (Set.range (v k)))
    (hc : (⋃ j, Set.range (v j)) = Set.univ)
    (hsplit : ∀ j, ∃ (V' : Scheme.{u}) (g : V' ⟶ V j),
      Surjective g ∧ Stacks.Morphisms.IsFiniteLocallyFree g ∧
      ∃ (n : ℕ)
        (q : (pullback f₀ (g ≫ v j)).nilradical.subscheme ⟶
          V'.nilradical.subscheme)
        (e : (pullback f₀ (g ≫ v j)).nilradical.subscheme ≅
          ∐ fun _ : Fin n => V'.nilradical.subscheme),
        q ≫ V'.nilradical.subschemeι =
          (pullback f₀ (g ≫ v j)).nilradical.subschemeι ≫
            pullback.snd f₀ (g ≫ v j) ∧
        e.hom ≫ Sigma.desc (fun _ : Fin n => 𝟙 V'.nilradical.subscheme) = q) :
    ∃ (W : J → Scheme.{u}) (w : ∀ j, W j ⟶ X),
      (∀ j, IsAffine (W j) ∧ IsImmersion (w j) ∧
        IsLocallyClosed (Set.range (w j)) ∧
        Topology.IsConstructible (Set.range (w j))) ∧
      (Pairwise fun j k => Disjoint (Set.range (w j)) (Set.range (w k))) ∧
      (⋃ j, Set.range (w j)) = Set.univ ∧
      ∀ j, ∃ (W' : Scheme.{u}) (g' : W' ⟶ W j),
        Surjective g' ∧ Stacks.Morphisms.IsFiniteLocallyFree g' ∧
        ∃ (n : ℕ)
          (q' : (pullback f (g' ≫ w j)).nilradical.subscheme ⟶
            W'.nilradical.subscheme)
          (e' : (pullback f (g' ≫ w j)).nilradical.subscheme ≅
            ∐ fun _ : Fin n => W'.nilradical.subscheme),
          q' ≫ W'.nilradical.subschemeι =
            (pullback f (g' ≫ w j)).nilradical.subschemeι ≫
              pullback.snd f (g' ≫ w j) ∧
          e'.hom ≫ Sigma.desc (fun _ : Fin n => 𝟙 W'.nilradical.subscheme) = q' := by
  classical
  let W (j : J) := pullback (v j) b
  let w (j : J) : W j ⟶ X := pullback.snd (v j) b
  have : ∀ j, IsAffine (V j) := fun j => (hV j).1
  have : ∀ j, IsImmersion (v j) := fun j => (hV j).2.1
  have : ∀ j, IsAffine (W j) := fun j => by dsimp [W]; infer_instance
  have : ∀ j, IsImmersion (w j) := fun j => by dsimp [w]; infer_instance
  have hrange (j : J) : Set.range (w j) = b ⁻¹' Set.range (v j) :=
    Scheme.Pullback.range_snd (v j) b
  refine ⟨W, w, ?_, ?_, ?_, ?_⟩
  · intro j
    exact ⟨inferInstance, inferInstance, (w j).isLocallyClosed_range,
      by rw [hrange]; exact b.isConstructible_preimage (hV j).2.2⟩
  · intro j k hjk
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hx' : b x ∈ Set.range (v j) := by rw [hrange] at hx; exact hx
    have hy' : b x ∈ Set.range (v k) := by rw [hrange] at hy; exact hy
    exact Set.disjoint_left.mp (hd hjk) hx' hy'
  · calc
      (⋃ j, Set.range (w j)) = ⋃ j, b ⁻¹' Set.range (v j) := by
        simp only [hrange]
      _ = b ⁻¹' (⋃ j, Set.range (v j)) := (Set.preimage_iUnion).symm
      _ = Set.univ := by rw [hc]; rfl
  · intro j
    obtain ⟨V', g, hg, hfree, n, q, e, hq, he⟩ := hsplit j
    let W' := pullback g (pullback.fst (v j) b)
    let g' : W' ⟶ W j := pullback.snd g (pullback.fst (v j) b)
    let c : W' ⟶ V' := pullback.fst g (pullback.fst (v j) b)
    have : Surjective g := hg
    have : Stacks.Morphisms.IsFiniteLocallyFree g := hfree
    have : Surjective g' := by dsimp [g']; infer_instance
    have : Stacks.Morphisms.IsFiniteLocallyFree g' :=
      MorphismProperty.pullback_snd g (pullback.fst (v j) b) hfree
    obtain ⟨m, q₁, e₁, hq₁, he₁⟩ :=
      exists_split_reduction_after_baseChange_of_split_pullback_general f₀
        (g ≫ v j) c q e hq he
    have hmap : c ≫ (g ≫ v j) = (g' ≫ w j) ≫ b := by
      rw [pullback.condition_assoc, Category.assoc, pullback.condition (f := v j) (g := b)]
    have hdata : ∃ (m : ℕ)
        (d : (pullback f₀ ((g' ≫ w j) ≫ b)).nilradical.subscheme ≅
          ∐ fun _ : Fin m => W'.nilradical.subscheme),
        d.hom ≫ Sigma.desc (fun _ : Fin m => 𝟙 W'.nilradical.subscheme) =
          reductionMap (pullback.snd f₀ ((g' ≫ w j) ≫ b)) := by
      rw [← hmap]
      exact ⟨m, e₁, he₁.trans (eq_reductionMap_of_comp_subschemeι _ q₁ hq₁)⟩
    obtain ⟨m, d, hd⟩ := hdata
    obtain ⟨d', hd'⟩ := split_reduction_of_isPullback f f₀ a b h
      (g' ≫ w j) d hd
    exact ⟨W', g', inferInstance, inferInstance, m,
      reductionMap (pullback.snd f (g' ≫ w j)), d',
      reductionMap_comp_subschemeι _, hd'⟩

private lemma fiber_dimension_le_zero_of_locallyQuasiFinite
    {Y X : Scheme.{u}} (f : Y ⟶ X)
    [LocallyQuasiFinite f] [QuasiCompact f] (x : X) :
    topologicalKrullDim (f.fiber x) ≤ (0 : WithBot ℕ∞) := by
  let : IsArtinianScheme (f.fiber x) := inferInstance
  let : DiscreteTopology (f.fiber x) :=
    (IsArtinianScheme.iff_isNoetherian_and_discreteTopology).mp ‹_› |>.2
  exact topologicalKrullDim_zero_of_discreteTopology _

private lemma locallyQuasiFinite_of_fiber_dimension_le_zero
    {Y X : Scheme.{u}} (f : Y ⟶ X) [LocallyOfFiniteType f]
    (h : ∀ x, topologicalKrullDim (f.fiber x) ≤ (0 : WithBot ℕ∞)) :
    LocallyQuasiFinite f := by
  rw [locallyQuasiFinite_iff_isDiscrete_preimage_singleton]
  intro x
  have : LocallyOfFiniteType (f.fiberToSpecResidueField x) := by
    let : MorphismProperty.IsStableUnderBaseChangeAlong
        (P := @LocallyOfFiniteType) (X.fromSpecResidueField x) :=
      ⟨fun pb hf => locallyOfFiniteType_isStableUnderBaseChange.of_isPullback pb hf⟩
    exact MorphismProperty.pullback_snd f (X.fromSpecResidueField x) inferInstance
  have : IsLocallyNoetherian (f.fiber x) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField x)
  have : IsLocallyArtinian (f.fiber x) :=
    IsLocallyArtinian.of_topologicalKrullDim_le_zero (h x)
  exact _root_.isDiscrete_iff_discreteTopology.mpr <|
    (f.fiberHomeo x).discreteTopology_iff.mp inferInstance

/-- A finite locally free cover of each affine stratum splits the reduced pullback into
finitely many copies of the reduced covering scheme. -/
@[stacks 095K "part (2)"]
public theorem exists_finite_affine_stratification_split_reduction
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsAffine Y] [IsAffine X]
    [LocallyOfFiniteType f] [QuasiCompact f] [LocallyQuasiFinite f]
    (hfp : FinitePresentation f) :
    ∃ (n : ℕ) (S : Fin n → Scheme.{u}) (s : ∀ i, S i ⟶ X),
      (∀ i, IsAffine (S i) ∧ IsImmersion (s i) ∧
        IsLocallyClosed (Set.range (s i).base) ∧
        Topology.IsConstructible (Set.range (s i).base)) ∧
      (∀ i j, i ≠ j → Disjoint (Set.range (s i).base) (Set.range (s j).base)) ∧
      (⋃ i, Set.range (s i).base) = Set.univ ∧
      ∀ i, ∃ (S' : Scheme.{u}) (g : S' ⟶ S i),
        Surjective g ∧ Stacks.Morphisms.IsFiniteLocallyFree g ∧
        ∃ (m : ℕ)
          (q : (pullback f (g ≫ s i)).nilradical.subscheme ⟶
            S'.nilradical.subscheme)
          (e : (pullback f (g ≫ s i)).nilradical.subscheme ≅
            ∐ (fun _ : Fin m ↦ S'.nilradical.subscheme)),
          q ≫ S'.nilradical.subschemeι =
              (pullback f (g ≫ s i)).nilradical.subschemeι ≫
                pullback.snd f (g ≫ s i) ∧
          e.hom ≫ Sigma.desc (fun _ : Fin m ↦ 𝟙 S'.nilradical.subscheme) = q := by
  classical
  obtain ⟨M, hdim⟩ :=
    exists_finiteTypeAffineModel_fiberDimension_le f hfp 0
      (fiber_dimension_le_zero_of_locallyQuasiFinite f)
  let : IsAffine M.X₀ := M.source_affine
  let : IsAffine M.S₀ := M.base_affine
  let : LocallyOfFiniteType M.f₀ := M.locallyOfFiniteType
  let : QuasiCompact M.f₀ := M.quasiCompact
  let eℤ : Spec (.of (ULift.{u} ℤ)) ≅ ⊤_ Scheme.{u} :=
    specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal
  let z : M.S₀ ⟶ Spec (.of (ULift.{u} ℤ)) := terminal.from M.S₀ ≫ eℤ.inv
  let : LocallyOfFiniteType (terminal.from M.S₀) := M.base_locallyOfFiniteType
  let : LocallyOfFiniteType z := by dsimp [z]; infer_instance
  let : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ (ULift.ringEquiv (R := ℤ)).symm
  let : IsLocallyNoetherian M.S₀ :=
    LocallyOfFiniteType.isLocallyNoetherian z
  let : IsNoetherian M.S₀ := ⟨⟩
  let : LocallyQuasiFinite M.f₀ :=
    locallyQuasiFinite_of_fiber_dimension_le_zero M.f₀ hdim
  obtain ⟨J, hJ, V, v, hV, hdV, hcV, hsplit⟩ :=
    exists_split_stratification_of_noetherian M.f₀
  let : Fintype J := hJ
  obtain ⟨W, w, hW, hdW, hcW, hchoice⟩ :=
    exists_split_stratification_of_isPullback f M.f₀ M.toSource M.toBase
      M.isPullback V v
      (fun j => ⟨(hV j).1, (hV j).2.2.1, (hV j).2.2.2.2⟩)
      hdV hcV hsplit
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  refine ⟨Fintype.card J, fun i => W (e.symm i), fun i => w (e.symm i),
    ?_, ?_, ?_, ?_⟩
  · intro i
    exact hW (e.symm i)
  · exact hdW.comp_of_injective e.symm.injective
  · rw [e.symm.surjective.iUnion_comp (fun j => Set.range (w j))]
    exact hcW
  · intro i
    exact hchoice (e.symm i)

/-- After a surjective affine base change, the pullback contains a finite étale thickening. -/
@[stacks 095K "part (1)"]
public theorem exists_surjective_affine_baseChange_thickening_finiteEtale
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsAffine Y] [IsAffine X]
    [LocallyOfFiniteType f] [QuasiCompact f] [LocallyQuasiFinite f]
    (hfp : FinitePresentation f) :
    ∃ (X' : Scheme.{u}) (_ : IsAffine X') (g : X' ⟶ X),
      Surjective g ∧
      ∃ (Z' : Scheme.{u}) (i : Z' ⟶ pullback f g),
        Stacks.Thickenings.IsThickening i ∧
        IsFinite (i ≫ pullback.snd f g) ∧
        Etale (i ≫ pullback.snd f g) := by
  obtain ⟨n, S, s, hS, _, hcover, hsplit⟩ :=
    exists_finite_affine_stratification_split_reduction f hfp
  let : ∀ i, IsAffine (S i) := fun i => (hS i).1
  exact exists_thickening_finiteEtale_of_split_reductions f S s hcover (fun i => by
    obtain ⟨T, g, hg, hfree, m, q, e, hq, he⟩ := hsplit i
    exact ⟨T, g, hg, hfree.toIsAffineHom, m, q, e, hq, he⟩)

end AlgebraicGeometry

end
