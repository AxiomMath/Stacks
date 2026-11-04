module

public import StacksFrontier.AlgebraicGeometry.CompactOpenInduction.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteFactorization.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.FibreSumMaximum
public import StacksFrontier.AlgebraicGeometry.Morphisms.ConstructibleAssociatedPointsLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.FiniteCover
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Constructible
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksCore.Tactic.StacksAttribute

/-!
# Constructibility of the level sets of a weighted fibre sum

Let `f : X ⟶ Y` be a locally quasi-finite morphism of finite presentation and let `w : X → ℤ` be
a weighting of `f`.  Then every level set of the weighted fibre sum
`∫_f w = separableDegreeWeightedFiberSum f w` is locally constructible in `Y`.

## Main results

* `AlgebraicGeometry.isLocallyConstructible_separableDegreeWeightedFiberSum_levelSet`:
  **[Stacks, Tag 0F3H]**, the level sets of the weighted fibre sum of a weighting of a locally
  quasi-finite morphism of finite presentation are locally constructible on the target.

## Implementation notes

Finite presentation is `AlgebraicGeometry.FinitePresentation`, the conjunction of [Stacks, Tag
01TP]; together with `AlgebraicGeometry.LocallyQuasiFinite` its local component supplies the
local finite type condition in the pointwise characterization of a locally quasi-finite morphism
of [Stacks, Tag 01TD].

Three reductions bring the statement to a situation where the weighted fibre sum is a finite sum
of functions whose level sets are visibly locally constructible.

The statement is local on the target, so `Y` may be assumed affine; the weighted fibre sum
commutes with the restriction by [Stacks, Tag 0F39] and the restricted weight is again a
weighting by [Stacks, Tag 0F3B].  The source is then quasi-compact and quasi-separated, and the
weighted fibre sums of the restrictions of `w` to two opens, to their union and to their
intersection satisfy inclusion-exclusion — both sides being sums of the terms
`AlgebraicGeometry.separableDegreeWeightedFiberTerm` over the four sets, which are supported on
the finite fibre.  The induction principle of [Stacks, Tag 08DR] therefore reduces the statement
to an affine open of the source.  This reduction is what makes Zariski's Main Theorem applicable:
a morphism between affine schemes is separated, which a locally quasi-finite morphism of finite
presentation need not be.

With `X` and `Y` affine, `Stacks.FiniteFactorization.exists_isOpenImmersion_isFinite_factorization`
([Stacks, Tag 05K0]) writes `f` as an open immersion `j : X ⟶ T` followed by a finite morphism
`p : T ⟶ Y`, and `Stacks.Morphisms.exists_finiteLocallyFree_cover_closedImmersion` ([Stacks, Tag
03HW]) produces a surjective finite locally free `g : Y' ⟶ Y` after which `T` embeds as a closed
subscheme of a scheme `Z` finite locally free over `Y'` and covered set-theoretically by finitely
many sections of `Z ⟶ Y'`.  Local constructibility descends along `g` by [Stacks, Tag 054K].

In that situation the base change of `f` is an immersion `i` of finite presentation into `Z`
followed by `q : Z ⟶ Y'`.  Every point of `Z` lies on one of the sections, so all residue-field
extensions of `q` — hence of `i ≫ q` — are trivial and the weighted fibre sum of `i ≫ q` is the
plain sum of the weight over the fibre.  Extending the weight by zero along `i`, which is to say
replacing it by its own weighted fibre sum `F` along `i`, turns that into a sum over the fibre of
`q`; and that fibre is enumerated bijectively by the sections that pass through a point of it
first.  So the weighted fibre sum of `i ≫ q` is a finite sum over the sections of `F` composed
with the section, cut off outside the locus where that section passes first.  Each such locus is
locally constructible because two sections agree exactly where one lands in the image of the
other; `F` has locally constructible level sets by Chevalley's theorem, since off the image of
`i` it vanishes and on the image it is the weight at the unique preimage; and `F` takes finitely
many values because `w` does ([Stacks, Tag 0F2M]).  A level set of a finite sum of such functions
is the finite union, over the tuples of values summing to the prescribed one, of the loci where
each summand takes its prescribed value.

The level sets of `w` itself are locally constructible by [Stacks, Tag 0F3G].

## References

* [Stacks Project, Tag 0F3H](https://stacks.math.columbia.edu/tag/0F3H)
* [Stacks Project, Tag 0F3G](https://stacks.math.columbia.edu/tag/0F3G)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
* [Stacks Project, Tag 05K0](https://stacks.math.columbia.edu/tag/05K0)
* [Stacks Project, Tag 03HW](https://stacks.math.columbia.edu/tag/03HW)
* [Stacks Project, Tag 054K](https://stacks.math.columbia.edu/tag/054K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

open scoped Set.Notation

universe u

namespace AlgebraicGeometry

/-! ### Level sets of integer-valued functions -/

/-- A level set of a finite sum of integer-valued functions is locally constructible as soon as
each summand has locally constructible level sets and takes only finitely many values: the level
set is the finite union, over the tuples of values summing to `n`, of the loci where each
summand takes its prescribed value. -/
private theorem isLocallyConstructible_levelSet_sum
    {T ι : Type*} [TopologicalSpace T] [Fintype ι] (g : ι → T → ℤ)
    (hlevel : ∀ (i : ι) (m : ℤ), IsLocallyConstructible {x : T | g i x = m})
    (hrange : ∀ i, (Set.range (g i)).Finite) (n : ℤ) :
    IsLocallyConstructible {x : T | ∑ i, g i x = n} := by
  classical
  let _ : ∀ i, Fintype (Set.range (g i)) := fun i ↦ (hrange i).fintype
  let A : Type _ := ∀ i, Set.range (g i)
  let S : Set A := {a | ∑ i, (a i : ℤ) = n}
  have heq : {x : T | ∑ i, g i x = n} = ⋃ a ∈ S, ⋂ i, {x : T | g i x = (a i : ℤ)} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion₂, Set.mem_iInter]
    refine ⟨fun hx ↦ ⟨fun i ↦ ⟨g i x, Set.mem_range_self x⟩, hx, fun _ ↦ rfl⟩, ?_⟩
    rintro ⟨a, ha, hx⟩
    exact (Finset.sum_congr rfl fun i _ ↦ hx i).trans ha
  rw [heq]
  exact IsLocallyConstructible.biUnion (Set.toFinite S)
    fun a _ ↦ IsLocallyConstructible.iInter fun i ↦ hlevel i _

/-- A level set of a function vanishing off `P` is locally constructible as soon as `P` is and the
level sets of the function inside `P` are. -/
private theorem isLocallyConstructible_levelSet_of_eq_zero_off
    {T : Type*} [TopologicalSpace T] {P : Set T} (hP : IsLocallyConstructible P) {G : T → ℤ}
    (hG : ∀ x, x ∉ P → G x = 0) (hlevel : ∀ m : ℤ, IsLocallyConstructible (P ∩ {x : T | G x = m}))
    (n : ℤ) : IsLocallyConstructible {x : T | G x = n} := by
  by_cases hn : n = 0
  · subst hn
    have heq : {x : T | G x = 0} = (P ∩ {x : T | G x = 0}) ∪ Pᶜ := by
      ext x
      by_cases hx : x ∈ P <;> simp [hx, hG]
    rw [heq]
    exact (hlevel 0).union hP.compl
  · have heq : {x : T | G x = n} = P ∩ {x : T | G x = n} := by
      ext x
      by_cases hx : x ∈ P <;> simp [hx, hG, Ne.symm hn]
    rw [heq]
    exact hlevel n

/-- A function takes only finitely many values if each value is zero or lies in a finite set. -/
private theorem finite_range_of_eq_zero_or_mem {T : Type*} {G : T → ℤ} {R : Set ℤ}
    (hR : R.Finite) (h : ∀ x, G x = 0 ∨ G x ∈ R) : (Set.range G).Finite := by
  refine (hR.union (Set.finite_singleton (0 : ℤ))).subset ?_
  rintro _ ⟨x, rfl⟩
  exact (h x).symm

/-! ### The weighted fibre sum of a morphism injective on points -/

/-- At a point of the fibre where the residue-field extension is trivial, the term of a weighted
fibre sum is the weight itself. -/
private theorem separableDegreeWeightedFiberTerm_eq_of_isIso_residueFieldMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) (w : X → ℤ) {y : Y} {x : X} (hxy : f x = y)
    (hres : IsIso (f.residueFieldMap x)) :
    separableDegreeWeightedFiberTerm f w y x = w x := by
  rw [separableDegreeWeightedFiberTerm_of_mem_fiber f w hxy,
    finSepDegree_eq_one_of_isIso_residueFieldMap f x hres]
  simp

/-- The weighted fibre sum of a morphism injective on points with trivial residue-field
extensions is the weight at the unique point of the fibre. -/
private theorem separableDegreeWeightedFiberSum_apply_of_injective
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hinj : Function.Injective f)
    (hres : ∀ x : X, IsIso (f.residueFieldMap x)) (w : X → ℤ) (x : X) :
    separableDegreeWeightedFiberSum f w (f x) = w x := by
  rw [separableDegreeWeightedFiberSum_eq_finsum_term,
    finsum_eq_single _ x fun z hz ↦
      separableDegreeWeightedFiberTerm_of_notMem_fiber f w fun h ↦ hz (hinj h)]
  exact separableDegreeWeightedFiberTerm_eq_of_isIso_residueFieldMap f w rfl (hres x)

/-- The weighted fibre sum vanishes outside the image. -/
private theorem separableDegreeWeightedFiberSum_eq_zero_of_notMem_range
    {X Y : Scheme.{u}} (f : X ⟶ Y) (w : X → ℤ) {y : Y} (hy : y ∉ Set.range f) :
    separableDegreeWeightedFiberSum f w y = 0 :=
  separableDegreeWeightedFiberSum_eq_zero_of_fiber_eq_empty f w y <| by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    exact fun h ↦ hy ⟨x, h⟩

/-- The weighted fibre sum of a morphism injective on points with trivial residue-field
extensions takes only the values of the weight and zero. -/
private theorem finite_range_separableDegreeWeightedFiberSum_of_injective
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hinj : Function.Injective f)
    (hres : ∀ x : X, IsIso (f.residueFieldMap x)) {w : X → ℤ} (hw : (Set.range w).Finite) :
    (Set.range (separableDegreeWeightedFiberSum f w)).Finite := by
  refine finite_range_of_eq_zero_or_mem hw fun y ↦ ?_
  by_cases hy : y ∈ Set.range f
  · obtain ⟨x, rfl⟩ := hy
    exact Or.inr ⟨x, (separableDegreeWeightedFiberSum_apply_of_injective f hinj hres w x).symm⟩
  · exact Or.inl (separableDegreeWeightedFiberSum_eq_zero_of_notMem_range f w hy)

/-- The range of a quasi-compact morphism locally of finite presentation is locally
constructible. -/
private theorem isLocallyConstructible_range {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [QuasiCompact f] : IsLocallyConstructible (Set.range f) := by
  simpa using f.isLocallyConstructible_image (IsLocallyConstructible.univ (X := X))

/-- A section of a morphism is a right inverse on points. -/
private theorem apply_section {V Z : Scheme.{u}} (q : Z ⟶ V) (s : V ⟶ Z) (hs : s ≫ q = 𝟙 V)
    (y : V) : q (s y) = y := by
  simpa using congrArg (fun k : V ⟶ V ↦ k y) hs

/-- The level sets of the weighted fibre sum of a morphism of finite presentation that is
injective on points and has trivial residue-field extensions are locally constructible.

Off the image the sum vanishes and on the image it is the weight at the unique preimage, so each
level set is the image of a level set of the weight, together with the complement of the image
when the value is zero.  Both are locally constructible, by Chevalley's theorem for the images
and because locally constructible sets are closed under complement. -/
private theorem isLocallyConstructible_levelSet_of_injective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f] [QuasiCompact f]
    (hinj : Function.Injective f) (hres : ∀ x : X, IsIso (f.residueFieldMap x))
    {w : X → ℤ} (hw : ∀ m : ℤ, IsLocallyConstructible {x : X | w x = m}) (n : ℤ) :
    IsLocallyConstructible {y : Y | separableDegreeWeightedFiberSum f w y = n} := by
  refine isLocallyConstructible_levelSet_of_eq_zero_off (isLocallyConstructible_range f)
    (fun y hy ↦ separableDegreeWeightedFiberSum_eq_zero_of_notMem_range f w hy) (fun m ↦ ?_) n
  have hf := separableDegreeWeightedFiberSum_apply_of_injective f hinj hres w
  have heq : Set.range f ∩ {y : Y | separableDegreeWeightedFiberSum f w y = m} =
      f '' {x : X | w x = m} := by
    ext y
    constructor
    · rintro ⟨⟨x, rfl⟩, hy⟩
      exact ⟨x, (hf x).symm.trans hy, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, rfl⟩, (hf x).trans hx⟩
  rw [heq]
  exact f.isLocallyConstructible_image (hw m)

/-! ### Summing over a fibre covered by finitely many sections -/

/-- For a morphism with trivial residue-field extensions the weighted fibre sum is the plain sum
of the weights over the fibre. -/
private theorem separableDegreeWeightedFiberSum_eq_finsum_mem_fiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) (w : X → ℤ)
    (hres : ∀ x : X, IsIso (f.residueFieldMap x)) (y : Y) :
    separableDegreeWeightedFiberSum f w y = ∑ᶠ x ∈ f ⁻¹' {y}, w x := by
  have hsupp : Function.support (separableDegreeWeightedFiberTerm f w y) ⊆ f ⁻¹' {y} := by
    intro x hx
    by_contra hxy
    exact hx (separableDegreeWeightedFiberTerm_of_notMem_fiber f w (by simpa using hxy))
  rw [separableDegreeWeightedFiberSum_eq_finsum_term, ← finsum_mem_univ,
    finsum_mem_inter_support_eq (separableDegreeWeightedFiberTerm f w y) Set.univ (f ⁻¹' {y})
      (by rw [Set.univ_inter, Set.inter_eq_self_of_subset_right hsupp])]
  exact finsum_mem_congr rfl fun x hx ↦
    separableDegreeWeightedFiberTerm_eq_of_isIso_residueFieldMap f w (by simpa using hx) (hres x)

/-- Summing a weight over the fibre of a composite `q ∘ i` with `i` injective is the same as
summing, over the fibre of `q`, any extension of the weight by zero. -/
private theorem finsum_mem_fiber_comp_eq_finsum_mem_fiber
    {A Z V : Type*} (i : A → Z) (q : Z → V) (w : A → ℤ) (F : Z → ℤ)
    (hinj : Function.Injective i) (hF : ∀ x, F (i x) = w x)
    (hF0 : ∀ z, z ∉ Set.range i → F z = 0) (y : V) :
    (∑ᶠ x ∈ (q ∘ i) ⁻¹' {y}, w x) = ∑ᶠ z ∈ q ⁻¹' {y}, F z := by
  have hbij : Set.BijOn i ((q ∘ i) ⁻¹' {y}) (q ⁻¹' {y} ∩ Set.range i) := by
    refine ⟨fun x hx ↦ ⟨hx, ⟨x, rfl⟩⟩, fun x _ x' _ h ↦ hinj h, fun z hz ↦ ?_⟩
    obtain ⟨x, rfl⟩ := hz.2
    exact ⟨x, hz.1, rfl⟩
  calc (∑ᶠ x ∈ (q ∘ i) ⁻¹' {y}, w x) = ∑ᶠ z ∈ q ⁻¹' {y} ∩ Set.range i, F z :=
        finsum_mem_eq_of_bijOn i hbij fun x _ ↦ (hF x).symm
    _ = ∑ᶠ z ∈ q ⁻¹' {y}, F z :=
        finsum_mem_inter_support_eq F _ _ (by
          rw [Set.inter_assoc, Set.inter_eq_right.2 (Function.support_subset_iff'.2 hF0)])

/-- The locus in the base where the `j`-th member of a family of sections is the first one
passing through the point it hits. -/
private def firstSectionLocus {Z V : Type*} {m : ℕ} (s : Fin m → V → Z) (j : Fin m) : Set V :=
  {y | ∀ k, k < j → s j y ≠ s k y}

/-- Over a point of the base, the sections that pass there first enumerate the fibre
bijectively. -/
private theorem bijOn_firstSectionLocus
    {Z V : Type*} {m : ℕ} (q : Z → V) (s : Fin m → V → Z)
    (hs : ∀ (j : Fin m) (y : V), q (s j y) = y) (hcover : ∀ z : Z, ∃ j, s j (q z) = z) (y : V) :
    Set.BijOn (fun j ↦ s j y) {j : Fin m | y ∈ firstSectionLocus s j} (q ⁻¹' {y}) := by
  classical
  refine ⟨fun j _ ↦ ?_, fun j hj k hk heq ↦ ?_, fun z hz ↦ ?_⟩
  · simpa using hs j y
  · change ∀ l, l < j → s j y ≠ s l y at hj
    change ∀ l, l < k → s k y ≠ s l y at hk
    rcases lt_trichotomy j k with hjk | heqjk | hkj
    · exact absurd heq.symm (hk j hjk)
    · exact heqjk
    · exact absurd heq (hj k hkj)
  · obtain ⟨j, hj⟩ := hcover z
    rw [show q z = y from hz] at hj
    let A : Finset (Fin m) := Finset.univ.filter fun k ↦ s k y = z
    have hA : A.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
    have hmin : s (A.min' hA) y = z := (Finset.mem_filter.mp (A.min'_mem hA)).2
    refine ⟨A.min' hA, fun k hk heq ↦ ?_, hmin⟩
    exact (A.min'_le k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq.symm.trans hmin⟩)).not_gt hk

/-- A sum over a fibre covered by finitely many sections is the finite sum, over the sections, of
the value at the section, taken only where that section passes first. -/
private theorem finsum_mem_fiber_eq_sum_sections
    {Z V : Type*} {m : ℕ} (q : Z → V) (s : Fin m → V → Z)
    (hs : ∀ (j : Fin m) (y : V), q (s j y) = y) (hcover : ∀ z : Z, ∃ j, s j (q z) = z)
    (F : Z → ℤ) (y : V) :
    (∑ᶠ z ∈ q ⁻¹' {y}, F z) =
      ∑ j, (firstSectionLocus s j).indicator (fun y' ↦ F (s j y')) y := by
  classical
  rw [← finsum_mem_eq_of_bijOn (fun j ↦ s j y) (bijOn_firstSectionLocus q s hs hcover y)
    (fun j _ ↦ rfl), finsum_mem_def, finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun j _ ↦ by
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]

/-- Two sections of a morphism agree exactly where the first lands in the image of the second,
so their agreement locus is locally constructible when the second is of finite presentation. -/
private theorem isLocallyConstructible_eq_section
    {V Z : Scheme.{u}} (q : Z ⟶ V) (s t : V ⟶ Z) (hs : s ≫ q = 𝟙 V) (ht : t ≫ q = 𝟙 V)
    (htfp : LocallyOfFinitePresentation t) (htqc : QuasiCompact t) :
    IsLocallyConstructible {y : V | s y = t y} := by
  let := htfp
  let := htqc
  have heq : {y : V | s y = t y} = s ⁻¹' Set.range t := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_range]
    refine ⟨fun h ↦ ⟨y, h.symm⟩, ?_⟩
    rintro ⟨y', hy'⟩
    have hyy : y' = y := by rw [← apply_section q t ht y', hy', apply_section q s hs y]
    rw [← hy', hyy]
  rw [heq]
  exact isLocallyConstructible_preimage s (isLocallyConstructible_range t)

/-- The locus where a section of a morphism passes first is locally constructible when the
sections are of finite presentation. -/
private theorem isLocallyConstructible_firstSectionLocus
    {V Z : Scheme.{u}} (q : Z ⟶ V) {m : ℕ} (s : Fin m → (V ⟶ Z))
    (hs : ∀ j, s j ≫ q = 𝟙 V) (hfp : ∀ j, LocallyOfFinitePresentation (s j))
    (hqc : ∀ j, QuasiCompact (s j)) (j : Fin m) :
    IsLocallyConstructible (firstSectionLocus (fun k ↦ ⇑(s k)) j) := by
  have heq : firstSectionLocus (fun k ↦ ⇑(s k)) j =
      ⋂ k : Fin m, (if k < j then {y : V | (s j) y = (s k) y}ᶜ else Set.univ) := by
    ext y
    simp only [firstSectionLocus, Set.mem_ofPred_eq, Set.mem_iInter]
    exact forall_congr' fun k ↦ by by_cases hkj : k < j <;> simp [hkj]
  rw [heq]
  refine IsLocallyConstructible.iInter fun k ↦ ?_
  split_ifs
  · exact (isLocallyConstructible_eq_section q (s j) (s k) (hs j) (hs k) (hfp k) (hqc k)).compl
  · exact IsLocallyConstructible.univ

/-- The level sets of the weighted fibre sum of `i ≫ q` are locally constructible when `i` is an
immersion of finite presentation and `q` is covered set-theoretically by finitely many sections
of finite presentation.

Every point of the target of `i` lies on one of the sections, so all residue-field extensions of
`q` — and hence of `i ≫ q` — are trivial, and the weighted fibre sum of `i ≫ q` is the plain sum
of the weight over the fibre.  Extending the weight by zero along `i`, which is to say replacing
it by its own weighted fibre sum `F` along `i`, turns that into a sum over the fibre of `q`, and
the sections that pass first enumerate that fibre bijectively.  The weighted fibre sum of `i ≫ q`
is therefore the finite sum over the sections of `F` composed with the section, taken only where
that section passes first; each summand has locally constructible level sets and finitely many
values. -/
private theorem isLocallyConstructible_levelSet_of_sections
    {A Z V : Scheme.{u}} (i : A ⟶ Z) (q : Z ⟶ V)
    [IsImmersion i] [LocallyOfFinitePresentation i] [QuasiCompact i]
    {m : ℕ} (s : Fin m → (V ⟶ Z)) (hs : ∀ j, s j ≫ q = 𝟙 V)
    (hfp : ∀ j, LocallyOfFinitePresentation (s j)) (hqc : ∀ j, QuasiCompact (s j))
    (hcover : ∀ z : Z, ∃ j, z ∈ Set.range (s j))
    {w : A → ℤ} (hlevel : ∀ k : ℤ, IsLocallyConstructible {x : A | w x = k})
    (hwrange : (Set.range w).Finite) (n : ℤ) :
    IsLocallyConstructible {y : V | separableDegreeWeightedFiberSum (i ≫ q) w y = n} := by
  have hinj : Function.Injective i := i.isEmbedding.injective
  have hresi : ∀ x : A, IsIso (i.residueFieldMap x) := fun x ↦
    isIso_residueFieldMap_of_isPreimmersion i x
  have hresq : ∀ z : Z, IsIso (q.residueFieldMap z) := by
    intro z
    obtain ⟨j, y, rfl⟩ := hcover z
    exact isIso_residueFieldMap_of_mem_range_section q (s j) (hs j) y
  set F : Z → ℤ := separableDegreeWeightedFiberSum i w
  have hF : ∀ x : A, F (i x) = w x := fun x ↦
    separableDegreeWeightedFiberSum_apply_of_injective i hinj hresi w x
  have hF0 : ∀ z : Z, z ∉ Set.range i → F z = 0 := fun z hz ↦
    separableDegreeWeightedFiberSum_eq_zero_of_notMem_range i w hz
  have hFlevel : ∀ k : ℤ, IsLocallyConstructible {z : Z | F z = k} := fun k ↦
    isLocallyConstructible_levelSet_of_injective i hinj hresi hlevel k
  have hFrange : (Set.range F).Finite :=
    finite_range_separableDegreeWeightedFiberSum_of_injective i hinj hresi hwrange
  have hsbase : ∀ (j : Fin m) (y : V), q ((s j) y) = y := fun j y ↦
    apply_section q (s j) (hs j) y
  have hcover' : ∀ z : Z, ∃ j, (s j) (q z) = z := by
    intro z
    obtain ⟨j, y, hy⟩ := hcover z
    exact ⟨j, by rw [← hy, hsbase j y]⟩
  have hrescomp : ∀ x : A, IsIso ((i ≫ q).residueFieldMap x) := by
    intro x
    rw [Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso' (hresq (i x)) (hresi x)
  have hkey : ∀ y : V, separableDegreeWeightedFiberSum (i ≫ q) w y =
      ∑ j, (firstSectionLocus (fun k ↦ ⇑(s k)) j).indicator (fun y' ↦ F ((s j) y')) y := by
    intro y
    calc separableDegreeWeightedFiberSum (i ≫ q) w y
        = ∑ᶠ x ∈ (⇑q ∘ ⇑i) ⁻¹' {y}, w x :=
          separableDegreeWeightedFiberSum_eq_finsum_mem_fiber (i ≫ q) w hrescomp y
      _ = ∑ᶠ z ∈ ⇑q ⁻¹' {y}, F z :=
          finsum_mem_fiber_comp_eq_finsum_mem_fiber ⇑i ⇑q w F hinj hF hF0 y
      _ = _ := finsum_mem_fiber_eq_sum_sections ⇑q (fun k ↦ ⇑(s k)) hsbase hcover' F y
  simp only [hkey]
  refine isLocallyConstructible_levelSet_sum _ (fun j k ↦ ?_) (fun j ↦ ?_) n
  · set P := firstSectionLocus (fun k ↦ ⇑(s k)) j
    refine isLocallyConstructible_levelSet_of_eq_zero_off
      (isLocallyConstructible_firstSectionLocus q s hs hfp hqc j)
      (fun y hy ↦ Set.indicator_of_notMem hy _) (fun l ↦ ?_) k
    have heq : P ∩ {y | P.indicator (fun y' ↦ F ((s j) y')) y = l} =
        P ∩ (s j) ⁻¹' {z | F z = l} := by
      ext y
      by_cases hy : y ∈ P <;> simp [hy]
    rw [heq]
    exact (isLocallyConstructible_firstSectionLocus q s hs hfp hqc j).inter
      (isLocallyConstructible_preimage (s j) (hFlevel l))
  · set P := firstSectionLocus (fun k ↦ ⇑(s k)) j
    refine finite_range_of_eq_zero_or_mem (hFrange.subset (Set.range_comp_subset_range (s j) F))
      fun y ↦ ?_
    by_cases hy : y ∈ P
    · exact Or.inr (by simp [hy])
    · exact Or.inl (Set.indicator_of_notMem hy _)

/-- The preimage of a level set of a weighted fibre sum under the base change map of a pullback
square is the level set of the weighted fibre sum of the base change. -/
private theorem preimage_levelSet_separableDegreeWeightedFiberSum
    {U U' V V' : Scheme.{u}} (f : U ⟶ V) (h : U' ⟶ U) (f' : U' ⟶ V') (g : V' ⟶ V)
    (sq : IsPullback h f' f g) [LocallyQuasiFinite f] [QuasiCompact f] (w : U → ℤ) (n : ℤ) :
    g ⁻¹' {y : V | separableDegreeWeightedFiberSum f w y = n} =
      {y : V' | separableDegreeWeightedFiberSum f' (w ∘ h) y = n} := by
  ext y
  have heq := congrFun (separableDegreeWeightedFiberSum_comp_of_isPullback f h f' g sq
    (fun v ↦ f.finite_preimage_singleton v) w) y
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, ← heq, Function.comp_apply]

/-! ### The affine case -/

/-- The level sets of the weighted fibre sum of a locally quasi-finite morphism of finite
presentation between affine schemes are locally constructible.

Zariski's Main Theorem writes the morphism as an open immersion `j` into a scheme finite over the
target, and after the surjective finite locally free base change of [Stacks, Tag 03HW] that
finite scheme sits inside one covered set-theoretically by finitely many sections.  Local
constructibility descends along that base change because the weighted fibre sum commutes with it
([Stacks, Tag 0F39]) and the base change is surjective, quasi-compact and locally of finite
presentation ([Stacks, Tag 054K]). -/
private theorem isLocallyConstructible_levelSet_of_isAffine
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine X] [IsAffine Y]
    [LocallyQuasiFinite f] [LocallyOfFinitePresentation f]
    {w : X → ℤ} (hlevel : ∀ k : ℤ, IsLocallyConstructible {x : X | w x = k}) (n : ℤ) :
    IsLocallyConstructible {y : Y | separableDegreeWeightedFiberSum f w y = n} := by
  obtain ⟨T, j, p, hj, hjqc, hp, hfac⟩ :=
    Stacks.FiniteFactorization.exists_isOpenImmersion_isFinite_factorization f
  subst hfac
  let := hj
  let := hjqc
  let := hp
  have : IsAffine T := isAffine_of_isAffineHom p
  obtain ⟨Y', g, hgsurj, hgflf, -, -, Z, q, i₀, hi₀, hi₀q, hqflf, m, s, hsprop, hcov⟩ :=
    Stacks.Morphisms.exists_finiteLocallyFree_cover_closedImmersion p
  let := hgsurj
  obtain ⟨hgfin, -, hgfp⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation g).mp hgflf
  let := hgfin
  let := hgfp
  have : IsAffine Y' := isAffine_of_isAffineHom g
  obtain ⟨hqfin, -, hqfp⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation q).mp hqflf
  let := hqfin
  let := hqfp
  have : IsAffine Z := isAffine_of_isAffineHom q
  let := hi₀
  have : IsAffine (pullback (j ≫ p) g) := isAffine_of_isAffineHom (pullback.fst (j ≫ p) g)
  have : IsOpenImmersion (baseChangeFactor j p g) :=
    MorphismProperty.of_isPullback (isPullback_baseChangeFactor j p g) hj
  have hcomp : (baseChangeFactor j p g ≫ i₀) ≫ q = pullback.snd (j ≫ p) g := by
    rw [Category.assoc, hi₀q, baseChangeFactor_snd]
  have : LocallyOfFinitePresentation ((baseChangeFactor j p g ≫ i₀) ≫ q) := by
    rw [hcomp]
    infer_instance
  have : LocallyOfFinitePresentation (baseChangeFactor j p g ≫ i₀) :=
    locallyOfFinitePresentation_of_comp (baseChangeFactor j p g ≫ i₀) q
  have hsq : ∀ k, s k ≫ q = 𝟙 Y' := fun k ↦ (hsprop k).2
  have hsfp : ∀ k, LocallyOfFinitePresentation (s k) := by
    intro k
    have : LocallyOfFinitePresentation (s k ≫ q) := by
      rw [hsq k]
      infer_instance
    exact locallyOfFinitePresentation_of_comp (s k) q
  have hscov : ∀ z : Z, ∃ k, z ∈ Set.range (s k) := by
    intro z
    obtain ⟨k, y, hy⟩ := hcov z
    exact ⟨k, y, hy⟩
  have hmain := isLocallyConstructible_levelSet_of_sections
    (baseChangeFactor j p g ≫ i₀) q s hsq hsfp (fun _ ↦ inferInstance) hscov
    (w := w ∘ pullback.fst (j ≫ p) g)
    (fun k ↦ isLocallyConstructible_preimage (pullback.fst (j ≫ p) g) (hlevel k))
    ((finite_range_of_isLocallyConstructible_levelSet w hlevel).subset
      (Set.range_comp_subset_range _ w)) n
  rw [hcomp] at hmain
  refine isLocallyConstructible_of_surjective_finitePresentation g ?_
  have hpre := preimage_levelSet_separableDegreeWeightedFiberSum (j ≫ p) (pullback.fst (j ≫ p) g)
    (pullback.snd (j ≫ p) g) g (IsPullback.of_hasPullback (j ≫ p) g) w n
  rw [hpre]
  exact hmain

/-! ### From an affine source to a quasi-compact quasi-separated one -/

/-- A level set of the sum of two integer-valued functions with locally constructible level sets
and finitely many values is locally constructible. -/
private theorem isLocallyConstructible_levelSet_add
    {T : Type*} [TopologicalSpace T] {F G : T → ℤ}
    (hF : ∀ k : ℤ, IsLocallyConstructible {x : T | F x = k})
    (hG : ∀ k : ℤ, IsLocallyConstructible {x : T | G x = k})
    (hFr : (Set.range F).Finite) (hGr : (Set.range G).Finite) (n : ℤ) :
    IsLocallyConstructible {x : T | F x + G x = n} := by
  have hset : {x : T | F x + G x = n} =
      {x : T | ∑ b : Bool, (fun b ↦ if b then G else F) b x = n} := by
    ext x
    simp [add_comm]
  rw [hset]
  refine isLocallyConstructible_levelSet_sum _ (fun b k ↦ ?_) (fun b ↦ ?_) n
  · cases b with
    | false => simpa using hF k
    | true => simpa using hG k
  · cases b with
    | false => simpa using hFr
    | true => simpa using hGr

/-- Mayer–Vietoris for the weighted fibre sum: the restrictions of a weight to two opens, to
their union and to their intersection have weighted fibre sums related by inclusion-exclusion.

Both sides are sums of the terms of the weighted fibre sum of `f` over the four sets, and those
terms are supported on the fibre, which is finite. -/
private theorem separableDegreeWeightedFiberSum_restrict_sup_add_inf
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] [QuasiCompact f] (w : X → ℤ)
    (U V : X.Opens) (y : Y) :
    separableDegreeWeightedFiberSum ((U ⊔ V).ι ≫ f) (w ∘ (U ⊔ V).ι) y +
        separableDegreeWeightedFiberSum ((U ⊓ V).ι ≫ f) (w ∘ (U ⊓ V).ι) y =
      separableDegreeWeightedFiberSum (U.ι ≫ f) (w ∘ U.ι) y +
        separableDegreeWeightedFiberSum (V.ι ≫ f) (w ∘ V.ι) y := by
  have hsupp : (Function.support (separableDegreeWeightedFiberTerm f w y)).Finite :=
    separableDegreeWeightedFiberTerm_hasFiniteSupport f w y (f.finite_preimage_singleton y)
  rw [← finsum_mem_separableDegreeWeightedFiberTerm f (U ⊔ V) w y,
    ← finsum_mem_separableDegreeWeightedFiberTerm f (U ⊓ V) w y,
    ← finsum_mem_separableDegreeWeightedFiberTerm f U w y,
    ← finsum_mem_separableDegreeWeightedFiberTerm f V w y]
  simp only [TopologicalSpace.Opens.coe_sup, TopologicalSpace.Opens.coe_inf]
  exact finsum_mem_union_inter' (hsupp.subset Set.inter_subset_right)
    (hsupp.subset Set.inter_subset_right)

/-- The weighted fibre sum of the restriction of a weight to the whole source is the weighted
fibre sum itself. -/
private theorem separableDegreeWeightedFiberSum_restrict_top
    {X Y : Scheme.{u}} (f : X ⟶ Y) (w : X → ℤ) (y : Y) :
    separableDegreeWeightedFiberSum ((⊤ : X.Opens).ι ≫ f) (w ∘ (⊤ : X.Opens).ι) y =
      separableDegreeWeightedFiberSum f w y := by
  rw [← finsum_mem_separableDegreeWeightedFiberTerm f ⊤ w y,
    separableDegreeWeightedFiberSum_eq_finsum_term]
  simp only [TopologicalSpace.Opens.coe_top]
  exact finsum_mem_univ _

/-- The level sets of the weighted fibre sum of a locally quasi-finite morphism of finite
presentation to an affine scheme are locally constructible.

The source is quasi-compact and quasi-separated, so the induction principle of [Stacks, Tag
08DR] reduces the statement to an affine open of the source, the union step being the
inclusion-exclusion identity for the weighted fibre sums of the restrictions.  Each of the three
functions appearing there takes finitely many values, because the source is quasi-compact and
their level sets are already known to be locally constructible. -/
private theorem isLocallyConstructible_levelSet_of_isAffine_target
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] [LocallyQuasiFinite f]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    {w : X → ℤ} (hlevel : ∀ k : ℤ, IsLocallyConstructible {x : X | w x = k}) (n : ℤ) :
    IsLocallyConstructible {y : Y | separableDegreeWeightedFiberSum f w y = n} := by
  have : CompactSpace X := (quasiCompact_iff_compactSpace f).1 inferInstance
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have haffine : ∀ W : X.Opens, IsAffineOpen W → ∀ k : ℤ, IsLocallyConstructible
      {y : Y | separableDegreeWeightedFiberSum (W.ι ≫ f) (w ∘ W.ι) y = k} := by
    intro W hW k
    have : IsAffine W.toScheme := hW
    exact isLocallyConstructible_levelSet_of_isAffine (W.ι ≫ f)
      (fun l ↦ isLocallyConstructible_preimage W.ι (hlevel l)) k
  have hsup : ∀ U V : X.Opens, IsCompact (U : Set X) → IsAffineOpen V →
      (∀ k : ℤ, IsLocallyConstructible
        {y : Y | separableDegreeWeightedFiberSum (U.ι ≫ f) (w ∘ U.ι) y = k}) →
      (∀ k : ℤ, IsLocallyConstructible
        {y : Y | separableDegreeWeightedFiberSum (V.ι ≫ f) (w ∘ V.ι) y = k}) →
      (∀ k : ℤ, IsLocallyConstructible
        {y : Y | separableDegreeWeightedFiberSum ((U ⊓ V).ι ≫ f) (w ∘ (U ⊓ V).ι) y = k}) →
      ∀ k : ℤ, IsLocallyConstructible
        {y : Y | separableDegreeWeightedFiberSum ((U ⊔ V).ι ≫ f) (w ∘ (U ⊔ V).ι) y = k} := by
    intro U V _ _ hPU hPV hPint k
    have hPsum : ∀ l : ℤ, IsLocallyConstructible
        {y : Y | separableDegreeWeightedFiberSum (U.ι ≫ f) (w ∘ U.ι) y +
          separableDegreeWeightedFiberSum (V.ι ≫ f) (w ∘ V.ι) y = l} := fun l ↦
      isLocallyConstructible_levelSet_add hPU hPV
        (finite_range_of_isLocallyConstructible_levelSet _ hPU)
        (finite_range_of_isLocallyConstructible_levelSet _ hPV) l
    have hPneg : ∀ l : ℤ, IsLocallyConstructible
        {y : Y | -separableDegreeWeightedFiberSum ((U ⊓ V).ι ≫ f) (w ∘ (U ⊓ V).ι) y = l} :=
      fun l ↦ by simpa only [neg_eq_iff_eq_neg] using hPint (-l)
    have hset : {y : Y | separableDegreeWeightedFiberSum ((U ⊔ V).ι ≫ f)
          (w ∘ (U ⊔ V).ι) y = k} =
        {y : Y | (separableDegreeWeightedFiberSum (U.ι ≫ f) (w ∘ U.ι) y +
            separableDegreeWeightedFiberSum (V.ι ≫ f) (w ∘ V.ι) y) +
          -separableDegreeWeightedFiberSum ((U ⊓ V).ι ≫ f) (w ∘ (U ⊓ V).ι) y = k} := by
      ext y
      have h := separableDegreeWeightedFiberSum_restrict_sup_add_inf f w U V y
      simp only [Set.mem_ofPred_eq]
      omega
    rw [hset]
    refine isLocallyConstructible_levelSet_add hPsum hPneg ?_ ?_ k
    · exact finite_range_of_isLocallyConstructible_levelSet _ hPsum
    · exact finite_range_of_isLocallyConstructible_levelSet _ hPneg
  simpa only [separableDegreeWeightedFiberSum_restrict_top] using
    Stacks.AlgebraicGeometry.CompactOpenInduction.top
      (P := fun W : X.Opens ↦ ∀ k : ℤ, IsLocallyConstructible
        {y : Y | separableDegreeWeightedFiberSum (W.ι ≫ f) (w ∘ W.ι) y = k}) haffine hsup n

/-! ### The theorem -/

/-- **Stacks Project, Tag 0F3H.** Each level set of the weighted fibre sum of a weighting of a
locally quasi-finite morphism of finite presentation is locally constructible on the target.

The statement is local on the target, so one restricts to an affine open of it; the restricted
morphism is again locally quasi-finite of finite presentation and the restricted weight is again
a weighting, by [Stacks, Tag 0F3B], while the weighted fibre sum commutes with the restriction by
[Stacks, Tag 0F39]. -/
@[stacks 0F3H]
theorem isLocallyConstructible_separableDegreeWeightedFiberSum_levelSet
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] (hf : FinitePresentation f)
    (w : X → ℤ) (hw : IsWeighting f w) (n : ℤ) :
    Topology.IsLocallyConstructible
      {y : Y | separableDegreeWeightedFiberSum f w y = n} := by
  obtain ⟨hfp, hqc, hqs⟩ := hf
  let := hfp
  let := hqc
  let := hqs
  have hlevel : ∀ k : ℤ, IsLocallyConstructible {x : X | w x = k} := fun k ↦
    isLocallyConstructible_weighting_levelSet hw k
  refine (isLocallyConstructible_iff_forall_affineOpens _).mpr fun U ↦ ?_
  have : IsAffine U.1.toScheme := U.2
  have hsq : IsPullback (f ⁻¹ᵁ U.1).ι (f ∣_ U.1) f U.1.ι :=
    (isPullback_morphismRestrict f U.1).flip
  have hlocal := isLocallyConstructible_levelSet_of_isAffine_target (f ∣_ U.1)
    (w := w ∘ (f ⁻¹ᵁ U.1).ι)
    (fun k ↦ isLocallyConstructible_preimage (f ⁻¹ᵁ U.1).ι (hlevel k)) n
  have hset := preimage_levelSet_separableDegreeWeightedFiberSum f (f ⁻¹ᵁ U.1).ι (f ∣_ U.1)
    U.1.ι hsq w n
  rw [show (U.1 : Set Y) ↓∩ _ = _ from hset]
  exact hlocal.isConstructible_of_subset_of_isCompact (Set.subset_univ _) isCompact_univ

end AlgebraicGeometry

end
