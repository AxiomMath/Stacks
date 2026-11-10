module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.CartesianEnlargement
public import StacksFrontier.CategoryTheory.Sites.Modules.DerivedCountableCoproducts
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import StacksCore.Tactic.StacksAttribute

/-!
# Factoring a map into a direct sum through a direct sum of small objects

Let `C` be a category, regarded as a site with the chaotic topology, let `O` be a presheaf of
rings on `C`, and write `|K|` for the size of an object of `D(O)`
(`Stacks.ModulesOnACategory.QuasiCoherentEquivalence.derivedObjectSize`).

Conclusion (2) of Stacks 0GYZ asserts the existence of a cardinal `κ` such that every morphism
`α : E ⟶ ⨁_n K_n` of the subcategory `QC(O)` of cartesian objects with `|E| ≤ κ` factors as
`E ⟶ ⨁_n E_n ⟶ ⨁_n K_n` for morphisms `E_n ⟶ K_n` of `QC(O)` with `|E_n| ≤ κ`. This file proves
that statement for `D(O)` in place of `QC(O)`, that is with the cartesianness demand dropped from
the source and from the summands; it is the exact analogue, for conclusion (2), of what
`Stacks.ModulesOnACategory.QuasiCoherentEquivalence.exists_nonzero_map_of_derivedObjectSize_le`
is for conclusion (1). Keeping the summands cartesian is the content of the enlargement claim of
the source's proof, which is isolated as
`Stacks.ModulesOnACategory.QuasiCoherentEquivalence.HasCartesianEnlargement` and is not used here.
Conclusion (2) for `QC(O)` is obtained from the statement proved here in
`StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.CartesianEnlargementExists`, by
replacing each summand produced here with a cartesian object of the same size bound.

The argument is the one of the source. The object `E` is represented by a complex and the
morphism `α` by an honest map of complexes out of a quasi-isomorphic complex (a right fraction in
the derived category); Stacks 0GYY shrinks that complex to a subcomplex `ℰ^•` with at most `κ`
sections, and `E_n` is taken to be the image of the `n`-th component of the resulting map
`ℰ^• ⟶ ⨁_n 𝒦_n^•`. That the map factors through `⨁_n E_n^•` is the only point needing the
concrete structure of the categories involved: a section of a coproduct of complexes of
`O`-modules is the finite sum of the images of its own components, which is proved here.

## Main definitions

* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.sigmaProj`: the projection of a coproduct
  of complexes of `O`-modules onto one of its summands.
* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.imageComplexSubmodule`: the image
  subcomplex of a map of complexes of `O`-modules.
* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.componentImage`: the image subcomplex of
  the `n`-th component of a map into a coproduct of complexes.
* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.sigmaQIso`: the comparison isomorphism
  between the image in `D(O)` of a coproduct of complexes and the coproduct of the images.

## Main results

* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.exists_finset_sum_sigma_components`: a
  section of a coproduct of complexes of `O`-modules is the finite sum of the images of its
  components.
* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.exists_factorization_componentImage`: a
  map into a coproduct of complexes factors through the coproduct of the images of its
  components.
* `exists_factorization_of_sum_of_derivedObjectSize_le`, in the same namespace: conclusion (2) of
  Stacks 0GYZ for `D(O)` in place of `QC(O)`.

## Implementation notes

The decomposition of a section of a coproduct is obtained formally, with no appeal to a
description of the coproduct in terms of sections. The sections which *are* the finite sum of the
images of their own components form a subcomplex of the coproduct, by
`decompPresheafSubmodule`, and every summand lands in it; a subcomplex of a coproduct containing
all of the summands is the whole coproduct, because the inclusions of the summands then factor
through it and their induced map is a section of its own inclusion
(`mem_of_sigma_ι_mem`). The same decomposition gives, again formally, that a coproduct of
degreewise monomorphisms is a monomorphism (`mono_sigmaMap`), which is what allows the
factorization through `⨁_n E_n^•` to be read off from the sections.

The index type of the coproducts is `J : Type` with `DecidableEq J` for the formal part and `ℕ`
for the statement about `D(O)`: the localization functor is known to preserve coproducts of
countable shape (`Stacks.SheafOfModules.derivedCategoryQ_preservesCountableCoproducts`), and
countable direct sums are what conclusion (2) and its consumer
`exists_iso_preadditiveYoneda_of_isHomological_of_sizeBound` are about.

## References

* [Stacks Project, Tag 0GYZ](https://stacks.math.columbia.edu/tag/0GYZ)
* [Stacks Project, Tag 0GYY](https://stacks.math.columbia.edu/tag/0GYY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.ModulesOnACategory.QuasiCoherentEquivalence

universe w u v r

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ RingCat.{r})

variable {J : Type} [DecidableEq J]
  (M : J → CochainComplex (PresheafOfModules.{max u v r w} O) ℤ) [HasCoproduct M]

/-- The projection of a coproduct onto one of its summands. -/
def sigmaProj (n : J) : (∐ M) ⟶ M n := Limits.Sigma.desc (Pi.single n (𝟙 (M n)))

/-- The projection onto a summand is a retraction of that summand's inclusion. -/
@[reassoc (attr := simp)]
lemma sigma_ι_sigmaProj_self (n : J) :
    Limits.Sigma.ι M n ≫ sigmaProj.{w} O M n = 𝟙 (M n) := by
  rw [sigmaProj, Limits.Sigma.ι_comp_desc, Pi.single_eq_same]

/-- The projection onto a summand kills the inclusion of a different summand. -/
@[reassoc]
lemma sigma_ι_sigmaProj_of_ne {m n : J} (h : m ≠ n) :
    Limits.Sigma.ι M m ≫ sigmaProj.{w} O M n = 0 := by
  rw [sigmaProj, Limits.Sigma.ι_comp_desc, Pi.single_eq_of_ne h]

omit [DecidableEq J] in
/-- A subcomplex of a coproduct containing the image of every summand is the whole coproduct. -/
theorem mem_of_sigma_ι_mem (N : ComplexSubmodule.{w} (∐ M))
    (hN : ∀ (n : J) (i : ℤ) (X : Cᵒᵖ) (y : ((M n).X i).obj X),
      ((Limits.Sigma.ι M n).f i).app X y ∈ (N.obj i).obj X)
    (i : ℤ) (X : Cᵒᵖ) (x : ((∐ M).X i).obj X) : x ∈ (N.obj i).obj X := by
  have hfac : ∀ n : J, ∃ t : M n ⟶ N.toComplex, t ≫ N.ι = Limits.Sigma.ι M n := fun n =>
    exists_hom_of_sectionwise_mem_range.{w} (Limits.Sigma.ι M n) N.ι
      (fun i X y => ⟨⟨_, hN n i X y⟩, rfl⟩)
  choose t ht using hfac
  have hid : Limits.Sigma.desc t ≫ N.ι = 𝟙 (∐ M) :=
    Limits.Sigma.hom_ext _ _ (fun n => by
      rw [← Category.assoc, Limits.Sigma.ι_comp_desc, ht n, Category.comp_id])
  have h2 : ((Limits.Sigma.desc t ≫ N.ι).f i).app X x = x :=
    congrArg (fun φ : (∐ M) ⟶ (∐ M) => ((φ.f i).app X) x) hid
  rw [← h2]
  exact (((Limits.Sigma.desc t).f i).app X x).property


/-! ### Decomposing a section of a coproduct into its components -/

/-- On sections: the projection onto a summand recovers a section of that summand from its
image in the coproduct. -/
lemma sigmaProj_sigma_ι_self (n : J) (i : ℤ) (X : Cᵒᵖ) (y : ((M n).X i).obj X) :
    ((sigmaProj.{w} O M n).f i).app X (((Limits.Sigma.ι M n).f i).app X y) = y := by
  exact congrArg (fun φ : M n ⟶ M n => ((φ.f i).app X) y) (sigma_ι_sigmaProj_self.{w} O M n)

/-- On sections: the projection onto a summand kills the image of a section of a different
summand. -/
lemma sigmaProj_sigma_ι_of_ne {m n : J} (h : n ≠ m) (i : ℤ) (X : Cᵒᵖ)
    (y : ((M n).X i).obj X) :
    ((sigmaProj.{w} O M m).f i).app X (((Limits.Sigma.ι M n).f i).app X y) = 0 := by
  exact congrArg (fun φ : M n ⟶ M m => ((φ.f i).app X) y) (sigma_ι_sigmaProj_of_ne.{w} O M h)

/-- A section which is the sum, over a finite set of indices, of the images of its own
components has vanishing components outside that set. -/
lemma sigmaProj_eq_zero_of_notMem {s : Finset J} {i : ℤ} {X : Cᵒᵖ}
    {x : ((∐ M).X i).obj X}
    (hx : x = ∑ n ∈ s, ((Limits.Sigma.ι M n).f i).app X
      (((sigmaProj.{w} O M n).f i).app X x))
    {m : J} (hm : m ∉ s) : ((sigmaProj.{w} O M m).f i).app X x = 0 := by
  conv_lhs => rw [hx]
  rw [map_sum]
  refine Finset.sum_eq_zero (fun n hn => ?_)
  exact sigmaProj_sigma_ι_of_ne.{w} O M (fun hnm => hm (by subst hnm; exact hn)) i X _

/-- Such a presentation of a section may be enlarged to any bigger finite set of indices, the
extra components being zero. -/
lemma sigma_sum_eq_of_subset {s t : Finset J} (hst : s ⊆ t) {i : ℤ} {X : Cᵒᵖ}
    {x : ((∐ M).X i).obj X}
    (hx : x = ∑ n ∈ s, ((Limits.Sigma.ι M n).f i).app X
      (((sigmaProj.{w} O M n).f i).app X x)) :
    x = ∑ n ∈ t, ((Limits.Sigma.ι M n).f i).app X
      (((sigmaProj.{w} O M n).f i).app X x) := by
  refine hx.trans (Finset.sum_subset hst (fun n _ hn => ?_))
  rw [sigmaProj_eq_zero_of_notMem.{w} O M hx hn, map_zero]


omit [DecidableEq J] in
/-- The inclusion of a summand commutes with the differentials, read on sections. -/
lemma sigma_ι_d_apply (n : J) (i j : ℤ) (X : Cᵒᵖ) (z : ((M n).X i).obj X) :
    (((∐ M).d i j).app X) ((((Limits.Sigma.ι M n).f i).app X) z) =
      (((Limits.Sigma.ι M n).f j).app X) ((((M n).d i j).app X) z) := by
  exact congrArg (fun φ : (M n).X i ⟶ (∐ M).X j => (φ.app X) z)
    ((Limits.Sigma.ι M n).comm i j)

/-- The projection onto a summand commutes with the differentials, read on sections. -/
lemma sigmaProj_d_apply (n : J) (i j : ℤ) (X : Cᵒᵖ) (x : ((∐ M).X i).obj X) :
    (((M n).d i j).app X) ((((sigmaProj.{w} O M n).f i).app X) x) =
      (((sigmaProj.{w} O M n).f j).app X) ((((∐ M).d i j).app X) x) := by
  exact congrArg (fun φ : (∐ M).X i ⟶ (M n).X j => (φ.app X) x)
    ((sigmaProj.{w} O M n).comm i j)

/-- The sections of `∐ M` in degree `i` which are the finite sum of the images of their own
components under the inclusions of the summands. -/
def decompPresheafSubmodule (i : ℤ) : ((∐ M).X i).Submodule where
  obj X :=
    { carrier := {x | ∃ s : Finset J, x = ∑ n ∈ s,
        ((Limits.Sigma.ι M n).f i).app X (((sigmaProj.{w} O M n).f i).app X x)}
      zero_mem' := ⟨∅, by simp⟩
      add_mem' := by
        rintro x y ⟨s, hs⟩ ⟨t, ht⟩
        have hs' := sigma_sum_eq_of_subset.{w} O M (Finset.subset_union_left (s₂ := t)) hs
        have ht' := sigma_sum_eq_of_subset.{w} O M (Finset.subset_union_right (s₁ := s)) ht
        refine ⟨s ∪ t, ?_⟩
        have key : ∑ n ∈ s ∪ t, ((Limits.Sigma.ι M n).f i).app X
              (((sigmaProj.{w} O M n).f i).app X (x + y)) =
            (∑ n ∈ s ∪ t, ((Limits.Sigma.ι M n).f i).app X
              (((sigmaProj.{w} O M n).f i).app X x)) +
            ∑ n ∈ s ∪ t, ((Limits.Sigma.ι M n).f i).app X
              (((sigmaProj.{w} O M n).f i).app X y) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun n _ => by rw [map_add, map_add])
        rw [key, ← hs', ← ht']
      smul_mem' := by
        rintro c x ⟨s, hs⟩
        refine ⟨s, ?_⟩
        have key : ∑ n ∈ s, ((Limits.Sigma.ι M n).f i).app X
              (((sigmaProj.{w} O M n).f i).app X (c • x)) =
            c • ∑ n ∈ s, ((Limits.Sigma.ι M n).f i).app X
              (((sigmaProj.{w} O M n).f i).app X x) := by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl (fun n _ => by rw [map_smul, map_smul])
        rw [key, ← hs] }
  map := by
    rintro X Y f x ⟨s, hs⟩
    refine ⟨s, ?_⟩
    simp only [PresheafOfModules.restrictₛₗ_apply]
    have h := congrArg (fun z => ((∐ M).X i).map f z) hs
    simp only [map_sum] at h
    refine h.trans (Finset.sum_congr rfl (fun n _ => ?_))
    rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply]

/-- Membership in `decompPresheafSubmodule` is the stated presentation as a finite sum. -/
lemma mem_decompPresheafSubmodule (i : ℤ) (X : Cᵒᵖ) (x : ((∐ M).X i).obj X) :
    x ∈ (decompPresheafSubmodule.{w} O M i).obj X ↔
      ∃ s : Finset J, x = ∑ n ∈ s, ((Limits.Sigma.ι M n).f i).app X
        (((sigmaProj.{w} O M n).f i).app X x) := Iff.rfl

/-- The subcomplex of `∐ M` cut out by `decompPresheafSubmodule`. -/
def decompSubmodule : ComplexSubmodule.{w} (∐ M) where
  obj i := decompPresheafSubmodule.{w} O M i
  d_mem i j X x hx := by
    rw [mem_decompPresheafSubmodule] at hx
    rw [mem_decompPresheafSubmodule]
    obtain ⟨s, hs⟩ := hx
    refine ⟨s, ?_⟩
    have h := congrArg (fun z => (((∐ M).d i j).app X) z) hs
    simp only [map_sum] at h
    refine h.trans (Finset.sum_congr rfl (fun n _ => ?_))
    rw [sigma_ι_d_apply.{w} O M, sigmaProj_d_apply.{w} O M]

/-- **Every section of a coproduct of complexes of `O`-modules is the finite sum of the images
of its components.** -/
theorem exists_finset_sum_sigma_components (i : ℤ) (X : Cᵒᵖ) (x : ((∐ M).X i).obj X) :
    ∃ s : Finset J, x = ∑ n ∈ s, ((Limits.Sigma.ι M n).f i).app X
      (((sigmaProj.{w} O M n).f i).app X x) := by
  rw [← mem_decompPresheafSubmodule]
  refine mem_of_sigma_ι_mem.{w} O M (decompSubmodule.{w} O M) (fun n i X y => ?_) i X x
  rw [show (decompSubmodule.{w} O M).obj i = decompPresheafSubmodule.{w} O M i from rfl,
    mem_decompPresheafSubmodule]
  exact ⟨{n}, by rw [Finset.sum_singleton, sigmaProj_sigma_ι_self.{w} O M]⟩


/-! ### The image subcomplex of a map of complexes -/

section Image

variable {O}
variable {S F : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ}

/-- The image subcomplex of a map of complexes of `O`-modules: in degree `i` it is the range
of the map in that degree, which is stable under the differentials because the map commutes
with them. -/
def imageComplexSubmodule (c : S ⟶ F) : ComplexSubmodule.{w} F where
  obj i := PresheafOfModules.Submodule.range (c.f i)
  d_mem i j X x hx := by
    obtain ⟨y, rfl⟩ := hx
    refine ⟨((S.d i j).app X) y, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← PresheafOfModules.comp_app, ← c.comm i j,
      PresheafOfModules.comp_app, ConcreteCategory.comp_apply]

/-- A map of complexes factors as a degreewise epimorphism onto its image subcomplex followed
by the inclusion of that subcomplex. -/
theorem exists_epi_factor_imageComplexSubmodule (c : S ⟶ F) :
    ∃ k : S ⟶ (imageComplexSubmodule.{w} c).toComplex,
      (∀ i, Epi (k.f i)) ∧ k ≫ (imageComplexSubmodule.{w} c).ι = c := by
  obtain ⟨k, hk⟩ := exists_hom_of_sectionwise_mem_range.{w} c (imageComplexSubmodule.{w} c).ι
    (fun i X x => ⟨⟨_, ⟨x, rfl⟩⟩, rfl⟩)
  refine ⟨k, fun i => PresheafOfModules.epi_of_surjective (fun X z => ?_), hk⟩
  obtain ⟨y, hy⟩ := z.property
  refine ⟨y, Subtype.ext ?_⟩
  exact (congrArg (fun φ : S ⟶ F => ((φ.f i).app X) y) hk).trans hy

/-- The image subcomplex of a map of complexes has at most as many sections as the source. -/
lemma complexSectionSize_imageComplexSubmodule_le (c : S ⟶ F) :
    complexSectionSize.{w} O (imageComplexSubmodule.{w} c).toComplex ≤
      complexSectionSize.{w} O S := by
  obtain ⟨k, hk, -⟩ := exists_epi_factor_imageComplexSubmodule.{w} c
  exact complexSectionSize_le_of_epi_f.{w} O k hk

end Image

/-! ### A coproduct of inclusions of subcomplexes is a monomorphism -/

section MonoSigmaMap

variable {A B : J → CochainComplex (PresheafOfModules.{max u v r w} O) ℤ}
  [HasCoproduct A] [HasCoproduct B]

/-- A coproduct of maps followed by a projection is the corresponding projection followed by
that map. -/
lemma sigmaMap_comp_sigmaProj (φ : ∀ n, A n ⟶ B n) (m : J) :
    Limits.Sigma.map φ ≫ sigmaProj.{w} O B m = sigmaProj.{w} O A m ≫ φ m := by
  refine Limits.Sigma.hom_ext _ _ (fun n => ?_)
  rw [← Category.assoc, Limits.Sigma.ι_map, Category.assoc]
  by_cases h : n = m
  · subst h
    rw [sigma_ι_sigmaProj_self.{w} O B, sigma_ι_sigmaProj_self_assoc.{w} O A, Category.comp_id]
  · rw [sigma_ι_sigmaProj_of_ne.{w} O B h, sigma_ι_sigmaProj_of_ne_assoc.{w} O A h,
      comp_zero, zero_comp]

omit [DecidableEq J] in
/-- The inclusion of a summand followed by a coproduct of maps. -/
@[reassoc]
lemma sigma_ι_comp_sigmaMap (φ : ∀ n, A n ⟶ B n) (n : J) :
    Limits.Sigma.ι A n ≫ Limits.Sigma.map φ = φ n ≫ Limits.Sigma.ι B n := by
  simp

omit [DecidableEq J] in
/-- A coproduct of degreewise monomorphisms of complexes is a monomorphism. -/
lemma mono_sigmaMap (φ : ∀ n, A n ⟶ B n) (hφ : ∀ (n : J) (i : ℤ), Mono ((φ n).f i)) :
    Mono (Limits.Sigma.map φ) := by
  classical
  refine HomologicalComplex.mono_of_mono_f _ (fun i => ?_)
  refine PresheafOfModules.mono_of_injective (fun X => ?_)
  rw [injective_iff_map_eq_zero]
  intro y hy
  have hcomp : ∀ m : J, ((φ m).f i).app X (((sigmaProj.{w} O A m).f i).app X y) = 0 := by
    intro m
    have h := congrArg (fun ψ : (∐ A) ⟶ B m => ((ψ.f i).app X) y)
      (sigmaMap_comp_sigmaProj.{w} O φ m)
    exact h.symm.trans (by
      change ((sigmaProj.{w} O B m).f i).app X (((Limits.Sigma.map φ).f i).app X y) = 0
      rw [hy, map_zero])
  have hzero : ∀ m : J, ((sigmaProj.{w} O A m).f i).app X y = 0 := by
    intro m
    have := hφ m i
    exact (injective_iff_map_eq_zero _).1
      (PresheafOfModules.injective_of_mono ((φ m).f i) X) _ (hcomp m)
  obtain ⟨s, hs⟩ := exists_finset_sum_sigma_components.{w} O A i X y
  rw [hs]
  exact Finset.sum_eq_zero (fun n _ => by rw [hzero n, map_zero])

end MonoSigmaMap


/-! ### Factoring a map into a coproduct through the coproduct of the component images -/

section Factorization

variable {K : J → CochainComplex (PresheafOfModules.{max u v r w} O) ℤ} [HasCoproduct K]
  {S : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ}

/-- The image subcomplex of the `n`-th component of a map into a coproduct of complexes. -/
def componentImage (c : S ⟶ ∐ K) (n : J) : ComplexSubmodule.{w} (K n) :=
  imageComplexSubmodule.{w} (c ≫ sigmaProj.{w} O K n)

/-- **A map into a coproduct of complexes factors through the coproduct of the images of its
components.** Each section of the target is the finite sum of the images of its components, and
the component of a section in the image of the map lies in the image of that component of the
map. -/
theorem exists_factorization_componentImage (c : S ⟶ ∐ K) :
    ∃ β : S ⟶ ∐ (fun n => (componentImage.{w} O c n).toComplex),
      β ≫ Limits.Sigma.map (fun n => (componentImage.{w} O c n).ι) = c := by
  have hmono : Mono (Limits.Sigma.map (fun n => (componentImage.{w} O c n).ι)) :=
    mono_sigmaMap.{w} O _ (fun n i => by
      rw [ComplexSubmodule.ι_f]
      exact PresheafOfModules.mono_of_injective (fun X => Subtype.val_injective))
  refine exists_hom_of_sectionwise_mem_range.{w} c _ (fun i X x => ?_)
  have hmem : ∀ n : J, (((sigmaProj.{w} O K n).f i).app X) (((c.f i).app X) x) ∈
      ((componentImage.{w} O c n).obj i).obj X := fun n => ⟨x, rfl⟩
  obtain ⟨s, hs⟩ := exists_finset_sum_sigma_components.{w} O K i X (((c.f i).app X) x)
  refine ⟨∑ n ∈ s,
    ((Limits.Sigma.ι (fun m => (componentImage.{w} O c m).toComplex) n).f i).app X
      ⟨_, hmem n⟩, ?_⟩
  rw [map_sum]
  refine Eq.trans (Finset.sum_congr rfl (fun n _ => ?_)) hs.symm
  exact congrArg
    (fun ψ : (componentImage.{w} O c n).toComplex ⟶ (∐ K) =>
      ((ψ.f i).app X) (⟨_, hmem n⟩ : ((componentImage.{w} O c n).toComplex.X i).obj X))
    (sigma_ι_comp_sigmaMap.{w} O (fun m => (componentImage.{w} O c m).ι) n)

end Factorization


/-! ### Coproducts in the derived category -/

section Derived

/-- The localization functor carries the coproduct of a countable family of complexes of
`O`-modules to the coproduct of their images. -/
def isColimitCofanQSigma (M : ℕ → CochainComplex (PresheafOfModules.{max u v r w} O) ℤ) :
    IsColimit (Cofan.mk (DerivedCategory.Q.obj (∐ M))
      (fun n => DerivedCategory.Q.map (Limits.Sigma.ι M n))) := by
  haveI := Stacks.SheafOfModules.derivedCategoryQ_preservesCountableCoproducts O ℕ
  exact (isColimitMapCoconeCofanMkEquiv DerivedCategory.Q M (Limits.Sigma.ι M))
    (isColimitOfPreserves DerivedCategory.Q (coproductIsCoproduct M))

/-- The comparison isomorphism between the image of a coproduct of complexes and the coproduct
of the images. -/
def sigmaQIso (M : ℕ → CochainComplex (PresheafOfModules.{max u v r w} O) ℤ) :
    DerivedCategory.Q.obj (∐ M) ≅ ∐ (fun n => DerivedCategory.Q.obj (M n)) :=
  (isColimitCofanQSigma.{w} O M).coconePointUniqueUpToIso
    (coproductIsCoproduct (fun n => DerivedCategory.Q.obj (M n)))

/-- The comparison isomorphism `sigmaQIso` matches the inclusions of the summands. -/
@[reassoc]
lemma Q_sigma_ι_comp_sigmaQIso_hom
    (M : ℕ → CochainComplex (PresheafOfModules.{max u v r w} O) ℤ) (n : ℕ) :
    DerivedCategory.Q.map (Limits.Sigma.ι M n) ≫ (sigmaQIso.{w} O M).hom =
      Limits.Sigma.ι (fun m => DerivedCategory.Q.obj (M m)) n := by
  have h := (isColimitCofanQSigma.{w} O M).comp_coconePointUniqueUpToIso_hom
    (coproductIsCoproduct (fun m => DerivedCategory.Q.obj (M m))) ⟨n⟩
  simpa only [Cofan.mk_ι_app, coproductIsCoproduct, Cofan.mk_pt, sigmaQIso] using h

end Derived


/-! ### Conclusion (2) of Stacks 0GYZ for `D(O)` -/

/-- **Conclusion (2) of Stacks 0GYZ with the cartesianness demand dropped.** There is a cardinal
`κ₀`, depending only on the category and its presheaf of rings, such that for every cardinal `κ`
above it, every morphism from an object of `D(O)` of size at most `κ` into a countable direct sum
factors through a direct sum of objects of size at most `κ` mapping to the summands.

The conclusion is stated at every `κ ≥ κ₀` rather than at `κ₀` alone — which is the source's
form, recovered by taking `κ = κ₀` — because the hypothesis and the conclusion both read `≤ κ`,
so the property is monotone in neither direction and the form at a single cardinal cannot be
combined with conclusion (1) at one cardinal, as Stacks 0GYZ asserts it is. -/
@[stacks 0GYZ "part (2) for D(O) in place of QC(O): cartesianness dropped from the source \
  and from the summands"]
theorem exists_factorization_of_sum_of_derivedObjectSize_le :
    ∃ κ₀ : Cardinal.{max u v r w}, ∀ κ : Cardinal.{max u v r w}, κ₀ ≤ κ →
      ∀ (E : DMod.{w} O) (K : ℕ → DMod.{w} O) (α : E ⟶ ∐ K),
        derivedObjectSize.{w} O E ≤ κ →
        ∃ (E' : ℕ → DMod.{w} O) (f : ∀ n, E' n ⟶ K n) (β : E ⟶ ∐ E'),
          (∀ n, derivedObjectSize.{w} O (E' n) ≤ κ) ∧ α = β ≫ Limits.Sigma.map f := by
  classical
  obtain ⟨kappa, hkappa⟩ :=
    Stacks.ModulesOnACategory.exists_small_quasiIso_subcomplex_presheaf.{w}
      (chaoticRingSheaf.{u, v, r} O)
  have hkappa' : ∀ (F : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ)
      (L : DMod.{w} O), Nonempty (DerivedCategory.Q.obj F ≅ L) →
      ∃ (H : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ) (h : H ⟶ F),
        Mono h ∧ QuasiIso h ∧
          complexSectionSize.{w} O H ≤ max kappa (derivedObjectSize.{w} O L) := hkappa
  clear hkappa
  refine ⟨kappa, fun kap hkap E K alpha hE => ?_⟩
  -- representatives of the summands, and the comparison isomorphism for the coproduct
  choose Kc hKc _ using fun n : ℕ => exists_representative_of_derivedObjectSize.{w} O (K n)
  set e : ∀ n, DerivedCategory.Q.obj (Kc n) ≅ K n := fun n => (hKc n).some with he
  set eps : DerivedCategory.Q.obj (∐ Kc) ≅ ∐ K :=
    sigmaQIso.{w} O Kc ≪≫ Limits.Sigma.mapIso e with heps_def
  have heps : ∀ n, DerivedCategory.Q.map (Limits.Sigma.ι Kc n) ≫ eps.hom =
      (e n).hom ≫ Limits.Sigma.ι K n := by
    intro n
    rw [heps_def, Iso.trans_hom, Q_sigma_ι_comp_sigmaQIso_hom_assoc,
      Limits.Sigma.ι_mapIso_hom]
  -- a representative of the source, and the chain-level model of `alpha`
  obtain ⟨E0, hE0, -⟩ := exists_representative_of_derivedObjectSize.{w} O E
  set eE : DerivedCategory.Q.obj E0 ≅ E := hE0.some with heE
  obtain ⟨E1, sq, hsq, g, hfac⟩ :=
    DerivedCategory.right_fac (eE.hom ≫ alpha ≫ eps.inv)
  have : IsIso (DerivedCategory.Q.map sq) := hsq
  obtain ⟨Ec, jc, hjmono, hjqi, hjsize⟩ :=
    hkappa' E1 E ⟨asIso (DerivedCategory.Q.map sq) ≪≫ eE⟩
  have : IsIso (DerivedCategory.Q.map jc) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]; exact hjqi
  have hsize : complexSectionSize.{w} O Ec ≤ kap := hjsize.trans (max_le hkap hE)
  -- the chain-level factorization through the coproduct of the component images
  set comp : ℕ → CochainComplex (PresheafOfModules.{max u v r w} O) ℤ :=
    fun n => (componentImage.{w} O (jc ≫ g) n).toComplex with hcomp
  set iota : ∀ n, comp n ⟶ Kc n := fun n => (componentImage.{w} O (jc ≫ g) n).ι with hiota
  obtain ⟨b0, hb0⟩ := exists_factorization_componentImage.{w} O (jc ≫ g)
  set theta : DerivedCategory.Q.obj Ec ≅ E :=
    asIso (DerivedCategory.Q.map jc) ≪≫ asIso (DerivedCategory.Q.map sq) ≪≫ eE with htheta
  refine ⟨fun n => DerivedCategory.Q.obj (comp n),
    fun n => DerivedCategory.Q.map (iota n) ≫ (e n).hom,
    theta.inv ≫ DerivedCategory.Q.map b0 ≫ (sigmaQIso.{w} O comp).hom, ?_, ?_⟩
  · intro n
    refine (derivedObjectSize_le_complexSectionSize.{w} O (comp n)).trans ?_
    exact (complexSectionSize_imageComplexSubmodule_le.{w}
      ((jc ≫ g) ≫ sigmaProj.{w} O Kc n)).trans hsize
  · -- the two factorizations agree
    have key : (sigmaQIso.{w} O comp).hom ≫
          Limits.Sigma.map (fun n => DerivedCategory.Q.map (iota n) ≫ (e n).hom) =
        DerivedCategory.Q.map (Limits.Sigma.map iota) ≫ eps.hom := by
      refine Cofan.IsColimit.hom_ext (isColimitCofanQSigma.{w} O comp) _ _ (fun n => ?_)
      simp only [Cofan.inj, Cofan.mk_ι_app]
      rw [← Category.assoc, Q_sigma_ι_comp_sigmaQIso_hom, Limits.Sigma.ι_map,
        ← Category.assoc, ← DerivedCategory.Q.map_comp,
        sigma_ι_comp_sigmaMap.{w} O iota n, DerivedCategory.Q.map_comp]
      simp only [Category.assoc]
      rw [heps n]
    have h1 : eE.hom ≫ alpha =
        inv (DerivedCategory.Q.map sq) ≫ DerivedCategory.Q.map g ≫ eps.hom := by
      rw [← Category.assoc, ← hfac, Category.assoc, Category.assoc, Iso.inv_hom_id,
        Category.comp_id]
    have hthetaα : theta.hom ≫ alpha = DerivedCategory.Q.map (jc ≫ g) ≫ eps.hom := by
      rw [htheta, Iso.trans_hom, Iso.trans_hom, asIso_hom, asIso_hom,
        DerivedCategory.Q.map_comp]
      simp only [Category.assoc]
      rw [h1]
      simp
    rw [Category.assoc, Category.assoc, key, ← Category.assoc (DerivedCategory.Q.map b0),
      ← DerivedCategory.Q.map_comp, hb0, ← hthetaα, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]

end Stacks.ModulesOnACategory.QuasiCoherentEquivalence

end
