module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.Basic
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineLocallySpannedDischarge

/-!
# Generators and relations surviving a base change

Two lemmas of commutative algebra used in the affine step of the extension of modules of finite
presentation from a quasi-compact open of an affine algebraic space
(`AlgebraicGeometry.Space.exists_isFinitePresentation_extension_of_isAffineSpace`).

Let `A → C` be a flat ring map, `M` an `A`-module and `β : M → N` an `A`-linear map to a
`C`-module of finite presentation whose `C`-linear extension `C ⊗_A M → N` is bijective.  Then
finitely many elements `x_i` of `M` (containing any given one) and finitely many relations
`k_j` among them over `A` can be chosen so that the `β(x_i)` generate `N` and the images of the
`k_j` generate all relations among the `β(x_i)` over `C`
(`AlgebraicGeometry.Space.AffineExtension.exists_finset_generators_relations`).  Such generators
and relations stay generators and relations after any further base change `C → D` along which
the comparison is bijective
(`AlgebraicGeometry.Space.AffineExtension.span_range_comp_eq_top` and
`AlgebraicGeometry.Space.AffineExtension.mem_span_of_linearCombination_eq_zero`).

The relations half rests on right exactness of the tensor product, in the form
`Module.BaseChange.mem_span_image_ker_of_liftBaseChange`; flatness of `A → C` is what makes the
comparison for the `A`-span of the chosen generators injective.
-/

@[expose] public section

open TensorProduct

namespace AlgebraicGeometry.Space.AffineExtension

section BaseChange

variable {C D : Type*} [CommRing C] [CommRing D] [Algebra C D]
  {N N' : Type*} [AddCommGroup N] [Module C N] [AddCommGroup N'] [Module C N'] [Module D N']
  [IsScalarTower C D N'] (ρ : N →ₗ[C] N') {ι κ : Type*}

/-- Generators survive a base change whose comparison map is surjective. -/
theorem span_range_comp_eq_top (hρ : Function.Surjective (ρ.liftBaseChange D)) (z : ι → N)
    (hz : Submodule.span C (Set.range z) = ⊤) :
    Submodule.span D (Set.range (ρ ∘ z)) = ⊤ := by
  have h1 : Set.range ρ ⊆ Submodule.span D (Set.range (ρ ∘ z)) := by
    rintro _ ⟨n, rfl⟩
    refine Submodule.span_le_restrictScalars C D _ ?_
    rw [Set.range_comp, ← Submodule.map_span, hz]
    exact Submodule.mem_map_of_mem Submodule.mem_top
  rw [eq_top_iff, ← LinearMap.range_eq_top.2 hρ, LinearMap.range_liftBaseChange]
  exact Submodule.span_le.2 h1

/-- The coefficientwise image of a finitely supported family under `algebraMap`, as a linear
map. -/
noncomputable abbrev finsuppAlgebraMap (C D : Type*) [CommRing C] [CommRing D] [Algebra C D]
    (ι : Type*) : (ι →₀ C) →ₗ[C] (ι →₀ D) :=
  Finsupp.mapRange.linearMap (Algebra.linearMap C D)

/-- A linear map carries a linear combination to the linear combination of the images with the
coefficients mapped by `algebraMap`. -/
theorem map_linearCombination (z : ι → N) (p : ι →₀ C) :
    ρ (Finsupp.linearCombination C z p) =
      Finsupp.linearCombination D (ρ ∘ z) (finsuppAlgebraMap C D ι p) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg, map_add, map_add]
  | single i a =>
    simp only [Finsupp.linearCombination_single, map_smul, finsuppAlgebraMap,
      Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, Algebra.linearMap_apply,
      Function.comp_apply, algebraMap_smul]

omit [Module C N'] [Module D N'] [IsScalarTower C D N'] in
/-- The base change comparison of `finsuppAlgebraMap` is surjective. -/
theorem surjective_liftBaseChange_finsuppAlgebraMap :
    Function.Surjective ((finsuppAlgebraMap C D ι).liftBaseChange D) := by
  rw [← LinearMap.range_eq_top]
  refine Submodule.eq_top_iff'.2 fun x => ?_
  induction x using Finsupp.induction_linear with
  | zero => exact zero_mem _
  | add f g hf hg => exact add_mem hf hg
  | single i d =>
    refine ⟨d ⊗ₜ Finsupp.single i 1, ?_⟩
    rw [LinearMap.liftBaseChange_tmul]
    simp [Finsupp.smul_single]

/-- The linear combinations of a family are everything iff the family spans. -/
private theorem surjective_linearCombination_iff {R V : Type*} [Semiring R] [AddCommMonoid V]
    [Module R V] {z : ι → V} :
    Function.Surjective (Finsupp.linearCombination R z) ↔ Submodule.span R (Set.range z) = ⊤ := by
  rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]

/-- Relations survive a base change whose comparison map is bijective (injectivity is what is
used; surjectivity is not needed). -/
theorem mem_span_of_linearCombination_eq_zero (hρ : Function.Injective (ρ.liftBaseChange D))
    (z : ι → N) (hz : Submodule.span C (Set.range z) = ⊤) (v : κ → (ι →₀ C))
    (hv : ∀ c : ι →₀ C, Finsupp.linearCombination C z c = 0 →
      c ∈ Submodule.span C (Set.range v))
    (c : ι →₀ D) (hc : Finsupp.linearCombination D (ρ ∘ z) c = 0) :
    c ∈ Submodule.span D (Set.range (fun k => finsuppAlgebraMap C D ι (v k))) := by
  refine Submodule.span_le.2 ?_ (Module.BaseChange.mem_span_image_ker_of_liftBaseChange
    (Finsupp.linearCombination C z) (Finsupp.linearCombination D (ρ ∘ z))
    (finsuppAlgebraMap C D ι) ρ (map_linearCombination ρ z)
    surjective_liftBaseChange_finsuppAlgebraMap hρ
    (surjective_linearCombination_iff.2 hz) hc)
  rintro _ ⟨p, hp, rfl⟩
  have h := Submodule.mem_map_of_mem (f := finsuppAlgebraMap C D ι) (hv p hp)
  rw [Submodule.map_span, ← Set.range_comp] at h
  exact Submodule.span_le_restrictScalars C D _ h

end BaseChange

/-- A finitely generated submodule contained in the span of `s` is contained in the span of a
finite subset of `s`. -/
theorem exists_finset_subset_of_fg_le_span {R V : Type*} [Semiring R] [AddCommMonoid V]
    [Module R V] {K : Submodule R V} (hK : K.FG) {s : Set V} (hle : K ≤ Submodule.span R s) :
    ∃ F : Finset V, ↑F ⊆ s ∧ K ≤ Submodule.span R (F : Set V) := by
  classical
  obtain ⟨G, rfl⟩ := hK
  have hT : ∀ g ∈ G, ∃ F : Finset V, ↑F ⊆ s ∧ g ∈ Submodule.span R (F : Set V) :=
    fun g hg => Submodule.mem_span_finite_of_mem_span (hle (Submodule.subset_span hg))
  choose T hTs hTmem using hT
  refine ⟨G.attach.biUnion fun g => T g.1 g.2, fun u hu => ?_,
    Submodule.span_le.2 fun g hg => Submodule.span_mono (fun u hu => ?_) (hTmem g hg)⟩
  · obtain ⟨g, -, hug⟩ := Finset.mem_biUnion.1 (Finset.mem_coe.1 hu)
    exact hTs g.1 g.2 hug
  · exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨⟨g, hg⟩, Finset.mem_attach _ _, hu⟩)

section Generators

variable {A C : Type*} [CommRing A] [CommRing C] [Algebra A C] [Module.Flat A C]
  {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module C N]
  [IsScalarTower A C N] (β : M →ₗ[A] N)

/-- The base change comparison of `β` restricted to a submodule stays injective, by flatness. -/
theorem injective_liftBaseChange_comp_subtype (hβ : Function.Injective (β.liftBaseChange C))
    (P : Submodule A M) : Function.Injective ((β ∘ₗ P.subtype).liftBaseChange C) := by
  have heq : ∀ t, (β ∘ₗ P.subtype).liftBaseChange C t =
      β.liftBaseChange C (LinearMap.lTensor C P.subtype t) := by
    intro t
    induction t with
    | tmul a m => rfl
    | add t t' ht ht' => rw [map_add, map_add, map_add, ht, ht']
  intro t t' htt
  rw [heq, heq] at htt
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := C) P.subtype
    (Submodule.injective_subtype _) (hβ htt)

/-- Every relation over `C` among the `β (x i)` is a `C`-combination of images of relations
among the `x i` over `A`. -/
theorem mem_span_image_ker_of_linearCombination_eq_zero {ι : Type*}
    (hβ : Function.Injective (β.liftBaseChange C)) (x : ι → M) {c : ι →₀ C}
    (hc : Finsupp.linearCombination C (β ∘ x) c = 0) :
    c ∈ Submodule.span C (finsuppAlgebraMap A C ι ''
      (LinearMap.ker (Finsupp.linearCombination A x) : Set (ι →₀ A))) := by
  simpa only [LinearMap.ker_rangeRestrict] using
    Module.BaseChange.mem_span_image_ker_of_liftBaseChange
      (Finsupp.linearCombination A x).rangeRestrict (Finsupp.linearCombination C (β ∘ x))
      (finsuppAlgebraMap A C ι) (β ∘ₗ (LinearMap.range (Finsupp.linearCombination A x)).subtype)
      (map_linearCombination β x) surjective_liftBaseChange_finsuppAlgebraMap
      (injective_liftBaseChange_comp_subtype β hβ _) (LinearMap.surjective_rangeRestrict _) hc

/-- **Finitely many generators and relations over `A` which become a presentation over `C`.**
Let `A → C` be flat and let `β : M → N` be `A`-linear with bijective comparison
`C ⊗_A M → N`, `N` finitely presented over `C`.  Then for any `q ∈ M` there are a finite set
`X ⊆ M` containing `q` and finitely many relations `R` among the elements of `X` such that the
`β(x)`, `x ∈ X`, generate `N` over `C` and every relation among them over `C` is a
`C`-combination of the images of the members of `R`. -/
theorem exists_finset_generators_relations (hβ : Function.Bijective (β.liftBaseChange C))
    [Module.FinitePresentation C N] (q : M) :
    ∃ X : Finset M, q ∈ X ∧ ∃ R : Finset (X →₀ A),
      (∀ k ∈ R, Finsupp.linearCombination A (fun i : X => (i : M)) k = 0) ∧
      Submodule.span C (Set.range fun i : X => β i) = ⊤ ∧
      ∀ c : X →₀ C, Finsupp.linearCombination C (fun i : X => β i) c = 0 →
        c ∈ Submodule.span C ((finsuppAlgebraMap A C X) '' (R : Set (X →₀ A))) := by
  classical
  have hspan : Submodule.span C (Set.range β) = ⊤ := by
    rw [← LinearMap.coe_range, ← LinearMap.range_liftBaseChange, LinearMap.range_eq_top.2 hβ.2]
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule C N).FG)
  have hc : ∀ y : N, ∃ c : M →₀ C, (c.sum fun m a => a • β m) = y := fun y =>
    Finsupp.mem_span_range_iff_exists_finsupp.1 (hspan ▸ Submodule.mem_top)
  choose c hcy using hc
  let X : Finset M := insert q (s.biUnion fun y => (c y).support)
  refine ⟨X, Finset.mem_insert_self _ _, ?_⟩
  have hXspan : Submodule.span C (Set.range fun i : X => β i) = ⊤ := by
    rw [eq_top_iff, ← hs, Submodule.span_le]
    intro y hy
    rw [← hcy y, Finsupp.sum]
    refine Submodule.sum_mem _ fun m hm => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨⟨m, Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨y, hy, hm⟩)⟩, rfl⟩
  obtain ⟨U, hUsub, hU⟩ := exists_finset_subset_of_fg_le_span
    (Module.FinitePresentation.fg_ker _ (surjective_linearCombination_iff.2 hXspan)) fun c hc =>
      mem_span_image_ker_of_linearCombination_eq_zero β hβ.1 (fun i : X => (i : M))
        (LinearMap.mem_ker.1 hc)
  have hU' : ∀ u ∈ U, ∃ k ∈ LinearMap.ker (Finsupp.linearCombination A fun i : X => (i : M)),
      finsuppAlgebraMap A C X k = u := fun u hu => hUsub hu
  choose! k hkker hku using hU'
  exact ⟨U.image k, Finset.forall_mem_image.2 hkker, hXspan, fun c hc0 => Submodule.span_mono
    (fun u hu => by exact ⟨k u, Finset.mem_coe.2 (Finset.mem_image_of_mem k hu), hku u hu⟩)
    (hU (LinearMap.mem_ker.2 hc0))⟩

end Generators

end AlgebraicGeometry.Space.AffineExtension

end
