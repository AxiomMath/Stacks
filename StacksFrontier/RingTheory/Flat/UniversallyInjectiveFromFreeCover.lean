module

public import StacksFrontier.RingTheory.Flat.MittagLeffler

/-!
# Universal injectivity from a free cover of the source

Let `(R, 𝔪)` be a local ring, `M` a flat `R`-module and `u : N → M` an `R`-linear map whose
reduction `N/𝔪N → M/𝔪M` is injective.  Suppose that `N` is covered, after tensoring with a test
module `Q`, by free `R`-modules mapping to `N` with injective reductions modulo `𝔪`.  Then
`u ⊗ id_Q` is injective.

This is the first paragraph of the proof of Stacks 0AT3, stripped of the colimit language.  The
source presents `N` as a filtered colimit of free modules `F_i` with transition maps injective
modulo `𝔪` (Stacks 05U7) and observes that each composite `F_i → N → M` is `R`-universally
injective by Stacks 05FQ, hence so is the colimit.  What the argument actually uses is only that
every element of `N ⊗ Q` comes from some `F_i ⊗ Q` and that each leg `F_i → N` is injective
modulo `𝔪`; no cocone, no colimit and no directedness of the index are needed.  Stating it this
way means a producer has to supply a *family* of free modules over `N`, which is strictly less
than a filtered colimit presentation.

Compare `AlgebraicGeometry.universallyInjective_of_colimit_free` in
`StacksFrontier.AlgebraicGeometry.Flatness.Flattening.HenselianColimitFreeStep`, which is the same
conclusion from the colimit presentation in the shape Stacks 05U7 states it.

## Main results

* `Module.Flat.rTensor_injective_of_free_cover`: the statement above, for one test module.
* `Module.Flat.universallyInjective_of_free_cover`: the same for every test module at once.
* `Module.Flat.exists_rTensor_eq_of_forall_finset`: the cover hypothesis in elementwise form — it
  is enough that every finite set of elements of `N` lifts through a single `φ i`.
* `Module.Flat.universallyInjective_of_free_cover_of_forall_finset`: the conclusion from that
  elementwise form, which is the interface a geometric producer can meet.

## Implementation notes

The reduction hypotheses are spelled out as `u x ∈ 𝔪 • ⊤ → x ∈ 𝔪 • ⊤`, the form
`Submodule.injective_mapQ_smul_top_iff` shows to be equivalent to injectivity of the induced map
on the quotients, and the form in which Stacks 05FQ
(`Module.Flat.rTensor_injective_of_projective_of_mem_maximalIdeal_smul_top`) consumes them.

All the modules live in a single universe `v` with `Small.{v} R`, which is the universe
restriction Stacks 05FQ carries in this repository.

## References

* [Stacks Project, Tag 0AT3](https://stacks.math.columbia.edu/tag/0AT3)
* [Stacks Project, Tag 05FQ](https://stacks.math.columbia.edu/tag/05FQ)
* [Stacks Project, Tag 05U7](https://stacks.math.columbia.edu/tag/05U7)
-/

@[expose] public section

open IsLocalRing

universe u v w

namespace Module.Flat

/-- **Universal injectivity at one test module from a free cover of the source.** -/
theorem rTensor_injective_of_free_cover
    {R : Type u} [CommRing R] [IsLocalRing R] [Small.{v} R]
    {N : Type v} [AddCommGroup N] [Module R N]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Flat R M]
    {ι : Type w} {F : ι → Type v} [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)]
    [∀ i, Module.Free R (F i)] (φ : ∀ i, F i →ₗ[R] N)
    (hφ : ∀ (i : ι) (x : F i), φ i x ∈ maximalIdeal R • (⊤ : Submodule R N) →
      x ∈ maximalIdeal R • (⊤ : Submodule R (F i)))
    (u : N →ₗ[R] M)
    (hu : ∀ y : N, u y ∈ maximalIdeal R • (⊤ : Submodule R M) →
      y ∈ maximalIdeal R • (⊤ : Submodule R N))
    (Q : Type v) [AddCommGroup Q] [Module R Q]
    (hcover : ∀ ξ : TensorProduct R N Q, ∃ (i : ι) (η : TensorProduct R (F i) Q),
      (φ i).rTensor Q η = ξ) :
    Function.Injective (u.rTensor Q) := by
  rw [injective_iff_map_eq_zero]
  intro ξ hξ
  obtain ⟨i, η, rfl⟩ := hcover ξ
  have hui :=
    Module.Flat.rTensor_injective_of_projective_of_mem_maximalIdeal_smul_top (u ∘ₗ φ i)
      (fun x hx ↦ hφ i x (hu _ hx)) Q
  rw [injective_iff_map_eq_zero] at hui
  rw [hui η (by rw [LinearMap.rTensor_comp, LinearMap.comp_apply, hξ]), map_zero]

/-- **Universal injectivity from a free cover of the source**, for every test module. -/
theorem universallyInjective_of_free_cover
    {R : Type u} [CommRing R] [IsLocalRing R] [Small.{v} R]
    {N : Type v} [AddCommGroup N] [Module R N]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Flat R M]
    {ι : Type w} {F : ι → Type v} [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)]
    [∀ i, Module.Free R (F i)] (φ : ∀ i, F i →ₗ[R] N)
    (hφ : ∀ (i : ι) (x : F i), φ i x ∈ maximalIdeal R • (⊤ : Submodule R N) →
      x ∈ maximalIdeal R • (⊤ : Submodule R (F i)))
    (u : N →ₗ[R] M)
    (hu : ∀ y : N, u y ∈ maximalIdeal R • (⊤ : Submodule R M) →
      y ∈ maximalIdeal R • (⊤ : Submodule R N))
    (hcover : ∀ (Q : Type v) [AddCommGroup Q] [Module R Q] (ξ : TensorProduct R N Q),
      ∃ (i : ι) (η : TensorProduct R (F i) Q), (φ i).rTensor Q η = ξ) :
    ∀ (Q : Type v) [AddCommGroup Q] [Module R Q], Function.Injective (u.rTensor Q) :=
  fun Q _ _ ↦ rTensor_injective_of_free_cover φ hφ u hu Q (hcover Q)

/-- **The cover hypothesis in elementwise form.** If every finite set of elements of `N` lifts
through a single `φ i`, then every element of `N ⊗ Q` comes from `F i ⊗ Q` for a single `i`.

This is the convenient interface: a producer only has to exhibit, for finitely many elements of
`N` at a time, one free module above them — which for `N` a stalk means one neighbourhood small
enough to carry all of them. -/
theorem exists_rTensor_eq_of_forall_finset
    {R : Type u} [CommRing R]
    {N : Type v} [AddCommGroup N] [Module R N]
    {ι : Type w} {F : ι → Type v} [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)]
    (φ : ∀ i, F i →ₗ[R] N)
    (hcover : ∀ t : Finset N, ∃ (i : ι) (g : N → F i), ∀ x ∈ t, φ i (g x) = x)
    (Q : Type v) [AddCommGroup Q] [Module R Q] (ξ : TensorProduct R N Q) :
    ∃ (i : ι) (η : TensorProduct R (F i) Q), (φ i).rTensor Q η = ξ := by
  classical
  obtain ⟨T, hT⟩ := TensorProduct.exists_finset ξ
  obtain ⟨i, g, hg⟩ := hcover (T.image Prod.fst)
  refine ⟨i, ∑ z ∈ T, (g z.1) ⊗ₜ[R] z.2, ?_⟩
  rw [hT, map_sum]
  refine Finset.sum_congr rfl fun z hz ↦ ?_
  rw [LinearMap.rTensor_tmul, hg z.1 (Finset.mem_image.2 ⟨z, hz, rfl⟩)]

/-- **Universal injectivity from a free cover given elementwise.** -/
theorem universallyInjective_of_free_cover_of_forall_finset
    {R : Type u} [CommRing R] [IsLocalRing R] [Small.{v} R]
    {N : Type v} [AddCommGroup N] [Module R N]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Flat R M]
    {ι : Type w} {F : ι → Type v} [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)]
    [∀ i, Module.Free R (F i)] (φ : ∀ i, F i →ₗ[R] N)
    (hφ : ∀ (i : ι) (x : F i), φ i x ∈ maximalIdeal R • (⊤ : Submodule R N) →
      x ∈ maximalIdeal R • (⊤ : Submodule R (F i)))
    (u : N →ₗ[R] M)
    (hu : ∀ y : N, u y ∈ maximalIdeal R • (⊤ : Submodule R M) →
      y ∈ maximalIdeal R • (⊤ : Submodule R N))
    (hcover : ∀ t : Finset N, ∃ (i : ι) (g : N → F i), ∀ x ∈ t, φ i (g x) = x) :
    ∀ (Q : Type v) [AddCommGroup Q] [Module R Q], Function.Injective (u.rTensor Q) :=
  universallyInjective_of_free_cover φ hφ u hu
    fun Q _ _ ↦ exists_rTensor_eq_of_forall_finset φ hcover Q

end Module.Flat

end
