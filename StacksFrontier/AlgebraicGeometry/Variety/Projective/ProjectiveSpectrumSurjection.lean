module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.Topology.KrullDimension

/-!
# `Proj` of a graded quotient is the zero locus of the kernel

Let `f : 𝒜 →+*ᵍ ℬ` be a homomorphism of graded rings satisfying the side condition
`ℬ₊ ≤ 𝒜₊.map f` under which `AlgebraicGeometry.ProjectiveSpectrum.comap f`, the map
`Proj ℬ → Proj 𝒜` on points, is defined. If `f` is surjective then `comap f` is a topological
embedding whose range is the projective zero locus of `ker f`. So `Proj ℬ` is homeomorphic to
`V₊(ker f) ⊆ Proj 𝒜`, and in particular the two have the same Krull dimension.

Both halves are the ones familiar from `Spec`: pulling back along a surjection is injective on
ideals and matches the relevant homogeneous primes of `ℬ` with those of `𝒜` containing `ker f`,
and the two Zariski topologies agree because the preimage of a zero locus is the zero locus of
the image.

Nothing here is about schemes. `AlgebraicGeometry.Proj.map f` is a closed immersion, which is
`AlgebraicGeometry.Proj.isClosedImmersion_map_of_surjective`, but the Krull dimension of a closed
subset of `Proj 𝒜` only needs the homeomorphism of underlying spaces, and that statement — unlike
`AlgebraicGeometry.Proj.map` — is available with `𝒜` and `ℬ` in different universes.

## Main results

* `AlgebraicGeometry.ProjectiveSpectrum.preimage_comap_zeroLocus`: the preimage of a zero locus
  under `comap f` is the zero locus of the image.
* `AlgebraicGeometry.ProjectiveSpectrum.range_comap_of_surjective`: **the range of `comap f` for
  a surjective `f` is the zero locus of `ker f`.**
* `AlgebraicGeometry.ProjectiveSpectrum.isEmbedding_comap_of_surjective`: `comap f` is a
  topological embedding.
* `AlgebraicGeometry.ProjectiveSpectrum.homeomorphZeroLocusKer` and
  `AlgebraicGeometry.ProjectiveSpectrum.topologicalKrullDim_zeroLocus_ker`: the resulting
  homeomorphism, and the equality of Krull dimensions it gives.

## References

* [Stacks Project, Tag 01N0](https://stacks.math.columbia.edu/tag/01N0)
-/

@[expose] public section

open Graded HomogeneousIdeal ProjectiveSpectrum Topology

namespace AlgebraicGeometry.ProjectiveSpectrum

variable {A B σ τ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f)

/-- The homogeneous prime of the image of a point under `comap f` is the pullback of its own
homogeneous prime. -/
theorem comap_asHomogeneousIdeal (p : ProjectiveSpectrum ℬ) :
    (comap f hf p).asHomogeneousIdeal = p.asHomogeneousIdeal.comap f := rfl

/-- An element lies in the homogeneous prime of the image of a point under `comap f` exactly when
its image lies in the homogeneous prime of the point. -/
theorem mem_comap_asHomogeneousIdeal (p : ProjectiveSpectrum ℬ) (a : A) :
    a ∈ (comap f hf p).asHomogeneousIdeal ↔ f a ∈ p.asHomogeneousIdeal := Iff.rfl

/-- **The preimage of a projective zero locus under `comap f` is the zero locus of the image.** -/
theorem preimage_comap_zeroLocus (s : Set A) :
    comap f hf ⁻¹' zeroLocus 𝒜 s = zeroLocus ℬ (f '' s) := by
  ext p
  simp only [Set.mem_preimage, mem_zeroLocus, Set.image_subset_iff]
  exact Iff.rfl

/-- The kernel of `f` vanishes at every point in the range of `comap f`. -/
theorem ker_le_comap_asHomogeneousIdeal (p : ProjectiveSpectrum ℬ) :
    RingHom.ker f ≤ (comap f hf p).asHomogeneousIdeal.toIdeal := fun a ha =>
  (mem_comap_asHomogeneousIdeal f hf p a).mpr (RingHom.mem_ker.mp ha ▸ zero_mem _)

/-- Pushing a relevant homogeneous prime containing `ker f` forward along a surjective `f` and
pulling it back again returns it. -/
theorem comap_map_of_ker_le (hfs : Function.Surjective f) {I : HomogeneousIdeal 𝒜}
    (hI : RingHom.ker f ≤ I.toIdeal) : (I.map f).comap f = I := by
  refine HomogeneousIdeal.toIdeal_injective ?_
  change (I.toIdeal.map f).comap f = I.toIdeal
  rw [Ideal.comap_map_of_surjective _ hfs, ← RingHom.ker_eq_comap_bot]
  exact sup_eq_left.mpr hI

/-- **The range of `comap f` for a surjective `f` is the projective zero locus of `ker f`.** A
relevant homogeneous prime of `𝒜` containing `ker f` is carried by `f` to a relevant homogeneous
prime of `ℬ` which pulls back to it: primeness is preserved because `f` is surjective with kernel
inside the ideal, and relevance because a positive-degree element of `𝒜` whose image lay in the
pushforward would itself lie in the ideal. -/
theorem range_comap_of_surjective (hfs : Function.Surjective f) :
    Set.range (comap f hf) = zeroLocus 𝒜 (RingHom.ker f) := by
  ext q
  rw [mem_zeroLocus]
  constructor
  · rintro ⟨p, rfl⟩
    exact ker_le_comap_asHomogeneousIdeal f hf p
  · intro hq
    replace hq : RingHom.ker f ≤ q.asHomogeneousIdeal.toIdeal := hq
    have hcm := comap_map_of_ker_le f hfs hq
    have hprime : (q.asHomogeneousIdeal.map f).toIdeal.IsPrime := by
      rw [HomogeneousIdeal.toIdeal_map]
      exact Ideal.map_isPrime_of_surjective hfs hq
    refine ⟨⟨q.asHomogeneousIdeal.map f, hprime, fun hirr => q.not_irrelevant_le ?_⟩,
      ProjectiveSpectrum.ext (by rw [comap_asHomogeneousIdeal, hcm])⟩
    rw [HomogeneousIdeal.irrelevant_le]
    intro i hi a ha
    exact hcm ▸ hirr (HomogeneousIdeal.mem_irrelevant_of_mem _ hi (Graded.map_mem f ha))

/-- `comap f` for a surjective `f` is injective: a relevant homogeneous prime of `ℬ` is the
pushforward of its own pullback. -/
theorem comap_injective_of_surjective (hfs : Function.Surjective f) :
    Function.Injective (comap f hf) := fun _ _ h =>
  ProjectiveSpectrum.ext (HomogeneousIdeal.toIdeal_injective
    (Ideal.comap_injective_of_surjective _ hfs
      (congrArg (·.asHomogeneousIdeal.toIdeal) h)))

/-- `comap f` for a surjective `f` is inducing: every closed subset of `Proj ℬ` is the zero locus
of some set `s`, and `zeroLocus ℬ s` is the preimage of `zeroLocus 𝒜 (f ⁻¹' s)`. -/
theorem isInducing_comap_of_surjective (hfs : Function.Surjective f) :
    IsInducing (comap f hf) where
  eq_induced := by
    refine TopologicalSpace.ext_isClosed fun Z => ⟨fun hZ => ?_, fun hZ => ?_⟩
    · obtain ⟨s, rfl⟩ := (isClosed_iff_zeroLocus ℬ Z).mp hZ
      refine isClosed_induced_iff.mpr ⟨zeroLocus 𝒜 (f ⁻¹' s), isClosed_zeroLocus _ _, ?_⟩
      rw [preimage_comap_zeroLocus, hfs.image_preimage]
    · obtain ⟨U, hU, rfl⟩ := isClosed_induced_iff.mp hZ
      exact hU.preimage (comap f hf).continuous

/-- **`comap f` for a surjective `f` is a topological embedding.** -/
theorem isEmbedding_comap_of_surjective (hfs : Function.Surjective f) :
    IsEmbedding (comap f hf) :=
  ⟨isInducing_comap_of_surjective f hf hfs, comap_injective_of_surjective f hf hfs⟩

/-- **`Proj ℬ` is homeomorphic to the zero locus of `ker f` in `Proj 𝒜`** when `f` is
surjective. -/
noncomputable def homeomorphZeroLocusKer (hfs : Function.Surjective f) :
    ProjectiveSpectrum ℬ ≃ₜ zeroLocus 𝒜 (RingHom.ker f) :=
  (isEmbedding_comap_of_surjective f hf hfs).toHomeomorph.trans
    (Homeomorph.setCongr (range_comap_of_surjective f hf hfs))

include hf in
/-- **The zero locus of `ker f` in `Proj 𝒜` has the Krull dimension of `Proj ℬ`** when `f` is
surjective. -/
theorem topologicalKrullDim_zeroLocus_ker (hfs : Function.Surjective f) :
    topologicalKrullDim (zeroLocus 𝒜 (RingHom.ker f)) =
      topologicalKrullDim (ProjectiveSpectrum ℬ) :=
  (IsHomeomorph.topologicalKrullDim_eq _
    (homeomorphZeroLocusKer f hf hfs).isHomeomorph).symm

end AlgebraicGeometry.ProjectiveSpectrum

end
