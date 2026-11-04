module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksFrontier.AlgebraicGeometry.ProjShared.RelevantCover
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpectrum.Topology
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The open on which a graded ring homomorphism induces a morphism of projective spectra

A homomorphism `ψ : 𝒜 →+*ᵍ ℬ` of nonnegatively graded rings does not in general induce a
morphism `Proj ℬ ⟶ Proj 𝒜`: a relevant homogeneous prime of `B` can pull back to an irrelevant
one. It does induce a morphism on the open

`U(ψ) = ⋃ D₊(ψ f)`,  `f` homogeneous of positive degree,

and that open is the subject of this file. Mathlib constructs the morphism only under the
hypothesis `ℬ₊ ≤ 𝒜₊.map ψ` (`AlgebraicGeometry.Proj.map`), which forces `U(ψ) = ⊤`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjShared.mapDomain`: the open `U(ψ)`.

## Main results

* `Stacks.AlgebraicGeometry.ProjShared.mem_mapDomain_iff` and
  `Stacks.AlgebraicGeometry.ProjShared.notMem_mapDomain_iff`: the pointwise descriptions, the
  second identifying the closed complement as the projective zero locus of `𝒜₊.map ψ`.
* `Stacks.AlgebraicGeometry.ProjShared.mapDomain_eq_top_iff_irrelevant_le_radical`: `U(ψ) = ⊤`
  if and only if `ℬ₊` lies in the **radical** of `𝒜₊.map ψ`.
* `Stacks.AlgebraicGeometry.ProjShared.mapDomain_eq_top_of_irrelevant_le_map`: Mathlib's
  hypothesis for `AlgebraicGeometry.Proj.map` is sufficient but, by the previous result, not
  necessary.
* `Stacks.AlgebraicGeometry.ProjShared.irrelevant_le_map_of_mem_span`: an element-level
  criterion for Mathlib's hypothesis, quantified over homogeneous elements only.
* `Stacks.AlgebraicGeometry.ProjShared.mapDomain_id` and
  `Stacks.AlgebraicGeometry.ProjShared.mapDomain_comp_le`: the identity is everywhere defined,
  and the domain of a composite is contained in the domain of the outer map.
* `Stacks.AlgebraicGeometry.ProjShared.mapDomain_eq_top_of_surjective`: a surjective graded
  homomorphism is everywhere defined.
* `Stacks.AlgebraicGeometry.ProjShared.mapDomain_eq_top_of_isLocalizationAway`: so is one that
  presents its target as the localization of its source at a degree-zero element.

## Implementation notes

The sharpness statement is the point of the file. The complement of `U(ψ)` is the projective
zero locus `V₊(𝒜₊.map ψ)`, because a homogeneous prime of `B` contains `𝒜₊.map ψ` exactly when
it contains `ψ f` for every positive-degree homogeneous `f` of `A`. Emptiness of a projective
zero locus is governed by a radical inclusion, not by a plain one — this is
`ProjectiveSpectrum.zeroLocus_empty_iff_irrelevant_le_radical` of
`StacksFrontier.AlgebraicGeometry.ProjectiveSpectrum.Topology` — so `U(ψ) = ⊤` is equivalent to
`ℬ₊ ≤ (𝒜₊.map ψ).radical` and is strictly weaker than Mathlib's `ℬ₊ ≤ 𝒜₊.map ψ`. For instance
for `ψ : k[x] → k[y]`, `x ↦ y²`, with both rings graded by degree, `𝒜₊.map ψ = (y²)` does not
contain `ℬ₊ = (y)`, while its radical does and `U(ψ) = Proj k[y] = ⊤`. Consequently a proof that
only knows `U(ψ) = ⊤` cannot invoke `AlgebraicGeometry.Proj.map` directly; it must either supply
the plain inclusion or redo the gluing. The radical criterion is what tells the two cases apart.

Both rings are taken in the same universe `u`, as they must be for `Proj ℬ ⟶ Proj 𝒜` to be a
morphism of `Scheme.{u}`, while the two `SetLike` carriers `σ` and `τ` are independent.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01MZ](https://stacks.math.columbia.edu/tag/01MZ)
* [Stacks Project, Tag 01N3](https://stacks.math.columbia.edu/tag/01N3)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public section

open AlgebraicGeometry HomogeneousIdeal TopologicalSpace

namespace Stacks.AlgebraicGeometry.ProjShared

universe u w w' w''

section

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-- The union of the standard opens `D₊(ψ f)` of `Proj ℬ` for `f` homogeneous of positive
degree: the largest open on which a graded ring homomorphism `ψ` induces a morphism to
`Proj 𝒜`. -/
@[stacks 01MY "the open domain", ega "II 2.8.1", ega "II 3.5.6" "partial"]
public def mapDomain (ψ : 𝒜 →+*ᵍ ℬ) : (Proj ℬ).Opens :=
  ⨆ (d : ℕ) (_ : 0 < d) (f : 𝒜 d), Proj.basicOpen ℬ (ψ f)

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
public theorem mem_mapDomain_iff (ψ : 𝒜 →+*ᵍ ℬ) (y : Proj ℬ) :
    y ∈ mapDomain 𝒜 ℬ ψ ↔
      ∃ (d : ℕ) (f : A), 0 < d ∧ f ∈ 𝒜 d ∧ ψ f ∉ y.asHomogeneousIdeal := by
  simp only [mapDomain, TopologicalSpace.Opens.mem_iSup, Proj.mem_basicOpen, Subtype.exists]
  exact ⟨fun ⟨d, hd, f, hf, hfy⟩ => ⟨d, f, hd, hf, hfy⟩,
    fun ⟨d, f, hd, hf, hfy⟩ => ⟨d, hd, f, hf, hfy⟩⟩

/-- A point lies outside `mapDomain 𝒜 ℬ ψ` exactly when it contains the image of the irrelevant
ideal: the complement of `mapDomain` is the projective zero locus `V₊(𝒜₊.map ψ)`. -/
public theorem notMem_mapDomain_iff (ψ : 𝒜 →+*ᵍ ℬ) (y : Proj ℬ) :
    y ∉ mapDomain 𝒜 ℬ ψ ↔
      (HomogeneousIdeal.irrelevant 𝒜).map ψ ≤ y.asHomogeneousIdeal := by
  rw [mem_mapDomain_iff]
  simp only [not_exists, not_and, not_not]
  refine ⟨fun h => toIdeal_le_toIdeal_iff.mp ?_, fun h i f hi hf =>
    h (Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hi hf))⟩
  rw [HomogeneousIdeal.toIdeal_map, Ideal.map_le_iff_le_comap]
  exact (HomogeneousIdeal.toIdeal_irrelevant_le 𝒜).mpr fun i hi f hf => h i f hi hf

/-- `mapDomain 𝒜 ℬ ψ = ⊤` exactly when the irrelevant ideal of `ℬ` lies in the **radical** of
the image of the irrelevant ideal of `𝒜`. This is strictly weaker than Mathlib's hypothesis
`ℬ₊ ≤ 𝒜₊.map ψ` for `AlgebraicGeometry.Proj.map`; see the module docstring. -/
@[ega "II 8.3.4" "more general"]
public theorem mapDomain_eq_top_iff_irrelevant_le_radical (ψ : 𝒜 →+*ᵍ ℬ) :
    mapDomain 𝒜 ℬ ψ = ⊤ ↔
      HomogeneousIdeal.irrelevant ℬ ≤ ((HomogeneousIdeal.irrelevant 𝒜).map ψ).radical := by
  rw [← ProjectiveSpectrum.zeroLocus_empty_iff_irrelevant_le_radical ℬ,
    Set.eq_empty_iff_forall_notMem]
  constructor
  · intro h y hy
    rw [ProjectiveSpectrum.mem_zeroLocus, SetLike.coe_subset_coe] at hy
    exact (notMem_mapDomain_iff 𝒜 ℬ ψ y).mpr hy (by rw [h]; trivial)
  · refine fun h => top_le_iff.mp fun y _ => ?_
    by_contra hy
    exact h (y : ProjectiveSpectrum ℬ)
      (SetLike.coe_subset_coe.mpr ((notMem_mapDomain_iff 𝒜 ℬ ψ y).mp hy))

/-- Under Mathlib's hypothesis for `AlgebraicGeometry.Proj.map`, the induced morphism is defined
on all of `Proj ℬ`. -/
public theorem mapDomain_eq_top_of_irrelevant_le_map (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ) :
    mapDomain 𝒜 ℬ ψ = ⊤ :=
  (mapDomain_eq_top_iff_irrelevant_le_radical 𝒜 ℬ ψ).mpr
    (hψ.trans (toIdeal_le_toIdeal_iff.mp Ideal.le_radical))

/-- An element-level criterion for Mathlib's hypothesis for `AlgebraicGeometry.Proj.map`: it
suffices that every homogeneous element of `ℬ` of positive degree lies in the ideal generated by
the images of the homogeneous elements of `𝒜` of positive degree. -/
public theorem irrelevant_le_map_of_mem_span (ψ : 𝒜 →+*ᵍ ℬ)
    (h : ∀ (d : ℕ), 0 < d → ∀ g : B, g ∈ ℬ d →
      g ∈ Ideal.span (ψ '' ⋃ n > 0, (𝒜 n : Set A))) :
    HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ := by
  refine (HomogeneousIdeal.irrelevant_le ℬ).mpr fun i hi g hg => ?_
  show g ∈ ((HomogeneousIdeal.irrelevant 𝒜).map ψ).toIdeal
  rw [HomogeneousIdeal.toIdeal_map, HomogeneousIdeal.irrelevant_eq_span, Ideal.map_span]
  exact h i hi g hg

/-- If the image of `a` is homogeneous of degree `n`, it is the image of the degree-`n` component
of `a`. -/
private theorem map_decompose_eq_of_mem (ψ : 𝒜 →+*ᵍ ℬ) {a : A} {n : ℕ} (h : ψ a ∈ ℬ n) :
    ψ (DirectSum.decompose 𝒜 a n) = ψ a := by
  rw [ψ.map_directSumDecompose, DirectSum.decompose_of_mem_same ℬ h]

/-- A surjective graded ring homomorphism is everywhere defined: the homogeneous component of a
preimage is a homogeneous preimage. -/
@[ega "II 3.5.1" "Criterion G(φ) = X"]
public theorem mapDomain_eq_top_of_surjective (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : Function.Surjective ψ) : mapDomain 𝒜 ℬ ψ = ⊤ := by
  refine top_le_iff.mp fun y _ => (mem_mapDomain_iff 𝒜 ℬ ψ y).mpr ?_
  obtain ⟨m, g, hm, hg, hgy⟩ := exists_homogeneous_pos_notMem ℬ y
  obtain ⟨a, rfl⟩ := hψ g
  refine ⟨m, DirectSum.decompose 𝒜 a m, hm, SetLike.coe_mem _, ?_⟩
  rwa [map_decompose_eq_of_mem 𝒜 ℬ ψ hg]

/-- **A graded homomorphism that presents its target as a localization of its source at a
degree-zero element is everywhere defined.**

A homogeneous element `b` of `B` of positive degree becomes, after multiplication by a power of
the image of `g`, the image of some `a ∈ A`; that image is homogeneous of the same degree, so `b`
lies in the ideal generated by the images of the positive-degree homogeneous elements of `A`.
Hence the irrelevant ideal of `ℬ` is contained in that ideal and the standard opens `D₊(ψ f)`
cover `Proj ℬ`.

The algebra structure is an arbitrary one whose structure map is `ψ`, which covers the structure
map `ψ.toRingHom.toAlgebra` in particular.

This is the first assertion of Tag 01N3, `U(ψ) = Y`. -/
@[stacks 01N3 "the open domain"]
public theorem mapDomain_eq_top_of_isLocalizationAway (ψ : 𝒜 →+*ᵍ ℬ) (g : 𝒜 0)
    [Algebra A B] (halg : algebraMap A B = (ψ : A →+* B))
    [IsLocalization.Away (g : A) B] :
    mapDomain 𝒜 ℬ ψ = ⊤ := by
  classical
  have hmap : ∀ x : A, algebraMap A B x = ψ x := DFunLike.congr_fun halg
  refine mapDomain_eq_top_of_irrelevant_le_map 𝒜 ℬ ψ
    (irrelevant_le_map_of_mem_span 𝒜 ℬ ψ fun n hn b hb => ?_)
  obtain ⟨k, a, ha⟩ := IsLocalization.Away.surj (x := (g : A)) b
  have hprod : b * (ψ (g : A)) ^ k = ψ a := by rwa [← hmap (g : A), ← hmap a]
  have hdeg : ψ a ∈ ℬ n := by
    have hpow : (ψ (g : A)) ^ k ∈ ℬ 0 := by
      simpa using SetLike.pow_mem_graded (A := ℬ) k (ψ.map_mem g.2)
    rw [← hprod]
    simpa using SetLike.mul_mem_graded (A := ℬ) hb hpow
  have hunit : IsUnit ((ψ (g : A)) ^ k) := by
    rw [← hmap (g : A)]
    exact (IsLocalization.Away.algebraMap_isUnit (g : A)).pow k
  rw [← Ideal.mul_unit_mem_iff_mem _ hunit, hprod, ← map_decompose_eq_of_mem 𝒜 ℬ ψ hdeg]
  exact Ideal.subset_span ⟨DirectSum.decompose 𝒜 a n,
    Set.mem_iUnion₂.mpr ⟨n, hn, SetLike.coe_mem _⟩, rfl⟩

end

section id

variable {A : Type u} {σ : Type w} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The identity graded ring homomorphism is everywhere defined. -/
public theorem mapDomain_id : mapDomain 𝒜 𝒜 (GradedRingHom.id 𝒜) = ⊤ :=
  mapDomain_eq_top_of_surjective 𝒜 𝒜 _ Function.surjective_id

end id

section comp

variable {A B C : Type u} {σ : Type w} {τ : Type w'} {υ : Type w''}
  [CommRing A] [CommRing B] [CommRing C]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  [SetLike υ C] [AddSubgroupClass υ C]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) (𝒞 : ℕ → υ) [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]

omit [AddSubgroupClass σ A] [AddSubgroupClass τ B] [GradedRing 𝒜] [GradedRing ℬ] in
/-- The domain of the morphism induced by a composite is contained in the domain of the morphism
induced by the outer homomorphism: the inner homomorphism takes a positive-degree homogeneous
element to one of the same degree. -/
public theorem mapDomain_comp_le (φ : 𝒜 →+*ᵍ ℬ) (ψ : ℬ →+*ᵍ 𝒞) :
    mapDomain 𝒜 𝒞 (ψ.comp φ) ≤ mapDomain ℬ 𝒞 ψ := by
  intro z hz
  obtain ⟨d, f, hd, hf, hfz⟩ := (mem_mapDomain_iff 𝒜 𝒞 (ψ.comp φ) z).mp hz
  exact (mem_mapDomain_iff ℬ 𝒞 ψ z).mpr ⟨d, φ f, hd, φ.map_mem hf, hfz⟩

end comp

end Stacks.AlgebraicGeometry.ProjShared

end
