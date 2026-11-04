module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# Rescaling the grading of a graded ring by a degree-zero element

Let `A = ⨁_{d ≥ 0} 𝒜 d` be a graded ring and let `u ∈ 𝒜 0`. Multiplying the degree `d` piece by
`u ^ d` is a graded ring endomorphism `degreeScale 𝒜 hu` of `𝒜`, and multiplication of
degree-zero elements corresponds to composition of these endomorphisms. When `u` is invertible in
`𝒜 0` the endomorphism is an automorphism, and the main result is that it induces the *identity*
on `Proj 𝒜`: rescaling a homogeneous coordinate of degree `d` by `u ^ d` changes neither the
relevant homogeneous primes nor the degree-zero fractions `a / f ^ n` out of which `Proj 𝒜` is
built.

Consequently two graded ring maps that differ by such a rescaling induce the same morphism of
homogeneous spectra. This is the well-definedness statement behind glueing a morphism of relative
`Proj`'s out of local comparisons that depend on a choice of generator of an invertible module:
two generators differ by a unit, and the two resulting graded comparison maps differ by exactly
the corresponding degree rescaling.

## Main definitions

* `Stacks.GradedRing.degreeScale`: the graded endomorphism of `𝒜` acting on `𝒜 d` by
  `a ↦ u ^ d * a`.

## Main results

* `Stacks.GradedRing.Proj_map_degreeScale`: rescaling by an invertible degree-zero element induces
  the identity morphism on `Proj 𝒜`.
* `Stacks.GradedRing.Proj_map_comp_degreeScale`, `Stacks.GradedRing.Proj_map_degreeScale_comp`:
  two graded ring maps differing by a rescaling induce the same morphism of homogeneous spectra.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry DirectSum Graded HomogeneousIdeal
open HomogeneousLocalization

namespace Stacks.GradedRing

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {u v : A}

section Hom

variable {𝒜}

/-- Every power of a degree-zero element has degree zero. -/
lemma pow_mem_graded_zero (hu : u ∈ 𝒜 0) (n : ℕ) : u ^ n ∈ 𝒜 0 := by
  simpa using SetLike.pow_mem_graded n hu

/-- If `u ∈ 𝒜 0` and `a ∈ 𝒜 i`, then `u ^ n * a ∈ 𝒜 i`. -/
lemma pow_mul_mem_graded (hu : u ∈ 𝒜 0) {n i : ℕ} {a : A} (ha : a ∈ 𝒜 i) :
    u ^ n * a ∈ 𝒜 i := by
  simpa using SetLike.mul_mem_graded (pow_mem_graded_zero hu n) ha

variable (𝒜)

/-- Two graded ring homomorphisms agreeing on homogeneous elements are equal. -/
lemma gradedRingHom_ext {B τ : Type*} [CommRing B] [SetLike τ B]
    {ℬ : ℕ → τ} {φ ψ : 𝒜 →+*ᵍ ℬ}
    (h : ∀ (i : ℕ) (a : A), a ∈ 𝒜 i → φ a = ψ a) : φ = ψ := by
  classical
  refine GradedRingHom.ext fun a ↦ ?_
  rw [← DirectSum.sum_support_decompose 𝒜 a, map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ h i _ (SetLike.coe_mem _)

/-- Multiplication by `u ^ i`, as an additive map from the degree `i` piece of `𝒜` to `A`. -/
def degreeScaleFamily (u : A) (i : ℕ) : (𝒜 i) →+ A where
  toFun x := u ^ i * (x : A)
  map_zero' := by simp
  map_add' x y := by push_cast; ring

/-- The ring homomorphism `⨁ i, 𝒜 i →+* A` which is multiplication by `u ^ i` on the degree `i`
summand. -/
def degreeScaleAux (u : A) : (⨁ i, 𝒜 i) →+* A :=
  DirectSum.toSemiring (degreeScaleFamily 𝒜 u) (by simp [degreeScaleFamily])
    fun {i j} ai aj ↦ by
      change u ^ (i + j) * ((ai : A) * aj) = u ^ i * (ai : A) * (u ^ j * aj)
      rw [pow_add]; ring

/-- `degreeScaleAux 𝒜 u` sends `x` in the degree `i` summand to `u ^ i * x`. -/
@[simp]
lemma degreeScaleAux_of (u : A) (i : ℕ) (x : 𝒜 i) :
    degreeScaleAux 𝒜 u (DirectSum.of _ i x) = u ^ i * (x : A) :=
  DirectSum.toSemiring_of (degreeScaleFamily 𝒜 u) _ _ i x

/-- For `u` of degree zero in a graded ring `A = ⨁_{d ≥ 0} 𝒜 d`, the graded ring endomorphism of
`𝒜` which multiplies the degree `d` piece by `u ^ d`. -/
def degreeScale (hu : u ∈ 𝒜 0) : 𝒜 →+*ᵍ 𝒜 where
  toRingHom := (degreeScaleAux 𝒜 u).comp (DirectSum.decomposeRingEquiv 𝒜).toRingHom
  map_mem {i x} hx := by
    change degreeScaleAux 𝒜 u (DirectSum.decompose 𝒜 x) ∈ 𝒜 i
    rw [DirectSum.decompose_of_mem 𝒜 hx, degreeScaleAux_of]
    exact pow_mul_mem_graded hu hx

/-- `degreeScale 𝒜 hu a` is `degreeScaleAux 𝒜 u` applied to the decomposition of `a`. -/
lemma degreeScale_apply (hu : u ∈ 𝒜 0) (a : A) :
    degreeScale 𝒜 hu a = degreeScaleAux 𝒜 u (DirectSum.decompose 𝒜 a) := rfl

/-- On a homogeneous element `a` of degree `i`, `degreeScale 𝒜 hu a = u ^ i * a`. -/
lemma degreeScale_apply_of_mem (hu : u ∈ 𝒜 0) {i : ℕ} {a : A} (ha : a ∈ 𝒜 i) :
    degreeScale 𝒜 hu a = u ^ i * a := by
  rw [degreeScale_apply, DirectSum.decompose_of_mem 𝒜 ha, degreeScaleAux_of]

/-- Rescaling by `1` is the identity. -/
lemma degreeScale_one : degreeScale 𝒜 (SetLike.one_mem_graded 𝒜) = GradedRingHom.id 𝒜 := by
  refine gradedRingHom_ext 𝒜 fun i a ha ↦ ?_
  rw [degreeScale_apply_of_mem 𝒜 _ ha, one_pow, one_mul, GradedRingHom.id_apply]

/-- Rescaling by `u` and then by `v` is rescaling by `v * u`. -/
lemma degreeScale_comp (hu : u ∈ 𝒜 0) (hv : v ∈ 𝒜 0) :
    (degreeScale 𝒜 hv).comp (degreeScale 𝒜 hu) =
      degreeScale 𝒜 (SetLike.mul_mem_graded hv hu) := by
  refine gradedRingHom_ext 𝒜 fun i a ha ↦ ?_
  rw [GradedRingHom.comp_apply, degreeScale_apply_of_mem 𝒜 hu ha,
    degreeScale_apply_of_mem 𝒜 hv (pow_mul_mem_graded hu ha),
    degreeScale_apply_of_mem 𝒜 _ ha, mul_pow]
  ring

end Hom

section Proj

variable {B τ : Type u} [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {ℬ : ℕ → τ} [GradedRing ℬ]

/-- Rescaling by an invertible degree-zero element preserves the irrelevant ideal, in the form
required for functoriality of `Proj`. -/
lemma irrelevant_le_map_degreeScale (hu : u ∈ 𝒜 0) (hv : v ∈ 𝒜 0) (huv : u * v = 1) :
    𝒜₊ ≤ 𝒜₊.map (degreeScale 𝒜 hu) := by
  refine (HomogeneousIdeal.irrelevant_le 𝒜).mpr fun i hi a ha ↦ ?_
  have ha' : v ^ i * a ∈ 𝒜 i := pow_mul_mem_graded hv ha
  have hscale : degreeScale 𝒜 hu (v ^ i * a) = a := by
    rw [degreeScale_apply_of_mem 𝒜 hu ha', ← mul_assoc, ← mul_pow, huv, one_pow, one_mul]
  exact hscale ▸ Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem _ hi ha')

/-- Rescaling the grading by a degree-zero element identifies the standard affine chart
`Spec (A_f)₀` of `Proj 𝒜` at a homogeneous `f` of positive degree with the chart at the rescaled
element `u ^ deg f * f`. -/
lemma SpecMap_AwayMap_degreeScale_awayι (hu : u ∈ 𝒜 0) {i : ℕ} (hi : 0 < i) {f : A}
    (hf : f ∈ 𝒜 i) :
    Spec.map (CommRingCat.ofHom (Away.map (degreeScale 𝒜 hu) f)) ≫ Proj.awayι 𝒜 f hf hi =
      Proj.awayι 𝒜 (degreeScale 𝒜 hu f) (map_mem _ hf) hi := by
  have hx : degreeScale 𝒜 hu f = f * u ^ i := by
    rw [degreeScale_apply_of_mem 𝒜 hu hf]; ring
  have hmap : Away.map (degreeScale 𝒜 hu) f = awayMap 𝒜 (pow_mem_graded_zero hu i) hx := by
    refine RingHom.ext fun z ↦ ?_
    obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hf z
    rw [Away.map_mk, awayMap_mk]
    refine HomogeneousLocalization.val_injective _ ?_
    rw [Away.val_mk, Away.val_mk, degreeScale_apply_of_mem 𝒜 hu ha]
    congr 1
    rw [smul_eq_mul, ← pow_mul]
    ring
  rw [hmap]
  exact Proj.SpecMap_awayMap_awayι 𝒜 hf hi (pow_mem_graded_zero hu i) hx

/-- Rescaling the grading of `𝒜` by an invertible degree-zero element induces the identity
morphism on `Proj 𝒜`. -/
theorem Proj_map_degreeScale (hu : u ∈ 𝒜 0) (hv : v ∈ 𝒜 0) (huv : u * v = 1) :
    Proj.map (degreeScale 𝒜 hu) (irrelevant_le_map_degreeScale 𝒜 hu hv huv) = 𝟙 (Proj 𝒜) := by
  refine (Proj.mapAffineOpenCover (degreeScale 𝒜 hu)
    (irrelevant_le_map_degreeScale 𝒜 hu hv huv)).openCover.hom_ext _ _ fun s ↦ ?_
  show Proj.awayι 𝒜 (degreeScale 𝒜 hu s.2) (map_mem _ s.2.2) s.1.2 ≫
      Proj.map (degreeScale 𝒜 hu) (irrelevant_le_map_degreeScale 𝒜 hu hv huv) =
    Proj.awayι 𝒜 (degreeScale 𝒜 hu s.2) (map_mem _ s.2.2) s.1.2 ≫ 𝟙 (Proj 𝒜)
  rw [Category.comp_id]
  exact (Proj.awayι_comp_map _ _ s.1.2 _ s.2.2).trans
    (SpecMap_AwayMap_degreeScale_awayι 𝒜 hu s.1.2 s.2.2)

/-- Two graded ring maps out of `𝒜` differing by a rescaling of the grading of `𝒜` by an
invertible degree-zero element induce the same morphism `Proj ℬ ⟶ Proj 𝒜`. -/
theorem Proj_map_comp_degreeScale (hu : u ∈ 𝒜 0) (hv : v ∈ 𝒜 0) (huv : u * v = 1)
    (φ : 𝒜 →+*ᵍ ℬ) (hφ : ℬ₊ ≤ 𝒜₊.map φ)
    (h : ℬ₊ ≤ 𝒜₊.map (φ.comp (degreeScale 𝒜 hu))) :
    Proj.map (φ.comp (degreeScale 𝒜 hu)) h = Proj.map φ hφ := by
  have key := Proj.map_comp (f := degreeScale 𝒜 hu) (g := φ)
    (hf := irrelevant_le_map_degreeScale 𝒜 hu hv huv) (hg := hφ)
  rw [Proj_map_degreeScale 𝒜 hu hv huv, Category.comp_id] at key
  exact key

/-- Two graded ring maps into `ℬ` differing by a rescaling of the grading of `ℬ` by an invertible
degree-zero element induce the same morphism `Proj ℬ ⟶ Proj 𝒜`. -/
theorem Proj_map_degreeScale_comp {w w' : B} (hw : w ∈ ℬ 0) (hw' : w' ∈ ℬ 0) (hww' : w * w' = 1)
    (φ : 𝒜 →+*ᵍ ℬ) (hφ : ℬ₊ ≤ 𝒜₊.map φ)
    (h : ℬ₊ ≤ 𝒜₊.map ((degreeScale ℬ hw).comp φ)) :
    Proj.map ((degreeScale ℬ hw).comp φ) h = Proj.map φ hφ := by
  have key := Proj.map_comp (f := φ) (g := degreeScale ℬ hw) (hf := hφ)
    (hg := irrelevant_le_map_degreeScale ℬ hw hw' hww')
  rw [Proj_map_degreeScale ℬ hw hw' hww', Category.id_comp] at key
  exact key

/-- **Well-definedness criterion.** Two graded ring maps `𝒜 →+*ᵍ ℬ` whose values on a homogeneous
element of degree `d` differ by multiplication by `u ^ d`, for `u` invertible in `𝒜 0`, induce the
same morphism `Proj ℬ ⟶ Proj 𝒜`. -/
theorem Proj_map_eq_of_source_degreeScale (hu : u ∈ 𝒜 0) (hv : v ∈ 𝒜 0) (huv : u * v = 1)
    (φ ψ : 𝒜 →+*ᵍ ℬ) (hφ : ℬ₊ ≤ 𝒜₊.map φ) (hψ : ℬ₊ ≤ 𝒜₊.map ψ)
    (h : ∀ (i : ℕ) (a : A), a ∈ 𝒜 i → ψ a = φ (u ^ i * a)) :
    Proj.map ψ hψ = Proj.map φ hφ := by
  have hcomp : ψ = φ.comp (degreeScale 𝒜 hu) :=
    gradedRingHom_ext 𝒜 fun i a ha ↦ by
      rw [GradedRingHom.comp_apply, degreeScale_apply_of_mem 𝒜 hu ha, h i a ha]
  subst hcomp
  exact Proj_map_comp_degreeScale 𝒜 hu hv huv φ hφ hψ

/-- **Well-definedness criterion, target form.** Two graded ring maps `𝒜 →+*ᵍ ℬ` whose values on a
homogeneous element of degree `d` differ by multiplication by `w ^ d`, for `w` invertible in
`ℬ 0`, induce the same morphism `Proj ℬ ⟶ Proj 𝒜`. -/
theorem Proj_map_eq_of_target_degreeScale {w w' : B} (hw : w ∈ ℬ 0) (hw' : w' ∈ ℬ 0)
    (hww' : w * w' = 1) (φ ψ : 𝒜 →+*ᵍ ℬ) (hφ : ℬ₊ ≤ 𝒜₊.map φ) (hψ : ℬ₊ ≤ 𝒜₊.map ψ)
    (h : ∀ (i : ℕ) (a : A), a ∈ 𝒜 i → ψ a = w ^ i * φ a) :
    Proj.map ψ hψ = Proj.map φ hφ := by
  have hcomp : ψ = (degreeScale ℬ hw).comp φ :=
    gradedRingHom_ext 𝒜 fun i a ha ↦ by
      rw [GradedRingHom.comp_apply, degreeScale_apply_of_mem ℬ hw (map_mem φ ha), h i a ha]
  subst hcomp
  exact Proj_map_degreeScale_comp 𝒜 hw hw' hww' φ hφ hψ

end Proj

end Stacks.GradedRing
