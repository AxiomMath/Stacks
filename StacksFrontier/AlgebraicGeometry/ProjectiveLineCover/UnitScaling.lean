module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# Rescaling a graded ring homomorphism by a unit does not change the induced map on `Proj`

Let `φ, φ' : 𝒜 →+*ᵍ ℬ` be homomorphisms of graded rings such that `φ' a = φ a * w ^ d` for
every `a` homogeneous of degree `d`, where `w` has degree zero in `ℬ` (a unit, in practice).
Then `φ` and `φ'` induce the same morphism `Proj ℬ ⟶ Proj 𝒜`. This is the statement that a point
of projective space has homogeneous coordinates only up to a common unit factor.

## Main results

* `AlgebraicGeometry.Proj.map_eq_of_eq_mul_pow`: the two induced morphisms agree.

## Implementation notes

The proof compares the two morphisms on the affine charts `Spec ℬ_{(φ' a)}` of the cover of
`Proj ℬ` attached to `φ'`. The element `φ' a = φ a * w ^ d` is a multiple of `φ a`, so its chart is
the chart of `φ a` precomposed with `Spec` of `HomogeneousLocalization.awayMap`, and on both
charts Mathlib computes `Proj.map` as `Spec` of the induced map of degree-zero localizations. What
remains is the identity of ring maps `ℬ_{(φ a)} → ℬ_{(φ' a)}`, which is the computation
`φ' b / φ' a ^ n = φ b · w ^ (n d) / (φ a · w ^ d) ^ n` with the common factor cancelled.
-/

@[expose] public section

open CategoryTheory HomogeneousLocalization

universe u

namespace AlgebraicGeometry.Proj

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

variable (φ φ' : 𝒜 →+*ᵍ ℬ) (hφ : HomogeneousIdeal.irrelevant ℬ ≤
      HomogeneousIdeal.map φ (HomogeneousIdeal.irrelevant 𝒜))
    (hφ' : HomogeneousIdeal.irrelevant ℬ ≤ HomogeneousIdeal.map φ' (HomogeneousIdeal.irrelevant 𝒜))
    (w : B)

/-- The degree-zero localization map of `φ'` at `a` is that of `φ` followed by the passage from
the localization at `φ a` to the localization at its multiple `φ' a = φ a * w ^ i`. -/
private lemma awayMap_comp_awayMap {i : ℕ} (a : A) (ha : a ∈ 𝒜 i) (hwi : w ^ i ∈ ℬ 0)
    (hx : φ' a = φ a * w ^ i) (h : ∀ (d : ℕ), ∀ a ∈ 𝒜 d, φ' a = φ a * w ^ d) :
    (awayMap ℬ hwi hx).comp (Away.map φ a) = Away.map φ' a := by
  ext z
  obtain ⟨n, z, hz, rfl⟩ := z.mk_surjective _ ha
  rw [RingHom.comp_apply, Away.map_mk, awayMap_mk, Away.map_mk]
  simp only [Away.val_mk]
  rw [h (n • i) z hz, smul_eq_mul, ← pow_mul, mul_comm i n]

private lemma chart_eq (hw0 : w ∈ ℬ 0) {i : ℕ} (hi : 0 < i) (a : A) (ha : a ∈ 𝒜 i)
    (h : ∀ (d : ℕ), ∀ a ∈ 𝒜 d, φ' a = φ a * w ^ d) :
    awayι ℬ (φ' a) (φ'.2 ha) hi ≫ map φ hφ = awayι ℬ (φ' a) (φ'.2 ha) hi ≫ map φ' hφ' := by
  have hwi : w ^ i ∈ ℬ 0 := by
    simpa using SetLike.pow_mem_graded i hw0
  have hx : φ' a = φ a * w ^ i := h i a ha
  rw [awayι_comp_map φ' hφ' hi a ha, ← SpecMap_awayMap_awayι ℬ (f := φ a) (φ.2 ha) hi hwi hx,
    Category.assoc, awayι_comp_map φ hφ hi a ha, ← Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, awayMap_comp_awayMap φ φ' w a ha hwi hx h]

/-- **Rescaling by a unit of degree zero does not change the morphism on `Proj`.** If
`φ' a = φ a * w ^ d` for every `a` of degree `d`, with `w` of degree zero, then
`Proj.map φ = Proj.map φ'`. (That `w` is a unit is forced by the irrelevant-ideal hypotheses and
is not needed in the proof.) -/
theorem map_eq_of_eq_mul_pow (hw0 : w ∈ ℬ 0) (h : ∀ (d : ℕ), ∀ a ∈ 𝒜 d, φ' a = φ a * w ^ d) :
    map φ hφ = map φ' hφ' :=
  (mapAffineOpenCover φ' hφ').openCover.hom_ext _ _ fun s ↦
    chart_eq φ φ' hφ hφ' w hw0 s.1.2 s.2 s.2.2 h

end AlgebraicGeometry.Proj
