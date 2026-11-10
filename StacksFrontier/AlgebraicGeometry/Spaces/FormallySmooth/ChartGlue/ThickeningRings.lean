module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartGlue.AffineObj
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Defs
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothScheme

/-!
# The rings of an affine square-zero thickening

Let `i : T ⟶ T'` be a square-zero closed immersion of affine objects of the big fppf site over
`S`. With `A' = Γ(T', ⊤)` and `A = Γ(T, ⊤)`, the map `A' → A` is surjective with square-zero
kernel, and `T' ≅ specObj A'`.

## Main results

* `AlgebraicGeometry.Space.ChartGlue.surjective_thickening`: the map `A' → A` is surjective.
* `AlgebraicGeometry.Space.ChartGlue.ker_sq_thickening`: the kernel of `A' → A` has square zero.
* `AlgebraicGeometry.Space.ChartGlue.specSelfIso`: `specObj A' ≅ T'`, over `T'`.
* `AlgebraicGeometry.Space.ChartGlue.eq_of_specObj_self`: two morphisms into `specObj A'` over
  `T'` are equal.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space.ChartGlue

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (T' : BigFppfOver B S hS)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]

/-- The spectrum of `A' = Γ(T', ⊤)` is contained in the site `B`. -/
lemma contains_specRingOf : B.Contains (Spec (CommRingCat.of (ringOf B S hS T'))) := by
  change (Spec Γ((BigFppfOver.toScheme B S hS).obj T', ⊤)).size < B.cutoff
  rw [← Scheme.size_congr ((BigFppfOver.toScheme B S hS).obj T').isoSpec]
  exact T'.left.property

/-- The structure map of `specObj A'` is an isomorphism onto `T'`. -/
lemma specStr_self :
    specStr B S hS T' (ringOf B S hS T') = ((BigFppfOver.toScheme B S hS).obj T').isoSpec.inv := by
  rw [specStr, show CommRingCat.ofHom (algebraMap (ringOf B S hS T') (ringOf B S hS T')) = 𝟙 _
    from rfl, Spec.map_id, Category.id_comp]

/-- The isomorphism `specObj A' ≅ T'` over `S`, where `A' = Γ(T', ⊤)`. -/
def specSelfIso : specObj B S hS T' (ringOf B S hS T') (contains_specRingOf B S hS T') ≅ T' where
  hom := specToT B S hS T' _ _
  inv := BigFppfOver.homMk B S hS (contains_specRingOf B S hS T') _
    ((BigFppfOver.toScheme B S hS).obj T').isoSpec.hom (by
      rw [specStr_self, Iso.hom_inv_id_assoc])
  hom_inv_id := by
    apply (BigFppfOver.toScheme B S hS).map_injective
    change specStr B S hS T' (ringOf B S hS T') ≫
      ((BigFppfOver.toScheme B S hS).obj T').isoSpec.hom = 𝟙 _
    rw [specStr_self]
    exact ((BigFppfOver.toScheme B S hS).obj T').isoSpec.inv_hom_id
  inv_hom_id := by
    apply (BigFppfOver.toScheme B S hS).map_injective
    change ((BigFppfOver.toScheme B S hS).obj T').isoSpec.hom ≫
      specStr B S hS T' (ringOf B S hS T') = 𝟙 _
    rw [specStr_self]
    exact ((BigFppfOver.toScheme B S hS).obj T').isoSpec.hom_inv_id

/-- The forward map of `specSelfIso` is the structure morphism `specToT` of `specObj A'`. -/
lemma specSelfIso_hom : (specSelfIso B S hS T').hom = specToT B S hS T' _ _ := rfl

/-- Two morphisms into `specObj A'` lying over `T'` are equal. -/
lemma eq_of_specObj_self {C₀ : BigFppfOver B S hS}
    (g₁ g₂ : C₀ ⟶ specObj B S hS T' (ringOf B S hS T') (contains_specRingOf B S hS T'))
    (h : g₁ ≫ specToT B S hS T' _ _ = g₂ ≫ specToT B S hS T' _ _) : g₁ = g₂ := by
  rw [← specSelfIso_hom] at h
  exact (cancel_mono _).1 h

variable {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (i : T ⟶ T')

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] in
/-- For a square-zero closed immersion `i : T ⟶ T'` of affine objects, the ring map
`Γ(T', ⊤) → Γ(T, ⊤)` is surjective. -/
lemma surjective_thickening (hi : IsSquareZeroClosedImmersion B S hS i) :
    letI := ringAlg B S hS T' i
    Function.Surjective (algebraMap (ringOf B S hS T') (ringE B S hS (E := T))) := by
  have : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i) := hi.1
  exact (AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine
    ((BigFppfOver.toScheme B S hS).map i)).2

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] in
/-- For a square-zero closed immersion `i : T ⟶ T'` of affine objects, the kernel of the ring map
`Γ(T', ⊤) → Γ(T, ⊤)` has square zero. -/
lemma ker_sq_thickening (hi : IsSquareZeroClosedImmersion B S hS i) :
    letI := ringAlg B S hS T' i
    RingHom.ker (algebraMap (ringOf B S hS T') (ringE B S hS (E := T))) ^ 2 = ⊥ := by
  have : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i) := hi.1
  exact (Stacks.Smooth.ker_pow_eq_bot_iff_of_isAffine ((BigFppfOver.toScheme B S hS).map i) 2).1
    hi.2

end AlgebraicGeometry.Space.ChartGlue

end
