module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyIdealQuotientBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace

/-!
# The closed subscheme cut out by an ideal of an affine object of the big fppf site

Let `V` be an object of the big fppf site over `S` whose underlying scheme is affine, with ring
of global functions `R`, and let `J ⊆ R` be an ideal. The morphism
`AlgebraicGeometry.Space.idealQuotientSpecMap : Spec (R ⧸ J) ⟶ V` of the site is a closed
immersion, so its Yoneda image is a closed immersion of algebraic spaces; a point of `V` lying
over `V(J)` is in its image; and if `g : V ⟶ T₀` is a morphism to an affine object with `R ⧸ J`
finite over `Γ(T₀)`, the composite `Spec (R ⧸ J) ⟶ T₀` is proper.

## Main results

* `AlgebraicGeometry.Space.isClosedImmersion_yoneda_map_idealQuotientSpecMap`.
* `AlgebraicGeometry.Space.pointsEquivScheme_symm_mem_range_idealQuotientSpecMap`.
* `AlgebraicGeometry.Space.isProper_yoneda_map_idealQuotientSpecMap_comp`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {V : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))

/-- The underlying morphism of schemes of `Spec (R ⧸ J) ⟶ V` is
`Spec (R ⟶ R ⧸ J)` followed by `Spec R ≅ V`. -/
theorem toScheme_map_idealQuotientSpecMap :
    (BigFppfOver.toScheme B S hS).map (idealQuotientSpecMap B S hS J) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫
        ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv :=
  rfl

/-- `Spec (R ⧸ J) ⟶ V` is a closed immersion of schemes. -/
instance isClosedImmersion_toScheme_map_idealQuotientSpecMap :
    _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (idealQuotientSpecMap B S hS J)) := by
  rw [toScheme_map_idealQuotientSpecMap]
  have : _root_.AlgebraicGeometry.IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _
      Ideal.Quotient.mk_surjective
  infer_instance

/-- The Yoneda image of `Spec (R ⧸ J) ⟶ V` is a closed immersion of algebraic spaces. -/
theorem isClosedImmersion_yoneda_map_idealQuotientSpecMap :
    IsClosedImmersion B S hS (yoneda.map (idealQuotientSpecMap B S hS J)) :=
  (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
    (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) _).2
    (isClosedImmersion_toScheme_map_idealQuotientSpecMap B S hS J)

/-- **A point of `V` over `V(J)` is the image of a point of `Spec (R ⧸ J)`**, on the points of
the represented algebraic spaces. -/
theorem pointsEquivScheme_symm_mem_range_idealQuotientSpecMap
    (x : (BigFppfOver.toScheme B S hS).obj V)
    (hx : ((BigFppfOver.toScheme B S hS).obj V).isoSpec.hom x ∈
      PrimeSpectrum.zeroLocus (J : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))) :
    (pointsEquivScheme B S hS V).symm x ∈
      Set.range (pointsMap B S hS _ (yoneda.map (idealQuotientSpecMap B S hS J))) := by
  have hrange := range_comap_of_surjective _ (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective
  rw [Ideal.mk_ker] at hrange
  rw [← hrange] at hx
  obtain ⟨w, hw⟩ := hx
  let w' : (BigFppfOver.toScheme B S hS).obj (idealQuotientSpecObject B S hS J) := w
  refine ⟨(pointsEquivScheme B S hS _).symm w', ?_⟩
  rw [← pointsEquivScheme_symm_map]
  congr 1
  have hw' : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) w' =
      ((BigFppfOver.toScheme B S hS).obj V).isoSpec.hom x := hw
  change ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv
    ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) w') = x
  rw [hw', ← Scheme.Hom.comp_apply, Iso.hom_inv_id]
  rfl

/-- **`Spec (R ⧸ J)` is proper over an affine `T₀` when `R ⧸ J` is finite over `Γ(T₀)`.** For
`g : V ⟶ T₀` with `T₀` affine, if the composite `Γ(T₀) ⟶ R ⟶ R ⧸ J` is finite then the Yoneda
image of `Spec (R ⧸ J) ⟶ V ⟶ T₀` is a proper morphism of algebraic spaces. -/
theorem isProper_yoneda_map_idealQuotientSpecMap_comp {T₀ : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)] (g : V ⟶ T₀)
    (hJ : ((Ideal.Quotient.mk J).comp ((BigFppfOver.toScheme B S hS).map g).appTop.hom).Finite) :
    IsProper B S hS (yoneda.map (idealQuotientSpecMap B S hS J ≫ g)) := by
  apply isProper_yoneda_map
  rw [Functor.map_comp, toScheme_map_idealQuotientSpecMap]
  have : _root_.AlgebraicGeometry.IsFinite
      ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫
        ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv) ≫
          (BigFppfOver.toScheme B S hS).map g) := by
    rw [Category.assoc, ← Scheme.isoSpec_inv_naturality, ← Category.assoc, ← Spec.map_comp]
    have : _root_.AlgebraicGeometry.IsFinite
        (Spec.map (((BigFppfOver.toScheme B S hS).map g).appTop ≫
          CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
      (_root_.AlgebraicGeometry.IsFinite.SpecMap_iff _).2 hJ
    infer_instance
  infer_instance

end AlgebraicGeometry.Space

end
