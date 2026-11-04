module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.FibreOfOpenRestriction
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GenericResidueField
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GenericResidueFieldOfSpec

/-!
# The fibre over the generic point of the spectrum of a domain is the base change to the fraction
field

Let `A` be a domain with fraction field `K` and let `g : Y ⟶ Spec A` be any morphism. The
scheme-theoretic fibre of `g` over the generic point of `Spec A` is the pullback of `g` along
`Spec K ⟶ Spec A`: the residue field of `Spec A` at its generic point is a field of fractions of
`A`, hence uniquely `A`-isomorphic to `K`, and the canonical morphism out of the spectrum of that
residue field is the spectrum of the structure map.

**Consequently a dense open subscheme of `Y ×_{Spec A} Spec K` smooth over `Spec K`, however that
base change is presented, yields a dense open subscheme of the fibre of `g` over the generic point
smooth over the residue field there.** That is the shape in which the first paragraph of the proof
of the reduced fibre theorem produces its dense smooth open — on a base change along
`Spec L ⟶ Spec A` — and the shape in which the later steps consume it — on
`g.fiber (genericPoint (Spec A))`, as in
`AlgebraicGeometry.finite_setOf_notMem_smoothLocus_mem_genericPoints_fiber` and
`AlgebraicGeometry.exists_finite_extension_forall_isSolution_stalk_of_dense_open_smooth`.

## Main results

* `CategoryTheory.IsPullback.comp_isIso_right`: a pullback square whose right leg factors through
  an isomorphism may have that isomorphism moved to the opposite leg.
* `AlgebraicGeometry.exists_isIso_isPullback_fiberι_genericPoint`: the defining pullback square of
  the fibre over the generic point, with its right leg rewritten as `Spec K ⟶ Spec A`.
* `AlgebraicGeometry.exists_dense_open_smooth_fiber_genericPoint_of_isPullback`: a dense open
  smooth over `Spec K` on any base change of `g` to `K` gives one on the fibre over the generic
  point.

## Implementation notes

`CategoryTheory.IsPullback.comp_isIso_right` is the elementary observation that if the right leg
of a pullback square factors through an isomorphism, then replacing it by the factor and
composing the opposite leg with the isomorphism leaves a pullback square; it is proved by pasting
the square with the pullback square of two isomorphisms.

The `Opens` on the fibre is the preimage of the given one under the inverse of the comparison
isomorphism. Density transports because that inverse is a homeomorphism, and smoothness because
the restriction of an isomorphism to an open is an isomorphism and an isomorphism is smooth.

## References

* [Stacks Project, Tag 09IL](https://stacks.math.columbia.edu/tag/09IL)
* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

/-- **Composing the right leg of a pullback square with an isomorphism.** If the right-hand leg of
a pullback square factors as an isomorphism followed by a morphism `g`, then replacing that leg by
`g` and composing the opposite leg with the isomorphism leaves a pullback square. -/
theorem CategoryTheory.IsPullback.comp_isIso_right {C : Type*} [Category C] {P X Y Y' Z : C}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {i : Y ⟶ Y'} {g : Y' ⟶ Z} [IsIso i]
    (h : IsPullback fst snd f (i ≫ g)) : IsPullback fst (snd ≫ i) f g := by
  have hsq : IsPullback i (i ≫ g) g (𝟙 Z) := IsPullback.of_horiz_isIso ⟨by simp⟩
  have hpaste := h.flip.paste_horiz hsq
  rw [Category.comp_id] at hpaste
  exact hpaste.flip

namespace AlgebraicGeometry

/-- **The fibre over the generic point of the spectrum of a domain is the base change to the
fraction field.** For `A` a domain with fraction field `K` and any `g : Y ⟶ Spec A`, the two legs
of the fibre of `g` over the generic point of `Spec A` present it as the pullback of `g` along
`Spec K ⟶ Spec A`, after composing the leg to the spectrum of the residue field with an
isomorphism `Spec κ(η) ≅ Spec K`.

The isomorphism is the spectrum of the unique `A`-algebra isomorphism between the two fields of
fractions `K` and `κ(η)` of `A`, the latter being a field of fractions by
`AlgebraicGeometry.isFractionRing_specResidueField_genericPoint`; the canonical morphism out of
`Spec κ(η)` is the spectrum of the structure map by
`AlgebraicGeometry.fromSpecResidueField_eq_specMap`. -/
theorem exists_isIso_isPullback_fiberι_genericPoint {A : Type u} [CommRing A] [IsDomain A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of A)) :
    ∃ i : Spec ((Spec (.of A)).residueField (genericPoint (Spec (.of A)))) ⟶ Spec (.of K),
      IsIso i ∧
      IsPullback (g.fiberι (genericPoint (Spec (.of A))))
        (g.fiberToSpecResidueField (genericPoint (Spec (.of A))) ≫ i) g
        (Spec.map (CommRingCat.ofHom (algebraMap A K))) := by
  have _ : IsDomain (CommRingCat.of A) := inferInstanceAs (IsDomain A)
  let κ := (Spec (.of A)).residueField (genericPoint (Spec (.of A)))
  let _ : Algebra (CommRingCat.of A) κ :=
    specResidueFieldAlgebra (CommRingCat.of A) (genericPoint (Spec (.of A)))
  have _ : IsFractionRing (CommRingCat.of A) κ :=
    isFractionRing_specResidueField_genericPoint (CommRingCat.of A)
  let ψ : K ≃ₐ[A] κ := IsLocalization.algEquiv (nonZeroDivisors A) K κ
  let ι : CommRingCat.of K ≅ CommRingCat.of κ := ψ.toRingEquiv.toCommRingCatIso
  refine ⟨Spec.map ι.hom, inferInstance, IsPullback.comp_isIso_right ?_⟩
  have hcomp : CommRingCat.ofHom (algebraMap A K) ≫ ι.hom =
      CommRingCat.ofHom (algebraMap (CommRingCat.of A) κ) := by
    ext a
    exact ψ.commutes a
  rw [← Spec.map_comp, hcomp, ← fromSpecResidueField_eq_specMap]
  exact isPullback_fiberι_fiberToSpecResidueField g (genericPoint (Spec (.of A)))

/-- **A dense smooth open on a base change to the fraction field gives one on the fibre over the
generic point.** Let `A` be a domain with fraction field `K`, let `g : Y ⟶ Spec A` and let
`XK` be any base change of `g` along `Spec K ⟶ Spec A`. A dense open subscheme of `XK` smooth
over `Spec K` produces a dense open subscheme of the fibre of `g` over the generic point of
`Spec A` which is smooth over the residue field there.

This is the bridge between the two presentations of the generic fibre used in the proof of the
reduced fibre theorem: the first paragraph produces its dense smooth open on a base change along
`Spec L ⟶ Spec A`, while the later paragraphs read it on `g.fiber (genericPoint (Spec A))`. -/
theorem exists_dense_open_smooth_fiber_genericPoint_of_isPullback {A : Type u} [CommRing A]
    [IsDomain A] (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K] {Y XK : Scheme.{u}}
    (g : Y ⟶ Spec (.of A)) {p : XK ⟶ Y} {q : XK ⟶ Spec (.of K)}
    (sq : IsPullback p q g (Spec.map (CommRingCat.ofHom (algebraMap A K))))
    (U : XK.Opens) (hU : Dense (U : Set XK)) (hsmooth : Smooth (U.ι ≫ q)) :
    ∃ V : (g.fiber (genericPoint (Spec (.of A)))).Opens,
      Dense (V : Set (g.fiber (genericPoint (Spec (.of A))))) ∧
      Smooth (V.ι ≫ g.fiberToSpecResidueField (genericPoint (Spec (.of A)))) := by
  obtain ⟨i, _, sq'⟩ := exists_isIso_isPullback_fiberι_genericPoint K g
  let e : XK ≅ g.fiber (genericPoint (Spec (.of A))) := sq.isoIsPullback _ _ sq'
  have hq : e.inv ≫ q = g.fiberToSpecResidueField (genericPoint (Spec (.of A))) ≫ i :=
    e.inv_comp_eq.2 (sq.isoIsPullback_hom_snd _ _ sq').symm
  refine ⟨e.inv ⁻¹ᵁ U, hU.preimage (Scheme.homeoOfIso e.symm).isOpenMap, ?_⟩
  have hsm : Smooth ((e.inv ⁻¹ᵁ U).ι ≫
      g.fiberToSpecResidueField (genericPoint (Spec (.of A))) ≫ i) := by
    rw [← hq, ← Category.assoc, ← morphismRestrict_ι e.inv U, Category.assoc]
    exact MorphismProperty.comp_mem _ _ _ inferInstance hsmooth
  simpa using MorphismProperty.comp_mem @Smooth _ _ hsm (inferInstance : Smooth (inv i))

end AlgebraicGeometry

end
