module

public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.InvariantBaseChangeMorphism
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.LocusBaseChange

/-!
# The étale locus of the map on invariant rings under a flat base change

Let `F : G' ⟶ G` be a morphism of groupoid schemes with affine object and arrow schemes, write
`C` and `C'` for the two rings of invariant functions, and let `C ⟶ C₁` be an extension of `C`.
The spectrum of `C' ⊗[C] C₁` is the fibre product `Spec C' ×_{Spec C} Spec C₁`
(`AlgebraicGeometry.GroupoidScheme.isPullback_invariantSpectrumMap_tensorBaseRing`), so the
pointwise form of the base change behaviour of the étale locus applies verbatim: when
`Spec C₁ ⟶ Spec C` is flat and `Spec C' ⟶ Spec C` is locally of finite presentation, a point of
`Spec (C' ⊗[C] C₁)` is a point of étaleness of `Spec (C' ⊗[C] C₁) ⟶ Spec C₁` exactly when its
image in `Spec C'` is a point of étaleness of `Spec C' ⟶ Spec C`.

This is the mechanism by which the "Claim" of [Stacks Project, Tag 0DT9] — proved there after
base changing to the strict henselization of a local ring of `Spec C` — is transported back to
`Spec C' ⟶ Spec C` itself.

## Main results

* `AlgebraicGeometry.GroupoidScheme.etaleAt_specMap_invariantRingMap_iff_tensorBaseRing`: the
  pointwise comparison of the two étale loci.
* `AlgebraicGeometry.GroupoidScheme.etaleAt_specMap_invariantRingMap_of_tensorBaseRing`: the
  direction which transports étaleness downwards, from the base change to the original map.
* `AlgebraicGeometry.GroupoidScheme.setOf_etaleAt_specMap_tensorBaseRingMap_eq_preimage`: the
  two étale loci as subsets, one the preimage of the other.

## Implementation notes

Both statements are about `AlgebraicGeometry.GroupoidScheme.tensorBaseRing`, the specified
extension `C' ⟶ C' ⊗[C] C₁` of the invariant ring of `G'`, and not about an arbitrary compatible
pair of extensions `C ⟶ C₁`, `C' ⟶ C'₁`: the hypothesis of
`AlgebraicGeometry.etaleAt_iff_of_isPullback` is that the square of the four spectra is
cartesian, which is exactly what the tensor product presentation supplies and what a general
compatible pair does not.

Flatness of `Spec C₁ ⟶ Spec C` and local finite presentation of `Spec C' ⟶ Spec C` are taken as
hypotheses rather than derived. The former is the flatness assumption the source text makes on
its base change; the latter is part of the conclusion of Tag 0DT9 and must therefore be
established before this comparison can be used in its proof — the source text leaves that
implicit.

## References

* [Stacks Project, Tag 0476](https://stacks.math.columbia.edu/tag/0476)
* [Stacks Project, Tag 03BK](https://stacks.math.columbia.edu/tag/03BK)
* [Stacks Project, Tag 0DT9](https://stacks.math.columbia.edu/tag/0DT9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}} {G G' : GroupoidScheme S} (F : GroupoidScheme.Hom G' G)
  (C₁ : Type u) [CommRing C₁] [Algebra (invariantRing G) C₁]

/-- **Stacks Project, Tag 0476, at the tensor product.** For a flat extension `C ⟶ C₁` of the
invariant ring of `G` and a map on invariant rings which is locally of finite presentation on
spectra, a point of `Spec (C' ⊗[C] C₁)` is a point of étaleness of the base changed map on
invariant rings exactly when its image in `Spec C'` is a point of étaleness of the map on
invariant rings. -/
theorem etaleAt_specMap_invariantRingMap_iff_tensorBaseRing
    [LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (invariantRingMap F)))]
    (hflat : Flat (invariantSpectrumMap G C₁)) :
    letI := invariantRingAlgebra F
    ∀ x : Spec (.of (tensorBaseRing F C₁)),
      EtaleAt (Spec.map (CommRingCat.ofHom (invariantRingMap F)))
          ((invariantSpectrumMap G' (tensorBaseRing F C₁)).base x) ↔
        EtaleAt (Spec.map (CommRingCat.ofHom (tensorBaseRingMap F C₁))) x :=
  let := invariantRingAlgebra F
  fun x => etaleAt_iff_of_isPullback (isPullback_invariantSpectrumMap_tensorBaseRing F C₁)
    (Or.inr hflat) x

/-- **Étaleness of the map on invariant rings is detected after a flat base change.** If the base
change of the map on invariant rings along a flat extension `C ⟶ C₁` is étale at a point of
`Spec (C' ⊗[C] C₁)`, then the map on invariant rings is étale at the image of that point in
`Spec C'`. -/
theorem etaleAt_specMap_invariantRingMap_of_tensorBaseRing
    [LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (invariantRingMap F)))]
    (hflat : Flat (invariantSpectrumMap G C₁)) :
    letI := invariantRingAlgebra F
    ∀ x : Spec (.of (tensorBaseRing F C₁)),
      EtaleAt (Spec.map (CommRingCat.ofHom (tensorBaseRingMap F C₁))) x →
        EtaleAt (Spec.map (CommRingCat.ofHom (invariantRingMap F)))
          ((invariantSpectrumMap G' (tensorBaseRing F C₁)).base x) :=
  let := invariantRingAlgebra F
  fun x => (etaleAt_specMap_invariantRingMap_iff_tensorBaseRing F C₁ hflat x).mpr

/-- The étale locus of the base changed map on invariant rings is the preimage of the étale locus
of the map on invariant rings. -/
theorem setOf_etaleAt_specMap_tensorBaseRingMap_eq_preimage
    [LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (invariantRingMap F)))]
    (hflat : Flat (invariantSpectrumMap G C₁)) :
    letI := invariantRingAlgebra F
    {x : Spec (.of (tensorBaseRing F C₁)) |
        EtaleAt (Spec.map (CommRingCat.ofHom (tensorBaseRingMap F C₁))) x} =
      (invariantSpectrumMap G' (tensorBaseRing F C₁)).base ⁻¹'
        {y : Spec (.of (invariantRing G')) |
          EtaleAt (Spec.map (CommRingCat.ofHom (invariantRingMap F))) y} :=
  let := invariantRingAlgebra F
  setOf_etaleAt_eq_preimage_of_isPullback
    (isPullback_invariantSpectrumMap_tensorBaseRing F C₁) (Or.inr hflat)

end AlgebraicGeometry.GroupoidScheme

end

end
