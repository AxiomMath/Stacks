module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.CohenMacaulay.Representable

/-!
# The Cohen–Macaulay locus read on a scheme presentation

A flat morphism of algebraic spaces over `S` which is locally of finite presentation can be
presented, over any chosen surjective étale chart of its target, by a morphism of the big
fppf site which is again flat and locally of finite presentation. The Cohen–Macaulay locus
of that morphism of the site is the preimage of the Cohen–Macaulay locus of the original
morphism under the chart of the source.

This is the step which transports questions about the Cohen–Macaulay locus of a morphism of
algebraic spaces — its openness, or its behaviour under base change — to the corresponding
questions about a morphism of schemes.

## Main results

* `AlgebraicGeometry.Space.exists_etale_presentation_cohenMacaulayLocus`: the presentation
  together with the identification of the two loci.

## Implementation notes

The presentation itself is Tag 02X1
(`AlgebraicGeometry.Space.exists_surjective_etale_presentation_lift`). Flatness and local
finite presentation of the presenting morphism are read off the resulting chart square and
fed back through `AlgebraicGeometry.Space.isFlat_yoneda_map` and
`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_yoneda_map`, so no chart-by-chart
argument is repeated here. The identification of the loci is
`AlgebraicGeometry.Space.isCohenMacaulayAt_chart_iff` applied to that same square, after
choosing a field-valued representative of a point of the source chart.

## References

* [Stacks Project, Tag 02X1](https://stacks.math.columbia.edu/tag/02X1)
* [Stacks Project, Tag 0E0V](https://stacks.math.columbia.edu/tag/0E0V)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- A flat morphism of algebraic spaces over `S` which is locally of finite presentation
admits, over a given surjective étale chart `q` of its target, a compatible surjective étale
chart `p` of its source whose presenting morphism `h` of the site is again flat and locally
of finite presentation, and the Cohen–Macaulay locus of `h` is the preimage under `p` of the
Cohen–Macaulay locus of the given morphism. -/
theorem exists_etale_presentation_cohenMacaulayLocus
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hf_flat : IsFlat B S hS f)
    (hf_lfp : IsLocallyOfFinitePresentation B S hS f)
    (V : BigFppfOver B S hS) (q : yoneda.obj V ⟶ Y)
    (hq_surjective : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (hq_etale : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q) :
    ∃ (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X) (h : U ⟶ V),
      p ≫ f = yoneda.map h ≫ q ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf p ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf p ∧
      IsFlat B S hS (yoneda.map h) ∧
      IsLocallyOfFinitePresentation B S hS (yoneda.map h) ∧
      {z : points B S hS (yoneda.obj U) | IsCohenMacaulayAt B S hS (yoneda.map h) z} =
        pointsMap B S hS (yoneda.obj U) p ⁻¹'
          {x : points B S hS X | IsCohenMacaulayAt B S hS f x} := by
  obtain ⟨U, p, h, comm, hp_surjective, hp_etale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V q hq_surjective hq_etale
  refine ⟨U, p, h, comm, hp_surjective, hp_etale,
    isFlat_yoneda_map B S hS h (hf_flat U V p q h hp_etale hq_etale comm.symm),
    isLocallyOfFinitePresentation_yoneda_map B S hS h
      (hf_lfp U V p q h hp_etale hq_etale comm.symm), Set.ext fun z => ?_⟩
  refine Quot.inductionOn z fun t => ?_
  exact isCohenMacaulayAt_chart_iff B S hS f U V p q h hp_etale hq_etale comm t
    (IsLocalRing.closedPoint t.carrier)

end AlgebraicGeometry.Space

end
