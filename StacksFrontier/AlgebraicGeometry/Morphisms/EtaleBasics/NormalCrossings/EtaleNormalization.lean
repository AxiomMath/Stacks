module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.NormalizationCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.EtaleBaseChange

/-!
# Étale localization of the normalization of a divisor

Let `f : U ⟶ X` be an étale morphism of locally Noetherian schemes and `D` a closed subscheme
of `X`. The closed subscheme cut out by the pullback of `D` is the fibre product of `U` with
the closed subscheme cut out by `D`, so it maps to the latter by an étale morphism; and because
normalization commutes with étale base change, the normalization of the pullback divisor is the
fibre product of the normalization of `D` with that subscheme.

## Main definitions

* `Stacks.Divisors.comapSubschemeMap` is the induced morphism from the subscheme cut out by the
  pullback divisor to the subscheme cut out by the divisor.
* `Stacks.Divisors.comapNormalizationMap` is the induced morphism of normalizations.

## Main results

* `Stacks.Divisors.isPullback_comapSubschemeMap`: the subscheme cut out by the pullback divisor
  is the fibre product of the étale chart with the subscheme cut out by the divisor.
* `Stacks.Divisors.etale_comapSubschemeMap`: that morphism of subschemes is étale.
* `Stacks.Divisors.isPullback_comapNormalizationMap`: the normalization of the pullback divisor
  is the fibre product of the normalization of the divisor with the pullback subscheme.

## Implementation notes

The finiteness hypothesis on irreducible components that the normalization of a scheme requires
is a proposition, so the proof term supplied by
`AlgebraicGeometry.finite_irreducibleComponents_of_isCompact` and the one
`AlgebraicGeometry.isPullback_normalizationSchemeMap_of_etale` manufactures from smoothness of the
chart are interchangeable by proof irrelevance; no transport is needed.

## References

* [Stacks Project, Tag 0CBR](https://stacks.math.columbia.edu/tag/0CBR)
* [Stacks Project, Tag 07TD](https://stacks.math.columbia.edu/tag/07TD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Divisors

variable {X U : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian U]
  (f : U ⟶ X) [Etale f] (D : X.IdealSheafData)

/-- The morphism from the subscheme cut out by the pullback of a divisor to the subscheme cut
out by the divisor. -/
def comapSubschemeMap : (D.comap f).subscheme ⟶ D.subscheme :=
  Scheme.IdealSheafData.subschemeMap _ _ f (D.le_map_comap f)

omit [IsLocallyNoetherian X] [IsLocallyNoetherian U] [Etale f] in
/-- The morphism of divisor subschemes is the second projection of the fibre product, read
through the identification of the pullback subscheme with that fibre product. -/
theorem comapIso_hom_snd_eq :
    (D.comapIso f).hom ≫ pullback.snd f D.subschemeι = comapSubschemeMap f D :=
  Scheme.IdealSheafData.comapIso_hom_snd D f

omit [IsLocallyNoetherian X] [IsLocallyNoetherian U] [Etale f] in
/-- The square of the two closed immersions and the two charts commutes. -/
theorem comapSubschemeMap_comp :
    (D.comap f).subschemeι ≫ f = comapSubschemeMap f D ≫ D.subschemeι :=
  (Scheme.IdealSheafData.subschemeMap_subschemeι _ _ f (D.le_map_comap f)).symm

omit [IsLocallyNoetherian X] [IsLocallyNoetherian U] [Etale f] in
/-- The subscheme cut out by the pullback of a divisor is the fibre product of the chart with
the subscheme cut out by the divisor. -/
theorem isPullback_comapSubschemeMap :
    IsPullback (D.comap f).subschemeι (comapSubschemeMap f D) f D.subschemeι :=
  IsPullback.of_iso_pullback ⟨comapSubschemeMap_comp f D⟩ (D.comapIso f)
    (Scheme.IdealSheafData.comapIso_hom_fst D f) (comapIso_hom_snd_eq f D)

/-- The morphism of divisor subschemes induced by an étale chart is étale. -/
instance etale_comapSubschemeMap : Etale (comapSubschemeMap f D) := by
  rw [← comapIso_hom_snd_eq f D]
  infer_instance

/-- The morphism of divisor subschemes induced by an étale chart is flat. -/
instance flat_comapSubschemeMap : Flat (comapSubschemeMap f D) := inferInstance

/-- The induced morphism from the normalization of the pullback divisor to the normalization of
the divisor. -/
def comapNormalizationMap :
    divisorNormalizationScheme (D.comap f) ⟶ divisorNormalizationScheme D :=
  letI : IsLocallyNoetherian D.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian D.subschemeι
  letI : IsLocallyNoetherian (D.comap f).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (D.comap f).subschemeι
  normalizationSchemeMap (comapSubschemeMap f D)
    (finite_irreducibleComponents_of_isCompact (D.comap f).subscheme)
    (finite_irreducibleComponents_of_isCompact D.subscheme)

/-- **Normalization commutes with étale localization of a divisor.** The normalization of the
pullback of `D` along an étale chart is the fibre product of the normalization of `D` with the
pullback subscheme. -/
theorem isPullback_comapNormalizationMap :
    IsPullback (comapNormalizationMap f D) (divisorNormalization (D.comap f))
      (divisorNormalization D) (comapSubschemeMap f D) :=
  let : IsLocallyNoetherian D.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian D.subschemeι
  let : IsLocallyNoetherian (D.comap f).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (D.comap f).subschemeι
  isPullback_normalizationSchemeMap_of_etale (comapSubschemeMap f D)
    (finite_irreducibleComponents_of_isCompact D.subscheme)

end Stacks.Divisors

end
