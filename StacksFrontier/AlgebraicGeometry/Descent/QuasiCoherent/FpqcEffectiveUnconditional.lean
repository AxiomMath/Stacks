module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.ZariskiTransitionExists
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Effective fpqc descent of quasi-coherent modules

Every quasi-coherent descent datum for an fpqc covering family of an arbitrary scheme is effective,
at an arbitrary index universe. Together with full faithfulness of the canonical descent functor,
`AlgebraicGeometry.nonempty_fullyFaithful_canonicalDescentFunctor'`, this makes that functor an
equivalence of categories.

## Main results

* `AlgebraicGeometry.QuasicoherentDescentData.isEffective_fpqcPrecoverage`: every quasi-coherent
  descent datum for an fpqc covering family is effective.
* `AlgebraicGeometry.QuasicoherentDescentData.isEquivalence_canonicalDescentFunctor_fpqc`: the
  canonical descent functor of an fpqc covering family is an equivalence.
* `AlgebraicGeometry.QuasicoherentDescentData.effectiveGluesOverAffineOpens`: effective descent for
  quasi-coherent modules is local on the base over the affine opens.
* `AlgebraicGeometry.QuasicoherentDescentData.effectiveSigmaFamilyOverAnyBase`: descent along the
  morphism out of the coproduct of a covering family is effective over an arbitrary base.

## References

* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.QuasicoherentDescentData

/-- Every quasi-coherent descent datum for an fpqc covering family of an arbitrary scheme is
effective, at an arbitrary index universe. -/
@[stacks 023T "effectivity, arbitrary fpqc covering family",
  stacks 03O8 "effectivity of all quasi-coherent descent data for an fpqc covering",
  sga "1 VIII 1.1" "effectivity", sga "4½ Arcata 1.4" "fpqc qcoh case"]
theorem isEffective_fpqcPrecoverage {S : Scheme.{u}} (𝒰 : PreZeroHypercover.{v} S)
    (h𝒰 : 𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage.{u} S) (D : QuasicoherentDescentData 𝒰.f) :
    D.IsEffective :=
  isEffective_fpqcPrecoverage_of_zariskiDatum zariskiDescentDatumOverAffineCover 𝒰 h𝒰 D

/-- For an fpqc covering family of a scheme `S`, indexed in `Type (u + 1)`, the canonical descent
functor from the quasi-coherent `𝒪_S`-modules to the descent data with respect to that family is an
equivalence of categories. -/
@[stacks 023T "both assertions in one statement: the canonical descent functor is an \
equivalence.  The index universe is u + 1, fixed by the full-faithfulness half \
nonempty_fullyFaithful_canonicalDescentFunctor'; effectivity on its own is \
isEffective_fpqcPrecoverage above, at an arbitrary index universe"]
theorem isEquivalence_canonicalDescentFunctor_fpqc {S : Scheme.{u}} {I : Type (u + 1)}
    {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S)
    (hfpqc : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage.{u} S) :
    (canonicalDescentFunctor f).IsEquivalence :=
  have hff := (nonempty_fullyFaithful_canonicalDescentFunctor' f hfpqc).some
  have : (canonicalDescentFunctor f).Full := hff.full
  have : (canonicalDescentFunctor f).Faithful := hff.faithful
  have : (canonicalDescentFunctor f).EssSurj :=
    ⟨fun D ↦ isEffective_fpqcPrecoverage ⟨I, X, f⟩ hfpqc D⟩
  {}

/-- `AlgebraicGeometry.QuasicoherentDescentData.EffectiveGluesOverAffineOpens` holds: effective
descent for quasi-coherent modules is local on the base over the affine opens. -/
theorem effectiveGluesOverAffineOpens : EffectiveGluesOverAffineOpens.{v, u} :=
  effectiveGluesOverAffineOpens_of_zariskiDatum zariskiDescentDatumOverAffineCover

/-- `AlgebraicGeometry.QuasicoherentDescentData.EffectiveSigmaFamilyOverAnyBase` holds: descent
along the single faithfully flat morphism out of the coproduct of a covering family is effective
over an arbitrary base. -/
theorem effectiveSigmaFamilyOverAnyBase : EffectiveSigmaFamilyOverAnyBase.{u} :=
  effectiveSigmaFamilyOverAnyBase_of_zariskiDatum zariskiDescentDatumOverAffineCover

end AlgebraicGeometry.QuasicoherentDescentData

end
