module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.Models.Reduction
public import StacksFrontier.AlgebraicGeometry.Curves.PrescribedLowCohomologyFieldExtension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.LocallyProjective
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ProperGlobalSections
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.GeometricallyRegularNormal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Semistable reduction after an extension of the ground field

Let `R` be a discrete valuation ring with fraction field `K`, let `C` be a smooth projective curve
over `K` with `H⁰(C, 𝒪_C) = K`, and let `K'/K` be a field extension. The base change
`C_{K'} = C ×_{Spec K} Spec K'` is again a smooth projective curve over `K'` with
`H⁰(C_{K'}, 𝒪) = K'`, so it makes sense to ask whether it has semistable reduction over a
discrete valuation ring with fraction field `K'`. The semistable reduction theorem
[Stacks, Tag 0CDN] asks this for the localizations `R'_𝔪` of the integral closure `R'` of `R` in
`K'` at its maximal ideals.

## Main definitions

* `Stacks.Models.HasSemistableReductionAtMaximalIdeals` — `C_{K'}` has semistable reduction over
  `R'_𝔪` for every maximal ideal `𝔪` of the integral closure `R'` of `R` in `K'`.

## Main results

* `AlgebraicGeometry.geometricallyIrreducible_of_smooth_of_isIso_globalSections` — a smooth
  proper scheme over a field with only constant global functions is geometrically irreducible
  ([Stacks, Tag 0FD3] together with [Stacks, Tag 056T]).
* `AlgebraicGeometry.isCurve_pullback_snd_of_isIso_globalSections` — its base change to any
  field extension is a curve, as an instance.
* `AlgebraicGeometry.IsProjective.pullback_snd` — the base change of a projective morphism, read
  through the second projection.

## Implementation notes

The base change is the chosen pullback `pullback c (Spec.map (algebraMap K K'))`, with structure
morphism `pullback.snd`, so that smoothness and `H⁰ = K'`
(`AlgebraicGeometry.isIso_globalSections_pullback`) are found by instance search.

The localization `R'_𝔪` is not fixed as `Localization.AtPrime 𝔪`, which carries no algebra
structure over `K'` in Mathlib. Instead the definition quantifies over every ring `A` which is a
localization of `R'` at `𝔪` (`IsLocalization.AtPrime A 𝔪`) together with an identification of
`K'` with its fraction field compatible with `R' ⊆ K'`. Any two such `A` are isomorphic over
`R'`, so this is the source's condition. Being a localization of the Dedekind domain `R'` at a
nonzero maximal ideal, such an `A` is a discrete valuation ring; that structure, needed to state
`Stacks.Models.HasSemistableReduction`, is quantified over as well.

## References

* [Stacks Project, Tag 0CDN](https://stacks.math.columbia.edu/tag/0CDN)
* [Stacks Project, Tag 0CDH](https://stacks.math.columbia.edu/tag/0CDH)
* [Stacks Project, Tag 0FD3](https://stacks.math.columbia.edu/tag/0FD3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- **A smooth proper scheme over a field with `H⁰(X, 𝒪_X) = k` is geometrically irreducible.**
A smooth scheme over a field is geometrically normal ([Stacks, Tag 056T]), and for a proper
geometrically normal scheme `H⁰ = k` is equivalent to geometric irreducibility
([Stacks, Tag 0FD3]). -/
@[ega "II 7.4.19" "partial"]
theorem geometricallyIrreducible_of_smooth_of_isIso_globalSections (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [Smooth f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] : GeometricallyIrreducible f :=
  have h := (isIso_globalSections_tfae_geometricallyConnected_irreducible_integral k f
    (isGeometricallyNormal_of_smooth f)).out 1 3
  h.mp ‹_›

/-- **The base change of a smooth proper curve with `H⁰ = k` to a field extension is a curve.** -/
instance isCurve_pullback_snd_of_isIso_globalSections (k k' : Type u) [Field k] [Field k']
    [Algebra k k'] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] [IsProper f] [Smooth f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] :
    IsCurve k' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) :=
  haveI := geometricallyIrreducible_of_smooth_of_isIso_globalSections k f
  isCurve_pullback_snd k k' f

/-- **A base change of a projective morphism is projective**, for the second projection. -/
theorem IsProjective.pullback_snd {X S S' : Scheme.{u}} {f : X ⟶ S} (g : S' ⟶ S)
    (hf : IsProjective f) : IsProjective (pullback.snd f g) := by
  obtain ⟨E, hq, hft, hqc, i, hi, hfac⟩ := hf.pullback_fst g
  refine ⟨E, hq, hft, hqc, (pullbackSymmetry f g).hom ≫ i, inferInstance, ?_⟩
  rw [Category.assoc, hfac, pullbackSymmetry_hom_comp_fst]

end AlgebraicGeometry

namespace Stacks.Models

variable (R : Type u) [CommRing R] (K' : Type u) [Field K'] [Algebra R K']

/-- **Semistable reduction over every localization of the integral closure.** Let `R` be a ring
with an algebra map to a field `K'`, let `R'` be the integral closure of `R` in `K'`, and let `C'`
be a smooth projective curve over `K'` with `H⁰(C', 𝒪) = K'`. Then `C'` has semistable reduction
over `R'_𝔪` for every maximal ideal `𝔪` of `R'`: for every localization `A` of `R'` at `𝔪`,
viewed inside `K'` as a discrete valuation ring with fraction field `K'`, `C'` has semistable
reduction over `A` in the sense of [Stacks, Tag 0CDH]. -/
def HasSemistableReductionAtMaximalIdeals {C' : Scheme.{u}} (c' : C' ⟶ Spec (.of K'))
    [IsCurve K' c'] [Smooth c'] (hproj : IsProjective c')
    [IsIso ((Scheme.ΓSpecIso (.of K')).inv ≫ c'.appTop)] : Prop :=
  ∀ (𝔪 : Ideal (integralClosure R K')) [𝔪.IsMaximal] (A : Type u) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Algebra (integralClosure R K') A] [IsLocalization.AtPrime A 𝔪]
    [Algebra A K'] [IsFractionRing A K'] [IsScalarTower (integralClosure R K') A K'],
    HasSemistableReduction A c' hproj


end Stacks.Models

end
