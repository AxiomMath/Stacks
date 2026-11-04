module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartStalkTensorIsomorphism
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.RankOneDescent

/-!
# Descending freeness of rank one from the geometric stalk to the Zariski stalk of the chart

Let `X` be an algebraic space over a scheme `S`, let `F` be a quasi-coherent `𝒪_X`-module, let
`x̄` be a geometric point of `X` and let `φ : (U, ū) → (X, x̄)` be an étale neighbourhood whose
chart `U` is a scheme.  Stacks 05VP identifies

`(φ^* F)_u ⊗_{𝒪_{U, u}} 𝒪_{X, x̄} = F_{x̄}`,

and the base-change map `𝒪_{U, u} → 𝒪_{X, x̄}` is faithfully flat with `𝒪_{X, x̄}` local.  So
if the geometric stalk `F_{x̄}` is free of rank one over `𝒪_{X, x̄}`, the Zariski stalk
`(φ^* F)_u` is free of rank one over `𝒪_{U, u}`.

This is the passage the source of Stacks 0EPQ performs implicitly when it reads the triviality
of an invertible module at a codimension-zero point `η` as the stalk `ℒ_η` being free of rank
one over the *Zariski* local ring `𝒪_{X, η}` of the schematic locus: the étale side is where a
tensor comparison of stalks is available, and this carries the conclusion back across
Stacks 05VP.

## Main results

* `AlgebraicGeometry.Space.nonempty_linearEquiv_chartZariskiModuleStalk_of_geometricModuleStalk`:
  freeness of rank one of the geometric stalk descends to the Zariski stalk of the chart.

## Implementation notes

The three inputs are all available and none of them is reproved here:
`AlgebraicGeometry.Space.isIso_chartStalkTensorComparison` (Stacks 05VP),
`AlgebraicGeometry.Space.faithfullyFlat_chartLocalRingToEtaleLocalRing` and
`AlgebraicGeometry.Space.isLocalRing_etaleLocalRing` (Stacks 08AH).  The algebra is
`Module.nonempty_linearEquiv_of_tensorProduct_of_faithfullyFlat`, which needs no finiteness of
the module, no locality of the source ring and no local-homomorphism hypothesis.

The quasi-coherence hypothesis and the module universe `m = u` are inherited verbatim from
`AlgebraicGeometry.Space.isIso_chartStalkTensorComparison`; both are what Stacks 05VP itself
assumes in this development, and neither is added here.

No `stacks` attribute is attached: the statement is a composition of Stacks 05VP with faithfully
flat descent, and each half carries its own tag already.

## References

* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
* [Stacks Project, Tag 08AH](https://stacks.math.columbia.edu/tag/08AH)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)

/-- **Freeness of rank one descends from the geometric stalk to the Zariski stalk of the
chart.**  Let `F` be a quasi-coherent `𝒪_X`-module, let `x̄` be a geometric point of the
algebraic space `X` and let `V` be a small étale neighbourhood of `x̄` whose chart is a scheme
`U`.  If the geometric stalk `F_{x̄}` is free of rank one over the étale local ring
`𝒪_{X, x̄}`, then the Zariski stalk `(φ^* F)_u` is free of rank one over the local ring
`𝒪_{U, u}` of the chart.

Stacks 05VP presents `F_{x̄}` as `(φ^* F)_u ⊗_{𝒪_{U, u}} 𝒪_{X, x̄}`, the base-change map is
faithfully flat and `𝒪_{X, x̄}` is a local ring, so this is faithfully flat descent of
freeness of rank one. -/
theorem nonempty_linearEquiv_chartZariskiModuleStalk_of_geometricModuleStalk
    {x : GeometricPoint B S hS X} (V : SmallEtaleNeighborhood x)
    (F : Modules.{u, u} B S hS X hX) [F.IsQuasicoherentOnSite]
    (e : ↥(geometricModuleStalk B S hS ⟨X, hX⟩ x F) ≃ₗ[↥(etaleLocalRing B S hS X x)]
      ↥(etaleLocalRing B S hS X x)) :
    Nonempty (↥(chartZariskiModuleStalk B S hS X hX V F) ≃ₗ[↥(chartLocalRing B S hS X V)]
      ↥(chartLocalRing B S hS X V)) := by
  let : Algebra ↥(chartLocalRing B S hS X V) ↥(etaleLocalRing B S hS X x) :=
    (chartLocalRingToEtaleLocalRing B S hS X hX V).toAlgebra
  have : IsLocalRing ↥(etaleLocalRing B S hS X x) := isLocalRing_etaleLocalRing B S hS X hX x
  have : Module.FaithfullyFlat ↥(chartLocalRing B S hS X V)
      ↥(etaleLocalRing B S hS X x) :=
    faithfullyFlat_chartLocalRingToEtaleLocalRing B S hS X hX V
  have := isIso_chartStalkTensorComparison B S hS hX V F
  exact Module.nonempty_linearEquiv_of_tensorProduct_of_faithfullyFlat _
    ((asIso (chartStalkTensorComparison B S hS hX V F)).toLinearEquiv.trans e)

end AlgebraicGeometry.Space

end
