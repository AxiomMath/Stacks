module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicEtaleExactnessReflection
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicPullbackExactNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.PullbackIdealImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.PullbackIdealPowerCompatible

/-!
# Coherent adic systems on Noetherian algebraic spaces: Stacks 089P

Let `S` be a scheme, `X` a Noetherian algebraic space over `S` and `𝓘 ⊆ 𝒪_X` a quasi-coherent
sheaf of ideals.  Stacks 089P states three facts about the category `Coh(X, 𝓘)` of coherent
`𝓘`-adic systems:

1. `Coh(X, 𝓘)` is abelian;
2. exactness in `Coh(X, 𝓘)` can be checked étale locally;
3. for a flat morphism `f : X' ⟶ X` of Noetherian algebraic spaces the inverse image
   `f^* : Coh(X, 𝓘) ⥤ Coh(X', f⁻¹𝓘 · 𝒪_{X'})` is exact.

In parts (2) and (3) the ideal on the source of the morphism is the inverse-image ideal
`f⁻¹𝓘 · 𝒪_{X'}`, `AlgebraicGeometry.Space.pullbackIdealImage`.  **This file states parts (2) and
(3) at that ideal, with nothing about it assumed**: it is quasi-coherent by
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_pullbackIdealImage`, and the inverse image of
modules is compatible with the ideal-power multiples of `𝓘` and of `f⁻¹𝓘 · 𝒪_{X'}` by
`AlgebraicGeometry.Space.idealPowerMultipleCompatible_pullbackIdealImage`, which is what the
inverse image of coherent adic systems is built from.  Part (1) is
`AlgebraicGeometry.Space.abelian_coherentAdicSystems`, and the three parts are bundled in
`AlgebraicGeometry.Space.coherentAdicSystems_abelian_and_exact`.

## Main definitions

* `AlgebraicGeometry.Space.coherentAdicInverseImage` — the inverse image
  `f^* : Coh(X, 𝓘) ⥤ Coh(X', f⁻¹𝓘 · 𝒪_{X'})` along a morphism of algebraic spaces whose source
  is locally Noetherian.

## Main results

* `AlgebraicGeometry.Space.coherentAdicRestrictToChart_pullbackIdealImage` — the restriction
  `Coh(X, 𝓘) ⥤ Coh(U, 𝓘 · 𝒪_U)` to an affine étale chart is the inverse image along the chart
  morphism.
* `AlgebraicGeometry.Space.exact_iff_forall_exact_coherentAdicChartRestriction` — **part (2):
  a short complex of `Coh(X, 𝓘)` is exact exactly when its restriction to each member of an
  étale covering of `X` by affine charts is exact.**
* `AlgebraicGeometry.Space.coherentAdicInverseImage_exact` — **part (3): the inverse image along
  a flat morphism of Noetherian algebraic spaces is exact.**
* `AlgebraicGeometry.Space.coherentAdicSystems_abelian_and_exact` — parts (1) to (3) together.

## Implementation notes

Quasi-coherence of a sheaf of ideals is expressed as being cartesian on affine charts,
`AlgebraicGeometry.Space.IsCartesianOnAffineCharts`, which is equivalent to quasi-coherence on the
small étale site by Stacks 03DX
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts`).

The étale coverings of part (2) are coverings by affine étale charts.  That is the correct
statement rather than a restriction of it: the restriction functor to a chart is a functor into
`Coh(U, 𝓘 · 𝒪_U)`, which is only known to be an abelian category, and the restriction only known
to be exact, when the chart is Noetherian, and an étale chart of a Noetherian algebraic space
need not be quasi-compact; the affine charts cover the small étale site, so no étale covering is
lost.  See the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicChartRestriction`.

## References

* [Stacks Project, Tag 089P](https://stacks.math.columbia.edu/tag/089P)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The inverse image at the inverse-image ideal -/

section InverseImage

variable {X X' : AlgebraicSpaces B S hS} (f : X' ⟶ X)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).Submodule)

/-- **The inverse image `f^* : Coh(X, 𝓘) ⥤ Coh(X', f⁻¹𝓘 · 𝒪_{X'})`** along a morphism of
algebraic spaces whose source is locally Noetherian: termwise inverse image of modules, which
carries coherent modules to coherent modules on the locally Noetherian source and is compatible
with the ideal-power multiples of `𝓘` and of the inverse-image ideal. -/
abbrev coherentAdicInverseImage
    (hLN : HasEtaleLocalProperty B S hS X'.1 (fun V : Scheme.{u} => IsLocallyNoetherian V)) :
    CoherentAdicSystems B S hS X.1 X.2 𝓘 ⥤
      CoherentAdicSystems B S hS X'.1 X'.2 (pullbackIdealImage B S hS f 𝓘) :=
  coherentAdicPullback B S hS f 𝓘 (pullbackIdealImage B S hS f 𝓘)
    (idealPowerMultipleCompatible_pullbackIdealImage B S hS f 𝓘)
    (isCoherent_modulePullback_of_hasEtaleLocalProperty B S hS f hLN)

variable (hZ : B.Contains (⊤_ Scheme.{u}))
    (hN : IsNoetherian B S hS hZ X.1) (hN' : IsNoetherian B S hS hZ X'.1)
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)

include hN hIcart in
/-- **Part (3) of Stacks 089P: the inverse image along a flat morphism of Noetherian algebraic
spaces is exact.**  For a flat morphism `f : X' ⟶ X` of Noetherian algebraic spaces and a
quasi-coherent sheaf of ideals `𝓘 ⊆ 𝒪_X`, the functor
`f^* : Coh(X, 𝓘) ⥤ Coh(X', f⁻¹𝓘 · 𝒪_{X'})` preserves finite limits and finite colimits. -/
@[stacks 089P "part (3): the inverse image along a flat morphism of Noetherian algebraic spaces \
is exact"]
theorem coherentAdicInverseImage_exact (hf : IsFlat B S hS f.hom) :
    exactFunctor (CoherentAdicSystems B S hS X.1 X.2 𝓘)
      (CoherentAdicSystems B S hS X'.1 X'.2 (pullbackIdealImage B S hS f 𝓘))
      (coherentAdicInverseImage B S hS f 𝓘 hN'.2.2) :=
  coherentAdicPullback_exact B S hS f 𝓘 (pullbackIdealImage B S hS f 𝓘) hZ hN hN' hIcart
    (isCartesianOnAffineCharts_pullbackIdealImage B S hS f 𝓘 hIcart)
    (idealPowerMultipleCompatible_pullbackIdealImage B S hS f 𝓘) hf

end InverseImage

/-! ### Restriction to affine étale charts -/

section Charts

variable (X : AlgebraicSpaces B S hS)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).Submodule)
    (hZ : B.Contains (⊤_ Scheme.{u})) (hN : IsNoetherian B S hS hZ X.1)
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)

/-- **The restriction `Coh(X, 𝓘) ⥤ Coh(U, 𝓘 · 𝒪_U)` to an affine étale chart `U` of a
Noetherian algebraic space, at the inverse-image ideal `𝓘 · 𝒪_U`, is the inverse image along
the chart morphism.** -/
theorem coherentAdicRestrictToChart_pullbackIdealImage (V : SmallEtale B S hS X.1)
    (hV : IsAffine (chartScheme V)) :
    coherentAdicRestrictToChart B S hS X V 𝓘
        (pullbackIdealImage B S hS (chartToSpace B S hS X V) 𝓘) hZ hN hV
        (idealPowerMultipleCompatible_pullbackIdealImage B S hS (chartToSpace B S hS X V) 𝓘) =
      coherentAdicInverseImage B S hS (chartToSpace B S hS X V) 𝓘
        (isNoetherian_chartSpace_of_isAffine B S hS X V hZ hN hV).2.2 :=
  rfl

include hIcart in
/-- **Part (2) of Stacks 089P: exactness in `Coh(X, 𝓘)` can be checked étale locally.**  For a
Noetherian algebraic space `X`, a quasi-coherent sheaf of ideals `𝓘 ⊆ 𝒪_X` and an étale covering
of `X` by affine charts `U i`, a short complex `E ⟶ G ⟶ H` of `Coh(X, 𝓘)` is exact exactly when
its restriction `E|_{U i} ⟶ G|_{U i} ⟶ H|_{U i}` to `Coh(U i, 𝓘 · 𝒪_{U i})` is exact for every
`i`. -/
@[stacks 089P "part (2): exactness can be checked on an étale covering by affine charts"]
theorem exact_iff_forall_exact_coherentAdicChartRestriction {I : Type v}
    (U : I → SmallEtale B S hS X.1) (hU : ∀ i, IsAffine (chartScheme (U i)))
    (hcov : IsEtaleCovering B S hS (fun i => (chartSpace B S hS X (U i)).1)
      (fun i => (chartToSpace B S hS X (U i)).hom))
    (T : ShortComplex (CoherentAdicSystems B S hS X.1 X.2 𝓘)) :
    T.Exact ↔ ∀ i, (coherentAdicRestrictToChartShortComplex B S hS X 𝓘 hZ hN (U i)
      (pullbackIdealImage B S hS (chartToSpace B S hS X (U i)) 𝓘) (hU i)
      (idealPowerMultipleCompatible_pullbackIdealImage B S hS (chartToSpace B S hS X (U i)) 𝓘)
      T).Exact :=
  exact_iff_forall_exact_coherentAdicRestrictToChart B S hS X 𝓘 hZ hN hIcart U
    (fun i => pullbackIdealImage B S hS (chartToSpace B S hS X (U i)) 𝓘) hU
    (fun i => isCartesianOnAffineCharts_pullbackIdealImage B S hS (chartToSpace B S hS X (U i)) 𝓘
      hIcart)
    (fun i => idealPowerMultipleCompatible_pullbackIdealImage B S hS
      (chartToSpace B S hS X (U i)) 𝓘) hcov T

/-! ### The three parts together -/

include hIcart in
/-- **Stacks 089P.**  Let `X` be a Noetherian algebraic space over a scheme `S` and `𝓘 ⊆ 𝒪_X` a
quasi-coherent sheaf of ideals.

1. `Coh(X, 𝓘)` is abelian.
2. Exactness in `Coh(X, 𝓘)` can be checked étale locally: on every étale covering of `X` by
   affine charts `U i`, a short complex is exact exactly when its restrictions to the categories
   `Coh(U i, 𝓘 · 𝒪_{U i})` are.
3. For every flat morphism `f : X' ⟶ X` of Noetherian algebraic spaces the inverse image
   `f^* : Coh(X, 𝓘) ⥤ Coh(X', f⁻¹𝓘 · 𝒪_{X'})` is exact. -/
@[stacks 089P]
theorem coherentAdicSystems_abelian_and_exact :
    Nonempty (Abelian (CoherentAdicSystems B S hS X.1 X.2 𝓘)) ∧
    (∀ {I : Type v} (U : I → SmallEtale B S hS X.1) (hU : ∀ i, IsAffine (chartScheme (U i))),
      IsEtaleCovering B S hS (fun i => (chartSpace B S hS X (U i)).1)
          (fun i => (chartToSpace B S hS X (U i)).hom) →
        ∀ T : ShortComplex (CoherentAdicSystems B S hS X.1 X.2 𝓘),
          T.Exact ↔ ∀ i, (coherentAdicRestrictToChartShortComplex B S hS X 𝓘 hZ hN (U i)
            (pullbackIdealImage B S hS (chartToSpace B S hS X (U i)) 𝓘) (hU i)
            (idealPowerMultipleCompatible_pullbackIdealImage B S hS
              (chartToSpace B S hS X (U i)) 𝓘) T).Exact) ∧
    (∀ {X' : AlgebraicSpaces B S hS} (f : X' ⟶ X) (hN' : IsNoetherian B S hS hZ X'.1),
      IsFlat B S hS f.hom →
        exactFunctor (CoherentAdicSystems B S hS X.1 X.2 𝓘)
          (CoherentAdicSystems B S hS X'.1 X'.2 (pullbackIdealImage B S hS f 𝓘))
          (coherentAdicInverseImage B S hS f 𝓘 hN'.2.2)) :=
  ⟨⟨abelian_coherentAdicSystems B S hS X.1 X.2 𝓘 hZ hN hIcart⟩,
    fun U hU hcov T =>
      exact_iff_forall_exact_coherentAdicChartRestriction B S hS X 𝓘 hZ hN hIcart U hU hcov T,
    fun f hN' hf => coherentAdicInverseImage_exact B S hS f 𝓘 hZ hN hN' hIcart hf⟩

end Charts

end AlgebraicGeometry.Space

end
