module

public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.Duality
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.ProperOverLocalBase
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekDualizingComplexOfCharts
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekChartModels

/-!
# Vanishing, support and Serre's condition for a proper scheme over a local base

Let `S` be an affine scheme whose ring of global sections `A = Γ(S, ⊤)` is a Noetherian local
ring, let `ω_S^•` be the complex on `S` associated to a normalized dualizing complex `ω_A^•` over
`A`, and let `f : X ⟶ S` be proper, with `ω_X^• = f^!ω_S^• = a(ω_S^•)` and
`ω_X = H^{-dim X}(ω_X^•)`; this is the situation of [Stacks, Tag 0AWI]. This file proves the four
assertions of [Stacks, Tag 0AWN] for `ω_X^•`, from the chart description of `f^!`
([Stacks, Tag 0BV2]).

## Main results

* `Stacks.Duality.UpperShriekCharts.hasTopCharts` — the chart description of `f^!E` over the
  affine open `⊤` of `S`, for a model of `E` on `⊤`.
* `Stacks.Duality.vanishing_and_support_relativeDualizingComplex` — the four assertions of
  [Stacks, Tag 0AWN].

## References

* [Stacks Project, Tag 0AWN](https://stacks.math.columbia.edu/tag/0AWN)
* [Stacks Project, Tag 0AWI](https://stacks.math.columbia.edu/tag/0AWI)
* [Stacks Project, Tag 0BV2](https://stacks.math.columbia.edu/tag/0BV2)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Duality

open ChartCompactification Stacks.Duality.ProjectiveSpace AlgebraicGeometry.ProjectiveSpace
  Stacks.AlgebraicGeometry.ProjPolyChart

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  [IsLocalRing Γ(S, ⊤)]

omit [IsLocalRing Γ(S, ⊤)] in
/-- An affine scheme with Noetherian ring of global sections is Noetherian. -/
theorem isNoetherian_of_isAffine_of_isNoetherianRing : AlgebraicGeometry.IsNoetherian S :=
  isNoetherian_of_isOpenImmersion S.isoSpec.hom

omit [IsLocalRing Γ(S, ⊤)] in
/-- The chart description of `f^!E` over `⊤ ⊆ S`, for a model `ω` of `E` on `⊤`, in the shape of
`Stacks.Duality.HasTopCharts`, read with the model of `D(𝒪_U)` of `IsTildeModelOnAnyModel`. -/
theorem UpperShriekCharts.hasTopCharts (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f]
    {j : CompactificationOf (Over.mk (ftsHomToBase f).left)}
    {E : quasiCoherentDerivedCategory S}
    (h : haveI := isNoetherian_of_isAffine_of_isNoetherianRing (S := S)
      UpperShriekCharts (ftsHomToBase f) j E)
    {ω : DerivedCategory (ModuleCat.{u} Γ(S, ⊤))}
    (hmodel : IsTildeModelOnAnyModel E.obj ⊤ (isAffineOpen_top S) ω) :
    haveI := isNoetherian_of_isAffine_of_isNoetherianRing (S := S)
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    HasTopCharts f ω ((upperShriek (ftsHomToBase f) j).obj E).obj := by
  have := isNoetherian_of_isAffine_of_isNoetherianRing (S := S)
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  intro U hU p
  obtain ⟨e⟩ := h ⊤ (isAffineOpen_top S) U hU le_top p ω hmodel
  exact ⟨Stacks.Injectives.isoOfTargetModelIso.{u} U.toScheme.Modules
    (Scheme.Modules.restrictFunctor U.ι)
    (hd₂ := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U)))
    (tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom) _ _ e⟩

/-- **Stacks Project, Tag 0AWN (Lemma 48.22.4).** Let `S` be affine with `A = Γ(S, ⊤)` a
Noetherian local ring, `ω_S^•` the complex associated to a normalized dualizing complex `ω_A^•`,
`f : X ⟶ S` proper, `ω_X^• = f^!ω_S^• = a(ω_S^•)` and `ω_X = H^{-dim X}(ω_X^•)`
([Stacks, Tag 0AWI]). Then
1. `H^i(ω_X^•) ≠ 0` implies `i ∈ {-dim X, …, 0}`;
2. the support of `H^i(ω_X^•)` has dimension at most `-i`;
3. `Supp(ω_X)` is the union of the irreducible components of dimension `dim X`;
4. `ω_X` (which is coherent) has property `(S₂)`. -/
@[stacks 0AWN]
theorem vanishing_and_support_relativeDualizingComplex
    (f : X ⟶ S) [IsProper f] (ωS : quasiCoherentDerivedCategory S)
    (ω : DerivedCategory (ModuleCat.{u} Γ(S, ⊤)))
    (hω : Dualizing.IsNormalizedDualizingComplex.{u, u} ω)
    (hmodel : IsTildeModelOnAnyModel ωS.obj ⊤ (isAffineOpen_top S) ω) :
    let L := (relativeDualizingComplex f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      ωS).obj
    (∀ i : ℤ, ¬ Limits.IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj L) →
      i ≤ 0 ∧ (((-i).toNat : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim X) ∧
    (∀ i : ℤ, topologicalKrullDim (_root_.SheafOfModules.supp
        ((DerivedCategory.homologyFunctor X.Modules i).obj L)) ≤
      if i ≤ 0 then (((-i).toNat : ℕ) : WithBot ℕ∞) else ⊥) ∧
    (relativeDualizingModule f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        ωS).IsCoherent ∧
    SheafHasPropertySk X (relativeDualizingModule f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f) ωS) 2 ∧
    _root_.SheafOfModules.supp (relativeDualizingModule f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f) ωS) =
      ⋃₀ {C ∈ irreducibleComponents X | topologicalKrullDim C = topologicalKrullDim X} := by
  have := isNoetherian_of_isAffine_of_isNoetherianRing (S := S)
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  have : IsProper (ftsHomToBase f).left := ‹IsProper f›
  have hdual : IsDualizingComplex ωS.obj := isDualizingComplex_of_isTildeModelOn_top hω.1 hmodel
  have hcharts := UpperShriekCharts.hasTopCharts f
    (upperShriekCharts (ftsHomToBase f) (properCompactification (ftsHomToBase f)) ωS
      (isBoundedBelow_of_isDualizingComplex _ hdual)) hmodel
  have hcharts' : HasTopCharts f ω (relativeDualizingComplex f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f) ωS).obj := fun U hU p =>
    isTildeModelOnAnyModel_of_iso ((ObjectProperty.ι _).mapIso
      ((upperShriekProperIso (ftsHomToBase f)).app ωS)) (hcharts U hU p)
  exact vanishing_and_support_of_hasTopCharts f hω hcharts'

end Stacks.Duality

end
