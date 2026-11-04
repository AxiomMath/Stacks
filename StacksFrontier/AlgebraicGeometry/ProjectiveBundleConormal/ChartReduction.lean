module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartConormalTarget
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.IsoLocality

/-!
# Tag 0B3V clause 3 reduced to one equation on a chart

The isomorphism assertion of [Stacks, Tag 0B3V] clause 3 is local
(`Stacks.ProjectiveBundleConormal.isIso_conormalCanonicalMap_of_forall_exists_isIso_restrict`),
and around every point of the base there is an affine open carrying the whole of the chart data
(`Stacks.ProjectiveBundleConormal.exists_affine_open_chartData`). On such a chart both the source
and the target of the clause's map have been computed, and they are the same sheaf: the source by
`Stacks.ProjectiveBundleConormal.restrictConormalSourceIsoTilde`, the target by
`Stacks.ProjectiveBundleConormal.restrictConormalTargetIsoTilde`, both landing on `(ker p)^~`.

**So all that remains of the clause is that those two computations are compatible with the map
itself**, and this file records exactly that: the clause follows from the single equation

  `(conormal map)|_W = (source identification) ≫ (target identification)⁻¹`

quantified over the chart data. No invertibility is left to prove — only this equality of
morphisms, which is what a generator computation discharges.

## Main results

* `Stacks.ProjectiveBundleConormal.isIso_conormalCanonicalMap_of_restrict_eq`: **the reduction.**

## Implementation notes

The chart data is produced by `Stacks.ProjectiveBundleConormal.exists_affine_open_chartData`
rather than by `Stacks.ProjectiveBundleConormal.exists_affine_open_chartLinearForm`, because the
source identification consumes a trivialisation of `𝓛` and the latter produces none. That cover
*pins* the trivialisation to the one the frame and the section induce,
`Stacks.ProjectiveBundleConormal.chartTrivialisation`, so the hypothesis below may assume the
relation; a cover producing an unrelated trivialisation would force the chart computation to treat
`pairing(q s, θ⁻¹ 1)` as an unknown unit.

The transport of invertibility across the hypothesis is `Eq.mp` of a `congrArg` and not a
rewrite: see the implementation notes of
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartRatio` for why no `rw` occurs on
this layer.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.ProjectiveBundleSplitting
open Stacks.SymGraded

universe u

namespace Stacks.ProjectiveBundleConormal

attribute [local instance] monoidalSheafTensor

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]
  (Q : Stacks.Divisors.InvertibleQuotient X E)
  {σ : X ⟶ (bundle E).scheme} (hσ : σ ≫ (bundle E).toBase = 𝟙 X)
  (e : (Scheme.Modules.pullback σ).obj (tautologicalTwist E (symPieces E)) ≅ Q.L)
  (hqe : (Scheme.Modules.pullbackId X).inv.app E ≫
    (Scheme.Modules.pullbackCongr hσ).inv.app E ≫
      (Scheme.Modules.pullbackComp σ (bundle E).toBase).inv.app E ≫
        (Scheme.Modules.pullback σ).map (tautologicalMap E (symPieces E)) ≫ e.hom = Q.q)
  [IsImmersion σ]

include hσ e hqe in
/-- **The isomorphism assertion of [Stacks, Tag 0B3V] clause 3 follows from one equation on a
chart.** If, over every affine open carrying a frame for `𝓛`, a section of `ℰ` at which the
chart's linear form takes the value `1`, and the trivialisation of `𝓛` **that data induces**
(`Stacks.ProjectiveBundleConormal.chartTrivialisation`), the restriction of the canonical map is
the source identification followed by the inverse of the target identification, then the canonical
map is an isomorphism.

The trivialisation is a variable carrying the equation that pins it rather than the term itself,
so that a consumer instantiates it from its own goal instead of unfolding; the cover
`Stacks.ProjectiveBundleConormal.exists_affine_open_chartData` supplies both.

Both identifications land on `(ker p)^~`, so the right-hand side is an isomorphism for formal
reasons; the content of the hypothesis is entirely that it *is* the clause's map. The passage
from the chart to `X` is
`Stacks.ProjectiveBundleConormal.isIso_conormalCanonicalMap_of_forall_exists_isIso_restrict` at
the cover `Stacks.ProjectiveBundleConormal.exists_affine_open_chartData`. -/
theorem isIso_conormalCanonicalMap_of_restrict_eq
    (h : ∀ (W : X.Opens) (hW : IsAffineOpen W) (eL : Γ(Q.L, W) ≃ₗ[Γ(X, W)] Γ(X, W))
      (s : Γ(E, W)) (hs : chartLinearForm Q W eL s = 1)
      (τ : (Scheme.Modules.restrictFunctor W.ι).obj Q.L ≅ 𝟙_ (↑W : Scheme.{u}).Modules),
      τ = chartTrivialisation Q hW eL s hs →
      (Scheme.Modules.restrictFunctor W.ι).map (conormalCanonicalMap E Q hσ e hqe) =
        (restrictConormalSourceIsoTilde Q W eL hW τ).hom ≫
          (restrictConormalTargetIsoTilde E Q hσ e hqe hW eL s hs).inv) :
    IsIso (conormalCanonicalMap E Q hσ e hqe) := by
  refine isIso_conormalCanonicalMap_of_forall_exists_isIso_restrict E Q hσ e hqe fun x => ?_
  obtain ⟨W, hxW, hW, eL, s, hs, τ, hτ⟩ := exists_affine_open_chartData Q x
  exact ⟨W, hxW,
    Eq.mp (congrArg (fun φ => IsIso φ) (h W hW eL s hs τ hτ).symm) inferInstance⟩

include hσ e hqe in
/-- **The same reduction with the source identification moved to the left**, which is the shape
the chart computation can actually attack.

`Stacks.ProjectiveBundleConormal.isIso_conormalCanonicalMap_of_restrict_eq` states the equation
between morphisms out of `(ker q ⊗ 𝓛^{⊗ -1})|_W`, a restricted tensor product, whose sections
over the chart are generated by nothing that has a name; so neither generator formula applies to
it and the equation cannot be read on a section at all. Cancelling the source identification
forwards puts both sides on `(ker p)^~` pulled back along `W ≅ Spec Γ(X, W)`, whose sections *are*
generated — by `AlgebraicGeometry.tilde.toOpen` through the unit of
`hW.isoSpec.hom^* ⊣ (hW.isoSpec.hom)_*`, which is what
`Stacks.ProjectiveBundleConormal.restrictKernelIsoTilde_inv_unit_toOpen` and
`Stacks.ProjectiveBundleConormal.conormalZeroSectionTildeIso_hom_unit_toOpen` are stated on, and
what `Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_pullbackSection` reduces an equation of
morphisms to.

It is `CategoryTheory.Iso.inv_comp_eq` and nothing else. -/
theorem isIso_conormalCanonicalMap_of_restrict_eq'
    (h : ∀ (W : X.Opens) (hW : IsAffineOpen W) (eL : Γ(Q.L, W) ≃ₗ[Γ(X, W)] Γ(X, W))
      (s : Γ(E, W)) (hs : chartLinearForm Q W eL s = 1)
      (τ : (Scheme.Modules.restrictFunctor W.ι).obj Q.L ≅ 𝟙_ (↑W : Scheme.{u}).Modules),
      τ = chartTrivialisation Q hW eL s hs →
      (restrictConormalSourceIsoTilde Q W eL hW τ).inv ≫
          (Scheme.Modules.restrictFunctor W.ι).map (conormalCanonicalMap E Q hσ e hqe) =
        (restrictConormalTargetIsoTilde E Q hσ e hqe hW eL s hs).inv) :
    IsIso (conormalCanonicalMap E Q hσ e hqe) :=
  isIso_conormalCanonicalMap_of_restrict_eq E Q hσ e hqe fun W hW eL s hs τ hτ =>
    (Iso.inv_comp_eq (restrictConormalSourceIsoTilde Q W eL hW τ)).mp (h W hW eL s hs τ hτ)

end Stacks.ProjectiveBundleConormal

end
