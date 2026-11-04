module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceDerivedCategory
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDefinition

/-!
# The cohomology of `RΓ(U, K)` over an affine chart, for `K` in `D_QCoh`

Let `X` be an algebraic space, `K` an object of `D_QCoh(𝒪_X)` and `U` an affine étale chart of
`X`. The quasi-coherent cohomology sheaves `Hᵐ(K)` have no higher cohomology on the affine charts
([Stacks, Tag 03P2] on charts), so the edge map `Hᵠ(RΓ(U, K)) ⟶ Γ(U, Hᵠ(K))` is an isomorphism
([Stacks, Tag 0BKZ]). This is the dictionary between the ring statements about `RΓ(U, K)` in the
proof of [Stacks, Tag 0CX9] and the cohomology sheaves of `K`.

## Main results

* `AlgebraicGeometry.Space.isIso_hypercohomologyEdge_app_of_isAffineChart`.
* `AlgebraicGeometry.Space.chartDerivedSectionsHomologyIso`: the isomorphism of
  `𝒪_X(U)`-modules `Hᵠ(RΓ(U, K)) ≅ Γ(U, Hᵠ(K))`, natural in `K` through `hypercohomologyEdge`.

## References

* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
* [Stacks Project, Tag 0CX9](https://stacks.math.columbia.edu/tag/0CX9)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] enoughInjectives_modules_ringUniverse
  isGrothendieckAbelian_modules_ringUniverse
attribute [local instance] hasRightDerivedFunctor_chartSections

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **[Stacks, Tag 0BKZ] on an affine chart, for `D_QCoh`.** For `K` with quasi-coherent
cohomology sheaves and an affine étale chart `U`, the edge map
`Hᵠ(RΓ(U, K)) ⟶ Γ(U, Hᵠ(K))` is an isomorphism. -/
theorem isIso_hypercohomologyEdge_app_of_isAffineChart (K : spaceDerivedCategory B S hS X)
    (hK : spaceQuasicoherentProp B S hS X K) (U : SmallEtale B S hS X.1)
    (hU : IsAffineChart B S hS X.1 U) (q : ℤ) :
    IsIso ((Stacks.Cohomology.HypercohomologyEdge.hypercohomologyEdge
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) U q).app
        K) := by
  have := smallEtaleRingedSite_hasSheafify B S hS X.1 X.2
  refine Stacks.Cohomology.HypercohomologyEdge.isIso_hypercohomologyEdge_app_of_acyclic_cover.{
      u + 1, u, u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) U K
    (IsAffineChart B S hS X.1) (hasEnoughObjects_isAffineChart B S hS X.1)
    (fun V hV p hp m => ?_) hU q
  exact isZero_rightDerived_evaluation_of_isAffineChart B S hS X.1 X.2 _ (hK m) V hV p hp

/-- **`Hᵠ(RΓ(U, K)) ≅ Γ(U, Hᵠ(K))`** for `K` in `D_QCoh(𝒪_X)` and `U` an affine chart, as
`𝒪_X(U)`-modules: the inverse of the edge map. -/
def chartDerivedSectionsHomologyIso (K : spaceDerivedCategory B S hS X)
    (hK : spaceQuasicoherentProp B S hS X K) (U : SmallEtale B S hS X.1)
    (hU : IsAffineChart B S hS X.1 U) (q : ℤ) :
    ((spaceDerivedHomology B S hS X q).obj K).val.obj (op U) ≅
      (DerivedCategory.homologyFunctor _ q).obj
        ((Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) U).obj
          K) :=
  haveI := isIso_hypercohomologyEdge_app_of_isAffineChart B S hS X K hK U hU q
  (asIso ((Stacks.Cohomology.HypercohomologyEdge.hypercohomologyEdge
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) U q).app
        K)).symm

end AlgebraicGeometry.Space

end
