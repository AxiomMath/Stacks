module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekRelativePerfection
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.AffineLocal

/-!
# The chart models of the relative dualizing complex of a perfect morphism

`Stacks.Duality.derivedCategoryBBounded_upperShriekFunctor_structureModel` puts the chart model
of `f^!𝒪_Y` in `D^b_Coh` of the chart ring for `f` flat of finite presentation. This file states
the same for `f` perfect: each chart ring map is then a perfect ring map, by the chart property of
[Stacks, Tag 0687] (`AlgebraicGeometry.HasRingHomProperty.appLE`), and [Stacks, Tag 0BZK] (2)
applies.

## Main results

* `Stacks.Duality.derivedCategoryBBounded_upperShriekFunctor_structureModel_of_perfect` — the
  chart model lies in `D^b_Coh` of the chart ring.

## References

* [Stacks Project, Tag 0BZK](https://stacks.math.columbia.edu/tag/0BZK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Duality

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : AlgebraicGeometry.FTS S} (f : X ⟶ Y)

/-- **The chart model of `f^!𝒪_Y` lies in `D^b_Coh` of the chart ring, `f` perfect.** For an
affine open `U ⊆ X` over an affine open `V ⊆ Y` and a polynomial presentation `p` of the chart
ring map `f.appLE V U`, the algebraic upper shriek along `p` of `Γ(Y, V)` in degree zero is
cohomologically bounded with finite cohomology modules.

Each chart ring map is a perfect ring map, by the chart property of [Stacks, Tag 0687]
(`AlgebraicGeometry.HasRingHomProperty.appLE`), and [Stacks, Tag 0BZK] (2) carries `Γ(Y, V)` in
degree zero, which lies in `D^b_Coh(Γ(Y, V))`, into `D^b_Coh(Γ(X, U))`. -/
theorem derivedCategoryBBounded_upperShriekFunctor_structureModel_of_perfect
    [Perfect f.left]
    {U : X.left.Opens} (hU : IsAffineOpen U) {V : Y.left.Opens} (hV : IsAffineOpen V)
    (hUV : U ≤ f.left ⁻¹ᵁ V)
    (p : Dualizing.PolynomialPresentation (f.left.appLE V U hUV).hom) :
    DerivedCategoryB.derivedCategoryBBounded
      (fun N : ModuleCat.{u} Γ(X.left, U) => Module.Finite Γ(X.left, U) N)
      (p.upperShriekFunctor.{u, u}.obj (structureModel (Y := Y) V)) := by
  have hn (Z : AlgebraicGeometry.FTS S) : IsLocallyNoetherian Z.left := by
    have : IsLocallyNoetherian ((Functor.fromPUnit S).obj Z.right) :=
      inferInstanceAs (IsLocallyNoetherian S)
    exact LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have hYn := hn Y
  have hXn := hn X
  have hVn : IsNoetherianRing Γ(Y.left, V) :=
    IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have hUn : IsNoetherianRing Γ(X.left, U) :=
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  exact Dualizing.upperShriekFunctor_derivedCategoryBBounded_of_perfect.{u, u} p
    (HasRingHomProperty.appLE @Perfect f.left ‹_› ⟨V, hV⟩ ⟨U, hU⟩ hUV)
    (derivedCategoryBBounded_structureModel (Y := Y) V)

end Stacks.Duality

end
