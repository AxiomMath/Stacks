module

public import StacksFrontier.AlgebraicGeometry.ComponentDegrees.Degree
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ContractedDegree

/-!
# Degrees on a component dominating a component of the target

Let `c : X ⟶ Y` be a morphism of proper schemes of dimension at most one over a field `k`, and
let `g : E ⟶ E₁` be a non-constant morphism from a one-dimensional reduced component of `X` to one
of `Y` lying over `c`. For an invertible `𝒪_Y`-module `L`, the degree of `c^* L` on `E` is a
positive multiple of the degree of `L` on `E₁`, namely `[R(E) : R(E₁)] · deg(L|_{E₁})`
([Stacks, Tag 0AYZ] in rank one,
`AlgebraicGeometry.invertibleCurveDegree_pullback_eq_degreeOver_mul`).

## Main results

* `exists_pos_mul_invertibleCurveDegree_reducedComponent_pullback`: the degree of `c^* L` on a
  component of `X` dominating a component of `Y` is a positive multiple of the degree of `L` on
  the latter.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ComponentDegrees

/-- **The degree on a dominating component is a positive multiple.** Let `c : X ⟶ Y` be a morphism
of proper schemes of dimension at most one over `k` and `g` a non-constant morphism of reduced
one-dimensional components lying over `c`. For every invertible `𝒪_Y`-module `L`, the degree of
`c^* L` on the component of `X` is `d` times the degree of `L` on the component of `Y`, for some
`d > 0`. -/
theorem exists_pos_mul_invertibleCurveDegree_reducedComponent_pullback (k : Type u) [Field k]
    {X Y : Scheme.{u}} (fX : X ⟶ Spec (.of k)) (fY : Y ⟶ Spec (.of k)) [IsProper fX]
    [IsProper fY] (c : X ⟶ Y) (hc : c ≫ fY = fX) (hdimX : topologicalKrullDim X ≤ 1)
    (hdimY : topologicalKrullDim Y ≤ 1) {ζ : genericPointsOne X} {ζ₁ : genericPointsOne Y}
    (g : reducedComponent X ζ ⟶ reducedComponent Y ζ₁)
    (hg : g ≫ reducedComponentι Y ζ₁ = reducedComponentι X ζ ≫ c)
    (hnc : ¬ ∃ y : reducedComponent Y ζ₁, ∀ x : reducedComponent X ζ, g.base x = y)
    (L : Y.Modules) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L] :
    ∃ d : ℤ, 0 < d ∧
      @invertibleCurveDegree k _ (reducedComponent X ζ) (reducedComponentι X ζ ≫ fX)
          (isProper_reducedComponentι_comp k fX ζ)
          (topologicalKrullDim_reducedComponent_le X hdimX ζ)
          ((Scheme.Modules.pullback (reducedComponentι X ζ)).obj
            ((Scheme.Modules.pullback c).obj L))
          (SheafOfModules.isInvertible_pullback (reducedComponentι X ζ)
            ((Scheme.Modules.pullback c).obj L)) =
        d * @invertibleCurveDegree k _ (reducedComponent Y ζ₁) (reducedComponentι Y ζ₁ ≫ fY)
          (isProper_reducedComponentι_comp k fY ζ₁)
          (topologicalKrullDim_reducedComponent_le Y hdimY ζ₁)
          ((Scheme.Modules.pullback (reducedComponentι Y ζ₁)).obj L)
          (SheafOfModules.isInvertible_pullback (reducedComponentι Y ζ₁) L) := by
  have := isCurve_reducedComponentι_comp k fX ζ
  have := isCurve_reducedComponentι_comp k fY ζ₁
  have := isProper_reducedComponentι_comp k fX ζ
  have := isProper_reducedComponentι_comp k fY ζ₁
  have := SheafOfModules.isInvertible_pullback c L
  have := SheafOfModules.isInvertible_pullback (reducedComponentι X ζ)
    ((Scheme.Modules.pullback c).obj L)
  have := SheafOfModules.isInvertible_pullback (reducedComponentι Y ζ₁) L
  have := SheafOfModules.isInvertible_pullback g
    ((Scheme.Modules.pullback (reducedComponentι Y ζ₁)).obj L)
  have hh : g ≫ reducedComponentι Y ζ₁ ≫ fY = reducedComponentι X ζ ≫ fX := by
    rw [← Category.assoc, hg, Category.assoc, hc]
  let e : (Scheme.Modules.pullback (reducedComponentι X ζ)).obj
        ((Scheme.Modules.pullback c).obj L) ≅
      (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback (reducedComponentι Y ζ₁)).obj L) :=
    (Scheme.Modules.pullbackComp (reducedComponentι X ζ) c).app L ≪≫
      (Scheme.Modules.pullbackCongr hg.symm).app L ≪≫
      ((Scheme.Modules.pullbackComp g (reducedComponentι Y ζ₁)).app L).symm
  refine ⟨_, Int.natCast_pos.mpr (degreeOver_pos_of_not_constant k _ _ g hh hnc), ?_⟩
  exact (invertibleCurveDegree_eq_of_iso k _ _ e).trans
    (invertibleCurveDegree_pullback_eq_degreeOver_mul k _ _ g hh hnc _)

end Stacks.AlgebraicGeometry.ComponentDegrees

end
