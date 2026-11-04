module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekBounded
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekFibreDimension
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekStructureSheafCharts
public import StacksFrontier.AlgebraicGeometry.Flatness.FiniteOverSmooth
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FibreDimensionBound

/-!
# Fibre-dimension bound for the upper shriek at an affine chart

For a morphism `f : X ⟶ Y` of schemes of finite type over a Noetherian scheme, and an affine
chart on which `f^!𝒪_Y` is the associated sheaf of an algebraic upper shriek, the stalk at `x`
of the cohomology `H^i(f^!𝒪_Y)` vanishes for `i < -dim_x(X_{f(x)})`.

## Main results

* `neg_fibreDim_le_of_nontrivial_stalk_homology_upperShriek_of_chart`: if `H^i(f^!𝒪_Y)_x ≠ 0`
  at a point `x` of such a chart, then `-dim_x(X_{f(x)}) ≤ i`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

attribute [local instance 5000] HasDerivedCategory.standard
attribute [local instance 10000] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

universe u w

namespace Stacks.Duality

open DerivedPushforward

/-! ### Nontriviality transports along isomorphisms of abelian groups -/

/-! ### The stalk of an associated sheaf is a localization -/

section TildeStalk

variable {R : CommRingCat.{u}}

end TildeStalk

/-! ### The stalk of the cohomology of a tilde model -/

section StalkModel

variable {X : Scheme.{u}} [HasDerivedCategory.{w} X.Modules]

end StalkModel

/-! ### Tag 0BV5 -/

section Shriek

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : AlgebraicGeometry.FTS S} (f : X ⟶ Y)
  (j : AlgebraicGeometry.CompactificationOf (Over.mk f.left))

/-- **The bound of [Stacks, Tag 0BV5] at a chart.** If on an affine open `U ∋ x` inside the
preimage of an affine open `V` the restriction of `f^!𝒪_Y` is the associated sheaf of the
algebraic upper shriek of `Γ(Y, V)` along a presentation of `f.appLE V U`, then
`H^i(f^!𝒪_Y)_x ≠ 0 ⟹ -dim_x(X_y) ≤ i`: this is [Stacks, Tag 0E9P] moved to the chart by the
stalk dictionary and the fibre-dimension dictionary. -/
theorem neg_fibreDim_le_of_nontrivial_stalk_homology_upperShriek_of_chart (x : X.left)
    (hchart : ∃ (U : X.left.Opens) (hU : IsAffineOpen U) (V : Y.left.Opens)
      (_hV : IsAffineOpen V) (hUV : U ≤ f.left ⁻¹ᵁ V), x ∈ U ∧
      ∃ p : Dualizing.PolynomialPresentation (f.left.appLE V U hUV).hom,
        Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj
            (((upperShriek f j).obj (derivedStructureSheaf Y.left)).obj) ≅
          (tilde.functor Γ(X.left, U) ⋙
            Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj
              (p.upperShriekFunctor.{u, u}.obj (structureModel (Y := Y) V))))
    (d : ℕ)
    (hd : topologicalKrullDimAt (f.left.fiber (f.left x)) (f.left.asFiber x) =
      (d : WithBot ℕ∞))
    (i : ℤ)
    (hi : Nontrivial (((DerivedCategory.homologyFunctor X.left.Modules i).obj
      (((upperShriek f j).obj
        (derivedStructureSheaf Y.left)).obj)).presheaf.stalk x)) :
    -(d : ℤ) ≤ i := by
  obtain ⟨U, hU, V, hV, hUV, hxU, p, he⟩ := hchart
  have hlocNoeth (Z : AlgebraicGeometry.FTS S) : IsLocallyNoetherian Z.left := by
    have : IsLocallyNoetherian ((Functor.fromPUnit S).obj Z.right) :=
      inferInstanceAs (IsLocallyNoetherian S)
    exact LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have hYn := hlocNoeth Y
  have hXn := hlocNoeth X
  have hVn : IsNoetherianRing Γ(Y.left, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have hUn : IsNoetherianRing Γ(X.left, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let _ : Algebra Γ(Y.left, V) Γ(X.left, U) := (f.left.appLE V U hUV).hom.toAlgebra
  let q : PrimeSpectrum Γ(X.left, U) := hU.primeIdealOf ⟨x, hxU⟩
  have hdq : Algebra.relativeDimensionAt Γ(Y.left, V) q.asIdeal = (d : WithBot ℕ∞) :=
    (Stacks.Flatness.topologicalKrullDimAt_fiber_eq_relativeDimensionAt
      f.left ⟨V, hV⟩ ⟨U, hU⟩ hUV x hxU).symm.trans hd
  have hloc := (nontrivial_stalk_homology_iff_nontrivial_localizedHomology hU he.some
    (⟨x, hxU⟩ : U.toScheme) q rfl i).mp hi
  -- Tag 0E9P on the chart.
  exact Dualizing.upperShriekFunctor_neg_relativeDimensionAt_le_of_nontrivial_localizedHomology
    p q d hdq i hloc

end Shriek

end Stacks.Duality

end
