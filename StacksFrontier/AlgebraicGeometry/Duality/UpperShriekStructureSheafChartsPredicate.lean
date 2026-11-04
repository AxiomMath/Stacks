module

public import StacksFrontier.AlgebraicGeometry.Duality.DualizingBaseChange.FibreDualizing
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekChartModels

/-!
# The affine chart description of `f^!E` and of `f^!𝒪_Y`, as predicates

For a morphism `f : X ⟶ Y` of `AlgebraicGeometry.FTS S`, a compactification `j` and
`E ∈ D_QCoh(𝒪_Y)`, the predicate `Stacks.Duality.UpperShriekCharts f j E` is the affine chart
description of `f^!E` of [Stacks, Tag 0BV2]: over affine opens `U ⊆ f⁻¹(V)`, every polynomial
presentation of `Γ(Y, V) → Γ(X, U)` and every model `ω` of `E` on `V`, the restriction of `f^!E` to
`U` is the associated sheaf of the algebraic upper shriek of `ω`.

For a morphism `f : X ⟶ Y` of `AlgebraicGeometry.FTS S` and a compactification `j`, the predicate
`Stacks.Duality.UpperShriekStructureSheafCharts f j` is the affine chart description of
`f^!𝒪_Y` of [Stacks, Tag 0BV2]: over every pair of affine opens `U ⊆ f⁻¹(V)` and every polynomial
presentation of `Γ(Y, V) → Γ(X, U)`, the restriction of `f^!𝒪_Y` to `U` is the associated sheaf of
the algebraic upper shriek of `Γ(Y, V)`. It is proved in
`StacksFrontier/AlgebraicGeometry/Duality/UpperShriekStructureSheafCharts.lean` and consumed, among
others, by `StacksFrontier/AlgebraicGeometry/Duality/GorensteinMorphisms/UpperShriekCriterion.lean`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Duality

variable {S : Scheme.{u}} [AlgebraicGeometry.IsNoetherian S] {X Y : AlgebraicGeometry.FTS S}
  (f : X ⟶ Y) (j : AlgebraicGeometry.CompactificationOf (Over.mk f.left))

/-- The affine chart description of `f^!E` over every affine pair, every polynomial presentation
of the chart ring map and every model of `E`: over affine opens `U ⊆ f⁻¹(V)`, a presentation `p`
of `Γ(Y, V) → Γ(X, U)` and `ω ∈ D(Γ(Y, V))` with `E|_V ≅ ω~`, the restriction of `f^!E` to `U` is
the associated sheaf of the algebraic upper shriek `φ^!(ω) = RHom_P(Γ(X, U), ω ⊗_R P)[n]`. -/
abbrev UpperShriekCharts (E : quasiCoherentDerivedCategory Y.left) : Prop :=
  ∀ (V : Y.left.Opens) (hV : IsAffineOpen V) (U : X.left.Opens) (hU : IsAffineOpen U)
    (hUV : U ≤ f.left ⁻¹ᵁ V) (p : Dualizing.PolynomialPresentation (f.left.appLE V U hUV).hom)
    (ω : @DerivedCategory (ModuleCat.{u} Γ(Y.left, V)) _ _ (HasDerivedCategory.standard _)),
    IsTildeModelOnAnyModel E.obj V hV ω →
    Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj
        ((upperShriek f j).obj E).obj ≅
      @Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.standard _) _ _ _ _
        (tilde.functor Γ(X.left, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom) _ _ _ |>.obj
          (p.upperShriekFunctor.{u, u}.obj ω))

/-- The affine chart description of `f^!𝒪_Y` over every affine pair and every polynomial
presentation of the chart ring map: over affine opens `U ⊆ f⁻¹(V)` and a presentation `p` of
`Γ(Y, V) → Γ(X, U)`, the restriction of `f^!𝒪_Y` to `U` is the associated sheaf of the algebraic
upper shriek along `p` of `Γ(Y, V)`. -/
abbrev UpperShriekStructureSheafCharts : Prop :=
  ∀ (V : Y.left.Opens) (_ : IsAffineOpen V) (U : X.left.Opens) (hU : IsAffineOpen U)
    (hUV : U ≤ f.left ⁻¹ᵁ V) (p : Dualizing.PolynomialPresentation (f.left.appLE V U hUV).hom),
    Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj
        (relativeDualizingComplexObj f j) ≅
      @Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.standard _) _ _ _ _
        (tilde.functor Γ(X.left, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom) _ _ _ |>.obj
          (p.upperShriekFunctor.{u, u}.obj (structureModel (Y := Y) V)))

/-- The chart description of `f^!𝒪_Y` is the chart description of `f^!E` at `E = 𝒪_Y` and the
model `Γ(Y, V)` of `𝒪_Y` on `V`. -/
theorem UpperShriekCharts.upperShriekStructureSheafCharts
    (h : UpperShriekCharts f j (DerivedPushforward.derivedStructureSheaf Y.left)) :
    UpperShriekStructureSheafCharts f j := fun V hV U hU hUV p =>
  h V hV U hU hUV p _ (isTildeModelOnAnyModel_unit V hV)

end Stacks.Duality
