module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekDualizingComplex
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionTwistedInverseImage
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexCoverCriterion
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexScheme
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Dualizing
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionRightAdjointPredicateSupplement

/-!
# Further results on `UpperShriekDualizingComplex`

Results about the objects of `StacksFrontier.AlgebraicGeometry.Duality.UpperShriekDualizingComplex`
that need imports beyond those of that module.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Duality

/-- In Situation 48.16.1, let `f : X ⟶ Y` be a morphism of `FTS S` and let `f^!` be an exceptional
inverse image functor `D⁺_QCoh(𝒪_Y) ⥤ D⁺_QCoh(𝒪_X)` for it, in the sense that on affine charts it
is the algebraic upper shriek of a polynomial presentation of the chart ring map. If `K` is a
dualizing complex for `Y`, then `f^!K` is a dualizing complex for `X`. -/
theorem isDualizingComplex_upperShriek_of_fts_unconditional {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FTS S} (f : X ⟶ Y)
    (fShriek : quasiCoherentDerivedCategoryPlusAtModel Y.left ⥤
      quasiCoherentDerivedCategoryPlusAtModel X.left)
    (K : quasiCoherentDerivedCategoryPlusAtModel Y.left)
    (h0AA1 : ∀ (U : X.left.Opens) (hU : IsAffineOpen U) (V : Y.left.Opens)
      (hV : IsAffineOpen V) (hUV : U ≤ f.left ⁻¹ᵁ V)
      (ω : DerivedCategory (ModuleCat.{u} Γ(Y.left, V))),
      IsTildeModelOn K.obj.obj V hV ω →
      ∃ p : Dualizing.PolynomialPresentation (f.left.appLE V U hUV).hom,
        IsTildeModelOn (fShriek.obj K).obj.obj U hU (p.upperShriekFunctor.{u, u}.obj ω))
    (hK : IsDualizingComplex K.obj.obj) :
    IsDualizingComplex (fShriek.obj K).obj.obj := by
  refine isDualizingComplex_of_forall_exists_hasDualizingModelOn fun x => ?_
  obtain ⟨V, hV, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y.left) (x := f.left.base x) (U := ⊤) (by simp)
  obtain ⟨U, hU, hxU, hUV⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X.left) (x := x) (U := f.left ⁻¹ᵁ V) hxV
  have hVnoeth : IsNoetherianRing Γ(Y.left, V) :=
    IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have hUnoeth : IsNoetherianRing Γ(X.left, U) :=
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨ω, hω, hmodel⟩ := exists_isTildeModelOn_of_hasDualizingModelOn (hK V hV)
  obtain ⟨p, hp⟩ := h0AA1 U hU V hV hUV ω hmodel
  exact ⟨U, hU, hxU,
    hasDualizingModelOn_of_isTildeModelOn
      (Dualizing.PolynomialPresentation.upperShriekFunctor_isDualizingComplex p ω hω) hp⟩

end Stacks.Duality

end
