module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalOverTerminal
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingOverTerminal
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStructureMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.Representability
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.LimitPreservingOnObjects
public import StacksFrontier.CategoryTheory.Limits.FilteredColimitCat
public import StacksFrontier.CategoryTheory.Sites.Stack.Setoid
public import StacksFrontier.Deformation.Artin.LimitPreserving
import all StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStructureMorphism

/-!
# Supplement to `LimitPreservingStructureMorphism`

The results of this module extend those of
`StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStructureMorphism`.
They use imports, universe variables or `open` declarations that the base module does not
have, and are kept in a module of their own so that its header is unchanged.

## Main results

* `isLimitPreservingOverTerminal_of_isLimitPreserving`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u v w uC vC uX vX v2 u2

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))

/-- **A limit preserving category fibred in groupoids has limit preserving on objects structure
morphism, at a free morphism universe.** If the comparison `colim 𝒳_{Tᵢ} ⥤ 𝒳_T` is an equivalence
for every cofiltered inverse system of affine schemes over `S` with limit `T`, then every object
of `𝒳` over such a limit descends to a finite stage, which is the condition of Stacks 06CU for
`𝒳 ⟶ (Sch/S)_{fppf}`.

Neither the stack condition nor algebraicity is used: an equivalence of categories is in
particular essentially surjective, and that is all that is needed. Nor are the universes of `𝒳`:
the descent lemmas above are stated for an arbitrary fibred category, and the target of the
structure morphism contributes only the fibres of the identity functor of the site. The
conclusion is therefore `IsLimitPreservingOverTerminal`, which does not name the target as an
object of the 2-category and so leaves those universes free. -/
theorem isLimitPreservingOverTerminal_of_isLimitPreserving
    (𝒳 : CatFiberedInGroupoids.{u, v2, u + 1, u2} (BigFppfOver B S hS))
    (h𝒳 : Deformation.Artin.IsLimitPreserving.{u, v, w, u2, v2} B S hS 𝒳) :
    IsLimitPreservingOverTerminal.{u, v, w} B S hS 𝒳 := by
  have hfib : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  intro I _ _ D c hc i y x γ hγ
  have hEq : (Deformation.Artin.colimitComparison 𝒳.val.p
      (D ⋙ BigAffineFppf.inclusion B S hS)
      ((BigAffineFppf.inclusion B S hS).mapCone c)).IsEquivalence := h𝒳 I D c hc
  exact exists_descent_of_essSurj 𝒳.val.p
    (D ⋙ BigAffineFppf.inclusion B S hS)
    ((BigAffineFppf.inclusion B S hS).mapCone c) hEq.essSurj i y x γ hγ

end AlgebraicGeometry.Stack

end
