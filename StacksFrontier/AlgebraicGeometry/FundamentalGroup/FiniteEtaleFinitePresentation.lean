module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProper
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint

/-!
# A finite étale cover is of finite presentation

A finite étale morphism is of finite presentation: it is quasi-compact and quasi-separated
because it is finite, and locally of finite presentation because it is étale.

## Main results

* `AlgebraicGeometry.finitePresentation_of_finiteEtale`: the structure morphism of an object of
  `FÉt_T` is of finite presentation.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The structure morphism of a scheme finite étale over `T` is of finite presentation. -/
theorem finitePresentation_of_finiteEtale
    {T : Scheme.{u}} (V : FiniteEtaleOver T) : FinitePresentation V.hom := by
  have := V.prop.1
  have := V.prop.2
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end AlgebraicGeometry

end
