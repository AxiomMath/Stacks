module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.RightAdjointDirectSums
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.Exactness
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.DerivedTensorDirectSums
public import
  StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonGeneral
public import StacksFrontier.CategoryTheory.Triangulated.RightAdjointCoproducts

/-!
# Further results on `RightAdjointDirectSums`

For a morphism of schemes `f : X ⟶ Y` whose derived pushforward preserves quasi-coherence, a
right adjoint `a` of the derived pushforward on quasi-coherent derived categories, and an object
`L` of the quasi-coherent derived category of `Y`, the composite `K ↦ a(K ⊗ᴸ_{𝒪_Y} L)` commutes
with direct sums, provided `X` has a compact weak generator with compact pushforward.

## Main results

* `preservesCoproducts_quasiCoherentDerivedTensorRight_comp_rightAdjoint_unconditional`:
  the functor `quasiCoherentDerivedTensorRight Y L ⋙ a` preserves coproducts of every shape
  `Discrete J`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open Stacks.Duality.DerivedPushforward

universe u

namespace Stacks.Duality

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)

/-- **The composite `K ↦ a(K ⊗ᴸ_{𝒪_Y} L)` commutes with direct sums.** If `a` is right adjoint
to the derived pushforward along `f`, and the quasi-coherent derived category of `X` has a compact
weak triangulated generator `E` whose pushforward is compact, then for every object `L` the
functor `quasiCoherentDerivedTensorRight Y L ⋙ a` preserves coproducts indexed by any
`J : Type u`. This is the form in which `isIso_compareWithPullbackTensor_of_isIso_generators`
([Stacks, Tag 0A9U]) uses [Stacks, Tag 0A9R]. It composes the commutation of `a` with direct sums,
`preservesCoproducts_rightAdjoint_of_isCompactObject_pushforward`, with the commutation of the
derived tensor product with direct sums,
`preservesColimitsOfShape_discrete_quasiCoherentDerivedTensorRight`. -/
theorem preservesCoproducts_quasiCoherentDerivedTensorRight_comp_rightAdjoint_unconditional
    {a : quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X}
    (adj : quasiCoherentDerivedPushforward f hpush ⊣ a) (L : quasiCoherentDerivedCategory Y)
    (E : quasiCoherentDerivedCategory X) (hEc : IsCompactObject.{u} E)
    (hE : (ObjectProperty.singleton E).IsWeakTriangulatedGenerator)
    (hpushE : IsCompactObject.{u} ((quasiCoherentDerivedPushforward f hpush).obj E)) :
    ∀ J : Type u, PreservesColimitsOfShape (Discrete J)
      (quasiCoherentDerivedTensorRight Y L ⋙ a) := by
  have ha := preservesCoproducts_rightAdjoint_of_isCompactObject_pushforward f hpush adj E hEc hE
    hpushE
  have htensor : ∀ J : Type u, PreservesColimitsOfShape (Discrete J)
      (quasiCoherentDerivedTensorRight Y L) :=
    fun J => preservesColimitsOfShape_discrete_quasiCoherentDerivedTensorRight Y J L
  intro J
  have := ha J
  have := htensor J
  infer_instance

end Stacks.Duality

end
