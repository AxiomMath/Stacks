module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPushforward
public import StacksCore.Tactic.StacksAttribute

/-!
# The pullback of sheaves of differential graded modules preserves colimits

Let `f : (C, J, R) ⟶ (C', J', R')` be a morphism of ringed sites, presented as a continuous
functor `u : C' ⥤ C` in the direction opposite to `f` together with the structure map `σ` of its
sheaves of rings, let `A` and `A'` be sheaves of differential graded algebras on the source and
on the target, and let `φ : A' ⟶ f_*A` be a homomorphism of sheaves of differential graded
algebras. The pullback `f^* : Mod^dg(A', d) ⥤ Mod^dg(A, d)`, carried by a `PullbackData` for
`φ`, **preserves all colimits**.

This is not a further condition on the pullback: it is a consequence of the adjunction
`f^* ⊣ f_*` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedPushforward.lean`, which every
pullback datum along a morphism of ringed *sites* has, the direct image along such a morphism
being constructed there. A left adjoint preserves colimits.

## Main results

* `SheafOfModules.DifferentialGradedModule.PullbackData.preservesColimitsOfSize_functor`: **the
  pullback functor of a pullback datum along a morphism of ringed sites preserves colimits of
  every shape**, because it is a left adjoint.
* `SheafOfModules.DifferentialGradedModule.PullbackData.preservesColimitsOfShape_functor` and
  `SheafOfModules.DifferentialGradedModule.PullbackData.isColimit_functor_mapCocone`: the same
  statement for one shape, and in the form a consumer uses it — the image of a colimit cocone of
  right differential graded modules is again a colimit cocone.

## Implementation notes

The right adjoint is the direct image, which needs the functor `u` of the morphism of ringed
sites to be continuous: that is what makes `u.op ⋙ -` carry sheaves to sheaves. Continuity does
not tie the universes of the two sites together. `CategoryTheory.Functor.IsContinuous` tests
sheaves valued in the single universe assembled from the four universes of the two sites, so it
is a condition on `u` for sites whose universes are otherwise unrelated, and the statements below
keep them so, as the neighbouring differential graded files do.

The two module universes are nevertheless one and the same `m`: the direct image of a right
differential graded `A`-module whose sections live in `m` has sections in `m` again, since the
sections of `f_*M` over `V` are those of `M` over `u V`, so the adjunction relates two categories
of modules with the same section universe.

## References

* [Stacks Project, Tag 0FSD](https://stacks.math.columbia.edu/tag/0FSD)
* [Stacks Project, Tag 0FRU](https://stacks.math.columbia.edu/tag/0FRU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w w' t a m v u a' v' u'

namespace SheafOfModules

namespace DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t}}
  {u : C' ⥤ C} [u.IsContinuous J' J] {σ : R'.obj ⟶ u.op ⋙ R.obj}
  {A : DifferentialGradedAlgebra.{t, a} R} {A' : DifferentialGradedAlgebra.{t, a'} R'}
  {φ : DifferentialGradedAlgebra.SemilinearHom u σ A' A}

namespace PullbackData

variable (P : PullbackData.{t, a, m, v, u, a', m, v', u'} φ)

/-- **The pullback of sheaves of differential graded modules along a morphism of ringed sites
preserves colimits of every shape.** The pullback is a left adjoint, the direct image along the
morphism being its right adjoint, and a left adjoint preserves colimits. -/
@[stacks 0FSD "colimits commute with pullback: the pullback along a morphism of ringed sites \
preserves every colimit, being the left adjoint of the direct image"]
theorem preservesColimitsOfSize_functor : PreservesColimitsOfSize.{w, w'} P.functor :=
  (pullbackPushforwardAdjunction P).leftAdjoint_preservesColimits

/-- The pullback along a morphism of ringed sites preserves the colimits of one shape. -/
theorem preservesColimitsOfShape_functor (D : Type w') [Category.{w} D] :
    PreservesColimitsOfShape D P.functor :=
  (preservesColimitsOfSize_functor P).preservesColimitsOfShape

/-- **The pullback along a morphism of ringed sites carries a colimit cocone of right
differential graded modules to a colimit cocone.** -/
noncomputable def isColimit_functor_mapCocone {D : Type w'} [Category.{w} D]
    {K : D ⥤ DifferentialGradedModule.{t, a', m} A'} {c : Cocone K} (hc : IsColimit c) :
    IsColimit (P.functor.mapCocone c) :=
  have := preservesColimitsOfShape_functor P D
  isColimitOfPreserves P.functor hc

end PullbackData

end DifferentialGradedModule

end SheafOfModules
