module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.DerivedLowerShriekFunctoriality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.MorphismLowerShriekAcyclic
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 08PC part (3) for abelian sheaves

Let `S` be a 1-morphism `u : C' ⥤ C` of fibred categories over a site, the standing data of
Stacks 08PA, and let `g : Sh(C') ⟶ Sh(C)` be the induced morphism of topoi.  The left derived
lower-shriek functor `Lg_!^{Ab} : D(Ab(C')) ⥤ D(Ab(C))` exists and is left adjoint to `g^{-1}` on
the unbounded derived categories, with no hypothesis beyond Situation 08PA.

Both are the conditional statements of `DerivedLowerShriekFunctoriality.lean` with their single
input, the acyclicity statement of Stacks 07AC for `g_!`, supplied by
`Stacks.Sites.FibredCategory.MorphismSituation.abelianLowerShriekAcyclic`.

## Main definitions

* `Stacks.Sites.FibredCategory.MorphismSituation.derivedAbelianLowerShriekAdjunctionUnconditional`:
  the adjunction `Lg_!^{Ab} ⊣ g^{-1}`.

## References

* [Stacks Project, Tag 08PC](https://stacks.math.columbia.edu/tag/08PC)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Stacks.Sites.FibredCategory.MorphismSituation

universe u₀ u₁ u₂ v₀ v₁ v₂ w

variable (S : MorphismSituation.{u₀, u₁, u₂, v₀, v₁, v₂, max w u₀ u₁ u₂ v₀ v₁ v₂})

attribute [local instance] HasDerivedCategory.standard

add_to_stacks 08PC "part (3), abelian sheaves: existence of Lg_!^Ab"
  hasPointwiseLeftDerivedFunctor_abelianLowerShriekOnHomotopy

/-- **Stacks 08PC part (3) for abelian sheaves, the adjunction.** The unbounded left derived
lower-shriek functor `Lg_!^{Ab} : D(Ab(C')) ⥤ D(Ab(C))` is left adjoint to `g^{-1}` on the
unbounded derived categories. This is `MorphismSituation.derivedAbelianLowerShriekAdjunction`
with its acyclicity input supplied by `abelianLowerShriekAcyclic`. -/
@[stacks 08PC "part (3), abelian sheaves: the adjunction Lg_!^Ab ⊣ g^-1"]
def derivedAbelianLowerShriekAdjunctionUnconditional :
    S.derivedAbelianLowerShriek ⊣ S.derivedAbelianInverseImage :=
  S.derivedAbelianLowerShriekAdjunction S.abelianLowerShriekAcyclic

end Stacks.Sites.FibredCategory.MorphismSituation

end
