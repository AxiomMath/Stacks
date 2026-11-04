module

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Limits
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restriction to a localized site preserves limits

Let `J` be a Grothendieck topology on `C` and `V : C`. The restriction functor
`J.overPullback A V : Sheaf J A ⥤ Sheaf (J.over V) A` is, on underlying presheaves, precomposition
with `(Over.forget V).op`. Limits of sheaves are computed in presheaves, where they are computed
objectwise, so restriction preserves all limits — with no sheafification, no size condition on `A`
and no condition on the site.

Colimits are a different matter: a colimit of sheaves is the sheafification of the colimit of the
underlying presheaves, and restriction commutes with sheafification only through the right adjoint
`(Over.forget V).sheafPushforwardCocontinuous`, which exists when the pointwise right Kan
extensions along `(Over.forget V).op` do. For `A = Type w` that holds when `w` is at least
`max u v` — the objects of `Over V` live in `Type (max u v)` — and is not available for an
arbitrary carrier universe. The colimit statement below therefore carries the Kan extension
hypothesis explicitly rather than hiding it.

## Main results

* `CategoryTheory.GrothendieckTopology.preservesLimitsOfShape_overPullback` — restriction to a
  localized site preserves limits of any shape.
* `CategoryTheory.GrothendieckTopology.preservesColimits_overPullback` — restriction to a
  localized site preserves colimits, when the right Kan extensions along `(Over.forget V).op`
  exist.

## References

* [Stacks Project, Tag 00XZ](https://stacks.math.columbia.edu/tag/00XZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t t' w' w v u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (A : Type w') [Category.{w} A] (V : C)

/-- Restriction of sheaves to a localized site preserves limits of any shape: on underlying
presheaves it is precomposition with `(Over.forget V).op`, and limits of sheaves are created by
the inclusion into presheaves. -/
instance preservesLimitsOfShape_overPullback (K : Type t) [Category.{t'} K]
    [HasLimitsOfShape K A] : PreservesLimitsOfShape K (J.overPullback A V) := by
  have h : PreservesLimitsOfShape K
      (J.overPullback A V ⋙ sheafToPresheaf (J.over V) A) :=
    preservesLimitsOfShape_of_natIso
      ((Over.forget V).sheafPushforwardContinuousCompSheafToPresheafIso A (J.over V) J).symm
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf (J.over V) A)

/-- Restriction of sheaves to a localized site preserves finite limits. -/
instance preservesFiniteLimits_overPullback [HasFiniteLimits A] :
    PreservesFiniteLimits (J.overPullback A V) where
  preservesFiniteLimits _ := inferInstance

/-- Restriction of sheaves to a localized site preserves colimits whenever the pointwise right
Kan extensions along `(Over.forget V).op` exist: the restriction functor is then the left adjoint
of `(Over.forget V).sheafPushforwardCocontinuous`. -/
@[sga "4 I 5.8.3" "Clause 1, special case",
  sga "4 IV 3.1.2" "special case",
  sga "4 IV 5.2" "special case"]
lemma preservesColimits_overPullback
    [∀ F : (Over V)ᵒᵖ ⥤ A, (Over.forget V).op.HasPointwiseRightKanExtension F] :
    PreservesColimitsOfSize.{t, t'} (J.overPullback A V) :=
  ((Over.forget V).sheafAdjunctionCocontinuous A (J.over V) J).leftAdjoint_preservesColimits

/-- Restriction of sheaves to a localized site preserves finite colimits whenever the pointwise
right Kan extensions along `(Over.forget V).op` exist. -/
@[sga "4 I 5.8.3" "Clause 1", sga "4 IV 5.2" "partial"]
lemma preservesFiniteColimits_overPullback
    [∀ F : (Over V)ᵒᵖ ⥤ A, (Over.forget V).op.HasPointwiseRightKanExtension F] :
    PreservesFiniteColimits (J.overPullback A V) :=
  have := preservesColimits_overPullback.{0, 0} J A V
  PreservesColimitsOfSize.preservesFiniteColimits _

end CategoryTheory.GrothendieckTopology

end
