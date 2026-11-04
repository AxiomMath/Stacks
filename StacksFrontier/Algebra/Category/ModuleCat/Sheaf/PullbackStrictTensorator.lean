module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardGradedAlgebraSections

/-!
# The tensorator of the monoidal pullback of sheaves of modules is the comparison of Tag 01CD

Let `f : X ⟶ Y` be a morphism of ringed spaces. There are two monoidal structures in the library
on the pullback `f^* : Mod(𝒪_Y) ⥤ Mod(𝒪_X)` for the monoidal structure of Tag 01CA:

* `Stacks.PullbackGradedAlgebra.pullbackStrictMonoidal`, obtained from the monoidal structure of
  the localization of presheaves of modules along sheafification, and
* `Stacks.PullbackTensorCoherence.pullbackComparisonMonoidal`, whose tensorator is the canonical
  comparison `f^*(A ⊗ B) ⟶ f^*A ⊗ f^*B` of Tag 01CD, with its section formula.

`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStrictUnit` identified the two **unit**
morphisms. The two **tensorators** were not identified, because — as the implementation note of
`pullbackCoreMonoidal` records — that amounts to computing the localization tensorator on local
sections, which was not available. It is available now:
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorSectionsSite` computes it for a
continuous functor of sites, and a morphism of ringed spaces is one. This file closes that
other half: the oplax tensorator of `pullbackStrictMonoidal` **is** the comparison of Tag 01CD,
so a statement about the multiplication of `f^*A` no longer has to say which of the two monoidal
structures it is about.

## Main results

* `Stacks.PullbackStrictTensorator.delta_pullbackStrictMonoidal_eq`: **the oplax tensorator of
  `pullbackStrictMonoidal` is the comparison of Tag 01CD.**
* `Stacks.PullbackStrictTensorator.mu_pullbackStrictMonoidal_eq`: its lax tensorator is the
  inverse of that comparison, which is the shape
  `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.app_mul` is stated at.

## Implementation notes

**The proof is the uniqueness clause of Tag 01CD.**
`Stacks.RingedSpace.comparison_unique` says that a morphism `f^*(A ⊗ B) ⟶ f^*A ⊗ f^*B` whose
adjoint transpose carries the sheafification-unit image of a pure tensor `a ⊗ b` to the pure
tensor of the two pullback-unit images is the comparison. For the oplax tensorator of
`pullbackStrictMonoidal` that is
`Stacks.PullbackTensorSectionsSite.delta_pullbackStrictMonoidal_pullSec_tmul` read at
`RingedSpaceModuleAdjunction.opensMap f`, after
`Stacks.RingedSpace.homEquiv_val_app` has moved the transpose onto the section.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD) — the comparison
  `f^*(A ⊗ B) ≅ f^*A ⊗ f^*B`.
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) — the tensor product of
  sheaves of modules.
-/

@[expose] public section

open CategoryTheory MonoidalCategory CategoryTheory.Sheaf PresheafOfModules AlgebraicGeometry
open RingedSpaceModuleAdjunction Stacks.RingedSpace Stacks.PullbackMonoidalSheaf
open TopologicalSpace
open Stacks.SheafOfModules.TensorSheafification
open Stacks.PullbackMonoidalSite Stacks.PullbackTensorSectionsSite
open Stacks.PullbackTensorCoherence

open scoped TensorProduct

universe u

namespace Stacks.PullbackStrictTensorator

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (A B : SheafOfModules.{u} (structureRingSheaf Y))

/-- **The oplax tensorator of `Stacks.PullbackGradedAlgebra.pullbackStrictMonoidal` is the
comparison of Tag 01CD.** This is the half of the identification of the two monoidal structures
on `f^*` that `Stacks.PullbackTensorCoherence.pullbackCoreMonoidal` left open; the other half,
for the unit morphisms, is `Stacks.PullbackStrictUnit.epsilon_pullbackFunctor`. -/
theorem delta_pullbackStrictMonoidal_eq :
    Functor.OplaxMonoidal.δ
        (self := (Stacks.PullbackGradedAlgebra.pullbackStrictMonoidal f).toOplaxMonoidal)
        (pullbackFunctor f) A B =
      pullbackTensorComparison f A B := by
  have := Stacks.PushforwardGradedAlgebra.isRightAdjoint_pushforward_sheafRingHom f
  refine Stacks.RingedSpace.comparison_unique f A B _ ?_
  intro U x y
  refine Eq.trans (Stacks.RingedSpace.homEquiv_val_app f _ _ _ U _) ?_
  exact delta_pullbackStrictMonoidal_pullSec_tmul (F := opensMap f)
    (O := Y.presheaf) (P := X.presheaf) f.hom.c
    (structureSheafRing Y).property (structureSheafRing X).property A B U x y

/-- **The lax tensorator of `Stacks.PullbackGradedAlgebra.pullbackStrictMonoidal` is the inverse
of the comparison of Tag 01CD.** This is the spelling the multiplicativity clause
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.app_mul` uses. -/
theorem mu_pullbackStrictMonoidal_eq :
    Functor.LaxMonoidal.μ
        (self := (Stacks.PullbackGradedAlgebra.pullbackStrictMonoidal f).toLaxMonoidal)
        (pullbackFunctor f) A B =
      inv (pullbackTensorComparison f A B) := by
  refine (IsIso.inv_eq_of_hom_inv_id ?_).symm
  refine Eq.trans (congrArg (fun z => z ≫ Functor.LaxMonoidal.μ
    (self := (Stacks.PullbackGradedAlgebra.pullbackStrictMonoidal f).toLaxMonoidal)
    (pullbackFunctor f) A B) (delta_pullbackStrictMonoidal_eq f A B).symm) ?_
  exact Functor.Monoidal.δ_μ
    (self := Stacks.PullbackGradedAlgebra.pullbackStrictMonoidal f) (pullbackFunctor f) A B

end Stacks.PullbackStrictTensorator

end
