module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SliceExtensionExact
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Sections of injective sheaves of modules are injective

Let `Λ` be a ring, not necessarily commutative, and `I` an injective sheaf of `Λ`-modules on the
small étale site of a scheme `X`. For every object `U` of the site, the module of sections `I(U)`
is an injective `Λ`-module. Indeed taking sections over `U` is the composite of the forgetful
functor to presheaves and evaluation at `U`, which have the left adjoints sheafification and
`M ↦ (V ↦ ⊕_{V ⟶ U} M)`; both preserve monomorphisms (sheafification is exact, and a direct sum of
injective linear maps is injective), so their right adjoint preserves injective objects.

## Main results

* `Stacks.EtaleCohomology.injective_obj_obj_of_injective`

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable {Λ : Type} [Ring Λ] {X : Scheme.{u}}

/-- The left adjoint of evaluation at `U`, `M ↦ (V ↦ ⊕_{V ⟶ U} M)`, preserves monomorphisms of
modules. -/
instance evaluationLeftAdjoint_preservesMonomorphisms_moduleCat (U : X.Etaleᵒᵖ) :
    (evaluationLeftAdjoint (ModuleCat.{u + 1} Λ) U).PreservesMonomorphisms where
  preserves {M N} f hf := by
    refine @NatTrans.mono_of_mono_app _ _ _ _ _ _ _ fun T => ?_
    have h : ((evaluationLeftAdjoint (ModuleCat.{u + 1} Λ) U).map f).app T =
        Limits.Sigma.map (fun _ : U ⟶ T => f) := by
      refine Sigma.hom_ext _ _ fun g => ?_
      simp [evaluationLeftAdjoint]
    rw [h]
    exact Stacks.Sites.OverModules.mono_sigmaMap.{u, 0, u + 1} _ fun _ => hf

/-- **The sections of an injective sheaf of modules over any object are an injective module.** -/
theorem injective_obj_obj_of_injective (I : EtaleModules.{u, 0} Λ X) [Injective I]
    (U : X.Etale) : Injective (I.obj.obj (op U)) := by
  let adj := (evaluationAdjunctionRight (ModuleCat.{u + 1} Λ) (op U)).comp
    (sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  exact adj.map_injective I inferInstance

end Stacks.EtaleCohomology
