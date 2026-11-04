module

public import Mathlib.Algebra.Category.Grp.Injective
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Sites.Continuous
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleCohomologyFilteredColimitsTypeU
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftInjective

/-!
# The universe lift of injective abelian sheaves on a small site

**On a small site no separator is needed.** There an injective sheaf is injective as a presheaf,
an injective presheaf is a retract of a product of cofree diagrams `t ↦ ∏_{t ⟶ c} I`, and both
products and cofree diagrams are preserved by a limit-preserving functor which preserves
injective objects, as the universe lift of abelian groups does. The products are indexed by the
objects of the site, which is why the site has to be small; a site which is only essentially
small, or which has an essentially small dense subsite, is reached by restricting sheaves along a
functor of sites whose restriction is an equivalence in both coefficient universes. The universe
lift commutes with that restriction on the nose, both being composition of functors.

The declarations extend
`StacksFrontier.CategoryTheory.Sites.UniverseLiftInjective` and are placed in a new module.
The statements `preservesInjectiveObjects_whiskeringRight` and
`preservesInjectiveObjects_sheafCompose` are not restated, since they are
`Stacks.Cohomology.CoefficientLowering.whiskeringRight_preservesInjectiveObjects` and
`Stacks.Cohomology.CoefficientLowering.sheafCompose_preservesInjectiveObjects`, which are used
instead.

## Main results

* `Stacks.Sheaves.UniverseLift.preservesInjectiveObjects_addCommGrpCat_uliftFunctor`
* `Stacks.Sheaves.UniverseLift.preservesInjectiveObjects_uliftSheafFunctor_of_isEquivalence`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open ZeroObject

universe z s t v u

namespace Stacks.Sheaves.UniverseLift

section SmallSite

/-- **Universe lifting of abelian groups preserves injective objects**: an abelian group is
injective exactly when it is injective as a `ℤ`-module, and the universe lift of modules
preserves injective modules. -/
theorem preservesInjectiveObjects_addCommGrpCat_uliftFunctor :
    AddCommGrpCat.uliftFunctor.{s, t}.PreservesInjectiveObjects where
  injective_obj {M} hM := by
    apply (AddCommGrpCat.injective_as_module_iff _).mp
    have := (AddCommGrpCat.injective_as_module_iff M).mpr hM
    exact (ModuleCat.uliftFunctor.{s, t} ℤ).injective_obj (ModuleCat.of ℤ M)

end SmallSite

section DenseSubsite

/-- **The universe lift preserves injective sheaves on `C` as soon as it does on `C₀`**, for a
continuous functor of sites `G : C₀ ⥤ C` whose restriction of abelian sheaves is an equivalence
in both coefficient universes.

The universe lift commutes with restriction along `G` on the nose, both being composition of
functors, and an equivalence both preserves and reflects injective objects. -/
theorem preservesInjectiveObjects_uliftSheafFunctor_of_isEquivalence.{s₁, t₁, z₁, v₁, z₂, v₂}
    {C₀ : Type z₁} [Category.{v₁} C₀] {D : Type z₂} [Category.{v₂} D] (G : C₀ ⥤ D)
    (J₀ : GrothendieckTopology C₀) (K : GrothendieckTopology D) [G.IsContinuous J₀ K]
    [(G.sheafPushforwardContinuous AddCommGrpCat.{t₁} J₀ K).IsEquivalence]
    [(G.sheafPushforwardContinuous AddCommGrpCat.{max t₁ s₁} J₀ K).IsEquivalence]
    (h : (uliftSheafFunctor.{s₁, t₁} J₀).PreservesInjectiveObjects) :
    (uliftSheafFunctor.{s₁, t₁} K).PreservesInjectiveObjects where
  injective_obj {I} hI := by
    let E := (G.sheafPushforwardContinuous AddCommGrpCat.{t₁} J₀ K).asEquivalence
    let E' := (G.sheafPushforwardContinuous AddCommGrpCat.{max t₁ s₁} J₀ K).asEquivalence
    have h₁ : Injective ((uliftSheafFunctor.{s₁, t₁} J₀).obj (E.functor.obj I)) :=
      (uliftSheafFunctor.{s₁, t₁} J₀).injective_obj_of_injective ((E.map_injective_iff I).2 hI)
    exact (E'.map_injective_iff ((uliftSheafFunctor.{s₁, t₁} K).obj I)).1 h₁

end DenseSubsite

end Stacks.Sheaves.UniverseLift

end
