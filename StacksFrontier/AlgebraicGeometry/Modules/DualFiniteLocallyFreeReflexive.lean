module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleBaseChange
public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.ReflexiveStalk.Basic
public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree

/-!
# A finite locally free module is reflexive

Let `X` be a scheme and `ℰ` a finite locally free `𝒪_X`-module. Then the canonical map
`ℰ ⟶ ℰ^∨∨` is an isomorphism.

Both `ℰ` and `ℰ^∨` are of finite presentation, so by the stalkwise criterion of Tag 0AY3,
`Stacks.AlgebraicGeometry.ReflexiveModules.isReflexive_of_forall_modStalk`, it suffices that
every stalk `ℰ_x` is a reflexive `𝒪_{X,x}`-module; and `ℰ_x` is finite free.

## Main results

* `Stacks.AlgebraicGeometry.ReflexiveModules.isReflexive_of_isFiniteLocallyFree` — a finite
  locally free module is reflexive.
* `Stacks.AlgebraicGeometry.ReflexiveModules.isIso_toDoubleDual_of_isFiniteLocallyFree` — the same,
  as an instance-ready statement about `toDoubleDual`.

## References

* [Stacks Project, Tag 0AY3](https://stacks.math.columbia.edu/tag/0AY3)
* [Stacks Project, Tag 01CP](https://stacks.math.columbia.edu/tag/01CP)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.SheafOfModules.SheafHomStalk

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

/-- **A finite locally free module on a scheme is reflexive**: the canonical map `ℰ ⟶ ℰ^∨∨` is an
isomorphism. -/
theorem isReflexive_of_isFiniteLocallyFree {X : Scheme.{u}} (E : X.Modules)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E] :
    IsReflexive E := by
  have : E.IsFinitePresentation := Stacks.Chow.isFinitePresentation_of_isFiniteLocallyFree E hE
  have : (dualSheaf E).IsFinitePresentation :=
    Stacks.Chow.isFinitePresentation_of_isFiniteLocallyFree _ (isFiniteLocallyFree_dualSheaf E hE)
  refine isReflexive_of_forall_modStalk E fun x => ?_
  obtain ⟨h1, h2⟩ := Stacks.StalkFreeBridge.freeAndFinite_stalk_of_isFiniteLocallyFree E x
  have h1' : Module.Free (ringStalk X.sheaf x) (modStalk E x) := h1
  have h2' : Module.Finite (ringStalk X.sheaf x) (modStalk E x) := h2
  infer_instance

/-- The canonical map `ℰ ⟶ ℰ^∨∨` of a finite locally free module is an isomorphism. -/
theorem isIso_toDoubleDual_of_isFiniteLocallyFree {X : Scheme.{u}} (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E] :
    IsIso (toDoubleDual E) :=
  isReflexive_of_isFiniteLocallyFree E

end Stacks.AlgebraicGeometry.ReflexiveModules
