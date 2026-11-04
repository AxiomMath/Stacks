module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.FGModuleCat.EssentiallySmall
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import StacksFrontier.RingTheory.Module.FinitePresentation.Colimit

/-!
# The category of finitely presented modules

For a ring `A`, the finitely presented `A`-modules form a full subcategory of `ModuleCat A`,
cut out by `Module.FinitePresentation`. This file introduces that subcategory and records the
two facts which make it a good subcategory to extend functors from: it is essentially small,
and every `A`-module is a filtered colimit of its objects.

## Main definitions

* `ModuleCat.finitelyPresentedModule` is the property of an object of `ModuleCat A` that its
  underlying module is finitely presented.
* `ModuleCat.FinitelyPresentedModuleCat` is the corresponding full subcategory.

## Main results

* `ModuleCat.essentiallySmall_finitelyPresentedModuleCat`: the subcategory is essentially small.
* `ModuleCat.ind_finitelyPresentedModule`: every object of `ModuleCat A` is a filtered colimit of
  finitely presented modules.

## Implementation notes

The module universe is `max u v` for a ring in `Type u`, so that free modules on a type in
`Type u` belong to the category.

## References

* [Stacks Project, Tag 0GNJ](https://stacks.math.columbia.edu/tag/0GNJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace ModuleCat

variable (A : Type u) [Ring A]

/-- The property that an object of `ModuleCat A` is finitely presented. -/
public def finitelyPresentedModule : ObjectProperty (ModuleCat.{max u v} A) :=
  fun M ↦ Module.FinitePresentation A M

/-- Membership in `finitelyPresentedModule` is algebraic finite presentation. -/
@[simp]
public lemma finitelyPresentedModule_iff (M : ModuleCat.{max u v} A) :
    finitelyPresentedModule A M ↔ Module.FinitePresentation A M := Iff.rfl

/-- The category of finitely presented `A`-modules. -/
public abbrev FinitelyPresentedModuleCat :=
  (finitelyPresentedModule A).FullSubcategory

/-- The underlying module of an object of `FinitelyPresentedModuleCat` is finitely presented. -/
public instance (M : FinitelyPresentedModuleCat.{u, max u v} A) :
    Module.FinitePresentation A M.obj := M.property

/-- The category of finitely presented `A`-modules is essentially small. -/
public lemma essentiallySmall_finitelyPresentedModuleCat :
    EssentiallySmall.{max u v} (FinitelyPresentedModuleCat.{u, max u v} A) := by
  have : EssentiallySmall.{max u v} (FGModuleCat.{max u v} A) :=
    (essentiallySmall_congr (FGModuleRepr.embed A).asEquivalence).mp
      (essentiallySmall_of_small_of_locallySmall _)
  have hle : finitelyPresentedModule.{u, max u v} A ≤ ModuleCat.isFG A := fun X hX ↦
    have : Module.FinitePresentation A X := hX
    (inferInstance : Module.Finite A X)
  exact essentiallySmall_of_fully_faithful (ObjectProperty.ιOfLE hle)

/-- Every `A`-module is a filtered colimit of finitely presented `A`-modules. -/
public lemma ind_finitelyPresentedModule (X : ModuleCat.{max u v} A) :
    (finitelyPresentedModule.{u, max u v} A).ind.{max u v} X := by
  obtain ⟨ι, hpre, hdir, hnon, hdec, G, hadd, hmod, f, hsys, hfp, ⟨e⟩⟩ :=
    Module.exists_linearEquiv_directLimit_finitePresentation_max A X
  let : Preorder ι := hpre
  let : IsDirected ι (· ≤ ·) := hdir
  let : Nonempty ι := hnon
  let : DecidableEq ι := hdec
  let : (i : ι) → AddCommGroup (G i) := hadd
  let : (i : ι) → Module A (G i) := hmod
  let : DirectedSystem G (fun i j h => f i j h) := hsys
  let : IsFiltered ι := inferInstance
  let p : ColimitPresentation ι (ModuleCat.of A (Module.DirectLimit G f)) :=
    { diag := ModuleCat.directLimitDiagram G f
      ι := (ModuleCat.directLimitCocone G f).ι
      isColimit := ModuleCat.directLimitIsColimit G f }
  exact ⟨ι, inferInstance, inferInstance, p.ofIso e.symm.toModuleIso, hfp⟩

end ModuleCat
