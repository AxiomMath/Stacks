module

public import StacksFrontier.AlgebraicGeometry.Reflexive.DoubleDual
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.FlatModuleSheavesAndStalks

/-!
# A monomorphism into the double dual forces torsion freeness

This file proves the *forward* implication of the second assertion of
[Stacks, Tag 0AY2](https://stacks.math.columbia.edu/tag/0AY2): if the canonical map
`j : F ⟶ F^∨∨` of an `𝒪_X`-module on an integral scheme is a monomorphism, then `F` is torsion
free.  The converse implication is the substantive half of that assertion and is not proved
here.

The only missing link was the passage from the categorical predicate `Mono` in the category
`X.Modules` of sheaves of modules to injectivity of the map on sections over each open; the
existing `isTorsionFree_of_injective_toDual` takes the latter.  That passage is
`injective_app_of_mono`, and it is assembled from `OXModule.mono_val_of_mono`, which is the
transport of `Mono` along the forgetful functors to presheaves of abelian groups.

## Main results

* `injective_app_of_mono`: a monomorphism of `𝒪_X`-modules is injective on sections over every
  open.  Stated for an arbitrary scheme; no hypothesis on `X` is used.
* `isTorsionFree_of_mono_toDoubleDual`: on an integral scheme, a module whose canonical map to
  its double dual is a monomorphism is torsion free.
* `isTorsionFree_of_mono_toDoubleDual_of_isLocallyNoetherian`: the same statement carrying the
  local Noetherianity and coherence hypotheses under which the Stacks Project states it, neither
  of which is used.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a `def`, not an `abbrev`, so `Mono φ` for `φ` a morphism
of `X.Modules` does not let instance search see the corresponding `Mono` in
`SheafOfModules X.ringCatSheaf`; `Mono ((SheafOfModules.forget X.ringCatSheaf).map φ)` fails to
synthesize.  `OXModule.mono_val_of_mono` already performs the transport over a ringed space, and
applying it with `@` lets the elaborator unfold `X.Modules` by unification.  That is the route
taken here, exactly as in `AlgebraicGeometry.stalk_map_injective_of_mono`.

Monomorphy is not an equivalent of injectivity on sections in general sheaf categories, but it is
here, and both directions are available: `PresheafOfModules.mono_of_injective` gives the converse
for the underlying presheaf of modules.

## References

* [Stacks Project, Tag 0AY2](https://stacks.math.columbia.edu/tag/0AY2)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

variable {X : Scheme.{u}}

/-- **A monomorphism of `𝒪_X`-modules is injective on sections.**  The categorical predicate
`Mono` in `X.Modules` is detected on the sections over each open. -/
public theorem injective_app_of_mono {M N : X.Modules} (φ : M ⟶ N) [Mono φ] (U : X.Opens) :
    Function.Injective (Scheme.Modules.Hom.app φ U) := by
  have hmono : Mono φ := inferInstance
  have hval : Mono ((PresheafOfModules.toPresheaf _).map φ.val) :=
    @OXModule.mono_val_of_mono _ M N φ hmono
  have hU : Mono (((PresheafOfModules.toPresheaf _).map φ.val).app (op U)) :=
    (NatTrans.mono_iff_mono_app _).1 hval (op U)
  exact (ConcreteCategory.mono_iff_injective_of_preservesPullback
    (((PresheafOfModules.toPresheaf _).map φ.val).app (op U))).1 hU

/-- **Stacks, Tag 0AY2 (2), forward implication.**  On an integral scheme, a module whose
canonical map to its double dual is a monomorphism is torsion free. -/
public theorem isTorsionFree_of_mono_toDoubleDual [IsIntegral X] (F : X.Modules)
    [Mono (toDoubleDual F)] : IsTorsionFree F :=
  isTorsionFree_of_injective_toDual (toDoubleDual F) (injective_app_of_mono (toDoubleDual F))

/-- **Stacks, Tag 0AY2 (2), forward implication**, in the form in which the Stacks Project
states it: on an integral locally Noetherian scheme, a coherent module whose canonical map to
its double dual is a monomorphism is torsion free.  Neither local Noetherianity nor coherence
is used. -/
public theorem isTorsionFree_of_mono_toDoubleDual_of_isLocallyNoetherian [IsIntegral X]
    [IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent] [Mono (toDoubleDual F)] :
    IsTorsionFree F :=
  isTorsionFree_of_mono_toDoubleDual F

end Stacks.AlgebraicGeometry.ReflexiveModules

end
