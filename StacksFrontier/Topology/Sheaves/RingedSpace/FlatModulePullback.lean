module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetPullbackLeftExact

/-!
# Flat pullback of sheaves of modules is exact

Let `f : X ⟶ Y` be a morphism of ringed spaces which is flat, that is, flat at every point of
`X` in the sense of `AlgebraicGeometry.IsFlat`: the germ map `𝒪_{Y,f(x)} ⟶ 𝒪_{X,x}` makes
`𝒪_{X,x}` a flat `𝒪_{Y,f(x)}`-module.  This file proves that the inverse image functor
`f^* : SheafOfModules 𝒪_Y ⥤ SheafOfModules 𝒪_X` is then exact.

Right exactness is unconditional, since `f^*` is a left adjoint
(`RingedSpaceModuleAdjunction.preservesColimits_modulePullback`).  The content is left
exactness, and it is obtained stalkwise.  By Stacks 0098, in the form
`Stacks.RingedSpace.stalkModulePullbackFunctorIso`, the stalk at `x` of `f^* A` is
`𝒪_{X,x} ⊗_{𝒪_{Y,f(x)}} A_{f(x)}`, so `f^*` followed by the stalk at `x` factors as an exact
stalk functor followed by base change along the germ map.  Flatness of the germ map makes that
base change exact, monomorphisms of sheaves of modules are detected on stalks, and a left exact
left adjoint preserves finite limits.

This is the input that `Mathlib/Algebra/Category/ModuleCat/Descent.lean` supplies for the ring
level: `ModuleCat.preservesFiniteLimits_extendScalars_of_flat`.

## Main results

* `Stacks.RingedSpace.flat_stalkRingMap_iff`: the `RingCat`-valued germ map `stalkRingMap f x`
  is flat if and only if the `CommRingCat`-valued stalk map `f.hom.stalkMap x` is, so flatness
  can be transferred between the two spellings of the germ map.
* `Stacks.RingedSpace.preservesFiniteLimits_stalkBaseChange_of_isFlatAt`: base change along a
  flat germ map is exact.
* `RingedSpaceModuleAdjunction.preservesMonomorphisms_modulePullback_of_isFlat`: `f^*`
  preserves monomorphisms when `f` is flat.
* `RingedSpaceModuleAdjunction.preservesFiniteLimits_modulePullback_of_isFlat`: `f^*` is left
  exact when `f` is flat.
* `RingedSpaceModuleAdjunction.preservesHomology_modulePullback_of_isFlat`: `f^*` preserves
  homology when `f` is flat.

## Implementation notes

The two spellings of the germ map are genuinely different terms.  `AlgebraicGeometry.IsFlat` is
stated for `f.hom.stalkMap x`, the stalk map of the underlying morphism of presheafed spaces,
whose stalks are `CommRingCat`-valued; `stalkBaseChange` is extension of scalars along
`stalkRingMap f x`, whose stalks are the `RingCat`-valued ones that `SheafOfModules` is stated
for.  `Stacks.RingedSpace.stalkRingMap_comp_ringStalkCommIso` identifies the two up to the
isomorphisms `ringStalkCommIso`, and since flatness of a ring homomorphism is unchanged by
composing with bijections on either side
(`RingHom.Flat.comp_iff_of_bijective_left` and `RingHom.Flat.comp_iff_of_bijective_right`),
`flat_stalkRingMap_iff` transfers it.

## References

* [Stacks Project, Tag 02N3](https://stacks.math.columbia.edu/tag/02N3)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.SheafOfModules RingedSpaceModuleAdjunction

universe u

namespace Stacks.RingedSpace

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y) (x : X.carrier)

/-- **The two germ maps have the same flatness.** `stalkRingMap f x` and the `CommRingCat`-valued
stalk map `f.hom.stalkMap x` differ by the isomorphisms `ringStalkCommIso` on either side
(`stalkRingMap_comp_ringStalkCommIso`), and flatness of a ring homomorphism is insensitive to
composing with bijections. -/
theorem flat_stalkRingMap_iff :
    letI := structureStalkCommRing Y (f.hom.base x)
    letI := structureStalkCommRing X x
    (stalkRingMap f x).hom.Flat ↔ (f.hom.stalkMap x).hom.Flat := by
  let := structureStalkCommRing Y (f.hom.base x)
  let := structureStalkCommRing X x
  let : CommRing ((forget₂ CommRingCat.{u} RingCat.{u}).obj (X.presheaf.stalk x)) :=
    inferInstanceAs (CommRing (X.presheaf.stalk x))
  let : CommRing ((forget₂ CommRingCat.{u} RingCat.{u}).obj
      (Y.presheaf.stalk (f.hom.base x))) :=
    inferInstanceAs (CommRing (Y.presheaf.stalk (f.hom.base x)))
  have key : ((ringStalkCommIso X x).hom.hom).comp (stalkRingMap f x).hom =
      ((f.hom.stalkMap x).hom).comp (ringStalkCommIso Y (f.hom.base x)).hom.hom :=
    congrArg RingCat.Hom.hom (stalkRingMap_comp_ringStalkCommIso f x)
  exact (RingHom.Flat.comp_iff_of_bijective_left
      (ConcreteCategory.bijective_of_isIso (ringStalkCommIso X x).hom)).symm.trans
    ((Eq.to_iff (congrArg RingHom.Flat key)).trans
      (RingHom.Flat.comp_iff_of_bijective_right
        (ConcreteCategory.bijective_of_isIso (ringStalkCommIso Y (f.hom.base x)).hom)))

/-- **Base change along a flat germ map is exact.** `stalkBaseChange f x` is
`ModuleCat.extendScalars` of the germ map, and extension of scalars along a flat ring
homomorphism preserves finite limits. -/
theorem preservesFiniteLimits_stalkBaseChange_of_isFlatAt
    (h : AlgebraicGeometry.IsFlatAt f x) :
    PreservesFiniteLimits (stalkBaseChange f x) := by
  let := structureStalkCommRing Y (f.hom.base x)
  let := structureStalkCommRing X x
  exact ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    ((flat_stalkRingMap_iff f x).mpr h)

end Stacks.RingedSpace

namespace RingedSpaceModuleAdjunction

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **Module pullback along a flat morphism preserves monomorphisms.** Monomorphisms of sheaves
of modules are detected on stalks, and on stalks `f^*` is the stalk at `f x` followed by base
change along the germ map (Stacks 0098) — the first factor exact, the second exact by
flatness. -/
theorem preservesMonomorphisms_modulePullback_of_isFlat
    (h : AlgebraicGeometry.IsFlat f) :
    (modulePullback f).PreservesMonomorphisms := by
  refine ⟨fun {A B} g _ => mono_of_stalk_mono _ _ fun x => ?_⟩
  have := Stacks.RingedSpace.preservesFiniteLimits_stalkBaseChange_of_isFlatAt f x (h x)
  have : (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Y)
      (f.hom.base x)).PreservesMonomorphisms :=
    Functor.preservesMonomorphisms_of_preservesFiniteLimits _
  have : (Stacks.RingedSpace.stalkBaseChange f x).PreservesMonomorphisms :=
    Functor.preservesMonomorphisms_of_preservesFiniteLimits _
  have : (modulePullback f ⋙
      AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing X)
        x).PreservesMonomorphisms :=
    Functor.PreservesMonomorphisms.of_iso
      (Stacks.RingedSpace.stalkModulePullbackFunctorIso f x).symm
  exact (modulePullback f ⋙
    AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing X) x).map_mono g

/-- **Module pullback along a flat morphism preserves homology.** Right exactness is
unconditional (`preservesColimits_modulePullback`), so with monomorphisms preserved the functor
preserves monomorphisms and cokernels, hence homology. -/
theorem preservesHomology_modulePullback_of_isFlat
    (h : AlgebraicGeometry.IsFlat f) :
    (modulePullback f).PreservesHomology := by
  have := preservesMonomorphisms_modulePullback_of_isFlat f h
  have : PreservesColimits (modulePullback f) := preservesColimits_modulePullback f
  have : ∀ {A B : _root_.SheafOfModules.{u} (structureSheafRing Y)} (u : A ⟶ B),
      PreservesColimit (parallelPair u 0) (modulePullback f) := fun _ => inferInstance
  exact Functor.preservesHomology_of_preservesMonos_and_cokernels _

/-- **Module pullback along a flat morphism is left exact.** A functor preserving homology
between abelian categories preserves finite limits. -/
theorem preservesFiniteLimits_modulePullback_of_isFlat
    (h : AlgebraicGeometry.IsFlat f) :
    PreservesFiniteLimits (modulePullback f) := by
  have := preservesHomology_modulePullback_of_isFlat f h
  exact Functor.preservesFiniteLimits_of_preservesHomology _

end RingedSpaceModuleAdjunction
