module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.RingTheory.RingHom.Flat
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetPullbackLeftExact
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Exactness of module pullback along a flat morphism, and its derived functor

A morphism of ringed spaces `f : X ⟶ Y` is *flat* when every germ map
`𝒪_{Y,f(x)} ⟶ 𝒪_{X,x}` is a flat ring homomorphism. This file proves that pullback of sheaves
of modules along such a morphism is an exact functor, and deduces that the unit
`f^* ⟶ R f^*` of its right derived functor on bounded-below complexes is an isomorphism: a flat
pullback needs no resolution, because it already computes its own derived functor.

The route is stalkwise and reuses the reduction already carried out for germ maps that are
*invertible*. `Stacks.RingedSpace.stalkModulePullbackFunctorIso` (Stacks 0098) identifies
`f^* ⋙ (-)_x` with `(-)_{f(x)} ⋙ (𝒪_{X,x} ⊗_{𝒪_{Y,f(x)}} -)`, the stalk functor on sheaves of
modules is exact, and monomorphisms of sheaves of modules are detected on stalks; so left
exactness of `f^*` follows from left exactness of base change along each germ map. For an
invertible germ map that is
`Stacks.RingedSpace.preservesFiniteLimits_stalkBaseChange`; for a flat one it is Mathlib's
`ModuleCat.preservesFiniteLimits_extendScalars_of_flat`. Right exactness is unconditional,
`f^*` being a left adjoint, and a right-exact additive functor preserving monomorphisms is
exact.

The derived half is a general statement about derived functors, proved here for an arbitrary
exact additive functor between abelian categories with enough injectives in the source: the unit
`F ⟶ R F` on `D⁺` is an isomorphism exactly because `F` inverts the quasi-isomorphisms of
bounded-below complexes, which is what exactness buys.

## Main results

* `Stacks.RingedSpace.flat_stalkRingMap`: the `RingCat`-valued germ map of a morphism of ringed
  spaces is flat as soon as the `CommRingCat`-valued stalk map of the underlying morphism of
  presheafed spaces is.
* `Stacks.RingedSpace.preservesFiniteLimits_stalkBaseChange_of_flat`: base change along a flat
  germ map is left exact.
* `RingedSpaceModuleAdjunction.preservesMonomorphisms_modulePullback_of_flat` and
  `RingedSpaceModuleAdjunction.preservesFiniteLimits_modulePullback_of_flat`: **pullback of
  sheaves of modules along a flat morphism of ringed spaces is left exact.**
* `RingedSpaceModuleAdjunction.exactFunctor_modulePullback_of_flat`: the same as membership of
  `CategoryTheory.exactFunctor`.
* `CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_of_exact`: the right-derived-functor
  unit of an exact additive functor is an isomorphism on `D⁺`.
* `RingedSpaceModuleAdjunction.isIso_rightDerivedFunctorPlusUnit_modulePullback_of_flat`:
  **flatness makes the unit from degreewise pullback to its right derived functor an isomorphism
  on every bounded-below complex**, and
  `RingedSpaceModuleAdjunction.derivedModulePullbackIso`, the resulting identification of
  degreewise pullback with derived pullback on `D⁺`.

## Implementation notes

`Stacks.RingedSpace.stalkRingMap` is the germ map at the `RingCat`-valued structure sheaf
`structureSheafRing`, which is the spelling `stalkBaseChange` is stated at,
while flatness of a morphism of ringed spaces is naturally a condition on
`AlgebraicGeometry.PresheafedSpace.Hom.stalkMap`, whose values are in `CommRingCat`. The two are
identified by `Stacks.RingedSpace.stalkRingMap_comp_ringStalkCommIso`, and `flat_stalkRingMap`
is the only declaration below in which they meet.

That identification cannot be used through `rw`. The stalk of the `RingCat`-valued structure
sheaf carries two `Ring` structures — the one the `RingCat` object has, and the one
`CommRing.toRing (Stacks.RingedSpace.structureStalkCommRing ..)` supplies, which is what
`RingHom.Flat` needs — and they are not identified at `instances` transparency, so the rewrite is
rejected with an application type mismatch between the two `NonAssocSemiring` instances. The
transport is therefore done by `▸` against a `have` whose type is written out, which elaborates
at default transparency where the two do agree.

`HasDerivedCategory.standard` is seated as a local instance for the two module categories, as
there is no canonical choice; the general derived-functor statement
`CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_of_exact` is stated for arbitrary
`HasDerivedCategory` instances so that it does not pin a universe.

## References

* [Stacks Project, Tag 02N3](https://stacks.math.columbia.edu/tag/02N3)
* [Stacks Project, Tag 02N7](https://stacks.math.columbia.edu/tag/02N7)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction

universe w₁ w₂ v₁ v₂ u₁ u₂ u

namespace CategoryTheory.Functor

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
  [EnoughInjectives A] (F : A ⥤ B) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- **An exact additive functor has an invertible right-derived-functor unit.** An exact functor
needs no resolution: it already computes its own derived functor.

The unit is a right derived functor of `F` along the localization of the bounded-below homotopy
category at its quasi-isomorphisms, so it is enough that `F` inverts those
(`CategoryTheory.Functor.isIso_of_isRightDerivedFunctor_of_inverts`). That is exactness: `F`
preserving finite limits and finite colimits makes `F.mapDerivedCategory` well defined and
compatible with `F.mapHomotopyCategory`, so a quasi-isomorphism of bounded-below complexes is
sent to an isomorphism in the derived category, and `DerivedCategory.Plus.ι` reflects
isomorphisms. -/
@[sga "4 XVIII 3.1.4.8" "special case"]
theorem isIso_rightDerivedFunctorPlusUnit_of_exact :
    IsIso F.rightDerivedFunctorPlusUnit := by
  apply Functor.isIso_of_isRightDerivedFunctor_of_inverts
    (W := HomotopyCategory.Plus.quasiIso A)
    F.rightDerivedFunctorPlus F.rightDerivedFunctorPlusUnit
  intro K L φ hφ
  have : IsIso (DerivedCategory.Qh.map φ.hom) :=
    Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso A (.up ℤ)) _ hφ
  have : IsIso ((DerivedCategory.Plus.ι).map
      ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map φ)) := by
    show IsIso (DerivedCategory.Qh.map ((F.mapHomotopyCategory (.up ℤ)).map φ.hom))
    exact (NatIso.isIso_map_iff F.mapDerivedCategoryFactorsh φ.hom).mp (by
      show IsIso (F.mapDerivedCategory.map (DerivedCategory.Qh.map φ.hom))
      infer_instance)
  exact isIso_of_reflects_iso _ DerivedCategory.Plus.ι

/-- `CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_of_exact` evaluated at a single
bounded-below complex. -/
@[sga "4 XVIII 3.1.4.8" "special case"]
theorem isIso_rightDerivedFunctorPlusUnit_app_of_exact (K : HomotopyCategory.Plus A) :
    IsIso (F.rightDerivedFunctorPlusUnit.app K) :=
  (NatTrans.isIso_iff_isIso_app F.rightDerivedFunctorPlusUnit).mp
    (isIso_rightDerivedFunctorPlusUnit_of_exact F) K

end CategoryTheory.Functor

namespace Stacks.RingedSpace

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y) (x : X.carrier)

/-- **The `RingCat`-valued germ map of a morphism of ringed spaces is flat as soon as the
`CommRingCat`-valued stalk map of the underlying morphism of presheafed spaces is.** The two are
identified by `Stacks.RingedSpace.stalkRingMap_comp_ringStalkCommIso` up to the ring isomorphisms
`Stacks.RingedSpace.ringStalkCommIso` on either side, and flatness is unchanged by composition
with a bijective ring homomorphism. -/
theorem flat_stalkRingMap (h : (f.hom.stalkMap x).hom.Flat) :
    letI := structureStalkCommRing Y (f.hom.base x)
    letI := structureStalkCommRing X x
    (stalkRingMap f x).hom.Flat := by
  let := structureStalkCommRing Y (f.hom.base x)
  let := structureStalkCommRing X x
  let : CommRing (ToType ((forget₂ CommRingCat.{u} RingCat.{u}).obj (X.presheaf.stalk x))) :=
    inferInstanceAs (CommRing (ToType (X.presheaf.stalk x)))
  let : CommRing (ToType ((forget₂ CommRingCat.{u} RingCat.{u}).obj
      (Y.presheaf.stalk (f.hom.base x)))) :=
    inferInstanceAs (CommRing (ToType (Y.presheaf.stalk (f.hom.base x))))
  have key : ((ringStalkCommIso X x).hom.hom).comp (stalkRingMap f x).hom =
      ((f.hom.stalkMap x).hom).comp ((ringStalkCommIso Y (f.hom.base x)).hom.hom) :=
    congrArg RingCat.Hom.hom (stalkRingMap_comp_ringStalkCommIso f x)
  have step : (((f.hom.stalkMap x).hom).comp
      ((ringStalkCommIso Y (f.hom.base x)).hom.hom)).Flat :=
    RingHom.Flat.comp
      (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)) h
  have step' : (((ringStalkCommIso X x).hom.hom).comp (stalkRingMap f x).hom).Flat := key ▸ step
  exact (RingHom.Flat.comp_iff_of_bijective_left (ConcreteCategory.bijective_of_isIso _)).mp step'

/-- **Base change along a flat germ map is left exact.** `Stacks.RingedSpace.stalkBaseChange` is
`ModuleCat.extendScalars` of the germ map, and extension of scalars along a flat ring
homomorphism preserves finite limits. -/
theorem preservesFiniteLimits_stalkBaseChange_of_flat (h : (f.hom.stalkMap x).hom.Flat) :
    PreservesFiniteLimits (stalkBaseChange f x) := by
  let := structureStalkCommRing Y (f.hom.base x)
  let := structureStalkCommRing X x
  exact ModuleCat.preservesFiniteLimits_extendScalars_of_flat (flat_stalkRingMap f x h)

end Stacks.RingedSpace

namespace RingedSpaceModuleAdjunction

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **Module pullback along a flat morphism of ringed spaces preserves monomorphisms.**
Monomorphisms of sheaves of modules are detected on stalks, and on stalks `f^*` is the stalk at
`f x` followed by base change along the germ map (Stacks 0098) — the first factor exact, the
second exact by flatness. -/
theorem preservesMonomorphisms_modulePullback_of_flat
    (hf : ∀ x : X.carrier, (f.hom.stalkMap x).hom.Flat) :
    (modulePullback f).PreservesMonomorphisms := by
  constructor
  intro M N g _
  apply AlgebraicGeometry.SheafOfModules.mono_of_stalk_mono
  intro x
  have : PreservesFiniteLimits (Stacks.RingedSpace.stalkBaseChange f x) :=
    Stacks.RingedSpace.preservesFiniteLimits_stalkBaseChange_of_flat f x (hf x)
  have : (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Y)
      (f.hom.base x)).PreservesMonomorphisms :=
    Functor.preservesMonomorphisms_of_preservesFiniteLimits _
  have : (Stacks.RingedSpace.stalkBaseChange f x).PreservesMonomorphisms :=
    Functor.preservesMonomorphisms_of_preservesFiniteLimits _
  have : (modulePullback f ⋙ AlgebraicGeometry.SheafOfModules.stalkFunctor
      (structureSheafRing X) x).PreservesMonomorphisms :=
    Functor.PreservesMonomorphisms.of_iso
      (Stacks.RingedSpace.stalkModulePullbackFunctorIso f x).symm
  exact (modulePullback f ⋙
    AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing X) x).map_mono g

/-- **Module pullback along a flat morphism of ringed spaces is left exact.** Right exactness is
unconditional (`RingedSpaceModuleAdjunction.preservesColimits_modulePullback`), so with
monomorphisms preserved the functor preserves homology, hence finite limits. -/
theorem preservesFiniteLimits_modulePullback_of_flat
    (hf : ∀ x : X.carrier, (f.hom.stalkMap x).hom.Flat) :
    PreservesFiniteLimits (modulePullback f) := by
  have := preservesMonomorphisms_modulePullback_of_flat f hf
  have : PreservesColimits (modulePullback f) := preservesColimits_modulePullback f
  have : ∀ {A B : _root_.SheafOfModules.{u} (structureSheafRing Y)} (u : A ⟶ B),
      PreservesColimit (parallelPair u 0) (modulePullback f) := fun _ => inferInstance
  have : (modulePullback f).PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels _
  exact Functor.preservesFiniteLimits_of_preservesHomology _

/-- **Pullback of sheaves of modules along a flat morphism of ringed spaces is exact.** This is
the exactness statement of Stacks 02N7: both halves of `CategoryTheory.exactFunctor` membership,
the colimit one free and the limit one by flatness. -/
theorem exactFunctor_modulePullback_of_flat
    (hf : ∀ x : X.carrier, (f.hom.stalkMap x).hom.Flat) :
    exactFunctor (SheafOfModules.{u} (structureSheafRing Y))
      (SheafOfModules.{u} (structureSheafRing X)) (modulePullback f) :=
  exactFunctor_modulePullback_of_preservesFiniteLimits f
    (preservesFiniteLimits_modulePullback_of_flat f hf)

end RingedSpaceModuleAdjunction

attribute [local instance] HasDerivedCategory.standard

namespace RingedSpaceModuleAdjunction

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **Flatness makes the unit from degreewise pullback to its right derived functor an
isomorphism on every bounded-below complex.** This is the derived-functor statement of
Stacks 02N7: for a flat morphism of ringed spaces, `f^*` is exact
(`RingedSpaceModuleAdjunction.preservesFiniteLimits_modulePullback_of_flat`), and an exact
functor computes its own right derived functor
(`CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_of_exact`). -/
theorem isIso_rightDerivedFunctorPlusUnit_modulePullback_of_flat
    (hf : ∀ x : X.carrier, (f.hom.stalkMap x).hom.Flat)
    (K : HomotopyCategory.Plus (SheafOfModules.{u} (structureSheafRing Y))) :
    IsIso ((modulePullback f).rightDerivedFunctorPlusUnit.app K) :=
  have := preservesFiniteLimits_modulePullback_of_flat f hf
  have := preservesFiniteColimits_modulePullback f
  Functor.isIso_rightDerivedFunctorPlusUnit_app_of_exact (modulePullback f) K

/-- **Derived pullback along a flat morphism is degreewise pullback.** The canonical
identification of `f^*` applied degreewise with its right derived functor on bounded-below
derived categories, `asIso` of the unit. -/
noncomputable def derivedModulePullbackIso
    (hf : ∀ x : X.carrier, (f.hom.stalkMap x).hom.Flat) :
    (modulePullback f).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
      DerivedCategory.Plus.Qh ⋙ (modulePullback f).rightDerivedFunctorPlus :=
  letI : IsIso ((modulePullback f).rightDerivedFunctorPlusUnit) :=
    (NatTrans.isIso_iff_isIso_app _).mpr
      (isIso_rightDerivedFunctorPlusUnit_modulePullback_of_flat f hf)
  asIso ((modulePullback f).rightDerivedFunctorPlusUnit)

end RingedSpaceModuleAdjunction

end
