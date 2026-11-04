module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.AlgebraicGeometry.Modules.ProjectionFormula
public import StacksFrontier.AlgebraicGeometry.SheafOfModulesEnoughInjectives
public import StacksFrontier.Topology.Sheaves.Cohomology.RelativeMayerVietoris.OpenImmersionPullback

/-!
# Invertibility in the bounded below derived category is local on the scheme

A morphism of sheaves of modules on a scheme is invertible as soon as its restrictions to the
members of an open covering are, and this file carries that locality across to the bounded below
derived category: a morphism of `D⁺(𝒪_Y)` whose images under the derived inverse images along the
members of an open covering of `Y` are invertible is invertible.

The passage is cohomology. A morphism of `D⁺` is invertible exactly when it is invertible on every
cohomology sheaf (`CategoryTheory.DerivedCategory.Plus.isIso_iff`); restriction to an open
subscheme is exact, so its right derived functor commutes with cohomology
(`Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso`); and invertibility of a morphism of
sheaves of modules is local
(`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict`).

## Main results

* `Stacks.AlgebraicGeometry.ModuleBaseChange.preservesFiniteLimits_modulePullback_opensι` and
  `preservesInjectiveObjects_modulePullback_opensι`: restriction to an open subscheme is exact and
  preserves injective objects.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_of_isIso_modulePullback`: **invertibility of a
  morphism of sheaves of modules is local**, at the `modulePullback` spelling of restriction.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_of_isIso_derivedPullback`: **invertibility in
  `D⁺(𝒪_Y)` is local on `Y`.**

## References

* [Stacks Project, Tag 007T](https://stacks.math.columbia.edu/tag/007T)
-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction

namespace Stacks.AlgebraicGeometry.ModuleBaseChange

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### Restriction to an open subscheme -/

/-- **Restriction to an open subscheme is left exact.**  The inverse image along an open immersion
preserves homology. -/
theorem preservesFiniteLimits_modulePullback_opensι {Y : Scheme.{u}} (V : Y.Opens) :
    PreservesFiniteLimits (modulePullback V.ι.toLRSHom.toShHom) :=
  let _ := Stacks.Cohomology.openImmersionModulePullback_preservesHomology
    V.ι.toLRSHom.toShHom
  (modulePullback V.ι.toLRSHom.toShHom).preservesFiniteLimits_of_preservesHomology

/-- **Restriction to an open subscheme is right exact**, being a left adjoint. -/
theorem preservesFiniteColimits_modulePullback_opensι {Y : Scheme.{u}} (V : Y.Opens) :
    PreservesFiniteColimits (modulePullback V.ι.toLRSHom.toShHom) :=
  let _ := Stacks.Cohomology.openImmersionModulePullback_preservesHomology
    V.ι.toLRSHom.toShHom
  (modulePullback V.ι.toLRSHom.toShHom).preservesFiniteColimits_of_preservesHomology

/-- **Restriction to an open subscheme preserves injective objects.**  It is a left adjoint of a
left adjoint, so a left adjoint of an exact functor. -/
theorem preservesInjectiveObjects_modulePullback_opensι {Y : Scheme.{u}} (V : Y.Opens) :
    (modulePullback V.ι.toLRSHom.toShHom).PreservesInjectiveObjects :=
  Stacks.Cohomology.RelativeMayerVietoris.modulePullback_preservesInjectiveObjects _

/-! ### Locality of invertibility -/

/-- **A morphism of sheaves of modules invertible after restriction to every member of an open
covering is invertible**, at the `modulePullback` spelling of restriction. -/
theorem isIso_of_isIso_modulePullback {Y : Scheme.{u}} {M N : Y.Modules} (φ : M ⟶ N)
    {I : Type*} (V : I → Y.Opens) (hV : IsOpenCover V)
    (h : ∀ i, IsIso ((Scheme.Modules.pullback (V i).ι).map φ)) : IsIso φ := by
  exact AffineBaseChange.isIso_of_isIso_restrict φ V hV fun i =>
    (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback (V i).ι) φ).2 (h i)

/-- Invertibility of the image of a morphism of `D⁺` under the right derived functor of an exact
functor passes to cohomology: the derived functor of an exact functor commutes with cohomology, so
the exact functor applied to the cohomology of the morphism is invertible. -/
theorem isIso_map_homologyFunctor_map {C D : Type*} [Category* C] [Category* D] [Abelian C]
    [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C] (E : C ⥤ D)
    [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    {A B : DerivedCategory.Plus C} (φ : A ⟶ B)
    (h : IsIso (E.rightDerivedFunctorPlus.map φ)) (n : ℤ) :
    IsIso (E.map ((DerivedCategory.Plus.homologyFunctor C n).map φ)) := by
  exact (NatIso.isIso_map_iff (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso E n) φ).1
    (Functor.map_isIso (DerivedCategory.Plus.homologyFunctor D n) _)

/-- **Invertibility in `D⁺(𝒪_Y)` is local on `Y`.**  A morphism of the bounded below derived
category whose image under the derived inverse image along every member of an open covering of `Y`
is invertible is itself invertible: a morphism of `D⁺` is invertible exactly when every cohomology
sheaf of it is, restriction to an open is exact so its derived functor commutes with cohomology,
and invertibility of a morphism of sheaves of modules is local. -/
theorem isIso_of_isIso_derivedPullback {Y : Scheme.{u}}
    {A B : DerivedCategory.Plus (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))}
    (φ : A ⟶ B) {I : Type*} (V : I → Y.Opens) (hV : IsOpenCover V)
    (h : ∀ i, IsIso ((modulePullback (V i).ι.toLRSHom.toShHom).rightDerivedFunctorPlus.map φ)) :
    IsIso φ := by
  rw [DerivedCategory.Plus.isIso_iff]
  intro n
  refine isIso_of_isIso_modulePullback
    ((DerivedCategory.Plus.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) n).map φ) V hV fun i => ?_
  let := preservesFiniteLimits_modulePullback_opensι (V i)
  let := preservesFiniteColimits_modulePullback_opensι (V i)
  exact isIso_map_homologyFunctor_map (modulePullback (V i).ι.toLRSHom.toShHom) φ (h i) n

end Stacks.AlgebraicGeometry.ModuleBaseChange

end
