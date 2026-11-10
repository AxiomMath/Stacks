module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBaseChangeVanishingChartRing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.ChaoticComparisonOnCartesianObjects

/-!
# Étale charts detect isomorphisms of modules on an algebraic space

A morphism of sheaves of modules on a site is invertible as soon as every one of its modules of
sections is, because the forgetful functor to presheaves of modules is fully faithful and a
morphism of presheaves of modules with invertible components has the inverse components for an
inverse.  On the small étale site of an algebraic space `Y` the sections over a chart `V` are
the sections of the restriction of the module along the étale structure morphism of `V`, so the
same statement reads: a morphism of `𝒪_Y`-modules is invertible as soon as its restriction to
every étale scheme chart of `Y` is.

That is the form in which the invertibility of a comparison map of `𝒪_Y`-modules is checked
étale-locally on `Y`, and it is the companion, for isomorphisms, of
`AlgebraicGeometry.Space.isZero_iff_forall_isZero_etaleModulePullback_chartToSpace`, which is
the same statement for the zero module.

## Main results

* `Stacks.SheafOfModules.isIso_of_forall_isIso_val_app`: sections detect isomorphisms of sheaves
  of modules on an arbitrary site.
* `Stacks.SheafOfModules.isIso_val_app_of_isIso_freeModuleUniverse`: the converse direction,
  sections of an invertible morphism, at a free module universe.
* `AlgebraicGeometry.Space.isIso_of_forall_isIso_val_app`: the same for `𝒪_Y`-modules on the
  small étale site of an algebraic space.
* `AlgebraicGeometry.Space.isIso_of_forall_isIso_etaleModulePullback_chartToSpace`: **étale
  charts detect isomorphisms.**  A morphism of `𝒪_Y`-modules whose restriction along the
  structure morphism of every étale scheme chart of `Y` is invertible is itself invertible.

## Implementation notes

The chart statement is proved by reading the restriction to `V` over the *identity* chart of
the algebraic space that `V` represents, where the sections of the restriction are the sections
over `V` on the nose.  That is
`AlgebraicGeometry.Space.etaleModulePullback_chartToSpace_map_val_app_idEtaleChart`, which is
stated at the module universe of the structure rings, so the chart statements below are stated
there too;  the two statements about an arbitrary site leave the module universe free.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m

namespace Stacks.SheafOfModules

/-- **Sections detect isomorphisms of sheaves of modules.**  A morphism of sheaves of modules
whose module of sections over every object of the site is invertible is invertible.

The inverse components of the underlying morphism of presheaves of modules are again natural and
so assemble into an inverse, by
`Stacks.ModulesOnACategory.ChaoticComparison.isIso_of_forall_isIso_app`;  the forgetful functor
from sheaves of modules to presheaves of modules reflects isomorphisms, being fully faithful. -/
theorem isIso_of_forall_isIso_val_app {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : _root_.SheafOfModules.{m} R} (φ : M ⟶ N)
    (hφ : ∀ U : Cᵒᵖ, IsIso (φ.val.app U)) : IsIso φ :=
  have : IsIso ((_root_.SheafOfModules.forget R).map φ) :=
    Stacks.ModulesOnACategory.ChaoticComparison.isIso_of_forall_isIso_app φ.val hφ
  isIso_of_reflects_iso φ (_root_.SheafOfModules.forget R)

/-- The sections of an invertible morphism of sheaves of modules are invertible:  reading
sections over an object is a functor.

`Stacks.SheafOfModules.isIso_val_app_of_isIso` is this statement with the module universe tied
to the universe of the structure rings;  this one leaves it free, which is what the chart
statements of this tree need. -/
theorem isIso_val_app_of_isIso_freeModuleUniverse {C : Type*} [Category* C]
    {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : _root_.SheafOfModules.{m} R} (φ : M ⟶ N) [IsIso φ]
    (U : Cᵒᵖ) : IsIso (φ.val.app U) :=
  inferInstanceAs (IsIso ((_root_.SheafOfModules.evaluation R U).map φ))

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Sections over the étale charts detect isomorphisms of `𝒪_Y`-modules.** -/
theorem isIso_of_forall_isIso_val_app (Y : AlgebraicSpaces B S hS)
    {M N : Modules.{u, m} B S hS Y.obj Y.property} (φ : M ⟶ N)
    (hφ : ∀ V : SmallEtale B S hS Y.obj, IsIso (φ.val.app (op V))) : IsIso φ :=
  Stacks.SheafOfModules.isIso_of_forall_isIso_val_app φ fun U => hφ U.unop

/-- **Étale charts detect isomorphisms of `𝒪_Y`-modules.**  A morphism of `𝒪_Y`-modules whose
restriction along the structure morphism of every étale scheme chart of `Y` is invertible is
itself invertible.

This is the statement that licenses checking the invertibility of a comparison map of
`𝒪_Y`-modules étale-locally on `Y`.  It is the companion of
`AlgebraicGeometry.Space.isZero_iff_forall_isZero_etaleModulePullback_chartToSpace` for
isomorphisms, and is proved the same way:  the sections of the restriction to `V` over the
identity chart are the sections over `V`. -/
theorem isIso_of_forall_isIso_etaleModulePullback_chartToSpace (Y : AlgebraicSpaces B S hS)
    {M N : Modules.{u, u} B S hS Y.obj Y.property} (φ : M ⟶ N)
    (hφ : ∀ V : SmallEtale B S hS Y.obj,
      IsIso ((etaleModulePullback B S hS (chartToSpace B S hS Y V)
        (isEtale_chartToSpace B S hS Y V)).map φ)) :
    IsIso φ := by
  refine isIso_of_forall_isIso_val_app B S hS Y φ fun V => ?_
  rw [← etaleModulePullback_chartToSpace_map_val_app_idEtaleChart B S hS φ V]
  have := hφ V
  exact Stacks.SheafOfModules.isIso_val_app_of_isIso_freeModuleUniverse _ _

/-- **Étale charts detect isomorphisms**, in the `↔` form:  a morphism of `𝒪_Y`-modules is
invertible exactly when all of its étale chart restrictions are.  The forward implication is
functoriality of restriction. -/
theorem isIso_iff_forall_isIso_etaleModulePullback_chartToSpace (Y : AlgebraicSpaces B S hS)
    {M N : Modules.{u, u} B S hS Y.obj Y.property} (φ : M ⟶ N) :
    IsIso φ ↔ ∀ V : SmallEtale B S hS Y.obj,
      IsIso ((etaleModulePullback B S hS (chartToSpace B S hS Y V)
        (isEtale_chartToSpace B S hS Y V)).map φ) :=
  ⟨fun _ _ => inferInstance, isIso_of_forall_isIso_etaleModulePullback_chartToSpace B S hS Y φ⟩

end AlgebraicGeometry.Space

end
