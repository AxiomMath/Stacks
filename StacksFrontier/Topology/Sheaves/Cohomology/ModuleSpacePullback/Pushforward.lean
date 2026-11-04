module

public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.DerivedSectionsOfAPushforward
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleSpacePullback.AcyclicCollapse
public import StacksFrontier.Topology.Sheaves.Functors.Module.ExactnessOfPushforwardAndPullback

/-!
# Cohomology along a pushforward, as an isomorphism of δ-functors

Let `f : X ⟶ Y` be a morphism of ringed spaces whose pushforward of modules is **exact** — a
closed immersion, say, by Stacks 08KS — and let `V` be an open of `Y`.  Then

`Hⁿ(f⁻¹V, F)` with scalars restricted along `𝒪_Y(V) ⟶ 𝒪_X(f⁻¹V)`  and  `Hⁿ(V, f_* F)`

are isomorphic, **as cohomological δ-functors in `F`**: the comparison commutes with the
connecting morphisms of the two long exact sequences.  Its inverse is therefore a δ-compatible
map `Hⁿ(V, f_* F) ⟶ Hⁿ(f⁻¹V, F)`, which is what a consumer comparing cohomology upstairs and
downstairs along an `f`-map needs.

`Stacks.Cohomology.DerivedPushforwardSections.rightDerivedSectionsRestrictionIso` is Stacks 01EZ,
the same square in the bounded-below derived categories, and
`Stacks.Cohomology.ClosedImmersion.closedImmersionCohomologyIso` is the degreewise statement at
the whole space for schemes.  Neither says anything about the connecting morphisms, and an
unconstrained degreewise family cannot be made to: that is the gap this file closes.

## What the hypotheses are, and what they are not

Exactness of `f_*` is the only hypothesis, carried as the instance
`[PreservesFiniteColimits (RingedSpaceModuleAdjunction.modulePushforward f)]` (`f_*` is a right
adjoint, so it preserves limits always,
`RingedSpaceModuleAdjunction.preservesLimits_modulePushforward`; right exactness is what has to
be assumed).  Everything else is unconditional:

* The acyclicity input is **Stacks 01EX part (2)**,
  `Stacks.Cohomology.DerivedPushforwardSections.rightAcyclic_modulePushforward_obj` — the
  pushforward of an injective module has acyclic sections over *every* open, for an *arbitrary*
  morphism of ringed spaces.  No flatness, no closedness, no properness.
* `f_*` does **not** preserve injective objects, and no statement below pretends it does; the
  counterexample is in the module docstring of
  `StacksFrontier/AlgebraicGeometry/ClosedImmersionCohomology/Basic.lean`.  Acyclicity of the values
  is the weaker property that survives, and by
  `Stacks.Cohomology.DeltaAcyclicCollapse.effaceable_precomp` it is *exactly* what effaceability
  of the target δ-functor needs — so nothing is lost.

## Relation to the flat route

This is the companion of
`StacksFrontier/Topology/Sheaves/Cohomology/ModuleSpacePullback/Basic.lean`, which compares
cohomology across a continuous map using the *inverse* image and needs no hypothesis at all but
lands in abelian cohomology downstairs.  Here the comparison is along the *direct* image and
stays in module cohomology on both sides, at the price of exactness of `f_*`.  For a thickening —
the morphism that condition (ii) of Stacks 07YG produces, which is a closed immersion and
therefore never flat — it is this route that applies and the flat one that does not.

## Main definitions and results

* `Stacks.Cohomology.ModulePushforwardDelta.cohomologyDeltaFunctor`: module cohomology over an
  open of a ringed space, as a δ-functor; its degree-`n` component is the right derived functor
  of sections.
* `Stacks.Cohomology.ModulePushforwardDelta.pushforwardDeltaIso`: **the comparison as an
  isomorphism of δ-functors**, in the `f_* ⋙ Γ(V, −)` spelling of the source.
* `Stacks.Cohomology.ModulePushforwardDelta.sectionsRestrictionDeltaIso`: the same in the
  `Γ(f⁻¹V, −) ⋙ restrictScalars` spelling, which is the one a consumer states its comparison in.
* `Stacks.Cohomology.ModulePushforwardDelta.comparison`: the degree-`n` map
  `Hⁿ(V, f_* F) ⟶ Hⁿ(f⁻¹V, F)`, and `isIso_comparison`, that it is an isomorphism.
* `Stacks.Cohomology.ModulePushforwardDelta.comparison_comp_δ`: **the comparison commutes with
  the connecting morphisms.**  This is the δ-naturality statement.

## References

* [Stacks Project, Tag 010U](https://stacks.math.columbia.edu/tag/010U)
* [Stacks Project, Tag 01EX](https://stacks.math.columbia.edu/tag/01EX)
* [Stacks Project, Tag 01EZ](https://stacks.math.columbia.edu/tag/01EZ)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedPushforwardSections

namespace Stacks.Cohomology.ModulePushforwardDelta

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (V : Opens Y.carrier)

/-- Sections over an open of a ringed space, as a functor on sheaves of modules with values in
modules over the ring of sections of the structure sheaf. -/
abbrev sections (Z : RingedSpace.{u, u}) (W : Opens Z.carrier) :
    SheafOfModules.{u} (structureSheafRing Z) ⥤
      ModuleCat.{u} ((structureSheafRing Z).obj.obj (op W)) :=
  SheafOfModules.evaluation (structureSheafRing Z) (op W)

/-- **Module cohomology over an open of a ringed space, as a cohomological δ-functor.**  Its
degree-`n` component is the `n`-th right derived functor of sections over that open. -/
abbrev cohomologyDeltaFunctor (Z : RingedSpace.{u, u}) (W : Opens Z.carrier) :
    DeltaFunctor (SheafOfModules.{u} (structureSheafRing Z))
      (ModuleCat.{u} ((structureSheafRing Z).obj.obj (op W))) :=
  Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives (sections Z W)

/-- **Restriction of scalars along the structure morphism is additive**, with its source category
spelled as the target of sections over `f⁻¹V`.

Published here because the existing statement of exactly this fact,
`Stacks.Cohomology.DerivedPushforwardSections.restrictScalarsSectionsAdditive`, is a
`local instance` and so does not reach a consumer; without it the composite
`Γ(f⁻¹V, −) ⋙ restrictScalars` has no `Additive` instance and its right derived functors cannot
be named at all.  Mathlib's own instance spells the source as `Γ(V, (opensMap f)_* 𝒪_X)`, which
agrees with this only after unfolding `Functor.sheafPushforwardContinuous`, and instance search
does not unfold it. -/
instance restrictScalarsSectionsAdditive :
    @Functor.Additive
      (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ((opensMap f).obj V))))
      (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V)))
      _ _ _ _
      (ModuleCat.restrictScalars.{u} ((structureSheafHom f).hom.app (op V)).hom) :=
  ⟨by intros; rfl⟩

/-- Pushforward of modules preserves finite limits, being a right adjoint. -/
instance preservesFiniteLimits_modulePushforward :
    PreservesFiniteLimits (modulePushforward f) :=
  have := RingedSpaceModuleAdjunction.preservesLimits_modulePushforward f
  inferInstance

variable [PreservesFiniteColimits (modulePushforward f)]

/-- **The comparison of cohomology along a pushforward, as an isomorphism of δ-functors**, in the
`f_* ⋙ Γ(V, −)` spelling of the source.  The acyclicity input is Stacks 01EX part (2), and it is
simultaneously what makes the degreewise collapse true and what makes it δ-compatible; see
`Stacks.Cohomology.DeltaAcyclicCollapse.collapseDeltaIso`. -/
def pushforwardDeltaIso :
    Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
        (modulePushforward f ⋙ sections Y V) ≅
      (cohomologyDeltaFunctor Y V).precomp (modulePushforward f) :=
  Stacks.Cohomology.DeltaAcyclicCollapse.collapseDeltaIso (modulePushforward f) (sections Y V)
    (rightAcyclic_modulePushforward_obj f V)

/-- **The comparison map `Hⁿ(V, f_* F) ⟶ Hⁿ(f_* ⋙ Γ(V, −))(F)`**, natural in `F`.  This is the
direction a consumer has: a class downstairs over `V` is carried to a class upstairs.  By
`sectionsRestrictionDeltaIso` the target is cohomology over `f⁻¹V` with scalars restricted. -/
def comparison (n : ℕ) :
    modulePushforward f ⋙ (sections Y V).rightDerived n ⟶
      (modulePushforward f ⋙ sections Y V).rightDerived n :=
  (pushforwardDeltaIso f V).inv.app n

/-- **The comparison is an isomorphism in every degree.**  Composition of morphisms of δ-functors
is componentwise, so the two round trips are the components of the two round trips of
`pushforwardDeltaIso`. -/
def comparisonIso (n : ℕ) :
    modulePushforward f ⋙ (sections Y V).rightDerived n ≅
      (modulePushforward f ⋙ sections Y V).rightDerived n where
  hom := comparison f V n
  inv := (pushforwardDeltaIso f V).hom.app n
  hom_inv_id :=
    congrArg (fun η => DeltaFunctor.Hom.app η n) (pushforwardDeltaIso f V).inv_hom_id
  inv_hom_id :=
    congrArg (fun η => DeltaFunctor.Hom.app η n) (pushforwardDeltaIso f V).hom_inv_id

/-- The comparison map `comparison f V n` is an isomorphism. -/
instance isIso_comparison (n : ℕ) : IsIso (comparison f V n) :=
  (comparisonIso f V n).isIso_hom

/-- **The comparison commutes with the connecting morphisms.**  For a short exact sequence `S` of
sheaves of `𝒪_X`-modules, the square

    Hⁿ(V, f_* S.X₃) ⟶ Hⁿ⁺¹(V, f_* S.X₁)
         ↓                   ↓
    Hⁿ(f⁻¹V, S.X₃) ⟶ Hⁿ⁺¹(f⁻¹V, S.X₁)

commutes, the horizontal arrows being the connecting morphisms of the two long exact sequences —
above, that of cohomology over `V` at the pushed-forward sequence `f_*(S)`, which is short exact
because `f_*` is exact; below, that of the right derived functors of `f_* ⋙ Γ(V, −)` at `S`, which
is cohomology over `f⁻¹V` by `sectionsRestrictionDeltaIso` — and the vertical arrows the
comparison.

**This is the δ-naturality of module cohomology along a morphism of ringed spaces**, and it is
what the degree induction of an obstruction theory consumes.

Stated in the `f_* ⋙ Γ(V, −)` spelling of the source rather than the
`Γ(f⁻¹V, −) ⋙ restrictScalars` one, and that is a matter of cost rather than aesthetics: crossing the two
spellings costs a `whnf` of `Functor.sheafPushforwardContinuous`, and a statement that crosses it
twice — once in the δ-functor and once in the comparison — exhausts the default heartbeat budget.
`sectionsRestrictionDeltaIso` pays the crossing exactly once, and a consumer that wants the other
spelling transports along it. -/
theorem comparison_comp_δ {S : ShortComplex (SheafOfModules.{u} (structureSheafRing X))}
    (hS : S.ShortExact) (n : ℕ) :
    (comparison f V n).app S.X₃ ≫
        (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
          (modulePushforward f ⋙ sections Y V)).δ hS n =
      (cohomologyDeltaFunctor Y V).δ (hS.map_of_exact (modulePushforward f)) n ≫
        (comparison f V (n + 1)).app S.X₁ :=
  Stacks.Cohomology.DeltaAcyclicCollapse.collapseDeltaIso_inv_comm (modulePushforward f)
    (sections Y V) (rightAcyclic_modulePushforward_obj f V) hS n

/-- **The source of the comparison is cohomology over `f⁻¹V` with scalars restricted.**  Sections
of a pushforward *are* sections over the inverse image with scalars restricted — the
identification `Stacks.Cohomology.DerivedPushforwardSections.sectionsRestrictionIso` is the
identity on sections, so the two functors are the same and no transport is needed; this
declaration is the one place where the spelling crossing is paid. -/
def sectionsRestrictionDeltaIso :
    Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
        (sections X ((opensMap f).obj V) ⋙
          ModuleCat.restrictScalars ((structureSheafHom f).hom.app (op V)).hom) ≅
      (cohomologyDeltaFunctor Y V).precomp (modulePushforward f) :=
  pushforwardDeltaIso f V

end Stacks.Cohomology.ModulePushforwardDelta

end
