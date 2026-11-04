module

public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally
public import StacksFrontier.Topology.Sheaves.Cohomology.ModulePushforwardComparison.HigherDirectImages
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.DerivedSectionsOfAPushforward
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.AmpleCohomologicalCriterion.Sections
public import StacksFrontier.AlgebraicGeometry.SheafOfModulesEnoughInjectives

/-!
# Cohomology along a morphism of schemes, read through the ringed space underneath it

The cohomology of a sheaf of modules on a scheme, and the pushforward of such a sheaf along a
morphism of schemes, are built in Mathlib directly out of `AlgebraicGeometry.Scheme.ringCatSheaf`
and `AlgebraicGeometry.Scheme.Modules.pushforward`. The theory of sheaf cohomology on a ringed
space -- global sections and its right derived functors, the acyclicity of the pushforward of an
injective module sheaf, the commuting square of derived sections and derived pushforward -- is
built instead out of `structureSheafRing` and
`RingedSpaceModuleAdjunction.modulePushforward`. Nothing connects the two, so none of that theory
can be used for a statement about schemes.

This file supplies the connection, and it costs nothing: every identification below holds by
`rfl`. The ring sheaf of a scheme *is* the ring sheaf of the ringed space underneath it, the
pushforward of module sheaves along a morphism of schemes *is* the pushforward along the
underlying morphism of ringed spaces, and -- the identity the comparison of cohomology turns on --
global sections on the source *is* the composite of pushforward with global sections on the
target.

Consequently a sheaf-cohomology statement about a morphism of schemes may be proved with the
ringed space machinery with no transport: the two sides are the same term, and an instance found
for one is an instance for the other. In particular the acyclicity input that
[Stacks, Tag 01EX] supplies -- that the pushforward of an injective module sheaf has acyclic
sections over every open -- becomes available for a morphism of schemes, which is what
`rightAcyclic_schemePushforward_obj` records.

## Main definitions

* `Stacks.SchemeCohomology.ringedSpace` and `Stacks.SchemeCohomology.hom`: the ringed space
  underlying a scheme and the morphism of ringed spaces underlying a morphism of schemes.

## Main results

* `Stacks.SchemeCohomology.ringSheaf_ringedSpace` and
  `Stacks.SchemeCohomology.modulePushforward_hom`: the ring sheaf and the pushforward functor of
  the ringed space underneath are the ring sheaf and the pushforward functor of the scheme.
* `Stacks.SchemeCohomology.pushforward_comp_secF`: global sections on the source is the
  composite of pushforward with global sections on the target, as functors, on the nose. This is
  the identity that makes the cohomology of a module sheaf and the cohomology of its pushforward
  two right derived functors of one functor.
* `Stacks.SchemeCohomology.Hfunctor_eq_rightDerived_comp`: therefore the cohomology functor of
  the source is the right derived functor of that composite.
* `Stacks.SchemeCohomology.secF_eq_evaluation_comp_forget`: global sections valued in abelian
  groups is module valued sections followed by forgetting the module structure.
* `Stacks.SchemeCohomology.rightAcyclic_schemePushforward_obj`: for a morphism of schemes, the
  pushforward of an injective module sheaf is right acyclic for module valued sections over
  every open of the target.

## Implementation notes

`AlgebraicGeometry.Scheme.ringCatSheaf` is valued in `TopCat.Sheaf`, which is a `def` rather
than an abbreviation of `CategoryTheory.Sheaf (Opens.grothendieckTopology _)`, and carries its
own derived `Category` instance. The identifications below therefore cross that boundary; they
are nevertheless all `rfl`, and are stated as equations of terms rather than as isomorphisms so
that a client may `rw` with them or, better, leave them implicit and let unification do the
unfolding.

The preimage of the top open under the underlying continuous map is the top open by `rfl`
(`opensMap_obj_top`), which is why `pushforward_comp_secF` can be stated at `⊤` on both sides
with no comparison of opens.

`rightAcyclic_schemePushforward_obj` is stated for module valued sections rather than for
`Tag01E3.secF`, which is the functor the cohomology functor derives. Carrying it across the
forgetful functor needs left exactness of `secF`, and there is no instance for that: the three
pieces (`SheafOfModules.toSheaf`, sections of an abelian sheaf over an open, and
`SheafOfModules.evaluation`) each have one, but `Limits.comp_preservesFiniteLimits` is not an
instance and applying it by hand produces `PreservesFiniteLimits` at universes that do not match
the goal's. That is the next step, and it is a universe bookkeeping problem, not a mathematical
one.

## References

* [Stacks Project, Tag 01EX](https://stacks.math.columbia.edu/tag/01EX)
* [Stacks Project, Tag 01EZ](https://stacks.math.columbia.edu/tag/01EZ)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.SchemeCohomology

/-- The ringed space underlying a scheme. -/
abbrev ringedSpace (X : Scheme.{u}) : RingedSpace.{u, u} :=
  X.toLocallyRingedSpace.toRingedSpace

/-- The morphism of ringed spaces underlying a morphism of schemes. -/
abbrev hom {X Y : Scheme.{u}} (f : X ⟶ Y) : ringedSpace X ⟶ ringedSpace Y :=
  f.toLRSHom.toShHom

/-- The ring sheaf of the ringed space underlying a scheme is the ring sheaf of the scheme. -/
theorem ringSheaf_ringedSpace (X : Scheme.{u}) :
    structureSheafRing (ringedSpace X) = X.ringCatSheaf :=
  rfl

/-- Pushforward of module sheaves along the morphism of ringed spaces underlying a morphism of
schemes is pushforward of module sheaves along the morphism of schemes. -/
theorem modulePushforward_hom {X Y : Scheme.{u}} (f : X ⟶ Y) :
    modulePushforward (hom f) = Scheme.Modules.pushforward f :=
  rfl

/-- The preimage of the top open is the top open. -/
theorem opensMap_obj_top {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (opensMap (hom f)).obj ⊤ = (⊤ : Opens X.carrier) :=
  rfl

/-- Pushforward of module sheaves along a morphism of schemes is additive. -/
instance pushforward_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pushforward f).Additive :=
  inferInstanceAs (modulePushforward (hom f)).Additive

/-- Pushforward of module sheaves along a morphism of schemes is left exact: it is a right
adjoint. -/
instance pushforward_preservesFiniteLimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (Scheme.Modules.pushforward f) :=
  inferInstanceAs (PreservesFiniteLimits (modulePushforward (hom f)))

/-- Global sections valued in abelian groups is module valued sections over the same open
followed by forgetting the module structure. -/
theorem secF_eq_evaluation_comp_forget (X : Scheme.{u}) (U : Opens X.carrier) :
    secF X.ringCatSheaf U =
      SheafOfModules.evaluation X.ringCatSheaf (op U) ⋙
        forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op U))) AddCommGrpCat.{u} :=
  rfl

/-- **Global sections on the source is pushforward followed by global sections on the target.**
The two functors `Mod(𝒪_X) ⥤ Ab` are the same functor, not merely isomorphic ones: sections of
`f_* M` over the top open of the target are by construction sections of `M` over its preimage,
which is the top open of the source.

This is the identity the comparison of the cohomology of `M` with the cohomology of `f_* M`
turns on. It says that the two cohomology functors being compared are the right derived functor
of a composite and the composite of a functor with a right derived functor, so that the
comparison is an instance of [Stacks, Tag 015M] rather than a construction. -/
theorem pushforward_comp_secF {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.Modules.pushforward f ⋙ secF Y.ringCatSheaf ⊤ = secF X.ringCatSheaf ⊤ :=
  rfl

/-- Pushforward followed by global sections on the target is additive: by
`pushforward_comp_secF` it *is* global sections on the source. -/
instance pushforward_comp_secF_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pushforward f ⋙ secF Y.ringCatSheaf ⊤).Additive :=
  inferInstanceAs (secF X.ringCatSheaf ⊤).Additive

/-- The cohomology functor of the source is the right derived functor of pushforward followed
by global sections on the target. -/
theorem Hfunctor_eq_rightDerived_comp {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    Hfunctor X.ringCatSheaf ⊤ n =
      (Scheme.Modules.pushforward f ⋙ secF Y.ringCatSheaf ⊤).rightDerived n :=
  rfl

section Acyclicity

attribute [local instance] HasDerivedCategory.standard

-- As in `StacksDraft.Ch20.Sec17.Tag01EZ`, whose statement is being transferred: the cheap
-- instance deriving pointwise right derivability from `EnoughInjectives` is given precedence
-- over the one that would try to prove termwise injectivity of an unknown complex.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- Module sheaves on a scheme form an abelian category, in the spelling that unfolds
`AlgebraicGeometry.Scheme.Modules`. -/
local instance sheafOfModules_abelian (X : Scheme.{u}) :
    Abelian (SheafOfModules.{u} X.ringCatSheaf) :=
  inferInstance

/-- Module sheaves on a scheme have enough injectives, in the spelling that unfolds
`AlgebraicGeometry.Scheme.Modules`. -/
local instance sheafOfModules_enoughInjectives (X : Scheme.{u}) :
    EnoughInjectives (SheafOfModules.{u} X.ringCatSheaf) :=
  IsGrothendieckAbelian.enoughInjectives

/-- **The acyclicity input of [Stacks, Tag 01EX] for a morphism of schemes.** The pushforward of
an injective sheaf of modules is right acyclic for module valued sections over any open of the
target: the single complex on it computes the right derived functor of those sections.

This is exactly the hypothesis that [Stacks, Tag 015M] asks of the pair (pushforward, sections)
in order that the composite of the two bounded below right derived functors be a right derived
functor of the composite. It is weaker than the pushforward preserving injective objects, which
is false; the ringed space statement is
`Stacks.Cohomology.DerivedPushforwardSections.rightAcyclic_modulePushforward_obj`, and this
records that it transfers to schemes with no transport. -/
theorem rightAcyclic_schemePushforward_obj {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Opens Y.carrier)
    (I : X.Modules) (hI : Injective I) :
    (SheafOfModules.evaluation Y.ringCatSheaf (op V)).rightAcyclic
      ((Scheme.Modules.pushforward f).obj I) :=
  Stacks.Cohomology.DerivedPushforwardSections.rightAcyclic_modulePushforward_obj
    (hom f) V I hI

end Acyclicity

end Stacks.SchemeCohomology

end
