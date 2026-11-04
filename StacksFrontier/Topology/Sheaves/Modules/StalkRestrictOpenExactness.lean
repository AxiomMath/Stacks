module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.Algebra.Homology.StrictlyPerfectRestrictionOfLE
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.SheafLevel
public import StacksFrontier.Topology.Sheaves.Modules.StalkRestrictOpen
public import StacksFrontier.Topology.Sheaves.Modules.StalkTensor

/-!
# Exactness and commutativity instances for the stalk comparison on a bare ringed space

`AlgebraicGeometry.RingedSpace.restrictModulesStalkNatIso` of
`StacksFrontier/Topology/Sheaves/Modules/StalkRestrictOpen.lean` compares, for a point `y` of an
open `U` of a ringed space `W` that is *not* assumed to be a scheme, the two routes

`restrictModules W U ⋙ stalkFunctor 𝒪_{W|U} ⟨y, hy⟩` and
`stalkFunctor 𝒪_W y ⋙ ModuleCat.restrictScalars (restrictModulesStalkRingIso W U hy)`.

Transporting that isomorphism to derived categories through
`CategoryTheory.Functor.mapDerivedCategoryCompIso` (which is public, in
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/PushforwardClosedImmersion.lean`, together with
`CategoryTheory.Functor.mapDerivedCategoryCongr`) needs each factor to be exact — `Additive`,
`PreservesFiniteLimits`, `PreservesFiniteColimits` — and a consumer reading a stalk ring as a
*commutative* ring needs a `CommRing` instance on it. All of that is already proved in this
repository, and none of it is *found* at the spellings `restrictModulesStalkNatIso` is stated
at. This file registers it there, and records the definitional bridges between the competing
spellings of the sheaf of rings of a ringed space and of restriction to an open.

## Main results

* `AlgebraicGeometry.RingedSpace.structureSheafOfRings_eq_tensorRingSheaf`: the sheaf of rings
  underlying a ringed space is the same whether it is spelled
  `StrictlyPerfect.structureSheafOfRings W` or `Stacks.SheafOfModules.Tensor.ringSheaf W.sheaf`.
  `AlgebraicGeometry.RingedSpace.stalkFunctor_eq_tensorRingSheaf` is the same for the stalk
  functor.
* `AlgebraicGeometry.RingedSpace.strictlyPerfectRestrictModules_eq`: restriction of
  `𝒪_W`-modules to an open is the same functor whether it is spelled
  `StrictlyPerfect.restrictModules` or `AlgebraicGeometry.RingedSpace.restrictModules`.
* Exactness of restriction to an open, as instances at both spellings:
  `AlgebraicGeometry.RingedSpace.preservesFiniteLimits_strictlyPerfectRestrictModules` and its
  colimit companion, and `AlgebraicGeometry.RingedSpace.additive_restrictModules`,
  `AlgebraicGeometry.RingedSpace.preservesFiniteLimits_restrictModules` and its colimit
  companion.
* Exactness of the stalk functor of a bare ringed space, as instances:
  `AlgebraicGeometry.RingedSpace.additive_stalkFunctor`,
  `AlgebraicGeometry.RingedSpace.preservesFiniteLimits_stalkFunctor`,
  `AlgebraicGeometry.RingedSpace.preservesFiniteColimits_stalkFunctor`, together with the
  `_restrict` variants at a point of an open subspace and the `_tensorRingSheaf` variants at the
  other spelling of the sheaf of rings.
* `AlgebraicGeometry.RingedSpace.commRing_stalk_structureSheafOfRings` and its `_restrict` and
  `_tensorRingSheaf` variants: the stalk of the structure sheaf of a ringed space, read in
  `RingCat`, is a commutative ring.

## Implementation notes

**Why respelling is needed, and why it is not duplication.** Instance search unifies the goal
with an instance's conclusion at *reducible* transparency only. Three separate failures arise,
and each is repaired by stating the same fact again at the spelling the consumer writes. This is
the discipline the implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/KoszulStalkComplexIso.lean` record for
`CategoryTheory.Functor.PreservesZeroMorphisms`, and the one to follow in general: pin
the spelling and restate the API at it rather than let the unifier see both. Every class
involved — `CategoryTheory.Functor.Additive`,
`CategoryTheory.Limits.PreservesFiniteLimits`,
`CategoryTheory.Limits.PreservesFiniteColimits` — is `Prop`-valued, so two instances for one
goal cannot disagree.

* *Lemmas that were never instances.*
  `StrictlyPerfect.preservesFiniteLimits_restrictModules` and
  `AlgebraicGeometry.RingedSpace.restrictModules_preservesFiniteLimits` are `lemma`s, used
  through `attribute [local instance]` at a dozen call sites. They are registered globally here.

* *`structureSheafOfRings` is a plain `def`.* `StrictlyPerfect.structureSheafOfRings W` is
  `⟨W.presheaf ⋙ forget₂ CommRingCat RingCat, _⟩`, so `(structureSheafOfRings W).obj` is the
  shape `_ ⋙ forget₂ CommRingCat RingCat` that `StacksDraft.StalkTensor.commRing_stalk` wants —
  but only after unfolding a `def`, which instance search does not do. The same unfolding is
  what hides the shape `Opens.grothendieckTopology ↑X` of the site from the generic stalk
  instances of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/StalkwiseExactness.lean`: the
  topology of the carrier of a presheafed space carries
  `AlgebraicGeometry.PresheafedSpace.instTopologicalSpaceCarrierCarrier`, not `TopCat.str`, and
  reconciling the two needs a non-reducible unfolding.

* *A point of an open subspace is a `Subtype.mk`.* The carrier of `W.restrict
  U.isOpenEmbedding` is `↥U` only after unfolding
  `AlgebraicGeometry.PresheafedSpace.restrict`, so the type Lean infers for the term `⟨y, hy⟩`
  that `restrictModulesStalkNatIso` is stated with is *not* reducibly the type `stalkFunctor`'s
  point argument has. An instance stated for a variable point of a variable ringed space
  therefore does not apply to it, even though it does apply to a variable point of
  `W.restrict U.isOpenEmbedding`. Hence the `_restrict` variants, keyed at `⟨y, hy⟩`.

**The two spellings of the sheaf of rings, and the Tor-amplitude consumer.**
`StacksDraft.TorAmplitude.HasTorAmplitudeCanonical` needs `CommRing` on the stalk ring, and
`Stacks.SheafOfModules.DerivedTensorStalk.hasTorAmplitudeCanonical_forall_stalk_iff` gets it
from `StacksDraft.StalkTensor.commRing_stalk_ringSheaf`, which is stated at
`Stacks.SheafOfModules.Tensor.ringSheaf R` for a sheaf `R` of commutative rings. On a ringed
space `W` that is `Stacks.SheafOfModules.Tensor.ringSheaf W.sheaf`, which is
`StrictlyPerfect.structureSheafOfRings W` on the nose —
`Stacks.SheafOfModules.Tensor.ringSheaf` is a reducible abbreviation for
`(sheafCompose _ (forget₂ CommRingCat RingCat)).obj`, and a sheaf is a presheaf together with a
proof — but `rfl` here is a default-transparency, not a reducible, equality. So both the
equality and the instances are recorded at *both* spellings; a consumer never has to make
instance search cross between them.

The crossing has to be made by `rfl` or `change`, never by `rw`. Rewriting
`AlgebraicGeometry.RingedSpace.stalkFunctor_eq_tensorRingSheaf` inside a term such as
`(stalkFunctor (structureSheafOfRings W) y).mapDerivedCategory` fails with *motive is not type
correct*: the exactness instances `CategoryTheory.Functor.mapDerivedCategory` takes are
instances *of the functor being abstracted*, so the motive does not typecheck. Both sides are
the same term, so `rfl` discharges the equality and `change` moves a goal across.

Note that `AlgebraicGeometry.RingedSpace.structureSheafOfRings_eq_ringSheaf` of
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/PushforwardOXMod.lean` is the same bridge for a
*third* spelling, `structureSheafRing`; hence the longer name here.

**Universes.** Everything is in a single universe `u`: the stalk API for sheaves of modules on
a space puts the space, the rings and the module sections in one universe, as recorded in
`StacksFrontier/Topology/Sheaves/Modules/StalkRestrictOpen.lean`, and
`AlgebraicGeometry.RingedSpace.restrictModules` is stated for
`AlgebraicGeometry.RingedSpace.{u, u}`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open StrictlyPerfect

universe u

namespace AlgebraicGeometry.RingedSpace

variable (W : AlgebraicGeometry.RingedSpace.{u, u})

/-! ### The competing spellings -/

/-- **The sheaf of rings underlying a ringed space, in the two spellings this development uses
for it, is one sheaf.** `StrictlyPerfect.structureSheafOfRings W` pairs the presheaf
`W.presheaf ⋙ forget₂ CommRingCat RingCat` with its sheaf condition directly, while
`Stacks.SheafOfModules.Tensor.ringSheaf W.sheaf` applies
`CategoryTheory.sheafCompose _ (forget₂ CommRingCat RingCat)` to the structure sheaf; the sheaf
condition is a proposition, so the two agree on the nose.

The second spelling is the one the Tor-amplitude API is stated at — see
`Stacks.SheafOfModules.DerivedTensorStalk.hasTorAmplitudeCanonical_forall_stalk_iff` — and the
first is the one the stalk comparison across restriction to an open is stated at, so a consumer
of both has to cross between them. -/
theorem structureSheafOfRings_eq_tensorRingSheaf :
    structureSheafOfRings W = Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} W.sheaf :=
  rfl

/-- **The stalk functor of a ringed space does not depend on which spelling of the sheaf of
rings it is read at.** This is
`AlgebraicGeometry.RingedSpace.structureSheafOfRings_eq_tensorRingSheaf` applied to
`AlgebraicGeometry.SheafOfModules.stalkFunctor`; both sides are literally the same functor, so
a consumer crossing between the two spellings never needs to transport along an isomorphism. -/
theorem stalkFunctor_eq_tensorRingSheaf (y : W.carrier) :
    AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafOfRings W) y =
      AlgebraicGeometry.SheafOfModules.stalkFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} W.sheaf) y :=
  rfl

/-- **Restriction of `𝒪_W`-modules to an open has two definitions in this development, and they
are the same functor.** `StrictlyPerfect.restrictModules` restricts the underlying presheaf of
modules along `V ↦ U.isOpenEmbedding.functor.obj V`, while
`AlgebraicGeometry.RingedSpace.restrictModules` is the pushforward along the identity of the
structure sheaf of the open subspace; the two are the same construction on the nose. -/
theorem strictlyPerfectRestrictModules_eq (U : Opens W.carrier) :
    StrictlyPerfect.restrictModules.{u, u, u} W U =
      AlgebraicGeometry.RingedSpace.restrictModules.{u, u} W U :=
  rfl

/-! ### Exactness of restriction to an open -/

/-- **Restriction of `𝒪_W`-modules to an open subspace preserves finite limits**, registered as
an instance at the `StrictlyPerfect.restrictModules` spelling. The content is
`StrictlyPerfect.preservesFiniteLimits_restrictModules`. -/
instance preservesFiniteLimits_strictlyPerfectRestrictModules (U : Opens W.carrier) :
    PreservesFiniteLimits (StrictlyPerfect.restrictModules.{u, u, u} W U) :=
  StrictlyPerfect.preservesFiniteLimits_restrictModules.{u} U

/-- **Restriction of `𝒪_W`-modules to an open subspace preserves finite colimits**, registered
as an instance at the `StrictlyPerfect.restrictModules` spelling. The content is
`StrictlyPerfect.preservesFiniteColimits_restrictModules`. -/
instance preservesFiniteColimits_strictlyPerfectRestrictModules (U : Opens W.carrier) :
    PreservesFiniteColimits (StrictlyPerfect.restrictModules.{u, u, u} W U) :=
  StrictlyPerfect.preservesFiniteColimits_restrictModules.{u} U

/-- **Restriction of `𝒪_W`-modules to an open subspace is additive**, registered as an instance
at the `AlgebraicGeometry.RingedSpace.restrictModules` spelling. The two spellings are the same
functor by `AlgebraicGeometry.RingedSpace.strictlyPerfectRestrictModules_eq`. -/
instance additive_restrictModules (U : Opens W.carrier) :
    (AlgebraicGeometry.RingedSpace.restrictModules.{u, u} W U).Additive :=
  inferInstanceAs (StrictlyPerfect.restrictModules.{u, u, u} W U).Additive

/-- **Restriction of `𝒪_W`-modules to an open subspace preserves finite limits**, registered as
an instance at the `AlgebraicGeometry.RingedSpace.restrictModules` spelling. The two spellings
are the same functor by `AlgebraicGeometry.RingedSpace.strictlyPerfectRestrictModules_eq`. -/
instance preservesFiniteLimits_restrictModules (U : Opens W.carrier) :
    PreservesFiniteLimits (AlgebraicGeometry.RingedSpace.restrictModules.{u, u} W U) :=
  StrictlyPerfect.preservesFiniteLimits_restrictModules.{u} U

/-- **Restriction of `𝒪_W`-modules to an open subspace preserves finite colimits**, registered
as an instance at the `AlgebraicGeometry.RingedSpace.restrictModules` spelling. The two
spellings are the same functor by
`AlgebraicGeometry.RingedSpace.strictlyPerfectRestrictModules_eq`. -/
instance preservesFiniteColimits_restrictModules (U : Opens W.carrier) :
    PreservesFiniteColimits (AlgebraicGeometry.RingedSpace.restrictModules.{u, u} W U) :=
  StrictlyPerfect.preservesFiniteColimits_restrictModules.{u} U

/-! ### Exactness of the stalk functor of a bare ringed space -/

/-- **The stalk functor of a bare ringed space is additive.** It preserves binary products and
zero morphisms, and a functor between preadditive categories that preserves binary biproducts is
additive. -/
instance additive_stalkFunctor (y : W.carrier) :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafOfRings W) y).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **The stalk functor of a bare ringed space preserves finite limits**, registered as an
instance at the `StrictlyPerfect.structureSheafOfRings` spelling of the sheaf of rings. The
content is `AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits`. -/
instance preservesFiniteLimits_stalkFunctor (y : W.carrier) :
    PreservesFiniteLimits
      (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafOfRings W) y) :=
  AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits _ y

/-- **The stalk functor of a bare ringed space preserves finite colimits**, registered as an
instance at the `StrictlyPerfect.structureSheafOfRings` spelling of the sheaf of rings. It
preserves all colimits, which is Stacks 01AH
(`AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits`). -/
instance preservesFiniteColimits_stalkFunctor (y : W.carrier) :
    PreservesFiniteColimits
      (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafOfRings W) y) :=
  have := AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits
    (structureSheafOfRings W) y
  inferInstance

/-- `AlgebraicGeometry.RingedSpace.additive_stalkFunctor` at the
`Stacks.SheafOfModules.Tensor.ringSheaf` spelling of the sheaf of rings, which is the spelling
the Tor-amplitude API is stated at. -/
instance additive_stalkFunctor_tensorRingSheaf (y : W.carrier) :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} W.sheaf) y).Additive :=
  additive_stalkFunctor W y

/-- `AlgebraicGeometry.RingedSpace.preservesFiniteLimits_stalkFunctor` at the
`Stacks.SheafOfModules.Tensor.ringSheaf` spelling of the sheaf of rings, which is the spelling
the Tor-amplitude API is stated at. -/
instance preservesFiniteLimits_stalkFunctor_tensorRingSheaf (y : W.carrier) :
    PreservesFiniteLimits (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} W.sheaf) y) :=
  preservesFiniteLimits_stalkFunctor W y

/-- `AlgebraicGeometry.RingedSpace.preservesFiniteColimits_stalkFunctor` at the
`Stacks.SheafOfModules.Tensor.ringSheaf` spelling of the sheaf of rings, which is the spelling
the Tor-amplitude API is stated at. -/
instance preservesFiniteColimits_stalkFunctor_tensorRingSheaf (y : W.carrier) :
    PreservesFiniteColimits (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} W.sheaf) y) :=
  preservesFiniteColimits_stalkFunctor W y

variable (U : Opens W.carrier) {y : W.carrier}

/-- `AlgebraicGeometry.RingedSpace.additive_stalkFunctor` at a point of an open subspace written
as `⟨y, hy⟩`, which is the spelling
`AlgebraicGeometry.RingedSpace.restrictModulesStalkNatIso` is stated at. -/
instance additive_stalkFunctor_restrict (hy : y ∈ U) :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (structureSheafOfRings (W.restrict U.isOpenEmbedding)) ⟨y, hy⟩).Additive :=
  additive_stalkFunctor _ _

/-- `AlgebraicGeometry.RingedSpace.preservesFiniteLimits_stalkFunctor` at a point of an open
subspace written as `⟨y, hy⟩`, which is the spelling
`AlgebraicGeometry.RingedSpace.restrictModulesStalkNatIso` is stated at. -/
instance preservesFiniteLimits_stalkFunctor_restrict (hy : y ∈ U) :
    PreservesFiniteLimits (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (structureSheafOfRings (W.restrict U.isOpenEmbedding)) ⟨y, hy⟩) :=
  preservesFiniteLimits_stalkFunctor _ _

/-- `AlgebraicGeometry.RingedSpace.preservesFiniteColimits_stalkFunctor` at a point of an open
subspace written as `⟨y, hy⟩`, which is the spelling
`AlgebraicGeometry.RingedSpace.restrictModulesStalkNatIso` is stated at. -/
instance preservesFiniteColimits_stalkFunctor_restrict (hy : y ∈ U) :
    PreservesFiniteColimits (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (structureSheafOfRings (W.restrict U.isOpenEmbedding)) ⟨y, hy⟩) :=
  preservesFiniteColimits_stalkFunctor _ _

/-! ### Commutativity of the stalk ring -/

/-- **The stalk of the structure sheaf of a ringed space, read in `RingCat`, is a commutative
ring**, registered as an instance at the `StrictlyPerfect.structureSheafOfRings` spelling.

Only a `Ring` structure comes with a `RingCat`-valued stalk, and
`StacksDraft.StalkTensor.commRing_stalk` upgrades it for a stalk of a presheaf of the shape
`_ ⋙ forget₂ CommRingCat RingCat`. `(structureSheafOfRings W).obj` *is* such a presheaf, but
only after unfolding a `def`, which instance search does not do. -/
instance commRing_stalk_structureSheafOfRings (y : W.carrier) :
    CommRing (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (structureSheafOfRings W).obj y)) :=
  StacksDraft.StalkTensor.commRing_stalk W.presheaf y

/-- `AlgebraicGeometry.RingedSpace.commRing_stalk_structureSheafOfRings` at the
`Stacks.SheafOfModules.Tensor.ringSheaf` spelling of the sheaf of rings, for a ringed space.
`StacksDraft.StalkTensor.commRing_stalk_ringSheaf` is this statement for a sheaf of commutative
rings on a `TopCat`; it is not found for a ringed space, because the topology of the carrier of
a presheafed space is not reducibly `TopCat.str` of a `TopCat`. -/
instance commRing_stalk_tensorRingSheaf (y : W.carrier) :
    CommRing (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} W.sheaf).obj y)) :=
  commRing_stalk_structureSheafOfRings W y

/-- `AlgebraicGeometry.RingedSpace.commRing_stalk_structureSheafOfRings` at a point of an open
subspace written as `⟨y, hy⟩`, which is the spelling
`AlgebraicGeometry.RingedSpace.restrictModulesStalkRingIso` is stated at. -/
instance commRing_stalk_structureSheafOfRings_restrict (hy : y ∈ U) :
    CommRing (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (structureSheafOfRings (W.restrict U.isOpenEmbedding)).obj ⟨y, hy⟩)) :=
  commRing_stalk_structureSheafOfRings _ _

end AlgebraicGeometry.RingedSpace

end
