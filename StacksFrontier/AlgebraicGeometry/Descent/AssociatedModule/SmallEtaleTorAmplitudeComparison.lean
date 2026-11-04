module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSmallModelPullbackExact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.DerivedPullbackReflection
import StacksCore.Tactic.StacksAttribute

/-!
# Tor amplitude across the comparison `ε` of the small étale and the Zariski site

Let `S` be a scheme and let `ε : S_étale ⟶ S_Zar` be the comparison morphism of ringed topoi of
Stacks 08H7, read through the `Type u`-presented model
`AlgebraicGeometry.SmallEtale.smallModelRingedTopos` of the small étale ringed topos so that
both of its ringed topoi are `AlgebraicGeometry.RingedTopos.{u, u, u}`.  Stacks 08HF asserts, for
an object `E` of `D(𝒪_S)`:

1. `E` has Tor amplitude in `[a, b]` **iff** `Lε^*E` has Tor amplitude in `[a, b]`;
2. `E` has finite Tor dimension **iff** `Lε^*E` has finite Tor dimension.

Both biconditionals are carried here.  The direction Stacks 08H5 supplies is
`AlgebraicGeometry.SmallEtale.hasTorAmplitude_derivedPullback_toZariskiSmallModel`, respectively
`AlgebraicGeometry.SmallEtale.hasFiniteTorDimension_derivedPullback_toZariskiSmallModel`.  The
converse is
`Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_of_hasTorAmplitude_derivedPullback`,
respectively its finite-dimension form, applied to `ε` on the model: that statement asks of the
morphism exactly the two assertions Stacks 08H8 makes about `ε` — that the degreewise pullback of
sheaves of modules is exact and that it detects the zero sheaf — and both are available at `ε`
read on the model, as
`AlgebraicGeometry.SmallEtale.preservesFiniteLimits_pullbackTopos_toZariskiSmallModelHom`,
`AlgebraicGeometry.SmallEtale.preservesFiniteColimits_pullbackTopos_toZariskiSmallModelHom` and
`AlgebraicGeometry.SmallEtale.isZero_of_isZero_pullbackTopos_toZariskiSmallModelHom`.

## Main results

* `AlgebraicGeometry.SmallEtale.hasTorAmplitude_derivedPullback_of_hasTorAmplitude`:
  **Stacks 08HF, clause (1)** — `E` has Tor amplitude in `[a, b]` iff `Lε^*E` does.
* `AlgebraicGeometry.SmallEtale.hasFiniteTorDimension_derivedPullback_of_hasFiniteTorDimension`:
  **Stacks 08HF, clause (2)** — `E` has finite Tor dimension iff `Lε^*E` does.

## Implementation notes

**Why the statements are read on the model.**  Stacks 08HF is a statement about the small étale
ringed topos `AlgebraicGeometry.SmallEtale.ringedTopos`, which is an
`AlgebraicGeometry.RingedTopos.{u, u + 1, u}` — its sections lie strictly below its objects — and
that is the one universe shape in which the Stacks 06YY chain constructing `Lε^*` is unavailable.
`AlgebraicGeometry.SmallEtale.smallModelRingedTopos` is the equivalent
`AlgebraicGeometry.RingedTopos.{u, u, u}` presentation built for that reason, and
`AlgebraicGeometry.SmallEtale.toZariskiSmallModelHom` is `ε` read on it; the derived pullback
`Lε^*` written below is the one that presentation carries.  Stacks 08H8 is proved on the small
étale site itself, and
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleSmallModelPullbackExact.lean`
carries it across to the model along the equivalence of the two presentations; that transport is
the only thing the converse needed beyond
`Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_of_hasTorAmplitude_derivedPullback`.

**The arbitrariness of the two derived tensor product data.**  Tor amplitude is measured against
a derived tensor product datum, and the statements below quantify over an arbitrary datum on
either side rather than fixing the canonical one, so they are formally stronger than the
source's, whose `⊗^{\mathbf L}` is the canonical datum
`Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct`.  Both directions survive that
strengthening, and for different reasons.  Forwards it is inherited from Stacks 08H5: the
direction of Stacks 08G1 that Stacks 08H5 uses — a bounded complex of flat modules has Tor
amplitude in its support interval — takes no input about the datum.  Backwards it is because the
argument is run on K-flat representatives, where the `comparisonRight` field of a datum pins its
value: the structure of `Stacks.SheafOfModules.DerivedTensorProduct` says that tensoring with a
K-flat complex *is* the total tensor complex, so no comparison of two data, and in particular no
comparison with the datum that Stacks 07A4 is stated for, is needed.

**Stacks 07A4 is not used.**  `AlgebraicGeometry.SmallEtale.derivedPullbackTensorIsoSmallModel`
is the derived flat base change for `ε` on the model, which is how the source argues the
converse; it is stated for
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`, a second structure with the same
fields as `Stacks.SheafOfModules.DerivedTensorProduct` and no conversion to it in this tree.
The computation on representatives described above avoids that conversion, so the gap is not on
the path to Stacks 08HF and nothing here depends on 07A4.

**Why the `HasDerivedCategory` instance is given a raised priority, and why the `iff` is written
with the pullback on the left.**  The hom universe of `D(𝒪)` is not a free parameter here: the
derived pullback of Stacks 06YY is constructed at `HasDerivedCategory.standard`, and both sides
of each biconditional must be read at that same localization.  Two things conspire against
instance search finding it.  The transitive imports of this module put a second
`HasDerivedCategory` instance for these categories in scope, at a different hom universe, and
nothing distinguishes them to instance search; raising the priority of `standard` — which is the
one `Lε^*` is built at — picks the right one.  And the universe of a binder is fixed when the
binder is elaborated, before the conclusion is seen, so the side of the `iff` that mentions
`Lε^*` has to come first for the derived tensor product data and the object `E` to be read at the
localization `Lε^*` lives at.  A biconditional is symmetric, so neither choice changes what is
asserted.

## References

* [Stacks Project, Tag 08HF](https://stacks.math.columbia.edu/tag/08HF)
* [Stacks Project, Tag 08H5](https://stacks.math.columbia.edu/tag/08H5)
* [Stacks Project, Tag 08H7](https://stacks.math.columbia.edu/tag/08H7)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.SheafOfModules Stacks.SheafOfModules.DerivedTensorProduct

universe u

attribute [local instance 20000] HasDerivedCategory.standard

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 08HF, clause (1).**  An object `E` of `D(𝒪_S)` has Tor amplitude in `[a, b]` for a
derived tensor product datum `T` on the small Zariski ringed site of `S` **if and only if** its
derived pullback `Lε^*E` along the comparison `ε` of Stacks 08H7, read on the `Type u`-presented
model of the small étale ringed topos, has Tor amplitude in `[a, b]` for a derived tensor product
datum `T'` on the model.  Both data are arbitrary.

Forwards this is Stacks 08H5.  Backwards it is
`Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_of_hasTorAmplitude_derivedPullback`,
whose two inputs about `ε_model` — that the degreewise pullback of sheaves of modules is exact
and that it detects the zero sheaf — are the two assertions of Stacks 08H8, read on the model in
`AlgebraicGeometry.SmallEtale.preservesFiniteLimits_pullbackTopos_toZariskiSmallModelHom` and
`AlgebraicGeometry.SmallEtale.isZero_of_isZero_pullbackTopos_toZariskiSmallModelHom`. -/
@[stacks 08HF "clause (1): `E` has tor amplitude in `[a, b]` ⟺ `ε^*E` has tor amplitude in
  `[a, b]`, for `ε` the comparison morphism of Equation 75.4.0.1 (Stacks 08H7) read on the
  `Type u`-presented model `AlgebraicGeometry.SmallEtale.smallModelRingedTopos` of the small
  étale ringed topos, and `ε^*` its derived pullback.  Stated for an arbitrary derived tensor
  product datum on either side rather than for the canonical one.  Clause (2) is
  `AlgebraicGeometry.SmallEtale.hasFiniteTorDimension_derivedPullback_of_hasFiniteTorDimension`"]
public theorem hasTorAmplitude_derivedPullback_of_hasTorAmplitude
    (T : DerivedTensorProduct S.zariskiRingedTopos.toRingedSite)
    (T' : DerivedTensorProduct (smallModelRingedTopos B S hS).toRingedSite)
    (E : RingedSite.DerivedModules S.zariskiRingedTopos.toRingedSite) (a b : ℤ) :
    HasTorAmplitude T' ((derivedPullback (toZariskiSmallModelHom B S hS)).obj E) a b ↔
      HasTorAmplitude T E a b :=
  ⟨hasTorAmplitude_of_hasTorAmplitude_derivedPullback (toZariskiSmallModelHom B S hS)
      (isMorphismOfSites_toZariskiSmallModelHom_u B S hS)
      (isZero_of_isZero_pullbackTopos_toZariskiSmallModelHom B S hS) T T' E a b,
    hasTorAmplitude_derivedPullback_toZariskiSmallModel B S hS T T' E a b⟩

/-- **Stacks 08HF, clause (2).**  An object `E` of `D(𝒪_S)` has finite Tor dimension for a
derived tensor product datum `T` on the small Zariski ringed site of `S` **if and only if** its
derived pullback `Lε^*E` has finite Tor dimension for a derived tensor product datum `T'` on the
model.  Both data are arbitrary.

This is clause (1) with the interval existentially quantified: an interval containing the Tor
amplitude of one of the two objects contains that of the other. -/
@[stacks 08HF "clause (2): `E` has finite tor dimension ⟺ `ε^*E` has finite tor dimension, for
  `ε` the comparison morphism of Equation 75.4.0.1 (Stacks 08H7) read on the `Type u`-presented
  model `AlgebraicGeometry.SmallEtale.smallModelRingedTopos` of the small étale ringed topos, and
  `ε^*` its derived pullback.  Stated for an arbitrary derived tensor product datum on either
  side rather than for the canonical one.  Clause (1) is
  `AlgebraicGeometry.SmallEtale.hasTorAmplitude_derivedPullback_of_hasTorAmplitude`"]
public theorem hasFiniteTorDimension_derivedPullback_of_hasFiniteTorDimension
    (T : DerivedTensorProduct S.zariskiRingedTopos.toRingedSite)
    (T' : DerivedTensorProduct (smallModelRingedTopos B S hS).toRingedSite)
    (E : RingedSite.DerivedModules S.zariskiRingedTopos.toRingedSite) :
    HasFiniteTorDimension T' ((derivedPullback (toZariskiSmallModelHom B S hS)).obj E) ↔
      HasFiniteTorDimension T E :=
  ⟨hasFiniteTorDimension_of_hasFiniteTorDimension_derivedPullback
      (toZariskiSmallModelHom B S hS) (isMorphismOfSites_toZariskiSmallModelHom_u B S hS)
      (isZero_of_isZero_pullbackTopos_toZariskiSmallModelHom B S hS) T T' E,
    hasFiniteTorDimension_derivedPullback_toZariskiSmallModel B S hS T T' E⟩

end AlgebraicGeometry.SmallEtale

end
