module

public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.DevissageNoetherian.EmptySupportVanishing
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.IsoTransport
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.ProperClosedSubsetCompact
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperSupportPerfection
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.LocallyFiniteCohomology
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.RestrictHomology
public import StacksFrontier.AlgebraicGeometry.Perfect.TorDimension
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedScalarRestriction
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.AlgebraicGeometry.TensorCoherence.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherenceClosure
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreeRank
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import StacksFrontier.Topology.Sheaves.Modules.StalkExactness
public import StacksFrontier.Topology.Sheaves.Modules.SupportCoproduct
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DerivedSymmetryAndUnit
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietorisAndLimits.InverseSystemsOnASpace
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TensorProduct
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
import StacksCore.Tactic.StacksAttribute

/-!
# Producing perfect complexes: the derived direct image

Let `S` be a Noetherian scheme and `f : X ⟶ S` a morphism locally of finite type.  This file
states the two results of the section *Producing perfect complexes* that make a derived direct
image perfect:

* if `E` is a perfect object of `D(𝒪_X)` and `𝒢` is a bounded complex of coherent
  `𝒪_X`-modules, flat over `S`, whose support is proper over `S`, then
  `Rf_*(E ⊗^L_{𝒪_X} 𝒢)` is a perfect object of `D(𝒪_S)`; and
* if `f` is flat and proper and `E` is perfect, then `Rf_*E` is perfect.

## Main definitions

* `Stacks.Cohomology.PerfectPushforward.PushforwardPerfectionInput` is the hypothesis of
  [Stacks, Tag 08EV] on an object of `D(𝒪_X)`: bounded with coherent cohomology sheaves, each of
  those sheaves supported on a closed subset proper over `S`, and of finite Tor dimension as an
  object of `D(f⁻¹𝒪_S)`.
* `Stacks.Cohomology.PerfectPushforward.PushforwardPerfectionCriterion` is the conclusion of
  [Stacks, Tag 08EV] read as a property of a direct-image functor: it carries every object
  satisfying `PushforwardPerfectionInput` to a perfect object of `D(𝒪_S)`.
* `Stacks.Cohomology.PerfectPushforward.PushforwardCoherenceResidue` and
  `Stacks.Cohomology.PerfectPushforward.PushforwardTorDimensionResidue` are the two residues of
  the proof of [Stacks, Tag 08EV] in
  `StacksFrontier/AlgebraicGeometry/Perfect/ProperSupportPerfection.lean`, quantified over the
  objects the criterion must handle.  They are what the two results below carry in place of that
  tag.
* `Stacks.Cohomology.PerfectPushforward.FlatProperSupportComplex` is the hypothesis on `𝒢` in
  [Stacks, Tag 0DJQ]: bounded, coherent in each degree, flat over `S` in each degree, and with
  all degrees supported on one closed subset proper over `S`.
* `Stacks.Cohomology.PerfectPushforward.structureComplex` is `𝒪_X` in degree zero, the complex
  `𝒢` of [Stacks, Tag 0DJQ] in the case of [Stacks, Tag 0B6F].
* `Stacks.Cohomology.PerfectPushforward.TensorPushforwardData` and
  `Stacks.Cohomology.PerfectPushforward.FlatProperPushforwardData` bundle the inputs of the two
  tags that this file does not derive; each field says so in its own docstring.

The derived direct image itself is `Stacks.Cohomology.ProperSupportPerfection.derivedPushforwardOX`
of `StacksFrontier/AlgebraicGeometry/Perfect/ProperSupportPerfection.lean`, where the conditional
form of [Stacks, Tag 08EV] that this file consumes concludes about it.

## Main results

* `Stacks.Cohomology.PerfectPushforward.pushforwardPerfectionCriterion_of_residues` derives the
  criterion from the conditional form of [Stacks, Tag 08EV] in
  `StacksFrontier/AlgebraicGeometry/Perfect/ProperSupportPerfection.lean`, leaving that form's two
  residues as the hypotheses.
* `Stacks.Cohomology.PerfectPushforward.isPerfect_derivedPushforward_derivedTensor` is a
  conditional form of [Stacks, Tag 0DJQ]; the two residues above and one of the four clauses of
  [Stacks, Tag 08EV]'s hypothesis for `E ⊗^L_{𝒪_X} 𝒢` are what it assumes.  It is not the
  registration of that tag: [Stacks, Tag 0DJQ] is proved with none of these inputs, as
  `Stacks.Cohomology.PerfectPushforward.isPerfect_derivedPushforward_derivedTensor_of_isPerfect`
  (`StacksFrontier/AlgebraicGeometry/Perfect/PerfectPushforwardDerivedTensor.lean`) and, at the
  canonical derived tensor product, as the registered
  `Stacks.Cohomology.PerfectPushforward.isPerfect_derivedPushforward_derivedTensorProductFunctor`
  (`StacksFrontier/AlgebraicGeometry/Perfect/PerfectPushforwardCanonicalTensor.lean`).
* `Stacks.Cohomology.PerfectPushforward.exists_local_tensorComplex_models` is the geometric step
  of [Stacks, Tag 0DJQ], and is proved: `E ⊗^L_{𝒪_X} 𝒢` is represented by `Tot(A ⊗_{𝒪_X} 𝒢)`
  for a K-flat `A`, and on a covering of `X` that complex is, in the derived category, the total
  tensor complex of a strictly perfect complex with the restriction of `𝒢`.
* `Stacks.Cohomology.PerfectPushforward.supp_homology_derivedTensor_subset` is the support clause
  of [Stacks, Tag 0DJQ], and is proved: the cohomology sheaves of `E ⊗^L_{𝒪_X} 𝒢` are supported
  wherever the terms of `𝒢` are.
* `Stacks.Cohomology.PerfectPushforward.exists_isZero_homology_derivedTensor` is the boundedness
  clause of [Stacks, Tag 0DJQ], and is proved: only finitely many cohomology sheaves of
  `E ⊗^L_{𝒪_X} 𝒢` are nonzero.
* `Stacks.Cohomology.PerfectPushforward.isCoherent_homology_derivedTensor` is the coherence clause
  of [Stacks, Tag 0DJQ], and is proved: every cohomology sheaf of `E ⊗^L_{𝒪_X} 𝒢` is coherent.
  Together with the two previous results it is why
  `Stacks.Cohomology.PerfectPushforward.TensorPushforwardData` carries one clause of
  [Stacks, Tag 08EV]'s hypothesis rather than four, the other three being assembled by
  `Stacks.Cohomology.PerfectPushforward.TensorPushforwardData.input` out of
  `Stacks.Cohomology.PerfectPushforward.TensorPushforwardData.bounded`,
  `Stacks.Cohomology.PerfectPushforward.TensorPushforwardData.isCoherent` and that support
  clause.
* `Stacks.Cohomology.PerfectPushforward.isPerfect_derivedPushforward_of_flatProper` is
  [Stacks, Tag 0B6F], obtained from the previous result at `𝒢 = 𝒪_X` in degree zero.  The
  reduction is proved; the results below are what it consists of.
* `Stacks.Cohomology.PerfectPushforward.isProperOver_top_of_isProper`: all of `X` is proper over
  `S` when `f` is.
* `Stacks.Cohomology.PerfectPushforward.exists_isZero_homology_of_isProper` is the boundedness
  clause for [Stacks, Tag 0B6F], and is proved: a proper `f` over a Noetherian `S` makes `X`
  quasi-compact, and the cohomology of a perfect object on a quasi-compact space is bounded.
  Together with
  `Stacks.Cohomology.PerfectPushforward.FlatProperPushforwardData.isCoherent`, which is
  [Stacks, Tag 0FEP] at the locally Noetherian `X` that a proper morphism to a Noetherian base
  produces, it is why
  `Stacks.Cohomology.PerfectPushforward.FlatProperPushforwardData` likewise carries one
  clause rather than four.
* `Stacks.Cohomology.PerfectPushforward.isCoherent_structureComplex_X`,
  `Stacks.Cohomology.PerfectPushforward.isFlatOver_structureComplex` and
  `Stacks.Cohomology.PerfectPushforward.flatProperSupportComplex_structureComplex`: `𝒪_X` in
  degree zero is a bounded complex of coherent `𝒪_X`-modules, flat over `S`, with support proper
  over `S`, hence a complex of the kind [Stacks, Tag 0DJQ] admits.
* `Stacks.Cohomology.PerfectPushforward.isFlatOver_structureModule`: the structure sheaf of `X`
  is flat over `S` when `f` is flat, which is [Stacks, Tag 02N3] read through the stalk
  comparisons that the three spellings of the structure sheaf force.
* `Stacks.Cohomology.PerfectPushforward.tensorStructureComplexIso`: the isomorphism
  `E ⊗^L_{𝒪_X} 𝒪_X ≅ E`, read off the unit constraint of [Stacks, Tag 0FPT].
* `Stacks.Cohomology.PerfectPushforward.PushforwardPerfectionInput.of_iso` and
  `Stacks.Cohomology.PerfectPushforward.supp_eq_of_iso_ringedSpace`: the hypothesis of
  [Stacks, Tag 08EV]
  depends only on the isomorphism class of the object, which is what lets the unit constraint
  carry it from `E` to `E ⊗^L_{𝒪_X} 𝒪_X`.

## Implementation notes

**Which notion of perfectness.**  `AlgebraicGeometry.RingedSpace.IsPerfect`, the predicate of
[Stacks, Tag 08CM] on an object of the derived category of `𝒪`-modules on a ringed space, read
at `S.toRingedSpace`.  It is the notion the rest of the perfect-complex development on a ringed
space uses — [Stacks, Tag 08DP] and [Stacks, Tag 09J5] among others — and `D(𝒪_S)` for a scheme
`S` is `D(𝒪_{S.toRingedSpace})`.  No second notion is introduced here.

**What is carried.**  Both source proofs run through [Stacks, Tag 08EV]: the statement that a
bounded object with coherent cohomology, proper cohomological support and finite Tor dimension
over `f⁻¹𝒪_S` has perfect derived direct image.  That tag is proved unconditionally as
`Stacks.AlgebraicGeometry.ProperSupportCoherent.isPerfect_derivedPushforward_of_isProperOver_supp`,
at the `AlgebraicGeometry.Scheme.Modules` spelling and for the canonical derived tensor product
on `(X, f⁻¹𝒪_S)`.  This file is stated instead at the `StrictlyPerfect.OXMod` spelling with an
arbitrary certified derived tensor datum `D`, for which the tag is available only in the
conditional form
`Stacks.Cohomology.ProperSupportPerfection.isPerfect_derivedPushforward_of_properSupport`, under
two named residues, and
`Stacks.Cohomology.PerfectPushforward.pushforwardPerfectionCriterion_of_residues` carries that
theorem to the criterion `PushforwardPerfectionCriterion` of this file with no comparison needed:
the four clauses of `PushforwardPerfectionInput` are literally that theorem's four hypotheses,
and its `AlgebraicGeometry.IsLocallyNoetherian` assumption on `S` is weaker than the
`AlgebraicGeometry.IsNoetherian` the two results below already make.  So the two results carry
`PushforwardCoherenceResidue` and `PushforwardTorDimensionResidue` instead of the criterion
itself; those are [Stacks, Tag 08E2] for the direct-image functor and the source's closing
Tor-dimension estimate.  Both are proved inside the proof of the complete theorem above; what
stands between them and this file is the spelling, and above all the datum `D`, whose underived
tensor product is a field rather than the tensor product of modules, so that Tor dimension for
`D` does not give Tor dimension for the canonical derived tensor product.  Restating the two
results below at the canonical derived tensor product would let them apply the complete theorem.

The clauses of the criterion are `PushforwardPerfectionInput`, written in the vocabulary of the
repository:
boundedness and coherence of the cohomology sheaves ([Stacks, Tag 01BV]),
`AlgebraicGeometry.IsProperOver` for the support ([Stacks, Tag 0CYM]) applied to a closed subset
containing `SheafOfModules.supp`, and
`AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring.HasFiniteTorDimension`
([Stacks, Tag 08CG]) applied to `AlgebraicGeometry.Scheme.Hom.derivedScalarRestriction`, which is
the functor `D(𝒪_X) ⥤ D(f⁻¹𝒪_S)`.

[Stacks, Tag 0DJQ] carries a second thing: the
verification that `E ⊗^L_{𝒪_X} 𝒢` satisfies those clauses, which is the content of that tag.  The
source's argument is one geometric step followed by appeals to locality: locally `E` is a
finite complex of finite free modules, so locally `E ⊗^L_{𝒪_X} 𝒢` is a finite complex whose terms
are finite direct sums of the `𝒢^i`; coherence of the cohomology sheaves, containment of their
supports in the support of `𝒢`, boundedness, and finiteness of the Tor dimension over `f⁻¹𝒪_S`
then all read off that local description, the last from flatness of the `𝒢^i` over `S`.

**The geometric step is proved here**, as
`Stacks.Cohomology.PerfectPushforward.exists_local_tensorComplex_models`: a K-flat resolution of
a representative of `E` gives a global complex `A` with
`Q(Tot(A ⊗_{𝒪_X} 𝒢)) ≅ E ⊗^L_{𝒪_X} 𝒢`, and on each member `U` of a covering of `X` the
restriction `Tot(A ⊗ 𝒢)|_U` is isomorphic in `D(𝒪_U)` to `Tot(P ⊗ 𝒢|_U)` for a strictly perfect
`P`.  It is `AlgebraicGeometry.RingedSpace.isPerfect_derivedTensorProduct`'s argument with only
one factor perfect, so the K-flat comparison of
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct` is needed on one side only
(`comparisonLeft`) and `𝒢` — flat over `S`, not over `𝒪_X` — is carried along unresolved by
`Stacks.Cohomology.RestrictionTensor.restrictComplexTensorIso`.

**Three of the four clauses are proved, here.**  The support clause is
`Stacks.Cohomology.PerfectPushforward.supp_homology_derivedTensor_subset`, and it needs no local
model at all: `Tot(A ⊗_{𝒪_X} 𝒢)` is a *global* representative, every one of its terms is a
coproduct of modules `A^p ⊗_{𝒪_X} 𝒢^q`, and off the support of `𝒢` each of those has subsingleton
stalk by the stalk of a tensor product ([Stacks, Tag 01CB],
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso`), whence so does the cohomology,
because the stalk functor is exact.  The boundedness clause is
`Stacks.Cohomology.PerfectPushforward.exists_isZero_homology_derivedTensor` and the coherence
clause is `Stacks.Cohomology.PerfectPushforward.isCoherent_homology_derivedTensor`, both described
below.  The one remaining clause is carried, as the
`hasFiniteTorDimension` field of
`Stacks.Cohomology.PerfectPushforward.TensorPushforwardData`, and needs a further
ingredient that this repository does not have at the `StrictlyPerfect.OXMod` spelling.

**Coherence is proved**, as
`Stacks.Cohomology.PerfectPushforward.isCoherent_homology_derivedTensor`.  Like boundedness it
needs the local models: `A` is only K-flat, so the terms of the global `Tot(A ⊗ 𝒢)` are not
coherent, whereas the terms of `Tot(P ⊗ 𝒢|_U)` for a *strictly perfect* `P` are coproducts of
modules `P^p ⊗ 𝒢^q`, each coherent — `P^p` is a direct summand of a finite free module, hence
coherent by
`Stacks.AlgebraicGeometry.PerfectCohomology.isCoherent_of_isDirectSummandOfFiniteFree`, and then
`AlgebraicGeometry.SheafOfModules.tensorSheaf_isCoherent` ([Stacks, Tag 01CE] (6)) applies.  Only
finitely many of those coproduct summands are nonzero, because `P` is bounded and the pair
`(p, q)` with `p + q = n` is determined by `p`; that is
`Stacks.Cohomology.PerfectPushforward.prop_mapBifunctor_X`, whose coproduct bookkeeping is
`Stacks.Cohomology.PerfectPushforward.sigmaSubtypeIsoOfIsZero`.  Coherent modules form a weak
Serre class (`SheafOfModules.coherentModules_isWeakSerreClass`), so
`CategoryTheory.ObjectProperty.prop_homology` gives coherence of the cohomology of
`Tot(P ⊗ 𝒢|_U)`; the restricted cohomology sheaf of `E ⊗^L_{𝒪_X} 𝒢` is that cohomology by
`Stacks.Cohomology.PerfectPushforward.restrictHomologyLocalModelIso`.

Locality is `Stacks.AlgebraicGeometry.PerfectCohomology.isCoherent_of_cover_restrict`, condition
(5) of [Stacks, Tag 01XZ] on a locally Noetherian scheme, which `X` is because `f` is locally of
finite type and `S` is Noetherian.  It is stated for
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` while the local models of this file restrict
along `AlgebraicGeometry.RingedSpace.restrictModules`; the two are identified by
`Stacks.AlgebraicGeometry.PerfectCohomology.restrictModulesIsoRestrict`, which is itself built
from the two `Iso.refl`s
`AlgebraicGeometry.RingedSpace.restrictModulesIsoOverComp`
(`StacksFrontier/AlgebraicGeometry/PseudoCoherent/StrictlyPerfectLocalRep.lean:332`) and
`AlgebraicGeometry.RingedSpace.restrictModulesIsoOverComp`
(`StacksFrontier/AlgebraicGeometry/PseudoCoherent/BoundedApproximation.lean:153`), so no bridge is
needed here and none should be written.  No transport of the site-level predicate
`Stacks.SheafOfModules.Site.IsCoherent` across an equivalence of sites is needed either: the whole
argument stays at the space-level predicate.  The repository's two space-level coherence classes
are crossed where needed by `SheafOfModules.IsCoherent.stacksIsCoherent` and
`Stacks.SheafOfModules.IsCoherent.rootIsCoherent`.

**Boundedness is proved**, as
`Stacks.Cohomology.PerfectPushforward.exists_isZero_homology_derivedTensor`.  It needs the local
models, for the reason just given — `Tot(A ⊗ 𝒢)` has a nonzero term in every degree, whereas
`Tot(P ⊗ 𝒢|_U)` for a *strictly perfect* `P` has one only between the sum of the two lower bounds
and the sum of the two upper bounds, which is
`Stacks.Cohomology.PerfectPushforward.isZero_homology_localTensorModel`.  That gives one interval
per member of the covering, transported to the restricted cohomology sheaf by
`Stacks.Cohomology.PerfectPushforward.exists_isZero_restrictModules_homology`; the per-member
intervals become one interval because the closed subset carrying `𝒢` is quasi-compact, so
finitely many members cover it, and off that subset the cohomology vanishes by the support clause
above.

The three ingredients.  Quasi-compactness is `AlgebraicGeometry.isCompact_of_isProperOver`
(`StacksFrontier/AlgebraicGeometry/Morphisms/Proper/ProperClosedSubsetCompact.lean:73`): a closed
subset proper over a base with compact space is compact, proved from Mathlib's
`IsProper → UniversallyClosed → QuasiCompact` instance together with
`QuasiCompact.compactSpace_of_compactSpace`, and applying directly in the setting of this file
because `IsNoetherian S` supplies `CompactSpace S` by resolution.  The second ingredient is
vanishing from an empty support, and what once looked like an obstruction here was a spelling
problem: `X.toRingedSpace.restrict U.isOpenEmbedding` and
`(X.restrict U.isOpenEmbedding).toRingedSpace`
are the same term by `rfl` — both are sheafed spaces with the same underlying presheafed space
and a `Prop`-valued sheaf condition — so a scheme-level criterion already applies on the local
models.  In the event no scheme-level copy is used: the proof
reads `IsZero` off an empty support at the natural generality, by
`SheafOfModules.isZero_of_supp_eq_empty`
(`StacksFrontier/AlgebraicGeometry/DevissageNoetherian/EmptySupportVanishing.lean:60`), for a sheaf
of modules over any sheaf of rings on any topological space, which subsumes the two scheme-level
copies in this tree; and the single point of a member at which the support has to be emptied is
removed by `Stacks.AlgebraicGeometry.PerfectCohomology.notMem_supp_of_isZero_restrictModules`.
The third ingredient, the locality step, is the four-step comparison of
`Stacks.Cohomology.PerfectPushforward.exists_isZero_restrictModules_homology`:
`DerivedCategory.homologyFunctorFactors`, at `X` and at the open subspace, turns the two
isomorphisms of derived categories that the local models come as into isomorphisms of the
cohomology of the representing complexes, and
`Stacks.AlgebraicGeometry.PerfectCohomology.mapHomologyIso` supplies the one fact about
restriction that is used, namely that it is exact and therefore commutes with the cohomology of a
complex.  So the comparison passes through no derived functor of the restriction, and neither
`AlgebraicGeometry.RingedSpace.isZero_of_restrictModules` nor
`AlgebraicGeometry.RingedSpace.derivedRestrictModulesObjQIso` is needed; the first is replaced by
the empty-support criterion above, which is what lets a cover of the *support* stand in for a
cover of `X`.

Only the boundedness and support fields of `FlatProperSupportComplex` enter this clause;
coherence and flatness of the `𝒢^q` are not used, which is why an argument of the same shape
settles the boundedness clause for [Stacks, Tag 0B6F]
(`Stacks.Cohomology.PerfectPushforward.exists_isZero_homology_of_isProper`), there with
compactness of `X` itself in place of compactness of the support, and with the local models of
`E` itself in place of those of `E ⊗^L_{𝒪_X} 𝒢`.

The Tor-dimension clause needs the same local description transported through
`AlgebraicGeometry.Scheme.Hom.derivedScalarRestriction`, and then flatness of the `𝒢^q` over `S`
converted into a Tor-amplitude interval.  At the `Stacks.Cohomology.TorAmplitude` predicate both
are done elsewhere in the tree: `AlgebraicGeometry.exists_hasTorAmplitudeOver_derivedTensor`
bounds the Tor amplitude of `E ⊗^L 𝒢` over the base from flatness of the `𝒢^q` over `S`, and
`Stacks.Cohomology.PerfectPushforward.hasFiniteTorDimension_derivedTensor`
(`StacksFrontier/AlgebraicGeometry/Perfect/PerfectPushforwardDerivedTensor.lean`) is the clause
there.  What keeps it carried in this file is only the spelling:
`AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring.HasFiniteTorDimension` — which
is what the clause is written with here, at an arbitrary certified tensoring `D` — has no
comparison with the `Stacks.Cohomology.TorAmplitude` predicate.

**What is proved.**  The reduction of [Stacks, Tag 0B6F] to [Stacks, Tag 0DJQ].  A flat proper
morphism to a Noetherian scheme is locally of finite type, so `X` is locally Noetherian and
`𝒪_X` is coherent ([Stacks, Tag 01XZ]); `𝒪_X` in degree zero is bounded; its support is all of
`X`, which is proper over `S` because `f` is — the zero ideal sheaf is a closed subscheme
structure on `⊤` whose closed immersion is an isomorphism, which is what
`AlgebraicGeometry.isProperOver_iff_exists_isProper` asks for; `𝒪_X` is flat over `S` because `f`
is flat ([Stacks, Tag 02N3]), which takes the stalk comparisons described below; and
`E ⊗^L_{𝒪_X} 𝒪_X ≅ E` is the unit constraint of [Stacks, Tag 0FPT], along which both the
hypothesis of [Stacks, Tag 08EV] and perfectness of the direct image transport.

**Spellings of the structure sheaf of rings.**  Three meet here, as they do in
`StacksFrontier/Topology/Sheaves/Cohomology/PerfectComplexes/ClosedSupportPerfect.lean`:
`StrictlyPerfect.structureSheafOfRings` (used by `StrictlyPerfect.OXMod`, hence by
[Stacks, Tag 08CM] and by the Tor-dimension and scalar-restriction material),
`structureSheafRing` (used by the pushforward functor) and
`AlgebraicGeometry.Scheme.ringCatSheaf` (used by the coherence material).  All three have the
same underlying presheaf of rings, and the first two are verbatim copies of each other
(`AlgebraicGeometry.RingedSpace.structureSheafOfRings_eq_ringSheaf`); they are identified for
this file by `attribute [local implicit_reducible]`, as in that file.  There are likewise two
coherence predicates on a sheaf of modules in the repository, `SheafOfModules.IsCoherent` and
`Stacks.SheafOfModules.IsCoherent`; this file uses the first, which is the one the scheme-level
material of [Stacks, Tag 01XZ] is stated at.

**The derived category.**  `HasDerivedCategory.standard` is a local instance, as in
[Stacks, Tag 08DP] and in the derived tensor product of [Stacks, Tag 0FPT], whose unit constraint
this file consumes.

## References

* [Stacks Project, Tag 0DJQ](https://stacks.math.columbia.edu/tag/0DJQ)
* [Stacks Project, Tag 0B6F](https://stacks.math.columbia.edu/tag/0B6F)
* [Stacks Project, Tag 08EV](https://stacks.math.columbia.edu/tag/08EV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction StrictlyPerfect
open Stacks.SheafOfModules.TensorStalkRingedSpace

namespace Stacks.Cohomology.PerfectPushforward

open Stacks.Cohomology.ProperSupportPerfection (derivedPushforwardOX)

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local implicit_reducible] structureSheafRing
  StrictlyPerfect.structureSheafOfRings StrictlyPerfect.structureModule

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The ringed site of the topological space underlying a scheme, with its structure sheaf: the
site at which the derived tensor product of [Stacks, Tag 06YU] and the unit constraint of
[Stacks, Tag 0FPT] are stated.  This is
`Stacks.Cohomology.SpaceInverseSystems.ringedSiteOfSpace` at `X.toRingedSpace`, named here only
so that the instance arguments those declarations carry are written at one spelling. -/
abbrev schemeSite (X : Scheme.{u}) : RingedSite.{u, u, u} :=
  Stacks.Cohomology.SpaceInverseSystems.ringedSiteOfSpace X.toRingedSpace

/-! ### The criterion of Stacks 08EV -/

/-- **The hypothesis of [Stacks, Tag 08EV] on an object `K` of `D(𝒪_X)**, for a morphism of
schemes `f : X ⟶ S` locally of finite type:

1. `K` lies in `D^b_{Coh}(𝒪_X)`, i.e. only finitely many of its cohomology sheaves are nonzero
   and each of them is coherent;
2. the support of each cohomology sheaf of `K` is proper over `S`; and
3. `K` has finite Tor dimension as an object of `D(f⁻¹𝒪_S)`.

Clause (2) is stated as the existence of a closed subset proper over `S` *containing* the
support rather than as properness of the support itself; the support of a coherent sheaf is
closed (`SheafOfModules.isClosed_supp`), so the two are equivalent by
`AlgebraicGeometry.isProperOver_of_le`, and the containment form is the one the chapter's
induction principles consume. Clause (3) reads `K` in `D(f⁻¹𝒪_S)` through
`AlgebraicGeometry.Scheme.Hom.derivedScalarRestriction` and measures its Tor dimension with a
certified derived tensor product `D` on the inverse-image ringed space `(X, f⁻¹𝒪_S)`. -/
structure PushforwardPerfectionInput [LocallyOfFiniteType f]
    (D : RingedSpace.CertifiedDerivedSheafTensoring
      (RingedSpace.inverseImage S.toRingedSpace f.base))
    (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) : Prop where
  /-- Only finitely many cohomology sheaves of `K` are nonzero. -/
  bounded : ∃ a b : ℤ, ∀ i : ℤ, i ∉ Set.Icc a b →
    IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) i).obj K)
  /-- Every cohomology sheaf of `K` is coherent. -/
  isCoherent : ∀ i : ℤ,
    ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) i).obj K).IsCoherent
  /-- The support of every cohomology sheaf of `K` lies in a closed subset proper over `S`. -/
  properSupport : ∀ i : ℤ, ∃ Z : Closeds X, IsProperOver f Z ∧
    SheafOfModules.supp
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) i).obj K) ⊆ (Z : Set X)
  /-- `K` has finite Tor dimension over `f⁻¹𝒪_S`. -/
  hasFiniteTorDimension :
    D.HasFiniteTorDimension ((Scheme.Hom.derivedScalarRestriction f).obj K)

/-- **[Stacks, Tag 08EV], read as a property of the derived direct image along `f`.**  A functor
`Rf` has this property when it carries every object of `D(𝒪_X)` satisfying
`Stacks.Cohomology.PerfectPushforward.PushforwardPerfectionInput` to a perfect object of
`D(𝒪_S)`.

This property is *not* carried as a hypothesis by the results below:
`Stacks.Cohomology.ProperSupportPerfection.isPerfect_derivedPushforward_of_properSupport` proves
the conditional form of [Stacks, Tag 08EV] at this spelling, and
`Stacks.Cohomology.PerfectPushforward.pushforwardPerfectionCriterion_of_residues` turns it into
this property.  What the results below carry instead are that theorem's own two residues,
`Stacks.Cohomology.PerfectPushforward.PushforwardCoherenceResidue` and
`Stacks.Cohomology.PerfectPushforward.PushforwardTorDimensionResidue`. -/
def PushforwardPerfectionCriterion [LocallyOfFiniteType f]
    (D : RingedSpace.CertifiedDerivedSheafTensoring
      (RingedSpace.inverseImage S.toRingedSpace f.base))
    (Rf : DerivedCategory (OXMod.{u, u} X.toRingedSpace) ⥤
      DerivedCategory (OXMod.{u, u} S.toRingedSpace)) : Prop :=
  ∀ K : DerivedCategory (OXMod.{u, u} X.toRingedSpace),
    PushforwardPerfectionInput f D K → RingedSpace.IsPerfect (X := S.toRingedSpace) (Rf.obj K)

/-- **The first residue of [Stacks, Tag 08EV]**: [Stacks, Tag 08E2] for the direct-image functor
`Rf`, read through [Stacks, Tag 08E8].  Granted a closed subset `T` of `X` proper over `S`
carrying the support of every cohomology sheaf of `K`, and granted coherence of those cohomology
sheaves, `Rf_*K` is pseudo-coherent.

This is `hpushforwardCoherence` of
`Stacks.Cohomology.ProperSupportPerfection.isPerfect_derivedPushforward_of_properSupport`,
quantified over `K`.  At the `AlgebraicGeometry.Scheme.Modules` spelling, for
`AlgebraicGeometry.derivedPushforwardModules` and a Noetherian base, the statement is proved, as
`isPseudoCoherent_derivedPushforward_of_isProperOver_supp_unconditional` in the namespace
`Stacks.AlgebraicGeometry.ProperSupportCoherent`; it is not transported here to an arbitrary
functor `Rf`. -/
def PushforwardCoherenceResidue [LocallyOfFiniteType f]
    (Rf : DerivedCategory (OXMod.{u, u} X.toRingedSpace) ⥤
      DerivedCategory (OXMod.{u, u} S.toRingedSpace)) : Prop :=
  ∀ (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) (T : Closeds X), IsProperOver f T →
    ProperSupportPerfection.SuppHomologySubset K T →
    (∀ i : ℤ,
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) i).obj K).IsCoherent) →
    RingedSpace.IsPseudoCoherent (X := S.toRingedSpace) (Rf.obj K)

/-- **The second residue of [Stacks, Tag 08EV]**: the closing step of the source's proof of that
tag.  Granted a closed subset `T` of `X` proper over `S` carrying the cohomological support of
`K`, and granted that `K` has finite Tor dimension over `f⁻¹𝒪_S`, the direct image `Rf_*K` has
finite Tor dimension over `𝒪_S`.

This is `hpushforwardTorDimension` of
`Stacks.Cohomology.ProperSupportPerfection.isPerfect_derivedPushforward_of_properSupport`,
quantified over `K`.  For the canonical derived tensor product on `(X, f⁻¹𝒪_S)` and
`AlgebraicGeometry.derivedPushforwardModules` the corresponding statement is proved, as
`AlgebraicGeometry.locallyHasFiniteTorDimension_derivedPushforward_of_isProperOver`; for an
arbitrary certified datum `D` the hypothesis `D.HasFiniteTorDimension` is about the underived
tensor product carried by `D`, not about the tensor product of modules, and does not give it. -/
def PushforwardTorDimensionResidue [LocallyOfFiniteType f]
    (D : RingedSpace.CertifiedDerivedSheafTensoring
      (RingedSpace.inverseImage S.toRingedSpace f.base))
    (Rf : DerivedCategory (OXMod.{u, u} X.toRingedSpace) ⥤
      DerivedCategory (OXMod.{u, u} S.toRingedSpace)) : Prop :=
  ∀ (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) (T : Closeds X), IsProperOver f T →
    ProperSupportPerfection.SuppHomologySubset K T →
    D.HasFiniteTorDimension ((Scheme.Hom.derivedScalarRestriction f).obj K) →
    Stacks.Cohomology.TorAmplitude.HasFiniteTorDimension S.toRingedSpace (Rf.obj K)

/-- **The conditional form of [Stacks, Tag 08EV] discharges the criterion.**  The four clauses of
`Stacks.Cohomology.PerfectPushforward.PushforwardPerfectionInput` are, field for field, the four
hypotheses of
`Stacks.Cohomology.ProperSupportPerfection.isPerfect_derivedPushforward_of_properSupport`, so
that theorem applied to each `K` is exactly
`Stacks.Cohomology.PerfectPushforward.PushforwardPerfectionCriterion`, modulo the two residues of
that theorem quantified over `K`.

[Stacks, Tag 08EV] asks only `AlgebraicGeometry.IsLocallyNoetherian` of `S`, which the
`AlgebraicGeometry.IsNoetherian` hypothesis of the two results below supplies; so the trade is
free.

The functor is `Stacks.Cohomology.ProperSupportPerfection.derivedPushforwardOX f`, since that is
what that conditional form concludes about.  Only the two residues are quantified over a functor,
which is right: each is a property *of* a functor, and the theorem applies both to this one. -/
theorem pushforwardPerfectionCriterion_of_residues [IsLocallyNoetherian S] [LocallyOfFiniteType f]
    (D : RingedSpace.CertifiedDerivedSheafTensoring
      (RingedSpace.inverseImage S.toRingedSpace f.base))
    (hcoh : PushforwardCoherenceResidue f (derivedPushforwardOX f))
    (htor : PushforwardTorDimensionResidue f D (derivedPushforwardOX f)) :
    PushforwardPerfectionCriterion f D (derivedPushforwardOX f) := fun K h =>
  ProperSupportPerfection.isPerfect_derivedPushforward_of_properSupport f K D
    h.bounded h.isCoherent h.properSupport h.hasFiniteTorDimension (hcoh K) (htor K)

/-! ### Transport of the criterion's hypothesis along an isomorphism -/

/-- **The support of a sheaf of modules depends only on its isomorphism class.**  The stalk
functor at a point is a functor, so it carries an isomorphism of sheaves of modules to an
isomorphism of stalks, and one of those stalks is nontrivial exactly when the other is.

This is the `StrictlyPerfect.OXMod` spelling on a ringed space, which is the spelling
`Stacks.Cohomology.PerfectPushforward.PushforwardPerfectionInput` is written at.  A statement of
the same fact for `AlgebraicGeometry.Scheme.Modules`, `SheafOfModules.supp_eq_of_iso`, is on the
way into `StacksFrontier/AlgebraicGeometry/Morphisms/Support/Defs.lean`; when it is available this
declaration should be replaced by it rather than kept alongside. -/
theorem supp_eq_of_iso_ringedSpace {Y : RingedSpace.{u, u}} {M N : OXMod.{u, u} Y} (e : M ≅ N) :
    SheafOfModules.supp M = SheafOfModules.supp N := by
  ext x
  have h : IsZero ((AlgebraicGeometry.SheafOfModules.stalkFunctor
        (structureSheafOfRings Y) x).obj M) ↔
      IsZero ((AlgebraicGeometry.SheafOfModules.stalkFunctor
        (structureSheafOfRings Y) x).obj N) :=
    ⟨fun hz => hz.of_iso
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafOfRings Y) x).mapIso
          e).symm,
      fun hz => hz.of_iso
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafOfRings Y) x).mapIso e)⟩
  rw [AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj_iff,
    AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj_iff,
    AddCommGrpCat.isZero_iff_subsingleton, AddCommGrpCat.isZero_iff_subsingleton] at h
  rw [SheafOfModules.mem_supp_iff_nontrivial_stalk M x,
    SheafOfModules.mem_supp_iff_nontrivial_stalk N x,
    ← not_subsingleton_iff_nontrivial, ← not_subsingleton_iff_nontrivial]
  exact not_congr h

/-- **The hypothesis of [Stacks, Tag 08EV] depends only on the isomorphism class of the object.**
Each of its four clauses is a property of the cohomology sheaves or of the image under a functor,
and both are carried along by an isomorphism:
`Stacks.Cohomology.PerfectPushforward.supp_eq_of_iso_ringedSpace` for the support clause, the
`IsClosedUnderIsomorphisms` instance of coherence for the second, and
functoriality of `DerivedCategory.homologyFunctor`, of
`AlgebraicGeometry.Scheme.Hom.derivedScalarRestriction` and of the derived tensor product for the
other two. -/
theorem PushforwardPerfectionInput.of_iso [LocallyOfFiniteType f]
    {D : RingedSpace.CertifiedDerivedSheafTensoring
      (RingedSpace.inverseImage S.toRingedSpace f.base)}
    {K K' : DerivedCategory (OXMod.{u, u} X.toRingedSpace)}
    (h : PushforwardPerfectionInput f D K) (e : K ≅ K') :
    PushforwardPerfectionInput f D K' where
  bounded := by
    obtain ⟨a, b, hab⟩ := h.bounded
    refine ⟨a, b, fun i hi => (hab i hi).of_iso ?_⟩
    exact (DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) i).mapIso e.symm
  isCoherent i :=
    (show ObjectProperty (OXMod.{u, u} X.toRingedSpace) from
        fun M => M.IsCoherent).prop_of_iso
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) i).mapIso e)
      (h.isCoherent i)
  properSupport i := by
    obtain ⟨Z, hZ, hsub⟩ := h.properSupport i
    refine ⟨Z, hZ, ?_⟩
    rw [← supp_eq_of_iso_ringedSpace
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) i).mapIso e)]
    exact hsub
  hasFiniteTorDimension := by
    obtain ⟨a, b, hab⟩ := h.hasFiniteTorDimension
    refine ⟨a, b, fun F i hi => (hab F i hi).of_iso ?_⟩
    exact (DerivedCategory.homologyFunctor _ i).mapIso
      ((D.derivedTensor.mapIso
        ((Scheme.Hom.derivedScalarRestriction f).mapIso e.symm)).app _)

/-! ### The hypothesis on the complex `𝒢` in Stacks 0DJQ -/

/-- **The hypothesis on `𝒢` in [Stacks, Tag 0DJQ]**: `𝒢` is a bounded complex of coherent
`𝒪_X`-modules, flat over `S`, with support proper over `S`.

Flatness over `S` of a single `𝒪_X`-module is `AlgebraicGeometry.IsFlatOver` ([Stacks, Tag 08KT]
part (2)), i.e. flatness of each stalk `𝒢^i_x` as a module over `𝒪_{S, f(x)}`; the support
condition is one closed subset `Z`, proper over `S` in the sense of
`AlgebraicGeometry.IsProperOver` ([Stacks, Tag 0CYM]), containing the support of every `𝒢^i`,
which for a bounded complex is the same as properness of the support of the complex. -/
structure FlatProperSupportComplex [LocallyOfFiniteType f]
    (G : CochainComplex (OXMod.{u, u} X.toRingedSpace) ℤ) : Prop where
  /-- `𝒢` is a bounded complex. -/
  bounded : ∃ a b : ℤ, G.IsStrictlyGE a ∧ G.IsStrictlyLE b
  /-- Every term of `𝒢` is a coherent `𝒪_X`-module. -/
  isCoherent : ∀ i : ℤ, (G.X i).IsCoherent
  /-- Every term of `𝒢` is flat over `S`. -/
  isFlatOver : ∀ i : ℤ, IsFlatOver f.toLRSHom.toShHom (G.X i)
  /-- The support of `𝒢` is contained in a closed subset proper over `S`. -/
  properSupport : ∃ Z : Closeds X, IsProperOver f Z ∧
    ∀ i : ℤ, SheafOfModules.supp (G.X i) ⊆ (Z : Set X)

/-! ### The local identification of `E ⊗^L_{𝒪_X} 𝒢`

The one geometric step of [Stacks, Tag 0DJQ]: a K-flat resolution of a representative of `E`
computes `E ⊗^L_{𝒪_X} 𝒢` globally as a total tensor complex, and on an open where `E` has a
strictly perfect model that total tensor complex is, in the derived category, the total tensor
complex of the model with the restriction of `𝒢`.  This is
`AlgebraicGeometry.RingedSpace.isPerfect_derivedTensorProduct`'s argument run with only *one*
factor perfect: there the two factors each contribute a covering and the two strictly perfect
models are tensored on the intersection, whereas here `𝒢` is global and one covering suffices,
so the models restrict no further and the comparison is needed on one side only.  That is what
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.comparisonLeft` provides, and
`Stacks.Cohomology.RestrictionTensor.restrictComplexTensorIso` — restriction commutes with the
total tensor complex, with no hypothesis on either factor — carries `𝒢` along. -/

variable (X) in
/-- **A K-flat representative of `E` computes `E ⊗^L_{𝒪_X} 𝒢` as a total tensor complex.**  If
`A` is K-flat and its class is `E`, then
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.comparisonLeft` identifies
`E ⊗^L_{𝒪_X} 𝒢` with the class of `Tot(A ⊗_{𝒪_X} 𝒢)`.  Nothing is asked of `𝒢`: the left
comparison needs K-flatness on the left factor only, which is why `𝒢` — a complex of coherent
modules flat over `S`, not over `𝒪_X` — need not be resolved. -/
private def tensorKFlatRepresentativeIso
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.toRingedSpace.sheaf)
    [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.toRingedSpace.sheaf).Additive]
    [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      X.toRingedSpace.sheaf).obj M).Additive]
    [∀ K L : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules X.toRingedSpace.sheaf) ℤ,
      HomologicalComplex.HasMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.toRingedSpace.sheaf)
        (ComplexShape.up ℤ)]
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (A G : CochainComplex (OXMod.{u, u} X.toRingedSpace) ℤ)
    (hA : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat X.toRingedSpace A)
    (aE : DerivedCategory.Q.obj A ≅ E) :
    DerivedCategory.Q.obj
        (((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSpace.sheaf).obj A).obj G) ≅
      (T.tensor.obj E).obj (DerivedCategory.Q.obj G) :=
  (T.comparisonLeft A G hA).symm ≪≫ (T.tensor.mapIso aE).app _

/-- **A strictly perfect model of `E` over `U` is, in `D(𝒪_U)`, the restriction to `U` of a
K-flat resolution of a representative of `E`.**  Restriction to an open subspace is exact, so it
carries the quasi-isomorphism `A ⟶ E'` to a quasi-isomorphism; the model's own
quasi-isomorphism `P ⟶ E'|_U` does the rest.  This is the one-factor analogue of the local
comparison used for [Stacks, Tag 09J5]: only one open occurs, so no further restriction along an
inclusion of opens is needed.

The `PreservesHomology` arguments of
`HomologicalComplex.quasiIso_map_of_preservesHomology` are written out, as they are at
[Stacks, Tag 09J5]: the goal and the available instances reach the `Preadditive` structure of the
category of modules on an open subspace by different routes. -/
private def restrictedFactorIso (U : Opens X)
    (E' A : CochainComplex (OXMod.{u, u} X.toRingedSpace) ℤ)
    (p : A ⟶ E') (hp : QuasiIso p)
    (P : CochainComplex (OXMod.{u, u} (X.toRingedSpace.restrict U.isOpenEmbedding)) ℤ)
    (fP : P ⟶ AlgebraicGeometry.RingedSpace.restrictComplex E' U) (hfP : QuasiIso fP) :
    DerivedCategory.Q.obj P ≅
      DerivedCategory.Q.obj (AlgebraicGeometry.RingedSpace.restrictComplex A U) :=
  _root_.CochainComplex.derivedIsoOfQuasiIso fP hfP ≪≫
    (_root_.CochainComplex.derivedIsoOfQuasiIso
      (((AlgebraicGeometry.RingedSpace.restrictModules X.toRingedSpace U).mapHomologicalComplex
        (ComplexShape.up ℤ)).map p)
      (@HomologicalComplex.quasiIso_map_of_preservesHomology _ _ _ _ _ _ _ _ _ _ p
        (AlgebraicGeometry.RingedSpace.restrictModules X.toRingedSpace U)
        _ _ _ _ _ _ hp)).symm

/-- **On an open where `E` has a strictly perfect model `P`, the total tensor complex
`Tot(A ⊗_{𝒪_X} 𝒢)` restricts to `Tot(P ⊗_{𝒪_U} 𝒢|_U)` in the derived category.**

Three steps on `U`, with the canonical derived tensor product there: a strictly perfect complex
is K-flat, so
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.comparisonLeft` turns the class of
`Tot(P ⊗ 𝒢|_U)` into `Q(P) ⊗^L Q(𝒢|_U)`; `Q(P)` is `Q(A|_U)` by
`Stacks.Cohomology.PerfectPushforward.restrictedFactorIso` and `A|_U` is K-flat, so the same
comparison turns `Q(A|_U) ⊗^L Q(𝒢|_U)` back into the class of `Tot(A|_U ⊗ 𝒢|_U)`; and that
complex is `Tot(A ⊗ 𝒢)|_U` by
`Stacks.Cohomology.RestrictionTensor.restrictComplexTensorIso`. -/
private def localTensorModelIso (U : Opens X)
    (E' A G : CochainComplex (OXMod.{u, u} X.toRingedSpace) ℤ)
    (p : A ⟶ E') (hp : QuasiIso p)
    (hA : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat X.toRingedSpace A)
    (P : CochainComplex (OXMod.{u, u} (X.toRingedSpace.restrict U.isOpenEmbedding)) ℤ)
    (hP : IsStrictlyPerfect P)
    (fP : P ⟶ AlgebraicGeometry.RingedSpace.restrictComplex E' U) (hfP : QuasiIso fP) :
    DerivedCategory.Q.obj
        (((Stacks.SheafOfModules.Tensor.tensorComplex
              (X.toRingedSpace.restrict U.isOpenEmbedding).sheaf).obj P).obj
          (AlgebraicGeometry.RingedSpace.restrictComplex G U)) ≅
      DerivedCategory.Q.obj (AlgebraicGeometry.RingedSpace.restrictComplex
        (((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSpace.sheaf).obj A).obj G) U) :=
  letI TW := Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
    (X.toRingedSpace.restrict U.isOpenEmbedding).sheaf
  (TW.comparisonLeft _ _
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.kFlat_of_isStrictlyPerfect P hP)).symm ≪≫
    (TW.tensor.mapIso (restrictedFactorIso U E' A p hp P fP hfP)).app _ ≪≫
    TW.comparisonLeft _ _
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.kFlat_restrictComplex U A hA) ≪≫
    (DerivedCategory.Q.mapIso
      (Stacks.Cohomology.RestrictionTensor.restrictComplexTensorIso
        X.toRingedSpace U A G)).symm

variable (X) in
/-- **The local identification that the proof of [Stacks, Tag 0DJQ] runs on.**  For `E` perfect
and `𝒢` any complex of `𝒪_X`-modules there are a K-flat complex `A` whose total tensor complex
with `𝒢` represents `E ⊗^L_{𝒪_X} 𝒢`, and an open covering of `X` on which that representative
is, in the derived category, the total tensor complex of a *strictly perfect* complex with the
restriction of `𝒢`.

This is the geometric content of [Stacks, Tag 0DJQ]: "locally `E` is a finite complex of finite
free modules, so locally `E ⊗^L_{𝒪_X} 𝒢` is a finite complex whose terms are finite direct sums
of the `𝒢^i`".  Each of the four clauses of
`Stacks.Cohomology.PerfectPushforward.PushforwardPerfectionInput` is read off this description
together with a locality principle; see the implementation notes of this file for what each
reading still requires.

The shape of the conclusion is the one
`AlgebraicGeometry.RingedSpace.isPerfect_of_strictlyPerfect_local_models` consumes — a global
representative plus, on a covering, isomorphisms *in the derived category* — because that is the
shape every locality principle in this chapter asks for. -/
theorem exists_local_tensorComplex_models
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.toRingedSpace.sheaf)
    [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.toRingedSpace.sheaf).Additive]
    [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      X.toRingedSpace.sheaf).obj M).Additive]
    [∀ K L : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules X.toRingedSpace.sheaf) ℤ,
      HomologicalComplex.HasMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.toRingedSpace.sheaf)
        (ComplexShape.up ℤ)]
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (G : CochainComplex (OXMod.{u, u} X.toRingedSpace) ℤ)
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E) :
    ∃ A : CochainComplex (OXMod.{u, u} X.toRingedSpace) ℤ,
      AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat X.toRingedSpace A ∧
      Nonempty (DerivedCategory.Q.obj
          (((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSpace.sheaf).obj A).obj G) ≅
        (T.tensor.obj E).obj (DerivedCategory.Q.obj G)) ∧
      ∃ (I : Type u) (U : I → Opens X), iSup U = ⊤ ∧ ∀ i : I,
        ∃ P : CochainComplex
            (OXMod.{u, u} (X.toRingedSpace.restrict (U i).isOpenEmbedding)) ℤ,
          IsStrictlyPerfect P ∧
            Nonempty (DerivedCategory.Q.obj
                (((Stacks.SheafOfModules.Tensor.tensorComplex
                      (X.toRingedSpace.restrict (U i).isOpenEmbedding).sheaf).obj P).obj
                  (AlgebraicGeometry.RingedSpace.restrictComplex G (U i))) ≅
              DerivedCategory.Q.obj (AlgebraicGeometry.RingedSpace.restrictComplex
                (((Stacks.SheafOfModules.Tensor.tensorComplex
                    X.toRingedSpace.sheaf).obj A).obj G) (U i))) := by
  classical
  obtain ⟨E', ⟨I, U, hU, hmodels⟩, ⟨eEK⟩⟩ := hE
  choose P hP fP hfP using hmodels
  obtain ⟨A, p, hA, -, hpq, -⟩ :=
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.exists_kFlatResolution
      X.toRingedSpace E'
  exact ⟨A, hA, ⟨tensorKFlatRepresentativeIso X T E A G hA
      (_root_.CochainComplex.derivedIsoOfQuasiIso p hpq ≪≫ eEK)⟩,
    I, U, hU, fun i => ⟨P i, hP i,
      ⟨localTensorModelIso (U i) E' A G p hpq hA (P i) (hP i) (fP i) (hfP i)⟩⟩⟩

/-! ### The support clause of Stacks 0DJQ

The support of every cohomology sheaf of `E ⊗^L_{𝒪_X} 𝒢` lies where the support of `𝒢` does.
This clause needs no local model: the global representative `Tot(A ⊗_{𝒪_X} 𝒢)` of
`exists_local_tensorComplex_models` already has every term a direct sum of modules `A^p ⊗ 𝒢^q`,
and at a point off the support of `𝒢` every one of those has vanishing stalk, by the stalk of a
tensor product of [Stacks, Tag 01CB].  Boundedness and coherence, by contrast, are false of
`Tot(A ⊗ 𝒢)` term by term — `A` is only K-flat — and so genuinely need the strictly perfect
models. -/

/-- A point lies in the support of a sheaf of modules exactly when the stalk there is nontrivial,
with the stalk written as `Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk`, the spelling
the stalk of a tensor product ([Stacks, Tag 01CB]) is stated at. -/
private theorem mem_supp_iff_nontrivial_grpStalk {Y : RingedSpace.{u, u}} (M : OXMod.{u, u} Y)
    (x : Y.carrier) :
    x ∈ SheafOfModules.supp M ↔ Nontrivial (grpStalk Y M.val x) :=
  SheafOfModules.mem_supp_iff_nontrivial_stalk M x

/-- Off the support of a sheaf of modules its stalk is a subsingleton.  This is the negation of
`Stacks.Cohomology.PerfectPushforward.mem_supp_iff_nontrivial_grpStalk`; it is stated separately
because `SheafOfModules.supp` is written for a sheaf of rings on a topological space and
`StrictlyPerfect.structureSheafOfRings` is a sheaf on the site of opens, so the two reach the
negated membership by routes `rw` will not cross. -/
private theorem notMem_supp_iff_subsingleton_grpStalk {Y : RingedSpace.{u, u}}
    (M : OXMod.{u, u} Y) (x : Y.carrier) :
    x ∉ SheafOfModules.supp M ↔ Subsingleton (grpStalk Y M.val x) :=
  (mem_supp_iff_nontrivial_grpStalk M x).not.trans not_nontrivial_iff_subsingleton

/-- The stalk functor of [Stacks, Tag 01AH] sends a sheaf of modules to a zero object exactly
when the stalk is a subsingleton. -/
private theorem isZero_stalkFunctor_obj_iff_subsingleton {Y : RingedSpace.{u, u}}
    (M : OXMod.{u, u} Y) (x : Y.carrier) :
    IsZero ((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafOfRings Y) x).obj M) ↔
      Subsingleton (grpStalk Y M.val x) := by
  rw [AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj_iff,
    AddCommGrpCat.isZero_iff_subsingleton]

/-- **A tensor product of sheaves of modules has subsingleton stalk wherever its right factor
does.**  The stalk of the tensor product is the tensor product of the stalks
([Stacks, Tag 01CB], `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso`), and a tensor
product with a subsingleton factor is a subsingleton.

`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso` is the comparison for the tensor
product of [Stacks, Tag 01CB]; that construction and the bifunctor
`Stacks.SheafOfModules.Tensor.sheafTensor` which `Stacks.SheafOfModules.Tensor.tensorComplex` is
built from are the same term, so no transport is involved.  The two stalk module structures are
passed explicitly rather than left to instance search, for the reason recorded at
`Stacks.Cohomology.PerfectPushforward.flat_compHom_of_addEquiv`.

`AlgebraicGeometry.notMem_supp_tensorSheaf_of_notMem_supp` is the same statement for the *left*
factor, on a scheme; this file needs the right factor, since `𝒢` is the right factor of
`A ⊗_{𝒪_X} 𝒢`, and needs it on a ringed space. -/
private theorem subsingleton_grpStalk_tensorSheaf_of_right {Y : RingedSpace.{u, u}}
    (F G : OXMod.{u, u} Y) (x : Y.carrier) (hG : Subsingleton (grpStalk Y G.val x)) :
    Subsingleton (grpStalk Y ((((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        ⟨((Y)).presheaf, ((Y)).IsSheaf⟩).obj (F)).obj (G))).val x) := by
  have iF : Module (ringStalk Y x) (grpStalk Y F.val x) := stalkModule Y F.val x
  have iG : Module (ringStalk Y x) (grpStalk Y G.val x) := stalkModule Y G.val x
  have hT : Subsingleton (TensorProduct (ringStalk Y x)
      (grpStalk Y F.val x) (grpStalk Y G.val x)) := inferInstance
  exact ⟨fun p q => (tensorStalkIso Y x F G).injective (Subsingleton.elim _ _)⟩

/-- **A coproduct of sheaves of modules has subsingleton stalk wherever every summand does**,
because the stalk functor preserves colimits ([Stacks, Tag 01AH]); this is
`AlgebraicGeometry.SheafOfModules.nontrivial_stalkFunctor_coproduct_iff` read contrapositively. -/
private theorem subsingleton_grpStalk_coproduct {Y : RingedSpace.{u, u}} {ι : Type}
    (M : ι → OXMod.{u, u} Y) (x : Y.carrier)
    (hM : ∀ j, Subsingleton (grpStalk Y (M j).val x)) :
    Subsingleton (grpStalk Y (∐ M).val x) := by
  rw [← not_nontrivial_iff_subsingleton]
  intro h
  obtain ⟨j, hj⟩ := (AlgebraicGeometry.SheafOfModules.nontrivial_stalkFunctor_coproduct_iff
    (structureSheafOfRings Y) x M).1 h
  exact (not_nontrivial_iff_subsingleton.2 (hM j)) hj

/-- **The cohomology of a complex has subsingleton stalk wherever the term in that degree does.**
The stalk functor preserves finite limits and finite colimits
(`StacksFrontier/Topology/Sheaves/Modules/StalkExactness.lean`), hence homology, so the stalk of
`H^r(C)` is the homology of the short complex of stalks around degree `r`; that short complex has
a zero object in the middle, so it is exact there. -/
private theorem subsingleton_grpStalk_homology {Y : RingedSpace.{u, u}}
    (C : CochainComplex (OXMod.{u, u} Y) ℤ) (x : Y.carrier) (r : ℤ)
    (h : Subsingleton (grpStalk Y (C.X r).val x)) :
    Subsingleton (grpStalk Y (C.homology r).val x) := by
  rw [← isZero_stalkFunctor_obj_iff_subsingleton] at h ⊢
  refine IsZero.of_iso ?_
    ((C.sc r).mapHomologyIso
      (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafOfRings Y) x)).symm
  rw [← ShortComplex.exact_iff_isZero_homology]
  exact ShortComplex.exact_of_isZero_X₂ _ h

variable (X) in
/-- **A term of the total complex of a bifunctor double complex is the coproduct of the values of
the bifunctor on the terms of the two factors in complementary degrees.**  This holds by `rfl`: the
total complex of [Stacks, Tag 0FNC] is `CategoryTheory.GradedObject.mapObj` of the double complex
along `p + q`, and that is by construction the coproduct over the fibre of `p + q = n`.  The fibre
is a subtype of `ℤ × ℤ`, hence lives in `Type`, which is what
`Stacks.Cohomology.PerfectPushforward.subsingleton_grpStalk_coproduct` asks for. -/
private theorem map₂_X_eq_coproduct {C₁ C₂ D : Type*} [Category C₁] [Category C₂]
    [Category D] [Preadditive C₁] [Preadditive C₂] [Preadditive D]
    (F : C₁ ⥤ C₂ ⥤ D) (K : CochainComplex C₁ ℤ) (L : CochainComplex C₂ ℤ)
    [F.Additive] [∀ M, (F.obj M).Additive]
    [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ),
      HomologicalComplex.HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)] (n : ℤ) :
    (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj K).obj L).X n =
      ∐ (((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj K).obj L).toGradedObject.mapObjFun
          (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) n := rfl

variable (X) in
/-- **Every term of `Tot(A ⊗_{𝒪_X} 𝒢)` has subsingleton stalk wherever every term of `𝒢` does.**
The term is a coproduct of modules `A^p ⊗_{𝒪_X} 𝒢^q`, each of which has subsingleton stalk
because its right factor does. -/
private theorem subsingleton_grpStalk_tensorComplex_X
    (A G : CochainComplex (OXMod.{u, u} X.toRingedSpace) ℤ)
    [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.toRingedSpace.sheaf).Additive]
    [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      X.toRingedSpace.sheaf).obj M).Additive]
    [∀ K L : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules X.toRingedSpace.sheaf) ℤ,
      HomologicalComplex.HasMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.toRingedSpace.sheaf)
        (ComplexShape.up ℤ)]
    (x : X) (hG : ∀ q : ℤ, Subsingleton (grpStalk X.toRingedSpace (G.X q).val x)) (n : ℤ) :
    Subsingleton (grpStalk X.toRingedSpace
      ((((Stacks.SheafOfModules.Tensor.tensorComplex
        X.toRingedSpace.sheaf).obj A).obj G).X n).val x) := by
  erw [map₂_X_eq_coproduct]
  exact subsingleton_grpStalk_coproduct _ x fun _ =>
    subsingleton_grpStalk_tensorSheaf_of_right _ _ x (hG _)

variable (X) in
/-- **The support clause of [Stacks, Tag 0DJQ], proved.**  If every term of `𝒢` is supported in a
subset `Z` of `X`, then so is every cohomology sheaf of `E ⊗^L_{𝒪_X} 𝒢`.

The global half of `Stacks.Cohomology.PerfectPushforward.exists_local_tensorComplex_models` gives
a K-flat `A` with `Q(Tot(A ⊗_{𝒪_X} 𝒢)) ≅ E ⊗^L_{𝒪_X} 𝒢`; support depends only on the
isomorphism class (`Stacks.Cohomology.PerfectPushforward.supp_eq_of_iso_ringedSpace`) and
`DerivedCategory.homologyFunctorFactors` identifies the cohomology of the class of a complex with
the homology of the complex, so the question becomes one about `Tot(A ⊗_{𝒪_X} 𝒢)`.  There every
term is a coproduct of `A^p ⊗_{𝒪_X} 𝒢^q`, and off `Z` all of those have subsingleton stalk.

No local model is used: the covering produced by perfectness of `E` is discarded.  Perfectness
of `E` enters only through that theorem, which is where the K-flat global representative comes
from. -/
theorem supp_homology_derivedTensor_subset
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.toRingedSpace.sheaf)
    [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.toRingedSpace.sheaf).Additive]
    [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      X.toRingedSpace.sheaf).obj M).Additive]
    [∀ K L : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules X.toRingedSpace.sheaf) ℤ,
      HomologicalComplex.HasMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.toRingedSpace.sheaf)
        (ComplexShape.up ℤ)]
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (G : CochainComplex (OXMod.{u, u} X.toRingedSpace) ℤ)
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
    (Z : Set X) (hZ : ∀ q : ℤ, SheafOfModules.supp (G.X q) ⊆ Z) (i : ℤ) :
    SheafOfModules.supp ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) i).obj
        ((T.tensor.obj E).obj (DerivedCategory.Q.obj G))) ⊆ Z := by
  obtain ⟨A, -, ⟨eA⟩, -⟩ := exists_local_tensorComplex_models X T E G hE
  rw [supp_eq_of_iso_ringedSpace
    (((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) i).mapIso eA).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (OXMod.{u, u} X.toRingedSpace) i).app
        (((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSpace.sheaf).obj A).obj G))]
  intro x hx
  by_contra hxZ
  exact (notMem_supp_iff_subsingleton_grpStalk _ x).2
    (subsingleton_grpStalk_homology _ x i (subsingleton_grpStalk_tensorComplex_X X A G x
      (fun q => (notMem_supp_iff_subsingleton_grpStalk _ x).1 fun hm => hxZ (hZ q hm)) i)) hx

/-! ### The boundedness clause of Stacks 0DJQ

Only finitely many cohomology sheaves of `E ⊗^L_{𝒪_X} 𝒢` are nonzero.  Unlike the support clause
this one does need the local models: `A` is only K-flat, so `Tot(A ⊗_{𝒪_X} 𝒢)` has a nonzero term
in every degree, whereas `Tot(P ⊗ 𝒢|_U)` for a *strictly perfect* `P` has a nonzero term only in
degrees between the sum of the two lower bounds and the sum of the two upper bounds.  Each member
of the covering therefore contributes an interval of its own, and two further facts turn those
intervals into one:  the closed subset carrying `𝒢` is quasi-compact, so finitely many members
suffice; and off that subset the cohomology vanishes, by the support clause above.  The second is
read off an empty support, by `SheafOfModules.isZero_of_supp_eq_empty`. -/

/-- A coproduct of zero objects is a zero object: the identity of the coproduct agrees with the
zero morphism on every summand, and a morphism out of a coproduct is determined by its
components. -/
private theorem isZero_coproduct_of_isZero {C : Type*} [Category C] [Preadditive C]
    [HasZeroObject C] {ι : Type*} (M : ι → C) [HasCoproduct M] (hM : ∀ j, IsZero (M j)) :
    IsZero (∐ M) := by
  rw [IsZero.iff_id_eq_zero]
  ext j
  simp only [Category.comp_id, comp_zero]
  exact (hM j).eq_of_src _ _

/-- **A term of the total complex of a bifunctor double complex vanishes as soon as, in every
pair of complementary degrees, one of the two factors does.**  The term in degree `n` is the
coproduct over the pairs `(p, q)` with `p + q = n` of the values `F(K^p, L^q)` — this holds by
`rfl`, the total complex of [Stacks, Tag 0FNC] being
`CategoryTheory.GradedObject.mapObj` of the double complex along `p + q` — and `F` is additive in
each variable, so it carries a zero object in either slot to a zero object.

Stated for an arbitrary bifunctor additive in each variable rather than for `⊗_{𝒪_X}`: the
tensor product of sheaves of modules has three spellings of its ring sheaf in play here, and the
statement at this generality mentions none of them. -/
private theorem isZero_mapBifunctor_X {C₁ C₂ D : Type*} [Category C₁] [Category C₂]
    [Category D] [Preadditive C₁] [Preadditive C₂] [Abelian D]
    (F : C₁ ⥤ C₂ ⥤ D) (K : CochainComplex C₁ ℤ) (L : CochainComplex C₂ ℤ)
    [F.Additive] [∀ M, (F.obj M).Additive]
    [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ),
      HomologicalComplex.HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)]
    (n : ℤ) (h : ∀ p q : ℤ, p + q = n → IsZero (K.X p) ∨ IsZero (L.X q)) :
    IsZero ((((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)).obj K).obj L).X n) := by
  rw [map₂_X_eq_coproduct]
  refine isZero_coproduct_of_isZero _ fun j => ?_
  obtain ⟨⟨p, q⟩, hpq⟩ := j
  rcases h p q hpq with hK | hL
  · exact (Functor.map_isZero F hK).obj _
  · exact Functor.map_isZero _ hL

/-- **The cohomology of the total complex of a bifunctor double complex vanishes outside the sum
of the two factors' ranges.**  If `K` vanishes outside `[aK, bK]` and `L` outside `[aL, bL]` then
every term of the total complex outside `[aK + aL, bK + bL]` vanishes, by
`Stacks.Cohomology.PerfectPushforward.isZero_mapBifunctor_X`, and a complex with a zero term in
degree `n` has zero cohomology there. -/
private theorem isZero_homology_map₂ {C₁ C₂ D : Type*} [Category C₁] [Category C₂]
    [Category D] [Preadditive C₁] [Preadditive C₂] [Abelian D]
    (F : C₁ ⥤ C₂ ⥤ D) (K : CochainComplex C₁ ℤ) (L : CochainComplex C₂ ℤ)
    [F.Additive] [∀ M, (F.obj M).Additive]
    [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ),
      HomologicalComplex.HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)]
    (aK bK aL bL : ℤ)
    (hK : ∀ p : ℤ, p < aK ∨ bK < p → IsZero (K.X p))
    (hL : ∀ q : ℤ, q < aL ∨ bL < q → IsZero (L.X q))
    (n : ℤ) (hn : n ∉ Set.Icc (aK + aL) (bK + bL)) :
    IsZero ((((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)).obj K).obj L).homology n) := by
  have hX : IsZero ((((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)).obj K).obj L).X n) := by
    refine isZero_mapBifunctor_X F K L n fun p q hpq => ?_
    simp only [Set.mem_Icc, not_and_or, not_le] at hn
    rcases hn with h | h
    · by_cases hp : p < aK
      · exact Or.inl (hK p (Or.inl hp))
      · exact Or.inr (hL q (Or.inl (by omega)))
    · by_cases hp : bK < p
      · exact Or.inl (hK p (Or.inr hp))
      · exact Or.inr (hL q (Or.inr (by omega)))
  simpa [HomologicalComplex.homology] using
    ShortComplex.isZero_homology_of_isZero_X₂ ((((F.map₂HomologicalComplex (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj L).sc n) hX

/-- **The cohomology of a local tensor model `Tot(P ⊗_{𝒪_U} 𝒢|_U)` vanishes outside the sum of
the two factors' ranges.**  This is
`Stacks.Cohomology.PerfectPushforward.isZero_homology_map₂` at `F = ⊗_{𝒪_U}`.

The two complexes are handed over at the
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules` spelling of the category of
`𝒪_U`-modules, which is `StrictlyPerfect.OXMod` of that space by `rfl` and so costs nothing.  It
is not optional: the instance arguments of the tensor product fix its ring sheaf as
`Stacks.SheafOfModules.Tensor.ringSheaf`, and a complex presented at the other spelling leaves
them to be synthesized before the two ring sheaves are unified, which fails.  The module
docstring of `StacksFrontier/Topology/Sheaves/Cohomology/KFlat/OnARingedSpace.lean` records the same
requirement. -/
private theorem isZero_homology_localTensorModel (U : Opens X)
    (P Gr : CochainComplex (OXMod.{u, u} (X.toRingedSpace.restrict U.isOpenEmbedding)) ℤ)
    (aP bP aG bG : ℤ)
    (hP : ∀ p : ℤ, p < aP ∨ bP < p → IsZero (P.X p))
    (hG : ∀ q : ℤ, q < aG ∨ bG < q → IsZero (Gr.X q))
    (n : ℤ) (hn : n ∉ Set.Icc (aP + aG) (bP + bG)) :
    IsZero ((((Stacks.SheafOfModules.Tensor.tensorComplex
      (X.toRingedSpace.restrict U.isOpenEmbedding).sheaf).obj P).obj Gr).homology n) :=
  isZero_homology_map₂ (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      (X.toRingedSpace.restrict U.isOpenEmbedding).sheaf)
    (show CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules
      (X.toRingedSpace.restrict U.isOpenEmbedding)) ℤ from P)
    (show CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules
      (X.toRingedSpace.restrict U.isOpenEmbedding)) ℤ from Gr)
    aP bP aG bG hP hG n hn

/-- **On a member `U` of the covering, the restriction of a cohomology sheaf of
`E ⊗^L_{𝒪_X} 𝒢` is the cohomology of the local tensor model.**

Three comparisons: `eA` and `DerivedCategory.homologyFunctorFactors` turn the cohomology of
`E ⊗^L_{𝒪_X} 𝒢` into the cohomology of the global representative `Tot(A ⊗_{𝒪_X} 𝒢)`;
restriction to `U` is exact, so it commutes with that cohomology
(`Stacks.AlgebraicGeometry.PerfectCohomology.mapHomologyIso`), which supplies the one fact about
restriction that is used; and `eP` with `DerivedCategory.homologyFunctorFactors` again turn the
result into the cohomology of `Tot(P ⊗_{𝒪_U} 𝒢|_U)`.  So the comparison passes through no derived
functor of the restriction, and neither
`AlgebraicGeometry.RingedSpace.isZero_of_restrictModules` nor
`AlgebraicGeometry.RingedSpace.derivedRestrictModulesObjQIso` is needed.

The two `PreservesFinite*` arguments of the exactness comparison are supplied as terms, as they
are at `Stacks.Cohomology.PerfectPushforward.restrictedFactorIso`.

Both clauses that need the local models read off this one isomorphism: the boundedness clause
through `Stacks.Cohomology.PerfectPushforward.exists_isZero_restrictModules_homology` and the
coherence clause through
`Stacks.Cohomology.PerfectPushforward.isCoherent_homology_derivedTensor`. -/
private def restrictHomologyLocalModelIso
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.toRingedSpace.sheaf)
    [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.toRingedSpace.sheaf).Additive]
    [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      X.toRingedSpace.sheaf).obj M).Additive]
    [∀ K L : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules X.toRingedSpace.sheaf) ℤ,
      HomologicalComplex.HasMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.toRingedSpace.sheaf)
        (ComplexShape.up ℤ)]
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (G A : CochainComplex (OXMod.{u, u} X.toRingedSpace) ℤ)
    (eA : DerivedCategory.Q.obj
        (((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSpace.sheaf).obj A).obj G) ≅
      (T.tensor.obj E).obj (DerivedCategory.Q.obj G))
    (U : Opens X)
    (P : CochainComplex (OXMod.{u, u} (X.toRingedSpace.restrict U.isOpenEmbedding)) ℤ)
    (eP : DerivedCategory.Q.obj
        (((Stacks.SheafOfModules.Tensor.tensorComplex
            (X.toRingedSpace.restrict U.isOpenEmbedding).sheaf).obj P).obj
          (AlgebraicGeometry.RingedSpace.restrictComplex G U)) ≅
      DerivedCategory.Q.obj (AlgebraicGeometry.RingedSpace.restrictComplex
        (((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSpace.sheaf).obj A).obj G) U))
    (n : ℤ) :
    (AlgebraicGeometry.RingedSpace.restrictModules X.toRingedSpace U).obj
        ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) n).obj
          ((T.tensor.obj E).obj (DerivedCategory.Q.obj G))) ≅
      (((Stacks.SheafOfModules.Tensor.tensorComplex
          (X.toRingedSpace.restrict U.isOpenEmbedding).sheaf).obj P).obj
        (AlgebraicGeometry.RingedSpace.restrictComplex G U)).homology n :=
  have : PreservesFiniteLimits (AlgebraicGeometry.RingedSpace.restrictModules
    X.toRingedSpace U) := AlgebraicGeometry.RingedSpace.restrictModules_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (AlgebraicGeometry.RingedSpace.restrictModules
    X.toRingedSpace U) := AlgebraicGeometry.RingedSpace.restrictModules_preservesFiniteColimits _ _
  (AlgebraicGeometry.RingedSpace.restrictModules X.toRingedSpace U).mapIso
      (((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) n).mapIso eA).symm ≪≫
        (DerivedCategory.homologyFunctorFactors (OXMod.{u, u} X.toRingedSpace) n).app _) ≪≫
    (Stacks.AlgebraicGeometry.PerfectCohomology.mapHomologyIso
      (AlgebraicGeometry.RingedSpace.restrictModules X.toRingedSpace U) _ n).symm ≪≫
    ((DerivedCategory.homologyFunctorFactors
      (OXMod.{u, u} (X.toRingedSpace.restrict U.isOpenEmbedding)) n).app _).symm ≪≫
    (DerivedCategory.homologyFunctor
      (OXMod.{u, u} (X.toRingedSpace.restrict U.isOpenEmbedding)) n).mapIso eP.symm ≪≫
    (DerivedCategory.homologyFunctorFactors
      (OXMod.{u, u} (X.toRingedSpace.restrict U.isOpenEmbedding)) n).app _

/-- **On one member of the covering the cohomology of `E ⊗^L_{𝒪_X} 𝒢` vanishes outside an
interval.**  Granted a strictly perfect model `P` of `E` over `U`, the restriction to `U` of the
`n`-th cohomology sheaf of `E ⊗^L_{𝒪_X} 𝒢` is zero for every `n` outside the sum of the range of
`P` and the range of `𝒢`.

`Stacks.Cohomology.PerfectPushforward.restrictHomologyLocalModelIso` identifies that restricted
cohomology sheaf with the cohomology of `Tot(P ⊗_{𝒪_U} 𝒢|_U)`, and the latter vanishes by
`Stacks.Cohomology.PerfectPushforward.isZero_homology_localTensorModel`.  The range of `P` is
`Stacks.Cohomology.TorAmplitude.exists_bounds_of_isStrictlyPerfect`. -/
private theorem exists_isZero_restrictModules_homology
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.toRingedSpace.sheaf)
    [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.toRingedSpace.sheaf).Additive]
    [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      X.toRingedSpace.sheaf).obj M).Additive]
    [∀ K L : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules X.toRingedSpace.sheaf) ℤ,
      HomologicalComplex.HasMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.toRingedSpace.sheaf)
        (ComplexShape.up ℤ)]
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (G A : CochainComplex (OXMod.{u, u} X.toRingedSpace) ℤ) (aG bG : ℤ)
    (hG : ∀ q : ℤ, q < aG ∨ bG < q → IsZero (G.X q))
    (eA : DerivedCategory.Q.obj
        (((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSpace.sheaf).obj A).obj G) ≅
      (T.tensor.obj E).obj (DerivedCategory.Q.obj G))
    (U : Opens X)
    (P : CochainComplex (OXMod.{u, u} (X.toRingedSpace.restrict U.isOpenEmbedding)) ℤ)
    (hP : IsStrictlyPerfect P)
    (eP : DerivedCategory.Q.obj
        (((Stacks.SheafOfModules.Tensor.tensorComplex
            (X.toRingedSpace.restrict U.isOpenEmbedding).sheaf).obj P).obj
          (AlgebraicGeometry.RingedSpace.restrictComplex G U)) ≅
      DerivedCategory.Q.obj (AlgebraicGeometry.RingedSpace.restrictComplex
        (((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSpace.sheaf).obj A).obj G) U)) :
    ∃ a b : ℤ, ∀ n : ℤ, n ∉ Set.Icc a b →
      IsZero ((AlgebraicGeometry.RingedSpace.restrictModules X.toRingedSpace U).obj
        ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) n).obj
          ((T.tensor.obj E).obj (DerivedCategory.Q.obj G)))) := by
  obtain ⟨aP, bP, -, hPz0⟩ :=
    Stacks.Cohomology.TorAmplitude.exists_bounds_of_isStrictlyPerfect P hP
  have hPz : ∀ p : ℤ, p < aP ∨ bP < p → IsZero (P.X p) := fun p hp =>
    hPz0 p (by simp only [Set.mem_Icc, not_and_or, not_le]; exact hp)
  refine ⟨aP + aG, bP + bG, fun n hn => ?_⟩
  have hres : ∀ q : ℤ, q < aG ∨ bG < q →
      IsZero ((AlgebraicGeometry.RingedSpace.restrictComplex G U).X q) := fun q hq =>
    Functor.map_isZero (AlgebraicGeometry.RingedSpace.restrictModules X.toRingedSpace U)
      (hG q hq)
  exact (isZero_homology_localTensorModel U P
      (AlgebraicGeometry.RingedSpace.restrictComplex G U) aP bP aG bG hPz hres n hn).of_iso
    (restrictHomologyLocalModelIso T E G A eA U P eP n)

/-- A family of `𝒪_X`-modules supported in a compact set, whose restrictions to the members of an
open covering each vanish outside an interval, vanishes outside a single interval. -/
private theorem exists_isZero_of_cover_bounds {I : Type u} (U : I → Opens X) (hU : iSup U = ⊤)
    {Z : Set X} (hZ : IsCompact Z) (M : ℤ → OXMod.{u, u} X.toRingedSpace)
    (hsupp : ∀ n, SheafOfModules.supp (M n) ⊆ Z)
    (hbd : ∀ i : I, ∃ a b : ℤ, ∀ n : ℤ, n ∉ Set.Icc a b →
      IsZero ((AlgebraicGeometry.RingedSpace.restrictModules X.toRingedSpace (U i)).obj (M n))) :
    ∃ a b : ℤ, ∀ n : ℤ, n ∉ Set.Icc a b → IsZero (M n) := by
  classical
  choose a b hab using hbd
  have hcover : ∀ x : X, ∃ i, x ∈ U i := fun x =>
    Opens.mem_iSup.mp (hU ▸ Opens.mem_top x)
  obtain ⟨s, hs⟩ := hZ.elim_finite_subcover
    (fun i : I => (U i : Set X)) (fun i => (U i).isOpen)
    (fun x _ => Set.mem_iUnion.mpr (hcover x))
  obtain ⟨c, hc⟩ := (s.finite_toSet.image b).bddAbove
  obtain ⟨d, hd⟩ := (s.finite_toSet.image a).bddBelow
  refine ⟨d, c, fun n hn => ?_⟩
  refine _root_.SheafOfModules.isZero_of_supp_eq_empty _
    (Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_)
  obtain ⟨i, his, hxi⟩ := Set.mem_iUnion₂.mp (hs (hsupp n hx))
  have hni : n ∉ Set.Icc (a i) (b i) := by
    simp only [Set.mem_Icc, not_and_or, not_le] at hn ⊢
    rcases hn with h' | h'
    · exact Or.inl (lt_of_lt_of_le h' (hd (Set.mem_image_of_mem a his)))
    · exact Or.inr (lt_of_le_of_lt (hc (Set.mem_image_of_mem b his)) h')
  exact Stacks.AlgebraicGeometry.PerfectCohomology.notMem_supp_of_isZero_restrictModules
    X (U i) _ (hab i n hni) x hxi hx

/-- **The boundedness clause of [Stacks, Tag 0DJQ], proved.**  For `E` perfect and `𝒢` a bounded
complex of coherent `𝒪_X`-modules, flat over `S`, with support proper over `S`, only finitely
many cohomology sheaves of `E ⊗^L_{𝒪_X} 𝒢` are nonzero.

The three ingredients.  (1) `Stacks.Cohomology.PerfectPushforward.exists_local_tensorComplex_models`
gives a covering of `X` on which `E ⊗^L_{𝒪_X} 𝒢` is the total tensor complex of a strictly
perfect complex with `𝒢|_U`, whence one vanishing interval per member, by
`Stacks.Cohomology.PerfectPushforward.exists_isZero_restrictModules_homology`.  (2) The closed
subset `Z` carrying `𝒢` is compact (`AlgebraicGeometry.isCompact_of_isProperOver`, which applies
because `AlgebraicGeometry.IsNoetherian S` supplies `CompactSpace S`), so finitely many members
cover it and their intervals have a common lower and a common upper bound.  (3) Outside `Z` there
is nothing to bound: `Stacks.Cohomology.PerfectPushforward.supp_homology_derivedTensor_subset`
puts the support of every cohomology sheaf inside `Z`, so for a degree outside the common interval
the support is empty — every point of `Z` lies in a member whose restriction of that cohomology
sheaf vanishes, and a vanishing restriction removes a point of the member from the support
(`Stacks.AlgebraicGeometry.PerfectCohomology.notMem_supp_of_isZero_restrictModules`) — and a sheaf
of modules with empty support is zero (`SheafOfModules.isZero_of_supp_eq_empty`).

Only the `bounded` and `properSupport` fields of `hG` are used; coherence and flatness of the
terms of `𝒢` play no part in this clause. -/
theorem exists_isZero_homology_derivedTensor [IsNoetherian S] [LocallyOfFiniteType f]
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.toRingedSpace.sheaf)
    [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.toRingedSpace.sheaf).Additive]
    [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      X.toRingedSpace.sheaf).obj M).Additive]
    [∀ K L : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules X.toRingedSpace.sheaf) ℤ,
      HomologicalComplex.HasMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.toRingedSpace.sheaf)
        (ComplexShape.up ℤ)]
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (G : CochainComplex (OXMod.{u, u} X.toRingedSpace) ℤ)
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
    (hG : FlatProperSupportComplex f G) :
    ∃ a b : ℤ, ∀ i : ℤ, i ∉ Set.Icc a b →
      IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) i).obj
        ((T.tensor.obj E).obj (DerivedCategory.Q.obj G))) := by
  classical
  obtain ⟨Z, hZ, hZsupp⟩ := hG.properSupport
  obtain ⟨aG, bG, hGE, hGL⟩ := hG.bounded
  have hGz : ∀ q : ℤ, q < aG ∨ bG < q → IsZero (G.X q) := by
    intro q hq
    rcases hq with hq | hq
    · exact G.isZero_of_isStrictlyGE aG q hq
    · exact G.isZero_of_isStrictlyLE bG q hq
  obtain ⟨A, -, ⟨eA⟩, I, U, hU, hmodels⟩ := exists_local_tensorComplex_models X T E G hE
  choose P hP hePn using hmodels
  exact exists_isZero_of_cover_bounds U hU (isCompact_of_isProperOver f Z hZ)
    (fun n => (DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) n).obj
      ((T.tensor.obj E).obj (DerivedCategory.Q.obj G)))
    (fun n => supp_homology_derivedTensor_subset X T E G hE _ hZsupp n) fun i =>
    exists_isZero_restrictModules_homology T E G A aG bG hGz eA (U i) (P i) (hP i)
      (hePn i).some

/-! ### The coherence clause of Stacks 0DJQ

Every cohomology sheaf of `E ⊗^L_{𝒪_X} 𝒢` is coherent.  Like the boundedness clause this one needs
the local models: `A` is only K-flat, so the terms of the global `Tot(A ⊗_{𝒪_X} 𝒢)` are not
coherent, whereas the terms of `Tot(P ⊗ 𝒢|_U)` for a *strictly perfect* `P` are finite direct sums
of modules `P^p ⊗ 𝒢^q`, each a tensor product of coherent modules.  Coherent modules form a weak
Serre subcategory, so the cohomology of such a complex is coherent; and coherence is local on an
open covering of a locally Noetherian scheme, which `X` is because `f` is locally of finite type
and `S` is Noetherian. -/

/-- **A coproduct all but finitely many of whose summands are zero is the coproduct of the
others.**  The two maps are the obvious ones: the inclusion of the sub-family indexed by `p`, and
the map out of the whole coproduct which is the inclusion on a summand satisfying `p` and zero on
the rest.  One composite is the identity because a summand satisfying `p` is hit by its own
inclusion, the other because on a summand not satisfying `p` both sides are maps out of a zero
object.

Stated for a predicate rather than for a finite subset, so that the predicate the consumer has —
"the first degree lies in the range of the strictly perfect factor" — is usable as it stands. -/
private def sigmaSubtypeIsoOfIsZero {C : Type*} [Category C] [Preadditive C]
    {J : Type*} (M : J → C) (p : J → Prop) [DecidablePred p] [HasCoproduct M]
    [HasCoproduct fun j : Subtype p => M j.1]
    (h : ∀ j, ¬ p j → IsZero (M j)) :
    (∐ fun j : Subtype p => M j.1) ≅ ∐ M where
  hom := Sigma.desc fun j => Sigma.ι M j.1
  inv := Sigma.desc fun j =>
    if hj : p j then Sigma.ι (fun k : Subtype p => M k.1) ⟨j, hj⟩ else 0
  hom_inv_id := by
    refine Sigma.hom_ext _ _ fun j => ?_
    rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc, dite_eq_left j.2, Category.comp_id]
  inv_hom_id := by
    refine Sigma.hom_ext _ _ fun j => ?_
    rw [Sigma.ι_comp_desc_assoc, Category.comp_id]
    by_cases hj : p j
    · rw [dite_eq_left hj, Sigma.ι_comp_desc]
    · rw [dite_eq_right hj, zero_comp]
      exact (h j hj).eq_of_src _ _

/-- **A property closed under finite coproducts holds of a coproduct with finitely many nonzero
summands**, as soon as it holds of every summand: by
`Stacks.Cohomology.PerfectPushforward.sigmaSubtypeIsoOfIsZero` such a coproduct is the coproduct
of its nonzero summands, and those are indexed by a finite type. -/
private theorem prop_coproduct_of_finite_support {C : Type*} [Category C] [Preadditive C]
    [HasFiniteCoproducts C] {J : Type*} (M : J → C) [HasCoproduct M]
    (Q : ObjectProperty C) [Q.IsClosedUnderIsomorphisms] [Q.IsClosedUnderFiniteCoproducts]
    (hfin : {j : J | ¬ IsZero (M j)}.Finite) (hQ : ∀ j, Q (M j)) :
    Q (∐ M) := by
  classical
  have : Finite {j : J // ¬ IsZero (M j)} := hfin.to_subtype
  exact Q.prop_of_iso
    (sigmaSubtypeIsoOfIsZero M (fun j => ¬ IsZero (M j)) fun _ hj => not_not.1 hj)
    (Q.prop_coproduct fun j => hQ j.1)

/-- **In the fibre of `(p, q) ↦ p + q` over `n` only finitely many pairs have first coordinate in
a bounded interval**, because such a pair is determined by its first coordinate: the second is
`n - p`. -/
private theorem finite_fibre_fst_mem_Icc (a b n : ℤ) :
    {j : ↑(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⁻¹'
      {n}) | ((j : ℤ × ℤ)).1 ∈ Set.Icc a b}.Finite := by
  have hinj : Function.Injective
      (fun j : ↑(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) ⁻¹' {n}) => ((j : ℤ × ℤ)).1) := by
    rintro ⟨⟨p₁, q₁⟩, h₁⟩ ⟨⟨p₂, q₂⟩, h₂⟩ hp
    have e₁ : p₁ + q₁ = n := h₁
    have e₂ : p₂ + q₂ = n := h₂
    have hp' : p₁ = p₂ := hp
    subst hp'
    have hq : q₁ = q₂ := by omega
    subst hq
    rfl
  refine Set.Finite.of_finite_image ?_ hinj.injOn
  exact (Set.finite_Icc a b).subset (by rintro x ⟨j, hj, rfl⟩; exact hj)

/-- **A term of the total complex of a bifunctor double complex has a property closed under finite
coproducts** as soon as the property holds of every value of the bifunctor on terms of the two
factors and the first factor is bounded.  The term in degree `n` is the coproduct over the pairs
`(p, q)` with `p + q = n` of the values `F(K^p, L^q)` — this holds by `rfl`, the total complex of
[Stacks, Tag 0FNC] being `CategoryTheory.GradedObject.mapObj` of the double complex along `p + q`
— and boundedness of `K` leaves only finitely many nonzero, by
`Stacks.Cohomology.PerfectPushforward.finite_fibre_fst_mem_Icc`.

This is the counterpart of `Stacks.Cohomology.PerfectPushforward.isZero_mapBifunctor_X` for a
property to be propagated rather than vanishing to be deduced, and like it is stated for an
arbitrary bifunctor additive in each variable rather than for `⊗_{𝒪_X}`, so that none of the three
spellings of the ring sheaf is mentioned.  No bound on `L` is needed: the property is asked of
every `F(K^p, L^q)`. -/
private theorem prop_mapBifunctor_X {C₁ C₂ A : Type*} [Category C₁] [Category C₂]
    [Category A] [Preadditive C₁] [Preadditive C₂] [Abelian A]
    (F : C₁ ⥤ C₂ ⥤ A) (K : CochainComplex C₁ ℤ) (L : CochainComplex C₂ ℤ)
    [F.Additive] [∀ M, (F.obj M).Additive]
    [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ),
      HomologicalComplex.HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)]
    (Q : ObjectProperty A) [Q.IsClosedUnderIsomorphisms] [Q.IsClosedUnderFiniteCoproducts]
    (a b : ℤ) (hK : ∀ p : ℤ, p < a ∨ b < p → IsZero (K.X p))
    (hQ : ∀ p q : ℤ, Q ((F.obj (K.X p)).obj (L.X q)))
    (n : ℤ) :
    Q ((((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)).obj K).obj L).X n) := by
  classical
  rw [map₂_X_eq_coproduct]
  refine prop_coproduct_of_finite_support _ Q ((finite_fibre_fst_mem_Icc a b n).subset ?_) ?_
  · intro j hj
    obtain ⟨⟨p, q⟩, hpq⟩ := j
    by_cases hc : a ≤ p ∧ p ≤ b
    · exact hc
    · exact absurd ((Functor.map_isZero F (hK p (by omega))).obj _) hj
  · intro j
    obtain ⟨⟨p, q⟩, hpq⟩ := j
    exact hQ p q

/-- **Every term of a local tensor model `Tot(P ⊗_{𝒪_Y} 𝒢_r)` is coherent**, for `Y` a locally
Noetherian scheme, `P` a bounded complex whose terms are direct summands of finite free modules,
and `𝒢_r` a complex of coherent modules.  The term in degree `n` is a coproduct of the
`P^p ⊗ 𝒢_r^q`, each coherent because a direct summand of a finite free module is coherent
(`Stacks.AlgebraicGeometry.PerfectCohomology.isCoherent_of_isDirectSummandOfFiniteFree`, which is
[Stacks, Tag 01BY] (1) applied to the retraction) and a tensor product of coherent modules is
coherent (`AlgebraicGeometry.SheafOfModules.tensorSheaf_isCoherent`, [Stacks, Tag 01CE] (6));
boundedness of `P` leaves finitely many of them nonzero, so
`Stacks.Cohomology.PerfectPushforward.prop_mapBifunctor_X` applies.

The two complexes are handed over at the
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules` spelling for the reason recorded at
`Stacks.Cohomology.PerfectPushforward.isZero_homology_localTensorModel`. -/
private theorem isCoherent_tensorComplex_X (Y : Scheme.{u}) [IsLocallyNoetherian Y]
    (P Gr : CochainComplex (OXMod.{u, u} Y.toRingedSpace) ℤ) (a b : ℤ)
    (hPz : ∀ p : ℤ, p < a ∨ b < p → IsZero (P.X p))
    (hPs : ∀ p : ℤ, IsDirectSummandOfFiniteFree (P.X p))
    (hGc : ∀ q : ℤ, (Gr.X q).IsCoherent) (n : ℤ) :
    Stacks.SheafOfModules.IsCoherent
      ((((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSpace.sheaf).obj P).obj Gr).X n) :=
  prop_mapBifunctor_X
    (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} Y.toRingedSpace.sheaf)
    (show CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules
      Y.toRingedSpace) ℤ from P)
    (show CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules
      Y.toRingedSpace) ℤ from Gr)
    (fun M => Stacks.SheafOfModules.IsCoherent M) a b hPz
    (fun p q =>
      (@AlgebraicGeometry.SheafOfModules.tensorSheaf_isCoherent Y.toRingedSpace (P.X p) (Gr.X q)
        (Stacks.AlgebraicGeometry.PerfectCohomology.isCoherent_of_isDirectSummandOfFiniteFree
          Y (P.X p) (hPs p)).rootIsCoherent (hGc q)).stacksIsCoherent)
    n

/-- **The coherence clause of [Stacks, Tag 0DJQ], proved.**  For `E` perfect and `𝒢` a bounded
complex of coherent `𝒪_X`-modules, flat over `S`, with support proper over `S`, every cohomology
sheaf of `E ⊗^L_{𝒪_X} 𝒢` is coherent.

Coherence is local on an open covering of a locally Noetherian scheme
(`Stacks.AlgebraicGeometry.PerfectCohomology.isCoherent_of_cover_restrict`, condition (5) of
[Stacks, Tag 01XZ]), and `X` is locally Noetherian because `f` is locally of finite type and `S`
is Noetherian.  So it suffices to prove the clause on each member `U` of the covering of
`Stacks.Cohomology.PerfectPushforward.exists_local_tensorComplex_models`, and there
`Stacks.Cohomology.PerfectPushforward.restrictHomologyLocalModelIso` identifies the restricted
cohomology sheaf with the cohomology of `Tot(P ⊗_{𝒪_U} 𝒢|_U)` for a strictly perfect `P`.  The
terms of that complex are coherent
(`Stacks.Cohomology.PerfectPushforward.isCoherent_tensorComplex_X`), and coherent modules form a
weak Serre subcategory
(`SheafOfModules.coherentModules_isWeakSerreClass`), so its cohomology is
coherent too, by `CategoryTheory.ObjectProperty.prop_homology`.

Only the `isCoherent` field of `hG` is used; boundedness, flatness and properness of the support
of `𝒢` play no part in this clause.  The restriction of `𝒢^q` to `U` is coherent by
`Stacks.AlgebraicGeometry.PerfectCohomology.isCoherent_restrict`, read through
`Stacks.AlgebraicGeometry.PerfectCohomology.restrictModulesIsoRestrict` because the local models
restrict along `AlgebraicGeometry.RingedSpace.restrictModules` while that result is stated for
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`; the two coherence classes of the repository
are crossed by `SheafOfModules.IsCoherent.stacksIsCoherent` and
`Stacks.SheafOfModules.IsCoherent.rootIsCoherent`. -/
theorem isCoherent_homology_derivedTensor [IsNoetherian S] [LocallyOfFiniteType f]
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.toRingedSpace.sheaf)
    [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.toRingedSpace.sheaf).Additive]
    [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      X.toRingedSpace.sheaf).obj M).Additive]
    [∀ K L : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules X.toRingedSpace.sheaf) ℤ,
      HomologicalComplex.HasMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.toRingedSpace.sheaf)
        (ComplexShape.up ℤ)]
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (G : CochainComplex (OXMod.{u, u} X.toRingedSpace) ℤ)
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
    (hG : FlatProperSupportComplex f G) (i : ℤ) :
    ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) i).obj
      ((T.tensor.obj E).obj (DerivedCategory.Q.obj G))).IsCoherent := by
  classical
  have hX : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨A, -, ⟨eA⟩, I, U, hU, hmodels⟩ := exists_local_tensorComplex_models X T E G hE
  choose P hP hePn using hmodels
  refine Stacks.AlgebraicGeometry.PerfectCohomology.isCoherent_of_cover_restrict _ U
    (IsOpenCover.mk hU) fun j => ?_
  refine Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isCoherent' ?_
  refine Stacks.AlgebraicGeometry.PerfectCohomology.isCoherentStacks_of_iso
    ((Stacks.AlgebraicGeometry.PerfectCohomology.restrictModulesIsoRestrict X (U j)).app _) ?_
  refine Stacks.AlgebraicGeometry.PerfectCohomology.isCoherentStacks_of_iso
    (restrictHomologyLocalModelIso T E G A eA (U j) (P j) (hePn j).some i).symm ?_
  obtain ⟨aP, bP, -, hPz0⟩ :=
    Stacks.Cohomology.TorAmplitude.exists_bounds_of_isStrictlyPerfect (P j) (hP j)
  have hNU : IsLocallyNoetherian (Scheme.Opens.toScheme (X := X) (U j)) :=
    isLocallyNoetherian_of_isOpenImmersion (Scheme.Opens.ι (X := X) (U j))
  refine ObjectProperty.prop_homology
    (fun M : OXMod.{u, u} (X.toRingedSpace.restrict (U j).isOpenEmbedding) =>
      Stacks.SheafOfModules.IsCoherent M) _ i fun m => ?_
  exact isCoherent_tensorComplex_X (Scheme.Opens.toScheme (X := X) (U j)) (P j)
    (AlgebraicGeometry.RingedSpace.restrictComplex G (U j)) aP bP
    (fun p hp => hPz0 p (by simp only [Set.mem_Icc, not_and_or, not_le]; exact hp))
    (hP j).directSummand
    (fun q => (Stacks.AlgebraicGeometry.PerfectCohomology.isCoherentStacks_of_iso
        ((Stacks.AlgebraicGeometry.PerfectCohomology.restrictModulesIsoRestrict X
          (U j)).app (G.X q)).symm
        (Stacks.AlgebraicGeometry.PerfectCohomology.isCoherent_restrict
          (Scheme.Opens.ι (X := X) (U j)) (G.X q)
          (hG.isCoherent q)).stacksIsCoherent).rootIsCoherent) m

/-! ### Stacks 0DJQ -/

/-- **The inputs of [Stacks, Tag 0DJQ] that this file does not derive.**  `E` is perfect, `𝒢` is
a bounded complex of coherent `𝒪_X`-modules flat over `S` with support proper over `S`, and
`E ⊗^L_{𝒪_X} 𝒢` satisfies **one of the four clauses** of the hypothesis of
[Stacks, Tag 08EV].

The last field is what is left of the source's proof of [Stacks, Tag 0DJQ], and it is
**carried, not derived**.  The source argues: locally `E` is a finite complex of finite free
modules, so locally `E ⊗^L_{𝒪_X} 𝒢` is a finite complex whose terms are finite direct sums of
the `𝒢^i`; hence its cohomology sheaves are coherent, their supports lie in the support of `𝒢`,
only finitely many of them are nonzero, and its Tor dimension over `f⁻¹𝒪_S` is finite because
each `𝒢^i` is flat over `f⁻¹𝒪_S`.

Three of the four clauses are **not** carried.  The support one is derived, by
`Stacks.Cohomology.PerfectPushforward.TensorPushforwardData.input`, from
`Stacks.Cohomology.PerfectPushforward.supp_homology_derivedTensor_subset` together with the
`properSupport` field of `flatProperSupport`.  The boundedness one is derived too, by
`Stacks.Cohomology.PerfectPushforward.TensorPushforwardData.bounded`, from
`Stacks.Cohomology.PerfectPushforward.exists_isZero_homology_derivedTensor`.  So is coherence, by
`Stacks.Cohomology.PerfectPushforward.TensorPushforwardData.isCoherent`, from
`Stacks.Cohomology.PerfectPushforward.isCoherent_homology_derivedTensor`.  That is why none of
the three appears here.

The local description all four clauses go through is proved, as
`Stacks.Cohomology.PerfectPushforward.exists_local_tensorComplex_models`; what the one
still-carried clause needs on top of it is listed in the implementation notes of this file.

The first two fields are what the source asks of `E` and of `𝒢`. -/
structure TensorPushforwardData [LocallyOfFiniteType f]
    (D : RingedSpace.CertifiedDerivedSheafTensoring
      (RingedSpace.inverseImage S.toRingedSpace f.base))
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.toRingedSpace.sheaf)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (G : CochainComplex (OXMod.{u, u} X.toRingedSpace) ℤ) : Prop where
  /-- `E` is a perfect object of `D(𝒪_X)`. -/
  isPerfect : RingedSpace.IsPerfect (X := X.toRingedSpace) E
  /-- `𝒢` is a bounded complex of coherent modules flat over `S` with proper support. -/
  flatProperSupport : FlatProperSupportComplex f G
  /-- `E ⊗^L_{𝒪_X} 𝒢` has finite Tor dimension over `f⁻¹𝒪_S`.  Carried, not derived. -/
  hasFiniteTorDimension :
    D.HasFiniteTorDimension ((Scheme.Hom.derivedScalarRestriction f).obj
      ((T.tensor.obj E).obj (DerivedCategory.Q.obj G)))

/-- **The coherence clause of [Stacks, Tag 08EV] for `E ⊗^L_{𝒪_X} 𝒢`**, derived rather than
carried: it is `Stacks.Cohomology.PerfectPushforward.isCoherent_homology_derivedTensor` applied to
the `isPerfect` and `flatProperSupport` fields.  This declaration replaces what used to be a field
of `Stacks.Cohomology.PerfectPushforward.TensorPushforwardData`, so a consumer writing
`h.isCoherent` is unaffected. -/
theorem TensorPushforwardData.isCoherent [IsNoetherian S] [LocallyOfFiniteType f]
    {D : RingedSpace.CertifiedDerivedSheafTensoring
      (RingedSpace.inverseImage S.toRingedSpace f.base)}
    {T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.toRingedSpace.sheaf}
    [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.toRingedSpace.sheaf).Additive]
    [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      X.toRingedSpace.sheaf).obj M).Additive]
    [∀ K L : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules X.toRingedSpace.sheaf) ℤ,
      HomologicalComplex.HasMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.toRingedSpace.sheaf)
        (ComplexShape.up ℤ)]
    {E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)}
    {G : CochainComplex (OXMod.{u, u} X.toRingedSpace) ℤ}
    (h : TensorPushforwardData f D T E G) (i : ℤ) :
    ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) i).obj
      ((T.tensor.obj E).obj (DerivedCategory.Q.obj G))).IsCoherent :=
  isCoherent_homology_derivedTensor f T E G h.isPerfect h.flatProperSupport i

/-- **The boundedness clause of [Stacks, Tag 08EV] for `E ⊗^L_{𝒪_X} 𝒢`**, derived rather than
carried: it is
`Stacks.Cohomology.PerfectPushforward.exists_isZero_homology_derivedTensor` applied to the
`isPerfect` and `flatProperSupport` fields.  This declaration replaces what used to be a field of
`Stacks.Cohomology.PerfectPushforward.TensorPushforwardData`, so a consumer writing `h.bounded`
is unaffected. -/
theorem TensorPushforwardData.bounded [IsNoetherian S] [LocallyOfFiniteType f]
    {D : RingedSpace.CertifiedDerivedSheafTensoring
      (RingedSpace.inverseImage S.toRingedSpace f.base)}
    {T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.toRingedSpace.sheaf}
    [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.toRingedSpace.sheaf).Additive]
    [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      X.toRingedSpace.sheaf).obj M).Additive]
    [∀ K L : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules X.toRingedSpace.sheaf) ℤ,
      HomologicalComplex.HasMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.toRingedSpace.sheaf)
        (ComplexShape.up ℤ)]
    {E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)}
    {G : CochainComplex (OXMod.{u, u} X.toRingedSpace) ℤ}
    (h : TensorPushforwardData f D T E G) :
    ∃ a b : ℤ, ∀ i : ℤ, i ∉ Set.Icc a b →
      IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) i).obj
        ((T.tensor.obj E).obj (DerivedCategory.Q.obj G))) :=
  exists_isZero_homology_derivedTensor f T E G h.isPerfect h.flatProperSupport

/-- **The hypothesis of [Stacks, Tag 08EV] for `E ⊗^L_{𝒪_X} 𝒢`**, assembled from the one clause
`Stacks.Cohomology.PerfectPushforward.TensorPushforwardData` carries and the three that are
derived.  The support clause: the `properSupport` field of `flatProperSupport` produces one closed
subset `Z` proper over `S` containing the support of every `𝒢^q`, and
`Stacks.Cohomology.PerfectPushforward.supp_homology_derivedTensor_subset` carries it over to the
cohomology sheaves of `E ⊗^L_{𝒪_X} 𝒢`.  The coherence clause is
`Stacks.Cohomology.PerfectPushforward.TensorPushforwardData.isCoherent`.  The boundedness clause
is `Stacks.Cohomology.PerfectPushforward.TensorPushforwardData.bounded`, which is where the
`AlgebraicGeometry.IsNoetherian` hypothesis on `S` is spent: it supplies the `CompactSpace S`
that makes `Z` quasi-compact. -/
theorem TensorPushforwardData.input [IsNoetherian S] [LocallyOfFiniteType f]
    {D : RingedSpace.CertifiedDerivedSheafTensoring
      (RingedSpace.inverseImage S.toRingedSpace f.base)}
    {T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.toRingedSpace.sheaf}
    [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.toRingedSpace.sheaf).Additive]
    [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      X.toRingedSpace.sheaf).obj M).Additive]
    [∀ K L : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules X.toRingedSpace.sheaf) ℤ,
      HomologicalComplex.HasMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.toRingedSpace.sheaf)
        (ComplexShape.up ℤ)]
    {E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)}
    {G : CochainComplex (OXMod.{u, u} X.toRingedSpace) ℤ}
    (h : TensorPushforwardData f D T E G) :
    PushforwardPerfectionInput f D ((T.tensor.obj E).obj (DerivedCategory.Q.obj G)) where
  bounded := h.bounded
  isCoherent := h.isCoherent
  properSupport i := by
    obtain ⟨Z, hZ, hsub⟩ := h.flatProperSupport.properSupport
    exact ⟨Z, hZ, supp_homology_derivedTensor_subset X T E G h.isPerfect _ hsub i⟩
  hasFiniteTorDimension := h.hasFiniteTorDimension

/-- **[Stacks, Tag 0DJQ], conditional form (not the registration of the tag).**  Let `S` be a
Noetherian scheme, `f : X ⟶ S` a morphism locally of finite type, `E` a perfect object of `D(𝒪_X)` and `𝒢` a bounded complex of coherent
`𝒪_X`-modules, flat over `S`, whose support is proper over `S`.  Then
`Rf_*(E ⊗^L_{𝒪_X} 𝒢)` is a perfect object of `D(𝒪_S)`, with `Rf_*` the derived direct image
`Stacks.Cohomology.ProperSupportPerfection.derivedPushforwardOX f` — the total right derived
functor of degreewise pushforward — and not a functor left unspecified.

[Stacks, Tag 08EV] itself is *not* a hypothesis: its conditional form at this spelling is proved
in `StacksFrontier/AlgebraicGeometry/Perfect/ProperSupportPerfection.lean`, and
`Stacks.Cohomology.PerfectPushforward.pushforwardPerfectionCriterion_of_residues` turns it into
the criterion this proof consumes.  What is carried in its place are that theorem's own two
residues, `hcoh` and `htor` — [Stacks, Tag 08E2] for `Rf_*` and the source's closing
Tor-dimension estimate, both statements about that same functor — each of which is strictly
smaller than the conclusion, with its obstruction identified in its own docstring.

One of the four clauses of [Stacks, Tag 08EV]'s hypothesis for `E ⊗^L_{𝒪_X} 𝒢` is still
carried, as the `hasFiniteTorDimension` field of `h`.  The support clause is
proved: see `Stacks.Cohomology.PerfectPushforward.supp_homology_derivedTensor_subset` and
`Stacks.Cohomology.PerfectPushforward.TensorPushforwardData.input`.  So is the boundedness
clause: see
`Stacks.Cohomology.PerfectPushforward.exists_isZero_homology_derivedTensor` and
`Stacks.Cohomology.PerfectPushforward.TensorPushforwardData.bounded`.  So is coherence: see
`Stacks.Cohomology.PerfectPushforward.isCoherent_homology_derivedTensor` and
`Stacks.Cohomology.PerfectPushforward.TensorPushforwardData.isCoherent`.  The geometric step the
remaining clause runs on — that `E ⊗^L_{𝒪_X} 𝒢` is, locally on a covering of `X`, the total tensor
complex of a strictly perfect complex with the restriction of `𝒢` — is proved above, as
`Stacks.Cohomology.PerfectPushforward.exists_local_tensorComplex_models`; what reading it off that
still needs is listed in the implementation notes of this file.

The tag itself is proved with none of these inputs, as
`Stacks.Cohomology.PerfectPushforward.isPerfect_derivedPushforward_derivedTensor_of_isPerfect`,
and registered at the canonical derived tensor product as
`Stacks.Cohomology.PerfectPushforward.isPerfect_derivedPushforward_derivedTensorProductFunctor`;
this conditional form is kept because the reduction of [Stacks, Tag 0B6F] below runs through it. -/
theorem isPerfect_derivedPushforward_derivedTensor [IsNoetherian S] [LocallyOfFiniteType f]
    (D : RingedSpace.CertifiedDerivedSheafTensoring
      (RingedSpace.inverseImage S.toRingedSpace f.base))
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.toRingedSpace.sheaf)
    [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.toRingedSpace.sheaf).Additive]
    [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      X.toRingedSpace.sheaf).obj M).Additive]
    [∀ K L : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules X.toRingedSpace.sheaf) ℤ,
      HomologicalComplex.HasMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.toRingedSpace.sheaf)
        (ComplexShape.up ℤ)]
    (hcoh : PushforwardCoherenceResidue f (derivedPushforwardOX f))
    (htor : PushforwardTorDimensionResidue f D (derivedPushforwardOX f))
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (G : CochainComplex (OXMod.{u, u} X.toRingedSpace) ℤ)
    (h : TensorPushforwardData f D T E G) :
    RingedSpace.IsPerfect (X := S.toRingedSpace)
      ((derivedPushforwardOX f).obj ((T.tensor.obj E).obj (DerivedCategory.Q.obj G))) :=
  pushforwardPerfectionCriterion_of_residues f D hcoh htor _ h.input

/-! ### Stacks 0B6F: the case `𝒢 = 𝒪_X`

A flat proper morphism to a Noetherian scheme makes `𝒪_X`, placed in degree zero, a complex of
the kind [Stacks, Tag 0DJQ] asks for.  This section verifies that, which is the whole of the
reduction of [Stacks, Tag 0B6F] to [Stacks, Tag 0DJQ]. -/

/-- The structure sheaf `𝒪_X` placed in degree zero, as a complex of `𝒪_X`-modules.  This is the
complex `𝒢` of [Stacks, Tag 0DJQ] in the case of [Stacks, Tag 0B6F]. -/
abbrev structureComplex (X : Scheme.{u}) : CochainComplex (OXMod.{u, u} X.toRingedSpace) ℤ :=
  (HomologicalComplex.single (OXMod.{u, u} X.toRingedSpace) (ComplexShape.up ℤ) 0).obj
    (structureModule X.toRingedSpace)

/-- **All of `X` is proper over `S` when `f` is proper.**  The reduced induced closed subscheme
of `⊤` is one closed subscheme structure on `⊤`, and the zero ideal sheaf is another one whose
closed immersion into `X` is an isomorphism (Mathlib's
`AlgebraicGeometry.Scheme.IdealSheafData.isIso_subschemeι_iff_eq_bot`); properness of the
composite of either with `f` therefore follows from properness of `f`, and
`AlgebraicGeometry.isProperOver_iff_exists_isProper` says that one such composite suffices. -/
theorem isProperOver_top_of_isProper [IsProper f] : IsProperOver f (⊤ : Closeds X) := by
  rw [isProperOver_iff_exists_isProper]
  exact ⟨⊥, Scheme.IdealSheafData.support_bot, inferInstance⟩

/-- **The structure sheaf of a locally Noetherian scheme is coherent**, at the
`StrictlyPerfect.OXMod` spelling of the category of `𝒪_X`-modules.  This is
`Stacks.AlgebraicGeometry.CoherentKernel.structureSheaf_isCoherent`, which is stated for
`AlgebraicGeometry.Scheme.Modules`; the two categories are the same, and the two structure
modules are the same sheaf of modules, but neither identification is one instance search
crosses, so the transfer is made once here. -/
@[sga "6 I 3.6"]
theorem isCoherent_structureModule (X : Scheme.{u}) [IsLocallyNoetherian X] :
    (structureModule X.toRingedSpace).IsCoherent :=
  Stacks.AlgebraicGeometry.CoherentKernel.structureSheaf_isCoherent X

/-- **Every term of `𝒪_X` in degree zero is a coherent `𝒪_X`-module** when `X` is locally
Noetherian: in degree zero it is the structure sheaf, coherent by [Stacks, Tag 01XZ], and in
every other degree it is a zero object, coherent by
`Stacks.SheafOfModules.isCoherent_of_isZero`. -/
theorem isCoherent_structureComplex_X (X : Scheme.{u}) [IsLocallyNoetherian X] (i : ℤ) :
    ((structureComplex X).X i).IsCoherent := by
  by_cases hi : i = 0
  · subst hi
    exact (show ObjectProperty (OXMod.{u, u} X.toRingedSpace) from
        fun M => M.IsCoherent).prop_of_iso
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
        (structureModule X.toRingedSpace)).symm (isCoherent_structureModule X)
  · exact (show ObjectProperty (OXMod.{u, u} X.toRingedSpace) from
        fun M => M.IsCoherent).prop_of_isZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
        (structureModule X.toRingedSpace) i hi)

/-- **Flatness of a module with scalars restricted along a ring homomorphism, read off an
additive isomorphism.**  Let `C` be a `B`-module, `φ : A →+* B` and `ε : C ≃+ B` an additive
isomorphism carrying the action of `B` on `C` to multiplication in `B`.  Then `C`, with scalars
restricted along `φ`, is flat over `A` as soon as `B` is.

This is the algebraic step of
`Stacks.Cohomology.PerfectPushforward.isFlatOver_structureModule`, isolated: restriction of
scalars is what `AlgebraicGeometry.IsFlatOverAt` performs, and writing it here rather than at the
geometric statement keeps it away from the three spellings of the structure sheaf.

The `B`-module structure on `C` is an explicit argument rather than an instance, so that a
consumer can hand over the one its own goal carries: the stalk of a sheaf of modules has more
than one `Module` instance available in the import closure of this file, and instance search
need not choose the one a given goal was built with. -/
private theorem flat_compHom_of_addEquiv {A B C : Type u} [CommRing A] [CommRing B]
    [AddCommGroup C] (instBC : Module B C) (φ : A →+* B) (ε : C ≃+ B)
    (hε : letI := instBC; ∀ (b : B) (c : C), ε (b • c) = b * ε c)
    (h : @Module.Flat A B _ _ (Module.compHom B φ)) :
    letI := instBC
    @Module.Flat A C _ _ (Module.compHom C φ) := by
  let _ := instBC
  let _ : Module A B := Module.compHom B φ
  let _ : Module A C := Module.compHom C φ
  refine Module.Flat.of_linearEquiv (M := B) (N := C) { ε with map_smul' := fun a c => ?_ }
  change ε (φ a • c) = φ a • ε c
  rw [hε, smul_eq_mul]

/-- **A subsingleton module is flat**, whatever its module structure: it is free, being a
subsingleton, and a free module is flat.  The module structure is an explicit argument for the
reason recorded at `Stacks.Cohomology.PerfectPushforward.flat_compHom_of_addEquiv`. -/
private theorem flat_of_subsingleton_inst {A C : Type u} [CommRing A] [AddCommGroup C]
    [Subsingleton C] (inst : Module A C) : @Module.Flat A C _ _ inst := by
  let _ := inst
  exact Module.Flat.of_free

/-- **The comparison of the stalk of the unit module with the stalk of the ring is semilinear.**
For a presheaf of commutative rings `R` on a space, the stalk of `PresheafOfModules.unit` of the
underlying presheaf of rings — a filtered colimit taken in `AddCommGrpCat` — is compared with the
stalk of `R` itself, the same colimit taken in `CommRingCat`, by
`LocallyFreeRank.unitStalkLEquiv` followed by
`AlgebraicGeometry.SemilinearStalk.commStalkRingEquiv`.  The first is linear over the stalk read
in `RingCat`, the second identifies that stalk with the one read in `CommRingCat`, and
`AlgebraicGeometry.SemilinearStalk.comm_smul_eq` says the identification does not change the
action; so the composite carries the action of `R_x` to multiplication in `R_x`.

Stated for a bare presheaf of rings rather than for the structure sheaf of a scheme, so that
both sides are written at one spelling of the presheaf of modules; the geometric statement
`Stacks.Cohomology.PerfectPushforward.isFlatOver_structureModule` consumes it across the
identification of `StrictlyPerfect.structureModule` with that unit module. -/
private theorem unitStalk_smul_eq {Y : TopCat.{u}} (R : TopCat.Presheaf CommRingCat.{u} Y)
    (y : Y) (b : R.stalk y)
    (m : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (PresheafOfModules.unit (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})).presheaf y) :
    ((LocallyFreeRank.unitStalkLEquiv
          (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) y).toAddEquiv.trans
        (SemilinearStalk.commStalkRingEquiv R y).toAddEquiv) (b • m) =
      b * ((LocallyFreeRank.unitStalkLEquiv
          (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) y).toAddEquiv.trans
        (SemilinearStalk.commStalkRingEquiv R y).toAddEquiv) m := by
  set e0 := LocallyFreeRank.unitStalkLEquiv (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) y with he0
  set e1 := SemilinearStalk.commStalkRingEquiv R y with he1
  have hs : e1 (e1.symm b) = b := e1.apply_symm_apply _
  have h1 := SemilinearStalk.comm_smul_eq R y
    (PresheafOfModules.unit (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})) (e1.symm b) m
  rw [hs] at h1
  change e1 (e0 (b • m)) = b * e1 (e0 m)
  rw [h1, map_smul e0, smul_eq_mul, map_mul, hs]

/-- **A zero `𝒪_X`-module is flat over `S`.**  Its stalk at a point is a zero object of
`AddCommGrpCat`, hence a subsingleton, hence free and so flat over any ring acting on it — in
particular over `𝒪_{S, f(x)}` acting through the stalk map of `f`.

This is the `StrictlyPerfect.OXMod` spelling.  A statement of the same fact for
`AlgebraicGeometry.Scheme.Modules`, `AlgebraicGeometry.isFlatOver_of_isZero`, is on the way into
`StacksFrontier/AlgebraicGeometry/Flatness/Devissage/Complete/AlgebraicFlatness.lean`; the two
categories are the same, so when it is available this declaration should be replaced by it
rather than kept alongside. -/
theorem isFlatOver_of_isZero_oxMod (M : OXMod.{u, u} X.toRingedSpace) (hM : IsZero M) :
    IsFlatOver f.toLRSHom.toShHom M := by
  intro x
  have hstalk : IsZero
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf x) :=
    (AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj_iff
      (structureSheafOfRings X.toRingedSpace) x M).1 (Functor.map_isZero _ hM)
  rw [AddCommGrpCat.isZero_iff_subsingleton] at hstalk
  have : Subsingleton
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf x) := hstalk
  exact flat_of_subsingleton_inst _

/-- **The structure sheaf of `X` is flat over `S` when `f` is flat**, which is
[Stacks, Tag 02N3].  `AlgebraicGeometry.Flat.stalkMap` gives flatness of the stalk of the
structure *sheaf* of `X` over the stalk of the structure sheaf of `S`, while
`AlgebraicGeometry.IsFlatOverAt` asks for flatness of the stalk of the structure *module*, which
is the same filtered colimit taken in `AddCommGrpCat` rather than in `CommRingCat`.
`Stacks.Cohomology.PerfectPushforward.unitStalk_smul_eq` is the comparison of the two colimits,
and `Stacks.Cohomology.PerfectPushforward.flat_compHom_of_addEquiv` transports flatness across
it, restricting scalars along the stalk map of `f` on both sides. -/
@[stacks 02N3 "the structure sheaf of the source is flat over the target", ega "IV 2.1.1" "partial"]
theorem isFlatOver_structureModule [Flat f] :
    IsFlatOver f.toLRSHom.toShHom (structureModule X.toRingedSpace) := fun x =>
  flat_compHom_of_addEquiv _ (f.toLRSHom.toShHom.hom.stalkMap x).hom
    ((LocallyFreeRank.unitStalkLEquiv
        (structureSheafOfRings X.toRingedSpace).obj x).toAddEquiv.trans
      (SemilinearStalk.commStalkRingEquiv X.presheaf x).toAddEquiv)
    (unitStalk_smul_eq X.presheaf x) (AlgebraicGeometry.Flat.stalkMap f x)

/-- **Every term of `𝒪_X` in degree zero is flat over `S` when `f` is flat.**  In degree zero the
term is the structure sheaf, flat over `S` by
`Stacks.Cohomology.PerfectPushforward.isFlatOver_structureModule`; in every other degree it is a
zero object, flat by `Stacks.Cohomology.PerfectPushforward.isFlatOver_of_isZero_oxMod`.
Flatness over the base depends only on the isomorphism class of the module
(`AlgebraicGeometry.isFlatOver_iff_of_moduleIso`), which is what carries the degree-zero term to
the structure sheaf itself. -/
theorem isFlatOver_structureComplex [Flat f] (i : ℤ) :
    IsFlatOver f.toLRSHom.toShHom ((structureComplex X).X i) := by
  by_cases hi : i = 0
  · subst hi
    rw [isFlatOver_iff_of_moduleIso f.toLRSHom.toShHom
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
        (structureModule X.toRingedSpace))]
    exact isFlatOver_structureModule f
  · exact isFlatOver_of_isZero_oxMod f _
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
        (structureModule X.toRingedSpace) i hi)

/-- **The structure sheaf in degree zero is a complex of the kind [Stacks, Tag 0DJQ] asks for**,
for a flat proper morphism to a Noetherian scheme: it is bounded, its terms are coherent, each of
them is flat over `S`, and its support is contained in `⊤`, which is proper over `S`.

Flatness over `S` is `Stacks.Cohomology.PerfectPushforward.isFlatOver_structureComplex`, i.e.
flatness of `f` itself ([Stacks, Tag 02N3]). -/
theorem flatProperSupportComplex_structureComplex [IsNoetherian S] [Flat f] [IsProper f] :
    FlatProperSupportComplex f (structureComplex X) where
  bounded := ⟨0, 0,
    inferInstanceAs (CochainComplex.IsStrictlyGE
      ((HomologicalComplex.single (OXMod.{u, u} X.toRingedSpace)
        (ComplexShape.up ℤ) 0).obj (structureModule X.toRingedSpace)) 0),
    inferInstanceAs (CochainComplex.IsStrictlyLE
      ((HomologicalComplex.single (OXMod.{u, u} X.toRingedSpace)
        (ComplexShape.up ℤ) 0).obj (structureModule X.toRingedSpace)) 0)⟩
  isCoherent := by
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    exact isCoherent_structureComplex_X X
  isFlatOver := isFlatOver_structureComplex f
  properSupport := ⟨⊤, isProperOver_top_of_isProper f, fun _ => by simp⟩

/-- **The unit constraint `E ⊗^L_{𝒪_X} 𝒪_X ≅ E`** of [Stacks, Tag 0FPT], read with `𝒪_X` spelled
as the complex `Stacks.Cohomology.PerfectPushforward.structureComplex`.

`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso` states it with `𝒪_X` spelled
by `DerivedCategory.singleFunctor`; `DerivedCategory.singleFunctorIsoCompQ` is the comparison of
that with the localization of `HomologicalComplex.single`. -/
def tensorStructureComplexIso
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.toRingedSpace.sheaf)
    [tensorAdditive : (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      X.toRingedSpace.sheaf).Additive]
    [tensorObjAdditive : ∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      X.toRingedSpace.sheaf).obj M).Additive]
    [tensorTotalization : ∀ K L :
      CochainComplex (Stacks.DerivedTensor.RingedSite.Modules X.toRingedSpace.sheaf) ℤ,
      HomologicalComplex.HasMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.toRingedSpace.sheaf)
        (ComplexShape.up ℤ)]
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :
    (T.tensor.obj E).obj (DerivedCategory.Q.obj (structureComplex X)) ≅ E :=
  (T.tensor.obj E).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ (OXMod.{u, u} X.toRingedSpace) 0).app
        (structureModule X.toRingedSpace)).symm ≪≫
    @Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso (schemeSite X)
      inferInstance inferInstance tensorAdditive tensorObjAdditive tensorTotalization T E

/-- **The boundedness clause of [Stacks, Tag 08EV] for a perfect `E`, when `f` is proper, proved.**
Only finitely many cohomology sheaves of a perfect object of `D(𝒪_X)` are nonzero as soon as `X`
is quasi-compact, and it is: a proper morphism is quasi-compact and `S` is Noetherian, hence
quasi-compact, so `AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace` makes the space of
`X` compact.

On a member `U` of the covering carrying a strictly perfect model `P` the restriction to `U` of
the `n`-th cohomology sheaf of `E` is `H^n(P)`
(`Stacks.AlgebraicGeometry.PerfectCohomology.derivedHomologyRestrictIso`), which vanishes outside
the range of `P` (`Stacks.Cohomology.TorAmplitude.exists_bounds_of_isStrictlyPerfect`); finitely
many members cover `X`, so their ranges have a common lower and a common upper bound; and outside
that interval the support of the cohomology sheaf meets no member
(`Stacks.AlgebraicGeometry.PerfectCohomology.notMem_supp_of_isZero_restrictModules`), hence is
empty, hence the sheaf is zero (`SheafOfModules.isZero_of_supp_eq_empty`).

This is the boundedness clause of [Stacks, Tag 0DJQ] read at `𝒢 = 𝒪_X`, but proved directly: at
`𝒢 = 𝒪_X` the support of `𝒢` is all of `X`, so the compactness used by
`Stacks.Cohomology.PerfectPushforward.exists_isZero_homology_derivedTensor` is compactness of `X`
itself and the derived tensor product plays no part. -/
theorem exists_isZero_homology_of_isProper [IsNoetherian S] [IsProper f]
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E) :
    ∃ a b : ℤ, ∀ i : ℤ, i ∉ Set.Icc a b →
      IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) i).obj E) := by
  classical
  obtain ⟨E', ⟨I, U, hU, hmodels⟩, ⟨eEK⟩⟩ := hE
  choose P hP fP hfP using hmodels
  have hbd : ∀ i : I, ∃ a b : ℤ, ∀ n : ℤ, n ∉ Set.Icc a b →
      IsZero ((AlgebraicGeometry.RingedSpace.restrictModules X.toRingedSpace (U i)).obj
        ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) n).obj E)) := by
    intro i
    obtain ⟨aP, bP, -, hPz⟩ :=
      Stacks.Cohomology.TorAmplitude.exists_bounds_of_isStrictlyPerfect (P i) (hP i)
    refine ⟨aP, bP, fun n hn => ?_⟩
    have hzeroH : IsZero ((P i).homology n) := by
      simpa [HomologicalComplex.homology] using
        ShortComplex.isZero_homology_of_isZero_X₂ ((P i).sc n) (hPz n hn)
    exact hzeroH.of_iso (Stacks.AlgebraicGeometry.PerfectCohomology.derivedHomologyRestrictIso
      X (U i) eEK (fP i) (hfP i) n).symm
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  exact exists_isZero_of_cover_bounds U hU isCompact_univ
    (fun n => (DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) n).obj E)
    (fun _ => Set.subset_univ _) hbd

/-- **The inputs of [Stacks, Tag 0B6F] that this file does not derive.**

The source's proof of [Stacks, Tag 0B6F] verifies the hypothesis of [Stacks, Tag 08EV] for `E`
itself: clauses (1) and (2) it calls immediate, and clause (3) it reduces to the affine case,
where `𝒪_X` is flat as a sheaf of `f⁻¹𝒪_S`-modules.  One of the four clauses is carried here;
the other three are not.  The support clause is free, because for a proper `f` all of `X` is proper
over `S` (`Stacks.Cohomology.PerfectPushforward.isProperOver_top_of_isProper`), so `⊤` serves as
the closed subset for every cohomology sheaf at once.  The boundedness clause is proved, by
`Stacks.Cohomology.PerfectPushforward.exists_isZero_homology_of_isProper`, from quasi-compactness
of `X`.  So is the coherence clause, by
`Stacks.Cohomology.PerfectPushforward.FlatProperPushforwardData.isCoherent`, which is
[Stacks, Tag 0FEP].  See `Stacks.Cohomology.PerfectPushforward.FlatProperPushforwardData.input`.

Everything else in the reduction of [Stacks, Tag 0B6F] to [Stacks, Tag 0DJQ] is proved, flatness
of `𝒪_X` over `S` included
(`Stacks.Cohomology.PerfectPushforward.isFlatOver_structureComplex`). -/
structure FlatProperPushforwardData [IsProper f]
    (D : RingedSpace.CertifiedDerivedSheafTensoring
      (RingedSpace.inverseImage S.toRingedSpace f.base))
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) : Prop where
  /-- `E` is a perfect object of `D(𝒪_X)`. -/
  isPerfect : RingedSpace.IsPerfect (X := X.toRingedSpace) E
  /-- `E` has finite Tor dimension over `f⁻¹𝒪_S`.  Carried, not derived. -/
  hasFiniteTorDimension :
    D.HasFiniteTorDimension ((Scheme.Hom.derivedScalarRestriction f).obj E)

/-- **The coherence clause of [Stacks, Tag 08EV] for `E`**, derived rather than carried: the
cohomology sheaves of a perfect object on a locally Noetherian scheme are coherent, which is
[Stacks, Tag 0FEP] (`Stacks.AlgebraicGeometry.PerfectCohomology.isCoherent_homology`), and `X` is
locally Noetherian because a proper morphism is locally of finite type and `S` is Noetherian.
This declaration replaces what used to be a field of
`Stacks.Cohomology.PerfectPushforward.FlatProperPushforwardData`, so a consumer writing
`h.isCoherent` is unaffected. -/
theorem FlatProperPushforwardData.isCoherent [IsNoetherian S] [IsProper f]
    {D : RingedSpace.CertifiedDerivedSheafTensoring
      (RingedSpace.inverseImage S.toRingedSpace f.base)}
    {E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)}
    (h : FlatProperPushforwardData f D E) (i : ℤ) :
    ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) i).obj E).IsCoherent :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  Stacks.AlgebraicGeometry.PerfectCohomology.isCoherent_homology X E h.isPerfect i

/-- **The boundedness clause of [Stacks, Tag 08EV] for `E`**, derived rather than carried: it is
`Stacks.Cohomology.PerfectPushforward.exists_isZero_homology_of_isProper` applied to the
`isPerfect` field.  This declaration replaces what used to be a field of
`Stacks.Cohomology.PerfectPushforward.FlatProperPushforwardData`, so a consumer writing
`h.bounded` is unaffected. -/
theorem FlatProperPushforwardData.bounded [IsNoetherian S] [IsProper f]
    {D : RingedSpace.CertifiedDerivedSheafTensoring
      (RingedSpace.inverseImage S.toRingedSpace f.base)}
    {E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)}
    (h : FlatProperPushforwardData f D E) :
    ∃ a b : ℤ, ∀ i : ℤ, i ∉ Set.Icc a b →
      IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) i).obj E) :=
  exists_isZero_homology_of_isProper f E h.isPerfect

/-- **The hypothesis of [Stacks, Tag 08EV] for `E`**, assembled from the one clause
`Stacks.Cohomology.PerfectPushforward.FlatProperPushforwardData` carries and the three that are
derived.  The support clause, for a proper `f`, is free: `⊤` is a closed subset of `X` proper over
`S` (`Stacks.Cohomology.PerfectPushforward.isProperOver_top_of_isProper`) and it contains every
support.  The coherence clause is
`Stacks.Cohomology.PerfectPushforward.FlatProperPushforwardData.isCoherent`.  The boundedness
clause is
`Stacks.Cohomology.PerfectPushforward.FlatProperPushforwardData.bounded`, which is where the
`AlgebraicGeometry.IsNoetherian` hypothesis on `S` is spent: it supplies the `CompactSpace S`
from which quasi-compactness of `X` is read off. -/
theorem FlatProperPushforwardData.input [IsNoetherian S] [IsProper f]
    {D : RingedSpace.CertifiedDerivedSheafTensoring
      (RingedSpace.inverseImage S.toRingedSpace f.base)}
    {E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)}
    (h : FlatProperPushforwardData f D E) : PushforwardPerfectionInput f D E where
  bounded := h.bounded
  isCoherent := h.isCoherent
  properSupport _ := ⟨⊤, isProperOver_top_of_isProper f, by simp⟩
  hasFiniteTorDimension := h.hasFiniteTorDimension

/-- **[Stacks, Tag 0B6F].**  Let `S` be a Noetherian scheme, `f : X ⟶ S` a flat proper morphism
and `E` a perfect object of `D(𝒪_X)`.  Then `Rf_*E` is a perfect object of `D(𝒪_S)`.

This is [Stacks, Tag 0DJQ] at `𝒢 = 𝒪_X` in degree zero, and the reduction is proved here: `f` is
locally of finite type because it is proper, so `X` is locally Noetherian and `𝒪_X` is coherent
([Stacks, Tag 01XZ], `Stacks.Cohomology.PerfectPushforward.isCoherent_structureComplex_X`); the
complex is bounded; its support is all of `X`, which is proper over `S` because `f` is
(`Stacks.Cohomology.PerfectPushforward.isProperOver_top_of_isProper`); and
`E ⊗^L_{𝒪_X} 𝒪_X ≅ E` is the unit constraint of [Stacks, Tag 0FPT]
(`Stacks.Cohomology.PerfectPushforward.tensorStructureComplexIso`), along which the hypothesis of
[Stacks, Tag 08EV] transports by
`Stacks.Cohomology.PerfectPushforward.PushforwardPerfectionInput.of_iso` and perfectness of the
direct image by `AlgebraicGeometry.RingedSpace.IsPerfect.of_iso`.

Flatness of `𝒪_X` over `S` is flatness of `f` ([Stacks, Tag 02N3]),
`Stacks.Cohomology.PerfectPushforward.isFlatOver_structureComplex`.

The source proves [Stacks, Tag 0B6F] from [Stacks, Tag 08EV] directly rather than from
[Stacks, Tag 0DJQ], but asks for nothing extra: a flat proper morphism to a Noetherian scheme is
exactly what makes `𝒪_X` a complex of the kind [Stacks, Tag 0DJQ] admits.

The direct image is `Stacks.Cohomology.ProperSupportPerfection.derivedPushforwardOX f`, the total
right derived functor of degreewise pushforward, and not a functor left unspecified.

What `h` carries is one of the four clauses of [Stacks, Tag 08EV]'s hypothesis for `E`; the
support clause is derived, from properness of `f`, the boundedness clause from quasi-compactness
of `X` (`Stacks.Cohomology.PerfectPushforward.exists_isZero_homology_of_isProper`) and the
coherence clause from [Stacks, Tag 0FEP]
(`Stacks.Cohomology.PerfectPushforward.FlatProperPushforwardData.isCoherent`).
[Stacks, Tag 08EV] itself is not a
hypothesis: its conditional form at this spelling is proved in
`StacksFrontier/AlgebraicGeometry/Perfect/ProperSupportPerfection.lean` and reaches this proof
through `Stacks.Cohomology.PerfectPushforward.pushforwardPerfectionCriterion_of_residues`, so
`hcoh` and `htor` — its two residues, [Stacks, Tag 08E2] for `Rf_*` and the source's closing
Tor-dimension estimate, both statements about that same functor — stand in its place. -/
theorem isPerfect_derivedPushforward_of_flatProper [IsNoetherian S] [Flat f] [IsProper f]
    (D : RingedSpace.CertifiedDerivedSheafTensoring
      (RingedSpace.inverseImage S.toRingedSpace f.base))
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.toRingedSpace.sheaf)
    [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.toRingedSpace.sheaf).Additive]
    [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      X.toRingedSpace.sheaf).obj M).Additive]
    [∀ K L : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules X.toRingedSpace.sheaf) ℤ,
      HomologicalComplex.HasMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.toRingedSpace.sheaf)
        (ComplexShape.up ℤ)]
    (hcoh : PushforwardCoherenceResidue f (derivedPushforwardOX f))
    (htor : PushforwardTorDimensionResidue f D (derivedPushforwardOX f))
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (h : FlatProperPushforwardData f D E) :
    RingedSpace.IsPerfect (X := S.toRingedSpace) ((derivedPushforwardOX f).obj E) := by
  have hiso := tensorStructureComplexIso (X := X) T E
  have hin := PushforwardPerfectionInput.of_iso f h.input hiso.symm
  have key := isPerfect_derivedPushforward_derivedTensor f D T hcoh htor E (structureComplex X)
    { isPerfect := h.isPerfect
      flatProperSupport := flatProperSupportComplex_structureComplex f
      hasFiniteTorDimension := hin.hasFiniteTorDimension }
  exact key.of_iso ((derivedPushforwardOX f).mapIso hiso)

end Stacks.Cohomology.PerfectPushforward

end
