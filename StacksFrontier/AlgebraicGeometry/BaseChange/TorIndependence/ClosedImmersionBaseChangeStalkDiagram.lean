module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.ClosedImmersionBaseChangeOnImage
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsRestrictComp
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsRingIso

/-!
# The derived stalk of the base change map and the ring comparison, as one diagram

Consider a cartesian diagram of schemes

```
Z' --i'--> X'
|g          |f
Z --i-----> X
```

with `i` a closed immersion, and suppose `Z` and `X'` are Tor independent over `X`.  Stacks 0E23
asserts that the derived base change map `Lf^*(Ri_* K) ⟶ Ri'_*(Lg^* K)` of Stacks 08HY is an
isomorphism of functors `D(𝒪_Z) ⟶ D(𝒪_{X'})`.

`StacksFrontier/AlgebraicGeometry/BaseChange/TorIndependence/ClosedImmersionBaseChangeOnImage.lean`
reduces that to the derived stalks at the points of `Z'`, and supplies, at each point `w : Z'`,
the invertibility of the ring-level comparison of Stacks 0661 at the four local rings of the
square.  What stood between the two was that the geometric derived stalk and the ring-level
comparison could not be written in one diagram: the stalk of `Lf^*` is taken over
`𝒪_{X, f (i' w)}` and the stalk of `Ri_*` over `𝒪_{X, i (g w)}`, two presentations of one local
ring, so the chain of comparisons on the source of the base change map produces derived extension
of scalars along a *composite* of a ring isomorphism with a germ map, while Stacks 0661 is stated
at a single germ map.

This file closes that gap and states the resulting single equality.  With
`StacksDraft.DerivedRingIso.derivedExtensionScalarsRestrictIso` the composite is identified with
derived extension of scalars along the composite homomorphism, and the two chains of comparisons
become two isomorphisms of functors with the ring-level comparison's source and target as their
targets.  Stacks 0E23 is then equivalent — under Tor independence — to the single equality
`DerivedStalkBaseChangeEq`: that the derived stalk of the base change map, read through those two
chains, *is* the comparison of Stacks 0661.

Nothing in this file carries the tag of Stacks 0E23.  What is proved here is the reduction of it to one
equality of morphisms, together with the two inputs that equality needs in order to be stated at
all.  Stacks 0E23 itself is proved without that equality, as
`Stacks.Cohomology.ClosedImmersionBaseChange.derivedBaseChangeSquareAsIso` in
`ClosedImmersionBaseChangeTorIndependent.lean`, in this directory.

## Main definitions

* `Stacks.Cohomology.ClosedImmersionBaseChange.derivedStalkSourceIso`: the chain of comparisons on
  the source, `(Lf^*(Ri_* -))_{i' w} ≅ 𝒪_{X',i'w} ⊗ᴸ_{𝒪_{X,i(gw)}} (-)_{g w}`, as an isomorphism
  of functors.
* `Stacks.Cohomology.ClosedImmersionBaseChange.derivedStalkTargetIso`: the chain of comparisons on
  the target, `(Ri'_*(Lg^* -))_{i' w} ≅ ((-)_{g w} ⊗ᴸ_{𝒪_{Z,gw}} 𝒪_{Z',w})` restricted along the
  germ map of `i'`, as an isomorphism of functors.
* `Stacks.Cohomology.ClosedImmersionBaseChange.stalkComparison`: the comparison of Stacks 0661 at
  the four local rings of the square, at the canonical models of the two total derived
  extension-of-scalars functors.
* `Stacks.Cohomology.ClosedImmersionBaseChange.DerivedStalkBaseChangeEq`: **the one remaining
  equality**, as a proposition attached to the square.
* `Stacks.Cohomology.ClosedImmersionBaseChange.derivedBaseChangeSquareIsoOfEq`: Stacks 0E23 as an
  isomorphism of functors, from that equality and Tor independence.

## Main results

* `Stacks.Cohomology.ClosedImmersionBaseChange.ptEq`: the two presentations `i (g w)` and
  `f (i' w)` of the image point of `w` in `X` agree.
* `Stacks.Cohomology.ClosedImmersionBaseChange.derivedExtensionStalkIso`: derived extension of
  scalars along the germ map of `f`, precomposed with derived restriction of scalars along the
  comparison of the two presentations of the image point, is derived extension of scalars along
  the composite.  This is what lets the source chain land on the functor Stacks 0661 is stated at.
* `Stacks.Cohomology.ClosedImmersionBaseChange.derivedExtensionStalkIso_hom_app_Q_comp_alphaG`:
  that isomorphism, composed with the comparison `alphaG` of Stacks 0661's source functor with
  termwise extension of scalars, computed at a complex.
* `Stacks.Cohomology.ClosedImmersionBaseChange.isIso_stalkComparison`: the comparison of Stacks
  0661 is invertible at the canonical models, which is
  `isIso_derivedBaseChangeComparison_stalk` instantiated.
* `Stacks.Cohomology.ClosedImmersionBaseChange.isIso_derivedStalk_derivedBaseChangeMap_of_eq`: the
  derived stalk of the base change map at a point of `Z'` is invertible, from the equality.
* `Stacks.Cohomology.ClosedImmersionBaseChange.isIso_derivedBaseChangeSquare_of_eq`: the morphism
  of functors of Stacks 08HY is an isomorphism, from the equality.

## Implementation notes

*What the equality replaces.*  `isIso_derivedBaseChangeSquare_of_onImage` already reduces Stacks
0E23 to a hypothesis, but that hypothesis is the invertibility of the derived stalk of the base
change map, which is exactly what Stacks 0E23 asserts; assuming it assumes the conclusion.  The
hypothesis here is an *equality of two canonical morphisms*, neither of which is asserted to be
invertible, and the invertibility is then supplied by Stacks 0661.  That is why this reduction is
progress and the earlier one was only a bookkeeping device.

*Why the two chains are stated at the canonical models.*  Stacks 0661 is parametric in the two
models of total derived extension of scalars, and `isIso_derivedBaseChangeComparison_stalk` keeps
that parametricity.  The geometric side has no freedom: `AlgebraicGeometry.derivedPullbackStalkIso`
is stated at `CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars`.  So `Lg` and
`Lh` below pin the models to that one, `alphaG` and `alphaH` pin the two comparisons, and the two
`local instance`s re-seat the left-derived universal property where the let-telescope of Stacks
0661 can pick it up.

*Why `alphaG` and `alphaH` are restated rather than used as they come.*  The underived functor of
a `Functor.IsLeftDerivedFunctor` is implicit, inferred from the comparison's type.  At
`TotalDerivedExtensionScalars.comparison` that type names
`CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexGeneral`, while the telescope of
`RingTheory.TorIndependence.derivedBaseChangeComparison` names
`(ModuleCat.extendScalars _).mapHomologicalComplex _ ⋙ DerivedCategory.Q`.  The two are
definitionally equal, by one delta step on a definition that is not reducible, and instance search
runs at reducible transparency, so an instance stated at the first spelling is not found at the
second.  The two `abbrev`s ascribe the second spelling; the terms are unchanged.

*Why the inverse of the point comparison is given by `TopCat.Presheaf.stalkCongr` of the symmetric
equation rather than by `Iso.inv`.*  `derivedStalkFunctorCongr` of
`ClosedImmersionBaseChangeOnImage.lean` restricts scalars along
`(stalkCongr (Inseparable.of_eq h)).hom` and is proved by substituting `b` for `a`, so applying it
to `hpt.symm` is what produces the comparison in the direction the source chain needs.  The two
germ maps are then mutually inverse by `stalkCongr_symm_hom_hom_apply` and
`stalkCongr_hom_symm_hom_apply`, which are again proved by substitution and so must be stated for
a free equation of points, not for `hpt` itself.

*About `DerivedStalkBaseChangeEq`.*  Stacks 0E23 is proved without it.  Its two sides are
characterized by counit equations — the base change map by
`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_adjoint` together with
`Stacks.Cohomology.ExactPushforwardAdjunction.derivedAdjunction_counit_app_eq`, the ring
comparison by `RingTheory.TorIndependence.derivedBaseChangeComparison_snd_app_comp_counit` — and
the underived bridge between them is
`Stacks.ModuleSkyscraper.extendScalars_map_pushStalkMap_comp_counit`, carried to a K-flat
resolution by `AlgebraicGeometry.derivedPullbackStalkIso_hom_app_eq_of_kFlatResolution`.

The two compatibilities that this paragraph used to name as missing are both available now, and
neither is the obstruction any more.  That
`Stacks.ClosedImmersion.stalkPushforwardModuleMap` is the germ map
`Stacks.ModuleSkyscraper.pushStalkMap` across the two spellings of the stalk of the sheaf of
rings is
`AlgebraicGeometry.pushStalkMap_app_eq_restrictScalarsStalkPushforwardMap`; the compatibility of
`AlgebraicGeometry.derivedPullbackStalkIso` with the composition isomorphism of derived pullbacks
of Tag 0D5S — which is what
`Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft` contributes to the adjoint
description of the base change map — is `AlgebraicGeometry.derivedPullbackStalkCompIso_eq`, now
unconditional.  The unit half of the mate correspondence is
`AlgebraicGeometry.map_unit_comp_restrictScalarsStalkPushforwardMap`, and the derived unit of
`Lf^* ⊣ Rf_*` is computed on a K-flat complex by
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_unit_app_eq_of_isKFlat`.

Both chains are now described at a complex.  The target chain is computed against the comparison
tail of Stacks 0661, unconditionally, by
`Stacks.Cohomology.ClosedImmersionBaseChange.derivedStalkTargetIso_hom_app_Q_comp_comparison`;
the source chain at `DerivedCategory.Q.obj P` is
`Stacks.Cohomology.ClosedImmersionBaseChange.derivedStalkSourceIso_hom_app_Q`, which goes through
the description below `DerivedCategory.Q` of the derived stalk of `Ri_*` on the image,
`AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing_hom_app_Q`.

*The compatibility of the source chain's last step with Stacks 0661 is available now.*  It is
`derivedExtensionStalkIso_hom_app_Q_comp_alphaG`, which is
`StacksDraft.DerivedRingIso.derivedExtensionScalarsRestrictIso_hom_app_Q_comp_comparison` at the
germ comparison.  This used to be the second of the two statements the equality was waiting on,
and it was blocked by the *construction* of
`StacksDraft.DerivedRingIso.derivedExtensionScalarsRestrictIso`, which was an
`CategoryTheory.Adjunction.leftAdjointUniq` of two adjunctions and so characterized only by their
units — nothing about the isomorphism below `DerivedCategory.Q`.  That isomorphism is now built as
the unique comparison of two total left derived functors of termwise extension of scalars along
the composite germ map, which carries the equation by construction; see the implementation notes
of `StacksFrontier/Homology/Tor/DerivedExtensionScalarsRingIso.lean`.

*What the equality still waits on.*  Not a description of
`(AlgebraicGeometry.derivedPullbackStalkIso f (i' w)).hom.app (DerivedCategory.Q.obj (i_* P))`.
Earlier notes in this file recorded that description as the obstruction, and recorded as
*unverified* a route that would avoid it by composing with its own comparison tail instead.  That
route holds.  It is
`Stacks.Cohomology.ClosedImmersionBaseChange.derivedStalkSourceIso_hom_app_Q_comp_alphaG`, in
`ClosedImmersionBaseChangeStalkSourceComparison.lean` in this directory:
composing the source chain with the comparison `alphaG` of Stacks 0661 — which is what the counit
equation `RingTheory.TorIndependence.derivedBaseChangeComparison_snd_app_comp_counit` puts there
anyway — turns the whole tail after `AlgebraicGeometry.derivedPullbackStalkIso` into the left-hand
side of the *unconditional*
`AlgebraicGeometry.derivedPullbackStalkIso_comp_comparison`.  The comparison at `i_* P` is
therefore never described, only composed with its own comparison, and no K-flat resolution of
`i_* P` is needed.  The identification of the two spellings of the stalk complex of `i_* P` that
this needs is
`Stacks.Cohomology.ClosedImmersionBaseChange.germTransport_comp_restrictFactors`, which rests on
`AlgebraicGeometry.pushStalkMap_app_eq_restrictScalarsStalkPushforwardMap`.

*Where the equality now stands.*  `DerivedStalkBaseChangeEq` is still open, but it is no longer
the frontier.  `ClosedImmersionBaseChangeStalkEquality.lean`, in this directory,
composes both of its sides with the comparison tail of Stacks 0661 and cancels it — the tail is
invertible on a K-flat complex, and every object of the derived category is `DerivedCategory.Q`
of one — so `DerivedStalkBaseChangeEq` follows from
`Stacks.Cohomology.ClosedImmersionBaseChange.DerivedStalkBaseChangeEqQ` by
`Stacks.Cohomology.ClosedImmersionBaseChange.derivedStalkBaseChangeEq_of_Q`, and Stacks 0E23 by
`Stacks.Cohomology.ClosedImmersionBaseChange.isIso_derivedBaseChangeSquare_of_Q`.  No isomorphism
of functors occurs in `DerivedStalkBaseChangeEqQ`: what is left is one equation whose only
undescribed ingredient is the derived stalk at `i' w` of the derived base change map itself.

That equation only has to be proved at a K-flat complex.
`Stacks.Cohomology.ClosedImmersionBaseChange.derivedStalkBaseChangeEqQ_of_eq` runs the tail
argument backwards — composing with the comparison tail instead of cancelling it, which needs no
hypothesis — so `Stacks.Cohomology.ClosedImmersionBaseChange.DerivedStalkBaseChangeEqQKFlat`,
the equality asked for only at the K-flat complexes, already implies
`DerivedStalkBaseChangeEqQ` at every complex, by
`Stacks.Cohomology.ClosedImmersionBaseChange.derivedStalkBaseChangeEqQ_of_kFlat`, and Stacks 0E23
by `Stacks.Cohomology.ClosedImmersionBaseChange.isIso_derivedBaseChangeSquare_of_Q_kFlat`.  At a
K-flat `P` the canonical map `AlgebraicGeometry.pullbackComparisonOnComplex g P` to the degreewise
pullback is invertible as well, by
`AlgebraicGeometry.isIso_pullbackComparisonOnComplex_of_kFlat`.
Discharging it is the counit chase —
`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_adjoint` with
`Stacks.Cohomology.ExactPushforwardAdjunction.derivedAdjunction_counit_app_eq` on one side,
bridged to the underived `Stacks.ModuleSkyscraper.extendScalars_map_pushStalkMap_comp_counit` by
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_unit_app_eq_of_isKFlat`,
`AlgebraicGeometry.map_unit_comp_restrictScalarsStalkPushforwardMap` and
`AlgebraicGeometry.derivedPullbackStalkCompIso_eq`.

*Four further ingredients that chase will want, and one route that is NOT verified.*  The
adjunction the chase has to be phrased against exists:
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction` makes any model of
total derived extension of scalars — `Lg` and `Lh` here, and the model at the germ map of `i'` —
left adjoint to derived restriction of scalars, and
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_counit_app_eq` computes
its counit at `DerivedCategory.Q` of a complex.  The derived counit of `Li'^* ⊣ Ri'_*` is
available at `DerivedCategory.Q` of a complex and not only at `DerivedCategory.Qh` of one, by
`derivedCounit_pushforwardComparisonQ` in
`Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces`, and translating between the two
spellings of the comparison `i'_* ⟶ Ri'_*` is
`Stacks.ClosedImmersion.derivedPushforwardUnit_app_comp_derivedPushforwardIsoMapDerivedCategory`
together with `CategoryTheory.Functor.mapHomologicalComplexUpToQuasiIsoFactorsh_hom_app`, which
is the only statement in the library relating `Functor.mapDerivedCategoryFactors` to
`Functor.mapDerivedCategoryFactorsh`.

The shape of the chase is to transpose across the adjunction at the germ map of `i'` — both
sides are morphisms into derived restriction of scalars — so that the unit of
`Li'^* ⊣ Ri'_*`, which `derivedBaseChangeMap_eq` puts in front of everything and which the
library describes only on a K-flat complex, disappears against the unit square.  What that
reading needs in its place is the counit half of a mate correspondence for
`AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing`: that derived extension
of scalars of its component, followed by the counit of
`derivedExtensionScalarsAdjunction`, is `AlgebraicGeometry.derivedPullbackStalkIso` for `i'` at
`w` read backwards at `Ri'_*` of the object, followed by the derived stalk of the counit of
`Li'^* ⊣ Ri'_*`.  That statement is the derived form of
`Stacks.ModuleSkyscraper.extendScalars_map_pushStalkMap_comp_counit`.

*That counit statement is now stated and reduced*, in
`StacksFrontier/AlgebraicGeometry/BaseChange/TorIndependence/DerivedStalkPushforwardMate.lean`.  It
is `AlgebraicGeometry.extendScalars_map_derivedStalkPushforward_comp_counit`, and it holds at
every object of `D(𝒪_{Z'})` as soon as the *unit* square
`AlgebraicGeometry.DerivedStalkPushforwardUnitSquareAt` of the same two comparisons does — the
mate identification being `AlgebraicGeometry.derivedStalkDerivedPushforwardIso_eq_mateEquiv`,
and the passage from the unit square to the counit square being
`CategoryTheory.map_counit_comp_of_unit`.  The unit square in turn has only to be checked at
`DerivedCategory.Q` of a K-flat complex, by
`AlgebraicGeometry.derivedStalkPushforwardUnitSquare_of_kFlat`.

*That unit square is now proved*, in
`StacksFrontier/AlgebraicGeometry/BaseChange/TorIndependence/DerivedStalkPushforwardUnitSquare.lean`:
`AlgebraicGeometry.derivedStalkPushforwardUnitSquareAt_all` holds at every object of `D(𝒪_X)`,
so the counit half
`AlgebraicGeometry.extendScalars_map_derivedStalkPushforward_comp_counit_of_schemes` and the mate
identification `AlgebraicGeometry.derivedStalkDerivedPushforwardIso_eq_mate` are unconditional.
The route was to transpose the square (`derivedStalkPushforwardUnitSquareAt_iff`), restrict to a
K-flat complex, and then compose with the right-hand side of
`AlgebraicGeometry.derivedPullbackStalkIso_comp_comparison` — invertible exactly because the
complex is K-flat — which removes the `Classical.choose` from `derivedPullbackStalkIso.inv`;
four transports then carry what remains to the degreewise
`AlgebraicGeometry.map_unit_comp_restrictScalarsStalkPushforwardMap`.  The `Q`/`Qh` bridge for
the unit of `Li'^* ⊣ Ri'_*` cost no new unfolding of `liftingLocalizedFunctor`:
`Stacks.DerivedFunctor.mapDerivedCategoryFactorsh_hom_app_comp_quotientCompQhIso` already
related the two factorizations.

*The first rungs of the counit chase are now proved*, in
`ClosedImmersionBaseChangeCounitChase.lean` in this directory.
These are machine-checked:

* `AlgebraicGeometry.derivedStalk_transpose_comp_derivedStalkPushforward` **removes the unit of
  `Li'^* ⊣ Ri'_*`.**  The derived stalk at `i' w` of a transpose `M ⟶ Ri'_* Y₀`, followed by the
  derived stalk of `Ri'_*` of a morphism `Y₀ ⟶ Y` and by
  `derivedStalkDerivedPushforwardIsoOfSchemesLocalRing` for `i'` at `w`, is the unit of
  `AlgebraicGeometry.derivedStalkGermAdjunction` followed by derived restriction of scalars of
  `AlgebraicGeometry.derivedPullbackStalkIso` for `i'` read backwards and the derived stalk at
  `w` of the adjoint.  Fed `derivedBaseChangeMap_eq` as the transpose and
  `AlgebraicGeometry.pullbackComparisonOnComplex g P` as the morphism, this is the left-hand
  side of `DerivedStalkBaseChangeEqQAt` with its one undescribed ingredient gone.
* `AlgebraicGeometry.derivedPullbackStalkIso_inv_comp_derivedStalk_compIso` and
  `AlgebraicGeometry.derivedStalk_compIso_inv_comp_derivedPullbackStalkIso` **dispose of the two
  Tag 0D5S isomorphisms** that the adjoint of the base change map carries: they are
  `derivedPullbackStalkCompIso_hom_eq` solved for the two shapes in which those isomorphisms
  occur there.
* `AlgebraicGeometry.derivedPullbackStalkIso_inv_comp_eqToHom_comp` **disposes of the transport**
  between the two readings `Lf^* ⋙ Li'^*` and `Li^* ⋙ Lg^*` of the derived pullback along the
  diagonal, which is what `derivedPullbackCompIsoLeft` contributes.

*What remains, and is the whole of what Stacks 0E23 waits on.*  On paper — this part is **not**
machine-checked — the three rungs above together with
`AlgebraicGeometry.extendScalars_map_derivedStalkPushforward_comp_counit_of_schemes` for `i` at
`g w` (which disposes of the counit of `Li^* ⊣ Ri_*`) and
`AlgebraicGeometry.derivedPullbackStalkIso_comp_comparison` for `g` at `w` and for `f` at
`i' w` bring both sides of `DerivedStalkBaseChangeEqQAt` to a common leading factor
`(derivedPullbackStalkIso f (i' w)).hom.app (Ri_* (DerivedCategory.Q.obj P))`.  What is left
after that factor is a **degreewise, ring-level** identity: it mentions no geometry beyond
`derivedStalkDerivedPushforwardIsoOfSchemesLocalRing` for `i` at `g w`, which
`derivedStalkDerivedPushforwardIsoOfSchemesLocalRing_hom_app_Q` computes below
`DerivedCategory.Q`, and otherwise only the unit and counit of
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction` at the two germ maps,
`AlgebraicGeometry.derivedStalkExtensionCompIso`, the comparisons `alphaG` and `alphaH`, the
factorizations of restriction of scalars,
`StacksDraft.DerivedRingIso.extendScalarsRestrictIso`, and the *underived* comparison
`(derivedBaseChangeComparison …).1` of Stacks 065Z.

That last ingredient was the obstruction.  Its only equation is
`RingTheory.TorIndependence.derivedBaseChangeComparison_fst_app_tmul`, which says it carries
`r' ⊗ m` to `i r' ⊗ m`, so the residual identity has to be checked on pure tensors.  In words
it is: *the unit of extension of scalars along `𝒪_{X',i'w}` applied to
`𝒪_{X',i'w} ⊗_{𝒪_{X,i(gw)}} M`, followed by the merge of the two extensions of scalars and by
extension along `g^♯_w` of the counit at `M`, is the comparison of Stacks 065Z* — the underived
mate identity for the ring square.

*That identity is now proved*, at the ring level, in
`StacksFrontier/Homology/Tor/BaseChangeIndependence/ComparisonEquations.lean`:
`RingTheory.TorIndependence.derivedBaseChangeComparison_fst_app_eq_unit_comp_counit` states it
with the merge as a hypothesis — all that is used of the merge is that it carries
`1 ⊗ (1 ⊗ m)` to `1 ⊗ (1 ⊗ m)`, which is as much as a consumer coming from geometry can be asked
to present, since the four local rings sit in four universes as the comparison is stated and
`ModuleCat.extendScalarsComp` needs them in one — and, in the same namespace,
`derivedBaseChangeComparison_fst_app_eq_unit_comp_counit_extendScalarsComp`
discharges that hypothesis for the canonical merge where the rings do share a universe, which is
the case the local rings of a cartesian square of schemes present.

What Stacks 0E23 still waits on is therefore no longer a missing statement but two transfers:
the ring-level identity read degreewise at each `K.X n` of the stalk complex, and the assembly
above — the part marked *not* machine-checked — carried out in Lean.

## References

* [Stacks Project, Tag 00AE](https://stacks.math.columbia.edu/tag/00AE)
* [Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 0E23](https://stacks.math.columbia.edu/tag/0E23)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open CochainComplex.DerivedExtensionScalars
open RingTheory.TorIndependence
open StacksDraft.DerivedRingIso

noncomputable section

namespace Stacks.Cohomology.ClosedImmersionBaseChange

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### The comparison of the stalks at two equal points is invertible -/

section Congr

variable {Y : Scheme.{u}}

/-- **The germ comparison at two equal points, composed with the one for the symmetric equation,
is the identity.**  Stated for a free equation of points, since it is proved by substituting one
point for the other. -/
theorem stalkCongr_symm_hom_hom_apply {a b : Y} (h : a = b)
    (x : ToType (Y.presheaf.stalk a)) :
    (Y.presheaf.stalkCongr (Inseparable.of_eq h.symm)).hom.hom
        ((Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom x) = x := by
  subst h
  simp [TopCat.Presheaf.stalkCongr]

/-- `stalkCongr_symm_hom_hom_apply` in the other order. -/
theorem stalkCongr_hom_symm_hom_apply {a b : Y} (h : a = b)
    (y : ToType (Y.presheaf.stalk b)) :
    (Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom
        ((Y.presheaf.stalkCongr (Inseparable.of_eq h.symm)).hom.hom y) = y :=
  stalkCongr_symm_hom_hom_apply h.symm y

/-- **The transport of the stalk functor at a self-equality of points is the collapse of
restriction of scalars.**  At an equality of a point with itself,
`Stacks.Cohomology.ClosedImmersionBaseChange.modulesStalkFunctorCongr` is
`ModuleCat.restrictScalarsId'` at the germ comparison, which `stalkCongr_self_hom_hom` identifies
with the identity homomorphism.

`modulesStalkFunctorCongr_unfold` exhibits the definition and `restrictScalarsId'_eqToIso`
absorbs the transport between the two spellings of that homomorphism. -/
theorem modulesStalkFunctorCongr_hom_app_self {a : Y} (h : a = a) (M : Y.Modules) :
    (modulesStalkFunctorCongr h).hom.app M =
      (ModuleCat.restrictScalarsId'.{u, u}
          (Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom
          (stalkCongr_self_hom_hom h)).hom.app
        ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y a).obj M) := by
  rw [modulesStalkFunctorCongr_unfold h]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
  exact restrictScalarsId'_eqToIso _ _ (stalkCongr_self_hom_hom h) rfl _ _

/-- `modulesStalkFunctorCongr_hom_app_self` on cochain complexes: the degreewise transport of the
stalk functor at a self-equality is the degreewise collapse
`StacksDraft.DerivedRingIso.restrictScalarsIdComplexApp` of restriction of scalars. -/
theorem mapHomologicalComplex_modulesStalkFunctorCongr_hom_app_self {a : Y} (h : a = a)
    (P : CochainComplex Y.Modules ℤ) :
    (NatIso.mapHomologicalComplex (modulesStalkFunctorCongr h)
        (ComplexShape.up ℤ)).hom.app P =
      StacksDraft.DerivedRingIso.restrictScalarsIdComplexApp.{u}
          (Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom
          (stalkCongr_self_hom_hom h)
        (((Stacks.ModuleSkyscraper.modulesStalkFunctor Y a).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) := by
  ext i
  simp [StacksDraft.DerivedRingIso.restrictScalarsIdComplexApp,
    StacksDraft.DerivedRingIso.restrictScalarsIdComplexIso,
    modulesStalkFunctorCongr_hom_app_self]

end Congr

section Square

variable {Z' X' Z X : Scheme.{u}} {i' : Z' ⟶ X'} {g : Z' ⟶ Z} {f : X' ⟶ X} {i : Z ⟶ X}

/-- **The two presentations of the image point agree.**  In a cartesian square the point `i (g w)`
of `X` and the point `f (i' w)` are the same point, by commutativity of the square. -/
theorem ptEq (sq : IsPullback i' g f i) (w : Z') : i (g w) = f (i' w) :=
  congrArg (fun h : Z' ⟶ X => h.base w) sq.w.symm

/-! ### The models of derived extension of scalars that the geometry presents -/

/-- The canonical model of derived extension of scalars along the germ map
`𝒪_{X, i (g w)} ⟶ 𝒪_{X', i' w}`, the two presentations of the image point being compared by
`TopCat.Presheaf.stalkCongr`.  This is the functor Stacks 0661 is instantiated at on the source
side. -/
abbrev Lg (w : Z') (hpt : i (g w) = f (i' w)) :=
  (totalDerivedExtensionScalars.{u, u, u}
    ((X.presheaf.stalkCongr (Inseparable.of_eq hpt)).hom ≫ f.stalkMap (i' w)).hom).functor

/-- The canonical model of derived extension of scalars along the germ map
`𝒪_{Z, g w} ⟶ 𝒪_{Z', w}`.  This is the functor Stacks 0661 is instantiated at on the target
side, and the one `AlgebraicGeometry.derivedPullbackStalkIso` for `g` produces. -/
abbrev Lh (w : Z') := (totalDerivedExtensionScalars.{u, u, u} (g.stalkMap w).hom).functor

/-- The germ map `𝒪_{X, i (g w)} ⟶ 𝒪_{X', i' w}`, through the comparison of the two presentations
of the image point, as a homomorphism of rings. -/
abbrev ringRR' (w : Z') (hpt : i (g w) = f (i' w)) :=
  ((X.presheaf.stalkCongr (Inseparable.of_eq hpt)).hom ≫ f.stalkMap (i' w)).hom

/-- **The source chain's last step.**  Derived extension of scalars along the germ map of `f`,
precomposed with derived restriction of scalars along the comparison of the two presentations of
the image point, is derived extension of scalars along the composite — which is the functor
Stacks 0661 is stated at.

This is `StacksDraft.DerivedRingIso.derivedExtensionScalarsRestrictIso` at the germ comparison,
whose invertibility is `stalkCongr_symm_hom_hom_apply` and `stalkCongr_hom_symm_hom_apply`. -/
def derivedExtensionStalkIso (w : Z') (hpt : i (g w) = f (i' w)) :
    (ModuleCat.restrictScalars.{u, u, u}
          (X.presheaf.stalkCongr (Inseparable.of_eq hpt.symm)).hom.hom).mapDerivedCategory ⋙
        (totalDerivedExtensionScalars.{u, u, u} (f.stalkMap (i' w)).hom).functor ≅
      Lg w hpt :=
  derivedExtensionScalarsRestrictIso
    (X.presheaf.stalkCongr (Inseparable.of_eq hpt)).hom.hom
    (X.presheaf.stalkCongr (Inseparable.of_eq hpt.symm)).hom.hom
    (stalkCongr_symm_hom_hom_apply hpt) (stalkCongr_hom_symm_hom_apply hpt)
    (f.stalkMap (i' w)).hom

open StacksDraft.DerivedExtensionScalarsComp in
/-- **The source chain's last step, merged with the germ map of `i'`.**  Extending scalars along
the germ map of `i'` of `derivedExtensionStalkIso`, followed by the merge of `ringRR'` with that
germ map, is the merge of the germ map of `f` with it followed by the absorption of the germ
comparison into the composite.

This is `StacksDraft.DerivedRingIso.derivedExtensionScalarsRestrictIso_comp_compIso` at the germ
comparison of the two presentations of the image point and the two germ maps.  It carries no
transport: composition of ring homomorphisms is associative definitionally.

Stated here, in the module that owns `derivedExtensionStalkIso`, so that no consumer has to
convert between that name and the isomorphism of derived extension of scalars it is. -/
theorem derivedExtensionStalkIso_hom_app_comp_compIso (w : Z') (hpt : i (g w) = f (i' w))
    (X₀ : DerivedCategory (ModuleCat.{u} (ToType (X.presheaf.stalk (i (g w)))))) :
    (totalDerivedExtensionScalars.{u, u, u} (i'.stalkMap w).hom).functor.map
          ((derivedExtensionStalkIso w hpt).hom.app X₀) ≫
        (derivedExtensionScalarsCompIso (ringRR' w hpt) (i'.stalkMap w).hom).hom.app X₀ =
      (derivedExtensionScalarsCompIso (f.stalkMap (i' w)).hom (i'.stalkMap w).hom).hom.app
          ((ModuleCat.restrictScalars.{u, u, u}
              (X.presheaf.stalkCongr
                (Inseparable.of_eq hpt.symm)).hom.hom).mapDerivedCategory.obj X₀) ≫
        (derivedExtensionScalarsRestrictIso
            (X.presheaf.stalkCongr (Inseparable.of_eq hpt)).hom.hom
            (X.presheaf.stalkCongr (Inseparable.of_eq hpt.symm)).hom.hom
            (stalkCongr_symm_hom_hom_apply hpt) (stalkCongr_hom_symm_hom_apply hpt)
            ((i'.stalkMap w).hom.comp (f.stalkMap (i' w)).hom)).hom.app X₀ :=
  derivedExtensionScalarsRestrictIso_comp_compIso _ _ _ _ _ _ X₀

/-! ### The two chains of comparisons -/

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces in
/-- **The source chain.**  The derived stalk at `i' w` of `Lf^*(Ri_* -)` is
`𝒪_{X', i' w} ⊗ᴸ_{𝒪_{X, i (g w)}} (-)_{g w}`, as an isomorphism of functors on
`D(𝒪_Z)`, with the tensor factor written as the canonical model `Lg` of derived extension of
scalars.

The three steps are `AlgebraicGeometry.derivedPullbackStalkIso` for `f` at `i' w`, which computes
the stalk of the derived pullback over `𝒪_{X, f (i' w)}`; the derived stalk of `Ri_*` on the image
(`AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing` for `i` at `g w`),
transported from `𝒪_{X, i (g w)}` to `𝒪_{X, f (i' w)}` by `derivedStalkFunctorCongr`; and
`derivedExtensionStalkIso`, which absorbs that transport into the extension of scalars. -/
def derivedStalkSourceIso [AlgebraicGeometry.IsClosedImmersion i] (w : Z')
    (hpt : i (g w) = f (i' w)) :
    derivedPushforward i.toLRSHom.toShHom ⋙ derivedPullback f.toLRSHom.toShHom ⋙
        AlgebraicGeometry.derivedStalkFunctor (i' w) ≅
      AlgebraicGeometry.derivedStalkFunctor (g w) ⋙
        (ModuleCat.restrictScalars.{u, u, u} (i.stalkMap (g w)).hom).mapDerivedCategory ⋙
          Lg w hpt :=
  Functor.isoWhiskerLeft _ (AlgebraicGeometry.derivedPullbackStalkIso f (i' w)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft _ (derivedStalkFunctorCongr hpt.symm).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing i (g w)) _) _ ≪≫
    Functor.isoWhiskerRight (Functor.associator _ _ _) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ (derivedExtensionStalkIso w hpt))

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces in
/-- **The target chain.**  The derived stalk at `i' w` of `Ri'_*(Lg^* -)` is
`(-)_{g w} ⊗ᴸ_{𝒪_{Z, g w}} 𝒪_{Z', w}` with scalars restricted along the germ map of `i'`, as an
isomorphism of functors on `D(𝒪_Z)`.

The two steps are the derived stalk of `Ri'_*` on the image
(`AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing` for `i'` at `w`) and
`AlgebraicGeometry.derivedPullbackStalkIso` for `g` at `w`.  No transport of the point is needed
here: both are stated at `w` and at `g w`. -/
def derivedStalkTargetIso [AlgebraicGeometry.IsClosedImmersion i'] (w : Z') :
    derivedPullback g.toLRSHom.toShHom ⋙ derivedPushforward i'.toLRSHom.toShHom ⋙
        AlgebraicGeometry.derivedStalkFunctor (i' w) ≅
      AlgebraicGeometry.derivedStalkFunctor (g w) ⋙ Lh w ⋙
        (ModuleCat.restrictScalars.{u, u, u} (i'.stalkMap w).hom).mapDerivedCategory :=
  Functor.isoWhiskerLeft _
      (AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing i' w) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (AlgebraicGeometry.derivedPullbackStalkIso g w) _ ≪≫
    Functor.associator _ _ _

/-! ### The comparison of Stacks 0661 at the chosen models -/

/-- The comparison of `Lg` with termwise extension of scalars, at the spelling Stacks 0661 asks
for; see the implementation notes on the two spellings of the underived functor. -/
abbrev alphaG (w : Z') (hpt : i (g w) = f (i' w)) :
    DerivedCategory.Q ⋙ Lg w hpt ⟶
      (ModuleCat.extendScalars.{u, u, u} (ringRR' w hpt)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  (totalDerivedExtensionScalars.{u, u, u} (ringRR' w hpt)).comparison

/-- The comparison of `Lh` with termwise extension of scalars, at the spelling Stacks 0661 asks
for. -/
abbrev alphaH (w : Z') :
    DerivedCategory.Q ⋙ Lh w ⟶
      (ModuleCat.extendScalars.{u, u, u} (g.stalkMap w).hom).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  (totalDerivedExtensionScalars.{u, u, u} (g.stalkMap w).hom).comparison

/-- **The compatibility of `derivedExtensionStalkIso` with `alphaG`.**  At a cochain complex `M`
of `𝒪_{X, i (g w)}`-modules, the last step of the source chain, composed with the comparison of
Stacks 0661's source functor `Lg` with termwise extension of scalars, is the comparison for the
germ map of `f` at the termwise restriction of `M`, followed by the underived identification
`StacksDraft.DerivedRingIso.extendScalarsRestrictIso` of the two presentations of termwise
extension of scalars along the composite.

This is `StacksDraft.DerivedRingIso.derivedExtensionScalarsRestrictIso_hom_app_Q_comp_comparison`
at the germ comparison.  It is one of the two inputs the open equality `DerivedStalkBaseChangeEq`
below needs: `derivedExtensionStalkIso` is the last factor of
`derivedStalkSourceIso_hom_app_Q`, and `alphaG` is what the counit compatibility
`RingTheory.TorIndependence.derivedBaseChangeComparison_snd_app_comp_counit` of Stacks 0661
produces on the source side. -/
theorem derivedExtensionStalkIso_hom_app_Q_comp_alphaG (w : Z') (hpt : i (g w) = f (i' w))
    (M : CochainComplex (ModuleCat.{u} (ToType (X.presheaf.stalk (i (g w))))) ℤ) :
    (derivedExtensionStalkIso w hpt).hom.app (DerivedCategory.Q.obj M) ≫
        (alphaG w hpt).app M =
      (totalDerivedExtensionScalars.{u, u, u} (f.stalkMap (i' w)).hom).functor.map
          ((ModuleCat.restrictScalars.{u, u, u}
            (X.presheaf.stalkCongr
              (Inseparable.of_eq hpt.symm)).hom.hom).mapDerivedCategoryFactors.hom.app M) ≫
        (totalDerivedExtensionScalars.{u, u, u} (f.stalkMap (i' w)).hom).comparison.app
            (((ModuleCat.restrictScalars.{u, u, u}
              (X.presheaf.stalkCongr
                (Inseparable.of_eq hpt.symm)).hom.hom).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj M) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (StacksDraft.DerivedRingIso.extendScalarsRestrictIso
              (X.presheaf.stalkCongr (Inseparable.of_eq hpt)).hom.hom
              (X.presheaf.stalkCongr (Inseparable.of_eq hpt.symm)).hom.hom
              (stalkCongr_symm_hom_hom_apply hpt) (stalkCongr_hom_symm_hom_apply hpt)
              (f.stalkMap (i' w)).hom).hom (ComplexShape.up ℤ)).app M) :=
  StacksDraft.DerivedRingIso.derivedExtensionScalarsRestrictIso_hom_app_Q_comp_comparison
    (X.presheaf.stalkCongr (Inseparable.of_eq hpt)).hom.hom
    (X.presheaf.stalkCongr (Inseparable.of_eq hpt.symm)).hom.hom
    (stalkCongr_symm_hom_hom_apply hpt) (stalkCongr_hom_symm_hom_apply hpt)
    (f.stalkMap (i' w)).hom M

/-- The left-derived universal property of `Lg`, re-seated at the spelling of `alphaG`. -/
instance isLeftDerived_alphaG (w : Z') (hpt : i (g w) = f (i' w)) :
    (Lg w hpt).IsLeftDerivedFunctor (alphaG w hpt)
      (HomologicalComplex.quasiIso
        (ModuleCat.{u} (ToType (X.presheaf.stalk (i (g w))))) (ComplexShape.up ℤ)) :=
  (totalDerivedExtensionScalars.{u, u, u} (ringRR' w hpt)).isLeftDerived

/-- The left-derived universal property of `Lh`, re-seated at the spelling of `alphaH`. -/
instance isLeftDerived_alphaH (w : Z') :
    (Lh w).IsLeftDerivedFunctor (alphaH w)
      (HomologicalComplex.quasiIso
        (ModuleCat.{u} (ToType (Z.presheaf.stalk (g w)))) (ComplexShape.up ℤ)) :=
  (totalDerivedExtensionScalars.{u, u, u} (g.stalkMap w).hom).isLeftDerived

/-- **The comparison of Stacks 0661 at the four local rings of the square**, at the canonical
models `Lg` and `Lh` of the two total derived extension-of-scalars functors — that is, at the
models the geometric chains produce. -/
def stalkComparison (sq : IsPullback i' g f i) (w : Z') (hpt : i (g w) = f (i' w)) :
    (ModuleCat.restrictScalars.{u, u, u} (i.stalkMap (g w)).hom).mapDerivedCategory ⋙
        Lg w hpt ⟶
      Lh w ⋙ (ModuleCat.restrictScalars.{u, u, u} (i'.stalkMap w).hom).mapDerivedCategory :=
  (derivedBaseChangeComparison.{u, u, u, u, u} (i.stalkMap (g w)).hom (ringRR' w hpt)
    (g.stalkMap w).hom (i'.stalkMap w).hom (stalkMap_ringHom_square sq w hpt)
    (Lg w hpt) (Lh w) (alphaG w hpt) (alphaH w)).2.1

/-- **The comparison of Stacks 0661 is invertible at the canonical models.**  This is
`isIso_derivedBaseChangeComparison_stalk` instantiated at `Lg`, `Lh`, `alphaG` and `alphaH`, which
is what the two `local instance`s above make possible. -/
theorem isIso_stalkComparison (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (htor : AlgebraicGeometry.TorIndependent i f)
    (w : Z') (hpt : i (g w) = f (i' w)) : IsIso (stalkComparison sq w hpt) :=
  isIso_derivedBaseChangeComparison_stalk sq htor w hpt (Lg w hpt) (Lh w)
    (alphaG w hpt) (alphaH w)

/-- A closed immersion stays one after base change, so the right-hand edge `i'` of the square is a
closed immersion as soon as `i` is. -/
theorem isClosedImmersion_of_isPullback (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] : AlgebraicGeometry.IsClosedImmersion i' :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback sq.flip inferInstance

/-! ### Stacks 0E23, reduced to one equality -/

open Stacks.Cohomology.DerivedBaseChange in
/-- **The one remaining equality.**  For every point `w` of `Z'` and every complex `K`, the derived
stalk at `i' w` of the derived base change map of Stacks 08HY, read through `derivedStalkSourceIso`
on the source and `derivedStalkTargetIso` on the target, is the comparison of Stacks 0661 at the
derived stalk of `K` at `g w`.

Neither side is asserted to be invertible: this says only that two canonical morphisms agree.  The
invertibility of the right-hand side is `isIso_stalkComparison`, and that is what makes the
equality sufficient for Stacks 0E23. -/
abbrev DerivedStalkBaseChangeEq (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] : Prop :=
  letI := isClosedImmersion_of_isPullback sq
  ∀ (w : Z') (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))),
    (derivedStalkSourceIso w (ptEq sq w)).inv.app K ≫
        (AlgebraicGeometry.derivedStalkFunctor (i' w)).map
          (derivedBaseChangeMap g.toLRSHom.toShHom i'.toLRSHom.toShHom i.toLRSHom.toShHom
            f.toLRSHom.toShHom (comp_toShHom_of_isPullback sq) K) ≫
        (derivedStalkTargetIso w).hom.app K =
      (stalkComparison sq w (ptEq sq w)).app
        ((AlgebraicGeometry.derivedStalkFunctor (g w)).obj K)

open Stacks.Cohomology.DerivedBaseChange in
/-- **The derived stalk of the base change map is invertible on the image, from the equality.**
The two chains are isomorphisms of functors and the comparison of Stacks 0661 is invertible, so
the equality transfers that invertibility to the derived stalk of the base change map. -/
theorem isIso_derivedStalk_derivedBaseChangeMap_of_eq (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (htor : AlgebraicGeometry.TorIndependent i f)
    (heq : DerivedStalkBaseChangeEq sq) (w : Z')
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))) :
    IsIso ((AlgebraicGeometry.derivedStalkFunctor (i' w)).map
      (derivedBaseChangeMap g.toLRSHom.toShHom i'.toLRSHom.toShHom i.toLRSHom.toShHom
        f.toLRSHom.toShHom (comp_toShHom_of_isPullback sq) K)) := by
  let _ := isClosedImmersion_of_isPullback sq
  have : IsIso (stalkComparison sq w (ptEq sq w)) :=
    isIso_stalkComparison sq htor w (ptEq sq w)
  rw [← isIso_comp_right_iff _ ((derivedStalkTargetIso w).hom.app K),
    ← isIso_comp_left_iff ((derivedStalkSourceIso w (ptEq sq w)).inv.app K), heq w K]
  infer_instance

open Stacks.Cohomology.DerivedBaseChange in
/-- **Stacks 0E23 at the level of functors, from the equality.**  The canonical morphism of
functors `Ri_* ⋙ Lf^* ⟶ Lg^* ⋙ Ri'_*` of Stacks 08HY is an isomorphism, for a cartesian square
with `i` a closed immersion and `Z`, `X'` Tor independent over `X`, as soon as
`DerivedStalkBaseChangeEq` holds.

This is `isIso_derivedBaseChangeSquare_of_onImage` with its on-image clause discharged by
`isIso_derivedStalk_derivedBaseChangeMap_of_eq`.  The equality enters as
a hypothesis. -/
theorem isIso_derivedBaseChangeSquare_of_eq (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (htor : AlgebraicGeometry.TorIndependent i f)
    (heq : DerivedStalkBaseChangeEq sq) :
    IsIso (derivedBaseChangeSquare g.toLRSHom.toShHom i'.toLRSHom.toShHom i.toLRSHom.toShHom
      f.toLRSHom.toShHom (comp_toShHom_of_isPullback sq)) :=
  isIso_derivedBaseChangeSquare_of_onImage sq fun w K =>
    isIso_derivedStalk_derivedBaseChangeMap_of_eq sq htor heq w K

/-- **Stacks 0E23 as an isomorphism of functors, from the equality.**  `Ri'_* ∘ Lg^*` and
`Lf^* ∘ Ri_*` are isomorphic as functors `D(𝒪_Z) ⟶ D(𝒪_{X'})`, by the canonical morphism of
Stacks 08HY, for a cartesian square with `i` a closed immersion and `Z`, `X'` Tor independent over
`X`, as soon as `DerivedStalkBaseChangeEq` holds.  The equality is an argument here, and this
carries no tag; Stacks 0E23 is `derivedBaseChangeSquareIso`. -/
def derivedBaseChangeSquareIsoOfEq (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (htor : AlgebraicGeometry.TorIndependent i f)
    (heq : DerivedStalkBaseChangeEq sq) :
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward i.toLRSHom.toShHom ⋙
        Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          f.toLRSHom.toShHom ≅
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g.toLRSHom.toShHom ⋙
        Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
          i'.toLRSHom.toShHom :=
  derivedBaseChangeSquareIsoOfOnImage sq fun w K =>
    isIso_derivedStalk_derivedBaseChangeMap_of_eq sq htor heq w K

end Square

end Stacks.Cohomology.ClosedImmersionBaseChange

end

end
