module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.MorphismFromStructureMap.RecoveryAndThickeningHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.MorphismFromStructureMap.DerivationModification

/-!
# Morphisms of thickenings determined by a map of structure sheaves

Let `B` be a big fppf site, `S` a scheme contained in it, `T` an algebraic space over `S`, and
let `G ⊂ X'` and `H ⊂ Y'` be thickenings of algebraic spaces over `T`, with inclusions
`i_X : X ⟶ X'` and `i_Y : Y ⟶ Y'`.  Let `f : X ⟶ Y` be a morphism.  A map of `𝒪_T`-algebras
`α : f^{-1}𝒪_{Y'} ⟶ 𝒪_{X'}` whose square with `f^♯`, `i_X^♯` and `i_Y^♯` commutes is the same
thing as a morphism of small étale ringed topoi
`Φ = (f_{spaces,étale}, α) : (Sh(X'_étale), 𝒪_{X'}) ⟶ (Sh(Y'_étale), 𝒪_{Y'})`, and the
assertion of [Stacks Project, Tag 05ZN] is that such a `Φ` comes from a unique morphism of
thickenings `(f, f')` over `T`.

The *existence* of `f'` is produced by [Stacks Project, Tag 04KL] over a base, the full
faithfulness of `X ↦ (Sh(X_étale), 𝒪_X)` on morphisms compatible with the two structure
morphisms to the base; that assertion is
`AlgebraicGeometry.Space.IsRecoveredFromSmallEtale`, and it holds for an arbitrary base scheme
(`AlgebraicGeometry.Space.isRecoveredFromSmallEtale_holds`, proved inline in the 05ZN theorem
here): the one thing the proof of Tag 04KL needs of the base, that the chart morphisms of the
morphism of topoi lie over it, follows from the 2-compatibility by
`AlgebraicGeometry.Space.isChartOverBase_of_twoCompatible`.  (An earlier
route, `AlgebraicGeometry.Space.isRecoveredFromSmallEtale_of_mono_toSpecΓ`, needed the canonical
morphism `S ⟶ Spec Γ(S, ⊤)` of the base scheme to be a monomorphism.)  The rest is proved for an
arbitrary base as well:

* that `Φ` is a morphism of *locally* ringed topoi, which is what makes Tag 04KL applicable at
  all and which the source deduces from the local nilpotency of the two kernels
  (`AlgebraicGeometry.Space.isLocallyRinged_of_thickeningSquare`);
* that the pair `(f, f')` is **unique**, that the `f'` so obtained *is* a morphism of
  thickenings, and that it is a morphism over `T`.  All three come from the *faithfulness* half
  of Tag 04KL over a base, which is **not** carried: it is
  `AlgebraicGeometry.Space.eq_of_inducesCommonSmallEtaleRingedToposHom` below, and that is proved
  outright from [Stacks Project, Tag 04M6],
  `AlgebraicGeometry.Space.eq_of_smallEtaleRingedToposHom_twoIso` — two morphisms of algebraic
  spaces over `S` whose morphisms of small étale ringed topoi are 2-isomorphic are equal.  The
  two equations use in addition that the morphism of small étale ringed topoi of a composite is
  the composite ([Stacks Project, Tag 04KJ],
  `AlgebraicGeometry.Space.smallEtaleRingedToposHom_isLocallyRinged` for the locality).

Locality of `Φ` is `AlgebraicGeometry.Space.isLocallyRinged_of_thickeningSquare`, and it needs
no nilpotency: the source's use of the local nilpotency of `ker i_X^♯` is precisely the
assertion that the units square of `i_X` is cartesian, which Tag 04KJ already gives for every
morphism of algebraic spaces.  What is left is a cancellation — the units square of `Φ ∘ i_X` is
the paste of the units square of `i_X` with the image under `i_X^{-1}` of that of `Φ`, so the
latter is cartesian, and it descends to `Φ` because `i_X^{-1}` is an equivalence
(`AlgebraicGeometry.Space.isEquivalence_inverseImage_inclusion_of_isThickening`, the
sheaf-of-sets half of [Stacks Project, Tag 05ZM]).

[Stacks Project, Tag 04D0] is one application of this to `α = (a')^♯ + D`, where
`D = d_{Y/T} ∘ θ` is the `𝒪_T`-derivation attached by Equation (0619) to an `𝒪_X`-linear map
`θ : a^*Ω_{Y/T} ⟶ 𝒞_{X/X'}`.  That sum *can* now be formed on the site of `X'`, by
`AlgebraicGeometry.Space.conormalAmbientSourceDerivationActionHom` of
`ConormalAmbientSquareZeroValues.lean`, and it is locally ringed there by
`AlgebraicGeometry.Space.isLocallyRinged_of_conormalAmbientSourceDerivationActionHom`.  The datum
`AlgebraicGeometry.Space.DerivationModification` can therefore now be *built*, by
`AlgebraicGeometry.Space.derivationModificationOfFamily`, from the assignment `θ ↦ D` of
Equation (0619) on the site of `X'` and three clauses that remain unproved; see the
implementation notes below for exactly what is and is not discharged.  The structure-sheaf half
of [Stacks Project, Tag 05ZM] is also available directly at the small étale sites, as
`AlgebraicGeometry.Space.isIso_ringUnit_of_isThickening` and its companion at commutative rings
`AlgebraicGeometry.Space.isIso_commRingUnit_of_isThickening`.

**`DerivationModification` is no longer the reason anything here is an argument.**  The datum
`α = (a')^♯ + D` is now *constructed* from `θ`, in
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/DerivationModificationMorphism.lean`:
`AlgebraicGeometry.Space.derivationModificationHomOfMap`, whose value on a section is
`(a')^♯(x) + D(x)` for `D` the `𝒪_T`-derivation attached to `θ` by Equation (0619)
(`AlgebraicGeometry.Space.thickeningRingSheafDerivation`).  All three of the properties that
Tag 05ZN consumes are proved there outright:
`derivationModificationHomOfMap_isLocallyRinged`,
`nonempty_smallEtaleTwoIso_derivationModificationHomOfMap_comp` (the source's square
`i_X^♯ ∘ α = a^♯ ∘ i_Y^♯`) and
`nonempty_smallEtaleTwoIso_derivationModificationHomOfMap_base` (that `α` is a map of
`𝒪_T`-algebras).  So the statements of this section are kept only because they are stated for an
abstract datum; the carriers of [Stacks Project, Tag 04D0] are
`AlgebraicGeometry.Space.eq_of_derivationModificationHomOfMap_induces` and
`AlgebraicGeometry.Space.existsUnique_hom_of_derivationModificationHomOfMap`, and both assume
nothing.

What `AlgebraicGeometry.Space.DerivationModification` still has that the construction does not is
its `injective` field — that distinct `θ` modify the structure map to *non-2-isomorphic*
morphisms.  Two morphisms inducing `α(θ₁)` and `α(θ₂)` produce a 2-*isomorphism* of the two, not
an equality, and nothing in this development rigidifies that;
`AlgebraicGeometry.Space.eq_of_smallEtaleRingedToposHom_twoIso` is about two morphisms of
algebraic *spaces*, not two morphisms of ringed topoi.  Neither registered statement of Tag 04D0
uses it.

## Main definitions

* `AlgebraicGeometry.Space.InducesSmallEtaleRingedToposHom`: the relation "the morphism of
  small étale ringed topoi of `k` is 2-isomorphic to `ψ`", i.e. "`k` induces `ψ`".
* `AlgebraicGeometry.Space.IsRecoveredFromSmallEtale`: the assertion of
  [Stacks Project, Tag 04KL] over a base, in the form its consumers use — a locally ringed
  morphism of the small étale ringed topoi of two algebraic spaces which is 2-compatible with a
  pair of structure morphisms to a third is induced by exactly one morphism of algebraic
  spaces.  It is a *definition* rather than a hypothesis: it is proved for a base scheme whose
  canonical morphism to the spectrum of its global functions is a monomorphism, by
  `AlgebraicGeometry.Space.isRecoveredFromSmallEtale_of_mono_toSpecΓ`.
* `AlgebraicGeometry.Space.IsRecoveredFromSmallEtaleOver`: the same assertion with the third
  algebraic space fixed, so that `IsRecoveredFromSmallEtale` is `∀ A₀, …Over A₀`.
* `AlgebraicGeometry.Space.baseSpace`: the base, read as the terminal algebraic space over
  itself.
* `AlgebraicGeometry.Space.smallEtaleRingedToposHomCompTwoIso`: functoriality of
  [Stacks Project, Tag 03G8] as a 2-isomorphism of morphisms of ringed topoi.
* `AlgebraicGeometry.Space.DerivationModification`: the modification of the structure map of a
  morphism of first order thickenings by an `𝒪_X`-linear map `θ : a^*Ω_{Y/T} ⟶ 𝒞_{X/X'}`.
* `AlgebraicGeometry.Space.ThickeningDerivationFamily`: the assignment `θ ↦ D` of Equation
  (0619) read on the site of `X'`, which is what remains unconstructed of that datum.
* `AlgebraicGeometry.Space.derivationFamilyHom`: **the modified structure map
  `α = (a')^♯ + D` as a morphism of the small étale ringed topoi of `X'` and `Y'`** — the field
  `hom` of the datum.
* `AlgebraicGeometry.Space.derivationModificationOfFamily`: **the datum built rather than
  assumed**, from the family and the three clauses `square`, `algebra` and `injective`.
* `AlgebraicGeometry.Space.ambientConormalDerivation`: **Equation (0619) carried to the site of
  the ambient space `X'`** — the `𝒪_T`-derivation of `(a')^{-1}𝒪_{Y'}` attached there to a map
  `(i_X ≫ a')^*Ω_{Y'/T} ⟶ 𝒞_{X/X'}`, and
  `AlgebraicGeometry.Space.ambientConormalDerivationFamily` its unbundled form.
* `AlgebraicGeometry.Space.ambientThickeningDerivationMap`: the map `θ` of Tag 04D0 read on the
  ambient target, given the square `i_X ≫ a' = a ≫ i_Y`.
* `AlgebraicGeometry.Space.thickeningDerivationFamilyOfHom`: **the family built rather than
  assumed**, from `θ`, that square, and the vanishing of the transport at the base point.

## Main results

* `AlgebraicGeometry.Space.isLocallyRinged_of_thickeningSquare`: a morphism of the small étale
  ringed topoi of the two ambient spaces fitting the source's square is locally ringed.
* `AlgebraicGeometry.Space.eq_of_inducesCommonSmallEtaleRingedToposHom`:
  **[Stacks Project, Tag 05ZN], the uniqueness clause**, unconditionally — at most one morphism
  of algebraic spaces over `S` induces a given morphism of their small étale ringed topoi.  This
  is the faithfulness half of Tag 04KL over a base, and [Stacks Project, Tag 04M6] proves it.
* `AlgebraicGeometry.Space.isRecoveredFromSmallEtale_of_mono_toSpecΓ`:
  **[Stacks Project, Tag 04KL] over a base scheme whose canonical morphism to the spectrum of its
  global functions is a monomorphism** — the existence half included.  The source proves the tag
  over `Spec ℤ` and the proof of Tag 05ZN omits the verification over a base; this is that
  verification, for such a base scheme.
* `AlgebraicGeometry.Space.existsUnique_thickeningHom`:
  **[Stacks Project, Tag 05ZN]** over such a base scheme, both clauses and with nothing taken
  as an argument.
* `AlgebraicGeometry.Space.existsUnique_thickeningHom_of_ringedToposHom`:
  **[Stacks Project, Tag 05ZN]** over an arbitrary base scheme, with nothing taken as an
  argument.
* `AlgebraicGeometry.Space.existsUnique_hom_of_derivationModification_of_mono_toSpecΓ`:
  **[Stacks Project, Tag 04D0]** over such a base scheme, with the modification datum taken
  as an argument.
* `AlgebraicGeometry.Space.isRecoveredFromSmallEtale_of_baseSpace`: **the quantification over
  the base in `IsRecoveredFromSmallEtale` is redundant, with nothing assumed** — Tag 04KL over
  the base `S` alone implies it over every base, by the 2-isomorphism calculus of
  `AlgebraicGeometry.Space.smallEtaleRingedToposHomCompTwoIso`.  This is the half of "Tag 04KL
  and Tag 04SG give the form used here" that needs no comparison of bases; Tag 04KL over a base
  itself is `AlgebraicGeometry.Space.isRecoveredFromSmallEtale_holds`, downstream of this file.
* `AlgebraicGeometry.Space.eq_of_derivationModification_induces`: **the uniqueness clause of
  Tag 04D0** for an abstract modification datum, proved outright — two morphisms with the
  modified structure map are equal.
* `AlgebraicGeometry.Space.eq_of_derivationModification_eq`: two maps `θ` which modify `(a')^♯`
  to the same morphism of thickenings are equal, so the correspondence `θ ↦ b'` is injective.
* `AlgebraicGeometry.Space.eq_of_derivationModification_base_of_induces`: the morphism of
  thickenings attached to the zero map is `a'` itself.  Tag 04KL over a base is **not** taken as
  an argument here: only its faithfulness half is used, and that is proved.
* `AlgebraicGeometry.Space.isLocallyRinged_derivationFamilyHom` and
  `AlgebraicGeometry.Space.derivationFamilyHom_base`: the fields `isLocallyRinged` and
  `hom_base` of the datum, proved.

Four declarations state the same results with Tag 04KL over a base — and, in one case, the local
ringedness of `Φ` — taken as explicit arguments:
`AlgebraicGeometry.Space.eq_of_inducesSmallEtaleRingedToposHom`,
`AlgebraicGeometry.Space.existsUnique_thickeningHom_of_isLocallyRinged`,
`AlgebraicGeometry.Space.existsUnique_hom_of_derivationModification` and
`AlgebraicGeometry.Space.eq_of_derivationModification_base`.  Those are the shapes in which the
results were first written, before either argument could be discharged; they are kept unchanged,
and the tags are registered on the forms above, which assume less.

## Implementation notes

The source's `α` is a map `f^{-1}𝒪_{Y'} ⟶ 𝒪_{X'}` of sheaves on the small étale site of
`X ≅ X'`, and both its source and the commuting square it is asked to fit into are stated
through the identification of the small étale topoi of `X` and of `X'`, which is
[Stacks Project, Tag 05ZM].  Both are written here on the ambient spaces instead: a pair
`(f_{spaces,étale}, α)` is exactly a `AlgebraicGeometry.RingedToposHom` between the small étale
ringed topoi of `X'` and `Y'`, and the source's commuting square becomes `hsquare` below, an
equation between two morphisms of ringed topoi from the small étale topos of `X` to that of
`Y'`.  The locality of `Φ` is read off that square on the ambient spaces, by
`AlgebraicGeometry.Space.isLocallyRinged_of_thickeningSquare`.

Both halves of Tag 05ZM are available, so `Φ` is known to be locally ringed and the sum
`(a')^♯ + D` can be formed.  The
structure-sheaf half is `AlgebraicGeometry.Space.isIso_thickeningFundamentalHom_fSharp` of
`EtaleRingedTopos.lean`, which with `thickeningFundamentalHom`,
`thickeningFundamentalHomInverse` and their two locally-ringed clauses gives an *invertible
morphism of locally ringed topoi* between `(Sh(X_étale), i^{-1}𝒪_{X'})` and
`(Sh(X'_étale), 𝒪_{X'})`.  The sum is formed by
`AlgebraicGeometry.Space.conormalSourceDerivationActionHom` of
`LiftDifferenceSquareZeroValues.lean`, and the technique for its local ringedness is
`AlgebraicGeometry.Space.isLocallyRinged_of_isNilpotent_sub_sections_smallEtale` of
`SmallEtaleRingedToposIsoLocallyRinged.lean`.

`hlocal` and `DerivationModification` are nevertheless still arguments rather than
conclusions.  The conormal ideal, which lives in `i^{-1}𝒪_{X'}` on the small étale site of `X`,
is carried onto the site of `X'`, where the field needs it, by a transport of a
`Stacks.Sites.SquareZeroValues` along an isomorphism of ringed topoi: the transport is
`AlgebraicGeometry.Space.conormalAmbientSquareZeroValues` of
`ConormalAmbientSquareZeroValues.lean`, which is
`Stacks.Sites.SquareZeroValues.ofIsoAmbient` at the unit `𝒪_{X'} ⟶ i_*i^{-1}𝒪_{X'}`, and the
locally ringed conclusion for a structure map perturbed by it is
`AlgebraicGeometry.Space.isLocallyRinged_of_sub_eq_conormalAmbientSquareZeroValues_ι`.

`hlocal` is still an argument of `existsUnique_thickeningHom_of_isLocallyRinged`, which is stated
for an arbitrary `Φ` and so cannot know where its structure map came from.  The field `hom θ` of
`DerivationModification` asks for the perturbed map of sheaves of rings to be carried back into an
`AlgebraicGeometry.RingedToposHom`.  The passage back is
`AlgebraicGeometry.Space.conormalAmbientDerivationRingedToposHom`: forgetting commutativity is
fully faithful on sheaves, so the perturbed map has a unique preimage on sheaves of commutative
rings, and `AlgebraicGeometry.RingedToposHom.ofInverseImageMap` transposes that preimage along
`Stacks.Sheaves.ToposPushforward.commRingImageAdjunction` — both steps are
generic, and neither needs Tag 05ZM.  With it `hom`, `isLocallyRinged` and `hom_base` are
all proved, the last as an equality of morphisms of ringed topoi; `square`, `algebra` and the
injectivity of Tag 0619 are the three clauses that genuinely remain, and the derivation
`D = d_{Y/T} ∘ θ` of Equation Tag 0619 is still assumed, as the field `d` of
`AlgebraicGeometry.Space.ThickeningDerivationFamily`.

The derivation of the family is constructed, although
`AlgebraicGeometry.Space.derivationDirectImageEquiv` states Equation (0619)
on the small étale site of the *closed subspace* `Y` while the modified structure map `α` needs a
derivation of `(a')^{-1}𝒪_{Y'}` on the site of `X'`, and although neither
`PresheafOfModules.Derivation'.precomp` — which precomposes along a morphism of presheaves of
rings over a *fixed* site — nor the inverse-image transport of
`StacksFrontier/Cotangent/SheavesOfRings/InverseImageDerivations.lean` performs the composite.
The transport does not need to
start on the site of `Y`: Equation (0619) is a statement about an arbitrary pair of morphisms, so
reading it at the *composite* `i_X ≫ a' : X ⟶ Y'` and at `p_{Y'}` gives an `𝒪_T`-derivation of
`𝒪_{Y'}` with values in `(i_X ≫ a')_*𝒞_{X/X'}` on the site of `Y'` directly, and the only step
left is the change of site, which is precisely what
`Stacks.Sheaves.RingedToposModules.inverseImageDerivationEquiv` of that file does.  The source
sheaf of rings never changes; what changes is the sheaf of differentials, and the comparison
`i_Y^*Ω_{Y'/T} ⟶ Ω_{Y/T}` carrying `θ` across it is [Stacks Project, Tag 04CX],
`AlgebraicGeometry.Space.sheafOfDifferentialsMap`.  The composite is
`AlgebraicGeometry.Space.ambientConormalDerivation`, and
`AlgebraicGeometry.Space.thickeningDerivationFamilyOfHom` builds the family from it.

Two inputs of that construction are not discharged, and neither concerns derivations.  The
square `i_X ≫ a' = a ≫ i_Y` — the hypothesis of Tag 04D0 that `(a, a')` *is* a morphism of
thickenings — is not among the parameters of `ThickeningDerivationFamily`, so it is an argument.
And the vanishing of the transported derivation at the base point is an argument: the proof
factors the zero coefficient map out through
`Stacks.Sheaves.RingedToposModules.inverseImageDerivationEquiv_symm_postcomp` and both
adjunctions involved are additive, but assembling it at the concrete instance runs into a
deterministic `isDefEq` timeout where two `PresheafOfModules.Derivation.postcomp`s have to be
composed — a composition that is `rfl` at an arbitrary site and not checkable at the sections of
the small étale structure sheaf.  That is the same hazard that forces the unbundled family in the
first place, and nothing here raises `maxHeartbeats` to step over it.

**There is a 04KL-free route to a narrower statement, and it is not a second route to this
tag.** `AlgebraicGeometry.Space.existsUnique_hom_structureSharpThroughThickeningAt_eq` of
`StacksFrontier/AlgebraicGeometry/Spaces/DeformationLiftDerivationActionChart.lean` proves the
existence and the uniqueness of the morphism of thickenings over the base realizing a prescribed
map of algebras, with no appeal to `IsRecoveredFromSmallEtale`: the morphism is glued from its
chartwise values and the uniqueness is the faithfulness of the comorphism on affine chart
diagrams,
`AlgebraicGeometry.Space.eq_of_structureSharpThroughThickeningAt_eq`.

That does **not** discharge `hKL` here, and no statement in this file may drop it on that
account. Two things differ, and each narrows the subject of Tag 05ZN rather than deferring a
hypothesis of it, which is why that statement carries no `@[stacks 05ZN]` attribute and
`AlgebraicGeometry.Space.existsUnique_thickeningHom_of_isLocallyRinged` below is the library's
only carrier of the tag. The map `α` is spelled there as a solution of the lifting problem, a
morphism `𝒪_{Y'} ⟶ (i_X ≫ a')_*(i_X^{-1}𝒪_{X'})` of sheaves on the small étale site of the
ambient *target*, where the statements here read `α` on the site of the ambient *source* and
packaged as an `AlgebraicGeometry.RingedToposHom`; the two readings are identified by Equation
[Stacks Project, Tag 05ZM], whose structure-sheaf half is proved as
`AlgebraicGeometry.Space.isIso_thickeningFundamentalHom_fSharp` and whose sheaf-of-sets half is
`AlgebraicGeometry.Space.isEquivalence_smallEtalePushforward_of_isThickening`, both for an
arbitrary thickening.  The identification is performed at a fixed morphism, in both directions, for an
arbitrary thickening, by `AlgebraicGeometry.Space.thickeningLiftComparison` and
`AlgebraicGeometry.Space.thickeningLiftComparisonInv` of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/ThickeningSharpChartProjection.lean`, with
`AlgebraicGeometry.Space.structureSharpThroughThickening_eq_comp` and
`AlgebraicGeometry.Space.structureSharpThroughThickening_comp_comparisonInv` the two directions.
What is *not* given by that comparison is the tag's reading of an **arbitrary** solution `α` on
the source site, the comparison being indexed by a morphism which in the tag is the conclusion.
And the uniqueness half there asks the thickening to be of first order, which Tag 05ZN does not.

So two separate things remain open at this tag.  For the chartwise
route, the arbitrary-thickening uniqueness is reached through a
`AlgebraicGeometry.RingedToposHom.TwoIso` and
`AlgebraicGeometry.Space.eq_of_smallEtaleRingedToposHom_twoIso` ([Stacks Project, Tag 04M6], the
proved uniqueness half of Theorem 04KL), rather than through the chart step, which rests on étale
lifting along a *first order* thickening ([Stacks Project, Tag 0611]).  **The geometric field of
that 2-isomorphism is constructed**, as `AlgebraicGeometry.Space.agreeingPushforwardIso` of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/EtaleRingedTopos.lean`; its structure-map field
is what remains, and the implementation notes there record both what closing it requires — a
reconciliation of the three parallel presentations of the structure map, not any further geometry
— and the kernel-defeq hazard that governs computation with the components.  The spelling of `α`
is a separate question, settled by neither.  The statements in this file keep `hKL`, the
*existence* half of Theorem 04KL over a base, which none of this supplies.

`IsRecoveredFromSmallEtale` is quantified over all pairs of algebraic spaces and over all of the
third spaces `A` playing the part of the base.  The deduction below uses it **once**, on `Φ`
with `A := T`, to produce `f'`; the two recognitions that follow — `i_X ≫ f'` as
`f ≫ i_Y`, and `f' ≫ p_{Y'}` as `p_{X'}` — are *not* further appeals to it, since each is an
equality of two morphisms inducing 2-isomorphic morphisms of small étale ringed topoi and so is
settled by the faithfulness half,
`AlgebraicGeometry.Space.eq_of_inducesCommonSmallEtaleRingedToposHom`
below, which is proved.  Both use Tag 04KJ for the locality of the morphism of ringed topoi of a
morphism of algebraic spaces and the functoriality 2-isomorphism
`AlgebraicGeometry.Space.smallEtaleRingedToposHomCompTwoIso` to split the composite.  So the only
input left to the caller is the 2-compatibility of `Φ` with `p_{X'}` and `p_{Y'}`, which is the
source's hypothesis that `α` is a map of `𝒪_T`-algebras.  The quantification over the pair and
over `A` is what makes the assumption Tag 04KL over a base rather than a restatement of the
conclusion: the consumers apply it at an arbitrary pair of ambient spaces and an arbitrary `T`.

`AlgebraicGeometry.Space.smallEtaleRingedToposHomCompTwoIso` assembles the comparison
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` of the direct images, which is Tag 03G2
part (3) at the universe of the structure rings, with the compatibility of the structure maps
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_comp_fSharp`.  Those are the two fields of a
2-isomorphism, so no new mathematics is involved; what the definition adds is the packaging,
without which the whiskering calculus of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RingedToposTwoMorphism.lean` cannot be applied to
the morphisms of ringed topoi of morphisms of algebraic spaces.

Of the sum `α = (a')^♯ + D` the datum `DerivationModification` records only what the source's
proof uses: that it fits the two squares which 05ZN consumes, that the zero map returns
`(a')^♯`, and that distinct `θ` give non-2-isomorphic morphisms of ringed topoi, the last being
injectivity of the bijection of Equation (0619)
(`AlgebraicGeometry.Space.derivationDirectImageEquiv`) composed with additivity of the
difference.  The first order conditions on the two thickenings are fields of the datum because
they are what make the sum a ring map and are used nowhere in the deduction from 05ZN.  The
source's base point is the zero map; it is a field `base` rather than the numeral `0` so that
the statement does not depend on which spelling of the zero map is used.

## References

* [Stacks Project, Tag 05ZN](https://stacks.math.columbia.edu/tag/05ZN)
* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0)
* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
* [Stacks Project, Tag 04M6](https://stacks.math.columbia.edu/tag/04M6), the faithfulness,
  which is what makes the uniqueness clauses here unconditional.
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 04KJ](https://stacks.math.columbia.edu/tag/04KJ)
* [Stacks Project, Tag 04HA](https://stacks.math.columbia.edu/tag/04HA)
* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM)
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619)
* [Stacks Project, Tag 08TQ](https://stacks.math.columbia.edu/tag/08TQ), the transposition of
  derivations along a morphism of topoi.
* [Stacks Project, Tag 04M6](https://stacks.math.columbia.edu/tag/04M6), the uniqueness half of
  Theorem 04KL.
* [Stacks Project, Tag 0611](https://stacks.math.columbia.edu/tag/0611), lifting along a
  formally étale morphism.
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX), the comparison map of
  sheaves of differentials attached to a commutative square.
-/
