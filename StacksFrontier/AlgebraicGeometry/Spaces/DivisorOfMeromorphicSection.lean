module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.IntegralClosedSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSections
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianIrreducibleComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.OrderOfVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.RationalFunctions

/-!
# The Weil divisor of a meromorphic section on an algebraic space

Let `X` be a locally Noetherian integral algebraic space over `S`, let `ℒ` be an `𝒪_X`-module
and let `s` be a regular meromorphic section of `ℒ`. At the generic point `ξ` of a prime
divisor `Z ⊆ X` the section has a ratio `s / s_ξ` against a generator `s_ξ` of `ℒ` there, a
unit of the total ring of fractions `Q(𝒪^h_{X,ξ})`, and the *order of vanishing of `s` along
`Z`* is the order of vanishing of that unit, that is
`length (𝒪^h_{X,ξ} ⧸ a) - length (𝒪^h_{X,ξ} ⧸ b)` for `s / s_ξ = a / b`. The family of these
integers over all prime divisors is the Weil divisor `div_ℒ(s) ∈ Div(X)`, and it is a Weil
divisor because only finitely many prime divisors meet a neighbourhood of any given point.

## Main definitions

* `AlgebraicGeometry.Space.LocalRatio` and `AlgebraicGeometry.Space.LocalRatioFamily` are a
  choice of generator of `ℒ` at the generic point of a prime divisor, respectively of every
  prime divisor, read off as the ratio it assigns to a meromorphic section.
* `AlgebraicGeometry.Space.orderOfVanishingSection` is `ord_{Z,ℒ}(s)` of Stacks 0EPR.
* `AlgebraicGeometry.Space.divisorCoefficients`,
  `AlgebraicGeometry.Space.divisorOfSection` and
  `AlgebraicGeometry.Space.divisorOfSectionOfGenerating` are `div_ℒ(s)` of Stacks 0EPU, as a
  family of integer coefficients and as an element of `Div(X)`.

## Main results

* `AlgebraicGeometry.Space.locallyFinite_primeDivisor_of_genericPoint_notMem` is the **Stacks
  0EE5 step in the proof of Stacks 0EPS**: a family of prime divisors whose generic points all
  avoid one nonempty open subset of `|X|` is locally finite. Both sets of the source are of
  that form, the open subset being the one over which `s` generates `ℒ`;
  `AlgebraicGeometry.Space.locallyFinite_divisorCoefficients_ne_zero` specializes it to the
  second of them. Both carry **Stacks 0EPS** and both carry the nonempty open subset as a
  *hypothesis*, which their attribute notes record, whereas Stacks 0EPS asserts local
  finiteness from regularity of `s` alone. See the implementation notes for what is missing,
  which differs between the two sets.
* `AlgebraicGeometry.Space.orderOfVanishingSection_eq_length_sub_length` is the length formula
  on any presentation of the ratio, hence its independence of the presentation;
  `AlgebraicGeometry.Space.exists_orderOfVanishingSection_eq_length_sub_length` is the
  companion existence clause — a presentation `s / s_ξ = a / b` by nonzerodivisors of
  `𝒪^h_{X,ξ}` always exists, so the length formula describes every value of
  `ord_{Z,ℒ}(s)`; and `AlgebraicGeometry.Space.orderOfVanishingSection_unit_smul` is the
  independence of the choice of the generator `s_ξ`.
* `AlgebraicGeometry.Space.orderOfVanishingSection_eq_zero_of_isUnit`: the order of vanishing
  is zero where the ratio is a unit of `𝒪^h_{X,ξ}` itself, that is where `s` generates `ℒ`.
* `AlgebraicGeometry.Space.orderOfVanishingSection_eq_add_ord` is **Stacks 0EPT** and
  `AlgebraicGeometry.Space.orderOfVanishingSection_mul` is **Stacks 0EPV**, both
  coefficientwise at each prime divisor.

## Implementation notes

The order of vanishing itself is `AlgebraicGeometry.Space.PrimeDivisor.ord` of
Stacks 0ENL, on the total ring of fractions of the henselian local ring at the generic point;
nothing of it is rebuilt here. Its three standing hypotheses — nontrivial, Noetherian, of Krull
dimension at most one — are the content of Stacks 0ENK and are carried, as there, as instance
arguments, quantified over all prime divisors where a whole family of orders is taken at once.

The ratio `s / s_ξ` of the source is the pullback of `s` along the canonical morphism
`c_ξ : Spec(𝒪^h_{X,ξ}) → X` divided by a generator `s_ξ` of `c_ξ^*ℒ`. Neither `c_ξ` nor the
canonical embedding `R(X) → Q(𝒪^h_{X,ξ})` of Stacks 0ENK is missing any more: `c_ξ` is
`AlgebraicGeometry.Space.PrimeDivisor.genericHenselianMorphism`
(`StacksFrontier/AlgebraicGeometry/Spaces/Decent/PrimeDivisorHenselianSpecMorphism.lean`), and it
is flat (`AlgebraicGeometry.Space.PrimeDivisor.isFlat_genericHenselianMorphism`), so the flat
pullback of meromorphic sections of Stacks 0EN8 and 0EN9 applies to it; and the embedding is
`AlgebraicGeometry.Space.PrimeDivisor.rationalFunctionsToGenericTotalFractionRing`
(`StacksFrontier/AlgebraicGeometry/Spaces/Decent/PrimeDivisorFunctionFieldEmbedding.lean`), which
is injective and reads a rational *function* at `ξ` through an affine elementary étale
neighbourhood of `ξ`.

What is still missing is the *quotient* by a generator. Reading a meromorphic *section* of `ℒ`
at `ξ` the same way needs in addition the sections of `𝒦_X(ℒ)` over an affine chart carrying a
free generator `e` of `ℒ` to be exactly the multiples `𝒦_X(U) · e`, the module analogue of
Stacks 0EN6, part (2), which is absent — over a covering sieve of the chart it is
`AlgebraicGeometry.Space.exists_eval_toMeromorphicSectionSheaf_sieve_mem`, and a covering sieve
admits no elementary refinement, a separable residue extension being étale. See also the
discussion of Stacks 0EPS below, where the two facts it needs are named.

So `ratio` and `emb` remain explicit parameters here, `emb` being the embedding along which
Stacks 0EPT below compares two ratios; the definitions have real bodies in terms of them and
the attribute strings record it. A single
`ratio` per prime divisor plays the role of the single choice of `s_ξ` the source makes there,
so that two meromorphic sections of the same module are compared through the same generator,
as in the proofs of Stacks 0EPT and 0EPV. That the ratio takes values in the *units* of
`Q(𝒪^h_{X,ξ})` is regularity of the meromorphic section, which is where the source uses it.

For the same reason the *restriction to the prime divisor* is absent. That restriction is not a
restriction of `s`, which would need the meromorphic pullback along a closed immersion and so
along a non-flat morphism: what Stacks 0EQU restricts is the chosen generator `s_ξ`, whose
image in the fibre `ℒ_ξ ⊗_{𝒪^h_{X,ξ}} κ(ξ)` is a nonzero meromorphic section `s_ξ|_Z` of
`ℒ|_Z`. Producing it needs `ℒ_ξ = c_ξ^*ℒ` as a free rank-one module, which is what `ratio`
stands in for, and the identification of `κ(ξ)` with the function field `R(Z)`; neither is
available, so `s_ξ|_Z` cannot be built here.

The source states `ord_{Z,ℒ}(s)` for an invertible `ℒ`; invertibility is never used, exactly
as for `AlgebraicGeometry.Space.IsRegularMeromorphicSection`, so the definitions are stated
for an arbitrary `𝒪_X`-module.

Stacks 0EPT and 0EPV are stated here coefficientwise, at each prime divisor; the equivalent
identities of Weil divisors that the source states need the group `Div(X)` and the principal
divisor of Stacks 0ENP, so they are proved where those are available, in
`AlgebraicGeometry.Space.divisorOfSection_eq_add_principalDivisor` for Stacks 0EPT and in
`AlgebraicGeometry.Space.PicardDivisorData.divisor_picardTensorModule` for Stacks 0EPV.

### What the Stacks 0EPS registrations still carry

`AlgebraicGeometry.Space.locallyFinite_primeDivisor_of_genericPoint_notMem` is the second and
third sentences of the proof of Stacks 0EPS — the appeal to Stacks 0EE5 — stated over an
arbitrary predicate on prime divisors, which is the form that proof establishes and which
covers both of the source's sets at once. The *first* sentence of that proof, "there exists a
nonempty open subspace `U ⊆ X` such that `s` corresponds to a section of `Γ(U, ℒ)` which
generates `ℒ` over `U`", is not available in this library, so it is carried as the hypothesis
quadruple `(U, hUopen, hUne, hP)`, which the attribute notes on the two lemmas record. The two
sets are blocked differently, and the first is much the closer of the two.

The geometric input the first sentence needs is available, and it does not even need Stacks
0ENA. For an *invertible* `ℒ` the route is Stacks 0EN6, part (2),
`AlgebraicGeometry.Space.isFractionRing_meromorphicFunctionSheaf_obj`: over an affine chart
`𝒦_X` is the total ring of fractions of `𝒪_X`. Over a chart where `ℒ` is free with generator
`e` — `AlgebraicGeometry.Space.exists_generator_cover_of_isInvertible`, which also makes
`a ↦ a ⊗ e` bijective on meromorphic sections — the section `s` is `a ⊗ e` for a single
meromorphic function `a`, available on a covering sieve by
`AlgebraicGeometry.Space.exists_eval_toMeromorphicSectionSheaf_sieve_mem`; refining to an
affine chart writes `a = p / q` with `q` a nonzerodivisor, and on the basic open of `q` the
function `a` is regular, so `s` is there the honest section `(p/q) • e`. That basic open
contains every generic point of the chart, by
`AlgebraicGeometry.mem_basicOpen_of_mem_nonZeroDivisors_of_mem_genericPoints`, so its image in
`|X|` is a nonempty open — this is exactly the argument the *function*-level
`AlgebraicGeometry.Space.exists_openSection_of_affineOpen`
(`StacksFrontier/AlgebraicGeometry/Spaces/SpaceRationalFunctionsMeromorphic.lean`) makes for
`𝒦_X`, transposed to `𝒦_X(ℒ)`. The three hypotheses of Stacks 0ENA that 0EN6, part (2) needs
are not carried: they are derived from "locally Noetherian integral" in
`StacksFrontier.AlgebraicGeometry.Spaces.IntegralCodimensionZeroHypotheses`.

The step that carries such a representation from `η` down to a codimension-one point `ξ` is
available too. `AlgebraicGeometry.Space.PrimeDivisor.genericMeromorphicGerm` reads `s` at `ξ`
through `AlgebraicGeometry.Space.pullbackMeromorphicSection` of Stacks 0ENC, part (1), and that
map **does** have an evaluation lemma:
`AlgebraicGeometry.Space.pullbackMeromorphicSection_eval`, with the chart-diagram variant
`AlgebraicGeometry.Space.pullbackMeromorphicSection_eval_chartDiagram`
(`StacksFrontier/AlgebraicGeometry/Spaces/MeromorphicSectionGlobalPullbackValue.lean`). Given a
chart `V` of `X` over which `s` is the image of a meromorphic section `t` of `ℒ ⊗_{𝒪_X} 𝒦_X`,
it computes the value of `f^*s` over a chart above `V` as the image of the chartwise rule
applied to `t`; and `AlgebraicGeometry.Space.chartPullbackMeromorphicSectionsSheaf_tmul`
evaluates that rule on a pure tensor, `a ⊗ m ↦ (f^♯a) ⊗ (f^*m)`. Taking `t` to be
`AlgebraicGeometry.Space.pureMeromorphicSection`, that is `1 ⊗ e` for an honest section `e` of
`ℒ` over `V` — which is exactly the hypothesis `AlgebraicGeometry.Space.toMeromorphicSectionValue`
packages — the rule returns `1 ⊗ (c_ξ^*e)`, so the germ of `s` at `ξ` is the image of a section
of `ℒ_ξ` and `AlgebraicGeometry.Space.PrimeDivisor.MemGenericModuleStalk` holds. No API is
missing for this step.

**What remains for the first set is one step, and it is not an API gap: the route through a
henselian retraction does not close, for a reason about residue fields.** The representation of
`s` above is obtained on *some* affine chart refining a covering, whereas
`AlgebraicGeometry.Space.pullbackMeromorphicSection_eval` can only be applied at a chart the
germ's own morphism factors through, and
`AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.toSpaceHom_hom` factors `c_ξ` through
exactly one chart, the elementary étale neighbourhood
`AlgebraicGeometry.Space.PrimeDivisor.genericChart` that `𝒪^h_{X,ξ}` is the henselization of.
Transporting the representation there asks for a morphism `Spec(𝒪^h_{X,ξ}) ⟶ W'` over
`genericChart`, for `W'` the étale refinement the representation was obtained on.

The obvious supply for that is item (7) of Stacks 04GG, the splitting of étale algebras over a
henselian local ring, which **is** formalized as `henselian_etale_retraction`
(`StacksFrontier/RingTheory/Henselian/EtaleLifting.lean:215`, with the uniqueness half at `:639`).
It does not apply. Its residue hypothesis is

`hres : Function.Bijective (Ideal.ResidueField.map (maximalIdeal S) 𝔫 (algebraMap S B) hlo.symm)`,

that is **`κ(𝔫) = κ(S)`, a trivial residue extension at the chosen prime**. For an arbitrary
étale refinement `W' ⟶ genericChart` with a point `w'` over `ξ` the extension
`κ(ξ) ⟶ κ(w')` is finite separable but need not be trivial, and nothing makes it so. Stacks
0EN0 (`AlgebraicGeometry.Space.exists_residueFieldEquiv_residueField`) does not supply it: it
identifies the residue field of `𝒪^h_{X,ξ}` with the residue field of `X` at `ξ`, saying
nothing about `κ(w')`.

Nor can the refinement be taken *elementary*, where the condition would hold by the
`mono_residueField` field of `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood`: elementary
étale neighbourhoods of `ξ` are **not** cofinal among étale charts carrying a point over `ξ`.
A morphism `E ⟶ W'` over `X` from an elementary neighbourhood would force the point of `W'` it
hits to have residue field `κ(ξ)`, so a `W'` all of whose points over `ξ` have nontrivial
residue extension admits none — `Spec` of a nontrivial finite separable extension of `κ(ξ)`,
étale over `X` near `ξ`, is such a `W'`. Accordingly
`AlgebraicGeometry.Space.elementaryEtaleNeighborhoodOfMono` takes monicity of the residue point
as a *hypothesis*, and the tree has no cofinality statement.

The descent that this suggests is now **proved**, and so is a lift that makes the étale covering
unnecessary at the one chart where it matters.

*The descent.* `AlgebraicGeometry.Space.injective_toMeromorphicSectionValue`
(`StacksFrontier/AlgebraicGeometry/Spaces/MeromorphicSectionValueDescent.lean`) is injectivity of
`ℒ ⟶ 𝒦_X(ℒ)` on the sections over every étale chart, for `ℒ` invertible, so the image of that
map is a *subsheaf* of `𝒦_X(ℒ)` and lying in `ℒ` is a local condition:
`AlgebraicGeometry.Space.exists_toMeromorphicSectionValue_eq_of_sieve`, with
`AlgebraicGeometry.Space.exists_eval_eq_toMeromorphicSectionValue_of_sieve` for the value of a
global meromorphic section at a chart. The general form is
`Stacks.Sites.exists_eq_of_locally_exists`: an injective family of maps of sections, natural in
the object of a site, out of a sheaf into a sheaf has a sheaf for its image. It is not an
instance of `Stacks.SheafOfModules.ImageSubsheaf.exists_app_eq_of_mem_imageSubmodule`, the same
argument for a monomorphism of sheaves of modules, because `ℒ ⟶ 𝒦_X(ℒ)` is not a morphism of
sheaves of modules over one sheaf of rings — the coefficients and the universes both differ,
which is exactly why `AlgebraicGeometry.Space.toMeromorphicSectionValue` is given chart by
chart. Invertibility of `ℒ` enters only through the free generator, and it is needed: for a
module with torsion the statement is false, the torsion being killed in `𝒦_X(ℒ)`.

*The lift, at the generic chart.* `c_ξ` factors through `genericChart` on the nose, and
`AlgebraicGeometry.Space.PrimeDivisor.genericEtaleChart`
(`StacksFrontier/AlgebraicGeometry/Spaces/Decent/PrimeDivisorGenericModuleStalkMem.lean`) is that
elementary étale neighbourhood read as an object of the small étale site of `X`. The
factorization is a commuting square of charts whose chart of `Spec(𝒪^h_{X,ξ})` is the identity
one, the structure morphism of the identity chart being `𝟙`, so
`AlgebraicGeometry.Space.pullbackMeromorphicSection_eval_toMeromorphicSectionValue` — the global
pullback of an honest section is an honest section — applies there and gives
`AlgebraicGeometry.Space.PrimeDivisor.memGenericModuleStalk_of_eval_genericEtaleChart_eq`: **if
`s` is an honest section of `ℒ` over the generic chart of `Z`, then `s` lies in `ℒ_ξ`.** No
retraction and no cofinality is used. The base-change form is available as well, as
`AlgebraicGeometry.Space.PrimeDivisor.memGenericModuleStalk_of_sieve`, which descends the
condition from any covering sieve of the identity chart of `Spec(𝒪^h_{X,ξ})`, the pullback
`ℒ_ξ` being invertible by `AlgebraicGeometry.Space.isInvertible_modulePullback_obj`.

So the first set reduces to **one** geometric statement, and
`AlgebraicGeometry.Space.locallyFinite_primeDivisor_not_memGenericModuleStalk`
(`StacksFrontier/AlgebraicGeometry/Spaces/Decent/LocallyFiniteNotMemGenericModuleStalk.lean`) is
that reduction carried out: the first collection of Stacks 0EPS is locally finite given a
nonempty open `U ⊆ |X|` such that

  (★) for every prime divisor `Z` with `ξ_Z ∈ U`, the section `s` is over
      `Z.genericEtaleChart` the image under
      `AlgebraicGeometry.Space.toMeromorphicSectionValue` of a section of `ℒ`.

What is missing is (★), and only (★). It needs two things, in this order. First the honest
chart: the `D(q)` argument above, transposed from `𝒦_X` to `𝒦_X(ℒ)`, producing a chart `W` of
`X`, a section `e` of `ℒ` over `W` with `s.eval (op W) = toMeromorphicSectionValue … W e`, and
`U` as the image of `W` in `|X|`. Second the covering: `s` is honest over the Zariski open
subchart of `Z.genericEtaleChart` cut out by the preimage of `U`, which `c_ξ` still factors
through because an open of the spectrum of a local ring containing the closed point is
everything (`AlgebraicGeometry.forall_eq_top_of_mem_of_isLocalRing` together with
`AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.specToScheme_closedPoint`), as soon as the
base change of `W` along that subchart covers it — which is
`AlgebraicGeometry.Space.SmallEtale.mem_topology_iff_exists_mem_range` together with
`AlgebraicGeometry.Space.isSurjective_pullback_snd_of_range_subset`, the surjectivity of a
pullback projection along a morphism whose image on points lies in the image of the other leg.
The second of those is a `private` statement about a slice `Over B` in
`StacksFrontier/AlgebraicGeometry/Spaces/Quotients/PreEquivalenceGeometricCriterion.lean`, whose
consumer `AlgebraicGeometry.Space.exists_lift_of_lft_of_range_subset` is stated for the same
slice; reading it for morphisms of algebraic spaces is what this will need.

Both remaining pieces are geometry on the small étale site of `X`, and neither is blocked: no
universe mismatch, no residue-field condition, no cofinality. Until they are done the two
Stacks 0EPS registrations below keep the nonempty open as a hypothesis and 0EPS stays honestly
half-covered; `AlgebraicGeometry.Space.locallyFinite_primeDivisor_not_memGenericModuleStalk`
deliberately carries no registration, (★) being a hypothesis there.

For the second set the obstruction is structural rather than an API gap.
`AlgebraicGeometry.Space.orderOfVanishingSection` is taken against the
  parameter `ratio` below, which is an arbitrary function of the meromorphic section and is
  constrained by nothing relating it to `ℒ`, to `s` or to `X`. The set of prime divisors with
  `ord_{Z,ℒ}(s) ≠ 0` is therefore not a function of `(ℒ, s)` at all, and no hypothesis on `s` —
  regularity included — can bound it; dropping `hgen` from
  `AlgebraicGeometry.Space.locallyFinite_divisorCoefficients_ne_zero` makes the statement false.
  Constructing `ratio` canonically is still out of reach, but **not for a universe reason.** The
  germ API is quantified over an abstract henselization `R : Type u` of
  the Zariski stalk of `AlgebraicGeometry.Space.PrimeDivisor.genericChart`, whereas
  `AlgebraicGeometry.Space.PrimeDivisor.genericTotalFractionRing`, in which the ratio must take
  its value, is the fraction ring of
  `AlgebraicGeometry.Space.PrimeDivisor.genericHenselianLocalRing`, which is a
  `CommRingCat.{u + 1}`, and the two are nevertheless comparable: both are henselizations of that
  one Zariski stalk with residue field its own residue
  field — the second by Stacks 0EMY,
  `AlgebraicGeometry.Space.henselianLocalRing_isHenselization` — and two henselizations with the
  same residue extension are isomorphic over the base by Stacks 08HT, in **independent
  universes**. That is
  `AlgebraicGeometry.Space.PrimeDivisor.exists_algEquiv_genericHenselianLocalRing`, with the
  forgetful `exists_ringEquiv_genericHenselianLocalRing` beside it
  (`StacksFrontier/AlgebraicGeometry/Spaces/Decent/HenselianLocalRingUniverseComparison.lean`). The
  universe-independent form of Stacks 08HT it rests on is
  `IsLocalRing.IsHenselization.exists_algEquiv_of_residueFieldEquiv`, and
  `exists_algEquiv_of_isHenselization` keeps its one-universe statement beside the
  independent-universe one, `exists_algEquiv_of_isHenselization_independentUniverses`.

  The canonical ratio needs three further inputs, each concerning the germ API. **All three
  are statements in the library**; what is left of each is recorded with it.

  1. *The quotient of germs.* This is settled.
     `AlgebraicGeometry.Space.PrimeDivisor.genericMeromorphicGerm` is a map of underlying sets,
     because `AlgebraicGeometry.Space.pullbackMeromorphicSection` of Stacks 0ENC, part (1) was
     a map of sets of global sections and was not asserted to be additive; it is now, by
     `AlgebraicGeometry.Space.pullbackMeromorphicSection_add` and the bundled
     `AlgebraicGeometry.Space.pullbackMeromorphicSectionAddHom`
     (`StacksFrontier/AlgebraicGeometry/Spaces/MeromorphicSectionGlobalPullbackAdditive.lean`),
     the group structure on `AlgebraicGeometry.Space.MeromorphicSection` being
     `PresheafOfModules.sectionsAddCommGroup`. So a quotient of germs is a
     well-defined notion.
  2. *The generator to divide by.* This is settled.
     `AlgebraicGeometry.Space.PrimeDivisor.exists_ne_zero_span_genericModuleStalk_eq_top`
     (`StacksFrontier/AlgebraicGeometry/Spaces/Decent/PrimeDivisorGenericModuleStalkGenerator.lean`)
     produces a nonzero `t_ξ` with `Submodule.span R {t_ξ} = ⊤` **and** `r ↦ r · t_ξ` bijective,
     out of `AlgebraicGeometry.Space.isInvertible_modulePullback_obj` and
     `AlgebraicGeometry.Space.nonempty_iso_unit_of_isInvertibleModule_of_forall_eq_top`. The
     bijectivity, not the span condition, is what the identification in item 3 consumes: span
     alone gives surjectivity of `r ↦ r · t_ξ` and no injectivity.
  3. *The target of the division.* Dividing the germ, which lives in
     `AlgebraicGeometry.Space.PrimeDivisor.genericMeromorphicModuleStalk`, by a generator of
     `ℒ_ξ` asks for the isomorphism `𝒦_X(ℒ)_ξ ≅ Q(𝒪^h_{X,ξ})` that a generator induces, and
     **both halves of it are now available at the identity chart of `Spec(𝒪^h_{X,ξ})`**, which
     is where the germ API reads everything.

     *The sheaf half does not need the functoriality of `𝒦` in its module at all.*
     `Space.CodimensionZeroPresentation.nonempty_uliftUnit_iso_meromorphicSectionSheaf`
     gives `𝒦_Y ≅ 𝒦_Y(M)` for an invertible `M` on any algebraic space `Y` satisfying
     hypotheses (a), (b) and (c) of Stacks 0ENA and trivialised at the codimension-zero points
     — the composite of `𝒦_Y(ℒ_ξ) ≅ 𝒦_Y(𝒪)` and `𝒦_Y(𝒪) ≅ 𝒦_Y` in one step, so the second of
     those, which the library does not have, is not needed. Its hypotheses for
     `Y = Spec(𝒪^h_{X,ξ})` are now theorems:
     `AlgebraicGeometry.Space.PrimeDivisor.forall_localRingDimension_genericHenselianSpace_eq_zero`,
     `.hasLocallyFiniteIrreducibleComponents_genericHenselianSpace`,
     `.hasMonomorphicCodimensionZeroPoints_genericHenselianSpace` and
     `.nonempty_codimensionZeroPresentation_genericHenselianSpace`
     (`StacksFrontier/AlgebraicGeometry/Spaces/Decent/GenericHenselianSpaceCodimensionZero.lean`),
     the trivialisation at the codimension-zero points being
     `AlgebraicGeometry.Space.CodimensionZeroPresentation.nonempty_iso_unit_of_isInvertibleModule`
     exactly as in the proof of Stacks 0EPQ. `Spec(𝒪^h_{X,ξ})` is representable, so (a) and (b)
     come from `𝒪^h_{X,ξ}` being reduced and Noetherian — which that same file proves of the
     *abstract henselization the germ API carries*, the six ring-theoretic results of Stacks
     0ENK being about `genericHenselianLocalRing`, a different constant one universe up — and
     (c) from `AlgebraicGeometry.Space.isDecentSpace_yoneda`.

     *The ring half is Stacks 0EN6, part (2) at that chart*, which is affine:
     `AlgebraicGeometry.Space.PrimeDivisor.isFractionRing_genericMeromorphicFunctions`
     (`StacksFrontier/AlgebraicGeometry/Spaces/Decent/GenericMeromorphicFractionRing.lean`) is
     `IsFractionRing R 𝒦_Y(V)` for the algebra structure
     `AlgebraicGeometry.Space.PrimeDivisor.genericToMeromorphicFunctions` gives, obtained from
     `AlgebraicGeometry.Space.isFractionRing_meromorphicFunctionSheaf_obj` and transported from
     `Γ(Spec(𝒪^h_{X,ξ}))` to `𝒪^h_{X,ξ}` along `AlgebraicGeometry.Scheme.ΓSpecIso`.

     The three steps between these and the canonical ratio are **all three proved**.

     *The spelling bridge.* The sections of `𝒦_Y` carry two spellings —
     `(Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite … ).O).obj.obj (op V)`,
     over which the scalar action on
     meromorphic sections is found, and `(meromorphicFunctionSheaf … ).obj.obj (op V)`, which is
     the `CommRingCat` object on which `IsFractionRing` can be stated. The two carriers are
     definitionally equal; what was missing was simply the `CommRing` instance at the first
     spelling, and it is now registered once and for all as
     `AlgebraicGeometry.Space.meromorphicChartRing_commRing`, on the named abbreviation
     `AlgebraicGeometry.Space.meromorphicChartRing`
     (`StacksFrontier/AlgebraicGeometry/Spaces/MeromorphicChartRing.lean`). It is built by adding
     `mul_comm` to the ambient `Ring` instance, exactly as
     `AlgebraicGeometry.Space.chartRing_commRing` does for `𝒪_F`, so the `Ring` field stays
     syntactically the one the module sections are modules over. With it,
     `AlgebraicGeometry.Space.PrimeDivisor.isFractionRing_genericMeromorphicChartRing` restates
     Stacks 0EN6, part (2) at the spelling the scalar action uses, with no transport at all, and
     the three steps read normally. No hand-placed bridge survives, and no agreement between
     `AlgebraicGeometry.Space.chartMeromorphicAlgebra`'s `algebraMap` and the component of
     `AlgebraicGeometry.Space.toMeromorphicFunctionSheaf` is needed: step (i) goes through the
     `R`-linear `AlgebraicGeometry.Space.PrimeDivisor.genericModuleStalkToMeromorphic`, whose
     semilinearity is already recorded there.

     (i) *Free generation of `𝒦_X(ℒ)_ξ` over `Q(𝒪^h_{X,ξ})` by the image of `t_ξ`.* Proved, as
     `AlgebraicGeometry.Space.PrimeDivisor.bijective_smul_toMeromorphicSectionValue`
     (`StacksFrontier/AlgebraicGeometry/Spaces/Decent/GenericMeromorphicStalkFree.lean`): for a
     free generator `t_ξ` of `ℒ_ξ` the map `k ↦ k · t_ξ` is a bijection of
     `𝒦(Spec(𝒪^h_{X,ξ}))` onto `𝒦_X(ℒ)_ξ`. The sheaf half is assembled at
     `Y = Spec(𝒪^h_{X,ξ})` as
     `AlgebraicGeometry.Space.PrimeDivisor.nonempty_uliftUnit_iso_genericMeromorphicSectionSheaf`,
     and the generator the isomorphism produces is compared with `t_ξ` by the nonzerodivisor
     argument above.

     (ii) *Regularity makes the ratio a unit.* Proved, as
     `Space.PrimeDivisor.isUnit_of_smul_toMeromorphicSectionValue_eq_genericMeromorphicGerm`
     (`StacksFrontier/AlgebraicGeometry/Spaces/Decent/GenericSectionRatio.lean`). It does not need
     `AlgebraicGeometry.Space.eq_zero_of_mul_eq_zero_of_eval_eq_tmul`: the pullback of a regular
     section along `c_ξ` is regular by Stacks 0ENC, part (2)
     (`AlgebraicGeometry.Space.isRegularMeromorphicSection_pullbackMeromorphicSection`), the
     germ at `ξ` *is* the value of that pullback over the identity chart, and the free
     generation of step (i) turns the resulting injectivity into `k` being a nonzerodivisor,
     hence a unit by `IsFractionRing.nonZeroDivisors_eq_isUnit`.

     (iii) *The transport across the universe gap.* Proved, as
     `AlgebraicGeometry.Space.PrimeDivisor.exists_ringEquiv_genericTotalFractionRing` in the
     same file: `exists_ringEquiv_genericHenselianLocalRing` above compares the two base rings
     and `IsFractionRing.ringEquivOfRingEquiv` carries the comparison to the fraction rings,
     compatibly with the two structure maps.
     Being existential it yields the isomorphism only up to that
     isomorphism.
     `AlgebraicGeometry.Space.PrimeDivisor.exists_ringEquiv_forall_smul_eq_genericMeromorphicGerm`
     is the three assembled: an isomorphism `ψ` of `𝒦(Spec(𝒪^h_{X,ξ}))` with
     `AlgebraicGeometry.Space.PrimeDivisor.genericTotalFractionRing` together with the map
     `s ↦ ψ(s / t_ξ)` on meromorphic sections, characterised by the equation
     `ψ⁻¹(f s) · t_ξ = germ_ξ(s)` and a *unit* at every regular `s`.

  This is a defect in the reading of Stacks 0EPR itself, not only an obstacle to Stacks 0EPS.
  Stacks 0EPR reads `ord_{Z,ℒ}(s)` off `s / s_ξ` for `s_ξ` an actual *generator of `ℒ_ξ`*,
  determined by `ℒ` and `ξ` up to a unit; `AlgebraicGeometry.Space.LocalRatio` below is instead
  an arbitrary function to the units, and
  `AlgebraicGeometry.Space.orderOfVanishingSection_unit_smul` supplies the right invariance
  without pinning the ratio to `ℒ` at all. **The canonical ratio itself is constructed** —
  items 1, 2, the two halves of item 3 and all three of (i), (ii), (iii) above are proved — and
  `AlgebraicGeometry.Space.PrimeDivisor.exists_ringEquiv_forall_smul_eq_genericMeromorphicGerm`
  is the construction. **`LocalRatio` is nevertheless still the arbitrary function type below,
  and two things stand in the way of cutting it down. The first is a defect in the obvious
  repair and the second is a genuine gap.**

  *The repair cannot be a subtype of the present function type, because that subtype is empty.*
  Cutting `LocalRatio` down to "the ratios that come from a generator" asks the induced map
  `s ↦ germ_ξ(s) / e` to land in the **units** of `Q(𝒪^h_{X,ξ})` for *every* meromorphic
  section `s`. It does not: `MeromorphicSection` is an additive group
  (`AlgebraicGeometry.Space.MeromorphicSection`'s `AddCommGroup` is
  `PresheafOfModules.sectionsAddCommGroup`) and `germ_ξ(0) = 0`, whose ratio against a free
  generator is `0`, not a unit — step (ii) gives a unit exactly at the *regular* sections, which
  is where the source takes `ord_{Z,ℒ}(s)`. So the subtype of the present type has no elements,
  and a wrapper stated over it would make the five tags vacuously true in the opposite
  direction: not `fun _ ↦ 1` inhabiting a type too wide, but an uninhabited hypothesis carried
  by every consumer. A correct repair has to change the *target* of the ratio from
  `(Q(𝒪^h_{X,ξ}))ˣ` to `Q(𝒪^h_{X,ξ})` and add regularity of `s` where unit-ness is used — that
  is, to `AlgebraicGeometry.Space.orderOfVanishingSection` and to the statements below that
  consume `(ratio s).isUnit`. That is faithful to Stacks 0EPR, which defines `ord_{Z,ℒ}(s)` for
  a regular meromorphic section, but it is a change of signature on the 0EPR, 0EPT and 0EPV
  registrations and on all of their consumers, and it is not a subtype of the present type.

  *And the canonicity constraint cannot be stated at the universe `z` that `LocalRatio` carries.*
  What pins the ratio down is the equation `ψ⁻¹(f s) · t_ξ = germ_ξ(s)`, and `germ_ξ` is
  `AlgebraicGeometry.Space.PrimeDivisor.genericMeromorphicGerm`, which exists only for
  `Modules.{u, u}` and `MeromorphicSection.{u, u}`: both the pullback of modules and the global
  pullback of meromorphic sections of Stacks 0ENC are defined at the module universe of the
  structure rings and nowhere else, as the implementation notes of
  `StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorGenericMeromorphicGerm` record. So a
  `LocalRatio` whose `Nonempty` is a theorem from the construction exists at `z = u` only, and
  cutting the type down forces `z := u` on `AlgebraicGeometry.Space.orderOfVanishingSection`,
  `AlgebraicGeometry.Space.divisorCoefficients`, `AlgebraicGeometry.Space.divisorOfSection` and
  on the six modules below that are polymorphic in `z` today
  (`…Spaces.Chow.FlatPullbackOrderOfVanishing`, `…Spaces.Chow.InvertibleSheafDivisor`,
  `…Spaces.Chow.KeyFormulaComponentDivisor`, `…Spaces.Chow.KeyFormulaCycleIdentities`,
  `…Spaces.DivisorOfMeromorphicSectionRatio`, `…Spaces.WeilDivisorClassOfSection`).  That
  narrowing loses nothing the source has — at `z ≠ u` there is no germ, hence no `s / s_ξ`, so
  those instances of the statements are about the arbitrary parameter and nothing else — but it
  does narrow the literal statements, so it is not made here: the universe `z` is kept.

  *The remaining way out would be to generalise the germ instead of narrowing its consumers, and
  it has been examined and does not work.* The obstruction is not a binder on
  `genericMeromorphicGerm` or on `AlgebraicGeometry.Space.pullbackMeromorphicSection`: it is that
  `Stacks.Sheaves.RingedToposModules`, through which
  `AlgebraicGeometry.Space.modulePullback` is defined, **identifies the module universe with the
  ring universe**, so that route returns modules over a lifted structure sheaf rather than
  `Modules.{u, max u z}` whatever is done to the universes of the topos machinery; and
  independently of that, the Stacks 03G1 comparison restriction at `Type (max u z)` is not known
  to be an equivalence, which blocks the *direct* image of modules as well as the inverse one.
  Only the first of these is decisive. The one route that could dissolve the wall goes outside
  the ringed-topos machinery altogether, through Mathlib's module-universe-free
  `SheafOfModules.pullback` along a *site* functor; the full account, with the declarations and
  the upstream binder each step turns on, is in the implementation notes of
  `StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorGenericMeromorphicGerm`, which also
  records what has since been checked about it: the site functor *does* exist
  (`AlgebraicGeometry.Space.smallBaseChange`), the adjointness at a module universe above the
  ring universe is available at presheaf level
  (`PresheafOfModules.isRightAdjoint_pushforward_of_essentiallySmall_univLE`), and what the route is
  actually blocked on is that `c_ξ` is not known to be a relatively *representable* morphism —
  which is what `smallBaseChange` requires, and which does not follow from the source of `c_ξ`
  being representable. Until that route is built, the constraint and the universe cannot both be
  had, and nothing of a partial conversion of `LocalRatio` belongs in the tree: a half-converted
  definition that five tags depend on is worse than the present state.

  *Which registrations the `{u, u}` collapse actually reaches, since the point is easy to
  overstate.* Every registration in this module and its downstream consumers is **already**
  stated at `Modules.{u, max u z}` and `MeromorphicSection.{u, z}`: all four of Stacks 0EPR
  (`orderOfVanishingSection`, `orderOfVanishingSection_eq_length_sub_length`,
  `exists_orderOfVanishingSection_eq_length_sub_length`, `orderOfVanishingSection_unit_smul`),
  both of Stacks 0EPT (`orderOfVanishingSection_eq_add_ord` and, in
  `…Spaces.DivisorOfMeromorphicSectionRatio`, `divisorOfSection_eq_add_principalDivisor`), all
  six of Stacks 0EPU (`divisorCoefficients`, `divisorOfSection`, `divisorOfSectionOfGenerating`
  and, in `…Spaces.WeilDivisorClassOfSection`, `divisorClassOfSection`,
  `divisorClassOfSection_eq`, `divisorClassOfSectionOfGenerating`),
  `locallyFinite_divisorCoefficients_ne_zero` of Stacks 0EPS, and
  `firstChernCapCycleMap_divisorCycleAt_eq_componentDivisorSum_of_isInvertible` of Section 0EQU.
  The collapse reaches **only the statements that mention the germ**, namely the four Stacks
  0EPS registrations under `…Spaces.Decent` —
  `locallyFinite_primeDivisor_not_memGenericModuleStalk_of_isIntegral`,
  `locallyFinite_primeDivisor_not_generatesGenericModuleStalk_of_isIntegral`,
  `locallyFinite_divisorCoefficients_ne_zero_of_isIntegral` and
  `exists_localRatioFamily_locallyFinite_divisorCoefficients_ne_zero` — together with
  `firstChernCapCycleMap_divisorCycleAt_eq_componentDivisorSum` of Section 0EQU. So the wall
  bounds how general the *germ-mediated* form of Stacks 0EPS can be, and nothing else here.

  *The geometry of the second set of Stacks 0EPS is now discharged; what the statements below
  keep is the ratio.* What the second set needs at a prime divisor `Z` whose generic point lies
  in the generating open is `ord_{Z,ℒ}(s) = 0`, that is the ratio being the image of a *unit of
  `𝒪^h_{X,ξ}`* rather than merely a unit of its fraction ring; equivalently, the germ of `s` at
  `ξ` must be the image of a **free generator** of `ℒ_ξ`, not just of some section of it. All of
  that is in the tree. `AlgebraicGeometry.Space.bijective_smul_of_sieve` is the descent of free
  generation — a section of a sheaf of modules whose restrictions along a covering sieve are
  free generators is a free generator, by the sheaf condition for `𝒪_X` and separatedness of the
  module. With it,
  `AlgebraicGeometry.Space.PrimeDivisor.generatesGenericModuleStalk_of_eval_eq_of_mem_range`
  carries the generating open of
  `AlgebraicGeometry.Space.exists_nonempty_generating_chart_eval_eq_toMeromorphicSectionValue`
  to `ξ` with its generation intact, where
  `AlgebraicGeometry.Space.PrimeDivisor.memGenericModuleStalk_of_eval_eq_of_mem_range` carried
  only honesty; and
  `AlgebraicGeometry.Space.locallyFinite_primeDivisor_not_generatesGenericModuleStalk_of_isIntegral`
  is the resulting local finiteness, at the source's hypotheses alone.
  `AlgebraicGeometry.Space.locallyFinite_divisorCoefficients_ne_zero_of_isIntegral` is the
  second set itself, with the quadruple `(U, hUopen, hUne, hgen)` replaced by the single
  hypothesis that `ord_{Z,ℒ}(s)` vanishes where `s` generates `ℒ_ξ`; and
  `AlgebraicGeometry.Space.PrimeDivisor.exists_isUnit_genericToMeromorphicFunctions_eq_of_generates`
  is that hypothesis for the canonical ratio, read in the meromorphic functions of
  `Spec(𝒪^h_{X,ξ})`.

  **That composite is now carried out**, in
  `StacksFrontier/AlgebraicGeometry/Spaces/Decent/GenericSectionRatioOrderZero.lean`:
  `AlgebraicGeometry.Space.orderOfVanishingSection_eq_zero_of_generatesGenericModuleStalk` is
  `hord` at one prime divisor for a `ratio` whose value at `s` is the canonical one, and
  `AlgebraicGeometry.Space.exists_localRatioFamily_locallyFinite_divisorCoefficients_ne_zero`
  is the second set of Stacks 0EPS at the source's hypotheses alone, `hord` being supplied
  there rather than assumed.  The ratio is pinned in the *conclusion* of that statement — it
  asserts a family whose value at `s` is the ratio of `s` against a free generator of `ℒ_ξ` —
  because `LocalRatio` cannot pin it in the type: that clause is what stops `fun _ ↦ 1`
  satisfying the rest vacuously, and carrying it is the price of the type being a bare function
  type.  What is still left is exactly the signature change: with `ratio` an unconstrained
  parameter nothing identifies `ratio s` with the canonical ratio *in the statements below*, so
  neither the `hgen` of those statements nor the `hfin`, `hfin'` of Stacks 0EPT and Stacks
  0EPU, part (2) can be dropped from them.

  **In particular the move that discharged the carried `t_W` of Stacks 0EQU does
  not transfer here, and the reason is worth recording.** There, the carried object occurred on
  both sides of the identity, so the identity held for any one of them and discharging the carry
  reduced to producing *some* regular meromorphic section, which Stacks 0EPQ
  (`AlgebraicGeometry.Space.exists_isRegularMeromorphicSection_of_isTrivialAtCodimensionZeroPoints`)
  does. For `LocalRatio` the analogous production is worthless: the type is a bare function type
  into a group of units, so `fun _ ↦ 1` is an element of it and `Nonempty` is trivially true.
  That triviality is the defect, not a step towards curing it, and it is why the type has to be
  cut down rather than inhabited.

  The both-sides observation is nevertheless true of two of the statements below, and it says
  something precise about them. In
  `AlgebraicGeometry.Space.divisorOfSection_eq_add_principalDivisor` (Stacks 0EPT) and in
  `AlgebraicGeometry.Space.divisorClassOfSection_eq` (Stacks 0EPU, part (2)) one `ratio` family
  is universally quantified and used on *both* sides of the identity, so the ratio parameter is
  not itself a weakening there — the identity is proved for every choice. What those two carry
  that the observation does not reach is, in each case, two further things: the pair
  `(f, hs)`, which is the source's assertion that `f = s/s'` lies in `R(X)^*` turned into a
  hypothesis — `f` occurs on one side only, and with an unconstrained ratio nothing produces it
  — and `hfin`, `hfin'`, which is the second set of Stacks 0EPS and needs `ord` to be a function
  of `(ℒ, s)`. Both of those need the repair. For the *definition* tags — Stacks 0EPR,
  `AlgebraicGeometry.Space.divisorCoefficients` and `AlgebraicGeometry.Space.divisorOfSection`
  of Stacks 0EPU part (1), and `AlgebraicGeometry.Space.divisorClassOfSection` of part (2) — no
  both-sides argument applies at all: their *value* depends on the parameter, so they denote a
  different object for each choice of it.

  The first sentence of the proof of Stacks 0EPS would then also have to be
  strengthened: the chart that
  `AlgebraicGeometry.Space.exists_nonempty_chart_eval_eq_toMeromorphicSectionValue` produces
  carries `s` as an honest section `r • e`, with `e` a generator and `r` the numerator of a
  fraction over an affine chart, and `r` is *not* asserted to be a unit — so `s` is not there
  asserted to generate `ℒ`, which is what makes `ord_{Z,ℒ}(s) = 0` at the generic points in its
  image. Until all of that, the parameter stands, and every attribute taking a `ratio` or
  `LocalRatioFamily` argument — Stacks 0EPR, 0EPS, 0EPT, 0EPU, 0EPV and 0EQU — discloses it in
  its note.

## References

* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EPS](https://stacks.math.columbia.edu/tag/0EPS)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
* [Stacks Project, Tag 0EPU](https://stacks.math.columbia.edu/tag/0EPU)
* [Stacks Project, Tag 0EPV](https://stacks.math.columbia.edu/tag/0EPV)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u z

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)

/-! ### Local finiteness of the prime divisors avoiding a nonempty open -/

/-- A point of codimension one outside a nonempty open subset of an irreducible space has, in
the closed complement of that open set, a closure which is a maximal irreducible subset.

A strictly larger irreducible closed subset of the complement would, together with the whole
space, exhibit a chain of length two above the closure of the point. -/
private theorem maximal_isIrreducible_closure_singleton {α : Type*} [TopologicalSpace α]
    [IrreducibleSpace α] {U : Set α} (hUopen : IsOpen U) (hUne : U.Nonempty) {ξ : α}
    (hξ : ξ ∈ Uᶜ) (hcod : codimension (IrreducibleCloseds.closureSingleton ξ) = 1) :
    Maximal IsIrreducible (closure ({⟨ξ, hξ⟩} : Set ↥(Uᶜ : Set α))) := by
  have hemb : Topology.IsClosedEmbedding ((↑) : ↥(Uᶜ : Set α) → α) :=
    hUopen.isClosed_compl.isClosedEmbedding_subtypeVal
  refine ⟨isIrreducible_singleton.closure, fun C hC hsub ↦ ?_⟩
  set C' : Set α := ((↑) : ↥(Uᶜ : Set α) → α) '' closure C with hC'def
  have hC'irr : IsIrreducible C' := hC.closure.image _ continuous_subtype_val.continuousOn
  have hC'closed : IsClosed C' := hemb.isClosedMap _ isClosed_closure
  have hC'sub : C' ⊆ Uᶜ := by rintro _ ⟨c, _, rfl⟩; exact c.2
  have hWimg : ((↑) : ↥(Uᶜ : Set α) → α) '' closure ({⟨ξ, hξ⟩} : Set ↥(Uᶜ : Set α)) =
      closure {ξ} := by
    rw [← hemb.closure_image_eq, Set.image_singleton]
  have hle : closure {ξ} ⊆ C' := by
    rw [← hWimg]
    exact Set.image_mono (hsub.trans subset_closure)
  have heq : closure {ξ} = C' := by
    by_contra hne
    set Y : IrreducibleCloseds α := IrreducibleCloseds.closureSingleton ξ with hYdef
    set Cc : IrreducibleCloseds α := ⟨C', hC'irr, hC'closed⟩ with hCcdef
    set Tp : IrreducibleCloseds α :=
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ α, isClosed_univ⟩ with hTpdef
    have hYc : (Y : Set α) = closure {ξ} := IrreducibleCloseds.coe_closureSingleton ξ
    have hYC : Y < Cc := by
      refine lt_of_le_of_ne ?_ fun h ↦ hne ?_
      · rw [← SetLike.coe_subset_coe, hYc]
        exact hle
      · rw [← hYc]
        exact congrArg (fun W : IrreducibleCloseds α ↦ (W : Set α)) h
    have hCT : Cc < Tp := by
      refine lt_of_le_of_ne (by rw [← SetLike.coe_subset_coe]; exact Set.subset_univ _)
        fun h ↦ ?_
      obtain ⟨y, hy⟩ := hUne
      have hC'univ : C' = Set.univ :=
        congrArg (fun W : IrreducibleCloseds α ↦ (W : Set α)) h
      exact hC'sub (by rw [hC'univ]; trivial) hy
    have hcoY : Order.coheight Y = 1 := by rw [← codimension_eq_coheight]; exact hcod
    have h1 : Order.coheight Cc + 1 ≤ Order.coheight Y := Order.coheight_add_one_le hYC
    rw [hcoY] at h1
    have h3 : (1 : ℕ∞) ≤ Order.coheight Cc :=
      le_trans (le_add_self : (1 : ℕ∞) ≤ Order.coheight Tp + 1) (Order.coheight_add_one_le hCT)
    have h4 : (2 : ℕ∞) ≤ 1 := by
      calc (2 : ℕ∞) = 1 + 1 := by norm_num
        _ ≤ Order.coheight Cc + 1 := by gcongr
        _ ≤ 1 := h1
    norm_num at h4
  have hind : Topology.IsInducing ((↑) : ↥(Uᶜ : Set α) → α) := hemb.isInducing
  have e1 : closure C = ((↑) : ↥(Uᶜ : Set α) → α) ⁻¹' C' := by
    conv_lhs => rw [← closure_closure]
    rw [hind.closure_eq_preimage_closure_image (closure C), ← hC'def, hC'closed.closure_eq]
  have e2 : closure ({⟨ξ, hξ⟩} : Set ↥(Uᶜ : Set α)) = ((↑) : ↥(Uᶜ : Set α) → α) ⁻¹' C' := by
    rw [hind.closure_eq_preimage_closure_image, Set.image_singleton]
    exact congrArg _ heq
  exact subset_closure.trans (e1.trans e2.symm).subset

/-- A prime divisor is determined by its underlying subspace. -/
theorem PrimeDivisor.eq_of_subspace_eq {Z W : PrimeDivisor B S hS X}
    (h : Z.subspace = W.subspace) :
    Z = W := by
  obtain ⟨zs, zc, zi, zd⟩ := Z
  obtain ⟨ws, wc, wi, wd⟩ := W
  subst h
  rfl

include hX in
/-- A prime divisor is determined by its set of points. -/
private theorem PrimeDivisor.ext_support {Z W : PrimeDivisor B S hS X}
    (h : Z.support B S hS X = W.support B S hS X) : Z = W := by
  have hICS : (⟨Z.subspace, Z.closed, Z.integral⟩ : IntegralClosedSubspace B S hS X) =
      ⟨W.subspace, W.closed, W.integral⟩ :=
    injective_integralClosedSubspaceSupport B S hS hX (IrreducibleCloseds.ext (by exact h))
  exact PrimeDivisor.eq_of_subspace_eq B S hS (congrArg IntegralClosedSubspace.subspace hICS)

include hX in
/-- **The Stacks 0EE5 step in the proof of Stacks 0EPS.** Any collection of prime divisors of a
locally Noetherian integral algebraic space whose generic points all avoid one nonempty open
subset of `|X|` is locally finite in `|X|`.

Such a prime divisor is an irreducible component of `|X| ∖ U`, because a strictly larger
irreducible closed subset of `|X| ∖ U` would make its codimension at least two, and the
irreducible components of a closed subset are locally finite by Stacks 0EE5.

This is the second and third sentences of the proof of Stacks 0EPS, in the generality that
covers both of that lemma's sets at once, and it is the same step the proofs of Stacks 0ENN and
Stacks 0EQU take. **It does not on its own prove Stacks 0EPS**: the nonempty open subset `U` is
a hypothesis here, while Stacks 0EPS asserts local finiteness from regularity of the
meromorphic section alone — its proof's first sentence, that `s` generates `ℒ` over some
nonempty open subspace, is what produces `U`, and the attribute note below records that this
statement carries it. Discharging `U` is the open part of Stacks 0EPS; the implementation notes
of this module say exactly what is missing for each of the lemma's two sets. -/
@[stacks 0EPS "both sets: prime divisors whose generic points avoid a nonempty open"]
theorem locallyFinite_primeDivisor_of_genericPoint_notMem
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))
    (hirr : IrreducibleSpace (points B S hS X)) (P : PrimeDivisor B S hS X → Prop)
    [DecidablePred P]
    (U : Set (points B S hS X)) (hUopen : IsOpen U) (hUne : U.Nonempty)
    (hP : ∀ Z : PrimeDivisor B S hS X, P Z → Z.genericPoint B S hS X ∈ Uᶜ) :
    LocallyFinite fun Z : PrimeDivisor B S hS X ↦ if P Z then Z.support B S hS X else ∅ := by
  have := hirr
  have hTclosed : IsClosed (Uᶜ : Set (points B S hS X)) := hUopen.isClosed_compl
  have hemb : Topology.IsClosedEmbedding
      ((↑) : ↥(Uᶜ : Set (points B S hS X)) → points B S hS X) :=
    hTclosed.isClosedEmbedding_subtypeVal
  have hsupp : ∀ Z : PrimeDivisor B S hS X,
      closure {Z.genericPoint B S hS X} = Z.support B S hS X :=
    fun Z ↦ Z.isGenericPoint_genericPoint B S hS X
  have hsub : ∀ Z : PrimeDivisor B S hS X, P Z →
      Z.support B S hS X ⊆ (Uᶜ : Set (points B S hS X)) := by
    intro Z hZ
    rw [← hsupp Z]
    exact hTclosed.closure_subset_iff.2 (Set.singleton_subset_iff.2 (hP Z hZ))
  set F : PrimeDivisor B S hS X → Set ↥(Uᶜ : Set (points B S hS X)) :=
    fun Z ↦ ((↑) : ↥(Uᶜ : Set (points B S hS X)) → points B S hS X) ⁻¹' Z.support B S hS X
    with hFdef
  have hFimg : ∀ Z : PrimeDivisor B S hS X, P Z →
      ((↑) : ↥(Uᶜ : Set (points B S hS X)) → points B S hS X) '' F Z = Z.support B S hS X :=
    fun Z hZ ↦ Set.image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact hsub Z hZ)
  have hFmem : ∀ Z : PrimeDivisor B S hS X, P Z →
      F Z ∈ irreducibleComponents ↥(Uᶜ : Set (points B S hS X)) := by
    intro Z hZ
    have hcl : F Z = closure ({⟨Z.genericPoint B S hS X, hP Z hZ⟩} :
        Set ↥(Uᶜ : Set (points B S hS X))) := by
      rw [hemb.isInducing.closure_eq_preimage_closure_image, Set.image_singleton, hFdef]
      exact congrArg _ (hsupp Z).symm
    rw [hcl]
    exact maximal_isIrreducible_closure_singleton hUopen hUne _
      (Z.codimension_genericPoint B S hS X)
  intro x
  obtain ⟨V, hVnhds, hVfin⟩ :=
    locallyFinite_irreducibleComponents_of_isClosed B S hS X hX hN _ hTclosed x
  refine ⟨V, hVnhds, ?_⟩
  have key : ∀ Z : PrimeDivisor B S hS X,
      (((if P Z then Z.support B S hS X else ∅)) ∩ V).Nonempty → P Z := by
    intro Z hZ
    by_contra h
    simp [h] at hZ
  refine Set.Finite.of_finite_image (f := F) ?_ ?_
  · refine Set.Finite.subset (hVfin.image
      (fun C : irreducibleComponents ↥(Uᶜ : Set (points B S hS X)) ↦
        (C : Set ↥(Uᶜ : Set (points B S hS X))))) ?_
    rintro _ ⟨Z, hZ, rfl⟩
    refine ⟨⟨F Z, hFmem Z (key Z hZ)⟩, ?_, rfl⟩
    change (((↑) : ↥(Uᶜ : Set (points B S hS X)) → points B S hS X) '' F Z ∩ V).Nonempty
    rw [hFimg Z (key Z hZ)]
    simpa [key Z hZ] using hZ
  · intro Z hZ W hW h
    refine PrimeDivisor.ext_support B S hS hX ?_
    rw [← hFimg Z (key Z hZ), ← hFimg W (key W hW), h]

/-! ### The order of vanishing of a meromorphic section -/

variable (hdec : IsDecentSpace B S hS X)
variable [∀ W : PrimeDivisor B S hS X,
  Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hdec)]
variable [∀ W : PrimeDivisor B S hS X,
  IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hdec)]
variable [∀ W : PrimeDivisor B S hS X,
  Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hdec)]
variable (Z : PrimeDivisor B S hS X)

/-- A choice of generator of `ℒ` at the generic point of a prime divisor `Z`, read off as the
ratio `s ↦ s / s_ξ` in the units of `Q(𝒪^h_{X,ξ})` that it assigns to a meromorphic section of
`ℒ`. The ratio is a unit because the meromorphic section is regular. -/
abbrev LocalRatio (L : Modules.{u, max u z} B S hS X hX) : Type (max (u + 1) z) :=
  MeromorphicSection.{u, z} B S hS X hX L → (Z.genericTotalFractionRing B S hS hX hdec)ˣ

/-- **Stacks 0EPR.** The *order of vanishing of a meromorphic section `s` of `ℒ` along `Z`*:
the order of vanishing of the ratio `s / s_ξ` in `Q(𝒪^h_{X,ξ})`, that is the difference
`length (𝒪^h_{X,ξ} ⧸ a) - length (𝒪^h_{X,ξ} ⧸ b)` for `s / s_ξ = a / b` with `a` and `b`
nonzerodivisors. -/
@[stacks 0EPR "ord_{Z,ℒ}(s), in the general form that takes the ratio s/s_ξ as data, so that it \
is available for an arbitrary module over an arbitrary space. The tag's own definition is at the \
CONSTRUCTED ratio: PrimeDivisor.canonicalLocalRatio and canonicalLocalRatioFamily of \
StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorCanonicalRatio build s/s_ξ for an \
invertible module on a locally Noetherian integral algebraic space and carry no parameter"]
def orderOfVanishingSection (L : Modules.{u, max u z} B S hS X hX)
    (s : MeromorphicSection.{u, z} B S hS X hX L)
    (ratio : LocalRatio.{u, z} B S hS hX hdec Z L) : ℤ :=
  Z.ord B S hS hX hdec (ratio s : Z.genericTotalFractionRing B S hS hX hdec) (ratio s).isUnit

/-- `ord_{Z,ℒ}(s)` is the order of vanishing of any unit equal to the ratio `s / s_ξ`. -/
private theorem orderOfVanishingSection_eq_ord (L : Modules.{u, max u z} B S hS X hX)
    (s : MeromorphicSection.{u, z} B S hS X hX L)
    (ratio : LocalRatio.{u, z} B S hS hX hdec Z L)
    {x : Z.genericTotalFractionRing B S hS hX hdec} (hx : IsUnit x)
    (h : (ratio s : Z.genericTotalFractionRing B S hS hX hdec) = x) :
    orderOfVanishingSection.{u, z} B S hS hX hdec Z L s ratio = Z.ord B S hS hX hdec x hx :=
  PrimeDivisor.ord_congr B S hS hX hdec Z _ hx h

/-- The image in `Q(𝒪^h_{X,ξ})` of a unit of `𝒪^h_{X,ξ}` has order of vanishing zero. -/
private theorem ord_algebraMap_of_isUnit
    {v : ↥(Z.genericHenselianLocalRing B S hS hX hdec)} (hv : IsUnit v)
    (hvu : IsUnit (algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hdec)
      (Z.genericTotalFractionRing B S hS hX hdec) v)) :
    Z.ord B S hS hX hdec _ hvu = 0 := by
  rw [Z.ord_algebraMap B S hS hX hdec v hv.mem_nonZeroDivisors, Ring.ord_of_isUnit hv]
  simp

/-- **Stacks 0EPR.** If the ratio `s / s_ξ` is `a / b` with `a` and `b` nonzerodivisors of
`𝒪^h_{X,ξ}`, then `ord_{Z,ℒ}(s)` is the difference of the lengths of the quotients of
`𝒪^h_{X,ξ}` by `a` and by `b`. In particular it does not depend on the presentation. -/
@[stacks 0EPR "the length formula on any presentation, hence independence of the presentation"]
theorem orderOfVanishingSection_eq_length_sub_length (L : Modules.{u, max u z} B S hS X hX)
    (s : MeromorphicSection.{u, z} B S hS X hX L)
    (ratio : LocalRatio.{u, z} B S hS hX hdec Z L)
    (a b : nonZeroDivisors ↥(Z.genericHenselianLocalRing B S hS hX hdec))
    (hab : (ratio s : Z.genericTotalFractionRing B S hS hX hdec) =
      IsLocalization.mk' (Z.genericTotalFractionRing B S hS hX hdec)
        (a : ↥(Z.genericHenselianLocalRing B S hS hX hdec)) b) :
    orderOfVanishingSection.{u, z} B S hS hX hdec Z L s ratio =
      ((Ring.ord ↥(Z.genericHenselianLocalRing B S hS hX hdec)
          (a : ↥(Z.genericHenselianLocalRing B S hS hX hdec))).toNat : ℤ) -
        ((Ring.ord ↥(Z.genericHenselianLocalRing B S hS hX hdec)
          (b : ↥(Z.genericHenselianLocalRing B S hS hX hdec))).toNat : ℤ) := by
  have hu : IsUnit (IsLocalization.mk' (Z.genericTotalFractionRing B S hS hX hdec)
      (a : ↥(Z.genericHenselianLocalRing B S hS hX hdec)) b) := hab ▸ (ratio s).isUnit
  rw [orderOfVanishingSection_eq_ord B S hS hX hdec Z L s ratio hu hab]
  exact Z.ord_mk' B S hS hX hdec a b hu

/-- A unit of a total ring of fractions `K` of a commutative ring `R` is a fraction `a / b` of
nonzerodivisors of `R`.

Every element of `K` is `a / b` with `b` a nonzerodivisor, by the localization. If moreover the
element is a unit then so is the image of `a`, because that image is the product of the element
with the image of `b`; and a nonzerodivisor of `K` whose preimage is taken along the injective
localization map comes from a nonzerodivisor of `R`. -/
private theorem exists_mk'_nonZeroDivisors_of_isUnit {R : Type*} [CommRing R] {K : Type*}
    [CommRing K] [Algebra R K] [IsFractionRing R K] {x : K} (hx : IsUnit x) :
    ∃ a b : nonZeroDivisors R, x = IsLocalization.mk' K (a : R) b := by
  set b : nonZeroDivisors R := (IsLocalization.sec (nonZeroDivisors R) x).2
  set a : R := (IsLocalization.sec (nonZeroDivisors R) x).1
  have hab : IsLocalization.mk' K a b = x := IsLocalization.mk'_sec K x
  have hspec : IsLocalization.mk' K a b * algebraMap R K (b : R) = algebraMap R K a :=
    IsLocalization.mk'_spec K a b
  have hu : IsUnit (algebraMap R K a) := by
    rw [← hspec, hab]
    exact hx.mul (IsLocalization.map_units K b)
  exact ⟨⟨a, mem_nonZeroDivisors_of_injective (IsFractionRing.injective R K)
    hu.mem_nonZeroDivisors⟩, b, hab.symm⟩

/-- **Stacks 0EPR, well-definedness.** The ratio `s / s_ξ` *is* a fraction `a / b` of
nonzerodivisors of `𝒪^h_{X,ξ}`, and for one — hence, by
`AlgebraicGeometry.Space.orderOfVanishingSection_eq_length_sub_length`, for every — such
presentation `ord_{Z,ℒ}(s)` is the difference
`length (𝒪^h_{X,ξ} ⧸ a) - length (𝒪^h_{X,ξ} ⧸ b)`.

This is the clause of the source's definition that fixes the integer: Definition 72.7.1 reads
`ord_{Z,ℒ}(s)` off nonzerodivisors `a, b` of `𝒪^h_{X,ξ}` *such that* `s / s_ξ = a / b`, so the
existence of such a pair is what makes the difference of lengths an admissible description of
`ord_{Z,ℒ}(s)` at all. Regularity of the meromorphic section — carried, as throughout this
module, by `ratio s` being a *unit* of `Q(𝒪^h_{X,ξ})` — is exactly what produces it: the
numerator of an arbitrary presentation of a unit is again a nonzerodivisor. -/
@[stacks 0EPR "existence of the presentation s/s_ξ = a/b by nonzerodivisors, with the length
  formula; the ratio s/s_ξ is the parameter `ratio`"]
theorem exists_orderOfVanishingSection_eq_length_sub_length
    (L : Modules.{u, max u z} B S hS X hX)
    (s : MeromorphicSection.{u, z} B S hS X hX L)
    (ratio : LocalRatio.{u, z} B S hS hX hdec Z L) :
    ∃ a b : nonZeroDivisors ↥(Z.genericHenselianLocalRing B S hS hX hdec),
      (ratio s : Z.genericTotalFractionRing B S hS hX hdec) =
          IsLocalization.mk' (Z.genericTotalFractionRing B S hS hX hdec)
            (a : ↥(Z.genericHenselianLocalRing B S hS hX hdec)) b ∧
        orderOfVanishingSection.{u, z} B S hS hX hdec Z L s ratio =
          ((Ring.ord ↥(Z.genericHenselianLocalRing B S hS hX hdec)
              (a : ↥(Z.genericHenselianLocalRing B S hS hX hdec))).toNat : ℤ) -
            ((Ring.ord ↥(Z.genericHenselianLocalRing B S hS hX hdec)
              (b : ↥(Z.genericHenselianLocalRing B S hS hX hdec))).toNat : ℤ) := by
  obtain ⟨a, b, hab⟩ := exists_mk'_nonZeroDivisors_of_isUnit
    (R := ↥(Z.genericHenselianLocalRing B S hS hX hdec)) (ratio s).isUnit
  exact ⟨a, b, hab,
    orderOfVanishingSection_eq_length_sub_length.{u, z} B S hS hX hdec Z L s ratio a b hab⟩

/-- The order of vanishing of `s` along `Z` is zero as soon as the ratio `s / s_ξ` is the image
of a unit of `𝒪^h_{X,ξ}`, which is the case when `s` generates `ℒ` at the generic point of `Z`.

Read contrapositively this is the step in the proof of Stacks 0EPS, and in the proof of Stacks
0EQU, that locates the prime divisors with `ord_{Z,ℒ}(s) ≠ 0` inside the complement of the open
subspace over which `s` generates `ℒ`: there the ratio is a unit of the local ring itself, whose
order of vanishing vanishes. -/
theorem orderOfVanishingSection_eq_zero_of_isUnit (L : Modules.{u, max u z} B S hS X hX)
    (s : MeromorphicSection.{u, z} B S hS X hX L)
    (ratio : LocalRatio.{u, z} B S hS hX hdec Z L)
    {v : ↥(Z.genericHenselianLocalRing B S hS hX hdec)} (hv : IsUnit v)
    (hvr : (ratio s : Z.genericTotalFractionRing B S hS hX hdec) =
      algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hdec)
        (Z.genericTotalFractionRing B S hS hX hdec) v) :
    orderOfVanishingSection.{u, z} B S hS hX hdec Z L s ratio = 0 := by
  have hvu : IsUnit (algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hdec)
      (Z.genericTotalFractionRing B S hS hX hdec) v) :=
    IsLocalization.map_units _ ⟨v, hv.mem_nonZeroDivisors⟩
  rw [orderOfVanishingSection_eq_ord B S hS hX hdec Z L s ratio hvu hvr,
    ord_algebraMap_of_isUnit B S hS hX hdec Z hv]

/-- **Stacks 0EPR, well-definedness.** Replacing the generator `s_ξ` of `ℒ` at the generic
point of `Z` by `u · s_ξ` for a unit `u` of `𝒪^h_{X,ξ}` replaces the ratio `s / s_ξ` by
`u · (s / s_ξ)` and does not change `ord_{Z,ℒ}(s)`. -/
@[stacks 0EPR "independence of the choice of the generator s_ξ"]
theorem orderOfVanishingSection_unit_smul (L : Modules.{u, max u z} B S hS X hX)
    (s : MeromorphicSection.{u, z} B S hS X hX L)
    (ratio ratio' : LocalRatio.{u, z} B S hS hX hdec Z L)
    {v : ↥(Z.genericHenselianLocalRing B S hS hX hdec)} (hv : IsUnit v)
    (hvr : (ratio' s : Z.genericTotalFractionRing B S hS hX hdec) =
      algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hdec)
        (Z.genericTotalFractionRing B S hS hX hdec) v *
      (ratio s : Z.genericTotalFractionRing B S hS hX hdec)) :
    orderOfVanishingSection.{u, z} B S hS hX hdec Z L s ratio' =
      orderOfVanishingSection.{u, z} B S hS hX hdec Z L s ratio := by
  have hvu : IsUnit (algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hdec)
      (Z.genericTotalFractionRing B S hS hX hdec) v) :=
    IsLocalization.map_units _ ⟨v, hv.mem_nonZeroDivisors⟩
  rw [orderOfVanishingSection_eq_ord B S hS hX hdec Z L s ratio' (hvu.mul (ratio s).isUnit) hvr,
    Z.ord_mul B S hS hX hdec _ _ hvu (ratio s).isUnit, ord_algebraMap_of_isUnit B S hS hX hdec Z hv,
    zero_add]
  rfl

/-- **Stacks 0EPT, coefficientwise.** If `s` and `s'` are meromorphic sections of `ℒ` whose
ratios at the generic point of `Z` differ by the image of a rational function `f`, then
`ord_{Z,ℒ}(s) = ord_{Z,ℒ}(s') + ord_Z(f)`. Summing over all prime divisors this is the
identity `div_ℒ(s) = div_ℒ(s') + div(f)` of Weil divisors.

That such an `f` exists — the first assertion of Stacks 0EPT — is the argument `hs` here, and is
proved at the canonical ratio of Stacks 0EPR by
`AlgebraicGeometry.Space.exists_units_orderOfVanishingSection_canonicalLocalRatio_eq_add_ord`,
which produces `f` rather than taking it. -/
@[stacks 0EPT "div_ℒ(s) = div_ℒ(s') + div(f) coefficientwise; f = s/s' is the argument `hs`,
  discharged at the canonical ratio of Stacks 0EPR by
  exists_units_orderOfVanishingSection_canonicalLocalRatio_eq_add_ord, which produces f"]
theorem orderOfVanishingSection_eq_add_ord (L : Modules.{u, max u z} B S hS X hX)
    (s s' : MeromorphicSection.{u, z} B S hS X hX L)
    (ratio : LocalRatio.{u, z} B S hS hX hdec Z L)
    (emb : rationalFunctions B S hS hX →+* Z.genericTotalFractionRing B S hS hX hdec)
    (f : rationalFunctions B S hS hX) (hf : IsUnit (emb f))
    (hs : (ratio s : Z.genericTotalFractionRing B S hS hX hdec) =
      emb f * (ratio s' : Z.genericTotalFractionRing B S hS hX hdec)) :
    orderOfVanishingSection.{u, z} B S hS hX hdec Z L s ratio =
      orderOfVanishingSection.{u, z} B S hS hX hdec Z L s' ratio +
        Z.ord B S hS hX hdec (emb f) hf := by
  rw [orderOfVanishingSection_eq_ord B S hS hX hdec Z L s ratio (hf.mul (ratio s').isUnit) hs,
    Z.ord_mul B S hS hX hdec _ _ hf (ratio s').isUnit, add_comm]
  rfl

/-- **Stacks 0EPV, coefficientwise.** If the ratio of `st` at the generic point of `Z` is the
product of the ratios of `s` and of `t`, then
`ord_{Z,ℒ⊗𝒩}(st) = ord_{Z,ℒ}(s) + ord_{Z,𝒩}(t)`. Summing over all prime divisors this is the
identity `div_{ℒ⊗𝒩}(st) = div_ℒ(s) + div_𝒩(t)` of Weil divisors. -/
@[stacks 0EPV "div_{ℒ⊗𝒩}(st) = div_ℒ(s) + div_𝒩(t) coefficientwise; ℒ⊗𝒩 is the module `M`"]
theorem orderOfVanishingSection_mul (L N M : Modules.{u, max u z} B S hS X hX)
    (s : MeromorphicSection.{u, z} B S hS X hX L)
    (t : MeromorphicSection.{u, z} B S hS X hX N)
    (st : MeromorphicSection.{u, z} B S hS X hX M)
    (ratioL : LocalRatio.{u, z} B S hS hX hdec Z L)
    (ratioN : LocalRatio.{u, z} B S hS hX hdec Z N)
    (ratioM : LocalRatio.{u, z} B S hS hX hdec Z M)
    (hst : (ratioM st : Z.genericTotalFractionRing B S hS hX hdec) =
      (ratioL s : Z.genericTotalFractionRing B S hS hX hdec) *
        (ratioN t : Z.genericTotalFractionRing B S hS hX hdec)) :
    orderOfVanishingSection.{u, z} B S hS hX hdec Z M st ratioM =
      orderOfVanishingSection.{u, z} B S hS hX hdec Z L s ratioL +
        orderOfVanishingSection.{u, z} B S hS hX hdec Z N t ratioN := by
  rw [orderOfVanishingSection_eq_ord B S hS hX hdec Z M st ratioM
      ((ratioL s).isUnit.mul (ratioN t).isUnit) hst,
    Z.ord_mul B S hS hX hdec _ _ (ratioL s).isUnit (ratioN t).isUnit]
  rfl

/-! ### The Weil divisor of a meromorphic section -/

/-- A choice of generator of `ℒ` at the generic point of every prime divisor of `X`, read off
as the family of ratios `s ↦ s / s_ξ` that it assigns to a meromorphic section of `ℒ`. -/
abbrev LocalRatioFamily (L : Modules.{u, max u z} B S hS X hX) : Type (max (u + 1) z) :=
  ∀ W : PrimeDivisor B S hS X, LocalRatio.{u, z} B S hS hX hdec W L

/-- **Stacks 0EPU, part (1).** The coefficients of the *Weil divisor associated to a
meromorphic section `s` of `ℒ`*: the coefficient at a prime divisor `Z` is `ord_{Z,ℒ}(s)`. -/
@[stacks 0EPU "part (1): the coefficients ord_{Z,ℒ}(s) of div_ℒ(s)"]
def divisorCoefficients (L : Modules.{u, max u z} B S hS X hX)
    (s : MeromorphicSection.{u, z} B S hS X hX L)
    (ratio : LocalRatioFamily.{u, z} B S hS hX hdec L) : PrimeDivisor B S hS X → ℤ :=
  fun W ↦ orderOfVanishingSection.{u, z} B S hS hX hdec W L s (ratio W)

/-- **Stacks 0EPU, part (1).** The *Weil divisor associated to a meromorphic section `s` of
`ℒ`*, that is `div_ℒ(s) = ∑ ord_{Z,ℒ}(s) [Z]` in `Div(X)`. The prime divisors with nonzero
coefficient are locally finite by Stacks 0EPS, which is the hypothesis `hfin`. -/
@[stacks 0EPU "part (1): div_ℒ(s) = ∑ ord_{Z,ℒ}(s) [Z] as an element of Div(X)"]
def divisorOfSection (L : Modules.{u, max u z} B S hS X hX)
    (s : MeromorphicSection.{u, z} B S hS X hX L)
    (ratio : LocalRatioFamily.{u, z} B S hS hX hdec L)
    (hfin : LocallyFinite fun W : PrimeDivisor B S hS X ↦
      if divisorCoefficients.{u, z} B S hS hX hdec L s ratio W = 0 then ∅
      else W.support B S hS X) :
    WeilDivisor B S hS X :=
  ⟨divisorCoefficients.{u, z} B S hS hX hdec L s ratio, hfin⟩

/-- The coefficient of `div_ℒ(s)` at a prime divisor `Z` is `ord_{Z,ℒ}(s)`. -/
@[simp]
theorem coe_divisorOfSection (L : Modules.{u, max u z} B S hS X hX)
    (s : MeromorphicSection.{u, z} B S hS X hX L)
    (ratio : LocalRatioFamily.{u, z} B S hS hX hdec L)
    (hfin : LocallyFinite fun W : PrimeDivisor B S hS X ↦
      if divisorCoefficients.{u, z} B S hS hX hdec L s ratio W = 0 then ∅
      else W.support B S hS X) :
    (divisorOfSection.{u, z} B S hS hX hdec L s ratio hfin : PrimeDivisor B S hS X → ℤ) Z =
      orderOfVanishingSection.{u, z} B S hS hX hdec Z L s (ratio Z) :=
  rfl

include hX in
/-- **The Stacks 0EE5 step in the proof of Stacks 0EPS, for its second set.** The prime divisors
at which `ord_{Z,ℒ}(s)` is nonzero are locally finite in `|X|`, given a nonempty open subset of
`|X|` containing the generic point of no such prime divisor — which in the source is the open
subspace over which the regular meromorphic section `s` generates `ℒ`.

This is `AlgebraicGeometry.Space.locallyFinite_primeDivisor_of_genericPoint_notMem` specialized
to the predicate `ord_{Z,ℒ}(s) ≠ 0`. Like it, it **carries the hypothesis `hgen` that Stacks
0EPS proves rather than assumes**, which the attribute note records. For this set `hgen` cannot
even be dropped: the order of vanishing is taken against the arbitrary parameter `ratio`, so
the set of prime divisors with nonzero coefficient is not determined by `ℒ` and `s`, and
without `hgen` the statement is false. See the implementation notes of this module. -/
@[stacks 0EPS "the second set: the prime divisors with ord_{Z,ℒ}(s) ≠ 0 are locally finite"]
theorem locallyFinite_divisorCoefficients_ne_zero
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))
    (hirr : IrreducibleSpace (points B S hS X)) (L : Modules.{u, max u z} B S hS X hX)
    (s : MeromorphicSection.{u, z} B S hS X hX L)
    (ratio : LocalRatioFamily.{u, z} B S hS hX hdec L)
    (U : Set (points B S hS X)) (hUopen : IsOpen U) (hUne : U.Nonempty)
    (hgen : ∀ W : PrimeDivisor B S hS X,
      divisorCoefficients.{u, z} B S hS hX hdec L s ratio W ≠ 0 →
        W.genericPoint B S hS X ∈ Uᶜ) :
    LocallyFinite fun W : PrimeDivisor B S hS X ↦
      if divisorCoefficients.{u, z} B S hS hX hdec L s ratio W = 0 then ∅
      else W.support B S hS X := by
  have h := locallyFinite_primeDivisor_of_genericPoint_notMem B S hS hX hN hirr
    (fun W ↦ divisorCoefficients.{u, z} B S hS hX hdec L s ratio W ≠ 0) U hUopen hUne hgen
  refine h.subset fun W ↦ ?_
  by_cases hW : divisorCoefficients.{u, z} B S hS hX hdec L s ratio W = 0 <;> simp [hW]

include hX in
/-- **Stacks 0EPU, part (1).** The Weil divisor `div_ℒ(s) = ∑ ord_{Z,ℒ}(s) [Z]` of a
meromorphic section `s` of `ℒ`, with the local finiteness of its support supplied by
`AlgebraicGeometry.Space.locallyFinite_divisorCoefficients_ne_zero` from a nonempty open subset
of `|X|` whose complement carries the generic point of every prime divisor with nonzero
coefficient — in the source, the open subspace over which `s` generates `ℒ`. That open subset
is a hypothesis: the first sentence of the proof of Stacks 0EPS, which produces it there, is
not established in this library, for the reasons given in the implementation notes of this
module. -/
@[stacks 0EPU "part (1): div_ℒ(s) in Div(X); the local finiteness that Stacks 0EPS supplies in
  the source comes from the hypothesis quadruple (U, hUopen, hUne, hgen), the open subspace over
  which s generates ℒ not being produced in this library"]
def divisorOfSectionOfGenerating
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))
    (hirr : IrreducibleSpace (points B S hS X)) (L : Modules.{u, max u z} B S hS X hX)
    (s : MeromorphicSection.{u, z} B S hS X hX L)
    (ratio : LocalRatioFamily.{u, z} B S hS hX hdec L)
    (U : Set (points B S hS X)) (hUopen : IsOpen U) (hUne : U.Nonempty)
    (hgen : ∀ W : PrimeDivisor B S hS X,
      divisorCoefficients.{u, z} B S hS hX hdec L s ratio W ≠ 0 →
        W.genericPoint B S hS X ∈ Uᶜ) :
    WeilDivisor B S hS X :=
  divisorOfSection.{u, z} B S hS hX hdec L s ratio
    (locallyFinite_divisorCoefficients_ne_zero.{u, z} B S hS hX hdec hN hirr L s ratio U
      hUopen hUne hgen)

end AlgebraicGeometry.Space

end
