module

public import StacksFrontier.AlgebraicGeometry.AmpleLocalGeneration.FromExtension
public import StacksFrontier.AlgebraicGeometry.TwistPullbackRatio.Comparison
public import StacksFrontier.AlgebraicGeometry.QuasiProjectiveChartRoute.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.AmpleTwistingSheaf

/-!
# Stacks Tags 01VS and 01VT on two named inputs

[Stacks, Tag 01VS] is reduced in
`StacksFrontier/AlgebraicGeometry/AmpleImmersionReduction/Basic.lean` to **four** named conditions:
`Stacks.AmpleImmersionReduction.TwistPullback`,
`Stacks.AmpleImmersionReduction.ChartImmersion`,
`Stacks.AmpleEventualGeneration.IsEventuallyFinGenPowers` and
`Stacks.AmpleImmersionReduction.TwistPassage`. **Two of the four are theorems**, and this
file uses that:

* `TwistPullback f` is a *theorem*, for every `f : X ⟶ S`. It is
  `Stacks.TwistPullbackChart.twistPullback_of_atUniverse` applied to
  `Stacks.TwistPullbackPinned.twistPullbackAtUniverse`, which is unconditional. The reduction in
  `./Basic.lean` carries it as a hypothesis, and the documentation of
  `StacksFrontier/AlgebraicGeometry/TwistPullbackChart/Basic.lean`
  still records the absolute form as "**not** proved"; both predate the proof.
* `IsEventuallyFinGenPowers X L` follows from the ampleness hypothesis that Tag 01VS already
  assumes, by `Stacks.AmpleLocalGeneration.isEventuallyFinGenPowers_of_isAmple`, which is also
  unconditional. It is an input of the four-way reduction only because that reduction is stated as
  an implication between named conditions rather than as a proof of
  `Stacks.AmpleProjectiveImmersion.ImmersionTwistGap`; moving the discharge inside the implication
  is all that is needed, since `ImmersionTwistGap` *is* an implication out of ampleness.

So Tag 01VS costs two conditions, `ChartImmersion` and `TwistPassage`, and [Stacks, Tag 01VT] —
which `Stacks.ProjectiveSpace.tfae_of_immersionTwistGapUniform` already carries on Tag 01VS alone
— costs the same two, with **no Stacks tag among its hypotheses**.

## Main definitions

* `Stacks.AmpleImmersionReduction.TwistPassageUniform`: the second remaining input, quantified
  over the situation, in the shape `Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform`
  is written in. The first is `Stacks.QuasiProjectiveChartRoute.ChartImmersionUniform`, which
  already exists.

## Main results

* `Stacks.AmpleImmersionReduction.twistPullback`: **`TwistPullback f` for every `f`**, with no
  hypothesis — the hypothesis of the four-way reduction, discharged.
* `Stacks.AmpleImmersionReduction.immersionTwistGap_of_chartImmersion_twistPassage`:
  **`Stacks.AmpleProjectiveImmersion.ImmersionTwistGap` — the whole of Tag 01VS — from two named
  inputs.**
* `Stacks.AmpleImmersionReduction.exists_immersion_projectiveSpaceOver_of_isAmple_of_two`:
  **Tag 01VS written out**, from the same two.
* `Stacks.AmpleImmersionReduction.hasImmersionTwistOver_of_isAmple_of_chartImmersion`: **Tag 01VS
  at a single degree from `ChartImmersion` alone** — the form the source calls "enough in virtually
  all applications", and the form a consumer that only needs one immersion into `ℙⁿ_S` should take.
* `Stacks.AmpleImmersionReduction.immersionTwistGapUniform_of_uniformInputs`: the uniform form,
  which is what Tag 01VT consumes.
* `Stacks.AmpleImmersionReduction.tfae_of_uniformInputs`: **Tag 01VT, conditions (1), (2), (5) and
  (6), on two conditions neither of which is a Stacks tag.** Every Stacks-tag hypothesis the
  earlier forms of this TFAE carried — Tag 01VS, Tag 02NN, Tag 0B3E — is gone.

## What is not done

**The two remaining inputs are not proved, and neither of them is Tag 01VS.**

* `Stacks.AmpleImmersionReduction.ChartImmersion` — steps 2 and 4 of the source: some positive
  power of `L` carries a generating family whose pinned morphism to `ℙⁿ_S` is an immersion. This is
  where the finite-type hypothesis is spent. **It is a gap in this library's own machinery, not a
  missing Stacks tag.** Of the four things the docstring of `./Basic.lean` records it as owing, the
  first two are available:

  - the finite-type algebra generators of [Stacks, Tag 01T2] are
    `AlgebraicGeometry.locallyOfFiniteType_iff`, the `mk_iff` lemma of the class, which carries the
    Tag 01T2 attribute at
    `StacksFrontier/AlgebraicGeometry/FiniteTypeClosedInFinitePresentation/QuasiAffine.lean:69`
    under the key `"(1) implies (2) and conversely"` — exactly the clause of the tag that is wanted;
  - the refinement of the cover so that each chart maps into an affine open of `S` is
    `Stacks.AmpleChartsOverBase.exists_generating_family_over_of_isAmple`
    (`../AmpleChartsOverBase/Basic.lean:125`), from ampleness alone, which produces step 1's family
    in one degree together with `∀ i, ∃ V, IsAffineOpen V ∧ nvCover s i ≤ f ⁻¹ᵁ V`;
    `exists_generating_hom_over_of_isAmple` (ibid. 215) adds the pinned morphism, and
    `exists_generating_family_finiteType_of_isAmple` (ibid. 192) adds the Tag 01T2 finite-type
    clause on each chart. The claim in `./Basic.lean` that this is unavailable is argued there from
    `Stacks.SectionExtension.exists_common_degree_affine_cover` having no base scheme in its
    signature, which is true of *that* declaration and not of the base clause, which
    `AmpleChartsOverBase` supplies separately.

  Two things are genuinely missing, and the first is the load-bearing one:

  - **the equalisation of the degrees.** Every degree-equalisation lemma in the library equalises
    degrees of *covering* sections while preserving their nonvanishing loci —
    `Stacks.FinGenFromCover.exists_common_degree_family` (`../FinGenFromCover/Powers.lean:148`),
    `Stacks.AmpleAffineAvoidance.exists_common_degree` and
    `Stacks.SectionExtension.exists_common_degree_affine_cover`. None equalises against the
    *numerators* that [Stacks, Tag 01PW] returns, and
    `Stacks.SectionExtension.isSectionRatio_of_isAmple` (`../SectionExtension/Ample.lean:502`)
    returns a denominator of uncontrolled degree rather than a power of `sᵢ`. Nothing anywhere
    relates `Stacks.ProjectiveFromSections.chartRatio` to an `Algebra.adjoin` generating set.
  - **the identification of the chart restriction with a ring map.** The chartwise datum that
    `Stacks.AmpleImmersionReduction.isImmersion_of_isImmersion_standardChart` (`./Charts.lean:228`)
    consumes must be produced for the *pinned* `p`, and
    `../ChartImmersionAssembly/Basic.lean:100-105` records the handle as
    `Stacks.SectionsToProjectiveSpace.resLE_toProjectiveSpaceAtUniverse`, which exists but is not
    applied there.

  Apart from that input, the passage from chart surjectivity to `IsImmersion p` is **present**, and
  as an equivalence: `./Charts.lean:174,228,266` and
  `../ChartImmersionAssembly/Basic.lean:229,245`; the one-chart ring-level case upgraded to algebra
  generation is `../ChartImmersionAssembly/Basic.lean:290`.
  `Stacks.QuasiProjectiveChartRoute.chartImmersion_of_isImmersion` proves the whole condition when
  `f` is itself an immersion, so it is not an implication from a false hypothesis.
* `Stacks.AmpleImmersionReduction.TwistPassage` — steps 6 and 7, the Segre passage, one degree at a
  time. [Stacks, Tag 01WD] itself is formalized (`Stacks.AlgebraicGeometry.SegreProdIso` and
  `Stacks.AlgebraicGeometry.Segre.ChartSurjective` carry the attribute), but what the passage needs
  is the *twist* along the Segre embedding, `Stacks.ChartImmersionAssembly.SegreTwist`, which
  strengthens Tag 01WD by one clause and is not proved;
  `StacksFrontier/AlgebraicGeometry/ExternalTensorPullback/Basic.lean` describes what lies
  between the two.

**No Tag 01VS or Tag 01VT attribute is attached, and none may be.** Both statements below carry
hypotheses their sources do not, so the covering-set rule withholds the labels. `./Basic.lean`
records that the Tag 01VS attribute belongs on its own final declaration once its inputs are
proved; that is still the right place, and the number of inputs is now two.

**`Stacks.ProductFamilyTwist.EventuallyGeneratesStalksPowers` is not discharged here**, but it is
discharged: it asks for a family `Fin (m + 1) → Γ(L ^⊗ d, ⊤)` satisfying
`Stacks.ProjectiveFromSections.GeneratesStalks`, whereas `IsEventuallyFinGenPowers` asks for a
`SheafOfModules.GeneratingSections` with a finite index, and the passage from the second predicate
to the first is `Stacks.StalkwiseGeneration.exists_generatesStalks_of_isFinGen`
(`StacksFrontier/AlgebraicGeometry/StalkwiseGeneration/Basic.lean`). It is not a Stacks tag: the
mathematics is that an epimorphism out of a finite free module is exactly a finite family of
global sections spanning every stalk, which `AlgebraicGeometry.generates_iff_stalkwise_generates`
states and `Stacks.AmpleLocalGeneration.isFinGenOn_of_isFinGen` packages, together with the
rewriting of each coefficient from the `RingCat` stalk into `𝒪_{X,x}` and the reindexing of a
finite type onto `Fin (m + 1)` by padding with the zero section. So the parallel route of
`StacksFrontier/AlgebraicGeometry/ProductFamilyTwist/Basic.lean` carries Tag 01VS with no named
input, as `Stacks.StalkwiseGeneration.exists_immersion_projectiveSpaceOver_of_isAmple`.

**Conditions (3) and (4) of Tag 01VT are statable but not linkable.** The claim recorded in
`StacksFrontier/AlgebraicGeometry/AmpleAffineBaseTFAE/Basic.lean` and in
`StacksFrontier/AlgebraicGeometry/VeryAmplePowersUniformDegree/Basic.lean`
that the projective bundle
`𝐏(E)` "has no library form in this repository", so that [Stacks, Tag 01VM] cannot be written down,
is **false**: `Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple`
(`../RelativeVeryAmpleTwist/DegreeOne.lean`) carries the Tag 01VM attribute, and everything it
quantifies over is constructed — `Stacks.SymGraded.schemeProjectiveBundle` for the bundle and
`Stacks.Tag01VMVeryAmple.twistOne` for `𝒪_{𝐏(E)}(1)`, whose invertibility is an instance.

What blocks the six-way equivalence is therefore not the statement but the two implications the
source gets from "`ℙⁿ_S` is a projective bundle over `S`" (Constructions, Lemma 27.21.5), namely
(5) ⟹ (3) and (6) ⟹ (4). **That lemma is [Stacks, Tag 01OE], and it is formalized**, in both halves:
`Stacks.SymGraded.projectiveBundleIsoProjectiveSpace` is the isomorphism `𝐏(𝒪_X^{n+1}) ≅ ℙⁿ_X` and
`Stacks.SymGraded.projectiveBundleIsoProjectiveSpace_hom_comp_fst` says it is an isomorphism *over*
`X`; both carry the Tag 01OE attribute
(`../SheafSymmetricAlgebra/ProjectiveSpaceMorphism.lean:633,644`), and
`Stacks.QuasiProjective.HProjective` already uses the pair to move an immersion into `ℙⁿ_S` across
to the bundle, which is the shape (5) ⟹ (3) needs. The comparison of `polyAlgebra` with `Sym` in
`../ProjPolynomialSections/Polynomial.lean` is not bridged, but Tag 01OE does not go through it.

The one thing still missing is the **twist** along that isomorphism: that it carries
`Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n S` to
`Stacks.Tag01VMVeryAmple.twistOne` of the free module. No declaration asserts it — there is no
mention of any twist anywhere in `../SheafSymmetricAlgebra/` — and it is a side condition rather
than a tag of its own, being the degree-one twist comparison of [Stacks, Tag 01NO] and
[Stacks, Tag 01O4] transported along an isomorphism that is already proved. The remaining
implication (3) ⟹ (2) is [Stacks, Tag 01VN] and is available as
`Stacks.Tag01VMVeryAmple.isRelativelyAmple_of_isRelativelyVeryAmple`, on the named premise
`Stacks.Tag01VNChartBasis.ProjOneBasisClause`.

## References

* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 01VT](https://stacks.math.columbia.edu/tag/01VT)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
* [Stacks Project, Tag 01VN](https://stacks.math.columbia.edu/tag/01VN)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01T2](https://stacks.math.columbia.edu/tag/01T2)
* [Stacks Project, Tag 01WD](https://stacks.math.columbia.edu/tag/01WD)
* [Stacks Project, Tag 01OE](https://stacks.math.columbia.edu/tag/01OE)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Ample Stacks.AmpleProjectiveImmersion

universe u

namespace Stacks.AmpleImmersionReduction

/-! ### The twist half of Tag 01NE is a theorem -/

/-- **`Stacks.AmpleImmersionReduction.TwistPullback f`, for every `f : X ⟶ S`, with no
hypothesis.** The morphism pinned on the charts by a generating family of global sections of an
invertible `M` pulls the hyperplane sheaf of `ℙⁿ_S` back to `M`.

`Stacks.TwistPullbackChart.twistPullback_of_atUniverse` reduces this to the base-free form
`Stacks.TwistPullbackChart.TwistPullbackAtUniverse`, and that form is proved unconditionally as
`Stacks.TwistPullbackPinned.twistPullbackAtUniverse`. So the first of the four named inputs of
`Stacks.AmpleImmersionReduction.immersionTwistGap_of_chartImmersionTwist` is not an input. -/
theorem twistPullback {X S : Scheme.{u}} (f : X ⟶ S) : TwistPullback f :=
  Stacks.TwistPullbackChart.twistPullback_of_atUniverse
    Stacks.TwistPullbackPinned.twistPullbackAtUniverse f

/-! ### Tag 01VS from two named inputs -/

section Reduction

variable {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules) [IsInvertibleModule X L]

/-- **Tag 01VS at a single degree, from `Stacks.AmpleImmersionReduction.ChartImmersion` alone.**
For `L` ample and `f` locally of finite type there are a positive degree `N` and an immersion
`X ⟶ ℙⁿ_S` over `S` pulling `𝒪(1)` back to `L ^⊗ N`.

`Stacks.AmpleImmersionReduction.hasImmersionTwistOver_of_isAmple` asks for `TwistPullback` as well;
it is `Stacks.AmpleImmersionReduction.twistPullback`. The source remarks that this single-degree
form "is enough in virtually all applications", and a consumer that needs only one immersion into
projective space — rather than every sufficiently high degree — should take this and not the
eventual form, because `Stacks.AmpleImmersionReduction.TwistPassage` is not needed for it. -/
theorem hasImmersionTwistOver_of_isAmple_of_chartImmersion (hch : ChartImmersion f L)
    (hL : IsAmple X L) (hft : LocallyOfFiniteType f) :
    ∃ N : ℤ, 1 ≤ N ∧ HasImmersionTwistOver f (tensorPowModule X L N) :=
  hasImmersionTwistOver_of_isAmple f L (twistPullback f) hch hL hft

/-- **The whole of `Stacks.AmpleProjectiveImmersion.ImmersionTwistGap`, hence the whole of
[Stacks, Tag 01VS], from two named inputs.**

`Stacks.AmpleImmersionReduction.immersionTwistGap_of_chartImmersionTwist` asks for four. The first,
`TwistPullback`, is `Stacks.AmpleImmersionReduction.twistPullback`. The third,
`Stacks.AmpleEventualGeneration.IsEventuallyFinGenPowers X L`, follows from the ampleness
hypothesis of `ImmersionTwistGap` itself by
`Stacks.AmpleLocalGeneration.isEventuallyFinGenPowers_of_isAmple`. Neither is an input. -/
theorem immersionTwistGap_of_chartImmersion_twistPassage (hch : ChartImmersion f L)
    (hpass : TwistPassage f L) :
    ImmersionTwistGap f L (tensorPowModule X L) := by
  intro hL hft
  exact immersionTwistGap_of_chartImmersionTwist f L (twistPullback f) hch
    (Stacks.AmpleLocalGeneration.isEventuallyFinGenPowers_of_isAmple L hL) hpass hL hft

/-- **[Stacks, Tag 01VS] written out, from two named inputs.** Every sufficiently high tensor power
of an ample invertible module on a scheme locally of finite type over `S` is the hyperplane sheaf
of a projective space over `S` pulled back along an immersion lying over `S`.

The conclusion is that of
`Stacks.AmpleImmersionReduction.exists_immersion_projectiveSpaceOver_of_isAmple` verbatim; what is
dropped is its `htw` and `hpow` hypotheses. -/
theorem exists_immersion_projectiveSpaceOver_of_isAmple_of_two (hL : IsAmple X L)
    [hf : LocallyOfFiniteType f] (hch : ChartImmersion f L) (hpass : TwistPassage f L) :
    ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
      ∃ (n : ℕ) (i : X ⟶ projectiveSpaceOver n S),
        IsImmersion i ∧
        i ≫ pullback.fst (terminal.from S)
          (terminal.from (projectiveSpaceAtUniverse.{u} n)) = f ∧
        Nonempty (tensorPowModule X L (d : ℤ) ≅
          (Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf n S)) :=
  exists_immersion_projectiveSpaceOver_of_isAmple' f L hL
    (immersionTwistGap_of_chartImmersion_twistPassage f L hch hpass)

end Reduction

/-! ### The remaining input, quantified over the situation -/

/-- **`Stacks.AmpleImmersionReduction.TwistPassage` at every situation.** Written with the
quantifier prefix of `Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform` so that the
inputs of Tag 01VT are comparable with the hypothesis they replace. -/
def TwistPassageUniform : Prop :=
  ∀ (A B : Scheme.{u}) (g : A ⟶ B) (N : A.Modules) [IsInvertibleModule A N],
    TwistPassage g N

/-- **`Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform` — [Stacks, Tag 01VS] at every
situation — from the two uniform inputs.** -/
theorem immersionTwistGapUniform_of_uniformInputs
    (hch : Stacks.QuasiProjectiveChartRoute.ChartImmersionUniform.{u})
    (hpass : TwistPassageUniform.{u}) :
    Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform.{u} :=
  fun A B g N _ => immersionTwistGap_of_chartImmersion_twistPassage g N
    (hch A B g N) (hpass A B g N)

/-! ### Tag 01VT with no Stacks tag among its hypotheses -/

/-- **[Stacks, Tag 01VT], conditions (1), (2), (5) and (6), on two conditions neither of which is a
Stacks tag.** For `f : X ⟶ S` locally of finite type and quasi-compact with `S` affine and `L` an
invertible `𝒪_X`-module, the following are equivalent:

1. `L` is ample on `X`;
2. `L` is ample relative to `f`;
3. (the source's (5)) some positive tensor power of `L` is `𝒪(1)` pulled back along an immersion
   `X ⟶ ℙⁿ_S` over `S`;
4. (the source's (6)) every sufficiently high tensor power of `L` is.

`Stacks.ProjectiveSpace.tfae_of_immersionTwistGapUniform` proves this from
`Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform`, which is the whole of
[Stacks, Tag 01VS]; the earlier `Stacks.Tag01VT.tfae` carried two further Stacks tags, Tag 02NN and
Tag 0B3E, both since proved. Here the last Stacks tag is replaced by the two conditions of
`Stacks.AmpleImmersionReduction.immersionTwistGapUniform_of_uniformInputs`.

The source's conditions (3) and (4) — relative very ampleness, [Stacks, Tag 01VM] — are not among
the four. They *can* be stated: `Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple` carries the Tag
01VM attribute. What is missing is the link to the other four; see "What is not done". -/
theorem tfae_of_uniformInputs (hch : Stacks.QuasiProjectiveChartRoute.ChartImmersionUniform.{u})
    (hpass : TwistPassageUniform.{u}) {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] [LocallyOfFiniteType f] (hqc : QuasiCompact f) :
    List.TFAE [
      IsAmple X L,
      Stacks.RelativeAmple.IsRelativelyAmple f L,
      ∃ d : ℕ, 1 ≤ d ∧ HasImmersionTwistOver f (tensorPowModule X L (d : ℤ)),
      ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
        HasImmersionTwistOver f (tensorPowModule X L (d : ℤ))] :=
  Stacks.ProjectiveSpace.tfae_of_immersionTwistGapUniform
    (immersionTwistGapUniform_of_uniformInputs hch hpass) f L hqc

end Stacks.AmpleImmersionReduction

end
