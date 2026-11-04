module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.SmoothQuotientStackAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SmoothGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageSystemProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactQuasiSeparatedStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack

/-!
# Descending an algebraic stack of finite presentation along a limit of algebraic spaces

Let `(X_i)` be a directed inverse system of quasi-compact, quasi-separated algebraic spaces over
`S` with affine transition morphisms and limit `X = lim X_i`. Stacks 0CN4 says that every
algebraic stack `𝒳` of finite presentation over `X` is a base change from a finite stage: there
are an `i` and an algebraic stack `𝒳_i` of finite presentation over `X_i` with
`𝒳 ≅ 𝒳_i ×_{X_i} X` as algebraic stacks over `X`.

## Main definitions

* `CategoryTheory.BasedCategory.EquivalenceOver`: an equivalence of categories over the base site
  which identifies two given 1-morphisms to a third, up to a 2-isomorphism. This is
  "`𝒳 ≅ 𝒴` as stacks over `𝒵`" at mixed hom universes, which is what an identification of an
  algebraic stack with a quotient stack is.
* `AlgebraicGeometry.Stack.equivalenceOfBasedEquivalence`: such an equivalence between two
  algebraic stacks, read as an equivalence in the 2-category of algebraic stacks of Stacks 03YP.
* `AlgebraicGeometry.Stack.StackDescentSystem`: the situation — the inverse system, its cardinality
  bounds, and the quasi-compactness and quasi-separatedness of its stages. It is the situation of
  Stacks 07SK, which is the input Stacks 0CN4 runs on.
* `AlgebraicGeometry.Stack.SmoothPresentationOverBase`: a smooth groupoid in algebraic spaces over
  an algebraic space `Y` whose object and arrow spaces are of finite presentation over `Y`,
  together with an identification of its quotient stack with a given algebraic stack over `Y`.
  This is the datum Stacks 04T4 (4), (5) and Stacks 04T5 (2) attach to a smooth chart.

## Main results

* `AlgebraicGeometry.Stack.StackDescentSystem.exists_stage_model_of_isFinitePresentation`:
  **Stacks 0CN4**, with six inputs of the source's proof carried as explicit hypotheses, one of
  which is a universe-lifting datum rather than a mathematical assumption. See the implementation
  notes for what each carries and, where an existing result falls short of discharging it, why.
* `AlgebraicGeometry.Stack.StackDescentSystem.exists_stage_model_objects` and
  `…exists_stage_model_arrows`: the essential-surjectivity clause of **Stacks 07SK** for the
  object and arrow spaces of a groupoid over the limit, proved from
  `AlgebraicGeometry.Space.exists_model_of_finitePresentation`.
* `AlgebraicGeometry.Stack.StackDescentSystem.exists_isSmooth_mapAt_of_isSmooth_mapLimit`:
  **Stacks 0CN2** in this situation, proved from the covariant form
  `AlgebraicGeometry.Space.MorphismDescentSystem.exists_isSmooth_mapAt_op` applied to
  `…morphismDescentSystem`. Stacks 0CN2 is applied here, never assumed.

## Implementation notes

**What is proved here and what is carried.** The source's proof of Stacks 0CN4 runs: `𝒳` is
quasi-compact, so it has an affine smooth surjective chart `U ⟶ 𝒳` (Stacks 04YC); the
self-intersection `R = U ×_𝒳 U` makes `(U, R, s, t, c)` a smooth groupoid in algebraic spaces of
finite presentation over `X` presenting `𝒳 = [U/R]` (Stacks 04T4, 04T5, with the quasi-compactness
and quasi-separatedness bookkeeping of Stacks 050K and 050H); Stacks 07SK and 0CN2 descend that
groupoid to a stage `X_i`; Stacks 04TK makes `[U_i/R_i]` an algebraic stack; and Stacks 044P,
044R, 046Q and 04Y1 identify `[U/R]` with `[U_i/R_i] ×_{X_i} X`.

The library has the ingredients of that chain but not its assembly. What is proved unconditionally
below is the part of the situation that does not need them — that the limit is a quasi-compact,
quasi-separated algebraic space (`StackDescentSystem.limit_isAlgebraicSpace`,
`StackDescentSystem.limit_quasiCompact`, `StackDescentSystem.limit_quasiSeparated`), by Stacks 07SF
and the affineness of the projections — together with the appeal to Stacks 04TK on the descended
groupoid, which is `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_of_isSmooth`. The
remaining steps are carried as named hypotheses, each a statement of a result the source cites
and none of them a restatement of the conclusion:

* `hPresentation`, what is left of the first half of the source's proof once **Stacks 04YC is
  discharged**. The chart no longer has to be assumed:
  `AlgebraicGeometry.Stack.hasAffineSmoothPresentation_of_isFinitePresentation` proves that an
  algebraic stack of finite presentation over a quasi-compact algebraic space has an affine smooth
  surjective chart, from `AlgebraicGeometry.Stack.isQuasiCompactStack_of_isQuasiCompactMorphism`
  and `AlgebraicGeometry.Stack.isQuasiCompactStack_iff_hasAffineSmoothPresentation`. The carried
  hypothesis is the `StackDescentSystem`-free
  `GroupoidPresentationOfAffineSmoothChart`, which *receives* the chart, and
  `AlgebraicGeometry.Stack.hasSmoothPresentationOverBase` derives the presentation over the base from it. What
  remains carried is Stacks 04T4 (4), (5), Stacks 04T5 (2) and the Stacks 050K / 050H bookkeeping.

  **Why Stacks 04T4 (4), (5) does not supply it directly.** The available datum is
  `AlgebraicGeometry.Stack.SelfIntersection.SelfIntersectionPresentation`, built by
  `…selfIntersectionPresentation`, and it has a field
  `baseIso : base.obj ≅ yoneda.obj (Over.mk (𝟙 (B.obj hS)))` pinning its base to the *terminal*
  algebraic space — the constructor sets `base := Space.terminalSpace B S hS`. So the groupoid it
  produces lives over the terminal space, whereas `SmoothPresentationOverBase` needs one over `Y`.
  Re-basing it along the invariant morphism `U ⟶ Y` would need `G.target ≫ u = G.source ≫ u` and
  `G.comp ≫ G.source = pullback.fst ≫ G.source`, neither of which the library states. The library
  does have a re-basing operation, `AlgebraicGeometry.GroupoidInAlgebraicSpaces.overBase`, under
  which the quotient stack is unchanged on the nose
  (`AlgebraicGeometry.Stack.quotientStack_overBase`), but it re-bases along a morphism *out of* the
  groupoid's current base, and here that base is terminal: a morphism from the terminal algebraic
  space to `Y` is exactly what does not exist. So `overBase` does not apply in this direction.
* `hDescent`, what is left of Stacks 07SK and 0CN2 on a groupoid object after the
  essential-surjectivity clause has been discharged. The *spaces* no longer have to be assumed to
  descend: `StackDescentSystem.exists_stage_model_objects` and `…exists_stage_model_arrows` prove
  that from `AlgebraicGeometry.Space.exists_model_of_finitePresentation`, and
  `StackDescentSystem.smoothGroupoidDescendsToStage` derives the full statement from the narrower
  `StackDescentSystem.GroupoidStructureDescendsToStage`, which receives the two stage models. What
  remains carried is the descent of `s`, `t`, `c` by the fullness and faithfulness clauses, the
  reconstruction of the `pointwiseGroupoid` field at the stage, the passage to a common stage, the
  smoothness of `s_i`, `t_i`, and the comparison of quotient stacks by Stacks 046Q.

  **The state of Stacks 0CN2 for this proof.** Stacks 0CN2 is formalized in two forms. The older,
  `AlgebraicGeometry.Space.MorphismDescentSystem.exists_isSmooth_mapAt`, states its conclusion over
  an inequality of the directed preorder that `AlgebraicGeometry.Space.MorphismDescentSystem`
  (Stacks 084W) is indexed by; the covariant form
  `AlgebraicGeometry.Space.MorphismDescentSystem.exists_isSmooth_mapAt_op` states it over a
  morphism of the cofiltered category `Iᵒᵖ`, which is the indexing Stacks 07SK uses and the one
  this module carries.

  Stacks 0CN2 is therefore **not assumed anywhere in this module**: it is applied, as
  `StackDescentSystem.exists_isSmooth_mapAt_of_isSmooth_mapLimit`, to the situation of Stacks 084W
  that `StackDescentSystem.morphismDescentSystem` builds out of a morphism of finite-presentation
  algebraic spaces over a stage. The quasi-compactness and quasi-separatedness of the source and
  target that Stacks 084W requires are derived there, not assumed, from finite presentation over
  the stage together with the stage's own quasi-compactness and quasi-separatedness — so the data
  the essential-surjectivity clause of Stacks 07SK already returns is enough to feed Stacks 0CN2.

  What `hDescent` still asserts, and the reason its `IsSmooth G_i` conjunct has not been replaced
  by an appeal to Stacks 0CN2, is **not** the identification of the two base-change constructions:
  that is `AlgebraicGeometry.Space.pullbackMapOver_hom_eq`, with the components
  `…pullbackMapOver_hom_comp_fst` and `…_snd`, so the base change `mapAt` builds as a
  `CategoryTheory.Limits.pullback.lift` and the one `AlgebraicGeometry.Space.baseChange` builds as
  a `pullbackMapOver` agree on the nose, and no property of morphisms has to be transported across
  a comparison. Three other ingredients are needed; two are in the library and one is
  not, as set out below.

  Stacks 0CN2 yields smoothness only at a *later* stage: it produces `j` and `g : j ⟶ i` and makes
  the base change along `C.diagram.map g` smooth, not `s_i` and `t_i` themselves. Using it
  therefore means replacing `G_i` by `AlgebraicGeometry.Space.baseChange G_i` along that
  transition, a groupoid over `X_j`, and then three further things are needed. Two of them the
  library now exposes:

  * the finite presentation of the base-changed object and arrow spaces over `X_j`, that is
    base-change stability of `AlgebraicGeometry.Space.IsFinitePresentation`:
    `AlgebraicGeometry.Space.IsFinitePresentation.of_isPullback`, in
    `StacksFrontier/AlgebraicGeometry/Spaces/FinitePresentationBaseChange.lean`;
  * the composition of two groupoid base changes — `Space.baseChange (Space.baseChange G h) k`
    against `Space.baseChange G (k ≫ h)` — which is what carries the comparison of quotient stacks
    over `X` from stage `i` to stage `j`. This is now
    `AlgebraicGeometry.Space.baseChangeCompIso`, an isomorphism of groupoids in algebraic spaces
    over the new base. Its object and arrow comparison is Mathlib's
    `CategoryTheory.Limits.pullbackRightPullbackFstIso` — note that Mathlib has no
    `pullbackLeftPullbackFstIso`, only that one and
    `CategoryTheory.Limits.pullbackLeftPullbackSndIso`; the two spaces agree under it on the nose,
    `AlgebraicGeometry.Space.pullbackMapOver_hom_eq` identifying the two base-change
    constructions; the source and target legs are
    `AlgebraicGeometry.Space.pullbackRightPullbackFstIso_hom_comp_baseChange_source` and
    `…_target`; the composition law is
    `AlgebraicGeometry.Space.pullbackRightPullbackFstIso_hom_baseChange_map_comp`, which compares
    the two nested `CategoryTheory.IsPullback.lift`s — neither of them computable — through their
    projections, named by `AlgebraicGeometry.Space.baseChangeComposableToOld` and the four lemmas
    beside it; `pointwiseGroupoid` needs no reconstruction, both sides being groupoids
    `AlgebraicGeometry.Space.baseChange` has already built; the identity law is not a hypothesis,
    `AlgebraicGeometry.Space.mapIdentityOfMapComp` deriving it from compatibility with composition
    and `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.mk'` packaging that discharge; and only
    one direction of the composition law had to be proved, because
    `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Iso.mk'` builds the backwards morphism out of
    two-sided inverses of the two maps.

  The third is **the one remaining obstacle**: the passage from that isomorphism of groupoids to an
  equivalence of quotient stacks over `X`. Stacks 046Q is formalized, as
  `AlgebraicGeometry.Stack.quotientStackMap`, the 1-morphism `[f]` induced by a morphism of
  groupoids over a fixed base; but an isomorphism of groupoids yields an *equivalence* of quotient
  stacks only through the functoriality of that construction — `quotientStackMap` of a composite
  against the composite of the `quotientStackMap`s, and `quotientStackMap` of an identity against
  an identity, each as a 2-isomorphism of based functors — and neither of those is stated.

  What that functoriality would be proved *from* is, however, already in the library. Stacks
  0436 asserts only existence — a 1-morphism `H` with a 2-commutative
  triangle — so `StacksFrontier/CategoryTheory/Sites/Stackification/UniversalPropertyGroupoid.lean`
  is faithful to its tag, and the uniqueness is **Stacks 04W9**, in
  `StacksFrontier/CategoryTheory/Sites/Stackification/UniversalPropertyUniqueness.lean`:
  `CategoryTheory.Functor.Stackification.restrict_isEquivalence` and `…restrictEquivalence` say
  that restriction along a stackification is an equivalence of morphism categories, with
  `…restrict_faithful`, `…restrict_full` and `…restrict_essSurj` as its three halves and
  `…extendTrans` as the 2-morphism that fullness extends. Its hypotheses are the ones the quotient
  stack already hands to `extendGroupoid`: `hG` from
  `(AlgebraicGeometry.Stack.isFibredOneMorphism_toQuotientStack G).comp_eq`, `hmor` from
  `AlgebraicGeometry.Stack.isLocallyBijective_toQuotientStack`, `hqmor` from the target being a
  stack, and `hobj` from `AlgebraicGeometry.Stack.essImage_toQuotientStack`. So 04W9 applies at
  exactly this instance, and the alternative route — asking instead that the stackification map
  reflect equivalences — is not needed.

  What is left is therefore not a missing input but the construction: compare the two restrictions
  along the stackification map, which is what
  `AlgebraicGeometry.Stack.quotientStackMap_commutes` is for, and then descend the comparison by
  the fullness and faithfulness of 04W9, a fully faithful functor reflecting isomorphisms.
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.id` and `…Hom.comp` are
  available, so the composites that an isomorphism of groupoids produces can be named. `StacksFrontier/CategoryTheory/Sites/Stackification/UniversalPropertyUniqueness.lean` carries a `set_option`, so the
  construction belongs beside `quotientStackMap` and not there.

  Concretely the chain is four steps, of which the last three are unobstructed.
  `AlgebraicGeometry.Stack.evaluation_comp` and `…evaluation_id` make
  `AlgebraicGeometry.Stack.quotientPointwiseMapData` functorial; Mathlib's
  `CategoryTheory.CoGrothendieck.map_comp_eq` and `…map_id_eq` are *equalities* and not merely
  isomorphisms, so that step carries `AlgebraicGeometry.Stack.quotientPointwiseMap` with it;
  `AlgebraicGeometry.Stack.quotientStackMap_commutes` compares the restrictions of the two
  candidate extensions along the stackification map; and `…restrict_full` with
  `…restrict_faithful` descend that comparison, a fully faithful functor reflecting isomorphisms.
  The step not yet done is the first one. `CategoryTheory.Pseudofunctor.StrongTrans` carries no
  `ext` lemma and its `naturality` field is dependent on its `app` field, so identifying the
  strong transformation of a composite with the vertical composite of the two transformations is a
  bicategorical computation: in `Cat` every structural 2-cell involved is an `eqToIso`, which is
  why the identification is true, but that has to be proved and not assumed. Note also that
  `AlgebraicGeometry.Stack.baseChangeQuotientStackSquare_commutes` does *not* apply: it is a
  square for `invariantTargetGroupoid`, a base change along a morphism of object spaces, not for
  the composition of two base changes along the base.
* The stage model, previously one bundled hypothesis, is now **three separate ones**, so that the
  universe step is isolated from the mathematics:

  * `hStageStackModel` (`StackDescentSystem.StageStackModel`) is the **universe-lifting datum**
    alone: an algebraic quotient stack has a model in `AlgebraicGeometry.Stack.AlgebraicStacks`.
    It asserts no mathematical property — only that the quotient stack may be replaced by an
    object whose hom sets lie one universe lower. Stackification raises hom sets, so
    `AlgebraicGeometry.Stack.quotientStack` is a `CategoryTheory.BasedCategory.{u + 1, u + 1}`
    while `AlgebraicStacks` objects have hom universe `u`; that is why
    `AlgebraicGeometry.Stack.liftedSpaceStack` exists. The library has no reduction the other way
    — Stacks 0457 transports representability across an equivalence but yields no small-hom model
    — and `AlgebraicGeometry.Stack.dimension_quotientStack_le` carries the same datum for the same
    reason, its notes recording that `AlgebraicStacks` objects "have their morphisms one universe
    below those of `AlgebraicGeometry.Stack.quotientStack`".
  * `hModelFinitePresentation` (`StackDescentSystem.ModelIsFinitePresentation`) is **Stacks 06Q2**
    for the model. Stacks 06Q2 is formalized as
    `AlgebraicGeometry.Stack.AlgebraicStacks.IsFinitePresentation`, the universal smooth-diagram
    test of Stacks 06FM; what is carried is the evaluation of that test on a quotient stack,
    which the library performs nowhere.
  * `hModelComparison` (`StackDescentSystem.ModelBaseChangeComparison`) is **Stacks 044P, 044R,
    046Q and 04Y1**: the quotient stack of a base-changed groupoid is the 2-fibre product. Stacks
    04Y1 is formalized as `CategoryTheory.TwoFibreProductOver.isStackification_stackifyMap` and
    Stacks 046Q as `AlgebraicGeometry.Stack.quotientStackMap`; what is carried is their
    combination for `AlgebraicGeometry.Space.baseChange`.

  `StackDescentSystem.stageModelOfSmoothGroupoid` reassembles the three into the bundled form
  `StackDescentSystem.StageModelOfSmoothGroupoid` that the main theorem's proof consumes.

**Index convention.** The source indexes by a directed set and an inverse system over it; here the
index is a cofiltered category and the system a covariant functor out of it, which is the
convention of Stacks 07SK and 0CN2 in this library. The two agree — a preorder is directed exactly
when it is cofiltered read with the arrows reversed — and matching Stacks 07SK is what lets its
clauses be cited.

**Shape of the conclusion.** `𝒳 ≅ 𝒳_i ×_{X_i} X as algebraic stacks over X` is an equivalence
`CategoryTheory.Bicategory.Equivalence` in the 2-category of algebraic stacks of Stacks 03YP whose
forward 1-morphism, composed with the projection of
`AlgebraicGeometry.Stack.twoFibreProductSquareAlgebraicStacks` to `X`, is 2-isomorphic to the
structure 1-morphism of `𝒳`. The 2-fibre product is the one of Stacks 04T2, taken in the
2-category of algebraic stacks and not merely in the ambient one.

The carried hypotheses are stated instead with `CategoryTheory.BasedCategory.EquivalenceOver`, an
equivalence over the big fppf site of `S` relative to two 1-morphisms to a third based category.
They have to be: the hom sets of a quotient stack sit one universe above those of an object of
`AlgebraicGeometry.Stack.AlgebraicStacks`, so an identification of `𝒳` with `[U/R]` is an
equivalence between based categories at *different* universes, which the single-universe
2-category of algebraic stacks cannot express.
`AlgebraicGeometry.Stack.equivalenceOfBasedEquivalence` converts back once both sides are
algebraic stacks, through
`CategoryTheory.Bicategory.Equivalence.mkOfAdjointifyCounit`.

## References

* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04T5](https://stacks.math.columbia.edu/tag/04T5)
* [Stacks Project, Tag 04TK](https://stacks.math.columbia.edu/tag/04TK)
* [Stacks Project, Tag 04YC](https://stacks.math.columbia.edu/tag/04YC)
* [Stacks Project, Tag 06Q2](https://stacks.math.columbia.edu/tag/06Q2)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 0CN2](https://stacks.math.columbia.edu/tag/0CN2)
* [Stacks Project, Tag 0CN4](https://stacks.math.columbia.edu/tag/0CN4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

/-! ### Equivalences of categories over the site, relative to a 1-morphism -/

namespace CategoryTheory.BasedCategory

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]

/-- Left-whiskering an isomorphism of based functors by a based functor. Mathlib's
`CategoryTheory.BasedCategory.whiskerLeft` is the same operation on 2-morphisms; the bicategory
of based categories has its objects at a single pair of universes, so the bicategorical
whiskering of isomorphisms does not apply to the mixed-universe composites below. -/
def isoWhiskerLeft {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    {𝒵 : BasedCategory.{v₄, u₄} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) {G H : 𝒴 ⥤ᵇ 𝒵} (α : G ≅ H) :
    F.comp G ≅ F.comp H :=
  BasedNatIso.mkNatIso
    (Functor.isoWhiskerLeft F.toFunctor ((BasedNatTrans.forgetful 𝒴 𝒵).mapIso α))
    fun a ↦ (whiskerLeft F α.hom).isHomLift' a

/-- Right-whiskering an isomorphism of based functors by a based functor. -/
def isoWhiskerRight {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    {𝒵 : BasedCategory.{v₄, u₄} 𝒮} {F G : 𝒳 ⥤ᵇ 𝒴} (α : F ≅ G) (H : 𝒴 ⥤ᵇ 𝒵) :
    F.comp H ≅ G.comp H :=
  BasedNatIso.mkNatIso
    (Functor.isoWhiskerRight ((BasedNatTrans.forgetful 𝒳 𝒴).mapIso α) H.toFunctor)
    fun a ↦ (whiskerRight α.hom H).isHomLift' a

/-- The composite of two equivalences of categories over `𝒮`. Composition of based functors is
strictly associative and unital, so the composites to be compared are equal and only the unit and
the counit have to be transported. -/
def Equivalence.trans {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    {𝒵 : BasedCategory.{v₄, u₄} 𝒮} (e : Equivalence 𝒳 𝒴) (e' : Equivalence 𝒴 𝒵) :
    Equivalence 𝒳 𝒵 where
  functor := e.functor.comp e'.functor
  inverse := e'.inverse.comp e.inverse
  unitIso := by
    have h := isoWhiskerLeft e.functor (isoWhiskerRight e'.unitIso e.inverse)
    exact h ≪≫ e.unitIso
  counitIso := by
    have h := isoWhiskerLeft e'.inverse (isoWhiskerRight e.counitIso e'.functor)
    exact h ≪≫ e'.counitIso

/-- **An equivalence of categories over `𝒮` which is an equivalence over a third based
category.** An equivalence `𝒳 ≅ 𝒴` over `𝒮` together with a 2-isomorphism identifying
`p : 𝒳 ⥤ᵇ 𝒵` with the composite of the equivalence with `q : 𝒴 ⥤ᵇ 𝒵`.

This is how "`𝒳 ≅ 𝒴` as stacks over `𝒵`" is read: an equivalence in the 2-category of categories
over `𝒮` whose forward 1-morphism commutes with the two structure 1-morphisms to `𝒵`, up to a
2-isomorphism. -/
structure EquivalenceOver {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    {𝒵 : BasedCategory.{v₅, u₅} 𝒮} (p : 𝒳 ⥤ᵇ 𝒵) (q : 𝒴 ⥤ᵇ 𝒵) where
  /-- The underlying equivalence of categories over `𝒮`. -/
  equiv : Equivalence 𝒳 𝒴
  /-- The 2-isomorphism exhibiting the equivalence as one over `𝒵`. -/
  compIso : equiv.functor.comp q ≅ p

/-- Equivalences over a third based category compose: the forward 1-morphism of the composite is
the composite of the two forward 1-morphisms, so its 2-isomorphism is the first one preceded by
the second whiskered into it. -/
def EquivalenceOver.trans {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    {𝒲 : BasedCategory.{v₄, u₄} 𝒮} {𝒵 : BasedCategory.{v₅, u₅} 𝒮}
    {p : 𝒳 ⥤ᵇ 𝒵} {q : 𝒴 ⥤ᵇ 𝒵} {r : 𝒲 ⥤ᵇ 𝒵}
    (e : EquivalenceOver p q) (e' : EquivalenceOver q r) : EquivalenceOver p r where
  equiv := e.equiv.trans e'.equiv
  compIso := by
    have h := isoWhiskerLeft e.equiv.functor e'.compIso
    exact h ≪≫ e.compIso

end CategoryTheory.BasedCategory

namespace AlgebraicGeometry.Stack

universe u w

/-! ### The situation -/

/-- **The situation of Stacks 0CN4**: a directed inverse system of quasi-compact,
quasi-separated algebraic spaces over `S` with affine transition morphisms, indexed by a directed
set small enough for the limits of the affine charts to stay inside the site.

The index is the directed set the tag itself assumes, and the system is carried as a covariant
diagram on the cofiltered category `Iᵒᵖ`. That is simultaneously the indexing of Stacks 07SK,
whose three clauses are what Stacks 0CN4 descends along, and of the covariant form of
Stacks 0CN2, `AlgebraicGeometry.Space.MorphismDescentSystem.exists_isSmooth_mapAt_op`; a
directed preorder is filtered, so `Iᵒᵖ` is cofiltered. -/
structure StackDescentSystem (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u})) (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)]
    [Nonempty I] where
  /-- The inverse system `(X_i)` of presheaves on the big fppf site over `S`, carried as a
  covariant diagram on the cofiltered category `Iᵒᵖ`. -/
  diagram : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- The index type is small compared to the cofinality of the site's size cutoff. -/
  indexSize : Cardinal.mk Iᵒᵖ < B.cutoff.ord.cof
  /-- Each hom type of the index is small compared to that cofinality. -/
  homSize : ∀ i j : Iᵒᵖ, Cardinal.mk (i ⟶ j) < B.cutoff.ord.cof
  /-- Every stage is an algebraic space over `S`. -/
  stage_isAlgebraicSpace : ∀ i, IsAlgebraicSpace B S hS (diagram.obj i)
  /-- Every transition morphism is affine. -/
  transition_affine : ∀ {i j : Iᵒᵖ} (f : i ⟶ j), Space.IsAffineHom B S hS (diagram.map f)
  /-- Every stage is quasi-compact. -/
  stage_quasiCompact : ∀ i, Space.IsQuasiCompactSpace B S hS (diagram.obj i)
  /-- Every stage is quasi-separated. -/
  stage_quasiSeparated : ∀ i, Space.IsAbsolutelyQuasiSeparated B S hS hZ (diagram.obj i)

namespace StackDescentSystem

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    [Nonempty I]
    (C : StackDescentSystem B S hS hZ I)

/-- **Stacks 07SF.** The limit `X = lim X_i` of the system is an algebraic space over `S`. -/
theorem limit_isAlgebraicSpace : IsAlgebraicSpace B S hS (limit C.diagram) :=
  Space.isAlgebraicSpace_limit B S hS C.diagram C.indexSize C.homSize
    C.stage_isAlgebraicSpace C.transition_affine

/-- Each projection `X ⟶ X_i` out of the limit is affine, the transition morphisms being so. -/
theorem limitπ_isAffineHom (i : Iᵒᵖ) : Space.IsAffineHom B S hS (limit.π C.diagram i) :=
  Space.isAffineHom_limitπ B S hS C.diagram C.indexSize C.homSize C.transition_affine i

/-- The limit `X = lim X_i` is quasi-compact: the projection to a stage is affine, hence
quasi-compact, and the base change of that projection along the identity of the stage is the
limit itself. -/
theorem limit_quasiCompact : Space.IsQuasiCompactSpace B S hS (limit C.diagram) := by
  obtain ⟨i⟩ : Nonempty Iᵒᵖ := inferInstance
  have hqc : Space.IsQuasiCompact B S hS (limit.π C.diagram i) :=
    Space.isQuasiCompact_of_isAffineHom' B S hS (limit.π C.diagram i)
      C.limit_isAlgebraicSpace (C.stage_isAlgebraicSpace i) (C.limitπ_isAffineHom i)
  let e : pullback (𝟙 (C.diagram.obj i)) (limit.π C.diagram i) ≅ limit C.diagram :=
    asIso (pullback.snd (𝟙 (C.diagram.obj i)) (limit.π C.diagram i))
  exact Space.isQuasiCompactSpace_of_iso B S hS e
    (hqc (C.diagram.obj i) (C.stage_isAlgebraicSpace i) (C.stage_quasiCompact i)
      (𝟙 (C.diagram.obj i)))

/-- The limit `X = lim X_i` is quasi-separated: it is affine, hence quasi-separated, over a
quasi-separated stage. -/
theorem limit_quasiSeparated :
    Space.IsAbsolutelyQuasiSeparated B S hS hZ (limit C.diagram) := by
  obtain ⟨i⟩ : Nonempty Iᵒᵖ := inferInstance
  exact Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ
    C.limit_isAlgebraicSpace (C.stage_quasiSeparated i)
    (Space.isQuasiSeparated_of_isAffineHom B S hS (limit.π C.diagram i)
      C.limit_isAlgebraicSpace (C.stage_isAlgebraicSpace i) (C.limitπ_isAffineHom i))

/-- The limit `X = lim X_i`, as an object of the category of algebraic spaces over `S`. -/
noncomputable abbrev limitSpace : AlgebraicSpaces B S hS :=
  ⟨limit C.diagram, C.limit_isAlgebraicSpace⟩

/-- The stage `X_i`, as an object of the category of algebraic spaces over `S`. -/
abbrev stageSpace (i : Iᵒᵖ) : AlgebraicSpaces B S hS :=
  ⟨C.diagram.obj i, C.stage_isAlgebraicSpace i⟩

/-- The projection `X ⟶ X_i`, as a morphism of algebraic spaces over `S`. -/
noncomputable abbrev limitProjection (i : Iᵒᵖ) : C.limitSpace ⟶ C.stageSpace i :=
  ObjectProperty.homMk (limit.π C.diagram i)

/-- The limit `X = lim X_i`, as an algebraic stack over `S`. -/
noncomputable abbrev limitStack : AlgebraicStacks.{u, w} B S hS :=
  algebraicSpaceStack.{u, w} B S hS (limit C.diagram) C.limit_isAlgebraicSpace

/-- The stage `X_i`, as an algebraic stack over `S`. -/
abbrev stageStack (i : Iᵒᵖ) : AlgebraicStacks.{u, w} B S hS :=
  algebraicSpaceStack.{u, w} B S hS (C.diagram.obj i) (C.stage_isAlgebraicSpace i)

/-- The projection `X ⟶ X_i`, as a 1-morphism of algebraic stacks over `S`. -/
noncomputable abbrev limitStackProjection (i : Iᵒᵖ) :
    C.limitStack.{u, w} ⟶ C.stageStack.{u, w} i :=
  Bicategory.InducedBicategory.mkHom (associatedMap B S hS (limit.π C.diagram i)).1

/-! ### Stacks 07SK in the situation of Stacks 0CN4 -/

/-- **Stacks 07SK, essential surjectivity, in the situation of Stacks 0CN4.** An algebraic space
of finite presentation over the limit `X = lim X_i` is the base change, along some projection
`X ⟶ X_i`, of an algebraic space of finite presentation over `X_i`.

This is `AlgebraicGeometry.Space.exists_model_of_finitePresentation`, whose hypotheses are
exactly the fields of `AlgebraicGeometry.Stack.StackDescentSystem`. -/
theorem exists_stage_model_of_isFinitePresentation_over_limit
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (p : F ⟶ limit C.diagram) (hp : Space.IsFinitePresentation B S hS p) :
    ∃ (i : Iᵒᵖ) (Fᵢ : Over (C.diagram.obj i)),
      IsAlgebraicSpace B S hS Fᵢ.left ∧ Space.IsFinitePresentation B S hS Fᵢ.hom ∧
        Nonempty (Over.mk p ≅ (Over.pullback (limit.π C.diagram i)).obj Fᵢ) :=
  Space.exists_model_of_finitePresentation B S hS hZ C.diagram C.indexSize C.homSize
    C.stage_isAlgebraicSpace C.transition_affine C.stage_quasiCompact C.stage_quasiSeparated
    (Over.mk p) hF hp

/-- **Stacks 07SK, essential surjectivity, for the object space of a groupoid over the limit.**
The object space of a groupoid in algebraic spaces over `X` which is of finite presentation over
`X` comes from a stage. -/
theorem exists_stage_model_objects (G : GroupoidInAlgebraicSpaces B S hS C.limitSpace)
    (hU : Space.IsFinitePresentation B S hS G.objectsToBase.hom) :
    ∃ (i : Iᵒᵖ) (Uᵢ : Over (C.diagram.obj i)),
      IsAlgebraicSpace B S hS Uᵢ.left ∧ Space.IsFinitePresentation B S hS Uᵢ.hom ∧
        Nonempty (Over.mk G.objectsToBase.hom ≅
          (Over.pullback (limit.π C.diagram i)).obj Uᵢ) :=
  C.exists_stage_model_of_isFinitePresentation_over_limit G.objects.property
    G.objectsToBase.hom hU

/-- **Stacks 07SK, essential surjectivity, for the arrow space of a groupoid over the limit.**
The arrow space of a groupoid in algebraic spaces over `X` which is of finite presentation over
`X` comes from a stage. -/
theorem exists_stage_model_arrows (G : GroupoidInAlgebraicSpaces B S hS C.limitSpace)
    (hR : Space.IsFinitePresentation B S hS G.arrowsToBase.hom) :
    ∃ (i : Iᵒᵖ) (Rᵢ : Over (C.diagram.obj i)),
      IsAlgebraicSpace B S hS Rᵢ.left ∧ Space.IsFinitePresentation B S hS Rᵢ.hom ∧
        Nonempty (Over.mk G.arrowsToBase.hom ≅
          (Over.pullback (limit.π C.diagram i)).obj Rᵢ) :=
  C.exists_stage_model_of_isFinitePresentation_over_limit G.arrows.property
    G.arrowsToBase.hom hR

/-! ### Stacks 0CN2 in the situation of Stacks 0CN4 -/

/-- **The situation of Stacks 084W attached to a morphism over a stage.** A morphism of algebraic
spaces of finite presentation over a stage `X_i` of the system, read as a morphism descent system
in the sense of Stacks 084W, so that the descent statements of this library's
`AlgebraicGeometry.Space.MorphismDescentSystem` namespace — Stacks 0CN2 among them — apply to it.

The quasi-compactness and quasi-separatedness of the source and the target that Stacks 084W
requires are not extra hypotheses: they follow from finite presentation over the stage together
with the quasi-compactness and quasi-separatedness of the stage itself, by
`AlgebraicGeometry.Space.isQuasiCompactSpace_of_isFinitePresentation` and
`AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated`. -/
noncomputable def morphismDescentSystem (i : Iᵒᵖ) (X₀ Y₀ : Over (C.diagram.obj i))
    (hX₀ : IsAlgebraicSpace B S hS X₀.left) (hY₀ : IsAlgebraicSpace B S hS Y₀.left)
    (hX₀fp : Space.IsFinitePresentation B S hS X₀.hom)
    (hY₀fp : Space.IsFinitePresentation B S hS Y₀.hom) (f₀ : X₀ ⟶ Y₀) :
    Space.MorphismDescentSystem B S hS hZ I where
  base := C.diagram
  indexSize := (Cardinal.mk_congr (Opposite.equivToOpposite (α := I))).trans_lt C.indexSize
  base_isAlgebraicSpace := fun j => C.stage_isAlgebraicSpace (Opposite.op j)
  transition_affine := C.transition_affine
  limit_isAlgebraicSpace := C.limit_isAlgebraicSpace
  initial := i.unop
  source₀ := X₀.left
  target₀ := Y₀.left
  sourceToBase := X₀.hom
  targetToBase := Y₀.hom
  map₀ := f₀.left
  map₀_over := Over.w f₀
  source₀_isAlgebraicSpace := hX₀
  target₀_isAlgebraicSpace := hY₀
  base₀_quasiCompact := C.stage_quasiCompact i
  base₀_quasiSeparated := C.stage_quasiSeparated i
  source₀_quasiCompact :=
    Space.isQuasiCompactSpace_of_isFinitePresentation B S hS X₀.hom
      (C.stage_isAlgebraicSpace i) (C.stage_quasiCompact i) hX₀fp
  source₀_quasiSeparated :=
    Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hX₀
      (C.stage_quasiSeparated i) hX₀fp.2.2
  target₀_quasiCompact :=
    Space.isQuasiCompactSpace_of_isFinitePresentation B S hS Y₀.hom
      (C.stage_isAlgebraicSpace i) (C.stage_quasiCompact i) hY₀fp
  target₀_quasiSeparated :=
    Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hY₀
      (C.stage_quasiSeparated i) hY₀fp.2.2

/-- **Stacks 0CN2 in the situation of Stacks 0CN4.** A morphism of algebraic spaces of finite
presentation over a stage whose base change to the limit is smooth, and which is itself locally of
finite presentation, becomes smooth after base change along some further transition morphism of
the system.

This is `AlgebraicGeometry.Space.MorphismDescentSystem.exists_isSmooth_mapAt_op` — the covariant
form of Stacks 0CN2 — applied to
`AlgebraicGeometry.Stack.StackDescentSystem.morphismDescentSystem`. Nothing about the situation
has to be assumed beyond what the system already carries. -/
theorem exists_isSmooth_mapAt_of_isSmooth_mapLimit (i : Iᵒᵖ) (X₀ Y₀ : Over (C.diagram.obj i))
    (hX₀ : IsAlgebraicSpace B S hS X₀.left) (hY₀ : IsAlgebraicSpace B S hS Y₀.left)
    (hX₀fp : Space.IsFinitePresentation B S hS X₀.hom)
    (hY₀fp : Space.IsFinitePresentation B S hS Y₀.hom) (f₀ : X₀ ⟶ Y₀)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS f₀.left)
    (hsmooth : Space.IsSmooth B S hS
      (C.morphismDescentSystem i X₀ Y₀ hX₀ hY₀ hX₀fp hY₀fp f₀).mapLimit) :
    ∃ (j : Iᵒᵖ) (g : j ⟶ i),
      Space.IsSmooth B S hS
        ((C.morphismDescentSystem i X₀ Y₀ hX₀ hY₀ hX₀fp hY₀fp f₀).mapAt j.unop
          (leOfHom g.unop)) :=
  Space.MorphismDescentSystem.exists_isSmooth_mapAt_op
    (C.morphismDescentSystem i X₀ Y₀ hX₀ hY₀ hX₀fp hY₀fp f₀) hsmooth hfp

end StackDescentSystem

/-! ### The carried inputs -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

/-- A 2-isomorphism of 1-morphisms of algebraic stacks over `S` from an isomorphism of the
underlying based functors: the 2-category of algebraic stacks is induced, twice over, from the
2-category of categories over the big fppf site. -/
def isoMkAlgebraicStacks {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {f g : 𝒳 ⟶ 𝒴}
    (φ : f.hom.hom ≅ g.hom.hom) : f ≅ g :=
  Bicategory.InducedBicategory.isoMk (Bicategory.InducedBicategory.isoMk φ)

/-- An equivalence of the underlying categories over the big fppf site of `S` is an equivalence in
the 2-category of algebraic stacks of Stacks 03YP: that 2-category is a full sub-2-category of the
2-category of categories over the site, so the unit and the counit transfer, and the triangle
identity is supplied by `CategoryTheory.Bicategory.Equivalence.mkOfAdjointifyCounit`. -/
noncomputable def equivalenceOfBasedEquivalence {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (e : BasedCategory.Equivalence 𝒳.val.val 𝒴.val.val) : Bicategory.Equivalence 𝒳 𝒴 :=
  Bicategory.Equivalence.mkOfAdjointifyCounit
    (f := Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom e.functor))
    (g := Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom e.inverse))
    (isoMkAlgebraicStacks B S hS e.unitIso.symm) (isoMkAlgebraicStacks B S hS e.counitIso)

/-- The forward 1-morphism of `AlgebraicGeometry.Stack.equivalenceOfBasedEquivalence` is the
forward based functor of the given equivalence. -/
@[simp]
theorem equivalenceOfBasedEquivalence_hom {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (e : BasedCategory.Equivalence 𝒳.val.val 𝒴.val.val) :
    (equivalenceOfBasedEquivalence.{u, w} B S hS e).hom.hom.hom = e.functor :=
  rfl

/-- **A smooth groupoid presentation of finite presentation over the base.** A smooth groupoid in
algebraic spaces over `Y` whose object and arrow spaces are of finite presentation over `Y`,
together with an equivalence of `𝒳` with its quotient stack over `Y`, carrying the given structure
1-morphism `f` to the one of Stacks 044R.

This is the datum Stacks 04T4 (4), (5) and Stacks 04T5 (2) attach to an affine smooth surjective
chart of `𝒳`. -/
structure SmoothPresentationOverBase {Y : AlgebraicSpaces B S hS}
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y.obj Y.property) where
  /-- The presenting groupoid in algebraic spaces over `Y`. -/
  groupoid : GroupoidInAlgebraicSpaces B S hS Y
  /-- It is smooth, in the sense of Stacks 04TH. -/
  isSmooth : GroupoidInAlgebraicSpaces.IsSmooth B S hS groupoid
  /-- Its object space is of finite presentation over `Y`. -/
  objects_finitePresentation : Space.IsFinitePresentation B S hS groupoid.objectsToBase.hom
  /-- Its arrow space is of finite presentation over `Y`. -/
  arrows_finitePresentation : Space.IsFinitePresentation B S hS groupoid.arrowsToBase.hom
  /-- The equivalence `𝒳 ≅ [U/R]` over `Y`. -/
  equivOver : BasedCategory.EquivalenceOver f.hom.hom (quotientStackToBase groupoid)

/-- **Stacks 04YC together with Stacks 04T4 (4), (5) and Stacks 04T5 (2).** Every algebraic stack
of finite presentation over a quasi-compact quasi-separated algebraic space `Y` over `S` has a
smooth groupoid presentation whose object and arrow spaces are of finite presentation over `Y`.

In the source this is the first half of the proof of Stacks 0CN4: finite presentation of the
structure 1-morphism makes `𝒳` quasi-compact, Stacks 04YC produces an affine smooth surjective
chart `U ⟶ 𝒳`, Stacks 04T4 forms `R = U ×_𝒳 U` and the groupoid, Stacks 04T5 (2) identifies `𝒳`
with `[U/R]`, and Stacks 050K and 050H supply the quasi-compactness and quasi-separatedness that
make `U` and `R` of finite presentation over `Y`. -/
abbrev HasSmoothPresentationOverBase : Prop :=
  ∀ (Y : AlgebraicSpaces B S hS), Space.IsQuasiCompactSpace B S hS Y.obj →
    Space.IsAbsolutelyQuasiSeparated B S hS hZ Y.obj →
    ∀ (𝒳 : AlgebraicStacks.{u, w} B S hS)
      (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y.obj Y.property),
      AlgebraicStacks.IsFinitePresentation B S hS f →
        Nonempty (SmoothPresentationOverBase.{u, w} B S hS 𝒳 f)

/-- **Stacks 04YC for an algebraic stack of finite presentation over a quasi-compact algebraic
space.** Such a stack has an affine smooth surjective chart.

This is the first step of the proof of Stacks 0CN4, and it is proved rather than assumed: finite
presentation of the structure 1-morphism includes quasi-compactness (Stacks 050U), the base is a
quasi-compact algebraic stack
(`AlgebraicGeometry.Stack.isQuasiCompactStack_fibredCategory`), so `𝒳` is quasi-compact by
`AlgebraicGeometry.Stack.isQuasiCompactStack_of_isQuasiCompactMorphism`, and Stacks 04YC
(`AlgebraicGeometry.Stack.isQuasiCompactStack_iff_hasAffineSmoothPresentation`) turns that into
the chart. -/
theorem hasAffineSmoothPresentation_of_isFinitePresentation
    (Y : AlgebraicSpaces B S hS) (hYqc : Space.IsQuasiCompactSpace B S hS Y.obj)
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y.obj Y.property)
    (hf : AlgebraicStacks.IsFinitePresentation B S hS f) :
    HasAffineSmoothPresentation.{u, w} B S hS 𝒳 :=
  (isQuasiCompactStack_iff_hasAffineSmoothPresentation.{u, w} B S hS 𝒳).1
    (isQuasiCompactStack_of_isQuasiCompactMorphism.{u, w} B S hS f hf.2.1
      (isQuasiCompactStack_fibredCategory.{u, w} B S hS Y.obj Y.property hYqc
        (algebraicSpaceStack.{u, w} B S hS Y.obj Y.property).property))

/-- **What remains of the first half of the proof of Stacks 0CN4 once Stacks 04YC is
discharged.** Given an affine smooth surjective chart of `𝒳`, produce the smooth groupoid
presentation of finite presentation over the base.

What is still carried here is Stacks 04T4 (4), (5) — the formation of `R = U ×_𝒳 U` and of the
groupoid — Stacks 04T5 (2) — that the canonical 1-morphism out of `[U/R]` is an equivalence — and
the Stacks 050K and 050H bookkeeping that makes `U` and `R` of finite presentation over `Y`.
Stacks 04YC is no longer assumed: see
`AlgebraicGeometry.Stack.hasAffineSmoothPresentation_of_isFinitePresentation`. -/
abbrev GroupoidPresentationOfAffineSmoothChart : Prop :=
  ∀ (Y : AlgebraicSpaces B S hS), Space.IsQuasiCompactSpace B S hS Y.obj →
    Space.IsAbsolutelyQuasiSeparated B S hS hZ Y.obj →
    ∀ (𝒳 : AlgebraicStacks.{u, w} B S hS)
      (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y.obj Y.property),
      AlgebraicStacks.IsFinitePresentation B S hS f →
      HasAffineSmoothPresentation.{u, w} B S hS 𝒳 →
        Nonempty (SmoothPresentationOverBase.{u, w} B S hS 𝒳 f)

/-- The smooth groupoid presentation of an algebraic stack of finite presentation over a
quasi-compact quasi-separated algebraic space, with Stacks 04YC discharged: the chart it needs is
produced by `AlgebraicGeometry.Stack.hasAffineSmoothPresentation_of_isFinitePresentation`. -/
theorem hasSmoothPresentationOverBase
    (h : GroupoidPresentationOfAffineSmoothChart.{u, w} B S hS hZ) :
    HasSmoothPresentationOverBase.{u, w} B S hS hZ := fun Y hYqc hYqs 𝒳 f hf =>
  h Y hYqc hYqs 𝒳 f hf
    (hasAffineSmoothPresentation_of_isFinitePresentation.{u, w} B S hS Y hYqc 𝒳 f hf)

/-! ### Stacks 0CN4 -/

namespace StackDescentSystem

variable {B S hS hZ}
variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (C : StackDescentSystem B S hS hZ I)

/-- **Stacks 07SK and Stacks 0CN2 read on a groupoid object.** A smooth groupoid in algebraic
spaces over the limit `X` whose object and arrow spaces are of finite presentation over `X` is,
up to equivalence of quotient stacks over `X`, the base change of a smooth groupoid over some
stage `X_i` whose object and arrow spaces are of finite presentation over `X_i`.

In the source this is the sentence "by Limits of Spaces, Lemma 70.7.1 we can find an `i` and a
groupoid `(U_i, R_i, s_i, t_i, c_i)` over `X_i`, and after increasing `i` the morphisms `s_i` and
`t_i` are smooth": Stacks 07SK applied to the object space, the arrow space and the three
structure morphisms, followed by Stacks 0CN2 on `s_i` and `t_i`.

The essential-surjectivity half of that sentence is *not* assumed: it is
`AlgebraicGeometry.Stack.StackDescentSystem.exists_stage_model_objects` and
`…exists_stage_model_arrows`, and
`AlgebraicGeometry.Stack.StackDescentSystem.smoothGroupoidDescendsToStage` derives this
statement from `AlgebraicGeometry.Stack.StackDescentSystem.GroupoidStructureDescendsToStage`,
which receives the two stage models rather than producing them. -/
abbrev SmoothGroupoidDescendsToStage : Prop :=
  ∀ G : GroupoidInAlgebraicSpaces B S hS C.limitSpace,
    GroupoidInAlgebraicSpaces.IsSmooth B S hS G →
    Space.IsFinitePresentation B S hS G.objectsToBase.hom →
    Space.IsFinitePresentation B S hS G.arrowsToBase.hom →
    ∃ (i : Iᵒᵖ) (Gᵢ : GroupoidInAlgebraicSpaces B S hS (C.stageSpace i)),
      GroupoidInAlgebraicSpaces.IsSmooth B S hS Gᵢ ∧
        Space.IsFinitePresentation B S hS Gᵢ.objectsToBase.hom ∧
        Space.IsFinitePresentation B S hS Gᵢ.arrowsToBase.hom ∧
        Nonempty (BasedCategory.EquivalenceOver (quotientStackToBase G)
          (quotientStackToBase (Space.baseChange Gᵢ (C.limitProjection i)).groupoid))

/-- **What remains of Stacks 07SK and Stacks 0CN2 for a groupoid object once its object and arrow
spaces have been descended.** Given a smooth groupoid over the limit `X` together with models of
its object and arrow spaces over two stages, reassemble a smooth groupoid over a common stage
whose base change to `X` has, over `X`, the same quotient stack.

What is left here, and so still carried, is: the descent of the three structure morphisms
`s`, `t`, `c` by the fullness and faithfulness clauses of Stacks 07SK
(`AlgebraicGeometry.Space.exists_morphism_after_baseChange` and
`…eventually_eq_of_baseChange_eq`); the reconstruction of the field
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.pointwiseGroupoid` at the stage, which is a
groupoid structure at *every* test object of the site and not a morphism equation; the passage to
a common stage; smoothness of `s_i` and `t_i` by Stacks 0CN2; and the comparison of the two
quotient stacks by Stacks 046Q. Stacks 0CN2 itself is no longer assumed anywhere — it is applied
in `AlgebraicGeometry.Stack.StackDescentSystem.exists_isSmooth_mapAt_of_isSmooth_mapLimit` — but
it yields smoothness only at a later stage, and moving `G_i` there means carrying the comparison
of quotient stacks over `X` along with it. The composition of two groupoid base changes that this
needs is available, as `AlgebraicGeometry.Space.baseChangeCompIso`; what is still missing is the
passage from that isomorphism of groupoids to an equivalence of quotient stacks, which Stacks 046Q
gives only through a functoriality of `AlgebraicGeometry.Stack.quotientStackMap` that the library
does not state — although Stacks 04W9, the uniqueness it would be proved from, is available. See the
module's implementation notes. -/
abbrev GroupoidStructureDescendsToStage : Prop :=
  ∀ G : GroupoidInAlgebraicSpaces B S hS C.limitSpace,
    GroupoidInAlgebraicSpaces.IsSmooth B S hS G →
    ∀ (iU : Iᵒᵖ) (Uᵢ : Over (C.diagram.obj iU)),
      IsAlgebraicSpace B S hS Uᵢ.left → Space.IsFinitePresentation B S hS Uᵢ.hom →
      (Over.mk G.objectsToBase.hom ≅ (Over.pullback (limit.π C.diagram iU)).obj Uᵢ) →
    ∀ (iR : Iᵒᵖ) (Rᵢ : Over (C.diagram.obj iR)),
      IsAlgebraicSpace B S hS Rᵢ.left → Space.IsFinitePresentation B S hS Rᵢ.hom →
      (Over.mk G.arrowsToBase.hom ≅ (Over.pullback (limit.π C.diagram iR)).obj Rᵢ) →
    ∃ (i : Iᵒᵖ) (Gᵢ : GroupoidInAlgebraicSpaces B S hS (C.stageSpace i)),
      GroupoidInAlgebraicSpaces.IsSmooth B S hS Gᵢ ∧
        Space.IsFinitePresentation B S hS Gᵢ.objectsToBase.hom ∧
        Space.IsFinitePresentation B S hS Gᵢ.arrowsToBase.hom ∧
        Nonempty (BasedCategory.EquivalenceOver (quotientStackToBase G)
          (quotientStackToBase (Space.baseChange Gᵢ (C.limitProjection i)).groupoid))

/-- **The essential-surjectivity half of Stacks 07SK for a groupoid object, discharged.** Given
the reassembly of the groupoid structure at a stage, a smooth groupoid over the limit whose object
and arrow spaces are of finite presentation over the limit descends: the two spaces come from
stages by `AlgebraicGeometry.Space.exists_model_of_finitePresentation`, and nothing about them has
to be assumed. -/
theorem smoothGroupoidDescendsToStage
    (hStructure : C.GroupoidStructureDescendsToStage) :
    C.SmoothGroupoidDescendsToStage := by
  intro G hGsmooth hU hR
  obtain ⟨iU, Uᵢ, hUalg, hUfp, ⟨eU⟩⟩ := C.exists_stage_model_objects G hU
  obtain ⟨iR, Rᵢ, hRalg, hRfp, ⟨eR⟩⟩ := C.exists_stage_model_arrows G hR
  exact hStructure G hGsmooth iU Uᵢ hUalg hUfp eU iR Rᵢ hRalg hRfp eR

/-! ### The stage model: the universe datum, Stacks 06Q2, and the Stacks 04Y1 comparison -/

/-- **A model of a quotient stack in the 2-category of algebraic stacks over `S`.** An algebraic
stack over `S` with a 1-morphism to the stage `X_i`, together with an identification over `X_i` of
its category with the quotient stack `[U_i/R_i]`.

A quotient stack is not itself an object of `AlgebraicGeometry.Stack.AlgebraicStacks`: its hom
sets sit one universe higher. This is the object that stands in for it. -/
structure QuotientStackModel (i : Iᵒᵖ)
    (Gᵢ : GroupoidInAlgebraicSpaces B S hS (C.stageSpace i)) where
  /-- The algebraic stack over `S` modelling `[U_i/R_i]`. -/
  stack : AlgebraicStacks.{u, w} B S hS
  /-- Its structure 1-morphism to the stage. -/
  structureMorphism : stack ⟶ C.stageStack.{u, w} i
  /-- The identification with the quotient stack, over the stage. -/
  equivOver : BasedCategory.EquivalenceOver (quotientStackToBase Gᵢ)
    structureMorphism.hom.hom

/-- **The universe-lifting datum for a quotient stack.** Every algebraic quotient stack of a
groupoid over a stage has a model in the 2-category of algebraic stacks over `S`.

This is **not a mathematical assumption**: it asserts no property of `[U_i/R_i]` beyond the
algebraicity already supplied, only that the quotient stack can be *replaced* by an object whose
hom sets lie one universe lower. It is needed because stackification raises hom sets:
`AlgebraicGeometry.Stack.quotientStack` is a `CategoryTheory.BasedCategory.{u + 1, u + 1}` while
the objects of `AlgebraicGeometry.Stack.AlgebraicStacks` have hom universe `u`, which is exactly
why `AlgebraicGeometry.Stack.liftedSpaceStack` exists. The library has no universe reduction in
the other direction — Stacks 0457
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_iff_of_equivalences`) transports
representability across an equivalence but produces no small-hom model — and the same datum is
carried for the same reason by `AlgebraicGeometry.Stack.dimension_quotientStack_le`, whose notes
record that `AlgebraicStacks` objects "have their morphisms one universe below those of
`AlgebraicGeometry.Stack.quotientStack`". -/
abbrev StageStackModel : Prop :=
  ∀ (i : Iᵒᵖ) (Gᵢ : GroupoidInAlgebraicSpaces B S hS (C.stageSpace i)),
    IsAlgebraicStack.{u, w} B S hS (quotientStack Gᵢ) →
      Nonempty (C.QuotientStackModel.{u, w} i Gᵢ)

/-- **Stacks 06Q2 for the model of a quotient stack.** The model of the quotient stack of a smooth
groupoid whose object and arrow spaces are of finite presentation over the stage is of finite
presentation over the stage.

Stacks 06Q2 is formalized as `AlgebraicGeometry.Stack.AlgebraicStacks.IsFinitePresentation`, the
universal smooth-diagram test of Stacks 06FM; what is carried is the evaluation of that test on a
quotient stack, which the library performs nowhere. -/
abbrev ModelIsFinitePresentation : Prop :=
  ∀ (i : Iᵒᵖ) (Gᵢ : GroupoidInAlgebraicSpaces B S hS (C.stageSpace i))
    (M : C.QuotientStackModel.{u, w} i Gᵢ),
    GroupoidInAlgebraicSpaces.IsSmooth B S hS Gᵢ →
    Space.IsFinitePresentation B S hS Gᵢ.objectsToBase.hom →
    Space.IsFinitePresentation B S hS Gᵢ.arrowsToBase.hom →
      AlgebraicStacks.IsFinitePresentation B S hS M.structureMorphism

/-- **Stacks 044P, 044R, 046Q and 04Y1 for a base-changed groupoid.** The quotient stack of the
base change of `G_i` along `X ⟶ X_i` is, over `X`, the 2-fibre product of the model of `[U_i/R_i]`
with `X` over `X_i`.

In the source this is the last paragraph of the proof of Stacks 0CN4: the induced map of presheaves
of groupoids is an isomorphism by Stacks 044P and 046Q, and stackification commutes with 2-fibre
products by Stacks 04Y1. Stacks 04Y1 is formalized as
`CategoryTheory.TwoFibreProductOver.isStackification_stackifyMap` and Stacks 046Q as
`AlgebraicGeometry.Stack.quotientStackMap`; what is carried is their combination for
`AlgebraicGeometry.Space.baseChange`. -/
abbrev ModelBaseChangeComparison : Prop :=
  ∀ (i : Iᵒᵖ) (Gᵢ : GroupoidInAlgebraicSpaces B S hS (C.stageSpace i))
    (M : C.QuotientStackModel.{u, w} i Gᵢ),
    Nonempty (BasedCategory.EquivalenceOver
      (quotientStackToBase (Space.baseChange Gᵢ (C.limitProjection i)).groupoid)
      (twoFibreProductSquareAlgebraicStacks.{u, w} B S hS M.structureMorphism
        (C.limitStackProjection.{u, w} i)).snd.hom.hom)

/-- **The three stage-model inputs assembled.** The bundled form the main theorem consumes, which
`AlgebraicGeometry.Stack.StackDescentSystem.stageModelOfSmoothGroupoid` derives from the universe
datum, Stacks 06Q2 and the Stacks 04Y1 comparison, each carried separately. -/
abbrev StageModelOfSmoothGroupoid : Prop :=
  ∀ (i : Iᵒᵖ) (Gᵢ : GroupoidInAlgebraicSpaces B S hS (C.stageSpace i)),
    IsAlgebraicStack.{u, w} B S hS (quotientStack Gᵢ) →
    GroupoidInAlgebraicSpaces.IsSmooth B S hS Gᵢ →
    Space.IsFinitePresentation B S hS Gᵢ.objectsToBase.hom →
    Space.IsFinitePresentation B S hS Gᵢ.arrowsToBase.hom →
    ∃ (𝒳ᵢ : AlgebraicStacks.{u, w} B S hS) (fᵢ : 𝒳ᵢ ⟶ C.stageStack.{u, w} i),
      AlgebraicStacks.IsFinitePresentation B S hS fᵢ ∧
        Nonempty (BasedCategory.EquivalenceOver
          (quotientStackToBase (Space.baseChange Gᵢ (C.limitProjection i)).groupoid)
          (twoFibreProductSquareAlgebraicStacks.{u, w} B S hS fᵢ
            (C.limitStackProjection.{u, w} i)).snd.hom.hom)

/-- The bundled stage-model input follows from the universe datum, Stacks 06Q2 for the model and
the Stacks 04Y1 comparison: nothing is combined beyond choosing the model once and reading the
other two off it. -/
theorem stageModelOfSmoothGroupoid (hModel : C.StageStackModel.{u, w})
    (hFp : C.ModelIsFinitePresentation.{u, w})
    (hComparison : C.ModelBaseChangeComparison.{u, w}) :
    C.StageModelOfSmoothGroupoid.{u, w} := by
  intro i Gᵢ hGᵢalg hGᵢsmooth hGᵢobjects hGᵢarrows
  obtain ⟨M⟩ := hModel i Gᵢ hGᵢalg
  exact ⟨M.stack, M.structureMorphism,
    hFp i Gᵢ M hGᵢsmooth hGᵢobjects hGᵢarrows, hComparison i Gᵢ M⟩

/-- **Stacks 0CN4.** Let `(X_i)` be a directed inverse system of quasi-compact, quasi-separated
algebraic spaces over `S` with affine transition morphisms, and let `X = lim X_i`. If `𝒳` is an
algebraic stack of finite presentation over `X`, then there are a stage `i` and an algebraic
stack `𝒳_i` of finite presentation over `X_i` with `𝒳 ≅ 𝒳_i ×_{X_i} X` as algebraic stacks
over `X`.

Five inputs are carried as explicit hypotheses — `hPresentation`, `hDescent`,
`hStageStackModel`, `hModelFinitePresentation` and `hModelComparison`. None is a restatement of
this conclusion, and `hStageStackModel` is a universe-lifting datum rather than a mathematical
assumption. The module's implementation notes say what each one is, which declaration of the library it
would come from, and — for Stacks 0CN2 — exactly why the existing result falls short. What is
discharged here is Stacks 07SF for the limit with its quasi-compactness and
quasi-separatedness, the essential-surjectivity clause of Stacks 07SK for the object and arrow
spaces of the presenting groupoid, Stacks 04TK on the descended groupoid, and the assembly of the
conclusion. -/
@[stacks 0CN4 "a reduction, not a proof: inputs of the source's proof are carried as the \
explicit hypotheses hPresentation (Stacks 04T4 (4), (5), Stacks 04T5 (2) \
and the 050K/050H bookkeeping, with Stacks 04YC discharged), hDescent (what is left of \
Stacks 07SK and 0CN2 on a groupoid object once the essential-surjectivity clause is \
discharged: the descent of s, t, c, the pointwiseGroupoid field, \
the common stage, and Stacks 046Q), hStageStackModel (a universe-lifting datum, not a \
mathematical assumption: a quotient stack has hom universe one above that of AlgebraicStacks), \
hModelFinitePresentation (Stacks 06Q2 evaluated on a quotient stack) and hModelComparison \
(Stacks 044P, 044R, 046Q and 04Y1 for a base-changed groupoid); what is discharged here is \
Stacks 07SF for the limit with its quasi-compactness and quasi-separatedness, the \
essential-surjectivity clause of Stacks 07SK for the object and arrow spaces of the presenting \
groupoid, Stacks 04TK on the descended groupoid, and the assembly of the conclusion"]
theorem exists_stage_model_of_isFinitePresentation
    (hPresentation : GroupoidPresentationOfAffineSmoothChart.{u, w} B S hS hZ)
    (hDescent : C.GroupoidStructureDescendsToStage)
    (hStageStackModel : C.StageStackModel.{u, w})
    (hModelFinitePresentation : C.ModelIsFinitePresentation.{u, w})
    (hModelComparison : C.ModelBaseChangeComparison.{u, w})
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (f : 𝒳 ⟶ C.limitStack.{u, w})
    (hf : AlgebraicStacks.IsFinitePresentation B S hS f) :
    ∃ (i : Iᵒᵖ) (𝒳ᵢ : AlgebraicStacks.{u, w} B S hS) (fᵢ : 𝒳ᵢ ⟶ C.stageStack.{u, w} i),
      AlgebraicStacks.IsFinitePresentation B S hS fᵢ ∧
        ∃ e : Bicategory.Equivalence 𝒳
          (twoFibreProductAlgebraicStack.{u, w} B S hS fᵢ
            (C.limitStackProjection.{u, w} i)),
          Nonempty (e.hom ≫ (twoFibreProductSquareAlgebraicStacks.{u, w} B S hS fᵢ
            (C.limitStackProjection.{u, w} i)).snd ≅ f) := by
  obtain ⟨P⟩ := hasSmoothPresentationOverBase.{u, w} B S hS hZ hPresentation
    C.limitSpace C.limit_quasiCompact C.limit_quasiSeparated 𝒳 f hf
  obtain ⟨i, Gᵢ, hGᵢsmooth, hGᵢobjects, hGᵢarrows, ⟨eDescent⟩⟩ :=
    C.smoothGroupoidDescendsToStage hDescent P.groupoid P.isSmooth
      P.objects_finitePresentation P.arrows_finitePresentation
  have hGᵢalgebraic : IsAlgebraicStack.{u, w} B S hS (quotientStack Gᵢ) :=
    isAlgebraicStack_quotientStack_of_isSmooth hGᵢsmooth
  obtain ⟨𝒳ᵢ, fᵢ, hfᵢ, ⟨eModel⟩⟩ :=
    C.stageModelOfSmoothGroupoid hStageStackModel hModelFinitePresentation hModelComparison
      i Gᵢ hGᵢalgebraic hGᵢsmooth hGᵢobjects hGᵢarrows
  have e := (P.equivOver.trans eDescent).trans eModel
  exact ⟨i, 𝒳ᵢ, fᵢ, hfᵢ, equivalenceOfBasedEquivalence.{u, w} B S hS e.equiv,
    ⟨isoMkAlgebraicStacks.{u, w} B S hS e.compIso⟩⟩

end StackDescentSystem

end AlgebraicGeometry.Stack

end
