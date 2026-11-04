module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorDescent
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorLimits
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientRestrictOver
-- the proofs of the descent inputs of Stacks 08IV; nothing of these appears in a statement here
import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPullbackStability
import StacksFrontier.AlgebraicGeometry.Quot.QuotientDescentClauses
import StacksFrontier.AlgebraicGeometry.Spaces.InverseImageLocalPresentations

/-!
# The functor of quotients is a sheaf in the source (Stacks 08IV)

In Situation 082M — a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` of a big fppf
site together with a quasi-coherent `𝒪_X`-module `F` — let `{X i ⟶ X}` be an fpqc covering and
for each pair `i, j` let `{X ijk ⟶ X i ×_X X j}` be an fpqc covering.  Write `F i`, resp.
`F ijk`, for the pullback of `F` to `X i`, resp. `X ijk`.  Stacks 08IV asserts that for every
scheme `T` over `Y` the diagram

`Q_{F/X/Y}(T) ⟶ ∏_i Q_{F i/X i/Y}(T) ⇉ ∏_{ijk} Q_{F ijk/X ijk/Y}(T)`

"presents the first arrow as the equalizer of the other two", the two maps being `pr₀^*` and
`pr₁^*`, and that the same is true for the subfunctor `Q^{fp}_{F/X/Y}`.

An equalizer of sets is a bijection onto the subset where the two maps agree, so that is the
form in which the conclusion is stated here:
`AlgebraicGeometry.Space.QuotientSituation.bijOn_restrictQuotientToMember` says that
restriction is a bijection from `Q_{F/X/Y}(T)` onto the set of families `(Q i)` of elements of
`Q_{F i/X i/Y}(T)` whose two restrictions to `X ijk` agree, and
`AlgebraicGeometry.Space.QuotientSituation.bijOn_restrictQuotientToMember_finitePresentation`
says the same for `Q^{fp}`.  Being a bijection onto that set contains all three assertions of
the source: the restriction maps land in the set — which is the commutativity
`pr₀^* ∘ res = pr₁^* ∘ res` — restriction is injective, and every compatible family is the
family of restrictions of a quotient.

## Main definitions

* `AlgebraicGeometry.Space.QuotientSituation.sourceRestricted`: **Situation 082M on a member of
  a covering of the source** — the standing data `(W, a ≫ f, a^*F)` obtained from a morphism
  `a : W ⟶ X`.  Its functor of quotients is the source's `Q_{F i/X i/Y}`.
* `AlgebraicGeometry.Space.QuotientSituation.restrictQuotientToMember`: the first arrow of the
  diagram, at one member of the covering.
* `AlgebraicGeometry.Space.QuotientSituation.restrictQuotientBetweenMembers`: the two arrows
  `pr₀^*` and `pr₁^*` of the diagram, at one member of a refining covering.

## Main results

* `AlgebraicGeometry.Space.QuotientSituation.restrictQuotientBetweenMembers_toMember`: the two
  arrows of the diagram agree on the image of the first, because both composites are
  restriction along the single morphism `X ijk ⟶ X`.  This is the commutativity of the diagram
  of the source.
* `AlgebraicGeometry.Space.QuotientSituation.restrictQuotientToMember_mem_quotients` and its
  companion `restrictQuotientToMember_mem_finitePresentationQuotients`: the first arrow is well
  defined, that is, lands in the quotient functors of the members.
* `AlgebraicGeometry.Space.QuotientSituation.eq_of_restrictQuotientToMember_eq`: the first
  arrow is injective.
* `AlgebraicGeometry.Space.QuotientSituation.restrictQuotientBetweenMembers_eq_of_refinement`:
  agreement of two quotients on a refining covering of a fibre product upgrades to agreement on
  the fibre product itself.  This is the step of Remark 08IT that consumes the refining
  coverings.
* `AlgebraicGeometry.Space.QuotientSituation.exists_mem_quotients_restrictQuotientToMember_eq`:
  every matching family is the family of restrictions of a quotient, that is, the first arrow is
  surjective onto the equalizer.
* `AlgebraicGeometry.Space.QuotientSituation.bijOn_restrictQuotientToMember`: **Stacks 08IV**
  for `Q_{F/X/Y}`.
* `AlgebraicGeometry.Space.QuotientSituation.bijOn_restrictQuotientToMember_finitePresentation`:
  **Stacks 08IV** for `Q^{fp}_{F/X/Y}`.

## Implementation notes

**Why the restriction maps are normalised.**  The module `F ijk` of the source is *the pullback
of `F` to `X ijk`*, and the two arrows `pr₀^*` and `pr₁^*` of the diagram reach it along the two
paths `X ijk ⟶ X i ⟶ X` and `X ijk ⟶ X j ⟶ X`.  Those two paths are the *same* morphism
`X ijk ⟶ X`, but the two iterated inverse images of `F` along them are only canonically
isomorphic, so a restriction map defined as an iterated inverse image makes the commutativity of
the diagram a coherence of the pseudofunctoriality of Stacks 03LU rather than an identity.
`AlgebraicGeometry.Space.quotientRestrictOver` of
`StacksFrontier/AlgebraicGeometry/Quot/QuotientRestrictOver.lean` therefore records a quotient on a
node
`a : W ⟶ X` as a subobject of the *single* inverse image `a^*F`, and restricts along
`g : W' ⟶ W` by conjugating with the comparison `a'^*F ≅ g^*a^*F` of Stacks 03LU; its
transitivity, `AlgebraicGeometry.Space.quotientRestrictOver_comp`, is the associativity
coherence of that comparison, and the commutativity of the diagram is then the single statement
that the two composite morphisms `X ijk,T ⟶ X_T` are equal, which
`AlgebraicGeometry.Space.baseChangeAlong_comp` provides.  Translating between a subobject of
`a^*F` and a subobject of the base-change module of
`AlgebraicGeometry.Space.QuotientSituation.sourceRestricted` is
`CategoryTheory.Limits.quotientTransport`, which is a bijection.

**What is proved and what is carried.**  The source's proof is three citations: Remark 08IT
(the bijection of Stacks 08IU, which is fpqc descent of quasi-coherent modules) produces a
quasi-coherent quotient `F_T ⟶ Q` restricting to the given family, Morphisms of Spaces,
Lemma 05VY makes `Q` flat over `T`, and Descent on Spaces, Lemma 060V makes it of finite
presentation.  All three, and everything the proof needs besides, are available in this
development, so **nothing is assumed**: the two main results below carry no hypothesis beyond
Situation 082M and the two coverings.  Where each input comes from:

* *The injectivity of the first arrow* is
  `AlgebraicGeometry.Space.eq_of_quotientRestrictOver_eq`, which is the injectivity half of
  Stacks 08IU proved in `StacksFrontier/AlgebraicGeometry/Quot/QuotientFunctorDescent.lean`.  Its
  faithfulness clause of Stacks 04W8 is
  `AlgebraicGeometry.Space.reflectsZeroAlongFpqcCovering` and its kernel clause of Stacks 03DO
  is `AlgebraicGeometry.Space.kernelQuasicoherent`, both of
  `StacksFrontier/AlgebraicGeometry/Quot/QuotientDescentClauses.lean`.
* *The commutativity of the diagram* is proved here from the pseudofunctoriality of Stacks 03LU,
  `AlgebraicGeometry.Space.modulePushforwardCoherence`.
* *The step of Remark 08IT that consumes the refining coverings* is proved here: the agreement
  of two members of a compatible family on `X ijk,T` is upgraded to their agreement on the
  fibre product `X i,T ×_{X_T} X j,T` by the same injectivity along the base change of
  `{X ijk ⟶ X i ×_X X j}`.  This is why the descent input is stated with the agreement
  condition on the fibre product, in the shape a descent datum has, and not with the refining
  coverings already folded in.
* *The base change of the two coverings to `T`* is proved in
  `StacksFrontier/AlgebraicGeometry/Quot/QuotientRestrictOver.lean`,
  `AlgebraicGeometry.Space.isFpqcCovering_baseChangeAlong`, from Stacks 03MO for flatness,
  `AlgebraicGeometry.Space.isFlat_isStableUnderBaseChange`, and the universal property of the
  base change for the affine refinements of Stacks 03MQ.
* *The rest of Remark 08IT* — that a descent datum of quasi-coherent quotients is effective and
  that the descended homomorphism is surjective — is
  `AlgebraicGeometry.Space.descendsQuotientsAlongFpqcCovering_of_isQuasicoherentOnSite'`.  That
  is the conclusion of `AlgebraicGeometry.Space.DescendsQuotientsAlongFpqcCovering` for a
  *quasi-coherent* module, which is all that is needed here: the module being descended is
  `D.F`, and `D.quasicoherent` is part of Situation 082M.  The predicate itself quantifies over
  every module, quasi-coherent or not, and in that generality is not proved.
* *Stacks 05VY for modules* is `AlgebraicGeometry.Space.flatOverDescendsAlongFpqcCovering`.
* *Stacks 060V* for `SheafOfModules.IsFinitePresentationOnSite`, the predicate Situation 082M's
  subfunctor `Q^{fp}` is cut out by, is
  `AlgebraicGeometry.Space.finitePresentationOnSiteDescendsAlongFpqcCovering`.
* *Stacks 03GA for the restriction maps* is
  `AlgebraicGeometry.Space.hasLocalInverseImagePresentations`, which holds along an arbitrary
  morphism of algebraic spaces, and *Stacks 05VW* is
  `AlgebraicGeometry.Space.isFlatOver_modulePullback_of_isFlat`, which asks the morphism to be
  flat — and the members of an fpqc covering are.  This is why
  `AlgebraicGeometry.Space.QuotientSituation.restrictQuotientToMember_mem_quotients` takes the
  flatness of the member rather than `AlgebraicGeometry.Space.FlatOverPullbackOver`, which
  asserts Stacks 05VW for an arbitrary morphism and in that generality is not proved.
  Preservation of finite presentation is
  `AlgebraicGeometry.Space.isFinitePresentationOnSite_modulePullback`.

The predicates naming these inputs —
`AlgebraicGeometry.Space.PullbackPreservesQuasicoherenceEverywhere`,
`AlgebraicGeometry.Space.KernelQuasicoherent`,
`AlgebraicGeometry.Space.FlatOverPullbackOver`,
`AlgebraicGeometry.Space.FlatOverDescendsAlongFpqcCovering`,
`AlgebraicGeometry.Space.FinitePresentationOnSiteDescendsAlongFpqcCovering` and
`AlgebraicGeometry.Space.DescendsQuotientsAlongFpqcCovering` — live in
`StacksFrontier/AlgebraicGeometry/Quot/QuotientRestrictOver.lean`.  The auxiliary results below
still take some of them as hypotheses; the two main results discharge every one.

## References

* [Stacks Project, Tag 08IV](https://stacks.math.columbia.edu/tag/08IV)
* [Stacks Project, Tag 082M](https://stacks.math.columbia.edu/tag/082M)
* [Stacks Project, Tag 08IU](https://stacks.math.columbia.edu/tag/08IU)
* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
* [Stacks Project, Tag 05VY](https://stacks.math.columbia.edu/tag/05VY)
* [Stacks Project, Tag 060V](https://stacks.math.columbia.edu/tag/060V)
* [Stacks Project, Tag 03MQ](https://stacks.math.columbia.edu/tag/03MQ)
* [Stacks Project, Tag 03MO](https://stacks.math.columbia.edu/tag/03MO)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso

namespace AlgebraicGeometry.Space

universe u v w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotientSituation

variable (D : QuotientSituation B S hS)

/-! ### Situation 082M on a member of a covering of the source -/

/-- **Stacks 03GA for the module of a quotient situation.**  The inverse image of `F` along any
morphism `a : W ⟶ X` of algebraic spaces is quasi-coherent, with no hypothesis on `a`. -/
theorem isQuasicoherentOnSite_modulePullback_F {W : AlgebraicSpaces B S hS} (a : W ⟶ D.X) :
    ((modulePullback B S hS a).obj D.F).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS a D.F D.quasicoherent

/-- **Situation 082M on a member of a covering of the source.**  For a morphism
`a : W ⟶ X` of algebraic spaces, the standing data consisting of `W`, the composite
`a ≫ f : W ⟶ Y` and the pullback `a^*F` of the module.

Its functor of quotients is the source's `Q_{F i/X i/Y}` when `a` is a member of a covering of
`X`, and the source's `Q_{F ijk/X ijk/Y}` when `a` is the composite `X ijk ⟶ X i ×_X X j ⟶ X`:
in both cases the module is *the* pullback of `F` to the member, which is what the source
writes.

Quasi-coherence of `a^*F` is Stacks 03GA, which holds along an arbitrary morphism of algebraic
spaces by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite` of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePullbackQuasicoherentFromChartDiagrams.lean`, so no
local-presentation hypothesis on `a` is asked for.

It is made reducible below so that the identifications `(D.sourceRestricted a).Y = D.Y` and
`(D.sourceRestricted a).f = a ≫ D.f`, on which the types of the restriction maps below depend,
are available to the unifier. -/
@[stacks 082M "the standing data on a member of a covering of the source"]
def sourceRestricted {W : AlgebraicSpaces B S hS} (a : W ⟶ D.X) :
    QuotientSituation B S hS where
  X := W
  Y := D.Y
  f := a ≫ D.f
  F := (modulePullback B S hS a).obj D.F
  quasicoherent := D.isQuasicoherentOnSite_modulePullback_F a

attribute [reducible] sourceRestricted

/-- The structure morphism of a node of a covering diagram of the source, read on base
changes. -/
theorem sourceRestricted_comp_f {W W' : AlgebraicSpaces B S hS} {a : W ⟶ D.X} {a' : W' ⟶ D.X}
    (b : W' ⟶ W) (hb : b ≫ a = a') : b ≫ (a ≫ D.f) = a' ≫ D.f := by
  rw [← Category.assoc, hb]

/-- The canonical morphism `W_T ⟶ X` from the base change of a node `a : W ⟶ X` of a covering
diagram of the source: the projection to `W` followed by `a`.  The module `a^*F` of
`AlgebraicGeometry.Space.QuotientSituation.sourceRestricted` pulls back along the projection to
the inverse image of `F` along this morphism, which is
`AlgebraicGeometry.Space.QuotientSituation.sourceNodeIso`. -/
def sourceNodeMap {W : AlgebraicSpaces B S hS} (a : W ⟶ D.X) (T : SchemesOver D.Y) :
    baseChangeSpace (a ≫ D.f) T ⟶ D.X :=
  baseChangeProjection (a ≫ D.f) T ≫ a

/-- The comparison of Stacks 03LU identifying the base-change module of
`AlgebraicGeometry.Space.QuotientSituation.sourceRestricted` with the inverse image of `F`
along `AlgebraicGeometry.Space.QuotientSituation.sourceNodeMap`. -/
def sourceNodeIso {W : AlgebraicSpaces B S hS} (a : W ⟶ D.X) (T : SchemesOver D.Y) :
    (D.sourceRestricted a).baseChangeModule T ≅
      (modulePullback B S hS (D.sourceNodeMap a T)).obj D.F :=
  ((modulePullbackTriangle B S hS
    (rfl : baseChangeProjection (a ≫ D.f) T ≫ a = D.sourceNodeMap a T)).app D.F).symm

/-- The base change of a node of a covering diagram of the source maps to the base change of
the source compatibly with the canonical morphisms to `X`. -/
theorem baseChangeAlong_comp_sourceProjection {W : AlgebraicSpaces B S hS} (a : W ⟶ D.X)
    (T : SchemesOver D.Y) :
    baseChangeAlong a (rfl : a ≫ D.f = a ≫ D.f) T ≫ D.sourceProjection T =
      D.sourceNodeMap a T :=
  baseChangeAlong_comp_projection a rfl T

/-- The base change of a morphism of nodes of a covering diagram of the source is compatible
with the canonical morphisms to `X`. -/
theorem baseChangeAlong_comp_sourceNodeMap {W W' : AlgebraicSpaces B S hS} {a : W ⟶ D.X}
    {a' : W' ⟶ D.X} (b : W' ⟶ W) (hb : b ≫ a = a') (T : SchemesOver D.Y) :
    baseChangeAlong b (D.sourceRestricted_comp_f b hb) T ≫ D.sourceNodeMap a T =
      D.sourceNodeMap a' T := by
  simp only [sourceNodeMap, ← Category.assoc, baseChangeAlong_comp_projection]
  rw [Category.assoc, hb]

/-! ### The three arrows of the diagram -/

/-- **The first arrow of the diagram of Stacks 08IV, at one node.**  The restriction of a
quotient in `Q_{F/X/Y}(T)` to the member `W` of a covering of the source: the inverse image of
the quotient along `W_T ⟶ X_T`, recorded by its kernel. -/
def restrictQuotientToMember {W : AlgebraicSpaces B S hS} (a : W ⟶ D.X) (T : SchemesOver D.Y)
    (K : Subobject (D.baseChangeModule T)) :
    Subobject ((D.sourceRestricted a).baseChangeModule T) :=
  quotientTransport (D.sourceNodeIso a T)
    (quotientRestrictOver (baseChangeAlong a (rfl : a ≫ D.f = a ≫ D.f) T)
      (D.baseChangeAlong_comp_sourceProjection a T) D.F K)

/-- The quotient by the restriction to a member is the inverse image of the quotient. -/
def restrictQuotientToMemberCokernelIso {W : AlgebraicSpaces B S hS} (a : W ⟶ D.X)
    (T : SchemesOver D.Y) (K : Subobject (D.baseChangeModule T)) :
    (D.sourceRestricted a).quotientModule T (D.restrictQuotientToMember a T K) ≅
      (modulePullback B S hS (baseChangeAlong a (rfl : a ≫ D.f = a ≫ D.f) T)).obj
        (D.quotientModule T K) :=
  quotientTransportCokernelIso _ _ ≪≫ quotientRestrictOverCokernelIso _ _ _ _

/-- **The restriction to a member, read on the single inverse image of `F`.**  Undoing the
comparison of Stacks 03LU that normalises the restriction map leaves the restriction of the
quotient along the morphism `W_T ⟶ X_T` of base changes. -/
theorem quotientTransport_sourceNodeIso_symm_restrictQuotientToMember
    {W : AlgebraicSpaces B S hS} (a : W ⟶ D.X) (T : SchemesOver D.Y)
    (K : Subobject (D.baseChangeModule T)) :
    quotientTransport (D.sourceNodeIso a T).symm (D.restrictQuotientToMember a T K) =
      quotientRestrictOver (baseChangeAlong a (rfl : a ≫ D.f = a ≫ D.f) T)
        (D.baseChangeAlong_comp_sourceProjection a T) D.F K :=
  quotientTransport_symm_quotientTransport (D.sourceNodeIso a T) _

/-- **The two other arrows of the diagram of Stacks 08IV, at one node.**  The restriction of a
quotient in `Q_{F i/X i/Y}(T)` along a morphism `b : W' ⟶ W` of members of coverings of the
source, that is, the inverse image of the quotient along `W'_T ⟶ W_T`.

Taking `b` to be `X ijk ⟶ X i ×_X X j ⟶ X i` gives `pr₀^*` and taking it to be
`X ijk ⟶ X i ×_X X j ⟶ X j` gives `pr₁^*`. -/
def restrictQuotientBetweenMembers {W W' : AlgebraicSpaces B S hS} {a : W ⟶ D.X}
    {a' : W' ⟶ D.X} (b : W' ⟶ W) (hb : b ≫ a = a') (T : SchemesOver D.Y)
    (K : Subobject ((D.sourceRestricted a).baseChangeModule T)) :
    Subobject ((D.sourceRestricted a').baseChangeModule T) :=
  quotientTransport (D.sourceNodeIso a' T)
    (quotientRestrictOver (baseChangeAlong b (D.sourceRestricted_comp_f b hb) T)
      (D.baseChangeAlong_comp_sourceNodeMap b hb T) D.F
      (quotientTransport (D.sourceNodeIso a T).symm K))

/-- The quotient by the restriction along a morphism of members is the inverse image of the
quotient. -/
def restrictQuotientBetweenMembersCokernelIso {W W' : AlgebraicSpaces B S hS} {a : W ⟶ D.X}
    {a' : W' ⟶ D.X} (b : W' ⟶ W) (hb : b ≫ a = a') (T : SchemesOver D.Y)
    (K : Subobject ((D.sourceRestricted a).baseChangeModule T)) :
    (D.sourceRestricted a').quotientModule T
        (D.restrictQuotientBetweenMembers b hb T K) ≅
      (modulePullback B S hS (baseChangeAlong b (D.sourceRestricted_comp_f b hb) T)).obj
        ((D.sourceRestricted a).quotientModule T K) :=
  quotientTransportCokernelIso _ _ ≪≫ quotientRestrictOverCokernelIso _ _ _ _ ≪≫
    (modulePullback B S hS _).mapIso (quotientTransportCokernelIso _ _)

/-- **The restriction along a morphism of members, read on the single inverse image of `F`.**
Undoing the comparison of Stacks 03LU that normalises the restriction map leaves the restriction
of the quotient along the morphism `W'_T ⟶ W_T` of base changes. -/
theorem quotientTransport_sourceNodeIso_symm_restrictQuotientBetweenMembers
    {W W' : AlgebraicSpaces B S hS} {a : W ⟶ D.X} {a' : W' ⟶ D.X} (b : W' ⟶ W)
    (hb : b ≫ a = a') (T : SchemesOver D.Y)
    (K : Subobject ((D.sourceRestricted a).baseChangeModule T)) :
    quotientTransport (D.sourceNodeIso a' T).symm
        (D.restrictQuotientBetweenMembers b hb T K) =
      quotientRestrictOver (baseChangeAlong b (D.sourceRestricted_comp_f b hb) T)
        (D.baseChangeAlong_comp_sourceNodeMap b hb T) D.F
        (quotientTransport (D.sourceNodeIso a T).symm K) :=
  quotientTransport_symm_quotientTransport (D.sourceNodeIso a' T) _

/-- **The diagram of Stacks 08IV commutes.**  Restricting a quotient in `Q_{F/X/Y}(T)` to a
member `W` of a covering of the source and then along a morphism `b : W' ⟶ W` of members is
restricting it to `W'` directly.

Applied to the two morphisms `X ijk ⟶ X i` and `X ijk ⟶ X j` this says that `pr₀^*` and `pr₁^*`
agree on the image of the first arrow: both composites are restriction to `X ijk` along the
*single* morphism `X ijk ⟶ X`, because the two paths through `X i` and through `X j` are the
same morphism. -/
theorem restrictQuotientBetweenMembers_toMember (hc : ModulePushforwardCoherence B S hS)
    {W W' : AlgebraicSpaces B S hS} {a : W ⟶ D.X} {a' : W' ⟶ D.X} (b : W' ⟶ W)
    (hb : b ≫ a = a') (T : SchemesOver D.Y)
    (K : Subobject (D.baseChangeModule T)) :
    D.restrictQuotientBetweenMembers b hb T (D.restrictQuotientToMember a T K) =
      D.restrictQuotientToMember a' T K :=
  congrArg (quotientTransport (D.sourceNodeIso a' T))
    ((congrArg (quotientRestrictOver (baseChangeAlong b (D.sourceRestricted_comp_f b hb) T)
        (D.baseChangeAlong_comp_sourceNodeMap b hb T) D.F)
        (D.quotientTransport_sourceNodeIso_symm_restrictQuotientToMember a T K)).trans
      (quotientRestrictOver_comp hc
        (baseChangeAlong_comp hb (rfl : a ≫ D.f = a ≫ D.f)
          (D.sourceRestricted_comp_f b hb) (rfl : a' ≫ D.f = a' ≫ D.f) T)
        (D.baseChangeAlong_comp_sourceProjection a T)
        (D.baseChangeAlong_comp_sourceNodeMap b hb T)
        (D.baseChangeAlong_comp_sourceProjection a' T) D.F K))

/-! ### The restriction maps land in the quotient functors -/

/-- The restriction to a member of a covering of the source of an element of `Q_{F/X/Y}(T)` is
an element of `Q_{F i/X i/Y}(T)`.  This is the well-definedness of the first arrow of the
diagram.

The quotient module stays quasi-coherent by Stacks 03GA, which holds along an arbitrary
morphism of algebraic spaces, and it stays flat over `T` because the base change `W_T ⟶ X_T` of
a flat `a` is flat (Stacks 03MO) and the inverse image of a quasi-coherent module flat over `T`
along a flat morphism over `T` is flat over `T` (Stacks 05VW for a flat morphism). -/
theorem restrictQuotientToMember_mem_quotients {W : AlgebraicSpaces B S hS} (a : W ⟶ D.X)
    (haf : IsFlat B S hS a.hom)
    (T : SchemesOver D.Y) {K : Subobject (D.baseChangeModule T)} (hK : K ∈ D.quotients T) :
    D.restrictQuotientToMember a T K ∈ (D.sourceRestricted a).quotients T := by
  refine ⟨SheafOfModules.IsQuasicoherentOnSite.of_iso
    (D.restrictQuotientToMemberCokernelIso a T K).symm
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ _ hK.1), ?_⟩
  exact IsFlatOver.of_iso B S hS _ (D.restrictQuotientToMemberCokernelIso a T K).symm
    (isFlatOver_modulePullback_of_isFlat B S hS
      (baseChangeAlong a (rfl : a ≫ D.f = a ≫ D.f) T)
      ((isFlat_isStableUnderBaseChange B S hS).of_isPullback
        (isPullback_baseChangeAlong a rfl T) haf)
      (baseChangeAlong_comp_inclusion a rfl T) _ hK.1 hK.2)

/-- The restriction to a member of a covering of the source of an element of
`Q^{fp}_{F/X/Y}(T)` is an element of `Q^{fp}_{F i/X i/Y}(T)`. -/
theorem restrictQuotientToMember_mem_finitePresentationQuotients
    {W : AlgebraicSpaces B S hS} (a : W ⟶ D.X) (haf : IsFlat B S hS a.hom) (T : SchemesOver D.Y)
    {K : Subobject (D.baseChangeModule T)} (hK : K ∈ D.finitePresentationQuotients T) :
    D.restrictQuotientToMember a T K ∈
      (D.sourceRestricted a).finitePresentationQuotients T :=
  ⟨D.restrictQuotientToMember_mem_quotients a haf T hK.1,
    SheafOfModules.IsFinitePresentationOnSite.of_iso
      (D.restrictQuotientToMemberCokernelIso a T K).symm
      (isFinitePresentationOnSite_modulePullback B S hS _ _ hK.2)⟩

/-! ### Injectivity of the first arrow -/

/-- **A quotient is determined by its restrictions to the members of a covering of the
source.**  This is the injectivity of the first arrow of the diagram of Stacks 08IV: two
elements of `Q_{F/X/Y}(T)` whose restrictions to every member of an fpqc covering of the source
agree are equal.

This is the injectivity half of Stacks 08IU, read through the normalised restriction maps on the
base change of the covering, so it carries what that half carries: the faithfulness clause of
Stacks 04W8, Stacks 03GA and the kernel clause of Stacks 03DO. -/
theorem eq_of_restrictQuotientToMember_eq
    (hfaith : ReflectsZeroAlongFpqcCovering.{u, v} B S hS)
    (hker : KernelQuasicoherent B S hS) {I : Type v} {W : I → AlgebraicSpaces B S hS}
    (a : ∀ i, W i ⟶ D.X) (hcov : IsFpqcCovering B S hS fun i ↦ (a i).hom)
    (T : SchemesOver D.Y) {K K' : Subobject (D.baseChangeModule T)}
    (hK : K ∈ D.quotients T) (hK' : K' ∈ D.quotients T)
    (h : ∀ i, D.restrictQuotientToMember (a i) T K =
      D.restrictQuotientToMember (a i) T K') : K = K' :=
  have hF : (D.baseChangeModule T).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      (D.sourceProjection T) D.F D.quasicoherent
  eq_of_quotientRestrictOver_eq hfaith
    (fun i ↦ baseChangeAlong (a i) (rfl : a i ≫ D.f = a i ≫ D.f) T)
    (fun i ↦ D.baseChangeAlong_comp_sourceProjection (a i) T)
    (isFpqcCovering_baseChangeAlong a (fun i ↦ (rfl : a i ≫ D.f = a i ≫ D.f)) hcov T) D.F
    (hker _ hF K hK.1) (hker _ hF K' hK'.1) hK.1 hK'.1 fun i ↦
      (D.quotientTransport_sourceNodeIso_symm_restrictQuotientToMember (a i) T K).symm.trans
        ((congrArg (quotientTransport (D.sourceNodeIso (a i) T).symm) (h i)).trans
          (D.quotientTransport_sourceNodeIso_symm_restrictQuotientToMember (a i) T K'))

/-! ### From a matching family to a quotient -/

/-- Two restrictions along morphisms of members agree iff they agree on the single inverse
image of `F`. -/
private theorem restrictQuotientBetweenMembers_eq_iff {W₁ W₂ W' : AlgebraicSpaces B S hS}
    {a₁ : W₁ ⟶ D.X} {a₂ : W₂ ⟶ D.X} {a' : W' ⟶ D.X} {b₁ : W' ⟶ W₁} {b₂ : W' ⟶ W₂}
    (hb₁ : b₁ ≫ a₁ = a') (hb₂ : b₂ ≫ a₂ = a') (T : SchemesOver D.Y)
    (Q₁ : Subobject ((D.sourceRestricted a₁).baseChangeModule T))
    (Q₂ : Subobject ((D.sourceRestricted a₂).baseChangeModule T)) :
    D.restrictQuotientBetweenMembers b₁ hb₁ T Q₁ = D.restrictQuotientBetweenMembers b₂ hb₂ T Q₂ ↔
      quotientRestrictOver (baseChangeAlong b₁ (D.sourceRestricted_comp_f b₁ hb₁) T)
          (D.baseChangeAlong_comp_sourceNodeMap b₁ hb₁ T) D.F
          (quotientTransport (D.sourceNodeIso a₁ T).symm Q₁) =
        quotientRestrictOver (baseChangeAlong b₂ (D.sourceRestricted_comp_f b₂ hb₂) T)
          (D.baseChangeAlong_comp_sourceNodeMap b₂ hb₂ T) D.F
          (quotientTransport (D.sourceNodeIso a₂ T).symm Q₂) := by
  rw [← (quotientTransport_injective (D.sourceNodeIso a' T).symm).eq_iff,
    D.quotientTransport_sourceNodeIso_symm_restrictQuotientBetweenMembers,
    D.quotientTransport_sourceNodeIso_symm_restrictQuotientBetweenMembers]

/-- Restricting along `c` and then along `q` is restricting along `q ≫ c`, on the single inverse
image of `F`. -/
private theorem quotientRestrictOver_comp_sourceNodeMap (hc : ModulePushforwardCoherence B S hS)
    {W P Z : AlgebraicSpaces B S hS} {a : W ⟶ D.X} {c : P ⟶ W} {q : Z ⟶ P} {d : P ⟶ D.X}
    {e : Z ⟶ D.X} (hd : c ≫ a = d) (hq : q ≫ d = e) (he : (q ≫ c) ≫ a = e) (T : SchemesOver D.Y)
    (K : Subobject ((modulePullback B S hS (D.sourceNodeMap a T)).obj D.F)) :
    quotientRestrictOver (baseChangeAlong q (D.sourceRestricted_comp_f q hq) T)
        (D.baseChangeAlong_comp_sourceNodeMap q hq T) D.F
        (quotientRestrictOver (baseChangeAlong c (D.sourceRestricted_comp_f c hd) T)
          (D.baseChangeAlong_comp_sourceNodeMap c hd T) D.F K) =
      quotientRestrictOver (baseChangeAlong (q ≫ c) (D.sourceRestricted_comp_f (q ≫ c) he) T)
        (D.baseChangeAlong_comp_sourceNodeMap (q ≫ c) he T) D.F K :=
  quotientRestrictOver_comp hc
    (baseChangeAlong_comp (rfl : q ≫ c = q ≫ c) (D.sourceRestricted_comp_f c hd)
      (D.sourceRestricted_comp_f q hq) (D.sourceRestricted_comp_f (q ≫ c) he) T)
    (D.baseChangeAlong_comp_sourceNodeMap c hd T) (D.baseChangeAlong_comp_sourceNodeMap q hq T)
    (D.baseChangeAlong_comp_sourceNodeMap (q ≫ c) he T) D.F K

/-- **Agreement on a refining covering upgrades to agreement on the fibre product.**  Let `W₁`
and `W₂` be members of a covering of the source and let `P` sit over both; two quotients on `W₁`
and `W₂` whose restrictions along `Z k ⟶ W₁` and `Z k ⟶ W₂` agree for every member of an fpqc
covering `{Z k ⟶ P}` have the same restriction along `P ⟶ W₁` and `P ⟶ W₂`.

This is the step of Remark 08IT that consumes the refining coverings `{X ijk ⟶ X i ×_X X j}` of
Stacks 08IV: the two restrictions to `P_T` are compared by the injectivity of Stacks 08IU along
the base change of `{Z k ⟶ P}`, so this carries the faithfulness clause of Stacks 04W8,
Stacks 03GA, the kernel clause of Stacks 03DO and the pseudofunctoriality of Stacks 03LU. -/
theorem restrictQuotientBetweenMembers_eq_of_refinement
    (hc : ModulePushforwardCoherence B S hS)
    (hfaith : ReflectsZeroAlongFpqcCovering.{u, v} B S hS)
    (hqc : PullbackPreservesQuasicoherenceEverywhere B S hS)
    (hker : KernelQuasicoherent B S hS) {κ : Type v} {W₁ W₂ P : AlgebraicSpaces B S hS}
    {Z : κ → AlgebraicSpaces B S hS} {a₁ : W₁ ⟶ D.X} {a₂ : W₂ ⟶ D.X} {c₁ : P ⟶ W₁}
    {c₂ : P ⟶ W₂} {d : P ⟶ D.X} {e : ∀ k, Z k ⟶ D.X} (q : ∀ k, Z k ⟶ P)
    (hd₁ : c₁ ≫ a₁ = d) (hd₂ : c₂ ≫ a₂ = d) (he₁ : ∀ k, (q k ≫ c₁) ≫ a₁ = e k)
    (he₂ : ∀ k, (q k ≫ c₂) ≫ a₂ = e k)
    (hcov : IsFpqcCovering B S hS fun k ↦ (q k).hom) (T : SchemesOver D.Y)
    {Q₁ : Subobject ((D.sourceRestricted a₁).baseChangeModule T)}
    {Q₂ : Subobject ((D.sourceRestricted a₂).baseChangeModule T)}
    (hQ₁ : ((D.sourceRestricted a₁).quotientModule T Q₁).IsQuasicoherentOnSite)
    (hQ₂ : ((D.sourceRestricted a₂).quotientModule T Q₂).IsQuasicoherentOnSite)
    (h : ∀ k, D.restrictQuotientBetweenMembers (q k ≫ c₁) (he₁ k) T Q₁ =
      D.restrictQuotientBetweenMembers (q k ≫ c₂) (he₂ k) T Q₂) :
    D.restrictQuotientBetweenMembers c₁ hd₁ T Q₁ =
      D.restrictQuotientBetweenMembers c₂ hd₂ T Q₂ := by
  have hq : ∀ k, q k ≫ d = e k := fun k ↦ by rw [← hd₁, ← Category.assoc, he₁]
  have hamb : ((modulePullback B S hS (D.sourceNodeMap d T)).obj D.F).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      (D.sourceNodeMap d T) D.F D.quasicoherent
  have hcok₁ := isQuasicoherentOnSite_cokernel_quotientRestrictOver hqc
    (baseChangeAlong c₁ (D.sourceRestricted_comp_f c₁ hd₁) T)
    (D.baseChangeAlong_comp_sourceNodeMap c₁ hd₁ T) D.F
    (isQuasicoherentOnSite_cokernel_quotientTransport (D.sourceNodeIso a₁ T).symm hQ₁)
  have hcok₂ := isQuasicoherentOnSite_cokernel_quotientRestrictOver hqc
    (baseChangeAlong c₂ (D.sourceRestricted_comp_f c₂ hd₂) T)
    (D.baseChangeAlong_comp_sourceNodeMap c₂ hd₂ T) D.F
    (isQuasicoherentOnSite_cokernel_quotientTransport (D.sourceNodeIso a₂ T).symm hQ₂)
  refine (D.restrictQuotientBetweenMembers_eq_iff hd₁ hd₂ T Q₁ Q₂).2 ?_
  refine eq_of_quotientRestrictOver_eq hfaith
    (fun k ↦ baseChangeAlong (q k) (D.sourceRestricted_comp_f (q k) (hq k)) T)
    (fun k ↦ D.baseChangeAlong_comp_sourceNodeMap (q k) (hq k) T)
    (isFpqcCovering_baseChangeAlong q (fun k ↦ D.sourceRestricted_comp_f (q k) (hq k)) hcov T)
    D.F (hker _ hamb _ hcok₁) (hker _ hamb _ hcok₂) hcok₁ hcok₂ fun k ↦ ?_
  exact (D.quotientRestrictOver_comp_sourceNodeMap hc hd₁ (hq k) (he₁ k) T _).trans
    (((D.restrictQuotientBetweenMembers_eq_iff (he₁ k) (he₂ k) T Q₁ Q₂).1 (h k)).trans
      (D.quotientRestrictOver_comp_sourceNodeMap hc hd₂ (hq k) (he₂ k) T _).symm)

/-- **Every matching family of quotients on a covering of the source is the family of
restrictions of a quotient.**  This is the surjectivity of the first arrow of the diagram of
Stacks 08IV onto the equalizer: given an fpqc covering `{a i : W i ⟶ X}` of the source, fibre
products `P i j = W i ×_X W j` and fpqc coverings `{Z i j k ⟶ P i j}`, a family of elements of
`Q_{F i/X i/Y}(T)` whose two restrictions to each `Z i j k` agree comes from an element of
`Q_{F/X/Y}(T)`.

The family is first upgraded to a descent datum on the fibre products by
`AlgebraicGeometry.Space.QuotientSituation.restrictQuotientBetweenMembers_eq_of_refinement`, and
then descended by
`AlgebraicGeometry.Space.descendsQuotientsAlongFpqcCovering_of_isQuasicoherentOnSite'`, the
conclusion of `AlgebraicGeometry.Space.DescendsQuotientsAlongFpqcCovering` for a quasi-coherent
module, which `D.F` is; flatness of the descended quotient over `T` is
`AlgebraicGeometry.Space.FlatOverDescendsAlongFpqcCovering`. -/
theorem exists_mem_quotients_restrictQuotientToMember_eq
    (hc : ModulePushforwardCoherence B S hS)
    (hfaith : ReflectsZeroAlongFpqcCovering.{u, v} B S hS)
    (hqc : PullbackPreservesQuasicoherenceEverywhere B S hS)
    (hker : KernelQuasicoherent B S hS)
    (hflatdesc : FlatOverDescendsAlongFpqcCovering.{u, v} B S hS)
    {I : Type v} {κ : I → I → Type v} {W : I → AlgebraicSpaces B S hS}
    {P : I → I → AlgebraicSpaces B S hS} {Z : ∀ i j, κ i j → AlgebraicSpaces B S hS}
    (a : ∀ i, W i ⟶ D.X) {c₀ : ∀ i j, P i j ⟶ W i} {c₁ : ∀ i j, P i j ⟶ W j}
    {d : ∀ i j, P i j ⟶ D.X} (q : ∀ i j k, Z i j k ⟶ P i j) {e : ∀ i j k, Z i j k ⟶ D.X}
    (hcov : IsFpqcCovering B S hS fun i ↦ (a i).hom)
    (hP : ∀ i j, IsPullback (c₀ i j) (c₁ i j) (a i) (a j))
    (hd₀ : ∀ i j, c₀ i j ≫ a i = d i j) (hd₁ : ∀ i j, c₁ i j ≫ a j = d i j)
    (hqcov : ∀ i j, IsFpqcCovering B S hS fun k ↦ (q i j k).hom)
    (he₀ : ∀ i j k, (q i j k ≫ c₀ i j) ≫ a i = e i j k)
    (he₁ : ∀ i j k, (q i j k ≫ c₁ i j) ≫ a j = e i j k) (T : SchemesOver D.Y)
    {Q : ∀ i, Subobject ((D.sourceRestricted (a i)).baseChangeModule T)}
    (hQ : ∀ i, Q i ∈ (D.sourceRestricted (a i)).quotients T)
    (hmatch : ∀ i j k,
      D.restrictQuotientBetweenMembers (q i j k ≫ c₀ i j) (he₀ i j k) T (Q i) =
        D.restrictQuotientBetweenMembers (q i j k ≫ c₁ i j) (he₁ i j k) T (Q j)) :
    ∃ K ∈ D.quotients T, ∀ i, D.restrictQuotientToMember (a i) T K = Q i := by
  obtain ⟨K, hKqc, hKres⟩ := descendsQuotientsAlongFpqcCovering_of_isQuasicoherentOnSite'
    (fun i ↦ baseChangeAlong (a i) (rfl : a i ≫ D.f = a i ≫ D.f) T)
    (fun i j ↦ baseChangeAlong (c₀ i j) (D.sourceRestricted_comp_f (c₀ i j) (hd₀ i j)) T)
    (fun i j ↦ baseChangeAlong (c₁ i j) (D.sourceRestricted_comp_f (c₁ i j) (hd₁ i j)) T)
    (fun i ↦ D.baseChangeAlong_comp_sourceProjection (a i) T)
    (fun i j ↦ D.baseChangeAlong_comp_sourceNodeMap (c₀ i j) (hd₀ i j) T)
    (fun i j ↦ D.baseChangeAlong_comp_sourceNodeMap (c₁ i j) (hd₁ i j) T)
    (isFpqcCovering_baseChangeAlong a (fun i ↦ (rfl : a i ≫ D.f = a i ≫ D.f)) hcov T)
    (fun i j ↦ isPullback_baseChangeAlong_pair D.f (hP i j) (hd₀ i j) (hd₁ i j)
      (D.sourceRestricted_comp_f (c₀ i j) (hd₀ i j))
      (D.sourceRestricted_comp_f (c₁ i j) (hd₁ i j)) T)
    D.F D.quasicoherent
    (fun i ↦ quotientTransport (D.sourceNodeIso (a i) T).symm (Q i))
    (fun i ↦ isQuasicoherentOnSite_cokernel_quotientTransport _ (hQ i).1) fun i j ↦
      (D.restrictQuotientBetweenMembers_eq_iff (hd₀ i j) (hd₁ i j) T _ _).1
        (D.restrictQuotientBetweenMembers_eq_of_refinement hc hfaith hqc hker (q i j)
          (hd₀ i j) (hd₁ i j) (he₀ i j) (he₁ i j) (hqcov i j) T (hQ i).1 (hQ j).1 (hmatch i j))
  have hres : ∀ i, D.restrictQuotientToMember (a i) T K = Q i := fun i ↦
    quotientTransport_injective (D.sourceNodeIso (a i) T).symm
      ((D.quotientTransport_sourceNodeIso_symm_restrictQuotientToMember (a i) T
        K).trans (hKres i))
  refine ⟨K, ⟨hKqc, ?_⟩, hres⟩
  refine hflatdesc (fun i ↦ baseChangeAlong (a i) (rfl : a i ≫ D.f = a i ≫ D.f) T)
    (fun i ↦ baseChangeAlong_comp_inclusion (a i) (rfl : a i ≫ D.f = a i ≫ D.f) T)
    (isFpqcCovering_baseChangeAlong a (fun i ↦ (rfl : a i ≫ D.f = a i ≫ D.f)) hcov T) _
    hKqc fun i ↦ ?_
  refine IsFlatOver.of_iso B S hS _
    (D.restrictQuotientToMemberCokernelIso (a i) T K) ?_
  rw [hres i]
  exact (hQ i).2

/-! ### Stacks 08IV -/

/-- The restrictions to two members of a covering agree on a common refinement. -/
private theorem restrictQuotientBetweenMembers_toMember_eq (hc : ModulePushforwardCoherence B S hS)
    {W₁ W₂ W' : AlgebraicSpaces B S hS} {a₁ : W₁ ⟶ D.X} {a₂ : W₂ ⟶ D.X} {a' : W' ⟶ D.X}
    {b₁ : W' ⟶ W₁} {b₂ : W' ⟶ W₂} (hb₁ : b₁ ≫ a₁ = a') (hb₂ : b₂ ≫ a₂ = a') (T : SchemesOver D.Y)
    (K : Subobject (D.baseChangeModule T)) :
    D.restrictQuotientBetweenMembers b₁ hb₁ T (D.restrictQuotientToMember a₁ T K) =
      D.restrictQuotientBetweenMembers b₂ hb₂ T (D.restrictQuotientToMember a₂ T K) :=
  (D.restrictQuotientBetweenMembers_toMember hc b₁ hb₁ T K).trans
    (D.restrictQuotientBetweenMembers_toMember hc b₂ hb₂ T K).symm

/-- **Stacks 08IV.**  In Situation 082M, let `{a i : W i ⟶ X}` be an fpqc covering of the source,
let `P i j` be the fibre product `W i ×_X W j` and let `{Z i j k ⟶ P i j}` be fpqc coverings.
For every scheme `T` over `Y` the diagram

`Q_{F/X/Y}(T) ⟶ ∏_i Q_{F i/W i/Y}(T) ⇉ ∏_{ijk} Q_{F ijk/Z i j k/Y}(T)`

presents the first arrow as the equalizer of the other two: restriction is a bijection from
`Q_{F/X/Y}(T)` onto the set of families `(Q i)` whose two restrictions to each `Z i j k` agree.

The three halves of this are
`AlgebraicGeometry.Space.QuotientSituation.restrictQuotientToMember_mem_quotients` together with
`AlgebraicGeometry.Space.QuotientSituation.restrictQuotientBetweenMembers_toMember`,
`AlgebraicGeometry.Space.QuotientSituation.eq_of_restrictQuotientToMember_eq` and
`AlgebraicGeometry.Space.QuotientSituation.exists_mem_quotients_restrictQuotientToMember_eq`.

Nothing beyond Situation 082M and the two coverings is assumed. -/
@[stacks 08IV "the full bijection onto the matching families, every T, with nothing assumed \
beyond Situation 082M and the two coverings: 03LU for commutativity, 04W8 faithfulness and 03DO \
kernels for injectivity, 03GA and 05VW along the flat members of the covering for the \
restrictions, Remark 08IT (04W8 fullness and effectivity, at the quasi-coherent module of the \
situation) and 05VY for surjectivity"]
theorem bijOn_restrictQuotientToMember
    {I : Type v} {κ : I → I → Type v} {W : I → AlgebraicSpaces B S hS}
    {P : I → I → AlgebraicSpaces B S hS} {Z : ∀ i j, κ i j → AlgebraicSpaces B S hS}
    (a : ∀ i, W i ⟶ D.X) {c₀ : ∀ i j, P i j ⟶ W i} {c₁ : ∀ i j, P i j ⟶ W j}
    {d : ∀ i j, P i j ⟶ D.X} (q : ∀ i j k, Z i j k ⟶ P i j) {e : ∀ i j k, Z i j k ⟶ D.X}
    (hcov : IsFpqcCovering B S hS fun i ↦ (a i).hom)
    (hP : ∀ i j, IsPullback (c₀ i j) (c₁ i j) (a i) (a j))
    (hd₀ : ∀ i j, c₀ i j ≫ a i = d i j) (hd₁ : ∀ i j, c₁ i j ≫ a j = d i j)
    (hqcov : ∀ i j, IsFpqcCovering B S hS fun k ↦ (q i j k).hom)
    (he₀ : ∀ i j k, (q i j k ≫ c₀ i j) ≫ a i = e i j k)
    (he₁ : ∀ i j k, (q i j k ≫ c₁ i j) ≫ a j = e i j k) (T : SchemesOver D.Y) :
    Set.BijOn (fun K i ↦
        D.restrictQuotientToMember (a i) T K)
      (D.quotients T)
      {Q | (∀ i, Q i ∈ (D.sourceRestricted (a i)).quotients T) ∧
        ∀ i j k, D.restrictQuotientBetweenMembers (q i j k ≫ c₀ i j) (he₀ i j k) T (Q i) =
          D.restrictQuotientBetweenMembers (q i j k ≫ c₁ i j) (he₁ i j k) T (Q j)} := by
  have hc := modulePushforwardCoherence B S hS
  have hqc : PullbackPreservesQuasicoherenceEverywhere B S hS :=
    fun g ↦ hasLocalInverseImagePresentations B S hS g
  refine ⟨fun K hK ↦ ⟨fun i ↦ D.restrictQuotientToMember_mem_quotients (a i) (hcov.1 i) T hK,
    fun i j k ↦ D.restrictQuotientBetweenMembers_toMember_eq hc (he₀ i j k) (he₁ i j k) T K⟩,
    fun K hK K' hK' h ↦ D.eq_of_restrictQuotientToMember_eq reflectsZeroAlongFpqcCovering.{u, v}
      kernelQuasicoherent a hcov T hK hK' fun i ↦ congrFun h i,
    fun Q hQ ↦ ?_⟩
  obtain ⟨K, hKmem, hKres⟩ := D.exists_mem_quotients_restrictQuotientToMember_eq hc
    reflectsZeroAlongFpqcCovering.{u, v} hqc kernelQuasicoherent
    flatOverDescendsAlongFpqcCovering.{u, v} a q hcov hP hd₀ hd₁ hqcov he₀ he₁ T hQ.1 hQ.2
  exact ⟨K, hKmem, funext hKres⟩

/-- **Stacks 08IV for the finite-presentation subfunctor.**  The diagram of Stacks 08IV presents
the first arrow as the equalizer of the other two for `Q^{fp}_{F/X/Y}` as well: restriction is a
bijection from `Q^{fp}_{F/X/Y}(T)` onto the set of families of elements of
`Q^{fp}_{F i/W i/Y}(T)` whose two restrictions to each `Z i j k` agree.

Only the two outer halves change: the restriction maps preserve finite presentation, which is
`restrictQuotientToMember_mem_finitePresentationQuotients` of this namespace, and the quotient
descended by
`AlgebraicGeometry.Space.QuotientSituation.exists_mem_quotients_restrictQuotientToMember_eq` is
of finite presentation by
`AlgebraicGeometry.Space.finitePresentationOnSiteDescendsAlongFpqcCovering`, Stacks 060V on the
site.

Nothing beyond Situation 082M and the two coverings is assumed. -/
@[stacks 08IV "the same equalizer property for the finite-presentation subfunctor Q^{fp}, \
again with nothing assumed and no weakening: the inputs of bijOn_restrictQuotientToMember \
together with Section 05VR for the restriction maps and 060V on the site for \
surjectivity"]
theorem bijOn_restrictQuotientToMember_finitePresentation
    {I : Type v} {κ : I → I → Type v} {W : I → AlgebraicSpaces B S hS}
    {P : I → I → AlgebraicSpaces B S hS} {Z : ∀ i j, κ i j → AlgebraicSpaces B S hS}
    (a : ∀ i, W i ⟶ D.X) {c₀ : ∀ i j, P i j ⟶ W i} {c₁ : ∀ i j, P i j ⟶ W j}
    {d : ∀ i j, P i j ⟶ D.X} (q : ∀ i j k, Z i j k ⟶ P i j) {e : ∀ i j k, Z i j k ⟶ D.X}
    (hcov : IsFpqcCovering B S hS fun i ↦ (a i).hom)
    (hP : ∀ i j, IsPullback (c₀ i j) (c₁ i j) (a i) (a j))
    (hd₀ : ∀ i j, c₀ i j ≫ a i = d i j) (hd₁ : ∀ i j, c₁ i j ≫ a j = d i j)
    (hqcov : ∀ i j, IsFpqcCovering B S hS fun k ↦ (q i j k).hom)
    (he₀ : ∀ i j k, (q i j k ≫ c₀ i j) ≫ a i = e i j k)
    (he₁ : ∀ i j k, (q i j k ≫ c₁ i j) ≫ a j = e i j k) (T : SchemesOver D.Y) :
    Set.BijOn (fun K i ↦
        D.restrictQuotientToMember (a i) T K)
      (D.finitePresentationQuotients T)
      {Q | (∀ i, Q i ∈ (D.sourceRestricted (a i)).finitePresentationQuotients T) ∧
        ∀ i j k, D.restrictQuotientBetweenMembers (q i j k ≫ c₀ i j) (he₀ i j k) T (Q i) =
          D.restrictQuotientBetweenMembers (q i j k ≫ c₁ i j) (he₁ i j k) T (Q j)} := by
  have hc := modulePushforwardCoherence B S hS
  have hqc : PullbackPreservesQuasicoherenceEverywhere B S hS :=
    fun g ↦ hasLocalInverseImagePresentations B S hS g
  refine ⟨fun K hK ↦ ⟨fun i ↦
      D.restrictQuotientToMember_mem_finitePresentationQuotients (a i) (hcov.1 i) T hK,
    fun i j k ↦ D.restrictQuotientBetweenMembers_toMember_eq hc (he₀ i j k) (he₁ i j k) T K⟩,
    fun K hK K' hK' h ↦ D.eq_of_restrictQuotientToMember_eq reflectsZeroAlongFpqcCovering.{u, v}
      kernelQuasicoherent a hcov T hK.1 hK'.1 fun i ↦ congrFun h i,
    fun Q hQ ↦ ?_⟩
  obtain ⟨K, hKmem, hKres⟩ := D.exists_mem_quotients_restrictQuotientToMember_eq hc
    reflectsZeroAlongFpqcCovering.{u, v} hqc kernelQuasicoherent
    flatOverDescendsAlongFpqcCovering.{u, v} a q hcov hP hd₀ hd₁ hqcov he₀ he₁ T
    (fun i ↦ (hQ.1 i).1) hQ.2
  refine ⟨K, ⟨hKmem, ?_⟩, funext hKres⟩
  refine finitePresentationOnSiteDescendsAlongFpqcCovering.{u, v}
    (fun i ↦ baseChangeAlong (a i) (rfl : a i ≫ D.f = a i ≫ D.f) T)
    (isFpqcCovering_baseChangeAlong a (fun i ↦ (rfl : a i ≫ D.f = a i ≫ D.f)) hcov T) _
    hKmem.1 fun i ↦ ?_
  refine SheafOfModules.IsFinitePresentationOnSite.of_iso
    (D.restrictQuotientToMemberCokernelIso (a i) T K) ?_
  rw [hKres i]
  exact (hQ.1 i).2

end QuotientSituation

end AlgebraicGeometry.Space

end
