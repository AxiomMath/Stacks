module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.ArbitraryBaseChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.BaseFunctionTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.ChartOverBase
public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.Main
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHomLocallyRinged
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStructureMapComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTwoIsoAffineCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.InclusionInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Order
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleCovering
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.Morphisms
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedTopoi.TwoIsoAndRightCancellation
public import StacksFrontier.Cotangent.SheavesOfRings.InverseImageDerivations

/-!
# Recovery of morphisms from small étale ringed topoi, and morphisms of thickenings

This file is the first part of
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.MorphismFromStructureMap`; see that module's
docstring for the mathematical overview.  It contains the 2-isomorphisms and composites of
morphisms of small étale ringed topoi of algebraic spaces over `S`, the statement
`AlgebraicGeometry.Space.IsRecoveredFromSmallEtale` of [Stacks Project, Tag 04KL] over a base
and its reductions, and [Stacks Project, Tag 05ZN]: a map of structure sheaves of thickenings
fitting the commuting square comes from a unique morphism of thickenings.
-/

@[expose] public section

open CategoryTheory Opposite
open Stacks.Sheaves.ToposPullback
open Stacks.Sheaves.RingedToposModules (directImageModules inverseImageDerivationEquiv)
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- 2-isomorphisms of morphisms of the small étale ringed topoi of algebraic spaces over `S`.
This is `AlgebraicGeometry.RingedToposHom.TwoIso` with the two ringed topoi named, which is what
pins down its universe parameters: the small étale ringed topos of an algebraic space is a
`AlgebraicGeometry.RingedTopos.{u, u + 1, u}`, and left to inference the parameters default. -/
abbrev SmallEtaleTwoIso {P Q : AlgebraicSpaces B S hS}
    (ψ χ : RingedToposHom (smallEtaleRingedTopos B S hS P) (smallEtaleRingedTopos B S hS Q)) :=
  RingedToposHom.TwoIso (A := smallEtaleRingedTopos B S hS P)
    (B := smallEtaleRingedTopos B S hS Q) ψ χ

/-- The composite of two morphisms of the small étale ringed topoi of algebraic spaces over
`S`.  This is `AlgebraicGeometry.RingedToposHom.comp` with the three ringed topoi named, for the
same reason as `AlgebraicGeometry.Space.SmallEtaleTwoIso`. -/
noncomputable abbrev smallEtaleComp {P Q R : AlgebraicSpaces B S hS}
    (χ : RingedToposHom (smallEtaleRingedTopos B S hS Q) (smallEtaleRingedTopos B S hS R))
    (ψ : RingedToposHom (smallEtaleRingedTopos B S hS P) (smallEtaleRingedTopos B S hS Q)) :
    RingedToposHom (smallEtaleRingedTopos B S hS P) (smallEtaleRingedTopos B S hS R) :=
  RingedToposHom.comp (X := smallEtaleRingedTopos B S hS P)
    (Y := smallEtaleRingedTopos B S hS Q) (Z := smallEtaleRingedTopos B S hS R) χ ψ

section Functoriality

variable {X Y Z : AlgebraicSpaces B S hS}

attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp MorphismOfTopoi.comp

/-- **Stacks 03G2, part (3)** at the level of ringed topoi: the morphism of small étale ringed
topoi of a composite of morphisms of algebraic spaces is 2-isomorphic to the composite of the
two morphisms of ringed topoi. -/
noncomputable def smallEtaleRingedToposHomCompTwoIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    SmallEtaleTwoIso B S hS
      (smallEtaleComp B S hS (smallEtaleRingedToposHom B S hS g)
        (smallEtaleRingedToposHom B S hS f))
      (smallEtaleRingedToposHom B S hS (f ≫ g)) where
  e := smallToposMorphismTypeU_comp B S hS f g
  commutes := by
    have h2 : (smallEtaleRingedTopos B S hS Z).forgetRing.map
        ((smallEtaleRingedToposHom_compRingIso B S hS f g).hom.app
          (smallEtaleRingedTopos B S hS X).O) =
        (smallToposMorphismTypeU_comp B S hS f g).hom.app (structureSetSheaf B S hS X) :=
      underlyingRingSheaf_map_pullbackCommRingSheafFunctorIsoOfNatIso_hom
        (SmallEtale.topology B S hS Z.1) _ (smallToposMorphismTypeU_comp B S hS f g)
    have h := congrArg (smallEtaleRingedTopos B S hS Z).forgetRing.map
      (smallEtaleRingedToposHom_comp_fSharp B S hS f g)
    rw [CategoryTheory.Functor.map_comp, h2] at h
    exact h

end Functoriality

/-- The morphism of algebraic spaces `k` **induces** the morphism `ψ` of the small étale ringed
topoi of its source and target when the morphism of ringed topoi of Stacks 03G8 attached to `k`
is 2-isomorphic to `ψ`.  This is the sense in which Stacks 04KL recovers a morphism of
algebraic spaces from a morphism of locally ringed topoi. -/
def InducesSmallEtaleRingedToposHom {P Q : AlgebraicSpaces B S hS} (k : P ⟶ Q)
    (ψ : RingedToposHom (smallEtaleRingedTopos B S hS P) (smallEtaleRingedTopos B S hS Q)) :
    Prop :=
  Nonempty (SmallEtaleTwoIso B S hS (smallEtaleRingedToposHom B S hS k) ψ)

/-- A morphism of algebraic spaces induces its own morphism of small étale ringed topoi. -/
theorem inducesSmallEtaleRingedToposHom_self {P Q : AlgebraicSpaces B S hS} (k : P ⟶ Q) :
    InducesSmallEtaleRingedToposHom B S hS k (smallEtaleRingedToposHom B S hS k) :=
  ⟨RingedToposHom.TwoIso.refl (smallEtaleRingedToposHom B S hS k)⟩

/-- **Stacks 04KL over a base**, in the form in which the result is used: a locally ringed
morphism `ψ` of the small étale ringed topoi of two algebraic spaces `P` and `Q` over `S` which
is 2-compatible with a pair of structure morphisms `pP : P ⟶ A`, `pQ : Q ⟶ A` to a third
algebraic space is induced by exactly one morphism `P ⟶ Q`.

The 2-compatibility is not optional, and it is what [Stacks Project, Tag 04SG] supplies.  A
morphism of `AlgebraicGeometry.AlgebraicSpaces B S hS` is a morphism *over* `S`, whereas the
small étale site of an algebraic space over `S` is its absolute small étale site —
`AlgebraicGeometry.Space.SmallEtale` is cut out of the scheme charts of the underlying presheaf,
and a chart of a space over `S` lies over `S` of its own accord — so a morphism of small étale
ringed topoi records nothing about either space's morphism to the base.  Dropping the
2-compatibility makes the assertion false.  Take `S = P = Q = A = Spec k` for `k = ℚ(i)` with
its nontrivial automorphism `σ`, and `pP = pQ = 𝟙`.  The only morphism `P ⟶ Q` over `S` is the
identity, while `(U, u) ↦ (U, σ⁻¹ ∘ u)` is a self-equivalence of the étale `S`-schemes which
fixes every ring of sections, hence a locally ringed automorphism of the small étale ringed
topos of `P`; it is not 2-isomorphic to the morphism of the identity, since a 2-isomorphism
would exhibit an isomorphism `Spec L ≅ Spec L^σ` over `k` for every finite separable `L`, and
`ℚ(i)(√(1 + i))` is not isomorphic over `ℚ(i)` to `ℚ(i)(√(1 - i))` because the quotient
`(1 + i)/(1 - i) = i` is not a square in `ℚ(i)`.  With `pP` and `pQ` present that `ψ` is
excluded, since the 2-compatibility reads there as `ψ` being 2-isomorphic to the identity.

Tag 04KL itself is the absolute statement, for algebraic spaces over `Spec ℤ`; the form here
follows from it together with the equivalence of [Stacks Project, Tag 04SG]
(`AlgebraicGeometry.spacesOverSmallerBaseEquivalence`), which identifies the morphisms over `S`
with the absolute morphisms commuting with the structure morphisms to `S`.

The **absolute** form is proved in this development:
`AlgebraicGeometry.Space.existsUnique_spaceHom_twoIso_of_isLocallyRinged` of
`StacksFrontier/AlgebraicGeometry/Spaces/RecoveringMorphisms/Main.lean:171` carries `@[stacks 04KL]`
and is unconditional, for `AlgebraicSpaces B (Spec (CommRingCat.of (ULift.{u} ℤ))) hZ` with
`Spec (ULift ℤ)` terminal.  Tag 04SG is proved too, as
`AlgebraicGeometry.spacesOverSmallerBaseEquivalence` of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallerBaseEquivalence.lean:127`.  The relative form is
**not** deduced from those two, and that deduction would not be a formality: the 2-compatibility
above is what makes the relative statement true at all, so the form here is strictly more than an
instance of the absolute one.  What that transport would need beyond Tag 04SG as formalized is a
comparison of the *small étale sites* across the two bases.  The equivalence of Tag 04SG is between
`AlgebraicSpaces B S hS` and the slice `AlgebraicGeometry.SpacesOverSmallerBase` of
`StacksFrontier/AlgebraicGeometry/Spaces/Category.lean:274` — algebraic spaces over the smaller base
carrying a morphism to `h_S` — and neither it nor
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleChartSmallerBase.lean`, which carries the étale chart
condition across a change of base, mentions `AlgebraicGeometry.Space.SmallEtale` at all; so
neither an equivalence of the small étale sites nor an identification of
`AlgebraicGeometry.Space.smallEtaleRingedToposHom` across a change of base is available to
transport `ψ` along.  It is proved instead directly, for a base scheme whose canonical
morphism to the spectrum of its global functions is a monomorphism:
`AlgebraicGeometry.Space.isRecoveredFromSmallEtale_of_mono_toSpecΓ` below.

**Exactly one statement separates the two, and it is not the Tag 04SG transport.**  The
development's proof of Tag 04KL is written over an arbitrary base scheme:
`AlgebraicGeometry.Space.recoveredHom'`,
`AlgebraicGeometry.Space.isChartCompatible_recoveredHom'`,
`AlgebraicGeometry.Space.nonempty_twoIso_recoveredHom'`,
`AlgebraicGeometry.Space.relSurjAt_of_isLocallyRinged'` and
`AlgebraicGeometry.Space.relInjAt_of_isLocallyRinged'` are stated for a general `S` with
`hover : IsChartOverBase g` as their only hypothesis on the base, and the uniqueness half
(`AlgebraicGeometry.Space.eq_of_smallEtaleRingedToposHom_twoIso`, Tag 04M6) assumes nothing
about `S` at all.  That hypothesis is consumed in one place only, in
`AlgebraicGeometry.Space.OverBase.chartOverHom` of
`StacksFrontier/AlgebraicGeometry/Spaces/RecoveringMorphisms/ChartComparison.lean`: the chart
morphism `f_s` is produced as a morphism of *schemes* by
`AlgebraicGeometry.Space.chartSchemeHom` of
`StacksFrontier/AlgebraicGeometry/Spaces/RecoveringMorphisms/ChartRingMap.lean:211`, which needs no
hypothesis on the base, and `OverBase.chartOverHom` then reads it as a morphism of the big fppf
site of `S` through `AlgebraicGeometry.BigFppfOver.homOfCompEq` of
`StacksFrontier/AlgebraicGeometry/Spaces/SchemePointsAffineHom.lean:97`, whose hypothesis is
exactly that the chart morphisms of `ψ` are morphisms over `S`:

```
∀ (V : SmallEtale B S hS Q.1) [IsAffine (chartSch V)] (U : SmallEtale B S hS P.1)
    (s : (invRep ψ V).obj.obj (op U)),
  chartSchemeHom ψ V U s ≫ B.inclusion.map V.obj.left.hom = B.inclusion.map U.obj.left.hom
```

and *that* is what the 2-compatibility yields.  The counterexample above is exactly a `ψ`
for which this equation fails: there the chart morphisms are the `σ`-twists of the charts, and
their two composites to `S` differ by `σ`.  So the Tag 04SG transport is one route to the
relative form and not the one taken — nothing in the construction of `k`, in the stalk arguments
or in the 2-isomorphism needs it.

*What that one equation costs.*  It is an equality of morphisms of schemes **into `S`**, while
the chart construction produces only the ring map on global functions
`AlgebraicGeometry.Space.chartRingHom`, and a ring map on global functions determines a morphism
of schemes exactly when the canonical morphism of the target to the spectrum of its global
functions is a monomorphism (`AlgebraicGeometry.ext_of_mono_toSpecΓ`).  So for such a base the
equation is equivalent to a ring identity, and that identity is reduced to a statement about `ψ`
alone in
`StacksFrontier/AlgebraicGeometry/Spaces/RecoveringMorphisms/ChartBaseFunction.lean`: a regular
function on `S` pulls back to a global regular function on every algebraic space over `S`
(`AlgebraicGeometry.Space.baseGlobalFunction`), the chart ring map of `ψ` carries it to the
function `ψ` transports it to **independently of the section `s`**
(`AlgebraicGeometry.Space.chartRingHom_baseGlobalFunction`, because the map `h_V ⟶ 𝒪_Q` of such
a function factors through the terminal sheaf), and over such a base the displayed equation
then follows from

```
∀ (r : Γ(S, ⊤)) (U : SmallEtale B S hS P.1),
  baseFunctionTransport ψ r U = (chartToBase B S hS P U).appTop.hom r
```

by `AlgebraicGeometry.Space.chartSchemeHom_comp_inclusion_map_of_baseFunctionTransport` — that
`ψ` transports the functions pulled back from the base to themselves.  That is the remaining
content and the 2-compatibility yields it, in
`StacksFrontier/AlgebraicGeometry/Spaces/RecoveringMorphisms/BaseFunctionTransport.lean`: the
transport along the morphism of ringed topoi of a morphism of algebraic spaces over `S` is
pullback along the vertical morphism of a diagram of étale charts, hence again the function
pulled back from the base
(`AlgebraicGeometry.Space.baseFunctionTransport_smallEtaleRingedToposHom`, Tag 03G8), the
transport is invariant under a 2-isomorphism
(`AlgebraicGeometry.Space.baseFunctionTransport_eq_of_twoIso`), and the transport along a
composite is the transport along its second factor of the transport along its first
(`AlgebraicGeometry.Space.baseFunctionTransport_comp`); the three together are
`AlgebraicGeometry.Space.baseFunctionTransport_eq_of_twoCompatible`.  So this assertion is a
**theorem** whenever the canonical morphism `S ⟶ Spec Γ(S, ⊤)` is a monomorphism,
`AlgebraicGeometry.Space.isRecoveredFromSmallEtale_of_mono_toSpecΓ`, and that hypothesis is the
exact reach of the route rather than an artefact of it: it is equivalent to the assertion that a
morphism of schemes into `S` is determined by its ring map on global functions.

*Over an arbitrary base.*  The chart equation holds for every base scheme, by
`AlgebraicGeometry.Space.isChartOverBase_of_twoCompatible`, and this assertion is therefore a
theorem outright, `AlgebraicGeometry.Space.isRecoveredFromSmallEtale_holds`.  That proof does not
go through the functions on the base: it reads the chart morphism of `ψ` at a section of `ψ⁻¹h_V`,
followed by the chart morphism of `p_Q` at a section of `p_Q⁻¹h_W` for an affine chart `W` of `A`,
as a chart morphism of `p_P` (by the 2-isomorphism), and the chart morphisms of a morphism of
algebraic spaces lie over the base; such sections exist locally, and the equation descends along
étale coverings because the fpqc topology is subcanonical.

The uniqueness in the `∃!` is redundant, since
`AlgebraicGeometry.Space.eq_of_inducesCommonSmallEtaleRingedToposHom` proves it unconditionally
from [Stacks Project, Tag 04M6] and for every base.  It is kept in the statement because that is
the shape of the source's assertion. -/
def IsRecoveredFromSmallEtale : Prop :=
  ∀ {A P Q : AlgebraicSpaces B S hS} (pP : P ⟶ A) (pQ : Q ⟶ A)
    (ψ : RingedToposHom (smallEtaleRingedTopos B S hS P) (smallEtaleRingedTopos B S hS Q)),
    ψ.IsLocallyRinged →
    Nonempty (SmallEtaleTwoIso B S hS
      (smallEtaleComp B S hS (smallEtaleRingedToposHom B S hS pQ) ψ)
      (smallEtaleRingedToposHom B S hS pP)) →
    ∃! k : P ⟶ Q, InducesSmallEtaleRingedToposHom B S hS k ψ

/-- **A morphism of algebraic spaces is determined by the morphism of small étale ringed topoi
it induces.**  At most one morphism `P ⟶ Q` over `S` is 2-isomorphic to a given morphism `ψ` of
the small étale ringed topoi.

This is the faithfulness half of Stacks 04KL over a base, and it is **not** carried: it holds
unconditionally, by Stacks 04M6,
`AlgebraicGeometry.Space.eq_of_smallEtaleRingedToposHom_twoIso`, which says exactly that two
morphisms of algebraic spaces over `S` with 2-isomorphic morphisms of small étale ringed topoi
are equal.  The *existence* half of Stacks 04KL over a base is
`AlgebraicGeometry.Space.IsRecoveredFromSmallEtale`, which is proved for every base scheme by
`AlgebraicGeometry.Space.isRecoveredFromSmallEtale_holds`.

Note that the 2-compatibility with structure morphisms to a base, which
`AlgebraicGeometry.Space.IsRecoveredFromSmallEtale` cannot do without, and the hypothesis on the
base scheme, which its proof cannot do without, are not needed here: the
counterexample recorded in that definition's docstring is a `ψ` induced by *no* morphism over
`S`, not by two. -/
@[stacks 05ZN "the uniqueness clause of the tag, unconditionally and in the \
generality in which it is true: at most one morphism `X' ⟶ Y'` of the ambient algebraic \
spaces over the base is 2-isomorphic to a given morphism of their small étale ringed \
topoi, so there is at most one morphism of thickenings `(f, f')` with \
`alpha = (f')^sharp`.  This is the faithfulness half of 04KL over a base and it is \
PROVED, by 04M6; no thickening hypothesis and no 2-compatibility with the base is used"]
theorem eq_of_inducesCommonSmallEtaleRingedToposHom {P Q : AlgebraicSpaces B S hS}
    {ψ : RingedToposHom (smallEtaleRingedTopos B S hS P) (smallEtaleRingedTopos B S hS Q)}
    (k₁ k₂ : P ⟶ Q) (h₁ : InducesSmallEtaleRingedToposHom B S hS k₁ ψ)
    (h₂ : InducesSmallEtaleRingedToposHom B S hS k₂ ψ) :
    k₁ = k₂ := by
  obtain ⟨t₁⟩ := h₁
  obtain ⟨t₂⟩ := h₂
  exact eq_of_smallEtaleRingedToposHom_twoIso B S hS k₁ k₂ (t₁.trans t₂.symm)

/-- `AlgebraicGeometry.Space.IsRecoveredFromSmallEtale` with the third algebraic space fixed:
a locally ringed morphism `ψ` of the small étale ringed topoi of two algebraic spaces over `S`
which is 2-compatible with a pair of structure morphisms **to `A₀`** is induced by exactly one
morphism of algebraic spaces.

So `IsRecoveredFromSmallEtale B S hS` is `∀ A₀, IsRecoveredFromSmallEtaleOver B S hS A₀`, and
`AlgebraicGeometry.Space.isRecoveredFromSmallEtale_of_isRecoveredFromSmallEtaleOver` says that
one weakly terminal `A₀` already suffices. -/
def IsRecoveredFromSmallEtaleOver (A₀ : AlgebraicSpaces B S hS) : Prop :=
  ∀ {P Q : AlgebraicSpaces B S hS} (pP : P ⟶ A₀) (pQ : Q ⟶ A₀)
    (ψ : RingedToposHom (smallEtaleRingedTopos B S hS P) (smallEtaleRingedTopos B S hS Q)),
    ψ.IsLocallyRinged →
    Nonempty (SmallEtaleTwoIso B S hS
      (smallEtaleComp B S hS (smallEtaleRingedToposHom B S hS pQ) ψ)
      (smallEtaleRingedToposHom B S hS pP)) →
    ∃! k : P ⟶ Q, InducesSmallEtaleRingedToposHom B S hS k ψ

/-- Stacks 04KL over a base, at every base, is Stacks 04KL over any one base. -/
theorem isRecoveredFromSmallEtaleOver_of_isRecoveredFromSmallEtale
    (h : IsRecoveredFromSmallEtale B S hS) (A₀ : AlgebraicSpaces B S hS) :
    IsRecoveredFromSmallEtaleOver B S hS A₀ :=
  fun pP pQ ψ => h pP pQ ψ

/-- **The quantification over the base in `IsRecoveredFromSmallEtale` is redundant.**  If `A₀`
is a weakly terminal algebraic space over `S` — every algebraic space over `S` admits *some*
morphism to it — then Stacks 04KL over the single base `A₀` implies Stacks 04KL over every
base.

The reduction is the 2-isomorphism calculus of Stacks 03G2 part (3), in the packaged form
`AlgebraicGeometry.Space.smallEtaleRingedToposHomCompTwoIso`, and nothing else.  Given
`pP : P ⟶ A` and `pQ : Q ⟶ A`, compose both with `u : A ⟶ A₀`; the 2-compatibility of `ψ` with
`pP` and `pQ` then gives its 2-compatibility with `pP ≫ u` and `pQ ≫ u`, because
`(pQ ≫ u)_{étale} ∘ ψ` is 2-isomorphic to `u_{étale} ∘ (pQ_{étale} ∘ ψ)`, hence to
`u_{étale} ∘ pP_{étale}`, hence to `(pP ≫ u)_{étale}`.  The recovered morphism `k : P ⟶ Q` is
asked to induce `ψ` in either case, so the two `∃!` statements are about the same `k` and no
uniqueness is lost.

This is the half of "Tag 04KL together with Tag 04SG gives the form used here" which needs no
comparison of bases: it removes the arbitrary third space, leaving the clause at a terminal
algebraic space, which is the form the absolute Tag 04KL supplies. -/
theorem isRecoveredFromSmallEtale_of_isRecoveredFromSmallEtaleOver
    {A₀ : AlgebraicSpaces B S hS} (u : ∀ A : AlgebraicSpaces B S hS, A ⟶ A₀)
    (h : IsRecoveredFromSmallEtaleOver B S hS A₀) :
    IsRecoveredFromSmallEtale B S hS := by
  intro A P Q pP pQ ψ hlocal hcompat
  obtain ⟨r⟩ := hcompat
  refine h (pP ≫ u A) (pQ ≫ u A) ψ hlocal ⟨?_⟩
  refine (RingedToposHom.TwoIso.whiskerLeft ψ
      (smallEtaleRingedToposHomCompTwoIso B S hS pQ (u A))).symm.trans ?_
  refine (RingedToposHom.TwoIso.associator ψ (smallEtaleRingedToposHom B S hS pQ)
      (smallEtaleRingedToposHom B S hS (u A))).symm.trans ?_
  exact (RingedToposHom.TwoIso.whiskerRight r
      (smallEtaleRingedToposHom B S hS (u A))).trans
    (smallEtaleRingedToposHomCompTwoIso B S hS pP (u A))

/-- The base, read as an algebraic space over itself: the presheaf represented by the terminal
object `Over.mk (𝟙 (B.obj hS))` of the big fppf site of `S`.  It is a terminal object of
`AlgebraicGeometry.AlgebraicSpaces B S hS` by
`AlgebraicGeometry.Space.toBaseSpace`. -/
noncomputable abbrev baseSpace : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj (Over.mk (𝟙 (B.obj hS))), isAlgebraicSpace_yoneda B S hS _⟩

/-- The structure morphism of an algebraic space over `S` to
`AlgebraicGeometry.Space.baseSpace`, which is terminal among algebraic spaces over `S` because
the presheaf represented by the terminal object of the site is terminal
(`AlgebraicGeometry.Space.isTerminal_yoneda_obj_base`) and the algebraic spaces are a full
subcategory of the presheaves. -/
noncomputable def toBaseSpace (A : AlgebraicSpaces B S hS) : A ⟶ baseSpace B S hS :=
  ObjectProperty.homMk ((isTerminal_yoneda_obj_base B S hS).from A.1)

/-- **Stacks 04KL over the base alone implies Stacks 04KL over every base.**  This is
`AlgebraicGeometry.Space.isRecoveredFromSmallEtale_of_isRecoveredFromSmallEtaleOver` with the
weakly terminal algebraic space supplied: the arbitrary third space of
`AlgebraicGeometry.Space.IsRecoveredFromSmallEtale` may always be taken to be the base. -/
theorem isRecoveredFromSmallEtale_of_baseSpace
    (h : IsRecoveredFromSmallEtaleOver B S hS (baseSpace B S hS)) :
    IsRecoveredFromSmallEtale B S hS :=
  isRecoveredFromSmallEtale_of_isRecoveredFromSmallEtaleOver B S hS (toBaseSpace B S hS) h

/-- **A morphism of algebraic spaces is determined by the morphism of small étale ringed topoi it
induces**, in the special form in which `ψ` is the morphism of ringed topoi of `k₂` itself.

This is the shape in which the statement was first written, taking Stacks 04KL over a base as the
argument `hKL`.  It is an instance of
`AlgebraicGeometry.Space.eq_of_inducesCommonSmallEtaleRingedToposHom`, which needs no such
argument and is where [Stacks Project, Tag 05ZN]'s uniqueness clause is registered; this form is
kept because the declarations below are stated in terms of it. -/
theorem eq_of_inducesSmallEtaleRingedToposHom (hKL : IsRecoveredFromSmallEtale B S hS)
    {P Q : AlgebraicSpaces B S hS} (k₁ k₂ : P ⟶ Q)
    (h : InducesSmallEtaleRingedToposHom B S hS k₁ (smallEtaleRingedToposHom B S hS k₂)) :
    k₁ = k₂ := by
  obtain ⟨_, -, huniq⟩ :=
    hKL k₂ (𝟙 Q) (smallEtaleRingedToposHom B S hS k₂)
      (smallEtaleRingedToposHom_isLocallyRinged B S hS k₂)
      ⟨by simpa only [Category.comp_id] using
        smallEtaleRingedToposHomCompTwoIso B S hS k₂ (𝟙 Q)⟩
  exact (huniq k₁ h).trans (huniq k₂ (inducesSmallEtaleRingedToposHom_self B S hS k₂)).symm

/-- A locally ringed morphism of small étale ringed topoi whose chart morphisms lie over the base
is induced by exactly one morphism of algebraic spaces. -/
private theorem existsUnique_induces_of_isChartOverBase {P Q : AlgebraicSpaces B S hS}
    {ψ : RingedToposHom (smallEtaleRingedTopos B S hS P) (smallEtaleRingedTopos B S hS Q)}
    (hψ : ψ.IsLocallyRinged) (hover : IsChartOverBase ψ) :
    ∃! k : P ⟶ Q, InducesSmallEtaleRingedToposHom B S hS k ψ := by
  obtain ⟨t'⟩ := nonempty_twoIso_recoveredHom' ψ hover
    (fun x _ _ _ _ c ↦ relSurjAt_of_isLocallyRinged' hψ _ x c)
    (fun x _ _ _ _ c ↦ relInjAt_of_isLocallyRinged' hψ _ x c)
    (fun x P τ ↦ exists_affineOpen_lift ψ x P τ) (fun x ↦ exists_affine_invStalk ψ x)
  have hind : InducesSmallEtaleRingedToposHom B S hS (recoveredHom' ψ hover) ψ := ⟨t'.symm⟩
  exact ⟨recoveredHom' ψ hover, hind,
    fun k hk ↦ eq_of_inducesCommonSmallEtaleRingedToposHom B S hS k _ hk hind⟩

/-- **Stacks 04KL over a base scheme determined by its global functions**, which is what
`AlgebraicGeometry.Space.IsRecoveredFromSmallEtale` asserts: when the canonical morphism
`S ⟶ Spec Γ(S, ⊤)` of the base scheme is a monomorphism, a locally ringed morphism `ψ` of the
small étale ringed topoi of two algebraic spaces over `S` which is 2-compatible with a pair of
structure morphisms to a third algebraic space is induced by exactly one morphism of algebraic
spaces over `S`.

The hypothesis holds for an affine base scheme — there `S.toSpecΓ` is an isomorphism — and for a
quasi-affine one, where it is an open immersion
(`AlgebraicGeometry.Scheme.IsQuasiAffine`), and more generally for any base which embeds in an
affine scheme.

The whole of `StacksDraft.AlgebraicGeometry.Spaces.RecoveringMorphisms` is written over an
arbitrary base scheme, and the one thing it needs of the base is that the chart morphisms of
`ψ` be morphisms over it (`AlgebraicGeometry.Space.IsChartOverBase`).  Under the hypothesis that
is a ring identity, and the identity follows from the 2-compatibility: `ψ` transports the
functions pulled back from the base to themselves
(`AlgebraicGeometry.Space.baseFunctionTransport_eq_of_twoCompatible`), and a morphism of schemes
into `S` is then pinned down by its ring map on global functions
(`AlgebraicGeometry.Space.chartSchemeHom_comp_inclusion_map_of_baseFunctionTransport`).

The hypothesis is exactly the reach of that route and not an artefact of it: by the Γ–Spec
adjunction it says precisely that a morphism of schemes into `S` is determined by its ring map on
global functions, which is all the chart construction produces.  For an arbitrary base the
chart equation is proved by a different route, and the assertion with it, in
`AlgebraicGeometry.Space.isRecoveredFromSmallEtale_holds`, which supersedes this statement.  The
source states Tag 04KL over `Spec ℤ` and the proof of Tag 05ZN omits the verification over a base
altogether.

Tag 04KL is **not** registered on this statement.  The source's tag is the absolute theorem,
over `Spec ℤ`, and that is where it is registered, on
`AlgebraicGeometry.Space.existsUnique_spaceHom_twoIso_of_isLocallyRinged`; the statement here is
a different one — the relative form, over a restricted class of base schemes — and a restriction
of a statement is not that statement. -/
theorem isRecoveredFromSmallEtale_of_mono_toSpecΓ (hSmono : Mono S.toSpecΓ) :
    IsRecoveredFromSmallEtale B S hS := by
  intro A P Q pP pQ ψ hψ hcompat
  obtain ⟨t⟩ := hcompat
  exact existsUnique_induces_of_isChartOverBase B S hS hψ fun V _ U s ↦
    chartSchemeHom_comp_inclusion_map_of_baseFunctionTransport ψ hSmono
      (fun r U ↦ baseFunctionTransport_eq_of_twoCompatible pP pQ ψ t r U) V U s

section Thickenings

variable {T X' Y' : AlgebraicSpaces B S hS} {G : Subfunctor X'.1} {H : Subfunctor Y'.1}

/-- **The locally ringed condition of [Stacks Project, Tag 05ZN] is automatic.**  A morphism
`Φ = (f_{spaces,étale}, α)` of the small étale ringed topoi of the two ambient spaces which fits
the source's commuting square over a morphism `f` of the two closed subspaces is a morphism of
*locally* ringed topoi.

This is the step the source settles by Modules on Sites, Definition 18.40.9 together with
[Stacks Project, Tag 04KJ] and the local nilpotency of the kernels of `i_X^♯` and `i_Y^♯`.  Here
it is the right cancellation
`AlgebraicGeometry.RingedToposHom.isLocallyRinged_of_comp_of_isEquivalence`: the square makes
`Φ ∘ i_X` 2-isomorphic to the morphism of ringed topoi of `f ≫ i_Y`, which is locally ringed by
Tag 04KJ, and `i_X` is locally ringed by the same tag, so `Φ` is locally ringed as soon as the
inverse image along `i_X` is an equivalence — which it is, by
`AlgebraicGeometry.Space.isEquivalence_inverseImage_inclusion_of_isThickening`, the
sheaf-of-sets half of [Stacks Project, Tag 05ZM].  The local nilpotency the source invokes is
exactly the cartesian units square of `i_X`, so Tag 04KJ supplies it. -/
theorem isLocallyRinged_of_thickeningSquare (hG : IsThickening B S hS X' G)
    (hH : IsThickening B S hS Y' H)
    (f : IsThickening.space B S hS hG ⟶ IsThickening.space B S hS hH)
    (Φ : RingedToposHom (smallEtaleRingedTopos B S hS X') (smallEtaleRingedTopos B S hS Y'))
    (hsquare : Nonempty (SmallEtaleTwoIso B S hS
      (smallEtaleComp B S hS Φ
        (smallEtaleRingedToposHom B S hS (IsThickening.inclusion B S hS hG)))
      (smallEtaleRingedToposHom B S hS (f ≫ IsThickening.inclusion B S hS hH)))) :
    Φ.IsLocallyRinged := by
  obtain ⟨s⟩ := hsquare
  have hcomp : (smallEtaleComp B S hS Φ
      (smallEtaleRingedToposHom B S hS (IsThickening.inclusion B S hS hG))).IsLocallyRinged :=
    RingedToposHom.isLocallyRinged_of_twoIso
      (X := smallEtaleRingedTopos B S hS (IsThickening.space B S hS hG))
      (Y := smallEtaleRingedTopos B S hS Y') s
      (smallEtaleRingedToposHom_isLocallyRinged B S hS
        (f ≫ IsThickening.inclusion B S hS hH))
  exact RingedToposHom.isLocallyRinged_of_comp_of_isEquivalence
    (X := smallEtaleRingedTopos B S hS (IsThickening.space B S hS hG))
    (Y := smallEtaleRingedTopos B S hS X') (Z := smallEtaleRingedTopos B S hS Y') Φ
    (smallEtaleRingedToposHom B S hS (IsThickening.inclusion B S hS hG))
    (isEquivalence_inverseImage_inclusion_of_isThickening B S hS hG) hcomp
    (smallEtaleRingedToposHom_isLocallyRinged B S hS (IsThickening.inclusion B S hS hG))

/-- A morphism `f'` inducing `Φ` satisfies the two equations of a morphism of thickenings over `T`
once `Φ` is compatible with the two inclusions and the two structure morphisms. -/
private theorem inclusion_comp_and_comp_structure_of_induces
    (hG : IsThickening B S hS X' G) (hH : IsThickening B S hS Y' H)
    (pX' : X' ⟶ T) (pY' : Y' ⟶ T)
    (f : IsThickening.space B S hS hG ⟶ IsThickening.space B S hS hH)
    (Φ : RingedToposHom (smallEtaleRingedTopos B S hS X') (smallEtaleRingedTopos B S hS Y'))
    (hsquare : Nonempty (SmallEtaleTwoIso B S hS
      (smallEtaleComp B S hS Φ
        (smallEtaleRingedToposHom B S hS (IsThickening.inclusion B S hS hG)))
      (smallEtaleRingedToposHom B S hS (f ≫ IsThickening.inclusion B S hS hH))))
    (halgebra : Nonempty (SmallEtaleTwoIso B S hS
      (smallEtaleComp B S hS (smallEtaleRingedToposHom B S hS pY') Φ)
      (smallEtaleRingedToposHom B S hS pX')))
    (f' : X' ⟶ Y') (hf' : InducesSmallEtaleRingedToposHom B S hS f' Φ) :
    IsThickening.inclusion B S hS hG ≫ f' = f ≫ IsThickening.inclusion B S hS hH ∧
      f' ≫ pY' = pX' := by
  obtain ⟨t⟩ := hf'
  obtain ⟨s⟩ := hsquare
  obtain ⟨r⟩ := halgebra
  refine ⟨?_, ?_⟩
  · exact eq_of_inducesCommonSmallEtaleRingedToposHom B S hS _ _
      ⟨(smallEtaleRingedToposHomCompTwoIso B S hS
            (IsThickening.inclusion B S hS hG) f').symm.trans
        ((RingedToposHom.TwoIso.whiskerLeft
          (smallEtaleRingedToposHom B S hS (IsThickening.inclusion B S hS hG)) t).trans s)⟩
      (inducesSmallEtaleRingedToposHom_self B S hS _)
  · exact eq_of_inducesCommonSmallEtaleRingedToposHom B S hS _ _
      ⟨(smallEtaleRingedToposHomCompTwoIso B S hS f' pY').symm.trans
        ((RingedToposHom.TwoIso.whiskerRight t (smallEtaleRingedToposHom B S hS pY')).trans r)⟩
      (inducesSmallEtaleRingedToposHom_self B S hS _)

/-- **Stacks 05ZN over a base scheme determined by its global functions.**  Let
`G ⊂ X'` and `H ⊂ Y'` be thickenings of algebraic spaces over `T`, let `f : X ⟶ Y` be a
morphism of the two closed subspaces, and let `Φ = (f_{spaces,étale}, α)` be a morphism of the
small étale ringed topoi of `X'` and `Y'` which is compatible with the two inclusions and with
the two structure morphisms to `T`.  Then there is exactly one morphism `f' : X' ⟶ Y'` inducing
`Φ`, and it makes `(f, f')` a morphism of thickenings over `T`.

The two compatibilities are the source's commuting square for `α`, `f^♯`, `i_X^♯` and `i_Y^♯`,
and the hypothesis that `α` is a map of `𝒪_T`-algebras.  That `Φ` is locally ringed is *not*
assumed: it is derived from the square by
`AlgebraicGeometry.Space.isLocallyRinged_of_thickeningSquare`, as in the source.  Neither is the
recovery of morphisms from their small étale ringed topoi assumed: it is
`AlgebraicGeometry.Space.isRecoveredFromSmallEtale_of_mono_toSpecΓ`, which is where the
hypothesis on the base scheme is used and the only place it is used.  That hypothesis holds for
an affine base scheme and for a quasi-affine one. -/
@[stacks 05ZN "over a base SCHEME whose canonical morphism to the spectrum of its global \
functions is a monomorphism -- an affine base, a quasi-affine base, any base which embeds in an \
affine scheme: that the recovered morphism is a morphism of thickenings over the base and that \
the pair is unique.  The source states the tag over an arbitrary base and ends `we omit the \
verification that f-prime is a morphism over B`; the existence of the morphism recovering a \
locally ringed morphism of the small etale ringed topoi over the base -- 04KL over a base -- is \
what that verification amounts to, and it is PROVED here for such a base scheme, by \
`isRecoveredFromSmallEtale_of_mono_toSpecGamma`.  That hypothesis is the exact reach of the \
route, being equivalent to the assertion that a morphism of schemes into the base is determined \
by its ring map on global functions, which is all the chart construction of 04KL produces.  So \
this clause is unconditional for those base schemes only, and is NOT the tag in the generality \
the source states it in.  The locally ringed condition on (f_spaces,etale, alpha) is derived \
from the commuting square, not assumed, and the uniqueness of the pair and the two equations are \
derived from the faithfulness half of 04KL over a base, which is PROVED for every base -- see \
`eq_of_inducesCommonSmallEtaleRingedToposHom`, from 04M6"]
theorem existsUnique_thickeningHom (hSmono : Mono S.toSpecΓ)
    (hG : IsThickening B S hS X' G) (hH : IsThickening B S hS Y' H)
    (pX' : X' ⟶ T) (pY' : Y' ⟶ T)
    (f : IsThickening.space B S hS hG ⟶ IsThickening.space B S hS hH)
    (Φ : RingedToposHom (smallEtaleRingedTopos B S hS X') (smallEtaleRingedTopos B S hS Y'))
    (hsquare : Nonempty (SmallEtaleTwoIso B S hS
      (smallEtaleComp B S hS Φ
        (smallEtaleRingedToposHom B S hS (IsThickening.inclusion B S hS hG)))
      (smallEtaleRingedToposHom B S hS (f ≫ IsThickening.inclusion B S hS hH))))
    (halgebra : Nonempty (SmallEtaleTwoIso B S hS
      (smallEtaleComp B S hS (smallEtaleRingedToposHom B S hS pY') Φ)
      (smallEtaleRingedToposHom B S hS pX'))) :
    ∃! f' : X' ⟶ Y', InducesSmallEtaleRingedToposHom B S hS f' Φ ∧
      IsThickening.inclusion B S hS hG ≫ f' = f ≫ IsThickening.inclusion B S hS hH ∧
      f' ≫ pY' = pX' := by
  obtain ⟨f', hf', huniq⟩ := isRecoveredFromSmallEtale_of_mono_toSpecΓ B S hS hSmono pX' pY' Φ
    (isLocallyRinged_of_thickeningSquare B S hS hG hH f Φ hsquare) halgebra
  obtain ⟨h₁, h₂⟩ :=
    inclusion_comp_and_comp_structure_of_induces B S hS hG hH pX' pY' f Φ hsquare halgebra f' hf'
  exact ⟨f', ⟨hf', h₁, h₂⟩, fun y hy => huniq y hy.1⟩

/-- **Stacks 05ZN with the recovery of morphisms over the base and the local ringedness of
`Φ` taken as arguments.**

This is the shape in which the statement was first written.  Both arguments are now available
without being assumed — `hlocal` from the commuting square by
`AlgebraicGeometry.Space.isLocallyRinged_of_thickeningSquare`, and `hKL` for a base scheme whose
canonical morphism to the spectrum of its global functions is a monomorphism by
`AlgebraicGeometry.Space.isRecoveredFromSmallEtale_of_mono_toSpecΓ` — so the tag is registered on
`AlgebraicGeometry.Space.existsUnique_thickeningHom` above rather than here.  This form is kept
because the declarations below are stated in terms of it. -/
@[stacks 05ZN "that the recovered morphism is a morphism of thickenings over the base and that \
the pair is unique, with the recovery of morphisms over the base taken as an argument \
(`IsRecoveredFromSmallEtale`, which is Stacks 04KL over a base) and with the locally ringed \
condition on (f_spaces,etale, alpha) taken as an argument, since the latter needs the \
structure-sheaf half of 05ZM"]
theorem existsUnique_thickeningHom_of_isLocallyRinged (hKL : IsRecoveredFromSmallEtale B S hS)
    (hG : IsThickening B S hS X' G) (hH : IsThickening B S hS Y' H)
    (pX' : X' ⟶ T) (pY' : Y' ⟶ T)
    (f : IsThickening.space B S hS hG ⟶ IsThickening.space B S hS hH)
    (Φ : RingedToposHom (smallEtaleRingedTopos B S hS X') (smallEtaleRingedTopos B S hS Y'))
    (hlocal : Φ.IsLocallyRinged)
    (hsquare : Nonempty (SmallEtaleTwoIso B S hS
      (smallEtaleComp B S hS Φ
        (smallEtaleRingedToposHom B S hS (IsThickening.inclusion B S hS hG)))
      (smallEtaleRingedToposHom B S hS (f ≫ IsThickening.inclusion B S hS hH))))
    (halgebra : Nonempty (SmallEtaleTwoIso B S hS
      (smallEtaleComp B S hS (smallEtaleRingedToposHom B S hS pY') Φ)
      (smallEtaleRingedToposHom B S hS pX'))) :
    ∃! f' : X' ⟶ Y', InducesSmallEtaleRingedToposHom B S hS f' Φ ∧
      IsThickening.inclusion B S hS hG ≫ f' = f ≫ IsThickening.inclusion B S hS hH ∧
      f' ≫ pY' = pX' := by
  obtain ⟨f', hf', huniq⟩ := hKL pX' pY' Φ hlocal halgebra
  obtain ⟨h₁, h₂⟩ :=
    inclusion_comp_and_comp_structure_of_induces B S hS hG hH pX' pY' f Φ hsquare halgebra f' hf'
  exact ⟨f', ⟨hf', h₁, h₂⟩, fun y hy => huniq y hy.1⟩

/-- **Stacks 05ZN.**  Let `B` be a big fppf site, `S` a scheme in it and `T` an algebraic space
over `S`.  Let `G ⊂ X'` and `H ⊂ Y'` be thickenings of algebraic spaces over `T`, with structure
morphisms `p_{X'} : X' ⟶ T` and `p_{Y'} : Y' ⟶ T`, and let `f : X ⟶ Y` be a morphism of the two
closed subspaces.  Let `Φ = (f_{spaces,étale}, α)` be a morphism of the small étale ringed topoi of
`X'` and `Y'` which is compatible with the two inclusions (the source's commuting square for
`α`, `f^♯`, `i_X^♯` and `i_Y^♯`) and with the two structure morphisms to `T` (the source's
hypothesis that `α` is a map of `𝒪_T`-algebras).  Then there is exactly one morphism
`f' : X' ⟶ Y'` inducing `Φ`, that is with `α = (f')^♯`, and `(f, f')` is a morphism of
thickenings over `T`: `f' ∘ i_X = i_Y ∘ f` and `p_{Y'} ∘ f' = p_{X'}`.

Nothing is assumed of the base scheme: the recovery of morphisms over the base is
`AlgebraicGeometry.Space.isRecoveredFromSmallEtale_holds`, Stacks 04KL over an arbitrary base, the
locality of `Φ` is derived from the square by
`AlgebraicGeometry.Space.isLocallyRinged_of_thickeningSquare`, and the two equations and the
uniqueness come from the faithfulness half of Tag 04KL,
`AlgebraicGeometry.Space.eq_of_inducesCommonSmallEtaleRingedToposHom`.  This supersedes
`AlgebraicGeometry.Space.existsUnique_thickeningHom`, which carries a hypothesis on the base. -/
@[stacks 05ZN "the whole lemma, over an arbitrary base scheme: the morphism (f_spaces,etale, \
alpha) of the small etale ringed topoi of the ambient spaces, compatible with the inclusions and \
with the structure morphisms to the base space, is induced by exactly one f', and (f, f') is a \
morphism of thickenings over the base space"]
theorem existsUnique_thickeningHom_of_ringedToposHom
    (hG : IsThickening B S hS X' G) (hH : IsThickening B S hS Y' H)
    (pX' : X' ⟶ T) (pY' : Y' ⟶ T)
    (f : IsThickening.space B S hS hG ⟶ IsThickening.space B S hS hH)
    (Φ : RingedToposHom (smallEtaleRingedTopos B S hS X') (smallEtaleRingedTopos B S hS Y'))
    (hsquare : Nonempty (SmallEtaleTwoIso B S hS
      (smallEtaleComp B S hS Φ
        (smallEtaleRingedToposHom B S hS (IsThickening.inclusion B S hS hG)))
      (smallEtaleRingedToposHom B S hS (f ≫ IsThickening.inclusion B S hS hH))))
    (halgebra : Nonempty (SmallEtaleTwoIso B S hS
      (smallEtaleComp B S hS (smallEtaleRingedToposHom B S hS pY') Φ)
      (smallEtaleRingedToposHom B S hS pX'))) :
    ∃! f' : X' ⟶ Y', InducesSmallEtaleRingedToposHom B S hS f' Φ ∧
      IsThickening.inclusion B S hS hG ≫ f' = f ≫ IsThickening.inclusion B S hS hH ∧
      f' ≫ pY' = pX' := by
  -- Stacks 04KL over an arbitrary base (`AlgebraicGeometry.Space.isRecoveredFromSmallEtale_holds`
  -- downstream), proved here directly since that file imports this one.
  have hKL : IsRecoveredFromSmallEtale B S hS := by
    intro A P Q pP pQ ψ hψ hcompat
    obtain ⟨t⟩ := hcompat
    exact existsUnique_induces_of_isChartOverBase B S hS hψ
      (isChartOverBase_of_twoCompatible pP pQ ψ t)
  exact existsUnique_thickeningHom_of_isLocallyRinged B S hS hKL hG hH
    pX' pY' f Φ (isLocallyRinged_of_thickeningSquare B S hS hG hH f Φ hsquare) hsquare halgebra

end Thickenings

end AlgebraicGeometry.Space

end
