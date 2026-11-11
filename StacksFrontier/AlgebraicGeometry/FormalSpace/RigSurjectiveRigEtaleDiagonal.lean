module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Flat
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalModificationBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveDvrCriterion

/-!
# Rig-surjectivity from a rig-étale rig-surjective diagonal

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
formal algebraic spaces over `S` with `X` and `Y` locally Noetherian, `f` locally of finite
type, and the relative diagonal `Δ_f : X ⟶ X ×_Y X` rig-étale and rig-surjective. **Stacks
0GDA** says that `f` is rig-surjective if and only if every adic morphism `Spf R ⟶ Y`, with
`R` a complete discrete valuation ring, lifts to a morphism `Spf R ⟶ X` — that is, without
passing to an extension of `R`.

The right-hand side is `AlgebraicGeometry.FormalSpace.FactorsAdicCompleteDvrPoints`, which
`StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveDvrCriterion` introduces for
**Stacks 0AR0**, the same biconditional under the hypothesis that `f` is a monomorphism rather
than that `Δ_f` is rig-étale and rig-surjective. The direction the source calls trivial is
therefore already available in the library and needs none of the hypotheses of Stacks 0GDA:
it is `AlgebraicGeometry.FormalSpace.isRigSurjective_of_factorsAdicCompleteDvrPoints`, which
takes the extension asked for by Definition 0AQQ to be `R` itself.

The substantial direction is the source's argument. Given an adic point `p : Spf R ⟶ Y`,
rig-surjectivity of `f` produces an extension `R ⊂ R'` of complete discrete valuation rings
and a lift `Spf R' ⟶ X`. Form the fibre product `W = Spf R ×_Y X` with projections
`p₁ : W ⟶ Spf R` and `p₂ : W ⟶ X`. Then

* `p₁` is locally of finite type, being a base change of `f` (**Stacks 0AQ5**);
* `W` is locally Noetherian (**Stacks 0AQ8**);
* `Δ_{p₁}` is a base change of `Δ_f` along the comparison morphism `W ×_{Spf R} W ⟶ X ×_Y X`,
  which is itself a base change of `p` and hence adic. So `Δ_{p₁}` is rig-étale (**Stacks
  0GD1**) and rig-surjective (**Stacks 0AQS**).

**Stacks 0GD9** therefore applies to `p₁`: the flat part `W' ⊂ W` of `W` over `R`, which is
the closed subspace of **Stacks 0GD8**, is either `Spf R` or empty. The lift `Spf R' ⟶ W`
determined by `Spf R' ⟶ Spf R` and `Spf R' ⟶ X` is flat over `R`, so it factors through `W'`
by the universal property of the flat part; hence `W'` is not empty, so `W' ⟶ Spf R` is an
isomorphism and its inverse composed with `W' ⟶ W ⟶ X` is the lift of `p` wanted.

## Main definitions

* `AlgebraicGeometry.FormalSpace.RigEtaleIsStableUnderRepresentableBaseChange`: **Stacks
  0GD1**, read through Stacks 0AQ3, stated for every cartesian square at once.
* `AlgebraicGeometry.FormalSpace.FormalSpectrumOfCompleteDvrIsLocallyNoetherian`: that the
  formal spectrum of a complete discrete valuation ring is locally Noetherian, which is
  **Stacks 0AKY** for `Spf` of a Noetherian adic ring.
* `AlgebraicGeometry.FormalSpace.FormalSpectrumMapOfDvrExtensionIsFlat`: that the formal
  spectrum map of an extension of complete discrete valuation rings is flat, which is **Stacks
  0GCD** applied to a flat presenting homomorphism.
* `AlgebraicGeometry.FormalSpace.FlatPartOfRigEtaleDiagonalIsBaseOrPointless`: **Stacks 0GD9**
  together with the existence statement of **Stacks 0GD8** that it presupposes.

## Main results

* `AlgebraicGeometry.FormalSpace.IsRigSurjective.of_isPullback_of_representable`: **Stacks
  0AQS** with the hypotheses on the morphism one bases along weakened to representability by
  algebraic spaces, and with the local finite typeness of `f` dropped.
* `AlgebraicGeometry.FormalSpace.factorsAdicCompleteDvrPoints_of_rigEtaleDiagonal`:
  the substantial direction of Stacks 0GDA, from five inputs stated as hypotheses — see below.
* `AlgebraicGeometry.FormalSpace.isRigSurjective_iff_factorsAdicCompleteDvrPoints_of_diagonal`:
  the equivalence of Stacks 0GDA from the same five inputs.

Stacks 0GDA itself, under exactly the source's hypotheses and with every input proved, is
`isRigSurjective_iff_factorsAdicCompleteDvrPoints_of_rigEtale_diagonal`
in `StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveRigEtaleDiagonalCriterion`, which
carries the tag. The two declarations here are kept for the statements downstream which still
take the five inputs as hypotheses.

## Implementation notes

The quantifier interface of the two lifting conditions is the one of
`AlgebraicGeometry.FormalSpace.IsRigSurjective`: the complete discrete valuation ring `R` is
presented over `S` by an `AlgebraicGeometry.FormalSpace.QuotientSystem`, completeness is
`IsAdicComplete` for the maximal ideal whose adic topology is the one `R` carries, weak
admissibility of that topology is quantified over rather than derived because it is what
`AlgebraicGeometry.FormalSpace.formalSpectrumMap` consumes, and adicness of a morphism is
rendered by representability by algebraic spaces, which **Stacks 0AQ3** identifies with
adicness for a morphism of locally adic\* formal algebraic spaces.

`AlgebraicGeometry.FormalSpace.IsRigSurjective.of_isPullback_of_representable` is a
strengthening of `AlgebraicGeometry.FormalSpace.IsRigSurjective.of_isPullback`, this library's
Stacks 0AQS, and is needed because the comparison morphism `W ×_{Spf R} W ⟶ X ×_Y X` one bases
`Δ_f` along is not known to be locally of finite type: that would need the adic point
`Spf R ⟶ Y` to be, which Definition 0AQQ does not ask of it. Inspecting the proof of Stacks
0AQS shows that local finite typeness of the morphism one bases along is used only through
representability by algebraic spaces, and that local finite typeness of `f` is used only for
the conclusion that the base change is locally of finite type, which is not needed here. Both
are therefore dropped.

The two categorical cartesian squares are
`AlgebraicGeometry.FormalSpace.isPullback_selfPullbackMap` and
`AlgebraicGeometry.FormalSpace.isPullback_diagonal_selfPullbackMap` of
`StacksFrontier.AlgebraicGeometry.FormalSpace.FormalModificationBaseChange`, proved there for an
arbitrary category with fibre products: they say that `W ×_Z W ⟶ X ×_Y X` is a base change of
`Z ⟶ Y` and that `Δ_p` is a base change of `Δ_f` along it. They are the exact statements the
source means by "`Δ_p` is the base change of `Δ_f`".

### The five inputs taken as hypotheses

Each is a theorem of the source, each is stated for all of its own data rather than for the
`f` of the conclusion, and none of them mentions the conclusion. The library now proves the
instances of each that Stacks 0GDA needs (all in the namespace `AlgebraicGeometry.FormalSpace`),
and `isRigSurjective_iff_factorsAdicCompleteDvrPoints_of_rigEtale_diagonal` uses those proofs
instead:

* `isLocallyNoetherian_of_isPullback'` for Stacks 0AQ8;
* `isRigEtale_pullback_snd_of_isLocallyNoetherian` for Stacks 0GD1;
* `isLocallyNoetherian_formalSpectrum_of_isAdicComplete` for Stacks 0AKY;
* `isFlat_formalSpectrumMap_of_isExtension` for Stacks 0GCD;
* `exists_flatPart_of_isLocallyNoetherian_of_isAdicComplete` and
  `isIso_or_isInitial_flatPart_of_isRigEtale_of_isRigSurjective_diagonal` for Stacks 0GD8 and
  Stacks 0GD9.

The inputs as stated here:

* `h0AQ8` is `AlgebraicGeometry.FormalSpace.FibreProductIsLocallyNoetherian`, **Stacks 0AQ8**,
  reused verbatim from `StacksFrontier.AlgebraicGeometry.FormalSpace.FormalModificationBaseChange`
  where it is carried for Stacks 0GDN.
* `h0GD1` is **Stacks 0GD1**, that a base change of a rig-étale morphism along an adic
  morphism is rig-étale, with "adic" read as representability by algebraic spaces, which is
  what Stacks 0AQ3 identifies it with for the locally Noetherian — hence locally adic\* —
  spaces the statement displays. The library proves Stacks 0GD1 for the chosen fibre product
  as `AlgebraicGeometry.FormalSpace.isRigEtale_pullback_snd_of_isLocallyNoetherian`; the
  hypothesis asks it of every cartesian square.
* `hSpfNoeth` is that `Spf A` is locally Noetherian for `A` a complete discrete valuation
  ring. `A` is Noetherian and its topology adic, so `Spf A` is a Noetherian affine formal
  algebraic space and in particular carries a one-member atlas as in Definition 0AIM.
* `hextFlat` is that `Spf R' ⟶ Spf R` is flat for an extension `R ⊂ R'` of complete discrete
  valuation rings. The ring-theoretic content is that `R'` is a flat `R`-module, which holds
  because `R` is a discrete valuation ring and `R'` is torsion free over it; turning that into
  `AlgebraicGeometry.FormalSpace.IsFlat` of the induced map of formal spectra is **Stacks
  0GCD**, which the library carries as
  `AlgebraicGeometry.FormalSpace.isFlat_formalSpectrumMap_of_isExtension`.
* `h0GD9` is **Stacks 0GD9** bundled with the existence statement of **Stacks 0GD8** that its
  phrase "let `X' ⊂ X` be as in Lemma 0GD8" presupposes: the flat part `ι : W' ⟶ W` with its
  closed immersion, flatness and universal property, and then the dichotomy, as the single
  statement the source's sentence makes. The library proves Stacks 0GD8 as
  `AlgebraicGeometry.FormalSpace.exists_flatPart_of_isLocallyNoetherian_of_isAdicComplete`
  and the dichotomy of Stacks 0GD9 as
  `isIso_or_isInitial_flatPart_of_isRigEtale_of_isRigSurjective_diagonal`.

The dichotomy is rendered as `IsIso (ι ≫ q)` — the source's "`X' = Spf(A)`", there being no
other morphism `X' ⟶ Spf(A)` in play — or the absence of points of `W'` out of formal spectra
of discrete valuation rings. That second disjunct is what the source's "`X' = ∅`" is used for,
and it is a consequence of emptiness. The unconditional proof renders emptiness as initiality
of `W'` and excludes it by `AlgebraicGeometry.FormalSpace.not_isInitial_of_hom_formalSpectrum`.

Local Noetherianity of `Y` is not used: it enters the source's proof only through the aside
that `X ×_Y X` is locally Noetherian, and the route taken here obtains that from local
Noetherianity of `X` and local finite typeness of `f` by Stacks 0AQ8. It is kept as `_hY`
because it is a hypothesis of Stacks 0GDA. Local finite typeness of `Δ_f`, which the source's
aside supplies by Formal Spaces, Lemma 0AN2, is likewise not needed: the only place Stacks
0AQS would consume it is the hypothesis dropped by
`AlgebraicGeometry.FormalSpace.IsRigSurjective.of_isPullback_of_representable`.

## References

* [Stacks Project, Tag 0AKY](https://stacks.math.columbia.edu/tag/0AKY)
* [Stacks Project, Tag 0AN2](https://stacks.math.columbia.edu/tag/0AN2)
* [Stacks Project, Tag 0AQ3](https://stacks.math.columbia.edu/tag/0AQ3)
* [Stacks Project, Tag 0AQ5](https://stacks.math.columbia.edu/tag/0AQ5)
* [Stacks Project, Tag 0AQ8](https://stacks.math.columbia.edu/tag/0AQ8)
* [Stacks Project, Tag 0AQQ](https://stacks.math.columbia.edu/tag/0AQQ)
* [Stacks Project, Tag 0AQS](https://stacks.math.columbia.edu/tag/0AQS)
* [Stacks Project, Tag 0AR0](https://stacks.math.columbia.edu/tag/0AR0)
* [Stacks Project, Tag 0GCD](https://stacks.math.columbia.edu/tag/0GCD)
* [Stacks Project, Tag 0GD1](https://stacks.math.columbia.edu/tag/0GD1)
* [Stacks Project, Tag 0GD8](https://stacks.math.columbia.edu/tag/0GD8)
* [Stacks Project, Tag 0GD9](https://stacks.math.columbia.edu/tag/0GD9)
* [Stacks Project, Tag 0GDA](https://stacks.math.columbia.edu/tag/0GDA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Base change of rig-surjectivity along a representable morphism -/

/-- **Stacks 0AQS**, with both hypotheses that
`AlgebraicGeometry.FormalSpace.IsRigSurjective.of_isPullback` makes on local finite typeness
dropped. A base change of a rig-surjective morphism of formal algebraic spaces over `S` along
a morphism representable by algebraic spaces is rig-surjective.

An adic point of `Z` out of the formal spectrum of a complete discrete valuation ring becomes,
after composition with `g`, an adic point of `Y`, because `g` is representable by algebraic
spaces; a lift of it to `X` over an extension of complete discrete valuation rings pairs with
the point of `Z` to give a lift to `W`. Local finite typeness of `g` enters Stacks 0AQS only
through this use of representability, and local finite typeness of `f` only through the
conclusion that the base change is locally of finite type, which is not asserted here. -/
@[stacks 0AQS "rig-surjectivity alone, for a base change along a morphism assumed only \
representable by algebraic spaces rather than locally of finite type"]
theorem IsRigSurjective.of_isPullback_of_representable {W X Y Z : FppfSheaf B S hS}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y} (sq : IsPullback p q g f)
    (hgrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS g.hom)
    (hsf : IsRigSurjective B S hS f) :
    IsRigSurjective B S hS p := by
  intro R _ _ _ _ _ _ hRadic hRcomplete hRweak D pt hpt
  obtain ⟨R', hR'ring, hR'dom, hR'dvr, hR'alg, hR'ext, hR'top, hR'topring, hR'lin, hR'adic,
    hR'complete, D', e, x, he, hx⟩ :=
    hsf R hRadic hRcomplete hRweak D (pt ≫ g)
      (Space.isRepresentableByAlgebraicSpacesULift_comp B S hS pt.hom g.hom hpt hgrep)
  exact ⟨R', hR'ring, hR'dom, hR'dvr, hR'alg, hR'ext, hR'top, hR'topring, hR'lin, hR'adic,
    hR'complete, D', e,
    sq.lift (formalSpectrumMap hRweak e ≫ pt) x (by rw [Category.assoc]; exact hx.symm),
    he, sq.lift_fst _ _ _⟩

/-! ### Stacks 0GD1, 0AKY, 0GCD and 0GD9 as statements -/

/-- **Stacks 0GD1** for every cartesian square at once, with adicness of the morphism one
bases along read as representability by algebraic spaces, which **Stacks 0AQ3** identifies it
with for locally adic\* — in particular locally Noetherian — formal algebraic spaces: a base
change of a rig-étale morphism of locally Noetherian formal algebraic spaces over `S` along an
adic morphism is rig-étale.

`AlgebraicGeometry.FormalSpace.isRigEtale_pullback_snd_of_isLocallyNoetherian` proves this for
the chosen fibre product. -/
abbrev RigEtaleIsStableUnderRepresentableBaseChange : Prop :=
  ∀ {W X Y Z : FppfSheaf B S hS} {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y},
    IsPullback p q g f →
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS g.hom →
    IsLocallyNoetherian B S hS X → IsLocallyNoetherian B S hS Y →
    IsLocallyNoetherian B S hS Z → IsRigEtale B S hS f → IsRigEtale B S hS p

/-- **Stacks 0AKY** for the formal spectrum of a complete discrete valuation ring `A`: since
`A` is Noetherian and its topology adic, `Spf A` is a Noetherian affine formal algebraic space
and so is locally Noetherian. This is proved, for any Noetherian adic complete ring, as
`AlgebraicGeometry.FormalSpace.isLocallyNoetherian_formalSpectrum_of_isAdicComplete`. -/
abbrev FormalSpectrumOfCompleteDvrIsLocallyNoetherian : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A],
    _root_.IsAdic (IsLocalRing.maximalIdeal A) →
    IsAdicComplete (IsLocalRing.maximalIdeal A) A →
    ∀ D : QuotientSystem B S hS A, IsLocallyNoetherian B S hS (formalSpectrum D)

/-- **Stacks 0GCD** for an extension `A ⊂ A'` of complete discrete valuation rings: `A'` is a
flat `A`-module, being torsion free over a discrete valuation ring, so the induced morphism
`Spf A' ⟶ Spf A` of formal spectra is flat in the sense of Definition 0GCC. This is proved as
`AlgebraicGeometry.FormalSpace.isFlat_formalSpectrumMap_of_isExtension`. -/
abbrev FormalSpectrumMapOfDvrExtensionIsFlat : Prop :=
  ∀ (A A' : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] [CommRing A'] [IsDomain A']
    [IsDiscreteValuationRing A'] [TopologicalSpace A'] [IsTopologicalRing A']
    [IsLinearTopology A' A'] [Algebra A A'] [IsDiscreteValuationRing.IsExtension A A'],
    _root_.IsAdic (IsLocalRing.maximalIdeal A) →
    IsAdicComplete (IsLocalRing.maximalIdeal A) A →
    _root_.IsAdic (IsLocalRing.maximalIdeal A') →
    IsAdicComplete (IsLocalRing.maximalIdeal A') A' →
    ∀ (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
      (D' : QuotientSystem B S hS A') (e : ContinuousHom D D'),
      e.toRingHom = algebraMap A A' → IsFlat B S hS (formalSpectrumMap hA e)

/-- **Stacks 0GD9**, bundled with the existence statement of **Stacks 0GD8** which its phrase
"let `X' ⊂ X` be as in Lemma 0GD8" presupposes. Let `A` be a complete discrete valuation ring
and let `q : W ⟶ Spf A` be a morphism of formal algebraic spaces over `S` with `W` locally
Noetherian and `q` locally of finite type, and suppose the relative diagonal
`Δ_q : W ⟶ W ×_{Spf A} W` is rig-étale and rig-surjective. Then the flat part `ι : W' ⟶ W` of
Stacks 0GD8 exists — a closed immersion with `W'` flat over `A` through which every locally
Noetherian `Z ⟶ W` flat over `A` factors — and `W'` is either `Spf A` or empty.

"`W' = Spf A`" is `IsIso (ι ≫ q)`, there being no other morphism `W' ⟶ Spf A` in play.
"`W' = ∅`" is rendered as the absence of points of `W'` out of formal spectra of discrete
valuation rings, which is the consequence of emptiness the source's argument uses. -/
abbrev FlatPartOfRigEtaleDiagonalIsBaseOrPointless : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A],
    _root_.IsAdic (IsLocalRing.maximalIdeal A) →
    IsAdicComplete (IsLocalRing.maximalIdeal A) A →
    ∀ (D : QuotientSystem B S hS A) (W : FppfSheaf B S hS) (q : W ⟶ formalSpectrum D),
      IsLocallyNoetherian B S hS W → IsLocallyOfFiniteType B S hS q →
      IsRigEtale B S hS (pullback.diagonal q) →
      IsRigSurjective B S hS (pullback.diagonal q) →
      ∃ (W' : FppfSheaf B S hS) (ι : W' ⟶ W),
        IsClosedImmersion B S hS ι ∧ IsFlat B S hS (ι ≫ q) ∧
        (∀ (Z : FppfSheaf B S hS) (z : Z ⟶ W), IsLocallyNoetherian B S hS Z →
            IsFlat B S hS (z ≫ q) → ∃ r : Z ⟶ W', r ≫ ι = z) ∧
        (IsIso (ι ≫ q) ∨
          ∀ (A' : Type u) [CommRing A'] [IsDomain A'] [IsDiscreteValuationRing A']
            [TopologicalSpace A'] (D' : QuotientSystem B S hS A'),
            (formalSpectrum D' ⟶ W') → False)

/-! ### Stacks 0GDA -/

/-- The substantial direction of Stacks 0GDA, from five inputs stated as hypotheses; Stacks
0GDA itself, with every input proved, is
`isRigSurjective_iff_factorsAdicCompleteDvrPoints_of_rigEtale_diagonal`.
Let `f : X ⟶ Y` be a
morphism of formal algebraic spaces over `S` with `X` locally Noetherian, `f` locally of finite
type and `Δ_f : X ⟶ X ×_Y X` rig-étale and rig-surjective. If `f` is rig-surjective then every
adic morphism `Spf R ⟶ Y`, with `R` a complete discrete valuation ring, lifts to `X` over `R`
itself.

Rig-surjectivity provides an extension `R ⊂ R'` of complete discrete valuation rings and a
lift `Spf R' ⟶ X` of the point `p`. In the fibre product `W = Spf R ×_Y X` the projection
`p₁ : W ⟶ Spf R` is locally of finite type by Stacks 0AQ5 and `W` is locally Noetherian by
`h0AQ8`, which is Stacks 0AQ8; the relative diagonal `Δ_{p₁}` is a base change of `Δ_f` along
the comparison morphism `W ×_{Spf R} W ⟶ X ×_Y X`, which is a base change of `p` and hence
representable by algebraic spaces, so `Δ_{p₁}` is rig-étale by `h0GD1`, which is Stacks 0GD1,
and rig-surjective by Stacks 0AQS. Hence `h0GD9`, which is Stacks 0GD9 together with Stacks
0GD8, gives the flat part `ι : W' ⟶ W` of `W` over `R` and the dichotomy. The lift
`Spf R' ⟶ W` is flat over `R` by `hextFlat`, which is Stacks 0GCD, and `Spf R'` is locally
Noetherian by `hSpfNoeth`, which is Stacks 0AKY, so the lift factors through `W'` and the
second alternative of the dichotomy is impossible. Therefore `ι ≫ p₁` is an isomorphism and
`inv (ι ≫ p₁) ≫ ι ≫ p₂` is the factorisation wanted.

Local Noetherianity of `Y` is a hypothesis of Stacks 0GDA and is kept as `_hY`; the proof does
not use it, obtaining local Noetherianity of `X ×_Y X` from that of `X` instead. -/
theorem factorsAdicCompleteDvrPoints_of_rigEtaleDiagonal
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyNoetherian B S hS X) (_hY : IsLocallyNoetherian B S hS Y)
    (hft : IsLocallyOfFiniteType B S hS f)
    (hdiagEtale : IsRigEtale B S hS (pullback.diagonal f))
    (hdiagSurj : IsRigSurjective B S hS (pullback.diagonal f))
    (h0AQ8 : FibreProductIsLocallyNoetherian B S hS)
    (h0GD1 : RigEtaleIsStableUnderRepresentableBaseChange B S hS)
    (hSpfNoeth : FormalSpectrumOfCompleteDvrIsLocallyNoetherian B S hS)
    (hextFlat : FormalSpectrumMapOfDvrExtensionIsFlat B S hS)
    (h0GD9 : FlatPartOfRigEtaleDiagonalIsBaseOrPointless B S hS)
    (hrig : IsRigSurjective B S hS f) :
    FactorsAdicCompleteDvrPoints B S hS f := by
  intro R _ _ _ _ _ _ hRadic hRcomplete hRweak D pt hpt
  obtain ⟨R', hR'ring, hR'dom, hR'dvr, hR'alg, hR'ext, hR'top, hR'topring, hR'lin, hR'adic,
    hR'complete, D', e, x, he, hx⟩ := hrig R hRadic hRcomplete hRweak D pt hpt
  let : CommRing R' := hR'ring
  let : IsDomain R' := hR'dom
  let : IsDiscreteValuationRing R' := hR'dvr
  let : Algebra R R' := hR'alg
  let : IsDiscreteValuationRing.IsExtension R R' := hR'ext
  let : TopologicalSpace R' := hR'top
  let : IsTopologicalRing R' := hR'topring
  let : IsLinearTopology R' R' := hR'lin
  -- The fibre product `W = Spf R ×_Y X` and its two projections.
  have sq : IsPullback (pullback.fst pt f) (pullback.snd pt f) pt f :=
    IsPullback.of_hasPullback pt f
  -- `p₁` is locally of finite type by Stacks 0AQ5 and `Spf R` is locally Noetherian.
  have hp₁ft : IsLocallyOfFiniteType B S hS (pullback.fst pt f) :=
    IsLocallyOfFiniteType.of_isPullback B S hS sq hft
  have hSpfR : IsLocallyNoetherian B S hS (formalSpectrum D) :=
    hSpfNoeth R hRadic hRcomplete D
  have hW : IsLocallyNoetherian B S hS (pullback pt f) := h0AQ8 sq hSpfR hft
  -- `X ×_Y X` and `W ×_{Spf R} W` are locally Noetherian by Stacks 0AQ8.
  have hfstff : IsLocallyOfFiniteType B S hS (pullback.fst f f) :=
    IsLocallyOfFiniteType.of_isPullback B S hS (IsPullback.of_hasPullback f f) hft
  have hXX : IsLocallyNoetherian B S hS (pullback f f) :=
    h0AQ8 (IsPullback.of_hasPullback f f) hX hft
  have hWW : IsLocallyNoetherian B S hS (pullback (pullback.fst pt f) (pullback.fst pt f)) :=
    h0AQ8 (isPullback_selfPullbackMap sq).flip hSpfR
      (IsLocallyOfFiniteType.comp B S hS _ _ hfstff hft)
  -- The comparison morphism is a base change of the adic point, hence representable.
  have hmrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (pullback.map (pullback.fst pt f) (pullback.fst pt f) f f (pullback.snd pt f)
        (pullback.snd pt f) pt sq.w sq.w).hom :=
    Space.isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS _ _ _ _
      (isPullback_hom_of_isPullback B S hS (isPullback_selfPullbackMap sq)) hpt
  -- `Δ_{p₁}` is a base change of `Δ_f`, hence rig-étale and rig-surjective.
  have sqd := isPullback_diagonal_selfPullbackMap sq
  have hdEtale : IsRigEtale B S hS (pullback.diagonal (pullback.fst pt f)) :=
    h0GD1 sqd hmrep hX hXX hWW hdiagEtale
  have hdSurj : IsRigSurjective B S hS (pullback.diagonal (pullback.fst pt f)) :=
    IsRigSurjective.of_isPullback_of_representable B S hS sqd hmrep hdiagSurj
  -- Stacks 0GD9 for the base change.
  obtain ⟨W', ι, _hι, _hιflat, huniv, hdich⟩ :=
    h0GD9 R hRadic hRcomplete D (pullback pt f) (pullback.fst pt f) hW hp₁ft hdEtale hdSurj
  -- The lift of the point to the fibre product is flat over `R`, so factors through `W'`.
  have hliftfst : sq.lift (formalSpectrumMap hRweak e) x hx.symm ≫ pullback.fst pt f =
      formalSpectrumMap hRweak e := sq.lift_fst _ _ _
  have hliftflat : IsFlat B S hS
      (sq.lift (formalSpectrumMap hRweak e) x hx.symm ≫ pullback.fst pt f) := by
    rw [hliftfst]
    exact hextFlat R R' hRadic hRcomplete hR'adic hR'complete hRweak D D' e he
  obtain ⟨r, -⟩ := huniv (formalSpectrum D') (sq.lift (formalSpectrumMap hRweak e) x hx.symm)
    (hSpfNoeth R' hR'adic hR'complete D') hliftflat
  -- Hence `W'` has a point and the dichotomy forces `ι ≫ p₁` to be an isomorphism.
  have hiso : IsIso (ι ≫ pullback.fst pt f) := by
    rcases hdich with hdich | hempty
    · exact hdich
    · exact absurd (hempty R' D') (fun h => h r)
  let : IsIso (ι ≫ pullback.fst pt f) := hiso
  have key : (ι ≫ pullback.snd pt f) ≫ f = (ι ≫ pullback.fst pt f) ≫ pt := by
    rw [Category.assoc, Category.assoc, sq.w]
  refine ⟨inv (ι ≫ pullback.fst pt f) ≫ ι ≫ pullback.snd pt f, ?_⟩
  rw [Category.assoc, key, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

/-- The equivalence of Stacks 0GDA from five inputs stated as hypotheses; Stacks 0GDA itself,
with every input proved, is
`isRigSurjective_iff_factorsAdicCompleteDvrPoints_of_rigEtale_diagonal`.
Let `f : X ⟶ Y` be a morphism of formal
algebraic spaces over `S` with `X` and `Y` locally Noetherian, `f` locally of finite type and
the relative diagonal `Δ_f : X ⟶ X ×_Y X` rig-étale and rig-surjective. Then `f` is
rig-surjective if and only if every adic morphism `Spf R ⟶ Y`, with `R` a complete discrete
valuation ring, lifts to a morphism `Spf R ⟶ X`.

The direction the source calls trivial is
`AlgebraicGeometry.FormalSpace.isRigSurjective_of_factorsAdicCompleteDvrPoints`, which needs
none of the hypotheses. The five inputs are used by the other direction only; see
the module docstring. -/
theorem isRigSurjective_iff_factorsAdicCompleteDvrPoints_of_diagonal
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y)
    (hft : IsLocallyOfFiniteType B S hS f)
    (hdiagEtale : IsRigEtale B S hS (pullback.diagonal f))
    (hdiagSurj : IsRigSurjective B S hS (pullback.diagonal f))
    (h0AQ8 : FibreProductIsLocallyNoetherian B S hS)
    (h0GD1 : RigEtaleIsStableUnderRepresentableBaseChange B S hS)
    (hSpfNoeth : FormalSpectrumOfCompleteDvrIsLocallyNoetherian B S hS)
    (hextFlat : FormalSpectrumMapOfDvrExtensionIsFlat B S hS)
    (h0GD9 : FlatPartOfRigEtaleDiagonalIsBaseOrPointless B S hS) :
    IsRigSurjective B S hS f ↔ FactorsAdicCompleteDvrPoints B S hS f :=
  ⟨factorsAdicCompleteDvrPoints_of_rigEtaleDiagonal B S hS f hX hY hft
    hdiagEtale hdiagSurj h0AQ8 h0GD1 hSpfNoeth hextFlat h0GD9,
    isRigSurjective_of_factorsAdicCompleteDvrPoints B S hS f⟩

end AlgebraicGeometry.FormalSpace

end
