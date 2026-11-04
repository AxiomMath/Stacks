module

public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.ImpurityFlatAscent
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityEtaleMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityFlatDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFiniteTypeModuleLocus

/-!
# Purity implies universal purity for a flat module

In the standing situation of Stacks 0CV6 — a finite type decent morphism `f : X ⟶ Y` of
algebraic spaces over a scheme `S`, a finite type quasi-coherent `𝒪_X`-module `ℱ` and a point
`y` of `Y` — purity of `ℱ` above `y` upgrades to *universal* purity above `y` as soon as `ℱ` is
flat over `Y` along the fibre `f^{-1}(\{y\})`. This is Stacks 0CW4, and quantifying it over the
points of `Y` gives Stacks 0CW5: for a module flat over `Y`, purity relative to `Y` and
universal purity relative to `Y` coincide.

The source's proof has two paragraphs. The first replaces `Y` by `Spec(𝒪_{Y, ȳ})`, a flat
morphism from the spectrum of a strictly henselian local ring sending the closed point to `y`,
and invokes the descent of universal purity along a flat pointed base change, Stacks 0CVG part
(2). The second works over that base: Stacks 0CVW produces an étale `g : X' ⟶ X` with `X'`
affine, with `g(|X'|) ⊇ |X_y|` and with `Γ(X', g^*ℱ)` free over the base ring, whence
`g^*ℱ` is universally pure relative to the base by More on Flatness, Stacks 05K6; and then
Stacks 0CW3 transfers that universal purity down to `ℱ`, its containment hypothesis on the
relative assassin `Ass_{X/Y}(ℱ)` being supplied by Stacks 0CW3 part (2).

The transfer step — the use of both parts of Stacks 0CW3 over an affine local base — is proved
here. The production of the étale cover is carried; see the implementation notes.

## Main definitions

* `AlgebraicGeometry.Space.PurityStrictlyHenselianReduction`: the hypothesis carrying the
  passage to `Spec(𝒪_{Y, ȳ})` of the source's first paragraph together with the étale cover of
  Stacks 0CVW whose pullback is universally pure by Stacks 05K6.

## Main results

* `AlgebraicGeometry.Space.isUniversallyPureAbove_of_exists_etaleOverSource`: over an affine
  local base with closed point `y`, an étale morphism into the source whose image on points
  contains the fibre and along which `ℱ` pulls back to a universally pure module makes `ℱ`
  universally pure above `y`. This is the second paragraph of the proof of Stacks 0CW4 after
  the étale cover has been produced, and it is proved outright.
* `AlgebraicGeometry.Space.isUniversallyPureAbove_of_isPureAbove`: Stacks 0CW4 granting the
  strictly henselian reduction; the unconditional statement is
  `AlgebraicGeometry.Space.isUniversallyPureAbove_of_flat_of_isPureAbove`.
* `AlgebraicGeometry.Space.isUniversallyPureRelative_of_isPureRelative` and
  `AlgebraicGeometry.Space.isPureRelative_iff_isUniversallyPureRelative`: **Stacks 0CW5**, the
  substantive implication and the equivalence of the statement.

## Implementation notes

Two inputs of the source's proof are not available in this development at the generality the
proof uses them, and both are carried by the single named hypothesis
`AlgebraicGeometry.Space.PurityStrictlyHenselianReduction`, which asserts the existence of the
reduced situation together with the cover:

* Stacks 0CVW is available here only as
  `AlgebraicGeometry.Space.exists_affineChart_hasFreeSectionsAlongFibre`, which delivers the
  elementary étale neighbourhood of the base and the affine scheme with free sections at an
  affine étale chart of `Y` — not an `AlgebraicGeometry.Space.EtaleOverSource` of the
  situation. Stacks 05K6 is available only for schemes, as
  `AlgebraicGeometry.isUniversallyPureRelative_of_pushforward_isLocallyProjective`, and its
  conclusion is the scheme-level purity predicate, not
  `AlgebraicGeometry.Space.IsUniversallyPureAbove`. Turning the pair into an étale morphism of
  algebraic spaces over the base along which `ℱ` pulls back to a universally pure module needs
  a comparison of the two purity predicates which this development does not have; it is the
  last conjunct of the carried hypothesis.
* The reduction of the first paragraph needs, besides the descent of Stacks 0CVG part (2),
  that purity above `y` *ascend* to purity above the closed point of `Spec(𝒪_{Y, ȳ})`. The
  flat pointed base change `Spec(𝒪_{Y, ȳ}) ⟶ Y` is not quasi-finite, so Stacks 0CVF,
  `AlgebraicGeometry.Space.isPureAbove_baseChange_of_isQuasiFiniteAt`, does not apply, and the
  equivalent conditions of Stacks 0CVB which would give it are not proved here. It is the
  conjunct `IsPureAbove c.baseChange` of the carried hypothesis.

The hypothesis also carries the ascent data of Stacks 0CVA in the form Stacks 0CVG consumes it,
`AlgebraicGeometry.Space.HasFlatImpurityAscentData` — which includes the flatness of
`Spec(𝒪_{Y, ȳ}) ⟶ Y` at the closed point — and the affine locality of the reduced base,
`AlgebraicGeometry.Space.PrePureSituation.IsAffineLocalAt`. Strict henselianity of the local
ring appears nowhere in the carried statement: it is needed only to produce the cover, which is
carried, while the step proved here needs just an affine local base with closed point `y`.

Nothing beyond that single hypothesis is carried. In particular Stacks 0CW5 is deduced from
Stacks 0CW4 with no further hypothesis of any kind: it is the hypothesis of Stacks 0CW4 at each
point of `Y`, the flatness hypothesis of Stacks 0CW5 being flatness along every fibre at once.

Flatness of `ℱ` over `Y` at a point is membership of the relative flat locus
`AlgebraicGeometry.Space.flatLocus` of Stacks 0DLR, which is the condition Stacks 0CVW consumes
in this development; "flat over `Y`" in Stacks 0CW5 is membership of every point of `|X|`.

## References

* [Stacks Project, Tag 0CW4](https://stacks.math.columbia.edu/tag/0CW4)
* [Stacks Project, Tag 0CW5](https://stacks.math.columbia.edu/tag/0CW5)
* [Stacks Project, Tag 0CW3](https://stacks.math.columbia.edu/tag/0CW3)
* [Stacks Project, Tag 0CVG](https://stacks.math.columbia.edu/tag/0CVG)
* [Stacks Project, Tag 0CVW](https://stacks.math.columbia.edu/tag/0CVW)
* [Stacks Project, Tag 05K6](https://stacks.math.columbia.edu/tag/05K6)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

/-! ### The transfer step over an affine local base -/

/-- **The second paragraph of the proof of Stacks 0CW4**, from the étale cover onwards. Let `Y`
be affine local with closed point `y`, let `ℱ` be pure above `y`, and let `g : X' ⟶ X` be étale
over `Y`, with `X' ⟶ Y` decent and of finite type, such that the image of `|X'| → |X|` contains
the fibre `f^{-1}(\{y\})` and `g^*ℱ` is universally pure above `y`. Then `ℱ` is universally
pure above `y`.

Purity above `y` over the affine local base forces the whole relative assassin
`Ass_{X/Y}(ℱ)` into the image of `|X'| → |X|` by Stacks 0CW3 part (2), and with that
containment Stacks 0CW3 part (1) carries universal purity of `g^*ℱ` down to `ℱ`. -/
theorem isUniversallyPureAbove_of_exists_etaleOverSource (P : PrePureSituation.{u, u} B S hS)
    (hlocal : P.IsAffineLocalAt) (hpure : IsPureAbove P)
    (hcover : ∃ c : EtaleOverSource P,
      pointsMap B S hS P.X P.f ⁻¹' {P.y} ⊆ Set.range (pointsMap B S hS c.X'.1 c.g.hom) ∧
        IsUniversallyPureAbove c.situation) :
    IsUniversallyPureAbove P := by
  obtain ⟨c, hfibre, huniv⟩ := hcover
  exact c.isUniversallyPureAbove_of_isUniversallyPureAbove_situation
    (c.relativeWeaklyAssociatedPoints_subset_range_of_isAffineLocalAt hlocal hpure hfibre) huniv

/-! ### The carried reduction -/

/-- **The reduction of the proof of Stacks 0CW4 to a strictly henselian local base, carried as
a hypothesis.** For a module flat over `Y` along the fibre `f^{-1}(\{y\})` and pure above `y`,
there is a morphism of pointed algebraic spaces `(Y₁, y₁) ⟶ (Y, y)` — intended to be
`Spec(𝒪_{Y, ȳ}) ⟶ Y` with its closed point — such that

* the base change admits the impurity ascent data of Stacks 0CVA, which Stacks 0CVG consumes
  and whose first conjunct is flatness of `Y₁ ⟶ Y` at `y₁`;
* `Y₁` is affine local with closed point `y₁`;
* the base change `ℱ_{Y₁}` is still pure above `y₁`; and
* there is an étale `g : X₁' ⟶ X_{Y₁}` over `Y₁` whose image on points contains the fibre of
  `X_{Y₁}` over `y₁` and along which `ℱ_{Y₁}` pulls back to a module universally pure above
  `y₁`.

The last conjunct is the conclusion the source draws from Stacks 0CVW and More on Flatness,
Stacks 05K6; the third is the ascent of purity along `Spec(𝒪_{Y, ȳ}) ⟶ Y` which the source's
"we reduce to the case described in the next paragraph" uses silently. Neither is available in
this development; see the implementation notes of this file. -/
def PurityStrictlyHenselianReduction (P : PrePureSituation.{u, u} B S hS) : Prop :=
  (∀ x : points B S hS P.X, pointsMap B S hS P.X P.f x = P.y →
      x ∈ flatLocus B S hS P.hX P.f P.F) →
    IsPureAbove P →
      ∃ c : PointedOver P,
        HasFlatImpurityAscentData c ∧
        c.baseChange.IsAffineLocalAt ∧
        IsPureAbove c.baseChange ∧
        ∃ e : EtaleOverSource c.baseChange,
          pointsMap B S hS c.baseChange.X c.baseChange.f ⁻¹' {c.baseChange.y} ⊆
              Set.range (pointsMap B S hS e.X'.1 e.g.hom) ∧
            IsUniversallyPureAbove e.situation

/-! ### Stacks 0CW4 -/

/-- **Stacks 0CW4, granting the strictly henselian reduction.** In the situation of Stacks 0CV6,
if `ℱ` is flat over `Y` at every point of `X` lying over `y` and pure above `y`, then `ℱ` is
universally pure above `y`.

This form carries the reduction as the hypothesis `hred`; Stacks 0CW4 itself, with exactly the
source's hypotheses, is `AlgebraicGeometry.Space.isUniversallyPureAbove_of_flat_of_isPureAbove`,
which carries the tag.

The reduction to a strictly henselian local base and the étale cover the source obtains there
are carried by `AlgebraicGeometry.Space.PurityStrictlyHenselianReduction`; the deduction of the
conclusion from them — Stacks 0CW3 over the reduced base, then the descent of Stacks 0CVG part
(2) — is proved here. -/
theorem isUniversallyPureAbove_of_isPureAbove (P : PrePureSituation.{u, u} B S hS)
    (hred : PurityStrictlyHenselianReduction P)
    (hflat : ∀ x : points B S hS P.X, pointsMap B S hS P.X P.f x = P.y →
      x ∈ flatLocus B S hS P.hX P.f P.F)
    (hpure : IsPureAbove P) :
    IsUniversallyPureAbove P := by
  obtain ⟨c, hascent, hlocal, hpure₁, e, hfibre, huniv⟩ := hred hflat hpure
  exact isUniversallyPureAbove_of_isFlatAt P c hascent.1
    (isUniversallyPureAbove_of_exists_etaleOverSource c.baseChange hlocal hpure₁
      ⟨e, hfibre, huniv⟩)

/-! ### Stacks 0CW5 -/

/-- **Stacks 0CW5**, the substantive implication, granting the reduction of Stacks 0CW4 at each
point; the unconditional statement is
`AlgebraicGeometry.Space.isUniversallyPureRelative_of_flat_of_isPureRelative`. In the situation of
Stacks 0CV6, if `ℱ` is flat over `Y` and pure relative to `Y`, then `ℱ` is universally pure
relative to `Y`.

Both notions of Stacks 0CVD quantify over the points of `Y`, so this is Stacks 0CW4 at each
point: flatness over `Y` is flatness at every point of `X`, hence in particular along every
fibre. No hypothesis beyond the one Stacks 0CW4 carries is needed. -/
theorem isUniversallyPureRelative_of_isPureRelative (P : PrePureSituation.{u, u} B S hS)
    (hred : ∀ y : points B S hS P.Y, PurityStrictlyHenselianReduction { P with y := y })
    (hflat : ∀ x : points B S hS P.X, x ∈ flatLocus B S hS P.hX P.f P.F)
    (hpure : IsPureRelative P) :
    IsUniversallyPureRelative P :=
  fun y => isUniversallyPureAbove_of_isPureAbove _ (hred y) (fun x _ => hflat x) (hpure y)

/-- **Stacks 0CW5, granting the reduction of Stacks 0CW4 at each point.** In the situation of
Stacks 0CV6, if `ℱ` is flat over `Y` then `ℱ` is pure relative to `Y` if and only if it is
universally pure relative to `Y`. The unconditional statement, which carries the tag, is
`AlgebraicGeometry.Space.isPureRelative_iff_isUniversallyPureRelative_of_flat`.

The forward implication is `isUniversallyPureRelative_of_isPureRelative`, which is Stacks 0CW4
at each point of `Y`; the reverse one is formal and holds with no flatness, by
`AlgebraicGeometry.Space.IsPureRelative.of_isUniversallyPureRelative`. -/
theorem isPureRelative_iff_isUniversallyPureRelative (P : PrePureSituation.{u, u} B S hS)
    (hred : ∀ y : points B S hS P.Y, PurityStrictlyHenselianReduction { P with y := y })
    (hflat : ∀ x : points B S hS P.X, x ∈ flatLocus B S hS P.hX P.f P.F) :
    IsPureRelative P ↔ IsUniversallyPureRelative P :=
  ⟨isUniversallyPureRelative_of_isPureRelative P hred hflat,
    IsPureRelative.of_isUniversallyPureRelative⟩

end AlgebraicGeometry.Space

end
