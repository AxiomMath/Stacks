module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.OpenSubschemeRankStrict
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.UniversallyBoundedFibresOpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Diagonal

/-!
# The fibre degree drops strictly on an open subobject which omits a point of the fibre

Let `Ψ : h_W ⟶ X` be a relatively representable morphism from the presheaf represented by an
object of the big fppf site to a presheaf, and let `σ : V ⟶ W` be a morphism of the site whose
underlying morphism of schemes is an open immersion. Fix **one** field-valued point `ξ` of `X`.
If the fibre of `Ψ` over `ξ` is finite locally free of degree at most `d`, and the base change
of `σ` to that fibre **omits a point of it**, then the fibre of `h_V ⟶ X` over `ξ` is finite
locally free of degree *strictly* below `d`.

This is the fibre-degree drop of the inductive step of [Stacks, Tag 09YB]. There `Ψ` is an étale
chart `p : U ⟶ X` pulled back to the relative compactification `Y`, `σ` is the inclusion of the
complementary piece `W` of the splitting `U ×_X Y = U ⨿ W`, and the omitted point is the one
supplied by the graph of `j : U ⟶ Y`, which is a section of the projection over the points of
`j(U)`. The source phrases the step as the `U` summand "accounting for one of the `d`"; what the
argument consumes from the splitting is only the omitted point, so no additivity of the degree
across the splitting is needed, and neither is a coproduct presentation of it.

**The statement is pointwise, and that is the whole point.** An earlier form of it quantified
the omitted-point hypothesis over *every* field-valued point of `X`. That form is unusable in
[Stacks, Tag 09YB]: there the graph of `j` supplies an omitted point only over the points of
`j(U)`, and over the points `Y` adds beyond `j(U)` the fibre genuinely need not drop. Carrying
the bound from `j(U)` to all of `Y` is a different step, performed by closedness of the degree
stratum of [Stacks, Tag 07S8] in
`AlgebraicGeometry.Space.exists_isFiniteLocallyFreeOfRank_lt_of_denseRange`, whose hypothesis is
exactly the pointwise drop restricted to the points of a dense subset. So the drop is stated at
one point, and the universally quantified consequence is recorded separately for callers that
do have the hypothesis everywhere.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.exists_isFiniteLocallyFreeOfRank_lt_of_isOpenImmersion_of_omits`:
  **the fibre-degree drop, at one field-valued point.** The fibre of `h_V ⟶ X` over `ξ` is
  finite locally free of some degree strictly below the bound for the fibre of `Ψ` over `ξ`,
  on a presentation this produces.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_lt_of_isOpenImmersion_of_omits`: the same
  drop read on a presentation of the fibre *supplied by the caller*, which is the shape
  `AlgebraicGeometry.Space.exists_isFiniteLocallyFreeOfRank_lt_of_denseRange` consumes.
* `AlgebraicGeometry.Space.exists_isFiniteLocallyFreeOfRank_le_of_isOpenImmersion_of_fibre`:
  the same bound **non-strictly**, which needs no omitted point.
* `AlgebraicGeometry.Space.hasUniversallyBoundedFibers_of_isOpenImmersion`: that non-strict
  bound at every field-valued point, as
  `AlgebraicGeometry.Space.HasUniversallyBoundedFibers`. This is the universal bound the carry
  asks for, and it cannot come from the drop, which the carry is what produces.
* `AlgebraicGeometry.Space.hasUniversallyBoundedFibers_of_isOpenImmersion_of_omits`: the drop
  in the form of `AlgebraicGeometry.Space.HasUniversallyBoundedFibers`, for a caller that has
  both hypotheses at every field-valued point.

## Implementation notes

The scheme-level content is `AlgebraicGeometry.finite_open_rank_lt_of_field`: an open immersion
into a finite scheme over a field which omits a point has strictly smaller degree. Everything
here is the passage from that to the site, and it follows the pattern of
`AlgebraicGeometry.Space.hasUniversallyBoundedFibers_of_finite_openCover`, which performs the
same passage for a finite open cover.

The omitted point is asked for on the *canonical* fibre
`CategoryTheory.Functor.relativelyRepresentable.pullback`, and the base change of `σ` to it is
the pullback of `σ` along `CategoryTheory.Functor.relativelyRepresentable.fst'`. Stating the
hypothesis there rather than on an arbitrary presentation of the fibre keeps it canonical; the
degree bound is supplied on *some* presentation, and is transported to the canonical one by
`AlgebraicGeometry.Space.property_of_isPullback_of_isPullback`, which is the uniqueness of a
pullback up to isomorphism in exactly this shape. The same lemma moves the conclusion from the
presentation produced here to one supplied by the caller.

## What is and is not proved

Nothing here carries a Stacks attribute, and no part of [Stacks, Tag 09YB] is registered. The
induction on the degree which this feeds is not performed, and the hypothesis that the base
change of `σ` omits a point of the fibre is *assumed*, not derived from a clopen splitting: the
derivation of that hypothesis from the graph splitting
(`AlgebraicGeometry.Space.exists_graphComplement_decomposition`) is
`AlgebraicGeometry.Space.exists_notMem_range_toScheme_map_pullback_snd_of_notMem_range`, in
`StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverGraphOmittedFibrePoint`, and not here.

## References

* [Stacks Project, Tag 03JL](https://stacks.math.columbia.edu/tag/03JL)
* [Stacks Project, Tag 07S8](https://stacks.math.columbia.edu/tag/07S8)
* [Stacks Project, Tag 09YB](https://stacks.math.columbia.edu/tag/09YB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Morphisms

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The base change of `σ` to the canonical fibre of `Ψ` over `ξ` is an open immersion of
schemes, being a base change of one. It is stated separately so that it is in scope as a local
instance wherever the drop needs it. -/
theorem isOpenImmersion_toScheme_map_pullback_snd_fst'
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {W V : BigFppfOver B S hS}
    {Ψ : yoneda.obj W ⟶ X} (hΨ : yoneda.relativelyRepresentable Ψ) (σ : V ⟶ W)
    (hopen : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map σ))
    {T : BigFppfOver B S hS} (ξ : yoneda.obj T ⟶ X) :
    _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (pullback.snd σ (hΨ.fst' ξ))) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @_root_.AlgebraicGeometry.IsOpenImmersion)
    ((IsPullback.of_hasPullback σ (hΨ.fst' ξ)).map (BigFppfOver.toScheme B S hS)) hopen

/-- **The fibre of an open subobject, at one field-valued point: the shared core.** Let
`Ψ : h_W ⟶ X` be relatively representable, let `σ : V ⟶ W` be an open immersion on underlying
schemes, and fix a field-valued point `ξ` of `X` together with any presentation `q : Q ⟶ T` of
the fibre of `Ψ` over `ξ`, of degree `r₀`. Then the *canonical* presentation of the fibre of
`h_V ⟶ X` over `ξ` — the base change of `σ` to the canonical fibre of `Ψ`, followed down to `T`
— is finite locally free of some degree `r ≤ r₀`, and the comparison may also be read over
`Spec k`.

This is everything the drop needs that does not mention the omitted point: both the non-strict
bound `AlgebraicGeometry.Space.exists_isFiniteLocallyFreeOfRank_le_of_isOpenImmersion_of_fibre`
and the strict one
`AlgebraicGeometry.Space.exists_isFiniteLocallyFreeOfRank_lt_of_isOpenImmersion_of_omits` are
read off it, the latter by feeding the last two conclusions and the omitted point to
`AlgebraicGeometry.finite_open_rank_lt_of_field`. The two degrees are returned over `Spec k` as
well as over `T` precisely so that the strict step needs nothing from this proof's interior. -/
theorem exists_le_isFiniteLocallyFreeOfRank_pullback_snd_of_isOpenImmersion
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {W V : BigFppfOver B S hS}
    (Ψ : yoneda.obj W ⟶ X) (hΨ : yoneda.relativelyRepresentable Ψ) (σ : V ⟶ W)
    (hopen : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map σ))
    {k : Type u} [Field k] {T : BigFppfOver B S hS}
    (hA : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of k))
    (ξ : yoneda.obj T ⟶ X)
    {Q : BigFppfOver B S hS} (q : Q ⟶ T) (c : yoneda.obj Q ⟶ yoneda.obj W) {r₀ : ℕ}
    (hrank₀ : IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map q) r₀)
    (hsq₀ : IsPullback c (yoneda.map q) Ψ ξ) :
    ∃ r : ℕ, r ≤ r₀ ∧
      IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map
        (pullback.snd σ (hΨ.fst' ξ) ≫ hΨ.snd ξ)) r ∧
      IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map (pullback.snd σ (hΨ.fst' ξ)) ≫
        (BigFppfOver.toScheme B S hS).map (hΨ.snd ξ) ≫ hA.hom) r ∧
      IsFiniteLocallyFreeOfRank
        ((BigFppfOver.toScheme B S hS).map (hΨ.snd ξ) ≫ hA.hom) r₀ := by
  have _hbopen := isOpenImmersion_toScheme_map_pullback_snd_fst' B S hS hΨ σ hopen ξ
  -- the degree of the canonical fibre of `Ψ`, transported from the presentation supplied
  have hrankQ : IsFiniteLocallyFreeOfRank
      ((BigFppfOver.toScheme B S hS).map (hΨ.snd ξ)) r₀ :=
    property_of_isPullback_of_isPullback B S hS
      (Q := IsFiniteLocallyFreeOfRank.property.{u} r₀) (hΨ.isPullback' ξ) hsq₀ hrank₀
  have hrankQ' : IsFiniteLocallyFreeOfRank
      ((BigFppfOver.toScheme B S hS).map (hΨ.snd ξ) ≫ hA.hom) r₀ :=
    ((IsFiniteLocallyFreeOfRank.property r₀).cancel_right_of_respectsIso
      ((BigFppfOver.toScheme B S hS).map (hΨ.snd ξ)) hA.hom).mpr hrankQ
  -- the open subscheme's own degree
  obtain ⟨r, hrle, hrank⟩ := exists_isFiniteLocallyFreeOfRank_le_of_isOpenImmersion
    ((BigFppfOver.toScheme B S hS).map (hΨ.snd ξ) ≫ hA.hom)
    ((BigFppfOver.toScheme B S hS).map (pullback.snd σ (hΨ.fst' ξ))) r₀ (h := hrankQ')
  refine ⟨r, hrle, ?_, hrank, hrankQ'⟩
  rw [Functor.map_comp]
  refine ((IsFiniteLocallyFreeOfRank.property r).cancel_right_of_respectsIso
    ((BigFppfOver.toScheme B S hS).map (pullback.snd σ (hΨ.fst' ξ)) ≫
      (BigFppfOver.toScheme B S hS).map (hΨ.snd ξ)) hA.hom).mp ?_
  rwa [Category.assoc]

/-- The canonical presentation of the fibre of `h_V ⟶ X` over `ξ` really is a presentation of
it: the base change of `σ` to the canonical fibre of `Ψ`, followed down to `T`, is cartesian over
`yoneda.map σ ≫ Ψ` and `ξ`. This is the vertical pasting of the base-change square of `σ` onto
the canonical fibre square of `Ψ`. -/
theorem isPullback_pullback_snd_comp_snd
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {W V : BigFppfOver B S hS}
    (Ψ : yoneda.obj W ⟶ X) (hΨ : yoneda.relativelyRepresentable Ψ) (σ : V ⟶ W)
    {T : BigFppfOver B S hS} (ξ : yoneda.obj T ⟶ X) :
    IsPullback (yoneda.map (pullback.fst σ (hΨ.fst' ξ)))
      (yoneda.map (pullback.snd σ (hΨ.fst' ξ) ≫ hΨ.snd ξ)) (yoneda.map σ ≫ Ψ) ξ := by
  rw [Functor.map_comp]
  exact IsPullback.paste_vert
    ((IsPullback.of_hasPullback σ (hΨ.fst' ξ)).map yoneda) (hΨ.isPullback' ξ)

/-- **The non-strict fibre bound on an open subobject, at one field-valued point.** If the fibre
of `Ψ` over `ξ` is finite locally free of degree at most `d`, so is the fibre of `h_V ⟶ X`.

No omitted point is needed: this is the bound before the drop, and it is what supplies the
universal bound which the carry of
`AlgebraicGeometry.Space.exists_isFiniteLocallyFreeOfRank_lt_of_denseRange` asks for. -/
theorem exists_isFiniteLocallyFreeOfRank_le_of_isOpenImmersion_of_fibre
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {W V : BigFppfOver B S hS}
    (Ψ : yoneda.obj W ⟶ X) (hΨ : yoneda.relativelyRepresentable Ψ) (σ : V ⟶ W)
    (hopen : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map σ))
    (d : ℕ) {k : Type u} [Field k] {T : BigFppfOver B S hS}
    (hA : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of k))
    (ξ : yoneda.obj T ⟶ X)
    (hbnd : ∃ (Q : BigFppfOver B S hS) (q : Q ⟶ T) (c : yoneda.obj Q ⟶ yoneda.obj W) (r : ℕ),
      r ≤ d ∧
        IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map q) r ∧
        IsPullback c (yoneda.map q) Ψ ξ) :
    ∃ (P : BigFppfOver B S hS) (p : P ⟶ T) (i : yoneda.obj P ⟶ yoneda.obj V) (r : ℕ),
      r ≤ d ∧
        IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map p) r ∧
        IsPullback i (yoneda.map p) (yoneda.map σ ≫ Ψ) ξ := by
  obtain ⟨Q, q, c, r₀, hr₀d, hrank₀, hsq₀⟩ := hbnd
  obtain ⟨r, hrle, hrank, -, -⟩ :=
    exists_le_isFiniteLocallyFreeOfRank_pullback_snd_of_isOpenImmersion B S hS Ψ hΨ σ hopen
      hA ξ q c hrank₀ hsq₀
  exact ⟨pullback σ (hΨ.fst' ξ), pullback.snd σ (hΨ.fst' ξ) ≫ hΨ.snd ξ,
    yoneda.map (pullback.fst σ (hΨ.fst' ξ)), r, hrle.trans hr₀d, hrank,
    isPullback_pullback_snd_comp_snd B S hS Ψ hΨ σ ξ⟩

/-- **The fibre-degree drop, at one field-valued point.** Let `Ψ : h_W ⟶ X` be relatively
representable, let `σ : V ⟶ W` be an open immersion on underlying schemes, and fix a
field-valued point `ξ` of `X`. If the fibre of `Ψ` over `ξ` is finite locally free of degree at
most `d`, and the base change of `σ` to the canonical fibre of `Ψ` over `ξ` omits a point of it,
then the fibre of `h_V ⟶ X` over `ξ` is finite locally free of some degree strictly below `d`.

The scheme-level step is `AlgebraicGeometry.finite_open_rank_lt_of_field`, applied to the fibre
of `Ψ` over the point and to the open subscheme of it cut out by `σ`.

Both hypotheses are at the single point `ξ`, because that is the only form in which
[Stacks, Tag 09YB] can supply the omitted one; see the module documentation. -/
theorem exists_isFiniteLocallyFreeOfRank_lt_of_isOpenImmersion_of_omits
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {W V : BigFppfOver B S hS}
    (Ψ : yoneda.obj W ⟶ X) (hΨ : yoneda.relativelyRepresentable Ψ) (σ : V ⟶ W)
    (hopen : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map σ))
    (d : ℕ) {k : Type u} [Field k] {T : BigFppfOver B S hS}
    (hA : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of k))
    (ξ : yoneda.obj T ⟶ X)
    (hbnd : ∃ (Q : BigFppfOver B S hS) (q : Q ⟶ T) (c : yoneda.obj Q ⟶ yoneda.obj W) (r : ℕ),
      r ≤ d ∧
        IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map q) r ∧
        IsPullback c (yoneda.map q) Ψ ξ)
    (homit : ∃ x : (BigFppfOver.toScheme B S hS).obj (hΨ.pullback ξ),
      x ∉ Set.range ((BigFppfOver.toScheme B S hS).map
        (pullback.snd σ (hΨ.fst' ξ))).base) :
    ∃ (P : BigFppfOver B S hS) (p : P ⟶ T) (i : yoneda.obj P ⟶ yoneda.obj V) (r : ℕ),
      r < d ∧
        IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map p) r ∧
        IsPullback i (yoneda.map p) (yoneda.map σ ≫ Ψ) ξ := by
  set Fs := BigFppfOver.toScheme B S hS
  have _hbopen := isOpenImmersion_toScheme_map_pullback_snd_fst' B S hS hΨ σ hopen ξ
  obtain ⟨Q, q, c, r₀, hr₀d, hrank₀, hsq₀⟩ := hbnd
  obtain ⟨r, hrle, hrank, hrankSpec, hrankQ'⟩ :=
    exists_le_isFiniteLocallyFreeOfRank_pullback_snd_of_isOpenImmersion B S hS Ψ hΨ σ hopen
      hA ξ q c hrank₀ hsq₀
  obtain ⟨x, hx⟩ := homit
  have := @isFinite_of_isFiniteLocallyFreeOfRank _ _ (Fs.map (hΨ.snd ξ) ≫ hA.hom) r₀ hrankQ'
  have := @isFinite_of_isFiniteLocallyFreeOfRank _ _
    (Fs.map (pullback.snd σ (hΨ.fst' ξ)) ≫ Fs.map (hΨ.snd ξ) ≫ hA.hom) r hrankSpec
  exact ⟨pullback σ (hΨ.fst' ξ), pullback.snd σ (hΨ.fst' ξ) ≫ hΨ.snd ξ,
    yoneda.map (pullback.fst σ (hΨ.fst' ξ)), r,
    (finite_open_rank_lt_of_field (Fs.map (pullback.snd σ (hΨ.fst' ξ)))
      (Fs.map (hΨ.snd ξ) ≫ hA.hom) r₀ r hrankQ' hrankSpec x hx).trans_le hr₀d, hrank,
    isPullback_pullback_snd_comp_snd B S hS Ψ hΨ σ ξ⟩

/-- **The fibre-degree drop, read on a presentation supplied by the caller.** Same hypotheses as
`AlgebraicGeometry.Space.exists_isFiniteLocallyFreeOfRank_lt_of_isOpenImmersion_of_omits`, but
with the fibre of `h_V ⟶ X` over `ξ` presented by a morphism `q : Vf ⟶ T` of the caller's
choosing rather than by one this produces. The two presentations are pullbacks of one cospan, so
`AlgebraicGeometry.Space.property_of_isPullback_of_isPullback` carries the degree between them.

This is the shape in which
`AlgebraicGeometry.Space.exists_isFiniteLocallyFreeOfRank_lt_of_denseRange` — the carry of the
bound from a dense set of points to all of them — takes its pointwise hypothesis, and so the
shape in which the inductive step of [Stacks, Tag 09YB] consumes the drop. -/
theorem isFiniteLocallyFreeOfRank_lt_of_isOpenImmersion_of_omits
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {W V : BigFppfOver B S hS}
    (Ψ : yoneda.obj W ⟶ X) (hΨ : yoneda.relativelyRepresentable Ψ) (σ : V ⟶ W)
    (hopen : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map σ))
    (d : ℕ) {k : Type u} [Field k] {T : BigFppfOver B S hS}
    (hA : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of k))
    (ξ : yoneda.obj T ⟶ X)
    (hbnd : ∃ (Q : BigFppfOver B S hS) (q : Q ⟶ T) (c : yoneda.obj Q ⟶ yoneda.obj W) (r : ℕ),
      r ≤ d ∧
        IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map q) r ∧
        IsPullback c (yoneda.map q) Ψ ξ)
    (homit : ∃ x : (BigFppfOver.toScheme B S hS).obj (hΨ.pullback ξ),
      x ∉ Set.range ((BigFppfOver.toScheme B S hS).map
        (pullback.snd σ (hΨ.fst' ξ))).base)
    {Vf : BigFppfOver B S hS} (q : Vf ⟶ T) (i : yoneda.obj Vf ⟶ yoneda.obj V)
    (hsq : IsPullback i (yoneda.map q) (yoneda.map σ ≫ Ψ) ξ) :
    ∃ r : ℕ, r < d ∧
      IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map q) r := by
  obtain ⟨P, p, i', r, hlt, hrank, hsq'⟩ :=
    exists_isFiniteLocallyFreeOfRank_lt_of_isOpenImmersion_of_omits B S hS Ψ hΨ σ hopen d hA ξ
      hbnd homit
  exact ⟨r, hlt, property_of_isPullback_of_isPullback B S hS
    (Q := IsFiniteLocallyFreeOfRank.property.{u} r) hsq hsq' hrank⟩

/-- **The universal bound on the fibres of an open subobject.** If the fibre of `Ψ` over every
field-valued point is finite locally free of degree at most `d`, then `h_V ⟶ X` has universally
bounded fibres, with the bound `d`.

No omitted point is needed. This is the hypothesis `hbound` of
`AlgebraicGeometry.Space.exists_isFiniteLocallyFreeOfRank_lt_of_denseRange`, and it is the one
input of the carry that the inductive step of [Stacks, Tag 09YB] cannot take from the drop: the
carry is what *produces* the strict bound everywhere, so its universal bound has to come from
before the drop. -/
theorem hasUniversallyBoundedFibers_of_isOpenImmersion
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {W V : BigFppfOver B S hS}
    (Ψ : yoneda.obj W ⟶ X) (hΨ : yoneda.relativelyRepresentable Ψ) (σ : V ⟶ W)
    (hopen : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map σ))
    (d : ℕ)
    (hbnd : ∀ (k : Type u) (_ : Field k) (T : BigFppfOver B S hS)
      (_ : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of k))
      (ξ : yoneda.obj T ⟶ X),
      ∃ (Q : BigFppfOver B S hS) (q : Q ⟶ T) (c : yoneda.obj Q ⟶ yoneda.obj W) (r : ℕ),
        r ≤ d ∧
          IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map q) r ∧
          IsPullback c (yoneda.map q) Ψ ξ) :
    HasUniversallyBoundedFibers B S hS V (yoneda.map σ ≫ Ψ) := by
  refine ⟨(d : ℤ), fun k hk T hA ξ ↦ ?_⟩
  let := hk
  obtain ⟨P, p, i, r, hle, hrank, hsq⟩ :=
    exists_isFiniteLocallyFreeOfRank_le_of_isOpenImmersion_of_fibre B S hS Ψ hΨ σ hopen d hA ξ
      (hbnd k hk T hA ξ)
  exact ⟨P, p, i, r, by exact_mod_cast hle, hrank, hsq⟩

/-- **The fibre-degree drop, as a universal bound.** For a caller which has the hypotheses of
`AlgebraicGeometry.Space.exists_isFiniteLocallyFreeOfRank_lt_of_isOpenImmersion_of_omits` at
*every* field-valued point, `h_V ⟶ X` has universally bounded fibres, with the bound `d - 1`
rather than `d`; the strict inequality itself is the content of that result and is not re-stated
here.

The inductive step of [Stacks, Tag 09YB] does **not** go through this declaration: there the
omitted point is available only over the points of `j(U)`, and the pointwise drop is fed to
`AlgebraicGeometry.Space.exists_isFiniteLocallyFreeOfRank_lt_of_denseRange` instead. -/
theorem hasUniversallyBoundedFibers_of_isOpenImmersion_of_omits
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {W V : BigFppfOver B S hS}
    (Ψ : yoneda.obj W ⟶ X) (hΨ : yoneda.relativelyRepresentable Ψ) (σ : V ⟶ W)
    (hopen : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map σ))
    (d : ℕ)
    (hbnd : ∀ (k : Type u) (_ : Field k) (T : BigFppfOver B S hS)
      (_ : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of k))
      (ξ : yoneda.obj T ⟶ X),
      ∃ (Q : BigFppfOver B S hS) (q : Q ⟶ T) (c : yoneda.obj Q ⟶ yoneda.obj W) (r : ℕ),
        r ≤ d ∧
          IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map q) r ∧
          IsPullback c (yoneda.map q) Ψ ξ)
    (homit : ∀ (k : Type u) (_ : Field k) (T : BigFppfOver B S hS)
      (_ : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of k))
      (ξ : yoneda.obj T ⟶ X),
      ∃ x : (BigFppfOver.toScheme B S hS).obj (hΨ.pullback ξ),
        x ∉ Set.range ((BigFppfOver.toScheme B S hS).map
          (pullback.snd σ (hΨ.fst' ξ))).base) :
    HasUniversallyBoundedFibers B S hS V (yoneda.map σ ≫ Ψ) := by
  refine ⟨(d : ℤ) - 1, fun k hk T hA ξ ↦ ?_⟩
  let := hk
  obtain ⟨P, p, i, r, hlt, hrank, hsq⟩ :=
    exists_isFiniteLocallyFreeOfRank_lt_of_isOpenImmersion_of_omits B S hS Ψ hΨ σ hopen d hA ξ
      (hbnd k hk T hA ξ) (homit k hk T hA ξ)
  exact ⟨P, p, i, r, by omega, hrank, hsq⟩

end AlgebraicGeometry.Space

end
