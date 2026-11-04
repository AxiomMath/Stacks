module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.BaseChange
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Finrank
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Open
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.SplitFiniteFibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.OpenSubschemeRankBound
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBoundedBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Lower semicontinuity of the degree of the fibres of a quasi-finite flat morphism

Let `g : Z ⟶ Y` be a flat, locally finitely presented, separated and locally quasi-finite
morphism of schemes with quasi-compact fibres. Every fibre of `g` is then a finite scheme over
the residue field below it, so it has a degree, and this file proves that the degree can only
*go up* under specialisation of the base point: the locus of points of `Y` where the degree is
at least a given `d` is open.

That statement is the content of Tag 086R, the stratification which the proof of Tag 086T —
and through it the proof of Tag 086U, Rydh's theorem — applies to a chart. Tag 086R itself is
the same assertion for a morphism with merely *locally* quasi-compact fibres, obtained from
this one by exhausting the source by quasi-compact opens; see the implementation notes for
exactly what is and is not proved here.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.isFinite_fiberToSpecResidueField_of_finite_fibre`: a fibre of a locally
  quasi-finite morphism with finitely many points is a finite scheme over the residue field
  below it, with no quasi-compactness of the morphism assumed.
* `AlgebraicGeometry.finite_preimage_singleton_of_locallyQuasiFinite`: a fibre of a
  quasi-compact locally quasi-finite morphism has finitely many points.
* `AlgebraicGeometry.isFinite_fiberToSpecResidueField`: hence such a fibre is a finite scheme
  over the residue field below it.
* `AlgebraicGeometry.exists_isFiniteLocallyFreeOfRank_fiberToSpecResidueField`: such a fibre is
  finite locally free of some rank, i.e. it has a degree. This is what makes the hypothesis of
  the next result satisfiable at *every* point of the target.
* `AlgebraicGeometry.exists_opens_mem_forall_le_rank_fiberToSpecResidueField`: the degree of
  the fibre is at least the degree at `y` on an open neighbourhood of `y` — the semicontinuity
  statement itself.
* `AlgebraicGeometry.isOpen_setOf_exists_le_rank_fiberToSpecResidueField`: equivalently, the
  locus where the degree of the fibre is at least `d` is open.
* `AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback_fst_iff`: the degree of the base change
  of `g` to the spectrum of an arbitrary field equals the degree of the fibre over the image of
  that spectrum, so the open locus above describes the degrees of all field-valued base
  changes.
* `AlgebraicGeometry.exists_antitone_opens_iff_fibreDegree_ge_of_quasiCompact`: Tag 086R for a
  morphism with quasi-compact source fibres, in the membership form.

## Implementation notes

**No Stacks attribute is placed here.** The final result is Tag 086R with the extra hypothesis
`QuasiCompact g`, so it is not the tag; and it is stated by membership of the image point in
the open rather than by a factorisation through it. Both gaps are named precisely at the end of
these notes.

*The argument.* Only the first paragraph of the induction of Tag 07RY is used, and it is used
once rather than inductively, which is why no stratification by *reduced closed* subschemes and
no induction on a universal bound appear. Given `y` with fibre of degree `e`, the fibre has
finitely many points, so Tag 02LP applies: there is an elementary étale neighbourhood
`(U, u)` of `y` and a decomposition `U ×_Y Z = V ⊔ W` into complementary opens with
`V ⟶ U` finite and `W` having no point over `u`. The morphism `V ⟶ U` is finite, flat and
locally of finite presentation, so `AlgebraicGeometry.Scheme.Hom.finrank` of it is locally
constant; the open of `U` where that rank is the rank at `u` maps to an open of `Y`, because an
étale morphism is open (Tag 03WT). Over a point `u'` of that open the fibre of `V` is an open
subscheme of the fibre of `U ×_Y Z`, which is a base change of the fibre of `g`, so the degree
of the latter is at least the rank at `u'`
(`AlgebraicGeometry.exists_isFiniteLocallyFreeOfRank_le_of_isOpenImmersion`); and over `u`
itself that open subscheme is the whole fibre, because `W` has no point there, so the rank at
`u` is exactly `e`.

*No descent is used.* The source descends the opens along the étale covering. Here the only
comparison between upstairs and downstairs is between the degree of a fibre and the degree of
its base change to a larger residue field, and that direction is base change, not descent: the
fibre downstairs already *has* a degree by
`AlgebraicGeometry.exists_isFiniteLocallyFreeOfRank_fiberToSpecResidueField`, and the degree of
a fibre over a field is unique, so the two agree. In particular neither Tag 02LA nor Tag 02VO
is needed.

*What is still owed for Tag 086R.* Two things, and nothing else.

1. **The quasi-compact exhaustion.** Tag 086R assumes only that `g` is locally quasi-finite,
   and reduces to the quasi-compact case by writing the degree-at-least-`d` locus as the union,
   over quasi-compact opens `W` of `Z`, of the degree-at-least-`d` locus of `W.ι ≫ g`. What that
   needs is the reverse inclusion: a point `y` whose fibre is either not finite or finite of
   degree at least `d` admits a quasi-compact open `W` of `Z` whose fibre over `y` has degree at
   least `d`. The two facts about fibres which that argument rests on are both available: a
   fibre with finitely many points is finite, by
   `AlgebraicGeometry.isFinite_fiberToSpecResidueField_of_finite_fibre`, so a non-finite fibre
   has infinitely many points and `d` of them can be chosen; and the degree of a fibre bounds
   its number of points, by `AlgebraicGeometry.cardinalMk_pullback_le_of_degree_le`. What is
   owed is the choice of the finitely many affine opens of `Z` around those points, and the
   reduction of openness of the locus to an affine base — which is what supplies
   `QuasiCompact (W.ι ≫ g)`, since the affine-target property of
   `AlgebraicGeometry.QuasiCompact` is `CompactSpace` of the source.
2. **The factorisation form.** Tag 086R, and the hypothesis `h086R` of
   `AlgebraicGeometry.Space.exists_antitone_openSubspaces_iff_fibreDegree_ge`, phrase the
   condition as the existence of a factorisation of `Spec k ⟶ Y` through the open. That is
   equivalent to the membership used here by
   `AlgebraicGeometry.Space.field_map_factors_through_open_iff`, which is already proved; it is
   not invoked here only because it lives in a module about algebraic spaces and importing that
   module here would invert the layering.

## References

* [Stacks Project, Tag 02LP](https://stacks.math.columbia.edu/tag/02LP)
* [Stacks Project, Tag 03WT](https://stacks.math.columbia.edu/tag/03WT)
* [Stacks Project, Tag 086R](https://stacks.math.columbia.edu/tag/086R)
* [Stacks Project, Tag 086T](https://stacks.math.columbia.edu/tag/086T)
* [Stacks Project, Tag 086U](https://stacks.math.columbia.edu/tag/086U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- **A locally quasi-finite morphism with finitely many points over a given point of the target
is finite over the residue field there.**

No quasi-compactness of the morphism is assumed: the fibre is quasi-compact because it is
*finite*, and a subset of a finite space is compact, so the criterion
`AlgebraicGeometry.quasiCompact_iff_forall_isAffineOpen` applies and
`AlgebraicGeometry.IsFinite.of_locallyQuasiFinite` finishes. This is the converse direction
needed to turn "the fibre of `g` over `y` is not a finite scheme" into "the fibre of `g` over
`y` has infinitely many points". -/
theorem isFinite_fiberToSpecResidueField_of_finite_fibre [LocallyQuasiFinite g] (y : Y)
    (hy : (g.base ⁻¹' {y}).Finite) : IsFinite (g.fiberToSpecResidueField y) := by
  have h1 : LocallyQuasiFinite (g.fiberToSpecResidueField y) :=
    inferInstanceAs (LocallyQuasiFinite (pullback.snd g (Y.fromSpecResidueField y)))
  have hfinpts : Finite (g.fiber y) := by
    have : Finite ↑(g.base ⁻¹' {y}) := hy
    exact Finite.of_equiv _ (g.fiberHomeo y).symm.toEquiv
  have h2 : CompactSpace (g.fiber y) := Finite.compactSpace
  have h3 : QuasiCompact (g.fiberToSpecResidueField y) :=
    quasiCompact_iff_forall_isAffineOpen.mpr fun _ _ => (Set.toFinite _).isCompact
  exact IsFinite.of_locallyQuasiFinite _

/-- The set of points of the source of a quasi-compact locally quasi-finite morphism lying over
a given point of the target is finite. -/
theorem finite_preimage_singleton_of_locallyQuasiFinite
    [LocallyQuasiFinite g] [QuasiCompact g] (y : Y) : (g.base ⁻¹' {y}).Finite := by
  have h1 : LocallyQuasiFinite (g.fiberToSpecResidueField y) :=
    inferInstanceAs (LocallyQuasiFinite (pullback.snd g (Y.fromSpecResidueField y)))
  have : IsLocallyArtinian (g.fiber y) :=
    IsLocallyArtinian.of_locallyQuasiFinite (g.fiberToSpecResidueField y)
  have : DiscreteTopology (g.fiber y) := inferInstance
  have : Finite (g.fiber y) := finite_of_compact_of_discrete
  have : Finite ↑(g.base ⁻¹' {y}) := Finite.of_equiv _ (g.fiberHomeo y).toEquiv
  exact Set.toFinite _

/-- The fibre of a quasi-compact locally quasi-finite morphism over a point is a finite scheme
over the residue field at that point. -/
@[ega "II 6.1.7" "more general"]
theorem isFinite_fiberToSpecResidueField [LocallyQuasiFinite g] [QuasiCompact g] (y : Y) :
    IsFinite (g.fiberToSpecResidueField y) :=
  isFinite_fiberToSpecResidueField_of_finite_fibre g y
    (finite_preimage_singleton_of_locallyQuasiFinite g y)

/-- Every fibre of a quasi-compact locally quasi-finite morphism is finite locally free of some
rank over the residue field at the point below it: every fibre has a degree. -/
theorem exists_isFiniteLocallyFreeOfRank_fiberToSpecResidueField
    [LocallyQuasiFinite g] [QuasiCompact g] (y : Y) :
    ∃ r : ℕ, Stacks.Morphisms.IsFiniteLocallyFreeOfRank (g.fiberToSpecResidueField y) r := by
  have hfin : IsFinite (g.fiberToSpecResidueField y) :=
    isFinite_fiberToSpecResidueField g y
  exact exists_isFiniteLocallyFreeOfRank_of_isFinite
    (k := (Y.residueField y : Type u)) (g.fiberToSpecResidueField y)

/-- The part of the fibre of `pullback.snd g g'` over `u` which lies in an open `V` of the fibre
product is finite locally free over the residue field at `u`, of rank the rank of the finite
flat morphism `V.ι ≫ pullback.snd g g'` at `u`.

Both squares of the pasted pullback are formed in `Scheme`; the composite exhibits the restricted
fibre as a base change of `V.ι ≫ pullback.snd g g'`, so
`AlgebraicGeometry.Scheme.Hom.finrank_of_isPullback` computes its rank function as the constant
value of the rank of that morphism at `u`. -/
private theorem isFiniteLocallyFreeOfRank_restricted_fibre
    {U : Scheme.{u}} (g' : U ⟶ Y) (V : (pullback g g').Opens)
    [Flat g] [LocallyOfFinitePresentation g] [IsFinite (V.ι ≫ pullback.snd g g')] (u : U) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (pullback.snd V.ι (pullback.fst (pullback.snd g g') (U.fromSpecResidueField u)) ≫
        pullback.snd (pullback.snd g g') (U.fromSpecResidueField u))
      ((V.ι ≫ pullback.snd g g').finrank u) := by
  have sq : IsPullback
      (pullback.fst V.ι (pullback.fst (pullback.snd g g') (U.fromSpecResidueField u)))
      (pullback.snd V.ι (pullback.fst (pullback.snd g g') (U.fromSpecResidueField u)) ≫
        pullback.snd (pullback.snd g g') (U.fromSpecResidueField u))
      (V.ι ≫ pullback.snd g g') (U.fromSpecResidueField u) :=
    (IsPullback.of_hasPullback V.ι
        (pullback.fst (pullback.snd g g') (U.fromSpecResidueField u))).paste_vert
      (IsPullback.of_hasPullback (pullback.snd g g') (U.fromSpecResidueField u))
  have hfin : IsFinite
      (pullback.snd V.ι (pullback.fst (pullback.snd g g') (U.fromSpecResidueField u)) ≫
        pullback.snd (pullback.snd g g') (U.fromSpecResidueField u)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@IsFinite.{u} : MorphismProperty Scheme.{u})) sq ‹_›
  have hflat : Flat
      (pullback.snd V.ι (pullback.fst (pullback.snd g g') (U.fromSpecResidueField u)) ≫
        pullback.snd (pullback.snd g g') (U.fromSpecResidueField u)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@Flat.{u} : MorphismProperty Scheme.{u})) sq inferInstance
  refine (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq _ _).mpr fun z => ?_
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ sq z]
  exact congrArg _ (Scheme.fromSpecResidueField_apply u z)

/-- The fibre of the base change `f'` of `f` over `y'` is the base change of the fibre of `f` over
the image of `y'`, so it inherits that fibre's degree. -/
private theorem isFiniteLocallyFreeOfRank_fiber_of_isPullback {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g) (y' : Y')
    {r : ℕ}
    (h : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (f.fiberToSpecResidueField (g.base y')) r) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank (f'.fiberToSpecResidueField y') r := by
  have := h
  exact Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback
    (f := f.fiberToSpecResidueField (g.base y'))
    (isPullback_fiberToSpecResidueField_of_isPullback sq y')

/-- If the fibre product splits as `V ⊔ W` with `W` lying over no point equal to `u`, then the
part of the fibre over `u` lying in `V` is the whole fibre. -/
private theorem isIso_pullbackSnd_ι_of_isCompl {U : Scheme.{u}} (g' : U ⟶ Y)
    {V W : (pullback g g').Opens} (hcompl : IsCompl V W) (u : U)
    (hWu : ∀ w : W, (pullback.snd g g').base (W.ι.base w) ≠ u) :
    IsIso (pullback.snd V.ι (pullback.fst (pullback.snd g g') (U.fromSpecResidueField u))) := by
  refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
  rw [Scheme.Hom.opensRange_pullbackSnd, Scheme.Opens.opensRange_ι]
  refine TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun z => ?_)
  have hqz : (pullback.snd g g').base
      ((pullback.fst (pullback.snd g g') (U.fromSpecResidueField u)).base z) = u := by
    have hc := congrArg (fun m : pullback (pullback.snd g g')
        (U.fromSpecResidueField u) ⟶ U => m.base z)
      (pullback.condition (f := pullback.snd g g') (g := U.fromSpecResidueField u))
    simp only [Scheme.Hom.comp_apply] at hc
    rw [hc]
    exact Scheme.fromSpecResidueField_apply u _
  have hmem : (pullback.fst (pullback.snd g g') (U.fromSpecResidueField u)).base z ∈
      (⊤ : (pullback g g').Opens) := trivial
  rw [← hcompl.sup_eq_top] at hmem
  rcases hmem with hV | hW
  · exact hV
  · exact absurd hqz (hWu ⟨_, hW⟩)

/-- The rank at `u'` of the finite flat piece `V.ι ≫ pullback.snd g g'` is at most the degree of
the fibre of `g` over the image of `u'`. -/
private theorem finrank_le_of_isFiniteLocallyFreeOfRank_fiber {U : Scheme.{u}} (g' : U ⟶ Y)
    (V : (pullback g g').Opens) [Flat g] [LocallyOfFinitePresentation g]
    [IsFinite (V.ι ≫ pullback.snd g g')] (u' : U) {r : ℕ}
    (hr : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (g.fiberToSpecResidueField (g'.base u')) r) :
    (V.ι ≫ pullback.snd g g').finrank u' ≤ r := by
  obtain ⟨r', hr'r, hr'⟩ := exists_isFiniteLocallyFreeOfRank_le_of_isOpenImmersion
    (k := (U.residueField u' : Type u))
    (pullback.snd (pullback.snd g g') (U.fromSpecResidueField u'))
    (pullback.snd V.ι (pullback.fst (pullback.snd g g') (U.fromSpecResidueField u'))) r
    (h := isFiniteLocallyFreeOfRank_fiber_of_isPullback (IsPullback.of_hasPullback g g') u' hr)
  rwa [rank_eq_of_isFiniteLocallyFreeOfRank _
    (isFiniteLocallyFreeOfRank_restricted_fibre g g' V u') hr']

/-- **The degree of the fibres of a quasi-finite flat morphism is lower semicontinuous.**

Let `g : Z ⟶ Y` be flat, locally of finite presentation, separated, locally quasi-finite and
quasi-compact, and let the fibre of `g` over `y` be finite locally free of rank `e` over the
residue field at `y`. Then `y` has an open neighbourhood over every point of which the fibre of
`g` is finite locally free of some rank at least `e`.

The hypothesis is satisfiable at every point, by
`AlgebraicGeometry.exists_isFiniteLocallyFreeOfRank_fiberToSpecResidueField`, so the statement
is not vacuous for any `g`.

This is the geometric content of Tag 086R; what Tag 086R adds is the reduction of a locally
quasi-finite morphism to its quasi-compact opens. -/
theorem exists_opens_mem_forall_le_rank_fiberToSpecResidueField
    [Flat g] [LocallyOfFinitePresentation g] [IsSeparated g] [LocallyQuasiFinite g]
    [QuasiCompact g] (y : Y) (e : ℕ)
    (he : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (g.fiberToSpecResidueField y) e) :
    ∃ Ω : Y.Opens, y ∈ Ω ∧ ∀ y' ∈ Ω, ∃ r : ℕ, e ≤ r ∧
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank (g.fiberToSpecResidueField y') r := by
  obtain ⟨U, g', u, hetale, hgu, -, V, W, hcompl, hVfin, hWu⟩ :=
    exists_elementaryEtale_isCompl_isEmpty_fiber_of_finite_fiber g
      (finite_preimage_singleton_of_locallyQuasiFinite g y)
  have _hetale : Etale g' := hetale
  have _hVfin : IsFinite (V.ι ≫ pullback.snd g g') := hVfin
  -- over `u` the finite piece is the whole fibre, so the rank there is `e`
  have := isIso_pullbackSnd_ι_of_isCompl g g' hcompl u hWu
  have hranku : (V.ι ≫ pullback.snd g g').finrank u = e :=
    rank_eq_of_isFiniteLocallyFreeOfRank _ (isFiniteLocallyFreeOfRank_restricted_fibre g g' V u)
      ((MorphismProperty.cancel_left_of_respectsIso
        (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} e)
        (pullback.snd V.ι (pullback.fst (pullback.snd g g') (U.fromSpecResidueField u)))
        (pullback.snd (pullback.snd g g') (U.fromSpecResidueField u))).mpr
          (isFiniteLocallyFreeOfRank_fiber_of_isPullback (IsPullback.of_hasPullback g g') u
            (by rwa [hgu])))
  refine ⟨⟨g'.base '' {u' : U | (V.ι ≫ pullback.snd g g').finrank u' =
      (V.ι ≫ pullback.snd g g').finrank u},
    g'.isOpenMap _ ((Scheme.Hom.isLocallyConstant_finrank _).isOpen_fiber _)⟩, ⟨u, rfl, hgu⟩, ?_⟩
  -- over any other point of the open the fibre contains a piece of that rank
  rintro y' ⟨u', hu' : (V.ι ≫ pullback.snd g g').finrank u' = _, rfl⟩
  obtain ⟨r, hr⟩ := exists_isFiniteLocallyFreeOfRank_fiberToSpecResidueField g (g'.base u')
  have := finrank_le_of_isFiniteLocallyFreeOfRank_fiber g g' V u' hr
  exact ⟨r, by omega, hr⟩

/-- **The locus where the fibre has degree at least `d` is open.**

This is `AlgebraicGeometry.exists_opens_mem_forall_le_rank_fiberToSpecResidueField` restated as
openness of a set: the degree at a point of the locus is at least `d`, and the neighbourhood the
semicontinuity statement produces at that point lies in the locus. -/
theorem isOpen_setOf_exists_le_rank_fiberToSpecResidueField
    [Flat g] [LocallyOfFinitePresentation g] [IsSeparated g] [LocallyQuasiFinite g]
    [QuasiCompact g] (d : ℕ) :
    IsOpen {y : Y | ∃ r : ℕ, d ≤ r ∧
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank (g.fiberToSpecResidueField y) r} := by
  rw [isOpen_iff_forall_mem_open]
  rintro y ⟨e, hde, he⟩
  obtain ⟨Ω, hyΩ, hΩ⟩ := exists_opens_mem_forall_le_rank_fiberToSpecResidueField g y e he
  refine ⟨(Ω : Set Y), fun y' hy' => ?_, Ω.isOpen, hyΩ⟩
  obtain ⟨r, her, hr⟩ := hΩ y' hy'
  exact ⟨r, hde.trans her, hr⟩

/-- The degree of a finite scheme over a field is the degree of its fibre over the unique point
of that field's spectrum.

Both inequalities come from `AlgebraicGeometry.boundsFiberDegrees_iff_field_baseChange`: the
degree of the fibre bounds the degrees of all field-valued base changes, of which `p` itself is
one up to an isomorphism of the source, and conversely the degree of `p` bounds itself after any
base change and hence bounds the degree of the fibre. -/
private theorem rank_eq_rank_fiberToSpecResidueField {k : Type u} [Field k] {V : Scheme.{u}}
    (p : V ⟶ Spec (.of k)) [IsFinite p] {a b : ℕ}
    (ha : Stacks.Morphisms.IsFiniteLocallyFreeOfRank p a)
    (hb : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (p.fiberToSpecResidueField (IsLocalRing.closedPoint k)) b) : a = b := by
  have hBb : BoundsFiberDegrees p (b : ℤ) := by
    intro z
    refine ⟨b, le_rfl, ?_⟩
    rwa [Subsingleton.elim z (IsLocalRing.closedPoint k)]
  obtain ⟨r', hr'b, hr'⟩ := (boundsFiberDegrees_iff_field_baseChange p (b : ℤ)).mp hBb
    k (𝟙 (Spec (.of k)))
  have hsnd : IsIso (pullback.snd (𝟙 (Spec (.of k))) p) :=
    (IsPullback.of_hasPullback (𝟙 (Spec (.of k))) p).isIso_snd_of_isIso
  have hfe : pullback.fst (𝟙 (Spec (.of k))) p = pullback.snd (𝟙 (Spec (.of k))) p ≫ p := by
    rw [← pullback.condition, Category.comp_id]
  have hap : Stacks.Morphisms.IsFiniteLocallyFreeOfRank p r' := by
    rw [hfe] at hr'
    exact (MorphismProperty.cancel_left_of_respectsIso
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r')
      (pullback.snd (𝟙 (Spec (.of k))) p) p).mp hr'
  have h1 : a = r' := rank_eq_of_isFiniteLocallyFreeOfRank p ha hap
  have hBa : BoundsFiberDegrees p (a : ℤ) := by
    refine (boundsFiberDegrees_iff_field_baseChange p (a : ℤ)).mpr fun k' _ c => ⟨a, le_rfl, ?_⟩
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} a)
      (IsPullback.of_hasPullback c p).flip ha
  obtain ⟨s, hsa, hs⟩ := hBa (IsLocalRing.closedPoint k)
  have h2 : b = s := rank_eq_of_isFiniteLocallyFreeOfRank _ hb hs
  omega

/-- The base change of a quasi-compact locally quasi-finite morphism to the spectrum of a field
is a finite morphism. -/
theorem isFinite_pullback_fst_of_locallyQuasiFinite
    [LocallyQuasiFinite g] [QuasiCompact g] {k : Type u} [Field k] (c : Spec (.of k) ⟶ Y) :
    IsFinite (pullback.fst c g) :=
  IsFinite.of_locallyQuasiFinite _

/-- **The degree of a field-valued base change is the degree of the fibre over its image
point.**

The base change of `g` along `c : Spec k ⟶ Y` is a finite scheme over `k`, and its fibre over
the unique point of `Spec k` is a base change of the fibre of `g` over the image of that point;
since the degree of a finite scheme over a field is unique, the two degrees agree. -/
theorem isFiniteLocallyFreeOfRank_pullback_fst_iff
    [LocallyQuasiFinite g] [QuasiCompact g] {k : Type u} [Field k] (c : Spec (.of k) ⟶ Y)
    (r : ℕ) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank (pullback.fst c g) r ↔
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank
        (g.fiberToSpecResidueField (c.base (IsLocalRing.closedPoint k))) r := by
  have hfin : IsFinite (pullback.fst c g) := isFinite_pullback_fst_of_locallyQuasiFinite g c
  obtain ⟨r₀, hr₀⟩ := exists_isFiniteLocallyFreeOfRank_fiberToSpecResidueField g
    (c.base (IsLocalRing.closedPoint k))
  have hfibre : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((pullback.fst c g).fiberToSpecResidueField (IsLocalRing.closedPoint k)) r₀ :=
    isFiniteLocallyFreeOfRank_fiber_of_isPullback (IsPullback.of_hasPullback c g).flip _ hr₀
  obtain ⟨a, hja⟩ := exists_isFiniteLocallyFreeOfRank_of_isFinite (k := k) (pullback.fst c g)
  have hab : a = r₀ := rank_eq_rank_fiberToSpecResidueField (pullback.fst c g) hja hfibre
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain rfl := rank_eq_of_isFiniteLocallyFreeOfRank (pullback.fst c g) h hja
    rwa [hab]
  · obtain rfl := rank_eq_of_isFiniteLocallyFreeOfRank
      (k := (Y.residueField (c.base (IsLocalRing.closedPoint k)) : Type u)) _ h hr₀
    rwa [← hab]

/-- **Stacks Project, Tag 086R**, for a morphism which is in addition quasi-compact, and in the
membership form.

Let `g : Z ⟶ Y` be flat, locally of finite presentation, separated, locally quasi-finite and
quasi-compact. Then there is a decreasing chain of opens `Y = V 0 ⊇ V 1 ⊇ V 2 ⊇ …` such that the
image of a morphism `Spec k ⟶ Y` from the spectrum of a field lies in `V d` exactly when the
base change of `g` to `Spec k` either fails to be finite or is finite locally free of some rank
at least `d`.

Two things separate this from Tag 086R, and nothing else: the hypothesis `QuasiCompact g`, and
the membership form of the conclusion. See the implementation notes of this module, which also
record that the disjunct `¬ IsFinite (pullback.fst c g)` is never the one that holds here — under
`QuasiCompact g` every field-valued base change is finite — so it is carried only to keep the
statement comparable with the tag. -/
theorem exists_antitone_opens_iff_fibreDegree_ge_of_quasiCompact
    [Flat g] [LocallyOfFinitePresentation g] [IsSeparated g] [LocallyQuasiFinite g]
    [QuasiCompact g] :
    ∃ V : ℕ → Y.Opens, V 0 = ⊤ ∧ Antitone V ∧
      ∀ (d : ℕ) (k : Type u) (_ : Field k) (c : Spec (.of k) ⟶ Y),
        c.base (IsLocalRing.closedPoint k) ∈ V d ↔
          (¬ IsFinite (pullback.fst c g) ∨
            ∃ r : ℕ, d ≤ r ∧
              Stacks.Morphisms.IsFiniteLocallyFreeOfRank (pullback.fst c g) r) := by
  refine ⟨fun d => ⟨{y : Y | ∃ r : ℕ, d ≤ r ∧
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank (g.fiberToSpecResidueField y) r},
    isOpen_setOf_exists_le_rank_fiberToSpecResidueField g d⟩, ?_, ?_, ?_⟩
  · refine TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun y => ?_)
    obtain ⟨r, hr⟩ := exists_isFiniteLocallyFreeOfRank_fiberToSpecResidueField g y
    exact ⟨r, Nat.zero_le r, hr⟩
  · rintro d d' hdd' y ⟨r, hr, hrr⟩
    exact ⟨r, hdd'.trans hr, hrr⟩
  · refine fun d k hk c => ⟨?_, ?_⟩
    · rintro ⟨r, hdr, hr⟩
      exact Or.inr ⟨r, hdr, (isFiniteLocallyFreeOfRank_pullback_fst_iff g c r).mpr hr⟩
    · rintro (hn | ⟨r, hdr, hr⟩)
      · exact absurd (isFinite_pullback_fst_of_locallyQuasiFinite g c) hn
      · exact ⟨r, hdr, (isFiniteLocallyFreeOfRank_pullback_fst_iff g c r).mp hr⟩

end AlgebraicGeometry

end
