module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Coproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSurjection
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Quasi-compactness of a morphism of algebraic spaces is étale-local on the target

Stacks 03KG lists six equivalent conditions on a morphism `f : X ⟶ Y` of algebraic spaces
over a scheme `S`. This file proves that its first four are equivalent:

* (1) `f` is quasi-compact in the sense of Stacks 03HE;
* (2) for every object `Z` of the site and every `g : h_Z ⟶ Y` the projection
  `Z ×_Y X ⟶ h_Z` is quasi-compact;
* (3) for every object `Z` of the site with affine underlying scheme and every
  `g : h_Z ⟶ Y` the algebraic space `Z ×_Y X` is quasi-compact;
* (4) there is an object `V` of the site and a surjective étale `φ : h_V ⟶ Y` such that the
  projection `V ×_Y X ⟶ h_V` is quasi-compact;
* (5) the same with `h_V` replaced by an arbitrary algebraic space `Y'` over `S`.

Seven implications are proved — (1) ⇒ (2), (2) ⇒ (3), (3) ⇒ (1), (1) ⇒ (4), (4) ⇒ (1),
(4) ⇒ (5) and (5) ⇒ (4) — which make `{1, 2, 3, 4, 5}` a single strongly connected component,
so four of the five adjacent equivalences of Stacks 03KG are closed. Condition (6), the
Zariski-local one, is not treated.

The implication (4) ⇒ (1) is the leg that Stacks 03JV invokes, in the step from its condition
(3) to its condition (4): there a quasi-compact monomorphism `Spec(k) ⟶ X` is produced by
checking quasi-compactness of its base change along a surjective étale chart of `X`.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isQuasiCompact_of_surjectiveEtale_atlas` is Stacks 03KG,
  part (4) implies part (1).
* `AlgebraicGeometry.Space.exists_surjectiveEtale_atlas_isQuasiCompact_pullback_snd` is the
  converse, Stacks 03KG part (1) implies part (4).
* `AlgebraicGeometry.Space.isQuasiCompact_pullback_snd_of_isQuasiCompact`,
  `AlgebraicGeometry.Space.isQuasiCompactSpace_pullback_of_isQuasiCompact_pullback_snd` and
  `AlgebraicGeometry.Space.isQuasiCompact_of_isQuasiCompactSpace_pullback_affine'` are
  Stacks 03KG parts (1) ⇒ (2), (2) ⇒ (3) and (3) ⇒ (1).
* `AlgebraicGeometry.Space.exists_isAlgebraicSpace_surjectiveEtale_isQuasiCompact_pullback_snd`
  and `AlgebraicGeometry.Space.exists_surjectiveEtale_atlas_of_isAlgebraicSpace_surjectiveEtale`
  are Stacks 03KG parts (4) ⇒ (5) and (5) ⇒ (4).
* `AlgebraicGeometry.Space.isQuasiCompactSpace_source_of_isQuasiCompact`: the source of a
  quasi-compact morphism of algebraic spaces with quasi-compact target is quasi-compact.
* `AlgebraicGeometry.Space.isQuasiCompactSpace_pullback_of_isSurjective`: a base change of
  `f` may be tested after a further surjective base change of the test object.
* `AlgebraicGeometry.Space.exists_compactSpace_factoring_of_isSurjective_isEtale`: a
  quasi-compact test object has a surjective base change by a quasi-compact object which
  moreover factors through the given chart `φ`.
* `AlgebraicGeometry.exists_isCompact_opens_image_eq_univ`: the scheme-level refinement, that
  an open surjection onto a quasi-compact scheme is already surjective on a quasi-compact open
  of its source.

## Implementation notes

The route of the source is *not* taken. Stacks reaches (1) from (4) through its condition (5)
and Stacks 04ZJ — quasi-compactness descends along a universally open surjection — together
with universal openness of an étale morphism of algebraic spaces. Tag 04ZJ has no site in this
repository, in any of the attribute forms, so the proof here is direct, and consists of two
reductions followed by one application of the hypothesis.

The first reduction, `isQuasiCompactSpace_pullback_of_isSurjective`, is Stacks 040W part (1)
pasted against `CategoryTheory.IsPullback.of_right'`: the comparison map between the two fibre
products over a surjection `u : Z' ⟶ Z` is itself a base change of `u`, hence surjective by
Stacks 03MH, and quasi-compactness of the source of a surjection of algebraic spaces passes
to its target. It is applied twice — once to replace an arbitrary quasi-compact test object by
an affine scheme chart of it (Stacks 03H6), which is exactly part (3) implies part (1), and
once to replace that affine scheme by the object produced by the second reduction.

The cycle through parts (2) and (3) costs nothing beyond that. Part (1) implies part (2) is
Stacks 03HF read at the chosen fibre product, and part (2) implies part (3) is
`isQuasiCompactSpace_source_of_isQuasiCompact` applied to the projection to `h_Z`, whose
target is a quasi-compact algebraic space because `Z` is affine. That last lemma is a gap in
this development noted in prose at
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleRefiningFiniteCover.lean`: a quasi-compact
morphism tested against the identity of its target gives its own source back, up to the
isomorphism `pullback.snd (𝟙 G) m`.

The second reduction is where the geometry is. The base change `U ×_Y V ⟶ U` of the chart `φ`
along the test object is surjective and étale, so an étale atlas `h_T ⟶ U ×_Y V` of it gives a
morphism `T ⟶ U` of the site whose underlying morphism of schemes is surjective and étale,
hence open. Only finitely many affine opens of `T` are needed to cover the quasi-compact `U`,
and their union is a quasi-compact open `W ⊆ T` which is again an object of the site by
`AlgebraicGeometry.exists_restrict_bigFppfOver`. That object is quasi-compact, still surjects
onto `U`, and — being built over the atlas of `U ×_Y V` — carries a morphism to `h_V` through
which its morphism to `Y` factors. Quasi-compactness of `V ×_Y X ⟶ V` may then be tested
against it directly, and `CategoryTheory.Limits.pullbackLeftPullbackSndIso` identifies the
resulting fibre product with the one wanted.

Both surjectivity and étaleness are carried in the represented form
`CategoryTheory.MorphismProperty.presheaf`, where base change and composition are available
from `CategoryTheory.MorphismProperty.relative_isStableUnderBaseChange` and the
multiplicativity statements of this development; the point-set form of Stacks 03ME is entered
and left through Stacks 03H5,
`AlgebraicGeometry.Space.presheafSurjective_iff_isSurjective_yoneda`.

Note that the hypothesis of part (4) is quasi-compactness of `pullback.snd f φ`, the
projection of `V ×_Y X` to `h_V`. The other projection `pullback.snd φ f` of the same fibre
product goes to `X`, and quasi-compactness of *that* morphism does not imply part (1): when
`φ` is an isomorphism it holds for every `f` whatsoever.

## References

* [Stacks Project, Tag 03KG](https://stacks.math.columbia.edu/tag/03KG)
* [Stacks Project, Tag 03E3](https://stacks.math.columbia.edu/tag/03E3)
* [Stacks Project, Tag 03FR](https://stacks.math.columbia.edu/tag/03FR)
* [Stacks Project, Tag 03H5](https://stacks.math.columbia.edu/tag/03H5)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 03HF](https://stacks.math.columbia.edu/tag/03HF)
* [Stacks Project, Tag 03ME](https://stacks.math.columbia.edu/tag/03ME)
* [Stacks Project, Tag 03MH](https://stacks.math.columbia.edu/tag/03MH)
* [Stacks Project, Tag 03WT](https://stacks.math.columbia.edu/tag/03WT)
* [Stacks Project, Tag 040W](https://stacks.math.columbia.edu/tag/040W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **An open surjection onto a quasi-compact scheme is surjective already on a quasi-compact
open of its source.** If `t : T ⟶ U` is a morphism of schemes whose underlying map is open and
surjective and whose target is quasi-compact, then some quasi-compact open `W` of `T` has
`t(W) = U`.

The affine opens of `T` cover it, so their open images cover `U`; finitely many of them already
do, and the union of those finitely many affine opens is quasi-compact. Openness is used only
to make the images open, and no hypothesis is placed on `T`. -/
theorem exists_isCompact_opens_image_eq_univ {T U : Scheme.{u}} (t : T ⟶ U)
    [CompactSpace U] (hopen : IsOpenMap t.base) (hsurj : Function.Surjective t.base) :
    ∃ W : T.Opens, IsCompact (W : Set T) ∧ t.base '' (W : Set T) = Set.univ := by
  classical
  have hopens : ∀ i, IsOpen (t.base '' ((T.affineCover.f i).opensRange : Set T)) := fun i =>
    hopen _ (T.affineCover.f i).opensRange.isOpen
  have huniv : (Set.univ : Set U) ⊆
      ⋃ i, t.base '' ((T.affineCover.f i).opensRange : Set T) := by
    intro y _
    obtain ⟨x, rfl⟩ := hsurj y
    exact Set.mem_iUnion.2 ⟨T.affineCover.idx x, ⟨x, T.affineCover.covers x, rfl⟩⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover _ hopens huniv
  have hset : ((⨆ i ∈ s, (T.affineCover.f i).opensRange : T.Opens) : Set T) =
      ⋃ i ∈ s, ((T.affineCover.f i).opensRange : Set T) := by simp
  refine ⟨⨆ i ∈ s, (T.affineCover.f i).opensRange, ?_, ?_⟩
  · rw [hset]
    refine s.finite_toSet.isCompact_biUnion fun i _ => ?_
    exact isCompact_range (Scheme.Hom.continuous (T.affineCover.f i))
  · rw [hset, Set.image_iUnion₂]
    exact Set.eq_univ_of_univ_subset hs

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A test object for quasi-compactness may be replaced by a surjective base change of
it.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`, let `g : Z ⟶ Y` be a test
morphism, and let `u : Z' ⟶ Z` be surjective on points. If the fibre product of `f` with the
composite `u ≫ g` is a quasi-compact algebraic space, then so is the fibre product of `f`
with `g`.

The comparison map `Z' ×_Y X ⟶ Z ×_Y X` is a base change of `u`, produced together with its
cartesian square by `CategoryTheory.IsPullback.of_right'`; it is therefore surjective by
Stacks 03MH, and Stacks 040W part (1) transfers quasi-compactness along it. The composite is
given as `g'` with an equation rather than as `u ≫ g` so that a consumer may hand over a
factorization of `g'` through another morphism. -/
theorem isQuasiCompactSpace_pullback_of_isSurjective
    {X Y Z Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (g : Z ⟶ Y) (u : Z' ⟶ Z)
    {g' : Z' ⟶ Y}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (hZ' : IsAlgebraicSpace B S hS Z')
    (hu : IsSurjective B S hS u) (hg : u ≫ g = g')
    (h : IsQuasiCompactSpace B S hS (pullback g' f)) :
    IsQuasiCompactSpace B S hS (pullback g f) := by
  subst hg
  have hbot : IsPullback (pullback.snd g f) (pullback.fst g f) f g :=
    (IsPullback.of_hasPullback g f).flip
  have htop : IsPullback (pullback.snd (u ≫ g) f) (pullback.fst (u ≫ g) f) f (u ≫ g) :=
    (IsPullback.of_hasPullback (u ≫ g) f).flip
  exact IsQuasiCompactSpace.of_isSurjective B S hS
    (isAlgebraicSpace_pullback B S hS (u ≫ g) f hZ' hX hY)
    (isAlgebraicSpace_pullback B S hS g f hZ hX hY)
    (surjective_pointsMap_of_isPullback B S hS (IsPullback.of_right' htop hbot).flip hu) h

/-- **A quasi-compact test object is covered by a quasi-compact one factoring through a given
surjective étale chart.** Let `Y` be an algebraic space over `S`, let `φ : h_V ⟶ Y` be
surjective and étale, and let `g : h_U ⟶ Y` be a morphism from an object `U` of the site whose
underlying scheme is quasi-compact. Then there are an object `A` of the site with quasi-compact
underlying scheme, a morphism `α : A ⟶ U` which is surjective on points, and a morphism
`w : h_A ⟶ h_V` with `α ≫ g = w ≫ φ`.

The base change `U ×_Y V ⟶ h_U` of `φ` is surjective and étale, and an étale atlas `h_T` of
`U ×_Y V` turns the composite into the Yoneda image of a morphism `τ : T ⟶ U` of the site whose
underlying morphism of schemes is surjective and étale, hence open by Stacks 03WT. By
`AlgebraicGeometry.exists_isCompact_opens_image_eq_univ` a quasi-compact open `W` of `T`
already surjects onto `U`, and `AlgebraicGeometry.exists_restrict_bigFppfOver` realises `W` as
an object of the site over `T`. The morphism to `h_V` is the atlas composed with the second
projection of the fibre product, and the factorization is the cartesian square of that fibre
product. -/
theorem exists_compactSpace_factoring_of_isSurjective_isEtale
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (U V : BigFppfOver B S hS)
    (hU : CompactSpace ((BigFppfOver.toScheme B S hS).obj U))
    (g : yoneda.obj U ⟶ Y) (φ : yoneda.obj V ⟶ Y)
    (hsurj : IsSurjective B S hS φ) (hφ : IsEtale B S hS φ) :
    ∃ (A : BigFppfOver B S hS) (α : A ⟶ U) (w : yoneda.obj A ⟶ yoneda.obj V),
      CompactSpace ((BigFppfOver.toScheme B S hS).obj A) ∧
      IsSurjective B S hS (yoneda.map α) ∧
      yoneda.map α ≫ g = w ≫ φ := by
  classical
  have hmulS := isMultiplicative_presheaf_surjective B S hS
  have hmulE := isMultiplicative_presheaf_etale B S hS
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have _ : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    MorphismProperty.inverseImage_isStableUnderBaseChange _ _
  have _ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    MorphismProperty.inverseImage_isStableUnderBaseChange _ _
  -- The chart `φ` in represented form.
  have hφS : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS Y hY V φ).mpr hsurj
  have hφE : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ := by
    simpa using hφ V (𝟙 (yoneda.obj V)) (MorphismProperty.id_mem _ _)
  -- Its base change along the test object.
  have sqD : IsPullback (pullback.fst g φ) (pullback.snd g φ) g φ := IsPullback.of_hasPullback _ _
  have hD : IsAlgebraicSpace B S hS (pullback g φ) :=
    isAlgebraicSpace_pullback B S hS g φ (isAlgebraicSpace_yoneda B S hS U)
      (isAlgebraicSpace_yoneda B S hS V) hY
  have hdS := (MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).of_isPullback sqD.flip hφS
  have hdE := (MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).of_isPullback sqD.flip hφE
  -- An atlas of the base change, and the morphism of the site it induces.
  obtain ⟨T, p, hpS, hpE⟩ := hD.exists_atlas
  have htS := MorphismProperty.comp_mem _ p (pullback.fst g φ) hpS hdS
  have htE := MorphismProperty.comp_mem _ p (pullback.fst g φ) hpE hdE
  obtain ⟨τ, hτ⟩ : ∃ τ : T ⟶ U, yoneda.map τ = p ≫ pullback.fst g φ :=
    ⟨yoneda.preimage _, yoneda.map_preimage _⟩
  have hτS' : MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS) τ :=
    MorphismProperty.of_relative_map (F := yoneda) (by rw [hτ]; exact htS)
  have hτE' : MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS) τ :=
    MorphismProperty.of_relative_map (F := yoneda) (by rw [hτ]; exact htE)
  have hτS : Surjective ((BigFppfOver.toScheme B S hS).map τ) := hτS'
  have hτE : Etale ((BigFppfOver.toScheme B S hS).map τ) := hτE'
  -- A quasi-compact open of `T` still surjecting onto `U`.
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj U) := hU
  have : Etale ((BigFppfOver.toScheme B S hS).map τ) := hτE
  obtain ⟨W, hWcpt, hWimg⟩ := exists_isCompact_opens_image_eq_univ
    ((BigFppfOver.toScheme B S hS).map τ)
    ((BigFppfOver.toScheme B S hS).map τ).isOpenMap hτS.surj
  obtain ⟨A, ι, hιoi, hιrange, -⟩ := exists_restrict_bigFppfOver T W
  have : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map ι) := hιoi
  have hAcpt : CompactSpace ((BigFppfOver.toScheme B S hS).obj A) := by
    rw [← isCompact_univ_iff]
    have hemb : Topology.IsEmbedding ((BigFppfOver.toScheme B S hS).map ι).base :=
      (Scheme.Hom.isOpenEmbedding ((BigFppfOver.toScheme B S hS).map ι)).isEmbedding
    rw [hemb.isCompact_iff, Set.image_univ, hιrange]
    exact hWcpt
  have hαsurj : Function.Surjective ((BigFppfOver.toScheme B S hS).map (ι ≫ τ)) := by
    intro y
    have hy : y ∈ ((BigFppfOver.toScheme B S hS).map τ) '' (W : Set _) := by
      rw [hWimg]; trivial
    obtain ⟨x, hxW, hxy⟩ := hy
    rw [← hιrange] at hxW
    obtain ⟨a, ha⟩ := hxW
    refine ⟨a, ?_⟩
    rw [Functor.map_comp, Scheme.Hom.comp_apply, ha]
    exact hxy
  have hαrel : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map (ι ≫ τ)) :=
    MorphismProperty.relative_map (F := yoneda)
      (show MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS) (ι ≫ τ) from ⟨hαsurj⟩)
  refine ⟨A, ι ≫ τ, yoneda.map ι ≫ p ≫ pullback.snd g φ, hAcpt,
    isSurjective_of_presheafSurjective B S hS _ hαrel, ?_⟩
  simp only [Functor.map_comp, hτ, Category.assoc, sqD.w]

/-- **The source of a quasi-compact morphism with quasi-compact target is quasi-compact.**
If `m : F ⟶ G` is a quasi-compact morphism of algebraic spaces over `S` and `G` is a
quasi-compact algebraic space, then so is `F`.

Testing `m` against the identity of `G` gives the fibre product `G ×_G F`, which is `F` up to
the isomorphism `pullback.snd (𝟙 G) m`. This fills a gap recorded in prose at
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleRefiningFiniteCover.lean`, where it is observed
that nothing in this development draws quasi-compactness of a source from a property of a
morphism over a merely quasi-compact target. -/
theorem isQuasiCompactSpace_source_of_isQuasiCompact
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hG : IsAlgebraicSpace B S hS G)
    (hGqc : IsQuasiCompactSpace B S hS G) {m : F ⟶ G} (hm : IsQuasiCompact B S hS m) :
    IsQuasiCompactSpace B S hS F :=
  isQuasiCompactSpace_of_iso B S hS (asIso (pullback.snd (𝟙 G) m)) (hm G hG hGqc (𝟙 G))

/-- **Stacks 03KG, part (1) implies part (2).** If `f : X ⟶ Y` is a quasi-compact morphism of
algebraic spaces over `S`, then for every object `Z` of the site and every `g : h_Z ⟶ Y` the
projection `Z ×_Y X ⟶ h_Z` is quasi-compact.

This is Stacks 03HF, `AlgebraicGeometry.Space.isQuasiCompact_of_isPullback`, read at the
cartesian square of the chosen fibre product; no representability of `Z` is used. -/
@[stacks 03KG "part (1) implies part (2)"]
theorem isQuasiCompact_pullback_snd_of_isQuasiCompact
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} (hf : IsQuasiCompact B S hS f)
    (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y) :
    IsQuasiCompact B S hS (pullback.snd f g) :=
  isQuasiCompact_of_isPullback B S hS (IsPullback.of_hasPullback f g) hf

/-- **Stacks 03KG, part (2) implies part (3).** If every projection `Z ×_Y X ⟶ h_Z` of
`f : X ⟶ Y` along a morphism from a represented presheaf is quasi-compact, then `Z ×_Y X` is a
quasi-compact algebraic space whenever the scheme underlying `Z` is affine.

An affine object of the site represents a quasi-compact algebraic space, and
`AlgebraicGeometry.Space.isQuasiCompactSpace_source_of_isQuasiCompact` then transfers
quasi-compactness from the target of the projection to its source. Only the single instance
`g` of part (2) is used, not the whole of it, and the algebraic-space hypotheses `_hX` and
`_hY` are retained from the source but are not needed. -/
@[stacks 03KG "part (2) implies part (3)"]
theorem isQuasiCompactSpace_pullback_of_isQuasiCompact_pullback_snd
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (_hX : IsAlgebraicSpace B S hS X) (_hY : IsAlgebraicSpace B S hS Y)
    (h : ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
      IsQuasiCompact B S hS (pullback.snd f g))
    (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y)
    (hZ : IsAffine ((BigFppfOver.toScheme B S hS).obj Z)) :
    IsQuasiCompactSpace B S hS (pullback f g) := by
  have hZcpt : CompactSpace ((BigFppfOver.toScheme B S hS).obj Z) := by
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj Z) := hZ
    infer_instance
  exact isQuasiCompactSpace_source_of_isQuasiCompact B S hS
    (isAlgebraicSpace_yoneda B S hS Z) (isQuasiCompactSpace_yoneda_obj B S hS hZcpt) (h Z g)

/-- **Stacks 03KG, part (3) implies part (1): quasi-compactness of a morphism of algebraic
spaces may be tested on affine schemes.** If `Z ×_Y X` is a quasi-compact algebraic space for
every object `Z` of the site with affine underlying scheme and every `g : h_Z ⟶ Y`, then
`f : X ⟶ Y` is quasi-compact.

A quasi-compact algebraic space has a surjective étale morphism from an affine scheme by
Stacks 03H6, and `AlgebraicGeometry.Space.isQuasiCompactSpace_pullback_of_isSurjective`
replaces the test object by that affine scheme.

`AlgebraicGeometry.Space.isQuasiCompact_of_isQuasiCompactSpace_pullback_affine` is the same
assertion with the fibre product of the hypothesis taken in the other order and the two
algebraic-space hypotheses in front of the morphism. -/
@[stacks 03KG "part (3) implies part (1)"]
theorem isQuasiCompact_of_isQuasiCompactSpace_pullback_affine'
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (h : ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
      IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
        IsQuasiCompactSpace B S hS (pullback f g)) :
    IsQuasiCompact B S hS f := by
  intro Z hZ hZqc g
  obtain ⟨U, e, hUaff, heS, heE⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS Z hZ).mp hZqc
  refine isQuasiCompactSpace_pullback_of_isSurjective B S hS f g e hX hY hZ
    (isAlgebraicSpace_yoneda B S hS U)
    (isSurjective_of_presheafSurjective B S hS e heS) rfl ?_
  exact isQuasiCompactSpace_of_iso B S hS (pullbackSymmetry f (e ≫ g)) (h U (e ≫ g) hUaff)

/-- **Stacks 03KG, part (4) implies part (1): quasi-compactness of a morphism of algebraic
spaces is étale-local on the target.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over
`S`. If there are an object `V` of the site and a surjective étale morphism `φ : h_V ⟶ Y` such
that the projection `V ×_Y X ⟶ h_V` is quasi-compact, then `f` is quasi-compact.

This is the leg of Stacks 03KG that the proof of Stacks 03JV uses in passing from its
condition (3) to its condition (4). Quasi-compactness of an arbitrary test object is reduced
in two steps — to an affine scheme chart of it, which is part (3) implies part (1), and from
there to a quasi-compact object factoring through `φ` by
`AlgebraicGeometry.Space.exists_compactSpace_factoring_of_isSurjective_isEtale` — after which
the hypothesis applies directly. -/
@[stacks 03KG "part (4) implies part (1)"]
theorem isQuasiCompact_of_surjectiveEtale_atlas
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (V : BigFppfOver B S hS) (φ : yoneda.obj V ⟶ Y)
    (hsurj : IsSurjective B S hS φ) (hφ : IsEtale B S hS φ)
    (h : IsQuasiCompact B S hS (pullback.snd f φ)) :
    IsQuasiCompact B S hS f := by
  refine isQuasiCompact_of_isQuasiCompactSpace_pullback_affine' B S hS f hX hY
    fun U g hUaff => ?_
  have hUcpt : CompactSpace ((BigFppfOver.toScheme B S hS).obj U) := by
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hUaff
    infer_instance
  obtain ⟨A, α, w, hAcpt, hαsurj, hcomm⟩ :=
    exists_compactSpace_factoring_of_isSurjective_isEtale B S hS hY U V hUcpt g φ hsurj hφ
  refine isQuasiCompactSpace_of_iso B S hS (pullbackSymmetry g f) ?_
  refine isQuasiCompactSpace_pullback_of_isSurjective B S hS f g (yoneda.map α)
    hX hY (isAlgebraicSpace_yoneda B S hS U) (isAlgebraicSpace_yoneda B S hS A) hαsurj hcomm ?_
  exact isQuasiCompactSpace_of_iso B S hS
    (pullbackSymmetry w (pullback.snd f φ) ≪≫ pullbackLeftPullbackSndIso f φ w ≪≫
      pullbackSymmetry f (w ≫ φ))
    (h (yoneda.obj A) (isAlgebraicSpace_yoneda B S hS A)
      (isQuasiCompactSpace_yoneda_obj B S hS hAcpt) w)

/-- **Stacks 03KG, part (1) implies part (4).** A quasi-compact morphism `f : X ⟶ Y` of
algebraic spaces over `S` has a surjective étale chart `φ : h_V ⟶ Y` of its target along
which its base change `V ×_Y X ⟶ h_V` is quasi-compact.

Any scheme atlas of `Y` will do: it is surjective and étale by Stacks 03H5 and by
multiplicativity of the represented étale morphisms, and the base change of `f` along it is
quasi-compact by Stacks 03HF. Together with
`AlgebraicGeometry.Space.isQuasiCompact_of_surjectiveEtale_atlas` this makes conditions (1) and
(4) of Stacks 03KG equivalent, and it exhibits the hypothesis of that statement as
satisfiable. -/
@[stacks 03KG "part (1) implies part (4)"]
theorem exists_surjectiveEtale_atlas_isQuasiCompact_pullback_snd
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hY : IsAlgebraicSpace B S hS Y) (hf : IsQuasiCompact B S hS f) :
    ∃ (V : BigFppfOver B S hS) (φ : yoneda.obj V ⟶ Y),
      IsSurjective B S hS φ ∧ IsEtale B S hS φ ∧
      IsQuasiCompact B S hS (pullback.snd f φ) := by
  obtain ⟨V, φ, hφS, hφE⟩ := hY.exists_atlas
  exact ⟨V, φ, (presheafSurjective_iff_isSurjective_yoneda B S hS Y hY V φ).mp hφS,
    isEtale_of_presheaf_etale B S hS hφE,
    isQuasiCompact_of_isPullback B S hS (IsPullback.of_hasPullback f φ) hf⟩

/-- **Stacks 03KG, part (4) implies part (5).** A surjective étale chart of `Y` by an object
of the site is in particular a surjective étale morphism of algebraic spaces onto `Y`.

The presheaf represented by an object of the site is an algebraic space, so this is a
repackaging; it is stated so that the implications recorded for Tag 03KG reach condition (5)
in the shape the source gives it. -/
@[stacks 03KG "part (4) implies part (5)"]
theorem exists_isAlgebraicSpace_surjectiveEtale_isQuasiCompact_pullback_snd
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (V : BigFppfOver B S hS) (φ : yoneda.obj V ⟶ Y)
    (hsurj : IsSurjective B S hS φ) (hφ : IsEtale B S hS φ)
    (h : IsQuasiCompact B S hS (pullback.snd f φ)) :
    ∃ (Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hY' : IsAlgebraicSpace B S hS Y')
      (g : Y' ⟶ Y), IsSurjective B S hS g ∧ IsEtale B S hS g ∧
        IsQuasiCompact B S hS (pullback.snd f g) :=
  ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V, φ, hsurj, hφ, h⟩

/-- **Stacks 03KG, part (5) implies part (4): an algebraic-space chart may be replaced by a
scheme chart.** If `g : Y' ⟶ Y` is a surjective étale morphism of algebraic spaces over `S`
along which the base change of `f : X ⟶ Y` is quasi-compact, then the same holds for a chart
of `Y` by an object of the site.

Compose `g` with a scheme atlas `a : h_V ⟶ Y'` of `Y'`. The composite is surjective on points
because `AlgebraicGeometry.Space.pointsMap` is functorial, étale because
`AlgebraicGeometry.Space.IsEtale g` tests exactly the étale charts of `Y'`, and the base change
of `f` along it is a base change of the base change along `g`, hence quasi-compact by
Stacks 03HF. Note that `Y` itself need not be assumed an algebraic space. -/
@[stacks 03KG "part (5) implies part (4)"]
theorem exists_surjectiveEtale_atlas_of_isAlgebraicSpace_surjectiveEtale
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    {Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY' : IsAlgebraicSpace B S hS Y')
    (g : Y' ⟶ Y) (hsurj : IsSurjective B S hS g) (hg : IsEtale B S hS g)
    (h : IsQuasiCompact B S hS (pullback.snd f g)) :
    ∃ (V : BigFppfOver B S hS) (φ : yoneda.obj V ⟶ Y),
      IsSurjective B S hS φ ∧ IsEtale B S hS φ ∧
      IsQuasiCompact B S hS (pullback.snd f φ) := by
  obtain ⟨V, a, haS, haE⟩ := hY'.exists_atlas
  have hcomp : IsSurjective B S hS (a ≫ g) := by
    rw [IsSurjective, pointsMap_comp]
    exact hsurj.comp (isSurjective_of_presheafSurjective B S hS a haS)
  refine ⟨V, a ≫ g, hcomp, isEtale_of_presheaf_etale B S hS (hg V a haE), ?_⟩
  exact isQuasiCompact_of_isPullback B S hS
    (IsPullback.of_right' (IsPullback.of_hasPullback f (a ≫ g))
      (IsPullback.of_hasPullback f g)) h

end Space

end AlgebraicGeometry

end
