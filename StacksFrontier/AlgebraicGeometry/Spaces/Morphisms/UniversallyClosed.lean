module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.UniversallyInjectiveUnramified.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Size.UniversallyClosedCutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineTranslation
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.PointsRelocalized
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibers
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDiagonalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.SelfProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints

/-!
# Local criteria for universal closedness of a morphism of algebraic spaces

Universal closedness of a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`,
Stacks 03HI, quantifies over all base changes of `f` by algebraic spaces over `S`. This file
proves that four weaker-looking conditions detect it: closedness of the base changes along
morphisms out of *schemes*, closedness of the base changes along morphisms out of *affine*
schemes, universal closedness of the base change along a single surjective étale morphism from
a scheme, and universal closedness of the base changes along the members of a Zariski covering
of the target. It then deduces two consequences: the four separation properties of Stacks 05Z2
descend along a surjective universally closed morphism, and the structure morphism of the
quotient of the affine line by the integer translations is universally closed over a field of
characteristic zero. The source calls the second one a strange example, since that quotient is,
by Stacks 02Z7, an algebraic space which is not a scheme.

## Main results

* `AlgebraicGeometry.Space.universallyClosed_tfae`: **Stacks 03IT**, the five equivalent
  conditions.
* `AlgebraicGeometry.Space.isQuasiCompact_of_universallyClosed`: **Stacks 04XW**, a universally
  closed morphism is quasi-compact, with
  `AlgebraicGeometry.Space.compactSpace_points_of_universallyClosed` its absolute form over a
  quasi-compact target.
* `AlgebraicGeometry.Space.isQuasiSeparated_of_isSurjective_of_universallyClosed` and
  `AlgebraicGeometry.Space.isSeparated_of_isSurjective_of_universallyClosed`: **Stacks 05Z2**,
  parts (3) and (4), with
  `AlgebraicGeometry.Space.isQuasiSeparatedOver_of_isSurjective_of_universallyClosed` and
  `AlgebraicGeometry.Space.isSeparatedOver_of_isSurjective_of_universallyClosed` their cases
  over the base scheme.
* `AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isSurjective_of_universallyClosed` and
  `AlgebraicGeometry.Space.isAbsolutelySeparated_of_isSurjective_of_universallyClosed`:
  **Stacks 05Z2**, parts (1) and (2), the same two statements for the absolute separation
  axioms of Stacks 03BS.
* `AlgebraicGeometry.Space.isSurjective_relocalize`,
  `AlgebraicGeometry.Space.isClosedMorphism_relocalize` and
  `AlgebraicGeometry.Space.universallyClosed_relocalize`: surjectivity, closedness and universal
  closedness survive the change of base scheme of Stacks 03I5, part (2).
* `AlgebraicGeometry.AffineLineTranslation.universallyClosed_structureMap`: **Stacks 03IV**,
  the strange example `𝔸¹_k/ℤ ⟶ Spec k`, whose structure morphism is
  `AlgebraicGeometry.AffineLineTranslation.structureMap`.

Each nontrivial implication of the list is also stated on its own, since all four are useful
without the list:

* `AlgebraicGeometry.Space.universallyClosed_of_isClosedMorphism_yoneda`: the scheme test.
* `AlgebraicGeometry.Space.isClosedMorphism_pullback_fst_of_affine`: the affine test.
* `AlgebraicGeometry.Space.universallyClosed_of_etale_atlas`: the étale-atlas test.
* `AlgebraicGeometry.Space.universallyClosed_of_isZariskiCover`: the Zariski-local test.

## Implementation notes

Everything rests on one statement of point-set topology,
`AlgebraicGeometry.Space.isClosedMap_of_isOpenMap_family_cartesian`: a map `q : A → C` is closed
as soon as it is covered by a family of commuting squares whose right-hand edges `v i : V i → C`
are open maps jointly covering `C`, whose squares are cartesian on underlying sets, and whose
bottom edges `r i : D i → V i` are closed. The complement of `q '' s` is then the union of the
images under the `v i` of the complements of the images of the preimages of `s`, each of which
is open. Its one-member case,
`AlgebraicGeometry.Space.isClosedMap_of_isOpenMap_surjective_cartesian`, is the descent of
closedness along an open surjection. Both live in
`StacksFrontier/AlgebraicGeometry/Spaces/UniversallyClosedRepresentable.lean`, the lowest module
that needs them.

The three inputs of that lemma are supplied, in each of the four implications, by the same
three results about the point topology of Stacks 03BX: the map on points is continuous, the map
on points of an étale morphism is open (Stacks 03IR, or Stacks 03BX clause (3) for a chart),
and a cartesian square of presheaves is cartesian on points (Stacks 03H4, in the form
`AlgebraicGeometry.Space.exists_points_of_isPullback`, which needs no algebraicity at all).
Surjectivity on points of a chart is Stacks 03H5.

What varies is the covering family.

*The scheme test.* The family has one member, a surjective étale atlas of the test space `Z`
supplied by `AlgebraicGeometry.IsAlgebraicSpace.exists_atlas`. Its base change is the base
change of `f` along the composite `h_U ⟶ Z ⟶ Y`, so the hypothesis applies to it through
`AlgebraicGeometry.Space.isClosedMap_pointsMap_pullback_fst_pullback_fst`.

*The affine test.* The family is indexed by the affine opens of the scheme representing the
test object, each giving an object of the site by
`AlgebraicGeometry.Space.openSiteObject`; they cover the points of the represented presheaf
because they cover the points of the scheme and the points of a represented presheaf are the
points of the scheme, which is
`AlgebraicGeometry.Space.exists_pointsMap_yonedaMap_eq_of_mem_range`.

*The étale-atlas and Zariski tests.* The family is the base change of the given atlas,
respectively the base changes of the members of the covering, along the test morphism; both are
again étale, hence open on points, because étaleness and open immersions are stable under base
change relative to Yoneda. The closedness of the bottom edge comes from the hypothesis at the
base-changed test object, transported by `isClosedMorphism_pullback_fst_of_comm`, which
compares the two ways of forming `D ×_Z (Z ×_Y X)` from a commuting square `D ⟶ Z ⟶ Y`,
`D ⟶ V ⟶ Y`.

Universal closedness is a property of a morphism of presheaves, so neither the statement of
the conditions nor the proofs of the implications need the source `X` to be an algebraic space;
the hypothesis `_hX` of the list is retained from the source statement and is not used.
Algebraicity of the target is used, in the two implications producing a covering of `Y`.

Stacks 04XW goes the other way round: it is the affine criterion of the list — in the form of
Stacks 03KG for quasi-compactness — fed by one absolute statement, that a universally closed
morphism onto an algebraic space with quasi-compact point space has quasi-compact point space.
That statement is proved by showing the map on points to be a proper map, so that the preimage of
the quasi-compact target is quasi-compact. Closedness is universal closedness at the identity;
compactness of the fibre over a point is compactness of the point space of the base change along
a field-valued representative of that point, and *that* is the content of the tag. Over a field
the argument is the one of `AlgebraicGeometry.compactSpace_of_universallyClosed` for schemes, run
on points and recorded here as `compactSpace_of_isClosedMap_specMvPolynomial`: the point space is
covered by the quasi-compact open images of the affine opens of a chart, and affine space over
the base on that index set — an object of the site by
`AlgebraicGeometry.affineCoverPolynomial_size_lt` — is a test object whose closedness forces
finitely many of those images to suffice. The fibre product with it is cartesian on points by
Stacks 03H4, which over a one-point base is joint surjectivity; that is the only property of it
the point-set argument uses, which is why that argument is stated for an abstract space mapping
to the two factors.

Parts (3) and (4) of Stacks 05Z2 are proved from the relative diagonal, not from the list: the
diagonal of `Y ⟶ T` is universally closed because the induced map `X ×_T X ⟶ Y ×_T Y` of
`AlgebraicGeometry.Space.selfProductMap` is, and because `X ⟶ X ×_T X ⟶ Y ×_T Y` is
`X ⟶ Y ⟶ Y ×_T Y`, so that Stacks 08AJ descends universal closedness along the surjection
`X ⟶ Y`. Each represented base change of that diagonal is then a universally closed
monomorphism of schemes, locally of finite type by Stacks 03HK, hence a closed immersion by the
characterisation of Stacks 04XV. Part (3) runs the same argument with the closed-immersion
property of the diagonal replaced by quasi-compactness of it, the map on relative self-products
being quasi-compact by `AlgebraicGeometry.Space.isQuasiCompact_of_universallyClosed` below and
quasi-compactness descending along the surjection by Stacks 040W, part (2).

Parts (1) and (2) are the absolute axioms of Stacks 03BS, which live over the terminal scheme:
the absolute axiom for `F` is the axiom over `Spec ℤ` for the lower-shriek extension of `F`
along `S ⟶ Spec ℤ`, so they are parts (3) and (4) applied to that extension of `X ⟶ Y`, exactly
as the source says. What this needs is that the extension of a surjective universally closed
morphism is again one, and that is the content of
`AlgebraicGeometry.Space.isSurjective_relocalize` and
`AlgebraicGeometry.Space.universallyClosed_relocalize`. Both rest on the transport of points
`AlgebraicGeometry.Space.relocalizedPointsMap`, which is bijective and — by uniqueness of the
family of Stacks 03BX, the transported family being
`AlgebraicGeometry.Space.relocalizedPointTopologyFamily` — induces the point topology; so the
map on points of the extension is conjugate to the map on points of the morphism, and is
surjective, respectively closed, exactly when that one is. Universal closedness is then tested
on represented base changes through `AlgebraicGeometry.Space.universallyClosed_tfae`'s scheme
criterion, every represented morphism into an extension being, by
`AlgebraicGeometry.Space.exists_relocalized_yoneda_factorization`, the extension of a
represented morphism up to isomorphism.

*The strange example.* The quotient `X = 𝔸¹_k/ℤ` of Stacks 02Z7 is
`AlgebraicGeometry.AffineLineTranslation.translationQuotient` and its chart is the quotient
chart `Stacks.Groupoids.quotientChart` of the graph relation of the translation action. The
structure morphism is the unique morphism to the terminal object `Spec k` of the site, so a
test morphism `g : Z ⟶ Spec k` from an algebraic space admits the zero section of the affine
line as a section `Z ⟶ Z ×_{Spec k} X`. Closedness of the first projection is then the
statement that every closed subset of `|Z ×_{Spec k} X|` is stable under replacing a point by
its image under that section, which is where characteristic zero enters: a point of the fibre
product over a field `K` lifts along the chart, the resulting `K`-point of the affine line can
be translated by every integer inside one `K[x]`-valued point, and a closed subset of
`𝔸¹_K` containing the infinitely many translates of a rational point is all of `𝔸¹_K` by
`Polynomial.eq_zero_of_infinite_isRoot`. Surjectivity on points of the
chart, which is what lets the point be lifted, is local surjectivity of
`Stacks.Groupoids.quotientChart` — unconditional, in particular free of the effective-descent
hypothesis of Stacks 0265 — read through
`AlgebraicGeometry.Space.points_cover_of_isLocallySurjective_sigma_desc`. Neither the
statement nor the proof needs `X` to be an algebraic space, because
`AlgebraicGeometry.Space.pointTopology` is defined for an arbitrary presheaf.

## References

* [Stacks Project, Tag 03IT](https://stacks.math.columbia.edu/tag/03IT)
* [Stacks Project, Tag 03HI](https://stacks.math.columbia.edu/tag/03HI)
* [Stacks Project, Tag 05Z2](https://stacks.math.columbia.edu/tag/05Z2)
* [Stacks Project, Tag 03IV](https://stacks.math.columbia.edu/tag/03IV)
* [Stacks Project, Tag 04XW](https://stacks.math.columbia.edu/tag/04XW)
* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `HasPullbacks` in this presheaf category exceeds the default budget
/-- Pullbacks of presheaves on `BigFppfOver B S hS`, stated once: instance search for them
times out at the default heartbeat limit under Mathlib v4.35.0. -/
local instance hasPullbacks_presheaf_universallyClosed :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  inferInstance

/-- Every cospan of presheaves on `BigFppfOver B S hS` has a limit, found directly from
`hasPullbacks_presheaf_universallyClosed` ahead of the slower general search. -/
local instance (priority := high) hasPullback_presheaf_universallyClosed
    {P Q R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : P ⟶ R) (b : Q ⟶ R) :
    HasLimit (cospan a b) :=
  HasLimitsOfShape.has_limit (cospan a b)

/-! ### Transport of closedness along a commuting square over the target -/

/-- Let `f : X ⟶ Y` and let `D ⟶ Z ⟶ Y` and `D ⟶ V ⟶ Y` be two factorisations of one morphism
`D ⟶ Y`. If the base change along `D ⟶ V` of the base change of `f` along `V ⟶ Y` is closed,
then so is the base change along `D ⟶ Z` of the base change of `f` along `Z ⟶ Y`: both are
`D ×_Y X`, compared by the two pasting isomorphisms for `D ⟶ V ⟶ Y` and `D ⟶ Z ⟶ Y` together
with the identification of the two composites. -/
theorem isClosedMorphism_pullback_fst_of_comm
    {Z V D : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (g : Z ⟶ Y) (φ : V ⟶ Y)
    (e : D ⟶ Z) (s : D ⟶ V) (hcomm : e ≫ g = s ≫ φ)
    (h : IsClosedMorphism B S hS (pullback.fst s (pullback.fst φ f))) :
    IsClosedMorphism B S hS (pullback.fst e (pullback.fst g f)) := by
  have hR : IsPullback (pullback.snd s (pullback.fst φ f) ≫ pullback.snd φ f)
      (pullback.fst s (pullback.fst φ f)) f (s ≫ φ) :=
    (IsPullback.of_hasPullback s (pullback.fst φ f)).flip.paste_horiz
      (IsPullback.of_hasPullback φ f).flip
  have hQ : IsPullback (pullback.snd e (pullback.fst g f) ≫ pullback.snd g f)
      (pullback.fst e (pullback.fst g f)) f (s ≫ φ) := by
    rw [← hcomm]
    exact (IsPullback.of_hasPullback e (pullback.fst g f)).flip.paste_horiz
      (IsPullback.of_hasPullback g f).flip
  exact isClosedMap_pointsMap_of_comp_isIso B S hS (hR.isoIsPullback _ _ hQ).inv
    (hR.isoIsPullback_inv_snd _ _ hQ) h

/-- The base change `Z ×_Y X ⟶ Z` of `f : X ⟶ Y` along `g : Z ⟶ Y` is closed as soon as `Z` is
covered on points by the images of open maps on points `a i : D i ⟶ Z` whose base changes of
`Z ×_Y X ⟶ Z` are closed. -/
private theorem isClosedMorphism_pullback_fst_of_isOpenMap_cover
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {I : Type*} {D : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (g : Z ⟶ Y)
    (a : ∀ i, D i ⟶ Z) (ha : ∀ i, IsOpenMap (pointsMap B S hS (D i) (a i)))
    (hcover : ∀ z, ∃ i w, pointsMap B S hS (D i) (a i) w = z)
    (hr : ∀ i, IsClosedMap (pointsMap B S hS (pullback (a i) (pullback.fst g f))
      (pullback.fst (a i) (pullback.fst g f)))) :
    IsClosedMorphism B S hS (pullback.fst g f) :=
  isClosedMap_of_isOpenMap_family_cartesian
    (pointsMap B S hS (pullback g f) (pullback.fst g f))
    (fun i ↦ pointsMap B S hS (pullback (a i) (pullback.fst g f))
      (pullback.snd (a i) (pullback.fst g f)))
    (fun i ↦ pointsMap B S hS (pullback (a i) (pullback.fst g f))
      (pullback.fst (a i) (pullback.fst g f)))
    (fun i ↦ pointsMap B S hS (D i) (a i))
    (fun _ d ↦ pointsMap_apply_comm B S hS pullback.condition.symm d)
    (fun i c w hcw ↦ exists_points_of_isPullback B S hS
      (IsPullback.of_hasPullback (a i) (pullback.fst g f)).flip c w hcw)
    (fun _ ↦ continuous_pointsMap B S hS _) ha hcover hr

/-! ### The scheme test -/

/-- **Stacks 03IT, (2) implies (1).** If the base change of `f : X ⟶ Y` along every morphism to
`Y` from a presheaf represented by an object of the site is closed, then `f` is universally
closed. -/
theorem universallyClosed_of_isClosedMorphism_yoneda (f : X ⟶ Y)
    (h : ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
      IsClosedMorphism B S hS (pullback.fst g f)) :
    UniversallyClosed B S hS f := by
  intro Z hZ g
  obtain ⟨U, a, hasurj, haetale⟩ := hZ.exists_atlas
  refine isClosedMorphism_pullback_fst_of_isOpenMap_cover B S hS f g (I := PUnit.{1})
    (fun _ ↦ a) (fun _ ↦ isOpenMap_pointsMap_of_etale B S hS hZ U a haetale)
    (fun z ↦ ?_) (fun _ ↦ isClosedMap_pointsMap_pullback_fst_pullback_fst B S hS f g a
      (h U (a ≫ g)))
  obtain ⟨w, hw⟩ := (surjective_iff_surjective_pointsMap B S hS Z hZ U a).mp hasurj z
  exact ⟨⟨⟩, w, hw⟩

/-! ### The affine test -/

/-- Every point of the presheaf represented by an object `T` of the big fppf site of `S` comes
from an affine open subscheme of the scheme representing `T`. -/
theorem exists_affineOpen_pointsMap_yonedaMap_eq (T : BigFppfOver B S hS)
    (z : points B S hS (yoneda.obj T)) :
    ∃ W : ((BigFppfOver.toScheme B S hS).obj T).affineOpens,
      ∃ w, pointsMap B S hS (yoneda.obj (openSiteObject B S hS T W.1))
        (yoneda.map (openSiteObjectHom B S hS T W.1)) w = z := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hzW, -⟩ :=
    ((BigFppfOver.toScheme B S hS).obj T).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (pointsToScheme B S hS T z)) isOpen_univ
  refine ⟨⟨W, hW⟩, exists_pointsMap_yonedaMap_eq_of_mem_range B S hS
    (openSiteObjectHom B S hS T W) z ?_⟩
  rw [map_openSiteObjectHom]
  exact ⟨⟨_, hzW⟩, rfl⟩

/-- An affine open subscheme of the scheme representing an object `T` of the big fppf site of
`S` gives an étale chart of the presheaf represented by `T`: the canonical morphism of the site
has the open inclusion as its underlying morphism of schemes. -/
theorem presheaf_etale_yonedaMap_openSiteObjectHom (T : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj T).Opens) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
      (yoneda.map (openSiteObjectHom B S hS T W)) := by
  have hmul := isMultiplicative_presheaf_etale B S hS
  have hopen : AlgebraicGeometry.Etale
      ((BigFppfOver.toScheme B S hS).map (openSiteObjectHom B S hS T W)) := by
    rw [map_openSiteObjectHom]
    exact (inferInstance : AlgebraicGeometry.Etale W.ι)
  have h := etale_comp_of_scheme B S hS (openSiteObjectHom B S hS T W) (𝟙 (yoneda.obj T))
    hopen (MorphismProperty.id_mem _ _)
  rwa [Category.comp_id] at h

/-- **Stacks 03IT, (3) implies (2).** If the base change of `f : X ⟶ Y` along every morphism to
`Y` from a presheaf represented by an object of the site with *affine* underlying scheme is
closed, then the same holds for every object of the site. -/
theorem isClosedMorphism_pullback_fst_of_affine (f : X ⟶ Y)
    (h : ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
      IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
        IsClosedMorphism B S hS (pullback.fst g f))
    (T : BigFppfOver B S hS) (φ : yoneda.obj T ⟶ Y) :
    IsClosedMorphism B S hS (pullback.fst φ f) := by
  refine isClosedMorphism_pullback_fst_of_isOpenMap_cover B S hS f φ
    (fun W : ((BigFppfOver.toScheme B S hS).obj T).affineOpens ↦
      yoneda.map (openSiteObjectHom B S hS T W.1))
    (fun W ↦ isOpenMap_pointsMap_of_etale B S hS (isAlgebraicSpace_yoneda B S hS T)
      (openSiteObject B S hS T W.1) (yoneda.map (openSiteObjectHom B S hS T W.1))
      (presheaf_etale_yonedaMap_openSiteObjectHom B S hS T W.1))
    (fun z ↦ exists_affineOpen_pointsMap_yonedaMap_eq B S hS T z)
    (fun W ↦ isClosedMap_pointsMap_pullback_fst_pullback_fst B S hS f φ
      (yoneda.map (openSiteObjectHom B S hS T W.1))
      (h (openSiteObject B S hS T W.1)
        (yoneda.map (openSiteObjectHom B S hS T W.1) ≫ φ) W.2))

/-! ### The étale-atlas test -/

/-- **Stacks 03IT, (4) implies (1).** If the base change of `f : X ⟶ Y` along one surjective
étale morphism `φ : V ⟶ Y` is universally closed, then `f` is universally closed. -/
theorem universallyClosed_of_etale_atlas (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (V : BigFppfOver B S hS) (φ : yoneda.obj V ⟶ Y)
    (hφsurj : IsSurjective B S hS φ) (hφetale : IsEtale B S hS φ)
    (h : UniversallyClosed B S hS (pullback.fst φ f)) :
    UniversallyClosed B S hS f := by
  have hbc : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  intro Z hZ g
  have hD : IsAlgebraicSpace B S hS (pullback g φ) :=
    isAlgebraicSpace_pullback B S hS g φ hZ (isAlgebraicSpace_yoneda B S hS V) hY
  have hesurj : Function.Surjective (pointsMap B S hS (pullback g φ) (pullback.fst g φ)) := by
    intro z
    obtain ⟨v, hv⟩ := hφsurj (pointsMap B S hS Z g z)
    obtain ⟨d, hd, -⟩ := exists_points_of_isPullback B S hS
      (IsPullback.of_hasPullback g φ) z v hv.symm
    exact ⟨d, hd⟩
  have heetale : IsEtale B S hS (pullback.fst g φ) :=
    isEtale_of_presheaf_etale B S hS (hbc.of_isPullback
      (IsPullback.of_hasPullback g φ).flip (presheaf_etale_of_isEtale B S hS hφetale))
  exact isClosedMorphism_pullback_fst_of_isOpenMap_cover B S hS f g (I := PUnit.{1})
    (fun _ ↦ pullback.fst g φ)
    (fun _ ↦ isOpenMap_pointsMap_of_isEtale B S hS (pullback.fst g φ) hD hZ heetale)
    (fun z ↦ ⟨⟨⟩, hesurj z⟩)
    (fun _ ↦ isClosedMorphism_pullback_fst_of_comm B S hS f g φ (pullback.fst g φ)
      (pullback.snd g φ) pullback.condition
      (h (pullback g φ) hD (pullback.snd g φ)))

/-! ### The Zariski-local test -/

/-- **Stacks 03IT, (5) implies (1).** If the base change of `f : X ⟶ Y` along each member of a
Zariski covering of `Y` is universally closed, then `f` is universally closed. -/
theorem universallyClosed_of_isZariskiCover (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    {I : Type u} (U : I → Subfunctor Y) (hU : IsZariskiCover B S hS I U)
    (h : ∀ i, UniversallyClosed B S hS (pullback.fst (U i).ι f)) :
    UniversallyClosed B S hS f := by
  have hbc : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hcoverY := (isZariskiCover_iff_iUnion_points B S hS Y hY I U hU.1).mp hU
  intro Z hZ g
  have hZi (i : I) : IsAlgebraicSpace B S hS (pullback g (U i).ι) :=
    isAlgebraicSpace_pullback B S hS g (U i).ι hZ (hU.1 i).1 hY
  have hietale (i : I) : IsEtale B S hS (pullback.fst g (U i).ι) :=
    isEtale_of_presheaf_etale B S hS (presheaf_etale_of_isOpenImmersion B S hS
      (hbc.of_isPullback (IsPullback.of_hasPullback g (U i).ι).flip (hU.1 i).2))
  refine isClosedMorphism_pullback_fst_of_isOpenMap_cover B S hS f g
    (fun i ↦ pullback.fst g (U i).ι)
    (fun i ↦ isOpenMap_pointsMap_of_isEtale B S hS (pullback.fst g (U i).ι) (hZi i) hZ
      (hietale i))
    (fun z ↦ ?_)
    (fun i ↦ isClosedMorphism_pullback_fst_of_comm B S hS f g (U i).ι
      (pullback.fst g (U i).ι) (pullback.snd g (U i).ι) pullback.condition
      (h i (pullback g (U i).ι) (hZi i) (pullback.snd g (U i).ι)))
  obtain ⟨i, y, hy⟩ := Set.mem_iUnion.1 (hcoverY ▸ Set.mem_univ (pointsMap B S hS Z g z))
  obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B S hS
    (IsPullback.of_hasPullback g (U i).ι) z y hy.symm
  exact ⟨i, w, hw⟩

/-! ### Stacks 03IT -/

/-- **Stacks 03IT.** For a morphism `f : X ⟶ Y` of algebraic spaces over `S` the following are
equivalent: `f` is universally closed; the base change of `f` along every morphism to `Y` from
a presheaf represented by an object of the site is closed; the same for the objects with affine
underlying scheme; the base change of `f` along some surjective étale morphism to `Y` from a
represented presheaf is universally closed; and there is a Zariski covering of `Y` along each
member of which the base change of `f` is universally closed.

Algebraicity of the source is retained from the source statement and is not used. -/
@[stacks 03IT]
theorem universallyClosed_tfae (_hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    List.TFAE
      [UniversallyClosed B S hS f,
        ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
          IsClosedMorphism B S hS (pullback.fst g f),
        ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
          IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
            IsClosedMorphism B S hS (pullback.fst g f),
        ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
          IsSurjective B S hS g ∧ IsEtale B S hS g ∧
            UniversallyClosed B S hS (pullback.fst g f),
        ∃ (I : Type u) (U : I → Subfunctor Y) (_ : IsZariskiCover B S hS I U),
          ∀ i, UniversallyClosed B S hS (pullback.fst (U i).ι f)] := by
  classical
  tfae_have 1 → 2 := fun h Z g ↦ h (yoneda.obj Z) (isAlgebraicSpace_yoneda B S hS Z) g
  tfae_have 2 → 3 := fun h Z g _ ↦ h Z g
  tfae_have 3 → 1 := fun h ↦ universallyClosed_of_isClosedMorphism_yoneda B S hS f
    (isClosedMorphism_pullback_fst_of_affine B S hS f h)
  tfae_have 1 → 4 := fun h ↦ by
    obtain ⟨U, a, hasurj, haetale⟩ := hY.exists_atlas
    exact ⟨U, a, (surjective_iff_surjective_pointsMap B S hS Y hY U a).mp hasurj,
      isEtale_of_presheaf_etale B S hS haetale,
      universallyClosed_pullback B S hS f a h⟩
  tfae_have 4 → 1 := fun h ↦ by
    obtain ⟨V, a, hasurj, haetale, hbase⟩ := h
    exact universallyClosed_of_etale_atlas B S hS hY f V a hasurj haetale hbase
  tfae_have 1 → 5 := fun h ↦ by
    refine ⟨PUnit.{u + 1}, fun _ ↦ ((openSubspacesOrderIso B S hS Y hY).symm ⊤).1, ?_,
      fun _ ↦ universallyClosed_pullback B S hS f _ h⟩
    refine (isZariskiCover_iff_iUnion_points B S hS Y hY PUnit.{u + 1} _
      (fun _ ↦ ((openSubspacesOrderIso B S hS Y hY).symm ⊤).2)).2 ?_
    have hrange : Set.range (pointsMap B S hS
        ((openSubspacesOrderIso B S hS Y hY).symm ⊤).1.toFunctor
        ((openSubspacesOrderIso B S hS Y hY).symm ⊤).1.ι) = Set.univ := by
      rw [← openSubspacesOrderIso_apply B S hS Y hY ((openSubspacesOrderIso B S hS Y hY).symm ⊤)]
      simp
    simpa [hrange] using Set.iUnion_const (ι := PUnit.{u + 1}) (Set.univ : Set (points B S hS Y))
  tfae_have 5 → 1 := fun h ↦ by
    obtain ⟨I, U, hU, hlocal⟩ := h
    exact universallyClosed_of_isZariskiCover B S hS hY f U hU hlocal
  tfae_finish

/-! ### Quasi-compactness of a universally closed morphism -/

section QuasiCompact

open MvPolynomial

/-- **The point-set heart of Stacks 04XW.** Let `P` be a topological space covered by
quasi-compact open subsets `C i` indexed by a type `ι`, let `T = Spec K[a_i; i ∈ ι]` be affine
space on that index set over a field `K`, and let `Q` be a space mapping to both `P` and `T` so
that every pair of points of `P` and of `T` is hit. If the map `Q → T` is closed, then `P` is
quasi-compact.

This is the argument of `AlgebraicGeometry.compactSpace_of_universallyClosed`, where `P` is a
scheme over `Spec K` and `Q` is its fibre product with `T`, with that fibre product replaced by
the abstract hypothesis on `Q`. -/
private theorem compactSpace_of_isClosedMap_specMvPolynomial {K : Type u} [Field K]
    {ι : Type u} {P Q : Type*} [TopologicalSpace P] [TopologicalSpace Q] (π : Q → P)
    (τ : Q → ↥(Spec (CommRingCat.of (MvPolynomial ι K)))) (hπ : Continuous π)
    (hτ : Continuous τ) (hclosed : IsClosedMap τ)
    (hsurj : ∀ (x : P) (t : ↥(Spec (CommRingCat.of (MvPolynomial ι K)))),
      ∃ w, π w = x ∧ τ w = t)
    (C : ι → Set P) (hCopen : ∀ i, IsOpen (C i)) (hCcompact : ∀ i, IsCompact (C i))
    (hCcover : ∀ x, ∃ i, x ∈ C i) :
    CompactSpace P := by
  classical
  let T : Scheme := Spec (CommRingCat.of (MvPolynomial ι K))
  let Ti (i : ι) : T.Opens := PrimeSpectrum.basicOpen (MvPolynomial.X i)
  let W : Set Q := (⋃ i, τ ⁻¹' (Ti i) ∩ π ⁻¹' C i)ᶜ
  have hWclosed : IsClosed W := by
    rw [isClosed_compl_iff]
    exact isOpen_iUnion fun i ↦ ((Ti i).2.preimage hτ).inter ((hCopen i).preimage hπ)
  let Wc : T.Opens := ⟨(τ '' W)ᶜ, (hclosed _ hWclosed).isOpen_compl⟩
  let ψ : MvPolynomial ι K →ₐ[K] K := MvPolynomial.aeval fun _ ↦ 1
  let t : T := Spec.map (CommRingCat.ofHom ψ.toRingHom) default
  have ht (i : ι) : t ∈ Ti i := show ψ (.X i) ≠ 0 by simp [ψ]
  have htWc : t ∈ Wc := by
    rintro ⟨w, hw, hwt⟩
    obtain ⟨i, hi⟩ := hCcover (π w)
    exact hw (Set.mem_iUnion.2 ⟨i, by rw [Set.mem_preimage, hwt]; exact ht i, hi⟩)
  obtain ⟨-, ⟨g, rfl⟩, htg, hgle⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp PrimeSpectrum.isBasis_basic_opens htWc
  let σ : Finset ι := MvPolynomial.vars g
  let φ : MvPolynomial ι K →+* MvPolynomial ι K :=
    (MvPolynomial.aeval fun i : ι ↦ if i ∈ σ then MvPolynomial.X i else 0).toRingHom
  let t' : T := Spec.map (CommRingCat.ofHom φ) t
  have ht'g : t' ∈ PrimeSpectrum.basicOpen g :=
    show φ g ∉ t.asIdeal from (show φ g = g from aeval_ite_mem_eq_self g subset_rfl).symm ▸ htg
  have h : t' ∉ τ '' W := hgle ht'g
  suffices hcov : ⋃ i ∈ σ, C i = Set.univ from
    ⟨hcov ▸ Finset.isCompact_biUnion _ fun i _ ↦ hCcompact i⟩
  rw [Set.iUnion₂_eq_univ_iff]
  contrapose! h
  obtain ⟨x, hx⟩ := h
  obtain ⟨w, hw₁, hw₂⟩ := hsurj x t'
  refine ⟨w, fun hw ↦ ?_, hw₂⟩
  obtain ⟨i, hi₁, hi₂⟩ := Set.mem_iUnion.1 hw
  rw [Set.mem_preimage, hw₂] at hi₁
  rw [Set.mem_preimage, hw₁] at hi₂
  by_cases hiσ : i ∈ σ
  · exact hx i hiσ hi₂
  · refine (show φ (MvPolynomial.X i) ∉ t.asIdeal from hi₁) ?_
    rw [show φ (MvPolynomial.X i) = 0 by simp [φ, hiσ]]
    exact t.asIdeal.zero_mem

/-- The point space of an algebraic space over `S` is covered by quasi-compact open subsets
indexed by the affine opens of a scheme inside the site. -/
private theorem exists_isOpen_isCompact_cover_points
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F) :
    ∃ (X : Scheme.{u}) (_ : B.Contains X)
      (C : X.directedAffineCover.I₀ → Set (points B S hS F)),
      (∀ i, IsOpen (C i)) ∧ (∀ i, IsCompact (C i)) ∧ ∀ x, ∃ i, x ∈ C i := by
  classical
  obtain ⟨U, a, hasurj, haetale⟩ := hF.exists_atlas
  set G := BigFppfOver.toScheme B S hS
  set 𝒰 := (G.obj U).directedAffineCover
  have hXi (i : 𝒰.I₀) : B.Contains (𝒰.X i) :=
    Scheme.size_lt_of_isOpenImmersion (𝒰.f i) U.left.property
  set chartArrow : ∀ i : 𝒰.I₀, B.obj (hXi i) ⟶ U.left := fun i ↦
    B.inclusion.preimage
      (show B.inclusion.obj (B.obj (hXi i)) ⟶ B.inclusion.obj U.left from 𝒰.f i)
  set Ui : 𝒰.I₀ → BigFppfOver B S hS := fun i ↦ Over.mk (chartArrow i ≫ U.hom)
  set ui : ∀ i, Ui i ⟶ U := fun i ↦ Over.homMk (chartArrow i)
  have hmapui (i : 𝒰.I₀) : G.map (ui i) = 𝒰.f i := B.inclusion.map_preimage _
  have hetale (i : 𝒰.I₀) : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) G).presheaf
      (yoneda.map (ui i) ≫ a) :=
    etale_comp_of_scheme B S hS (ui i) a (by rw [hmapui]; infer_instance) haetale
  refine ⟨G.obj U, U.left.property,
    fun i ↦ Set.range (pointsMap B S hS (yoneda.obj (Ui i)) (yoneda.map (ui i) ≫ a)),
    fun i ↦ ?_, fun i ↦ ?_, fun x ↦ ?_⟩
  · change IsOpen (Set.range (pointsMap B S hS (yoneda.obj (Ui i)) (yoneda.map (ui i) ≫ a)))
    rw [← Set.image_univ]
    exact isOpenMap_pointsMap_of_etale B S hS hF (Ui i) _ (hetale i) _ isOpen_univ
  · change IsCompact (Set.range (pointsMap B S hS (yoneda.obj (Ui i)) (yoneda.map (ui i) ≫ a)))
    have : IsAffine (G.obj (Ui i)) := i.2
    have : CompactSpace (G.obj (Ui i)) := Scheme.compactSpace_of_isAffine _
    have : CompactSpace (points B S hS (yoneda.obj (Ui i))) :=
      compactSpace_points_yoneda B S hS (Ui i)
    exact isCompact_range (continuous_pointsMap B S hS _)
  · change ∃ i, x ∈ Set.range (pointsMap B S hS (yoneda.obj (Ui i)) (yoneda.map (ui i) ≫ a))
    obtain ⟨y, hy⟩ := (surjective_iff_surjective_pointsMap B S hS F hF U a).mp hasurj x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
      (𝒰.iUnion_range ▸ Set.mem_univ (pointsToScheme B S hS U y))
    obtain ⟨z, hz⟩ := exists_pointsMap_yonedaMap_eq_of_mem_range B S hS (ui i) y
      (by rw [hmapui]; exact hi)
    exact ⟨i, z, by rw [pointsMap_comp_apply, hz, hy]⟩

/-- **The key case of Stacks 04XW.** An algebraic space over `S` which is universally closed
over the spectrum of a field of the site has quasi-compact point space. -/
private theorem compactSpace_points_of_universallyClosed_specField {K : Type u} [Field K]
    (hK : B.Contains (Spec (.of K))) (b : Spec (.of K) ⟶ S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (f : F ⟶ yoneda.obj (Over.mk (⟨b⟩ : B.obj hK ⟶ B.obj hS) : BigFppfOver B S hS))
    (hf : UniversallyClosed B S hS f) :
    CompactSpace (points B S hS F) := by
  classical
  have hsubScheme : Subsingleton ((BigFppfOver.toScheme B S hS).obj
      (Over.mk (⟨b⟩ : B.obj hK ⟶ B.obj hS) : BigFppfOver B S hS)) :=
    inferInstanceAs (Subsingleton ↥(Spec (CommRingCat.of K)))
  have hsub : Subsingleton (points B S hS
      (yoneda.obj (Over.mk (⟨b⟩ : B.obj hK ⟶ B.obj hS) : BigFppfOver B S hS))) :=
    ⟨fun x y ↦ (schemePointsHomeomorph B S hS _).injective (Subsingleton.elim _ _)⟩
  obtain ⟨X, hX, C, hCopen, hCcompact, hCcover⟩ := exists_isOpen_isCompact_cover_points B S hS hF
  obtain ⟨T, qT, ⟨eT⟩⟩ : ∃ (T : BigFppfOver B S hS)
      (_ : T ⟶ (Over.mk (⟨b⟩ : B.obj hK ⟶ B.obj hS) : BigFppfOver B S hS)),
      Nonempty (points B S hS (yoneda.obj T) ≃ₜ
        ↥(Spec (CommRingCat.of (MvPolynomial X.directedAffineCover.I₀ K)))) := by
    refine ⟨Over.mk (B.inclusion.preimage
      (show B.inclusion.obj (B.obj (affineCoverPolynomial_size_lt B hX K hK)) ⟶
          B.inclusion.obj (B.obj hK) from
        Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : K →+* MvPolynomial X.directedAffineCover.I₀ K))) ≫
      (⟨b⟩ : B.obj hK ⟶ B.obj hS)), Over.homMk _ rfl, ⟨schemePointsHomeomorph B S hS _⟩⟩
  refine compactSpace_of_isClosedMap_specMvPolynomial
    (pointsMap B S hS (pullback (yoneda.map qT) f) (pullback.snd (yoneda.map qT) f))
    (fun w ↦ eT (pointsMap B S hS (pullback (yoneda.map qT) f)
      (pullback.fst (yoneda.map qT) f) w))
    (continuous_pointsMap B S hS _)
    (eT.continuous.comp (continuous_pointsMap B S hS _))
    (eT.isClosedMap.comp
      (hf (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) (yoneda.map qT)))
    (fun x t ↦ ?_) C hCopen hCcompact hCcover
  obtain ⟨w, hw₁, hw₂⟩ := exists_points_of_isPullback B S hS
    (IsPullback.of_hasPullback (yoneda.map qT) f) (eT.symm t) x (Subsingleton.elim _ _)
  exact ⟨w, hw₂, by rw [hw₁, eT.apply_symm_apply]⟩

/-- A universally closed morphism of algebraic spaces over `S` whose target has quasi-compact
point space has quasi-compact point space. -/
theorem compactSpace_points_of_universallyClosed
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) (hf : UniversallyClosed B S hS f)
    (hGcompact : CompactSpace (points B S hS G)) :
    CompactSpace (points B S hS F) := by
  have := hGcompact
  have hfib (y : points B S hS G) : IsCompact (pointsMap B S hS F f ⁻¹' {y}) := by
    induction y using Quot.ind with | _ q => ?_
    change IsCompact (pointsMap B S hS F f ⁻¹' {q.class B S hS G})
    have hsubScheme : Subsingleton ((BigFppfOver.toScheme B S hS).obj
        (FieldValuedPoint.siteObject B S hS G q)) :=
      inferInstanceAs (Subsingleton ↥(Spec (CommRingCat.of q.carrier)))
    have hsub : Subsingleton
        (points B S hS (yoneda.obj (FieldValuedPoint.siteObject B S hS G q))) :=
      ⟨fun x y ↦ (schemePointsHomeomorph B S hS _).injective (Subsingleton.elim _ _)⟩
    have hbase (z : points B S hS (yoneda.obj (FieldValuedPoint.siteObject B S hS G q))) :
        pointsMap B S hS (yoneda.obj (FieldValuedPoint.siteObject B S hS G q))
          (fieldMorphism B S hS G q) z = q.class B S hS G := by
      rw [Subsingleton.elim z
        ((FieldValuedPoint.tautologicalPoint B S hS G q).class B S hS _)]
      exact pointsMap_fieldMorphism_tautologicalPoint B S hS G q
    have : CompactSpace (points B S hS (pullback (fieldMorphism B S hS G q) f)) :=
      compactSpace_points_of_universallyClosed_specField B S hS q.contained q.toBase
        (isAlgebraicSpace_pullback B S hS (fieldMorphism B S hS G q) f
          (isAlgebraicSpace_yoneda B S hS _) hF hG)
        (pullback.fst (fieldMorphism B S hS G q) f)
        (universallyClosed_pullback B S hS f (fieldMorphism B S hS G q) hf)
    have hrange : pointsMap B S hS F f ⁻¹' {q.class B S hS G} =
        Set.range (pointsMap B S hS (pullback (fieldMorphism B S hS G q) f)
          (pullback.snd (fieldMorphism B S hS G q) f)) := by
      refine Set.eq_of_subset_of_subset (fun x hx ↦ ?_) (fun x hx ↦ ?_)
      · obtain ⟨w, -, hw⟩ := exists_points_of_isPullback B S hS
          (IsPullback.of_hasPullback (fieldMorphism B S hS G q) f)
          ((FieldValuedPoint.tautologicalPoint B S hS G q).class B S hS _) x
          ((hbase _).trans hx.symm)
        exact ⟨w, hw⟩
      · obtain ⟨w, rfl⟩ := hx
        rw [Set.mem_preimage, Set.mem_singleton_iff,
          ← pointsMap_apply_comm B S hS pullback.condition w]
        exact hbase _
    rw [hrange]
    exact isCompact_range (continuous_pointsMap B S hS _)
  have hproper : IsProperMap (pointsMap B S hS F f) :=
    isProperMap_iff_isClosedMap_and_compact_fibers.2
      ⟨continuous_pointsMap B S hS f, isClosed_of_universallyClosed B S hS hG f hf, hfib⟩
  refine ⟨?_⟩
  simpa using hproper.isCompact_preimage
    (K := (Set.univ : Set (points B S hS G))) isCompact_univ

/-- **Stacks 04XW.** A universally closed morphism of algebraic spaces over `S` is
quasi-compact. -/
@[stacks 04XW]
theorem isQuasiCompact_of_universallyClosed
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) (hf : UniversallyClosed B S hS f) :
    IsQuasiCompact B S hS f := by
  refine ((isQuasiCompact_tfae B S hS hF hG f).out 3 1).mp fun Z g hZ ↦ ?_
  have := hZ
  have hbase : IsAlgebraicSpace B S hS (pullback g f) :=
    isAlgebraicSpace_pullback B S hS g f (isAlgebraicSpace_yoneda B S hS Z) hF hG
  rw [isQuasiCompactSpace_iff_compactSpace_points B S hS _ hbase]
  exact compactSpace_points_of_universallyClosed B S hS hbase
    (isAlgebraicSpace_yoneda B S hS Z) (pullback.fst g f)
    (universallyClosed_pullback B S hS f g hf)
    (compactSpace_points_yoneda B S hS Z)

end QuasiCompact

/-! ### Descent of separatedness along a universally closed surjection -/

section Descent

variable {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 05Z2, part (4).** Let `X ⟶ Y ⟶ T` be morphisms of algebraic spaces over `S`, with
`X ⟶ Y` surjective and universally closed. If `X` is separated over `T`, then so is `Y`. -/
@[stacks 05Z2 "part (4): separated over the base"]
theorem isSeparated_of_isSurjective_of_universallyClosed
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hT : IsAlgebraicSpace B S hS T) (f : X ⟶ Y) (g : Y ⟶ T)
    (hfsurj : IsSurjective B S hS f) (hfclosed : UniversallyClosed B S hS f)
    (hsep : IsSeparated B S hS (f ≫ g)) :
    IsSeparated B S hS g := by
  have hXX : IsAlgebraicSpace B S hS (pullback (f ≫ g) (f ≫ g)) :=
    isAlgebraicSpace_pullback B S hS (f ≫ g) (f ≫ g) hX hX hT
  have hYY : IsAlgebraicSpace B S hS (pullback g g) :=
    isAlgebraicSpace_pullback B S hS g g hY hY hT
  have hm : UniversallyClosed B S hS
      (pullback.map (f ≫ g) (f ≫ g) g g f f (𝟙 T) (by simp) (by simp)) :=
    universallyClosed_selfProductMap (Bs := (⟨T, hT⟩ : AlgebraicSpaces B S hS))
      (X := ⟨X, hX⟩) (Y := ⟨Y, hY⟩) (ObjectProperty.homMk g) (ObjectProperty.homMk f) hfclosed
  have hcomp : UniversallyClosed B S hS (f ≫ pullback.diagonal g) := by
    rw [pullback.comp_diagonal]
    exact universallyClosed_comp B S hS hXX hYY _ _
      (universallyClosed_of_isClosedImmersion B S hS hX hXX _ hsep) hm
  have hdY : UniversallyClosed B S hS (pullback.diagonal g) :=
    universallyClosed_of_isSurjective_comp B S hS hX hY hYY f (pullback.diagonal g)
      hcomp hfsurj
  have hrep := relativelyRepresentable_pullbackDiagonal B S hS g hY
  have hpres := presheaf_universallyClosed_of_universallyClosed B S hS hrep hdY
  have hlft := presheaf_locallyOfFiniteType_pullbackDiagonal B S hS g hY
  have hmono := presheaf_monomorphisms_pullbackDiagonal B S hS g hY
  refine ⟨hrep, fun U V k fst snd sq ↦ ?_⟩
  have hc : AlgebraicGeometry.UniversallyClosed ((BigFppfOver.toScheme B S hS).map snd) ∧
      (AlgebraicGeometry.LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map snd) ∧
        Mono ((BigFppfOver.toScheme B S hS).map snd)) :=
    ⟨hpres.2 k fst snd sq, hlft.2 k fst snd sq, hmono.2 k fst snd sq⟩
  exact (AlgebraicGeometry.IsClosedImmersion.iff_isProper_and_mono _).2
    (((closedImmersion_conditions_tfae ((BigFppfOver.toScheme B S hS).map snd)).out 5 1).mp hc)

/-- Let `X ⟶ Y` be a surjective universally closed morphism of algebraic spaces over `S`. If
`X` is separated over `S`, then so is `Y`.

This is the case of `AlgebraicGeometry.Space.isSeparated_of_isSurjective_of_universallyClosed`,
which carries Tag 05Z2, part (4), in which the base algebraic space is the terminal presheaf;
separatedness over it is separatedness over `S` by
`AlgebraicGeometry.Space.isSeparatedOver_iff_isSeparated_of_isTerminal`. -/
theorem isSeparatedOver_of_isSurjective_of_universallyClosed
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hterm : IsAlgebraicSpace B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)))
    (f : X ⟶ Y) (hfsurj : IsSurjective B S hS f)
    (hfclosed : UniversallyClosed B S hS f) (hsep : IsSeparatedOver B S hS X) :
    IsSeparatedOver B S hS Y :=
  (isSeparatedOver_iff_isSeparated_of_isTerminal B S hS terminalIsTerminal
      (terminal.from Y)).2 <|
    isSeparated_of_isSurjective_of_universallyClosed B S hS hX hY hterm f (terminal.from Y)
      hfsurj hfclosed
      (by
        rw [terminal.comp_from]
        exact (isSeparatedOver_iff_isSeparated_of_isTerminal B S hS terminalIsTerminal
          (terminal.from X)).1 hsep)

/-- **Stacks 05Z2, part (3).** Let `X ⟶ Y ⟶ T` be morphisms of algebraic spaces over `S`, with
`X ⟶ Y` surjective and universally closed. If `X` is quasi-separated over `T`, then so is `Y`. -/
@[stacks 05Z2 "part (3): quasi-separated over the base"]
theorem isQuasiSeparated_of_isSurjective_of_universallyClosed
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hT : IsAlgebraicSpace B S hS T) (f : X ⟶ Y) (g : Y ⟶ T)
    (hfsurj : IsSurjective B S hS f) (hfclosed : UniversallyClosed B S hS f)
    (hqs : IsQuasiSeparated B S hS (f ≫ g)) :
    IsQuasiSeparated B S hS g := by
  have hXX : IsAlgebraicSpace B S hS (pullback (f ≫ g) (f ≫ g)) :=
    isAlgebraicSpace_pullback B S hS (f ≫ g) (f ≫ g) hX hX hT
  have hYY : IsAlgebraicSpace B S hS (pullback g g) :=
    isAlgebraicSpace_pullback B S hS g g hY hY hT
  have hm : IsQuasiCompact B S hS
      (pullback.map (f ≫ g) (f ≫ g) g g f f (𝟙 T) (by simp) (by simp)) :=
    isQuasiCompact_of_universallyClosed B S hS hXX hYY _
      (universallyClosed_selfProductMap (Bs := (⟨T, hT⟩ : AlgebraicSpaces B S hS))
        (X := ⟨X, hX⟩) (Y := ⟨Y, hY⟩) (ObjectProperty.homMk g) (ObjectProperty.homMk f) hfclosed)
  have hcomp : IsQuasiCompact B S hS (f ≫ pullback.diagonal g) := by
    rw [pullback.comp_diagonal]
    exact isQuasiCompact_comp B S hS hXX hYY _ _ hqs hm
  exact isQuasiCompact_of_comp_surjective B S hS hX hY hYY f (f ≫ pullback.diagonal g)
    (pullback.diagonal g) rfl hfsurj hcomp

/-- Let `X ⟶ Y` be a surjective universally closed morphism of algebraic spaces over `S`. If
`X` is quasi-separated over `S`, then so is `Y`.

This is the case of
`AlgebraicGeometry.Space.isQuasiSeparated_of_isSurjective_of_universallyClosed`, which carries
Tag 05Z2, part (3), in which the base algebraic space is the terminal presheaf;
quasi-separatedness over it is quasi-separatedness over `S` by
`AlgebraicGeometry.Space.isQuasiSeparatedOver_iff_diagonalProp_quasiCompact_of_isTerminal`. -/
theorem isQuasiSeparatedOver_of_isSurjective_of_universallyClosed
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hterm : IsAlgebraicSpace B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)))
    (f : X ⟶ Y) (hfsurj : IsSurjective B S hS f)
    (hfclosed : UniversallyClosed B S hS f) (hqs : IsQuasiSeparatedOver B S hS X) :
    IsQuasiSeparatedOver B S hS Y :=
  (isQuasiSeparatedOver_iff_diagonalProp_quasiCompact_of_isTerminal B S hS terminalIsTerminal
      (terminal.from Y)).2 <|
    diagonalProp_quasiCompact_of_isQuasiSeparated B S hS
      (relativelyRepresentable_pullbackDiagonal B S hS (terminal.from Y) hY)
      (isQuasiSeparated_of_isSurjective_of_universallyClosed B S hS hX hY hterm f
        (terminal.from Y) hfsurj hfclosed
        (by
          rw [terminal.comp_from]
          exact isQuasiSeparated_of_diagonalProp_quasiCompact B S hS
            ((isQuasiSeparatedOver_iff_diagonalProp_quasiCompact_of_isTerminal B S hS
              terminalIsTerminal (terminal.from X)).1 hqs)))

end Descent

/-! ### Change of base scheme

The absolute separation axioms of Stacks 03BS are the axioms over the terminal scheme, taken
after the lower-shriek extension of Stacks 03I5 part (2). Parts (1) and (2) of Stacks 05Z2 are
therefore parts (3) and (4) over the terminal scheme, applied to the extension of the given
morphism — which calls for surjectivity and universal closedness of that extension, and that is
what this section supplies.
-/

section Relocalize

variable (S' : Scheme.{u}) (hS' : B.Contains S') (k : B.obj hS ⟶ B.obj hS')

/-- **Surjectivity survives a change of base scheme.** The map on points of the lower-shriek
extension of a morphism along `k : S ⟶ S'` is the map on points of the morphism itself, read
through the bijections of `AlgebraicGeometry.Space.relocalizedPointsEquiv`; it is therefore
surjective as soon as the latter is. No algebraicity hypothesis is needed. -/
theorem isSurjective_relocalize (f : X ⟶ Y) (hf : IsSurjective B S hS f) :
    IsSurjective B S' hS' ((OverShriek.relocalizePresheafFunctor k).map f) := by
  intro y
  obtain ⟨y₀, rfl⟩ := relocalizedPointsMap_surjective B S S' hS hS' k Y y
  obtain ⟨x, rfl⟩ := hf y₀
  exact ⟨relocalizedPointsMap B S S' hS hS' k X x,
    (relocalizedPointsMap_naturality B S S' hS hS' k f x).symm⟩

/-- **Surjectivity does not change with the base scheme**: a morphism of presheaves on the big
fppf site of `S` is surjective exactly when its lower-shriek extension along `k : S ⟶ S'` is, the
maps on points of the two being identified by `AlgebraicGeometry.Space.relocalizedPointsEquiv`. -/
theorem isSurjective_relocalize_iff (f : X ⟶ Y) :
    IsSurjective B S' hS' ((OverShriek.relocalizePresheafFunctor k).map f) ↔
      IsSurjective B S hS f := by
  refine ⟨fun h y => ?_, isSurjective_relocalize B S hS S' hS' k f⟩
  obtain ⟨x', hx'⟩ := h (relocalizedPointsMap B S S' hS hS' k Y y)
  obtain ⟨x, rfl⟩ := relocalizedPointsMap_surjective B S S' hS hS' k X x'
  refine ⟨x, relocalizedPointsMap_injective B S S' hS hS' k Y ?_⟩
  rw [relocalizedPointsMap_naturality]
  exact hx'

/-- The point topology of Stacks 03BX on an algebraic space over `S` is the topology induced,
along the transport of points of
`AlgebraicGeometry.Space.relocalizedPointsMap`, from the point topology of its lower-shriek
extension to the big fppf site of `S'`. -/
theorem pointTopology_eq_induced_relocalizedPointsMap
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    pointTopology B S hS F =
      TopologicalSpace.induced (relocalizedPointsMap B S S' hS hS' k F)
        (pointTopology B S' hS' ((OverShriek.relocalizePresheafFunctor k).obj F)) :=
  congrArg (fun T : PointTopologyFamily B S hS => T.topology F hF)
    (PointTopologyFamily.eq B S hS (pointTopologyFamily B S hS)
      (relocalizedPointTopologyFamily B S S' hS hS' k))

/-- A map `q : A' → C'` is closed as soon as it is conjugate, along two surjections `u` and `v`
which induce the topologies of their sources, to a closed map `p : A → C`. -/
private theorem isClosedMap_of_topology_eq_induced {A C A' C' : Type*}
    [tA : TopologicalSpace A] [tC : TopologicalSpace C] [tA' : TopologicalSpace A']
    [tC' : TopologicalSpace C'] (u : A → A') (v : C → C') (hu : Function.Surjective u)
    (hv : Function.Surjective v) (htA : tA = TopologicalSpace.induced u tA')
    (htC : tC = TopologicalSpace.induced v tC') (p : A → C) (q : A' → C')
    (hcomm : ∀ a, q (u a) = v (p a)) (hp : IsClosedMap p) : IsClosedMap q := by
  subst htA
  subst htC
  intro D hD
  obtain ⟨E, hE, hEeq⟩ := isClosed_induced_iff.1 (hp _ (isClosed_induced_iff.2 ⟨D, hD, rfl⟩))
  have himg : q '' D = E :=
    calc q '' D = q '' (u '' (u ⁻¹' D)) := by rw [Set.image_preimage_eq _ hu]
      _ = v '' (p '' (u ⁻¹' D)) := by
          rw [← Set.image_comp, ← Set.image_comp]
          exact Set.image_congr' hcomm
      _ = v '' (v ⁻¹' E) := by rw [hEeq]
      _ = E := Set.image_preimage_eq _ hv
  rw [himg]
  exact hE

/-- **Closedness survives a change of base scheme.** The lower-shriek extension of a closed
morphism of algebraic spaces over `S` along `k : S ⟶ S'` is closed over `S'`. -/
theorem isClosedMorphism_relocalize (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsClosedMorphism B S hS f) :
    IsClosedMorphism B S' hS' ((OverShriek.relocalizePresheafFunctor k).map f) :=
  isClosedMap_of_topology_eq_induced (relocalizedPointsMap B S S' hS hS' k X)
    (relocalizedPointsMap B S S' hS hS' k Y)
    (relocalizedPointsMap_surjective B S S' hS hS' k X)
    (relocalizedPointsMap_surjective B S S' hS hS' k Y)
    (pointTopology_eq_induced_relocalizedPointsMap B S hS S' hS' k X hX)
    (pointTopology_eq_induced_relocalizedPointsMap B S hS S' hS' k Y hY)
    _ _ (fun x => (relocalizedPointsMap_naturality B S S' hS hS' k f x).symm) hf

/-- **Universal closedness survives a change of base scheme.** The lower-shriek extension of a
universally closed morphism of algebraic spaces over `S` along `k : S ⟶ S'` is universally
closed over `S'`. -/
theorem universallyClosed_relocalize (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : UniversallyClosed B S hS f) :
    UniversallyClosed B S' hS' ((OverShriek.relocalizePresheafFunctor k).map f) := by
  set Λ := OverShriek.relocalizePresheafFunctor k with hΛdef
  refine universallyClosed_of_isClosedMorphism_yoneda B S' hS' (Λ.map f) ?_
  intro W a
  obtain ⟨U, e, b, rfl⟩ := exists_relocalized_yoneda_factorization B S S' hS hS' k Y W a
  have hUalg := isAlgebraicSpace_yoneda B S hS U
  have hPalg : IsAlgebraicSpace B S hS (pullback b f) :=
    isAlgebraicSpace_pullback B S hS b f hUalg hX hY
  have hclosed : IsClosedMorphism B S' hS' (Λ.map (pullback.fst b f)) :=
    isClosedMorphism_relocalize B S hS S' hS' k hPalg hUalg _ (hf _ hUalg b)
  set iU := relocalizedYonedaIso B (B.obj hS) (B.obj hS') k U with hiUdef
  have hpb : IsPullback (Λ.map (pullback.fst b f) ≫ iU.hom ≫ yoneda.map e.inv)
      (Λ.map (pullback.snd b f))
      (yoneda.map e.hom ≫ iU.inv ≫ Λ.map b) (Λ.map f) :=
    ((IsPullback.of_hasPullback b f).map Λ).of_iso (Iso.refl _)
      (iU ≪≫ (yoneda.mapIso e).symm) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp)
      (by simp)
  have hgoal : IsClosedMorphism B S' hS'
      (Λ.map (pullback.fst b f) ≫ iU.hom ≫ yoneda.map e.inv) := by
    change IsClosedMap (pointsMap B S' hS' _ (Λ.map (pullback.fst b f) ≫ _))
    rw [pointsMap_comp]
    exact (isClosedMap_pointsMap_of_isIso B S' hS' (iU.hom ≫ yoneda.map e.inv)).comp hclosed
  have hfac : hpb.isoPullback.inv ≫ (Λ.map (pullback.fst b f) ≫ iU.hom ≫ yoneda.map e.inv) =
      pullback.fst (yoneda.map e.hom ≫ iU.inv ≫ Λ.map b) (Λ.map f) :=
    calc hpb.isoPullback.inv ≫ (Λ.map (pullback.fst b f) ≫ iU.hom ≫ yoneda.map e.inv)
        = hpb.isoPullback.inv ≫ hpb.isoPullback.hom ≫
            pullback.fst (yoneda.map e.hom ≫ iU.inv ≫ Λ.map b) (Λ.map f) := by
          rw [hpb.isoPullback_hom_fst]
      _ = pullback.fst (yoneda.map e.hom ≫ iU.inv ≫ Λ.map b) (Λ.map f) := by
          rw [Iso.inv_hom_id_assoc]
  exact isClosedMap_pointsMap_of_comp_isIso B S' hS' hpb.isoPullback.inv hfac hgoal

end Relocalize

/-! ### Descent of the absolute separation axioms -/

section Absolute

/-- The terminal presheaf on the big fppf site of `T` is an algebraic space over `T`: it is
isomorphic to the presheaf represented by the identity of `T`, which is an object of the
site. -/
theorem isAlgebraicSpace_terminal (T : Scheme.{u}) (hT : B.Contains T) :
    IsAlgebraicSpace B T hT (⊤_ ((BigFppfOver B T hT)ᵒᵖ ⥤ Type u)) := by
  have hV : IsTerminal (yoneda.obj (Over.mk (𝟙 (B.obj hT)))) :=
    (Over.mkIdTerminal (X := B.obj hT)).isTerminalObj yoneda _
  exact isAlgebraicSpace_of_iso B T hT (hV.uniqueUpToIso terminalIsTerminal)
    (isAlgebraicSpace_yoneda B T hT (Over.mk (𝟙 (B.obj hT))))

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **Stacks 05Z2, part (1).** Let `X ⟶ Y` be a surjective universally closed morphism of
algebraic spaces over `S`. If `X` is quasi-separated, then so is `Y`.

This is part (3) over the terminal scheme, as the source says: quasi-separatedness of an
algebraic space is quasi-separatedness over `Spec ℤ` of its lower-shriek extension along
`S ⟶ Spec ℤ`, by Stacks 03BS, and that extension of `X ⟶ Y` is again surjective and universally
closed by `AlgebraicGeometry.Space.isSurjective_relocalize` and
`AlgebraicGeometry.Space.universallyClosed_relocalize`. -/
@[stacks 05Z2 "part (1): quasi-separated"]
theorem isAbsolutelyQuasiSeparated_of_isSurjective_of_universallyClosed
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hfsurj : IsSurjective B S hS f) (hfclosed : UniversallyClosed B S hS f)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X) :
    IsAbsolutelyQuasiSeparated B S hS hZ Y :=
  isQuasiSeparatedOver_of_isSurjective_of_universallyClosed B (⊤_ Scheme.{u}) hZ
    (isAlgebraicSpace_viewOver B S (⊤_ Scheme.{u}) hS hZ ⟨terminal.from S⟩ X hX)
    (isAlgebraicSpace_viewOver B S (⊤_ Scheme.{u}) hS hZ ⟨terminal.from S⟩ Y hY)
    (isAlgebraicSpace_terminal B (⊤_ Scheme.{u}) hZ) _
    (isSurjective_relocalize B S hS (⊤_ Scheme.{u}) hZ ⟨terminal.from S⟩ f hfsurj)
    (universallyClosed_relocalize B S hS (⊤_ Scheme.{u}) hZ ⟨terminal.from S⟩ hX hY f hfclosed)
    hqs

/-- **Stacks 05Z2, part (2).** Let `X ⟶ Y` be a surjective universally closed morphism of
algebraic spaces over `S`. If `X` is separated, then so is `Y`.

This is part (4) over the terminal scheme, as the source says: separatedness of an algebraic
space is separatedness over `Spec ℤ` of its lower-shriek extension along `S ⟶ Spec ℤ`, by
Stacks 03BS, and that extension of `X ⟶ Y` is again surjective and universally closed by
`AlgebraicGeometry.Space.isSurjective_relocalize` and
`AlgebraicGeometry.Space.universallyClosed_relocalize`. -/
@[stacks 05Z2 "part (2): separated"]
theorem isAbsolutelySeparated_of_isSurjective_of_universallyClosed
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hfsurj : IsSurjective B S hS f) (hfclosed : UniversallyClosed B S hS f)
    (hsep : IsAbsolutelySeparated B S hS hZ X) :
    IsAbsolutelySeparated B S hS hZ Y :=
  isSeparatedOver_of_isSurjective_of_universallyClosed B (⊤_ Scheme.{u}) hZ
    (isAlgebraicSpace_viewOver B S (⊤_ Scheme.{u}) hS hZ ⟨terminal.from S⟩ X hX)
    (isAlgebraicSpace_viewOver B S (⊤_ Scheme.{u}) hS hZ ⟨terminal.from S⟩ Y hY)
    (isAlgebraicSpace_terminal B (⊤_ Scheme.{u}) hZ) _
    (isSurjective_relocalize B S hS (⊤_ Scheme.{u}) hZ ⟨terminal.from S⟩ f hfsurj)
    (universallyClosed_relocalize B S hS (⊤_ Scheme.{u}) hZ ⟨terminal.from S⟩ hX hY f hfclosed)
    hsep

end Absolute

/-! ### Closedness from a saturating section -/

/-- A map `q : A → C` of topological spaces with a continuous section `s` is closed as soon as
every closed set of `A` is saturated along `s`, in the sense that it contains `s (q a)` whenever
it contains `a`: the image of such a set under `q` is then its preimage under `s`. -/
private theorem isClosedMap_of_isSaturated_section {A C : Type*} [TopologicalSpace A]
    [TopologicalSpace C] (q : A → C) (s : C → A) (hs : Continuous s) (hqs : ∀ c, q (s c) = c)
    (hsat : ∀ W : Set A, IsClosed W → ∀ a ∈ W, s (q a) ∈ W) :
    IsClosedMap q := by
  intro W hW
  have himg : q '' W = s ⁻¹' W := by
    refine Set.eq_of_subset_of_subset (fun c hc ↦ ?_) (fun c hc ↦ ⟨s c, hc, hqs c⟩)
    obtain ⟨a, ha, rfl⟩ := hc
    exact hsat W hW a ha
  rw [himg]
  exact hW.preimage hs

/-! ### Surjectivity on points -/

/-! ### Closed sets of points of a scheme -/

/-- A closed set of points of a presheaf represented by an object of the big fppf site of `S` is
cut out by a closed subset of the representing scheme, membership being tested at the underlying
scheme point of a field-valued representative.

This is clause (1) of Stacks 03BX, in the form
`AlgebraicGeometry.Space.isOpen_yoneda_iff_isSchemeOpen`, read on complements. -/
private theorem exists_isClosed_schemePoint_mem_iff (U : BigFppfOver B S hS)
    (W : Set (points B S hS (yoneda.obj U))) (hW : IsClosed W) :
    ∃ V : Set ((BigFppfOver.toScheme B S hS).obj U), IsClosed V ∧
      ∀ p : FieldValuedPoint B S hS (yoneda.obj U),
        p.class B S hS (yoneda.obj U) ∈ W ↔ schemePoint B S hS U p ∈ V := by
  obtain ⟨V, hV, hmem⟩ := (isOpen_yoneda_iff_isSchemeOpen B S hS U Wᶜ).mp hW.isOpen_compl
  exact ⟨Vᶜ, hV.isClosed_compl, fun p ↦ by
    simpa only [Set.mem_compl_iff, not_not] using (not_congr (hmem p))⟩

/-! ### Lifting a field-valued point along a chart -/

/-- Let `q : h_U ⟶ G` be surjective on points and let `f : F ⟶ G`. Every field-valued point of
`F` is equivalent to one whose image in `G` factors through `q` by a morphism of the site. -/
private theorem exists_dominating_fieldValuedPoint_factor
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : BigFppfOver B S hS} (q : yoneda.obj U ⟶ G)
    (hq : Function.Surjective (pointsMap B S hS (yoneda.obj U) q)) (f : F ⟶ G)
    (p : FieldValuedPoint B S hS F) :
    ∃ (r : FieldValuedPoint B S hS F) (a : r.siteObject B S hS F ⟶ U),
      r.class B S hS F = p.class B S hS F ∧
        q.app (Opposite.op (r.siteObject B S hS F)) a =
          f.app (Opposite.op (r.siteObject B S hS F)) r.value := by
  obtain ⟨x, hx⟩ := hq ((FieldValuedPoint.map B S hS F f p).class B S hS G)
  obtain ⟨a, rfl⟩ := Quot.exists_rep x
  obtain ⟨r, ⟨j, hj⟩, ⟨i, hi⟩⟩ :=
    (FieldValuedPoint.class_eq_class_iff B S hS G _ _).mp hx
  refine ⟨{ carrier := r.carrier
            field := r.field
            contained := r.contained
            toBase := r.toBase
            value := F.map i.op p.value }, j ≫ a.value, ?_, ?_⟩
  · exact Quot.sound ⟨_, FieldValuedPoint.dominates_refl B S hS F _, ⟨i, rfl⟩⟩
  · change q.app _ ((yoneda.obj U).map j.op a.value) = f.app _ (F.map i.op p.value)
    exact (NatTrans.naturality_apply q j.op a.value).trans
      (hj.trans (hi.symm.trans (NatTrans.naturality_apply f i.op p.value).symm))

/-! ### The terminal presheaf -/

/-- The presheaf represented by the terminal object of the big fppf site of `S`, the base `S`
viewed over itself, is the terminal presheaf: Yoneda preserves the terminal object. -/
noncomputable def yonedaMkIdTerminal :
    IsTerminal (yoneda.obj (Over.mk (𝟙 (B.obj hS)) : BigFppfOver B S hS)) :=
  (Over.mkIdTerminal (X := B.obj hS)).isTerminalObj yoneda _

end AlgebraicGeometry.Space

/-! ### The strange universally closed morphism of Stacks 03IV -/

namespace AlgebraicGeometry.AffineLineTranslation

open AffineLineInvolution Stacks.Groupoids

attribute [local instance] Space.pointTopology

/-- A closed subset of the affine line over a field of characteristic zero which contains the
rational point `a + n` for every integer `n` is the whole line. -/
private theorem eq_univ_of_isClosed_of_forall_int_translate_mem {K : Type u} [Field K]
    [CharZero K] (a : K) (V : Set (PrimeSpectrum (Polynomial K))) (hV : IsClosed V)
    (h : ∀ n : ℤ, PrimeSpectrum.comap (Polynomial.evalRingHom (a + n))
      (IsLocalRing.closedPoint K) ∈ V) :
    V = Set.univ := by
  obtain ⟨I, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus V).mp hV
  have hzero : ∀ g ∈ I, g = 0 := by
    intro g hg
    apply Polynomial.eq_zero_of_infinite_isRoot
    have hinj : Function.Injective (fun n : ℤ ↦ a + (n : K)) :=
      fun m n hmn ↦ Int.cast_injective (add_left_cancel hmn)
    apply (Set.infinite_range_of_injective hinj).mono
    rintro _ ⟨n, rfl⟩
    have hn := (h n) hg
    change Polynomial.eval (a + (n : K)) g ∈ (IsLocalRing.closedPoint K).asIdeal at hn
    simpa only [Ideal.eq_bot_of_prime, Ideal.mem_bot, Set.mem_ofPred_eq,
      Polynomial.IsRoot.def] using hn
  ext x
  simp only [Set.mem_univ, iff_true]
  intro g hg
  rw [hzero g hg]
  exact x.asIdeal.zero_mem

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of k)))

attribute [local instance] Space.hasPullbacks_presheaf_universallyClosed
attribute [local instance high] Space.hasPullback_presheaf_universallyClosed

/-! #### The affine line as the spectrum of a polynomial algebra over a field point -/

/-- The object of the big fppf site over `Spec k` given by the spectrum of a field `K` of the
site, over the base along a prescribed morphism `Spec K ⟶ Spec k`. -/
private noncomputable abbrev fieldObject {K : Type u} [Field K] (hK : B.Contains (Spec (.of K)))
    (b : Spec (.of K) ⟶ Spec (.of k)) : BigFppfOver B (Spec (.of k)) hS :=
  Over.mk (⟨b⟩ : B.obj hK ⟶ B.obj hS)

/-- The tautological field-valued point of the presheaf represented by
`AlgebraicGeometry.AffineLineTranslation.fieldObject`. -/
private noncomputable abbrev fieldPoint {K : Type u} [Field K] (hK : B.Contains (Spec (.of K)))
    (b : Spec (.of K) ⟶ Spec (.of k)) :
    Space.FieldValuedPoint B (Spec (.of k)) hS (yoneda.obj (fieldObject k B hS hK b)) where
  carrier := K
  contained := hK
  toBase := b
  value := 𝟙 _

/-- The affine line over a field `K` of the site, as an object of the big fppf site over
`Spec k` along a prescribed morphism `Spec K ⟶ Spec k`: it is the spectrum of `K[x]`, which
satisfies the site's cutoff because `K[x]` is of finite type over `K`. -/
private noncomputable def polynomialObject {K : Type u} [Field K]
    (hK : B.Contains (Spec (.of K))) (b : Spec (.of K) ⟶ Spec (.of k)) :
    BigFppfOver B (Spec (.of k)) hS :=
  Over.mk (⟨Spec.map (CommRingCat.ofHom (Polynomial.C : K →+* Polynomial K)) ≫ b⟩ :
    B.obj (Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
      K (Polynomial K) hK) ⟶ B.obj hS)

/-- The structure morphism of the affine line over a field point of the site. -/
private noncomputable def polynomialProjection {K : Type u} [Field K]
    (hK : B.Contains (Spec (.of K))) (b : Spec (.of K) ⟶ Spec (.of k)) :
    polynomialObject k B hS hK b ⟶ fieldObject k B hS hK b :=
  Over.homMk (⟨Spec.map (CommRingCat.ofHom (Polynomial.C : K →+* Polynomial K))⟩)

/-- Evaluating a polynomial at a scalar splits the inclusion of scalars. -/
private theorem specMap_evalRingHom_comp_specMap_C {K : Type u} [CommRing K] (a : K) :
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : K →+* Polynomial K)) = 𝟙 (Spec (.of K)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
    show (Polynomial.evalRingHom a).comp Polynomial.C = RingHom.id K by ext x; simp]
  exact Spec.map_id _

/-- The `K`-point of the affine line over a field point of the site at a scalar `a`, the
spectrum of evaluation at `a`. -/
private noncomputable def polynomialEvaluation {K : Type u} [Field K]
    (hK : B.Contains (Spec (.of K))) (b : Spec (.of K) ⟶ Spec (.of k)) (a : K) :
    fieldObject k B hS hK b ⟶ polynomialObject k B hS hK b :=
  Over.homMk (⟨Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))⟩)
    (by
      apply ObjectProperty.hom_ext
      change Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : K →+* Polynomial K)) ≫ b = b
      rw [← Category.assoc, specMap_evalRingHom_comp_specMap_C, Category.id_comp])

/-- Every `K`-point of the affine line over a field point of the site is a section of its
structure morphism. -/
private theorem polynomialEvaluation_comp_polynomialProjection {K : Type u} [Field K]
    (hK : B.Contains (Spec (.of K))) (b : Spec (.of K) ⟶ Spec (.of k)) (a : K) :
    polynomialEvaluation k B hS hK b a ≫ polynomialProjection k B hS hK b = 𝟙 _ :=
  Over.OverMorphism.ext (ObjectProperty.hom_ext _ (specMap_evalRingHom_comp_specMap_C a))

/-- **Saturation along the fibres of the affine line in characteristic zero.** Let
`l : h_V ⟶ F` be a morphism out of the presheaf represented by the affine line over a field
point `Spec K` of characteristic zero. If a closed set of points of `F` contains the image of
the `K`-point of `V` at `a + n` for every integer `n`, then it contains the image of the
`K`-point at `0`. -/
private theorem mem_of_isClosed_of_forall_int_translate_mem
    {F : (BigFppfOver B (Spec (.of k)) hS)ᵒᵖ ⥤ Type u} {K : Type u} [Field K] [CharZero K]
    (hK : B.Contains (Spec (.of K))) (b : Spec (.of K) ⟶ Spec (.of k))
    (l : yoneda.obj (polynomialObject k B hS hK b) ⟶ F)
    (W : Set (Space.points B (Spec (.of k)) hS F)) (hW : IsClosed W) (a : K)
    (h : ∀ n : ℤ, Space.pointsMap B (Spec (.of k)) hS _
      (yoneda.map (polynomialEvaluation k B hS hK b (a + n)) ≫ l)
      ((fieldPoint k B hS hK b).class B (Spec (.of k)) hS _) ∈ W) :
    Space.pointsMap B (Spec (.of k)) hS _
      (yoneda.map (polynomialEvaluation k B hS hK b 0) ≫ l)
      ((fieldPoint k B hS hK b).class B (Spec (.of k)) hS _) ∈ W := by
  obtain ⟨V, hV, hmem⟩ := Space.exists_isClosed_schemePoint_mem_iff B (Spec (.of k)) hS
    (polynomialObject k B hS hK b)
    (Space.pointsMap B (Spec (.of k)) hS _ l ⁻¹' W)
    (hW.preimage (Space.continuous_pointsMap B (Spec (.of k)) hS l))
  have hall : V = Set.univ := by
    refine eq_univ_of_isClosed_of_forall_int_translate_mem a V hV fun n ↦ ?_
    exact (hmem (Space.FieldValuedPoint.map B (Spec (.of k)) hS _
      (yoneda.map (polynomialEvaluation k B hS hK b (a + n))) (fieldPoint k B hS hK b))).mp (h n)
  refine (hmem (Space.FieldValuedPoint.map B (Spec (.of k)) hS _
    (yoneda.map (polynomialEvaluation k B hS hK b 0)) (fieldPoint k B hS hK b))).mpr ?_
  rw [hall]
  trivial

/-! #### The polynomial chart and the zero section of the affine line -/

section Chart

variable (hU : B.Contains (affineLine k).left)

/-- The tautological `K[x]`-point of the affine line over `Spec k`, out of the affine line over
a field point `Spec K` of the site: it sends the standard coordinate to the indeterminate. -/
private noncomputable def polynomialToLine {K : Type u} [Field K]
    (hK : B.Contains (Spec (.of K))) (b : Spec (.of K) ⟶ Spec (.of k)) :
    polynomialObject k B hS hK b ⟶ siteAffineLine k B hS hU :=
  Over.homMk (⟨AffineSpace.homOfVector
      (Spec.map (CommRingCat.ofHom (Polynomial.C : K →+* Polynomial K)) ≫ b)
      (fun _ ↦ (Scheme.ΓSpecIso (.of (Polynomial K))).inv Polynomial.X)⟩)
    (ObjectProperty.hom_ext _ (AffineSpace.homOfVector_over _ _))

/-- The zero section of the affine line over `Spec k`, as a morphism out of the terminal object
of the big fppf site over `Spec k`. -/
private noncomputable def zeroSectionLine :
    (Over.mk (𝟙 (B.obj hS)) : BigFppfOver B (Spec (.of k)) hS) ⟶ siteAffineLine k B hS hU :=
  Over.homMk (⟨AffineSpace.homOfVector (𝟙 _) (fun _ ↦ 0)⟩)
    (ObjectProperty.hom_ext _ (AffineSpace.homOfVector_over _ _))

/-- Translating the standard coordinate of a `K`-point `a` of the affine line by an integer `n`
is evaluating the tautological `K[x]`-point at `a + n`. -/
private theorem polynomialEvaluation_comp_polynomialToLine {K : Type u} [Field K]
    (hK : B.Contains (Spec (.of K))) (b : Spec (.of K) ⟶ Spec (.of k))
    (a : fieldObject k B hS hK b ⟶ siteAffineLine k B hS hU) (n : ℤ) :
    (Over.post B.inclusion).map
      (polynomialEvaluation k B hS hK b
        ((Scheme.ΓSpecIso (.of K)).hom
          (a.left.hom.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit)) + n) ≫
        polynomialToLine k B hS hU hK b) =
      (Over.post B.inclusion).map a ≫
        (translationAction k (Multiplicative.ofAdd n)).asIso.hom := by
  apply Over.OverMorphism.ext
  apply AffineSpace.hom_ext
  · exact (Over.w _).trans (Over.w _).symm
  · intro i
    cases i
    set f : Spec (.of K) ⟶ AffineSpace PUnit.{u + 1} (Spec (.of k)) := a.left.hom with hf
    set v : Γ(Spec (.of K), ⊤) := f.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit) with hv
    set c : K := (Scheme.ΓSpecIso (.of K)).hom v + (n : K) with hc
    change (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom c)) ≫
      AffineSpace.homOfVector
        (Spec.map (CommRingCat.ofHom (Polynomial.C : K →+* Polynomial K)) ≫ b)
        (fun _ ↦ (Scheme.ΓSpecIso (.of (Polynomial K))).inv Polynomial.X)).appTop
          (AffineSpace.coord (Spec (.of k)) PUnit.unit) =
      (f ≫ (translationAction k (Multiplicative.ofAdd n)).asIso.hom.left).appTop
        (AffineSpace.coord (Spec (.of k)) PUnit.unit)
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      AffineSpace.homOfVector_appTop_coord]
    calc
      _ = (Scheme.ΓSpecIso (.of K)).inv ((Polynomial.evalRingHom c) Polynomial.X) := by
        rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply,
          CommRingCat.ofHom_apply]
      _ = v + (n : Γ(Spec (.of K), ⊤)) := by
        simp only [Polynomial.coe_evalRingHom, Polynomial.eval_X, hc, map_add, map_intCast]
        exact congrArg (fun t ↦ t + (n : Γ(Spec (.of K), ⊤)))
          ((Scheme.ΓSpecIso (.of K)).hom_inv_id_apply v)
      _ = _ := by
        have h := congrArg (fun t : Γ(AffineSpace PUnit.{u + 1} (Spec (.of k)), ⊤) ↦ f.appTop t)
          (translationAction_apply k n)
        simpa only [map_add, map_intCast] using h.symm

/-- Evaluating the tautological `K[x]`-point of the affine line at zero is the zero section. -/
private theorem polynomialEvaluation_zero_comp_polynomialToLine {K : Type u} [Field K]
    (hK : B.Contains (Spec (.of K))) (b : Spec (.of K) ⟶ Spec (.of k)) :
    polynomialEvaluation k B hS hK b 0 ≫ polynomialToLine k B hS hU hK b =
      Over.mkIdTerminal.from (fieldObject k B hS hK b) ≫ zeroSectionLine k B hS hU := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Over.mkIdTerminal_from_left]
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : K))) ≫
      AffineSpace.homOfVector
        (Spec.map (CommRingCat.ofHom (Polynomial.C : K →+* Polynomial K)) ≫ b)
        (fun _ ↦ (Scheme.ΓSpecIso (.of (Polynomial K))).inv Polynomial.X) =
    b ≫ AffineSpace.homOfVector (𝟙 _) (fun _ : PUnit.{u + 1} ↦ 0)
  apply AffineSpace.hom_ext
  · simp only [Category.assoc, AffineSpace.homOfVector_over, Category.comp_id]
    rw [← Category.assoc, specMap_evalRingHom_comp_specMap_C, Category.id_comp]
  · intro i
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      AffineSpace.homOfVector_appTop_coord, map_zero]
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply,
      CommRingCat.ofHom_apply]
    simp only [Polynomial.coe_evalRingHom, Polynomial.eval_X, map_zero]

/-! #### The quotient of the affine line by the integer translations -/

variable [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)]

/-- **Stacks 02Z7.** The graph relation of the integer translation action, as a pre-relation on
the affine line read inside the big fppf site over `Spec k`. -/
private noncomputable abbrev siteTranslationRelation :
    PreRelation
      (Space.actionRelationScheme
        (Space.underlyingOver B hS (siteAffineLine k B hS hU)) (Multiplicative ℤ))
      (Space.underlyingOver B hS (siteAffineLine k B hS hU)) :=
  Space.actionRelation (Space.underlyingOver B hS (siteAffineLine k B hS hU))
    (Multiplicative ℤ) (translationAction k)

/-- The chart of the translation quotient: the canonical morphism to `𝔸¹_k/ℤ` from the presheaf
represented by the affine line in the big fppf site over `Spec k`. -/
private noncomputable abbrev translationChart :
    yoneda.obj (siteAffineLine k B hS hU) ⟶ translationQuotient k B hS hU :=
  quotientChart (BigFppfOver.topology B (Spec (.of k)) hS) (Over.post B.inclusion)
    (siteAffineLine k B hS hU) (siteTranslationRelation k B hS hU)

/-- The chart of the translation quotient is surjective on the points of Stacks 03BU.

The chart of a quotient sheaf is locally surjective with no hypothesis at all, by
`Stacks.Groupoids.isLocallySurjective_quotientChart`; in particular this needs none of the
effective fppf descent of Stacks 0265 that the representability of the chart needs. -/
private theorem surjective_pointsMap_translationChart :
    Function.Surjective (Space.pointsMap B (Spec (.of k)) hS _ (translationChart k B hS hU)) :=
  Space.surjective_pointsMap_of_isLocallySurjective B (Spec (.of k)) hS _
    (isLocallySurjective_quotientChart _ _ _ _)

/-- Two morphisms to the affine line differing by an integer translation have the same image in
the translation quotient: they are the target and the source of a point of the graph relation,
namely the first one read in the copy of the affine line indexed by that integer. -/
private theorem translationChart_app_eq_of_translate
    {T : BigFppfOver B (Spec (.of k)) hS} (f g : T ⟶ siteAffineLine k B hS hU) (n : ℤ)
    (hg : (Over.post B.inclusion).map g = (Over.post B.inclusion).map f ≫
      (translationAction k (Multiplicative.ofAdd n)).asIso.hom) :
    (translationChart k B hS hU).app (Opposite.op T) g =
      (translationChart k B hS hU).app (Opposite.op T) f := by
  have ht : Sigma.ι (fun _ : Multiplicative ℤ ↦
        Space.underlyingOver B hS (siteAffineLine k B hS hU)) (Multiplicative.ofAdd n) ≫
      (siteTranslationRelation k B hS hU).target =
        (translationAction k (Multiplicative.ofAdd n)).asIso.hom := by
    dsimp only [siteTranslationRelation, Space.actionRelation, PreRelation.target,
      Space.actionRelationTarget]
    rw [prod.lift_fst]
    exact Sigma.ι_comp_desc _ _
  have hs : Sigma.ι (fun _ : Multiplicative ℤ ↦
        Space.underlyingOver B hS (siteAffineLine k B hS hU)) (Multiplicative.ofAdd n) ≫
      (siteTranslationRelation k B hS hU).source = 𝟙 _ := by
    dsimp only [siteTranslationRelation, Space.actionRelation, PreRelation.source,
      Space.actionRelationSource]
    rw [prod.lift_snd]
    exact Sigma.ι_comp_desc _ _
  refine quotientChart_app_eq_of_rel _ _ _ _
    ⟨(Over.post B.inclusion).map f ≫ Sigma.ι (fun _ : Multiplicative ℤ ↦
      Space.underlyingOver B hS (siteAffineLine k B hS hU)) (Multiplicative.ofAdd n), ?_, ?_⟩
  · rw [Category.assoc, ht]
    exact hg.symm
  · rw [Category.assoc, hs, Category.comp_id]

/-- **Stacks 03IV.** The structure morphism of the quotient `𝔸¹_k/ℤ` of Stacks 02Z7, the unique
morphism to the terminal object `Spec k` of the big fppf site over `Spec k`. -/
@[stacks 03IV "the structure morphism"]
noncomputable def structureMap :
    translationQuotient k B hS hU ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS))) :=
  (Space.yonedaMkIdTerminal B (Spec (.of k)) hS).from _

/-- Every base change of the structure morphism of the translation quotient along a morphism
from an algebraic space is closed. -/
private theorem isClosedMorphism_pullback_fst_structureMap [CharZero k]
    (Z : (BigFppfOver B (Spec (.of k)) hS)ᵒᵖ ⥤ Type u)
    (g : Z ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS)))) :
    Space.IsClosedMorphism B (Spec (.of k)) hS (pullback.fst g (structureMap k B hS hU)) := by
  let X := translationQuotient k B hS hU
  let P := pullback g (structureMap k B hS hU)
  let π : P ⟶ Z := pullback.fst _ _
  let τ : P ⟶ X := pullback.snd _ _
  let q := translationChart k B hS hU
  let z := yoneda.map (zeroSectionLine k B hS hU) ≫ q
  let s : Z ⟶ P := pullback.lift (𝟙 Z) (g ≫ z)
    ((Space.yonedaMkIdTerminal B (Spec (.of k)) hS).hom_ext _ _)
  have hsπ : s ≫ π = 𝟙 Z := pullback.lift_fst _ _ _
  refine Space.isClosedMap_of_isSaturated_section
    (Space.pointsMap B (Spec (.of k)) hS P π) (Space.pointsMap B (Spec (.of k)) hS Z s)
    (Space.continuous_pointsMap B (Spec (.of k)) hS s) (fun y ↦ ?_) (fun W hW x hx ↦ ?_)
  · have h := congrFun (Space.pointsMap_comp B (Spec (.of k)) hS Z s π) y
    rw [hsπ, Space.pointsMap_id] at h
    exact h.symm
  · obtain ⟨p, rfl⟩ := Quot.exists_rep x
    obtain ⟨r, a, hr, ha⟩ := Space.exists_dominating_fieldValuedPoint_factor
      B (Spec (.of k)) hS q (surjective_pointsMap_translationChart k B hS hU) τ p
    dsimp only [Space.FieldValuedPoint.class] at hr
    rw [← hr] at hx ⊢
    let K := r.carrier
    let ρ : k →+* K := ((Scheme.ΓSpecIso (.of k)).inv ≫ r.toBase.appTop ≫
      (Scheme.ΓSpecIso (.of K)).hom).hom
    have : CharZero K := charZero_of_injective_ringHom ρ.injective
    let A := fieldObject k B hS r.contained r.toBase
    let V := polynomialObject k B hS r.contained r.toBase
    let φ : yoneda.obj A ⟶ P := yonedaEquiv.symm r.value
    let l : yoneda.obj V ⟶ P := pullback.lift
      (yoneda.map (polynomialProjection k B hS r.contained r.toBase) ≫ φ ≫ π)
      (yoneda.map (polynomialToLine k B hS hU r.contained r.toBase) ≫ q)
      ((Space.yonedaMkIdTerminal B (Spec (.of k)) hS).hom_ext _ _)
    let c : K := (Scheme.ΓSpecIso (.of K)).hom
      (a.left.hom.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit))
    have hφ : Space.pointsMap B (Spec (.of k)) hS (yoneda.obj A) φ
        ((fieldPoint k B hS r.contained r.toBase).class B (Spec (.of k)) hS _) =
          Quot.mk _ r :=
      Space.pointsMap_fieldMorphism_tautologicalPoint B (Spec (.of k)) hS P r
    have hφτ : yoneda.map a ≫ q = φ ≫ τ := by
      apply yonedaEquiv.injective
      simpa only [φ, yonedaEquiv_comp, yonedaEquiv_yoneda_map, Equiv.apply_symm_apply]
        using ha
    have heval (n : ℤ) :
        yoneda.map (polynomialEvaluation k B hS r.contained r.toBase (c + n)) ≫ l = φ := by
      apply pullback.hom_ext
      · dsimp only [l, π]
        simp only [Category.assoc, pullback.lift_fst, ← Functor.map_comp_assoc,
          polynomialEvaluation_comp_polynomialProjection]
        rw [yoneda.map_id A, Category.id_comp]
      · change _ ≫ l ≫ τ = φ ≫ τ
        rw [← hφτ]
        change _ ≫ (pullback.lift _ _ _) ≫ pullback.snd _ _ = _
        rw [pullback.lift_snd, ← Functor.map_comp_assoc]
        apply yonedaEquiv.injective
        simpa only [X, c, q, K, fieldObject, ObjectProperty.homMk,
          Space.FieldValuedPoint.siteObject, yonedaEquiv_comp, yonedaEquiv_yoneda_map] using
          translationChart_app_eq_of_translate k B hS hU a _ n
            (polynomialEvaluation_comp_polynomialToLine k B hS hU r.contained r.toBase a n)
    have heval0 : yoneda.map (polynomialEvaluation k B hS r.contained r.toBase 0) ≫ l =
        φ ≫ π ≫ s := by
      apply pullback.hom_ext
      · dsimp only [l, π, s]
        simp only [Category.assoc, pullback.lift_fst, ← Functor.map_comp_assoc,
          polynomialEvaluation_comp_polynomialProjection, Category.comp_id]
        rw [yoneda.map_id A, Category.id_comp]
      · have hb : φ ≫ π ≫ g = yoneda.map (Over.mkIdTerminal.from A) :=
          (Space.yonedaMkIdTerminal B (Spec (.of k)) hS).hom_ext _ _
        change _ ≫ l ≫ τ = φ ≫ π ≫ s ≫ τ
        dsimp only [l, s, τ]
        simp only [pullback.lift_snd]
        rw [← Functor.map_comp_assoc, polynomialEvaluation_zero_comp_polynomialToLine,
          Functor.map_comp]
        dsimp only [z]
        simpa only [Category.assoc] using congrArg (fun t ↦ t ≫
          yoneda.map (zeroSectionLine k B hS hU) ≫ q) hb.symm
    have hclosed := mem_of_isClosed_of_forall_int_translate_mem k B hS r.contained r.toBase l
      W hW c (fun n ↦ by rw [heval n]; exact hφ.symm ▸ hx)
    rw [heval0, Space.pointsMap_comp, Function.comp_apply, hφ, Space.pointsMap_comp,
      Function.comp_apply] at hclosed
    exact hclosed

/-- **Stacks 03IV.** For a field `k` of characteristic zero the structure morphism of the
quotient `𝔸¹_k/ℤ` of Stacks 02Z7 to `Spec k` is universally closed.

The source calls this a strange example because the quotient is, by Stacks 02Z7, an algebraic
space which is not a scheme. The statement needs no hypothesis beyond characteristic zero — in
particular none of the effective fppf descent of Stacks 0265, which the representability of the
quotient's chart does need. -/
@[stacks 03IV "universally closed"]
theorem universallyClosed_structureMap [CharZero k] :
    Space.UniversallyClosed B (Spec (.of k)) hS (structureMap k B hS hU) :=
  fun Z _ g ↦ isClosedMorphism_pullback_fst_structureMap k B hS hU Z g

end Chart

end AlgebraicGeometry.AffineLineTranslation

end
