module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeOfIntegralBijection
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Unramified

/-!
# Topological invariance of the étale site, on schemes and on affines (Stacks 07VW)

Let `f : X ⟶ Y` be an integral, universally injective and surjective morphism of algebraic
spaces over a scheme `S`. Stacks 05ZH asserts that base change `V ↦ X ×_Y V` is an equivalence
from the spaces-étale site of `Y` to that of `X`. This file shows that this equivalence
*restricts* to the sub-sites of schemes étale over the base (Stacks 03ED) and of affine schemes
étale over the base (Stacks 0H01): base change carries étale scheme charts to étale scheme
charts and affine ones to affine ones, and both restrictions are again equivalences of
categories.

The mathematical content is that for `V` étale over `Y` the projection `X ×_Y V ⟶ V` inherits
from `f` the properties of being integral, universally injective and surjective, so that `V` is
a scheme exactly when `X ×_Y V` is (Stacks 07VV) and `V` is affine exactly when `X ×_Y V` is
(the nontrivial direction being Stacks 07VT).

## Main definitions

* `AlgebraicGeometry.Space.smallEtalePullback`: base change on the small étale sites, the
  restriction of base change on the spaces-étale sites to the étale scheme charts.
* `AlgebraicGeometry.Space.affineEtalePullback`: base change on the affine étale sites.

## Main results

* `AlgebraicGeometry.Space.smallEtalePullbackComparisonIso` and
  `AlgebraicGeometry.Space.affineEtalePullbackInclusionIso`: the two functors above *are* the
  restrictions of the spaces-étale base change, not merely functors with the same source and
  target.
* `AlgebraicGeometry.Space.smallEtalePullback_isEquivalence`: base change is an equivalence of
  small étale sites, granted four hypotheses; a special case of
  `AlgebraicGeometry.Space.isEquivalence_smallEtalePullback` (Stacks 07VW on schemes).
* The equivalence on the affine étale sites, Stacks 07VW on affines, is
  `AlgebraicGeometry.Space.isEquivalence_affineEtalePullback`.

## Implementation notes

**What the hypotheses carry and what is proved from them.** Four hypotheses are carried, and
each of the two equivalences above carries all four:

* `hEquiv`, the conclusion of Stacks 05ZH that base change on the *spaces*-étale sites is an
  equivalence. Stacks 07VW is stated in the source as a statement *about* that equivalence —
  "with assumptions and notation as in Theorem 05ZH, the equivalence restricts" — so the
  equivalence is an input to the tag, not part of its content. The library proves Stacks 05ZH
  only for the inclusion of a first-order thickening,
  `AlgebraicGeometry.Space.isEquivalence_spacesBaseChange_of_isFirstOrderThickening`, and not
  for an arbitrary integral, universally injective and surjective morphism, so the general
  equivalence cannot be supplied here.
* `h09YA`, `h07SQ` and `hFinitePresentation`, the three hypotheses of Stacks 07VT carried
  unchanged from `AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_universallyClosed`
  and from `AlgebraicGeometry.Space.isRepresentable_of_isIntegralHom_of_bijective`. None is the
  universally quantified form of any conclusion here: the first two conclude about inverse
  systems and the third about affineness of the target of a finite morphism of finite
  presentation.

Everything else is proved. The restriction of the functor to schemes needs no hypothesis beyond
integrality of `f`: the projection `X ×_Y V ⟶ V` is integral by Stacks 03ZS, so a scheme chart
`V` of `Y` has a scheme base change by the implication of Stacks 07VV from the target,
`AlgebraicGeometry.Space.isRepresentable_of_isIntegralHom`, which is unconditional. The
restriction to affines likewise needs only integrality: an integral morphism with affine target
has affine source, because the defining affine-local representative of the morphism over the
target itself is then a base change along an isomorphism.

The two converses are where the carried hypotheses are used. That a scheme base change forces a
scheme chart is the implication of Stacks 07VV from the source,
`AlgebraicGeometry.Space.isRepresentable_of_isIntegralHom_of_bijective`, applied to the
projection — which is bijective on points because `f` is universally injective (Stacks 03MW,
`AlgebraicGeometry.Space.universallyInjective_of_isPullback`, followed by
`AlgebraicGeometry.Space.injective_pointsMap_of_universallyInjective`) and surjective (Stacks
03MH, `AlgebraicGeometry.Space.isSurjective_of_isPullback`). That an affine base change forces
an affine chart is Stacks 07VT applied to the same projection, which is surjective and
universally closed, the latter by Stacks 0415.

**How the functors are built.** The comparison functor of Stacks 03G1 from the small étale site
to the spaces-étale site is fully faithful, so a functor into the small étale site is determined
by a functor into the spaces-étale site landing in the essential image; that is
`CategoryTheory.Functor.essImage.liftFunctor`, and
`CategoryTheory.Functor.essImage.liftFunctorCompIso` is the comparison isomorphism exhibiting
the lift as a restriction. Membership in the essential image of the comparison is exactly
representability of the underlying presheaf,
`AlgebraicGeometry.Space.essImage_comparisonFunctor_iff`, which is what turns Stacks 07VV into a
statement about the sites. The affine étale site is a full subcategory of the small étale one,
so there the lift is `CategoryTheory.ObjectProperty.lift`.

Both equivalences then follow from one category-theoretic step,
`AlgebraicGeometry.Space.isEquivalence_of_restriction`: a functor whose composition with a fully
faithful functor is isomorphic to an equivalence precomposed with a fully faithful functor is
itself fully faithful, and it is essentially surjective as soon as the equivalence reflects
membership in the two essential images. Full faithfulness is therefore free, and only essential
surjectivity uses the two converses above.

## References

* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03MH](https://stacks.math.columbia.edu/tag/03MH)
* [Stacks Project, Tag 03MW](https://stacks.math.columbia.edu/tag/03MW)
* [Stacks Project, Tag 03ZS](https://stacks.math.columbia.edu/tag/03ZS)
* [Stacks Project, Tag 0415](https://stacks.math.columbia.edu/tag/0415)
* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 07VT](https://stacks.math.columbia.edu/tag/07VT)
* [Stacks Project, Tag 07VV](https://stacks.math.columbia.edu/tag/07VV)
* [Stacks Project, Tag 07VW](https://stacks.math.columbia.edu/tag/07VW)
* [Stacks Project, Tag 0H01](https://stacks.math.columbia.edu/tag/0H01)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### Restricting an equivalence along two fully faithful functors -/

/-- **A restriction of an equivalence along fully faithful functors is an equivalence.** Let
`G : C ⥤ E` be an equivalence, let `K : A ⥤ C` and `L : D ⥤ E` be fully faithful, and let
`F : A ⥤ D` satisfy `F ⋙ L ≅ K ⋙ G`. If `G` reflects membership in the essential images — an
object of `C` whose image under `G` lies in the essential image of `L` lies in the essential
image of `K` — then `F` is an equivalence.

Full faithfulness of `F` is formal: `F ⋙ L` is fully faithful because `K ⋙ G` is, and a functor
whose composition with a faithful functor is full is full. Essential surjectivity is where the
hypothesis enters: an object `W` of `D` has a `G`-preimage `V` of `L.obj W`, which exhibits
`G.obj V` in the essential image of `L`, hence `V` in the essential image of `K`, say
`K.obj U ≅ V`; chasing the isomorphisms gives `L.obj (F.obj U) ≅ L.obj W`, and `L` is fully
faithful. -/
theorem isEquivalence_of_restriction {A C D E : Type*} [Category* A] [Category* C]
    [Category* D] [Category* E] (K : A ⥤ C) (L : D ⥤ E) (F : A ⥤ D) (G : C ⥤ E)
    [K.Full] [K.Faithful] [L.Full] [L.Faithful] [G.IsEquivalence]
    (e : F ⋙ L ≅ K ⋙ G) (h : ∀ V, L.essImage (G.obj V) → K.essImage V) : F.IsEquivalence := by
  have : (F ⋙ L).Full := Functor.Full.of_iso e.symm
  have : (F ⋙ L).Faithful := Functor.Faithful.of_iso e.symm
  have : F.Full := Functor.Full.of_comp_faithful F L
  have : F.Faithful := Functor.Faithful.of_comp F L
  have : F.EssSurj := ⟨fun W ↦ by
    obtain ⟨U, ⟨j⟩⟩ := h (G.objPreimage (L.obj W))
      ⟨W, ⟨(G.objObjPreimageIso (L.obj W)).symm⟩⟩
    exact ⟨U, ⟨L.preimageIso (e.app U ≪≫ G.mapIso j ≪≫
      G.objObjPreimageIso (L.obj W))⟩⟩⟩
  exact ⟨inferInstance, inferInstance, inferInstance⟩

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The inclusion of the algebraic spaces over `S` into the presheaves on the big fppf site of
`S`. -/
private abbrev spaceInclusion :
    AlgebraicSpaces B S hS ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F)

/-- The presheaf underlying an object of the spaces-étale site of `X`, functorially. -/
private abbrev spacesEtalePresheaf (X : AlgebraicSpaces B S hS) :
    SpacesEtale B S hS X ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  SpacesEtale.toSpaces B S hS X ⋙ spaceInclusion B S hS

/-! ### The essential image of the comparison functor of Stacks 03G1 -/

/-- **An algebraic space étale over `X` is in the essential image of the small étale site
exactly when it is a scheme.** The comparison functor of Stacks 03G1 sends a chart to the
presheaf it represents, so its essential image consists of the objects of the spaces-étale site
whose underlying presheaf is representable; conversely a representable such object is the étale
chart given by any representing object, the chart being étale because it is an isomorphism
followed by the étale structure morphism. -/
theorem essImage_comparisonFunctor_iff (X : AlgebraicSpaces B S hS)
    (V : SpacesEtale B S hS X) :
    (comparisonFunctor B S hS X).essImage V ↔ V.1.left.1.IsRepresentable := by
  constructor
  · rintro ⟨U, ⟨e⟩⟩
    have hrep : ((spacesEtalePresheaf B S hS X).obj
        ((comparisonFunctor B S hS X).obj U)).IsRepresentable := by
      change (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U)).IsRepresentable
      infer_instance
    exact isRepresentable_of_natIso _ ((spacesEtalePresheaf B S hS X).mapIso e)
  · intro hV
    have _ : V.1.left.1.IsRepresentable := hV
    set e : yoneda.obj V.1.left.1.reprX ≅ V.1.left.1 := V.1.left.1.reprW with he
    have hchart : IsEtaleChart B S hS X.1
        (CostructuredArrow.mk (e.hom ≫ V.1.hom.hom)) :=
      presheaf_etale_of_isEtale B S hS
        (isEtale_comp B S hS (isEtale_of_isIso B S hS e.hom) V.2)
    refine ⟨⟨CostructuredArrow.mk (e.hom ≫ V.1.hom.hom), hchart⟩,
      ⟨ObjectProperty.isoMk _ (Over.isoMk (ObjectProperty.isoMk _ e) ?_)⟩⟩
    exact ObjectProperty.hom_ext _ rfl

/-! ### The essential image of the inclusion of the affine étale site -/

/-- **An étale chart is in the essential image of the affine étale site exactly when it is
affine.** The inclusion of a full subcategory has as essential image the objects isomorphic to
one of its own, and an étale chart isomorphic to an affine one has isomorphic underlying
scheme. -/
theorem essImage_affineEtaleInclusion_iff (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (U : SmallEtale B S hS F) :
    (AffineEtale.inclusion B S hS F).essImage U ↔ IsAffineChart B S hS F U := by
  constructor
  · rintro ⟨V, ⟨e⟩⟩
    exact (IsAffine.iff_of_isIso
      (((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS)).map e.hom)).mp V.2
  · exact fun hU ↦ ⟨⟨U, hU⟩, ⟨Iso.refl _⟩⟩

/-! ### The projection of a base change along `f` -/

variable {X Y : AlgebraicSpaces B S hS}

/-- The cartesian square of presheaves exhibiting the base change of an object of the
spaces-étale site of `Y` as a fibre product over `f`. -/
private theorem isPullback_spacesBaseChange_projection (f : X ⟶ Y)
    (V : SpacesEtale B S hS Y) :
    IsPullback ((spacesBaseChange B S hS f).projection.app V).hom
      ((spacesBaseChange B S hS f).functor.obj V).1.hom.hom V.1.hom.hom f.hom :=
  AlgebraicSpaces.isPullback_hom B S hS ((spacesBaseChange B S hS f).isPullback V)

/-- **The projection of a base change is integral**, by Stacks 03ZS. -/
private theorem isIntegralHom_spacesBaseChange_projection (f : X ⟶ Y)
    (hf : IsIntegralHom B S hS f.hom) (V : SpacesEtale B S hS Y) :
    IsIntegralHom B S hS ((spacesBaseChange B S hS f).projection.app V).hom :=
  isIntegralHom_of_isPullback B S hS
    (isPullback_spacesBaseChange_projection B S hS f V).flip hf

/-- **The projection of a base change is bijective on points**, by Stacks 03MW and Stacks
03MH. -/
private theorem bijective_pointsMap_spacesBaseChange_projection (f : X ⟶ Y)
    (hinj : UniversallyInjective B S hS f.hom) (hsurj : IsSurjective B S hS f.hom)
    (V : SpacesEtale B S hS Y) :
    Function.Bijective (pointsMap B S hS
      ((spacesBaseChange B S hS f).functor.obj V).1.left.1
      ((spacesBaseChange B S hS f).projection.app V).hom) := by
  refine ⟨injective_pointsMap_of_universallyInjective B S hS V.1.left.2 ?_,
    isSurjective_of_isPullback B S hS ((spacesBaseChange B S hS f).isPullback V).flip hsurj⟩
  exact universallyInjective_of_isPullback B S hS X.2 V.1.left.2 Y.2 f.hom V.1.hom.hom hinj
    (isPullback_spacesBaseChange_projection B S hS f V)

/-! ### Being a scheme passes both ways along the projection -/

/-- An integral morphism of algebraic spaces over `S` with affine target has affine source: the
affine-local representative of the morphism over an affine presentation of the target is a base
change along an isomorphism, hence an isomorphism. -/
private theorem isAffineSpace_of_isIntegralHom {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : F ⟶ G) (hg : IsIntegralHom B S hS g) (hG : IsAffineSpace B S hS G) :
    IsAffineSpace B S hS F := by
  obtain ⟨T, hT, ⟨e⟩⟩ := hG
  obtain ⟨W, p, q, sq, hW, -⟩ := hg T hT e.inv
  have _ : IsIso q := IsPullback.isIso_fst_of_isIso sq
  exact ⟨W, hW, ⟨(asIso q).symm⟩⟩

/-- Affineness of a presheaf on the big fppf site of `S` transports along an isomorphism. -/
private theorem isAffineSpace_of_iso {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G)
    (hF : IsAffineSpace B S hS F) : IsAffineSpace B S hS G := by
  obtain ⟨T, hT, ⟨i⟩⟩ := hF
  exact ⟨T, hT, ⟨e.symm ≪≫ i⟩⟩

/-- **A base change of a scheme chart is a scheme chart**, by the implication of Stacks 07VV
from the target, which carries no hypothesis beyond integrality. -/
private theorem isRepresentable_spacesBaseChange (f : X ⟶ Y)
    (hf : IsIntegralHom B S hS f.hom) (V : SpacesEtale B S hS Y)
    (hV : V.1.left.1.IsRepresentable) :
    ((spacesBaseChange B S hS f).functor.obj V).1.left.1.IsRepresentable :=
  isRepresentable_of_isIntegralHom B S hS
    ((spacesBaseChange B S hS f).functor.obj V).1.left.2
    ((spacesBaseChange B S hS f).projection.app V).hom
    (isIntegralHom_spacesBaseChange_projection B S hS f hf V) hV

/-- **The base change of a scheme is a scheme**, in the sense of the objects of the sites: the
étale scheme charts of `Y` are carried by base change into the essential image of the comparison
functor of `X`. -/
theorem essImage_comparisonFunctor_spacesBaseChange (f : X ⟶ Y)
    (hf : IsIntegralHom B S hS f.hom) (U : SmallEtale B S hS Y.1) :
    (comparisonFunctor B S hS X).essImage
      ((spacesBaseChange B S hS f).functor.obj ((comparisonFunctor B S hS Y).obj U)) :=
  (essImage_comparisonFunctor_iff B S hS X _).2
    (isRepresentable_spacesBaseChange B S hS f hf _
      ((essImage_comparisonFunctor_iff B S hS Y _).1
        ((comparisonFunctor B S hS Y).obj_mem_essImage U)))

/-! ### The base-change functor on the small étale sites -/

/-- **Stacks 07VW, the base-change functor on the étale schemes.** For an integral morphism
`f : X ⟶ Y` of algebraic spaces over `S`, base change `V ↦ X ×_Y V` carries the small étale
site of `Y` to that of `X`.

It is the restriction of base change on the spaces-étale sites along the fully faithful
comparison functors of Stacks 03G1 — see
`AlgebraicGeometry.Space.smallEtalePullbackComparisonIso` — which exists because the base change
of a scheme étale over `Y` is a scheme, by the implication of Stacks 07VV from the target. -/
@[stacks 07VW "the base-change functor on the étale schemes, which needs only integrality of \
`f`; the two equivalences are stated separately"]
noncomputable def smallEtalePullback (f : X ⟶ Y) (hf : IsIntegralHom B S hS f.hom) :
    SmallEtale B S hS Y.1 ⥤ SmallEtale B S hS X.1 :=
  letI := comparisonFunctor_full B S hS X
  letI := comparisonFunctor_faithful B S hS X
  Functor.essImage.liftFunctor
    (comparisonFunctor B S hS Y ⋙ (spacesBaseChange B S hS f).functor)
    (comparisonFunctor B S hS X) (essImage_comparisonFunctor_spacesBaseChange B S hS f hf)

/-- **Stacks 07VW, canonicity of the base-change functor on the étale schemes.**
`AlgebraicGeometry.Space.smallEtalePullback` is the restriction of base change on the
spaces-étale sites: composing it with the comparison functor of `X` recovers base change applied
to the comparison functor of `Y`. -/
@[stacks 07VW "the restriction to the étale schemes is the spaces-étale base change"]
noncomputable def smallEtalePullbackComparisonIso (f : X ⟶ Y)
    (hf : IsIntegralHom B S hS f.hom) :
    smallEtalePullback B S hS f hf ⋙ comparisonFunctor B S hS X ≅
      comparisonFunctor B S hS Y ⋙ (spacesBaseChange B S hS f).functor :=
  letI := comparisonFunctor_full B S hS X
  letI := comparisonFunctor_faithful B S hS X
  Functor.essImage.liftFunctorCompIso
    (comparisonFunctor B S hS Y ⋙ (spacesBaseChange B S hS f).functor)
    (comparisonFunctor B S hS X) (essImage_comparisonFunctor_spacesBaseChange B S hS f hf)

/-- The presheaf underlying the base change of an étale chart is the presheaf underlying the
base change of the algebraic space it represents, up to isomorphism. -/
private theorem isAffineSpace_smallEtalePullback_iff (f : X ⟶ Y)
    (hf : IsIntegralHom B S hS f.hom) (U : SmallEtale B S hS Y.1) :
    IsAffineSpace B S hS ((comparisonFunctor B S hS X).obj
        ((smallEtalePullback B S hS f hf).obj U)).1.left.1 ↔
      IsAffineSpace B S hS ((spacesBaseChange B S hS f).functor.obj
        ((comparisonFunctor B S hS Y).obj U)).1.left.1 :=
  let e := (spacesEtalePresheaf B S hS X).mapIso
    ((smallEtalePullbackComparisonIso B S hS f hf).app U)
  ⟨isAffineSpace_of_iso B S hS e, isAffineSpace_of_iso B S hS e.symm⟩

/-- **Affineness of an étale chart is equivalent to affineness of the underlying algebraic
space.** An affine étale chart represents an affine algebraic space, and a representable affine
algebraic space has affine representing object. -/
theorem isAffineSpace_comparisonFunctor_iff (X : AlgebraicSpaces B S hS)
    (U : SmallEtale B S hS X.1) :
    IsAffineSpace B S hS ((comparisonFunctor B S hS X).obj U).1.left.1 ↔
      IsAffineChart B S hS X.1 U := by
  constructor
  · intro hU
    obtain ⟨T, hT, ⟨e⟩⟩ := hU
    have e' : yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U) ≅ yoneda.obj T := e
    exact (IsAffine.iff_of_isIso
      ((BigFppfOver.toScheme B S hS).map (yoneda.preimageIso e').hom)).mpr hT
  · intro hU
    exact isAffineSpace_yoneda B S hS ((SmallEtale.toOver B S hS X.1).obj U) hU

/-! ### Affineness passes both ways along the projection -/

/-- **A base change of an affine étale chart is an affine étale chart.** The projection is
integral, and an integral morphism with affine target has affine source. -/
theorem isAffineChart_smallEtalePullback (f : X ⟶ Y)
    (hf : IsIntegralHom B S hS f.hom) (U : SmallEtale B S hS Y.1)
    (hU : IsAffineChart B S hS Y.1 U) :
    IsAffineChart B S hS X.1 ((smallEtalePullback B S hS f hf).obj U) := by
  refine (isAffineSpace_comparisonFunctor_iff B S hS X _).1
    ((isAffineSpace_smallEtalePullback_iff B S hS f hf U).2 ?_)
  exact isAffineSpace_of_isIntegralHom B S hS
    ((spacesBaseChange B S hS f).projection.app _).hom
    (isIntegralHom_spacesBaseChange_projection B S hS f hf _)
    ((isAffineSpace_comparisonFunctor_iff B S hS Y U).2 hU)

/-! ### The base-change functor on the affine étale sites -/

/-- **Stacks 07VW, the base-change functor on the affine étale schemes.** For an integral
morphism `f : X ⟶ Y` of algebraic spaces over `S`, base change `V ↦ X ×_Y V` carries the affine
étale site of `Y` to that of `X`: a base change of an affine chart is affine, because the
projection is integral and an integral morphism with affine target has affine source. -/
@[stacks 07VW "the base-change functor on the affine étale schemes, which needs only \
integrality of `f`; the two equivalences are stated separately"]
noncomputable def affineEtalePullback (f : X ⟶ Y) (hf : IsIntegralHom B S hS f.hom) :
    AffineEtale B S hS Y.1 ⥤ AffineEtale B S hS X.1 :=
  (IsAffineChart B S hS X.1).lift
    (AffineEtale.inclusion B S hS Y.1 ⋙ smallEtalePullback B S hS f hf)
    (fun U ↦ isAffineChart_smallEtalePullback B S hS f hf U.1 U.2)

/-- **Stacks 07VW, canonicity of the base-change functor on the affine étale schemes.**
`AlgebraicGeometry.Space.affineEtalePullback` is the restriction of
`AlgebraicGeometry.Space.smallEtalePullback` to the affine charts. -/
@[stacks 07VW "the restriction to the affine étale schemes is the small étale base change"]
noncomputable def affineEtalePullbackInclusionIso (f : X ⟶ Y)
    (hf : IsIntegralHom B S hS f.hom) :
    affineEtalePullback B S hS f hf ⋙ AffineEtale.inclusion B S hS X.1 ≅
      AffineEtale.inclusion B S hS Y.1 ⋙ smallEtalePullback B S hS f hf :=
  ObjectProperty.liftCompιIso (IsAffineChart B S hS X.1)
    (AffineEtale.inclusion B S hS Y.1 ⋙ smallEtalePullback B S hS f hf)
    (fun U ↦ isAffineChart_smallEtalePullback B S hS f hf U.1 U.2)

/-! ### The two equivalences -/

/-- Base change on the small étale sites is an equivalence, granted the four extra hypotheses
`hEquiv`, `h09YA`, `h07SQ` and `hFinitePresentation`. This is a special case of
`AlgebraicGeometry.Space.isEquivalence_smallEtalePullback`, which needs none of them; that full
version is not available in this module, since its own module imports this one. -/
theorem smallEtalePullback_isEquivalence (f : X ⟶ Y) (hf : IsIntegralHom B S hS f.hom)
    (hinj : UniversallyInjective B S hS f.hom) (hsurj : IsSurjective B S hS f.hom)
    (hEquiv : (spacesBaseChange B S hS f).functor.IsEquivalence)
    (h09YA : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' → IsIntegralHom B S hS g →
      IsQuasiCompactSpace B S hS Y' →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y' →
      IntegralFiniteSystem B S hS g)
    (h07SQ : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B S hS B.contains_terminal I),
      IsAffineSpace B S hS D.limitCone.pt →
      ∃ i : I, D.base ≤ i ∧ IsAffineSpace B S hS (D.system.obj (Opposite.op i)))
    (hFinitePresentation : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' → IsFinite B S hS g →
      IsFinitePresentation B S hS g → IsSurjective B S hS g → IsAffineSpace B S hS X' →
      IsAffineSpace B S hS Y') :
    (smallEtalePullback B S hS f hf).IsEquivalence := by
  have := comparisonFunctor_full B S hS X
  have := comparisonFunctor_faithful B S hS X
  have := comparisonFunctor_full B S hS Y
  have := comparisonFunctor_faithful B S hS Y
  have := hEquiv
  refine isEquivalence_of_restriction (comparisonFunctor B S hS Y)
    (comparisonFunctor B S hS X) _ ((spacesBaseChange B S hS f).functor)
    (smallEtalePullbackComparisonIso B S hS f hf) fun V hV ↦ ?_
  refine (essImage_comparisonFunctor_iff B S hS Y V).2 ?_
  exact isRepresentable_of_isIntegralHom_of_bijective B S hS
    ((spacesBaseChange B S hS f).functor.obj V).1.left.2 V.1.left.2
    ((spacesBaseChange B S hS f).projection.app V).hom
    (isIntegralHom_spacesBaseChange_projection B S hS f hf V)
    (bijective_pointsMap_spacesBaseChange_projection B S hS f hinj hsurj V)
    ((essImage_comparisonFunctor_iff B S hS X _).1 hV) h09YA h07SQ hFinitePresentation

end AlgebraicGeometry.Space

end
