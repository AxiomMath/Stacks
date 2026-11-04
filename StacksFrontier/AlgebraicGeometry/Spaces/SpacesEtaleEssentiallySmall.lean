module

public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.KernelPair
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleToposMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleToposRingUniverse

/-!
# The spaces-étale site is essentially small

The spaces-étale site of an algebraic space `X` over a scheme `S` of universe `u` has its
objects in `Type (u + 1)`: they are the algebraic spaces étale over `X`, and an algebraic space
is a presheaf on the big fppf site of `S`, whose objects already live in `Type (u + 1)`. The
site is nevertheless *essentially small* at `u`, and this file proves it.

The reason is that an algebraic space is not an arbitrary presheaf: it is the quotient, in fppf
sheaves, of a scheme atlas by the étale equivalence relation given by the kernel pair of the
atlas (Stacks 0262, part (3), `AlgebraicGeometry.Space.isCoequalizer_of_surjectiveEtale`). Both
the atlas and its relation scheme are objects of the big fppf site of `S`, which is essentially
small at `u` by the size cutoff (Stacks 000J); so an algebraic space is determined up to
isomorphism by a triple `(R, U, s, t : R ⇉ U)` of data in a `Type u` category, and the
isomorphism classes of algebraic spaces are indexed by a type in `Type u`.

Essential smallness of the spaces-étale site is the input the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleToposRingUniverse` name as missing, and the
second half of this file spends it: it descends the morphism of small étale topoi of Stacks
03G2, part (3) from `Type (u + 1)` to `Type u`, the universe of the structure rings, which is
the universe at which a ringed topos in the sense of Stacks 01D3 declares its underlying topos.

## Main definitions

* `AlgebraicGeometry.Space.PresentationData` is the `Type u` of presentation data — two objects
  of a small model of the big fppf site of `S` and two morphisms between them — and
  `AlgebraicGeometry.Space.presentationModel` is the fppf sheaf it presents.
* `AlgebraicGeometry.Space.smallModelTopology` and
  `AlgebraicGeometry.Space.smallModelBaseChange` transport the spaces-étale site and its
  base-change functor to the small models.
* `AlgebraicGeometry.Space.spacesToposMorphismTypeU`,
  `AlgebraicGeometry.Space.smallEtaleToposEquivTypeU` and
  `AlgebraicGeometry.Space.smallToposMorphismTypeU` are the spaces-étale morphism of topoi, the
  comparison equivalence of Stacks 03G1 and the induced morphism of small étale topoi, all for
  sheaves of sets valued in `Type u`.

## Main results

* `AlgebraicGeometry.Space.essentiallySmall_isAlgebraicSpace`: being an algebraic space over `S`
  is an essentially small property of presheaves on the big fppf site of `S`.
* `AlgebraicGeometry.Space.essentiallySmall_algebraicSpaces` and
  `AlgebraicGeometry.Space.essentiallySmall_spacesEtale`: the category of algebraic spaces over
  `S` and the spaces-étale site of an algebraic space are essentially small at `u`.
* `AlgebraicGeometry.Space.preservesFiniteLimits_sheafPullback_spacesBaseChange`: the
  spaces-étale inverse image of Stacks 03G2, part (1) is left exact on sheaves of sets valued in
  `Type u`. This is what was missing for a morphism of topoi at that universe.
* `AlgebraicGeometry.Space.smallToposMorphismTypeU_comparison` pins the descended morphism of
  topoi down: its direct image agrees, through the comparison equivalences of Stacks 03G1, with
  the spaces-étale direct image.

## Implementation notes

The reconstruction of an algebraic space from its presentation is taken from Stacks 0262, part
(3), which is stated in the strong form "the atlas is the coequalizer of its kernel pair in fppf
sheaves". Only the relation `R` has to be produced by hand: it is the represented pullback
`hsurj.rep.pullback f` of the atlas along itself, which exists because the atlas is relatively
representable, and the kernel-pair square is `hsurj.rep.isPullback'`. No size argument about `R`
is needed here — `Stacks.Groupoids.contains_left_of_mono` is not used — because the atlas is
relatively representable *into the site*, so `R` is an object of the big fppf site of `S` by
construction rather than by a cardinality bound.

The indexing type is built from `CategoryTheory.SmallModel` of the big fppf site of `S`, so the
presentation attached to an algebraic space has to be transported along the unit of
`CategoryTheory.equivSmallModel`. That transport is done on the *cofork*, by
`CategoryTheory.Limits.Cofork.isColimitOfIsos`, rather than on the atlas: moving the atlas would
require knowing that `MorphismProperty.presheaf` of surjectivity and étaleness is stable under
precomposition with an isomorphism of representables, whereas moving the cofork needs only
naturality of the unit.

Essential smallness is then fed into the universe-general comma-category instances: the slice of
the algebraic spaces over `X` is `CategoryTheory.CostructuredArrow` of the identity, which is
essentially small by `CategoryTheory.CostructuredArrow.essentiallySmall` because the algebraic
spaces are essentially small at `u` and locally small at `u`
(`AlgebraicGeometry.Space.locallySmall_algebraicSpaces`); and the spaces-étale site is a full
subcategory of that slice.

For the descent the obstruction is a universe mismatch, not a missing theorem. Left exactness of
the sheaf inverse image follows from representable flatness of the functor
(`CategoryTheory.Functor.preservesFiniteLimits_sheafPullback`, Stacks 00X5), but Mathlib proves
that only when the universe of the sheaves equals the universe of the site, because it factors
through `CategoryTheory.lan_preservesFiniteLimits_of_flat`, which is stated for small
categories. The spaces-étale sites are `Type (u + 1)` categories and the sheaves are `Type u`.
With essential smallness the whole situation moves to the small models, where the two universes
do agree: the topologies transport by `CategoryTheory.Functor.inducedTopology`, the transported
base change is continuous and representably flat, and
`AlgebraicGeometry.Space.preservesFiniteLimits_sheafPullback_smallModelBaseChange` is Stacks
00X5 applied there.

Moving the conclusion back is `CategoryTheory.Adjunction.preservesFiniteLimits_of_conjugate`,
which is pure adjunction calculus and belongs upstream in
`StacksFrontier/CategoryTheory/Sites/`; it is stated here to keep that directory untouched. The
restriction functors along the two equivalences are *equal on the nose* to the transported
direct image — `AlgebraicGeometry.Space.sheafPushforwardContinuous_smallModelBaseChange` holds
by `rfl`, being `CategoryTheory.Functor.sheafPushforwardContinuousComp` — so the only genuine
content of the transport is uniqueness of left adjoints.

Representable flatness of the base change is obtained from the same finite-limit data that
`AlgebraicGeometry.Space.spacesBaseChange_isMorphismOfSites` uses: the spaces-étale site of `Y`
has a terminal object and fibre products, base change preserves both, and
`CategoryTheory.flat_of_preservesFiniteLimits` is universe-general.

## References

* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 000J](https://stacks.math.columbia.edu/tag/000J)
* [Stacks Project, Tag 00X5](https://stacks.math.columbia.edu/tag/00X5)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ u

/-- Transport of left exactness of a left adjoint along equivalences on both sides: if
`P₀ ⊣ W ⋙ R ⋙ V` with `V` and `W` equivalences and `P₀` left exact, then every left adjoint of
`R` is left exact, being isomorphic to `V ⋙ P₀ ⋙ W` by uniqueness of left adjoints. -/
theorem CategoryTheory.Adjunction.preservesFiniteLimits_of_conjugate
    {A : Type u₁} [Category.{v₁} A] {A₀ : Type u₂} [Category.{v₂} A₀]
    {B₀ : Type u₃} [Category.{v₃} B₀] {C : Type u₄} [Category.{v₄} C]
    (V : A ⥤ A₀) (W : B₀ ⥤ C) (R : C ⥤ A) (P₀ : A₀ ⥤ B₀)
    [V.IsEquivalence] [W.IsEquivalence] (hP₀ : PreservesFiniteLimits P₀)
    (adj₀ : P₀ ⊣ W ⋙ R ⋙ V) {L : A ⥤ C} (adjL : L ⊣ R) :
    PreservesFiniteLimits L :=
  have hiso : W.asEquivalence.inverse ⋙ ((W ⋙ R ⋙ V) ⋙ V.asEquivalence.inverse) ≅ R :=
    Functor.isoWhiskerLeft W.asEquivalence.inverse
        (Functor.associator W (R ⋙ V) V.asEquivalence.inverse) ≪≫
      W.asEquivalence.invFunIdAssoc ((R ⋙ V) ⋙ V.asEquivalence.inverse) ≪≫
      Functor.associator R V V.asEquivalence.inverse ≪≫
      Functor.isoWhiskerLeft R V.asEquivalence.unitIso.symm ≪≫ R.rightUnitor
  have adj' : (V ⋙ P₀) ⋙ W ⊣ R :=
    ((V.asEquivalence.toAdjunction.comp adj₀).comp
      W.asEquivalence.toAdjunction).ofNatIsoRight hiso
  have : PreservesFiniteLimits (V ⋙ P₀) :=
    have := hP₀
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits ((V ⋙ P₀) ⋙ W) := comp_preservesFiniteLimits _ _
  preservesFiniteLimits_of_natIso (Adjunction.leftAdjointUniq adjL adj').symm

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Essential smallness -/

/-- The `Type u` of *presentation data* for an algebraic space over `S`: two objects `R` and `U`
of a small model of the big fppf site of `S` together with two morphisms `R ⇉ U`.

Every algebraic space over `S` is the quotient in fppf sheaves of such a datum, by Stacks 0262,
part (3), which is what makes its isomorphism classes `u`-small. -/
abbrev PresentationData : Type u :=
  Σ V : SmallModel.{u} (BigFppfOver B S hS) × SmallModel.{u} (BigFppfOver B S hS),
    (V.1 ⟶ V.2) × (V.1 ⟶ V.2)

/-- The fppf sheaf presented by a presentation datum: the coequalizer, in sheaves of sets valued
in `Type u` on the big fppf site of `S`, of the two represented morphisms. -/
noncomputable def presentationModel (i : PresentationData B S hS) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  letI := BigFppfOver.hasSheafify_type B S hS
  (coequalizer
      ((BigFppfOver.topology B S hS).yoneda.map
        ((equivSmallModel.{u} (BigFppfOver B S hS)).inverse.map i.2.1))
      ((BigFppfOver.topology B S hS).yoneda.map
        ((equivSmallModel.{u} (BigFppfOver B S hS)).inverse.map i.2.2))).obj

/-- Being an algebraic space over `S` is an essentially small property of presheaves of sets on
the big fppf site of `S`: every algebraic space is isomorphic to the sheaf presented by a
presentation datum.

The datum is read off the atlas of the algebraic space: `U` is the atlas, `R` is the represented
kernel pair of the atlas along itself, and the two morphisms are the two projections. That this
presents the algebraic space is Stacks 0262, part (3). -/
theorem essentiallySmall_isAlgebraicSpace :
    ObjectProperty.EssentiallySmall.{u}
      (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F) := by
  have := BigFppfOver.hasSheafify_type B S hS
  refine ⟨ObjectProperty.ofObj (presentationModel B S hS), inferInstance, fun F hF => ?_⟩
  obtain ⟨U, f, hsurj, hetale⟩ := hF.exists_atlas
  obtain ⟨R, s, t, hR⟩ : ∃ (R : BigFppfOver B S hS) (s t : R ⟶ U),
      IsPullback (yoneda.map s) (yoneda.map t) f f :=
    ⟨hsurj.rep.pullback f, hsurj.rep.fst' f, hsurj.rep.snd f, hsurj.rep.isPullback' f⟩
  obtain ⟨hRsh, hUsh, ⟨hcolim⟩⟩ :=
    isCoequalizer_of_surjectiveEtale B S hS f s t hR hF hsurj hetale
  set J := BigFppfOver.topology B S hS
  set e := equivSmallModel.{u} (BigFppfOver B S hS)
  set FF : Sheaf J (Type u) := ⟨F, hF.isSheaf⟩
  set ff : J.yoneda.obj U ⟶ FF := ⟨f⟩
  -- The unit of the small model is natural, which is all that is needed to move the cofork.
  have hnat : ∀ {V W : BigFppfOver B S hS} (k : V ⟶ W),
      (e.unitIso.app V).hom ≫ e.inverse.map (e.functor.map k) =
        k ≫ (e.unitIso.app W).hom := fun k => (e.unitIso.hom.naturality k).symm
  set e₀ : J.yoneda.obj R ≅ J.yoneda.obj (e.inverse.obj (e.functor.obj R)) :=
    J.yoneda.mapIso (e.unitIso.app R) with he₀
  set e₁ : J.yoneda.obj U ≅ J.yoneda.obj (e.inverse.obj (e.functor.obj U)) :=
    J.yoneda.mapIso (e.unitIso.app U) with he₁
  have hw : J.yoneda.map s ≫ ff = J.yoneda.map t ≫ ff := Sheaf.hom_ext hR.w
  have hc : ∀ k : R ⟶ U, e₀.hom ≫ J.yoneda.map (e.inverse.map (e.functor.map k)) =
      J.yoneda.map k ≫ e₁.hom := fun k => by
    simp only [he₀, he₁, Functor.mapIso_hom, ← Functor.map_comp]
    exact congrArg J.yoneda.map (hnat k)
  have hw' : J.yoneda.map (e.inverse.map (e.functor.map s)) ≫ (e₁.inv ≫ ff) =
      J.yoneda.map (e.inverse.map (e.functor.map t)) ≫ (e₁.inv ≫ ff) := by
    rw [(Iso.eq_inv_comp e₀).2 (hc s), (Iso.eq_inv_comp e₀).2 (hc t)]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, hw]
  have hcolim' : IsColimit (Cofork.ofπ (e₁.inv ≫ ff) hw') :=
    Cofork.isColimitOfIsos (Cofork.ofπ ff hw) hcolim _ e₀ e₁ (Iso.refl FF) (hc s) (hc t) (by simp)
  refine ⟨presentationModel B S hS ⟨(e.functor.obj R, e.functor.obj U),
      (e.functor.map s, e.functor.map t)⟩, ObjectProperty.ofObj_apply _ _,
    ⟨((sheafToPresheaf J (Type u)).mapIso
      (IsColimit.coconePointUniqueUpToIso (coequalizerIsCoequalizer _ _) hcolim')).symm⟩⟩

/-- **Stacks 02X2.** The category of algebraic spaces over `S` is essentially small at the
universe of its schemes: being an algebraic space is an essentially small property of presheaves,
and the presheaves of sets valued in `Type u` on the big fppf site of `S` are locally small at
`u`. -/
instance essentiallySmall_algebraicSpaces : EssentiallySmall.{u} (AlgebraicSpaces B S hS) :=
  have := essentiallySmall_isAlgebraicSpace B S hS
  inferInstance

/-- Every slice of the algebraic spaces over `S` is essentially small at the universe of the
schemes, being a costructured-arrow category over the identity. -/
instance essentiallySmall_over_algebraicSpaces (X : AlgebraicSpaces B S hS) :
    EssentiallySmall.{u} (Over X) :=
  inferInstanceAs (EssentiallySmall.{u} (CostructuredArrow (𝟭 (AlgebraicSpaces B S hS)) X))

/-- **Stacks 03G0.** The spaces-étale site of an algebraic space is essentially small at the
universe of the schemes, even though its objects live in `Type (u + 1)`.

It is the full subcategory of the slice of the algebraic spaces over `X` cut out by étaleness of
the structure morphism, and that slice is essentially small because the algebraic spaces over `S`
are. -/
@[stacks 03G0 "the set-theoretic condition: the site is essentially small"]
instance essentiallySmall_spacesEtale (X : AlgebraicSpaces B S hS) :
    EssentiallySmall.{u} (SpacesEtale B S hS X) :=
  essentiallySmall_of_fully_faithful (SpacesEtale.inclusion B S hS X)

/-! ### Descent of the morphism of small étale topoi to the universe of the structure rings -/

section Descent

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- The spaces-étale base change of Stacks 03G2, part (1) preserves finite limits: the
spaces-étale site of `Y` has a terminal object and fibre products, and base change preserves
both. -/
instance preservesFiniteLimits_spacesBaseChange :
    PreservesFiniteLimits (spacesBaseChange B S hS f).functor :=
  have := (SpacesEtale.isTerminal_idObj B S hS Y).hasTerminal
  have := Functor.preservesLimitsOfShape_pempty_of_isTerminal
    (spacesBaseChange B S hS f).functor (SpacesEtale.isTerminal_idObj B S hS Y)
    (isTerminal_spacesBaseChange_idObj B S hS f)
  preservesFiniteLimits_of_preservesTerminal_and_pullbacks _

/-- The spaces-étale base change is representably flat, that is, all the index categories
`(I_V^u)ᵒᵖ` of Stacks 00VC are filtered. This is Stacks 00X3 for the finite-limit data of
`AlgebraicGeometry.Space.spacesBaseChange_isMorphismOfSites`, and unlike that lemma it is stated
without any constraint tying the universe of the sheaves to the universe of the site. -/
instance representablyFlat_spacesBaseChange :
    RepresentablyFlat (spacesBaseChange B S hS f).functor :=
  have := (SpacesEtale.isTerminal_idObj B S hS Y).hasTerminal
  have : HasFiniteLimits (SpacesEtale B S hS Y) :=
    hasFiniteLimits_of_hasTerminal_and_pullbacks
  flat_of_preservesFiniteLimits _

/-- The spaces-étale topology transported to a small model of the spaces-étale site. The small
model is a genuinely small category, so the universe of its sheaves of sets may be taken to be
the universe of the site. -/
noncomputable abbrev smallModelTopology (Z : AlgebraicSpaces B S hS) :
    GrothendieckTopology (SmallModel.{u} (SpacesEtale B S hS Z)) :=
  (equivSmallModel.{u} (SpacesEtale B S hS Z)).inverse.inducedTopology
    (SpacesEtale.topology B S hS Z)

/-- The spaces-étale base change transported to the small models of the two sites. -/
noncomputable abbrev smallModelBaseChange :
    SmallModel.{u} (SpacesEtale B S hS Y) ⥤ SmallModel.{u} (SpacesEtale B S hS X) :=
  (equivSmallModel.{u} (SpacesEtale B S hS Y)).inverse ⋙
    (spacesBaseChange B S hS f).functor ⋙
      (equivSmallModel.{u} (SpacesEtale B S hS X)).functor

/-- The transported base change is continuous for the transported topologies, being a composite
of continuous functors: the two comparisons with the small models are dense subsite inclusions
and hence continuous, and the base change itself is continuous by Stacks 03G2, part (1). -/
instance isContinuous_smallModelBaseChange : (smallModelBaseChange B S hS f).IsContinuous
    (smallModelTopology B S hS Y) (smallModelTopology B S hS X) :=
  have : ((spacesBaseChange B S hS f).functor ⋙
      (equivSmallModel.{u} (SpacesEtale B S hS X)).functor).IsContinuous
      (SpacesEtale.topology B S hS Y) (smallModelTopology B S hS X) :=
    Functor.isContinuous_comp _ _ _ (SpacesEtale.topology B S hS X) _
  Functor.isContinuous_comp _ _ _ (SpacesEtale.topology B S hS Y) _

/-- The comma categories indexing the right Kan extension along the comparison of a
spaces-étale site with its small model have limits of sets in universe `u`: they are essentially
small at `u`, because the small model is small and the spaces-étale site is locally small. -/
instance hasLimitsOfShape_structuredArrow_smallModel_inverse_op
    (Z : AlgebraicSpaces B S hS) (W : (SpacesEtale B S hS Z)ᵒᵖ) :
    HasLimitsOfShape
      (StructuredArrow W (equivSmallModel.{u} (SpacesEtale B S hS Z)).inverse.op) (Type u) :=
  have : EssentiallySmall.{u}
      (StructuredArrow W (equivSmallModel.{u} (SpacesEtale B S hS Z)).inverse.op) :=
    inferInstance
  hasLimitsOfShape_of_essentiallySmall _ _

/-- The same for the comparison in the other direction. Together with the previous instance this
is what makes the two restriction functors between the sheaves of the spaces-étale site and the
sheaves of its small model equivalences at `Type u`. -/
instance hasLimitsOfShape_structuredArrow_smallModel_functor_op
    (Z : AlgebraicSpaces B S hS) (W : (SmallModel.{u} (SpacesEtale B S hS Z))ᵒᵖ) :
    HasLimitsOfShape
      (StructuredArrow W (equivSmallModel.{u} (SpacesEtale B S hS Z)).functor.op) (Type u) :=
  have : EssentiallySmall.{u}
      (StructuredArrow W (equivSmallModel.{u} (SpacesEtale B S hS Z)).functor.op) :=
    inferInstance
  hasLimitsOfShape_of_essentiallySmall _ _

/-- The direct image of the transported base change is the direct image of the base change
conjugated by the two restrictions along the comparisons with the small models. This holds by
`rfl`, being `CategoryTheory.Functor.sheafPushforwardContinuousComp` for the two functors whose
composite `AlgebraicGeometry.Space.smallModelBaseChange` is. -/
theorem sheafPushforwardContinuous_smallModelBaseChange :
    ((equivSmallModel.{u} (SpacesEtale B S hS X)).functor.sheafPushforwardContinuous (Type u)
        (SpacesEtale.topology B S hS X) (smallModelTopology B S hS X)) ⋙
      ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
        (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)) ⋙
      ((equivSmallModel.{u} (SpacesEtale B S hS Y)).inverse.sheafPushforwardContinuous (Type u)
        (smallModelTopology B S hS Y) (SpacesEtale.topology B S hS Y)) =
    (smallModelBaseChange B S hS f).sheafPushforwardContinuous (Type u)
      (smallModelTopology B S hS Y) (smallModelTopology B S hS X) := rfl

/-- **Stacks 00X5** for the transported base change: its inverse image on sheaves of sets valued
in `Type u` is left exact. The small models are genuinely small categories, so the universe of
the sheaves agrees with the universe of the site and the flatness criterion applies. -/
theorem preservesFiniteLimits_sheafPullback_smallModelBaseChange :
    PreservesFiniteLimits ((smallModelBaseChange B S hS f).sheafPullback (Type u)
      (smallModelTopology B S hS Y) (smallModelTopology B S hS X)) :=
  Functor.preservesFiniteLimits_sheafPullback _ _ _

/-- **The input that was missing for Stacks 03G2 at the universe of the structure rings.** The
spaces-étale inverse image of Stacks 03G2, part (1) is left exact on sheaves of sets valued in
`Type u`.

Mathlib's two sufficient conditions are both stated with the universe of the sheaves tied to the
universe of the site, which here is `u + 1`. Essential smallness of the spaces-étale sites unties
them: the situation transports to the small models, where Stacks 00X5 applies at `Type u`, and
the conclusion comes back by uniqueness of left adjoints. -/
instance preservesFiniteLimits_sheafPullback_spacesBaseChange :
    PreservesFiniteLimits ((spacesBaseChange B S hS f).functor.sheafPullback (Type u)
      (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)) :=
  Adjunction.preservesFiniteLimits_of_conjugate
    (V := (equivSmallModel.{u} (SpacesEtale B S hS Y)).inverse.sheafPushforwardContinuous
      (Type u) (smallModelTopology B S hS Y) (SpacesEtale.topology B S hS Y))
    (W := (equivSmallModel.{u} (SpacesEtale B S hS X)).functor.sheafPushforwardContinuous
      (Type u) (SpacesEtale.topology B S hS X) (smallModelTopology B S hS X))
    (R := (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
      (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X))
    (P₀ := (smallModelBaseChange B S hS f).sheafPullback (Type u)
      (smallModelTopology B S hS Y) (smallModelTopology B S hS X))
    (preservesFiniteLimits_sheafPullback_smallModelBaseChange B S hS f)
    ((smallModelBaseChange B S hS f).sheafAdjunctionContinuous (Type u)
      (smallModelTopology B S hS Y) (smallModelTopology B S hS X))
    ((spacesBaseChange B S hS f).functor.sheafAdjunctionContinuous (Type u)
      (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X))

/-- **Stacks 03G2, part (1)** at the universe of the structure rings: the morphism of
spaces-étale topoi attached by Stacks 00XC to the base-change morphism of sites, for sheaves of
sets valued in `Type u`. Its direct image and inverse image are the spaces-étale direct and
inverse images of `StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleToposRingUniverse`; what is new
is that the inverse image is now known to be left exact. -/
noncomputable def spacesToposMorphismTypeU :
    MorphismOfTopoi (Sheaf (SpacesEtale.topology B S hS X) (Type u))
      (Sheaf (SpacesEtale.topology B S hS Y) (Type u)) where
  pushforward := (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
    (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)
  inverseImage := (spacesBaseChange B S hS f).functor.sheafPullback (Type u)
    (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)
  adj := (spacesBaseChange B S hS f).functor.sheafAdjunctionContinuous (Type u)
    (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)
  preservesFiniteLimits := inferInstance

/-- **Stacks 03G1** at the universe of the structure rings: the comparison equivalence between
the spaces-étale topos of an algebraic space and its small étale topos, for sheaves of sets
valued in `Type u`. -/
noncomputable def smallEtaleToposEquivTypeU (Z : AlgebraicSpaces B S hS) :
    Sheaf (SpacesEtale.topology B S hS Z) (Type u) ≌
      Sheaf (SmallEtale.topology B S hS Z.1) (Type u) :=
  ((comparisonFunctor B S hS Z).sheafPushforwardContinuous (Type u)
    (SmallEtale.topology B S hS Z.1) (SpacesEtale.topology B S hS Z)).asEquivalence

/-- **Stacks 03G2, part (3)** at the universe of the structure rings: the morphism of small étale
topoi induced by a morphism `f : X ⟶ Y` of algebraic spaces, for sheaves of sets valued in
`Type u`.

This is the descent of `AlgebraicGeometry.Space.smallToposMorphism`, which is stated at
`Type (u + 1)`, to the universe of the structure rings — the universe at which a ringed topos in
the sense of Stacks 01D3 declares its underlying topos. It is built exactly as that one is: the
spaces-étale morphism of topoi, transported along the comparison equivalences of Stacks 03G1. -/
noncomputable def smallToposMorphismTypeU :
    MorphismOfTopoi (Sheaf (SmallEtale.topology B S hS X.1) (Type u))
      (Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) :=
  (spacesToposMorphismTypeU B S hS f).transport
    (smallEtaleToposEquivTypeU B S hS X) (smallEtaleToposEquivTypeU B S hS Y)

/-- The direct image of `AlgebraicGeometry.Space.smallToposMorphismTypeU` agrees, through the
comparison equivalences of Stacks 03G1, with the spaces-étale direct image at `Type u`. This
identifies the descended morphism of topoi and is not an extra choice. -/
noncomputable def smallToposMorphismTypeU_comparison :
    ((comparisonFunctor B S hS X).sheafPushforwardContinuous (Type u)
          (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)) ⋙
        (smallToposMorphismTypeU B S hS f).pushforward ≅
      ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
          (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)) ⋙
        (comparisonFunctor B S hS Y).sheafPushforwardContinuous (Type u)
          (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y) :=
  MorphismOfTopoi.transport_pushforward_comparison _ _ _

end Descent

end AlgebraicGeometry.Space

end
