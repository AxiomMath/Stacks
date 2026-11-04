module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExact
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.OrdinaryDerived
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupportProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom

/-!
# Full faithfulness of the small étale direct image

Let `f : X ⟶ Y` be a representable morphism of algebraic spaces over a scheme `S`. Its direct
image on small étale sheaves of sets is, by Stacks 03G8
(`AlgebraicGeometry.Space.smallEtaleRingedToposHom_representable`), restriction along the
base-change functor `smallBaseChange f` on étale scheme charts of Stacks 03G2, part (4). So the
direct image is fully faithful as soon as that functor exhibits the small étale site of `X` as a
*dense subsite* of itself through base change: Mathlib's
`CategoryTheory.Functor.IsCoverDense.full_sheafPushforwardContinuous` and
`…faithful_sheafPushforwardContinuous` need nothing beyond cover density and local fullness.

Concretely, cover density of `smallBaseChange f` asks that every étale scheme chart of `X` be
covered, in the small étale topology of `X`, by charts of the form `V ×_Y X` with `V` an étale
scheme chart of `Y`. For a *closed immersion* `f` that is the lifting of étale morphisms across a
closed immersion, Stacks 057R and 04E3, available for schemes as
`Stacks.Etale.exists_etale_openCover_isomorphic_pullback_of_isClosedImmersion` and
`AlgebraicGeometry.exists_etale_zariskiCover_baseChange_of_isClosedImmersion`. Local fullness
asks that every morphism of base-changed charts be, locally on the source, base changed from a
morphism of charts of `Y`; it rests on the same input. Both are proved for a closed immersion in
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionChartBaseChangeDense.lean`, which is where
Stacks 04E5 is tagged and which cannot be imported here because it consumes the statements
below. Nothing in this file carries `@[stacks 04E5]`, each declaration here having the two site
conditions as hypotheses.

## Main results

* `AlgebraicGeometry.Space.fullyFaithfulSmallEtaleRestriction`: restriction along the chart
  base-change functor is fully faithful on sheaves with values in *any* category, as soon as that
  functor is cover dense and locally full.
* `AlgebraicGeometry.Space.fullyFaithfulSmallEtalePushforward`: the direct image on small étale
  sheaves of sets along a representable morphism is fully faithful as soon as the chart
  base-change functor is cover dense and locally full.
* `AlgebraicGeometry.Space.closedImmersionComplementSubfunctor` is the open complement `X \ Z`
  of a closed immersion as a subfunctor of `X`,
  `AlgebraicGeometry.Space.closedImmersionComplement` the same thing as an algebraic space over
  `S`, and `AlgebraicGeometry.Space.closedImmersionComplementHom` its open immersion into `X`,
  whose point set is the complement of the point set of the immersion
  (`AlgebraicGeometry.Space.range_pointsMap_closedImmersionComplementHom`).
* `AlgebraicGeometry.Space.smallEtalePushforward_isRightAdjoint_abelian`: on abelian sheaves the
  small étale direct image along a representable morphism is a right adjoint. This needs no
  hypothesis on the chart base change.
* `AlgebraicGeometry.Space.smallEtalePushforward_full`,
  `AlgebraicGeometry.Space.smallEtalePushforward_faithful` and
  `AlgebraicGeometry.Space.smallEtaleAdjunction_counit_isIso`: for sheaves of sets, full
  faithfulness of the direct image along a closed immersion and the left-inverse assertion,
  granted cover density and local fullness of the chart base change;
  `AlgebraicGeometry.Space.smallEtalePushforward_full_abelian`,
  `AlgebraicGeometry.Space.smallEtalePushforward_faithful_abelian` and
  `AlgebraicGeometry.Space.smallEtaleAdjunction_counit_isIso_abelian` are the same for abelian
  sheaves.
* `AlgebraicGeometry.Space.smallEtalePushforward_essImage_iff` and
  `AlgebraicGeometry.Space.smallEtalePushforward_essImage_iff_abelian`: the two essential-image
  descriptions, granted in addition the computation of the direct image away from `Z` and the
  essential-image half of Stacks 04CA.
* `AlgebraicGeometry.Space.openSubspacesOrderIso_symm_val_eq_openSubspaceOfPoints`: the open
  subspace attached by Stacks 03BZ to an open set of points is the subspace that set cuts out.

## Implementation notes

The direct image in the conclusion is the one of
`AlgebraicGeometry.Space.smallToposMorphismTypeU`, the morphism of small étale topoi of
Stacks 03G2, part (3) at the universe of the structure rings; that is the form the modules
development consumes. Transporting full faithfulness from the restriction functor to it is
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_representable`, which is an identification and
not a choice.

Cover density and local fullness are taken as explicit arguments rather than as instances: at a
concrete site neither is going to be found by instance search, and both are the content of the
statement rather than ambient structure.

Mathlib's `CategoryTheory.Functor.IsCoverDense.full_sheafPushforwardContinuous` and
`…faithful_sheafPushforwardContinuous` are stated for sheaves with values in an arbitrary
category, so the geometry is independent of the coefficients: that is
`AlgebraicGeometry.Space.fullyFaithfulSmallEtaleRestriction`, of which the statement about
sheaves of sets is the instance at the universe of the structure rings. Only the identification
with the direct image of the morphism of topoi is special to sets. Neither statement needs local
*faithfulness* of the chart base change; that is true and provable from the openness of the
equalizer of two morphisms of schemes étale over `X`, but it is not used and so is not assumed.

The remaining clauses of Stacks 04E5 are reduced, in the second half of this file, to the same
two site-theoretic inputs for a closed immersion `i : Z ⟶ X`, carried as the hypotheses `h04FW`
(cover density, Stacks 04FW) and `h04FV` (local fullness, Stacks 04FV), together with two
further hypotheses for the essential images: `h04FX`, the computation of the direct image away
from `Z`, and `h04CA`, the essential-image half of Stacks 04CA. Both site-theoretic inputs are
already available for *schemes* — `AlgebraicGeometry.exists_span_baseChange_iso` is Stacks 04FV
for a closed immersion of schemes and
`AlgebraicGeometry.exists_etale_zariskiCover_baseChange_of_isClosedImmersion` is Stacks 04FW —
so what they still need is the passage to étale charts of an algebraic space, not new geometry.

The complement `X \ Z` is `AlgebraicGeometry.Space.openSubspaceOfPoints` applied to the
complement of the point set of `i`, which is an open subspace by
`AlgebraicGeometry.Space.isOpenSubspace_openSubspaceOfPoints_compl_range_pointsMap`. It is *not*
built as the inverse image of that open set of points under the order isomorphism of Stacks 03BZ,
because that isomorphism is a `Classical.choose` of an `ExistsUnique` and nothing computes with
its inverse. The two agree:
`AlgebraicGeometry.Space.openSubspacesOrderIso_symm_val_eq_openSubspaceOfPoints` proves it, by
uniqueness of the order isomorphism, so the choice-free presentation is a presentation of the
same subspace and not of a different one.

The left-inverse assertions are the counit-iso halves of the equivalences proved for an arbitrary
representable morphism in `StacksFrontier.AlgebraicGeometry.Spaces.OrdinaryDerived`; only the easy
direction of those equivalences is used, since full faithfulness is available directly.

Right-adjointness of the abelian direct image is unconditional at the universe `max (u + 1) v` of
the statement: `AlgebraicGeometry.Space.SmallEtale.instHasSheafify` does not apply, but
`CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat` does, since the small étale site
has its objects in `Type (u + 1)` and its morphisms in `Type u`. It is a theorem rather than an
instance, so it has to be supplied by hand.

The essential-image descriptions are reduced to the unit of the adjunction by
`CategoryTheory.Adjunction.isIso_unit_app_iff_mem_essImage`, which applies exactly because the
direct image has already been shown fully faithful. Nothing below is universe-specialised: the
coefficient universe `v` of the sheaves is free throughout, as in the source.

## References

* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 04CA](https://stacks.math.columbia.edu/tag/04CA)
* [Stacks Project, Tag 04D6](https://stacks.math.columbia.edu/tag/04D6)
* [Stacks Project, Tag 04E3](https://stacks.math.columbia.edu/tag/04E3)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
* [Stacks Project, Tag 04FV](https://stacks.math.columbia.edu/tag/04FV)
* [Stacks Project, Tag 04FW](https://stacks.math.columbia.edu/tag/04FW)
* [Stacks Project, Tag 04FX](https://stacks.math.columbia.edu/tag/04FX)
* [Stacks Project, Tag 057R](https://stacks.math.columbia.edu/tag/057R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicGeometry.Space

/-! ### Full faithfulness from cover density of chart base change -/

section Restriction

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **Full faithfulness of restriction along chart base change**, for sheaves with values in an
arbitrary category. For a representable morphism `f : X ⟶ Y` of algebraic spaces whose chart
base-change functor `AlgebraicGeometry.Space.smallBaseChange` of Stacks 03G2, part (4) is cover
dense and locally full for the small étale topology of `X`, restriction along it is fully
faithful on `A`-valued sheaves.

Restriction along a continuous functor exhibiting a dense subsite is fully faithful whatever the
coefficients are; the two geometric inputs are the same for every `A`. Stacks 04E5 is this
statement for `A` the category of sets, in part (1), and the category of abelian groups, in
part (2), with both inputs discharged for a closed immersion; neither is done in this
development, so no tag is carried. -/
def fullyFaithfulSmallEtaleRestriction (A : Type w) [Category.{v} A] (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom)
    (hcd : (smallBaseChange B S hS f hf).IsCoverDense (SmallEtale.topology B S hS X.1))
    (hlf : (smallBaseChange B S hS f hf).IsLocallyFull (SmallEtale.topology B S hS X.1)) :
    letI := (smallBaseChange_isMorphismOfSites B S hS f hf).toIsContinuous
    ((smallBaseChange B S hS f hf).sheafPushforwardContinuous A
      (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)).FullyFaithful :=
  letI := (smallBaseChange_isMorphismOfSites B S hS f hf).toIsContinuous
  haveI := hcd
  haveI := hlf
  Functor.FullyFaithful.ofFullyFaithful _

/-- **Full faithfulness of the small étale direct image**, from cover density of chart base
change. For a representable morphism `f : X ⟶ Y` of algebraic spaces whose chart base-change
functor `AlgebraicGeometry.Space.smallBaseChange` is cover dense and locally full for the small
étale topology of `X`, the direct image of sheaves of sets along the morphism of small étale
topoi of Stacks 03G2, part (3) is fully faithful.

By Stacks 03G8 the direct image is restriction along chart base change, and restriction along a
cover-dense, locally full, continuous functor is fully faithful. Part (1) of Stacks 04E5 is this
statement with the two hypotheses discharged for a closed immersion; that is done, and tagged, in
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionChartBaseChangeDense.lean`, so no tag is
carried here. -/
def fullyFaithfulSmallEtalePushforward (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
    (hcd : (smallBaseChange B S hS f hf).IsCoverDense (SmallEtale.topology B S hS X.1))
    (hlf : (smallBaseChange B S hS f hf).IsLocallyFull (SmallEtale.topology B S hS X.1)) :
    (smallToposMorphismTypeU B S hS f).pushforward.FullyFaithful :=
  Functor.FullyFaithful.ofIso
    (fullyFaithfulSmallEtaleRestriction B S hS (Type u) f hf hcd hlf)
    (smallEtaleRingedToposHom_representable B S hS f hf).symm

end Restriction

/-! ### The open complement of a closed immersion -/

section Complement

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The open subspace that Stacks 03BZ attaches to an open set of points of an algebraic space
is the subspace that set cuts out.

The order isomorphism of Stacks 03BZ is a `Classical.choose` of an `ExistsUnique`, so its
inverse is opaque; this identifies it, on the nose, with
`AlgebraicGeometry.Space.openSubspaceOfPoints`, whose point set is the given set by part (1) of
Stacks 03BZ. -/
theorem openSubspacesOrderIso_symm_val_eq_openSubspaceOfPoints
    (hF : IsAlgebraicSpace B S hS F) (W : TopologicalSpace.Opens (points B S hS F)) :
    ((openSubspacesOrderIso B S hS F hF).symm W).1 =
      openSubspaceOfPoints B S hS F (W : Set (points B S hS F)) := by
  have h : (openSubspacesOrderIso B S hS F hF).symm W =
      ⟨openSubspaceOfPoints B S hS F (W : Set (points B S hS F)),
        isOpenSubspace_openSubspaceOfPoints B S hS hF _ W.2⟩ :=
    (OrderIso.symm_apply_eq _).mpr (TopologicalSpace.Opens.ext
      ((openSubspacesOrderIso_apply B S hS F hF _).trans
        (range_pointsMap_ι_openSubspaceOfPoints B S hS _)).symm)
  rw [h]

end Complement

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X : AlgebraicSpaces B S hS} (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom)

/-- The open complement `X \ Z` of a closed immersion `i : Z ⟶ X` of algebraic spaces over
`S`, as a subfunctor of `X`: the subfunctor cut out by the complement of the point set of
`i`. -/
def closedImmersionComplementSubfunctor : Subfunctor X.1 :=
  openSubspaceOfPoints B S hS X.1 (Set.range (pointsMap B S hS Z.1 i.hom))ᶜ

include hi in
/-- The open complement of a closed immersion is an open subspace, by Stacks 04CD and part (1)
of Stacks 03BZ. -/
theorem isOpenSubspace_closedImmersionComplementSubfunctor :
    IsOpenSubspace B S hS (closedImmersionComplementSubfunctor B S hS i) :=
  isOpenSubspace_openSubspaceOfPoints_compl_range_pointsMap B S hS X.property i.hom hi

/-- The open complement `X \ Z` of a closed immersion `i : Z ⟶ X` of algebraic spaces over
`S`, as an algebraic space over `S`. -/
@[simps]
def closedImmersionComplement : AlgebraicSpaces B S hS :=
  ⟨(closedImmersionComplementSubfunctor B S hS i).toFunctor,
    (isOpenSubspace_closedImmersionComplementSubfunctor B S hS i hi).1⟩

/-- The open immersion of the open complement of a closed immersion into the ambient algebraic
space. -/
def closedImmersionComplementHom : closedImmersionComplement B S hS i hi ⟶ X :=
  ObjectProperty.homMk (closedImmersionComplementSubfunctor B S hS i).ι

/-- The inclusion of the open complement of a closed immersion into the ambient algebraic space
is an open immersion. -/
theorem isOpenImmersion_closedImmersionComplementHom :
    IsOpenImmersion B S hS (closedImmersionComplementHom B S hS i hi).hom :=
  (isOpenSubspace_closedImmersionComplementSubfunctor B S hS i hi).2

/-- The inclusion of the open complement of a closed immersion is representable, being an open
immersion. -/
theorem relativelyRepresentable_closedImmersionComplementHom :
    yoneda.relativelyRepresentable (closedImmersionComplementHom B S hS i hi).hom :=
  (isOpenImmersion_closedImmersionComplementHom B S hS i hi).rep

/-- The point set of the open complement of a closed immersion is the complement of the point
set of the immersion, by part (1) of Stacks 03BZ.

This is what makes the essential-image clause below a statement about `X \ Z`: the subspace it
restricts along is the one whose points are exactly the points of `X` outside `Z`. -/
theorem range_pointsMap_closedImmersionComplementHom :
    Set.range (pointsMap B S hS (closedImmersionComplement B S hS i hi).1
        (closedImmersionComplementHom B S hS i hi).hom) =
      (Set.range (pointsMap B S hS Z.1 i.hom))ᶜ :=
  range_pointsMap_ι_openSubspaceOfPoints B S hS _

/-! ### The two site-theoretic inputs -/

variable
    (h04FW : (smallBaseChange B S hS i hi.1).IsCoverDense (SmallEtale.topology B S hS Z.1))
    (h04FV : (smallBaseChange B S hS i hi.1).IsLocallyFull (SmallEtale.topology B S hS Z.1))

/-! ### Sheaves of sets -/

include h04FW h04FV in
/-- **Stacks 04E5, part (1), fullness**, granted Stacks 04FW and Stacks 04FV for the chart
base change of the closed immersion.

`h04FW` is cover-density and `h04FV` local fullness of the base-change functor on étale scheme
charts; together with the continuity of that functor, which is part (4) of Stacks 03G2, they
give fullness of the direct image for any coefficient category. -/
theorem smallEtalePushforward_full :
    letI := (smallBaseChange_isMorphismOfSites B S hS i hi.1).toIsContinuous
    ((smallBaseChange B S hS i hi.1).sheafPushforwardContinuous
      (Type (max (u + 1) v)) (SmallEtale.topology B S hS X.1)
      (SmallEtale.topology B S hS Z.1)).Full := by
  exact (fullyFaithfulSmallEtaleRestriction B S hS _ i hi.1 h04FW h04FV).full

include h04FW h04FV in
/-- **Stacks 04E5, part (1), faithfulness**, granted Stacks 04FW and Stacks 04FV for the chart
base change of the closed immersion. -/
theorem smallEtalePushforward_faithful :
    letI := (smallBaseChange_isMorphismOfSites B S hS i hi.1).toIsContinuous
    ((smallBaseChange B S hS i hi.1).sheafPushforwardContinuous
      (Type (max (u + 1) v)) (SmallEtale.topology B S hS X.1)
      (SmallEtale.topology B S hS Z.1)).Faithful := by
  exact (fullyFaithfulSmallEtaleRestriction B S hS _ i hi.1 h04FW h04FV).faithful

include h04FW h04FV in
/-- **Stacks 04E5, part (1), the left-inverse assertion**, granted Stacks 04FW and Stacks 04FV
for the chart base change of the closed immersion: the counit
`i_{small}^{-1}i_{small, *}\mathcal{G} \to \mathcal{G}` is an isomorphism.

This is the easy direction of
`AlgebraicGeometry.Space.smallEtalePushforward_counit_isIso_iff_fullyFaithful`, which is Stacks
04D6, applied to the full faithfulness just obtained. -/
theorem smallEtaleAdjunction_counit_isIso
    (G : Sheaf (SmallEtale.topology B S hS Z.1) (Type (max (u + 1) v))) :
    letI := (smallBaseChange_isMorphismOfSites B S hS i hi.1).toIsContinuous
    IsIso (((smallBaseChange B S hS i hi.1).sheafAdjunctionContinuous
      (Type (max (u + 1) v)) (SmallEtale.topology B S hS X.1)
      (SmallEtale.topology B S hS Z.1)).counit.app G) := by
  exact (smallEtalePushforward_counit_isIso_iff_fullyFaithful.{v} B S hS i hi.1).mpr
    ⟨inferInstance, inferInstance⟩ G

include h04FW h04FV in
/-- **Stacks 04E5, part (1), the essential image**, granted Stacks 04FW and Stacks 04FV for the
chart base change, the computation `h04FX` of the direct image away from `Z`, and the
essential-image half `h04CA` of Stacks 04CA: a sheaf of sets on `X_{étale}` is in the essential
image of `i_{small, *}` exactly when its restriction to `X \ Z` is a singleton.

`h04FX` is the half of Stacks 04FX computing the stalk of `i_{small, *}\mathcal{G}` outside
`Z`, in the form "the restriction of `i_{small, *}\mathcal{G}` to `X \ Z` is terminal"; `h04CA`
is the implication the source proves by reduction to the case of schemes. The translation of
membership of the essential image into invertibility of the unit is
`CategoryTheory.Adjunction.isIso_unit_app_iff_mem_essImage`, available because the direct image
is fully faithful. -/
theorem smallEtalePushforward_essImage_iff
    (h04FX : letI := (smallBaseChange_isMorphismOfSites B S hS
        (closedImmersionComplementHom B S hS i hi)
        (relativelyRepresentable_closedImmersionComplementHom B S hS i hi)).toIsContinuous
      letI := (smallBaseChange_isMorphismOfSites B S hS i hi.1).toIsContinuous
      ∀ G : Sheaf (SmallEtale.topology B S hS Z.1) (Type (max (u + 1) v)),
        Nonempty (IsTerminal (((smallBaseChange B S hS
          (closedImmersionComplementHom B S hS i hi)
          (relativelyRepresentable_closedImmersionComplementHom B S hS i hi)).sheafPullback
            (Type (max (u + 1) v)) (SmallEtale.topology B S hS X.1)
            (SmallEtale.topology B S hS (closedImmersionComplement B S hS i hi).1)).obj
          (((smallBaseChange B S hS i hi.1).sheafPushforwardContinuous
            (Type (max (u + 1) v)) (SmallEtale.topology B S hS X.1)
            (SmallEtale.topology B S hS Z.1)).obj G))))
    (h04CA : letI := (smallBaseChange_isMorphismOfSites B S hS
        (closedImmersionComplementHom B S hS i hi)
        (relativelyRepresentable_closedImmersionComplementHom B S hS i hi)).toIsContinuous
      letI := (smallBaseChange_isMorphismOfSites B S hS i hi.1).toIsContinuous
      ∀ F : Sheaf (SmallEtale.topology B S hS X.1) (Type (max (u + 1) v)),
        Nonempty (IsTerminal (((smallBaseChange B S hS
          (closedImmersionComplementHom B S hS i hi)
          (relativelyRepresentable_closedImmersionComplementHom B S hS i hi)).sheafPullback
            (Type (max (u + 1) v)) (SmallEtale.topology B S hS X.1)
            (SmallEtale.topology B S hS (closedImmersionComplement B S hS i hi).1)).obj F)) →
          IsIso (((smallBaseChange B S hS i hi.1).sheafAdjunctionContinuous
            (Type (max (u + 1) v)) (SmallEtale.topology B S hS X.1)
            (SmallEtale.topology B S hS Z.1)).unit.app F))
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type (max (u + 1) v))) :
    letI := (smallBaseChange_isMorphismOfSites B S hS i hi.1).toIsContinuous
    ((smallBaseChange B S hS i hi.1).sheafPushforwardContinuous
      (Type (max (u + 1) v)) (SmallEtale.topology B S hS X.1)
      (SmallEtale.topology B S hS Z.1)).essImage F ↔
      letI := (smallBaseChange_isMorphismOfSites B S hS
        (closedImmersionComplementHom B S hS i hi)
        (relativelyRepresentable_closedImmersionComplementHom B S hS i hi)).toIsContinuous
      Nonempty (IsTerminal (((smallBaseChange B S hS
        (closedImmersionComplementHom B S hS i hi)
        (relativelyRepresentable_closedImmersionComplementHom B S hS i hi)).sheafPullback
          (Type (max (u + 1) v)) (SmallEtale.topology B S hS X.1)
          (SmallEtale.topology B S hS (closedImmersionComplement B S hS i hi).1)).obj F)) := by
  let _ := (smallBaseChange_isMorphismOfSites B S hS i hi.1).toIsContinuous
  let _ := (smallBaseChange_isMorphismOfSites B S hS
    (closedImmersionComplementHom B S hS i hi)
    (relativelyRepresentable_closedImmersionComplementHom B S hS i hi)).toIsContinuous
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨G, ⟨e⟩⟩
    exact (h04FX G).elim fun t => ⟨t.ofIso (Functor.mapIso _ e)⟩
  · exact (Adjunction.isIso_unit_app_iff_mem_essImage _).mp (h04CA F h)

/-! ### Abelian sheaves -/

/-- **Stacks 04E5, part (2), existence of the inverse-image adjunction.** On abelian sheaves in
any universe at least `u + 1` the small étale direct image along a representable morphism of
algebraic spaces is a right adjoint, so that the inverse image of part (2) exists.

This needs no hypothesis on the morphism beyond representability, and in particular none of the
two site-theoretic inputs of this file. Sheafification of `AddCommGrpCat.{max (u + 1) v}`-valued
presheaves on the small étale site is
`CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat`, which applies because the site
has its objects in `Type (u + 1)` and its morphisms in `Type u`; it is a theorem and not an
instance, so it is supplied by hand.

This is the one clause of Stacks 04E5 proved here without any hypothesis, and it still carries
no `@[stacks 04E5]` attribute: a tag on it would present 04E5 as formalized while
its five mathematical clauses are still conditional on `h04FW` and `h04FV`. -/
theorem smallEtalePushforward_isRightAdjoint_abelian :
    letI := (smallBaseChange_isMorphismOfSites B S hS i hi.1).toIsContinuous
    Nonempty (((smallBaseChange B S hS i hi.1).sheafPushforwardContinuous
      AddCommGrpCat.{max (u + 1) v} (SmallEtale.topology B S hS X.1)
      (SmallEtale.topology B S hS Z.1)).IsRightAdjoint) := by
  let _ := (smallBaseChange_isMorphismOfSites B S hS i hi.1).toIsContinuous
  have : HasSheafify (SmallEtale.topology B S hS Z.1) AddCommGrpCat.{max (u + 1) v} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max (u + 1) v, u, u + 1}
      (SmallEtale.topology B S hS Z.1)
  exact ⟨inferInstance⟩

include h04FW h04FV in
/-- **Stacks 04E5, part (2), fullness**, granted Stacks 04FW and Stacks 04FV for the chart base
change of the closed immersion. -/
theorem smallEtalePushforward_full_abelian :
    letI := (smallBaseChange_isMorphismOfSites B S hS i hi.1).toIsContinuous
    ((smallBaseChange B S hS i hi.1).sheafPushforwardContinuous
      AddCommGrpCat.{max (u + 1) v} (SmallEtale.topology B S hS X.1)
      (SmallEtale.topology B S hS Z.1)).Full := by
  exact (fullyFaithfulSmallEtaleRestriction B S hS _ i hi.1 h04FW h04FV).full

include h04FW h04FV in
/-- **Stacks 04E5, part (2), faithfulness**, granted Stacks 04FW and Stacks 04FV for the chart
base change of the closed immersion. -/
theorem smallEtalePushforward_faithful_abelian :
    letI := (smallBaseChange_isMorphismOfSites B S hS i hi.1).toIsContinuous
    ((smallBaseChange B S hS i hi.1).sheafPushforwardContinuous
      AddCommGrpCat.{max (u + 1) v} (SmallEtale.topology B S hS X.1)
      (SmallEtale.topology B S hS Z.1)).Faithful := by
  exact (fullyFaithfulSmallEtaleRestriction B S hS _ i hi.1 h04FW h04FV).faithful

include h04FW h04FV in
/-- **Stacks 04E5, part (2), the left-inverse assertion**, granted Stacks 04FW and Stacks 04FV
for the chart base change of the closed immersion.

The adjunction is the one whose existence is
`AlgebraicGeometry.Space.smallEtalePushforward_isRightAdjoint_abelian`, as in the source, where
part (2) presupposes it. -/
theorem smallEtaleAdjunction_counit_isIso_abelian
    (G : Sheaf (SmallEtale.topology B S hS Z.1) AddCommGrpCat.{max (u + 1) v}) :
    letI := (smallBaseChange_isMorphismOfSites B S hS i hi.1).toIsContinuous
    letI := Classical.choice (smallEtalePushforward_isRightAdjoint_abelian.{v, u} B S hS i hi)
    IsIso (((smallBaseChange B S hS i hi.1).sheafAdjunctionContinuous
      AddCommGrpCat.{max (u + 1) v} (SmallEtale.topology B S hS X.1)
      (SmallEtale.topology B S hS Z.1)).counit.app G) := by
  exact (smallEtalePushforwardAb_counit_isIso_iff_fullyFaithful.{v} B S hS i hi.1).mpr
    ⟨inferInstance, inferInstance⟩ G

include h04FW h04FV in
/-- **Stacks 04E5, part (2), the essential image**, granted Stacks 04FW and Stacks 04FV for the
chart base change, the support computation `h04FX` and the essential-image half `h04CA` of
Stacks 04CA: an abelian sheaf on `X_{étale}` is in the essential image of `i_{small, *}` exactly
when its support is contained in the point set of `Z`.

`h04FX` is the half of Stacks 04FX computing the stalk of `i_{small, *}\mathcal{G}` outside
`Z`, in the form "the support of `i_{small, *}\mathcal{G}` lies in `|Z|`". Transporting it along
an isomorphism of abelian sheaves uses parts (5) of Stacks 04KB; `h04CA` is the implication the
source proves by reduction to the case of schemes. -/
theorem smallEtalePushforward_essImage_iff_abelian
    (h04FX : letI := (smallBaseChange_isMorphismOfSites B S hS i hi.1).toIsContinuous
      ∀ G : Sheaf (SmallEtale.topology B S hS Z.1) AddCommGrpCat.{max (u + 1) v},
        supportOfSheaf B S hS X.1 (((smallBaseChange B S hS i hi.1).sheafPushforwardContinuous
            AddCommGrpCat.{max (u + 1) v} (SmallEtale.topology B S hS X.1)
            (SmallEtale.topology B S hS Z.1)).obj G) ⊆
          Set.range (pointsMap B S hS Z.1 i.hom))
    (h04CA : letI := (smallBaseChange_isMorphismOfSites B S hS i hi.1).toIsContinuous
      letI := Classical.choice (smallEtalePushforward_isRightAdjoint_abelian.{v, u} B S hS i hi)
      ∀ F : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{max (u + 1) v},
        supportOfSheaf B S hS X.1 F ⊆ Set.range (pointsMap B S hS Z.1 i.hom) →
          IsIso (((smallBaseChange B S hS i hi.1).sheafAdjunctionContinuous
            AddCommGrpCat.{max (u + 1) v} (SmallEtale.topology B S hS X.1)
            (SmallEtale.topology B S hS Z.1)).unit.app F))
    (F : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{max (u + 1) v}) :
    letI := (smallBaseChange_isMorphismOfSites B S hS i hi.1).toIsContinuous
    ((smallBaseChange B S hS i hi.1).sheafPushforwardContinuous
      AddCommGrpCat.{max (u + 1) v} (SmallEtale.topology B S hS X.1)
      (SmallEtale.topology B S hS Z.1)).essImage F ↔
      supportOfSheaf B S hS X.1 F ⊆ Set.range (pointsMap B S hS Z.1 i.hom) := by
  let _ := (smallBaseChange_isMorphismOfSites B S hS i hi.1).toIsContinuous
  let _ := Classical.choice (smallEtalePushforward_isRightAdjoint_abelian.{v, u} B S hS i hi)
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨G, ⟨e⟩⟩
    exact fun x hx => h04FX G
      (supportOfSheaf_subset_of_isLocallySurjective B S hS X.1 X.property e.hom hx)
  · exact (Adjunction.isIso_unit_app_iff_mem_essImage _).mp (h04CA F h)

end AlgebraicGeometry.Space

end
