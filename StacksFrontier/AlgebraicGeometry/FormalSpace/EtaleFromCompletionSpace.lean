module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionFunctor
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.EtaleAt
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFibreProduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionRigEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubspaceLocalTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.Scheme.SchemeStructure
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleTargetChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteBaseChange

/-!
# The étale clause of Stacks 0AR4 for a morphism of algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`, let `f : R ⟶ U` be a morphism of
algebraic spaces over `S` with `U` locally Noetherian, and let `T ⊆ |U|` be a closed set of
points. The étale clause of **Stacks 0AR4** says that if `f` is locally of finite type, if the
restriction `f⁻¹(|U| ∖ T) ⟶ |U| ∖ T` of `f` to the open complement of `T` is étale, and if the
morphism of completions `f_{/T}` is étale, then `f` is étale.

For a morphism of *schemes* of the site this is
`AlgebraicGeometry.FormalSpace.isEtale_of_isEtale_completionSheafMap`. This file deduces the
statement for a morphism of algebraic spaces from it.

## Main results

* `AlgebraicGeometry.FormalSpace.isEtale_of_isEtale_completionSheafMap_space`: the étale
  clause of **Stacks 0AR4** for a morphism of algebraic spaces over `S`.

## Implementation notes

The reduction to the scheme case is the standard one: étaleness of a morphism of algebraic
spaces may be checked on one commuting square of étale charts
(`AlgebraicGeometry.Space.isEtale_iff_exists_etale_chart_square`), and base-changing to a
surjective étale chart `ψ : V ⟶ U` of the target
(`AlgebraicGeometry.Space.isEtale_of_isEtale_pullback_snd`) makes the target of that square
representable, so the chart of the target may be taken to be the identity. What is left is a
morphism `α : P ⟶ V` of objects of the site, for which the scheme-level statement applies.

Checking its five hypotheses is the content of the file.

* Local Noetherianity of the scheme of `V` is Stacks 03E8,
  `AlgebraicGeometry.Space.exists_atlas_iff_forall_etale`, applied to the étale chart `ψ`.
* The closed subscheme cut out by `|ψ|⁻¹T` is the reduced induced scheme structure of Stacks
  01J4 on the image of that set under the bijection
  `AlgebraicGeometry.Space.pointsToScheme`, which is closed by Stacks 03BX.
* Finite type of `α` is composition of the étale chart of the fibre product with the base
  change of `f`.
* Étaleness of `α` away from `|ψ|⁻¹T` is where the hypothesis on the open complement enters.
  A point of `P` outside that set lies in the open subspace cut out by the preimage of the
  open complement; that open subspace of a *representable* presheaf is again representable,
  by `AlgebraicGeometry.Space.openSiteObject`, and the morphism to `V` it carries factors
  through the open complement of `T` in `R`, hence is étale. Locality of étaleness at a point
  on the source then gives étaleness of `α` at the point.
* Étaleness of the completion of `α` is Stacks 0GI0 for the étale chart of the fibre product,
  composed with the base change of the hypothesis along the completion of `ψ`.

The last two steps both have to move across an `eqToHom`: the completion functor indexes its
source by a preimage of the given set of points, and a preimage along a composite agrees with
the iterated preimage only propositionally. The moves are made by reading the `eqToHom` as the
left edge of a cartesian square with an isomorphism for its top edge
(`CategoryTheory.IsPullback.of_horiz_isIso`), so that the base-change lemmas for the bootstrap
notion of étaleness apply to it unchanged.

## References

* [Stacks Project, Tag 0AR4](https://stacks.math.columbia.edu/tag/0AR4)
* [Stacks Project, Tag 0GI0](https://stacks.math.columbia.edu/tag/0GI0)
* [Stacks Project, Tag 0AMC](https://stacks.math.columbia.edu/tag/0AMC)
* [Stacks Project, Tag 03E8](https://stacks.math.columbia.edu/tag/03E8)
* [Stacks Project, Tag 01J4](https://stacks.math.columbia.edu/tag/01J4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.FormalSpace

attribute [local instance] Space.pointTopology

/-! ### Locality of étaleness at a point on the source -/

/-- A morphism of schemes locally of finite type over a locally Noetherian scheme whose
restriction to an open neighbourhood of a point is étale is étale at that point.

Étaleness at a point is read on the stalk, and the stalk map of the open immersion is an
isomorphism, so the stalk map of the restriction and that of the morphism itself differ by an
isomorphism; flatness, formal unramifiedness and essential finite type all respect
isomorphisms. -/
private theorem etaleAt_of_etale_opens_ι_comp {X Y : Scheme.{u}} (k : X ⟶ Y)
    [LocallyOfFiniteType k] [_root_.AlgebraicGeometry.IsLocallyNoetherian Y] (V : X.Opens)
    {x : X} (hx : x ∈ V) (h : AlgebraicGeometry.Etale (V.ι ≫ k)) :
    AlgebraicGeometry.EtaleAt k x := by
  have : _root_.AlgebraicGeometry.IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian k
  let xV : V.toScheme := ⟨x, hx⟩
  have hV : AlgebraicGeometry.IsEtaleAt (V.ι ≫ k) xV :=
    (AlgebraicGeometry.etale_iff_forall_isEtaleAt (V.ι ≫ k)).mp h _
  have hstalk : IsIso (V.ι.stalkMap xV) := inferInstance
  rw [← AlgebraicGeometry.isEtaleAt_iff_etaleAt]
  change ((V.ι ≫ k).stalkMap xV).hom.Flat ∧ ((V.ι ≫ k).stalkMap xV).hom.FormallyUnramified ∧
    ((V.ι ≫ k).stalkMap xV).hom.EssFiniteType at hV
  rw [Scheme.Hom.stalkMap_comp V.ι k xV] at hV
  have key : ∀ {P : ∀ {R S : Type u} [CommRing R] [CommRing S] (_ : R →+* S), Prop},
      RingHom.RespectsIso @P → P ((V.ι.stalkMap xV).hom.comp (k.stalkMap x).hom) →
        P (k.stalkMap x).hom := fun hP h ↦
    (@RingHom.RespectsIso.cancel_right_isIso _ hP _ _ _ (k.stalkMap x) (V.ι.stalkMap xV)
      hstalk).mp h
  exact ⟨key RingHom.Flat.respectsIso hV.1, key RingHom.FormallyUnramified.respectsIso hV.2.1,
    key RingHom.EssFiniteType.respectsIso hV.2.2⟩

/-! ### Two permanence facts for morphisms of algebraic spaces -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

local instance (priority := high) hasLimitsOfSize_presheaf_EtaleFromCompletionSpace :
    HasLimitsOfSize.{u, u} ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfSize

local instance (priority := high) hasPullback_presheaf_EtaleFromCompletionSpace
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- An étale morphism of algebraic spaces over `S` is locally of finite type: on a commuting
square of étale charts both charts of the square and the composite of the source chart with
the morphism are étale, so the induced morphism of schemes is étale by Stacks 03FV and
therefore locally of finite type. -/
private theorem isLocallyOfFiniteType_of_isEtale
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : F ⟶ G) (hg : Space.IsEtale B S hS g) :
    Space.IsLocallyOfFiniteType B S hS g := by
  intro X Y a b h ha hb hcomm
  have : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map h) :=
    Space.etale_of_etale_charts B S hS (a ≫ g) b (hg X a ha) hb h hcomm
  infer_instance

/-- The underlying morphism of schemes of a morphism of the site which is locally of finite
type as a morphism of algebraic spaces is locally of finite type: read the every-chart
condition on the square of identity charts. -/
private theorem locallyOfFiniteType_map_of_isLocallyOfFiniteType {X Y : BigFppfOver B S hS}
    (h : X ⟶ Y) (hh : Space.IsLocallyOfFiniteType B S hS (yoneda.map h)) :
    LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map h) :=
  hh X Y (𝟙 _) (𝟙 _) h (Space.presheaf_etale_id B S hS X) (Space.presheaf_etale_id B S hS Y)
    (by simp)

/-! ### Transport of the bootstrap notion of étaleness -/

/-- Shorthand for the bootstrap condition of Stacks 03XZ at étaleness: a morphism of fppf
sheaves of `Type (u + 1)` which is representable by algebraic spaces and all of whose base
changes along universe-lifted scheme-valued points of its target are étale. This is the shape
in which étaleness of a morphism of completions is stated throughout this library. -/
private abbrev BootstrapIsEtale {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (a : F ⟶ G) :
    Prop :=
  ∃ hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS a,
    Space.HasPropertyULift.{u + 1} B S hS
      (fun ⦃A C : Space.AlgebraicSpacesULift.{u + 1} B S hS⦄ (g : A ⟶ C) ↦
        Space.IsEtaleULift.{u + 1} B S hS g.hom) a hrep

/-- A base change of a morphism which is étale in the bootstrap sense of Stacks 03XZ is again
étale in that sense: representability and the property are both stable under base change. -/
private theorem bootstrapIsEtale_of_isPullback
    {F G G' H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (p : H ⟶ F) (a' : H ⟶ G') (a : F ⟶ G) (g : G' ⟶ G) (hsq : IsPullback p a' a g)
    (ha : BootstrapIsEtale B S hS a) : BootstrapIsEtale B S hS a' := by
  obtain ⟨hrep, hP⟩ := ha
  have hrep' :=
    Space.isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS p a' a g hsq hrep
  exact ⟨hrep', hasPropertyULift_isEtaleULift_of_isPullback B S hS p a' a g hsq hrep hrep' hP⟩

/-- Étaleness in the bootstrap sense of Stacks 03XZ is stable under composition. -/
private theorem bootstrapIsEtale_comp {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (g : F ⟶ G) (a : G ⟶ H) (hg : BootstrapIsEtale B S hS g) (ha : BootstrapIsEtale B S hS a) :
    BootstrapIsEtale B S hS (g ≫ a) := by
  obtain ⟨hrg, hPg⟩ := hg
  obtain ⟨hra, hPa⟩ := ha
  refine ⟨Space.isRepresentableByAlgebraicSpacesULift_comp B S hS g a hrg hra, ?_⟩
  intro W ξ
  exact isEtaleULift_pullback_fst_comp B S hS hra (fun W' ξ' ↦ hPa W' ξ') (fun W' ξ' ↦ hPg W' ξ')
    W ξ

/-! ### Reindexing a morphism of completions -/

variable {B S hS}

/-- The restriction morphism between completions does not depend on the chosen set of points
of the source beyond its value: two equal index sets give the same morphism, up to the
`eqToHom` comparing the two completions. -/
private theorem completionSheafRestrict_index_eq
    {F' F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F' ⟶ F)
    {T₁ T₂ : Set (Space.points B S hS F')} (hT : T₁ = T₂) (T : Set (Space.points B S hS F))
    (h₁ : T₁ ⊆ Space.pointsMap B S hS F' f ⁻¹' T)
    (h₂ : T₂ ⊆ Space.pointsMap B S hS F' f ⁻¹' T) :
    Space.completionSheafRestrict B S hS f T₁ T h₁ =
      eqToHom (congrArg (Space.completionSheaf B S hS F') hT) ≫
        Space.completionSheafRestrict B S hS f T₂ T h₂ := by
  subst hT
  simp

/-- The preimage of a set of points along a morphism which factors as `g ≫ k` is the iterated
preimage along the two factors. -/
private theorem preimage_pointsMap_eq_of_eq_comp
    {F'' F' F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a : F'' ⟶ F} {g : F'' ⟶ F'} {k : F' ⟶ F}
    (hak : a = g ≫ k) (T : Set (Space.points B S hS F)) :
    Space.pointsMap B S hS F'' a ⁻¹' T =
      Space.pointsMap B S hS F'' g ⁻¹' (Space.pointsMap B S hS F' k ⁻¹' T) := by
  rw [hak, Space.pointsMap_comp B S hS F'' g k]
  rfl

/-- **Functoriality of the completion.** A morphism which factors as `g ≫ k` has for its
completion the composite of the completions of `g` and of `k`, up to the `eqToHom` comparing
the preimage of the set of points along the morphism with the iterated preimage along the two
factors. -/
private theorem completionSheafMap_eq_eqToHom_comp
    {F'' F' F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a : F'' ⟶ F} (g : F'' ⟶ F') (k : F' ⟶ F)
    (hak : a = g ≫ k) (T : Set (Space.points B S hS F)) :
    Space.completionSheafMap B S hS a T =
      eqToHom (congrArg (Space.completionSheaf B S hS F'')
          (preimage_pointsMap_eq_of_eq_comp hak T)) ≫
        Space.completionSheafMap B S hS g (Space.pointsMap B S hS F' k ⁻¹' T) ≫
          Space.completionSheafMap B S hS k T := by
  have hT := preimage_pointsMap_eq_of_eq_comp hak T
  have hcomp := preimage_pointsMap_eq_of_eq_comp (rfl : g ≫ k = g ≫ k) T
  rw [← Space.completionSheafRestrict_self B S hS a T subset_rfl,
    completionSheafRestrict_index_eq a hT T subset_rfl hT.ge,
    Space.completionSheafRestrict_congr B S hS hak _ T hT.ge hcomp.ge,
    Space.completionSheafRestrict_comp B S hS g k _ _ T subset_rfl subset_rfl hcomp.ge,
    Space.completionSheafRestrict_self B S hS g _ subset_rfl,
    Space.completionSheafRestrict_self B S hS k T subset_rfl]

/-! ### Étaleness of a chart away from the closed set -/

variable (B S hS)

/-- **An open neighbourhood of a point of a chart, carried into an open subspace.** Let
`Tc ⊆ |R|` be an open set of points of an algebraic space `R` and `pr : P ⟶ R` an étale morphism
from an object of the site. A point of `P` over `Tc` lies in an open subscheme `VP` of the scheme
of `P` whose morphism to `R` factors, by an étale morphism, through the open subspace of `R` cut
out by `Tc`.

The open subscheme is the one cut out by `|pr|⁻¹Tc`: `P` being representable, it is an open
subscheme of the scheme of `P` by Stacks 03BX and `AlgebraicGeometry.Space.openSiteObject`; all
of its points lie over `Tc`, so its morphism to `R` factors through the open subspace, and the
factorization is étale by left cancellation. -/
theorem exists_opens_lift_openSubspaceOfPoints
    {R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hR : IsAlgebraicSpace B S hS R)
    {Tc : Set (Space.points B S hS R)} (hTc : IsOpen Tc)
    {P : BigFppfOver B S hS} (pr : yoneda.obj P ⟶ R) (hpr : Space.IsEtale B S hS pr)
    (p : Space.points B S hS (yoneda.obj P))
    (hp : Space.pointsMap B S hS (yoneda.obj P) pr p ∈ Tc) :
    ∃ VP : ((BigFppfOver.toScheme B S hS).obj P).Opens,
      (VP : Set ((BigFppfOver.toScheme B S hS).obj P)) = Space.pointsToScheme B S hS P ''
        (Space.pointsMap B S hS (yoneda.obj P) pr ⁻¹' Tc) ∧
      Space.pointsToScheme B S hS P p ∈ VP ∧
      ∃ δ : yoneda.obj (Space.openSiteObject B S hS P VP) ⟶
          (Space.openSubspaceOfPoints B S hS R Tc).toFunctor,
        Space.IsEtale B S hS δ ∧
          δ ≫ (Space.openSubspaceOfPoints B S hS R Tc).ι =
            yoneda.map (Space.openSiteObjectHom B S hS P VP) ≫ pr := by
  have hAopen : Space.IsOpenSubspace B S hS (Space.openSubspaceOfPoints B S hS R Tc) :=
    Space.isOpenSubspace_openSubspaceOfPoints B S hS hR Tc hTc
  have hNopen : IsOpen (Space.pointsMap B S hS (yoneda.obj P) pr ⁻¹' Tc) :=
    hTc.preimage (Space.continuous_pointsMap B S hS pr)
  have hbij : Function.Bijective (Space.pointsToScheme B S hS P) :=
    ⟨Space.injective_pointsToScheme B S hS P, Space.surjective_pointsToScheme B S hS P⟩
  -- the open subscheme of the scheme of `P` cut out by the preimage of `Tc`
  have himgopen : IsOpen (Space.pointsToScheme B S hS P ''
      (Space.pointsMap B S hS (yoneda.obj P) pr ⁻¹' Tc)) := by
    rw [← isClosed_compl_iff, ← Set.image_compl_eq hbij]
    exact Space.isClosed_image_pointsToScheme B S hS P hNopen.isClosed_compl
  obtain ⟨VP, hVP⟩ : ∃ VP : ((BigFppfOver.toScheme B S hS).obj P).Opens,
      (VP : Set ((BigFppfOver.toScheme B S hS).obj P)) = Space.pointsToScheme B S hS P ''
        (Space.pointsMap B S hS (yoneda.obj P) pr ⁻¹' Tc) :=
    ⟨⟨_, himgopen⟩, rfl⟩
  have hxVP : Space.pointsToScheme B S hS P p ∈ VP := by
    change Space.pointsToScheme B S hS P p ∈ (VP : Set _)
    rw [hVP]
    exact ⟨p, hp, rfl⟩
  -- that open subscheme as an object of the site, with its open immersion into `P`
  have hmapi : (BigFppfOver.toScheme B S hS).map (Space.openSiteObjectHom B S hS P VP) = VP.ι :=
    Space.map_openSiteObjectHom B S hS P VP
  have hyi : Space.IsEtale B S hS (yoneda.map (Space.openSiteObjectHom B S hS P VP)) := by
    refine (Space.isEtale_iff_presheaf_of_yoneda B S hS _).mpr
      ((Space.presheaf_yoneda_map_etale_iff B S hS _).mpr ?_)
    rw [hmapi]
    exact (inferInstance : AlgebraicGeometry.Etale VP.ι)
  -- every point of the open subscheme maps into the preimage of `Tc`
  have hiN : ∀ q : Space.points B S hS
        (yoneda.obj (Space.openSiteObject B S hS P VP)),
      Space.pointsMap B S hS (yoneda.obj (Space.openSiteObject B S hS P VP))
          (yoneda.map (Space.openSiteObjectHom B S hS P VP)) q ∈
        Space.pointsMap B S hS (yoneda.obj P) pr ⁻¹' Tc := by
    intro q
    have h1 : Space.pointsToScheme B S hS P
          (Space.pointsMap B S hS (yoneda.obj (Space.openSiteObject B S hS P VP))
            (yoneda.map (Space.openSiteObjectHom B S hS P VP)) q) =
        VP.ι (Space.pointsToScheme B S hS (Space.openSiteObject B S hS P VP) q) := by
      rw [Space.pointsToScheme_pointsMap B S hS (Space.openSiteObjectHom B S hS P VP) q,
        hmapi]
      rfl
    have h2 : VP.ι (Space.pointsToScheme B S hS (Space.openSiteObject B S hS P VP) q) ∈
        (VP : Set ((BigFppfOver.toScheme B S hS).obj P)) := by
      rw [← Scheme.Opens.range_ι VP]
      exact Set.mem_range_self _
    rw [hVP] at h2
    obtain ⟨n, hn, hne⟩ := h2
    exact Space.injective_pointsToScheme B S hS P (hne.trans h1.symm) ▸ hn
  -- the composite to `R` factors through the open subspace cut out by `Tc`
  have hle : Subfunctor.range (yoneda.map (Space.openSiteObjectHom B S hS P VP) ≫ pr) ≤
      Space.openSubspaceOfPoints B S hS R Tc := by
    refine (Space.range_le_openSubspaceOfPoints_range_pointsMap
      (yoneda.map (Space.openSiteObjectHom B S hS P VP) ≫ pr)).trans
      (Space.openSubspaceOfPoints_mono B S hS ?_)
    rintro y ⟨q, rfl⟩
    rw [Space.pointsMap_comp B S hS _ (yoneda.map (Space.openSiteObjectHom B S hS P VP)) pr]
    exact hiN q
  have hδ : Subfunctor.lift (yoneda.map (Space.openSiteObjectHom B S hS P VP) ≫ pr) hle ≫
      (Space.openSubspaceOfPoints B S hS R Tc).ι =
      yoneda.map (Space.openSiteObjectHom B S hS P VP) ≫ pr := Subfunctor.lift_ι _ _
  have hδe : Space.IsEtale B S hS
      (Subfunctor.lift (yoneda.map (Space.openSiteObjectHom B S hS P VP) ≫ pr) hle) :=
    Space.isEtale_of_isEtale_over B S hS
      (isAlgebraicSpace_yoneda B S hS (Space.openSiteObject B S hS P VP)) hAopen.1 hR _ _ _
      (Space.isEtale_comp B S hS hyi hpr) (Space.isEtale_ι_of_isOpenSubspace hAopen) hδ
  exact ⟨VP, hVP, hxVP, _, hδe, hδ⟩

/-- **Étaleness of a chart of the source away from the closed set.** Let `f : R ⟶ U` be a
morphism of algebraic spaces over `S`, let `Tc ⊆ |R|` be an open set of points and assume the
restriction of `f` to the open subspace cut out by `Tc` is étale. Let `α : P ⟶ V` be a
morphism of objects of the site fitting into a commuting square with an étale chart
`ψ : V ⟶ U` of the target and an étale morphism `pr : P ⟶ R`. Then `α` is étale at every point
of `P` whose image in `|R|` lies in `Tc`.

The point lies in the open subspace of `P` cut out by `|pr|⁻¹Tc`, which — `P` being
representable — is the presheaf represented by an open subscheme of the scheme of `P`, by
Stacks 03BX and `AlgebraicGeometry.Space.openSiteObject`. The morphism to `R` carried by that
open subscheme has all its points in `Tc`, hence factors through the open subspace cut out by
`Tc`; the factorization is étale by left cancellation, so its composite with the restriction of
`f` is étale. That composite is the chart of `U` attached to the square, so Stacks 03FV
identifies the induced morphism of schemes as étale, and étaleness at the point follows by
locality on the source. -/
private theorem etaleAt_of_isEtale_restriction
    {R U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hR : IsAlgebraicSpace B S hS R) (f : R ⟶ U)
    {Tc : Set (Space.points B S hS R)} (hTc : IsOpen Tc)
    (hAf : Space.IsEtale B S hS ((Space.openSubspaceOfPoints B S hS R Tc).ι ≫ f))
    {P V : BigFppfOver B S hS} (pr : yoneda.obj P ⟶ R) (hpr : Space.IsEtale B S hS pr)
    (ψ : yoneda.obj V ⟶ U)
    (hψe : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf ψ)
    (α : P ⟶ V) (hcomm : yoneda.map α ≫ ψ = pr ≫ f)
    [LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map α)]
    [_root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)]
    (p : Space.points B S hS (yoneda.obj P))
    (hp : Space.pointsMap B S hS (yoneda.obj P) pr p ∈ Tc) :
    AlgebraicGeometry.EtaleAt ((BigFppfOver.toScheme B S hS).map α)
      (Space.pointsToScheme B S hS P p) := by
  obtain ⟨VP, -, hxVP, δ, hδe, hδ⟩ :=
    exists_opens_lift_openSubspaceOfPoints B S hS hR hTc pr hpr p hp
  have hmapi : (BigFppfOver.toScheme B S hS).map (Space.openSiteObjectHom B S hS P VP) = VP.ι :=
    Space.map_openSiteObjectHom B S hS P VP
  -- hence the chart of `U` attached to the square is étale
  have hfin : Space.IsEtale B S hS
      (yoneda.map (Space.openSiteObjectHom B S hS P VP) ≫ pr ≫ f) := by
    have h := Space.isEtale_comp B S hS hδe hAf
    rwa [← Category.assoc, hδ, Category.assoc] at h
  have hφ : Space.IsEtale B S hS
      (yoneda.map (Space.openSiteObjectHom B S hS P VP ≫ α) ≫ ψ) := by
    rw [Functor.map_comp, Category.assoc, hcomm]
    exact hfin
  have hEt : AlgebraicGeometry.Etale
      ((BigFppfOver.toScheme B S hS).map (Space.openSiteObjectHom B S hS P VP ≫ α)) :=
    Space.etale_of_etale_charts B S hS _ ψ
      ((Space.isEtale_iff_presheaf_of_yoneda B S hS _).mp hφ) hψe _ rfl
  have hEt' : AlgebraicGeometry.Etale
      ((BigFppfOver.toScheme B S hS).map (Space.openSiteObjectHom B S hS P VP) ≫
        (BigFppfOver.toScheme B S hS).map α) := by
    simpa only [Functor.map_comp] using hEt
  refine etaleAt_of_etale_opens_ι_comp ((BigFppfOver.toScheme B S hS).map α) VP hxVP ?_
  rw [← hmapi]
  exact hEt'

/-- **A chart square of a morphism étale over the open complement of `T` is étale off `T`.**
Let `f : R ⟶ U` be a morphism of algebraic spaces over `S` and `T ⊆ |U|` closed, such that the
restriction `f⁻¹(|U| ∖ T) ⟶ |U| ∖ T` is étale. For a commuting square of an étale chart
`pr : P ⟶ R`, an étale chart `ψ : V ⟶ U` and a morphism `α : P ⟶ V` of the site, the morphism of
schemes underlying `α` is étale at every point of `P` lying over the complement of `T`.

This is the step of the source's proofs of Stacks 0GDH and 0AR2 saying that the charts of `f`
induce étale (respectively smooth) morphisms away from the inverse images of `T`. -/
theorem etaleAt_of_isEtale_openComplementRestriction
    {R U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hR : IsAlgebraicSpace B S hS R)
    (hU : IsAlgebraicSpace B S hS U) (f : R ⟶ U) (T : Set (Space.points B S hS U))
    (hT : IsClosed T)
    (haway : Space.IsEtale B S hS (Space.openComplementRestriction B S hS f T))
    {P V : BigFppfOver B S hS} (pr : yoneda.obj P ⟶ R) (hpr : Space.IsEtale B S hS pr)
    (ψ : yoneda.obj V ⟶ U)
    (hψe : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf ψ)
    (α : P ⟶ V) (hcomm : yoneda.map α ≫ ψ = pr ≫ f)
    [LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map α)]
    [_root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)]
    (p : Space.points B S hS (yoneda.obj P))
    (hp : Space.pointsMap B S hS (yoneda.obj P) (pr ≫ f) p ∉ T) :
    AlgebraicGeometry.EtaleAt ((BigFppfOver.toScheme B S hS).map α)
      (Space.pointsToScheme B S hS P p) := by
  have hTcopen : IsOpen (Space.pointsMap B S hS R f ⁻¹' Tᶜ) :=
    hT.isOpen_compl.preimage (Space.continuous_pointsMap B S hS f)
  have hAf : Space.IsEtale B S hS
      ((Space.openSubspaceOfPoints B S hS R (Space.pointsMap B S hS R f ⁻¹' Tᶜ)).ι ≫ f) := by
    rw [← Space.openComplementRestriction_ι B S hS f T]
    exact Space.isEtale_comp B S hS haway (Space.isEtale_ι_of_isOpenSubspace
      (Space.isOpenSubspace_openSubspaceOfPoints_compl_of_isClosed B S hS hU T hT))
  refine etaleAt_of_isEtale_restriction B S hS hR f hTcopen hAf pr hpr ψ hψe α hcomm p ?_
  change Space.pointsMap B S hS R f (Space.pointsMap B S hS (yoneda.obj P) pr p) ∈ Tᶜ
  rw [← Function.comp_apply (f := Space.pointsMap B S hS R f), ← Space.pointsMap_comp]
  exact hp

/-! ### The étale clause of Stacks 0AR4 for algebraic spaces -/

/-- **Stacks 0AR4, the étale clause, for a morphism of algebraic spaces.** Let `f : R ⟶ U` be a
morphism of algebraic spaces over `S` which is locally of finite type, with `U` locally
Noetherian, and let `T ⊆ |U|` be closed. If the restriction of `f` to the open complement of
`T` is étale and the morphism of completions `f_{/T}` is étale in the bootstrap sense of
Stacks 03XZ, then `f` is étale.

Étaleness of a morphism of algebraic spaces may be checked on a single commuting square of
étale charts, and after base change to a surjective étale chart of the target that square may
be taken to have the identity for its chart of the target. The morphism of schemes left over is
handled by the scheme case,
`AlgebraicGeometry.FormalSpace.isEtale_of_isEtale_completionSheafMap`. -/
theorem isEtale_of_isEtale_completionSheafMap_space
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {R U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hR : IsAlgebraicSpace B S hS R) (hU : IsAlgebraicSpace B S hS U)
    (f : R ⟶ U) (T : Set (Space.points B S hS U)) (hT : IsClosed T)
    (hUnoeth : Space.HasEtaleLocalProperty B S hS U
      (fun W : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian W))
    (hf : Space.IsLocallyOfFiniteType B S hS f)
    (haway : Space.IsEtale B S hS (Space.openComplementRestriction B S hS f T))
    (hetale : ∃ hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (Space.completionSheafMap B S hS f T).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun ⦃A C : Space.AlgebraicSpacesULift.{u + 1} B S hS⦄ (g : A ⟶ C) ↦
          Space.IsEtaleULift.{u + 1} B S hS g.hom)
        (Space.completionSheafMap B S hS f T).hom hrep) :
    Space.IsEtale B S hS f := by
  -- a surjective étale chart of the target, and the base change of `f` along it
  obtain ⟨V, ψ, hψs, hψe⟩ := hU.exists_atlas
  have hVsp := isAlgebraicSpace_yoneda B S hS V
  have hψE : Space.IsEtale B S hS ψ := (Space.isEtale_iff_presheaf_of_yoneda B S hS ψ).mpr hψe
  refine Space.isEtale_of_isEtale_pullback_snd B S hS hU f ψ hψs hψe ?_
  have hPb : IsAlgebraicSpace B S hS (pullback f ψ) :=
    isAlgebraicSpace_pullback B S hS f ψ hR hVsp hU
  -- a surjective étale chart of the base change, and the morphism of the site it induces
  obtain ⟨P, π, hπs, hπe⟩ := hPb.exists_atlas
  have hπE : Space.IsEtale B S hS π := (Space.isEtale_iff_presheaf_of_yoneda B S hS π).mpr hπe
  obtain ⟨α, hα⟩ : ∃ α : P ⟶ V, yoneda.map α = π ≫ pullback.snd f ψ :=
    ⟨yoneda.preimage (π ≫ pullback.snd f ψ), yoneda.map_preimage _⟩
  rw [Space.isEtale_iff_exists_etale_chart_square B S hS hPb hVsp]
  refine ⟨P, V, π, 𝟙 (yoneda.obj V), α, by simp [hα], hπs, hπe,
    Space.presheaf_etale_id B S hS V, ?_⟩
  -- local Noetherianity of the scheme of the chart of the target, by Stacks 03E8
  have hVnoeth : _root_.AlgebraicGeometry.IsLocallyNoetherian
      ((BigFppfOver.toScheme B S hS).obj V) :=
    (Space.exists_atlas_iff_forall_etale B S hS U
      (fun W : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian W) hU).mp
      hUnoeth V ψ hψe
  -- the morphism of the site is locally of finite type
  have hlftα : Space.IsLocallyOfFiniteType B S hS (yoneda.map α) := by
    rw [hα]
    exact Space.isLocallyOfFiniteType_comp B S hS (isAlgebraicSpace_yoneda B S hS P) hPb hVsp
      π (pullback.snd f ψ) (isLocallyOfFiniteType_of_isEtale B S hS π hπE)
      (Space.IsLocallyOfFiniteType.of_isPullback B S hS
        (IsPullback.of_hasPullback f ψ).flip hR hU hf)
  have _ := locallyOfFiniteType_map_of_isLocallyOfFiniteType B S hS α hlftα
  -- the closed subscheme of the chart of the target cut out by the preimage of `T`
  have hZclosed : IsClosed (Space.pointsToScheme B S hS V ''
      (Space.pointsMap B S hS (yoneda.obj V) ψ ⁻¹' T)) :=
    Space.isClosed_image_pointsToScheme B S hS V
      (hT.preimage (Space.continuous_pointsMap B S hS ψ))
  refine (Space.presheaf_yoneda_map_etale_iff B S hS α).mp
    ((Space.isEtale_iff_presheaf_of_yoneda B S hS (yoneda.map α)).mp
      (isEtale_of_isEtale_completionSheafMap B S hS α
        (Space.pointsMap B S hS (yoneda.obj V) ψ ⁻¹' T)
        (Scheme.reducedInduced (X := (BigFppfOver.toScheme B S hS).obj V)
          ⟨_, hZclosed⟩).ι (Scheme.SchemeStructure.range_ι _) hlftα ?_ ?_))
  · intro p hp
    have hsq : (π ≫ pullback.fst f ψ) ≫ f = yoneda.map α ≫ ψ := by
      rw [hα, Category.assoc, Category.assoc, (IsPullback.of_hasPullback f ψ).w]
    refine etaleAt_of_isEtale_openComplementRestriction B S hS hR hU f T hT haway
      (π ≫ pullback.fst f ψ)
      (Space.isEtale_comp B S hS hπE
        (Space.isEtale_pullback_fst B S hS hR hU hVsp f ψ hψE)) ψ hψe α hsq.symm p ?_
    rw [hsq, Space.pointsMap_comp B S hS _ (yoneda.map α) ψ]
    exact hp
  · -- étaleness of the completion
    -- the completion of the base change of `f` is a base change of the completion of `f`
    have hpb := Space.isPullback_completionSheafMap_of_isPullback B S hS
      (IsPullback.of_hasPullback f ψ) T
    have hpb' : IsPullback
        (eqToHom (congrArg (Space.completionSheaf B S hS (pullback f ψ))
            (Space.preimage_pointsMap_eq_of_comm B S hS
              (IsPullback.of_hasPullback f ψ).w T)).symm ≫
          Space.completionSheafMap B S hS (pullback.fst f ψ)
            (Space.pointsMap B S hS R f ⁻¹' T))
        (Space.completionSheafMap B S hS (pullback.snd f ψ)
          (Space.pointsMap B S hS (yoneda.obj V) ψ ⁻¹' T))
        (Space.completionSheafMap B S hS f T) (Space.completionSheafMap B S hS ψ T) :=
      hpb.of_iso (eqToIso (congrArg (Space.completionSheaf B S hS (pullback f ψ))
          (Space.preimage_pointsMap_eq_of_comm B S hS (IsPullback.of_hasPullback f ψ).w T)))
        (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)
    have hbcfV : BootstrapIsEtale B S hS
        (Space.completionSheafMap B S hS (pullback.snd f ψ)
          (Space.pointsMap B S hS (yoneda.obj V) ψ ⁻¹' T)).hom :=
      bootstrapIsEtale_of_isPullback B S hS _ _ _ _
        (hpb'.map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))) hetale
    -- the completion of the chart of the base change is étale by Stacks 0GI0
    have hbcπ : BootstrapIsEtale B S hS
        (Space.completionSheafMap B S hS π
          (Space.pointsMap B S hS (pullback f ψ) (pullback.snd f ψ) ⁻¹'
            (Space.pointsMap B S hS (yoneda.obj V) ψ ⁻¹' T))).hom :=
      isEtale_completionSheafMap B S hS (isAlgebraicSpace_yoneda B S hS P) hPb π _ hπE
    have hbccomp := bootstrapIsEtale_comp B S hS _ _ hbcπ hbcfV
    -- reindex: the completion of `α` is the composite, up to an `eqToHom`
    have hTeq := preimage_pointsMap_eq_of_eq_comp hα
      (Space.pointsMap B S hS (yoneda.obj V) ψ ⁻¹' T)
    have hsq : IsPullback
        (eqToHom (congrArg (Space.completionSheaf B S hS (yoneda.obj P)) hTeq))
        (Space.completionSheafMap B S hS (yoneda.map α)
          (Space.pointsMap B S hS (yoneda.obj V) ψ ⁻¹' T))
        (Space.completionSheafMap B S hS π
            (Space.pointsMap B S hS (pullback f ψ) (pullback.snd f ψ) ⁻¹'
              (Space.pointsMap B S hS (yoneda.obj V) ψ ⁻¹' T)) ≫
          Space.completionSheafMap B S hS (pullback.snd f ψ)
            (Space.pointsMap B S hS (yoneda.obj V) ψ ⁻¹' T))
        (𝟙 _) := by
      refine IsPullback.of_horiz_isIso ⟨?_⟩
      rw [Category.comp_id, completionSheafMap_eq_eqToHom_comp π (pullback.snd f ψ) hα
        (Space.pointsMap B S hS (yoneda.obj V) ψ ⁻¹' T)]
    exact bootstrapIsEtale_of_isPullback B S hS _ _ _ _
      (hsq.map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))) hbccomp

end AlgebraicGeometry.FormalSpace

end
