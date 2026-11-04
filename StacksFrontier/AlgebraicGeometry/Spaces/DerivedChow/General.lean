module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedChow.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedChow.Noetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ProperFlatNoetherianModel
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeDerivedInverse
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTorIndependentBaseChange
import StacksCore.Tactic.StacksAttribute

/-!
# The derived Chow lemma over a general ring (Stacks 0CTR)

Let `g : T ⟶ S` be a morphism of a big fppf site, `X₀` an algebraic space over `S` with a datum
`D₀` of the derived Chow lemma at `x₀` (`AlgebraicGeometry.Space.DerivedChowDatum`), and `X` an
algebraic space over `T` with `X ≅ R X₀`, its restriction to `T`. If the closed immersion
`W₀ ⟶ X₀ ×_S V₀` of `D₀` is Tor independent of the base changes of `X₀ ×_S V₀` along morphisms
of schemes to `S` (`AlgebraicGeometry.Space.DerivedChowDatum.TorIndependentOverBase`), then the
restriction of `D₀` is a datum of the derived Chow lemma on `X` at every point `x` over `x₀`.
This is the first paragraph of the source's proof; with the Noetherian case and the
Noetherian approximation of `X` it proves Stacks 0CTR.

The restricted datum is `(n, R Z₀, R V₀, E)` with `E` the derived pullback of `E₀` along
`X ×_T ℙⁿ_T ≅ R(X₀ ×_S ℙⁿ_S) ⟶ X₀ ×_S ℙⁿ_S`. The second arrow is a morphism of algebraic spaces
over `S` after the lower-shriek extension `Λ`, and the derived pullback is read on `R(X₀ ×_S ℙⁿ_S)`
through the equivalence `D(𝒪_{R Y}) ≌ D(𝒪_{Λ R Y})` (`AlgebraicGeometry.Space.relocalizeInverse`).

## Main results

* `AlgebraicGeometry.Space.DerivedChowDatum.nonempty_baseChange`: the restricted datum.
* `AlgebraicGeometry.Space.nonempty_derivedChowDatum`: **Stacks 0CTR.**

## References

* [Stacks Project, Tag 0CTR](https://stacks.math.columbia.edu/tag/0CTR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 10000] HasDerivedCategory.standard

open DerivedChow

namespace DerivedChowDatum

variable {B : BigFppfSite.{u}} {T S : Scheme.{u}} {hT : B.Contains T} {hS : B.Contains S}
  (g : B.obj hT ⟶ B.obj hS) {X₀ : AlgebraicSpaces B S hS} {x₀ : points B S hS X₀.1}
  (D₀ : DerivedChowDatum X₀ x₀) {X : AlgebraicSpaces B T hT}
  (eX : X.1 ≅ (OverShriek.relocalizeRestrict g).obj X₀.1)

/-- A point of `R Y` below which a point of `X` lies over its image in `Y` lifts to `R X`. -/
private theorem exists_points_relocalizeRestrict_map {T S : Scheme.{u}} {B : BigFppfSite.{u}}
    {hT : B.Contains T} {hS : B.Contains S} (g : B.obj hT ⟶ B.obj hS)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (a : points B S hS X)
    (b : points B T hT ((OverShriek.relocalizeRestrict g).obj Y))
    (hab : pointsMap B S hS X f a = pointsMap B S hS _ (OverShriek.relocalizeRestrictCounit g Y)
      (pointsRelocalize B T S hT hS g _ b)) :
    ∃ z : points B T hT ((OverShriek.relocalizeRestrict g).obj X),
      pointsMap B T hT _ ((OverShriek.relocalizeRestrict g).map f) z = b := by
  obtain ⟨w, -, hw⟩ := exists_points_of_isPullback B S hS
    (isPullback_relocalize_relocalizeRestrict_map B S hS f hT g) a _ hab
  obtain ⟨z, rfl⟩ := pointsRelocalize_surjective B T S hT hS g _ w
  rw [← pointsRelocalize_naturality] at hw
  exact ⟨z, pointsRelocalize_injective B T S hT hS g _ hw⟩

/-- `ℙⁿ_T` lies in the site, given a morphism `T ⟶ S` of the site. -/
theorem bcContains (g' : B.obj hT ⟶ B.obj hS) : B.Contains (projectiveSpaceOver D₀.n T) :=
  contains_projectiveSpaceOver_of_hom g' D₀.n D₀.contains

/-- The isomorphism `X ×_T ℙⁿ_T ≅ R(X₀ ×_S ℙⁿ_S)` of the restricted datum. -/
abbrev bcProductIso :
    (product B T hT X D₀.n (bcContains D₀ g)).1 ≅
      (relocalizeRestrictSpace g (product B S hS X₀ D₀.n D₀.contains)).1 :=
  restrictProductIso g eX D₀.n D₀.contains (bcContains D₀ g)

/-- The isomorphism `R(ℙⁿ_S) ≅ ℙⁿ_T` of the restricted datum. -/
abbrev bcProjIso :
    (relocalizeRestrictSpace g (schemeSpace (projectiveSpaceSiteObj B S hS D₀.n D₀.contains))).1 ≅
      yoneda.obj (projectiveSpaceSiteObj B T hT D₀.n (bcContains D₀ g)) :=
  restrictYonedaProjectiveSpaceIso g D₀.n D₀.contains (bcContains D₀ g)

/-- The closed immersion `R Z₀ ⟶ X ×_T ℙⁿ_T` of the restricted datum. -/
def bcI : relocalizeRestrictSpace g D₀.Z ⟶ product B T hT X D₀.n (bcContains D₀ g) :=
  restrictHom g D₀.i ≫ ObjectProperty.homMk (bcProductIso g D₀ eX).inv

/-- The open immersion `R V₀ ⟶ ℙⁿ_T` of the restricted datum. -/
def bcV : relocalizeRestrictSpace g D₀.V ⟶
    schemeSpace (projectiveSpaceSiteObj B T hT D₀.n (bcContains D₀ g)) :=
  restrictHom g D₀.v ≫ ObjectProperty.homMk (bcProjIso g D₀).hom

/-- The composite `R Z₀ ⟶ X ×_T ℙⁿ_T ⟶ ℙⁿ_T` is the restriction of `Z₀ ⟶ ℙⁿ_S` followed by
`R(ℙⁿ_S) ≅ ℙⁿ_T`. -/
theorem bcI_comp_snd :
    (bcI g D₀ eX ≫ productSnd X D₀.n (bcContains D₀ g)).hom =
      (OverShriek.relocalizeRestrict g).map (D₀.i ≫ productSnd X₀ D₀.n D₀.contains).hom ≫
        (bcProjIso g D₀).hom := by
  change (OverShriek.relocalizeRestrict g).map D₀.i.hom ≫ (bcProductIso g D₀ eX).inv ≫
    (productSnd X D₀.n (bcContains D₀ g)).hom = _
  rw [restrictProductIso_inv_snd]
  rfl

/-- The composite `R Z₀ ⟶ X ×_T ℙⁿ_T ⟶ X` is the restriction of `Z₀ ⟶ X₀` followed by
`R X₀ ≅ X`. -/
theorem bcI_comp_fst :
    (bcI g D₀ eX ≫ productFst X D₀.n (bcContains D₀ g)).hom =
      (OverShriek.relocalizeRestrict g).map (D₀.i ≫ productFst X₀ D₀.n D₀.contains).hom ≫
        eX.inv := by
  change (OverShriek.relocalizeRestrict g).map D₀.i.hom ≫ (bcProductIso g D₀ eX).inv ≫
    (productFst X D₀.n (bcContains D₀ g)).hom = _
  rw [restrictProductIso_inv_fst]
  rfl

/-- The square exhibiting the restriction of `W₀` as the part of `R Z₀` over `R V₀`. -/
theorem bc_isPullback_overOpen :
    IsPullback ((OverShriek.relocalizeRestrict g).map (overOpenι D₀.i D₀.v).hom)
      ((OverShriek.relocalizeRestrict g).map (overOpenToOpen D₀.i D₀.v).hom)
      (bcI g D₀ eX ≫ productSnd X D₀.n (bcContains D₀ g)).hom (bcV g D₀).hom := by
  have h := ((IsPullback.of_hasPullback (D₀.i ≫ productSnd X₀ D₀.n D₀.contains).hom
      D₀.v.hom).map (OverShriek.relocalizeRestrict g)).paste_vert
    (IsPullback.of_vert_isIso (f := (bcProjIso g D₀).hom) (snd := 𝟙 _) (g := (bcV g D₀).hom)
      ⟨(Category.id_comp _).symm⟩)
  rw [Category.comp_id] at h
  rwa [bcI_comp_snd]

/-- The part `W` of the restricted datum is the restriction of the part `W₀` of `D₀`. -/
def bcOverOpenIso :
    (overOpen (bcI g D₀ eX) (bcV g D₀)).1 ≅ (relocalizeRestrictSpace g (overOpen D₀.i D₀.v)).1 :=
  IsPullback.isoIsPullback _ _ (IsPullback.of_hasPullback _ _) (bc_isPullback_overOpen g D₀ eX)

/-- `W ≅ R W₀` commutes with the maps to `R Z₀`. -/
@[reassoc]
theorem bcOverOpenIso_hom_ι :
    (bcOverOpenIso g D₀ eX).hom ≫ (OverShriek.relocalizeRestrict g).map (overOpenι D₀.i D₀.v).hom =
      (overOpenι (bcI g D₀ eX) (bcV g D₀)).hom :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- `W ≅ R W₀` commutes with the maps to `R V₀`. -/
@[reassoc]
theorem bcOverOpenIso_hom_toOpen :
    (bcOverOpenIso g D₀ eX).hom ≫
        (OverShriek.relocalizeRestrict g).map (overOpenToOpen D₀.i D₀.v).hom =
      (overOpenToOpen (bcI g D₀ eX) (bcV g D₀)).hom :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- `R Z₀ ⟶ X ×_T ℙⁿ_T` is a closed immersion. -/
theorem isClosedImmersion_bcI : IsClosedImmersion B T hT (bcI g D₀ eX).hom :=
  MorphismProperty.RespectsIso.postcomp (closedImmersionPresheafProperty B T hT) _ _
    (isClosedImmersion_restrictHom g D₀.i D₀.isClosedImmersion_i)

/-- `R V₀ ⟶ ℙⁿ_T` is an open immersion. -/
theorem isOpenImmersion_bcV : IsOpenImmersion B T hT (bcV g D₀).hom := by
  have : IsIso (ObjectProperty.homMk (bcProjIso g D₀).hom :
      relocalizeRestrictSpace g (schemeSpace (projectiveSpaceSiteObj B S hS D₀.n D₀.contains)) ⟶
        schemeSpace (projectiveSpaceSiteObj B T hT D₀.n (bcContains D₀ g))).hom :=
    inferInstanceAs (IsIso (bcProjIso g D₀).hom)
  have : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B T hT)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  exact MorphismProperty.RespectsIso.postcomp _ _ _
    (isOpenImmersion_restrictHom g D₀.v D₀.isOpenImmersion_v)

/-- `R Z₀ ⟶ X ×_T ℙⁿ_T` is of finite presentation. -/
theorem isFinitePresentation_bcI : IsFinitePresentation B T hT (bcI g D₀ eX).hom := by
  have h := isFinitePresentation_relocalizeRestrict_map B S hS D₀.i.hom hT g D₀.Z.2
    (product B S hS X₀ D₀.n D₀.contains).2 D₀.isFinitePresentation_i
  have sq : IsPullback (𝟙 (relocalizeRestrictSpace g D₀.Z)) (bcI g D₀ eX) (restrictHom g D₀.i)
      (ObjectProperty.homMk (bcProductIso g D₀ eX).hom :
        product B T hT X D₀.n (bcContains D₀ g) ⟶
          relocalizeRestrictSpace g (product B S hS X₀ D₀.n D₀.contains)) :=
    IsPullback.of_horiz_isIso ⟨ObjectProperty.hom_ext _ (by
      change (OverShriek.relocalizeRestrict g).map D₀.i.hom = ((OverShriek.relocalizeRestrict g).map
        D₀.i.hom ≫ (bcProductIso g D₀ eX).inv) ≫ (bcProductIso g D₀ eX).hom
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id])⟩
  exact (isFinitePresentation_isStableUnderBaseChange B T hT).of_isPullback sq h

/-- `W ⟶ R V₀` is a closed immersion. -/
theorem isClosedImmersion_bc_overOpenToOpen :
    IsClosedImmersion B T hT (overOpenToOpen (bcI g D₀ eX) (bcV g D₀)).hom := by
  rw [← bcOverOpenIso_hom_toOpen]
  exact MorphismProperty.RespectsIso.precomp (closedImmersionPresheafProperty B T hT) _ _
    (isClosedImmersion_restrictHom g _ D₀.isClosedImmersion_overOpenToOpen)

/-- The composite `W ⟶ R Z₀ ⟶ X ×_T ℙⁿ_T ⟶ X` is `W ≅ R W₀`, the restriction of
`W₀ ⟶ X₀`, and `R X₀ ≅ X`. -/
theorem bc_overOpen_comp_fst :
    (overOpenι (bcI g D₀ eX) (bcV g D₀) ≫ bcI g D₀ eX ≫ productFst X D₀.n (bcContains D₀ g)).hom =
      (bcOverOpenIso g D₀ eX).hom ≫ (OverShriek.relocalizeRestrict g).map
        (overOpenι D₀.i D₀.v ≫ D₀.i ≫ productFst X₀ D₀.n D₀.contains).hom ≫ eX.inv := by
  rw [ObjectProperty.FullSubcategory.comp_hom, bcI_comp_fst, ← bcOverOpenIso_hom_ι_assoc,
    ← Functor.map_comp_assoc]
  rfl

/-- The composite `W ⟶ X` is étale. -/
theorem isEtale_bc_overOpen :
    IsEtale B T hT (overOpenι (bcI g D₀ eX) (bcV g D₀) ≫ bcI g D₀ eX ≫
      productFst X D₀.n (bcContains D₀ g)).hom := by
  rw [bc_overOpen_comp_fst]
  exact isEtale_comp B T hT (isEtale_of_isIso B T hT _)
    (isEtale_comp B T hT (isEtale_restrictHom g _ D₀.isEtale_overOpen) (isEtale_of_isIso B T hT _))

/-- A point of `W` over `x`, for `x` over `x₀`. -/
theorem exists_bc_point (x : points B T hT X.1)
    (hx : pointsMap B S hS _ (OverShriek.relocalizeRestrictCounit g X₀.1)
      (pointsRelocalize B T S hT hS g _ (pointsMap B T hT X.1 eX.hom x)) = x₀) :
    ∃ w : points B T hT (overOpen (bcI g D₀ eX) (bcV g D₀)).1,
      pointsMap B T hT _ (overOpenι (bcI g D₀ eX) (bcV g D₀) ≫ bcI g D₀ eX ≫
        productFst X D₀.n (bcContains D₀ g)).hom w = x := by
  let b₀ := (overOpenι D₀.i D₀.v ≫ D₀.i ≫ productFst X₀ D₀.n D₀.contains).hom
  obtain ⟨w'', h⟩ := exists_points_relocalizeRestrict_map g b₀ D₀.w (pointsMap B T hT X.1 eX.hom x)
    (by rw [D₀.pointsMap_w, hx])
  refine ⟨pointsMap B T hT _ (bcOverOpenIso g D₀ eX).inv w'', ?_⟩
  rw [bc_overOpen_comp_fst, pointsMap_comp, pointsMap_comp, Function.comp_apply,
    Function.comp_apply,
    ← Function.comp_apply (f := pointsMap B T hT _ (bcOverOpenIso g D₀ eX).hom),
    ← pointsMap_comp, Iso.inv_hom_id, pointsMap_id, id, h, ← Function.comp_apply
      (f := pointsMap B T hT _ eX.inv), ← pointsMap_comp, Iso.hom_inv_id, pointsMap_id, id]

/-- The morphism `X ×_T ℙⁿ_T ⟶ R(X₀ ×_S ℙⁿ_S)` of the restricted datum. -/
abbrev bcθ : product B T hT X D₀.n (bcContains D₀ g) ⟶
    relocalizeRestrictSpace g (product B S hS X₀ D₀.n D₀.contains) :=
  ObjectProperty.homMk (bcProductIso g D₀ eX).hom

/-- The counit `Λ R(X₀ ×_S ℙⁿ_S) ⟶ X₀ ×_S ℙⁿ_S`, a morphism of algebraic spaces over `S`. -/
abbrev bcκ :
    relocalizeSpace B hT hS g (relocalizeRestrictSpace g (product B S hS X₀ D₀.n D₀.contains)) ⟶
      product B S hS X₀ D₀.n D₀.contains :=
  ObjectProperty.homMk (OverShriek.relocalizeRestrictCounit g _)

/-- The object `E` of the restricted datum: the derived pullback of `E₀` along
`X ×_T ℙⁿ_T ≅ R(X₀ ×_S ℙⁿ_S) ⟶ X₀ ×_S ℙⁿ_S`. -/
def bcE : DerivedCategory (Modules.{u, u} B T hT (product B T hT X D₀.n (bcContains D₀ g)).1
    (product B T hT X D₀.n (bcContains D₀ g)).2) :=
  (smallEtaleDerivedModulePullback B T hT (bcθ g D₀ eX)).obj
    ((relocalizeInverse B hT hS g _
        (relocalizeRestrictSpace g (product B S hS X₀ D₀.n D₀.contains)).2).obj
      ((smallEtaleDerivedModulePullback B S hS (bcκ g D₀)).obj D₀.E))

/-- The object `E` of the restricted datum is pseudo-coherent. -/
theorem isPseudoCoherent_bcE :
    (smallEtaleRingedSite B T hT (product B T hT X D₀.n (bcContains D₀ g)).1
      (product B T hT X D₀.n (bcContains D₀ g)).2).IsPseudoCoherent (bcE g D₀ eX) :=
  isPseudoCoherent_smallEtaleDerivedModulePullback (bcθ g D₀ eX) _
    (isPseudoCoherent_relocalizeInverse_obj B hT hS g _
      (relocalizeRestrictSpace g (product B S hS X₀ D₀.n D₀.contains)).2 _
      (isPseudoCoherent_smallEtaleDerivedModulePullback (bcκ g D₀) D₀.E D₀.isPseudoCoherent_E))

/-- The cohomology of `E` is supported on the image of `|R Z₀|`. -/
theorem cohomologySupportedOn_bcE :
    CohomologySupportedOn B T hT (product B T hT X D₀.n (bcContains D₀ g)).1
      (product B T hT X D₀.n (bcContains D₀ g)).2
      (Set.range (pointsMap B T hT (relocalizeRestrictSpace g D₀.Z).1 (bcI g D₀ eX).hom))
      (bcE g D₀ eX) := by
  refine CohomologySupportedOn.mono B T hT _ _
    (cohomologySupportedOn_smallEtaleDerivedModulePullback (bcθ g D₀ eX) _
      (cohomologySupportedOn_relocalizeInverse_obj B hT hS g _
        (relocalizeRestrictSpace g (product B S hS X₀ D₀.n D₀.contains)).2 _ _
        (cohomologySupportedOn_smallEtaleDerivedModulePullback (bcκ g D₀) D₀.E
          D₀.cohomologySupportedOn_E))) ?_
  rintro y ⟨z₀, hz₀⟩
  obtain ⟨z, h⟩ := exists_points_relocalizeRestrict_map g D₀.i.hom z₀ _ hz₀
  refine ⟨z, ?_⟩
  change pointsMap B T hT _ ((OverShriek.relocalizeRestrict g).map D₀.i.hom ≫
    (bcProductIso g D₀ eX).inv) z = y
  have hθ : (bcθ g D₀ eX).hom ≫ (bcProductIso g D₀ eX).inv = 𝟙 _ :=
    (bcProductIso g D₀ eX).hom_inv_id
  rw [pointsMap_comp, Function.comp_apply, h, ← Function.comp_apply
    (f := pointsMap B T hT _ (bcProductIso g D₀ eX).inv), ← pointsMap_comp, hθ, pointsMap_id, id]

/-- The square exhibiting `R(X₀ ×_S V₀)` as the part of `X ×_T ℙⁿ_T` over `R V₀`. -/
theorem bc_isPullback_productOver :
    IsPullback ((OverShriek.relocalizeRestrict g).map (productOverι X₀ D₀.n D₀.contains D₀.v).hom ≫
        (bcProductIso g D₀ eX).inv)
      ((OverShriek.relocalizeRestrict g).map
        (ObjectProperty.homMk (pullback.snd _ _) : productOver X₀ D₀.n D₀.contains D₀.v ⟶ D₀.V).hom)
      (productSnd X D₀.n (bcContains D₀ g)).hom (bcV g D₀).hom :=
  IsPullback.of_iso ((IsPullback.of_hasPullback (productSnd X₀ D₀.n D₀.contains).hom
      D₀.v.hom).map (OverShriek.relocalizeRestrict g))
    (fst' := (OverShriek.relocalizeRestrict g).map (productOverι X₀ D₀.n D₀.contains D₀.v).hom ≫
        (bcProductIso g D₀ eX).inv)
    (snd' := (OverShriek.relocalizeRestrict g).map
        (ObjectProperty.homMk (pullback.snd _ _) : productOver X₀ D₀.n D₀.contains D₀.v ⟶ D₀.V).hom)
    (f' := (productSnd X D₀.n (bcContains D₀ g)).hom) (g' := (bcV g D₀).hom)
    (Iso.refl _) (bcProductIso g D₀ eX).symm (Iso.refl _) (bcProjIso g D₀)
    (Category.id_comp _).symm ((Category.comp_id _).trans (Category.id_comp _).symm)
    (restrictProductIso_inv_snd g eX D₀.n D₀.contains (bcContains D₀ g)).symm
    (Category.id_comp _).symm

/-- The isomorphism `X ×_T V ≅ R(X₀ ×_S V₀)` of the restricted datum. -/
def bcProductOverIso :
    (productOver X D₀.n (bcContains D₀ g) (bcV g D₀)).1 ≅
      (relocalizeRestrictSpace g (productOver X₀ D₀.n D₀.contains D₀.v)).1 :=
  IsPullback.isoIsPullback _ _ (IsPullback.of_hasPullback _ _) (bc_isPullback_productOver g D₀ eX)

/-- `X ×_T V ≅ R(X₀ ×_S V₀)` commutes with the maps to `X ×_T ℙⁿ_T`. -/
@[reassoc]
theorem bcProductOverIso_hom_ι :
    (bcProductOverIso g D₀ eX).hom ≫
        (OverShriek.relocalizeRestrict g).map (productOverι X₀ D₀.n D₀.contains D₀.v).hom ≫
          (bcProductIso g D₀ eX).inv =
      (productOverι X D₀.n (bcContains D₀ g) (bcV g D₀)).hom :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- `X ×_T V ≅ R(X₀ ×_S V₀)` commutes with the maps to `R V₀`. -/
@[reassoc]
theorem bcProductOverIso_hom_snd :
    (bcProductOverIso g D₀ eX).hom ≫ (OverShriek.relocalizeRestrict g).map
        (ObjectProperty.homMk (pullback.snd _ _) :
          productOver X₀ D₀.n D₀.contains D₀.v ⟶ D₀.V).hom =
      (ObjectProperty.homMk (pullback.snd _ _) :
        productOver X D₀.n (bcContains D₀ g) (bcV g D₀) ⟶ relocalizeRestrictSpace g D₀.V).hom :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- The morphism `X ×_T V ⟶ R(X₀ ×_S V₀)` of the restricted datum. -/
abbrev bcθV : productOver X D₀.n (bcContains D₀ g) (bcV g D₀) ⟶
    relocalizeRestrictSpace g (productOver X₀ D₀.n D₀.contains D₀.v) :=
  ObjectProperty.homMk (bcProductOverIso g D₀ eX).hom

/-- The morphism `W ⟶ R W₀` of the restricted datum. -/
abbrev bcφ : overOpen (bcI g D₀ eX) (bcV g D₀) ⟶ relocalizeRestrictSpace g (overOpen D₀.i D₀.v) :=
  ObjectProperty.homMk (bcOverOpenIso g D₀ eX).hom

/-- `X ×_T V ⟶ X ×_T ℙⁿ_T ⟶ R(X₀ ×_S ℙⁿ_S)` is
`X ×_T V ⟶ R(X₀ ×_S V₀) ⟶ R(X₀ ×_S ℙⁿ_S)`. -/
theorem productOverι_comp_bcθ :
    productOverι X D₀.n (bcContains D₀ g) (bcV g D₀) ≫ bcθ g D₀ eX =
      bcθV g D₀ eX ≫ restrictHom g (productOverι X₀ D₀.n D₀.contains D₀.v) := by
  refine ObjectProperty.hom_ext _ ?_
  change (productOverι X D₀.n (bcContains D₀ g) (bcV g D₀)).hom ≫ (bcProductIso g D₀ eX).hom =
    (bcProductOverIso g D₀ eX).hom ≫
      (OverShriek.relocalizeRestrict g).map (productOverι X₀ D₀.n D₀.contains D₀.v).hom
  rw [← bcProductOverIso_hom_ι, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- `W ⟶ R W₀ ⟶ R(X₀ ×_S V₀)` is `W ⟶ X ×_T V ⟶ R(X₀ ×_S V₀)`. -/
theorem bcφ_comp_restrictHom :
    bcφ g D₀ eX ≫ restrictHom g (overOpenToProductOver D₀.i D₀.v) =
      overOpenToProductOver (bcI g D₀ eX) (bcV g D₀) ≫ bcθV g D₀ eX := by
  refine ObjectProperty.hom_ext _ ((bc_isPullback_productOver g D₀ eX).hom_ext ?_ ?_)
  · change (bcOverOpenIso g D₀ eX).hom ≫ (OverShriek.relocalizeRestrict g).map
        (overOpenToProductOver D₀.i D₀.v).hom ≫
        (OverShriek.relocalizeRestrict g).map (productOverι X₀ D₀.n D₀.contains D₀.v).hom ≫
          (bcProductIso g D₀ eX).inv =
      (overOpenToProductOver (bcI g D₀ eX) (bcV g D₀)).hom ≫ (bcProductOverIso g D₀ eX).hom ≫
        (OverShriek.relocalizeRestrict g).map (productOverι X₀ D₀.n D₀.contains D₀.v).hom ≫
          (bcProductIso g D₀ eX).inv
    rw [bcProductOverIso_hom_ι, ← Functor.map_comp_assoc, ← ObjectProperty.FullSubcategory.comp_hom,
      overOpenToProductOver_ι, ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp_assoc,
      bcOverOpenIso_hom_ι_assoc, ← ObjectProperty.FullSubcategory.comp_hom,
      overOpenToProductOver_ι]
    rfl
  · change (bcOverOpenIso g D₀ eX).hom ≫ (OverShriek.relocalizeRestrict g).map
        (overOpenToProductOver D₀.i D₀.v).hom ≫ (OverShriek.relocalizeRestrict g).map
          (ObjectProperty.homMk (pullback.snd _ _) :
            productOver X₀ D₀.n D₀.contains D₀.v ⟶ D₀.V).hom =
      (overOpenToProductOver (bcI g D₀ eX) (bcV g D₀)).hom ≫ (bcProductOverIso g D₀ eX).hom ≫
        (OverShriek.relocalizeRestrict g).map
          (ObjectProperty.homMk (pullback.snd _ _) :
            productOver X₀ D₀.n D₀.contains D₀.v ⟶ D₀.V).hom
    rw [bcProductOverIso_hom_snd, ← Functor.map_comp, ← ObjectProperty.FullSubcategory.comp_hom,
      overOpenToProductOver_snd, bcOverOpenIso_hom_toOpen,
      ← ObjectProperty.FullSubcategory.comp_hom, overOpenToProductOver_snd]

/-- The morphism `W ⟶ X ×_T V` of the restricted datum. -/
abbrev bcI' : overOpen (bcI g D₀ eX) (bcV g D₀) ⟶ productOver X D₀.n (bcContains D₀ g) (bcV g D₀) :=
  overOpenToProductOver (bcI g D₀ eX) (bcV g D₀)

/-- The counit `Λ R(X₀ ×_S V₀) ⟶ X₀ ×_S V₀`. -/
abbrev bcκV :
    relocalizeSpace B hT hS g (relocalizeRestrictSpace g (productOver X₀ D₀.n D₀.contains D₀.v)) ⟶
      productOver X₀ D₀.n D₀.contains D₀.v :=
  ObjectProperty.homMk (OverShriek.relocalizeRestrictCounit g _)

/-- The counit `Λ R W₀ ⟶ W₀`. -/
abbrev bcκW : relocalizeSpace B hT hS g (relocalizeRestrictSpace g (overOpen D₀.i D₀.v)) ⟶
    overOpen D₀.i D₀.v :=
  ObjectProperty.homMk (OverShriek.relocalizeRestrictCounit g _)

/-- The counits `Λ R(X₀ ×_S V₀) ⟶ X₀ ×_S V₀` and `Λ R(X₀ ×_S ℙⁿ_S) ⟶ X₀ ×_S ℙⁿ_S` commute
with the inclusions. -/
theorem bcκ_naturality_productOverι :
    relocalizeHom B hT hS g (restrictHom g (productOverι X₀ D₀.n D₀.contains D₀.v)) ≫ bcκ g D₀ =
      bcκV g D₀ ≫ productOverι X₀ D₀.n D₀.contains D₀.v :=
  ObjectProperty.hom_ext _
    (isPullback_relocalize_relocalizeRestrict_map B S hS
      (productOverι X₀ D₀.n D₀.contains D₀.v).hom hT g).w.symm

/-- `Λ R W₀` is the base change of `W₀ ⟶ X₀ ×_S V₀` along `Λ R(X₀ ×_S V₀) ⟶ X₀ ×_S V₀`. -/
theorem bc_isPullback_κ :
    IsPullback (bcκW g D₀)
      (relocalizeHom B hT hS g (restrictHom g (overOpenToProductOver D₀.i D₀.v)))
      (overOpenToProductOver D₀.i D₀.v) (bcκV g D₀) :=
  IsPullback.of_map (ObjectProperty.ι _)
    (ObjectProperty.hom_ext _ (isPullback_relocalize_relocalizeRestrict_map B S hS
      (overOpenToProductOver D₀.i D₀.v).hom hT g).w)
    (isPullback_relocalize_relocalizeRestrict_map B S hS (overOpenToProductOver D₀.i D₀.v).hom hT g)

/-- `W₀ ⟶ X₀ ×_S V₀` is Tor independent of `Λ R(X₀ ×_S V₀) ⟶ X₀ ×_S V₀`. -/
theorem bc_torIndependent (hD₀ : D₀.TorIndependentOverBase) :
    TorIndependent (overOpen D₀.i D₀.v).2
      (relocalizeSpace B hT hS g
        (relocalizeRestrictSpace g (productOver X₀ D₀.n D₀.contains D₀.v))).2
      (productOver X₀ D₀.n D₀.contains D₀.v).2 (overOpenToProductOver D₀.i D₀.v).hom
      (bcκV g D₀).hom :=
  hD₀ (Over.mk g) _ (bcκV g D₀) (OverShriek.relocalizeToYoneda g _)
    (OverShriek.isPullback_relocalizeRestrictCounit g _
      (fun _ => ⟨fun a b => Over.mkIdTerminal.hom_ext a b⟩) _ _)

/-- The base change square `W ≅ R W₀` over `X ×_T V ≅ R(X₀ ×_S V₀)`. -/
theorem bc_isPullback_φ :
    IsPullback (bcφ g D₀ eX) (bcI' g D₀ eX) (restrictHom g (overOpenToProductOver D₀.i D₀.v))
      (bcθV g D₀ eX) :=
  IsPullback.of_horiz_isIso ⟨bcφ_comp_restrictHom g D₀ eX⟩

/-- `L(Λ R ι₀)^* Lκ^* E₀ ≅ Lκ_V^* Lι₀^* E₀`. -/
def bcIsoStep₃ :
    (smallEtaleDerivedModulePullback B S hS
        (relocalizeHom B hT hS g (restrictHom g (productOverι X₀ D₀.n D₀.contains D₀.v)))).obj
        ((smallEtaleDerivedModulePullback B S hS (bcκ g D₀)).obj D₀.E) ≅
      (smallEtaleDerivedModulePullback B S hS (bcκV g D₀)).obj
        ((smallEtaleDerivedModulePullback B S hS
          (productOverι X₀ D₀.n D₀.contains D₀.v)).obj D₀.E) :=
  (smallEtaleDerivedModulePullbackCompIso B S hS _ _).app D₀.E ≪≫
    (smallEtaleDerivedModulePullbackCongr B S hS (bcκ_naturality_productOverι g D₀)).app D₀.E ≪≫
    ((smallEtaleDerivedModulePullbackCompIso B S hS _ _).app D₀.E).symm

/-- `Lκ_V^* R(i₀')_* 𝒪_{W₀} ≅ R(Λ R i₀')_* 𝒪_{Λ R W₀}`, by Tor independent base change (08IR). -/
def bcIsoStep₅ (hD₀ : D₀.TorIndependentOverBase) :
    (smallEtaleDerivedModulePullback B S hS (bcκV g D₀)).obj
        ((derivedModulePushforward B S hS (overOpenToProductOver D₀.i D₀.v)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS (overOpen D₀.i D₀.v))))) ≅
      (derivedModulePushforward B S hS
          (relocalizeHom B hT hS g (restrictHom g (overOpenToProductOver D₀.i D₀.v)))).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS
            (relocalizeSpace B hT hS g (relocalizeRestrictSpace g (overOpen D₀.i D₀.v)))))) :=
  have hcl := isClosedImmersion_overOpenToProductOver D₀.i D₀.v D₀.isClosedImmersion_i
  @asIso _ _ _ _ (smallEtaleDerivedModuleBaseChangeMap B S hS _ _ _ _ (bc_isPullback_κ g D₀).w _)
    (isIso_smallEtaleDerivedBaseChangeMap_of_torIndependent B S hS _ _ _ _ (bc_isPullback_κ g D₀)
      (isQuasiCompact_of_isClosedImmersion' B S hS hcl)
      (isQuasiSeparated_of_isClosedImmersion B S hS hcl)
      (bc_torIndependent g D₀ hD₀) _ (derivedStructureSheaf B S hS _ _).property) ≪≫
    (derivedModulePushforward B S hS _).mapIso (smallEtaleDerivedModulePullbackUnitIso (bcκW g D₀))

/-- `G R(Λ R i₀')_* 𝒪 ≅ R(R i₀')_* 𝒪`. -/
def bcIsoStep₆ :
    (relocalizeInverse B hT hS g _
        (relocalizeRestrictSpace g (productOver X₀ D₀.n D₀.contains D₀.v)).2).obj
        ((derivedModulePushforward B S hS
          (relocalizeHom B hT hS g (restrictHom g (overOpenToProductOver D₀.i D₀.v)))).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS
              (relocalizeSpace B hT hS g (relocalizeRestrictSpace g (overOpen D₀.i D₀.v))))))) ≅
      (derivedModulePushforward B T hT (restrictHom g (overOpenToProductOver D₀.i D₀.v))).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (SheafOfModules.unit (ringedToposStructureRingSheaf B T hT
            (relocalizeRestrictSpace g (overOpen D₀.i D₀.v))))) :=
  ((relocalizeInversePushforwardIso B hT hS g (restrictHom g (overOpenToProductOver D₀.i D₀.v))).app
      _).symm ≪≫
    (derivedModulePushforward B T hT _).mapIso (relocalizeInverseUnitIso B hT hS g _ _)

/-- `Lθ_V^* R(R i₀')_* 𝒪 ≅ R(i')_* 𝒪_W`, by étale base change along the isomorphism `θ_V`. -/
def bcIsoStep₇ :
    (smallEtaleDerivedModulePullback B T hT (bcθV g D₀ eX)).obj
        ((derivedModulePushforward B T hT (restrictHom g (overOpenToProductOver D₀.i D₀.v))).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (SheafOfModules.unit (ringedToposStructureRingSheaf B T hT
              (relocalizeRestrictSpace g (overOpen D₀.i D₀.v)))))) ≅
      (derivedModulePushforward B T hT (bcI' g D₀ eX)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (SheafOfModules.unit (ringedToposStructureRingSheaf B T hT
            (overOpen (bcI g D₀ eX) (bcV g D₀))))) :=
  @asIso _ _ _ _ (smallEtaleDerivedModuleBaseChangeMap B T hT _ _ _ _ (bc_isPullback_φ g D₀ eX).w _)
    (isIso_smallEtaleDerivedBaseChangeMap_of_isEtale B T hT _ _ _ _ (bc_isPullback_φ g D₀ eX)
      (isEtale_of_isIso B T hT _) (Functor.relativelyRepresentable.of_isIso yoneda _) _) ≪≫
    (derivedModulePushforward B T hT _).mapIso
      (smallEtaleDerivedModulePullbackUnitIso (bcφ g D₀ eX))

/-- **Clause (4) of the restricted datum**: `E|_{X ×_T V} ≅ R(W ⟶ X ×_T V)_*𝒪_W`. -/
def bcRestrictIso (hD₀ : D₀.TorIndependentOverBase) :
    (smallEtaleDerivedModulePullback B T hT (productOverι X D₀.n (bcContains D₀ g) (bcV g D₀))).obj
        (bcE g D₀ eX) ≅
      (derivedModulePushforward B T hT (bcI' g D₀ eX)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (SheafOfModules.unit (ringedToposStructureRingSheaf B T hT
            (overOpen (bcI g D₀ eX) (bcV g D₀))))) :=
  (smallEtaleDerivedModulePullbackCompIso B T hT _ _).app _ ≪≫
    (smallEtaleDerivedModulePullbackCongr B T hT (productOverι_comp_bcθ g D₀ eX)).app _ ≪≫
    ((smallEtaleDerivedModulePullbackCompIso B T hT _ _).app _).symm ≪≫
    (smallEtaleDerivedModulePullback B T hT (bcθV g D₀ eX)).mapIso
      ((relocalizeInversePullbackIso B hT hS g
          (restrictHom g (productOverι X₀ D₀.n D₀.contains D₀.v))).app
          ((smallEtaleDerivedModulePullback B S hS (bcκ g D₀)).obj D₀.E) ≪≫
        (relocalizeInverse B hT hS g _
            (relocalizeRestrictSpace g (productOver X₀ D₀.n D₀.contains D₀.v)).2).mapIso
          (bcIsoStep₃ g D₀ ≪≫ (smallEtaleDerivedModulePullback B S hS (bcκV g D₀)).mapIso
            (D₀.restrictIso.some ≪≫
              restrictSinglePushforwardIso D₀.i D₀.v D₀.isClosedImmersion_i D₀.isOpenImmersion_v) ≪≫
            bcIsoStep₅ g D₀ hD₀) ≪≫
        bcIsoStep₆ g D₀) ≪≫
    bcIsoStep₇ g D₀ eX

/-- **Clause (4) of the restricted datum**: `E|_{X ×_T V}` is the restriction of the pushforward
of `𝒪_{R Z₀}`. -/
theorem bc_restrictIso (hD₀ : D₀.TorIndependentOverBase) :
    Nonempty ((smallEtaleDerivedModulePullback B T hT
        (productOverι X D₀.n (bcContains D₀ g) (bcV g D₀))).obj (bcE g D₀ eX) ≅
      (smallEtaleDerivedModulePullback B T hT
          (productOverι X D₀.n (bcContains D₀ g) (bcV g D₀))).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (structureSheafPushforward B T hT (bcI g D₀ eX)))) :=
  ⟨bcRestrictIso g D₀ eX hD₀ ≪≫ (restrictSinglePushforwardIso (bcI g D₀ eX) (bcV g D₀)
    (isClosedImmersion_bcI g D₀ eX) (isOpenImmersion_bcV g D₀)).symm⟩

/-- **The restriction of a datum of the derived Chow lemma.** Let `g : T ⟶ S` be a morphism of
the site, `D₀` a datum of the derived Chow lemma on `X₀` at `x₀` whose closed immersion
`W₀ ⟶ X₀ ×_S V₀` is Tor independent of the base changes along schemes over `S`, and `X ≅ R X₀`.
Then every point `x` of `X` over `x₀` carries a datum of the derived Chow lemma. -/
def baseChange (hD₀ : D₀.TorIndependentOverBase) (x : points B T hT X.1)
    (hx : pointsMap B S hS _ (OverShriek.relocalizeRestrictCounit g X₀.1)
      (pointsRelocalize B T S hT hS g _ (pointsMap B T hT X.1 eX.hom x)) = x₀) :
    DerivedChowDatum X x :=
  have hw := exists_bc_point g D₀ eX x hx
  { n := D₀.n
    contains := bcContains D₀ g
    Z := relocalizeRestrictSpace g D₀.Z
    i := bcI g D₀ eX
    isClosedImmersion_i := isClosedImmersion_bcI g D₀ eX
    isFinitePresentation_i := isFinitePresentation_bcI g D₀ eX
    V := relocalizeRestrictSpace g D₀.V
    v := bcV g D₀
    isOpenImmersion_v := isOpenImmersion_bcV g D₀
    isClosedImmersion_overOpenToOpen := isClosedImmersion_bc_overOpenToOpen g D₀ eX
    isEtale_overOpen := isEtale_bc_overOpen g D₀ eX
    w := hw.choose
    pointsMap_w := hw.choose_spec
    E := bcE g D₀ eX
    restrictIso := bc_restrictIso g D₀ eX hD₀
    isPseudoCoherent_E := isPseudoCoherent_bcE g D₀ eX
    cohomologySupportedOn_E := cohomologySupportedOn_bcE g D₀ eX }

/-- **The restriction of a datum of the derived Chow lemma** exists, see
`AlgebraicGeometry.Space.DerivedChowDatum.baseChange`. -/
theorem nonempty_baseChange (hD₀ : D₀.TorIndependentOverBase) (x : points B T hT X.1)
    (hx : pointsMap B S hS _ (OverShriek.relocalizeRestrictCounit g X₀.1)
      (pointsRelocalize B T S hT hS g _ (pointsMap B T hT X.1 eX.hom x)) = x₀) :
    Nonempty (DerivedChowDatum X x) :=
  ⟨baseChange g D₀ eX hD₀ x hx⟩

end DerivedChowDatum

section General

variable (B : BigFppfSite.{u}) {A : Type u} [CommRing A] (hA : B.Contains (Spec (.of A)))

/-- **Stacks 0CTR (derived Chow lemma).** Let `A` be a ring and `X` an algebraic space separated
and of finite presentation over `A`. Every point `x ∈ |X|` carries a datum of the derived Chow
lemma: `n ≥ 0`, a closed subspace `Z ⊂ X ×_A ℙⁿ_A` of finite presentation, an open `V ⊂ ℙⁿ_A`,
a point of `c⁻¹(V)` over `x` and `E ∈ D(𝒪_{X ×_A ℙⁿ_A})` with properties (1)–(5) of the source
(`AlgebraicGeometry.Space.DerivedChowDatum`). -/
@[stacks 0CTR]
theorem nonempty_derivedChowDatum (X : AlgebraicSpaces B (Spec (.of A)) hA)
    (hsep : IsSeparated B (Spec (.of A)) hA (toBase B (Spec (.of A)) hA X).hom)
    (hfp : IsFinitePresentation B (Spec (.of A)) hA (toBase B (Spec (.of A)) hA X).hom)
    (x : points B (Spec (.of A)) hA X.1) :
    Nonempty (DerivedChowDatum X x) := by
  obtain ⟨A₀, _, _, _, hA₀, X₀', hX₀', f₀, hfp₀, hsep₀, -, hiso⟩ :=
    exists_finiteType_model_of_isFinitePresentation B X.2 (toBase B (Spec (.of A)) hA X).hom hfp
  have : IsNoetherianRing A₀ := Algebra.FiniteType.isNoetherianRing ℤ A₀
  let g : B.obj hA ⟶ B.obj hA₀ :=
    B.inclusion.preimage (Spec.map (CommRingCat.ofHom (algebraMap A₀ A)))
  obtain ⟨eX⟩ := hiso g (B.inclusion.map_preimage _)
  let X₀ : AlgebraicSpaces B (Spec (.of A₀)) hA₀ := ⟨X₀', hX₀'⟩
  have hf₀ : (toBase B (Spec (.of A₀)) hA₀ X₀).hom = f₀ :=
    (isTerminal_yoneda_obj_base B (Spec (.of A₀)) hA₀).hom_ext _ _
  obtain ⟨D₀, hD₀⟩ := exists_derivedChowDatum_torIndependentOverBase_of_isNoetherianRing B hA₀ X₀
    (hf₀ ▸ hsep₀ hsep) (hf₀ ▸ hfp₀)
    (pointsMap B (Spec (.of A₀)) hA₀ _ (OverShriek.relocalizeRestrictCounit g X₀.1)
      (pointsRelocalize B (Spec (.of A)) (Spec (.of A₀)) hA hA₀ g _
        (pointsMap B (Spec (.of A)) hA X.1 eX.hom x)))
  exact DerivedChowDatum.nonempty_baseChange g D₀ eX hD₀ x rfl

end General

end AlgebraicGeometry.Space

end
