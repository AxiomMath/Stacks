module

public import StacksCore.CategoryTheory.FiberedInGroupoids
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CartesianFamilies
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilies
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.DimensionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.DimensionLocallyConstant
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Slice

/-!
# Families of curves inside proper flat families of spaces (Stacks 0D51, 0D5B)

The category of families of curves of Stacks 0D4Z is fibred in groupoids over the big fppf site
of schemes: every morphism of base schemes lifts to a morphism of families of curves, and lifts
satisfy the existence-and-uniqueness of fill-ins.

Forgetting the bound on the relative dimension embeds that category into the category of finitely
presented, flat and proper families of algebraic spaces, and the resulting `1`-morphism of
categories fibred in groupoids is representable by algebraic spaces, each representing morphism
being both an open and a closed immersion: over a scheme `S` carrying such a family `X ⟶ S`, the
locus of points whose fibre has dimension at most one is a clopen subscheme of `S`, and a scheme
over `S` factors through it exactly when the family it induces is a family of curves.

## Main definitions

* `AlgebraicGeometry.CurveFamily.toCartesianProperFlat` reads a family of curves as a finitely
  presented, flat and proper family of algebraic spaces over a varying base scheme.
* `AlgebraicGeometry.curvesProjectionOver`, `AlgebraicGeometry.curvesFiberedCategory` and
  `AlgebraicGeometry.cartesianProperFlatFiberedCategory` present the two categories as categories
  fibred in groupoids over the big fppf site.
* `AlgebraicGeometry.curvesToCartesianProperFlat`: **Stacks equation 0D50**, the inclusion of
  families of curves into finitely presented, flat and proper families of algebraic spaces, as a
  functor; `AlgebraicGeometry.curvesToCartesianProperFlatHom` is the same inclusion as a
  `1`-morphism of categories fibred in groupoids.

## Main results

* `AlgebraicGeometry.curvesProjection_isFiberedInGroupoids`: **Stacks 0D51**, the category of
  families of curves is fibred in groupoids over the big fppf site of schemes.
* `AlgebraicGeometry.curvesToCartesianProperFlat_comp_cartesianProperFlatProjection` and
  `AlgebraicGeometry.curvesToCartesianProperFlat_comp_projection`: the inclusion of Stacks
  equation 0D50 commutes on the nose with the projections of the two categories to the big fppf
  site.
* `AlgebraicGeometry.curvesToCartesianProperFlat_full` and
  `AlgebraicGeometry.curvesToCartesianProperFlat_faithful`: that inclusion is the inclusion of a
  full subcategory.
* `AlgebraicGeometry.isRepresentableByAlgebraicSpaces_curvesToCartesianProperFlat`,
  `AlgebraicGeometry.isOpenImmersion_curvesToCartesianProperFlat` and
  `AlgebraicGeometry.isClosedImmersion_curvesToCartesianProperFlat`: **Stacks 0D5B**, the
  inclusion is representable by open and closed immersions.

## Implementation notes

For Stacks 0D51 the source argues through the inclusion (0D50) of families of curves into the
finitely presented, flat and proper families of algebraic spaces over a varying base: that
inclusion is fully faithful with cartesian squares on both sides, its image is cut out by the
condition that the structure morphism have relative dimension at most one, and the corresponding
statement for the larger category is Stacks 0D1E, here
`AlgebraicGeometry.cartesianProperFlatProjection_isFiberedInGroupoids`. What remains is the
description of the image: the condition cutting it out descends along a cartesian square, so the
cartesian lift supplied by Stacks 0D1E is again a family of curves. That descent is part (1) of
Stacks 04NS, base-change invariance of the relative dimension at a point, here
`AlgebraicGeometry.Space.hasRelativeDimensionAt_iff_of_isPullback`: the structure morphism of the
lift is the base change of the structure morphism of the given family, by Stacks 04U9 in the form
`AlgebraicGeometry.isPullback_hom_of_isStronglyCartesian`, and local finite typeness of the latter
needed by 04NS is the first assertion of Stacks 0464 applied to its finite presentation.

The proof of Stacks 0D51 uses only `AlgebraicGeometry.CurveFamily.toCartesianProperFlat` on
objects, because the two categories have the *same* cartesian squares and differ only by an object
property; the inclusion as a functor is needed for Stacks 0D5B, where it must be a `1`-morphism of
the `2`-category of categories fibred in groupoids. Uniqueness of the fill-in is proved directly
rather than transported: a morphism of families of curves is determined by its base map and its
morphism of total spaces, the first by terminality of `Spec(ℤ)` and the second by the universal
property of the cartesian square of the morphism it is required to factor.

Stacks equation 0D50 therefore sits on `AlgebraicGeometry.curvesToCartesianProperFlat`, the
inclusion as a functor: the displayed inclusion is one of categories, so the object map alone
does not state it and is left untagged. Fullness, faithfulness and the compatibility with the
projections are left untagged too: the equation displays only the inclusion, and those three are
what the surrounding Situation 99.15.1 provides for it rather than assertions of the equation.

Stacks 0D5B is split over three declarations, because being an open immersion and being a closed
immersion are independent conclusions and both presuppose representability by algebraic spaces.
The two immersion conclusions are `AlgebraicGeometry.Stack.IsOpenImmersion` and
`AlgebraicGeometry.Stack.IsClosedImmersion`, the Stacks 04XB notions for a `1`-morphism of
categories fibred in groupoids; they are the relative property of Stacks 03YK at the open- and
closed-immersion properties of algebraic spaces, by
`AlgebraicGeometry.Stack.isOpenImmersion_iff_hasRelativeProperty` and its companion, but are
stated in the written-out form so that no locality instance has to be assumed. Nothing is asked of
either side beyond being fibred in groupoids, as in the source.

The clopen locus is produced from Stacks 0D4R, local constancy of the fibre dimension of a
finitely presented, flat and proper morphism
(`AlgebraicGeometry.Space.isLocallyConstant_fiberDimension`): the sublevel set of the fibre
dimension and its complement are both open for the topology of Stacks 03BX, and clause (1) of that
tag turns the two into complementary opens of the base scheme. That a scheme over the base factors
through the locus exactly when the induced family has relative dimension at most one combines
Stacks 0D4M, which identifies the dimension bound on a fibre with the bound on the relative
dimension above the corresponding point, and Stacks 0D4N, base-change invariance of the fibre
dimension.

Representability is then the comparison of two categories over the big fppf site of the base: the
`2`-fibre product of the inclusion with a scheme-valued point, whose first projection is fully
faithful because the inclusion is, and the category of elements of the sheaf of points of the
locus, whose projection is fully faithful because the locus has at most one morphism from any
scheme over the base. Two fully faithful categories over a base with the same image on objects are
equivalent over it, and the image of the first projection is exactly the relative-dimension bound.

## References

* [Stacks Project, Tag 0D51](https://stacks.math.columbia.edu/tag/0D51)
* [Stacks Project, Tag 0D5B](https://stacks.math.columbia.edu/tag/0D5B)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

set_option synthInstance.maxHeartbeats 400000 in
/-- Limits of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasLimits_presheaf_CurveFamiliesFibered
    {S : Scheme.{u}} {hS : B.Contains S} :
    HasLimitsOfSize.{u, u} ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Limits of small (universe `0`) shape of presheaves on the big fppf site. -/
local instance (priority := high) hasLimitsOfSizeZero_presheaf_CurveFamiliesFibered
    {S : Scheme.{u}} {hS : B.Contains S} :
    HasLimitsOfSize.{0, 0} ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  hasLimitsOfSizeShrink.{0, 0, u, u} _

/-- Discrete limits of universe-`0` shape of presheaves on the big fppf site. -/
local instance (priority := high) hasLimitsOfShapeDiscrete_presheaf_CurveFamiliesFibered
    {S : Scheme.{u}} {hS : B.Contains S} (J : Type) :
    HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  HasLimitsOfSize.has_limits_of_shape.{0, 0} _

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_CurveFamiliesFibered
    {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_CurveFamiliesFibered
    {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- A family of curves, read as a finitely presented, flat and proper family of algebraic spaces
over a varying base scheme, forgetting the bound on the relative dimension of the structure
morphism. This is the action on objects of `AlgebraicGeometry.curvesToCartesianProperFlat`, the
inclusion of Stacks equation 0D50, and is kept separate because the proof of Stacks 0D51 needs
only the object map. -/
def CurveFamily.toCartesianProperFlat (X : CurveFamily B hZ) :
    CartesianProperFlatSpaces B integerBase hZ :=
  ⟨⟨⟨X.total, X.base, X.toBase.hom⟩, ⟨X.finitePresentation, X.flat, X.proper⟩⟩⟩

/-- Over `Spec(ℤ)`, every morphism between the underlying schemes is a morphism over it, by
terminality of `Spec(ℤ)`. -/
private theorem comp_hom_eq_hom {X Y : BigFppfOver B integerBase hZ} (f : X.left ⟶ Y.left) :
    f ≫ Y.hom = X.hom := by
  apply B.inclusion.map_injective
  change B.inclusion.map f ≫ B.inclusion.map Y.hom = B.inclusion.map X.hom
  exact specULiftZIsTerminal.hom_ext _ _

/-- **Stacks 0D51.** The category of families of curves is fibred in groupoids over the big fppf
site of schemes. -/
@[stacks 0D51]
theorem curvesProjection_isFiberedInGroupoids :
    (curvesProjection B hZ).IsFiberedInGroupoids := by
  constructor
  · intro V U f X hX
    let V₀ : BigFppfOver B integerBase hZ :=
      Over.mk (B.inclusion.preimage (X := V) (Y := B.obj hZ)
        (show B.inclusion.obj V ⟶ B.inclusion.obj (B.obj hZ) from
          specULiftZIsTerminal.from V.1))
    let f₀ : V ⟶ X.base.left := f ≫ eqToHom hX.symm
    let g : V₀ ⟶ X.base := Over.homMk f₀ (comp_hom_eq_hom B hZ (X := V₀) f₀)
    let QX := X.toCartesianProperFlat
    obtain ⟨QY, η, hη⟩ :=
      (cartesianProperFlatProjection_isFiberedInGroupoids B integerBase hZ).exists_lift g QX rfl
    let m : QY.obj.obj ⟶ QX.obj.obj := (isProperFlatSpace B integerBase hZ).ι.map η.hom
    have hsc : (spacesProjection B integerBase hZ).IsStronglyCartesian m.right m := η.property
    have hpull : IsPullback m.left.hom QY.obj.obj.hom QX.obj.obj.hom (yoneda.map m.right) :=
      (isPullback_hom_of_isStronglyCartesian B integerBase hZ m hsc).flip
    let y : CurveFamily B hZ :=
      { base := QY.obj.obj.right
        total := QY.obj.obj.left
        toBase := ObjectProperty.homMk QY.obj.obj.hom
        finitePresentation := QY.obj.property.1
        flat := QY.obj.property.2.1
        proper := QY.obj.property.2.2
        relativeDimensionLE := by
          intro x'
          obtain ⟨e, he, hrel⟩ := X.relativeDimensionLE
            (Space.pointsMap B integerBase hZ QY.obj.obj.left.obj m.left.hom x')
          refine ⟨e, he, ?_⟩
          have hfinite : Space.IsLocallyOfFiniteType B integerBase hZ QX.obj.obj.hom :=
            Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B integerBase hZ
              X.finitePresentation.1
          exact (Space.hasRelativeDimensionAt_iff_of_isPullback B integerBase hZ hpull
            QX.obj.obj.left.property
            (isAlgebraicSpace_yoneda B integerBase hZ QY.obj.obj.right)
            (isAlgebraicSpace_yoneda B integerBase hZ QX.obj.obj.right)
            hfinite x' (e : ℕ∞)).mp hrel }
    have hcod : (cartesianProperFlatProjection B integerBase hZ).obj QX = X.base := rfl
    let φ : y ⟶ X :=
      { baseMap := m.right ≫ eqToHom hcod
        totalMap := ObjectProperty.homMk m.left.hom
        cartesian :=
          hpull.of_map (ObjectProperty.ι _) (f := m.left)
            (g := (ObjectProperty.homMk QY.obj.obj.hom :
              QY.obj.obj.left ⟶ schemeSpace QY.obj.obj.right))
            (h := (ObjectProperty.homMk QX.obj.obj.hom :
              QX.obj.obj.left ⟶ schemeSpace QX.obj.obj.right))
            (i := schemeSpaceMap m.right)
            (ObjectProperty.hom_ext _ (by
              simpa [schemeSpaceMap, schemeSpace, ObjectProperty.ι_obj,
                ObjectProperty.homMk_hom] using hpull.w)) }
    refine ⟨y, φ, ?_⟩
    let _ : (cartesianProperFlatProjection B integerBase hZ).IsHomLift g η := hη
    have hdom : (cartesianProperFlatProjection B integerBase hZ).obj QY = V₀ :=
      IsHomLift.domain_eq _ g η
    have ha : (curvesProjection B hZ).obj y = V := congrArg Over.left hdom
    have hdomMap : (eqToHom hdom.symm).left = eqToHom ha.symm := by
      rw [Over.eqToHom_left]
      congr 1
    have hfac : g = eqToHom hdom.symm ≫
        (cartesianProperFlatProjection B integerBase hZ).map η ≫ eqToHom hcod :=
      IsHomLift.fac (cartesianProperFlatProjection B integerBase hZ) g η
    have hleft := congrArg (fun k : V₀ ⟶ X.base => k.left) hfac
    rw [Over.comp_left, Over.comp_left] at hleft
    apply IsHomLift.of_fac (p := curvesProjection B hZ) f φ ha hX
    have hl : f₀ = eqToHom ha.symm ≫ (curvesProjection B hZ).map φ := by
      rw [hdomMap] at hleft
      simpa [g, f₀, hdom, ha, φ, curvesProjection_map, cartesianProperFlatProjection,
        CurveFamily.toCartesianProperFlat, hcod, m, Over.comp_left, Over.eqToHom_left] using hleft
    have h' : f ≫ eqToHom hX.symm = eqToHom ha.symm ≫ (curvesProjection B hZ).map φ := by
      simpa [f₀] using hl
    have hcancel : eqToHom hX.symm ≫ eqToHom hX = 𝟙 U := by
      rw [eqToHom_trans]
      have heq : hX.symm.trans hX = rfl := Subsingleton.elim _ _
      rw [heq]
      rfl
    calc
      f = f ≫ (eqToHom hX.symm ≫ eqToHom hX) := by rw [hcancel]; simp
      _ = (f ≫ eqToHom hX.symm) ≫ eqToHom hX := by simp [Category.assoc]
      _ = (eqToHom ha.symm ≫ (curvesProjection B hZ).map φ) ≫ eqToHom hX := by rw [h']
      _ = eqToHom ha.symm ≫ (curvesProjection B hZ).map φ ≫ eqToHom hX := by
          simp [Category.assoc]
  · intro X Y Z φ ψ f h
    let b : Z.base ⟶ Y.base := Over.homMk f (comp_hom_eq_hom B hZ f)
    have hb : b ≫ φ.baseMap = ψ.baseMap := by
      apply Over.OverMorphism.ext
      change f ≫ φ.baseMap.left = ψ.baseMap.left
      simpa [curvesProjection_map] using h
    have hcomm : (Z.toBase ≫ schemeSpaceMap b) ≫ schemeSpaceMap φ.baseMap =
        ψ.totalMap ≫ X.toBase := by
      calc
        (Z.toBase ≫ schemeSpaceMap b) ≫ schemeSpaceMap φ.baseMap =
            Z.toBase ≫ schemeSpaceMap (b ≫ φ.baseMap) := by
              rw [schemeSpaceMap_comp]
              exact Category.assoc _ _ _
        _ = Z.toBase ≫ schemeSpaceMap ψ.baseMap := by rw [hb]
        _ = ψ.totalMap ≫ X.toBase := ψ.cartesian.w.symm
    let t : Z.total ⟶ Y.total :=
      φ.cartesian.lift ψ.totalMap (Z.toBase ≫ schemeSpaceMap b) hcomm.symm
    have ht₁ : t ≫ φ.totalMap = ψ.totalMap := φ.cartesian.lift_fst _ _ _
    have ht₂ : t ≫ Y.toBase = Z.toBase ≫ schemeSpaceMap b := φ.cartesian.lift_snd _ _ _
    have hcart : IsPullback t Z.toBase Y.toBase (schemeSpaceMap b) := by
      apply IsPullback.of_right ?_ ht₂ φ.cartesian
      rw [ht₁, ← schemeSpaceMap_comp, hb]
      exact ψ.cartesian
    let χ : Z ⟶ Y := ⟨b, t, hcart⟩
    refine ⟨χ, ?_, ?_⟩
    · constructor
      · change b.left = f
        rfl
      · apply CurveFamily.Hom.ext
        · exact hb
        · exact ht₁
    · intro χ' hχ'
      have hbχ : χ'.baseMap = b := by
        apply Over.OverMorphism.ext
        rw [show b.left = f from rfl]
        simpa [curvesProjection_map] using hχ'.1
      apply CurveFamily.Hom.ext
      · exact hbχ
      · apply φ.cartesian.hom_ext
        · calc
            χ'.totalMap ≫ φ.totalMap = (χ' ≫ φ).totalMap := rfl
            _ = ψ.totalMap := congrArg (fun k : Z ⟶ X => k.totalMap) hχ'.2
            _ = t ≫ φ.totalMap := ht₁.symm
        · calc
            χ'.totalMap ≫ Y.toBase = Z.toBase ≫ schemeSpaceMap χ'.baseMap := χ'.cartesian.w
            _ = Z.toBase ≫ schemeSpaceMap b := by rw [hbχ]
            _ = t ≫ Y.toBase := ht₂.symm

/-! ### The inclusion of families of curves as a 1-morphism -/

/-- The projection taking a family of curves to its base scheme over `Spec(ℤ)`: the lift of
`AlgebraicGeometry.curvesProjection` through the slice site, which is how the category of
families of curves is a category over the big fppf site of `Spec(ℤ)`. -/
def curvesProjectionOver : CurveFamily B hZ ⥤ BigFppfOver B integerBase hZ where
  obj X := X.base
  map f := f.baseMap
  map_id := by intro; rfl
  map_comp := by intros; rfl

/-- The category of families of curves as an object of the 2-category of categories fibred in
groupoids over the big fppf site of `Spec(ℤ)`. -/
def curvesFiberedCategory :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B integerBase hZ) :=
  CatFiberedInGroupoids.mk (BasedCategory.ofFunctor (curvesProjectionOver B hZ))
    (Functor.IsFiberedInGroupoids.of_comp_over (B.obj hZ) (curvesProjection B hZ)
      (curvesProjectionOver B hZ) rfl (curvesProjection_isFiberedInGroupoids B hZ))

section ProperFlatFibered

variable (S : Scheme.{u}) (hS : B.Contains S)

/-- The category of finitely presented, flat and proper families of algebraic spaces over
varying base schemes as an object of the 2-category of categories fibred in groupoids over the
big fppf site of `S`. -/
def cartesianProperFlatFiberedCategory :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk (BasedCategory.ofFunctor (cartesianProperFlatProjection B S hS))
    (cartesianProperFlatProjection_isFiberedInGroupoids B S hS)

end ProperFlatFibered

/-- A cartesian square of families of curves, read as an arrow of the underlying finitely
presented, flat and proper families of algebraic spaces over varying base schemes. -/
def CurveFamily.toCartesianProperFlatMap {X Y : CurveFamily B hZ} (f : X ⟶ Y) :
    (X.toCartesianProperFlat).obj ⟶ (Y.toCartesianProperFlat).obj := by
  apply ObjectProperty.homMk
  refine { left := f.totalMap, right := f.baseMap, w := ?_ }
  change f.totalMap.hom ≫ Y.toBase.hom = X.toBase.hom ≫ yoneda.map f.baseMap
  have hw := congrArg (fun g => g.hom) f.cartesian.w
  simp only [ObjectProperty.FullSubcategory.comp_hom] at hw
  change f.totalMap.hom ≫ Y.toBase.hom = X.toBase.hom ≫ yoneda.map f.baseMap at hw
  exact hw

/-- The arrow of proper flat families underlying a cartesian square of families of curves is
strongly cartesian over the big fppf site. -/
theorem CurveFamily.toCartesianProperFlatMap_isStronglyCartesian
    {X Y : CurveFamily B hZ} (f : X ⟶ Y) :
    (spacesProjection B integerBase hZ).IsStronglyCartesian f.baseMap
      ((isProperFlatSpace B integerBase hZ).ι.map (CurveFamily.toCartesianProperFlatMap B hZ f)) :=
  by
  apply (spacesProjection_isStronglyCartesian_iff
    ((isProperFlatSpace B integerBase hZ).ι.map
      (CurveFamily.toCartesianProperFlatMap B hZ f))).2
  have hP := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ
    (schemeSpaceMap f.baseMap) (ObjectProperty.homMk Y.toBase.hom)
  have hwf : X.toBase.hom ≫ (schemeSpaceMap f.baseMap).hom =
      f.totalMap.hom ≫ Y.toBase.hom := by
    have hw := congrArg (fun g => g.hom) f.cartesian.w
    simp only [ObjectProperty.FullSubcategory.comp_hom] at hw
    change f.totalMap.hom ≫ Y.toBase.hom = X.toBase.hom ≫ yoneda.map f.baseMap at hw
    exact hw.symm
  let i := f.cartesian.flip.isoIsPullback _ _ hP
  have hi : i.hom = ObjectProperty.homMk (pullback.lift X.toBase.hom f.totalMap.hom hwf) := by
    apply ObjectProperty.hom_ext
    apply pullback.hom_ext
    · exact (congrArg (fun g => g.hom) (f.cartesian.flip.isoIsPullback_hom_fst _ _ hP)).trans
        (pullback.lift_fst _ _ hwf).symm
    · exact (congrArg (fun g => g.hom) (f.cartesian.flip.isoIsPullback_hom_snd _ _ hP)).trans
        (pullback.lift_snd _ _ hwf).symm
  have hii : IsIso i.hom := inferInstance
  simpa [hi, CurveFamily.toCartesianProperFlatMap, CurveFamily.toCartesianProperFlat] using hii

/-- **Stacks equation 0D50.** The inclusion of the category of families of curves into the
category of finitely presented, flat and proper families of algebraic spaces over varying base
schemes, forgetting the bound on the relative dimension of the structure morphism: on objects it
is `AlgebraicGeometry.CurveFamily.toCartesianProperFlat` and on morphisms it keeps the morphism
of total spaces and the morphism of base schemes, the cartesian square of a morphism of families
of curves being exactly the strongly cartesian condition on the larger side.

The equation displays only this inclusion. That the two sides are categories fibred in groupoids
over the big fppf site and that the inclusion is one of categories over that site is the ambient
Situation 99.15.1 of the source, realised here by
`AlgebraicGeometry.curvesProjection_isFiberedInGroupoids`,
`AlgebraicGeometry.cartesianProperFlatProjection_isFiberedInGroupoids` and
`AlgebraicGeometry.curvesToCartesianProperFlat_comp_cartesianProperFlatProjection`; that the
inclusion is one of a full subcategory is
`AlgebraicGeometry.curvesToCartesianProperFlat_full` together with
`AlgebraicGeometry.curvesToCartesianProperFlat_faithful`. -/
@[stacks 0D50 "the inclusion"]
def curvesToCartesianProperFlat :
    CurveFamily B hZ ⥤ CartesianProperFlatSpaces B integerBase hZ where
  obj X := X.toCartesianProperFlat
  map f := ⟨CurveFamily.toCartesianProperFlatMap B hZ f,
    CurveFamily.toCartesianProperFlatMap_isStronglyCartesian B hZ f⟩
  map_id X := by ext <;> rfl
  map_comp f g := by ext <;> rfl

/-- The inclusion of Stacks equation 0D50 is a functor over the big fppf site of `Spec(ℤ)`, as
the ambient Situation 99.15.1 asks: composing it with the projection of the category of finitely
presented, flat and proper families gives the projection of the category of families of curves,
on the nose. Both sides take a family to its base scheme and a cartesian square to its morphism
of base schemes. -/
theorem curvesToCartesianProperFlat_comp_cartesianProperFlatProjection :
    curvesToCartesianProperFlat B hZ ⋙ cartesianProperFlatProjection B integerBase hZ =
      curvesProjectionOver B hZ :=
  rfl

/-- The same compatibility read in the big fppf site itself rather than in the slice over
`Spec(ℤ)`: the inclusion of Stacks equation 0D50 followed by the projection of the larger
category and the forgetful functor of the slice is the projection
`AlgebraicGeometry.curvesProjection` of Stacks 0D4Z, again on the nose. -/
theorem curvesToCartesianProperFlat_comp_projection :
    curvesToCartesianProperFlat B hZ ⋙ cartesianProperFlatProjection B integerBase hZ ⋙
        Over.forget (B.obj hZ) = curvesProjection B hZ :=
  rfl

/-- The inclusion (0D50) of families of curves into finitely presented, flat and proper families
of algebraic spaces, as a 1-morphism of categories fibred in groupoids over the big fppf site of
`Spec(ℤ)`. -/
def curvesToCartesianProperFlatHom :
    curvesFiberedCategory B hZ ⟶ cartesianProperFlatFiberedCategory B integerBase hZ :=
  Bicategory.InducedBicategory.mkHom
    ({ toFunctor := curvesToCartesianProperFlat B hZ, w := rfl })

/-- The inclusion of Stacks equation 0D50 is faithful: a morphism of families of curves consists
of its morphism of base schemes and its morphism of total spaces, both of which the underlying
morphism of proper flat families records, so it is determined by that morphism. This is part of
the inclusion being one of a full subcategory, which is the setting of Situation 99.15.1 and not
asserted by the displayed equation. -/
theorem curvesToCartesianProperFlat_faithful :
    (curvesToCartesianProperFlat B hZ).Faithful where
  map_injective := by
    intro X Y f g h
    apply CurveFamily.Hom.ext
    · exact congrArg (fun k => k.hom.hom.right) h
    · exact congrArg (fun k => k.hom.hom.left) h

/-- The inclusion of Stacks equation 0D50 is full: being a family of curves is a property of the
object, the bound on the relative dimension of the structure morphism, and carries no extra
structure on morphisms, so a strongly cartesian arrow of finitely presented, flat and proper
families between the images of two families of curves already has a cartesian square of
structure morphisms and is a morphism of families of curves. Together with faithfulness this is
the inclusion of a full subcategory, which is the setting of Situation 99.15.1 and not asserted
by the displayed equation. -/
theorem curvesToCartesianProperFlat_full :
    (curvesToCartesianProperFlat B hZ).Full where
  map_surjective := by
    intro X Y f
    refine ⟨{ baseMap := f.hom.hom.right
              totalMap := f.hom.hom.left
              cartesian := ?_ }, ?_⟩
    · exact (isPullback_hom_of_isStronglyCartesian B integerBase hZ
        f.hom.hom f.property).flip.of_map (ObjectProperty.ι _)
        (f := f.hom.hom.left) (g := X.toBase) (h := Y.toBase)
        (i := schemeSpaceMap f.hom.hom.right)
        (ObjectProperty.hom_ext _ f.hom.hom.w)
    · apply WideSubcategory.hom_ext
      apply ObjectProperty.hom_ext
      rfl

/-! ### The locus of relative dimension at most one -/

section Locus

attribute [local instance] Space.pointTopology

variable (S : Scheme.{u}) (hS : B.Contains S)

/-- Having relative dimension at most one is the bound by one on the dimension of every fibre. -/
private theorem hasRelativeDimensionLE_one_iff
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) :
    Space.HasRelativeDimensionLE 1 B S hS f ↔
      ∀ y : Space.points B S hS Y,
        Space.fiberDimension B S hS f y ≤ ((1 : ℕ) : WithBot ℕ∞) := by
  constructor
  · intro hdim y
    refine (Space.fiberDimension_le_iff B S hS f y 1).2 fun x _ ↦ ?_
    obtain ⟨n, hn, hAt⟩ := hdim x
    exact ⟨(n : ℕ∞), hAt, by exact_mod_cast hn⟩
  · intro hdim x
    obtain ⟨e, hAt, he⟩ := (Space.fiberDimension_le_iff B S hS f _ 1).1 (hdim _) x rfl
    have he' : e ≤ (1 : ℕ∞) := by exact_mod_cast he
    have hne : e ≠ ⊤ := by
      intro h
      rw [h] at he'
      simp at he'
    exact ⟨e.toNat, ENat.toNat_le_of_le_natCast he', by rwa [ENat.natCast_toNat hne]⟩

/-- The locus in the target where the fibres of a finitely presented, flat and proper morphism of
algebraic spaces have dimension at most one is open and closed, the fibre dimension being locally
constant by Stacks 0D4R. -/
private theorem isClopen_setOf_fiberDimension_le_one
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hProper : Space.IsProper B S hS f) (hFlat : Space.IsFlat B S hS f)
    (hFP : Space.IsFinitePresentation B S hS f) :
    IsClopen {y : Space.points B S hS Y |
      Space.fiberDimension B S hS f y ≤ ((1 : ℕ) : WithBot ℕ∞)} :=
  have hlc := Space.isLocallyConstant_fiberDimension B S hS hX hY f hProper hFlat hFP
  ⟨⟨hlc {d | ¬ d ≤ ((1 : ℕ) : WithBot ℕ∞)}⟩, hlc {d | d ≤ ((1 : ℕ) : WithBot ℕ∞)}⟩

/-- The clopen subscheme of the base cutting out the locus where a finitely presented, flat and
proper family of algebraic spaces over a scheme has fibres of dimension at most one. -/
private theorem exists_opens_fiberDimension_le_one (U : BigFppfOver B S hS)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ yoneda.obj U)
    (hX : IsAlgebraicSpace B S hS X) (hProper : Space.IsProper B S hS f)
    (hFlat : Space.IsFlat B S hS f) (hFP : Space.IsFinitePresentation B S hS f) :
    ∃ V : ((BigFppfOver.toScheme B S hS).obj U).Opens,
      IsClosed (V : Set ((BigFppfOver.toScheme B S hS).obj U)) ∧
        ∀ x : Space.points B S hS (yoneda.obj U),
          Space.pointsToScheme B S hS U x ∈ (V : Set _) ↔
            Space.fiberDimension B S hS f x ≤ ((1 : ℕ) : WithBot ℕ∞) := by
  have hclopen := isClopen_setOf_fiberDimension_le_one B S hS f hX
    (isAlgebraicSpace_yoneda B S hS U) hProper hFlat hFP
  obtain ⟨V, hVopen, hV⟩ := (Space.isSchemeOpen_iff_exists_preimage B S hS U _).1
    ((Space.isOpen_yoneda_iff_isSchemeOpen B S hS U _).1 hclopen.2)
  obtain ⟨V', hV'open, hV'⟩ := (Space.isSchemeOpen_iff_exists_preimage B S hS U _).1
    ((Space.isOpen_yoneda_iff_isSchemeOpen B S hS U _).1 hclopen.1.isOpen_compl)
  have hVc : V' = Vᶜ :=
    (Space.surjective_pointsToScheme B S hS U).preimage_injective
      (by rw [hV', Set.preimage_compl, hV])
  refine ⟨⟨V, hVopen⟩, ?_, fun x ↦ Set.ext_iff.1 hV x⟩
  rw [← isOpen_compl_iff]
  exact hVc ▸ hV'open

/-- A morphism of schemes factors through an open subscheme of its target exactly when its image
is contained in that open subscheme. -/
private theorem exists_factorisation_opens_iff {X Y : Scheme.{u}} (V : Y.Opens) (f : X ⟶ Y) :
    (∃ g : X ⟶ V, g ≫ V.ι = f) ↔ Set.range f.base ⊆ (V : Set Y) := by
  constructor
  · rintro ⟨g, hg⟩
    have hpoint (x : X) : V.ι (g x) = f x := by
      simpa only [Scheme.Hom.comp_apply] using congrArg (fun k : X ⟶ Y => k x) hg
    rintro x ⟨x, rfl⟩
    rw [← hpoint x]
    exact (g x).property
  · intro hf
    have hf' : Set.range f ⊆ Set.range V.ι := by
      simpa only [Scheme.Opens.range_ι] using hf
    exact ⟨IsOpenImmersion.lift V.ι f hf', IsOpenImmersion.lift_fac V.ι f hf'⟩

/-- Relative dimension at most one for a base change is the fibre-dimension bound along the
base-change morphism, by base-change invariance of the fibre dimension. -/
private theorem hasRelativeDimensionLE_one_pullback_snd_iff
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ' : IsAlgebraicSpace B S hS Z) (hf : Space.IsFiniteType B S hS f) :
    Space.HasRelativeDimensionLE 1 B S hS (pullback.snd f g) ↔
      ∀ z : Space.points B S hS Z,
        Space.fiberDimension B S hS f (Space.pointsMap B S hS Z g z) ≤
          ((1 : ℕ) : WithBot ℕ∞) := by
  rw [hasRelativeDimensionLE_one_iff B S hS (pullback.snd f g),
    Space.fiberDimension_pullback_snd B S hS f g hX hY hZ' hf]
  rfl

/-- A base change of a morphism of finite type of algebraic spaces is of finite type. -/
private theorem isFiniteType_pullback_snd
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ' : IsAlgebraicSpace B S hS Z) (hf : Space.IsFiniteType B S hS f) :
    Space.IsFiniteType B S hS (pullback.snd f g) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := fun ⦃A C : AlgebraicSpaces B S hS⦄ (k : A ⟶ C) ↦ Space.IsFiniteType B S hS k.hom)
    (AlgebraicSpaces.isPullback_fiberProduct B S hS
      (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
      (ObjectProperty.homMk g : (⟨Z, hZ'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)) hf

/-- The relative-dimension bound is invariant under an isomorphism of families: isomorphisms of
the sources and of the targets intertwining two morphisms carry the bound across. -/
private theorem hasRelativeDimensionLE_one_iff_of_iso
    {X X' Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (ea : X' ≅ X) (eb : Y' ≅ Y) (hsq : f' ≫ eb.hom = ea.hom ≫ f)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hY' : IsAlgebraicSpace B S hS Y')
    (hf : Space.IsLocallyOfFiniteType B S hS f) :
    Space.HasRelativeDimensionLE 1 B S hS f' ↔ Space.HasRelativeDimensionLE 1 B S hS f := by
  have hpb : IsPullback f' ea.hom eb.hom f := IsPullback.of_vert_isIso (CommSq.mk hsq)
  have hiff (d : ℕ∞) (x' : Space.points B S hS X') :
      Space.HasRelativeDimensionAt d B S hS f' x' ↔
        Space.HasRelativeDimensionAt d B S hS f
          (Space.pointsMap B S hS X' ea.hom x') :=
    Space.hasRelativeDimensionAt_iff_of_isPullback' B S hS d hpb hX hY hY' hf x'
  have hcancel (x : Space.points B S hS X) :
      Space.pointsMap B S hS X' ea.hom (Space.pointsMap B S hS X ea.inv x) = x := by
    rw [← Function.comp_apply (f := Space.pointsMap B S hS X' ea.hom),
      ← Space.pointsMap_comp, ea.inv_hom_id, Space.pointsMap_id, id_eq]
  constructor
  · intro h x
    obtain ⟨n, hn, hAt⟩ := h (Space.pointsMap B S hS X ea.inv x)
    exact ⟨n, hn, hcancel x ▸ (hiff _ _).1 hAt⟩
  · intro h x'
    obtain ⟨n, hn, hAt⟩ := h (Space.pointsMap B S hS X' ea.hom x')
    exact ⟨n, hn, (hiff _ _).2 hAt⟩

/-- The relative-dimension bound is invariant under an isomorphism of families of algebraic
spaces over varying base schemes. -/
private theorem hasRelativeDimensionLE_one_iff_of_commaIso
    {A C : Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    (E : A ≅ C) (hf : Space.IsLocallyOfFiniteType B S hS C.hom) :
    Space.HasRelativeDimensionLE 1 B S hS A.hom ↔
      Space.HasRelativeDimensionLE 1 B S hS C.hom :=
  hasRelativeDimensionLE_one_iff_of_iso B S hS
    ((Comma.fst _ _ ⋙ ObjectProperty.ι _).mapIso E) ((Comma.snd _ _ ⋙ yoneda).mapIso E)
    E.hom.w.symm C.left.property (isAlgebraicSpace_yoneda B S hS C.right)
    (isAlgebraicSpace_yoneda B S hS A.right) hf

/-- For a cartesian arrow of finitely presented, flat and proper families of algebraic spaces,
the relative-dimension bound on the source is the fibre-dimension bound on the target along the
morphism of base schemes. -/
private theorem hasRelativeDimensionLE_one_iff_forall_fiberDimension_base
    {P Q : CartesianProperFlatSpaces B S hS} (m : P ⟶ Q) :
    Space.HasRelativeDimensionLE 1 B S hS P.obj.obj.hom ↔
      ∀ z : Space.points B S hS (yoneda.obj P.obj.obj.right),
        Space.fiberDimension B S hS Q.obj.obj.hom
          (Space.pointsMap B S hS (yoneda.obj P.obj.obj.right)
            (yoneda.map m.hom.hom.right) z) ≤ ((1 : ℕ) : WithBot ℕ∞) := by
  have hsq := isPullback_hom_of_isStronglyCartesian B S hS m.hom.hom m.property
  have hQ := Q.obj.obj.left.property
  have hPr := isAlgebraicSpace_yoneda B S hS P.obj.obj.right
  have hQr := isAlgebraicSpace_yoneda B S hS Q.obj.obj.right
  have hft : Space.IsFiniteType B S hS Q.obj.obj.hom := Q.obj.property.2.2.2.1
  have hpull : IsAlgebraicSpace B S hS
      (pullback Q.obj.obj.hom (yoneda.map m.hom.hom.right)) :=
    isAlgebraicSpace_pullback B S hS Q.obj.obj.hom (yoneda.map m.hom.hom.right) hQ hPr hQr
  have hftpull : Space.IsFiniteType B S hS
      (pullback.snd Q.obj.obj.hom (yoneda.map m.hom.hom.right)) :=
    isFiniteType_pullback_snd B S hS Q.obj.obj.hom (yoneda.map m.hom.hom.right) hQ hQr hPr hft
  exact (hasRelativeDimensionLE_one_iff_of_iso B S hS hsq.flip.isoPullback (Iso.refl _)
      (by rw [Iso.refl_hom, Category.comp_id]; exact hsq.flip.isoPullback_hom_snd.symm)
      hpull hPr hPr hftpull.1).trans
    (hasRelativeDimensionLE_one_pullback_snd_iff B S hS Q.obj.obj.hom
      (yoneda.map m.hom.hom.right) hQ hQr hPr hft)

/-- A scheme over `U` factors through the clopen locus cut out by the fibre-dimension bound
exactly when the base change of the family along it satisfies that bound at every point. -/
private theorem exists_factorisation_iff_forall_fiberDimension_le_one
    (U : BigFppfOver B S hS) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ yoneda.obj U)
    (O : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (hO : ∀ x : Space.points B S hS (yoneda.obj U),
      Space.pointsToScheme B S hS U x ∈ (O : Set _) ↔
        Space.fiberDimension B S hS f x ≤ ((1 : ℕ) : WithBot ℕ∞))
    (R : BigFppfOver B S hS) (h : R ⟶ U) :
    (∃ l : (BigFppfOver.toScheme B S hS).obj R ⟶ O,
        l ≫ O.ι = (BigFppfOver.toScheme B S hS).map h) ↔
      ∀ z : Space.points B S hS (yoneda.obj R),
        Space.fiberDimension B S hS f
          (Space.pointsMap B S hS (yoneda.obj R) (yoneda.map h) z) ≤
            ((1 : ℕ) : WithBot ℕ∞) := by
  rw [exists_factorisation_opens_iff]
  constructor
  · intro hsub z
    rw [← hO, Space.pointsToScheme_pointsMap]
    exact hsub ⟨_, rfl⟩
  · rintro hz x ⟨a, rfl⟩
    obtain ⟨z, hz'⟩ := Space.surjective_pointsToScheme B S hS R a
    rw [← hz', ← Space.pointsToScheme_pointsMap]
    exact (hO _).2 (hz z)

end Locus

/-- A clopen subscheme is the source of both an open and a closed immersion into the ambient
scheme. -/
@[ega "IV 4.9.6" "more general"]
private theorem isOpenImmersion_and_isClosedImmersion_opens_ι {X : Scheme.{u}} (V : X.Opens)
    (hV : IsClosed (V : Set X)) : IsOpenImmersion V.ι ∧ IsClosedImmersion V.ι :=
  ⟨inferInstance, IsClosedImmersion.of_isPreimmersion V.ι
    (by simpa only [Scheme.Opens.range_ι] using hV)⟩

/-- The clopen subscheme of `U` cut out by the relative-dimension bound: for a scheme-valued
point of the category of finitely presented, flat and proper families of algebraic spaces over
`U`, a scheme over `U` maps into it exactly when the family it induces is a family of curves. -/
private theorem exists_curveLocus (U : BigFppfOver B integerBase hZ)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ CartesianProperFlatSpaces B integerBase hZ)
    (hy : y ⋙ cartesianProperFlatProjection B integerBase hZ = Over.map U.hom) :
    ∃ V : BigFppfOver B U.left.1 U.left.2,
      IsOpenImmersion V.hom.hom ∧ IsClosedImmersion V.hom.hom ∧
        ∀ T : BigFppfOver B U.left.1 U.left.2, Nonempty (T ⟶ V) ↔
          Space.HasRelativeDimensionLE 1 B integerBase hZ (y.obj T).obj.obj.hom := by
  let T₀ : BigFppfOver B U.left.1 U.left.2 := Over.mk (𝟙 U.left)
  let Q := y.obj T₀
  obtain ⟨O, hOclosed, hOmem⟩ := exists_opens_fiberDimension_le_one B integerBase hZ
    Q.obj.obj.right Q.obj.obj.hom Q.obj.obj.left.property Q.obj.property.2.2
    Q.obj.property.2.1 Q.obj.property.1
  have hOsize : B.Contains (O : Scheme.{u}) :=
    (Scheme.size_coe_opens_le _ O).trans_lt Q.obj.obj.right.left.property
  let W : Over Q.obj.obj.right.left :=
    Over.mk (B.inclusion.preimage (X := B.obj hOsize) (Y := Q.obj.obj.right.left) O.ι)
  have hWhom : W.hom.hom = O.ι :=
    B.inclusion.map_preimage (X := B.obj hOsize) (Y := Q.obj.obj.right.left) O.ι
  have hyb : y ⋙ cartesianProperFlatProjection B integerBase hZ ⋙
      Over.forget (B.obj hZ) = Over.forget U.left := by
    rw [← Functor.assoc, hy]
    rfl
  let e (T : BigFppfOver B U.left.1 U.left.2) : (y.obj T).obj.obj.right.left ≅ T.left :=
    eqToIso (congrArg (fun F => F.obj T) hyb)
  have hiso (T : BigFppfOver B U.left.1 U.left.2) : IsIso ((e T).hom.hom) :=
    inferInstanceAs (IsIso (B.inclusion.map (e T).hom))
  let V : BigFppfOver B U.left.1 U.left.2 := Over.mk (W.hom ≫ (e T₀).hom)
  have hWhom' : B.inclusion.map W.hom = O.ι := hWhom
  have hVhom : V.hom.hom = O.ι ≫ (e T₀).hom.hom := by
    change W.hom.hom ≫ (e T₀).hom.hom = O.ι ≫ (e T₀).hom.hom
    rw [hWhom]
  have hO := isOpenImmersion_and_isClosedImmersion_opens_ι O hOclosed
  refine ⟨V, ?_, ?_, ?_⟩
  · rw [hVhom]
    have := hiso T₀
    have := hO.1
    infer_instance
  · rw [hVhom]
    have := hiso T₀
    have := hO.2
    infer_instance
  · intro T
    let t : T ⟶ T₀ := Over.homMk T.hom (by simp [T₀])
    let m := y.map t
    have hm : m.hom.hom.right.left ≫ (e T₀).hom = (e T).hom ≫ T.hom := by
      have hh := CategoryTheory.Functor.congr_hom hyb t
      change m.hom.hom.right.left = (e T).hom ≫ T.hom ≫ (e T₀).inv at hh
      rw [hh]
      simp
    refine Iff.trans ?_ (Iff.trans
      (exists_factorisation_iff_forall_fiberDimension_le_one B integerBase hZ
        Q.obj.obj.right Q.obj.obj.hom O hOmem (y.obj T).obj.obj.right m.hom.hom.right)
      (hasRelativeDimensionLE_one_iff_forall_fiberDimension_base B integerBase hZ m).symm)
    constructor
    · rintro ⟨a⟩
      have hVw : a.left ≫ (W.hom ≫ (e T₀).hom) = T.hom := Over.w a
      have key : (e T).hom ≫ a.left ≫ W.hom = m.hom.hom.right.left := by
        apply (cancel_mono (e T₀).hom).mp
        calc ((e T).hom ≫ a.left ≫ W.hom) ≫ (e T₀).hom
            = (e T).hom ≫ a.left ≫ (W.hom ≫ (e T₀).hom) := by
              simp only [Category.assoc]
          _ = (e T).hom ≫ T.hom := by rw [hVw]
          _ = m.hom.hom.right.left ≫ (e T₀).hom := hm.symm
      have key' : ((e T).hom ≫ a.left) ≫ W.hom = m.hom.hom.right.left := by
        rw [Category.assoc]
        exact key
      refine ⟨B.inclusion.map ((e T).hom ≫ a.left), ?_⟩
      change B.inclusion.map ((e T).hom ≫ a.left) ≫ O.ι =
        B.inclusion.map m.hom.hom.right.left
      rw [← hWhom', ← Functor.map_comp, key']
    · rintro ⟨l, hl⟩
      let l' : (y.obj T).obj.obj.right.left ⟶ W.left := B.inclusion.preimage l
      have hl' : l' ≫ W.hom = m.hom.hom.right.left := by
        apply B.inclusion.map_injective
        change B.inclusion.map l' ≫ W.hom.hom = m.hom.hom.right.left.hom
        rw [hWhom, B.inclusion.map_preimage]
        exact hl
      refine ⟨Over.homMk ((e T).inv ≫ l') ?_⟩
      change ((e T).inv ≫ l') ≫ (W.hom ≫ (e T₀).hom) = T.hom
      calc ((e T).inv ≫ l') ≫ (W.hom ≫ (e T₀).hom)
          = (e T).inv ≫ (l' ≫ W.hom) ≫ (e T₀).hom := by simp only [Category.assoc]
        _ = (e T).inv ≫ (e T).hom ≫ T.hom := by rw [hl', hm]
        _ = T.hom := by rw [Iso.inv_hom_id_assoc]

/-! ### Representability of the inclusion -/

section Representable

universe v

/-- The first projection of a 2-fibre product over the base is faithful as soon as the second
leg is: a morphism of the 2-fibre product is determined by its first component. -/
private theorem twoFibreProduct_fst_faithful {C A D E : Type*} [Category C] [Category A]
    [Category D] [Category E] (p : A ⥤ C) (q : D ⥤ C) (r : E ⥤ C)
    (F : A ⥤ E) (G : D ⥤ E) [G.Faithful] :
    (TwoFibreProductOver.fst p q r F G).Faithful where
  map_injective {X Y} f g h := by
    apply TwoFibreProductOver.Hom.ext' h
    apply G.map_injective
    apply (cancel_epi X.iso.hom).mp
    rw [← f.w, ← g.w]
    exact congrArg (fun a => F.map a ≫ Y.iso.hom) h

/-- The first projection of a 2-fibre product over the base is full as soon as the second leg is
fully faithful. -/
private theorem twoFibreProduct_fst_full {C A D E : Type*} [Category C] [Category A]
    [Category D] [Category E] (p : A ⥤ C) (q : D ⥤ C) (r : E ⥤ C)
    (F : A ⥤ E) (G : D ⥤ E) (hF : F ⋙ r = p) (hG : G ⋙ r = q)
    [G.Full] [G.Faithful] : (TwoFibreProductOver.fst p q r F G).Full where
  map_surjective {X Y} a := by
    subst p q
    change X.x ⟶ Y.x at a
    let b := G.preimage (X.iso.inv ≫ F.map a ≫ Y.iso.hom)
    have hbase : eqToHom X.hy.symm ≫ (G ⋙ r).map b ≫ eqToHom Y.hy =
        eqToHom X.hx.symm ≫ (F ⋙ r).map a ≫ eqToHom Y.hx := by
      have hXhom : r.IsHomLift (𝟙 X.base) X.iso.hom := X.vertical
      have hYhom : r.IsHomLift (𝟙 Y.base) Y.iso.hom := Y.vertical
      have hXinv : r.IsHomLift (𝟙 X.base) X.iso.inv := inferInstance
      have hXm := IsHomLift.fac' r (𝟙 X.base) X.iso.inv
      have hYm := IsHomLift.fac' r (𝟙 Y.base) Y.iso.hom
      change eqToHom X.hy.symm ≫ r.map (G.map b) ≫ eqToHom Y.hy = _
      dsimp [b]
      rw [G.map_preimage, r.map_comp, r.map_comp, hXm, hYm]
      simp
    refine ⟨TwoFibreProductOver.Hom.mk' a b hbase ?_, rfl⟩
    dsimp [b]
    simp

/-- A fully faithful functor over the base whose image contains the image of another one receives
a 1-morphism over the base from it. -/
private theorem nonempty_morphismOver_of_fullyFaithful
    {C A D : Type*} [Category C] [Category A] [Category D]
    (p : A ⥤ C) (q : D ⥤ C) [q.Full] [q.Faithful]
    (h : ∀ a, ∃ d, q.obj d = p.obj a) :
    Nonempty (StacksRepresentableCFG.MorphismOver p q) := by
  classical
  choose obj ho using h
  let F : A ⥤ D :=
    { obj := obj
      map := fun {a b} f => q.preimage (eqToHom (ho a) ≫ p.map f ≫ eqToHom (ho b).symm)
      map_id := by intro a; apply q.map_injective; simp
      map_comp := by intro a b c f g; apply q.map_injective; simp }
  refine ⟨F, CategoryTheory.Functor.ext ho ?_⟩
  intro a b f
  change q.map (q.preimage _) = _
  simp

/-- Two fully faithful functors over the base with the same image are equivalent over the
base. -/
private theorem nonempty_equivalenceOver_of_fullyFaithful
    {C A D : Type*} [Category C] [Category A] [Category D]
    (p : A ⥤ C) (q : D ⥤ C) [p.Full] [p.Faithful] [q.Full] [q.Faithful]
    (h : ∀ c, (∃ a, p.obj a = c) ↔ ∃ d, q.obj d = c) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver p q) := by
  obtain ⟨F⟩ := nonempty_morphismOver_of_fullyFaithful p q (fun a => (h _).mp ⟨a, rfl⟩)
  obtain ⟨G⟩ := nonempty_morphismOver_of_fullyFaithful q p (fun d => (h _).mpr ⟨d, rfl⟩)
  have hu : (F.functor ⋙ G.functor) ⋙ p = p := by rw [Functor.assoc, G.w, F.w]
  have hc : (G.functor ⋙ F.functor) ⋙ q = q := by rw [Functor.assoc, F.w, G.w]
  let η : 𝟭 A ≅ F.functor ⋙ G.functor :=
    (Functor.FullyFaithful.ofFullyFaithful ((Functor.whiskeringRight A A C).obj p)).preimageIso
      (eqToIso (by change 𝟭 A ⋙ p = (F.functor ⋙ G.functor) ⋙ p; rw [Functor.id_comp, hu]))
  let ε : G.functor ⋙ F.functor ≅ 𝟭 D :=
    (Functor.FullyFaithful.ofFullyFaithful ((Functor.whiskeringRight D D C).obj q)).preimageIso
      (eqToIso (by change (G.functor ⋙ F.functor) ⋙ q = 𝟭 D ⋙ q; rw [Functor.id_comp, hc]))
  refine ⟨F, G, η, ε, ?_, ?_⟩
  · exact (Functor.FullyFaithful.ofFullyFaithful
      ((Functor.whiskeringRight A A C).obj p)).map_preimage _
  · exact (Functor.FullyFaithful.ofFullyFaithful
      ((Functor.whiskeringRight D D C).obj q)).map_preimage _

attribute [local implicit_reducible] Functor.toPseudofunctor' pseudofunctorOfIsLocallyDiscrete
  Quiver.Hom.toLoc

/-- The projection from the category of elements of a presheaf of sets is faithful. -/
private theorem presheafProjection_faithful {C : Type*} [Category C]
    (F : Cᵒᵖ ⥤ Type*) : (presheafOfCategories (F ⋙ typeToCat)).p.Faithful where
  map_injective {X Y} f g h := by
    apply Pseudofunctor.CoGrothendieck.Hom.ext _ _ h
    exact @Subsingleton.elim (Discrete.mk X.fiber.as ⟶
      Discrete.mk (F.map f.base.op Y.fiber.as)) inferInstance _ _

/-- The projection from the category of elements of a subsingleton-valued presheaf is full. -/
private theorem presheafProjection_full {C : Type*} [Category C]
    (F : Cᵒᵖ ⥤ Type*) (hF : ∀ X, Subsingleton (F.obj X)) :
    (presheafOfCategories (F ⋙ typeToCat)).p.Full where
  map_surjective {X Y} f := by
    refine ⟨⟨f, ?_⟩, rfl⟩
    exact eqToHom (by
      apply Discrete.ext
      exact (hF _).elim _ _)

/-- An object of the base is in the image of the projection from the category of elements of a
presheaf exactly when the presheaf has a section over it. -/
private theorem presheafProjection_image {C : Type*} [Category C]
    (F : Cᵒᵖ ⥤ Type*) (X : C) :
    (∃ a, (presheafOfCategories (F ⋙ typeToCat)).p.obj a = X) ↔
      Nonempty (F.obj (Opposite.op X)) := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.fiber.as⟩
  · rintro ⟨a⟩
    exact ⟨⟨X, Discrete.mk a⟩, rfl⟩

/-- A presheaf whose category of elements has full projection takes subsingleton values. -/
private theorem subsingleton_of_presheafProjection_full {C : Type*} [Category C]
    (F : Cᵒᵖ ⥤ Type*) [(presheafOfCategories (F ⋙ typeToCat)).p.Full]
    (X : Cᵒᵖ) : Subsingleton (F.obj X) := by
  constructor
  intro a b
  let A : (presheafOfCategories (F ⋙ typeToCat)).obj := ⟨X.unop, Discrete.mk a⟩
  let D : (presheafOfCategories (F ⋙ typeToCat)).obj := ⟨X.unop, Discrete.mk b⟩
  obtain ⟨m, hm⟩ := (presheafOfCategories (F ⋙ typeToCat)).p.map_surjective
    (X := A) (Y := D) (𝟙 X.unop)
  have he : a = F.map m.base.op b := Discrete.eq_of_hom m.fiber
  change m.base = 𝟙 X.unop at hm
  rw [hm] at he
  change a = F.map (𝟙 X) b at he
  simpa only [F.map_id, types_id_apply] using he

/-- Two subsingleton-valued presheaves with the same support are isomorphic. -/
private theorem nonempty_presheafIso_of_subsingleton {C : Type*} [Category C]
    (F G : Cᵒᵖ ⥤ Type v) (hF : ∀ X, Subsingleton (F.obj X)) (hG : ∀ X, Subsingleton (G.obj X))
    (h : ∀ X, Nonempty (F.obj X) ↔ Nonempty (G.obj X)) : Nonempty (F ≅ G) := by
  classical
  let e (X : Cᵒᵖ) : F.obj X ≃ G.obj X :=
    { toFun := fun a => ((h X).mp ⟨a⟩).some
      invFun := fun b => ((h X).mpr ⟨b⟩).some
      left_inv := fun _ => (hF X).elim _ _
      right_inv := fun _ => (hG X).elim _ _ }
  exact ⟨NatIso.ofComponents (fun X => (e X).toIso) (fun {X Y} f => by
    ext a
    exact (hG Y).elim _ _)⟩

/-- An equivalence over the base has the same image on objects. -/
private theorem equivalenceOver_image
    {C A D : Type*} [Category C] [Category A] [Category D]
    {p : A ⥤ C} {q : D ⥤ C} (e : StacksRepresentableCFG.EquivalenceOver p q)
    (c : C) : (∃ a, p.obj a = c) ↔ ∃ d, q.obj d = c := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨e.hom.functor.obj a, congrArg (fun F => F.obj a) e.hom.w⟩
  · rintro ⟨d, rfl⟩
    exact ⟨e.inv.functor.obj d, congrArg (fun F => F.obj d) e.inv.w⟩

/-- Fullness transports along an equivalence over the base. -/
private theorem equivalenceOver_full
    {C A D : Type*} [Category C] [Category A] [Category D]
    {p : A ⥤ C} {q : D ⥤ C} (e : StacksRepresentableCFG.EquivalenceOver p q)
    [p.Full] : q.Full := by
  have : e.inv.functor.Full := by
    change e.toEquivalence.inverse.Full
    infer_instance
  rw [← e.inv.w]
  infer_instance

end Representable

/-! ### The inclusion is representable by open and closed immersions -/

section Immersion

universe v

/-- A finitely presented, flat and proper family of algebraic spaces whose structure morphism has
relative dimension at most one is a family of curves. -/
private def properFlatObjectAsCurve (P : CartesianProperFlatSpaces B integerBase hZ)
    (hDim : Space.HasRelativeDimensionLE 1 B integerBase hZ P.obj.obj.hom) :
    CurveFamily B hZ where
  base := P.obj.obj.right
  total := P.obj.obj.left
  toBase := ObjectProperty.homMk P.obj.obj.hom
  flat := P.obj.property.2.1
  proper := P.obj.property.2.2
  finitePresentation := P.obj.property.1
  relativeDimensionLE := hDim

/-- A scheme over `U` is in the image of the first projection of the 2-fibre product of the
inclusion (0D50) with a scheme-valued point exactly when the family it induces has relative
dimension at most one. -/
private theorem curveFiber_image (U : BigFppfOver B integerBase hZ)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ CartesianProperFlatSpaces B integerBase hZ)
    (hy : y ⋙ cartesianProperFlatProjection B integerBase hZ = Over.map U.hom)
    (T : BigFppfOver B U.left.1 U.left.2) :
    (∃ a, (TwoFibreProductOver.fst (Over.map U.hom) (curvesProjectionOver B hZ)
      (cartesianProperFlatProjection B integerBase hZ) y
      (curvesToCartesianProperFlat B hZ)).obj a = T) ↔
      Space.HasRelativeDimensionLE 1 B integerBase hZ (y.obj T).obj.obj.hom := by
  constructor
  · rintro ⟨a, rfl⟩
    have hfinite : Space.IsLocallyOfFiniteType B integerBase hZ (y.obj a.x).obj.obj.hom :=
      Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B integerBase hZ
        (y.obj a.x).obj.property.1.1
    exact (hasRelativeDimensionLE_one_iff_of_commaIso B integerBase hZ
      ((wideSubcategoryInclusion _ ⋙ (isProperFlatSpace B integerBase hZ).ι).mapIso
        a.iso.symm) hfinite).mp a.y.relativeDimensionLE
  · intro h
    have hbase : (properFlatObjectAsCurve B hZ (y.obj T) h).base = (Over.map U.hom).obj T :=
      congrArg (fun F => F.obj T) hy
    refine ⟨{ base := (properFlatObjectAsCurve B hZ (y.obj T) h).base
              x := T
              y := properFlatObjectAsCurve B hZ (y.obj T) h
              hx := hbase.symm
              hy := rfl
              iso := Iso.refl _
              vertical := ?_ }, rfl⟩
    change (cartesianProperFlatProjection B integerBase hZ).IsHomLift
      (𝟙 ((cartesianProperFlatProjection B integerBase hZ).obj (y.obj T))) (𝟙 (y.obj T))
    infer_instance

/-- There is at most one morphism to the clopen locus, its structure morphism being a
monomorphism. -/
private theorem curveLocus_subsingleton (U : BigFppfOver B integerBase hZ)
    (V : BigFppfOver B U.left.1 U.left.2) (hV : IsOpenImmersion V.hom.hom)
    (T : BigFppfOver B U.left.1 U.left.2) : Subsingleton (T ⟶ V) := by
  have : IsOpenImmersion V.hom.hom := hV
  have : Mono V.hom := B.inclusion.mono_of_mono_map (by
    change Mono V.hom.hom
    infer_instance)
  refine ⟨fun a b ↦ ?_⟩
  apply Over.OverMorphism.ext
  apply (cancel_mono V.hom).mp
  exact (Over.w a).trans (Over.w b).symm

/-- Every algebraic space representing the base change of the inclusion (0D50) along a
scheme-valued point is the clopen locus cut out by the relative-dimension bound. -/
private theorem exists_curveLocus_presheafIso (U : BigFppfOver B integerBase hZ)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ CartesianProperFlatSpaces B integerBase hZ)
    (hy : y ⋙ cartesianProperFlatProjection B integerBase hZ = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) (curvesProjectionOver B hZ)
        (cartesianProperFlatProjection B integerBase hZ) y (curvesToCartesianProperFlat B hZ))
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    ∃ V : BigFppfOver B U.left.1 U.left.2,
      IsOpenImmersion V.hom.hom ∧ IsClosedImmersion V.hom.hom ∧
        Nonempty (F ≅ yoneda.obj V) := by
  obtain ⟨V, hVo, hVc, hV⟩ := exists_curveLocus B hZ U y hy
  have := curvesToCartesianProperFlat_full B hZ
  have := curvesToCartesianProperFlat_faithful B hZ
  have := twoFibreProduct_fst_full (Over.map U.hom) (curvesProjectionOver B hZ)
    (cartesianProperFlatProjection B integerBase hZ) y (curvesToCartesianProperFlat B hZ) hy rfl
  have := equivalenceOver_full e
  refine ⟨V, hVo, hVc, nonempty_presheafIso_of_subsingleton F (yoneda.obj V)
    (subsingleton_of_presheafProjection_full F)
    (fun T ↦ curveLocus_subsingleton B hZ U V hVo T.unop) ?_⟩
  intro T
  rw [← presheafProjection_image F T.unop, ← equivalenceOver_image e T.unop,
    curveFiber_image B hZ U y hy T.unop]
  exact (hV T.unop).symm

/-- The comparison from the lower-shriek extension of a representable presheaf on a slice site to
the presheaf represented by the pushforward of the representing object. -/
private def relocalizeYonedaHom {C : Type u} [Category.{v} C]
    {U S : C} (g : U ⟶ S) (V : Over U) :
    (OverShriek.relocalizePresheafFunctor g).obj (yoneda.obj V) ⟶
      yoneda.obj ((Over.map g).obj V) where
  app W := ↾fun s => Over.homMk s.1.2.left (by
    change s.1.2.left ≫ (V.hom ≫ g) = W.unop.hom
    rw [← Category.assoc, Over.w s.1.2]
    exact s.2)
  naturality _ _ _ := by ext s; rfl

/-- The lower-shriek extension of a representable presheaf on a slice site is represented by the
pushforward of the representing object. -/
private def relocalizeYonedaIso {C : Type u} [Category.{v} C]
    {U S : C} (g : U ⟶ S) (V : Over U) :
    (OverShriek.relocalizePresheafFunctor g).obj (yoneda.obj V) ≅
      yoneda.obj ((Over.map g).obj V) := by
  refine NatIso.ofComponents (fun W => Equiv.toIso {
    toFun := (relocalizeYonedaHom g V).app W
    invFun := fun a => ⟨⟨a.left ≫ V.hom, Over.homMk a.left rfl⟩, by
      change (a.left ≫ V.hom) ≫ g = W.unop.hom
      rw [Category.assoc]
      exact a.w⟩
    left_inv := ?_
    right_inv := ?_ }) ?_
  · intro s
    rcases s with ⟨⟨ψ, a⟩, h⟩
    apply Subtype.ext
    change (⟨a.left ≫ V.hom, Over.homMk a.left rfl⟩ :
      Σ ψ : W.unop.left ⟶ U, (Over.mk ψ ⟶ V)) = ⟨ψ, a⟩
    have hh := OverShriek.sigmaMk_eq (yoneda.obj V) (𝟙 V)
      (Over.homMk a.left rfl : Over.mk (a.left ≫ V.hom) ⟶ V) a rfl
    change (⟨a.left ≫ V.hom, (Over.homMk a.left rfl : Over.mk (a.left ≫ V.hom) ⟶ V) ≫ 𝟙 V⟩ :
      Σ ψ : W.unop.left ⟶ U, (Over.mk ψ ⟶ V)) = ⟨ψ, a ≫ 𝟙 V⟩ at hh
    simpa only [Category.comp_id] using hh
  · intro a
    apply Over.OverMorphism.ext
    rfl
  · intro W W' f
    exact (relocalizeYonedaHom g V).naturality f

/-- The structural morphism of the lower-shriek extension of a presheaf on a slice site: it reads
off the factorization through the slice object. -/
private def relocalizeStructureMap {C : Type u} [Category.{v} C]
    {U S : C} (g : U ⟶ S) (F : (Over U)ᵒᵖ ⥤ Type v) :
    (OverShriek.relocalizePresheafFunctor g).obj F ⟶ yoneda.obj (Over.mk g) where
  app W := ↾fun s => Over.homMk s.1.1 s.2
  naturality _ _ _ := by ext s; rfl

/-- The lower-shriek extension of a morphism of presheaves is a morphism over the slice
object. -/
private theorem relocalizeMap_structure {C : Type u} [Category.{v} C]
    {U S : C} (g : U ⟶ S) {F G : (Over U)ᵒᵖ ⥤ Type v} (a : F ⟶ G) :
    (OverShriek.relocalizePresheafFunctor g).map a ≫ relocalizeStructureMap g G =
      relocalizeStructureMap g F := by
  ext W s
  rfl

/-- The identification of the lower-shriek extension of a representable presheaf is one over the
slice object. -/
private theorem relocalizeYonedaIso_structure {C : Type u} [Category.{v} C]
    {U S : C} (g : U ⟶ S) (V : Over U) :
    (relocalizeYonedaIso g V).hom ≫
        yoneda.map (Over.homMk V.hom rfl : (Over.map g).obj V ⟶ Over.mk g) =
      relocalizeStructureMap g (yoneda.obj V) := by
  ext W s
  apply Over.OverMorphism.ext
  exact Over.w s.1.2

/-- An algebraic space over `U` isomorphic to a clopen subscheme of `U`, read over the base `S`,
has open and closed immersion structural morphism. -/
private theorem smallerBase_structureMap_immersion (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
    (V : BigFppfOver B U.left.1 U.left.2) (e : F ≅ yoneda.obj V)
    (hVo : IsOpenImmersion V.hom.hom) (hVc : IsClosedImmersion V.hom.hom) :
    Space.IsOpenImmersion B S hS
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩).1.hom ∧
      Space.IsClosedImmersion B S hS
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩).1.hom := by
  let H := (spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩
  let i := (spacesOverSmallerBaseFunctorForgetIso B U.left.1 S U.left.2 hS U.hom).app ⟨F, hF⟩
  let L := OverShriek.relocalizePresheafFunctor U.hom
  let j : H.1.left ≅ yoneda.obj ((Over.map U.hom).obj V) :=
    i ≪≫ L.mapIso e ≪≫ relocalizeYonedaIso U.hom V
  let k : (Over.map U.hom).obj V ⟶ Over.mk U.hom := Over.homMk V.hom rfl
  have hi : i.inv ≫ H.1.hom = relocalizeStructureMap U.hom F := by
    ext W s
    exact spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app B U.left.1 S U.left.2 hS U.hom
      ⟨F, hF⟩ W s
  have hj : j.hom ≫ yoneda.map k = H.1.hom := by
    dsimp only [j, Iso.trans_hom, Functor.mapIso_hom]
    rw [Category.assoc, Category.assoc, relocalizeYonedaIso_structure, relocalizeMap_structure]
    change i.hom ≫ relocalizeStructureMap U.hom F = H.1.hom
    rw [← hi, Iso.hom_inv_id_assoc]
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  have key (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] [P.RespectsIso]
      (hP : P V.hom.hom) :
      (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf
        (j.hom ≫ yoneda.map k) := by
    have := MorphismProperty.inverseImage_isStableUnderBaseChange
      (BigFppfOver.toScheme B S hS) P
    exact (MorphismProperty.cancel_left_of_respectsIso _ j.hom (yoneda.map k)).mpr
      (MorphismProperty.relative_map (P := MorphismProperty.inverseImage P
        (BigFppfOver.toScheme B S hS)) hP)
  rw [← hj]
  exact ⟨key _ hVo, key _ hVc⟩

/-- **Stacks 0D5B.** The 1-morphism from the category of families of curves to the category of
finitely presented, flat and proper families of algebraic spaces of Stacks equation 0D50 is
representable by algebraic spaces. -/
@[stacks 0D5B "representability by algebraic spaces"]
theorem isRepresentableByAlgebraicSpaces_curvesToCartesianProperFlat :
    Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
      (curvesToCartesianProperFlatHom B hZ).hom := by
  intro U
  dsimp only
  intro y hy
  obtain ⟨V, hVo, hVc, hV⟩ := exists_curveLocus B hZ U y hy
  have hGfull : (curvesToCartesianProperFlatHom B hZ).hom.toFunctor.Full :=
    curvesToCartesianProperFlat_full B hZ
  have hGfaithful : (curvesToCartesianProperFlatHom B hZ).hom.toFunctor.Faithful :=
    curvesToCartesianProperFlat_faithful B hZ
  have hfull : (TwoFibreProductOver.fst (Over.map U.hom)
      (curvesFiberedCategory B hZ).val.p
      (cartesianProperFlatFiberedCategory B integerBase hZ).val.p y
      (curvesToCartesianProperFlatHom B hZ).hom.toFunctor).Full :=
    twoFibreProduct_fst_full _ _ _ _ _ hy rfl
  have hfaithful : (TwoFibreProductOver.fst (Over.map U.hom)
      (curvesFiberedCategory B hZ).val.p
      (cartesianProperFlatFiberedCategory B integerBase hZ).val.p y
      (curvesToCartesianProperFlatHom B hZ).hom.toFunctor).Faithful :=
    twoFibreProduct_fst_faithful _ _ _ _ _
  have := presheafProjection_full (yoneda.obj V)
    (fun T ↦ curveLocus_subsingleton B hZ U V hVo T.unop)
  have := presheafProjection_faithful (yoneda.obj V)
  refine ⟨yoneda.obj V, isAlgebraicSpace_yoneda B U.left.1 U.left.2 V,
    nonempty_equivalenceOver_of_fullyFaithful _ _ ?_⟩
  intro T
  have hfib : (∃ a, (TwoFibreProductOver.fst (Over.map U.hom)
        (curvesFiberedCategory B hZ).val.p
        (cartesianProperFlatFiberedCategory B integerBase hZ).val.p y
        (curvesToCartesianProperFlatHom B hZ).hom.toFunctor).obj a = T) ↔
      Space.HasRelativeDimensionLE 1 B integerBase hZ (y.obj T).obj.obj.hom :=
    curveFiber_image B hZ U y hy T
  rw [hfib, presheafProjection_image]
  exact (hV T).symm

/-- **Stacks 0D5B.** The 1-morphism from the category of families of curves to the category of
finitely presented, flat and proper families of algebraic spaces of Stacks equation 0D50 is an
open immersion: every algebraic space representing one of its base changes has open immersion
structural morphism. -/
@[stacks 0D5B "open immersions"]
theorem isOpenImmersion_curvesToCartesianProperFlat :
    Stack.IsOpenImmersion B integerBase hZ (curvesToCartesianProperFlatHom B hZ) := by
  intro U y hy F hF he
  obtain ⟨V, hVo, hVc, ⟨i⟩⟩ := exists_curveLocus_presheafIso B hZ U y hy F he.some
  exact (smallerBase_structureMap_immersion B integerBase hZ U F hF V i hVo hVc).1

/-- **Stacks 0D5B.** The 1-morphism from the category of families of curves to the category of
finitely presented, flat and proper families of algebraic spaces of Stacks equation 0D50 is a
closed immersion: every algebraic space representing one of its base changes has closed immersion
structural morphism. -/
@[stacks 0D5B "closed immersions"]
theorem isClosedImmersion_curvesToCartesianProperFlat :
    Stack.IsClosedImmersion B integerBase hZ (curvesToCartesianProperFlatHom B hZ) := by
  intro U y hy F hF he
  obtain ⟨V, hVo, hVc, ⟨i⟩⟩ := exists_curveLocus_presheafIso B hZ U y hy F he.some
  exact (smallerBase_structureMap_immersion B integerBase hZ U F hF V i hVo hVc).2

end Immersion

end AlgebraicGeometry

end
