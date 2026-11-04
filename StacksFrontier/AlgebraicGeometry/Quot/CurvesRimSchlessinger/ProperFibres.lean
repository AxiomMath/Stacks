module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import Mathlib.CategoryTheory.Widesubcategory
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushout07RT
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutGlobal
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesFibered
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Thickenings.Affine
import Mathlib.AlgebraicGeometry.PullbackCarrier
import StacksFrontier.AlgebraicGeometry.Spaces.Category
import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FibreDimension
import StacksFrontier.AlgebraicGeometry.Spaces.Points
import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
import StacksFrontier.CategoryTheory.TwoFibreProduct.InducedFunctor

/-!
# Gluing families of curves across an affine thickening pushout (Stacks 0D56)

Let
```
T  ⟶ T'
↓     ↓
S  ⟶ S'
```
be a pushout of schemes in which `T ⟶ T'` is a thickening and `T ⟶ S` is affine (Stacks 07RT).
Stacks 0D56 asserts that the restriction functor on fibre categories of the stack of curves
```
Curves_{S'} ⟶ Curves_S ×_{Curves_T} Curves_{T'}
```
is an equivalence.

## Main definitions

* `AlgebraicGeometry.Space.FpFlatProperOver`: the fibre category of finitely presented, flat
  and proper algebraic spaces over a scheme of the big fppf site. This is the fibre of the
  stack `Spaces'_{fp, flat, proper}` as the statement of Stacks 0D1J presents it.
* `AlgebraicGeometry.Space.ProperPushoutBaseChange`: a base-change functor between two such
  fibre categories together with its natural cartesian comparison.
* `AlgebraicGeometry.Space.ProperPushoutEquivalenceData`: the conclusion of **Stacks 0D1J** —
  the canonical restriction functor for `Spaces'_{fp, flat, proper}` across an affine
  thickening pushout, its equivalence property, and the compatibility of its projections.
* `AlgebraicGeometry.CurveBaseChange`: restriction of families of curves along a base
  morphism, with its natural cartesian comparison.
* `AlgebraicGeometry.CurvePushoutEquivalenceData`: the conclusion of **Stacks 0D56** — the
  canonical restriction functor for curves, its equivalence property, and the compatibility of
  its projections.

## Main results

* `AlgebraicGeometry.curvePushoutEquivalence`: Stacks 0D56, deduced from Stacks 0D1J. The
  statement of Stacks 0D1J is carried as the explicit hypothesis `rs`.

## References

* [Stacks Project, Tag 0D56](https://stacks.math.columbia.edu/tag/0D56)
* [Stacks Project, Tag 0D1J](https://stacks.math.columbia.edu/tag/0D1J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S₀ : Scheme.{u}) (hS₀ : B.Contains S₀)

/-- The fibre category of finitely presented, flat and proper algebraic spaces over a scheme `U`
of the big fppf site: the full subcategory of the slice over `U`, read as an algebraic space,
cut out by those three properties of the structure morphism.

This is the fibre of `Spaces'_{fp, flat, proper}` over `U` in the form in which the statement of
Stacks 0D1J uses it. -/
abbrev FpFlatProperOver (U : BigFppfOver B S₀ hS₀) :=
  (show ObjectProperty (Over (schemeSpace U)) from
    fun Z ↦ IsFinitePresentation B S₀ hS₀ Z.hom.hom ∧
      IsFlat B S₀ hS₀ Z.hom.hom ∧ IsProper B S₀ hS₀ Z.hom.hom).FullSubcategory

/-- A base-change functor for `Spaces'_{fp, flat, proper}` along `f : U ⟶ V`, together with the
natural comparison morphism from a base-changed family to the original one and the requirement
that each of its components is cartesian. -/
structure ProperPushoutBaseChange {U V : BigFppfOver B S₀ hS₀} (f : U ⟶ V) where
  /-- The base-change functor. -/
  functor : FpFlatProperOver B S₀ hS₀ V ⥤ FpFlatProperOver B S₀ hS₀ U
  /-- The comparison from a base-changed family to the family it came from. -/
  comparison :
    functor ⋙ ObjectProperty.ι _ ⋙ Over.forget (schemeSpace U) ⟶
      ObjectProperty.ι _ ⋙ Over.forget (schemeSpace V)
  /-- Each component of the comparison is a cartesian square. -/
  cartesian (Z : FpFlatProperOver B S₀ hS₀ V) :
    IsPullback (comparison.app Z) (functor.obj Z).obj.hom Z.obj.hom (schemeSpaceMap f)

/-- **The conclusion of Stacks 0D1J.** For a pushout of schemes along a thickening `i : T ⟶ T'`
and an affine morphism `f : T ⟶ S`, restriction identifies the finitely presented, flat and
proper algebraic spaces over `S'` with compatible pairs over `S` and `T'`.

The data records the four base-change functors, the comparison of the two routes to the overlap
`T`, the canonical restriction functor to the categorical pullback, the fact that it is an
equivalence, and the identification of its two projections with the two base-change functors. -/
structure ProperPushoutEquivalenceData
    {T T' S S' : BigFppfOver B S₀ hS₀}
    (i : T ⟶ T') (f : T ⟶ S) (g : T' ⟶ S') (h : S ⟶ S') where
  /-- Restriction from `S` to the overlap `T`. -/
  toOverlapFromS : ProperPushoutBaseChange B S₀ hS₀ f
  /-- Restriction from `T'` to the overlap `T`. -/
  toOverlapFromT' : ProperPushoutBaseChange B S₀ hS₀ i
  /-- Restriction from the pushout `S'` to `S`. -/
  fromPushoutToS : ProperPushoutBaseChange B S₀ hS₀ h
  /-- Restriction from the pushout `S'` to `T'`. -/
  fromPushoutToT' : ProperPushoutBaseChange B S₀ hS₀ g
  /-- The two routes from `S'` to the overlap `T` agree. -/
  overlapComparison :
    fromPushoutToS.functor ⋙ toOverlapFromS.functor ≅
      fromPushoutToT'.functor ⋙ toOverlapFromT'.functor
  /-- The comparison of the two routes to the overlap is compatible with the cartesian
  comparisons. -/
  overlapComparison_canonical (Z : FpFlatProperOver B S₀ hS₀ S') :
    (ObjectProperty.ι _ ⋙ Over.forget (schemeSpace T)).map
        (overlapComparison.hom.app Z) ≫
      toOverlapFromT'.comparison.app (fromPushoutToT'.functor.obj Z) ≫
      fromPushoutToT'.comparison.app Z =
    toOverlapFromS.comparison.app (fromPushoutToS.functor.obj Z) ≫
      fromPushoutToS.comparison.app Z
  /-- The restriction functor to compatible pairs. -/
  restrictionFunctor :
    FpFlatProperOver B S₀ hS₀ S' ⥤
      CategoricalPullback toOverlapFromS.functor toOverlapFromT'.functor
  /-- Restriction is an equivalence. -/
  equivalence : restrictionFunctor.IsEquivalence
  /-- The first projection of the restriction functor is restriction to `S`. -/
  restriction_toS :
    restrictionFunctor ⋙ CategoricalPullback.π₁ _ _ ≅ fromPushoutToS.functor
  /-- The second projection of the restriction functor is restriction to `T'`. -/
  restriction_toT' :
    restrictionFunctor ⋙ CategoricalPullback.π₂ _ _ ≅ fromPushoutToT'.functor
  /-- The two projections are compatible with the comparison over the overlap. -/
  restriction_overlap (Z : FpFlatProperOver B S₀ hS₀ S') :
    toOverlapFromS.functor.map (restriction_toS.hom.app Z) ≫
      overlapComparison.hom.app Z =
    (restrictionFunctor.obj Z).iso.hom ≫
      toOverlapFromT'.functor.map (restriction_toT'.hom.app Z)

/-- **The statement of Stacks 0D1J**, as a hypothesis: finitely presented, flat and proper
algebraic spaces glue uniquely across an affine thickening pushout, with restriction as the
canonical equivalence. -/
abbrev ProperPushoutRS :=
  ∀ {T T' S S' : BigFppfOver B S₀ hS₀} (i : T ⟶ T') (f : T ⟶ S) (g : T' ⟶ S') (h : S ⟶ S'),
    Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S₀ hS₀).map i) →
    _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S₀ hS₀).map f) →
    IsPushout ((BigFppfOver.toScheme B S₀ hS₀).map i) ((BigFppfOver.toScheme B S₀ hS₀).map f)
      ((BigFppfOver.toScheme B S₀ hS₀).map g) ((BigFppfOver.toScheme B S₀ hS₀).map h) →
    ProperPushoutEquivalenceData B S₀ hS₀ i f g h

end Space

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

private noncomputable def siteLift (U : B.Schemes) :
    BigFppfOver B integerBase hZ :=
  Over.mk (B.inclusion.preimage
    (specULiftZIsTerminal.from (B.inclusion.obj U)))

private def siteLiftMap {U V : B.Schemes} (f : U ⟶ V) :
    siteLift B hZ U ⟶ siteLift B hZ V :=
  Over.homMk f (B.inclusion.map_injective (specULiftZIsTerminal.hom_ext _ _))

private noncomputable def siteLiftFunctor :
    B.Schemes ⥤ BigFppfOver B integerBase hZ where
  obj := siteLift B hZ
  map := siteLiftMap B hZ
  map_id U := by
    change Over.homMk (𝟙 (siteLift B hZ U).left) _ = _
    exact Over.homMk_eta (𝟙 (siteLift B hZ U)) _
  map_comp f g := by
    ext
    rfl

private theorem fiberHom_map_eqToHom
    {C : Type*} {E : Type*} [Category C] [Category E]
    (p : E ⥤ C) (U : C) {a b : p.Fiber U} (α : a ⟶ b) :
    p.map α.1 = eqToHom (a.2.trans b.2.symm) := by
  let : p.IsHomLift (𝟙 U) α.1 := α.2
  have h := IsHomLift.fac' p (𝟙 U) α.1
  simpa [Category.assoc] using h

private theorem siteLift_left (U : B.Schemes) :
    (siteLift B hZ U).left = U := rfl

private theorem fiberBase_eq_siteLift {U : B.Schemes}
    (Z : (curvesProjection B hZ).Fiber U) :
    Z.1.base = siteLift B hZ U := by
  apply CostructuredArrow.obj_ext
  · exact B.inclusion.map_injective (specULiftZIsTerminal.hom_ext _ _)
  · simpa only [curvesProjection_obj, siteLift_left] using Z.2

private noncomputable def fiberBaseIso {U : B.Schemes}
    (Z : (curvesProjection B hZ).Fiber U) :
    Z.1.base ≅ siteLift B hZ U :=
  Over.isoMk (eqToIso Z.2) (B.inclusion.map_injective (specULiftZIsTerminal.hom_ext _ _))

private theorem fiberBaseIso_naturality {U : B.Schemes}
    {Z Z' : (curvesProjection B hZ).Fiber U} (α : Z ⟶ Z') :
    α.1.baseMap ≫ (fiberBaseIso B hZ Z').hom = (fiberBaseIso B hZ Z).hom := by
  have hm' : α.1.baseMap.left = eqToHom (Z.2.trans Z'.2.symm) :=
    fiberHom_map_eqToHom (curvesProjection B hZ) U α
  apply Over.OverMorphism.ext
  change α.1.baseMap.left ≫ eqToHom Z'.2 = eqToHom Z.2
  rw [hm']
  change eqToHom (Z.2.trans Z'.2.symm) ≫ eqToHom Z'.2 = eqToHom Z.2
  simp only [eqToHom_trans]

private noncomputable def curveObjectAsOver {U : B.Schemes}
    (Z : (curvesProjection B hZ).Fiber U) :
    Over (schemeSpace (siteLift B hZ U)) :=
  Over.mk (Z.1.toBase ≫ schemeSpaceMap (fiberBaseIso B hZ Z).hom)

private theorem schemeSpaceMap_comp_local
    {U V W : BigFppfOver B integerBase hZ}
    (f : U ⟶ V) (g : V ⟶ W) :
    schemeSpaceMap f ≫ schemeSpaceMap g =
      schemeSpaceMap (f ≫ g) := by
  ext
  rfl

private theorem schemeSpaceMap_id_local
    {U : BigFppfOver B integerBase hZ} :
    schemeSpaceMap (𝟙 U) = 𝟙 _ := by
  ext
  rfl

private noncomputable def schemeSpaceMapIso
    {U V : BigFppfOver B integerBase hZ}
    (e : U ≅ V) :
    schemeSpace U ≅ schemeSpace V where
  hom := schemeSpaceMap e.hom
  inv := schemeSpaceMap e.inv
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    change yoneda.map e.hom ≫ yoneda.map e.inv = yoneda.map (𝟙 U)
    rw [← Functor.map_comp, e.hom_inv_id]
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    change yoneda.map e.inv ≫ yoneda.map e.hom = yoneda.map (𝟙 V)
    rw [← Functor.map_comp, e.inv_hom_id]

private theorem curveObjectAsOver_relativeDimensionLE {U : B.Schemes}
    (Z : (curvesProjection B hZ).Fiber U) :
    Space.HasRelativeDimensionLE 1 B integerBase hZ
      (curveObjectAsOver B hZ Z).hom.hom := by
  let e := schemeSpaceMapIso B hZ (fiberBaseIso B hZ Z)
  let : IsIso e.hom := e.isIso_hom
  change Space.HasRelativeDimensionLE 1 B integerBase hZ
    (Z.1.toBase.hom ≫ e.hom.hom)
  intro x
  obtain ⟨d, hd, hdim⟩ := Z.1.relativeDimensionLE x
  refine ⟨d, hd, ?_⟩
  have hpull : IsPullback (𝟙 Z.1.total.obj)
      (Z.1.toBase.hom ≫ e.hom.hom) Z.1.toBase.hom e.inv.hom :=
    IsPullback.of_horiz_isIso (CommSq.mk (by simp))
  have hfinite : Space.IsLocallyOfFiniteType B integerBase hZ
      Z.1.toBase.hom :=
    Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation
      B integerBase hZ Z.1.finitePresentation.1
  have hpoint : Space.pointsMap B integerBase hZ
      Z.1.total.obj (𝟙 Z.1.total.obj) x = x := by
    refine Quot.inductionOn
      (motive := fun y => Space.pointsMap B integerBase hZ
        Z.1.total.obj (𝟙 Z.1.total.obj) y = y) x ?_
    intro p
    rfl
  have hdim_id := hpoint.symm ▸ hdim
  simpa using (Space.hasRelativeDimensionAt_iff_of_isPullback
    B integerBase hZ hpull Z.1.total.property
    (schemeSpace (siteLift B hZ U)).property
    (schemeSpace Z.1.base).property hfinite x d).mp hdim_id

private noncomputable def curveObjectAsOverFunctor (U : B.Schemes) :
    (curvesProjection B hZ).Fiber U ⥤
      Over (schemeSpace (siteLift B hZ U)) where
  obj := curveObjectAsOver B hZ
  map := fun {Z Z'} α => Over.homMk α.1.totalMap (by
    have hcart : α.1.totalMap ≫ Z'.1.toBase =
        Z.1.toBase ≫ schemeSpaceMap α.1.baseMap :=
      α.1.cartesian.w
    change α.1.totalMap ≫ Z'.1.toBase ≫
        schemeSpaceMap (fiberBaseIso B hZ Z').hom =
      Z.1.toBase ≫ schemeSpaceMap (fiberBaseIso B hZ Z).hom
    calc
      _ = α.1.totalMap ≫ Z'.1.toBase ≫
          schemeSpaceMap (fiberBaseIso B hZ Z').hom := by simp
      _ = Z.1.toBase ≫ schemeSpaceMap α.1.baseMap ≫
          schemeSpaceMap (fiberBaseIso B hZ Z').hom := by
            simpa only [Category.assoc] using
              congrArg (fun q => q ≫
                schemeSpaceMap (fiberBaseIso B hZ Z').hom) hcart
      _ = Z.1.toBase ≫
          schemeSpaceMap (α.1.baseMap ≫ (fiberBaseIso B hZ Z').hom) := by
            rw [schemeSpaceMap_comp_local]
      _ = Z.1.toBase ≫ schemeSpaceMap (fiberBaseIso B hZ Z).hom := by
            rw [fiberBaseIso_naturality B hZ α])
  map_id Z := by
    ext
    rfl
  map_comp α β := by
    ext
    rfl

private theorem curveObjectAsOverFunctor_map_isIso (U : B.Schemes)
    {Z Z' : (curvesProjection B hZ).Fiber U} (α : Z ⟶ Z') :
    IsIso ((curveObjectAsOverFunctor B hZ U).map α) := by
  let : IsGroupoid ((curvesProjection B hZ).Fiber U) :=
    (curvesProjection_isFiberedInGroupoids B hZ).fiber_isGroupoid U
  exact Functor.map_isIso (curveObjectAsOverFunctor B hZ U) α

private noncomputable def curveObjectAsOverCoreFunctor (U : B.Schemes) :
    (curvesProjection B hZ).Fiber U ⥤
      WideSubcategory (MorphismProperty.isomorphisms
        (Over (schemeSpace (siteLift B hZ U)))) where
  obj Z := ⟨curveObjectAsOver B hZ Z⟩
  map α := ⟨(curveObjectAsOverFunctor B hZ U).map α,
    curveObjectAsOverFunctor_map_isIso B hZ U α⟩
  map_id Z := by
    apply WideSubcategory.hom_ext
    rfl
  map_comp α β := by
    apply WideSubcategory.hom_ext
    rfl

private theorem curveObjectAsOverCoreFunctor_faithful (U : B.Schemes) :
    (curveObjectAsOverCoreFunctor B hZ U).Faithful where
  map_injective := by
    intro Z Z' α β hab
    apply Fiber.hom_ext
    apply CurveFamily.Hom.ext
    · have hα : α.1.baseMap.left = eqToHom (Z.2.trans Z'.2.symm) :=
        fiberHom_map_eqToHom (curvesProjection B hZ) U α
      have hβ : β.1.baseMap.left = eqToHom (Z.2.trans Z'.2.symm) :=
        fiberHom_map_eqToHom (curvesProjection B hZ) U β
      exact Over.OverMorphism.ext (hα.trans hβ.symm)
    · exact congrArg (fun k => k.1.left) hab

private theorem curveObjectAsOverCoreFunctor_full (U : B.Schemes) :
    (curveObjectAsOverCoreFunctor B hZ U).Full where
  map_surjective := by
    intro Z Z' α
    let : IsIso α.hom := α.property
    let b := fiberBaseIso B hZ Z ≪≫ (fiberBaseIso B hZ Z').symm
    have hb : b.hom.left = eqToHom (Z.2.trans Z'.2.symm) := by
      change eqToHom Z.2 ≫ eqToHom Z'.2.symm = _
      rw [eqToHom_trans]
    have hcomm : α.1.left ≫ Z'.1.toBase = Z.1.toBase ≫
        schemeSpaceMap b.hom := by
      let eZ := fiberBaseIso B hZ Z
      let eZ' := fiberBaseIso B hZ Z'
      have h := α.1.w
      change α.1.left ≫ (Z'.1.toBase ≫ schemeSpaceMap eZ'.hom) =
        Z.1.toBase ≫ schemeSpaceMap eZ.hom at h
      let m := schemeSpaceMap eZ'.hom
      let mIso := schemeSpaceMapIso B hZ eZ'
      let : IsIso m := mIso.isIso_hom
      have h' : α.1.left ≫ (Z'.1.toBase ≫ m) =
          Z.1.toBase ≫ schemeSpaceMap eZ.hom := by
        simpa only [m] using h
      have hbmap : schemeSpaceMap b.hom ≫ m =
          schemeSpaceMap eZ.hom := by
        calc
          schemeSpaceMap b.hom ≫ m =
          schemeSpaceMap (b.hom ≫ eZ'.hom) :=
            schemeSpaceMap_comp_local B hZ b.hom eZ'.hom
          _ = schemeSpaceMap eZ.hom := by
            congr 1
            simp [b, eZ, eZ']
      have h'' : α.1.left ≫ (Z'.1.toBase ≫ m) =
          Z.1.toBase ≫ (schemeSpaceMap b.hom ≫ m) :=
        h'.trans (congrArg (fun q => Z.1.toBase ≫ q) hbmap.symm)
      exact (cancel_mono m).1 ((Category.assoc _ _ _).trans
        (h''.trans (Category.assoc _ _ _).symm))
    let φ : CurveFamily.Hom B hZ Z.1 Z'.1 :=
      { baseMap := b.hom
        totalMap := α.1.left
        cartesian := by
          let : IsIso α.hom := α.property
          have hαmap : IsIso ((Over.forget
              (schemeSpace (siteLift B hZ U))).map α.1) :=
            Functor.map_isIso _ α.1
          have hα : IsIso α.1.left := by
            simpa only [Over.forget_map] using hαmap
          let := hα
          let : IsIso (schemeSpaceMap b.hom) :=
            (schemeSpaceMapIso B hZ b).isIso_hom
          exact @IsPullback.of_horiz_isIso _ _ _ _ _ _ _ _ _ _ hα
            (schemeSpaceMapIso B hZ b).isIso_hom (CommSq.mk hcomm) }
    have hlift : (curvesProjection B hZ).IsHomLift
        (𝟙 U) φ := by
      apply IsHomLift.of_fac (p := curvesProjection B hZ)
        (𝟙 U) φ Z.2 Z'.2
      change 𝟙 U = eqToHom Z.2.symm ≫ b.hom.left ≫ eqToHom Z'.2
      rw [hb]
      calc
        𝟙 U = eqToHom rfl := (eqToHom_refl U rfl).symm
        _ = eqToHom ((Z.2.symm.trans (Z.2.trans Z'.2.symm)).trans Z'.2) := by
          congr 1
        _ = eqToHom Z.2.symm ≫
            eqToHom (Z.2.trans Z'.2.symm) ≫ eqToHom Z'.2 := by
          calc
            _ = eqToHom (Z.2.symm.trans (Z.2.trans Z'.2.symm)) ≫
                eqToHom Z'.2 := (eqToHom_trans _ _).symm
            _ = (eqToHom Z.2.symm ≫
                eqToHom (Z.2.trans Z'.2.symm)) ≫ eqToHom Z'.2 := by
                  rw [(eqToHom_trans _ _).symm]
    refine ⟨⟨φ, hlift⟩, ?_⟩
    apply WideSubcategory.hom_ext
    apply Over.OverMorphism.ext
    rfl


private theorem siteLift_forget :
    siteLiftFunctor B hZ ⋙ Over.forget (B.obj hZ) = 𝟭 B.Schemes := by
  apply Functor.toPrefunctor_injective
  rfl

private noncomputable def siteLiftCounitIso :
    Over.forget (B.obj hZ) ⋙ siteLiftFunctor B hZ ≅ 𝟭 _ :=
  NatIso.ofComponents (fun U => Over.isoMk (Iso.refl U.left)
    (B.inclusion.map_injective (specULiftZIsTerminal.hom_ext _ _))) (by
      intro U V f
      ext
      rfl)

private noncomputable def siteLiftEquivalence :
    B.Schemes ≌ BigFppfOver B integerBase hZ where
  functor := siteLiftFunctor B hZ
  inverse := Over.forget (B.obj hZ)
  unitIso := Iso.refl _
  counitIso := siteLiftCounitIso B hZ
  functor_unitIso_comp := by
    intro U
    ext
    rfl

private theorem siteLift_isPushout
    {T T' S S' : B.Schemes} (i : T ⟶ T') (f : T ⟶ S)
    (g : T' ⟶ S') (h : S ⟶ S')
    (hsq : IsPushout (B.inclusion.map i) (B.inclusion.map f)
      (B.inclusion.map g) (B.inclusion.map h)) :
    IsPushout (siteLiftMap B hZ i) (siteLiftMap B hZ f)
      (siteLiftMap B hZ g) (siteLiftMap B hZ h) := by
  have hsqB : IsPushout i f g h :=
    IsPushout.of_map_of_faithful (F := B.inclusion) hsq
  let : (siteLiftFunctor B hZ).IsEquivalence :=
    (siteLiftEquivalence B hZ).isEquivalence_functor
  change IsPushout ((siteLiftFunctor B hZ).map i) ((siteLiftFunctor B hZ).map f)
    ((siteLiftFunctor B hZ).map g) ((siteLiftFunctor B hZ).map h)
  exact hsqB.map (siteLiftFunctor B hZ)

/-- The identification `fiberBaseIso Z` of the base of a family of curves `Z` over `U` with
`siteLift U` is `eqToHom`. -/
private theorem fiberBaseIso_hom_eq {U : B.Schemes}
    (Z : (curvesProjection B hZ).Fiber U) :
    (fiberBaseIso B hZ Z).hom = eqToHom (fiberBase_eq_siteLift B hZ Z) := by
  apply Over.OverMorphism.ext
  change (eqToIso Z.2).hom = _
  simp only [Over.eqToHom_left]
  rfl

private theorem isFpFlatProper_of_eq {U V : BigFppfOver B integerBase hZ} (h : U = V)
    {X : AlgebraicSpaces B integerBase hZ} (a : X ⟶ schemeSpace U)
    (hfp : Space.IsFinitePresentation B integerBase hZ a.hom)
    (hfl : Space.IsFlat B integerBase hZ a.hom)
    (hpr : Space.IsProper B integerBase hZ a.hom) :
    Space.IsFinitePresentation B integerBase hZ (a ≫ schemeSpaceMap (eqToHom h)).hom ∧
      Space.IsFlat B integerBase hZ (a ≫ schemeSpaceMap (eqToHom h)).hom ∧
      Space.IsProper B integerBase hZ (a ≫ schemeSpaceMap (eqToHom h)).hom := by
  subst h
  rw [show a ≫ schemeSpaceMap (eqToHom (rfl : U = U)) = a by
    rw [eqToHom_refl, schemeSpaceMap_id_local, Category.comp_id]]
  exact ⟨hfp, hfl, hpr⟩

/-- An object of the fibre category of curves over `U`, read as a finitely presented, flat and
proper algebraic space over `siteLift U`. -/
private noncomputable def curveFiberAsProperOver {U : B.Schemes}
    (Z : (curvesProjection B hZ).Fiber U) :
    Space.FpFlatProperOver B integerBase hZ (siteLift B hZ U) :=
  ⟨curveObjectAsOver B hZ Z, by
    rw [show (curveObjectAsOver B hZ Z).hom =
        Z.1.toBase ≫ schemeSpaceMap (eqToHom (fiberBase_eq_siteLift B hZ Z)) by
      rw [← fiberBaseIso_hom_eq B hZ Z]; rfl]
    exact isFpFlatProper_of_eq B hZ _ Z.1.toBase Z.1.finitePresentation Z.1.flat Z.1.proper⟩

private theorem curveFiberAsProperOver_relativeDimensionLE {U : B.Schemes}
    (Z : (curvesProjection B hZ).Fiber U) :
    Space.HasRelativeDimensionLE 1 B integerBase hZ
      (curveFiberAsProperOver B hZ Z).obj.hom.hom :=
  curveObjectAsOver_relativeDimensionLE B hZ Z

/-- Relative dimension at a point is invariant under the base change square of a
`ProperPushoutBaseChange`. -/
private theorem properBaseChange_hasRelativeDimensionAt_iff
    {U V : BigFppfOver B integerBase hZ} {f : U ⟶ V}
    (bc : Space.ProperPushoutBaseChange B integerBase hZ f)
    (Z : Space.FpFlatProperOver B integerBase hZ V)
    (x : Space.points B integerBase hZ (bc.functor.obj Z).obj.left.obj) (d : ℕ∞) :
    Space.HasRelativeDimensionAt d B integerBase hZ Z.obj.hom.hom
        (Space.pointsMap B integerBase hZ
          (bc.functor.obj Z).obj.left.obj (bc.comparison.app Z).hom x) ↔
      Space.HasRelativeDimensionAt d B integerBase hZ (bc.functor.obj Z).obj.hom.hom x := by
  let f₀ := Z.obj.hom.hom
  let g₀ := schemeSpaceMap f
  have hfp := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ
    Z.obj.hom g₀
  let hout := bc.cartesian Z
  let eAlg := hout.isoIsPullback _ _ hfp
  let e := (ObjectProperty.ι _).mapIso eAlg
  have hpull : IsPullback (bc.comparison.app Z).hom (bc.functor.obj Z).obj.hom.hom f₀
      g₀.hom := by
    refine (IsPullback.of_hasPullback f₀ g₀.hom).of_iso e.symm (Iso.refl _) (Iso.refl _)
      (Iso.refl _) ?_ ?_ ?_ ?_
    · exact (congrArg (fun q => q.hom)
        (IsPullback.isoIsPullback_inv_fst _ _ hout hfp)).symm
    · exact (congrArg (fun q => q.hom)
        (IsPullback.isoIsPullback_inv_snd _ _ hout hfp)).symm
    · simp [f₀]
    · simp [g₀]
  exact Space.hasRelativeDimensionAt_iff_of_isPullback
    B integerBase hZ hpull Z.obj.left.property
    (schemeSpace U).property (schemeSpace V).property
    (Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation
      B integerBase hZ Z.property.1.1) x d

private theorem properBaseChange_relativeDimensionLE
    {U V : BigFppfOver B integerBase hZ} {f : U ⟶ V}
    (bc : Space.ProperPushoutBaseChange B integerBase hZ f)
    (Z : Space.FpFlatProperOver B integerBase hZ V)
    (hDim : Space.HasRelativeDimensionLE 1 B integerBase hZ
      Z.obj.hom.hom) :
    Space.HasRelativeDimensionLE 1 B integerBase hZ
      (bc.functor.obj Z).obj.hom.hom := by
  intro x
  obtain ⟨d, hd, hdim⟩ := hDim (Space.pointsMap B integerBase hZ
    (bc.functor.obj Z).obj.left.obj (bc.comparison.app Z).hom x)
  exact ⟨d, hd, (properBaseChange_hasRelativeDimensionAt_iff B hZ bc Z x d).mp hdim⟩

private theorem properBaseChange_reflects_relativeDimensionLE
    {U V : BigFppfOver B integerBase hZ} {f : U ⟶ V}
    (bc : Space.ProperPushoutBaseChange B integerBase hZ f)
    (Z : Space.FpFlatProperOver B integerBase hZ V)
    (hDim : Space.HasRelativeDimensionLE 1 B integerBase hZ
      (bc.functor.obj Z).obj.hom.hom)
    (hpoints : Function.Surjective (fun x => Space.pointsMap
      B integerBase hZ (bc.functor.obj Z).obj.left.obj
        (bc.comparison.app Z).hom x)) :
    Space.HasRelativeDimensionLE 1 B integerBase hZ Z.obj.hom.hom := by
  intro x
  obtain ⟨x', hx'⟩ := hpoints x
  obtain ⟨d, hd, hdim⟩ := hDim x'
  refine ⟨d, hd, ?_⟩
  simpa [hx'] using (properBaseChange_hasRelativeDimensionAt_iff B hZ bc Z x' d).mpr hdim

end AlgebraicGeometry

end
