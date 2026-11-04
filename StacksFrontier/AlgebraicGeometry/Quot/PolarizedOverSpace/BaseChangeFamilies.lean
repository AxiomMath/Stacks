module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedOverSpace.BaseChangePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowTwistWitness
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallBaseChangeChartFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.ModuleFiniteness
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSequenceSplitExact
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties

/-!
# The polarized families of schemes attached to a polarized family of algebraic spaces

Let `(X ⟶ T, L)` be a polarized family of algebraic spaces over `T` and `(U, t)` a point of `T`.
The base change `Z ⟶ U` of `X ⟶ T` along `t`, with the inverse image `q^* L` of `L` along the
projection `q : Z ⟶ X`, is an object of
`AlgebraicGeometry.PolarizedOverSpace.RepresentedPolarized`: the morphism `Z ⟶ U` is proper, flat
and of finite presentation because `X ⟶ T` is (Stacks 04WP, 03MO, 03XR, read on schemes), the
module `q^* L` is quasi-coherent because `L` is invertible, and its restriction to the Zariski
site of `Z` is invertible and ample on `Z/U` by the definition of relative ampleness
(Stacks 0D31). A morphism of points gives a cartesian square of schemes, and an isomorphism of
polarized families an isomorphism of base changes; in both cases the comparison of modules is an
isomorphism.

## Main definitions

* `AlgebraicGeometry.PolarizedOverSpace.representedFamily`: the object at a point.
* `AlgebraicGeometry.PolarizedOverSpace.baseChangeRepresented`: the functor over the site from the
  points of `T` to `RepresentedPolarized`.
* `AlgebraicGeometry.PolarizedOverSpace.baseChangeRepresentedFunctor`: the functor `F^R` from the
  polarized families of algebraic spaces over `T` to the functors over the site from the points of
  `T` to `RepresentedPolarized`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Pseudofunctor.CoGrothendieck

universe u

namespace CategoryTheory

/-- A functor all of whose morphisms satisfy a multiplicative property `P` lifts to the wide
subcategory of `P`. -/
@[simps]
def WideSubcategory.lift {C D : Type*} [Category C] [Category D] (P : MorphismProperty C)
    [P.IsMultiplicative] (F : D ⥤ C) (hF : ∀ {X Y : D} (f : X ⟶ Y), P (F.map f)) :
    D ⥤ WideSubcategory P where
  obj X := ⟨F.obj X⟩
  map f := ⟨F.map f, hF f⟩
  map_id X := WideSubcategory.hom_ext _ (F.map_id X)
  map_comp f g := WideSubcategory.hom_ext _ (F.map_comp f g)

/-- A natural transformation between functors all of whose morphisms satisfy `P`, whose
components satisfy `P`, lifts to the wide subcategory of `P`. -/
@[simps]
def WideSubcategory.liftNatTrans {C D : Type*} [Category C] [Category D] (P : MorphismProperty C)
    [P.IsMultiplicative] {F G : D ⥤ C} (hF : ∀ {X Y : D} (f : X ⟶ Y), P (F.map f))
    (hG : ∀ {X Y : D} (f : X ⟶ Y), P (G.map f)) (α : F ⟶ G) (hα : ∀ X, P (α.app X)) :
    WideSubcategory.lift P F hF ⟶ WideSubcategory.lift P G hG where
  app X := ⟨α.app X, hα X⟩
  naturality _ _ f := WideSubcategory.hom_ext _ (α.naturality f)

/-- The lift of a natural transformation equal to the identity is the identity. -/
theorem WideSubcategory.liftNatTrans_id {C D : Type*} [Category C] [Category D]
    (P : MorphismProperty C) [P.IsMultiplicative] {F : D ⥤ C}
    (hF : ∀ {X Y : D} (f : X ⟶ Y), P (F.map f)) (α : F ⟶ F) (hα : ∀ X, P (α.app X))
    (h : α = 𝟙 F) : WideSubcategory.liftNatTrans P hF hF α hα = 𝟙 _ := by
  subst h
  rfl

/-- The lift of a natural transformation equal to a composite `α ≫ β` is the composite of the lifts
of `α` and `β`. -/
theorem WideSubcategory.liftNatTrans_comp {C D : Type*} [Category C] [Category D]
    (P : MorphismProperty C) [P.IsMultiplicative] {F G H : D ⥤ C}
    (hF : ∀ {X Y : D} (f : X ⟶ Y), P (F.map f)) (hG : ∀ {X Y : D} (f : X ⟶ Y), P (G.map f))
    (hH : ∀ {X Y : D} (f : X ⟶ Y), P (H.map f)) (α : F ⟶ G) (hα : ∀ X, P (α.app X))
    (β : G ⟶ H) (hβ : ∀ X, P (β.app X)) (γ : F ⟶ H) (hγ : ∀ X, P (γ.app X)) (h : γ = α ≫ β) :
    WideSubcategory.liftNatTrans P hF hH γ hγ =
      WideSubcategory.liftNatTrans P hF hG α hα ≫ WideSubcategory.liftNatTrans P hG hH β hβ := by
  subst h
  rfl

/-- A natural transformation between functors into a full subcategory's ambient category lifts
to the full subcategory. -/
@[simps]
def ObjectProperty.liftNatTrans {C D : Type*} [Category C] [Category D] (P : ObjectProperty C)
    {F G : D ⥤ C} (hF : ∀ X, P (F.obj X)) (hG : ∀ X, P (G.obj X)) (α : F ⟶ G) :
    P.lift F hF ⟶ P.lift G hG where
  app X := ObjectProperty.homMk (α.app X)
  naturality _ _ f := ObjectProperty.hom_ext _ (α.naturality f)

/-- The lift of a natural transformation equal to the identity is the identity. -/
theorem ObjectProperty.liftNatTrans_id {C D : Type*} [Category C] [Category D]
    (P : ObjectProperty C) {F : D ⥤ C} (hF : ∀ X, P (F.obj X)) (α : F ⟶ F) (h : α = 𝟙 F) :
    ObjectProperty.liftNatTrans P hF hF α = 𝟙 _ := by
  subst h
  rfl

/-- The lift of a natural transformation equal to a composite `α ≫ β` is the composite of the lifts
of `α` and `β`. -/
theorem ObjectProperty.liftNatTrans_comp {C D : Type*} [Category C] [Category D]
    (P : ObjectProperty C) {F G H : D ⥤ C} (hF : ∀ X, P (F.obj X)) (hG : ∀ X, P (G.obj X))
    (hH : ∀ X, P (H.obj X)) (α : F ⟶ G) (β : G ⟶ H) (γ : F ⟶ H) (h : γ = α ≫ β) :
    ObjectProperty.liftNatTrans P hF hH γ =
      ObjectProperty.liftNatTrans P hF hG α ≫ ObjectProperty.liftNatTrans P hG hH β := by
  subst h
  rfl

end CategoryTheory

namespace AlgebraicGeometry.PolarizedOverSpace

attribute [local implicit_reducible] Stack.fibredCategory BasedCategory.ofFunctor schemeSpace
  Functor.toPseudofunctor' pseudofunctorOfIsLocallyDiscrete typeToGrpd Grpd.forgetToCat
  MorphismProperty

-- `AlgebraicGeometry.Space.isFlat_isStableUnderBaseChange` (Stacks 03MO) is a theorem rather than
-- an instance on the base.
attribute [local instance] Space.isFlat_isStableUnderBaseChange

variable {B : BigFppfSite.{u}} {T : AlgebraicSpaces B integerBase (hZ B)}

/-- The inverse images of modules along the projections of base changes. -/
abbrev fibreInverseImage :
    Comma (arrowSpace B) (forget (Space.modulesPseudofunctor B integerBase (hZ B))) ⥤
      Pseudofunctor.CoGrothendieck (arrowModules B) :=
  inverseImage (Space.modulesPseudofunctor B integerBase (hZ B)) (arrowSpace B)

section Objects

variable (ξ : PolarizedSpacesOver B T) (a : (Points T).obj)

/-- The base change at a point of a polarized family, with the inverse image of the
polarization. -/
abbrev fibreFamily : Pseudofunctor.CoGrothendieck (arrowModules B) :=
  fibreInverseImage.obj ((fibreComma ξ).obj a)

/-- The base change of a finitely presented, flat and proper morphism of algebraic spaces along a
point is finitely presented, flat and proper. -/
theorem properFlat_fibreProj :
    SpacesOverSpace.properFlatProperty B integerBase (hZ B) (schemeSpaceMap (fibreProj ξ a)) :=
  (SpacesOverSpace.properFlatProperty B integerBase (hZ B)).of_isPullback
    (Space.isPullback_homMk B integerBase (hZ B) _ _ _ _ (isPullback_fibre ξ a))
    ξ.of.obj.base.property

/-- The structure morphism of the base change is proper. -/
theorem isProper_fibreProj : IsProper (sch B (fibreProj ξ a)) :=
  Space.isProper_toScheme_map_of_isProper_yoneda_map B integerBase (hZ B) (fibreProj ξ a)
    (properFlat_fibreProj ξ a).2.2

/-- The structure morphism of the base change is flat. -/
theorem flat_fibreProj : Flat (sch B (fibreProj ξ a)) :=
  Space.flat_of_isFlat_yoneda B integerBase (hZ B) _ _ (fibreProj ξ a)
    (properFlat_fibreProj ξ a).2.1

/-- The structure morphism of the base change is of finite presentation. -/
theorem finitePresentation_fibreProj : FinitePresentation (sch B (fibreProj ξ a)) :=
  Space.finitePresentation_of_isFinitePresentation_yoneda_map B integerBase (hZ B)
    (fibreProj ξ a) (properFlat_fibreProj ξ a).1

/-- The inverse image of the polarization is quasi-coherent, the polarization being invertible. -/
theorem isQuasicoherentOnSite_fibreFamily :
    SheafOfModules.IsQuasicoherentOnSite (fibreFamily ξ a).fiber :=
  Space.isQuasicoherentOnSite_modulePullback_of_isInvertible (fibreSpaceMap ξ a) _
    ξ.of.property.1

/-- The restriction to the Zariski site of the inverse image of the polarization is the module of
Stacks 0D31. -/
def zariskiFibreFamilyIso :
    Space.baseChangeModule B integerBase (hZ B) ((familyPair B T).obj ξ).fiber (fibreScheme ξ a)
        (fibreFst ξ a) ≅ zariskiPolarization B (fibreFamily ξ a) :=
  Space.restrictToChartSchemeIdEtaleChartIso B integerBase (hZ B) (fibreScheme ξ a) _

/-- The base change of the polarization along the first projection is invertible and relatively
ample for the structure morphism of the base change. -/
theorem baseChange_isRelativelyAmple :
    ∃ hL : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B integerBase (hZ B)).obj
        (fibreScheme ξ a))
        (Space.baseChangeModule B integerBase (hZ B) ((familyPair B T).obj ξ).fiber
          (fibreScheme ξ a) (fibreFst ξ a)),
      @Stacks.RelativeAmple.IsRelativelyAmple _ _ (sch B (fibreProj ξ a))
        (Space.baseChangeModule B integerBase (hZ B) ((familyPair B T).obj ξ).fiber
          (fibreScheme ξ a) (fibreFst ξ a)) hL :=
  ξ.of.property.2.isRelativelyAmple_baseChange a.base (fibreScheme ξ a)
    (SpacesOverSpace.pointMap a).hom (fibreFst ξ a) (fibreProj ξ a) (isPullback_fibre ξ a)

/-- The restriction to the Zariski site of the inverse image of the polarization is invertible. -/
theorem isInvertible_fibreFamily :
    SheafOfModules.IsInvertible
      ((BigFppfOver.toScheme B integerBase (hZ B)).obj (fibreFamily ξ a).base.left).presheaf
      ((BigFppfOver.toScheme B integerBase (hZ B)).obj (fibreFamily ξ a).base.left).ringCatSheaf.2
      (zariskiPolarization B (fibreFamily ξ a)) :=
  Stacks.Picard.isInvertible_of_iso (zariskiFibreFamilyIso ξ a)
    (baseChange_isRelativelyAmple ξ a).choose

/-- **The base change at a point is a polarized family.** -/
theorem isRepresentedPolarized_fibreFamily : IsRepresentedPolarized B (fibreFamily ξ a) where
  proper := isProper_fibreProj ξ a
  flat := flat_fibreProj ξ a
  finitePresentation := finitePresentation_fibreProj ξ a
  quasicoherent := isQuasicoherentOnSite_fibreFamily ξ a
  invertible := isInvertible_fibreFamily ξ a
  relativelyAmple := by
    obtain ⟨hL, hamp⟩ := baseChange_isRelativelyAmple ξ a
    have := hL
    let this := isInvertible_fibreFamily ξ a
    exact (@Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ _ _ hL
      (isInvertible_fibreFamily ξ a) (zariskiFibreFamilyIso ξ a)).mp hamp

end Objects

section Morphisms

/-- **A morphism of points gives a cartesian square of base changes**, on schemes. -/
theorem isPullback_sch_fibreMap (ξ : PolarizedSpacesOver B T) {a' a : (Points T).obj}
    (u : a' ⟶ a) :
    IsPullback (sch B (fibreMap ξ u)) (sch B (fibreProj ξ a')) (sch B (fibreProj ξ a))
      (sch B u.base) := by
  have big : IsPullback (yoneda.map (fibreMap ξ u) ≫ fibreFst ξ a) (yoneda.map (fibreProj ξ a'))
      (familyMap ξ).hom (yoneda.map u.base ≫ (SpacesOverSpace.pointMap a).hom) := by
    rw [fibreMap_fst, SpacesOverSpace.yoneda_map_comp_pointMap_hom u]
    exact isPullback_fibre ξ a'
  have sq : IsPullback (yoneda.map (fibreMap ξ u)) (yoneda.map (fibreProj ξ a'))
      (yoneda.map (fibreProj ξ a)) (yoneda.map u.base) :=
    IsPullback.of_right big (by rw [← Functor.map_comp, ← Functor.map_comp, fibreMap_proj])
      (isPullback_fibre ξ a)
  have := Space.preservesLimitsOfShape_walkingCospan_toScheme B integerBase (hZ B)
  exact (IsPullback.of_map_of_faithful (F := yoneda) sq).map _

/-- The comparison of modules along the base change of a morphism of points is an isomorphism. -/
theorem isIso_fibreFamily_map_fiber (ξ : PolarizedSpacesOver B T) {a' a : (Points T).obj}
    (u : a' ⟶ a) : IsIso (fibreInverseImage.map ((fibreComma ξ).map u)).fiber :=
  isIso_inverseImage_map_fiber (arrowSpace B) ((fibreComma ξ).map u)
    (inferInstance : IsIso (𝟙 ((familyPair B T).obj ξ)))

/-- **The base changes along a morphism of points form a morphism of polarized families.** -/
theorem cartesianIso_fibreFamily_map (ξ : PolarizedSpacesOver B T) {a' a : (Points T).obj}
    (u : a' ⟶ a) :
    cartesianIso B (X := ⟨fibreFamily ξ a', isRepresentedPolarized_fibreFamily ξ a'⟩)
      (Y := ⟨fibreFamily ξ a, isRepresentedPolarized_fibreFamily ξ a⟩)
      (ObjectProperty.homMk (fibreInverseImage.map ((fibreComma ξ).map u))) :=
  ⟨isPullback_sch_fibreMap ξ u, isIso_fibreFamily_map_fiber ξ u⟩

/-- The morphism of base changes along an isomorphism of polarized families is an isomorphism. -/
instance isIso_fibreHomMap {ξ ξ' : PolarizedSpacesOver B T} (e : ξ ⟶ ξ') (a : (Points T).obj) :
    IsIso (fibreHomMap e a) :=
  ⟨⟨fibreHomMap (inv e) a, by rw [← fibreHomMap_comp, IsIso.hom_inv_id, fibreHomMap_id],
    by rw [← fibreHomMap_comp, IsIso.inv_hom_id, fibreHomMap_id]⟩⟩

/-- The morphism of base changes induced by an isomorphism of polarized families gives a cartesian
square of schemes over the identity of the point. -/
theorem isPullback_sch_fibreHomMap {ξ ξ' : PolarizedSpacesOver B T} (e : ξ ⟶ ξ')
    (a : (Points T).obj) :
    IsPullback (sch B (fibreHomMap e a)) (sch B (fibreProj ξ a)) (sch B (fibreProj ξ' a))
      (sch B (𝟙 a.base)) :=
  IsPullback.of_horiz_isIso ⟨by rw [← Functor.map_comp, ← Functor.map_comp, fibreHomMap_proj,
    Category.comp_id]⟩

/-- The comparison of modules along the morphism of base changes induced by an isomorphism of
polarized families is an isomorphism. -/
theorem isIso_fibreFamily_hom_fiber {ξ ξ' : PolarizedSpacesOver B T} (e : ξ ⟶ ξ')
    (a : (Points T).obj) :
    IsIso (fibreInverseImage.map ((fibreCommaNatTrans e).app a)).fiber :=
  isIso_inverseImage_map_fiber (arrowSpace B) ((fibreCommaNatTrans e).app a)
    (inferInstance : IsIso ((familyPair B T).map e))

/-- **An isomorphism of polarized families gives morphisms of polarized families at every
point.** -/
theorem cartesianIso_fibreFamily_hom {ξ ξ' : PolarizedSpacesOver B T} (e : ξ ⟶ ξ')
    (a : (Points T).obj) :
    cartesianIso B (X := ⟨fibreFamily ξ a, isRepresentedPolarized_fibreFamily ξ a⟩)
      (Y := ⟨fibreFamily ξ' a, isRepresentedPolarized_fibreFamily ξ' a⟩)
      (ObjectProperty.homMk (fibreInverseImage.map ((fibreCommaNatTrans e).app a))) :=
  ⟨isPullback_sch_fibreHomMap e a, isIso_fibreFamily_hom_fiber e a⟩

end Morphisms

section Functor

/-- The base changes of a polarized family at the points of `T`, as polarized families. -/
def baseChangeRepresentedFunctor' (ξ : PolarizedSpacesOver B T) :
    (Points T).obj ⥤ RepresentedPolarized B :=
  WideSubcategory.lift (cartesianIso B)
    (ObjectProperty.lift (IsRepresentedPolarized B) (fibreComma ξ ⋙ fibreInverseImage)
      (isRepresentedPolarized_fibreFamily ξ))
    (fun u => cartesianIso_fibreFamily_map ξ u)

/-- **The base changes of a polarized family at the points of `T`**, a functor over the site. -/
def baseChangeRepresented (ξ : PolarizedSpacesOver B T) :
    Points T ⥤ᵇ BasedCategory.ofFunctor (representedPolarizedProjection B) where
  toFunctor := baseChangeRepresentedFunctor' ξ
  w := rfl

variable (B T) in
/-- The base changes with the inverse images of the polarizations, before lifting to
`RepresentedPolarized`. -/
abbrev fibreFamilyFunctor : PolarizedSpacesOver B T ⥤
    ((Points T).obj ⥤ Pseudofunctor.CoGrothendieck (arrowModules B)) :=
  fibreCommaFunctor B T ⋙ (Functor.whiskeringRight _ _ _).obj fibreInverseImage

/-- The morphism of base-change functors induced by an isomorphism of polarized families. -/
def baseChangeRepresentedHom {ξ ξ' : PolarizedSpacesOver B T} (e : ξ ⟶ ξ') :
    baseChangeRepresented ξ ⟶ baseChangeRepresented ξ' where
  toNatTrans := WideSubcategory.liftNatTrans (cartesianIso B)
    (fun u => cartesianIso_fibreFamily_map ξ u) (fun u => cartesianIso_fibreFamily_map ξ' u)
    (ObjectProperty.liftNatTrans (IsRepresentedPolarized B) (isRepresentedPolarized_fibreFamily ξ)
      (isRepresentedPolarized_fibreFamily ξ') ((fibreFamilyFunctor B T).map e))
    (fun a => cartesianIso_fibreFamily_hom e a)
  isHomLift' a := Functor.IsHomLift.map (p := representedPolarizedProjection B)
    (⟨ObjectProperty.homMk (fibreInverseImage.map ((fibreCommaNatTrans e).app a)),
      cartesianIso_fibreFamily_hom e a⟩ :
        (baseChangeRepresented ξ).obj a ⟶ (baseChangeRepresented ξ').obj a)

variable (B T) in
/-- **The functor `F^R` of Stacks 0E94 into `RepresentedPolarized`**: a polarized family
`(X ⟶ T, L)` of algebraic spaces goes to the functor over the site sending a point `(U, t)` of `T`
to the base change `U ×_T X ⟶ U` with the inverse image of `L`. -/
def baseChangeRepresentedFunctor : PolarizedSpacesOver B T ⥤
    (Points T ⥤ᵇ BasedCategory.ofFunctor (representedPolarizedProjection B)) where
  obj := baseChangeRepresented
  map := baseChangeRepresentedHom
  map_id ξ := BasedNatTrans.ext _ _ (WideSubcategory.liftNatTrans_id (cartesianIso B)
    (fun u => cartesianIso_fibreFamily_map ξ u) _ (fun a => cartesianIso_fibreFamily_hom (𝟙 ξ) a)
    (ObjectProperty.liftNatTrans_id (IsRepresentedPolarized B)
      (isRepresentedPolarized_fibreFamily ξ) _ ((fibreFamilyFunctor B T).map_id ξ)))
  map_comp {ξ ξ' ξ''} e e' := BasedNatTrans.ext _ _ (WideSubcategory.liftNatTrans_comp
    (cartesianIso B) (fun u => cartesianIso_fibreFamily_map ξ u)
    (fun u => cartesianIso_fibreFamily_map ξ' u) (fun u => cartesianIso_fibreFamily_map ξ'' u) _
    (fun a => cartesianIso_fibreFamily_hom e a) _ (fun a => cartesianIso_fibreFamily_hom e' a) _
    (fun a => cartesianIso_fibreFamily_hom (e ≫ e') a)
    (ObjectProperty.liftNatTrans_comp (IsRepresentedPolarized B)
      (isRepresentedPolarized_fibreFamily ξ) (isRepresentedPolarized_fibreFamily ξ')
      (isRepresentedPolarized_fibreFamily ξ'') _ _ _ ((fibreFamilyFunctor B T).map_comp e e')))

end Functor

end AlgebraicGeometry.PolarizedOverSpace

end
