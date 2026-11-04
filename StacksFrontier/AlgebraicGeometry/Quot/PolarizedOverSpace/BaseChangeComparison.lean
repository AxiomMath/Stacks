module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedOverSpace.RepresentedPolarizedForget

/-!
# The families underlying `F^R` are the base changes of Stacks 0E93

For a polarized family `(X ⟶ T, L)` of algebraic spaces and a point `(U, t)` of `T`, the family
of algebraic spaces underlying the polarized family `F^R(X, L)(U, t)` is `yoneda Z ⟶ yoneda U`,
where the scheme `Z` represents the fibre product `U ×_T X`; the base-change functor of
Stacks 0E93 (`AlgebraicGeometry.SpacesOverSpace.baseChangeFunctor`) sends `X ⟶ T` to the presheaf
fibre product itself. The two are identified by the canonical isomorphism, naturally in the point.

## Main definitions

* `AlgebraicGeometry.PolarizedOverSpace.fibreComparisonIso`: the isomorphism at a point.
* `AlgebraicGeometry.PolarizedOverSpace.baseChangeComparison`: the isomorphism of functors over the
  site `F^R(X, L) ⋙ forget ≅ baseChange X`.

## Main results

* `AlgebraicGeometry.PolarizedOverSpace.fibreComparisonIso_naturality`: the isomorphisms
  `fibreComparisonIso` are natural in the point.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.PolarizedOverSpace

attribute [local implicit_reducible] Stack.fibredCategory BasedCategory.ofFunctor schemeSpace
  AlgebraicSpaces.fiberProduct Functor.toPseudofunctor' pseudofunctorOfIsLocallyDiscrete typeToGrpd
  Grpd.forgetToCat MorphismProperty

variable {B : BigFppfSite.{u}} {T : AlgebraicSpaces B integerBase (hZ B)}

/-- The base-change functor of Stacks 0E93 for finitely presented, flat and proper morphisms. -/
abbrev spacesBaseChange (X : ProperFlatOver B T) :
    Points T ⥤ᵇ BasedCategory.ofFunctor (SpacesOverSpace.cartesianProjection B integerBase (hZ B)
      (SpacesOverSpace.properFlatProperty B integerBase (hZ B))) :=
  SpacesOverSpace.baseChangeBased X

section Comparison

variable (ξ : PolarizedSpacesOver B T)

/-- The canonical isomorphism from the scheme representing the fibre product to the presheaf
fibre product. -/
abbrev fibreIsoPullback (a : (Points T).obj) :
    yoneda.obj (fibreScheme ξ a) ≅ pullback (SpacesOverSpace.pointMap a).hom (familyMap ξ).hom :=
  (isPullback_fibre ξ a).flip.isoPullback

/-- The isomorphism `fibreIsoPullback` followed by the first projection is the image under
Yoneda of the projection `fibreProj` to `U`. -/
theorem fibreIsoPullback_hom_fst (a : (Points T).obj) :
    (fibreIsoPullback ξ a).hom ≫ pullback.fst _ _ = yoneda.map (fibreProj ξ a) :=
  IsPullback.isoPullback_hom_fst _

/-- The isomorphism `fibreIsoPullback` followed by the second projection is the map
`fibreFst` to `X`. -/
theorem fibreIsoPullback_hom_snd (a : (Points T).obj) :
    (fibreIsoPullback ξ a).hom ≫ pullback.snd _ _ = fibreFst ξ a :=
  IsPullback.isoPullback_hom_snd _

/-- The comparison of the families at a point, as an isomorphism of comma objects. -/
def fibreComparisonComma (a : (Points T).obj) :
    ((forgetModules B).obj ((baseChangeRepresented ξ).obj a)).obj.obj ≅
      ((spacesBaseChange ξ.of.obj.base).obj a).obj.obj :=
  Comma.isoMk (ObjectProperty.isoMk _ (fibreIsoPullback ξ a)) (Iso.refl a.base) (by
    change (fibreIsoPullback ξ a).hom ≫ pullback.fst _ _ =
      yoneda.map (fibreProj ξ a) ≫ yoneda.map (𝟙 _)
    rw [CategoryTheory.Functor.map_id, Category.comp_id, fibreIsoPullback_hom_fst])

/-- An isomorphism of comma objects is strongly cartesian over its underlying morphism of bases. -/
private theorem isStronglyCartesian_of_isIso_comma
    {A C : Comma (ObjectProperty.ι (fun F : (BigFppfOver B integerBase (hZ B))ᵒᵖ ⥤ Type u =>
      IsAlgebraicSpace B integerBase (hZ B) F))
      (yoneda : BigFppfOver B integerBase (hZ B) ⥤ (BigFppfOver B integerBase (hZ B))ᵒᵖ ⥤ Type u)}
    (m : A ⟶ C) [IsIso m] :
    (spacesProjection B integerBase (hZ B)).IsStronglyCartesian m.right m :=
  SpacesDescent.isStronglyCartesian_of_isPullback _ _ rfl rfl
    (by simp only [eqToHom_refl, Category.id_comp, Category.comp_id])
    (by simp only [eqToHom_refl, CategoryTheory.Functor.map_id]; exact Category.comp_id _)
    (by simp only [eqToHom_refl, CategoryTheory.Functor.map_id]; exact Category.comp_id _)
    (IsPullback.of_horiz_isIso ⟨m.w⟩)

/-- The forward map of `fibreComparisonComma` is strongly cartesian over its underlying
morphism of bases. -/
theorem isStronglyCartesian_fibreComparisonComma_hom (a : (Points T).obj) :
    (spacesProjection B integerBase (hZ B)).IsStronglyCartesian
      (fibreComparisonComma ξ a).hom.right (fibreComparisonComma ξ a).hom :=
  isStronglyCartesian_of_isIso_comma _

/-- The inverse map of `fibreComparisonComma` is strongly cartesian over its underlying
morphism of bases. -/
theorem isStronglyCartesian_fibreComparisonComma_inv (a : (Points T).obj) :
    (spacesProjection B integerBase (hZ B)).IsStronglyCartesian
      (fibreComparisonComma ξ a).inv.right (fibreComparisonComma ξ a).inv :=
  isStronglyCartesian_of_isIso_comma _

/-- **The comparison of the families at a point.** -/
def fibreComparisonIso (a : (Points T).obj) :
    (forgetModules B).obj ((baseChangeRepresented ξ).obj a) ≅
      (spacesBaseChange ξ.of.obj.base).obj a :=
  WideSubcategory.isoMk (ObjectProperty.isoMk _ (fibreComparisonComma ξ a))
    (isStronglyCartesian_fibreComparisonComma_hom ξ a)
    (isStronglyCartesian_fibreComparisonComma_inv ξ a)

/-- The isomorphisms `fibreComparisonIso` are natural in the point: they commute with the maps
induced by a morphism of points `u : a' ⟶ a`. -/
theorem fibreComparisonIso_naturality {a' a : (Points T).obj} (u : a' ⟶ a) :
    (forgetModules B).map ((baseChangeRepresented ξ).map u) ≫ (fibreComparisonIso ξ a).hom =
      (fibreComparisonIso ξ a').hom ≫ (spacesBaseChange ξ.of.obj.base).map u :=
  WideSubcategory.hom_ext _ (ObjectProperty.hom_ext _ (Comma.hom_ext _ _
    (ObjectProperty.hom_ext _ (pullback.hom_ext
      (by
        show (yoneda.map (fibreMap ξ u) ≫ (fibreIsoPullback ξ a).hom) ≫ pullback.fst _ _ =
          ((fibreIsoPullback ξ a').hom ≫
            (SpacesOverSpace.baseChangeCommaMap ξ.of.obj.base.obj.of u).left.hom) ≫
            pullback.fst _ _
        refine (Category.assoc _ _ _).trans ?_
        refine (congrArg (yoneda.map (fibreMap ξ u) ≫ ·) (fibreIsoPullback_hom_fst ξ a)).trans ?_
        refine ((yoneda.map_comp _ _).symm.trans (congrArg yoneda.map (fibreMap_proj ξ u))).trans ?_
        refine (yoneda.map_comp _ _).trans ?_
        refine Eq.trans ?_ (Category.assoc _ _ _).symm
        refine Eq.trans ?_ (congrArg (_ ≫ ·)
          (SpacesOverSpace.baseChangeCommaMap_left_fst ξ.of.obj.base.obj.of u).symm)
        refine Eq.trans ?_ (Category.assoc _ _ _)
        exact congrArg (· ≫ _) (fibreIsoPullback_hom_fst ξ a').symm)
      (by
        show (yoneda.map (fibreMap ξ u) ≫ (fibreIsoPullback ξ a).hom) ≫ pullback.snd _ _ =
          ((fibreIsoPullback ξ a').hom ≫
            (SpacesOverSpace.baseChangeCommaMap ξ.of.obj.base.obj.of u).left.hom) ≫
            pullback.snd _ _
        refine (Category.assoc _ _ _).trans ?_
        refine (congrArg (yoneda.map (fibreMap ξ u) ≫ ·) (fibreIsoPullback_hom_snd ξ a)).trans ?_
        refine (fibreMap_fst ξ u).trans ?_
        refine Eq.trans ?_ (Category.assoc _ _ _).symm
        refine Eq.trans ?_ (congrArg (_ ≫ ·)
          (SpacesOverSpace.baseChangeCommaMap_left_snd ξ.of.obj.base.obj.of u).symm)
        exact (fibreIsoPullback_hom_snd ξ a').symm)))
    ((Category.comp_id _).trans (Category.id_comp _).symm)))

/-- **The families underlying `F^R(X, L)` are the base changes of Stacks 0E93.** -/
def baseChangeComparison :
    BasedFunctor.comp (baseChangeRepresented ξ) (forgetModulesBased B) ≅
      spacesBaseChange ξ.of.obj.base :=
  BasedNatIso.mkNatIso (NatIso.ofComponents (fibreComparisonIso ξ)
      (fun u => fibreComparisonIso_naturality ξ u))
    (fun a => Functor.IsHomLift.map (p := SpacesOverSpace.cartesianProjection B integerBase (hZ B)
      (SpacesOverSpace.properFlatProperty B integerBase (hZ B))) (fibreComparisonIso ξ a).hom)

end Comparison

end AlgebraicGeometry.PolarizedOverSpace

end
