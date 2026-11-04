module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedOverSpace.BaseChangeFamilies
public import StacksFrontier.AlgebraicGeometry.Quot.SpacesOverSpaceEquivalence

/-!
# Forgetting the polarization of a family in `RepresentedPolarized`

An object `(s : Z ⟶ V, M)` of `AlgebraicGeometry.PolarizedOverSpace.RepresentedPolarized` has an
underlying family of algebraic spaces `yoneda Z ⟶ yoneda V`, finitely presented, flat and proper
because `s` is, and a morphism of `RepresentedPolarized` (a cartesian square of schemes) is a
cartesian square of algebraic spaces, i.e. a morphism of the stack `Spaces'_{fp, flat, proper}`
of Stacks 0E93. This is the functor through which the families of Stacks 0E94 are compared with
those of Stacks 0E93.

## Main definitions

* `AlgebraicGeometry.PolarizedOverSpace.forgetModules`: the functor
  `RepresentedPolarized ⥤ Spaces'_{fp, flat, proper}`, over the site.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.PolarizedOverSpace

variable (B : BigFppfSite.{u})

/-- The family of algebraic spaces represented by a finitely presented, flat and proper morphism
of schemes of the site is finitely presented, flat and proper. -/
theorem properFlatProperty_schemeSpaceMap {Z V : Site B} (s : Z ⟶ V) (hp : IsProper (sch B s))
    (hf : Flat (sch B s)) (hfp : FinitePresentation (sch B s)) :
    SpacesOverSpace.properFlatProperty B integerBase (hZ B) (schemeSpaceMap s) := by
  show Space.IsFinitePresentation B integerBase (hZ B) (yoneda.map s) ∧
    Space.IsFlat B integerBase (hZ B) (yoneda.map s) ∧
      Space.IsProper B integerBase (hZ B) (yoneda.map s)
  have hqc : Space.IsQuasiCompact B integerBase (hZ B) (yoneda.map s) :=
    Space.isQuasiCompact_yoneda_map B integerBase (hZ B) _ hfp.quasiCompact
  refine ⟨⟨?_, hqc, ?_⟩, ?_, ?_, ⟨?_, hqc⟩, ?_⟩
  · exact Space.holdsOnEveryEtaleChart_yoneda_map B integerBase (hZ B)
      LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget _
      hfp.locallyOfFinitePresentation
  · rw [Space.isQuasiSeparated_iff_diagonalProp_quasiCompact B integerBase (hZ B)
      (relativelyRepresentable_pullback_diagonal B integerBase (hZ B) _
        (Functor.relativelyRepresentable.map yoneda _)),
      Space.diagonalProp_quasiCompact_yoneda_map_iff]
    exact hfp.quasiSeparated
  · exact Space.holdsOnEveryEtaleChart_yoneda_map B integerBase (hZ B)
      Flat.isEtaleLocalOnSourceAndTarget _ hf
  · rw [Space.isSeparated_yoneda_map_iff]
    exact (inferInstance : IsSeparated (sch B s))
  · exact Space.holdsOnEveryEtaleChart_yoneda_map B integerBase (hZ B)
      LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget _
      (inferInstance : LocallyOfFiniteType (sch B s))
  · exact Space.universallyClosed_yoneda_map B integerBase (hZ B) _
      (inferInstance : _root_.AlgebraicGeometry.UniversallyClosed (sch B s))

/-- The family of algebraic spaces underlying an object of `RepresentedPolarized`. -/
def forgetModulesObj (R : RepresentedPolarized B) :
    SpacesOverSpace.CartesianFamilies B integerBase (hZ B)
      (SpacesOverSpace.properFlatProperty B integerBase (hZ B)) :=
  ⟨⟨⟨schemeSpace R.obj.obj.base.left, R.obj.obj.base.right, yoneda.map R.obj.obj.base.hom⟩,
    properFlatProperty_schemeSpaceMap B R.obj.obj.base.hom R.obj.property.proper
      R.obj.property.flat R.obj.property.finitePresentation⟩⟩

/-- The morphism of families of algebraic spaces underlying a morphism of
`RepresentedPolarized`. -/
def forgetModulesComma {R R' : RepresentedPolarized B} (f : R ⟶ R') :
    (forgetModulesObj B R).obj.obj ⟶ (forgetModulesObj B R').obj.obj where
  left := schemeSpaceMap f.hom.hom.base.left
  right := f.hom.hom.base.right
  w := by
    change yoneda.map f.hom.hom.base.left ≫ yoneda.map R'.obj.obj.base.hom =
      yoneda.map R.obj.obj.base.hom ≫ yoneda.map f.hom.hom.base.right
    rw [← Functor.map_comp, ← Functor.map_comp, Arrow.w]

/-- The square of a morphism of `RepresentedPolarized` is cartesian in the site. -/
theorem isPullback_site {R R' : RepresentedPolarized B} (f : R ⟶ R') :
    IsPullback f.hom.hom.base.left R.obj.obj.base.hom R'.obj.obj.base.hom f.hom.hom.base.right :=
  IsPullback.of_map_of_faithful (BigFppfOver.toScheme B integerBase (hZ B)) f.property.1

/-- The morphism of families underlying a morphism of `RepresentedPolarized` is strongly
cartesian (Stacks 04U9). -/
theorem isStronglyCartesian_forgetModulesComma {R R' : RepresentedPolarized B} (f : R ⟶ R') :
    (spacesProjection B integerBase (hZ B)).IsStronglyCartesian (forgetModulesComma B f).right
      (forgetModulesComma B f) :=
  SpacesDescent.isStronglyCartesian_of_isPullback _ _ rfl rfl
    (by simp only [eqToHom_refl, Category.id_comp, Category.comp_id])
    (by simp only [eqToHom_refl, CategoryTheory.Functor.map_id]; exact Category.comp_id _)
    (by simp only [eqToHom_refl, CategoryTheory.Functor.map_id]; exact Category.comp_id _)
    ((isPullback_site B f).map yoneda)

/-- **Forgetting the polarization**, `RepresentedPolarized ⥤ Spaces'_{fp, flat, proper}`. -/
def forgetModules : RepresentedPolarized B ⥤ SpacesOverSpace.CartesianFamilies B integerBase (hZ B)
    (SpacesOverSpace.properFlatProperty B integerBase (hZ B)) where
  obj := forgetModulesObj B
  map f :=
    ⟨ObjectProperty.homMk (forgetModulesComma B f), isStronglyCartesian_forgetModulesComma B f⟩
  map_id _ := WideSubcategory.hom_ext _ (ObjectProperty.hom_ext _
    (Comma.hom_ext _ _ (ObjectProperty.hom_ext _ (yoneda.map_id _)) rfl))
  map_comp _ _ := WideSubcategory.hom_ext _ (ObjectProperty.hom_ext _
    (Comma.hom_ext _ _ (ObjectProperty.hom_ext _ (yoneda.map_comp _ _)) rfl))

/-- Forgetting the polarization, as a functor over the site. -/
def forgetModulesBased : BasedCategory.ofFunctor (representedPolarizedProjection B) ⥤ᵇ
    BasedCategory.ofFunctor (SpacesOverSpace.cartesianProjection B integerBase (hZ B)
      (SpacesOverSpace.properFlatProperty B integerBase (hZ B))) where
  toFunctor := forgetModules B
  w := rfl

end AlgebraicGeometry.PolarizedOverSpace

end
