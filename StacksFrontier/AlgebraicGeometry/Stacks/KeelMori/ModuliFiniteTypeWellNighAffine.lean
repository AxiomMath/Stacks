module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalLocallyOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMori.FiniteTypeIntegralQuotient
public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMori.ModuliSpaceBasics
public import StacksFrontier.AlgebraicGeometry.Stacks.MorphismSpaceIsoClass
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryConverse
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffineModuliTopology
public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffineUniformModuliSpace

/-!
# The moduli space of a well-nigh affine stack is locally of finite type over the base

This file proves the well-nigh affine case of Stacks 0DUX. Let `𝒳` be a well-nigh affine algebraic
stack, `p : 𝒳 ⟶ Y` a 1-morphism to a locally Noetherian algebraic space which is locally of finite
type, and `f : 𝒳 ⟶ M` any categorical moduli space. The morphism `q : M ⟶ Y` through which `p`
factors is locally of finite type.

As in the source: `𝒳 = [U/R]` with `U = Spec A` affine and `M = Spec C`, `C ⊂ A` the ring of
`R`-invariant functions (Stacks 0DUM, 0DUP, and 0DUR for the comparison with an arbitrary
categorical moduli space). The chart `U ⟶ 𝒳` is of finite presentation, so `U ⟶ Y` is locally
of finite type; `A` is integral over `C` (Stacks 03BJ) and `C ⟶ A` is injective, so
`AlgebraicGeometry.Space.isLocallyOfFiniteType_of_isIntegralHom_of_injective_appTop` (Artin–Tate,
Stacks 00IS) concludes.

## Main results

* `AlgebraicGeometry.GroupoidScheme.injective_appTop_objectsToInvariantSpectrum`: `C ⟶ A` is
  injective.
* `AlgebraicGeometry.Stack.WellNighAffineChart.isLocallyOfFiniteType_chart`: the chart of a
  well-nigh affine stack is locally of finite type.
* `AlgebraicGeometry.Stack.isLocallyOfFiniteType_of_isWellNighAffine_of_isCategoricalModuliSpace`:
  the well-nigh affine case of Stacks 0DUX.

## References

* [Stacks Project, Tag 0DUX](https://stacks.math.columbia.edu/tag/0DUX)
* [Stacks Project, Tag 03BJ](https://stacks.math.columbia.edu/tag/03BJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.GroupoidScheme

/-- **The ring of invariants injects into the global functions on the object scheme**: on global
sections, `U ⟶ Spec C` is the inclusion `C ⊆ Γ(U)`. -/
theorem injective_appTop_objectsToInvariantSpectrum {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) :
    Function.Injective (objectsToInvariantSpectrum G).appTop.hom := by
  have h : (objectsToInvariantSpectrum G).appTop =
      (Scheme.ΓSpecIso (.of (invariantRing G))).hom ≫
        CommRingCat.ofHom (invariantRing G).subtype := by
    rw [objectsToInvariantSpectrum, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop,
      Scheme.ΓSpecIso_naturality]
  rw [h, CommRingCat.hom_comp]
  exact Subtype.val_injective.comp (ConcreteCategory.bijective_of_isIso _).injective

end AlgebraicGeometry.GroupoidScheme

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The morphism of representing presheaves of `h_U ⟶ G`, read through the comparison of the
slice over `U` with the category of elements of `h_U`, is the morphism itself.** -/
theorem representingMap_sliceElementsComparison_associatedMap (U : BigFppfOver B S hS)
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (φ : yoneda.obj U ⟶ G) :
    representingMap B S hS (schemeFibredCategory B S hS U) (fibredCategory B S hS G)
        (yoneda.obj U) G (PresheafOfCategories.sliceElementsEquivalenceOver U)
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (Bicategory.InducedBicategory.mkHom
          (BasedFunctor.comp (sliceElementsComparison B S hS U) (associatedMap B S hS φ).1.hom)) =
      φ :=
  morphismSpaceEquiv_eq_of_comp_eq B S hS _ _ _ G _ _ _ φ rfl

/-- **A 1-morphism from the stack of `U` to the stack of an algebraic space `Y` which is locally
of finite type induces a morphism `h_U ⟶ Y` locally of finite type.** Stated for a 1-morphism
2-isomorphic to the one attached to `φ : h_U ⟶ Y`. -/
theorem isLocallyOfFiniteType_of_schemeStack_hom (U : BigFppfOver B S hS)
    (Y : AlgebraicSpaces B S hS)
    (g : schemeStack.{u, w} B S hS U ⟶ algebraicSpaceStack.{u, w} B S hS Y.obj Y.property)
    (hg : AlgebraicStacks.IsLocallyOfFiniteType B S hS g) (φ : yoneda.obj U ⟶ Y.obj)
    (η : g.hom ≅ Bicategory.InducedBicategory.mkHom
      (BasedFunctor.comp (sliceElementsComparison B S hS U) (associatedMap B S hS φ).1.hom)) :
    Space.IsLocallyOfFiniteType B S hS φ := by
  have hsome := (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
    (fun _ _ h => Space.IsLocallyOfFiniteType B S hS h)
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
    (schemeStack.{u, w} B S hS U).property
    (algebraicSpaceStack.{u, w} B S hS Y.obj Y.property).property g.hom).1 hg
  have hrep := (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS
    (fun _ _ h => Space.IsLocallyOfFiniteType B S hS h)
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
    (schemeStack.{u, w} B S hS U).property
    (algebraicSpaceStack.{u, w} B S hS Y.obj Y.property).property
    (yoneda.obj U) Y.obj (isAlgebraicSpace_yoneda B S hS U) Y.property
    (PresheafOfCategories.sliceElementsEquivalenceOver U)
    (StacksRepresentableCFG.EquivalenceOver.refl _) g.hom).1 hsome
  have h1 : representingMap B S hS (schemeStack.{u, w} B S hS U).val
      (algebraicSpaceStack.{u, w} B S hS Y.obj Y.property).val (yoneda.obj U) Y.obj
      (PresheafOfCategories.sliceElementsEquivalenceOver U)
      (StacksRepresentableCFG.EquivalenceOver.refl _) g.hom = φ := by
    have h2 := representingMap_congr_twoIso B S hS (yoneda.obj U) Y.obj
      (PresheafOfCategories.sliceElementsEquivalenceOver U)
      (StacksRepresentableCFG.EquivalenceOver.refl _) η
    rwa [representingMap_sliceElementsComparison_associatedMap] at h2
  rwa [h1] at hrep

/-- **Precomposing with an isomorphism preserves local finite type.** -/
theorem _root_.AlgebraicGeometry.Space.isLocallyOfFiniteType_iso_hom_comp
    {X X' Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX' : IsAlgebraicSpace B S hS X')
    (hX : IsAlgebraicSpace B S hS X) (hZ : IsAlgebraicSpace B S hS Z) (e : X' ≅ X) (g : X ⟶ Z)
    (hg : Space.IsLocallyOfFiniteType B S hS g) :
    Space.IsLocallyOfFiniteType B S hS (e.hom ≫ g) :=
  Space.isLocallyOfFiniteType_comp B S hS hX' hX hZ e.hom g
    (Space.isLocallyOfFiniteType_of_isEtale B S hS hX (Space.isEtale_of_isIso B S hS e.hom)) hg

namespace WellNighAffineChart

variable {B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS} (K : WellNighAffineChart.{u, w} B S hS 𝒳)

/-- **The chart of a well-nigh affine stack is locally of finite type**: it is of finite
presentation in the sense of Stacks 03YK, so passes the smooth-diagram test (Stacks 06FM). -/
theorem isLocallyOfFiniteType_chart : AlgebraicStacks.IsLocallyOfFiniteType B S hS K.chart := by
  obtain ⟨hrep, hfp⟩ := K.isRelativelyFinitePresentation_chart
  apply (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS _
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
    (schemeStack.{u, w} B S hS K.U).property 𝒳.property K.chart.hom).2
  apply (hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u} B S hS _
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
    (schemeStack.{u, w} B S hS K.U).property 𝒳.property K.chart.hom hrep).2
  exact fun V y hy G hG he =>
    Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS (hfp V y hy G hG he).1

/-- `U ⟶ M` is injective on global sections. -/
theorem injective_appTop_toScheme_map_quotientMap :
    Function.Injective ((BigFppfOver.toScheme B S hS).map K.quotientMap).appTop.hom := by
  rw [toScheme_map_quotientMap]
  exact GroupoidScheme.injective_appTop_objectsToInvariantSpectrum K.groupoidScheme

/-- **The well-nigh affine case of Stacks 0DUX at the moduli map of a chart.** -/
theorem isLocallyOfFiniteType_of_comp_moduliMap {Y : AlgebraicSpaces B S hS}
    (hY : Space.HasEtaleLocalProperty B S hS Y.obj (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (p : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y.obj Y.property)
    (hp : AlgebraicStacks.IsLocallyOfFiniteType B S hS p) (q : K.moduliSpace ⟶ Y)
    (hq : Nonempty (K.moduliMap.hom ≫ (associatedMap B S hS q.hom).1 ≅ p.hom)) :
    Space.IsLocallyOfFiniteType B S hS q.hom := by
  obtain ⟨ε⟩ := hq
  let : IsAffine ((BigFppfOver.toScheme B S hS).obj K.U) := K.isAffine_U
  have hcp := AlgebraicStacks.isLocallyOfFiniteType_comp B S hS K.chart p
    K.isLocallyOfFiniteType_chart hp
  have hcomp : K.chart.hom ≫ K.moduliMap.hom =
      Bicategory.InducedBicategory.mkHom
        (BasedFunctor.comp (sliceElementsComparison B S hS K.U)
          (associatedMap B S hS (yoneda.map K.quotientMap)).1.hom) :=
    Bicategory.InducedBicategory.hom_ext K.chart_comp_moduliMap
  have hassoc : Bicategory.InducedBicategory.mkHom
        (BasedFunctor.comp (sliceElementsComparison B S hS K.U)
          (associatedMap B S hS (yoneda.map K.quotientMap)).1.hom) ≫
          (associatedMap B S hS q.hom).1 =
      Bicategory.InducedBicategory.mkHom
        (BasedFunctor.comp (sliceElementsComparison B S hS K.U)
          (associatedMap B S hS (yoneda.map K.quotientMap ≫ q.hom)).1.hom) := by
    rw [associatedMap_comp]
    rfl
  let η : (K.chart ≫ p).hom ≅ Bicategory.InducedBicategory.mkHom
      (BasedFunctor.comp (sliceElementsComparison B S hS K.U)
        (associatedMap B S hS (yoneda.map K.quotientMap ≫ q.hom)).1.hom) :=
    Bicategory.whiskerLeftIso K.chart.hom ε.symm ≪≫ (Bicategory.associator _ _ _).symm ≪≫
      eqToIso (by rw [hcomp, hassoc])
  exact Space.isLocallyOfFiniteType_of_isIntegralHom_of_injective_appTop B S hS K.U
    K.moduliObject K.quotientMap K.injective_appTop_toScheme_map_quotientMap Y.property hY q.hom
    (isLocallyOfFiniteType_of_schemeStack_hom B S hS K.U Y (K.chart ≫ p) hcp _ η)

end WellNighAffineChart

/-- **Stacks 0DUX, the well-nigh affine case.** Let `𝒳` be a well-nigh affine algebraic stack,
`p : 𝒳 ⟶ Y` a 1-morphism locally of finite type to a locally Noetherian algebraic space, and
`f : 𝒳 ⟶ M` a categorical moduli space. A morphism `q : M ⟶ Y` with `f ≫ q ≅ p` is locally of
finite type. -/
theorem isLocallyOfFiniteType_of_isWellNighAffine_of_isCategoricalModuliSpace
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (h𝒳 : IsWellNighAffine.{u, w} B S hS 𝒳)
    {Y : AlgebraicSpaces B S hS}
    (hY : Space.HasEtaleLocalProperty B S hS Y.obj (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (p : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y.obj Y.property)
    (hp : AlgebraicStacks.IsLocallyOfFiniteType B S hS p) {M : AlgebraicSpaces B S hS}
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS M.obj M.property)
    (hf : IsCategoricalModuliSpace B S hS M f.hom) (q : M ⟶ Y)
    (hq : Nonempty (f.hom ≫ (associatedMap B S hS q.hom).1 ≅ p.hom)) :
    Space.IsLocallyOfFiniteType B S hS q.hom := by
  obtain ⟨K⟩ := nonempty_wellNighAffineChart B S hS 𝒳 h𝒳
  have hK : IsCategoricalModuliSpace B S hS K.moduliSpace K.moduliMap.hom :=
    isCategoricalModuliSpace_of_isUniformCategoricalModuliSpace B S hS
      (isUniformCategoricalModuliSpace_of_isUniformCategoricalModuliSpaceIn B S hS 𝒳 h𝒳
        K.moduliSpace K.moduliMap.hom K.isUniformCategoricalModuliSpaceIn_moduliMap)
  obtain ⟨e, he⟩ := exists_iso_of_isCategoricalModuliSpace B S hS hK hf
  obtain ⟨ε⟩ := hq
  have hqK : Nonempty (K.moduliMap.hom ≫ (associatedMap B S hS (e.hom ≫ q).hom).1 ≅ p.hom) := by
    refine ⟨eqToIso ?_ ≪≫ ε⟩
    change K.moduliMap.hom ≫ (associatedMap B S hS (e.hom.hom ≫ q.hom)).1 = _
    rw [associatedMap_comp, ← Category.assoc, he]
  have h := K.isLocallyOfFiniteType_of_comp_moduliMap hY p hp (e.hom ≫ q) hqK
  have hq' : q.hom = e.inv.hom ≫ (e.hom ≫ q).hom :=
    congrArg (·.hom) (e.inv_hom_id_assoc q).symm
  rw [hq']
  exact Space.isLocallyOfFiniteType_iso_hom_comp B S hS M.property K.moduliSpace.property
    Y.property ((ObjectProperty.ι _).mapIso e.symm) _ h

end AlgebraicGeometry.Stack

end
