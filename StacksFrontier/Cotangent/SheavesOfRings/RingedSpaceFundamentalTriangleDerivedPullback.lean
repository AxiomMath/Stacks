module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.TopoiBridge.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalTypesSitePresentedPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackSectionsBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.InverseImageExactness
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.InverseImageComparison
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesComparison
public import StacksFrontier.Cotangent.SheavesOfRings.BaseChangedCotangentDerived
public import StacksFrontier.Cotangent.SheavesOfRings.BaseChangedCotangentTowerIso
public import StacksFrontier.Cotangent.SheavesOfRings.PullbackCotangentComplex
public import StacksFrontier.Cotangent.SheavesOfRings.RingedSpaceFundamentalTriangleDerived
public import StacksFrontier.Cotangent.SheavesOfRings.RingedSpaceTransitivityTriangle
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.MixedDerivedTensorOnARingedSpace
public import StacksFrontier.Topology.Sheaves.Functors.Pullback.Comp

/-!
# The first vertex of the ringed-space tower is the derived pullback `Lf^*L_{Y/Z}`

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of ringed spaces. The first vertex of the
fundamental triangle of the tower `(g ∘ f)⁻¹𝒪_Z ⟶ f⁻¹𝒪_Y ⟶ 𝒪_X`
(`Stacks.Sheaves.RingedSpaceCotangent.exists_distTriang_cotangentTower`) is the degreewise base
change `L_{f⁻¹𝒪_Y/(g ∘ f)⁻¹𝒪_Z} ⊗_{f⁻¹𝒪_Y} 𝒪_X`. This file identifies it with the derived
pullback `Lf^*L_{Y/Z}` of Tag 06YJ, and so proves that

`Lf^*L_{Y/Z} ⟶ L_{X/Z} ⟶ L_{X/Y} ⟶ (Lf^*L_{Y/Z})[1]`

is distinguished in `D(𝒪_X)`, its second arrow being the change-of-base-ring map
`Stacks.Sheaves.RingedSpaceCotangent.cotangentChangeOfBase`.

## Main definitions

* `Stacks.Sheaves.RingedSpaceCotangent.degreewisePullbackCotangentComplexIso`: the degreewise
  pullback `f^*L_{Y/Z}` is the first vertex of the triangle of the tower.
* `Stacks.Sheaves.RingedSpaceCotangent.derivedPullbackBaseChangedCotangentIso`: the derived
  pullback `Lf^*L_{Y/Z}` is the first vertex of the triangle of the tower.
* `Stacks.Sheaves.RingedSpaceCotangent.derivedPullbackCotangentBaseChange`: the first arrow
  `Lf^*L_{Y/Z} ⟶ L_{X/Z}`.

## Main results

* `Stacks.Sheaves.RingedSpaceCotangent.baseStructureMap_eq`: the middle homomorphism of the tower
  is `f⁻¹` of the structure map of `g`, across `(g ∘ f)⁻¹ ≅ f⁻¹ ∘ g⁻¹` (Tag 008I).
* `Stacks.Sheaves.RingedSpaceCotangent.derivedPullbackBaseChangedCotangentIso_inv_comp`: the
  first arrow is the derived pullback comparison followed by the degreewise arrow.
* `Stacks.Sheaves.RingedSpaceCotangent.exists_distTriang_derivedPullback_cotangentTower`: the
  triangle `Lf^*L_{Y/Z} ⟶ L_{X/Z} ⟶ L_{X/Y} ⟶ ⋯` is distinguished.

## Implementation notes

The identification goes through the morphism of ringed topoi presented by `f`
(`Stacks.ToposBridge.ringedToposHom`). `L_{Y/Z}` is a bounded above complex of flat modules, so
`Lf^*` is computed on it degreewise (Tag 06YJ); the degreewise pullback of sheaves of modules on
ringed spaces is the one along the presented morphism of ringed topoi, both being left adjoint to
the direct image; along a morphism of ringed topoi the pullback of a cotangent complex is the
first vertex of the tower of topos inverse images
(`CategoryTheory.Sheaf.pullbackModulesCotangentComplexIso`, through Tag 08SV); and that tower is
isomorphic to the tower `(g ∘ f)⁻¹𝒪_Z ⟶ f⁻¹𝒪_Y ⟶ 𝒪_X` of inverse images on spaces, the two inverse
images being left adjoint to the same direct image
(`CategoryTheory.Sheaf.baseChangedCotangentComplexIsoOfTower`).

The derived categories are the standard models `HasDerivedCategory.standard`, those Tag 06YJ is
stated for.

## References

* [Stacks Project, Tag 08T4](https://stacks.math.columbia.edu/tag/08T4)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 08SV](https://stacks.math.columbia.edu/tag/08SV)
* [Stacks Project, Tag 008I](https://stacks.math.columbia.edu/tag/008I)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace
open Stacks.Sheaves.RingedSpaceDifferentials (sheafAdjunction structureSheafMap inverseImageSheaf
  inverseImageStructureMap homEquiv_inverseImageStructureMap)
open Stacks.Cohomology.MixedDerivedTensorOnARingedSpace (ringedToposSiteHom isMorphismOfSites)
open Stacks.Sheaves.InverseImageExactness (invCommRingIso)

universe u

namespace Stacks.Sheaves.RingedSpaceCotangent

variable {X Y Z : RingedSpace.{u, u}}

/-! ## The tower of inverse images and the tower of topos inverse images -/

/-- **The middle homomorphism of the tower is `f⁻¹` of the structure map of `g`.** Across the
identification `(g ∘ f)⁻¹𝒪_Z ≅ f⁻¹g⁻¹𝒪_Z` of Tag 008I, the homomorphism
`baseStructureMap f g : (g ∘ f)⁻¹𝒪_Z ⟶ f⁻¹𝒪_Y` is `f⁻¹` of `g⁻¹𝒪_Z ⟶ 𝒪_Y`. -/
theorem baseStructureMap_eq (f : X ⟶ Y) (g : Y ⟶ Z) :
    baseStructureMap f g =
      (sheafPullbackCompIso f.hom.base g.hom.base CommRingCat.{u}).hom.app Z.sheaf ≫
        (TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).map (inverseImageStructureMap g) := by
  have h := Adjunction.leftAdjointUniq_hom_app_homEquiv_symm (sheafAdjunction (f ≫ g))
    (((sheafAdjunction g).comp (sheafAdjunction f)).ofNatIsoRight
      (sheafPushforwardCompIso f.hom.base g.hom.base CommRingCat.{u}).symm)
    (structureSheafMap g ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map
      ((sheafAdjunction f).unit.app Y.sheaf))
  refine h.symm.trans (congrArg (fun k => _ ≫ k) ?_)
  refine (Adjunction.homEquiv_ofNatIsoRight_symm_apply _ _ _).trans ?_
  have e : (structureSheafMap g ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map
        ((sheafAdjunction f).unit.app Y.sheaf)) ≫
      (sheafPushforwardCompIso f.hom.base g.hom.base CommRingCat.{u}).symm.inv.app
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj Y.sheaf) =
      structureSheafMap g ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map
        ((sheafAdjunction f).unit.app Y.sheaf) :=
    Category.comp_id _
  refine (congrArg (⇑(((sheafAdjunction g).comp (sheafAdjunction f)).homEquiv _ _).symm) e).trans
    ((Adjunction.comp_homEquiv_symm_comp _ _ _ _).trans ?_)
  exact (congrArg (fun k => _ ≫ k) (Adjunction.homEquiv_symm_unit _ _)).trans (Category.comp_id _)

/-- The identification `(g ∘ f)⁻¹𝒪_Z ≅ φ⁻¹g⁻¹𝒪_Z` of sheaves of rings on `X`, where `φ⁻¹` is the
inverse image along the morphism of topoi presented by `f`: Tag 008I followed by the comparison
of the two inverse images along `f`. -/
def compInverseImageSheafIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    inverseImageSheaf (f ≫ g) ≅
      (Stacks.ToposBridge.ringedToposHom f).toToposHom.inverseImageRing.obj
        (inverseImageSheaf g) :=
  (sheafPullbackCompIso f.hom.base g.hom.base CommRingCat.{u}).app Z.sheaf ≪≫
    ((invCommRingIso (ringedToposSiteHom f) (isMorphismOfSites f)).app _).symm

/-- The left square of the comparison of the tower `(g ∘ f)⁻¹𝒪_Z ⟶ f⁻¹𝒪_Y ⟶ 𝒪_X` with the tower
`φ⁻¹g⁻¹𝒪_Z ⟶ φ⁻¹𝒪_Y ⟶ 𝒪_X` of topos inverse images. -/
theorem baseStructureMap_comp_invCommRingIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    baseStructureMap f g ≫
        (invCommRingIso (ringedToposSiteHom f) (isMorphismOfSites f)).inv.app Y.sheaf =
      (compInverseImageSheafIso f g).hom ≫
        (Stacks.ToposBridge.ringedToposHom f).toToposHom.inverseImageRing.map
          (inverseImageStructureMap g) := by
  rw [baseStructureMap_eq]
  exact (Category.assoc _ _ _).trans (congrArg (fun k => _ ≫ k)
    ((invCommRingIso (ringedToposSiteHom f) (isMorphismOfSites f)).inv.naturality
      (inverseImageStructureMap g)))

/-- **Tag 08SV for the tower.** The first vertex of the fundamental triangle of the tower
`(g ∘ f)⁻¹𝒪_Z ⟶ f⁻¹𝒪_Y ⟶ 𝒪_X` is the first vertex of the triangle of the tower
`φ⁻¹g⁻¹𝒪_Z ⟶ φ⁻¹𝒪_Y ⟶ 𝒪_X` of topos inverse images. -/
def baseChangedCotangentComplexIsoRingedTopos (f : X ⟶ Y) (g : Y ⟶ Z) :
    baseChangedCotangentComplex f g ≅
      CategoryTheory.Sheaf.baseChangedCotangentComplex.{u, u, u}
        (Opens.grothendieckTopology X.carrier)
        ((Stacks.ToposBridge.ringedToposHom f).toToposHom.inverseImageRing.map
          (inverseImageStructureMap g))
        (Stacks.ToposBridge.ringedToposHom f).fSharpInverseImage :=
  CategoryTheory.Sheaf.baseChangedCotangentComplexIsoOfTower (compInverseImageSheafIso f g)
    ((invCommRingIso (ringedToposSiteHom f) (isMorphismOfSites f)).app Y.sheaf).symm
    (baseStructureMap_comp_invCommRingIso f g) (invCommRingIso_inv_app_comp_fSharpInverseImage f)

/-- **The degreewise pullback `f^*L_{Y/Z}` is the first vertex of the triangle of the tower**
`(g ∘ f)⁻¹𝒪_Z ⟶ f⁻¹𝒪_Y ⟶ 𝒪_X`. -/
def degreewisePullbackCotangentComplexIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    degreewisePullbackCotangentComplex f g ≅ baseChangedCotangentComplex f g :=
  (toposPullbackModulesComplexIso f (cotangentComplex g)).symm ≪≫
    (NatIso.mapHomologicalComplex (eqToIso (congrArg (·.pullbackModules)
      (RingedToposHom.toModulesHom_eq_toRingedToposModulesHom
        (Stacks.ToposBridge.ringedToposHom f)))) (ComplexShape.up ℤ)).app _ ≪≫
    CategoryTheory.Sheaf.pullbackModulesCotangentComplexIso.{u, u, u, u, u, u}
      (Stacks.ToposBridge.ringedToposHom f) (inverseImageStructureMap g) ≪≫
    (baseChangedCotangentComplexIsoRingedTopos f g).symm

/-! ## The derived pullback -/

section DerivedPullback

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The derived pullback `Lf^*L_{Y/Z}` is the first vertex of the triangle of the tower.** The
cotangent complex `L_{Y/Z}` is K-flat, so the canonical comparison `Lf^*L_{Y/Z} ⟶ f^*L_{Y/Z}` of
Tag 06YJ is invertible, and the degreewise pullback `f^*L_{Y/Z}` is the degreewise base change
`L_{f⁻¹𝒪_Y/(g ∘ f)⁻¹𝒪_Z} ⊗_{f⁻¹𝒪_Y} 𝒪_X` by `degreewisePullbackCotangentComplexIso`. -/
def derivedPullbackBaseChangedCotangentIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj
        (cotangentComplexDerived g) ≅
      DerivedCategory.Q.obj (baseChangedCotangentComplex f g) :=
  haveI := isIso_derivedPullbackComparison_cotangentComplex f g (kFlatComplex_cotangentComplex g)
  (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).mapIso
      ((DerivedCategory.quotientCompQhIso _).app _).symm ≪≫
    asIso ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (cotangentComplex g))) ≪≫
    (DerivedCategory.quotientCompQhIso _).app _ ≪≫
    DerivedCategory.Q.mapIso (degreewisePullbackCotangentComplexIso f g)

/-- The first arrow `Lf^*L_{Y/Z} ⟶ L_{X/Z}` of the triangle:
`derivedPullbackBaseChangedCotangentIso` followed by the degreewise base-change arrow
`cotangentBaseChange`. -/
def derivedPullbackCotangentBaseChange (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj
        (cotangentComplexDerived g) ⟶ cotangentComplexDerived (f ≫ g) :=
  (derivedPullbackBaseChangedCotangentIso f g).hom ≫
    DerivedCategory.Q.map (cotangentBaseChange f g)

/-- **The first arrow through the comparison.** Composed with the inverse of
`derivedPullbackBaseChangedCotangentIso`, the first arrow `Lf^*L_{Y/Z} ⟶ L_{X/Z}` is the image in
`D(𝒪_X)` of the degreewise base-change arrow `cotangentBaseChange`. -/
theorem derivedPullbackBaseChangedCotangentIso_inv_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    (derivedPullbackBaseChangedCotangentIso f g).inv ≫ derivedPullbackCotangentBaseChange f g =
      DerivedCategory.Q.map (cotangentBaseChange f g) :=
  Iso.inv_hom_id_assoc _ _

/-- **The triangle with first vertex `Lf^*L_{Y/Z}`.** For morphisms of ringed spaces
`f : X ⟶ Y` and `g : Y ⟶ Z` the triangle

`Lf^*L_{Y/Z} ⟶ L_{X/Z} ⟶ L_{X/Y} ⟶ (Lf^*L_{Y/Z})[1]`

whose first arrow is `derivedPullbackCotangentBaseChange` and whose second arrow is the
change-of-base-ring map `cotangentChangeOfBase` is distinguished in `D(𝒪_X)`. -/
theorem exists_distTriang_derivedPullback_cotangentTower (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∃ δ : cotangentComplexDerived f ⟶
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj
          (cotangentComplexDerived g))⟦(1 : ℤ)⟧,
      Triangle.mk (derivedPullbackCotangentBaseChange f g)
          (DerivedCategory.Q.map (cotangentChangeOfBase f g)) δ ∈
        distTriang (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) := by
  obtain ⟨δ, hT⟩ := exists_distTriang_cotangentTower f g
  let e := derivedPullbackBaseChangedCotangentIso f g
  refine ⟨δ ≫ (shiftFunctor (DerivedCategory (structureModules X)) (1 : ℤ)).map e.inv,
    isomorphic_distinguished _ hT _
      (Triangle.isoMk _ _ e (Iso.refl _) (Iso.refl _) (Category.comp_id _) ?_ ?_)⟩
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact ((Category.assoc _ _ _).trans (congrArg (fun k => δ ≫ k)
      ((shiftFunctor (DerivedCategory (structureModules X)) (1 : ℤ)).mapIso e).inv_hom_id)).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm)

end DerivedPullback

end Stacks.Sheaves.RingedSpaceCotangent

end
