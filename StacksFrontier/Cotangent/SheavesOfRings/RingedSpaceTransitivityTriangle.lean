module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.TopoiBridge.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalTypesSitePresentedPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackSectionsBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.InverseImageExactness
public import StacksFrontier.Cotangent.SheavesOfRings.RingedSpace
public import StacksFrontier.Cotangent.SheavesOfRings.RingedToposTransitivityTriangleDerived
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.MixedDerivedTensorOnARingedSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Unconditional
public import StacksFrontier.Topology.Sheaves.Functors.Pullback.Comp
import StacksCore.Tactic.StacksAttribute

/-!
# The transitivity triangle of the cotangent complex for morphisms of ringed spaces

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of ringed spaces. There is a canonical
distinguished triangle

`Lf^* L_{Y/Z} ⟶ L_{X/Z} ⟶ L_{X/Y} ⟶ Lf^* L_{Y/Z}[1]`

in `D(𝒪_X)`, where `L_{X/S}` is the cotangent complex of Definition 08UU and `Lf^*` is the
derived pullback of Tag 06YJ.

## Main definitions

* `Stacks.Sheaves.RingedSpaceCotangent.cotangentComplexIsoRingedTopos`: `L_{X/S}` is the
  cotangent complex of the morphism of ringed topoi presented by `X ⟶ S`.
* `Stacks.Sheaves.RingedSpaceCotangent.compCotangentComplexIsoRingedTopos`: `L_{X/Z}` is the
  cotangent complex of the composite of the two presented morphisms of ringed topoi.
* `Stacks.Sheaves.RingedSpaceCotangent.derivedPullbackCotangentComplexIso`: the ringed-space
  `Lf^* L_{Y/Z}` is the ringed-topos derived pullback of the cotangent complex of the presented
  morphism.
* `Stacks.Sheaves.RingedSpaceCotangent.transitivityUnit` and
  `Stacks.Sheaves.RingedSpaceCotangent.transitivityCounit`: the two canonical arrows
  `Lf^* L_{Y/Z} ⟶ L_{X/Z} ⟶ L_{X/Y}`.

## Main results

* `Stacks.Sheaves.RingedSpaceCotangent.sheafPullbackCompIso_hom_app_comp_inverseImageStructureMap`:
  the structure map of `g ∘ f` is the composite of the tower
  `(g ∘ f)⁻¹𝒪_Z = f⁻¹g⁻¹𝒪_Z ⟶ f⁻¹𝒪_Y ⟶ 𝒪_X`.
* `Stacks.Sheaves.RingedSpaceCotangent.exists_distTriang_transitivity`: the transitivity
  triangle `Lf^* L_{Y/Z} ⟶ L_{X/Z} ⟶ L_{X/Y} ⟶ Lf^* L_{Y/Z}[1]` is distinguished.

## Implementation notes

A ringed space presents a ringed topos (`Stacks.ToposBridge.ringedTopos`) and a morphism of
ringed spaces a morphism of ringed topoi (`Stacks.ToposBridge.ringedToposHom`). The triangle is
the one of Tag 08V1 for the two presented morphisms, with its three vertices identified with the
ringed-space objects.

The derived categories are the standard models `HasDerivedCategory.standard`, the models the
derived pullbacks of Tags 06YJ and 06YY are stated for. The derived pullback `Lf^*` is
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback`, the ringed-space one;
`Stacks.Cohomology.MixedDerivedTensorOnARingedSpace.derivedPullback_eq` records that it is the
ringed-topos derived pullback of Tag 06YY along the presented morphism of ringed sites.

Everything is at `AlgebraicGeometry.RingedSpace.{u, u}`, the universes of the ringed-space
cotangent complex of Definition 08UU and of the derived pullback of Tag 06YJ.

## References

* [Stacks Project, Tag 08T4](https://stacks.math.columbia.edu/tag/08T4)
* [Stacks Project, Tag 08V1](https://stacks.math.columbia.edu/tag/08V1), the triangle for
  morphisms of ringed topoi.
* [Stacks Project, Tag 08UU](https://stacks.math.columbia.edu/tag/08UU), the cotangent complex
  of a morphism of ringed spaces.
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ), the derived pullback.
* [Stacks Project, Tag 008I](https://stacks.math.columbia.edu/tag/008I), the composition of
  inverse images.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace
open Stacks.Sheaves.RingedSpaceDifferentials (sheafAdjunction structureSheafMap inverseImageSheaf
  inverseImageStructureMap)
open Stacks.Cohomology.MixedDerivedTensorOnARingedSpace (ringedToposSiteHom isMorphismOfSites)
open Stacks.Sheaves.InverseImageExactness (invCommRingIso)

universe u

namespace Stacks.Sheaves.RingedSpaceCotangent

variable {X Y Z : RingedSpace.{u, u}}

/-! ## The structure map of the presented morphism of ringed topoi -/

/-- The inverse-image form of the structure map of the morphism of ringed topoi presented by a
morphism of ringed spaces `f : X ⟶ Y` is `f⁻¹𝒪_Y ⟶ 𝒪_X`, read through the identification of
the topos inverse image of `𝒪_Y` with `f⁻¹𝒪_Y`: both are adjuncts of `f^♯`. -/
theorem invCommRingIso_hom_app_comp_inverseImageStructureMap (f : X ⟶ Y) :
    (invCommRingIso (ringedToposSiteHom f) (isMorphismOfSites f)).hom.app Y.sheaf ≫
      inverseImageStructureMap f = (Stacks.ToposBridge.ringedToposHom f).fSharpInverseImage :=
  (Adjunction.leftAdjointUniq_hom_app_homEquiv_symm _ _ (structureSheafMap f)).trans
    (Adjunction.homEquiv_ofNatIsoRight_symm_apply _ _ _)

/-- `f⁻¹𝒪_Y ⟶ 𝒪_X` is the inverse-image form of the structure map of the presented morphism of
ringed topoi, read through the identification of the two inverse images of `𝒪_Y`. -/
theorem invCommRingIso_inv_app_comp_fSharpInverseImage (f : X ⟶ Y) :
    (invCommRingIso (ringedToposSiteHom f) (isMorphismOfSites f)).inv.app Y.sheaf ≫
      (Stacks.ToposBridge.ringedToposHom f).fSharpInverseImage = inverseImageStructureMap f :=
  (Iso.inv_comp_eq ((invCommRingIso (ringedToposSiteHom f) (isMorphismOfSites f)).app
    Y.sheaf)).mpr (invCommRingIso_hom_app_comp_inverseImageStructureMap f).symm

/-- The square of sheaves of rings comparing `f⁻¹𝒪_Y ⟶ 𝒪_X` with the inverse-image form of the
structure map of the presented morphism of ringed topoi commutes. -/
theorem inverseImageStructureMap_comp_id (f : X ⟶ Y) :
    inverseImageStructureMap f ≫ 𝟙 X.sheaf =
      (invCommRingIso (ringedToposSiteHom f) (isMorphismOfSites f)).inv.app Y.sheaf ≫
        (Stacks.ToposBridge.ringedToposHom f).fSharpInverseImage :=
  (Category.comp_id _).trans (invCommRingIso_inv_app_comp_fSharpInverseImage f).symm

/-- **`L_{X/Y}` is the cotangent complex of the presented morphism of ringed topoi.** The
cotangent complex `L_{𝒪_X/f⁻¹𝒪_Y}` of Definition 08UU is the cotangent complex of the
inverse-image form of the structure map of `Stacks.ToposBridge.ringedToposHom f`. -/
def cotangentComplexIsoRingedTopos (f : X ⟶ Y) :
    cotangentComplex f ≅ (Stacks.ToposBridge.ringedToposHom f).cotangentComplex :=
  @Sheaf.squareCotangentComplexIso.{u, u, u} (Opens X.carrier) _
    (Opens.grothendieckTopology X.carrier) _ _ _ _ _ _ _ _ (inverseImageStructureMap_comp_id f)
    (Iso.isIso_inv ((invCommRingIso (ringedToposSiteHom f) (isMorphismOfSites f)).app Y.sheaf))
    (IsIso.id _) ≪≫
    SheafOfModules.restrictScalarsIdComplexIso _ (CategoryTheory.Functor.map_id _ _) _

/-! ## The middle vertex -/

/-- The structure map of `g ∘ f` is the structure map of `g` pulled back along `f` followed by
the structure map of `f`, across `(g ∘ f)⁻¹𝒪_Z ≅ f⁻¹g⁻¹𝒪_Z` (Tag 008I). -/
@[stacks 08T4 "the tower (g ∘ f)⁻¹O_Z = f⁻¹g⁻¹O_Z ⟶ f⁻¹O_Y ⟶ O_X of the proof: the structure \
  map of g ∘ f is the composite of the tower"]
theorem sheafPullbackCompIso_hom_app_comp_inverseImageStructureMap (f : X ⟶ Y) (g : Y ⟶ Z) :
    (sheafPullbackCompIso f.hom.base g.hom.base CommRingCat.{u}).hom.app Z.sheaf ≫
        (TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).map (inverseImageStructureMap g) ≫
          inverseImageStructureMap f =
      inverseImageStructureMap (f ≫ g) := by
  have h := Adjunction.leftAdjointUniq_hom_app_homEquiv_symm (sheafAdjunction (f ≫ g))
    (((sheafAdjunction g).comp (sheafAdjunction f)).ofNatIsoRight
      (sheafPushforwardCompIso f.hom.base g.hom.base CommRingCat.{u}).symm)
    (structureSheafMap (f ≫ g))
  have h2 : structureSheafMap (f ≫ g) ≫
      (sheafPushforwardCompIso f.hom.base g.hom.base CommRingCat.{u}).symm.inv.app X.sheaf =
      structureSheafMap g ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map (structureSheafMap f) :=
    Category.comp_id _
  refine Eq.trans ?_ h
  congr 1
  refine ((Adjunction.comp_homEquiv_symm_comp (sheafAdjunction g) (sheafAdjunction f)
    (structureSheafMap g) (structureSheafMap f)).symm.trans ?_)
  rw [← h2]
  exact (Adjunction.homEquiv_ofNatIsoRight_symm_apply
    ((sheafAdjunction g).comp (sheafAdjunction f))
    (sheafPushforwardCompIso f.hom.base g.hom.base CommRingCat.{u}).symm
    (structureSheafMap (f ≫ g))).symm

/-- The identification `(g ∘ f)⁻¹𝒪_Z ≅ f⁻¹g⁻¹𝒪_Z` of sheaves of rings on `X`, with the two
inverse images on the right taken along the presented morphisms of topoi. -/
def compInverseImageRingIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    inverseImageSheaf (f ≫ g) ≅
      (Stacks.ToposBridge.ringedToposHom f).toToposHom.inverseImageRing.obj
        ((Stacks.ToposBridge.ringedToposHom g).toToposHom.inverseImageRing.obj Z.sheaf) :=
  (sheafPullbackCompIso f.hom.base g.hom.base CommRingCat.{u}).app Z.sheaf ≪≫
    (TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).mapIso
      ((invCommRingIso (ringedToposSiteHom g) (isMorphismOfSites g)).app Z.sheaf).symm ≪≫
    ((invCommRingIso (ringedToposSiteHom f) (isMorphismOfSites f)).app _).symm

/-- The structure map `(g ∘ f)⁻¹𝒪_Z ⟶ 𝒪_X` is the composite of the tower
`f⁻¹g⁻¹𝒪_Z ⟶ f⁻¹𝒪_Y ⟶ 𝒪_X` of topos inverse images, across `compInverseImageRingIso`. -/
theorem inverseImageStructureMap_comp_comp_id (f : X ⟶ Y) (g : Y ⟶ Z) :
    inverseImageStructureMap (f ≫ g) ≫ 𝟙 X.sheaf =
      (compInverseImageRingIso f g).hom ≫
        (RingedToposHom.towerBaseMap.{u, u, u, u, u, u, u, u, u}
          (Stacks.ToposBridge.ringedToposHom g) (Stacks.ToposBridge.ringedToposHom f) ≫
          (Stacks.ToposBridge.ringedToposHom f).fSharpInverseImage) := by
  let c := (sheafPullbackCompIso f.hom.base g.hom.base CommRingCat.{u}).hom.app Z.sheaf
  let κf := invCommRingIso (ringedToposSiteHom f) (isMorphismOfSites f)
  let κg := invCommRingIso (ringedToposSiteHom g) (isMorphismOfSites g)
  let pf := TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base
  have e3 : pf.map (κg.inv.app Z.sheaf ≫ (Stacks.ToposBridge.ringedToposHom g).fSharpInverseImage)
      ≫ κf.inv.app Y.sheaf ≫ (Stacks.ToposBridge.ringedToposHom f).fSharpInverseImage =
      pf.map (κg.inv.app Z.sheaf) ≫ κf.inv.app _ ≫
        (Stacks.ToposBridge.ringedToposHom f).toToposHom.inverseImageRing.map
          (Stacks.ToposBridge.ringedToposHom g).fSharpInverseImage ≫
        (Stacks.ToposBridge.ringedToposHom f).fSharpInverseImage :=
    ((pf.map_comp _ _).symm ▸ rfl : _ = (pf.map (κg.inv.app Z.sheaf) ≫ pf.map _) ≫ _).trans
      ((Category.assoc _ _ _).trans (congrArg (fun k => pf.map (κg.inv.app Z.sheaf) ≫ k)
        (κf.inv.naturality_assoc _ _)))
  exact (Category.comp_id _).trans
    ((sheafPullbackCompIso_hom_app_comp_inverseImageStructureMap f g).symm.trans
      ((congrArg (fun k => c ≫ pf.map k ≫ inverseImageStructureMap f)
        (invCommRingIso_inv_app_comp_fSharpInverseImage g).symm).trans
      ((congrArg (fun k => c ≫ pf.map (κg.inv.app Z.sheaf ≫
          (Stacks.ToposBridge.ringedToposHom g).fSharpInverseImage) ≫ k)
        (invCommRingIso_inv_app_comp_fSharpInverseImage f).symm).trans
      ((congrArg (fun k => c ≫ k) e3).trans
        ((congrArg (fun k => c ≫ k) (Category.assoc _ _ _).symm).trans
          (Category.assoc _ _ _).symm)))))

/-- `L_{X/Z}` is the cotangent complex `L_{𝒪_X/f⁻¹g⁻¹𝒪_Z}` of the tower of topos inverse
images, the middle vertex of the fundamental triangle of Tag 08V1 for the presented
morphisms. -/
def compCotangentComplexIsoTower (f : X ⟶ Y) (g : Y ⟶ Z) :
    cotangentComplex (f ≫ g) ≅
      RingedToposHom.compositeCotangentComplex.{u, u, u, u, u, u, u, u, u}
        (Stacks.ToposBridge.ringedToposHom g) (Stacks.ToposBridge.ringedToposHom f) :=
  @Sheaf.squareCotangentComplexIso.{u, u, u} (Opens X.carrier) _
    (Opens.grothendieckTopology X.carrier) _ _ _ _ _ _ _ _
    (inverseImageStructureMap_comp_comp_id f g)
    (Iso.isIso_hom (compInverseImageRingIso f g)) (IsIso.id _) ≪≫
    SheafOfModules.restrictScalarsIdComplexIso _ (CategoryTheory.Functor.map_id _ _) _

/-- **`L_{X/Z}` is the cotangent complex of the composite of the presented morphisms of ringed
topoi.** -/
def compCotangentComplexIsoRingedTopos (f : X ⟶ Y) (g : Y ⟶ Z) :
    cotangentComplex (f ≫ g) ≅
      ((Stacks.ToposBridge.ringedToposHom g).comp
        (Stacks.ToposBridge.ringedToposHom f)).cotangentComplex :=
  compCotangentComplexIsoTower f g ≪≫
    (RingedToposHom.compCotangentComplexIso.{u, u, u, u, u} (Stacks.ToposBridge.ringedToposHom g)
      (Stacks.ToposBridge.ringedToposHom f)).symm

/-! ## The first vertex -/

/-- The morphism of ringed sites presented by `f`, written as the morphism of ringed topoi
presented by `f` read on its site, is `Stacks.Cohomology.MixedDerivedTensorOnARingedSpace`'s
`ringedToposSiteHom f`. -/
theorem ofMorphismOfSites_eq_ringedToposSiteHom (f : X ⟶ Y) :
    RingedToposSiteHom.ofMorphismOfSites (isMorphismOfSites f)
      (Stacks.ToposBridge.ringedToposHom f).fSharp = ringedToposSiteHom f := by
  unfold RingedToposSiteHom.ofMorphismOfSites ringedToposSiteHom
  congr 1

/-- The pullback of sheaves of modules along the presented morphism of ringed topoi is the
pullback `f^*` of sheaves of modules on ringed spaces. -/
def toposPullbackModulesIso (f : X ⟶ Y) :
    (Stacks.ToposBridge.ringedToposHom f).toModulesHom.pullbackModules ≅
      RingedSpaceModuleAdjunction.modulePullback f :=
  RingedToposHom.pullbackModulesIsoPullbackTopos (isMorphismOfSites f)
      (Stacks.ToposBridge.ringedToposHom f).fSharp ≪≫
    eqToIso (congrArg (fun h : RingedToposSiteHom (Stacks.ToposBridge.ringedTopos X)
      (Stacks.ToposBridge.ringedTopos Y) => h.pullbackTopos)
      (ofMorphismOfSites_eq_ringedToposSiteHom f)) ≪≫
    eqToIso (Stacks.Cohomology.MixedDerivedTensorOnARingedSpace.pullbackTopos_eq f)

/-- `toposPullbackModulesIso`, degreewise on a cochain complex. -/
def toposPullbackModulesComplexIso (f : X ⟶ Y)
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) :
    (((Stacks.ToposBridge.ringedToposHom f).toModulesHom.pullbackModules).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K ≅
      ((RingedSpaceModuleAdjunction.modulePullback f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K :=
  (@NatIso.mapHomologicalComplex ℤ _ _ _ _ _ _ _ _
    (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
      (Stacks.ToposBridge.ringedToposHom f).toModulesHom.pullbackModules
      (RingedToposHom.pullbackModules_additive (Stacks.ToposBridge.ringedToposHom f)))
    (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
      (RingedSpaceModuleAdjunction.modulePullback f)
      (RingedSpaceModuleAdjunction.modulePullback_additive f))
    (toposPullbackModulesIso f) (ComplexShape.up ℤ)).app K

section DerivedPullback

attribute [local instance 10000] HasDerivedCategory.standard

/-- The cotangent complex `L_{Y/Z}` is K-flat. -/
theorem kFlatComplex_cotangentComplex (g : Y ⟶ Z) :
    Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y (cotangentComplex g) :=
  (Sheaf.isKFlat_cotangentComplex' (Opens.grothendieckTopology Y.carrier)
    (inverseImageStructureMap g)).1

/-- The derived pullback `Lf^* L_{Y/Z}` of Tag 06YJ is the ringed-topos derived pullback of
Tag 06YY, along the presented morphism, of the cotangent complex of the presented morphism
`g`. -/
def derivedPullbackCotangentComplexIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj
        (cotangentComplexDerived g) ≅
      (RingedToposHom.derivedPullback.{u, u, u, u, u, u}
        (Stacks.ToposBridge.ringedToposHom f)).obj
        (Stacks.ToposBridge.ringedToposHom g).cotangentComplexDerived :=
  haveI : IsIso ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (cotangentComplex g))) :=
    Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat f
      (cotangentComplex g) (kFlatComplex_cotangentComplex g)
  haveI : IsIso ((Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackComparison
      (Stacks.ToposBridge.ringedToposHom f)).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (cotangentComplex g))) :=
    Stacks.Cohomology.DerivedPullbackOfToposHom.isIso_derivedPullbackComparison_app
      (Stacks.ToposBridge.ringedToposHom f)
      (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
        (Y := Stacks.ToposBridge.ringedTopos Y))
      (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.hasResolutions_isKFlat
        (Y := Stacks.ToposBridge.ringedTopos Y))
      (Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackInvertsQuasiIso_isKFlat
        (Stacks.ToposBridge.ringedToposHom f))
      _ (Sheaf.isKFlat_cotangentComplex' (Opens.grothendieckTopology Y.carrier)
        (inverseImageStructureMap g))
  (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).mapIso
      ((DerivedCategory.quotientCompQhIso _).app _).symm ≪≫
    asIso ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (cotangentComplex g))) ≪≫
    (DerivedCategory.quotientCompQhIso _).app _ ≪≫
    DerivedCategory.Q.mapIso (toposPullbackModulesComplexIso f (cotangentComplex g)).symm ≪≫
    ((DerivedCategory.quotientCompQhIso _).app _).symm ≪≫
    (asIso ((Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackComparison
      (Stacks.ToposBridge.ringedToposHom f)).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (cotangentComplex g)))).symm ≪≫
    (RingedToposHom.derivedPullback.{u, u, u, u, u, u} (Stacks.ToposBridge.ringedToposHom f)).mapIso
      ((DerivedCategory.quotientCompQhIso _).app _ ≪≫
        DerivedCategory.Q.mapIso (cotangentComplexIsoRingedTopos g))

end DerivedPullback

/-! ## Tag 08T4 -/

/-- Cancelling `F.map e.inv ≫ F.map e.hom` at the end of a composite. -/
private theorem comp_comp_map_inv_comp_map_hom {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A : D} {B B' : C} (e : B ≅ B') {M : D} (u : A ⟶ M) (v : M ⟶ F.obj B') :
    (u ≫ v ≫ F.map e.inv) ≫ F.map e.hom = u ≫ v := by
  rw [Category.assoc, Category.assoc, ← F.map_comp, e.inv_hom_id, F.map_id, Category.comp_id]

section Triangle

attribute [local instance 10000] HasDerivedCategory.standard

/-- The first arrow `Lf^* L_{Y/Z} ⟶ L_{X/Z}` of the transitivity triangle: the first arrow of
the triangle of Tag 08V1 for the presented morphisms of ringed topoi, read through
`derivedPullbackCotangentComplexIso` and `compCotangentComplexIsoRingedTopos`. -/
@[stacks 08T4 "the canonical first arrow Lf^* L_{Y/Z} ⟶ L_{X/Z} of the triangle"]
def transitivityUnit (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj
        (cotangentComplexDerived g) ⟶ cotangentComplexDerived (f ≫ g) :=
  (derivedPullbackCotangentComplexIso f g).hom ≫
    RingedToposHom.transitivityUnit.{u, u, u, u, u} (Stacks.ToposBridge.ringedToposHom g)
      (Stacks.ToposBridge.ringedToposHom f) ≫
    DerivedCategory.Q.map (compCotangentComplexIsoRingedTopos f g).inv

/-- The second arrow `L_{X/Z} ⟶ L_{X/Y}` of the transitivity triangle: the second arrow of the
triangle of Tag 08V1 for the presented morphisms of ringed topoi, read through
`compCotangentComplexIsoRingedTopos` and `cotangentComplexIsoRingedTopos`. -/
@[stacks 08T4 "the canonical second arrow L_{X/Z} ⟶ L_{X/Y} of the triangle"]
def transitivityCounit (f : X ⟶ Y) (g : Y ⟶ Z) :
    cotangentComplexDerived (f ≫ g) ⟶ cotangentComplexDerived f :=
  DerivedCategory.Q.map (compCotangentComplexIsoRingedTopos f g).hom ≫
    RingedToposHom.transitivityCounit.{u, u, u, u, u} (Stacks.ToposBridge.ringedToposHom g)
      (Stacks.ToposBridge.ringedToposHom f) ≫
    DerivedCategory.Q.map (cotangentComplexIsoRingedTopos f).inv

/-- **The transitivity triangle.** Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of ringed
spaces. The canonical triangle

`Lf^* L_{Y/Z} ⟶ L_{X/Z} ⟶ L_{X/Y} ⟶ Lf^* L_{Y/Z}[1]`

is distinguished in `D(𝒪_X)`. Here `L_{X/S}` is the cotangent complex of Definition 08UU,
`Lf^*` is the derived pullback of Tag 06YJ, and the two arrows are `transitivityUnit` and
`transitivityCounit`, those of the fundamental triangle of the tower
`(g ∘ f)⁻¹𝒪_Z = f⁻¹g⁻¹𝒪_Z ⟶ f⁻¹𝒪_Y ⟶ 𝒪_X` (Tags 08SZ and 08V1). -/
@[stacks 08T4]
theorem exists_distTriang_transitivity (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∃ δ : cotangentComplexDerived f ⟶
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj
          (cotangentComplexDerived g))⟦(1 : ℤ)⟧,
      Triangle.mk (transitivityUnit f g) (transitivityCounit f g) δ ∈
        distTriang (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) := by
  obtain ⟨δ, h⟩ := RingedToposHom.exists_distTriang_transitivity.{u, u, u, u, u}
    (Stacks.ToposBridge.ringedToposHom g) (Stacks.ToposBridge.ringedToposHom f)
  refine ⟨DerivedCategory.Q.map (cotangentComplexIsoRingedTopos f).hom ≫ δ ≫
      (shiftFunctor (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (1 : ℤ)).map
        (derivedPullbackCotangentComplexIso f g).inv,
    isomorphic_distinguished _ h _ (Triangle.isoMk _ _ (derivedPullbackCotangentComplexIso f g)
      (DerivedCategory.Q.mapIso (compCotangentComplexIsoRingedTopos f g))
      (DerivedCategory.Q.mapIso (cotangentComplexIsoRingedTopos f)) ?_ ?_ ?_)⟩
  · exact comp_comp_map_inv_comp_map_hom _ _ _ _
  · exact comp_comp_map_inv_comp_map_hom _ _ _ _
  · exact comp_comp_map_inv_comp_map_hom _ _ _ _

end Triangle

end Stacks.Sheaves.RingedSpaceCotangent

end
