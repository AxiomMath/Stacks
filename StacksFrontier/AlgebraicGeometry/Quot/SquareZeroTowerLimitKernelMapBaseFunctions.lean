module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatDeformationMapGlobalSection
public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerExtensionSections
public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerLimitComparisonData
public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerLimitKernelFunctionComponents
public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerLimitKernelMapIdealSide
public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerLimitKernelMapSets
public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerLimitKernelMapValues
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RestrictedFirstOrderExtensionSectionSets
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickenedBaseGlobalSectionSets

/-!
# The class `σ_m` and functions of `Y` through the thickened base, on sheaves of sets

In the situation of `AlgebraicGeometry.ProperFlatFibre.towerProblem` (body of the proof of
[Stacks Project, Tag 0D3X]): the class `σ_m` of the function `c_m` of `Y = Spec(lim Rₙ)` in the
base thickening, the base map on sections given by functions of `Y`, and `gₙ^♯ c_m = g^♯ mₙ` on
`Xₙ`, all on underlying sheaves of sets.

## Main results

* `ringOneHom_comp_map_towerLimitKernelFunction_comp_limitBaseExtension_inclSheafSets`:
  the class `σ_m` included into `i⁻¹𝒪_Y` is the restricted inverse image of `c_m`.
* `globalSectionMap_comp_forget_map_towerProblemBaseIso_hom`: the restricted inverse image of a
  global section `t` of `𝒪_Y`, read in the thickened base, is `i⁻¹t`.
* `globalSectionMap_comp_forget_map_thickenedBaseIso_inv_comp_towerLimitBaseMapApp`: the base
  map sends `f⁻¹(i⁻¹τ)` to the restricted inverse image of the function `gₙ^♯(gₙ⁻¹τ)` of `Xₙ`.
* `globalSectionMap_towerLimitKernelFunction_comp_structureSharpInverseImage`:
  `gₙ^♯ c_m = g^♯ mₙ` on `Xₙ`.
* `towerLimitKernelFunction_inclSheafSets_comp_forget_map_towerProblemBaseIso_hom`: `σ_m`
  included into `i⁻¹𝒪_Y`, read in the thickened base, is `i⁻¹c_m`.
* `globalSectionMap_towerLimitKernelFunction_comp_structureSharpInverseImage_eq`:
  `gₙ^♯ c_m = g^♯ mₙ`, inside the restriction of the inverse image.

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite

universe u

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

/- The global instance `Abelian (SheafOfModules.{max u v r w} O)` leaves a stuck universe
constraint against the `𝒪_X`-modules at the universe of the schemes. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.ProperFlatFibre

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (ξ : ℕ ⥤ CartesianProperFlatSpaces B S hS)
  {Λ : Type u} [CommRing Λ] {R : ℕᵒᵖ ⥤ CommAlgCat.{u} Λ}
  (hsurj : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), Function.Surjective (R.map f).hom)
  (hsq : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), RingHom.ker (R.map f).hom.toRingHom ^ 2 = ⊥)
  (e : ∀ n : ℕ, (BigFppfOver.toScheme B S hS).obj (towerBase ξ n) ≅
    Spec (.of (R.obj (.op n))))
  (he : ∀ {i j : ℕ} (f : i ⟶ j),
    (BigFppfOver.toScheme B S hS).map ((ξ ⋙ cartesianProperFlatProjection B S hS).map f) ≫
      (e j).hom = (e i).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (R.map f.op).hom.toRingHom).op)
  (cR : Cone R) (hcR : IsLimit cR) (c : Cocone (ξ ⋙ cartesianProperFlatProjection B S hS))
  (eLimit : (BigFppfOver.toScheme B S hS).obj c.pt ≅ Spec (.of cR.pt))
  (hc : ∀ n : ℕ, (BigFppfOver.toScheme B S hS).map (c.ι.app n) ≫ eLimit.hom =
    (e n).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (cR.π.app (.op n)).hom.toRingHom).op)

attribute [local instance] instIsContinuousSmallEtalePostcompTowerFibreIsoKernelMapFunctions
  instIsContinuousSmallEtalePostcompLimitBaseRangeIsoKernelMapFunctions

/-- **The class `σ_m` in the base thickening, on sheaves of sets**: the unit section followed by
`σ_m` (the class of `c_m` restricted to `Y₀`) and the inclusion of `𝒞_{Y₀/Y}` into `i⁻¹𝒪_Y` is the
restriction along `Y₀ ≅ (Y₀ ⊆ Y)` of the inverse image of the function `c_m`. -/
theorem ringOneHom_comp_map_towerLimitKernelFunction_comp_limitBaseExtension_inclSheafSets
    (m : ↑(limit (towerBaseKernelSystem ξ hsurj hsq e))) :
    ringOneHom ((sheafCompose (Space.SmallEtale.topology B S hS (schemeSpace (towerBase ξ 0)).1)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (schemeSpace
        (towerBase ξ 0))).O) ≫ (moduleSheafFunctor ((sheafCompose (Space.SmallEtale.topology B S hS
        (schemeSpace (towerBase ξ 0)).1) (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (Space.smallEtaleRingedTopos B S hS (schemeSpace (towerBase ξ 0))).O)).map
        ((Space.modulePullbackGlobalSection B S hS (X := schemeSpace (towerBase ξ 0))
        (Space.rangeSpaceIso B S hS (c.ι.app 0) (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e
        cR hcR c eLimit hc).1).hom (Space.rangeConormalSection B S hS (c.ι.app 0)
        (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1
        (towerLimitKernelFunction ξ hsurj hsq e cR hcR c eLimit hc m))) ≫
        ((Space.modulePullbackIsoEtaleRestrictionModule B S hS (U := schemeSpace (towerBase ξ 0))
        (Space.rangeSpaceIso B S hS (c.ι.app 0) (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e
        cR hcR c eLimit hc).1).hom (Space.isEtale_hom_of_iso B S hS _)).app
        (Space.rangeConormalModule B S hS (c.ι.app 0) (isSquareZeroClosedImmersion_limitBase ξ hsurj
        hsq e cR hcR c eLimit hc).1)).hom : SheafOfModules.unit ((sheafCompose
        (Space.SmallEtale.topology B S hS (schemeSpace (towerBase ξ 0)).1) (forget₂ CommRingCat.{u}
        RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (schemeSpace (towerBase ξ 0))).O) ⟶
        limitBaseConormal ξ hsurj hsq e cR hcR c eLimit hc) ≫
        (limitBaseExtension ξ hsurj hsq e cR hcR c eLimit hc).inclSheafSets =
            ((Space.smallEtaleSetRestriction B S hS (limitBaseRangeIso ξ hsurj hsq e cR hcR c eLimit
            hc).hom (Space.isEtale_hom_of_iso B S hS _)).globalSectionMap ((Space.thickeningToposHom
            B S hS (limitBaseSubspace ξ hsurj hsq e cR hcR c eLimit
            hc)).inverseImage.globalSectionMap (ringOneHom (Space.structureRingSheaf B S hS
            (schemeSpace c.pt)) ≫ (moduleSheafFunctor (Space.structureRingSheaf B S hS (schemeSpace
            c.pt))).map (Space.unitModuleMul B S hS (schemeSpace c.pt) (Space.globalFunctionsOfMap
            (𝟙 (schemeSpace c.pt)) (towerLimitKernelFunction ξ hsurj hsq e cR hcR c eLimit hc m).1))
            : ⊤_ _ ⟶ (sheafCompose (Space.SmallEtale.topology B S hS (schemeSpace c.pt).1) (forget
            CommRingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (schemeSpace c.pt)).O))) := by
  have hG :=
    Space.ringOneHom_comp_map_rangeConormalSection_comp_restrictedFirstOrderExtension_inclSheafSets
    B S hS (c.ι.app 0) (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1
        (Space.isFirstOrderThickening_range_yoneda_map B S hS (c.ι.app 0)
        (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc))
    (limitBaseRangeIso ξ hsurj hsq e cR hcR c eLimit hc) (𝟙 _) (towerLimitKernelFunction ξ hsurj hsq
        e cR hcR c eLimit hc m)
  refine Eq.trans ?_ (hG.trans ?_)
  · refine congrArg₂ (· ≫ ·) rfl (congrArg₂ (· ≫ ·) ?_ rfl)
    refine congrArg _ ?_
    refine congrArg₂ (· ≫ ·) ?_ rfl
    exact rfl
  · exact rfl

/-- The restriction along `Y₀ ≅ (Y₀ ⊆ Y)` of the inverse image of a global section `t` of `𝒪_Y`,
read in `i⁻¹𝒪_Y` through the identification of the thickened base, is `i⁻¹t`. -/
theorem globalSectionMap_comp_forget_map_towerProblemBaseIso_hom
    (t : ⊤_ _ ⟶ (sheafCompose (Space.SmallEtale.topology B S hS (schemeSpace c.pt).1) (forget
        CommRingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (schemeSpace c.pt)).O) :
    (Space.smallEtaleSetRestriction B S hS (limitBaseRangeIso ξ hsurj hsq e cR hcR c eLimit hc).hom
        (Space.isEtale_hom_of_iso B S hS _)).globalSectionMap
        ((Space.thickeningToposHom B S hS (limitBaseSubspace ξ hsurj hsq e cR hcR c eLimit
            hc)).inverseImage.globalSectionMap t) ≫
      (sheafCompose (Space.SmallEtale.topology B S hS (schemeSpace (towerBase ξ 0)).1)
        (forget CommRingCat.{u})).map (towerProblemBaseIso ξ hsurj hsq e cR hcR c eLimit hc).hom =
      (Space.smallEtaleRingedToposHom B S hS
        (schemeSpaceMap (c.ι.app 0))).toToposHom.inverseImage.globalSectionMap t :=
  Space.globalSectionMap_comp_forget_map_restrictedFirstOrderExtensionIso_inv_comp_eqToHom B S hS
    (limitBaseSubspace ξ hsurj hsq e cR hcR c eLimit hc)
        (Space.isFirstOrderThickening_range_yoneda_map B S hS (c.ι.app 0)
        (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc)) (limitBaseRangeIso
        ξ hsurj hsq e cR hcR c eLimit hc) (𝟙 _)
    (Space.rangeSpaceIso_hom_comp_subspaceInclusion B S hS (c.ι.app 0)
        (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1) t

/-- **The base map on sections given by functions of `Y`**: if a global section `β` of the
thickened base is `i⁻¹τ`, then `f⁻¹β`, carried by the base map to `𝒜` and projected to `Aₙ`, is the
restriction along `X₀ ≅ g⁻¹(Y₀)` of the inverse image of the function `gₙ^♯(gₙ⁻¹τ)` of `Xₙ`,
`gₙ : Xₙ ⟶ Y`. -/
theorem globalSectionMap_comp_forget_map_thickenedBaseIso_inv_comp_towerLimitBaseMapApp (n : ℕ)
    (β : ⊤_ _ ⟶ (sheafCompose (Space.SmallEtale.topology B S hS (schemeSpace (towerBase ξ 0)).1)
      (forget CommRingCat.{u})).obj (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).baseExtension)
    (τ : ⊤_ _ ⟶ (sheafCompose (Space.SmallEtale.topology B S hS (schemeSpace c.pt).1) (forget
        CommRingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (schemeSpace c.pt)).O)
    (hβ : β ≫ (sheafCompose (Space.SmallEtale.topology B S hS (schemeSpace (towerBase ξ 0)).1)
      (forget CommRingCat.{u})).map (towerProblemBaseIso ξ hsurj hsq e cR hcR c eLimit hc).hom =
      (Space.smallEtaleRingedToposHom B S hS
        (schemeSpaceMap (c.ι.app 0))).toToposHom.inverseImage.globalSectionMap τ) :
    (Space.smallEtaleRingedToposHom B S hS (towerStructureMap ξ
        0)).toToposHom.inverseImage.globalSectionMap β ≫ (sheafCompose (Space.SmallEtale.topology B
        S hS (towerSpace ξ 0).1) (forget CommRingCat.{u})).map ((Space.thickenedBaseIso B S hS
        (towerStructureMap ξ 0) (schemeSpaceMap (c.ι.app 0)) (towerProblemBaseIso ξ hsurj hsq e cR
        hcR c eLimit hc)).inv ≫ towerLimitBaseMapApp ξ c n ≫ (towerRingSystemExtensionIso ξ hsurj
        hsq e he n (𝟙 _)).hom) =
      (Space.smallEtaleSetRestriction B S hS (towerFibreIso ξ hsurj hsq e he n).hom
          (Space.isEtale_hom_of_iso B S hS _)).globalSectionMap
        ((Space.thickeningToposHom B S hS (towerFibre ξ hsurj hsq e he
            n)).inverseImage.globalSectionMap
          ((Space.smallEtaleRingedToposHom B S hS (towerLimitStructureMap ξ c
              n)).toToposHom.inverseImage.globalSectionMap τ ≫
            (sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ n).1) (forget
                CommRingCat.{u})).map (Space.structureSharpInverseImage B S hS
                (towerLimitStructureMap ξ c n)))) :=
  Space.globalSectionMap_comp_forget_map_thickenedBaseIso_inv_comp_etaleRestrictionRingComparison_α
    B S hS (towerStructureMap ξ 0) (schemeSpaceMap (c.ι.app 0)) (towerProblemBaseIso ξ hsurj hsq e
        cR hcR c eLimit hc) τ β (towerInclusion ξ n) (towerLimitStructureMap ξ c n)
    (towerInclusion_comp_towerLimitStructureMap ξ c n) (towerFibre ξ hsurj hsq e he n)
        (towerFibreIso ξ hsurj hsq e he n)
    (towerFibreIso_hom_comp_subspaceInclusion ξ hsurj hsq e he n) hβ

/-- **`gₙ^♯ c_m = g^♯ mₙ` on `Xₙ`**: the function `c_m` of `Y`, pulled back along
`gₙ : Xₙ ⟶ Yₙ ⟶ Y`, is the function `mₙ` of `Yₙ` pulled back along `g : Xₙ ⟶ Yₙ`, on underlying
sheaves of sets. -/
theorem globalSectionMap_towerLimitKernelFunction_comp_structureSharpInverseImage (n : ℕ)
    (m : ↑(limit (towerBaseKernelSystem ξ hsurj hsq e))) :
    (Space.smallEtaleRingedToposHom B S hS (towerLimitStructureMap ξ c
        n)).toToposHom.inverseImage.globalSectionMap (ringOneHom (Space.structureRingSheaf B S hS
        (schemeSpace c.pt)) ≫ (moduleSheafFunctor (Space.structureRingSheaf B S hS (schemeSpace
        c.pt))).map (Space.unitModuleMul B S hS (schemeSpace c.pt) (Space.globalFunctionsOfMap (𝟙
        (schemeSpace c.pt)) (towerLimitKernelFunction ξ hsurj hsq e cR hcR c eLimit hc m).1)) : ⊤_ _
        ⟶ (sheafCompose (Space.SmallEtale.topology B S hS (schemeSpace c.pt).1) (forget
        CommRingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (schemeSpace c.pt)).O) ≫
      (sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ n).1) (forget
          CommRingCat.{u})).map (Space.structureSharpInverseImage B S hS (towerLimitStructureMap ξ c
          n)) = ((ringOneHom (Space.structureRingSheaf B S hS (towerSpace ξ n)) ≫
          (moduleSheafFunctor (Space.structureRingSheaf B S hS (towerSpace ξ n))).map
          (Space.unitModuleMul B S hS (towerSpace ξ n) (Space.globalFunctionsOfMap
          (towerStructureMap ξ n) ((towerBaseKernelSystemObjIso ξ hsurj hsq e he n).hom (limit.π
          (towerBaseKernelSystem ξ hsurj hsq e) (op n) m)).1))) : ⊤_ _ ⟶ (sheafCompose
          (Space.SmallEtale.topology B S hS (towerSpace ξ n).1) (forget CommRingCat.{u})).obj
          (Space.smallEtaleRingedTopos B S hS (towerSpace ξ n)).O) :=
  (Space.ringOneHom_comp_map_unitModuleMul_globalFunctionsOfMap_eq B S hS (towerLimitStructureMap ξ
      c n) (towerLimitKernelFunction ξ hsurj hsq e cR hcR c eLimit hc m).1).symm.trans
    (congrArg (fun r => ringOneHom (Space.structureRingSheaf B S hS (towerSpace ξ n)) ≫
      (moduleSheafFunctor (Space.structureRingSheaf B S hS (towerSpace ξ n))).map
        (Space.unitModuleMul B S hS (towerSpace ξ n) r))
      ((Space.globalFunctionsOfMap_comp B S hS (towerStructureMap ξ n) (c.ι.app n)
          (towerLimitKernelFunction ξ hsurj hsq e cR hcR c eLimit hc m).1).trans
        (congrArg (Space.globalFunctionsOfMap (towerStructureMap ξ n))
          (Γ_map_towerLimitKernelFunction ξ @hsurj @hsq e @he cR hcR c eLimit hc n m))))

/-- `σ_m` included into `i⁻¹𝒪_Y`, read in the thickened base, is `i⁻¹c_m`. -/
theorem towerLimitKernelFunction_inclSheafSets_comp_forget_map_towerProblemBaseIso_hom (m : ↑(limit
    (towerBaseKernelSystem ξ hsurj hsq e))) :
    ((ringOneHom ((sheafCompose (Space.SmallEtale.topology B S hS (schemeSpace (towerBase ξ 0)).1)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (schemeSpace
        (towerBase ξ 0))).O) ≫ (moduleSheafFunctor ((sheafCompose (Space.SmallEtale.topology B S hS
        (schemeSpace (towerBase ξ 0)).1) (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (Space.smallEtaleRingedTopos B S hS (schemeSpace (towerBase ξ 0))).O)).map
        ((Space.modulePullbackGlobalSection B S hS (X := schemeSpace (towerBase ξ 0))
        (Space.rangeSpaceIso B S hS (c.ι.app 0) (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e
        cR hcR c eLimit hc).1).hom (Space.rangeConormalSection B S hS (c.ι.app 0)
        (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1
        (towerLimitKernelFunction ξ hsurj hsq e cR hcR c eLimit hc m))) ≫
        ((Space.modulePullbackIsoEtaleRestrictionModule B S hS (U := schemeSpace (towerBase ξ 0))
        (Space.rangeSpaceIso B S hS (c.ι.app 0) (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e
        cR hcR c eLimit hc).1).hom (Space.isEtale_hom_of_iso B S hS _)).app
        (Space.rangeConormalModule B S hS (c.ι.app 0) (isSquareZeroClosedImmersion_limitBase ξ hsurj
        hsq e cR hcR c eLimit hc).1)).hom : SheafOfModules.unit ((sheafCompose
        (Space.SmallEtale.topology B S hS (schemeSpace (towerBase ξ 0)).1) (forget₂ CommRingCat.{u}
        RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (schemeSpace (towerBase ξ 0))).O) ⟶
        limitBaseConormal ξ hsurj hsq e cR hcR c eLimit hc)) ≫ (limitBaseExtension ξ hsurj hsq e cR
        hcR c eLimit hc).inclSheafSets) ≫ (sheafCompose (Space.SmallEtale.topology B S hS
        (schemeSpace (towerBase ξ 0)).1)
      (forget CommRingCat.{u})).map (towerProblemBaseIso ξ hsurj hsq e cR hcR c eLimit hc).hom =
      (Space.smallEtaleRingedToposHom B S hS
        (schemeSpaceMap (c.ι.app 0))).toToposHom.inverseImage.globalSectionMap (ringOneHom
            (Space.structureRingSheaf B S hS (schemeSpace c.pt)) ≫ (moduleSheafFunctor
            (Space.structureRingSheaf B S hS (schemeSpace c.pt))).map (Space.unitModuleMul B S hS
            (schemeSpace c.pt) (Space.globalFunctionsOfMap (𝟙 (schemeSpace c.pt))
            (towerLimitKernelFunction ξ hsurj hsq e cR hcR c eLimit hc m).1)) : ⊤_ _ ⟶ (sheafCompose
            (Space.SmallEtale.topology B S hS (schemeSpace c.pt).1) (forget CommRingCat.{u})).obj
            (Space.smallEtaleRingedTopos B S hS (schemeSpace c.pt)).O) :=
  (congrArg (· ≫ (sheafCompose (Space.SmallEtale.topology B S hS (schemeSpace (towerBase ξ 0)).1)
      (forget CommRingCat.{u})).map (towerProblemBaseIso ξ hsurj hsq e cR hcR c eLimit hc).hom)
          ((Category.assoc _ _ _).trans
        (ringOneHom_comp_map_towerLimitKernelFunction_comp_limitBaseExtension_inclSheafSets ξ @hsurj
          @hsq e cR hcR c eLimit hc m))).trans
      (globalSectionMap_comp_forget_map_towerProblemBaseIso_hom ξ @hsurj @hsq e cR hcR c eLimit hc
        (ringOneHom (Space.structureRingSheaf B S hS (schemeSpace c.pt)) ≫ (moduleSheafFunctor
            (Space.structureRingSheaf B S hS (schemeSpace c.pt))).map (Space.unitModuleMul B S hS
            (schemeSpace c.pt) (Space.globalFunctionsOfMap (𝟙 (schemeSpace c.pt))
            (towerLimitKernelFunction ξ hsurj hsq e cR hcR c eLimit hc m).1)) : ⊤_ _ ⟶ (sheafCompose
            (Space.SmallEtale.topology B S hS (schemeSpace c.pt).1) (forget CommRingCat.{u})).obj
            (Space.smallEtaleRingedTopos B S hS (schemeSpace c.pt)).O))

/-- `gₙ^♯ c_m = g^♯ mₙ`, inside the restriction of the inverse image. -/
theorem globalSectionMap_towerLimitKernelFunction_comp_structureSharpInverseImage_eq (n : ℕ) (m :
    ↑(limit (towerBaseKernelSystem ξ hsurj hsq e))) :
    (Space.smallEtaleSetRestriction B S hS (towerFibreIso ξ hsurj hsq e he n).hom
        (Space.isEtale_hom_of_iso B S hS _)).globalSectionMap
        ((Space.thickeningToposHom B S hS (towerFibre ξ hsurj hsq e he
            n)).inverseImage.globalSectionMap
          ((Space.smallEtaleRingedToposHom B S hS (towerLimitStructureMap ξ c
              n)).toToposHom.inverseImage.globalSectionMap (ringOneHom (Space.structureRingSheaf B S
              hS (schemeSpace c.pt)) ≫ (moduleSheafFunctor (Space.structureRingSheaf B S hS
              (schemeSpace c.pt))).map (Space.unitModuleMul B S hS (schemeSpace c.pt)
              (Space.globalFunctionsOfMap (𝟙 (schemeSpace c.pt)) (towerLimitKernelFunction ξ hsurj
              hsq e cR hcR c eLimit hc m).1)) : ⊤_ _ ⟶ (sheafCompose (Space.SmallEtale.topology B S
              hS (schemeSpace c.pt).1) (forget CommRingCat.{u})).obj (Space.smallEtaleRingedTopos B
              S hS (schemeSpace c.pt)).O) ≫
            (sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ n).1) (forget
                CommRingCat.{u})).map (Space.structureSharpInverseImage B S hS
                (towerLimitStructureMap ξ c n)))) = ((Space.smallEtaleSetRestriction B S hS
                (towerFibreIso ξ hsurj hsq e he n).hom (Space.isEtale_hom_of_iso B S hS
                _)).globalSectionMap ((Space.thickeningToposHom B S hS (towerFibre ξ hsurj hsq e he
                n)).inverseImage.globalSectionMap ((ringOneHom (Space.structureRingSheaf B S hS
                (towerSpace ξ n)) ≫ (moduleSheafFunctor (Space.structureRingSheaf B S hS (towerSpace
                ξ n))).map (Space.unitModuleMul B S hS (towerSpace ξ n) (Space.globalFunctionsOfMap
                (towerStructureMap ξ n) ((towerBaseKernelSystemObjIso ξ hsurj hsq e he n).hom
                (limit.π (towerBaseKernelSystem ξ hsurj hsq e) (op n) m)).1))) : ⊤_ _ ⟶
                (sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ n).1) (forget
                CommRingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (towerSpace ξ n)).O))) :=
  congrArg (fun t => (Space.smallEtaleSetRestriction B S hS (towerFibreIso ξ hsurj hsq e he n).hom
          (Space.isEtale_hom_of_iso B S hS _)).globalSectionMap
          ((Space.thickeningToposHom B S hS (towerFibre ξ hsurj hsq e he
              n)).inverseImage.globalSectionMap t))
        (globalSectionMap_towerLimitKernelFunction_comp_structureSharpInverseImage ξ @hsurj @hsq e
          @he cR hcR c eLimit hc n m)

end AlgebraicGeometry.ProperFlatFibre

end
