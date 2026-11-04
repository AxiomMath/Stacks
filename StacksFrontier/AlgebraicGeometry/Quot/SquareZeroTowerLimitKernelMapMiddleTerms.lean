module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatDeformationMapGlobalSection
public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerExtensionSections
public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerLimitComparisonData
public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerLimitKernelFunctionComponents
public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerLimitKernelMapBaseFunctions
public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerLimitKernelMapBaseProjection
public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerLimitKernelMapIdealSide
public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerLimitKernelMapSets
public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerLimitKernelMapValues
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RestrictedFirstOrderExtensionSectionSets
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickenedBaseGlobalSectionSets

/-!
# The two sides of the computation of `φ` on `1 ⊗ m`, in the middle terms

In the situation of `AlgebraicGeometry.ProperFlatFibre.towerProblem` (body of the proof of
[Stacks Project, Tag 0D3X]): the left-hand side (the inverse image along `f` of `σ_m`, carried
by the base map to `𝒜` and projected to `Aₙ`) is the restriction along `X₀ ≅ g⁻¹(Y₀)` of the
inverse image of `g^♯mₙ`, hence equals the right-hand side, the image of `1 ⊗ mₙ` in `Aₙ`.

## Main results

* `globalSectionMap_towerLimitKernelFunction_comp_forget_map_towerLimitBaseMapApp_eq`: the base
  map on `f⁻¹σ_m` is the restriction of the inverse image of `gₙ^♯(gₙ⁻¹c_m)`.
* `globalSectionMap_towerLimitKernelFunction_comp_towerProblemLimitBaseMap_π`: the left-hand side
  is the restriction along `X₀ ≅ g⁻¹(Y₀)` of the inverse image of `g^♯mₙ`.
* `globalSectionMap_towerLimitKernelFunction_comp_towerProblemLimitBaseMap_π_eq`: the left-hand
  side equals the image of `1 ⊗ mₙ` in `Aₙ`.

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

/-- The base map on `f⁻¹σ_m`: the restriction of the inverse image of `gₙ^♯(gₙ⁻¹c_m)`. -/
theorem globalSectionMap_towerLimitKernelFunction_comp_forget_map_towerLimitBaseMapApp_eq (n : ℕ) (m
    : ↑(limit (towerBaseKernelSystem ξ hsurj hsq e))) :
    (Space.smallEtaleRingedToposHom B S hS (towerStructureMap ξ
        0)).toToposHom.inverseImage.globalSectionMap ((ringOneHom ((sheafCompose
        (Space.SmallEtale.topology B S hS (schemeSpace (towerBase ξ 0)).1) (forget₂ CommRingCat.{u}
        RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (schemeSpace (towerBase ξ 0))).O) ≫
        (moduleSheafFunctor ((sheafCompose (Space.SmallEtale.topology B S hS (schemeSpace (towerBase
        ξ 0)).1) (forget₂ CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS
        (schemeSpace (towerBase ξ 0))).O)).map ((Space.modulePullbackGlobalSection B S hS (X :=
        schemeSpace (towerBase ξ 0)) (Space.rangeSpaceIso B S hS (c.ι.app 0)
        (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1).hom
        (Space.rangeConormalSection B S hS (c.ι.app 0) (isSquareZeroClosedImmersion_limitBase ξ
        hsurj hsq e cR hcR c eLimit hc).1 (towerLimitKernelFunction ξ hsurj hsq e cR hcR c eLimit hc
        m))) ≫ ((Space.modulePullbackIsoEtaleRestrictionModule B S hS (U := schemeSpace (towerBase ξ
        0)) (Space.rangeSpaceIso B S hS (c.ι.app 0) (isSquareZeroClosedImmersion_limitBase ξ hsurj
        hsq e cR hcR c eLimit hc).1).hom (Space.isEtale_hom_of_iso B S hS _)).app
        (Space.rangeConormalModule B S hS (c.ι.app 0) (isSquareZeroClosedImmersion_limitBase ξ hsurj
        hsq e cR hcR c eLimit hc).1)).hom : SheafOfModules.unit ((sheafCompose
        (Space.SmallEtale.topology B S hS (schemeSpace (towerBase ξ 0)).1) (forget₂ CommRingCat.{u}
        RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (schemeSpace (towerBase ξ 0))).O) ⟶
        limitBaseConormal ξ hsurj hsq e cR hcR c eLimit hc)) ≫ (limitBaseExtension ξ hsurj hsq e cR
        hcR c eLimit hc).inclSheafSets) ≫ (sheafCompose (Space.SmallEtale.topology B S hS
        (towerSpace ξ 0).1) (forget CommRingCat.{u})).map ((Space.thickenedBaseIso B S hS
        (towerStructureMap ξ 0) (schemeSpaceMap (c.ι.app 0)) (towerProblemBaseIso ξ hsurj hsq e cR
        hcR c eLimit hc)).inv ≫ towerLimitBaseMapApp ξ c n ≫ (towerRingSystemExtensionIso ξ hsurj
        hsq e he n (𝟙 _)).hom) =
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
                (towerLimitStructureMap ξ c n)))) := by
  refine Eq.trans ?_
      ((globalSectionMap_comp_forget_map_thickenedBaseIso_inv_comp_towerLimitBaseMapApp ξ @hsurj
      @hsq
      e @he cR hcR c eLimit hc n _ (ringOneHom (Space.structureRingSheaf B S hS (schemeSpace c.pt))
          ≫ (moduleSheafFunctor (Space.structureRingSheaf B S hS (schemeSpace c.pt))).map
          (Space.unitModuleMul B S hS (schemeSpace c.pt) (Space.globalFunctionsOfMap (𝟙 (schemeSpace
          c.pt)) (towerLimitKernelFunction ξ hsurj hsq e cR hcR c eLimit hc m).1)) : ⊤_ _ ⟶
          (sheafCompose (Space.SmallEtale.topology B S hS (schemeSpace c.pt).1) (forget
          CommRingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (schemeSpace c.pt)).O)
          (towerLimitKernelFunction_inclSheafSets_comp_forget_map_towerProblemBaseIso_hom ξ @hsurj
          @hsq e cR hcR c eLimit hc m)).trans ?_)
  · exact congrArg₂ (· ≫ ·) rfl rfl
  · rfl

/-- **The left-hand side**: the inverse image along `f` of the class `σ_m`, read in `i⁻¹𝒪_Y`,
carried by the base map to `𝒜` and projected to `Aₙ`, is the restriction along `X₀ ≅ g⁻¹(Y₀)` of
the inverse image of the function `g^♯mₙ`. -/
theorem globalSectionMap_towerLimitKernelFunction_comp_towerProblemLimitBaseMap_π (n : ℕ)
    (m : ↑(limit (towerBaseKernelSystem ξ hsurj hsq e))) :
    (Space.smallEtaleRingedToposHom B S hS (towerStructureMap ξ
        0)).toToposHom.inverseImage.globalSectionMap ((ringOneHom ((sheafCompose
        (Space.SmallEtale.topology B S hS (schemeSpace (towerBase ξ 0)).1) (forget₂ CommRingCat.{u}
        RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (schemeSpace (towerBase ξ 0))).O) ≫
        (moduleSheafFunctor ((sheafCompose (Space.SmallEtale.topology B S hS (schemeSpace (towerBase
        ξ 0)).1) (forget₂ CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS
        (schemeSpace (towerBase ξ 0))).O)).map ((Space.modulePullbackGlobalSection B S hS (X :=
        schemeSpace (towerBase ξ 0)) (Space.rangeSpaceIso B S hS (c.ι.app 0)
        (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1).hom
        (Space.rangeConormalSection B S hS (c.ι.app 0) (isSquareZeroClosedImmersion_limitBase ξ
        hsurj hsq e cR hcR c eLimit hc).1 (towerLimitKernelFunction ξ hsurj hsq e cR hcR c eLimit hc
        m))) ≫ ((Space.modulePullbackIsoEtaleRestrictionModule B S hS (U := schemeSpace (towerBase ξ
        0)) (Space.rangeSpaceIso B S hS (c.ι.app 0) (isSquareZeroClosedImmersion_limitBase ξ hsurj
        hsq e cR hcR c eLimit hc).1).hom (Space.isEtale_hom_of_iso B S hS _)).app
        (Space.rangeConormalModule B S hS (c.ι.app 0) (isSquareZeroClosedImmersion_limitBase ξ hsurj
        hsq e cR hcR c eLimit hc).1)).hom : SheafOfModules.unit ((sheafCompose
        (Space.SmallEtale.topology B S hS (schemeSpace (towerBase ξ 0)).1) (forget₂ CommRingCat.{u}
        RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (schemeSpace (towerBase ξ 0))).O) ⟶
        limitBaseConormal ξ hsurj hsq e cR hcR c eLimit hc)) ≫ (limitBaseExtension ξ hsurj hsq e cR
        hcR c eLimit hc).inclSheafSets) ≫
      (sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1) (forget RingCat.{u})).map
          ((sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1) (forget₂
          CommRingCat.{u} RingCat.{u})).map ((towerProblemLimitBaseMap ξ c hsurj hsq e cR hcR eLimit
          hc) ≫ limit.π (towerRingSystem ξ) (op n) ≫ (towerRingSystemExtensionIso ξ hsurj hsq e he n
          (𝟙 _)).hom)) = ((Space.smallEtaleSetRestriction B S hS (towerFibreIso ξ hsurj hsq e he
          n).hom (Space.isEtale_hom_of_iso B S hS _)).globalSectionMap ((Space.thickeningToposHom B
          S hS (towerFibre ξ hsurj hsq e he n)).inverseImage.globalSectionMap ((ringOneHom
          (Space.structureRingSheaf B S hS (towerSpace ξ n)) ≫ (moduleSheafFunctor
          (Space.structureRingSheaf B S hS (towerSpace ξ n))).map (Space.unitModuleMul B S hS
          (towerSpace ξ n) (Space.globalFunctionsOfMap (towerStructureMap ξ n)
          ((towerBaseKernelSystemObjIso ξ hsurj hsq e he n).hom (limit.π (towerBaseKernelSystem ξ
          hsurj hsq e) (op n) m)).1))) : ⊤_ _ ⟶ (sheafCompose (Space.SmallEtale.topology B S hS
          (towerSpace ξ n).1) (forget CommRingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS
          (towerSpace ξ n)).O))) :=
  (globalSectionMap_towerLimitKernelFunction_comp_forget_map_forget₂_map_eq ξ @hsurj @hsq e @he cR
      hcR c eLimit hc n m).trans
      ((globalSectionMap_towerLimitKernelFunction_comp_forget_map_towerProblemLimitBaseMap_π_eq ξ
      @hsurj @hsq e @he cR hcR c eLimit hc n m).trans
      ((globalSectionMap_towerLimitKernelFunction_comp_forget_map_towerLimitBaseMapApp_eq ξ @hsurj
      @hsq e @he cR hcR c eLimit hc n m).trans
      (globalSectionMap_towerLimitKernelFunction_comp_structureSharpInverseImage_eq ξ @hsurj @hsq e
      @he cR hcR c eLimit hc n m)))

/-- **The hypothesis of the reduction, on the sections `1 ⊗ m`, as read in the middle terms**:
the inverse image along `f` of `σ_m` in `i⁻¹𝒪_Y`, carried to `𝒜` and projected to `Aₙ`, is the
image of `1 ⊗ mₙ` in `Aₙ`. -/
theorem globalSectionMap_towerLimitKernelFunction_comp_towerProblemLimitBaseMap_π_eq (n : ℕ)
    (m : ↑(limit (towerBaseKernelSystem ξ hsurj hsq e))) :
    (Space.smallEtaleRingedToposHom B S hS (towerStructureMap ξ
          0)).toToposHom.inverseImage.globalSectionMap
          ((ringOneHom ((sheafCompose (Space.SmallEtale.topology B S hS (schemeSpace (towerBase ξ
              0)).1) (forget₂ CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS
              (schemeSpace (towerBase ξ 0))).O) ≫ (moduleSheafFunctor ((sheafCompose
              (Space.SmallEtale.topology B S hS (schemeSpace (towerBase ξ 0)).1) (forget₂
              CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (schemeSpace
              (towerBase ξ 0))).O)).map ((Space.modulePullbackGlobalSection B S hS (X := schemeSpace
                  (towerBase ξ 0)) (Space.rangeSpaceIso B S hS (c.ι.app 0)
                  (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1).hom
                  (Space.rangeConormalSection B S hS (c.ι.app 0)
                  (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1
                  (towerLimitKernelFunction ξ hsurj hsq e cR hcR c eLimit hc m))) ≫
                  ((Space.modulePullbackIsoEtaleRestrictionModule B S hS (U := schemeSpace
                  (towerBase ξ 0)) (Space.rangeSpaceIso B S hS (c.ι.app 0)
                  (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1).hom
                  (Space.isEtale_hom_of_iso B S hS _)).app (Space.rangeConormalModule B S hS
                  (c.ι.app 0) (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit
                  hc).1)).hom : SheafOfModules.unit ((sheafCompose (Space.SmallEtale.topology B S hS
                  (schemeSpace (towerBase ξ 0)).1) (forget₂ CommRingCat.{u} RingCat.{u})).obj
                  (Space.smallEtaleRingedTopos B S hS (schemeSpace (towerBase ξ 0))).O) ⟶
                  limitBaseConormal ξ hsurj hsq e cR hcR c eLimit hc)) ≫ (limitBaseExtension ξ hsurj
                  hsq e cR hcR c eLimit
              hc).inclSheafSets) ≫
        (sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1) (forget
            RingCat.{u})).map
          ((sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1) (forget₂
              CommRingCat.{u} RingCat.{u})).map
            (towerProblemLimitBaseMap ξ c hsurj hsq e cR hcR eLimit hc ≫
              limit.π (towerRingSystem ξ) (op n) ≫
              (towerRingSystemExtensionIso ξ hsurj hsq e he n (𝟙 _)).hom)) =
      ringOneHom ((sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1) (forget₂
        CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (towerSpace ξ 0)).O)
        ≫ (moduleSheafFunctor ((sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (towerSpace
        ξ 0)).O)).map (Space.baseRingTensorSection B S hS (towerSpace ξ 0) (Space.baseRingHomOfMap
            (towerStructureMap ξ 0)) _ (limit.π (towerBaseKernelSystem ξ hsurj hsq e) (op n) m) ≫
            (towerIdealSystemObjIso ξ hsurj hsq e he n).hom) ≫ (towerExtension ξ hsurj hsq e he n (𝟙
            _)).inclSheafSets :=
  (globalSectionMap_towerLimitKernelFunction_comp_towerProblemLimitBaseMap_π ξ @hsurj @hsq e @he cR
    hcR c eLimit hc n m).trans
    (ringOneHom_comp_map_baseRingTensorSection_comp_towerIdealSystemObjIso_hom_comp_inclSheafSets ξ
      @hsurj @hsq e @he n m).symm

end AlgebraicGeometry.ProperFlatFibre

end
