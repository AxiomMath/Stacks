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
# The base map of the tower problem followed by the projections, on sheaves of sets

In the situation of `AlgebraicGeometry.ProperFlatFibre.towerProblem` (body of the proof of
[Stacks Project, Tag 0D3X]): the base map followed by the `n`-th projection and `Aₙ ≅ 𝒪'ₙ` is
the thickened base followed by `(f ≫ i)⁻¹𝒪_Y ⟶ aₙ⁻¹𝒪_{Xₙ}`, and its value on `f⁻¹σ_m`, on
underlying sheaves of sets.

## Main results

* `towerProblemLimitBaseMap_comp_π_comp_towerRingSystemExtensionIso_hom`: the base map followed
  by the `n`-th projection and `Aₙ ≅ 𝒪'ₙ` is the thickened base followed by
  `(f ≫ i)⁻¹𝒪_Y ⟶ aₙ⁻¹𝒪_{Xₙ}`.
* `globalSectionMap_towerLimitKernelFunction_comp_forget_map_forget₂_map_eq`: the ring map
  `𝒜 ⟶ Aₙ` on underlying sheaves of sets, read through the sheaves of rings.
* `forget_map_towerProblemLimitBaseMap_comp_π_comp_towerRingSystemExtensionIso_hom`: the same
  identity of the base map on underlying sheaves of sets.
* `globalSectionMap_towerLimitKernelFunction_comp_forget_map_towerProblemLimitBaseMap_π_eq`: the
  base map followed by the `n`-th projection, applied to `f⁻¹σ_m`, through the thickened base.

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

/-- The base map followed by the `n`-th projection and `Aₙ ≅ 𝒪'ₙ` is the thickened base followed
by `(f ≫ i)⁻¹𝒪_Y ⟶ aₙ⁻¹𝒪_{Xₙ}`. -/
theorem towerProblemLimitBaseMap_comp_π_comp_towerRingSystemExtensionIso_hom (n : ℕ) :
    (towerProblemLimitBaseMap ξ c hsurj hsq e cR hcR eLimit hc) ≫ limit.π (towerRingSystem ξ) (op n)
        ≫ (towerRingSystemExtensionIso ξ hsurj hsq e he n (𝟙 _)).hom =
      (Space.thickenedBaseIso B S hS (towerStructureMap ξ 0) (schemeSpaceMap (c.ι.app 0))
          (towerProblemBaseIso ξ hsurj hsq e cR hcR c eLimit hc)).inv ≫ towerLimitBaseMapApp ξ c n ≫
          (towerRingSystemExtensionIso ξ hsurj hsq e he n (𝟙 _)).hom :=
  (Category.assoc (Space.thickenedBaseIso B S hS (towerStructureMap ξ 0) (schemeSpaceMap (c.ι.app
      0)) (towerProblemBaseIso ξ hsurj hsq e cR hcR c eLimit hc)).inv (towerLimitBaseLift ξ c)
      (limit.π (towerRingSystem ξ) (op n) ≫ (towerRingSystemExtensionIso ξ hsurj hsq e he n (𝟙
      _)).hom)).trans
    (congrArg ((Space.thickenedBaseIso B S hS (towerStructureMap ξ 0) (schemeSpaceMap (c.ι.app 0))
        (towerProblemBaseIso ξ hsurj hsq e cR hcR c eLimit hc)).inv ≫ ·) (limit.lift_π_assoc
        (towerLimitBaseCone ξ c) (op n) (towerRingSystemExtensionIso ξ hsurj hsq e he n (𝟙 _)).hom))

/-- The ring map `𝒜 ⟶ Aₙ` on underlying sheaves of sets, read through the sheaves of rings. -/
theorem globalSectionMap_towerLimitKernelFunction_comp_forget_map_forget₂_map_eq (n : ℕ) (m :
    ↑(limit (towerBaseKernelSystem ξ hsurj hsq e))) :
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
          (𝟙 _)).hom)) =
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
        (towerSpace ξ 0).1) (forget CommRingCat.{u})).map ((towerProblemLimitBaseMap ξ c hsurj hsq e
        cR hcR eLimit hc) ≫ limit.π (towerRingSystem ξ) (op n) ≫ (towerRingSystemExtensionIso ξ
        hsurj hsq e he n (𝟙 _)).hom) := rfl

/-- On underlying sheaves of sets, the base map followed by the `n`-th projection and
`Aₙ ≅ 𝒪'ₙ` is the thickened base followed by `(f ≫ i)⁻¹𝒪_Y ⟶ aₙ⁻¹𝒪_{Xₙ}`. -/
theorem forget_map_towerProblemLimitBaseMap_comp_π_comp_towerRingSystemExtensionIso_hom (n : ℕ) :
    (sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1) (forget
        CommRingCat.{u})).map ((towerProblemLimitBaseMap ξ c hsurj hsq e cR hcR eLimit hc) ≫ limit.π
        (towerRingSystem ξ) (op n) ≫ (towerRingSystemExtensionIso ξ hsurj hsq e he n (𝟙 _)).hom) =
      (sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1) (forget
          CommRingCat.{u})).map ((Space.thickenedBaseIso B S hS (towerStructureMap ξ 0)
          (schemeSpaceMap (c.ι.app 0)) (towerProblemBaseIso ξ hsurj hsq e cR hcR c eLimit hc)).inv ≫
          towerLimitBaseMapApp ξ c n ≫ (towerRingSystemExtensionIso ξ hsurj hsq e he n (𝟙 _)).hom)
          :=
  congrArg (sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1) (forget
      CommRingCat.{u})).map (towerProblemLimitBaseMap_comp_π_comp_towerRingSystemExtensionIso_hom ξ
      @hsurj @hsq e @he cR
        hcR c eLimit hc n)

/-- The base map followed by the `n`-th projection, applied to `f⁻¹σ_m`, through the thickened
base. -/
theorem globalSectionMap_towerLimitKernelFunction_comp_forget_map_towerProblemLimitBaseMap_π_eq (n :
    ℕ) (m : ↑(limit (towerBaseKernelSystem ξ hsurj hsq e))) :
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
        (towerSpace ξ 0).1) (forget CommRingCat.{u})).map ((towerProblemLimitBaseMap ξ c hsurj hsq e
        cR hcR eLimit hc) ≫ limit.π (towerRingSystem ξ) (op n) ≫ (towerRingSystemExtensionIso ξ
        hsurj hsq e he n (𝟙 _)).hom) =
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
        hsq e he n (𝟙 _)).hom) :=
  congrArg₂ (· ≫ ·) rfl
      (forget_map_towerProblemLimitBaseMap_comp_π_comp_towerRingSystemExtensionIso_hom ξ @hsurj @hsq
      e @he cR hcR c eLimit hc n)

end AlgebraicGeometry.ProperFlatFibre

end
