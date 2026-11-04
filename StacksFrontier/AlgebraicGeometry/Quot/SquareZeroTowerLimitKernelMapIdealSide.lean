module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatDeformationMapGlobalSection
public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerExtensionSections
public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerLimitComparisonData
public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerLimitKernelFunctionComponents
public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerLimitKernelMapSets
public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerLimitKernelMapValues
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RestrictedFirstOrderExtensionSectionSets
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickenedBaseGlobalSectionSets

/-!
# The sections `1 ⊗ mₙ` of the ideals of the tower extensions, on sheaves of sets

In the situation of `AlgebraicGeometry.ProperFlatFibre.towerProblem` (body of the proof of
[Stacks Project, Tag 0D3X]), the right-hand side of the computation of
`φ = towerLimitKernelMap` on the sections `1 ⊗ m`: the section `1 ⊗ mₙ` of the ideal
`𝒪_{X₀} ⊗ Iₙ` of `0 → 𝒪_{X₀} ⊗ Iₙ → 𝒪_{Xₙ} → 𝒪_{X₀} → 0`, read in the middle term `Aₙ`, is the
restriction along `X₀ ≅ g⁻¹(Y₀)` of the inverse image of the function `g^♯mₙ`.

All names below are in the namespace `AlgebraicGeometry.ProperFlatFibre`.

## Main results

* `ringOneHom_comp_map_baseRingTensorSection_comp_towerExtensionIdealIso_inv_comp_inclSheafSets`:
  for `m ∈ Iₙ`, the section `1 ⊗ m` of the ideal of the `n`-th extension, included into `Aₙ`, is
  the restriction along `X₀ ≅ g⁻¹(Y₀)` of the inverse image of the function `g^♯m`.
* `baseRingTensorSection_comp_towerIdealSystemObjIso_hom`: the section `1 ⊗ mₙ`, read in the ideal
  of the `n`-th extension, is `1 ⊗ mₙ` read through `towerExtensionIdealIso`.
* `moduleSheafFunctor_map_baseRingTensorSection_comp_towerIdealSystemObjIso_hom`: the same identity
  under the module sheaf functor.
* `ringOneHom_comp_map_towerIdealSystemObjIso_hom_comp_inclSheafSets_eq`: the same identity after
  the unit section and the inclusion of the ideal into `Aₙ`.
* `ringOneHom_comp_map_baseRingTensorSection_towerBaseKernelSystemObjIso_comp_inclSheafSets`: the
  first result at the identity map and the section `mₙ`.
* `ringOneHom_comp_map_baseRingTensorSection_comp_towerIdealSystemObjIso_hom_comp_inclSheafSets`:
  the section `1 ⊗ mₙ` of `𝒪_{X₀} ⊗ Iₙ`, in the middle term `Aₙ`, is the restriction along
  `X₀ ≅ g⁻¹(Y₀)` of the inverse image of the function `g^♯mₙ`.

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

/-- Postcomposition along the isomorphism `towerFibreIso` is a continuous functor of small
étale sites. -/
local instance instIsContinuousSmallEtalePostcompTowerFibreIsoKernelMapFunctions (n : ℕ) :
    (Space.smallEtalePostcomp B S hS (towerFibreIso ξ hsurj hsq e he n).hom
    (Space.isEtale_hom_of_iso B S hS _)).IsContinuous
    (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1)
    (Space.SmallEtale.topology B S hS (towerFibreSpace ξ hsurj hsq e he n).1) :=
  Space.smallEtalePostcomp_isContinuous B S hS _ _

/-- Postcomposition along the isomorphism `limitBaseRangeIso` is a continuous functor of small
étale sites. -/
local instance instIsContinuousSmallEtalePostcompLimitBaseRangeIsoKernelMapFunctions :
    (Space.smallEtalePostcomp B S hS (limitBaseRangeIso ξ hsurj hsq e cR hcR c eLimit hc).hom
    (Space.isEtale_hom_of_iso B S hS _)).IsContinuous
    (Space.SmallEtale.topology B S hS (schemeSpace (towerBase ξ 0)).1)
    (Space.SmallEtale.topology B S hS (⟨(limitBaseSubspace ξ hsurj hsq e cR hcR c eLimit
        hc).1.toFunctor, (limitBaseSubspace ξ hsurj hsq e cR hcR c eLimit hc).2.1⟩ : AlgebraicSpaces
        B S hS).1) :=
  Space.smallEtalePostcomp_isContinuous B S hS _ _

/-- **The section `1 ⊗ m` of the ideal of the `n`-th tower extension, on sheaves of sets**: for
`m ∈ Iₙ = Ker(Γ(Yₙ) → Γ(Y₀))`, the unit section followed by `1 ⊗ m` (read through
`AlgebraicGeometry.ProperFlatFibre.towerExtensionIdealIso`) and the inclusion of the ideal into
`Aₙ` is the restriction along `X₀ ≅ g⁻¹(Y₀)` of the inverse image of the function `g^♯m` of
`Xₙ`. -/
theorem ringOneHom_comp_map_baseRingTensorSection_comp_towerExtensionIdealIso_inv_comp_inclSheafSets
    (n : ℕ) {Y : AlgebraicSpaces B S hS} (h : towerSpace ξ n ⟶ Y) (x : RingHom.ker (Scheme.Γ.map
        ((BigFppfOver.toScheme B S hS).map ((ξ ⋙ cartesianProperFlatProjection B S hS).map (homOfLE
        (Nat.zero_le n)))).op).hom) :
    ringOneHom ((sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1) (forget₂
        CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (towerSpace ξ 0)).O) ≫
        (moduleSheafFunctor ((sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (towerSpace ξ
        0)).O)).map
        (Space.baseRingTensorSection B S hS (towerSpace ξ 0)
          (Space.baseRingHomOfMap (towerStructureMap ξ 0)) (RingHom.squareZeroKer _
              (surjective_and_ker_sq_eq_bot_towerBase_map ξ hsurj hsq e he (homOfLE (Nat.zero_le
              n))).1 (surjective_and_ker_sq_eq_bot_towerBase_map ξ hsurj hsq e he (homOfLE
              (Nat.zero_le n))).2) x ≫
          (towerExtensionIdealIso ξ hsurj hsq e he n).inv) ≫
      (towerExtension ξ hsurj hsq e he n h).inclSheafSets =
    (Space.smallEtaleSetRestriction B S hS (towerFibreIso ξ hsurj hsq e he n).hom
        (Space.isEtale_hom_of_iso B S hS _)).globalSectionMap
      ((Space.thickeningToposHom B S hS (towerFibre ξ hsurj hsq e he
          n)).inverseImage.globalSectionMap
        (ringOneHom (Space.structureRingSheaf B S hS (towerSpace ξ n)) ≫
          (moduleSheafFunctor (Space.structureRingSheaf B S hS (towerSpace ξ n))).map
            (Space.unitModuleMul B S hS (towerSpace ξ n)
              (Space.globalFunctionsOfMap (towerStructureMap ξ n) x.1)) :
          ⊤_ _ ⟶ (sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ n).1) (forget
              CommRingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (towerSpace ξ n)).O)) := by
  have hG := (Space.ringOneHom_comp_map_comp_castBase_restrictedFirstOrderExtension_inclSheafSets B
      S hS (towerFibre ξ hsurj hsq e he n)
    (isFirstOrderThickening_towerFibre ξ hsurj hsq e he n) (towerFibreIso ξ hsurj hsq e he n) h
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ h)
      (towerFibreIso_hom_comp_subspaceInclusion ξ hsurj hsq e he n)))
    (Space.preimageIdealSection B S hS (towerStructureMap ξ n)
      (Space.rangeSubspace B S hS _ (isClosedImmersion_towerBase_map ξ hsurj hsq e he
        (homOfLE (Nat.zero_le n))))
      ⟨x.1, (Space.closedSubspaceBaseIdeal_rangeSubspace B S hS _
        (isClosedImmersion_towerBase_map ξ hsurj hsq e he
          (homOfLE (Nat.zero_le n)))).symm ▸ x.2⟩)
    (Space.preimageIdealSection_ι B S hS (towerStructureMap ξ n)
      (Space.rangeSubspace B S hS _ (isClosedImmersion_towerBase_map ξ hsurj hsq e he
        (homOfLE (Nat.zero_le n))))
      ⟨x.1, (Space.closedSubspaceBaseIdeal_rangeSubspace B S hS _
        (isClosedImmersion_towerBase_map ξ hsurj hsq e he
          (homOfLE (Nat.zero_le n)))).symm ▸ x.2⟩))
  refine Eq.trans ?_ (hG.trans ?_)
  · refine congrArg₂ (· ≫ ·) rfl (congrArg₂ (· ≫ ·) ?_ rfl)
    refine congrArg _ ((baseRingTensorSection_towerExtensionIdealIso_inv ξ @hsurj @hsq e @he n
        x).trans ?_)
    refine congrArg₂ (· ≫ ·) ?_ rfl
    exact rfl
  · exact rfl

/-- The section `1 ⊗ mₙ`, read in the ideal of the `n`-th extension, is `1 ⊗ mₙ` read through
`AlgebraicGeometry.ProperFlatFibre.towerExtensionIdealIso`. -/
theorem baseRingTensorSection_comp_towerIdealSystemObjIso_hom (n : ℕ)
    (m : ↑(limit (towerBaseKernelSystem ξ hsurj hsq e))) :
    (Space.baseRingTensorSection B S hS (towerSpace ξ 0) (Space.baseRingHomOfMap (towerStructureMap
        ξ 0)) _ (limit.π (towerBaseKernelSystem ξ hsurj hsq e) (op n) m) ≫ (towerIdealSystemObjIso ξ
        hsurj hsq e he n).hom) = Space.baseRingTensorSection B S hS (towerSpace ξ 0)
        (Space.baseRingHomOfMap (towerStructureMap ξ 0)) (RingHom.squareZeroKer _
            (surjective_and_ker_sq_eq_bot_towerBase_map ξ hsurj hsq e he (homOfLE (Nat.zero_le
            n))).1 (surjective_and_ker_sq_eq_bot_towerBase_map ξ hsurj hsq e he (homOfLE
            (Nat.zero_le n))).2) ((towerBaseKernelSystemObjIso ξ hsurj hsq e he n).hom (limit.π
            (towerBaseKernelSystem ξ hsurj hsq e) (op n) m)) ≫
      (towerExtensionIdealIso ξ hsurj hsq e he n).inv :=
  have h5 : (towerIdealSystemObjIso ξ hsurj hsq e he n).hom =
      ((Space.baseRingTensorModule B S hS (towerSpace ξ 0)
        (Space.baseRingHomOfMap (towerStructureMap ξ 0))).mapIso
        (towerBaseKernelSystemObjIso ξ hsurj hsq e he n) ≪≫
          (towerExtensionIdealIso ξ hsurj hsq e he n).symm).hom := rfl
  have h6 : ((Space.baseRingTensorModule B S hS (towerSpace ξ 0)
        (Space.baseRingHomOfMap (towerStructureMap ξ 0))).mapIso
        (towerBaseKernelSystemObjIso ξ hsurj hsq e he n) ≪≫
          (towerExtensionIdealIso ξ hsurj hsq e he n).symm).hom =
      (Space.baseRingTensorModule B S hS (towerSpace ξ 0)
        (Space.baseRingHomOfMap (towerStructureMap ξ 0))).map
        (towerBaseKernelSystemObjIso ξ hsurj hsq e he n).hom ≫
          (towerExtensionIdealIso ξ hsurj hsq e he n).inv :=
    (Iso.trans_hom _ _).trans (congrArg₂ (· ≫ ·) (Functor.mapIso_hom _ _) (Iso.symm_hom _))
  (congrArg (Space.baseRingTensorSection B S hS (towerSpace ξ 0)
      (Space.baseRingHomOfMap (towerStructureMap ξ 0)) ((towerBaseKernelSystem ξ hsurj hsq e).obj
          (op n))
      (limit.π (towerBaseKernelSystem ξ hsurj hsq e) (op n) m) ≫ ·) (h5.trans h6)).trans
  ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ (towerExtensionIdealIso ξ hsurj hsq e he n).inv)
      (Space.baseRingTensorSection_map B S hS (towerSpace ξ 0)
        (Space.baseRingHomOfMap (towerStructureMap ξ 0))
        (towerBaseKernelSystemObjIso ξ hsurj hsq e he n).hom
        (limit.π (towerBaseKernelSystem ξ hsurj hsq e) (op n) m))))

/-- `AlgebraicGeometry.ProperFlatFibre.baseRingTensorSection_comp_towerIdealSystemObjIso_hom`
under the module sheaf functor. -/
theorem moduleSheafFunctor_map_baseRingTensorSection_comp_towerIdealSystemObjIso_hom (n : ℕ)
    (m : ↑(limit (towerBaseKernelSystem ξ hsurj hsq e))) :
    (moduleSheafFunctor ((sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (towerSpace ξ
        0)).O)).map (Space.baseRingTensorSection B S hS (towerSpace ξ 0) (Space.baseRingHomOfMap
        (towerStructureMap ξ 0)) _ (limit.π (towerBaseKernelSystem ξ hsurj hsq e) (op n) m) ≫
        (towerIdealSystemObjIso ξ hsurj hsq e he n).hom) = (moduleSheafFunctor ((sheafCompose
        (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1) (forget₂ CommRingCat.{u}
        RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (towerSpace ξ 0)).O)).map
        (Space.baseRingTensorSection B S hS (towerSpace ξ 0)
          (Space.baseRingHomOfMap (towerStructureMap ξ 0)) (RingHom.squareZeroKer _
              (surjective_and_ker_sq_eq_bot_towerBase_map ξ hsurj hsq e he (homOfLE (Nat.zero_le
              n))).1 (surjective_and_ker_sq_eq_bot_towerBase_map ξ hsurj hsq e he (homOfLE
              (Nat.zero_le n))).2) ((towerBaseKernelSystemObjIso ξ hsurj hsq e he n).hom (limit.π
              (towerBaseKernelSystem ξ hsurj hsq e) (op n) m)) ≫
          (towerExtensionIdealIso ξ hsurj hsq e he n).inv) :=
  congrArg (moduleSheafFunctor ((sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (towerSpace ξ
      0)).O)).map
    (baseRingTensorSection_comp_towerIdealSystemObjIso_hom ξ @hsurj @hsq e @he n m)

/-- The section `1 ⊗ mₙ` of the ideal of the `n`-th extension, included into `Aₙ`, read through
`AlgebraicGeometry.ProperFlatFibre.towerExtensionIdealIso`. -/
theorem ringOneHom_comp_map_towerIdealSystemObjIso_hom_comp_inclSheafSets_eq
    (n : ℕ) (m : ↑(limit (towerBaseKernelSystem ξ hsurj hsq e))) :
    ringOneHom ((sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1) (forget₂
        CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (towerSpace ξ 0)).O) ≫
        (moduleSheafFunctor ((sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (towerSpace ξ
        0)).O)).map (Space.baseRingTensorSection B S hS (towerSpace ξ 0) (Space.baseRingHomOfMap
        (towerStructureMap ξ 0)) _ (limit.π (towerBaseKernelSystem ξ hsurj hsq e) (op n) m) ≫
        (towerIdealSystemObjIso ξ hsurj hsq e he n).hom) ≫
      (towerExtension ξ hsurj hsq e he n (𝟙 _)).inclSheafSets =
    ringOneHom ((sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1) (forget₂
        CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (towerSpace ξ 0)).O) ≫
        (moduleSheafFunctor ((sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (towerSpace ξ
        0)).O)).map (Space.baseRingTensorSection B S hS (towerSpace ξ 0)
          (Space.baseRingHomOfMap (towerStructureMap ξ 0)) (RingHom.squareZeroKer _
              (surjective_and_ker_sq_eq_bot_towerBase_map ξ hsurj hsq e he (homOfLE (Nat.zero_le
              n))).1 (surjective_and_ker_sq_eq_bot_towerBase_map ξ hsurj hsq e he (homOfLE
              (Nat.zero_le n))).2) ((towerBaseKernelSystemObjIso ξ hsurj hsq e he n).hom (limit.π
              (towerBaseKernelSystem ξ hsurj hsq e) (op n) m)) ≫
          (towerExtensionIdealIso ξ hsurj hsq e he n).inv) ≫
      (towerExtension ξ hsurj hsq e he n (𝟙 _)).inclSheafSets :=
  congrArg (fun φ => ringOneHom ((sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (towerSpace ξ
      0)).O) ≫ φ ≫ (towerExtension ξ hsurj hsq e he n (𝟙 _)).inclSheafSets)
    (moduleSheafFunctor_map_baseRingTensorSection_comp_towerIdealSystemObjIso_hom ξ @hsurj @hsq e
        @he
      n m)

/-- For `m` in the limit of the kernels, the section `1 ⊗ mₙ` of the ideal of the `n`-th extension
(read through `AlgebraicGeometry.ProperFlatFibre.towerExtensionIdealIso`), included into `Aₙ`,
is the restriction along `X₀ ≅ g⁻¹(Y₀)` of the inverse image of the function `g^♯mₙ`. -/
theorem ringOneHom_comp_map_baseRingTensorSection_towerBaseKernelSystemObjIso_comp_inclSheafSets
    (n : ℕ) (m : ↑(limit (towerBaseKernelSystem ξ hsurj hsq e))) :
    ringOneHom ((sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1) (forget₂
        CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (towerSpace ξ 0)).O) ≫
        (moduleSheafFunctor ((sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (towerSpace ξ
        0)).O)).map (Space.baseRingTensorSection B S hS (towerSpace ξ 0)
          (Space.baseRingHomOfMap (towerStructureMap ξ 0)) (RingHom.squareZeroKer _
              (surjective_and_ker_sq_eq_bot_towerBase_map ξ hsurj hsq e he (homOfLE (Nat.zero_le
              n))).1 (surjective_and_ker_sq_eq_bot_towerBase_map ξ hsurj hsq e he (homOfLE
              (Nat.zero_le n))).2) ((towerBaseKernelSystemObjIso ξ hsurj hsq e he n).hom (limit.π
              (towerBaseKernelSystem ξ hsurj hsq e) (op n) m)) ≫
          (towerExtensionIdealIso ξ hsurj hsq e he n).inv) ≫
      (towerExtension ξ hsurj hsq e he n (𝟙 _)).inclSheafSets = ((Space.smallEtaleSetRestriction B S
          hS (towerFibreIso ξ hsurj hsq e he n).hom (Space.isEtale_hom_of_iso B S hS
          _)).globalSectionMap ((Space.thickeningToposHom B S hS (towerFibre ξ hsurj hsq e he
          n)).inverseImage.globalSectionMap ((ringOneHom (Space.structureRingSheaf B S hS
          (towerSpace ξ n)) ≫ (moduleSheafFunctor (Space.structureRingSheaf B S hS (towerSpace ξ
          n))).map (Space.unitModuleMul B S hS (towerSpace ξ n) (Space.globalFunctionsOfMap
          (towerStructureMap ξ n) ((towerBaseKernelSystemObjIso ξ hsurj hsq e he n).hom (limit.π
          (towerBaseKernelSystem ξ hsurj hsq e) (op n) m)).1))) : ⊤_ _ ⟶ (sheafCompose
          (Space.SmallEtale.topology B S hS (towerSpace ξ n).1) (forget CommRingCat.{u})).obj
          (Space.smallEtaleRingedTopos B S hS (towerSpace ξ n)).O))) :=
  ringOneHom_comp_map_baseRingTensorSection_comp_towerExtensionIdealIso_inv_comp_inclSheafSets ξ
    @hsurj @hsq e @he n (𝟙 _) ((towerBaseKernelSystemObjIso ξ hsurj hsq e he n).hom (limit.π
        (towerBaseKernelSystem ξ hsurj hsq e) (op n) m))

/-- **The right-hand side**: the section `1 ⊗ mₙ` of `𝒪_{X₀} ⊗ Iₙ`, in the middle term `Aₙ`, is
the restriction along `X₀ ≅ g⁻¹(Y₀)` of the inverse image of the function `g^♯mₙ`. -/
theorem ringOneHom_comp_map_baseRingTensorSection_comp_towerIdealSystemObjIso_hom_comp_inclSheafSets
    (n : ℕ) (m : ↑(limit (towerBaseKernelSystem ξ hsurj hsq e))) :
    ringOneHom ((sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1) (forget₂
        CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (towerSpace ξ 0)).O) ≫
        (moduleSheafFunctor ((sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (towerSpace ξ
        0)).O)).map (Space.baseRingTensorSection B S hS (towerSpace ξ 0) (Space.baseRingHomOfMap
        (towerStructureMap ξ 0)) _ (limit.π (towerBaseKernelSystem ξ hsurj hsq e) (op n) m) ≫
        (towerIdealSystemObjIso ξ hsurj hsq e he n).hom) ≫
      (towerExtension ξ hsurj hsq e he n (𝟙 _)).inclSheafSets = ((Space.smallEtaleSetRestriction B S
          hS (towerFibreIso ξ hsurj hsq e he n).hom (Space.isEtale_hom_of_iso B S hS
          _)).globalSectionMap ((Space.thickeningToposHom B S hS (towerFibre ξ hsurj hsq e he
          n)).inverseImage.globalSectionMap ((ringOneHom (Space.structureRingSheaf B S hS
          (towerSpace ξ n)) ≫ (moduleSheafFunctor (Space.structureRingSheaf B S hS (towerSpace ξ
          n))).map (Space.unitModuleMul B S hS (towerSpace ξ n) (Space.globalFunctionsOfMap
          (towerStructureMap ξ n) ((towerBaseKernelSystemObjIso ξ hsurj hsq e he n).hom (limit.π
          (towerBaseKernelSystem ξ hsurj hsq e) (op n) m)).1))) : ⊤_ _ ⟶ (sheafCompose
          (Space.SmallEtale.topology B S hS (towerSpace ξ n).1) (forget CommRingCat.{u})).obj
          (Space.smallEtaleRingedTopos B S hS (towerSpace ξ n)).O))) :=
  (ringOneHom_comp_map_towerIdealSystemObjIso_hom_comp_inclSheafSets_eq ξ
    @hsurj @hsq e @he n m).trans
    (ringOneHom_comp_map_baseRingTensorSection_towerBaseKernelSystemObjIso_comp_inclSheafSets ξ
      @hsurj @hsq e @he n m)

end AlgebraicGeometry.ProperFlatFibre

end
