module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatDeformationMapGlobalSection
public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerExtensionSections
public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerLimitComparisonData
public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerLimitKernelFunctionComponents
public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerLimitKernelMapMiddleTerms
public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerLimitKernelMapSets
public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerLimitKernelMapValues
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RestrictedFirstOrderExtensionSectionSets
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickenedBaseGlobalSectionSets

/-!
# The values of `φ` on the sections `1 ⊗ m`, computed

In the situation of `AlgebraicGeometry.ProperFlatFibre.towerProblem`, the map
`φ = towerLimitKernelMap : f^*𝒞_{Y₀/Y} ⟶ lim 𝒪_{X₀} ⊗ Iₙ` of the body of the proof of
[Stacks Project, Tag 0D3X] carries the section `1 ⊗ m` of `𝒪_{X₀} ⊗ lim Iₙ` (read in `f^*𝒞_{Y₀/Y}`)
to the family of sections `1 ⊗ mₙ`. The two sides are read in the middle terms `𝒪_{Xₙ}` in
`StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerLimitKernelMapMiddleTerms`.
This discharges the hypothesis of
`AlgebraicGeometry.ProperFlatFibre.towerProblem_limitComparison_data`.

## Main results

All in the namespace `AlgebraicGeometry.ProperFlatFibre`:

* `modulePullbackGlobalSection_comp_towerLimitKernelMap_π_of_sets_unitModule`: the value of `φ`
  on a pulled-back global section, for a target section with source `Space.unitModule`.
* `baseRingTensorSection_comp_towerProblemKernelIso_inv_comp_towerLimitKernelMap_π_of_eq`: the
  value of `φ` on `1 ⊗ m`, for sections given by equations.
* `baseRingTensorSection_comp_towerProblemKernelIso_inv_comp_towerLimitKernelMap_π`: `φ` carries
  `1 ⊗ m` to the family of sections `1 ⊗ mₙ`.
* `towerProblem_limitComparison`: `φ` factors as `α ≫ (𝒪_{X₀} ⊗ lim Iₙ ⟶ lim 𝒪_{X₀} ⊗ Iₙ) ≫ β`
  with `α` and `β` isomorphisms.

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite

universe u v u' w

/-- Products of presheaves of sets on the site of a ringed topos, given directly: instance search
for them times out under Lean v4.35.0. -/
local instance (priority := high)
    hasLimitsOfShape_discrete_presheaf_SquareZeroTowerLimitKernelMapFunctions
    {C : Type u'} [Category.{v} C] (K : Type u) :
    HasLimitsOfShape (Discrete K) (Cᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

/-- The terminal sheaf of sets on a site, given directly: instance search for it times out under
Lean v4.35.0. -/
local instance (priority := high) hasTerminal_sheaf_SquareZeroTowerLimitKernelMapFunctions
    {C : Type u'} [Category.{v} C] (J : GrothendieckTopology C) : HasTerminal (Sheaf J (Type w)) :=
  haveI : HasLimitsOfShape (Discrete PEmpty.{1}) (Cᵒᵖ ⥤ Type w) :=
    functorCategoryHasLimitsOfShape
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (sheafToPresheaf J (Type w))

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

/-- `modulePullbackGlobalSection_comp_towerLimitKernelMap_π_of_sets` for a section
`w'` whose source is spelled `AlgebraicGeometry.Space.unitModule`. -/
theorem modulePullbackGlobalSection_comp_towerLimitKernelMap_π_of_sets_unitModule (n : ℕ)
    (σ : SheafOfModules.unit ((sheafCompose (Space.SmallEtale.topology B S hS (schemeSpace
        (towerBase ξ 0)).1) (forget₂ CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos
        B S hS (schemeSpace (towerBase ξ 0))).O) ⟶ limitBaseConormal ξ hsurj hsq e cR hcR c eLimit
        hc)
    (w' : Space.unitModule B S hS (towerSpace ξ 0).2 ⟶ (towerIdealSystem ξ hsurj hsq e he).obj (op
        n))
    (hτ : (Space.smallEtaleRingedToposHom B S hS (towerStructureMap ξ
          0)).toToposHom.inverseImage.globalSectionMap
          ((ringOneHom ((sheafCompose (Space.SmallEtale.topology B S hS (schemeSpace (towerBase ξ
              0)).1) (forget₂ CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS
              (schemeSpace (towerBase ξ 0))).O) ≫ (moduleSheafFunctor ((sheafCompose
              (Space.SmallEtale.topology B S hS (schemeSpace (towerBase ξ 0)).1) (forget₂
              CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (schemeSpace
              (towerBase ξ 0))).O)).map σ) ≫ (limitBaseExtension ξ hsurj hsq e cR hcR c eLimit
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
        ξ 0)).O)).map w' ≫ (towerExtension ξ hsurj hsq e he n (𝟙 _)).inclSheafSets) :
    Space.modulePullbackGlobalSection B S hS (towerStructureMap ξ 0) σ ≫
        towerLimitKernelMap ξ hsurj hsq e he cR hcR c eLimit hc ≫
        limit.π (towerIdealSystem ξ hsurj hsq e he) (op n) = w' :=
  modulePullbackGlobalSection_comp_towerLimitKernelMap_π_of_sets ξ @hsurj @hsq e @he cR hcR c eLimit
    hc n σ w' hτ

/-- `φ` on `1 ⊗ m` from the reading in the middle terms, for sections `σ = σ'` and `w'` given by
equations. -/
theorem baseRingTensorSection_comp_towerProblemKernelIso_inv_comp_towerLimitKernelMap_π_of_eq (n :
    ℕ) (m : ↑(limit (towerBaseKernelSystem ξ hsurj hsq e)))
    (σ σ' : SheafOfModules.unit ((sheafCompose (Space.SmallEtale.topology B S hS (schemeSpace
        (towerBase ξ 0)).1) (forget₂ CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos
        B S hS (schemeSpace (towerBase ξ 0))).O) ⟶ limitBaseConormal ξ hsurj hsq e cR hcR c eLimit
        hc)
    (hA : Space.baseRingTensorSection B S hS (towerSpace ξ 0)
        (Space.baseRingHomOfMap (towerStructureMap ξ 0))
        (limit (towerBaseKernelSystem ξ hsurj hsq e)) m ≫
        (towerProblemKernelIso ξ hsurj hsq e cR hcR c eLimit hc).inv =
      Space.modulePullbackGlobalSection B S hS (towerStructureMap ξ 0)
        (M := limitBaseConormal ξ hsurj hsq e cR hcR c eLimit hc) σ)
    (hσ : σ = σ')
    (w' : Space.unitModule B S hS (towerSpace ξ 0).2 ⟶ (towerIdealSystem ξ hsurj hsq e he).obj (op
        n))
    (hw : w' = Space.baseRingTensorSection B S hS (towerSpace ξ 0)
          (Space.baseRingHomOfMap (towerStructureMap ξ 0)) _
          (limit.π (towerBaseKernelSystem ξ hsurj hsq e) (op n) m) ≫
        (towerIdealSystemObjIso ξ hsurj hsq e he n).hom)
    (hτ : (Space.smallEtaleRingedToposHom B S hS (towerStructureMap ξ
          0)).toToposHom.inverseImage.globalSectionMap
          ((ringOneHom ((sheafCompose (Space.SmallEtale.topology B S hS (schemeSpace (towerBase ξ
              0)).1) (forget₂ CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS
              (schemeSpace (towerBase ξ 0))).O) ≫ (moduleSheafFunctor ((sheafCompose
              (Space.SmallEtale.topology B S hS (schemeSpace (towerBase ξ 0)).1) (forget₂
              CommRingCat.{u} RingCat.{u})).obj (Space.smallEtaleRingedTopos B S hS (schemeSpace
              (towerBase ξ 0))).O)).map σ') ≫ (limitBaseExtension ξ hsurj hsq e cR hcR c eLimit
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
        ξ 0)).O)).map w' ≫ (towerExtension ξ hsurj hsq e he n (𝟙 _)).inclSheafSets) :
      Space.baseRingTensorSection B S hS (towerSpace ξ 0)
          (Space.baseRingHomOfMap (towerStructureMap ξ 0)) _ m ≫
        (towerProblemKernelIso ξ hsurj hsq e cR hcR c eLimit hc).inv ≫
        towerLimitKernelMap ξ hsurj hsq e he cR hcR c eLimit hc ≫
        limit.π (towerIdealSystem ξ hsurj hsq e he) (op n) =
      Space.baseRingTensorSection B S hS (towerSpace ξ 0)
          (Space.baseRingHomOfMap (towerStructureMap ξ 0)) _
          (limit.π (towerBaseKernelSystem ξ hsurj hsq e) (op n) m) ≫
        (towerIdealSystemObjIso ξ hsurj hsq e he n).hom :=
  (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ towerLimitKernelMap ξ hsurj hsq e he cR hcR c
      eLimit hc ≫ limit.π (towerIdealSystem ξ hsurj hsq e he) (op n))
    (hA.trans (congrArg (Space.modulePullbackGlobalSection B S hS (towerStructureMap ξ 0))
        hσ))).trans
    ((modulePullbackGlobalSection_comp_towerLimitKernelMap_π_of_sets_unitModule ξ @hsurj @hsq e @he
        cR hcR c eLimit
      hc n σ' w' hτ).trans hw))

/-- **`φ` on the sections `1 ⊗ m`**: the section `1 ⊗ m` of `𝒪_{X₀} ⊗ lim Iₙ`, read in
`f^*𝒞_{Y₀/Y}`, followed by `φ = towerLimitKernelMap` and the `n`-th projection, is the section
`1 ⊗ mₙ` of `𝒪_{X₀} ⊗ Iₙ`. -/
theorem baseRingTensorSection_comp_towerProblemKernelIso_inv_comp_towerLimitKernelMap_π (n : ℕ)
    (m : ↑(limit (towerBaseKernelSystem ξ hsurj hsq e))) :
      Space.baseRingTensorSection B S hS (towerSpace ξ 0)
          (Space.baseRingHomOfMap (towerStructureMap ξ 0)) _ m ≫
        (towerProblemKernelIso ξ hsurj hsq e cR hcR c eLimit hc).inv ≫
        towerLimitKernelMap ξ hsurj hsq e he cR hcR c eLimit hc ≫
        limit.π (towerIdealSystem ξ hsurj hsq e he) (op n) =
      Space.baseRingTensorSection B S hS (towerSpace ξ 0)
          (Space.baseRingHomOfMap (towerStructureMap ξ 0)) _
          (limit.π (towerBaseKernelSystem ξ hsurj hsq e) (op n) m) ≫
        (towerIdealSystemObjIso ξ hsurj hsq e he n).hom :=
  baseRingTensorSection_comp_towerProblemKernelIso_inv_comp_towerLimitKernelMap_π_of_eq ξ @hsurj
      @hsq e @he cR hcR c eLimit hc n m _ _
    (baseRingTensorSection_towerProblemKernelIso_inv_eq_modulePullbackGlobalSection ξ @hsurj @hsq e
        cR
      hcR c eLimit hc m) (by exact rfl) _ (by exact rfl)
    (globalSectionMap_towerLimitKernelFunction_comp_towerProblemLimitBaseMap_π_eq ξ @hsurj @hsq e
        @he cR
      hcR c eLimit hc n m)

/-- **The data `(α, β, hφ)` of the limit comparison of the tower problem** (body of the proof of
[Stacks Project, Tag 0D3X]): there are isomorphisms `α : f^*𝒞_{Y₀/Y} ≅ 𝒪_{X₀} ⊗ lim Iₙ` and
`β : lim 𝒪_{X₀} ⊗ Iₙ ≅ lim ℳₙ` with `φ = α ≫ (𝒪_{X₀} ⊗ lim Iₙ ⟶ lim 𝒪_{X₀} ⊗ Iₙ) ≫ β`, the input
of `AlgebraicGeometry.ProperFlatFibre.exists_towerProblem_kernelChangeHom_of_limitComparison`
for the system `Iₙ = towerBaseKernelSystem`. -/
theorem towerProblem_limitComparison
    [HasLimit (towerBaseKernelSystem ξ hsurj hsq e ⋙ Space.baseRingTensorModule B S hS
      (towerSpace ξ 0) (Space.baseRingHomOfMap (towerStructureMap ξ 0)))] :
    ∃ (α : (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).G ≅ (Space.baseRingTensorModule B S hS
        (towerSpace ξ 0) (Space.baseRingHomOfMap (towerStructureMap ξ 0))).obj (limit
        (towerBaseKernelSystem ξ hsurj hsq e)))
      (β : limit (towerBaseKernelSystem ξ hsurj hsq e ⋙ Space.baseRingTensorModule B S hS
          (towerSpace ξ 0) (Space.baseRingHomOfMap (towerStructureMap ξ 0))) ≅
        ((towerProblem ξ hsurj hsq e cR hcR c eLimit hc).changeKernel (towerLimitKernelMap ξ hsurj
            hsq e he cR hcR c eLimit hc)).G),
      towerLimitKernelMap ξ hsurj hsq e he cR hcR c eLimit hc =
        α.hom ≫ limit.post (towerBaseKernelSystem ξ hsurj hsq e) (Space.baseRingTensorModule B S hS
            (towerSpace ξ 0) (Space.baseRingHomOfMap (towerStructureMap ξ 0))) ≫ β.hom :=
  towerProblem_limitComparison_data ξ @hsurj @hsq e @he cR hcR c eLimit hc
    (baseRingTensorSection_comp_towerProblemKernelIso_inv_comp_towerLimitKernelMap_π ξ @hsurj @hsq e
      @he cR hcR c eLimit hc)

end AlgebraicGeometry.ProperFlatFibre

end
