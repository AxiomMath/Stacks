module

public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionBaseRestriction
public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionClassIdealMap
public import StacksFrontier.Deformation.RingedSpaceThickening.PulledIdealNaiveClass
public import StacksFrontier.Deformation.RingedSpaceThickening.CotangentObstructionCriterion
public import StacksFrontier.Cotangent.SheavesOfRings.RingedSpaceFundamentalTriangleDerived
public import StacksFrontier.Cotangent.SheavesOfRings.FundamentalTriangleGeneral
import StacksCore.Tactic.StacksAttribute

/-!
# The obstruction class of Stacks 08UZ, clause (1)

Let `t : S ⟶ S'` be a first order thickening of ringed spaces with ideal `𝒥`, `f : X ⟶ S` a
morphism, `𝒢` an `𝒪_X`-module and `c : f^* t^* 𝒥 ⟶ 𝒢` the prescribed map on ideals (**Stacks
08UY**). Write `A' = (f ∘ t)⁻¹𝒪_{S'} ⟶ A = f⁻¹𝒪_S ⟶ 𝒪_X` for the tower of **Stacks 08T4**, whose
fundamental triangle is `L_{A/A'} ⊗_A 𝒪_X ⟶ L_{X/S'} ⟶ L_{X/S} ⟶ (L_{A/A'} ⊗_A 𝒪_X)[1]`.

Since `A' ⟶ A` is surjective with kernel the pulled ideal, the first vertex maps to its
truncation `NL_{A/A'} ⊗_A 𝒪_X`, which is quasi-isomorphic to `f^* t^* 𝒥` placed in degree `-1`;
this gives `κ : L_{A/A'} ⊗_A 𝒪_X ⟶ (f^* t^* 𝒥)[1]`, an isomorphism on `H^{-1}`
(`firstVertexToPulledIdeal`). The class of the source is
`ξ = (c[1] ∘ κ)[1] ∘ δ ∈ Ext²_{𝒪_X}(L_{X/S}, 𝒢)`, `δ` the connecting morphism
(`cotangentObstruction`).

The first arrow of the triangle followed by `L_{X/S'} ⟶ NL_{X/S'}` is `κ` followed by the map
`(f^* t^* 𝒥)[1] ⟶ NL_{X/S'}` sending a section of `𝒥` to the conormal class of its coefficient
image (`cotangentBaseChange_comp_canonicalNaiveComparison`, `pulledIdealToNaive_eq`), and the
class of a square-zero extension restricted along that map is minus its shifted ideal map
(`idealToNaiveCotangent_comp_extClass`). The criterion
`CategoryTheory.Pretriangulated.shiftedHom_comp_eq_zero_iff_exists` then reads the vanishing of
`ξ` as the existence of an extension with bijective ideal inducing `c`, which is a solution.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.firstVertexToPulledIdeal`: `κ`.
* `AlgebraicGeometry.RingedSpaceThickening.cotangentObstruction`: the class `ξ`.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.cotangentObstruction_eq_zero_iff`: **Stacks 08UZ,
  clause (1)**.

## References

* [Stacks Project, Tag 08UZ](https://stacks.math.columbia.edu/tag/08UZ)
* [Stacks Project, Tag 08T4](https://stacks.math.columbia.edu/tag/08T4)
* [Stacks Project, Tag 0GQ3](https://stacks.math.columbia.edu/tag/0GQ3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Sheaves.RingedSpaceDifferentials (sheafAdjunction inverseImageSheaf)
open Stacks.Sheaves.RingedSpaceCotangent (baseStructureMap structureModules)

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X S S' : RingedSpace.{u, u}} (f : X ⟶ S) {t : S ⟶ S'}

local notation "Jₓ" => Opens.grothendieckTopology X.carrier
local notation "hₓ" => Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f

/-- The two readings of the conormal class of the coefficient image of a section `s` of `𝒪_{S'}`
killed by `t^♯` in the conormal term of `NL_{X/S'}` agree. -/
theorem doubleXIso₀_hom_naiveConormalClass_eq_coefficientConormalClass
    (V : (Opens S'.carrier)ᵒᵖ) (s : S'.presheaf.obj V) (hs : (t.hom.c.app V).hom s = 0)
    (hk : ((Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap (f ≫ t)).hom.app
      (op ((Opens.map (f ≫ t).hom.base).obj V.unop))).hom
      (((sheafAdjunction (f ≫ t)).unit.app S'.sheaf).hom.app V s) = 0) :
    ((HomologicalComplex.doubleXIso₀
        (Stacks.SheafOfModules.canonicalConormalSequence.{u, u, u, u} Jₓ (inverseImageSheaf (f ≫ t))
          X.sheaf (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap (f ≫ t))).f
        ComplexShape.upIntRelNegOneZero).hom.val.app (op ((Opens.map (f ≫ t).hom.base).obj V.unop)))
      (CategoryTheory.Sheaf.naiveConormalClass.{u, u, u} Jₓ
        (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap (f ≫ t))
        (op ((Opens.map (f ≫ t).hom.base).obj V.unop))
        (CategoryTheory.Sheaf.coefficientRelation.{u, u, u} Jₓ
          (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap (f ≫ t))
          _ (((sheafAdjunction (f ≫ t)).unit.app S'.sheaf).hom.app V s) hk)) =
      coefficientConormalClass f t (Stacks.Sites.FreeAlgebra.underlyingPresheaf Jₓ X.sheaf) (𝟙 _)
        V (baseIdealSection t V s hs) := by
  have hmem := coefficient_mem_kernelIdeal f t
    (Stacks.Sites.FreeAlgebra.underlyingPresheaf Jₓ X.sheaf) (𝟙 _) V s hs
  have h₁ :=
    CategoryTheory.Sheaf.doubleXIso₀_hom_naiveConormalClass_coefficientRelation.{u, u, u} Jₓ
      (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap (f ≫ t))
      (op ((Opens.map (f ≫ t).hom.base).obj V.unop))
      (((sheafAdjunction (f ≫ t)).unit.app S'.sheaf).hom.app V s) hk hmem
  refine h₁.trans ?_
  have hι := idealSheafι_baseIdealSection t V s hs
  generalize baseIdealSection t V s hs = y at hι ⊢
  subst hι
  rfl

/-- **The degree `-1` compatibility of Tag 08UZ.** The pulled ideal `f^* t^* 𝒥`, read through
`NL_{A/A'} ⊗_A 𝒪_X` and the first arrow of Tag 08T4 into `NL_{X/S'}`, is the map of `f^* t^* 𝒥`
into the conormal term of `NL_{X/S'}`: both send a section of `𝒥` to the conormal class of its
coefficient image. -/
theorem pulledIdealBaseNaiveMap_comp_eqToHom (ht : IsFirstOrderThickening t) :
    pulledIdealBaseNaiveMap f ht ≫
        (eqToHom (congrArg (fun k => Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} Jₓ
          (inverseImageSheaf (f ≫ t)) X.sheaf k)
          (Stacks.Sheaves.RingedSpaceCotangent.baseStructureMap_comp f t))).f (-1) =
      idealConormalMap f t := by
  refine prescribedIdealMap_ext (fun V y => ?_)
  set s := (Stacks.ClosedImmersion.idealSheafι t).val.app V y with hsdef
  have hs : (t.hom.c.app V).hom s = 0 := app_idealSheafι_eq_zero t V y
  have hy : y = baseIdealSection t V s hs :=
    Stacks.ClosedImmersion.injective_idealSheafι_val_app t V.unop
      (idealSheafι_baseIdealSection t V s hs).symm
  have hk : ((Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap (f ≫ t)).hom.app
      (op ((Opens.map (f ≫ t).hom.base).obj V.unop))).hom
      (((sheafAdjunction (f ≫ t)).unit.app S'.sheaf).hom.app V s) = 0 :=
    (congrArg (fun k => ((k.hom.app (op ((Opens.map (f ≫ t).hom.base).obj V.unop))).hom
        (((sheafAdjunction (f ≫ t)).unit.app S'.sheaf).hom.app V s)))
        (Stacks.Sheaves.RingedSpaceCotangent.baseStructureMap_comp f t)).symm.trans
      ((congrArg ((hₓ).hom.app _).hom
        (RingHom.mem_ker.1 (unit_mem_kernelIdeal f V s hs))).trans (map_zero _))
  have hL := prescribedIdealMap_pulledIdealBaseNaiveMap_eqToHom f ht
    (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap (f ≫ t))
    (Stacks.Sheaves.RingedSpaceCotangent.baseStructureMap_comp f t) V s hs hk
  rw [hy]
  refine hL.trans (Eq.trans ?_ (prescribedIdealMap_comp_app _ _ V _).symm)
  rw [prescribedIdealMap_presentationIdealMap,
    ← doubleXIso₀_hom_naiveConormalClass_eq_coefficientConormalClass f V s hs hk]
  exact (CategoryTheory.Sheaf.iso_inv_val_app_hom_val_app.{u, u, u} Jₓ _ _ _).symm

/-- In degree `-1`, the map of the pulled ideal `f^* t^* 𝒥` into `NL_{A/A'} ⊗_A 𝒪_X` followed by
the first arrow of Tag 08T4 into `NL_{X/S'}` is the map of `f^* t^* 𝒥` into the conormal term of
`NL_{X/S'}`. -/
theorem pulledIdealNaiveMapNegOne_comp_towerNaiveMap (ht : IsFirstOrderThickening t) :
    pulledIdealNaiveMapNegOne f ht ≫ (towerNaiveMap f t).f (-1) = idealConormalMap f t :=
  (pulledIdealNaiveMapNegOne_comp_towerNaiveMapOf_f f ht _
    (Stacks.Sheaves.RingedSpaceCotangent.baseStructureMap_comp f t)).trans
    (pulledIdealBaseNaiveMap_comp_eqToHom f ht)

/-- **The compatibility of Tag 08UZ on complexes**: the pulled ideal in degree `-1` mapping to
`NL_{A/A'} ⊗_A 𝒪_X` and on to `NL_{X/S'}` is the map of the pulled ideal into `NL_{X/S'}`. -/
theorem pulledIdealNaiveMap_comp_towerNaiveMap (ht : IsFirstOrderThickening t) :
    ((pulledIdealNaiveMap f ht ≫ towerNaiveMap f t :
      (HomologicalComplex.single (structureModules X) (ComplexShape.up ℤ) (-1)).obj
        (pulledIdealModule f t) ⟶ _) :
      (HomologicalComplex.single
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (J := Jₓ) X.sheaf))
        (ComplexShape.up ℤ) (-1)).obj (pulledIdeal f t) ⟶
          RingedSpace.naiveCotangentComplex (f ≫ t)) =
      idealConormalChainMap f t := by
  refine HomologicalComplex.from_single_hom_ext ?_
  have h₄ : (pulledIdealNaiveMap f ht ≫ towerNaiveMap f t).f (-1) =
      (pulledIdealNaiveMap f ht).f (-1) ≫ (towerNaiveMap f t).f (-1) :=
    HomologicalComplex.comp_f _ _ _
  refine h₄.trans (Eq.trans ?_ (idealConormalChainMap_f f t).symm)
  exact (congrArg (· ≫ (towerNaiveMap f t).f (-1)) (pulledIdealNaiveMap_f_negOne f ht)).trans
    ((Category.assoc _ _ _).trans
      (congrArg _ (pulledIdealNaiveMapNegOne_comp_towerNaiveMap f ht)))

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- `f^* t^* 𝒥`, placed in degree `-1`, is isomorphic in `D(𝒪_X)` to `NL_{A/A'} ⊗_A 𝒪_X`. -/
def pulledIdealNaiveIso (ht : IsFirstOrderThickening t) :
    (DerivedCategory.Q (C := structureModules X)).obj
        ((HomologicalComplex.single (structureModules X) (ComplexShape.up ℤ) (-1)).obj
          (pulledIdealModule f t)) ≅
      (DerivedCategory.Q (C := structureModules X)).obj (pulledNaiveComplex f t) :=
  @asIso _ _ _ _ (DerivedCategory.Q.map (pulledIdealNaiveMap f ht))
    ((DerivedCategory.isIso_Q_map_iff_quasiIso (φ := pulledIdealNaiveMap f ht)).2
      (quasiIso_pulledIdealNaiveMap f ht))

/-- **The map `κ : L_{A/A'} ⊗_A 𝒪_X ⟶ (f^* t^* 𝒥)[1]` of Tag 08UZ**: the first vertex of the
fundamental triangle of `X ⟶ S ⟶ S'` (Tag 08T4) mapped to its truncation `NL_{A/A'} ⊗_A 𝒪_X`,
which is quasi-isomorphic to the pulled ideal `f^* t^* 𝒥` placed in degree `-1`. -/
def firstVertexToPulledIdeal (ht : IsFirstOrderThickening t) :
    (DerivedCategory.Q (C := structureModules X)).obj
        (Stacks.Sheaves.RingedSpaceCotangent.baseChangedCotangentComplex f t) ⟶
      ((DerivedCategory.singleFunctor (structureModules X) 0).obj
        (pulledIdealModule f t))⟦(1 : ℤ)⟧ :=
  DerivedCategory.Q.map (CategoryTheory.Sheaf.baseChangedNaiveComparison.{u, u, u} Jₓ
      (baseStructureMap f t) hₓ) ≫
    (pulledIdealNaiveIso f ht).inv ≫
    (CochainComplex.singleZeroShiftOneIso (pulledIdealModule f t)).inv

/-- **The map `ν : (f^* t^* 𝒥)[1] ⟶ NL_{X/S'}`** through `NL_{A/A'} ⊗_A 𝒪_X`. -/
def pulledIdealToNaive (ht : IsFirstOrderThickening t) :
    ((DerivedCategory.singleFunctor (structureModules X) 0).obj (pulledIdealModule f t))⟦(1 : ℤ)⟧ ⟶
      (DerivedCategory.Q (C := structureModules X)).obj
        (RingedSpace.naiveCotangentComplex (f ≫ t)) :=
  (CochainComplex.singleZeroShiftOneIso (pulledIdealModule f t)).hom ≫
    DerivedCategory.Q.map (pulledIdealNaiveMap f ht ≫ towerNaiveMap f t)

/-- **The compatibility of Tag 08UZ in `D(𝒪_X)`**: the first arrow of the fundamental triangle
of `X ⟶ S ⟶ S'` followed by `L_{X/S'} ⟶ NL_{X/S'}` is `κ` followed by `ν`. -/
theorem cotangentBaseChange_comp_canonicalNaiveComparison (ht : IsFirstOrderThickening t) :
    DerivedCategory.Q.map (Stacks.Sheaves.RingedSpaceCotangent.cotangentBaseChange f t) ≫
        DerivedCategory.Q.map
          (Stacks.Sheaves.RingedSpaceCotangent.canonicalNaiveComparison (f ≫ t)) =
      firstVertexToPulledIdeal f ht ≫ pulledIdealToNaive f ht := by
  have h₁ : ((pulledIdealNaiveIso f ht).inv ≫
        (CochainComplex.singleZeroShiftOneIso (pulledIdealModule f t)).inv) ≫
      (CochainComplex.singleZeroShiftOneIso (pulledIdealModule f t)).hom ≫
        DerivedCategory.Q.map (pulledIdealNaiveMap f ht ≫ towerNaiveMap f t) =
      DerivedCategory.Q.map (towerNaiveMap f t) :=
    (Category.assoc _ _ _).trans ((congrArg _ ((Iso.inv_hom_id_assoc _ _).trans
      (DerivedCategory.Q.map_comp _ _))).trans ((pulledIdealNaiveIso f ht).inv_hom_id_assoc _))
  have h₂ : DerivedCategory.Q.map (CategoryTheory.Sheaf.baseChangedNaiveComparison.{u, u, u} Jₓ
        (baseStructureMap f t) hₓ) ≫ DerivedCategory.Q.map (towerNaiveMap f t) =
      DerivedCategory.Q.map (Stacks.Sheaves.RingedSpaceCotangent.cotangentBaseChange f t) ≫
        DerivedCategory.Q.map
          (Stacks.Sheaves.RingedSpaceCotangent.canonicalNaiveComparison (f ≫ t)) :=
    (DerivedCategory.Q.map_comp _ _).symm.trans ((congrArg DerivedCategory.Q.map
      (baseChangedNaiveComparison_comp_towerNaiveMap f t)).trans (DerivedCategory.Q.map_comp _ _))
  refine h₂.symm.trans ((congrArg (DerivedCategory.Q.map
    (CategoryTheory.Sheaf.baseChangedNaiveComparison.{u, u, u} Jₓ (baseStructureMap f t) hₓ) ≫ ·)
    h₁.symm).trans ?_)
  exact (Category.assoc _ _ _).symm

/-- `ν` is the map of the pulled ideal into `NL_{X/S'}` (`idealToNaiveCotangent`). -/
theorem pulledIdealToNaive_eq (ht : IsFirstOrderThickening t) :
    pulledIdealToNaive f ht = idealToNaiveCotangent f t := by
  rw [pulledIdealToNaive, idealToNaiveCotangent_eq]
  exact congrArg (fun φ => (CochainComplex.singleZeroShiftOneIso (pulledIdeal f t)).hom ≫
    DerivedCategory.Q.map φ) (pulledIdealNaiveMap_comp_towerNaiveMap f ht)

/-- The first vertex `L_{A/A'} ⊗_A 𝒪_X` of the fundamental triangle of `X ⟶ S ⟶ S'` lies in
degrees `≤ -1`: `A' ⟶ A` is surjective. -/
theorem isLE_negOne_firstVertex (ht : IsFirstOrderThickening t) :
    ((DerivedCategory.Q (C := structureModules X)).obj
      (Stacks.Sheaves.RingedSpaceCotangent.baseChangedCotangentComplex f t)).IsLE (-1) :=
  DerivedCategory.isLE_negOne_Q_obj_of_iso (𝒞 := structureModules X)
    (CategoryTheory.Sheaf.baseChangedNaiveComparison.{u, u, u} Jₓ (baseStructureMap f t) hₓ)
    (pulledIdealNaiveIso f ht)
    (CategoryTheory.Sheaf.baseChangedNaiveComparison_isIso_homologyMap_zero.{u, u, u} Jₓ
      (baseStructureMap f t) hₓ)
    (fun i hi => CategoryTheory.Sheaf.baseChangedCotangentComplex_isZero_pos.{u, u, u} Jₓ
      (baseStructureMap f t) hₓ i hi)

/-- `κ` is an isomorphism on `H^{-1}`. -/
theorem isIso_homologyFunctor_map_firstVertexToPulledIdeal (ht : IsFirstOrderThickening t) :
    IsIso ((DerivedCategory.homologyFunctor (structureModules X) (-1)).map
      (firstVertexToPulledIdeal f ht)) := by
  have h := DerivedCategory.isIso_homologyFunctor_map_Q_map_comp_iso_inv (𝒞 := structureModules X)
    (CategoryTheory.Sheaf.baseChangedNaiveComparison.{u, u, u} Jₓ (baseStructureMap f t) hₓ)
    (pulledIdealNaiveIso f ht) (-1)
    (CategoryTheory.Sheaf.baseChangedNaiveComparison_isIso_homologyMap_negOne.{u, u, u} Jₓ
      (baseStructureMap f t) hₓ)
  have e : (DerivedCategory.homologyFunctor (structureModules X) (-1)).map
      (firstVertexToPulledIdeal f ht) =
      (DerivedCategory.homologyFunctor (structureModules X) (-1)).map
        (DerivedCategory.Q.map (CategoryTheory.Sheaf.baseChangedNaiveComparison.{u, u, u} Jₓ
          (baseStructureMap f t) hₓ) ≫ (pulledIdealNaiveIso f ht).inv) ≫
      (DerivedCategory.homologyFunctor (structureModules X) (-1)).map
        (CochainComplex.singleZeroShiftOneIso (pulledIdealModule f t)).inv :=
    (congrArg (DerivedCategory.homologyFunctor (structureModules X) (-1)).map
      (Category.assoc _ _ _).symm).trans (Functor.map_comp _ _ _)
  rw [e]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h inferInstance

end Derived

/-! ### The obstruction class -/

section Obstruction

attribute [local instance] HasDerivedCategory.standard

variable (t) in
/-- The connecting morphism `L_{X/S} ⟶ (L_{A/A'} ⊗_A 𝒪_X)[1]` of the fundamental triangle of
`X ⟶ S ⟶ S'` (Tag 08T4). -/
def cotangentTowerConnecting :
    (DerivedCategory.Q (C := structureModules X)).obj
        (Stacks.Sheaves.RingedSpaceCotangent.cotangentComplex f) ⟶
      ((DerivedCategory.Q (C := structureModules X)).obj
        (Stacks.Sheaves.RingedSpaceCotangent.baseChangedCotangentComplex f t))⟦(1 : ℤ)⟧ :=
  (Stacks.Sheaves.RingedSpaceCotangent.exists_distTriang_cotangentTower f t).choose

variable (t) in
/-- The fundamental triangle of `X ⟶ S ⟶ S'` with connecting morphism
`cotangentTowerConnecting` is distinguished (Tag 08T4). -/
theorem cotangentTowerConnecting_distTriang :
    Triangle.mk
        (DerivedCategory.Q.map (Stacks.Sheaves.RingedSpaceCotangent.cotangentBaseChange f t))
        (DerivedCategory.Q.map (Stacks.Sheaves.RingedSpaceCotangent.cotangentChangeOfBase f t))
        (cotangentTowerConnecting f t) ∈
      distTriang (DerivedCategory (structureModules X)) :=
  (Stacks.Sheaves.RingedSpaceCotangent.exists_distTriang_cotangentTower f t).choose_spec

variable (G : SheafOfModules.{u} (structureSheafRing X))

variable (t) in
/-- Maps `f^* t^* 𝒥 ⟶ 𝒢`, shifted, as maps `(f^* t^* 𝒥)[1] ⟶ 𝒢[1]` in `D(𝒪_X)`. -/
def pulledIdealShiftHom :
    ((modulePullback f).obj
        ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G) →+
      ((((DerivedCategory.singleFunctor (structureModules X) 0).obj
          (pulledIdealModule f t))⟦(1 : ℤ)⟧ ⟶
        ((DerivedCategory.singleFunctor (structureModules X) 0).obj G)⟦(1 : ℤ)⟧)) :=
  AddMonoidHom.mk'
    (fun a => ((DerivedCategory.singleFunctor (structureModules X) 0).map a)⟦(1 : ℤ)⟧')
    (fun a b => by
      refine (congrArg
        (fun z => (shiftFunctor (DerivedCategory (structureModules X)) (1 : ℤ)).map z)
        ((DerivedCategory.singleFunctor (structureModules X) 0).map_add
          (X := pulledIdealModule f t) (Y := G) (f := a) (g := b))).trans ?_
      exact (shiftFunctor (DerivedCategory (structureModules X)) (1 : ℤ)).map_add)

variable (ht : IsFirstOrderThickening t) (c : (modulePullback f).obj
    ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G)

/-- **The obstruction class `ξ ∈ Ext²_{𝒪_X}(L_{X/S}, 𝒢)` of Tag 08UZ, clause (1).** The connecting
morphism `L_{X/S} ⟶ (L_{A/A'} ⊗_A 𝒪_X)[1]` of the fundamental triangle of `X ⟶ S ⟶ S'`
(Tag 08T4), followed by `κ[1] : (L_{A/A'} ⊗_A 𝒪_X)[1] ⟶ (f^* t^* 𝒥)[2]` and by `c[2]`, where
`κ` is the canonical map of the first vertex to the pulled ideal placed in degree `-1`: the image
of `ξ' = c ∘ κ ∈ Ext¹_{𝒪_X}(L_{A/A'} ⊗_A 𝒪_X, 𝒢)` under the connecting morphism. -/
def cotangentObstruction : Stacks.Sheaves.RingedSpaceCotangent.cotangentExt f G 2 :=
  ShiftedHom.comp (cotangentTowerConnecting f t)
    (firstVertexToPulledIdeal f ht ≫ pulledIdealShiftHom f t G c) (show (1 : ℤ) + 1 = 2 by omega)

/-- **Stacks Project, Tag 08UZ, clause (1).** Let `t : S ⟶ S'` be a first order thickening of
ringed spaces with ideal `𝒥`, `f : X ⟶ S` a morphism of ringed spaces, `𝒢` an `𝒪_X`-module and
`c : f^* t^* 𝒥 ⟶ 𝒢` the prescribed map on ideals (the setup of **Stacks 08UY**). The canonical
class `ξ = cotangentObstruction f G ht c ∈ Ext²_{𝒪_X}(L_{X/S}, 𝒢)` vanishes if and only if the
deformation problem (08UY) has a solution.

The proof is the source's: by **Stacks 0GQ3** (realized here through square-zero extensions of
`(f ∘ t)⁻¹𝒪_{S'}`-algebras with bijective ideal, `exists_ideal_bijective_extClass_eq`, and the
correspondence `DeformationSolution.toAlgebraExtension` / `toDeformationSolution` with solutions)
a solution exists exactly when `ξ' = c ∘ κ ∈ Ext¹(L_{A/A'} ⊗_A 𝒪_X, 𝒢)` comes from
`Ext¹(L_{X/S'}, 𝒢) = Ext¹(𝖭𝖫_{X/S'}, 𝒢)` (**Stacks 08UW**), and the long exact sequence of the
distinguished triangle of **Stacks 08T4** identifies those classes with the ones whose image
in `Ext²(L_{X/S}, 𝒢)` vanishes. -/
@[stacks 08UZ "clause (1): there is a canonical element ξ ∈ Ext²(L_{X/S}, 𝒢) whose vanishing \
is a sufficient and necessary condition for the existence of a solution to (08UY)"]
theorem cotangentObstruction_eq_zero_iff :
    cotangentObstruction f G ht c = 0 ↔ Nonempty (DeformationSolution t ht f G c) := by
  have := isLE_negOne_firstVertex f ht
  have hκ := isIso_homologyFunctor_map_firstVertexToPulledIdeal f ht
  have hπ : ∀ z : (DerivedCategory.Q (C := structureModules X)).obj
        (Stacks.Sheaves.RingedSpaceCotangent.cotangentComplex (f ≫ t)) ⟶
        ((DerivedCategory.singleFunctor (structureModules X) 0).obj G)⟦(1 : ℤ)⟧,
      ∃ z' : (DerivedCategory.Q (C := structureModules X)).obj
          (RingedSpace.naiveCotangentComplex (f ≫ t)) ⟶
          ((DerivedCategory.singleFunctor (structureModules X) 0).obj G)⟦(1 : ℤ)⟧,
        z = DerivedCategory.Q.map
          (Stacks.Sheaves.RingedSpaceCotangent.canonicalNaiveComparison (f ≫ t)) ≫ z' := by
    intro z
    obtain ⟨z', hz'⟩ :=
      (Stacks.Sheaves.RingedSpaceCotangent.naiveExtCotangentAddEquiv (f ≫ t) G
        (le_refl 1)).surjective z
    exact ⟨z', hz'.symm.trans
      (Stacks.Sheaves.RingedSpaceCotangent.naiveExtCotangentAddEquiv_apply (f ≫ t) G (le_refl 1)
        z')⟩
  have hinj : ∀ a, firstVertexToPulledIdeal f ht ≫ pulledIdealShiftHom f t G a = 0 → a = 0 :=
    fun a ha => DerivedCategory.eq_zero_of_comp_shift_map_eq_zero (𝒞 := structureModules X)
      (firstVertexToPulledIdeal f ht) inferInstance a ha
  let cls : {P : AlgebraSquareZeroExtension (f ≫ t) G // P.IdealBijective} →
      ((DerivedCategory.Q (C := structureModules X)).obj
          (RingedSpace.naiveCotangentComplex (f ≫ t)) ⟶
        ((DerivedCategory.singleFunctor (structureModules X) 0).obj G)⟦(1 : ℤ)⟧) :=
    fun P => have := P.1.presentation_isLocallySurjective; P.1.toPresented.extClass
  have hcls : Function.Surjective cls := fun ζ =>
    let ⟨P, hP, h⟩ := exists_ideal_bijective_extClass_eq (f := f ≫ t) (G := G) ζ
    ⟨⟨P, hP⟩, h⟩
  have hγ : ∀ E, pulledIdealToNaive f ht ≫ cls E = -(pulledIdealShiftHom f t G E.1.idealMap) :=
    fun E => (congrArg (· ≫ cls E) (pulledIdealToNaive_eq f ht)).trans
      (idealToNaiveCotangent_comp_extClass f t E.1)
  have key := shiftedHom_comp_eq_zero_iff_exists _ (cotangentTowerConnecting_distTriang f t)
    (DerivedCategory.Q.map (Stacks.Sheaves.RingedSpaceCotangent.canonicalNaiveComparison (f ≫ t)))
    hπ (firstVertexToPulledIdeal f ht) (pulledIdealToNaive f ht)
    (cotangentBaseChange_comp_canonicalNaiveComparison f ht) (pulledIdealShiftHom f t G) hinj cls
    hcls (fun E => E.1.idealMap) hγ c
  refine key.trans ⟨?_, ?_⟩
  · rintro ⟨⟨P, hP⟩, h⟩
    exact ⟨P.toDeformationSolution hP ht ((P.idealMap_eq_iff c).1 h)⟩
  · rintro ⟨Q⟩
    exact ⟨⟨Q.toAlgebraExtension, Q.toAlgebraExtension_idealBijective⟩,
      Q.toAlgebraExtension_idealMap⟩

end Obstruction

end AlgebraicGeometry.RingedSpaceThickening

end
