module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatNeighbourhoodCech
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.IdealOfGlobalSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.RestrictScalarsQuotientHypothesis

/-!
# The flat-neighbourhood comparison of extended alternating Čech complexes

Let `φ : O ⟶ O'` be a flat morphism of sheaves of commutative rings on a site and let
`f₁, …, f_r` be global sections of `O` with `O/(f₁, …, f_r) ≅ O'/(f₁, …, f_r)O'`.  This file
states and proves [Stacks, Tag 099H] in the source's own terms: the map of extended alternating
Čech complexes

`O → ∏_{i₀} O_{f_{i₀}} → ⋯ → O_{f₁⋯f_r}`  ⟶  `O' → ∏_{i₀} O'_{f_{i₀}} → ⋯ → O'_{f₁⋯f_r}`

induced by the canonical maps `O_{f_S} ⟶ O'_{f_S}` is a quasi-isomorphism.

## Main definitions

* `Stacks.Sheaves.CechFlatNeighbourhood.structureMap`: the map `O ⟶ O'` of sheaves of
  `O`-modules underlying `φ`; on sections it is `φ`.
* `Stacks.Sheaves.CechFlatNeighbourhood.cechSystemBaseChangeMap`: a map of systems
  `O_{f_S} ⟶ O'_{f_S}` of sheaves of `O`-modules, natural in `S`.

## Main results

* `Stacks.Sheaves.CechFlatNeighbourhood.unitToAwayModule_comp_cechSystemBaseChangeMap_app`:
  `cechSystemBaseChangeMap` is a map *over* `O`: composed with `O ⟶ O_{f_S}` it is
  `O ⟶ O' ⟶ O'_{f_S}`.
* `Stacks.Sheaves.CechFlatNeighbourhood.eq_cechSystemBaseChangeMap`: it is the *only* such map
  of systems, so it is the canonical map `O_{f_S} ⟶ O'_{f_S}` of the source.
* `Stacks.Sheaves.CechFlatNeighbourhood.extendedAlternatingCechBaseChangeMap_eq`: the comparison
  `extendedAlternatingCechBaseChangeMap` of `FlatNeighbourhoodCech.lean` is the map of Čech
  complexes induced by `cechSystemBaseChangeMap`.
* `Stacks.Sheaves.CechFlatNeighbourhood.quasiIso_complexMap_cechSystemBaseChangeMap`:
  **[Stacks, Tag 099H]**.

## Implementation notes

A map of sheaves of `O`-modules out of `O_{f_S}` is determined by its composites with the maps
`O ⟶ O_{f_S}` "divided by `f_S^{n+1}`" (`AlgebraicGeometry.RingedSite.awayModule_hom_ext`), and
when its target is a module on which `f_S` acts invertibly those composites are determined by
the one at `n = 0`, because multiplication by a global section is an endomorphism of the
identity functor.  That is the uniqueness `eq_cechSystemBaseChangeMap`.

## References

* [Stacks Project, Tag 099H](https://stacks.math.columbia.edu/tag/099H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open AlgebraicGeometry AlgebraicGeometry.SheafOfModules AlgebraicGeometry.RingedSite
open Stacks.Sheaves.FlatNeighbourhood

universe u

namespace Stacks.Sheaves.CechFlatNeighbourhood

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify J AddCommGrpCat.{u}]
  [HasWeakSheafify J CommRingCat.{u}]

attribute [local instance] isMulCommutative_underlyingRingSheafOfSite_obj

variable (O : Sheaf J CommRingCat.{u}) {r : ℕ}
  (f : Fin r → Presheaf.globalSections (O.obj ⋙ forget CommRingCat.{u}))
  {O' : Sheaf J CommRingCat.{u}} (φ : O ⟶ O')

/-- The map `O ⟶ O'` of sheaves of `O`-modules underlying `φ`: on sections it is `φ`. -/
abbrev structureMap :
    SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (ringedSite O).O) ⟶
      RestrictedRingModule φ :=
  SheafOfModules.unitToRestrictScalarsUnit (baseChangeRingSheafMap (ringedSite O) O' φ)

omit [HasWeakSheafify J CommRingCat.{u}] in
/-- `x ↦ x ⊗ 1` at the rank-one module, followed by `O ⊗_O O' ≅ O'`, is the map `O ⟶ O'`
underlying `φ`. -/
theorem tensorUnitMap_comp_sheafTensorRightUnitIso_hom :
    (tensorUnitMap φ (RingModule O)).val ≫
        (sheafTensorRightUnitIso O (RestrictedRingModule φ)).hom =
      structureMap O φ := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun X => ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
  let lam := ((PresheafOfModules.monoidalCategoryStruct (R := O.obj)).leftUnitor
    (RestrictedRingModule φ).val).hom
  have hτ := (tensorUnitMap φ (RingModule O)).property X x
  have hnat := fun y => congrArg (fun k => (k.app X).hom y) (adj.unit.naturality lam)
  have htri := fun y => congrArg (fun k => (k.app X).hom y)
    (adj.right_triangle_components (RestrictedRingModule φ))
  have e1 := congrArg ((sheafTensorRightUnitIso O (RestrictedRingModule φ)).hom.val.app X).hom hτ
  refine e1.trans ?_
  refine (congrArg ((adj.counit.app (RestrictedRingModule φ)).val.app X).hom
    (hnat (x ⊗ₜ[O.obj.obj X] restrictedOne φ X)).symm).trans ?_
  refine (htri _).trans ?_
  show (φ.hom.app X).hom x * (1 : O'.obj.obj X) = (φ.hom.app X).hom x
  exact mul_one _

/-- The extension-of-scalars map `x ↦ x ⊗ 1` applied to the system `S ↦ O_{f_S}`. -/
def cechSystemTensorUnit :
    awayLocalizationFunctor (ringedSite O) f ⟶
      awayLocalizationFunctor (ringedSite O) f ⋙
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).flip.obj
          (RestrictedRingModule φ)) where
  app S := (tensorUnitMap φ ((awayLocalizationFunctor (ringedSite O) f).obj S)).val
  naturality _ _ g := tensorUnitMap_naturality φ ((awayLocalizationFunctor (ringedSite O) f).map g)

/-- **The map of systems `O_{f_S} ⟶ O'_{f_S}`** of sheaves of `O`-modules: extension of scalars
followed by the identification `O_{f_S} ⊗_O O' ≅ O'_{f'_S}` of `awayLocalizationBaseChangeIso`.
By `eq_cechSystemBaseChangeMap` it is the unique map of systems over `O`, so it is the canonical
map of localizations. -/
def cechSystemBaseChangeMap :
    awayLocalizationFunctor (ringedSite O) f ⟶
      awayLocalizationFunctor (ringedSite O') (baseChangeFamily O f φ) ⋙
        SheafOfModules.restrictScalars (baseChangeRingSheafMap (ringedSite O) O' φ) :=
  cechSystemTensorUnit O f φ ≫ (awayLocalizationBaseChangeIso O f φ).hom

/-- On the maps `O ⟶ O_{f_S}` divided by `f_S^{n+1}`, `cechSystemBaseChangeMap` is
`O ⟶ O'` followed by the corresponding map `O' ⟶ O'_{f'_S}`. -/
theorem awayModuleCoconeι_comp_cechSystemBaseChangeMap_app (S : Finset (Fin r)) (n : ℕ) :
    awayModuleCoconeι (ringedSite O) (prodGlobalSection f S) (n + 1) ≫
        (cechSystemBaseChangeMap O f φ).app S =
      structureMap O φ ≫
        (SheafOfModules.restrictScalars (baseChangeRingSheafMap (ringedSite O) O' φ)).map
          (awayModuleCoconeι (ringedSite O') (prodGlobalSection (baseChangeFamily O f φ) S)
            (n + 1)) := by
  have hleg := NatTrans.congr_app (IsColimit.comp_coconePointsIsoOfNatIso_hom
    (isColimitTensorKoszulPowerFunctorCocone O f φ)
    (isColimitRestrictKoszulPowerFunctorCocone O f φ)
    (koszulPowerFunctorSystemBaseChangeIso O f φ) n) S
  have hleg' : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).flip.obj
      (RestrictedRingModule φ))).map
        (awayModuleCoconeι (ringedSite O) (prodGlobalSection f S) (n + 1)) ≫
        (awayLocalizationBaseChangeIso O f φ).hom.app S =
      (sheafTensorRightUnitIso O (RestrictedRingModule φ)).hom ≫
        (SheafOfModules.restrictScalars (baseChangeRingSheafMap (ringedSite O) O' φ)).map
          (awayModuleCoconeι (ringedSite O') (prodGlobalSection (baseChangeFamily O f φ) S)
            (n + 1)) := hleg
  have e1 := tensorUnitMap_naturality φ
    (awayModuleCoconeι (ringedSite O) (prodGlobalSection f S) (n + 1))
  have e2 := tensorUnitMap_comp_sheafTensorRightUnitIso_hom O φ
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (awayLocalizationBaseChangeIso O f φ).hom.app S) e1).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hleg').trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) e2)))))

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}] in
/-- Multiplication by a monomial in the `f_i` commutes with `O ⟶ O'`, where on the target it is
multiplication by the monomial in the images of the `f_i`. -/
theorem koszulScalar_comp_structureMap (e : Fin r → ℕ) :
    koszulScalar (ringedSite O) f e ≫ structureMap O φ =
      structureMap O φ ≫
        (SheafOfModules.restrictScalars (baseChangeRingSheafMap (ringedSite O) O' φ)).map
          (koszulScalar (ringedSite O') (baseChangeFamily O f φ) e) := by
  rw [restrictScalars_map_koszulScalar]
  exact ((Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf O)
    (koszulFamily (ringedSite O) f e)).naturality (structureMap O φ)).symm

/-- Multiplication by `f_S` followed by division by `f_S^{1}` is the map `𝒪 ⟶ 𝒪_{f_S}`. -/
private theorem koszulScalar_comp_unit (X : RingedSite.{u, u, u})
    [HasWeakSheafify X.J CommRingCat.{u}]
    (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
    (S : Finset (Fin r)) :
    koszulScalar X f (koszulIndicator S 1) ≫
        awayModuleCoconeι X (prodGlobalSection f S) (0 + 1) =
      unitToAwayModule X (prodGlobalSection f S) :=
  (comp_awayModuleCoconeι_succ X (prodGlobalSection f S) (koszulScalar X f (koszulIndicator S 1))
    (koszulScalar_koszulIndicator_one_app_apply X f S) 0).trans (awayModuleCoconeι_zero _ _)

/-- **`cechSystemBaseChangeMap` is a map over `O`**: composed with `O ⟶ O_{f_S}` it is
`O ⟶ O' ⟶ O'_{f'_S}`. -/
theorem unitToAwayModule_comp_cechSystemBaseChangeMap_app (S : Finset (Fin r)) :
    unitToAwayModule (ringedSite O) (prodGlobalSection f S) ≫
        (cechSystemBaseChangeMap O f φ).app S =
      structureMap O φ ≫
        (SheafOfModules.restrictScalars (baseChangeRingSheafMap (ringedSite O) O' φ)).map
          (unitToAwayModule (ringedSite O') (prodGlobalSection (baseChangeFamily O f φ) S)) := by
  have e3 := awayModuleCoconeι_comp_cechSystemBaseChangeMap_app O f φ S 0
  have e4 := koszulScalar_comp_structureMap O f φ (koszulIndicator S 1)
  rw [← koszulScalar_comp_unit (ringedSite O) f S]
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e3).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e4).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Functor.map_comp _ _ _).symm).trans ?_)))))
  exact congrArg (structureMap O φ ≫
    (SheafOfModules.restrictScalars (baseChangeRingSheafMap (ringedSite O) O' φ)).map ·)
    (koszulScalar_comp_unit (ringedSite O') (baseChangeFamily O f φ) S)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  [HasWeakSheafify J CommRingCat.{u}] in
/-- Restriction of scalars along `φ` carries multiplication by the image of a global section `h`
to multiplication by `h`. -/
theorem restrictScalars_map_awaySmul
    (h : Presheaf.globalSections (O.obj ⋙ forget CommRingCat.{u}))
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (ringedSite O').O)) :
    (SheafOfModules.restrictScalars (baseChangeRingSheafMap (ringedSite O) O' φ)).map
        ((awaySmul (ringedSite O') (baseChangeGlobalSection (ringedSite O) O' φ h)).app M) =
      (awaySmul (ringedSite O) h).app
        ((SheafOfModules.restrictScalars (baseChangeRingSheafMap (ringedSite O) O' φ)).obj M) := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  [HasWeakSheafify J CommRingCat.{u}] in
/-- Restriction of scalars along `φ` carries multiplication by a power of the image of a global
section `h` to multiplication by that power of `h`. -/
theorem restrictScalars_map_awaySmul_pow
    (h : Presheaf.globalSections (O.obj ⋙ forget CommRingCat.{u}))
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (ringedSite O').O))
    (n : ℕ) :
    (SheafOfModules.restrictScalars (baseChangeRingSheafMap (ringedSite O) O' φ)).map
        ((awaySmul (ringedSite O') (baseChangeGlobalSection (ringedSite O) O' φ h) ^ n).app M) =
      (awaySmul (ringedSite O) h ^ n).app
        ((SheafOfModules.restrictScalars (baseChangeRingSheafMap (ringedSite O) O' φ)).obj M) := by
  induction n with
  | zero =>
    rw [awaySmul_pow_app_zero, awaySmul_pow_app_zero]
    exact CategoryTheory.Functor.map_id _ _
  | succ n ih =>
    rw [awaySmul_pow_app_succ, awaySmul_pow_app_succ, CategoryTheory.Functor.map_comp, ih,
      restrictScalars_map_awaySmul]

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}] in
/-- Restriction of scalars along `φ` carries multiplication by `f'_S` to multiplication by
`f_S`. -/
theorem restrictScalars_map_awaySmul_pow_prodGlobalSection (S : Finset (Fin r))
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (ringedSite O').O))
    (n : ℕ) :
    (SheafOfModules.restrictScalars (baseChangeRingSheafMap (ringedSite O) O' φ)).map
        ((awaySmul (ringedSite O') (prodGlobalSection (baseChangeFamily O f φ) S) ^ n).app M) =
      (awaySmul (ringedSite O) (prodGlobalSection f S) ^ n).app
        ((SheafOfModules.restrictScalars (baseChangeRingSheafMap (ringedSite O) O' φ)).obj M) := by
  have h := restrictScalars_map_awaySmul_pow O φ (prodGlobalSection (X := ringedSite O) f S) M n
  rwa [baseChangeGlobalSection_prodGlobalSection] at h

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}] in
/-- A map of systems over `O` is, on the maps `O ⟶ O_{f_S}` divided by `f_S^{n+1}`, the map
`O ⟶ O'` followed by the corresponding map `O' ⟶ O'_{f'_S}`. -/
theorem awayModuleCoconeι_comp_app_of_comp_app
    (β : awayLocalizationFunctor (ringedSite O) f ⟶
      awayLocalizationFunctor (ringedSite O') (baseChangeFamily O f φ) ⋙
        SheafOfModules.restrictScalars (baseChangeRingSheafMap (ringedSite O) O' φ))
    (S : Finset (Fin r))
    (hβ : unitToAwayModule (ringedSite O) (prodGlobalSection f S) ≫ β.app S =
      structureMap O φ ≫
        (SheafOfModules.restrictScalars (baseChangeRingSheafMap (ringedSite O) O' φ)).map
          (unitToAwayModule (ringedSite O') (prodGlobalSection (baseChangeFamily O f φ) S)))
    (n : ℕ) :
    awayModuleCoconeι (ringedSite O) (prodGlobalSection f S) n ≫ β.app S =
      structureMap O φ ≫
        (SheafOfModules.restrictScalars (baseChangeRingSheafMap (ringedSite O) O' φ)).map
          (awayModuleCoconeι (ringedSite O') (prodGlobalSection (baseChangeFamily O f φ) S)
            n) := by
  let R := SheafOfModules.restrictScalars (baseChangeRingSheafMap (ringedSite O) O' φ)
  let A := awayModule (ringedSite O) (prodGlobalSection f S)
  let A' := awayModule (ringedSite O') (prodGlobalSection (baseChangeFamily O f φ) S)
  let s := (awaySmul (ringedSite O) (prodGlobalSection f S) ^ n).app (R.obj A')
  let sA := (awaySmul (ringedSite O) (prodGlobalSection f S) ^ n).app A
  let s' := (awaySmul (ringedSite O') (prodGlobalSection (baseChangeFamily O f φ) S) ^ n).app A'
  have : IsIso sA := isIso_awaySmul_pow_awayModule (ringedSite O) (prodGlobalSection f S) n
  have : IsIso s' := isIso_awaySmul_pow_awayModule (ringedSite O')
    (prodGlobalSection (baseChangeFamily O f φ) S) n
  let es := R.mapIso (asIso s')
  have hes : es.hom = s := restrictScalars_map_awaySmul_pow_prodGlobalSection O f φ S A' n
  have hnat : β.app S ≫ es.hom = sA ≫ β.app S := by
    rw [hes]
    exact (awaySmul (ringedSite O) (prodGlobalSection f S) ^ n).naturality (β.app S)
  have hinv : inv sA ≫ β.app S = β.app S ≫ es.inv := by
    refine (IsIso.inv_comp_eq sA).2 ?_
    exact ((((Category.assoc _ _ _).trans (congrArg (β.app S ≫ ·) es.hom_inv_id)).trans
      (Category.comp_id _)).symm.trans (congrArg (· ≫ es.inv) hnat)).trans (Category.assoc _ _ _)
  have e0 : awayModuleCoconeι (ringedSite O) (prodGlobalSection f S) n ≫ β.app S =
      (unitToAwayModule (ringedSite O) (prodGlobalSection f S) ≫ inv sA) ≫ β.app S := rfl
  exact e0.trans ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hinv).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ es.inv) hβ).trans
      ((Category.assoc _ _ _).trans
        (congrArg (structureMap O φ ≫ ·) (R.map_comp _ _).symm))))))

/-- **`cechSystemBaseChangeMap` is the only map of systems over `O`**: a map of systems
`O_{f_S} ⟶ O'_{f'_S}` of sheaves of `O`-modules which, composed with `O ⟶ O_{f_S}`, is
`O ⟶ O' ⟶ O'_{f'_S}` for every `S`, is `cechSystemBaseChangeMap`.  So the latter is the
canonical map of localizations. -/
theorem eq_cechSystemBaseChangeMap
    (β : awayLocalizationFunctor (ringedSite O) f ⟶
      awayLocalizationFunctor (ringedSite O') (baseChangeFamily O f φ) ⋙
        SheafOfModules.restrictScalars (baseChangeRingSheafMap (ringedSite O) O' φ))
    (hβ : ∀ S : Finset (Fin r),
      unitToAwayModule (ringedSite O) (prodGlobalSection f S) ≫ β.app S =
        structureMap O φ ≫
          (SheafOfModules.restrictScalars (baseChangeRingSheafMap (ringedSite O) O' φ)).map
            (unitToAwayModule (ringedSite O') (prodGlobalSection (baseChangeFamily O f φ) S))) :
    β = cechSystemBaseChangeMap O f φ :=
  NatTrans.ext (funext fun S => awayModule_hom_ext (ringedSite O) f S fun n =>
    (awayModuleCoconeι_comp_app_of_comp_app O f φ β S (hβ S) (n + 1)).trans
      (awayModuleCoconeι_comp_app_of_comp_app O f φ (cechSystemBaseChangeMap O f φ) S
        (unitToAwayModule_comp_cechSystemBaseChangeMap_app O f φ S) (n + 1)).symm)

/-- The map of Čech complexes induced by a composite of maps of systems is the composite. -/
theorem _root_.CategoryTheory.AlternatingCech.complexMap_comp {𝒜 : Type*} [Category 𝒜]
    [Preadditive 𝒜] [HasFiniteProducts 𝒜] {F F' F'' : Finset (Fin r) ⥤ 𝒜}
    (α : F ⟶ F') (β : F' ⟶ F'') :
    AlternatingCech.complexMap (α ≫ β) =
      AlternatingCech.complexMap α ≫ AlternatingCech.complexMap β :=
  HomologicalComplex.hom_ext _ _ fun p => AlternatingCech.mapTerm_comp α β p

section Flat

variable [PreservesFiniteLimits
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).flip.obj
      (RestrictedRingModule φ)))]
  [PreservesFiniteColimits
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).flip.obj
      (RestrictedRingModule φ)))]

omit [PreservesFiniteColimits
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).flip.obj
      (RestrictedRingModule φ))] in
/-- Extension of scalars applied degreewise to `Č(f)`, read through
`tensorExtendedAlternatingCechIso`, is the map of Čech complexes induced by extension of scalars
on the system `S ↦ O_{f_S}`. -/
theorem tensorUnitComplexMap_comp_tensorExtendedAlternatingCechIso_hom :
    tensorUnitComplexMap φ (extendedAlternatingCech (ringedSite O) f) ≫
        (tensorExtendedAlternatingCechIso O f φ).hom =
      AlternatingCech.complexMap (cechSystemTensorUnit O f φ) := by
  let : Functor.Additive (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).flip.obj
      (RestrictedRingModule φ))) :=
    Functor.additive_of_preserves_binary_products _
  refine HomologicalComplex.hom_ext _ _ fun p => ?_
  refine Pi.hom_ext _ _ fun A => ?_
  show ((tensorUnitMap φ
      (AlternatingCech.term (awayLocalizationFunctor (ringedSite O) f) p)).val ≫
      (AlternatingCech.mapTermIso
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).flip.obj
            (RestrictedRingModule φ)))
        (awayLocalizationFunctor (ringedSite O) f) p).hom) ≫ _ =
    AlternatingCech.mapTerm (cechSystemTensorUnit O f φ) p ≫ _
  rw [AlternatingCech.mapTerm_comp_pi, Category.assoc, AlternatingCech.mapTermIso_hom_comp_pi,
    ← tensorUnitMap_naturality]
  rfl

omit [PreservesFiniteColimits
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).flip.obj
      (RestrictedRingModule φ))] in
/-- **The comparison of `FlatNeighbourhoodCech.lean` is the map induced by
`cechSystemBaseChangeMap`**, followed by the identification of `Č(O')` read degreewise over `O`
with `Č(O')` read over `O`. -/
theorem extendedAlternatingCechBaseChangeMap_eq :
    letI : (SheafOfModules.restrictScalars
        (baseChangeRingSheafMap (ringedSite O) O' φ)).Additive :=
      SheafOfModules.instAdditiveRestrictScalars _
    extendedAlternatingCechBaseChangeMap O f φ =
      AlternatingCech.complexMap (cechSystemBaseChangeMap O f φ) ≫
        (AlternatingCech.mapComplexIso (SheafOfModules.restrictScalars
            (baseChangeRingSheafMap (ringedSite O) O' φ))
          (awayLocalizationFunctor (ringedSite O') (baseChangeFamily O f φ))).inv := by
  rw [extendedAlternatingCechBaseChangeMap, extendedAlternatingCechBaseChangeIso,
    cechSystemBaseChangeMap, AlternatingCech.complexMap_comp,
    ← tensorUnitComplexMap_comp_tensorExtendedAlternatingCechIso_hom]
  simp only [Iso.trans_hom]
  rfl

end Flat

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  [HasWeakSheafify J CommRingCat.{u}] in
/-- The ideal sheaf generated by `f₁, …, f_r` is generated by them in the sense of
`IsLocallyGeneratedBySections`: every section is locally an `O`-linear combination of them. -/
theorem isLocallyGeneratedBySections_idealOfGlobalSections :
    IsLocallyGeneratedBySections O f (idealOfGlobalSections (ringedSite O) f).ι := by
  intro Y t
  obtain ⟨S, hS, hle⟩ := (mem_idealOfGlobalSections_iff (ringedSite O) f Y).1 t.2
  refine ⟨S, hS, fun Z g hg => ?_⟩
  obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (ringedSite O).O).obj.obj
      (Opposite.op Z))).1 (hle g hg)
  exact ⟨c, hc.symm⟩

/-- **Stacks Project, Tag 099H.**  Let `C` be a site, let `φ : O ⟶ O'` be a flat homomorphism
of sheaves of commutative rings on `C`, and let `f₁, …, f_r` be global sections of `O` such that
the canonical map `O/(f₁, …, f_r) ⟶ O'/(f₁, …, f_r)O'` of sheaves of `O`-modules
(`Stacks.SheafOfModules.DerivedRestrictScalars.quotientMap`) is an isomorphism; here
`(f₁, …, f_r)` is the ideal sheaf generated by the `f_k`
(`AlgebraicGeometry.RingedSite.idealOfGlobalSections`) and `(f₁, …, f_r)O'` is the ideal sheaf of
`O'` it generates (`AlgebraicGeometry.RingedSite.extendIdeal`), which is the ideal sheaf generated
by the images of the `f_k`
(`Stacks.Sheaves.CechFlatNeighbourhood.extendedIdeal_idealOfGlobalSections`). Then the map of
extended alternating Čech complexes

`O → ∏_{i₀} O_{f_{i₀}} → ∏_{i₀ < i₁} O_{f_{i₀}f_{i₁}} → ⋯ → O_{f₁⋯f_r}`
`  ⟶ O' → ∏_{i₀} O'_{f_{i₀}} → ∏_{i₀ < i₁} O'_{f_{i₀}f_{i₁}} → ⋯ → O'_{f₁⋯f_r}`

is a quasi-isomorphism.  The map is the one induced by the canonical maps
`O_{f_S} ⟶ O'_{f_S}` of sheaves of `O`-modules, `cechSystemBaseChangeMap`: they are compatible
with `O ⟶ O_{f_S}` and `O ⟶ O' ⟶ O'_{f_S}`
(`unitToAwayModule_comp_cechSystemBaseChangeMap_app`), and they are the only such family
(`eq_cechSystemBaseChangeMap`).  The lower complex is the extended alternating Čech complex of
the system `S ↦ O'_{f_S}` of sheaves of `O`-modules.

The proof is the source's: `quasiIso_extendedAlternatingCechBaseChangeMap`. -/
@[stacks 099H]
theorem quasiIso_complexMap_cechSystemBaseChangeMap (hφ : IsFlatMap φ)
    (hiso : IsIso (Stacks.SheafOfModules.DerivedRestrictScalars.quotientMap φ
      (idealOfGlobalSections (ringedSite O) f))) :
    QuasiIso (AlternatingCech.complexMap (cechSystemBaseChangeMap O f φ)) := by
  have : PreservesFiniteLimits
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).flip.obj
        (RestrictedRingModule φ))) := hφ.1
  have : PreservesFiniteColimits
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).flip.obj
        (RestrictedRingModule φ))) := hφ.2
  let : (SheafOfModules.restrictScalars
      (baseChangeRingSheafMap (ringedSite O) O' φ)).Additive :=
    SheafOfModules.instAdditiveRestrictScalars _
  obtain ⟨e, he⟩ := Stacks.SheafOfModules.DerivedRestrictScalars.exists_quotientIso_of_isIso φ
    (idealOfGlobalSections (ringedSite O) f) hiso
  have hq := quasiIso_extendedAlternatingCechBaseChangeMap O f φ
    (idealOfGlobalSections (ringedSite O) f).ι e he
    (isLocallyGeneratedBySections_idealOfGlobalSections O f)
  rw [extendedAlternatingCechBaseChangeMap_eq] at hq
  have hc : AlternatingCech.complexMap (cechSystemBaseChangeMap O f φ) =
      (AlternatingCech.complexMap (cechSystemBaseChangeMap O f φ) ≫
        (AlternatingCech.mapComplexIso (SheafOfModules.restrictScalars
            (baseChangeRingSheafMap (ringedSite O) O' φ))
          (awayLocalizationFunctor (ringedSite O') (baseChangeFamily O f φ))).inv) ≫
        (AlternatingCech.mapComplexIso (SheafOfModules.restrictScalars
            (baseChangeRingSheafMap (ringedSite O) O' φ))
          (awayLocalizationFunctor (ringedSite O') (baseChangeFamily O f φ))).hom := by
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hc]
  exact quasiIso_comp _ _ (hφ := hq) (hφ' := quasiIso_of_isIso _)

/-- [Stacks, Tag 099H] for any map of systems over `O`: by `eq_cechSystemBaseChangeMap` it is
`cechSystemBaseChangeMap`. -/
theorem quasiIso_complexMap_of_isFlatMap (hφ : IsFlatMap φ)
    (hiso : IsIso (Stacks.SheafOfModules.DerivedRestrictScalars.quotientMap φ
      (idealOfGlobalSections (ringedSite O) f)))
    (β : awayLocalizationFunctor (ringedSite O) f ⟶
      awayLocalizationFunctor (ringedSite O') (baseChangeFamily O f φ) ⋙
        SheafOfModules.restrictScalars (baseChangeRingSheafMap (ringedSite O) O' φ))
    (hβ : ∀ S : Finset (Fin r),
      unitToAwayModule (ringedSite O) (prodGlobalSection f S) ≫ β.app S =
        structureMap O φ ≫
          (SheafOfModules.restrictScalars (baseChangeRingSheafMap (ringedSite O) O' φ)).map
            (unitToAwayModule (ringedSite O') (prodGlobalSection (baseChangeFamily O f φ) S))) :
    QuasiIso (AlternatingCech.complexMap β) := by
  rw [eq_cechSystemBaseChangeMap O f φ β hβ]
  exact quasiIso_complexMap_cechSystemBaseChangeMap O f φ hφ hiso

end Stacks.Sheaves.CechFlatNeighbourhood

end
