module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyLocalSplittingFromBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01Open
public import StacksFrontier.AlgebraicGeometry.Quot.ExtendsFibreIsoNearPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPushforwardHigherDirectImages
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UnitRestrictScalarsIsoAnySite
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforwardExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness
public import StacksFrontier.Homology.Perfect.MinimalComplexUnitSplitting
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffinePerfectStrictlyPerfectModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleStructureSheafPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedPerfectAnnihilator
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeCoefficients

/-!
# Parts (2) and (3) of Stacks 0E1J, with nothing assumed

Let `f : X → S` be a family of curves (Stacks 0D4Z) with `κ(s) = H⁰(X_s, 𝒪_{X_s})` for every point
`s` of the base. Parts (2) and (3) of Stacks 0E1J say that `R¹f_*𝒪_X` is a finite locally free
`𝒪_S`-module whose formation commutes with arbitrary base change.
`firstHigherDirectImage_of_baseChange_of_affineSplitting` reduces both to two inputs, which are
proved here:

* the base change clause of Stacks 0CTM (1) at `𝒪_X`: `Lh^*Rf_*𝒪_X ⟶ Rf'_*𝒪_{X'}` is invertible
  for every morphism of families, `f` being flat, quasi-compact and quasi-separated
  (`AlgebraicGeometry.Space.isIso_smallEtaleDerivedBaseChangeMap_of_isFlat`);
* the splitting of Stacks 0E6B (b): étale locally on `S`, `Rf_*𝒪_X ≅ 𝒪_S ⊕ P` with `P` strictly
  perfect in degrees `≥ 1`.

The splitting follows the source's proof. `Rf_*𝒪_X` is perfect (Stacks 0A1P), so on an affine étale
chart `V = Spec A` of the base it is `M^~` for a bounded complex `M` of finite projective
`A`-modules. For every affine `W ⟶ V`, cohomology and base change identifies `M ⊗^L_A Γ(W)` with
`RΓ(X_W, 𝒪)`, which has no cohomology in negative degrees and `H⁰ = Γ(W)`, the structure map
`𝒪_W ⟶ (f_W)_*𝒪` being invertible (Stacks 0E6B (a), from `k = H⁰(X_k, 𝒪)` on all field fibres,
which the hypothesis on residue fields gives by the openness of that locus). At a prime `𝔭` the
minimal representative of Stacks 0BCD of `M` near `𝔭` is then `A_f` in degree zero followed by
free modules, its degree-zero cohomology is free of rank one, so its first differential vanishes
and it splits off `A_f[0]` (`StacksDraft.Perfect.exists_notMem_iso_single_biprod_of_fibre`).

## Main results

* `hasBijectiveGlobalFunctionsOnFieldFibres_of_hasResidueFieldGlobalFunctions`: `κ(s) = H⁰(X_s, 𝒪)`
  at every point gives `k = H⁰(X_k, 𝒪)` at every field-valued point.
* `hasUniversallyBijectiveGlobalFunctions_of_hasResidueFieldGlobalFunctions`: `κ(s) = H⁰(X_s, 𝒪)`
  at every point gives `f_*𝒪_X = 𝒪_S` universally (Stacks 0E1J (1)).
* `hasDerivedStructureSheafBaseChange`: Stacks 0CTM (1) at `𝒪_X`.
* `homology_representedAffineDerivedExtension`: the derived sections of `Rf_*𝒪_X` over an affine
  chart, after base change to an affine object.
* `hasAffineStrictlyPerfectLocalSplitting_of_fieldFibres`: Stacks 0E6B (b) for a family of curves.
* `firstHigherDirectImage_of_hasResidueFieldGlobalFunctions`: parts (2) and (3) of Stacks 0E1J for
  every family of curves with `κ(s) = H⁰(X_s, 𝒪)` at every point of the base.

## Implementation notes

The derived categories are the standard models, fixed by `letI` inside the statements, which is
the model in which `firstHigherDirectImage_of_baseChange_of_affineSplitting` and the base change
theorem are stated.

## References

* [Stacks Project, Tag 0E1J](https://stacks.math.columbia.edu/tag/0E1J)
* [Stacks Project, Tag 0E6B](https://stacks.math.columbia.edu/tag/0E6B)
* [Stacks Project, Tag 0CTM](https://stacks.math.columbia.edu/tag/0CTM)
* [Stacks Project, Tag 0A1P](https://stacks.math.columbia.edu/tag/0A1P)
* [Stacks Project, Tag 0BCD](https://stacks.math.columbia.edu/tag/0BCD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

namespace CurveFamily

/-- The point of the base underlying the residue-field-valued point at `s` is `s`. -/
theorem schemePoint_residueFieldValuedPoint (X : CurveFamily B hZ) (s : X.base.left.1) :
    Space.schemePoint B integerBase hZ X.base (residueFieldValuedPoint B hZ X.base s) = s :=
  X.base.left.1.fromSpecResidueField_apply s _

/-- **`κ(s) = H⁰(X_s, 𝒪)` at every point gives `k = H⁰(X_k, 𝒪)` at every field-valued point.**
The locus of field-valued points where `k = H⁰` holds is a neighbourhood of each of its points
(`exists_isOpen_forall_isH0BijectiveAt`), and every field-valued point has the same point as the
residue-field point under it. -/
theorem hasBijectiveGlobalFunctionsOnFieldFibres_of_hasResidueFieldGlobalFunctions
    {X : CurveFamily B hZ} (hX : X.HasResidueFieldGlobalFunctions) :
    HasBijectiveGlobalFunctionsOnFieldFibres B hZ X := by
  intro q
  let s := Space.schemePoint B integerBase hZ X.base q
  obtain ⟨Ω, -, hpΩ, hq⟩ := exists_isOpen_forall_isH0BijectiveAt
    (residueFieldValuedPoint B hZ X.base s) (hX s)
  refine hq q ?_
  have hc : q.class B integerBase hZ _ =
      (residueFieldValuedPoint B hZ X.base s).class B integerBase hZ _ :=
    Space.class_eq_class_of_schemePoint_eq X.base _ _
      (schemePoint_residueFieldValuedPoint X s).symm
  rwa [hc]

/-- **`f_*𝒪_X = 𝒪_S` universally from `κ(s) = H⁰(X_s, 𝒪)` at every point** (Stacks 0E1J,
part (1)). -/
theorem hasUniversallyBijectiveGlobalFunctions_of_hasResidueFieldGlobalFunctions
    {X : CurveFamily B hZ} (hX : X.HasResidueFieldGlobalFunctions) :
    HasUniversallyBijectiveGlobalFunctions B hZ X :=
  hasUniversallyBijectiveGlobalFunctions_of_fieldFibres _
    (hasBijectiveGlobalFunctionsOnFieldFibres_of_hasResidueFieldGlobalFunctions hX)

/-- **The base change clause of Stacks 0CTM, part (1), at `𝒪_X`, for every family of curves**:
the structure morphism is flat, quasi-compact and quasi-separated, so the base change map
`Lh^*Rf_*𝒪_X ⟶ Rf'_*𝒪_{X'}` is invertible for every morphism of families
(`AlgebraicGeometry.Space.isIso_smallEtaleDerivedBaseChangeMap_of_isFlat`). -/
theorem hasDerivedStructureSheafBaseChange (X : CurveFamily B hZ) :
    X.HasDerivedStructureSheafBaseChange := fun _ a =>
  Space.isIso_smallEtaleDerivedBaseChangeMap_of_isFlat a.cartesian X.proper.2.1.2
    (Space.isQuasiSeparated_of_isSeparated B integerBase hZ X.proper.1) X.flat _
    (Space.qcohDerived_singleFunctor_structureModule (hX := X.total.2))

end CurveFamily

/-! ### `H⁰(Rf_*𝒪_X) = 𝒪_Y` when the structure map is invertible -/

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- **`f_*𝒪_X = 𝒪_Y` as modules when `f♯ : 𝒪_Y ⟶ f_*𝒪_X` is invertible**: the direct image of
the unit module is the restriction of scalars along `f♯` of the unit module of `f_*𝒪_X`
(`Stacks.Sheaves.ToposPullback.pullbackModuleUnitIso`, which is `Iso.refl`). -/
noncomputable def structureSheafModuleIsoModulePushforward (f : X ⟶ Y)
    [IsIso (structureSharp B S hS f)] :
    structureSheafModule B S hS Y ≅
      (modulePushforward B S hS f).obj (structureSheafModule B S hS X) :=
  Stacks.SheafOfModules.ChangeOfRings.unitRestrictScalarsIsoOfIsoAnySite
    (asIso (structureSharp B S hS f))

section Derived

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives
attribute [local instance] isGrothendieckAbelian_modules

/-- **`H⁰(Rf_*𝒪_X) ≅ 𝒪_Y` when `f♯` is invertible.** -/
noncomputable def homologyZeroDerivedPushforwardStructureSheafIso (f : X ⟶ Y)
    [IsIso (structureSharp B S hS f)] :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS Y.1 Y.2)
    (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) 0).obj
        ((smallEtaleDerivedModulePushforward B S hS f).obj
          ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj
            (structureSheafModule B S hS X))) ≅
      structureSheafModule B S hS Y :=
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS Y.1 Y.2)
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  (DerivedCategory.homologyFunctor _ 0).mapIso
      ((smallEtaleDerivedModulePushforwardIso B S hS f).app _) ≪≫
    homologyDerivedModulePushforwardSingleIso B S hS f (structureSheafModule B S hS X) 0 0 0
      (by norm_num) ≪≫
    (modulePushforward B S hS f).rightDerivedZeroIsoSelf.app _ ≪≫
    (structureSheafModuleIsoModulePushforward B S hS f).symm

/-- **`Rf_*𝒪_X` has no cohomology in negative degrees.** -/
theorem isZero_homology_derivedPushforward_structureSheaf_of_neg (f : X ⟶ Y) (i : ℤ)
    (hi : i < 0) :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS Y.1 Y.2)
    IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).obj
        ((smallEtaleDerivedModulePushforward B S hS f).obj
          ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj
            (structureSheafModule B S hS X)))) := by
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS Y.1 Y.2)
  have := Stacks.DerivedFunctor.isGE_totalRightDerived_obj (modulePushforward B S hS f)
    ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj
      (structureSheafModule B S hS X)) 0
  exact (DerivedCategory.isZero_of_isGE _ 0 i hi).of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso
      ((smallEtaleDerivedModulePushforwardIso B S hS f).app _))

end Derived

end Space

/-! ### The derived sections of `Rf_*𝒪_X` over an affine chart, after base change -/

attribute [local instance] Space.etaleModulePullback_additive
  Space.preservesFiniteLimits_etaleModulePullback Space.preservesFiniteColimits_etaleModulePullback

namespace CurveFamily

/-- If `k = H⁰(X_k, 𝒪)` on every fibre over a field, the structure map of every base change of
the family is invertible (Stacks 0E6B (a)). -/
theorem isIso_structureSharp_baseChange_toBase {X : CurveFamily B hZ}
    (hX : HasBijectiveGlobalFunctionsOnFieldFibres B hZ X) {V : BigFppfOver B integerBase hZ}
    (h : V ⟶ X.base) :
    IsIso (Space.structureSharp B integerBase hZ (X.baseChange h).toBase) := by
  have hY : HasBijectiveGlobalFunctionsOnFieldFibres B hZ (X.baseChange h) := fun q =>
    (isH0BijectiveAt_iff_of_hom (X.baseChangeHom h) q).2 (hX _)
  exact (Space.isIso_structureSharp_and_baseChange_of_bijective_algebraMap_fibre B integerBase hZ
    (X.baseChange h).toBase (X.baseChange h).proper (X.baseChange h).flat
    (X.baseChange h).finitePresentation fun p =>
      Space.bijective_algebraMap_fibreOverFieldValuedPoint_of_bijective B integerBase hZ
        (X.baseChange h).toBase.hom p (X.baseChange h).total.2
        (schemeSpace (X.baseChange h).base).2 (hY p)).1

/-- **The derived sections of `Rf_*𝒪_X` over an affine chart, base changed to an affine object,
are `Γ` in degree zero and nothing below.** Let `X` be a family of curves with `k = H⁰(X_k, 𝒪)` on
every fibre over a field, `V = Spec A` an affine étale chart of the base and `M ∈ D(A)` with
`M^~ ≅ (Rf_*𝒪_X)|_V`. For every morphism `w : W ⟶ V` from an affine object of the site,
`M ⊗^L_A Γ(W)` has no cohomology in negative degrees and its degree-zero cohomology is free of
rank one: by cohomology and base change (`hasDerivedStructureSheafBaseChange`) it is
`RΓ(X_W, 𝒪)`, and `H⁰(R(f_W)_*𝒪) = 𝒪_W` since the structure map of `X_W ⟶ W` is invertible. -/
theorem homology_representedAffineDerivedExtension {X : CurveFamily B hZ}
    (hX : HasBijectiveGlobalFunctionsOnFieldFibres B hZ X)
    (V : Space.SmallEtale B integerBase hZ (schemeSpace X.base).1)
    [IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj (X.chartObject V))]
    (M :
      letI := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B integerBase
        hZ).obj (X.chartObject V), ⊤))
      DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B integerBase hZ).obj
        (X.chartObject V), ⊤)))
    (eM :
      letI := HasDerivedCategory.standard
        (Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2)
      letI := HasDerivedCategory.standard
        (Space.Modules.{u, u} B integerBase hZ (schemeSpace X.base).1 (schemeSpace X.base).2)
      letI := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B integerBase
        hZ).obj (X.chartObject V), ⊤))
      letI := HasDerivedCategory.standard
        (Space.Modules.{u, u} B integerBase hZ
          (Space.chartSpace B integerBase hZ (schemeSpace X.base) V).1
          (Space.chartSpace B integerBase hZ (schemeSpace X.base) V).2)
      (Space.etaleModulePullback.{u, u} B integerBase hZ
          (Space.chartToSpace B integerBase hZ (schemeSpace X.base) V)
          (Space.isEtale_chartToSpace B integerBase hZ (schemeSpace X.base)
              V)).mapDerivedCategory.obj
          ((Space.smallEtaleDerivedModulePushforward B integerBase hZ X.toBase).obj
            ((DerivedCategory.singleFunctor
              (Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2) 0).obj
              (Space.structureSheafModule B integerBase hZ X.total))) ≅
        (Space.representedAffineDerivedAssociated B integerBase hZ (X.chartObject V)).obj M)
    {W : BigFppfOver B integerBase hZ} [IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj W)]
    (w : W ⟶ X.chartObject V) :
    letI := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B integerBase
        hZ).obj (X.chartObject V), ⊤))
    letI := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B integerBase
        hZ).obj W, ⊤))
    (∀ i : ℤ, i < 0 → IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((Space.representedAffineDerivedExtension B integerBase hZ w).functor.obj M))) ∧
    Nonempty ((DerivedCategory.homologyFunctor _ 0).obj
      ((Space.representedAffineDerivedExtension B integerBase hZ w).functor.obj M) ≅
        ModuleCat.of Γ((BigFppfOver.toScheme B integerBase hZ).obj W, ⊤)
          Γ((BigFppfOver.toScheme B integerBase hZ).obj W, ⊤)) := by
  let := HasDerivedCategory.standard
    (Space.Modules.{u, u} B integerBase hZ (X.total).1 (X.total).2)
  let := HasDerivedCategory.standard
    (Space.Modules.{u, u} B integerBase hZ (schemeSpace X.base).1 (schemeSpace X.base).2)
  let := HasDerivedCategory.standard
    (Space.Modules.{u, u} B integerBase hZ (Space.chartSpace B integerBase hZ (schemeSpace X.base)
        V).1 (Space.chartSpace B integerBase hZ (schemeSpace X.base) V).2)
  let := HasDerivedCategory.standard
    (Space.Modules.{u, u} B integerBase hZ (yoneda.obj W)
      (isAlgebraicSpace_yoneda B integerBase hZ W))
  let jV : (X.chartObject V) ⟶ X.base := yoneda.preimage V.obj.hom
  let h : W ⟶ X.base := w ≫ jV
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B integerBase hZ (schemeSpace
        (X.baseChange h).base)))
  have hbcF := X.hasDerivedStructureSheafBaseChange (X.baseChange h) (X.baseChangeHom h)
  let gY := Space.representedSpaceMap B integerBase hZ w
  have hw : gY ≫ Space.chartToSpace B integerBase hZ (schemeSpace X.base) V =
      schemeSpaceMap (X.baseChangeHom h).baseMap := by
    refine InducedCategory.hom_ext ?_
    change yoneda.map w ≫ V.obj.hom = yoneda.map (w ≫ jV)
    rw [Functor.map_comp]
    congr 1
    exact (Functor.map_preimage yoneda
      (V.obj.hom : yoneda.obj (X.chartObject V) ⟶ yoneda.obj X.base)).symm
  let R := (Space.smallEtaleDerivedModulePushforward B integerBase hZ X.toBase).obj
    ((DerivedCategory.singleFunctor
      (Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2) 0).obj
      (Space.structureSheafModule B integerBase hZ X.total))
  let Lg := Space.smallEtaleDerivedModulePullback B integerBase hZ gY
  let c₁ : Lg.obj ((Space.etaleModulePullback.{u, u} B integerBase hZ
      (Space.chartToSpace B integerBase hZ (schemeSpace X.base) V)
      (Space.isEtale_chartToSpace B integerBase hZ (schemeSpace X.base) V)).mapDerivedCategory.obj
        R) ≅ (Space.smallEtaleDerivedModulePullback B integerBase hZ
          (schemeSpaceMap (X.baseChangeHom h).baseMap)).obj R :=
    Lg.mapIso ((Space.smallEtaleDerivedModulePullbackIsoEtale B integerBase hZ
        (Space.chartToSpace B integerBase hZ (schemeSpace X.base) V)
        (Space.isEtale_chartToSpace B integerBase hZ (schemeSpace X.base) V)).app R).symm ≪≫
      (Space.smallEtaleDerivedModulePullbackCompIso B integerBase hZ gY
        (Space.chartToSpace B integerBase hZ (schemeSpace X.base) V)).app R ≪≫
      (Space.smallEtaleDerivedModulePullbackCongr B integerBase hZ hw).app R
  let c₂ := @asIso _ _ _ _ _ hbcF ≪≫
    (Space.smallEtaleDerivedModulePushforward B integerBase hZ (X.baseChange h).toBase).mapIso
      (Space.smallEtaleDerivedModulePullbackUnitIso (B := B) (S := integerBase) (hS := hZ)
        (X.baseChangeHom h).totalMap)
  let β := Space.representedAffineDerivedBaseChangeIso B integerBase hZ w
  let T := (β.app M).symm ≪≫ Lg.mapIso eM.symm ≪≫ c₁ ≪≫ c₂
  have hFF := Space.representedAffineAssociatedFullyFaithful B integerBase hZ W
  let Hi := fun i : ℤ =>
    (((Space.representedAffineAssociated B integerBase hZ W).mapDerivedCategoryHomologyIso
      i).app ((Space.representedAffineDerivedExtension B integerBase hZ w).functor.obj M)).symm ≪≫
    (DerivedCategory.homologyFunctor (SheafOfModules.{u}
        (Space.ringedToposStructureRingSheaf B integerBase hZ (schemeSpace
          (X.baseChange h).base))) i).mapIso T
  refine ⟨fun i hi => ?_, ⟨?_⟩⟩
  · have hZa := (Space.isZero_homology_derivedPushforward_structureSheaf_of_neg B integerBase hZ
      (X.baseChange h).toBase i hi).of_iso (Hi i)
    rw [IsZero.iff_id_eq_zero]
    exact hFF.map_injective (by
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
      exact hZa.eq_of_src _ _)
  · have := isIso_structureSharp_baseChange_toBase hX h
    exact hFF.preimageIso (Hi 0 ≪≫
      Space.homologyZeroDerivedPushforwardStructureSheafIso B integerBase hZ
        (X.baseChange h).toBase ≪≫
      (Space.representedAffineAssociatedObjUnitIso B integerBase hZ W).symm)

/-- **`Rf_*𝒪_X` is perfect for a family of curves** (Stacks 0A1P at `E = 𝒪_X[0]`, `𝒢 = 𝒪_X`):
the structure morphism is flat, proper and of finite presentation. -/
theorem isPerfect_derivedPushforward_structureSheaf (X : CurveFamily B hZ) :
    letI := HasDerivedCategory.standard
      (Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2)
    letI := HasDerivedCategory.standard
      (Space.Modules.{u, u} B integerBase hZ (schemeSpace X.base).1 (schemeSpace X.base).2)
    (Space.smallEtaleRingedSite B integerBase hZ (schemeSpace X.base).1
      (schemeSpace X.base).2).IsPerfect
      ((Space.smallEtaleDerivedModulePushforward B integerBase hZ X.toBase).obj
        ((DerivedCategory.singleFunctor
          (Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2) 0).obj
          (Space.structureSheafModule B integerBase hZ X.total))) := by
  let := HasDerivedCategory.standard
    (Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2)
  let := HasDerivedCategory.standard
    (Space.Modules.{u, u} B integerBase hZ (schemeSpace X.base).1 (schemeSpace X.base).2)
  have hft := Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B integerBase hZ
    X.finitePresentation.1
  have h := Space.isPerfect_derivedModulePushforward_derivedTensor_single X.toBase
    X.finitePresentation _
    (Space.isPerfect_derivedStructureSheaf B integerBase hZ X.total.1 X.total.2)
    (Space.structureSheafModule B integerBase hZ X.total) inferInstance
    (Space.isFlatOver_structureSheafModule B integerBase hZ X.toBase X.flat)
    (Space.hasProperSupport_structureSheafModule B integerBase hZ X.toBase X.proper hft)
  exact RingedSite.IsPerfect.of_iso _ h
    ((Space.derivedModulePushforward B integerBase hZ X.toBase).mapIso
    (Space.smallEtaleDerivedTensorUnitLeftIso B integerBase hZ X.total _))

/-- **`(Rf_*𝒪_X)|_V = M^~` for a bounded complex `M` of finite projective modules over an affine
chart `V = Spec A`**: `Rf_*𝒪_X` is perfect (`isPerfect_derivedPushforward_structureSheaf`), hence
so is its restriction to `V`, which therefore has a strictly perfect model, the associated
complex of its complex of sections. -/
theorem exists_chartModel (X : CurveFamily B hZ)
    (V : Space.SmallEtale B integerBase hZ (schemeSpace X.base).1)
    [IsAffine (Space.chartScheme V)] :
    ∃ (N : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B integerBase hZ).obj
        (X.chartObject V), ⊤)) ℤ) (n b : ℤ), N.IsStrictlyGE n ∧ N.IsStrictlyLE b ∧
      (∀ j, Module.Finite Γ((BigFppfOver.toScheme B integerBase hZ).obj (X.chartObject V), ⊤)
        (N.X j)) ∧
      (∀ j, Module.Projective Γ((BigFppfOver.toScheme B integerBase hZ).obj (X.chartObject V), ⊤)
        (N.X j)) ∧
      letI := HasDerivedCategory.standard
        (Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2)
      letI := HasDerivedCategory.standard
        (Space.Modules.{u, u} B integerBase hZ (schemeSpace X.base).1 (schemeSpace X.base).2)
      letI := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B integerBase
        hZ).obj (X.chartObject V), ⊤))
      letI := HasDerivedCategory.standard
        (Space.Modules.{u, u} B integerBase hZ
          (Space.chartSpace B integerBase hZ (schemeSpace X.base) V).1
          (Space.chartSpace B integerBase hZ (schemeSpace X.base) V).2)
      Nonempty ((Space.etaleModulePullback.{u, u} B integerBase hZ
          (Space.chartToSpace B integerBase hZ (schemeSpace X.base) V)
          (Space.isEtale_chartToSpace B integerBase hZ (schemeSpace X.base)
              V)).mapDerivedCategory.obj
          ((Space.smallEtaleDerivedModulePushforward B integerBase hZ X.toBase).obj
            ((DerivedCategory.singleFunctor
              (Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2) 0).obj
              (Space.structureSheafModule B integerBase hZ X.total))) ≅
        (Space.representedAffineDerivedAssociated B integerBase hZ (X.chartObject V)).obj
          (DerivedCategory.Q.obj N)) := by
  have hEV := Space.isPerfect_etaleModulePullback_standard B integerBase hZ
    (Space.chartToSpace B integerBase hZ (schemeSpace X.base) V)
    (Space.isEtale_chartToSpace B integerBase hZ (schemeSpace X.base) V) _
    (isPerfect_derivedPushforward_structureSheaf X)
  obtain ⟨PV, hPV, ⟨eV⟩⟩ := Space.exists_isStrictlyPerfect_iso_of_isPerfect B integerBase hZ
    (X.chartObject V) _ hEV
  obtain ⟨n, -, hn, -⟩ := Space.exists_isStrictlyGE_isStrictlyLE_of_isStrictlyPerfect B
    integerBase hZ (X.chartObject V) PV hPV
  obtain ⟨N, bN, hNn, hNb, hfin, hproj, ⟨eN⟩⟩ :=
    Space.exists_isStrictlyGE_iso_representedAffineDerivedAssociated_of_isStrictlyPerfect B
      integerBase hZ (X.chartObject V) PV hPV n (hn := hn)
  exact ⟨N, n, bN, hNn, hNb, hfin, hproj, ⟨eV ≪≫ eN.symm⟩⟩

/-- **The splitting of `M ⊗_A A_f`.** Let `X` be a family of curves with `k = H⁰(X_k, 𝒪)` on every
fibre over a field, `V = Spec A` an affine étale chart of the base and `M` a bounded complex of
finite projective `A`-modules with `M^~ ≅ (Rf_*𝒪_X)|_V`. At a prime `𝔭` the derived fibre of `M` is
`κ(𝔭)` in degree zero and nothing below, and `H⁰(M ⊗_A Γ(D(f))) ≅ Γ(D(f))` for every `f`
(`homology_representedAffineDerivedExtension`), so near `𝔭`, `M ⊗_A Γ(D(f))` is `Γ(D(f))` in degree
zero plus a bounded complex of finite projective modules in degrees `≥ 1`
(`StacksDraft.Perfect.exists_notMem_iso_single_biprod_of_fibre`). -/
theorem exists_notMem_iso_single_biprod_chart {X : CurveFamily B hZ}
    (hX : HasBijectiveGlobalFunctionsOnFieldFibres B hZ X)
    (V : Space.SmallEtale B integerBase hZ (schemeSpace X.base).1)
    [IsAffine (Space.chartScheme V)]
    (N : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B integerBase hZ).obj
        (X.chartObject V), ⊤)) ℤ) (n bN : ℤ) [N.IsStrictlyGE n] [N.IsStrictlyLE bN]
    (hfin : ∀ j, Module.Finite Γ((BigFppfOver.toScheme B integerBase hZ).obj (X.chartObject V), ⊤)
        (N.X j))
    (hproj : ∀ j, Module.Projective Γ((BigFppfOver.toScheme B integerBase hZ).obj
        (X.chartObject V), ⊤) (N.X j))
    (eM :
      letI := HasDerivedCategory.standard
        (Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2)
      letI := HasDerivedCategory.standard
        (Space.Modules.{u, u} B integerBase hZ (schemeSpace X.base).1 (schemeSpace X.base).2)
      letI := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B integerBase
        hZ).obj (X.chartObject V), ⊤))
      letI := HasDerivedCategory.standard
        (Space.Modules.{u, u} B integerBase hZ
          (Space.chartSpace B integerBase hZ (schemeSpace X.base) V).1
          (Space.chartSpace B integerBase hZ (schemeSpace X.base) V).2)
      (Space.etaleModulePullback.{u, u} B integerBase hZ
          (Space.chartToSpace B integerBase hZ (schemeSpace X.base) V)
          (Space.isEtale_chartToSpace B integerBase hZ (schemeSpace X.base)
              V)).mapDerivedCategory.obj
          ((Space.smallEtaleDerivedModulePushforward B integerBase hZ X.toBase).obj
            ((DerivedCategory.singleFunctor
              (Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2) 0).obj
              (Space.structureSheafModule B integerBase hZ X.total))) ≅
        (Space.representedAffineDerivedAssociated B integerBase hZ (X.chartObject V)).obj
          (DerivedCategory.Q.obj N))
    (p : Ideal Γ(Space.chartScheme V, ⊤)) [p.IsPrime] :
    ∃ f : Γ(Space.chartScheme V, ⊤), f ∉ p ∧
      ∃ (T : CochainComplex (ModuleCat.{u} Γ(Space.chartScheme (Space.openChart B integerBase hZ _ V
          ((Space.chartScheme V).basicOpen f)), ⊤)) ℤ) (bT : ℤ),
        T.IsStrictlyGE 1 ∧ T.IsStrictlyLE bT ∧
        (∀ j, Module.Finite Γ(Space.chartScheme (Space.openChart B integerBase hZ _ V
          ((Space.chartScheme V).basicOpen f)), ⊤) (T.X j)) ∧
        (∀ j, Module.Projective Γ(Space.chartScheme (Space.openChart B integerBase hZ _ V
          ((Space.chartScheme V).basicOpen f)), ⊤) (T.X j)) ∧
        letI := HasDerivedCategory.standard (ModuleCat.{u} Γ(Space.chartScheme
          (Space.openChart B integerBase hZ _ V ((Space.chartScheme V).basicOpen f)), ⊤))
        Nonempty (DerivedCategory.Q.obj (StacksDraft.Perfect.FibreCycleLift.fibreComplex
            (Space.representedAffineCommRingCatHom B integerBase hZ
              ((Space.SmallEtale.toOver B integerBase hZ (schemeSpace X.base).1).map
                (Space.openChartInclusion B integerBase hZ _ V
                  ((Space.chartScheme V).basicOpen f)))).hom N) ≅
          (DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of _ Γ(Space.chartScheme
            (Space.openChart B integerBase hZ _ V ((Space.chartScheme V).basicOpen f)), ⊤)) ⊞
            DerivedCategory.Q.obj T) := by
  classical
  have : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj (X.chartObject V)) :=
    inferInstanceAs (IsAffine (Space.chartScheme V))
  have : ∀ j, Projective (N.X j) := fun j => (IsProjective.iff_projective (N.X j)).mp (hproj j)
  let w := Space.primeResidueMap B integerBase hZ (X.chartObject V) p
  have key := homology_representedAffineDerivedExtension hX V (DerivedCategory.Q.obj N) eM w
  have hnegW := key.1
  have h0W := key.2.some
  have hneg : ∀ j : ℤ, j < 0 → IsZero ((StacksDraft.Perfect.FibreCycleLift.fibreComplex
      (algebraMap _ p.ResidueField) N).homology j) := by
    intro j hj
    have h := StacksDraft.Perfect.isZero_homology_fibreComplex_comp_ringEquiv
      (Space.representedAffineCommRingCatHom B integerBase hZ w).hom
      (Space.primeResidueRingEquiv B integerBase hZ (X.chartObject V) p) N j
      ((hnegW j hj).of_iso (StacksDraft.Perfect.homologyTotalDerivedExtensionScalarsQIso _
        (Space.representedAffineDerivedExtension B integerBase hZ w) N bN j).symm)
    rwa [Space.primeResidueRingEquiv_comp] at h
  have hrank : Module.finrank p.ResidueField ((StacksDraft.Perfect.FibreCycleLift.fibreComplex
      (algebraMap _ p.ResidueField) N).homology 0) = 1 := by
    have h := StacksDraft.Perfect.finrank_homology_fibreComplex_comp_ringEquiv
      (Space.representedAffineCommRingCatHom B integerBase hZ w).hom
      (Space.primeResidueRingEquiv B integerBase hZ (X.chartObject V) p) N 0
      ⟨(StacksDraft.Perfect.homologyTotalDerivedExtensionScalarsQIso _
        (Space.representedAffineDerivedExtension B integerBase hZ w) N bN 0).symm ≪≫ h0W⟩
    rwa [Space.primeResidueRingEquiv_comp] at h
  let A' : Γ(Space.chartScheme V, ⊤) → Type u := fun f =>
    Γ(Space.chartScheme (Space.openChart B integerBase hZ _ V ((Space.chartScheme V).basicOpen f)),
      ⊤)
  let ι := fun f : Γ(Space.chartScheme V, ⊤) =>
    (Space.SmallEtale.toOver B integerBase hZ (schemeSpace X.base).1).map
      (Space.openChartInclusion B integerBase hZ _ V ((Space.chartScheme V).basicOpen f))
  let ψ : ∀ f, Γ(Space.chartScheme V, ⊤) →+* A' f := fun f =>
    (Space.representedAffineCommRingCatHom B integerBase hZ (ι f)).hom
  have hψ : ∀ f, let := (ψ f).toAlgebra; IsLocalization.Away f (A' f) := fun f =>
    Space.isLocalization_away_representedAffineRingHom_openChartInclusion B integerBase hZ
      V f
  have hloc : ∀ f, Nonempty ((StacksDraft.Perfect.FibreCycleLift.fibreComplex (ψ f) N).homology 0
      ≃ₗ[A' f] A' f) := fun f => by
    have : IsAffine (Space.chartScheme (Space.openChart B integerBase hZ _ V
        ((Space.chartScheme V).basicOpen f))) :=
      Space.isAffine_chartScheme_openChart_basicOpen B integerBase hZ _ V inferInstance f
    let := HasDerivedCategory.standard (ModuleCat.{u} (A' f))
    have h0 := (homology_representedAffineDerivedExtension hX V (DerivedCategory.Q.obj N) eM
      (ι f)).2.some
    exact ⟨((StacksDraft.Perfect.homologyTotalDerivedExtensionScalarsQIso _
      (Space.representedAffineDerivedExtension B integerBase hZ (ι f)) N bN 0).symm ≪≫
        h0).toLinearEquiv⟩
  exact StacksDraft.Perfect.exists_notMem_iso_single_biprod_of_fibre p N n bN hfin hproj hneg
    hrank A' ψ hψ hloc

/-- **Carrying the splitting of `M ⊗_A Γ(D(f))` to the chart `D(f)`.** If `M^~ ≅ (Rf_*𝒪_X)|_V` and
`M ⊗_A Γ(D(f)) ≅ Γ(D(f))[0] ⊕ T` with `T` a bounded complex of finite projective modules in
degrees `≥ 1`, then `(Rf_*𝒪_X)|_{D(f)} ≅ 𝒪[0] ⊕ T^~` with `T^~` strictly perfect in degrees `≥ 1`:
restriction to `D(f)` is restriction to `V` followed by restriction along `D(f) ⟶ V`, which on
associated modules is derived extension of scalars (Stacks 08DW), computed termwise on `M`. -/
theorem exists_chartSplitting_of_model {X : CurveFamily B hZ}
    (V : Space.SmallEtale B integerBase hZ (schemeSpace X.base).1)
    [IsAffine (Space.chartScheme V)]
    (N : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B integerBase hZ).obj
        (X.chartObject V), ⊤)) ℤ) (bN : ℤ) [N.IsStrictlyLE bN]
    (hproj : ∀ j, Module.Projective Γ((BigFppfOver.toScheme B integerBase hZ).obj
        (X.chartObject V), ⊤) (N.X j))
    (eM :
      letI := HasDerivedCategory.standard
        (Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2)
      letI := HasDerivedCategory.standard
        (Space.Modules.{u, u} B integerBase hZ (schemeSpace X.base).1 (schemeSpace X.base).2)
      letI := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B integerBase
        hZ).obj (X.chartObject V), ⊤))
      letI := HasDerivedCategory.standard
        (Space.Modules.{u, u} B integerBase hZ
          (Space.chartSpace B integerBase hZ (schemeSpace X.base) V).1
          (Space.chartSpace B integerBase hZ (schemeSpace X.base) V).2)
      (Space.etaleModulePullback.{u, u} B integerBase hZ
          (Space.chartToSpace B integerBase hZ (schemeSpace X.base) V)
          (Space.isEtale_chartToSpace B integerBase hZ (schemeSpace X.base)
              V)).mapDerivedCategory.obj
          ((Space.smallEtaleDerivedModulePushforward B integerBase hZ X.toBase).obj
            ((DerivedCategory.singleFunctor
              (Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2) 0).obj
              (Space.structureSheafModule B integerBase hZ X.total))) ≅
        (Space.representedAffineDerivedAssociated B integerBase hZ (X.chartObject V)).obj
          (DerivedCategory.Q.obj N))
    (f : Γ(Space.chartScheme V, ⊤))
    (T : CochainComplex (ModuleCat.{u} Γ(Space.chartScheme (Space.openChart B integerBase hZ _ V
          ((Space.chartScheme V).basicOpen f)), ⊤)) ℤ) (bT : ℤ)
    (hT1 : T.IsStrictlyGE 1) (hTb : T.IsStrictlyLE bT)
    (hTfin : ∀ j, Module.Finite Γ(Space.chartScheme (Space.openChart B integerBase hZ _ V
          ((Space.chartScheme V).basicOpen f)), ⊤) (T.X j))
    (hTproj : ∀ j, Module.Projective Γ(Space.chartScheme (Space.openChart B integerBase hZ _ V
          ((Space.chartScheme V).basicOpen f)), ⊤) (T.X j))
    (eT :
        letI := HasDerivedCategory.standard (ModuleCat.{u} Γ(Space.chartScheme
          (Space.openChart B integerBase hZ _ V ((Space.chartScheme V).basicOpen f)), ⊤))
        DerivedCategory.Q.obj (StacksDraft.Perfect.FibreCycleLift.fibreComplex
            (Space.representedAffineCommRingCatHom B integerBase hZ
              ((Space.SmallEtale.toOver B integerBase hZ (schemeSpace X.base).1).map
                (Space.openChartInclusion B integerBase hZ _ V
                  ((Space.chartScheme V).basicOpen f)))).hom N) ≅
          (DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of _ Γ(Space.chartScheme
            (Space.openChart B integerBase hZ _ V ((Space.chartScheme V).basicOpen f)), ⊤)) ⊞
            DerivedCategory.Q.obj T) :
      ∃ P : CochainComplex (Space.Modules.{u, u} B integerBase hZ
        (Space.chartSpace B integerBase hZ (schemeSpace X.base)
          (Space.openChart B integerBase hZ _ V ((Space.chartScheme V).basicOpen f))).1
        (Space.chartSpace B integerBase hZ (schemeSpace X.base)
          (Space.openChart B integerBase hZ _ V ((Space.chartScheme V).basicOpen f))).2) ℤ,
      IsStrictlyPerfect.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B integerBase hZ
          (Space.chartSpace B integerBase hZ (schemeSpace X.base)
            (Space.openChart B integerBase hZ _ V ((Space.chartScheme V).basicOpen f))).1
          (Space.chartSpace B integerBase hZ (schemeSpace X.base)
            (Space.openChart B integerBase hZ _ V ((Space.chartScheme V).basicOpen f))).2).O)) P ∧
      P.IsStrictlyGE 1 ∧
      letI := HasDerivedCategory.standard
        (Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2)
      letI := HasDerivedCategory.standard
        (Space.Modules.{u, u} B integerBase hZ (schemeSpace X.base).1 (schemeSpace X.base).2)
      letI := HasDerivedCategory.standard
        (Space.Modules.{u, u} B integerBase hZ
          (Space.chartSpace B integerBase hZ (schemeSpace X.base)
            (Space.openChart B integerBase hZ _ V ((Space.chartScheme V).basicOpen f))).1
          (Space.chartSpace B integerBase hZ (schemeSpace X.base)
            (Space.openChart B integerBase hZ _ V ((Space.chartScheme V).basicOpen f))).2)
      Nonempty ((Space.etaleModulePullback.{u, u} B integerBase hZ
          (Space.chartToSpace B integerBase hZ (schemeSpace X.base)
            (Space.openChart B integerBase hZ _ V ((Space.chartScheme V).basicOpen f)))
          (Space.isEtale_chartToSpace B integerBase hZ (schemeSpace X.base)
            (Space.openChart B integerBase hZ _ V
              ((Space.chartScheme V).basicOpen f)))).mapDerivedCategory.obj
          ((Space.smallEtaleDerivedModulePushforward B integerBase hZ X.toBase).obj
            ((DerivedCategory.singleFunctor
              (Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2) 0).obj
              (Space.structureSheafModule B integerBase hZ X.total))) ≅
        (Space.etaleModulePullback.{u, u} B integerBase hZ
          (Space.chartToSpace B integerBase hZ (schemeSpace X.base)
            (Space.openChart B integerBase hZ _ V ((Space.chartScheme V).basicOpen f)))
          (Space.isEtale_chartToSpace B integerBase hZ (schemeSpace X.base)
            (Space.openChart B integerBase hZ _ V
              ((Space.chartScheme V).basicOpen f)))).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor
            (Space.Modules.{u, u} B integerBase hZ (schemeSpace X.base).1
              (schemeSpace X.base).2) 0).obj
            (Space.structureSheafModule B integerBase hZ (schemeSpace X.base))) ⊞
          DerivedCategory.Q.obj P) := by
  classical
  have : IsAffine (Space.chartScheme (Space.openChart B integerBase hZ _ V ((Space.chartScheme
      V).basicOpen f))) :=
    Space.isAffine_chartScheme_openChart_basicOpen B integerBase hZ _ V inferInstance f
  let U := (Space.SmallEtale.toOver B integerBase hZ (schemeSpace X.base).1).obj
    (Space.openChart B integerBase hZ _ V ((Space.chartScheme V).basicOpen f))
  let Φ₀ := Space.representedAffineAssociated B integerBase hZ U
  refine ⟨(Φ₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj T,
    Space.isStrictlyPerfect_representedAffineAssociated_mapHomologicalComplex B integerBase hZ U T
      1 bT hT1 hTb hTfin hTproj,
    (CochainComplex.isStrictlyGE_iff _ 1).2 fun i hi =>
      Φ₀.map_isZero (T.isZero_of_isStrictlyGE 1 i hi), ?_⟩
  let := HasDerivedCategory.standard
    (Space.Modules.{u, u} B integerBase hZ (Space.chartSpace B integerBase hZ (schemeSpace X.base)
        (Space.openChart B integerBase hZ _ V ((Space.chartScheme V).basicOpen f))).1
            (Space.chartSpace B integerBase hZ (schemeSpace X.base) (Space.openChart B integerBase
                hZ _ V ((Space.chartScheme V).basicOpen f))).2)
  have : ∀ j, Projective (N.X j) := fun j => (IsProjective.iff_projective (N.X j)).mp (hproj j)
  let ι := Space.openChartInclusion B integerBase hZ _ V ((Space.chartScheme V).basicOpen f)
  let g := (Space.SmallEtale.toOver B integerBase hZ (schemeSpace X.base).1).map ι
  let Φ := Space.representedAffineDerivedAssociated B integerBase hZ U
  let Φ₀W : ModuleCat.{u} Γ((BigFppfOver.toScheme B integerBase hZ).obj U, ⊤) ⥤
      Space.Modules.{u, u} B integerBase hZ
        (Space.chartSpace B integerBase hZ (schemeSpace X.base) (Space.openChart B integerBase hZ _
          V ((Space.chartScheme V).basicOpen f))).1
        (Space.chartSpace B integerBase hZ (schemeSpace X.base) (Space.openChart B integerBase hZ _
          V ((Space.chartScheme V).basicOpen f))).2 := Φ₀
  have : Φ₀W.Additive := inferInstanceAs Φ₀.Additive
  have : PreservesFiniteLimits Φ₀W := inferInstanceAs (PreservesFiniteLimits Φ₀)
  have : PreservesFiniteColimits Φ₀W := inferInstanceAs (PreservesFiniteColimits Φ₀)
  let Φ' := Φ₀W.mapDerivedCategory
  have := preservesBinaryBiproducts_of_preservesBiproducts Φ'
  let eB := Φ'.mapBiprod ((DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of _
      Γ(Space.chartScheme (Space.openChart B integerBase hZ _ V
        ((Space.chartScheme V).basicOpen f)),
        ⊤))) (DerivedCategory.Q.obj T)
  have hc :=
    (Space.representedAffineDerivedExtension B integerBase hZ g).comparison_isIso_of_projective
      N bN
  let Lι := Space.smallEtaleDerivedModulePullback B integerBase hZ
    (Space.chartMap B integerBase hZ (schemeSpace X.base) ι)
  let cres := fun E => ((Space.smallEtaleDerivedModulePullbackIsoEtale B integerBase hZ
      (Space.chartToSpace B integerBase hZ (schemeSpace X.base) (Space.openChart B integerBase hZ
          _ V ((Space.chartScheme V).basicOpen f)))
      (Space.isEtale_chartToSpace B integerBase hZ (schemeSpace X.base) (Space.openChart B
          integerBase hZ _ V ((Space.chartScheme V).basicOpen f)))).app E).symm ≪≫
    (Space.smallEtaleDerivedModulePullbackCongr B integerBase hZ
      (Space.chartMap_comp_chartToSpace B integerBase hZ (schemeSpace X.base) ι).symm).app E ≪≫
    ((Space.smallEtaleDerivedModulePullbackCompIso B integerBase hZ
      (Space.chartMap B integerBase hZ (schemeSpace X.base) ι) (Space.chartToSpace B integerBase
          hZ (schemeSpace X.base) V)).app E).symm ≪≫
    Lι.mapIso ((Space.smallEtaleDerivedModulePullbackIsoEtale B integerBase hZ
      (Space.chartToSpace B integerBase hZ (schemeSpace X.base) V)
      (Space.isEtale_chartToSpace B integerBase hZ (schemeSpace X.base) V)).app E)
  let firstW := ((Space.smallEtaleDerivedModulePullbackIsoEtale B integerBase hZ
      (Space.chartToSpace B integerBase hZ (schemeSpace X.base) (Space.openChart B integerBase hZ
          _ V ((Space.chartScheme V).basicOpen f)))
      (Space.isEtale_chartToSpace B integerBase hZ (schemeSpace X.base) (Space.openChart B
          integerBase hZ _ V ((Space.chartScheme V).basicOpen f)))).app _).symm ≪≫
    Space.smallEtaleDerivedModulePullbackUnitIso (B := B) (S := integerBase) (hS := hZ)
      (Space.chartToSpace B integerBase hZ (schemeSpace X.base) (Space.openChart B integerBase hZ
          _ V ((Space.chartScheme V).basicOpen f)))
  exact ⟨cres _ ≪≫ Lι.mapIso eM ≪≫
    (Space.representedAffineDerivedBaseChangeIso B integerBase hZ g).app _ ≪≫
    Φ.mapIso (@asIso _ _ _ _
      ((Space.representedAffineDerivedExtension B integerBase hZ g).comparison.app N) hc) ≪≫
    Φ'.mapIso eT ≪≫ eB ≪≫
    biprod.mapIso (W := Φ'.obj ((DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of _
      Γ(Space.chartScheme (Space.openChart B integerBase hZ _ V
        ((Space.chartScheme V).basicOpen f)),
        ⊤)))) (X := Φ'.obj (DerivedCategory.Q.obj T))
      (Space.representedAffineDerivedAssociatedSingleUnitIso B integerBase hZ U 0 ≪≫ firstW.symm)
      ((Φ₀W.mapDerivedCategoryFactors).app T)⟩

/-- **The splitting of Stacks 0E6B (b) on an étale chart `W` of the base**: `(Rf_*𝒪_X)|_W ≅ 𝒪 ⊕ P`
with `P` a strictly perfect complex in degrees `≥ 1`; the per-chart clause of
`AlgebraicGeometry.CurveFamily.HasAffineStrictlyPerfectLocalSplitting`. -/
def HasStrictlyPerfectChartSplitting (X : CurveFamily B hZ)
    (W : Space.SmallEtale B integerBase hZ (schemeSpace X.base).1) : Prop :=
      ∃ P : CochainComplex (Space.Modules.{u, u} B integerBase hZ
        (Space.chartSpace B integerBase hZ (schemeSpace X.base) W).1
        (Space.chartSpace B integerBase hZ (schemeSpace X.base) W).2) ℤ,
      IsStrictlyPerfect.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B integerBase hZ
          (Space.chartSpace B integerBase hZ (schemeSpace X.base) W).1
          (Space.chartSpace B integerBase hZ (schemeSpace X.base) W).2).O)) P ∧
      P.IsStrictlyGE 1 ∧
      letI := HasDerivedCategory.standard
        (Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2)
      letI := HasDerivedCategory.standard
        (Space.Modules.{u, u} B integerBase hZ (schemeSpace X.base).1 (schemeSpace X.base).2)
      letI := HasDerivedCategory.standard
        (Space.Modules.{u, u} B integerBase hZ
          (Space.chartSpace B integerBase hZ (schemeSpace X.base) W).1
          (Space.chartSpace B integerBase hZ (schemeSpace X.base) W).2)
      Nonempty ((Space.etaleModulePullback.{u, u} B integerBase hZ
          (Space.chartToSpace B integerBase hZ (schemeSpace X.base) W)
          (Space.isEtale_chartToSpace B integerBase hZ
            (schemeSpace X.base) W)).mapDerivedCategory.obj
          ((Space.smallEtaleDerivedModulePushforward B integerBase hZ X.toBase).obj
            ((DerivedCategory.singleFunctor
              (Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2) 0).obj
              (Space.structureSheafModule B integerBase hZ X.total))) ≅
        (Space.etaleModulePullback.{u, u} B integerBase hZ
          (Space.chartToSpace B integerBase hZ (schemeSpace X.base) W)
          (Space.isEtale_chartToSpace B integerBase hZ
            (schemeSpace X.base) W)).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor
            (Space.Modules.{u, u} B integerBase hZ (schemeSpace X.base).1
              (schemeSpace X.base).2) 0).obj
            (Space.structureSheafModule B integerBase hZ (schemeSpace X.base))) ⊞
          DerivedCategory.Q.obj P)

/-- **Stacks 0E6B (b) near a point of an affine chart: `Rf_*𝒪_X ≅ 𝒪 ⊕ P` with `P` strictly
perfect in degrees `≥ 1`.** Let `X` be a family of curves with `k = H⁰(X_k, 𝒪)` on every fibre over
a field and `V = Spec A` an affine étale chart of the base. Every prime `𝔭` of `A` lies in a basic
open `D(a)` on whose chart `(Rf_*𝒪_X)|_{D(a)} ≅ 𝒪 ⊕ P` with `P` strictly perfect in degrees
`≥ 1`. -/
theorem exists_notMem_strictlyPerfect_splitting_basicOpen {X : CurveFamily B hZ}
    (hX : HasBijectiveGlobalFunctionsOnFieldFibres B hZ X)
    (V : Space.SmallEtale B integerBase hZ (schemeSpace X.base).1)
    [IsAffine (Space.chartScheme V)]
    (p : Ideal Γ(Space.chartScheme V, ⊤)) [p.IsPrime] :
    ∃ a : Γ(Space.chartScheme V, ⊤), a ∉ p ∧
      X.HasStrictlyPerfectChartSplitting (Space.openChart B integerBase hZ _ V
        ((Space.chartScheme V).basicOpen a)) := by
  obtain ⟨N, n, bN, hNn, hNb, hfin, hproj, hM⟩ := exists_chartModel X V
  have := hNn
  have := hNb
  obtain ⟨f, hf, T, bT, hT1, hTb, hTfin, hTproj, hT⟩ :=
    exists_notMem_iso_single_biprod_chart hX V N n bN hfin hproj hM.some p
  exact ⟨f, hf, exists_chartSplitting_of_model V N bN hproj hM.some f T bT hT1 hTb hTfin hTproj
    hT.some⟩

/-- **Stacks 0E6B (b) for a family of curves: an affine strictly perfect splitting
`Rf_*𝒪_X ≅ 𝒪 ⊕ P`**, for a family with `k = H⁰(X_k, 𝒪)` on every fibre over a field: the basic
opens of the affine étale charts of the base given by
`exists_notMem_strictlyPerfect_splitting_basicOpen` at the points of the charts cover the base. -/
theorem hasAffineStrictlyPerfectLocalSplitting_of_fieldFibres {X : CurveFamily B hZ}
    (hX : HasBijectiveGlobalFunctionsOnFieldFibres B hZ X) :
    X.HasAffineStrictlyPerfectLocalSplitting := by
  let κ₀ := {V : Space.SmallEtale B integerBase hZ (schemeSpace X.base).1 //
    IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj
      ((Space.SmallEtale.toOver B integerBase hZ (schemeSpace X.base).1).obj V))}
  have hloc : ∀ (k : κ₀) (x : Space.chartScheme k.1), ∃ a : Γ(Space.chartScheme k.1, ⊤),
      have : IsAffine (Space.chartScheme k.1) := k.2
      x ∈ (Space.chartScheme k.1).basicOpen a ∧ (IsAffine (Space.chartScheme
        (Space.openChart B integerBase hZ _ k.1 ((Space.chartScheme k.1).basicOpen a))) ∧
      X.HasStrictlyPerfectChartSplitting
        (Space.openChart B integerBase hZ _ k.1 ((Space.chartScheme k.1).basicOpen a))) := by
    intro k x
    have : IsAffine (Space.chartScheme k.1) := k.2
    obtain ⟨a, ha, h⟩ := exists_notMem_strictlyPerfect_splitting_basicOpen hX k.1
      ((Space.chartScheme k.1).toSpecΓ x).asIdeal
    refine ⟨a, ?_, Space.isAffine_chartScheme_openChart_basicOpen B integerBase hZ _ k.1
      inferInstance a, h⟩
    rw [← Scheme.toSpecΓ_preimage_basicOpen]
    exact ha
  choose a hxa hiso using hloc
  let W : (Σ k : κ₀, Space.chartScheme k.1) →
      Space.SmallEtale B integerBase hZ (schemeSpace X.base).1 :=
    fun kx => Space.openChart B integerBase hZ _ kx.1.1
      ((Space.chartScheme kx.1.1).basicOpen (a kx.1 kx.2))
  refine ⟨Σ k : κ₀, Space.chartScheme k.1, W, ?_, fun kx => hiso kx.1 kx.2⟩
  intro T
  refine (Space.SmallEtale.topology B integerBase hZ (schemeSpace X.base).1).transitive
    (Space.SmallEtale.coversTop_affineCharts B integerBase hZ _ T) _ ?_
  intro T' f hf
  obtain ⟨k, ⟨g⟩⟩ := hf
  have hcov : Sieve.ofArrows (fun x : Space.chartScheme k.1 => W ⟨k, x⟩)
      (fun x => Space.openChartInclusion B integerBase hZ _ k.1
        ((Space.chartScheme k.1).basicOpen (a k x))) ∈
      Space.SmallEtale.topology B integerBase hZ (schemeSpace X.base).1 k.1 := by
    refine Space.SmallEtale.ofArrows_mem_topology B integerBase hZ _ _ _ ?_
    rw [ofArrows_mem_etalePrecoverage_iff]
    refine ⟨fun x => ⟨x, ?_⟩, fun x => ?_⟩
    · rw [Space.toScheme_map_toOver_map_openChartInclusion]
      exact ⟨⟨x, hxa k x⟩, rfl⟩
    · rw [Space.toScheme_map_toOver_map_openChartInclusion]
      exact (inferInstance : Etale ((Space.chartScheme k.1).basicOpen (a k x)).ι)
  refine (Space.SmallEtale.topology B integerBase hZ (schemeSpace X.base).1).superset_covering ?_
    ((Space.SmallEtale.topology B integerBase hZ (schemeSpace X.base).1).pullback_stable g hcov)
  intro T'' h hh
  obtain ⟨_, h', _, ⟨x⟩, -⟩ := hh
  exact ⟨⟨k, x⟩, ⟨h'⟩⟩

/-! ### Parts (2) and (3) of Stacks 0E1J -/

/-- **Parts (2) and (3) of Stacks 0E1J, unconditionally**: for every family of curves with
`κ(s) = H⁰(X_s, 𝒪)` at every point of the base, `R¹f_*𝒪_X` is finite locally free and its formation
commutes with arbitrary base change. The two inputs of
`firstHigherDirectImage_of_baseChange_of_affineSplitting` are proved: the base change clause of
Stacks 0CTM (1) at `𝒪_X` (`hasDerivedStructureSheafBaseChange`), and the affine strictly perfect
splitting of Stacks 0E6B (b) (`hasAffineStrictlyPerfectLocalSplitting_of_fieldFibres`), the
hypothesis on residue fields giving `k = H⁰` on all field fibres
(`hasBijectiveGlobalFunctionsOnFieldFibres_of_hasResidueFieldGlobalFunctions`). -/
theorem firstHigherDirectImage_of_hasResidueFieldGlobalFunctions :
    (∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.HasFiniteLocallyFreeFirstHigherDirectImage) ∧
    (∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.FirstHigherDirectImageCommutesWithBaseChange) :=
  firstHigherDirectImage_of_baseChange_of_affineSplitting
    (fun X _ => X.hasDerivedStructureSheafBaseChange)
    (fun _ hX => hasAffineStrictlyPerfectLocalSplitting_of_fieldFibres
      (hasBijectiveGlobalFunctionsOnFieldFibres_of_hasResidueFieldGlobalFunctions hX))

end CurveFamily

end AlgebraicGeometry

end
