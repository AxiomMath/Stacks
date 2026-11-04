module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedCoherator
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianCoherator.DerivedPushforwardBound
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedFunctorAmplitude
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedFunctorAmplitudeUnbounded
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartModuleCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsTerminalChart
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.SingleObject
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.GlobalCohomologyOnALargeSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsTerminalObject
public import StacksFrontier.Homology.Ext.DerivedCoyoneda
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The coherator of a quasi-compact quasi-separated algebraic space is bounded

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S` and let `DQ_X` be
the right adjoint of the inclusion `D_QCoh(𝒪_X) ⥤ D(𝒪_X)` (Stacks 0CR4).  Stacks 0CSS asserts
that there is an integer `N = N(X)` such that, whenever `H^i(U, K) = 0` for every affine `U` étale
over `X` and every `i ∉ [a, b]`, the cohomology sheaves of `DQ_X(K)` vanish outside
`[a, b + N]`.

## Main results

* `AlgebraicGeometry.Space.exists_isZero_homology_coherator_obj`: Stacks 0CSS.
* `AlgebraicGeometry.Space.coheratorDerivedPushforwardIsoOfIsEtale`: Stacks 0CR5 for an étale
  quasi-compact quasi-separated morphism, `Rj_* ∘ DQ_V ≅ DQ_X ∘ Rj_*`.

## References

* [Stacks Project, Tag 0CSS](https://stacks.math.columbia.edu/tag/0CSS)
* [Stacks Project, Tag 0CR4](https://stacks.math.columbia.edu/tag/0CR4)
* [Stacks Project, Tag 0CR5](https://stacks.math.columbia.edu/tag/0CR5)
* [Stacks Project, Tag 0CR6](https://stacks.math.columbia.edu/tag/0CR6)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Tag 08H0](https://stacks.math.columbia.edu/tag/08H0)
* [Stacks Project, Tag 08FA](https://stacks.math.columbia.edu/tag/08FA)
* [Stacks Project, Tag 08GW](https://stacks.math.columbia.edu/tag/08GW)
* [Stacks Project, Tag 0CSA](https://stacks.math.columbia.edu/tag/0CSA)
* [Stacks Project, Tag 08F7](https://stacks.math.columbia.edu/tag/08F7)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 08F4](https://stacks.math.columbia.edu/tag/08F4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] HasDerivedCategory.standard isGrothendieckAbelian_modules
  enoughInjectives_modules

/-! ### Sections over an affine chart of a complex with quasi-coherent cohomology -/

section ChartSections

variable (Y : AlgebraicSpaces B S hS) (V : SmallEtale B S hS Y.1)

/-- The higher derived functors of the sections over an affine chart vanish on quasi-coherent
modules. -/
theorem isZero_rightDerivedPlus_chartSectionsAb_of_isAffineChart
    (hV : IsAffineChart B S hS Y.1 V) (M : Modules.{u, u} B S hS Y.1 Y.2)
    (hM : M.IsQuasicoherentOnSite) (p : ℤ) (hp : (1 : ℕ) ≤ p) :
    IsZero (((chartSectionsAb B S hS Y V).rightDerivedPlus p).obj M) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = k := ⟨p.toNat, by omega⟩
  refine (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff _ rfl M).2 ?_
  refine IsZero.of_iso ?_ ((Stacks.Cohomology.ColimitsOfCohomology.rightDerivedCompExactIso
    (SheafOfModules.evaluation (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O) (op V))
    (forget₂ (ModuleCat.{u} _) AddCommGrpCat.{u}) k).app M)
  exact (forget₂ (ModuleCat.{u} _) AddCommGrpCat.{u}).map_isZero
    (isZero_rightDerived_evaluation_of_isQuasicoherentOnSite B S hS Y.1 Y.2 V hV M hM k
      (by omega))

variable (RF : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤ DerivedCategory AddCommGrpCat.{u})
  (α : (chartSectionsAb B S hS Y V).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor α
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ))]

/-- **The derived sections over an affine chart commute with cohomology on `D_QCoh`**:
`H^i(RΓ(V, E)) ≅ Γ(V, H^i(E))` for every `E` with quasi-coherent cohomology sheaves and every
`i`. -/
def homologyRightDerivedChartSectionsIso (hV : IsAffineChart B S hS Y.1 V)
    (E : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS Y.1 Y.2) i).obj E).IsQuasicoherentOnSite) (i : ℤ) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj (RF.obj E) ≅
      (chartSectionsAb B S hS Y V).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).obj E) := by
  let F := chartSectionsAb B S hS Y V
  let PA := SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)
  let HA := DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i
  let HB := DerivedCategory.homologyFunctor AddCommGrpCat.{u} i
  let E₁ := (DerivedCategory.TStructure.t.truncGE i).obj E
  have hcoh₁ : ∀ j : ℤ, PA ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS Y.1 Y.2) j).obj E₁) := fun j =>
    Stacks.SmallDerivedCategory.prop_homologyFunctor_truncGE_obj PA E hcoh i j
  let E₂ := (DerivedCategory.TStructure.t.truncLE i).obj E₁
  have _ : E₂.IsGE i := inferInstanceAs
    (((DerivedCategory.TStructure.t.truncLE i).obj E₁).IsGE i)
  have _ : E₂.IsLE i := inferInstanceAs
    (((DerivedCategory.TStructure.t.truncLE i).obj E₁).IsLE i)
  let M := (E₂.exists_iso_singleFunctor_obj_of_isGE_of_isLE i).choose
  let e : E₂ ≅ (DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).obj M :=
    (E₂.exists_iso_singleFunctor_obj_of_isGE_of_isLE i).choose_spec.some
  let eM : HA.obj E₂ ≅ M := HA.mapIso e ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (Modules.{u, u} B S hS Y.1 Y.2) i).app M
  have hπ₀ := isIso_homologyFunctor_map_rightDerived_truncGE_unbounded B S hS Y.1 Y.2 F RF α 1
    (isZero_rightDerivedPlus_chartSectionsAb_of_isAffineChart B S hS Y V hV) E hcoh i i le_rfl
  have hii : i - ((1 : ℕ) : ℤ) + 1 = i := by omega
  rw [hii] at hπ₀
  have hι := isIso_homologyFunctor_map_rightDerived_truncLE B S hS Y.1 Y.2 F RF α E₁ hcoh₁ i i
    le_rfl
  have hgπ := DerivedCategory.isIso_homologyFunctor_map_truncGEπ i i le_rfl E
  have hgι := Stacks.SmallDerivedCategory.isIso_homologyFunctor_map_truncLEι E₁ i i le_rfl
  let eE : HA.obj E ≅ M :=
    asIso (HA.map ((DerivedCategory.TStructure.t.truncGEπ i).app E)) ≪≫
      (asIso (HA.map ((DerivedCategory.TStructure.t.truncLEι i).app E₁))).symm ≪≫ eM
  exact asIso (HB.map (RF.map ((DerivedCategory.TStructure.t.truncGEπ i).app E))) ≪≫
      (asIso (HB.map (RF.map ((DerivedCategory.TStructure.t.truncLEι i).app E₁)))).symm ≪≫
      HB.mapIso (RF.mapIso e) ≪≫
      Stacks.DerivedFunctor.homologyTotalRightDerivedSingleSelfIso F RF α
        (exists_quasiIso_isKInjective_modules B S hS Y.1 Y.2) M i ≪≫
      F.mapIso eE.symm

/-- The total right derived functor of the sections over a chart exists. -/
theorem hasRightDerivedFunctor_chartSectionsAb :
    ((chartSectionsAb B S hS Y V).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ)) :=
  have := (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
    ((chartSectionsAb B S hS Y V).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (exists_quasiIso_isKInjective_modules B S hS Y.1 Y.2)).1
  Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _

/-- **Sections over an affine chart of a K-injective complex with quasi-coherent cohomology**:
`H^i(Γ(V, J^•)) ≅ Γ(V, H^i(J))`. -/
def homologyChartSectionsIsoOfIsKInjective (hV : IsAffineChart B S hS Y.1 V)
    (J : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ) (hJ : J.IsKInjective)
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS Y.1 Y.2) i).obj (DerivedCategory.Q.obj J)).IsQuasicoherentOnSite)
    (i : ℤ) :
    ((((chartSectionsAb B S hS Y V).mapHomologicalComplex (ComplexShape.up ℤ)).obj J).homology
        i) ≅
      (chartSectionsAb B S hS Y V).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).obj
          (DerivedCategory.Q.obj J)) :=
  haveI := hasRightDerivedFunctor_chartSectionsAb B S hS Y V
  ((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} i).app _).symm ≪≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).mapIso
      (CategoryTheory.PushforwardMayerVietoris.rightDerivedObjIsoOfKInjective
        (exists_quasiIso_isKInjective_modules B S hS Y.1 Y.2) (chartSectionsAb B S hS Y V)
        inferInstance
        (((chartSectionsAb B S hS Y V).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
            (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ)))
        (((chartSectionsAb B S hS Y V).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
            (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ)))
        inferInstance J hJ) ≪≫
    homologyRightDerivedChartSectionsIso B S hS Y V _
      (((chartSectionsAb B S hS Y V).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
            (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ)))
      hV _ hcoh i

end ChartSections

/-! ### Quasi-coherent modules on an affine algebraic space -/

/-- **A quasi-coherent module with no sections over an affine terminal chart is zero.** -/
theorem isZero_of_isZero_chartSectionsAb_of_isTerminal (Y : AlgebraicSpaces B S hS)
    {T : SmallEtale B S hS Y.1} (hT : IsTerminal T) (hTa : IsAffineChart B S hS Y.1 T)
    (M : Modules.{u, u} B S hS Y.1 Y.2) (hM : M.IsQuasicoherentOnSite)
    (h : IsZero ((chartSectionsAb B S hS Y T).obj M)) : IsZero M := by
  have hT0 : Subsingleton (M.val.obj (op T)) := AddCommGrpCat.subsingleton_of_isZero h
  have hcart := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS Y.1 Y.2 M hM
  have hW : ∀ W : SmallEtale B S hS Y.1, IsAffineChart B S hS Y.1 W →
      Subsingleton (M.val.obj (op W)) := by
    intro W hWa
    refine ⟨fun x y => ?_⟩
    obtain ⟨tx, rfl⟩ := (hcart T W hTa hWa (hT.from W)).2 x
    obtain ⟨ty, rfl⟩ := (hcart T W hTa hWa (hT.from W)).2 y
    have h0 : ∀ t, sectionsBaseChange M (hT.from W) t = 0 := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => exact map_zero _
      | tmul b m => rw [Subsingleton.elim m 0, TensorProduct.tmul_zero, map_zero]
      | add t₁ t₂ h₁ h₂ => rw [map_add, h₁, h₂, add_zero]
    rw [h0, h0]
  rw [IsZero.iff_id_eq_zero]
  refine (SheafOfModules.toSheaf (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).map_injective
    ?_
  rw [Functor.map_zero]
  refine Sheaf.hom_eq_zero_of_isCoveringFamily _ (isCoveringFamily_isAffineChart B S hS Y)
    fun W hWa => ?_
  ext x
  exact (hW W hWa).elim _ _

/-! ### Cohomology over a terminal chart as morphisms out of the structure sheaf -/

section Terminal

variable (Y : AlgebraicSpaces B S hS) {T : SmallEtale B S hS Y.1} (hT : IsTerminal T)

include hT

/-- **Morphisms out of the structure sheaf are the sections over a terminal chart.** -/
def unitHomAddEquivChartSections (N : Modules.{u, u} B S hS Y.1 Y.2) :
    (SheafOfModules.unit (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O) ⟶ N) ≃+
      (chartSectionsAb B S hS Y T).obj N where
  toEquiv := (SheafOfModules.unitHomEquiv N).trans ((Equiv.ofBijective _
      (Stacks.Cohomology.SiteModules.bijective_globalSectionsEval _ hT N)).trans Equiv.ulift)
  map_add' _ _ := rfl

/-- `unitHomAddEquivChartSections` carries the composite `φ ≫ d` to the image of the section of `φ`
under the map induced by `d`. -/
theorem unitHomAddEquivChartSections_comp {N N' : Modules.{u, u} B S hS Y.1 Y.2}
    (φ : SheafOfModules.unit (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O) ⟶ N)
    (d : N ⟶ N') :
    unitHomAddEquivChartSections B S hS Y hT N' (φ ≫ d) =
      ((chartSectionsAb B S hS Y T).map d).hom (unitHomAddEquivChartSections B S hS Y hT N φ) :=
  rfl

/-- **The cohomology of the sections over a terminal chart of a K-injective complex** is the
group of morphisms `𝒪[0] ⟶ I⟦n⟧` of the derived category. -/
def homologyChartSectionsAddEquiv (I : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ)
    [I.IsKInjective] (n : ℤ) :
    ((((chartSectionsAb B S hS Y T).mapHomologicalComplex (ComplexShape.up ℤ)).obj I).homology
        n) ≃+
      ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) 0).obj
          (SheafOfModules.unit (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)) ⟶
        (DerivedCategory.Q.obj I)⟦n⟧) := by
  let O := SheafOfModules.unit (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)
  let F := DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) 0
  let K := ((chartSectionsAb B S hS Y T).mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  let L := ((StacksDraft.DerivedCoyoneda.smallCoyoneda O).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj I
  let e (i : ℤ) : K.X i ≃+ L.X i :=
    (unitHomAddEquivChartSections B S hS Y hT (I.X i)).symm.trans
      (AddEquiv.ofBijective F.mapAddHom ⟨F.map_injective, F.map_surjective⟩)
  have he (i j : ℤ) (x : K.X i) : e j ((K.d i j).hom x) = (L.d i j).hom (e i x) := by
    change F.map ((unitHomAddEquivChartSections B S hS Y hT (I.X j)).symm
        (((chartSectionsAb B S hS Y T).map (I.d i j)).hom x)) =
      F.map ((unitHomAddEquivChartSections B S hS Y hT (I.X i)).symm x) ≫ F.map (I.d i j)
    rw [← F.map_comp]
    congr 1
    apply (unitHomAddEquivChartSections B S hS Y hT (I.X j)).injective
    rw [unitHomAddEquivChartSections_comp, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply]
  exact (StacksDraft.DerivedCoyoneda.homologyAddEquivOfComponents K L e he n).trans
    (StacksDraft.DerivedCoyoneda.homologySmallCoyonedaAddEquiv O I n)

/-- **Cohomology over a terminal chart vanishes exactly when `𝒪[-n]` maps trivially**: for a
K-injective complex `I`, `H^n(Γ(T, I^•)) = 0` if and only if every morphism `𝒪[-n] ⟶ I` of the
derived category is zero. -/
theorem isZero_homology_chartSections_iff (I : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ)
    (hI : I.IsKInjective) (n : ℤ) :
    IsZero ((((chartSectionsAb B S hS Y T).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        I).homology n) ↔
      Subsingleton ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) n).obj
          (SheafOfModules.unit (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)) ⟶
        DerivedCategory.Q.obj I) := by
  have := hI
  let O := SheafOfModules.unit (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)
  let e₁ := (homologyChartSectionsAddEquiv B S hS Y hT I n).toEquiv
  let e₂ : ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) 0).obj O ⟶
      (DerivedCategory.Q.obj I)⟦n⟧) ≃
      ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) n).obj O ⟶
        DerivedCategory.Q.obj I) :=
    ((shiftEquiv (DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) n).symm.toAdjunction.homEquiv
        _ _).symm.trans
      (Iso.homCongr (((DerivedCategory.singleFunctors (Modules.{u, u} B S hS Y.1 Y.2)).shiftIso
        (-n) n 0 (by omega)).app O) (Iso.refl _))
  rw [AddCommGrpCat.isZero_iff_subsingleton, e₁.subsingleton_congr, e₂.subsingleton_congr]

end Terminal

/-! ### The affine case -/

/-- `D_QCoh(𝒪_Y)`, the complexes of `𝒪_Y`-modules with quasi-coherent cohomology sheaves. -/
abbrev qcohDerivedCategoryB (Y : AlgebraicSpaces B S hS) :
    ObjectProperty (DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) :=
  DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))

/-- **The affine case of Stacks 0CSS, degree by degree.**  Let `Y` be an algebraic space with an
affine terminal chart `T` (an affine algebraic space), let `DQ_Y` be a right adjoint of the
inclusion `D_QCoh(𝒪_Y) ⥤ D(𝒪_Y)` and let `L` be an object of `D(𝒪_Y)` represented by the
K-injective complex `I`.  If `H^n(Y, L) = H^n(Γ(T, I^•))` vanishes, so does the cohomology sheaf
`H^n(DQ_Y(L))`. -/
theorem isZero_homology_coherator_obj_of_isTerminal (Y : AlgebraicSpaces B S hS)
    {T : SmallEtale B S hS Y.1} (hT : IsTerminal T) (hTa : IsAffineChart B S hS Y.1 T)
    (DQ : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
      (qcohDerivedCategoryB B S hS Y).FullSubcategory)
    (adj : (qcohDerivedCategoryB B S hS Y).ι ⊣ DQ)
    (L : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (I : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ) (hI : I.IsKInjective)
    (eI : Nonempty (DerivedCategory.Q.obj I ≅ L)) (n : ℤ)
    (h : IsZero ((((chartSectionsAb B S hS Y T).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      I).homology n)) :
    IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) n).obj
      ((qcohDerivedCategoryB B S hS Y).ι.obj (DQ.obj L))) := by
  let PA := SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)
  let O := SheafOfModules.unit (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)
  obtain ⟨eI⟩ := eI
  obtain ⟨J, hJ, ⟨eJ⟩⟩ :=
    CategoryTheory.PushforwardMayerVietoris.exists_isKInjective_representative_of_universe
    (exists_quasiIso_isKInjective_modules B S hS Y.1 Y.2)
    ((qcohDerivedCategoryB B S hS Y).ι.obj (DQ.obj L))
  have hcohJ : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS Y.1 Y.2) i).obj (DerivedCategory.Q.obj J)).IsQuasicoherentOnSite :=
    fun i => PA.prop_of_iso ((DerivedCategory.homologyFunctor _ i).mapIso eJ.symm)
      ((DQ.obj L).property i)
  have hO : qcohDerivedCategoryB B S hS Y
      ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) n).obj O) := by
    intro k
    by_cases hk : k = n
    · subst hk
      exact PA.prop_of_iso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ k).app O).symm
        (SheafOfModules.isQuasicoherentOnSite_unit _)
    · rcases lt_or_gt_of_ne hk with hk | hk
      · exact PA.prop_of_isZero
          (((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) n).obj O).isZero_of_isGE
            n k hk)
      · exact PA.prop_of_isZero
          (((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) n).obj O).isZero_of_isLE
            n k hk)
  let A : (qcohDerivedCategoryB B S hS Y).FullSubcategory := ⟨_, hO⟩
  have h₁ := (isZero_homology_chartSections_iff B S hS Y hT I hI n).1 h
  have h₂ : Subsingleton ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) n).obj O ⟶
      L) := (Iso.homCongr (Iso.refl _) eI).subsingleton_congr.1 h₁
  have h₃ : Subsingleton ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) n).obj O ⟶
      (qcohDerivedCategoryB B S hS Y).ι.obj (DQ.obj L)) :=
    (((qcohDerivedCategoryB B S hS Y).fullyFaithfulι.homEquiv (X := A) (Y := DQ.obj L)).symm.trans
      (adj.homEquiv A L).symm).subsingleton_congr.2 h₂
  have h₄ : Subsingleton ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) n).obj O ⟶
      DerivedCategory.Q.obj J) := (Iso.homCongr (Iso.refl _) eJ).subsingleton_congr.2 h₃
  have h₅ := (isZero_homology_chartSections_iff B S hS Y hT J hJ n).2 h₄
  have h₆ := h₅.of_iso (homologyChartSectionsIsoOfIsKInjective B S hS Y T hTa J hJ hcohJ n).symm
  exact (isZero_of_isZero_chartSectionsAb_of_isTerminal B S hS Y hT hTa _ (hcohJ n) h₆).of_iso
    ((DerivedCategory.homologyFunctor _ n).mapIso eJ.symm)

/-! ### The hypothesis of Stacks 0CSS -/

/-- **The hypothesis of Stacks 0CSS**: `H^i(U, K) = 0` for every affine `U` étale over `X` and
every `i ∉ [a, b]`.  The cohomology `H^i(U, K)` is the cohomology of the complex of sections over
the chart `U` of a K-injective complex `I` representing `K`, which computes the unbounded derived
sections `RΓ(U, K)`; it is asked of every such representative. -/
def AffineChartAmplitudeIn (X : AlgebraicSpaces B S hS) (a b : ℤ)
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) : Prop :=
  ∀ U : SmallEtale B S hS X.1, IsAffineChart B S hS X.1 U →
    ∀ I : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ, I.IsKInjective →
      Nonempty (DerivedCategory.Q.obj I ≅ K) → ∀ i : ℤ, i < a ∨ b < i →
        IsZero ((((chartSectionsAb B S hS X U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          I).homology i)

/-! ### The coherator commutes with the derived direct image along an étale morphism -/

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

/-- **Stacks 0CR5 for an étale quasi-compact quasi-separated morphism.**  If `j : V ⟶ X` is
étale, quasi-compact and quasi-separated and `DQ_X`, `DQ_V` are right adjoints of the two
inclusions of `D_QCoh`, then `Rj_* ∘ DQ_V ≅ DQ_X ∘ Rj_*` as functors `D(𝒪_V) ⥤ D_QCoh(𝒪_X)`, the
left-hand `Rj_*` being the restriction `D_QCoh(𝒪_V) ⥤ D_QCoh(𝒪_X)` (Stacks 08FA (1)). -/
def coheratorDerivedPushforwardIsoOfIsEtale {V X : AlgebraicSpaces B S hS}
    (j : V ⟶ X) (hj : IsEtale B S hS j.hom) (hjqc : IsQuasiCompact B S hS j.hom)
    (hjqs : IsQuasiSeparated B S hS j.hom)
    (Rj : DerivedCategory (Modules.{u, u} B S hS V.1 V.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (αj : (modulePushforward B S hS j).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj)
    [Rj.IsRightDerivedFunctor αj
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS V.1 V.2) (ComplexShape.up ℤ))]
    (DQX : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      (qcohDerivedCategoryB B S hS X).FullSubcategory)
    (adjX : (qcohDerivedCategoryB B S hS X).ι ⊣ DQX)
    (DQV : DerivedCategory (Modules.{u, u} B S hS V.1 V.2) ⥤
      (qcohDerivedCategoryB B S hS V).FullSubcategory)
    (adjV : (qcohDerivedCategoryB B S hS V).ι ⊣ DQV) :
    DQV ⋙ (qcohDerivedCategoryB B S hS X).lift ((qcohDerivedCategoryB B S hS V).ι ⋙ Rj)
        (fun E => derivedCategoryB_derivedPushforward_obj_of_isQuasiCompact_of_isQuasiSeparated
          B S hS j hjqc hjqs Rj αj E.obj E.property) ≅
      Rj ⋙ DQX :=
  let QX := qcohDerivedCategoryB B S hS X
  let QV := qcohDerivedCategoryB B S hS V
  let Lj := (etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory
  let adj : Lj ⊣ Rj := Stacks.DerivedFunctor.derivedAdjunction
    (etaleModulePullbackAdjunction B S hS j hj) Rj αj
    (exists_quasiIso_isKInjective_modules B S hS V.1 V.2)
  let Lj' : QX.FullSubcategory ⥤ QV.FullSubcategory := QV.lift (QX.ι ⋙ Lj)
    (fun E => derivedQuasicoherent_etaleModulePullback B S hS j hj E.obj E.property)
  let Rj' : QV.FullSubcategory ⥤ QX.FullSubcategory := QX.lift (QV.ι ⋙ Rj)
    (fun E => derivedCategoryB_derivedPushforward_obj_of_isQuasiCompact_of_isQuasiSeparated
      B S hS j hjqc hjqs Rj αj E.obj E.property)
  let adj' : Lj' ⊣ Rj' := adj.restrictFullyFaithful QX.fullyFaithfulι QV.fullyFaithfulι
    (QV.liftCompιIso _ _).symm (QX.liftCompιIso _ _).symm
  Adjunction.rightAdjointUniq ((adj'.comp adjV).ofNatIsoLeft (QV.liftCompιIso _ _))
    (adjX.comp adj)

/-- **Stacks 0CR5 for an étale quasi-compact quasi-separated morphism, objectwise**:
`DQ_X(Rj_* L) ≅ Rj_*(DQ_V L)` in `D(𝒪_X)`
(`AlgebraicGeometry.Space.coheratorDerivedPushforwardIsoOfIsEtale`). -/
theorem nonempty_coherator_derivedPushforward_obj_iso_of_isEtale {V X : AlgebraicSpaces B S hS}
    (j : V ⟶ X) (hj : IsEtale B S hS j.hom) (hjqc : IsQuasiCompact B S hS j.hom)
    (hjqs : IsQuasiSeparated B S hS j.hom)
    (Rj : DerivedCategory (Modules.{u, u} B S hS V.1 V.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (αj : (modulePushforward B S hS j).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj)
    [Rj.IsRightDerivedFunctor αj
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS V.1 V.2) (ComplexShape.up ℤ))]
    (DQX : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      (qcohDerivedCategoryB B S hS X).FullSubcategory)
    (adjX : (qcohDerivedCategoryB B S hS X).ι ⊣ DQX)
    (DQV : DerivedCategory (Modules.{u, u} B S hS V.1 V.2) ⥤
      (qcohDerivedCategoryB B S hS V).FullSubcategory)
    (adjV : (qcohDerivedCategoryB B S hS V).ι ⊣ DQV)
    (L : DerivedCategory (Modules.{u, u} B S hS V.1 V.2)) :
    Nonempty ((qcohDerivedCategoryB B S hS X).ι.obj (DQX.obj (Rj.obj L)) ≅
      Rj.obj ((qcohDerivedCategoryB B S hS V).ι.obj (DQV.obj L))) :=
  ⟨((qcohDerivedCategoryB B S hS X).ι.mapIso
    ((coheratorDerivedPushforwardIsoOfIsEtale B S hS j hj hjqc hjqs Rj αj DQX adjX DQV
      adjV).app L)).symm⟩

/-! ### The predicate of the induction -/

/-- **The boundedness of Stacks 0CSS along an étale morphism `j : Y ⟶ X`**: there is an integer
`N`, depending on `j` only, such that `DQ_X(Rj_*(K|_Y))` has its cohomology sheaves in
`[a, b + N]` whenever `K` satisfies the hypothesis of Stacks 0CSS on `X` for `[a, b]`, for every
right derived functor `Rj_*` of the direct image.  For `j = 𝟙` it is the conclusion of
Stacks 0CSS. -/
def CoheratorBoundedAlong (X : AlgebraicSpaces B S hS)
    (DQ : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      (qcohDerivedCategoryB B S hS X).FullSubcategory)
    {Y : AlgebraicSpaces B S hS} (j : Y ⟶ X) (hj : IsEtale B S hS j.hom) : Prop :=
  ∃ N : ℤ, ∀ (Rj : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (αj : (modulePushforward B S hS j).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj),
    Rj.IsRightDerivedFunctor αj
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ)) →
    ∀ (a b : ℤ) (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)),
      AffineChartAmplitudeIn B S hS X a b K →
      ((qcohDerivedCategoryB B S hS X).ι.obj (DQ.obj (Rj.obj
        ((etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory.obj K)))).IsGE a ∧
      ((qcohDerivedCategoryB B S hS X).ι.obj (DQ.obj (Rj.obj
        ((etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory.obj K)))).IsLE (b + N)

/-- `CoheratorBoundedAlong` along `j` gives it along any `j'` equal to `j`. -/
theorem CoheratorBoundedAlong.of_eq {X Y : AlgebraicSpaces B S hS}
    {DQ : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      (qcohDerivedCategoryB B S hS X).FullSubcategory}
    {j j' : Y ⟶ X} (h : j = j') {hj : IsEtale B S hS j.hom} (hj' : IsEtale B S hS j'.hom)
    (hb : CoheratorBoundedAlong B S hS X DQ j hj) : CoheratorBoundedAlong B S hS X DQ j' hj' := by
  subst h
  exact hb

/-- Sections over a chart of an étale restriction are the sections over the composite chart. -/
def etaleModulePullbackCompChartSectionsAbIso {V X : AlgebraicSpaces B S hS} (v : V ⟶ X)
    (hv : IsEtale B S hS v.hom) (T : SmallEtale B S hS V.1) :
    etaleModulePullback.{u, u} B S hS v hv ⋙ chartSectionsAb B S hS V T ≅
      chartSectionsAb B S hS X ((smallEtalePostcomp B S hS v hv).obj T) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- The cohomology over a chart of an étale restriction is the cohomology over the composite
chart. -/
theorem isZero_homology_chartSectionsAb_etaleModulePullback {V X : AlgebraicSpaces B S hS}
    (v : V ⟶ X) (hv : IsEtale B S hS v.hom) (T : SmallEtale B S hS V.1)
    (I : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) (i : ℤ)
    (h : IsZero ((((chartSectionsAb B S hS X
      ((smallEtalePostcomp B S hS v hv).obj T)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I).homology i)) :
    IsZero ((((chartSectionsAb B S hS V T).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((etaleModulePullback.{u, u} B S hS v hv).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I)).homology i) :=
  h.of_iso (HomologicalComplex.homologyMapIso
    ((Functor.mapHomologicalComplexCompIso
      (etaleModulePullbackCompChartSectionsAbIso B S hS v hv T) (ComplexShape.up ℤ)).app I) i)

/-- An object of the derived category lives in `[a, c]` iff its cohomology vanishes outside. -/
private theorem isGE_isLE_iff_isZero_homology {A : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] (Z : DerivedCategory A) (a c : ℤ) :
    (Z.IsGE a ∧ Z.IsLE c) ↔
      ∀ i : ℤ, i < a ∨ c < i → IsZero ((DerivedCategory.homologyFunctor A i).obj Z) := by
  refine ⟨fun ⟨_, _⟩ i hi => hi.elim (fun h => Z.isZero_of_isGE a i h)
    (fun h => Z.isZero_of_isLE c i h), fun h => ⟨?_, ?_⟩⟩
  · rw [DerivedCategory.isGE_iff]
    exact fun i hi => h i (Or.inl hi)
  · rw [DerivedCategory.isLE_iff]
    exact fun i hi => h i (Or.inr hi)

/-- Living in `[a, c]` is invariant under isomorphism. -/
private theorem isGE_isLE_of_iso {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {Z Z' : DerivedCategory A} (e : Z ≅ Z') (a c : ℤ) (h : Z.IsGE a ∧ Z.IsLE c) :
    Z'.IsGE a ∧ Z'.IsLE c :=
  have := h.1
  have := h.2
  ⟨DerivedCategory.TStructure.t.isGE_of_iso e a, DerivedCategory.TStructure.t.isLE_of_iso e c⟩

/-- **The boundedness of Stacks 0CSS holds along an étale morphism out of an affine algebraic
space** into a quasi-compact and quasi-separated `X`. -/
theorem coheratorBoundedAlong_of_isAffineSpace (X : AlgebraicSpaces B S hS)
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (DQ : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      (qcohDerivedCategoryB B S hS X).FullSubcategory)
    (adj : (qcohDerivedCategoryB B S hS X).ι ⊣ DQ)
    {V : AlgebraicSpaces B S hS} (hV : IsAffineSpace B S hS V.1) (v : V ⟶ X)
    (hv : IsEtale B S hS v.hom) : CoheratorBoundedAlong B S hS X DQ v hv := by
  have := isLeftAdjoint_ι_of_isAffineSpace B S hS V hV
  let adjV := Adjunction.ofIsLeftAdjoint (qcohDerivedCategoryB B S hS V).ι
  have hvqc : IsQuasiCompact B S hS v.hom :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS B.contains_terminal X.2 hXqs
      hV.isQuasiCompactSpace v.hom
  have hvqs : IsQuasiSeparated B S hS v.hom :=
    isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS B.contains_terminal V.2
      (IsAffineSpace.isAbsolutelyQuasiSeparated B S hS B.contains_terminal hV) v.hom
  obtain ⟨N, hN⟩ := exists_derivedPushforwardQuasicoherentBounded_of_isQuasiCompact B S hS v
    hvqc hvqs hXqc
  obtain ⟨T, ⟨hT⟩, hTa⟩ := exists_isTerminal_isAffine_chart B S hS V hV
  refine ⟨N, fun Rv αv hRv a b K hK => ?_⟩
  have := hRv
  let L := (etaleModulePullback.{u, u} B S hS v hv).mapDerivedCategory.obj K
  obtain ⟨I, hI, ⟨eI⟩⟩ :=
    CategoryTheory.PushforwardMayerVietoris.exists_isKInjective_representative_of_universe
      (exists_quasiIso_isKInjective_modules B S hS X.1 X.2) K
  let I' := ((etaleModulePullback.{u, u} B S hS v hv).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj I
  have hI' := isKInjective_etaleModulePullback_mapHomologicalComplex B S hS v hv I hI
  let eI' : DerivedCategory.Q.obj I' ≅ L :=
    ((etaleModulePullback.{u, u} B S hS v hv).mapDerivedCategoryFactors.app I).symm ≪≫
      (etaleModulePullback.{u, u} B S hS v hv).mapDerivedCategory.mapIso eI
  have hzero : ∀ i : ℤ, i < a ∨ b < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((qcohDerivedCategoryB B S hS V).ι.obj
        ((qcohDerivedCategoryB B S hS V).ι.rightAdjoint.obj L))) := fun i hi =>
    isZero_homology_coherator_obj_of_isTerminal B S hS V hT hTa _ adjV L I' hI' ⟨eI'⟩ i
      (isZero_homology_chartSectionsAb_etaleModulePullback B S hS v hv T I i
        (hK ((smallEtalePostcomp B S hS v hv).obj T) hTa I hI ⟨eI⟩ i hi))
  obtain ⟨hge, hle⟩ := (isGE_isLE_iff_isZero_homology _ a b).2 hzero
  obtain ⟨e⟩ := nonempty_coherator_derivedPushforward_obj_iso_of_isEtale B S hS v hv hvqc hvqs
    Rv αv DQ adj _ adjV L
  have h₁ : (Rv.obj ((qcohDerivedCategoryB B S hS V).ι.obj
      ((qcohDerivedCategoryB B S hS V).ι.rightAdjoint.obj L))).IsGE a :=
    Stacks.SmallDerivedCategory.isGE_obj_of_isGE (modulePushforward B S hS v) Rv αv
      (fun I hI => isIso_app_of_isKInjective_modulePushforward B S hS v DerivedCategory.Qh Rv αv
        I hI) _ a hge
  have h₂ : (Rv.obj ((qcohDerivedCategoryB B S hS V).ι.obj
      ((qcohDerivedCategoryB B S hS V).ι.rightAdjoint.obj L))).IsLE (b + N) :=
    (hN Rv αv hRv _ ((qcohDerivedCategoryB B S hS V).ι.rightAdjoint.obj L).property).2 b hle
  exact isGE_isLE_of_iso e.symm a (b + N) ⟨h₁, h₂⟩

/-! ### Amplitude along distinguished triangles -/

section Triangles

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]

/-- The middle vertex of a distinguished triangle whose outer vertices live in `[a, c]` lives in
`[a, c]`. -/
theorem isGE_isLE_obj₂_of_distinguished (T : Triangle (DerivedCategory A))
    (hT : T ∈ distTriang (DerivedCategory A)) (a c : ℤ) (h₁ : T.obj₁.IsGE a ∧ T.obj₁.IsLE c)
    (h₃ : T.obj₃.IsGE a ∧ T.obj₃.IsLE c) : T.obj₂.IsGE a ∧ T.obj₂.IsLE c :=
  ⟨DerivedCategory.TStructure.t.isGE₂ T hT a h₁.1 h₃.1,
    DerivedCategory.TStructure.t.isLE₂ T hT c h₁.2 h₃.2⟩

/-- The first vertex of a distinguished triangle whose other vertices live in `[a, c]` lives in
`[a, c + 1]`. -/
theorem isGE_isLE_obj₁_of_distinguished (T : Triangle (DerivedCategory A))
    (hT : T ∈ distTriang (DerivedCategory A)) (a c : ℤ) (h₂ : T.obj₂.IsGE a ∧ T.obj₂.IsLE c)
    (h₃ : T.obj₃.IsGE a ∧ T.obj₃.IsLE c) : T.obj₁.IsGE a ∧ T.obj₁.IsLE (c + 1) := by
  refine ⟨?_, isLE_obj₁_of_distinguished T hT c h₂.2 h₃.2⟩
  have : T.obj₃.IsGE a := h₃.1
  have h₃' : DerivedCategory.TStructure.t.IsGE
      ((shiftFunctor (DerivedCategory A) (-1 : ℤ)).obj T.obj₃) a :=
    have := DerivedCategory.TStructure.t.isGE_shift T.obj₃ a (-1) (a + 1) (by omega)
    DerivedCategory.TStructure.t.isGE_of_ge _ a (a + 1) (by omega)
  exact DerivedCategory.TStructure.t.isGE₂ T.invRotate (inv_rot_of_distTriang T hT) a h₃' h₂.1

end Triangles

/-! ### The inductive step -/

attribute [local instance] hasRightDerivedFunctor_mapHomotopyCategory_modules
  hasRightDerivedFunctor_modulePushforward

/-- **One vertex of the Mayer–Vietoris triangle.**  For `j : Y ⟶ W` and `w : W ⟶ X` étale, if
the boundedness holds along `j ≫ w` with the integer `N`, then `DQ_X(Rw_*(R(K|_W)))` lives in
`[a, b + N]` for every right derived functor `R` of `F ↦ j_*(F|_Y)`. -/
theorem isGE_isLE_coherator_derivedPushforward_restrictPush {X Y W : AlgebraicSpaces B S hS}
    (DQ : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      (qcohDerivedCategoryB B S hS X).FullSubcategory)
    (j : Y ⟶ W) (hj : IsEtale B S hS j.hom) (w : W ⟶ X) (hw : IsEtale B S hS w.hom)
    (hjw : IsEtale B S hS (j ≫ w).hom) {N : ℤ}
    (hN : ∀ (Rj : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
      (αj : (modulePushforward B S hS (j ≫ w)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj),
      Rj.IsRightDerivedFunctor αj
        (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ)) →
      ∀ (a b : ℤ) (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)),
        AffineChartAmplitudeIn B S hS X a b K →
        ((qcohDerivedCategoryB B S hS X).ι.obj (DQ.obj (Rj.obj
          ((etaleModulePullback.{u, u} B S hS (j ≫ w) hjw).mapDerivedCategory.obj K)))).IsGE a ∧
        ((qcohDerivedCategoryB B S hS X).ι.obj (DQ.obj (Rj.obj
          ((etaleModulePullback.{u, u} B S hS (j ≫ w) hjw).mapDerivedCategory.obj K)))).IsLE
            (b + N))
    (R : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (αR : (etaleModulePullback.{u, u} B S hS j hj ⋙ modulePushforward B S hS j).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R)
    [R.IsRightDerivedFunctor αR
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))]
    (Rw : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (αw : (modulePushforward B S hS w).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rw)
    [Rw.IsRightDerivedFunctor αw
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))]
    (a b : ℤ) (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hK : AffineChartAmplitudeIn B S hS X a b K) :
    ((qcohDerivedCategoryB B S hS X).ι.obj (DQ.obj (Rw.obj (R.obj
      ((etaleModulePullback.{u, u} B S hS w hw).mapDerivedCategory.obj K))))).IsGE a ∧
    ((qcohDerivedCategoryB B S hS X).ι.obj (DQ.obj (Rw.obj (R.obj
      ((etaleModulePullback.{u, u} B S hS w hw).mapDerivedCategory.obj K))))).IsLE (b + N) := by
  let Rjw := ((modulePushforward B S hS (j ≫ w)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ))
  let αjw := ((modulePushforward B S hS (j ≫ w)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ))
  let Fw := etaleModulePullback.{u, u} B S hS w hw
  let Fj := etaleModulePullback.{u, u} B S hS j hj
  let Fjw := etaleModulePullback.{u, u} B S hS (j ≫ w) hjw
  obtain ⟨e₁⟩ := nonempty_derivedPushforward_restrictPush_obj_iso B S hS j hj w R αR Rw αw Rjw αjw
    (Fw.mapDerivedCategory.obj K)
  let K₀ := DerivedCategory.Q.objPreimage K
  let eK := DerivedCategory.Q.objObjPreimageIso K
  let e₂ : Fj.mapDerivedCategory.obj (Fw.mapDerivedCategory.obj K) ≅
      Fjw.mapDerivedCategory.obj K :=
    ((Functor.mapDerivedCategoryComp Fw Fj).app K).symm ≪≫
      (Fw ⋙ Fj).mapDerivedCategory.mapIso eK.symm ≪≫
      (Fw ⋙ Fj).mapDerivedCategoryFactors.app K₀ ≪≫
      DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex
        (etaleModulePullbackCompIso B S hS j w hj hw hjw) (ComplexShape.up ℤ)).app K₀) ≪≫
      (Fjw.mapDerivedCategoryFactors.app K₀).symm ≪≫ Fjw.mapDerivedCategory.mapIso eK
  let e : (qcohDerivedCategoryB B S hS X).ι.obj (DQ.obj (Rw.obj (R.obj
      (Fw.mapDerivedCategory.obj K)))) ≅
      (qcohDerivedCategoryB B S hS X).ι.obj (DQ.obj (Rjw.obj (Fjw.mapDerivedCategory.obj K))) :=
    (qcohDerivedCategoryB B S hS X).ι.mapIso (DQ.mapIso (e₁ ≪≫ Rjw.mapIso e₂))
  obtain ⟨h₁, h₂⟩ := hN Rjw αjw inferInstance a b K hK
  exact isGE_isLE_of_iso e.symm a (b + N) ⟨h₁, h₂⟩

/-- **The inductive step of Stacks 0CSS.**  Let `(U ⊆ W, V ⟶ W)` be an elementary distinguished
square and `w : W ⟶ X` étale.  If the boundedness holds along the three étale morphisms
`U, V, U ×_W V ⟶ X`, it holds along `w`, with the largest of the three integers increased by
one. -/
theorem coheratorBoundedAlong_of_elementaryDistinguishedSquare (X : AlgebraicSpaces B S hS)
    (DQ : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      (qcohDerivedCategoryB B S hS X).FullSubcategory)
    (adj : (qcohDerivedCategoryB B S hS X).ι ⊣ DQ)
    {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
    (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV) (w : W ⟶ X)
    (hw : IsEtale B S hS w.hom)
    (hU : IsEtale B S hS (edsOpenHom B S hS hsq ≫ w).hom)
    (hV : IsEtale B S hS (edsEtaleHom B S hS hsq ≫ w).hom)
    (hP : IsEtale B S hS (edsInterHom B S hS hsq ≫ w).hom)
    (bU : CoheratorBoundedAlong B S hS X DQ (edsOpenHom B S hS hsq ≫ w) hU)
    (bV : CoheratorBoundedAlong B S hS X DQ (edsEtaleHom B S hS hsq ≫ w) hV)
    (bP : CoheratorBoundedAlong B S hS X DQ (edsInterHom B S hS hsq ≫ w) hP) :
    CoheratorBoundedAlong B S hS X DQ w hw := by
  let : DQ.CommShift ℤ := adj.rightAdjointCommShift ℤ
  let : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  have : adj.IsTriangulated := Adjunction.IsTriangulated.mk' adj
  have : DQ.IsTriangulated := inferInstance
  obtain ⟨NU, hNU⟩ := bU
  obtain ⟨NV, hNV⟩ := bV
  obtain ⟨NP, hNP⟩ := bP
  refine ⟨max NU (max NV NP) + 1, fun Rw αw hRw a b K hK => ?_⟩
  have := hRw
  let _ := Functor.IsRightDerivedFunctor.commShift Rw αw
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)) ℤ
  have : Rw.IsTriangulated :=
    Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor
      (modulePushforward B S hS w) Rw αw
  let G := Rw ⋙ DQ ⋙ (qcohDerivedCategoryB B S hS X).ι
  have : G.IsTriangulated := inferInstance
  let E := (etaleModulePullback.{u, u} B S hS w hw).mapDerivedCategory.obj K
  let c := b + max NU (max NV NP)
  have hmono : ∀ (Z : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (M : ℤ),
      M ≤ max NU (max NV NP) → Z.IsGE a ∧ Z.IsLE (b + M) → Z.IsGE a ∧ Z.IsLE c :=
    fun Z M hM h => ⟨h.1, have := h.2
      DerivedCategory.TStructure.t.isLE_of_le Z (b + M) c (by omega)⟩
  have h₁ : (G.obj ((edsDerivedRestrictPushOpen B S hS hsq).obj E)).IsGE a ∧
      (G.obj ((edsDerivedRestrictPushOpen B S hS hsq).obj E)).IsLE c :=
    hmono _ NU (le_max_left _ _)
      (isGE_isLE_coherator_derivedPushforward_restrictPush B S hS DQ (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq) w hw hU hNU _ (edsTotalRightDerivedUnitOpen B S hS hsq)
        Rw αw a b K hK)
  have h₂ : (G.obj ((edsDerivedRestrictPushEtale B S hS hsq).obj E)).IsGE a ∧
      (G.obj ((edsDerivedRestrictPushEtale B S hS hsq).obj E)).IsLE c :=
    hmono _ NV (le_trans (le_max_left _ _) (le_max_right _ _))
      (isGE_isLE_coherator_derivedPushforward_restrictPush B S hS DQ (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq) w hw hV hNV _ (edsTotalRightDerivedUnitEtale B S hS hsq)
        Rw αw a b K hK)
  have h₃ : (G.obj ((edsDerivedRestrictPushInter B S hS hsq).obj E)).IsGE a ∧
      (G.obj ((edsDerivedRestrictPushInter B S hS hsq).obj E)).IsLE c :=
    hmono _ NP (le_trans (le_max_right _ _) (le_max_right _ _))
      (isGE_isLE_coherator_derivedPushforward_restrictPush B S hS DQ (edsInterHom B S hS hsq)
        (isEtale_edsInterHom B S hS hsq) w hw hP hNP _ (edsTotalRightDerivedUnitInter B S hS hsq)
        Rw αw a b K hK)
  have hmid := isGE_isLE_obj₂_of_distinguished _
    (G.map_distinguished _ (binaryBiproductTriangle_distinguished
      ((edsDerivedRestrictPushOpen B S hS hsq).obj E)
      ((edsDerivedRestrictPushEtale B S hS hsq).obj E)))
    a c h₁ h₂
  obtain ⟨δ, hT⟩ :=
    exists_mem_distTriang_edsDerivedRestrictPushMayerVietorisLowerShriek B S hS hsq E
  have hE := isGE_isLE_obj₁_of_distinguished _ (G.map_distinguished _ hT) a c hmid h₃
  rwa [show b + (max NU (max NV NP) + 1) = c + 1 by omega]

/-! ### Stacks 0CSS -/

/-- **Stacks 0CSS.**  Let `S` be a scheme and `X` a quasi-compact and quasi-separated algebraic
space over `S`, and let `DQ_X` be the right adjoint of the inclusion `D_QCoh(𝒪_X) ⥤ D(𝒪_X)`
(Stacks 0CR4; any right adjoint, with its adjunction).  There is an integer `N = N(X)` such that
for all integers `a`, `b` and every `K` in `D(𝒪_X)` with `H^i(U, K) = 0` for every affine `U`
étale over `X` and every `i ∉ [a, b]`, the cohomology sheaves `H^i(DQ_X(K))` vanish for
`i ∉ [a, b + N]`.

The affine `U` étale over `X` are the étale charts `U` of `X` whose scheme is affine, and
`H^i(U, K)` is the `i`-th cohomology of the complex of sections over `U` of a K-injective complex
`I` representing `K`, i.e. of the unbounded derived sections `RΓ(U, K)`; the hypothesis is asked
of every such representative. -/
@[stacks 0CSS]
theorem exists_isZero_homology_coherator_obj (X : AlgebraicSpaces B S hS)
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (DQ : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).FullSubcategory)
    (adj : (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).ι ⊣ DQ) :
    ∃ N : ℤ, ∀ (a b : ℤ) (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)),
      (∀ U : SmallEtale B S hS X.1, IsAffineChart B S hS X.1 U →
        ∀ I : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ, I.IsKInjective →
          Nonempty (DerivedCategory.Q.obj I ≅ K) → ∀ i : ℤ, i < a ∨ b < i →
            IsZero ((((chartSectionsAb B S hS X U).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj I).homology i)) →
      ∀ i : ℤ, i < a ∨ b + N < i →
        IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj
          ((DerivedCategoryB.derivedCategoryB
            (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
              (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).ι.obj (DQ.obj K))) := by
  have key := qcqs_induction_on_self B S hS B.contains_terminal X hXqc hXqs
    (fun T j => ∀ (hT : IsAlgebraicSpace B S hS T) (hj : IsEtale B S hS j),
      CoheratorBoundedAlong B S hS X DQ (Y := ⟨T, hT⟩) (ObjectProperty.homMk j) hj)
    (fun V hV hT hj => coheratorBoundedAlong_of_isAffineSpace B S hS X hXqc hXqs DQ adj
      (V := ⟨V.1.left.1, hT⟩) hV _ hj)
    (fun W V U f hf hsq _ _ _ _ hU hV hP hT hw => ?_)
  · have h1 : IsEtale B S hS (𝟙 X : X ⟶ X).hom := isEtale_of_isIso B S hS (𝟙 X.1)
    obtain ⟨N, hN⟩ := (key X.2 h1).of_eq B S hS (j' := 𝟙 X) rfl h1
    refine ⟨N, fun a b K hK i hi => ?_⟩
    let R₁ := ((modulePushforward B S hS (𝟙 X)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))
    let α₁ := ((modulePushforward B S hS (𝟙 X)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))
    obtain ⟨hge, hle⟩ := hN R₁ α₁ inferInstance a b K hK
    let F := etaleModulePullback.{u, u} B S hS (𝟙 X) h1
    obtain ⟨I, hI, ⟨eI⟩⟩ :=
      CategoryTheory.PushforwardMayerVietoris.exists_isKInjective_representative_of_universe
        (exists_quasiIso_isKInjective_modules B S hS X.1 X.2) K
    let I₁ := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I
    have hI₁ := isKInjective_etaleModulePullback_mapHomologicalComplex B S hS (𝟙 X) h1 I hI
    let eII : ((modulePushforward B S hS (𝟙 X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj I₁ ≅
        I :=
      (NatIso.mapHomologicalComplex (modulePushforwardIdIso B S hS X) (ComplexShape.up ℤ)).app I₁ ≪≫
        (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).app I₁ ≪≫
        (NatIso.mapHomologicalComplex (etaleModulePullbackIdIso B S hS h1)
          (ComplexShape.up ℤ)).app I ≪≫
        (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).app I
    let eK : K ≅ R₁.obj (F.mapDerivedCategory.obj K) :=
      eI.symm ≪≫ DerivedCategory.Q.mapIso eII.symm ≪≫
        derivedPushforwardObjIsoOfIsKInjective B S hS (𝟙 X) R₁ α₁ I₁ hI₁ ≪≫
        R₁.mapIso ((F.mapDerivedCategoryFactors.app I).symm ≪≫ F.mapDerivedCategory.mapIso eI)
    let e := (qcohDerivedCategoryB B S hS X).ι.mapIso (DQ.mapIso eK)
    exact ((isGE_isLE_iff_isZero_homology _ a (b + N)).1
      (isGE_isLE_of_iso e.symm a (b + N) ⟨hge, hle⟩)) i hi
  · let W' : AlgebraicSpaces B S hS := ⟨W.1.left.1, hT⟩
    have hsq' : IsElementaryDistinguishedSquare B S hS W'.2 U f := hsq
    let w : W' ⟶ X := ObjectProperty.homMk W.1.hom.hom
    have hUe : IsEtale B S hS (edsOpenHom B S hS hsq' ≫ w).hom :=
      isEtale_comp B S hS (isEtale_edsOpenHom B S hS hsq') hw
    have hVe : IsEtale B S hS (edsEtaleHom B S hS hsq' ≫ w).hom :=
      isEtale_comp B S hS (isEtale_edsEtaleHom B S hS hsq') hw
    have hPe : IsEtale B S hS (edsInterHom B S hS hsq' ≫ w).hom :=
      isEtale_comp B S hS (isEtale_edsInterHom B S hS hsq') hw
    have hVe' : IsEtale B S hS V.1.hom.hom := hf ▸ hVe
    have hPe' : IsEtale B S hS (pullback.fst U.ι f ≫ U.ι ≫ W.1.hom.hom) :=
      isEtale_comp B S hS (isEtale_edsFst B S hS hsq')
        (isEtale_comp B S hS (isEtale_edsOpenHom B S hS hsq') hw)
    exact coheratorBoundedAlong_of_elementaryDistinguishedSquare B S hS X DQ adj hsq' w hw
      hUe hVe hPe
      ((hU (edsOpen B S hS hsq').2 hUe).of_eq B S hS rfl hUe)
      ((hV (edsEtale B S hS hsq').2 hVe').of_eq B S hS
        (ObjectProperty.hom_ext _ hf.symm) hVe)
      ((hP (edsInter B S hS hsq').2 hPe').of_eq B S hS
        (ObjectProperty.hom_ext _ (Category.assoc _ _ _).symm) hPe)

end AlgebraicGeometry.Space

end
