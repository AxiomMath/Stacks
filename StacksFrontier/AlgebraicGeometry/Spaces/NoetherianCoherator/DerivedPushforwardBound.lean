module

public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianCoherator.HigherDirectImageBound
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageSectionsOverChart
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBasePushforwardInjectiveAcyclic
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartModuleCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedFunctorAmplitudeUnbounded
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDenseSubsite
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedModulePushforward
public import StacksFrontier.CategoryTheory.Sites.VanishingOfDerivedSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.GlobalCohomologyOnALargeSite
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# The derived direct image of a quasi-compact quasi-separated morphism has bounded amplitude

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of quasi-compact and
quasi-separated algebraic spaces.  There is an integer `N` such that `Rf_*` carries an object of
`D(𝒪_X)` with quasi-coherent cohomology sheaves living in degrees `≤ d` to an object living in
degrees `≤ d + N - 1`.

The argument is the source's (Stacks 08FA).  The higher direct images `R^p f_*𝓕` of
quasi-coherent modules vanish for `p ≥ N`
(`AlgebraicGeometry.Space.exists_isZero_rightDerived_modulePushforward_of_qcqs`).  For an affine
étale chart `V` of `Y` the functor `F_V = Γ(V, f_*-)` therefore has
`R^p F_V(𝓕) = Γ(V, R^p f_*𝓕) = 0` for `p ≥ N`, the Leray spectral sequence degenerating because
the direct image of an injective module and the quasi-coherent higher direct images are acyclic
for sections over an affine chart.  Stacks 08F7 then bounds `RF_V`, and `RF_V(E)` is the complex
of sections over `V` of `f_* I` for a K-injective `I` representing `E`.  A complex of sheaves
whose complexes of sections over the affine charts are acyclic in a degree is acyclic in that
degree.

## Main results

* `AlgebraicGeometry.Space.isZero_homology_of_forall_isAffineChart`: a complex of `𝒪_Y`-modules
  is acyclic in degree `q` as soon as its complexes of sections over the affine étale charts are.
* `AlgebraicGeometry.Space.exists_isLE_rightDerivedFunctor_obj_modulePushforward`: the bound.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard hasInjectiveResolutions_modules
  isGrothendieckAbelian_modules enoughInjectives_modules

attribute [local instance 5000] modulePushforward_additive

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Sections over an étale chart, as an abelian group. -/
abbrev chartSectionsAb (Y : AlgebraicSpaces B S hS) (V : SmallEtale B S hS Y.1) :
    Modules.{u, u} B S hS Y.1 Y.2 ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS Y.1 Y.2).O) (op V) ⋙
    forget₂ (ModuleCat.{u} _) AddCommGrpCat.{u}

/-- The affine étale charts form a covering family of the small étale site: every chart is
covered by the affine charts mapping to it, the inclusion of the affine étale site being cover
dense (Stacks 04JS). -/
theorem isCoveringFamily_isAffineChart (Y : AlgebraicSpaces B S hS) :
    (SmallEtale.topology B S hS Y.1).IsCoveringFamily (IsAffineChart B S hS Y.1) := by
  have := (AffineEtale.inclusion_isSpecialCocontinuous B S hS Y.1 Y.2).2
  have hc : (AffineEtale.inclusion B S hS Y.1).IsCoverDense (SmallEtale.topology B S hS Y.1) :=
    Functor.IsDenseSubsite.isCoverDense (AffineEtale.topology B S hS Y.1) _ _
  intro U
  refine ⟨fun Z _ => IsAffineChart B S hS Y.1 Z, ?_, fun Z _ hZ => hZ⟩
  refine (SmallEtale.topology B S hS Y.1).superset_covering ?_
    ((AffineEtale.inclusion B S hS Y.1).is_cover_of_isCoverDense _ U)
  rintro Z g ⟨⟨W, k, h, rfl⟩⟩
  exact ⟨_, k, h, W.2, rfl⟩

/-- **A complex of `𝒪_Y`-modules whose complexes of sections over the affine étale charts are
acyclic in degree `q` is acyclic in degree `q`.**  Sections over a chart are left exact, so they
carry the projection `Z^q ⟶ H^q` to a map factoring through the `q`-th homology of the complex
of sections, which vanishes; a morphism of sheaves vanishing on the affine charts vanishes,
those charts covering the site, and the projection is an epimorphism. -/
theorem isZero_homology_of_forall_isAffineChart (Y : AlgebraicSpaces B S hS)
    (C : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ) (q : ℤ)
    (h : ∀ V : SmallEtale B S hS Y.1, IsAffineChart B S hS Y.1 V →
      IsZero ((((chartSectionsAb B S hS Y V).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C).homology q)) :
    IsZero (C.homology q) := by
  let R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O
  have hφ : (SheafOfModules.toSheaf R).map (C.homologyπ q) = 0 :=
    Sheaf.hom_eq_zero_of_isCoveringFamily _ (isCoveringFamily_isAffineChart B S hS Y) fun V hV =>
      Stacks.Cohomology.DerivedSectionsVanishing.map_homologyπ_eq_zero
        (chartSectionsAb B S hS Y V) C q (h V hV)
  have h0 : C.homologyπ q = 0 := (SheafOfModules.toSheaf R).map_injective (by simpa using hφ)
  rw [IsZero.iff_id_eq_zero]
  exact (cancel_epi (C.homologyπ q)).1 (by rw [h0, zero_comp, comp_zero])

section Bound

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- **The Leray degeneration at an affine chart.**  For `f` quasi-compact and quasi-separated, a
quasi-coherent `𝓕` and an affine étale chart `V` of `Y`, if `R^n f_*𝓕 = 0` then the `n`-th right
derived functor of `Γ(V, f_* -)` vanishes at `𝓕`: applying `f_*` to an injective resolution of `𝓕`
gives a complex whose terms are acyclic for sections over `V` (Stacks 072Z) and whose cohomology
objects, the higher direct images, are quasi-coherent (Stacks 0720), hence acyclic over the
affine `V`, so that sections over `V` commute with its cohomology. -/
theorem isZero_rightDerived_modulePushforward_comp_evaluation
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (V : SmallEtale B S hS Y.1) (hV : IsAffineChart B S hS Y.1 V)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite) (n : ℕ)
    (hn : IsZero (((modulePushforward B S hS f).rightDerived n).obj M)) :
    IsZero (((modulePushforward B S hS f ⋙ SheafOfModules.evaluation
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)
        (op V)).rightDerived n).obj M) := by
  let T := SheafOfModules.evaluation
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O) (op V)
  refine IsZero.of_iso (T.map_isZero hn) ((injectiveResolution M).isoRightDerivedObj
      (modulePushforward B S hS f ⋙ T) n ≪≫
    Stacks.Cohomology.RightDerivedCoEdge.homologyIsoMapHomologyOfAcyclic T
      (Stacks.RightDerivedComp.mapCocomplex (modulePushforward B S hS f)
        (injectiveResolution M))
      (fun q k hk => isZero_rightDerived_evaluation_modulePushforward_of_injective B S hS f _
        ((injectiveResolution M).injective q) V k hk)
      (fun q => Stacks.Cohomology.RightDerivedCoEdge.acyclic_of_iso T
        ((injectiveResolution M).isoRightDerivedObj (modulePushforward B S hS f) q)
        (fun k hk => isZero_rightDerived_evaluation_of_isQuasicoherentOnSite B S hS Y.1 Y.2 V hV
          _ (isQuasicoherentOnSite_rightDerived_modulePushforward' B S hS f hfqc hfqs M q) k hk))
      n ≪≫
    T.mapIso ((injectiveResolution M).isoRightDerivedObj (modulePushforward B S hS f) n).symm)

/-- `Γ(V, f_* -)` as an abelian-group-valued functor commutes with countable products: `f_*` is
a right adjoint, and sections over a chart and the forgetful functor preserve limits. -/
theorem preservesLimitsOfShape_modulePushforward_comp_chartSectionsAb (V : SmallEtale B S hS Y.1) :
    PreservesLimitsOfShape (Discrete ℕ)
      (modulePushforward B S hS f ⋙ chartSectionsAb B S hS Y V) := by
  have : PreservesLimitsOfSize.{0, 0} (modulePushforward B S hS f) :=
    (modulePullbackAdjunction B S hS f).rightAdjoint_preservesLimits
  infer_instance

/-- `R^n Γ(V, f_* -)` vanishes at a quasi-coherent module above a vanishing bound of the higher
direct images, in the `ℤ`-indexed form of Stacks 08F7. -/
theorem isZero_rightDerivedPlus_modulePushforward_comp_chartSectionsAb
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (V : SmallEtale B S hS Y.1) (hV : IsAffineChart B S hS Y.1 V)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite) (k : ℕ)
    (hk : IsZero (((modulePushforward B S hS f).rightDerived k).obj M)) :
    IsZero (((modulePushforward B S hS f ⋙ chartSectionsAb B S hS Y V).rightDerivedPlus
      (k : ℤ)).obj M) := by
  refine (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff _ rfl M).2 ?_
  refine IsZero.of_iso ?_ ((Stacks.Cohomology.ColimitsOfCohomology.rightDerivedCompExactIso
    (modulePushforward B S hS f ⋙ SheafOfModules.evaluation
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O) (op V))
    (forget₂ (ModuleCat.{u} _) AddCommGrpCat.{u}) k).app M)
  exact (forget₂ (ModuleCat.{u} _) AddCommGrpCat.{u}).map_isZero
    (isZero_rightDerived_modulePushforward_comp_evaluation B S hS f hfqc hfqs V hV M hM k hk)

/-- The value of a right derived functor at a complex where its derivation unit is invertible is
the class of the termwise image of that complex. -/
def _root_.CategoryTheory.Functor.rightDerivedObjIsoOfIsIso {A C : Type*} [Category* A]
    [Category* C] [Abelian A] [Abelian C] [HasDerivedCategory A] [HasDerivedCategory C]
    (F : A ⥤ C) [F.Additive] (RF : DerivedCategory A ⥤ DerivedCategory C)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF) (I : CochainComplex A ℤ)
    [IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I))] :
    RF.obj (DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  RF.mapIso ((DerivedCategory.quotientCompQhIso A).app I).symm ≪≫
    (asIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I))).symm ≪≫
    DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app I).symm ≪≫
    (DerivedCategory.quotientCompQhIso C).app _

/-- If the derivation unit is invertible at `I`, the homology of `RF.obj E` for `E ≅ Q I` vanishes
exactly when that of the termwise image `F I` does. -/
private theorem isZero_homologyFunctor_obj_iff_of_isIso {A C : Type*} [Category* A]
    [Category* C] [Abelian A] [Abelian C] [HasDerivedCategory A] [HasDerivedCategory C]
    (F : A ⥤ C) [F.Additive] (RF : DerivedCategory A ⥤ DerivedCategory C)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF) (I : CochainComplex A ℤ)
    [IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I))]
    {E : DerivedCategory A} (eE : DerivedCategory.Q.obj I ≅ E) (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor C i).obj (RF.obj E)) ↔
      IsZero (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I).homology i) :=
  Iso.isZero_iff ((DerivedCategory.homologyFunctor C i).mapIso
      (RF.mapIso eE.symm ≪≫ F.rightDerivedObjIsoOfIsIso RF α I) ≪≫
    (DerivedCategory.homologyFunctorFactors C i).app _)

/-- **Stacks 08FA, part (2), in amplitude form.**  Let `f : X ⟶ Y` be a morphism of quasi-compact
and quasi-separated algebraic spaces.  There is an integer `N` such that every right derived
functor `Rf_*` of the direct image carries an object of `D(𝒪_X)` with quasi-coherent cohomology
sheaves living in degrees `≤ d` to an object living in degrees `≤ d + N - 1`. -/
theorem exists_isLE_rightDerivedFunctor_obj_modulePushforward (hZ : B.Contains (⊤_ Scheme.{u}))
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (hYqc : IsQuasiCompactSpace B S hS Y.1) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1) :
    ∃ N : ℕ, ∀ (Rf : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
        DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
      (α : (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf),
      Rf.IsRightDerivedFunctor α
        (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) →
      ∀ E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2),
        (∀ i : ℤ, ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj
          E).IsQuasicoherentOnSite) →
        ∀ d : ℤ, E.IsLE d → (Rf.obj E).IsLE (d + N - 1) := by
  have hfqc := isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hXqc f.hom
  have hfqs := isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X.2 hXqs f.hom
  obtain ⟨N, hN⟩ := exists_isZero_rightDerived_modulePushforward_of_qcqs B S hS hZ f hXqc hXqs
    hYqc hYqs
  refine ⟨N, fun Rf α hRf E hqc d hE => ?_⟩
  obtain ⟨I, q, hI, hq⟩ := exists_quasiIso_isKInjective_modules B S hS X.1 X.2
    (DerivedCategory.Q.objPreimage E)
  have eE : DerivedCategory.Q.obj I ≅ E :=
    (asIso (DerivedCategory.Q.map q)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso E
  have : IsIso (α.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) :=
    isIso_app_of_isKInjective_modulePushforward B S hS f DerivedCategory.Qh Rf α I hI
  rw [DerivedCategory.isLE_iff]
  intro i hi
  refine (isZero_homologyFunctor_obj_iff_of_isIso (modulePushforward B S hS f) Rf α I eE i).2 ?_
  refine isZero_homology_of_forall_isAffineChart B S hS Y _ i fun V hV => ?_
  let FV := modulePushforward B S hS f ⋙ chartSectionsAb B S hS Y V
  let W := HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)
  let G := FV.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  obtain ⟨_, hiso⟩ :=
    Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective G
      (exists_quasiIso_isKInjective_modules B S hS X.1 X.2)
  have : G.HasRightDerivedFunctor W :=
    Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _
  let RFV := G.totalRightDerived DerivedCategory.Qh W
  let αV := G.totalRightDerivedUnit DerivedCategory.Qh W
  have := preservesLimitsOfShape_modulePushforward_comp_chartSectionsAb B S hS f V
  have := isLE_rightDerived_obj_of_isLE B S hS X.1 X.2 FV RFV αV N
    (fun M hM p hp => by
      obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = k := ⟨p.toNat, by omega⟩
      exact isZero_rightDerivedPlus_modulePushforward_comp_chartSectionsAb B S hS f hfqc hfqs V
        hV M hM k (hN M hM k (by omega)))
    E hqc d hE
  have : IsIso (αV.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) :=
    hiso DerivedCategory.Qh RFV αV I hI
  exact (isZero_homologyFunctor_obj_iff_of_isIso FV RFV αV I eE i).1
    ((RFV.obj E).isZero_of_isLE (d + N - 1) i (by omega))

end Bound

end AlgebraicGeometry.Space

end
