module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDerivedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePushforwardFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts

/-!
# The derived direct image along an affine morphism of algebraic spaces on `D_QCoh`

Let `g : W ⟶ Y` be an affine morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, and let `Rg_*` be a right derived functor of the direct image of modules on the
unbounded derived categories. For `E` in `D_QCoh(𝒪_W)`:

* `Rg_*E` lies in degrees `≤ c` whenever `E` does;
* every cohomology sheaf of `Rg_*E` is quasi-coherent.

## Main results

* `AlgebraicGeometry.Space.exactAt_modulePushforward_of_isAffineHom`: the direct image of a
  K-injective complex with quasi-coherent cohomology in degrees `≤ c` is exact above `c`.
* `AlgebraicGeometry.Space.exists_isKInjective_iso_modules`: every object of the derived category
  is isomorphic to a K-injective complex.
* `AlgebraicGeometry.Space.nonempty_rightDerived_obj_iso_of_isKInjective`: a right derived functor
  of the direct image is computed by K-injective complexes.
* `AlgebraicGeometry.Space.isLE_rightDerived_modulePushforward_of_isAffineHom`: `Rg_*E` lies in
  degrees `≤ c` whenever `E` in `D_QCoh(𝒪_W)` does.
* `isQuasicoherentOnSite_homology_rightDerived_modulePushforward_of_isAffineHom`:
  `Rg_*` carries `D_QCoh(𝒪_W)` into `D_QCoh(𝒪_Y)`.

## References

* [Stacks Project, Tag 08F7](https://stacks.math.columbia.edu/tag/08F7)
* [Stacks Project, Tag 073H](https://stacks.math.columbia.edu/tag/073H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

variable {W Y : AlgebraicSpaces B S hS}

/-- The direct image along an affine morphism of a K-injective complex of `𝒪_W`-modules with
quasi-coherent cohomology vanishing above `c` is exact above `c`. -/
theorem exactAt_modulePushforward_of_isAffineHom (g : W ⟶ Y) (hg : IsAffineHom B S hS g.hom)
    (I : CochainComplex (Modules.{u, u} B S hS W.1 W.2) ℤ) (hI : I.IsKInjective)
    (hqc : ∀ q : ℤ, (I.homology q).IsQuasicoherentOnSite)
    (c : ℤ) (hc : ∀ q : ℤ, c < q → IsZero (I.homology q)) (j : ℤ) (hj : c < j) :
    (((modulePushforward B S hS g).mapHomologicalComplex (ComplexShape.up ℤ)).obj I).ExactAt j := by
  have hrep := relativelyRepresentable_of_isAffineHom B S hS g hg
  have := Functor.preservesZeroMorphisms_of_iso (modulePushforwardChartIso B S hS g hrep)
  refine HomologicalComplex.ExactAt.of_iso ?_
    ((NatIso.mapHomologicalComplex (modulePushforwardChartIso B S hS g hrep)
      (ComplexShape.up ℤ)).app I).symm
  refine exactAt_of_forall_isAffineChart B S hS Y.1 Y.2 _ j fun V hV => ?_
  have hV' := isAffine_smallBaseChange_obj B S hS g hrep hg V hV
  have h := exactAt_sections_of_isKInjective_of_isAffineChart B S hS W.1 W.2
    ((smallBaseChange B S hS g hrep).obj V) hV' I hI hqc c hc j hj
  rwa [HomologicalComplex.exactAt_iff' _ (j - 1) j (j + 1) (by simp) (by simp),
    ShortComplex.ab_exact_iff] at h ⊢

/-- Every object of `D(𝒪_W)` is isomorphic to a K-injective complex. -/
theorem exists_isKInjective_iso_modules (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) :
    ∃ (I : CochainComplex (Modules.{u, u} B S hS W.1 W.2) ℤ), I.IsKInjective ∧
      Nonempty (E ≅ DerivedCategory.Q.obj I) := by
  obtain ⟨I, φ, hI, hφ⟩ := exists_quasiIso_isKInjective_modules B S hS W.1 W.2
    (DerivedCategory.Q.objPreimage E)
  exact ⟨I, hI, ⟨(DerivedCategory.Q.objObjPreimageIso E).symm ≪≫
    asIso (DerivedCategory.Q.map φ)⟩⟩

section RightDerived

variable (g : W ⟶ Y)
  (RF : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
    DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
  (α : (modulePushforward B S hS g).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor α
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))]

include α in
/-- A right derived functor of the direct image is computed by K-injective complexes:
`RF(Q I) ≅ Q(g_* I)`. -/
theorem nonempty_rightDerived_obj_iso_of_isKInjective
    (I : CochainComplex (Modules.{u, u} B S hS W.1 W.2) ℤ) (hI : I.IsKInjective) :
    Nonempty (RF.obj (DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj (((modulePushforward B S hS g).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I)) := by
  have h := isIso_app_of_isKInjective_modulePushforward B S hS g DerivedCategory.Qh RF α I hI
  exact ⟨RF.mapIso ((DerivedCategory.quotientCompQhIso _).app I).symm ≪≫
    (@asIso _ _ _ _ (α.app ((HomotopyCategory.quotient _ _).obj I)) h).symm ≪≫
    (DerivedCategory.quotientCompQhIso _).app _⟩

include α in
/-- If `E` has quasi-coherent cohomology sheaves and lives in degrees `≤ c`, then so does `Rg_*E`,
for every right derived functor `Rg_*` of the direct image along an affine `g`. -/
theorem isLE_rightDerived_modulePushforward_of_isAffineHom (hg : IsAffineHom B S hS g.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hqc : ∀ q : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS W.1 W.2) q).obj E).IsQuasicoherentOnSite)
    (c : ℤ) (hE : E.IsLE c) : (RF.obj E).IsLE c := by
  obtain ⟨I, hI, ⟨e⟩⟩ := exists_isKInjective_iso_modules B S hS E
  obtain ⟨e'⟩ := nonempty_rightDerived_obj_iso_of_isKInjective B S hS g RF α I hI
  have hIc : (DerivedCategory.Q.obj I).IsLE c := DerivedCategory.TStructure.t.isLE_of_iso e c
  rw [DerivedCategory.isLE_Q_obj_iff, CochainComplex.isLE_iff] at hIc
  have hEI : ∀ q : ℤ, (I.homology q).IsQuasicoherentOnSite := fun q =>
    SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((DerivedCategory.homologyFunctor _ q).mapIso e ≪≫
        (DerivedCategory.homologyFunctorFactors _ q).app I) (hqc q)
  have hpush : CochainComplex.IsLE (((modulePushforward B S hS g).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I) c := by
    rw [CochainComplex.isLE_iff]
    exact fun j hj => exactAt_modulePushforward_of_isAffineHom B S hS g hg I hI hEI c
      (fun q hq => (hIc q hq).isZero_homology) j hj
  exact DerivedCategory.TStructure.t.isLE_of_iso (RF.mapIso e ≪≫ e').symm c

include α in
/-- For an affine `g` and `E` in `D_QCoh(𝒪_W)`, every cohomology sheaf of `Rg_*E` is
quasi-coherent, for every right derived functor `Rg_*` of the direct image along `g`. -/
theorem isQuasicoherentOnSite_homology_rightDerived_modulePushforward_of_isAffineHom
    (hg : IsAffineHom B S hS g.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hqc : ∀ q : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS W.1 W.2) q).obj E).IsQuasicoherentOnSite)
    (i : ℤ) :
    ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).obj
      (RF.obj E)).IsQuasicoherentOnSite := by
  let PW := SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O))
  let PY := SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))
  have hcomp : ∀ I : CochainComplex (Modules.{u, u} B S hS W.1 W.2) ℤ, I.IsKInjective →
      IsIso (α.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) :=
    fun I hI => isIso_app_of_isKInjective_modulePushforward B S hS g DerivedCategory.Qh RF α I hI
  let _ := Functor.IsRightDerivedFunctor.commShift RF α
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)) ℤ
  have : RF.IsTriangulated :=
    Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor
      (modulePushforward B S hS g) RF α
  have hsingle : ∀ M : Modules.{u, u} B S hS W.1 W.2, M.IsQuasicoherentOnSite → ∀ n j : ℤ,
      PY ((DerivedCategory.homologyFunctor _ j).obj
        (RF.obj ((DerivedCategory.singleFunctor _ n).obj M))) := by
    intro M hM n j
    refine Stacks.SmallDerivedCategory.prop_homologyFunctor_obj_singleFunctor_obj
      (modulePushforward B S hS g) RF α hcomp PY M (fun p => ?_) n j
    obtain ⟨e⟩ := Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus
      (modulePushforward B S hS g) RF α hcomp
      ((DerivedCategory.Plus.singleFunctor _ 0).obj M) 0 (by
        show ((DerivedCategory.singleFunctor _ 0).obj M).IsGE 0
        infer_instance)
    have a₁ : ((modulePushforward B S hS g).rightDerivedPlus p).obj M ≅
        (DerivedCategory.homologyFunctor _ p).obj
          (RF.obj ((DerivedCategory.singleFunctor _ 0).obj M)) :=
      ((DerivedCategory.homologyFunctor _ p).mapIso e).symm
    rcases eq_or_ne p 0 with rfl | hp0
    · exact PY.prop_of_iso
        (Stacks.RightDerivedPlus.rightDerivedPlusZeroObjIso (modulePushforward B S hS g) M).symm
        (isQuasicoherentOnSite_modulePushforward_isAffineHom B S hS g hg M hM)
    refine PY.prop_of_isZero (.of_iso ?_ a₁)
    rcases lt_or_gt_of_ne hp0 with hp | hp
    · have : (RF.obj ((DerivedCategory.singleFunctor _ 0).obj M)).IsGE 0 :=
        Stacks.SmallDerivedCategory.isGE_obj_of_isGE (modulePushforward B S hS g) RF α hcomp
          _ 0 inferInstance
      exact (RF.obj _).isZero_of_isGE 0 p hp
    · have hqc0 : ∀ q : ℤ, ((DerivedCategory.homologyFunctor _ q).obj
          ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS W.1 W.2) 0).obj
            M)).IsQuasicoherentOnSite := by
        intro q
        rcases eq_or_ne q 0 with rfl | hq0
        · exact PW.prop_of_iso
            ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M).symm hM
        refine PW.prop_of_isZero ?_
        rcases lt_or_gt_of_ne hq0 with hq | hq
        · exact DerivedCategory.isZero_of_isGE _ 0 q hq
        · exact DerivedCategory.isZero_of_isLE _ 0 q hq
      have : (RF.obj ((DerivedCategory.singleFunctor _ 0).obj M)).IsLE 0 :=
        isLE_rightDerived_modulePushforward_of_isAffineHom B S hS g RF α hg _ hqc0 0
          inferInstance
      exact (RF.obj _).isZero_of_isLE 0 p hp
  have hπ : IsIso ((DerivedCategory.homologyFunctor _ i).map
      (RF.map ((DerivedCategory.TStructure.t.truncGEπ i).app E))) := by
    let T := RF.mapTriangle.obj ((DerivedCategory.TStructure.t.triangleLEGE
      (i - 1) i (by omega)).obj E)
    have hT : T ∈ distTriang _ := RF.map_distinguished _
      (DerivedCategory.TStructure.t.triangleLEGE_distinguished (i - 1) i (by omega) E)
    have hl : T.obj₁.IsLE (i - 1) :=
      isLE_rightDerived_modulePushforward_of_isAffineHom B S hS g RF α hg _
        (fun q => Stacks.SmallDerivedCategory.prop_homologyFunctor_truncLE_obj PW E hqc
          (i - 1) q) (i - 1) inferInstance
    have hz := T.obj₁.isZero_of_isLE (i - 1) i (by omega)
    have hz' := T.obj₁.isZero_of_isLE (i - 1) (i + 1) (by omega)
    have : Mono ((DerivedCategory.homologyFunctor _ i).map T.mor₂) :=
      (DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff T hT i).2 (hz.eq_of_src _ _)
    have : Epi ((DerivedCategory.homologyFunctor _ i).map T.mor₂) :=
      (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT i (i + 1) rfl).2
        (hz'.eq_of_tgt _ _)
    exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor _ i).map T.mor₂)
  let E₁ := (DerivedCategory.TStructure.t.truncGE i).obj E
  have hqc₁ : ∀ q : ℤ, PW ((DerivedCategory.homologyFunctor _ q).obj E₁) := fun q =>
    Stacks.SmallDerivedCategory.prop_homologyFunctor_truncGE_obj PW E hqc i q
  have hι : IsIso ((DerivedCategory.homologyFunctor _ i).map
      (RF.map ((DerivedCategory.TStructure.t.truncLEι i).app E₁))) := by
    let T := RF.mapTriangle.obj ((DerivedCategory.TStructure.t.triangleLEGE i (i + 1) rfl).obj E₁)
    have hT : T ∈ distTriang _ := RF.map_distinguished _
      (DerivedCategory.TStructure.t.triangleLEGE_distinguished i (i + 1) rfl E₁)
    have hg' : T.obj₃.IsGE (i + 1) :=
      Stacks.SmallDerivedCategory.isGE_obj_of_isGE (modulePushforward B S hS g) RF α hcomp
        ((DerivedCategory.TStructure.t.truncGE (i + 1)).obj E₁) (i + 1) inferInstance
    have hz := T.obj₃.isZero_of_isGE (i + 1) i (by omega)
    have hz' := T.obj₃.isZero_of_isGE (i + 1) (i - 1) (by omega)
    have : Epi ((DerivedCategory.homologyFunctor _ i).map T.mor₁) :=
      (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i).2 (hz.eq_of_tgt _ _)
    have : Mono ((DerivedCategory.homologyFunctor _ i).map T.mor₁) :=
      (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT (i - 1) i (by omega)).2
        (hz'.eq_of_src _ _)
    exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor _ i).map T.mor₁)
  let E₂ := (DerivedCategory.TStructure.t.truncLE i).obj E₁
  have hqc₂ : ∀ q : ℤ, PW ((DerivedCategory.homologyFunctor _ q).obj E₂) := fun q =>
    Stacks.SmallDerivedCategory.prop_homologyFunctor_truncLE_obj PW E₁ hqc₁ i q
  have _ : E₂.IsGE i := inferInstanceAs
    (((DerivedCategory.TStructure.t.truncLE i).obj E₁).IsGE i)
  have _ : E₂.IsLE i := inferInstanceAs
    (((DerivedCategory.TStructure.t.truncLE i).obj E₁).IsLE i)
  obtain ⟨M, ⟨e⟩⟩ := E₂.exists_iso_singleFunctor_obj_of_isGE_of_isLE i
  have hM : M.IsQuasicoherentOnSite := PW.prop_of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso _ i).app M) (hqc₂ i)
  have h₂ : PY ((DerivedCategory.homologyFunctor _ i).obj (RF.obj E₂)) :=
    PY.prop_of_iso ((DerivedCategory.homologyFunctor _ i).mapIso (RF.mapIso e)).symm
      (hsingle M hM i i)
  have h₁ : PY ((DerivedCategory.homologyFunctor _ i).obj (RF.obj E₁)) :=
    PY.prop_of_iso (asIso ((DerivedCategory.homologyFunctor _ i).map
      (RF.map ((DerivedCategory.TStructure.t.truncLEι i).app E₁)))) h₂
  exact PY.prop_of_iso (asIso ((DerivedCategory.homologyFunctor _ i).map
    (RF.map ((DerivedCategory.TStructure.t.truncGEπ i).app E)))).symm h₁

end RightDerived

end AlgebraicGeometry.Space

end
