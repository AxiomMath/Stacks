module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCover
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPushforwardAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedDirectImage
public import StacksFrontier.Homology.DerivedCategory.IsZero
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncationLevelHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.SingleObject

/-!
# The derived direct image along an affine morphism is conservative on `D_QCoh`

Let `g : W ⟶ Y` be an affine morphism of algebraic spaces. A quasi-coherent `𝒪_W`-module `𝓕`
with `g_*𝓕 = 0` is zero, and an object `E` of `D_QCoh(𝒪_W)` with `Rg_*E = 0` is zero.

## Main results

* `AlgebraicGeometry.Space.isZero_of_isZero_modulePushforward_of_isAffineHom`: the module case.
* `AlgebraicGeometry.Space.isZero_of_isZero_rightDerived_modulePushforward_of_isAffineHom`: the
  derived case, for every right derived functor of the direct image.

## Implementation notes

For the module case, every chart of `W` is covered by affine charts `W'` mapping to a chart
`V ×_Y W` with `V` affine (`AlgebraicGeometry.Space.mem_topology_of_hasAffineChartDiagram`), and
quasi-coherence makes the sections over `W'` the base change of the sections over `V ×_Y W`,
which are the sections of `g_*𝓕` over `V`.

For the derived case fix a degree `i`. The derived direct image raises no upper bound on
`D_QCoh` (`AlgebraicGeometry.Space.isLE_rightDerived_modulePushforward_of_isAffineHom`) and
lowers no lower bound, so the truncation triangles of `E` at `i` show that `Rg_*` kills
`τ_{≥ i}E` and then `τ_{≤ i}τ_{≥ i}E`, which is `Hⁱ(E)` placed in degree `i`; in degree zero the
derived direct image of a module is its direct image, and the module case applies.

## References

* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Pretriangulated

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {W Y : AlgebraicSpaces B S hS}

/-- **A quasi-coherent module with zero direct image along an affine morphism is zero.** -/
theorem isZero_of_isZero_modulePushforward_of_isAffineHom (g : W ⟶ Y)
    (hg : IsAffineHom B S hS g.hom) (F : Modules.{u, u} B S hS W.1 W.2)
    (hF : F.IsQuasicoherentOnSite) (h : IsZero ((modulePushforward B S hS g).obj F)) :
    IsZero F := by
  have hrep := relativelyRepresentable_of_isAffineHom B S hS g hg
  have hcart := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS W.1 W.2 F hF
  have h' : IsZero ((smallBaseChangeModulePushforward.{u, u} B S hS g hrep).obj F) :=
    h.of_iso ((modulePushforwardChartIso B S hS g hrep).app F).symm
  have hsBC : ∀ (V : SmallEtale B S hS Y.1)
      (x : F.val.obj (op ((smallBaseChange B S hS g hrep).obj V))), x = 0 := fun V x =>
    (ModuleCat.subsingleton_of_isZero
      ((SheafOfModules.isZero_iff_forall_isZero_obj _ _).mp h' V)).elim x 0
  have hW' : ∀ (W' : SmallEtale B S hS W.1), HasAffineChartDiagram B S hS g W' →
      ∀ x : F.val.obj (op W'), x = 0 := by
    rintro W' ⟨hW'aff, V, q, hq, hVaff⟩ x
    let k : W' ⟶ (smallBaseChange B S hS g hrep).obj V :=
      ObjectProperty.homMk (CostructuredArrow.homMk (hrep.lift W'.1.hom q hq.symm)
        (hrep.lift_fst _ _ _))
    obtain ⟨y, rfl⟩ :=
      (hcart _ _ (isAffine_smallBaseChange_obj B S hS g hrep hg V hVaff) hW'aff k).2 x
    have : Subsingleton (F.val.obj (op ((smallBaseChange B S hS g hrep).obj V))) :=
      ⟨fun a b => (hsBC V a).trans (hsBC V b).symm⟩
    rw [Subsingleton.elim y 0, map_zero]
  have key : ∀ {A A' A'' : (smallEtaleRingedSite B S hS W.1 W.2).C} (a : A' ⟶ A) (b : A'' ⟶ A')
      (y : F.val.presheaf.obj (op A)),
      F.val.presheaf.map (b ≫ a).op y = F.val.presheaf.map b.op (F.val.presheaf.map a.op y) := by
    intro A A' A'' a b y
    rw [op_comp, F.val.presheaf.map_comp, ConcreteCategory.comp_apply]
  refine isZero_of_sections_eq_zero B S hS W.1 W.2 F fun U x => ?_
  let R : Sieve U :=
    { arrows := fun _ f => F.val.presheaf.map f.op x = 0
      downward_closed := by
        intro V V' f hf g
        exact (key f g x).trans ((congrArg (F.val.presheaf.map g.op) hf).trans (map_zero _)) }
  exact F.isSheaf.isSeparated U R
    (mem_topology_of_hasAffineChartDiagram B S hS g U R fun W' _ hdiag => hW' W' hdiag _) x 0
    fun _ _ hf => hf.trans (map_zero _).symm

section RightDerived

variable (g : W ⟶ Y)
  (RF : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
    DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
  (α : (modulePushforward B S hS g).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor α
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))]

include α in
/-- Along an affine `g`, the right derived direct image of `τ_{≥ i}` induces an isomorphism on
`Hⁱ` of an object of `D_QCoh`. -/
private theorem isIso_homologyMap_rightDerived_truncGEπ_of_isAffineHom
    (hg : IsAffineHom B S hS g.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hqc : ∀ q : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS W.1 W.2) q).obj E).IsQuasicoherentOnSite) (i : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor _ i).map
      (RF.map ((DerivedCategory.TStructure.t.truncGEπ i).app E))) := by
  let PW := SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O))
  let _ := Functor.IsRightDerivedFunctor.commShift RF α
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)) ℤ
  have : RF.IsTriangulated :=
    Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor
      (modulePushforward B S hS g) RF α
  let T := RF.mapTriangle.obj ((DerivedCategory.TStructure.t.triangleLEGE
    (i - 1) i (by omega)).obj E)
  have hT : T ∈ distTriang _ := RF.map_distinguished _
    (DerivedCategory.TStructure.t.triangleLEGE_distinguished (i - 1) i (by omega) E)
  have hl : T.obj₁.IsLE (i - 1) :=
    isLE_rightDerived_modulePushforward_of_isAffineHom B S hS g RF α hg _
      (fun q => Stacks.SmallDerivedCategory.prop_homologyFunctor_truncLE_obj PW E hqc
        (i - 1) q) (i - 1) inferInstance
  have : Mono ((DerivedCategory.homologyFunctor _ i).map T.mor₂) :=
    ((DerivedCategory.homologyFunctor _ 0).homologySequence_mono_shift_map_mor₂_iff
      T hT i).2 ((T.obj₁.isZero_of_isLE (i - 1) i (by omega)).eq_of_src _ _)
  have : Epi ((DerivedCategory.homologyFunctor _ i).map T.mor₂) :=
    ((DerivedCategory.homologyFunctor _ 0).homologySequence_epi_shift_map_mor₂_iff
      T hT i (i + 1) rfl).2 ((T.obj₁.isZero_of_isLE (i - 1) (i + 1) (by omega)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor _ i).map T.mor₂)

include α in
/-- The right derived direct image of `τ_{≤ i}` induces an isomorphism on `Hⁱ`. -/
private theorem isIso_homologyMap_rightDerived_truncLEι
    (E₁ : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) (i : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor _ i).map
      (RF.map ((DerivedCategory.TStructure.t.truncLEι i).app E₁))) := by
  let _ := Functor.IsRightDerivedFunctor.commShift RF α
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)) ℤ
  have : RF.IsTriangulated :=
    Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor
      (modulePushforward B S hS g) RF α
  let T := RF.mapTriangle.obj ((DerivedCategory.TStructure.t.triangleLEGE i (i + 1) rfl).obj E₁)
  have hT : T ∈ distTriang _ := RF.map_distinguished _
    (DerivedCategory.TStructure.t.triangleLEGE_distinguished i (i + 1) rfl E₁)
  have hg' : T.obj₃.IsGE (i + 1) :=
    Stacks.SmallDerivedCategory.isGE_obj_of_isGE (modulePushforward B S hS g) RF α
      (fun I hI =>
        isIso_app_of_isKInjective_modulePushforward B S hS g DerivedCategory.Qh RF α I hI)
      ((DerivedCategory.TStructure.t.truncGE (i + 1)).obj E₁) (i + 1) inferInstance
  have : Epi ((DerivedCategory.homologyFunctor _ i).map T.mor₁) :=
    ((DerivedCategory.homologyFunctor _ 0).homologySequence_epi_shift_map_mor₁_iff
      T hT i).2 ((T.obj₃.isZero_of_isGE (i + 1) i (by omega)).eq_of_tgt _ _)
  have : Mono ((DerivedCategory.homologyFunctor _ i).map T.mor₁) :=
    ((DerivedCategory.homologyFunctor _ 0).homologySequence_mono_shift_map_mor₁_iff
      T hT (i - 1) i (by omega)).2
        ((T.obj₃.isZero_of_isGE (i + 1) (i - 1) (by omega)).eq_of_src _ _)
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor _ i).map T.mor₁)

include α in
/-- **The derived direct image along an affine morphism is conservative on `D_QCoh`.** An object
`E` of `D(𝒪_W)` with quasi-coherent cohomology sheaves and `Rg_*E = 0` is zero, for every right
derived functor `Rg_*` of the direct image along an affine `g`. -/
theorem isZero_of_isZero_rightDerived_modulePushforward_of_isAffineHom
    (hg : IsAffineHom B S hS g.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hqc : ∀ q : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS W.1 W.2) q).obj E).IsQuasicoherentOnSite)
    (hE : IsZero (RF.obj E)) : IsZero E := by
  let PW := SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O))
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  intro i
  have hπ := isIso_homologyMap_rightDerived_truncGEπ_of_isAffineHom B S hS g RF α hg E hqc i
  let E₁ := (DerivedCategory.TStructure.t.truncGE i).obj E
  have hι := isIso_homologyMap_rightDerived_truncLEι B S hS g RF α E₁ i
  let E₂ := (DerivedCategory.TStructure.t.truncLE i).obj E₁
  have _ : E₂.IsGE i := inferInstanceAs
    (((DerivedCategory.TStructure.t.truncLE i).obj E₁).IsGE i)
  have _ : E₂.IsLE i := inferInstanceAs
    (((DerivedCategory.TStructure.t.truncLE i).obj E₁).IsLE i)
  obtain ⟨M, ⟨e⟩⟩ := E₂.exists_iso_singleFunctor_obj_of_isGE_of_isLE i
  have eM : M ≅ (DerivedCategory.homologyFunctor _ i).obj E :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ i).app M).symm ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso e.symm ≪≫
      (@asIso _ _ _ _ ((DerivedCategory.homologyFunctor _ i).map
        ((DerivedCategory.TStructure.t.truncLEι i).app E₁))
        (Stacks.TruncationLevel.isIso_homologyMap_truncLEι_app i i le_rfl E₁)) ≪≫
      (@asIso _ _ _ _ ((DerivedCategory.homologyFunctor _ i).map
        ((DerivedCategory.TStructure.t.truncGEπ i).app E))
        (DerivedCategory.isIso_homologyMap_truncGEπ_app i i le_rfl E)).symm
  refine IsZero.of_iso (isZero_of_isZero_modulePushforward_of_isAffineHom B S hS g hg M
    (PW.prop_of_iso eM.symm (hqc i)) ?_) eM.symm
  have hzE₂ : IsZero ((DerivedCategory.homologyFunctor _ i).obj (RF.obj E₂)) :=
    (((DerivedCategory.homologyFunctor _ i).map_isZero hE).of_iso
      (asIso ((DerivedCategory.homologyFunctor _ i).map
        (RF.map ((DerivedCategory.TStructure.t.truncGEπ i).app E)))).symm).of_iso
      (asIso ((DerivedCategory.homologyFunctor _ i).map
        (RF.map ((DerivedCategory.TStructure.t.truncLEι i).app E₁))))
  exact hzE₂.of_iso (((modulePushforward B S hS g).rightDerivedZeroIsoSelf.app M).symm ≪≫
    (Stacks.DerivedFunctor.homologyTotalRightDerivedSingleShiftIso
      (modulePushforward B S hS g) RF α
      (exists_quasiIso_isKInjective_modules B S hS W.1 W.2) M i i 0 (by simp)).symm ≪≫
    ((DerivedCategory.homologyFunctor _ i).mapIso (RF.mapIso e)).symm)

end RightDerived

/-- **The canonical `Rg_*` along an affine morphism is conservative on `D_QCoh`.** -/
theorem isZero_of_isZero_derivedModulePushforward_of_isAffineHom (g : W ⟶ Y)
    (hg : IsAffineHom B S hS g.hom) (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hE : QcohDerived B S hS W E) (h : IsZero ((derivedModulePushforward B S hS g).obj E)) :
    IsZero E :=
  isZero_of_isZero_rightDerived_modulePushforward_of_isAffineHom B S hS g
    (derivedModulePushforward B S hS g) (derivedModulePushforwardUnit B S hS g) hg E
    (fun q => hE q) h

end AlgebraicGeometry.Space

end
