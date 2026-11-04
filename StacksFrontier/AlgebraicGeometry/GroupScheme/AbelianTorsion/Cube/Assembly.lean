module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianTorsion.Cube.OpenSubgroup
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianTorsion.Cube.AssemblyStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Descent.TrivialOverBaseCover

/-!
# The cube module is trivial, from its triviality near the unit

Let `k` be an algebraically closed field, `A` an abelian variety over `k`, `L` an invertible
`𝒪_A`-module and `N` the cube module of `L` on `P = W × Z` with `W = A × A` (the first two
factors) and `Z = A` (the third factor). Assume the openness statement
`Stacks.Groupoids.OpenAtUnitStatement`: an invertible module on `P` trivial on the three faces is
trivial over `W × U` for an open neighbourhood `U` of the unit of `Z`. Under this hypothesis `N`
is trivial, and the cube relation ([Stacks, Tag 0BFE](https://stacks.math.columbia.edu/tag/0BFE))
holds for `L`.

## Main results

* `Stacks.Groupoids.cubeClass_eq_zero_of_isTrivial_pullback_fst`: the cube class vanishes on any
  triple whose third member lands in an open over which the cube module is trivial.
* `Stacks.Groupoids.isTrivial_cubeModule_of_openAtUnit`: the cube module is trivial, given
  `Stacks.Groupoids.OpenAtUnitStatement` (argument `hopen`).
* `Stacks.Groupoids.cubeClass_eq_zero_of_openAtUnit`: the cube class vanishes identically, given
  `Stacks.Groupoids.OpenAtUnitStatement`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules (schemeTensor picardClass pullbackPicardClass)
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Groupoids

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A]
  (L : SheafOfModules.{u} (structureSheafRing A.left.toRingedSpace))
  (hL : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf L)

section

variable (N₁₂ N₁₃ N₂₃ : SheafOfModules.{u} (structureSheafRing (cubeObj A).left.toRingedSpace))
    (h₁₂ : Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf N₁₂)
    (h₁₃ : Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf N₁₃)
    (h₂₃ : Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf N₂₃)
    (t₁₂ : Stacks.SheafOfModules.IsTrivial (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf (schemeTensor (cubeObj A).left
        (pullbackOver (cubeProj₁ A * cubeProj₂ A) L) N₁₂))
    (t₁₃ : Stacks.SheafOfModules.IsTrivial (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf (schemeTensor (cubeObj A).left
        (pullbackOver (cubeProj₁ A * cubeProj₃ A) L) N₁₃))
    (t₂₃ : Stacks.SheafOfModules.IsTrivial (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf (schemeTensor (cubeObj A).left
        (pullbackOver (cubeProj₂ A * cubeProj₃ A) L) N₂₃))

include h₁₂ h₁₃ h₂₃ t₁₂ t₁₃ t₂₃

/-- **The cube class vanishes over an open of triviality.** If the cube module of `L` is trivial
over `W × U` and `t : Y ⟶ A` factors through `U`, then `D_L(f, g, t) = 0` for all `f, g`. -/
theorem cubeClass_eq_zero_of_isTrivial_pullback_fst (U : A.left.Opens)
    (hU : Stacks.SheafOfModules.IsTrivial (pullback (cubeProj₃ A).left U.ι).presheaf
      (pullback (cubeProj₃ A).left U.ι).ringCatIsSheaf
      ((modulePullback (pullback.fst (cubeProj₃ A).left U.ι).toLRSHom.toShHom).obj
        (cubeModule A L N₁₂ N₁₃ N₂₃)))
    {Y : Over (Spec (.of k))} (f g t : Y ⟶ A) (q : Y.left ⟶ U.toScheme)
    (hq : q ≫ U.ι = t.left) :
    cubeClass L hL f g t = 0 := by
  have hφ := pullbackPicardClass_cubeModule_eq_cubeClass L hL N₁₂ N₁₃ N₂₃ h₁₂ h₁₃ h₂₃
    t₁₂ t₁₃ t₂₃ (lift (lift f g) t)
  simp only [lift_lift_cubeProj₁, lift_lift_cubeProj₂, lift_lift_cubeProj₃] at hφ
  rw [← hφ]
  have hw : (lift (lift f g) t).left ≫ (cubeProj₃ A).left = q ≫ U.ι := by
    rw [hq, ← Over.comp_left, lift_lift_cubeProj₃]
  let m : Y.left ⟶ pullback (cubeProj₃ A).left U.ι :=
    pullback.lift (lift (lift f g) t).left q hw
  have hm : (lift (lift f g) t).left = m ≫ pullback.fst (cubeProj₃ A).left U.ι :=
    (pullback.lift_fst _ _ _).symm
  have hN := isInvertible_cubeModule A L hL N₁₂ N₁₃ N₂₃ h₁₂ h₁₃ h₂₃
  rw [hm, Stacks.SheafOfModules.pullbackPicardClass_comp m
    (pullback.fst (cubeProj₃ A).left U.ι) _ hN
    (have := hN; Stacks.RingedSpace.modulePullback_isInvertible _ _),
    Stacks.SheafOfModules.pullbackPicardClass_eq_zero_iff]
  exact ⟨(modulePullback m.toLRSHom.toShHom).mapIso hU.some ≪≫
    modulePullbackObjUnitIso m.toLRSHom.toShHom⟩

/-- **The cube class vanishes at the `k`-points of an open of triviality.** -/
theorem isCubeTrivialAt_of_mem (U : A.left.Opens)
    (hU : Stacks.SheafOfModules.IsTrivial (pullback (cubeProj₃ A).left U.ι).presheaf
      (pullback (cubeProj₃ A).left U.ι).ringCatIsSheaf
      ((modulePullback (pullback.fst (cubeProj₃ A).left U.ι).toLRSHom.toShHom).obj
        (cubeModule A L N₁₂ N₁₃ N₂₃)))
    (b : 𝟙_ (Over (Spec (.of k))) ⟶ A) (hb : b.left (IsLocalRing.closedPoint k) ∈ U) :
    IsCubeTrivialAt L hL b := by
  intro B f g
  have hr : Set.range b.left.base ⊆ Set.range U.ι.base := by
    rintro _ ⟨x, rfl⟩
    have hx : x = IsLocalRing.closedPoint k := Subsingleton.elim (α := PrimeSpectrum k) x _
    rw [Scheme.Opens.range_ι, hx]
    exact hb
  refine cubeClass_eq_zero_of_isTrivial_pullback_fst L hL N₁₂ N₁₃ N₂₃ h₁₂ h₁₃ h₂₃ t₁₂ t₁₃ t₂₃
    U hU f g (toUnit B ≫ b) (B.hom ≫ IsOpenImmersion.lift U.ι b.left hr) ?_
  rw [Category.assoc, IsOpenImmersion.lift_fac, Over.comp_left]
  rfl

end

/-- Openness at the unit: an invertible module on `A × A × A` trivial on the three faces is
trivial over `A × A × U` for an open neighbourhood `U` of the unit of the third factor. -/
abbrev OpenAtUnitStatement (A : Over (Spec (.of k))) [GrpObj A] : Prop :=
  ∀ (N : SheafOfModules.{u} (structureSheafRing (cubeObj A).left.toRingedSpace)),
    Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf
        (cubeObj A).left.ringCatIsSheaf N →
      Stacks.SheafOfModules.IsTrivial (A ⊗ A).left.presheaf (A ⊗ A).left.ringCatIsSheaf
        (pullbackOver (cubeFace₁ A) N) →
      Stacks.SheafOfModules.IsTrivial (A ⊗ A).left.presheaf (A ⊗ A).left.ringCatIsSheaf
        (pullbackOver (cubeFace₂ A) N) →
      Stacks.SheafOfModules.IsTrivial (A ⊗ A).left.presheaf (A ⊗ A).left.ringCatIsSheaf
        (pullbackOver (cubeFace₃ A) N) →
      ∃ U : A.left.Opens, η[A].left (IsLocalRing.closedPoint k) ∈ U ∧
        Stacks.SheafOfModules.IsTrivial (pullback (cubeProj₃ A).left U.ι).presheaf
          (pullback (cubeProj₃ A).left U.ι).ringCatIsSheaf
          ((modulePullback (pullback.fst (cubeProj₃ A).left U.ι).toLRSHom.toShHom).obj N)

include hL in
/-- Given `OpenAtUnitStatement A`, the cube module of `L` is trivial over `A × A × U` for an
open neighbourhood `U` of the unit of the third factor. -/
theorem exists_isTrivial_cubeModule_of_openAtUnit (hopen : OpenAtUnitStatement A)
    (N₁₂ N₁₃ N₂₃ : SheafOfModules.{u} (structureSheafRing (cubeObj A).left.toRingedSpace))
    (h₁₂ : Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf N₁₂)
    (h₁₃ : Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf N₁₃)
    (h₂₃ : Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf N₂₃)
    (t₁₂ : Stacks.SheafOfModules.IsTrivial (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf (schemeTensor (cubeObj A).left
        (pullbackOver (cubeProj₁ A * cubeProj₂ A) L) N₁₂))
    (t₁₃ : Stacks.SheafOfModules.IsTrivial (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf (schemeTensor (cubeObj A).left
        (pullbackOver (cubeProj₁ A * cubeProj₃ A) L) N₁₃))
    (t₂₃ : Stacks.SheafOfModules.IsTrivial (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf (schemeTensor (cubeObj A).left
        (pullbackOver (cubeProj₂ A * cubeProj₃ A) L) N₂₃)) :
    ∃ U : A.left.Opens, η[A].left (IsLocalRing.closedPoint k) ∈ U ∧
      Stacks.SheafOfModules.IsTrivial (pullback (cubeProj₃ A).left U.ι).presheaf
        (pullback (cubeProj₃ A).left U.ι).ringCatIsSheaf
        ((modulePullback (pullback.fst (cubeProj₃ A).left U.ι).toLRSHom.toShHom).obj
          (cubeModule A L N₁₂ N₁₃ N₂₃)) :=
  hopen _ (isInvertible_cubeModule A L hL N₁₂ N₁₃ N₂₃ h₁₂ h₁₃ h₂₃)
    (isTrivial_cubeModule_cubeFace₁ A L hL N₁₂ N₁₃ N₂₃ h₁₂ h₁₃ h₂₃ t₁₂ t₁₃ t₂₃)
    (isTrivial_cubeModule_cubeFace₂ A L hL N₁₂ N₁₃ N₂₃ h₁₂ h₁₃ h₂₃ t₁₂ t₁₃ t₂₃)
    (isTrivial_cubeModule_cubeFace₃ A L hL N₁₂ N₁₃ N₂₃ h₁₂ h₁₃ h₂₃ t₁₂ t₁₃ t₂₃)

/-- Every invertible `L` has invertible modules `N` making the three pairwise tensors trivial. -/
private theorem exists_cube_data
    (M : SheafOfModules.{u} (structureSheafRing A.left.toRingedSpace))
    (hM : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf M) :
    ∃ N₁₂ N₁₃ N₂₃ : SheafOfModules.{u} (structureSheafRing (cubeObj A).left.toRingedSpace),
      Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf
        (cubeObj A).left.ringCatIsSheaf N₁₂ ∧
      Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf
        (cubeObj A).left.ringCatIsSheaf N₁₃ ∧
      Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf
        (cubeObj A).left.ringCatIsSheaf N₂₃ ∧
      Stacks.SheafOfModules.IsTrivial (cubeObj A).left.presheaf
        (cubeObj A).left.ringCatIsSheaf (schemeTensor (cubeObj A).left
          (pullbackOver (cubeProj₁ A * cubeProj₂ A) M) N₁₂) ∧
      Stacks.SheafOfModules.IsTrivial (cubeObj A).left.presheaf
        (cubeObj A).left.ringCatIsSheaf (schemeTensor (cubeObj A).left
          (pullbackOver (cubeProj₁ A * cubeProj₃ A) M) N₁₃) ∧
      Stacks.SheafOfModules.IsTrivial (cubeObj A).left.presheaf
        (cubeObj A).left.ringCatIsSheaf (schemeTensor (cubeObj A).left
          (pullbackOver (cubeProj₂ A * cubeProj₃ A) M) N₂₃) := by
  obtain ⟨N₁₂, h₁₂, t₁₂⟩ := Stacks.SheafOfModules.exists_invertible_isTrivial_tensorSheaf
    (pullbackOver (cubeProj₁ A * cubeProj₂ A) M)
    (isInvertible_pullbackOver (cubeProj₁ A * cubeProj₂ A) M hM)
  obtain ⟨N₁₃, h₁₃, t₁₃⟩ := Stacks.SheafOfModules.exists_invertible_isTrivial_tensorSheaf
    (pullbackOver (cubeProj₁ A * cubeProj₃ A) M)
    (isInvertible_pullbackOver (cubeProj₁ A * cubeProj₃ A) M hM)
  obtain ⟨N₂₃, h₂₃, t₂₃⟩ := Stacks.SheafOfModules.exists_invertible_isTrivial_tensorSheaf
    (pullbackOver (cubeProj₂ A * cubeProj₃ A) M)
    (isInvertible_pullbackOver (cubeProj₂ A * cubeProj₃ A) M hM)
  exact ⟨N₁₂, N₁₃, N₂₃, h₁₂, h₁₃, h₂₃, t₁₂, t₁₃, t₂₃⟩

variable [IsAlgClosed k]

/-- **The cube class of `L` vanishes at every `k`-point**, given `OpenAtUnitStatement A`
(`hopen`). -/
theorem isCubeTrivialAt_of_openAtUnit [AlgebraicGeometry.IsAbelianVariety k A]
    (hopen : OpenAtUnitStatement A) (a : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    IsCubeTrivialAt L hL a := by
  let : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
  obtain ⟨N₁₂, N₁₃, N₂₃, h₁₂, h₁₃, h₂₃, t₁₂, t₁₃,
      t₂₃⟩ := exists_cube_data L hL
  obtain ⟨U, heU, hU⟩ := exists_isTrivial_cubeModule_of_openAtUnit L hL hopen N₁₂ N₁₃ N₂₃
    h₁₂ h₁₃ h₂₃ t₁₂ t₁₃ t₂₃
  exact forall_of_mul_of_isOpen (IsCubeTrivialAt L hL) (fun _ _ ha hb => ha.mul L hL hb) U heU
    (isCubeTrivialAt_of_mem L hL N₁₂ N₁₃ N₂₃ h₁₂ h₁₃ h₂₃ t₁₂ t₁₃ t₂₃ U hU) a

include hL in
/-- **The cube module of `L` is trivial**, given `OpenAtUnitStatement A` (`hopen`). -/
theorem isTrivial_cubeModule_of_openAtUnit [AlgebraicGeometry.IsAbelianVariety k A]
    (hopen : OpenAtUnitStatement A)
    (N₁₂ N₁₃ N₂₃ : SheafOfModules.{u} (structureSheafRing (cubeObj A).left.toRingedSpace))
    (h₁₂ : Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf N₁₂)
    (h₁₃ : Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf N₁₃)
    (h₂₃ : Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf N₂₃)
    (t₁₂ : Stacks.SheafOfModules.IsTrivial (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf (schemeTensor (cubeObj A).left
        (pullbackOver (cubeProj₁ A * cubeProj₂ A) L) N₁₂))
    (t₁₃ : Stacks.SheafOfModules.IsTrivial (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf (schemeTensor (cubeObj A).left
        (pullbackOver (cubeProj₁ A * cubeProj₃ A) L) N₁₃))
    (t₂₃ : Stacks.SheafOfModules.IsTrivial (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf (schemeTensor (cubeObj A).left
        (pullbackOver (cubeProj₂ A * cubeProj₃ A) L) N₂₃)) :
    Stacks.SheafOfModules.IsTrivial (cubeObj A).left.presheaf (cubeObj A).left.ringCatIsSheaf
      (cubeModule A L N₁₂ N₁₃ N₂₃) := by
  let : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
  have hN := isInvertible_cubeModule A L hL N₁₂ N₁₃ N₂₃ h₁₂ h₁₃ h₂₃
  have hnear : ∀ a : 𝟙_ (Over (Spec (.of k))) ⟶ A, ∃ V : A.left.Opens,
      a.left (IsLocalRing.closedPoint k) ∈ V ∧
      Stacks.SheafOfModules.IsTrivial (pullback (cubeProj₃ A).left V.ι).presheaf
        (pullback (cubeProj₃ A).left V.ι).ringCatIsSheaf
        ((modulePullback (pullback.fst (cubeProj₃ A).left V.ι).toLRSHom.toShHom).obj
          (cubeModule A L N₁₂ N₁₃ N₂₃)) := by
    intro a
    let L' := pullbackOver (translate a) L
    have hL' : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf L' :=
      isInvertible_pullbackOver (translate a) L hL
    obtain ⟨N'₁₂, N'₁₃, N'₂₃, h'₁₂, h'₁₃, h'₂₃, t'₁₂, t'₁₃,
        t'₂₃⟩ := exists_cube_data L' hL'
    obtain ⟨U', heU', hU'⟩ := exists_isTrivial_cubeModule_of_openAtUnit L' hL' hopen
      N'₁₂ N'₁₃ N'₂₃ h'₁₂ h'₁₃ h'₂₃ t'₁₂ t'₁₃ t'₂₃
    let s := (translate a⁻¹).left
    have has : a ≫ translate a⁻¹ = η[A] := by
      rw [comp_translate, Subsingleton.elim (toUnit _) (𝟙 _), Category.id_comp, mul_inv_cancel,
        Hom.one_def, Subsingleton.elim (toUnit _) (𝟙 _), Category.id_comp]
    refine ⟨s ⁻¹ᵁ U', ?_, ?_⟩
    · show s (a.left (IsLocalRing.closedPoint k)) ∈ U'
      have : s (a.left (IsLocalRing.closedPoint k)) =
          η[A].left (IsLocalRing.closedPoint k) := by
        rw [← has]; rfl
      rw [this]
      exact heU'
    · let V := s ⁻¹ᵁ U'
      let jV := pullback.fst (cubeProj₃ A).left V.ι
      let Y : Over (Spec (.of k)) := Over.mk (jV ≫ (cubeObj A).hom)
      let ψ : Y ⟶ cubeObj A := Over.homMk jV rfl
      rw [← Stacks.SheafOfModules.pullbackPicardClass_eq_zero_iff jV _ hN]
      show pullbackPicardClass ψ.left _ hN = 0
      rw [pullbackPicardClass_cubeModule_eq_cubeClass L hL N₁₂ N₁₃ N₂₃ h₁₂ h₁₃ h₂₃
        t₁₂ t₁₃ t₂₃ ψ]
      have h3 : ψ ≫ cubeProj₃ A =
          (ψ ≫ cubeProj₃ A ≫ translate a⁻¹) * (toUnit Y ≫ a) := by
        rw [← Category.assoc, comp_translate, mul_assoc, ← MonObj.comp_mul, inv_mul_cancel,
          Hom.one_def, ← Category.assoc, Subsingleton.elim (toUnit Y ≫ toUnit _) (toUnit Y),
          ← Hom.one_def, mul_one]
      rw [h3, ← cubeClass_translate L hL (isCubeTrivialAt_of_openAtUnit L hL hopen a)]
      refine cubeClass_eq_zero_of_isTrivial_pullback_fst L' hL' N'₁₂ N'₁₃ N'₂₃ h'₁₂ h'₁₃ h'₂₃
        t'₁₂ t'₁₃ t'₂₃ U' hU' _ _ _
        (pullback.snd (cubeProj₃ A).left V.ι ≫ s.resLE U' V le_rfl) ?_
      rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, ← pullback.condition]
      rfl
  choose V hV hVt using hnear
  have htop := eq_top_of_forall_comp_mem (⨆ a, V a) (fun a => Opens.mem_iSup.2 ⟨a, hV a⟩)
  let δ : A ⟶ cubeObj A := lift (lift 1 1) (𝟙 A)
  have hδ : δ.left ≫ (cubeProj₃ A).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_lift_cubeProj₃, Over.id_left]
  have hδL : Stacks.SheafOfModules.IsTrivial A.left.presheaf A.left.ringCatIsSheaf
      ((modulePullback δ.left.toLRSHom.toShHom).obj (cubeModule A L N₁₂ N₁₃ N₂₃)) := by
    rw [← Stacks.SheafOfModules.pullbackPicardClass_eq_zero_iff δ.left _ hN,
      pullbackPicardClass_cubeModule_eq_cubeClass L hL N₁₂ N₁₃ N₂₃ h₁₂ h₁₃ h₂₃
        t₁₂ t₁₃ t₂₃ δ]
    simp only [δ, lift_lift_cubeProj₁, lift_lift_cubeProj₂, lift_lift_cubeProj₃, cubeClass_def,
      one_mul, pullbackPicardClass_one L hL]
    abel
  have := hN
  refine AlgebraicGeometry.SheafOfModules.isTrivial_of_isTrivial_modulePullback_fst_ι
    (cubeProj₃ A).left (isIso_structureSheafHom_cubeProj₃ A) δ.left hδ _ hδL fun z => ?_
  have hz : z ∈ ⨆ a, V a := htop ▸ trivial
  obtain ⟨a, ha⟩ := Opens.mem_iSup.1 hz
  exact ⟨V a, ha, hVt a⟩

/-- **The cube class vanishes identically**, given `OpenAtUnitStatement A` (`hopen`):
`D_L(f, g, t) = 0` in `Pic(B)` for all `f, g, t : B ⟶ A`. -/
theorem cubeClass_eq_zero_of_openAtUnit [AlgebraicGeometry.IsAbelianVariety k A]
    (hopen : OpenAtUnitStatement A) {B : Over (Spec (.of k))} (f g t : B ⟶ A) :
    cubeClass L hL f g t = 0 := by
  obtain ⟨N₁₂, N₁₃, N₂₃, h₁₂, h₁₃, h₂₃, t₁₂, t₁₃,
      t₂₃⟩ := exists_cube_data L hL
  have htriv := isTrivial_cubeModule_of_openAtUnit L hL hopen N₁₂ N₁₃ N₂₃ h₁₂ h₁₃ h₂₃
    t₁₂ t₁₃ t₂₃
  have hN := isInvertible_cubeModule A L hL N₁₂ N₁₃ N₂₃ h₁₂ h₁₃ h₂₃
  have h0 := pullbackPicardClass_cubeModule_eq_cubeClass L hL N₁₂ N₁₃ N₂₃ h₁₂ h₁₃ h₂₃
    t₁₂ t₁₃ t₂₃ (𝟙 (cubeObj A))
  rw [Over.id_left, Stacks.SheafOfModules.pullbackPicardClass_id,
    (Stacks.SheafOfModules.picardClass_eq_zero_iff _ _ _ hN).mpr htriv] at h0
  simpa only [← Category.assoc, Category.comp_id, lift_lift_cubeProj₁, lift_lift_cubeProj₂,
    lift_lift_cubeProj₃] using cubeClass_comp_eq_zero L hL h0.symm (lift (lift f g) t)

end Stacks.Groupoids

end
