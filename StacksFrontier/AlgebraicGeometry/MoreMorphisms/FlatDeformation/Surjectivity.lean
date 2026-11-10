module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FlatDeformation.Realization
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FirstOrderThickeningConormalConverse

/-!
# Every solution of the deformation problem comes from a flat deformation
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite
open Stacks.Sheaves.RingedSpaceDifferentials (sheafAdjunction)
open Deformation.ToposThickening.RingedToposExtensionProblem

universe u

namespace Stacks.Thickenings.FlatDeformation

variable {X S S' : Scheme.{u}} {t : S ⟶ S'} {f : X ⟶ S} [IsClosedImmersion t]
  {hst : t.ker ^ 2 = ⊥}
  {c : ideal t f hst ⟶ (SheafOfModules.restrictScalars
      ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).map
        (structureHom f).fSharpInverseImage)).obj (conormalModule t f)}
  (P : (problem t f hst c).CompatibleFirstOrderThickening)

/-- The scheme realizing a solution, by [Stacks Project, Tag 05YV]. -/
abbrev real : Realization (toSquareZeroExtension P) :=
  Stacks.Thickenings.realization (toSquareZeroExtension P)

/-- The immersion of the realization of a solution is a closed immersion. -/
instance : IsClosedImmersion (real P).immersion := (real P).immersion_isFirstOrder.1

/-- The ideal of `X` in the realization of a solution has square zero. -/
theorem real_ker_sq : (real P).immersion.ker ^ 2 = ⊥ := (real P).immersion_isFirstOrder.2

/-- The immersion of the realization of a solution is a homeomorphism on underlying spaces. -/
instance : IsIso (real P).immersion.base := isIso_base_of_firstOrder _ (real_ker_sq P)

/-- The comparison of the solution with the transported structure sheaf of its realization, as a
morphism of sheafed spaces. -/
def compareHom :
    thickenedSpace X P.extension ⟶ thickenedSpace X (transported (real P).immersion) :=
  (real P).sheafedIso.inv ≫ (ambientIso (real P).immersion).hom

/-- `compareHom P` is compatible with the reductions to `X`. -/
theorem thickenedHom_reduction_comp_compareHom :
    thickenedHom P.reduction ≫ compareHom P =
      thickenedHom (transportedReduction (real P).immersion) := by
  have h := (real P).inclusion_eq
  change _ = thickenedHom P.reduction at h
  refine (congrArg (· ≫ compareHom P) h.symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (Iso.hom_inv_id_assoc (real P).sheafedIso _)).trans ?_
  exact ambientIso_inclusion _

/-- The underlying map of `compareHom P` is the identity. -/
theorem compareHom_base : (compareHom P).hom.base = 𝟙 (X : TopCat) :=
  congrArg (fun Φ => Φ.hom.base) (thickenedHom_reduction_comp_compareHom P)

/-- The inverse comparison. -/
def compareInvHom :
    thickenedSpace X (transported (real P).immersion) ⟶ thickenedSpace X P.extension :=
  (ambientIso (real P).immersion).inv ≫ (real P).sheafedIso.hom

/-- `compareInvHom P` is a left inverse of `compareHom P`. -/
theorem compareHom_comp_compareInvHom : compareHom P ≫ compareInvHom P = 𝟙 _ :=
  ((real P).sheafedIso.symm ≪≫ ambientIso (real P).immersion).hom_inv_id

/-- `compareInvHom P` is a right inverse of `compareHom P`. -/
theorem compareInvHom_comp_compareHom : compareInvHom P ≫ compareHom P = 𝟙 _ :=
  ((real P).sheafedIso.symm ≪≫ ambientIso (real P).immersion).inv_hom_id

/-- The underlying map of `compareInvHom P` is the identity. -/
theorem compareInvHom_base : (compareInvHom P).hom.base = 𝟙 (X : TopCat) := by
  have h := congrArg (fun Φ => Φ.hom.base) (compareHom_comp_compareInvHom P)
  change (compareHom P).hom.base ≫ (compareInvHom P).hom.base = 𝟙 _ at h
  exact (Category.id_comp _).symm.trans ((congrArg (· ≫ (compareInvHom P).hom.base)
    (compareHom_base P).symm).trans h)

/-- **The structure sheaf of the realization of a solution is the solution's own sheaf.** -/
def compare : transported (real P).immersion ≅ P.extension where
  hom := sheafOfThickened (compareHom P) (compareHom_base P)
  inv := sheafOfThickened (compareInvHom P) (compareInvHom_base P)
  hom_inv_id := thickenedHom_injective ((thickenedHom_comp _ _).symm.trans
    ((congrArg₂ (· ≫ ·) (thickenedHom_sheafOfThickened _ _)
      (thickenedHom_sheafOfThickened _ _)).trans (compareInvHom_comp_compareHom P)))
  inv_hom_id := thickenedHom_injective ((thickenedHom_comp _ _).symm.trans
    ((congrArg₂ (· ≫ ·) (thickenedHom_sheafOfThickened _ _)
      (thickenedHom_sheafOfThickened _ _)).trans (compareHom_comp_compareInvHom P)))

/-- `compare P` is compatible with the reductions to `𝒪_X`. -/
theorem compare_hom_comp_reduction :
    (compare P).hom ≫ P.reduction = transportedReduction (real P).immersion := by
  refine thickenedHom_injective ((thickenedHom_comp _ _).symm.trans ?_)
  exact (congrArg (thickenedHom P.reduction ≫ ·)
    (thickenedHom_sheafOfThickened (compareHom P) (compareHom_base P))).trans
    (thickenedHom_reduction_comp_compareHom P)

/-- `compare P` is compatible with the comorphisms from `𝒪_{S'}`. -/
theorem transportedBase_comp_compare :
    transportedBase (real P).immersion (real P).over_base ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} (f.base ≫ t.base)).map (compare P).hom =
      baseComorphism P := by
  refine thickenedToBase_injective (t := t) (f := f) ?_
  refine (thickenedHom_comp_thickenedToBase _ _).symm.trans ?_
  refine (congrArg (· ≫ _) (thickenedHom_sheafOfThickened (compareHom P)
    (compareHom_base P))).trans ?_
  refine (congrArg (compareHom P ≫ ·) (ambientIso_toBase _ (real P).over_base).symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg ((real P).sheafedIso.inv ≫ ·)
    (Iso.hom_inv_id_assoc (ambientIso (real P).immersion) _)).trans ?_
  exact (real P).toBase_eq

/-- The inverse of `compare P` is compatible with the reductions to `𝒪_X`. -/
theorem compare_inv_comp_reduction :
    (compare P).inv ≫ transportedReduction (real P).immersion = P.reduction :=
  (congrArg ((compare P).inv ≫ ·) (compare_hom_comp_reduction P).symm).trans
    (Iso.inv_hom_id_assoc (compare P) _)

/-- The reduction of a solution is locally surjective as a morphism of sheaves of rings. -/
instance isLocallySurjective_forget₂_solutionReduction :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).map
        P.reduction).hom :=
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) P.reduction.hom :=
    P.locallySurjective
  isLocallySurjective_forget₂_map _

/-- The reduction of the realization of a solution is locally surjective as a morphism of
sheaves of rings. -/
instance isLocallySurjective_forget₂_realReduction :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).map
        (transportedReduction (real P).immersion)).hom :=
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (transportedReduction (real P).immersion).hom :=
    isLocallySurjective_transportedReduction _
  isLocallySurjective_forget₂_map _

/-- The identification of the conormal sheaf of the realization with the ideal of `X` in it. -/
abbrev realKernel :=
  kernelInclusion (real P).immersion (real_ker_sq P) (Iso.refl (conormalModules (real P).immersion))

/-- `baseComorphism P` on a section `j` is `baseMap₀ P` on the image of `j` under the unit. -/
theorem baseComorphism_app (W : S'.Opens) (j : Γ(S', W)) :
    ((baseComorphism P).hom.app (op W)).hom j =
      ((baseMap₀ P).hom.app (op ((Opens.map (f.base ≫ t.base)).obj W))).hom
        ((pullbackUnitApp (f.base ≫ t.base) S'.sheaf W).hom j) := by
  have h := Adjunction.homEquiv_unit
    (sheafAdjunction (f.toLRSHom.toShHom ≫ t.toLRSHom.toShHom)) _ _ (baseMap₀ P)
  exact congr($(h).hom.app (op W) j)

/-- The inverse of `compare P` sends the base map of `unitSection W j` to the transported
comorphism of the realization on `j`. -/
theorem compare_inv_baseMap (W : S'.Opens) (j : Γ(S', W)) :
    ((compare P).inv.hom.app (op ((Opens.map (f.base ≫ t.base)).obj W))).hom
        ((P.baseMap.hom.app (op ((Opens.map (f.base ≫ t.base)).obj W))).hom (unitSection W j)) =
      ((transportedBase (real P).immersion (real P).over_base).hom.app (op W)).hom j := by
  have h : baseComorphism P ≫ (TopCat.Sheaf.pushforward CommRingCat.{u}
      (f.base ≫ t.base)).map (compare P).inv =
        transportedBase (real P).immersion (real P).over_base :=
    (congrArg (· ≫ _) (transportedBase_comp_compare P).symm).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) ((Functor.map_comp _ _ _).symm.trans ((congrArg _
        (compare P).hom_inv_id).trans (CategoryTheory.Functor.map_id _ _)))).trans
          (Category.comp_id _)))
  refine Eq.trans ?_ (congr($(h).hom.app (op W) j))
  change _ = ((compare P).inv.hom.app _).hom (((baseComorphism P).hom.app (op W)).hom j)
  rw [baseComorphism_app]
  change _ = ((compare P).inv.hom.app _).hom ((P.baseMap.hom.app _).hom
    (((idIso f (thickenedBaseRing t f)).inv.hom.app _).hom _))
  exact congrArg (fun z => ((compare P).inv.hom.app _).hom ((P.baseMap.hom.app _).hom z))
    (idIso_inv_app_apply f _ _ _).symm

variable (hcan : ∀ (W : S'.Opens) (j : Γ(S', W)) (hj : (t.app W).hom j = 0),
  (c.val.app (op ((Opens.map (f.base ≫ t.base)).obj W))).hom (idealSection hst W j hj) =
    canonicalSection W j hj)
include hcan

/-- The kernel inclusion of a solution sends the canonical section of `j` to the base map of
`unitSection W j`. -/
theorem kernelInclusion_canonicalSection (W : S'.Opens) (j : Γ(S', W))
    (hj : (t.app W).hom j = 0) :
    (P.kernelInclusion.val.app (op ((Opens.map (f.base ≫ t.base)).obj W))).hom
        (canonicalSection W j hj) =
      (P.baseMap.hom.app (op ((Opens.map (f.base ≫ t.base)).obj W))).hom (unitSection W j) := by
  rw [← hcan W j hj]
  exact (P.baseMap_ideal _ (idealSection hst W j hj)).symm

/-- **The canonical map `f^*𝒞_{S/S'} ⟶ 𝒞_{X/X'}` of the realization `X'` of a solution is an
isomorphism.** -/
theorem isIso_immersionConormalSheafMap_real :
    IsIso (Stacks.Immersion.immersionConormalSheafMap (real P).immersion t f (real P).toBase
      (Stacks.Immersion.toShHom_square (real P).over_base)) := by
  obtain ⟨ψ, hψ⟩ := exists_hom_of_kernel P.reduction (transportedReduction (real P).immersion)
    P.kernelInclusion (realKernel P)
    (fun U => kernelSection_injective _ (real_ker_sq P) _ U.unop)
    (fun U a ha => exists_kernelSection_eq _ (real_ker_sq P) _ U.unop a ha)
    (fun U m => P.kernelZero U m) (compare P).inv (compare_inv_comp_reduction P)
  obtain ⟨ψ', hψ'⟩ := exists_hom_of_kernel (transportedReduction (real P).immersion)
    P.reduction (realKernel P) P.kernelInclusion (fun U => P.incl_injective)
    (fun U a ha => P.exists_incl a ha)
    (fun U m => transportedReduction_kernelSection _ (real_ker_sq P) _ U.unop m)
    (compare P).hom (compare_hom_comp_reduction P)
  have h1 : ψ ≫ ψ' = 𝟙 _ := SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun m => P.incl_injective (by
      change (P.kernelInclusion.val.app U).hom ((ψ'.val.app U).hom ((ψ.val.app U).hom m)) =
        (P.kernelInclusion.val.app U).hom m
      rw [hψ', hψ]
      exact congr($((compare P).inv_hom_id).hom.app U _))))
  have h2 : ψ' ≫ ψ = 𝟙 _ := SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun m =>
      kernelSection_injective _ (real_ker_sq P) _ U.unop (by
      change ((realKernel P).val.app U).hom ((ψ.val.app U).hom ((ψ'.val.app U).hom m)) =
        ((realKernel P).val.app U).hom m
      rw [hψ, hψ']
      exact congr($((compare P).hom_inv_id).hom.app U _))))
  have h3 : (Stacks.Immersion.immersionConormalSheafMap (real P).immersion t f (real P).toBase
        (Stacks.Immersion.toShHom_square (real P).over_base) :
          pullbackConormalModule f t ⟶ conormalModules (real P).immersion) = ψ := by
    refine conormalModule_hom_ext hst _ _ fun W j hj =>
      kernelSection_injective _ (real_ker_sq P) (Iso.refl _) _ ?_
    refine Eq.trans ?_ (hψ _ (canonicalSection W j hj)).symm
    rw [kernelInclusion_canonicalSection P hcan, compare_inv_baseMap, transportedBase_app]
    refine (kernelSection_eq_of_conormalClass (real P).immersion (real_ker_sq P)
      (Iso.refl (conormalModules (real P).immersion)) ((Opens.map (f.base ≫ t.base)).obj W) _
      ((real P).toBase ⁻¹ᵁ W) (toAmbient_comm (real P).immersion (real P).over_base W).le
      (((real P).toBase.app W).hom j)
      (Stacks.Conormal.app_app_eq_zero_of_square (real P).over_base W j hj) ?_).trans ?_
    · exact immersionConormalSheafMap_canonicalSection (real P).immersion (real P).toBase
        (real P).over_base W j hj
    exact congrArg (fun g => ((real P).ambient.presheaf.map g).hom (((real P).toBase.app W).hom j))
      (Subsingleton.elim _ _)
  exact ⟨ψ', (congrArg (· ≫ ψ') h3).trans h1, (congrArg (ψ' ≫ ·) h3).trans h2⟩

variable [Flat f]

/-- The realization of a solution is flat over `S'` and restricts to `X` over `S`. -/
theorem flat_and_isPullback_real :
    Flat (real P).toBase ∧ IsPullback (real P).immersion f (real P).toBase t :=
  Stacks.Thickenings.flat_and_isPullback_of_isIso_immersionConormalSheafMap (real P).immersion t f
    (real P).toBase (real P).over_base (real_ker_sq P) hst
    (isIso_immersionConormalSheafMap_real P hcan)

/-- **The flat deformation realizing a solution.** -/
def deformationOf : FlatDeformation t f where
  X' := (real P).ambient
  f' := (real P).toBase
  flat := (flat_and_isPullback_real P hcan).1
  i := (real P).immersion
  isPullback := (flat_and_isPullback_real P hcan).2

/-- The immersion of `deformationOf P hcan` is a homeomorphism on underlying spaces. -/
instance : IsIso (deformationOf P hcan).i.base :=
  inferInstanceAs (IsIso (real P).immersion.base)

/-- The map `c` of the problem is the map `c` of the flat deformation realizing a solution. -/
theorem idealMap_deformationOf : c = idealMap hst (deformationOf P hcan) :=
  ideal_hom_ext hst _ _ fun W j hj =>
    (hcan W j hj).trans (idealMap_idealSection hst (deformationOf P hcan) W j hj).symm

/-- **Every solution is isomorphic to the solution of the flat deformation it realizes.** -/
def solutionIsoDeformationOf :
    CompatibleFirstOrderThickening.Iso.{u, u, u, u, u, u}
      (S := problem t f hst c)
      (toSolution hst (deformationOf P hcan) c (idealMap_deformationOf P hcan)) P where
  hom := compare P
  reduction_comm := compare_hom_comp_reduction P
  baseMap_comm := by
    have h : baseRingMap (deformationOf P hcan) ≫ (compare P).hom = baseMap₀ P := by
      refine (Adjunction.homEquiv_naturality_right_symm
        (sheafAdjunction (f.toLRSHom.toShHom ≫ t.toLRSHom.toShHom)) _ _).symm.trans ?_
      refine (congrArg _ (transportedBase_comp_compare P)).trans ?_
      exact Equiv.symm_apply_apply _ _
    exact (Category.assoc _ _ _).trans ((congrArg ((idIso f (thickenedBaseRing t f)).hom ≫ ·)
      h).trans (Iso.hom_inv_id_assoc _ _))
  kernel_comm U g := kernel_comm_of_canonical hst (reduction (deformationOf P hcan)) P.reduction
    (kernelIncl hst (deformationOf P hcan)) P.kernelInclusion (fun U => P.incl_injective)
    (fun U a ha => P.exists_incl a ha)
    (fun U m => reduction_kernelIncl hst (deformationOf P hcan) U.unop m) (compare P).hom
    (compare_hom_comp_reduction P)
    (fun W j hj => by
      refine (congrArg _ (kernelIncl_canonicalSection hst (deformationOf P hcan) W j hj)).trans ?_
      refine Eq.trans ?_ (kernelInclusion_canonicalSection P hcan W j hj).symm
      refine (congr($(transportedBase_comp_compare P).hom.app (op W) j)).trans ?_
      refine (baseComorphism_app P W j).trans ?_
      change ((P.baseMap.hom.app _).hom (((idIso f _).inv.hom.app _).hom _)) = _
      exact congrArg (fun z => (P.baseMap.hom.app _).hom z) (idIso_inv_app_apply f _ _ _)) U g

end Stacks.Thickenings.FlatDeformation
