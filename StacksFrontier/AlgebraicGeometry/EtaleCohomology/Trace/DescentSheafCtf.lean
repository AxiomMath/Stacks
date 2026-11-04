module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfOpenClosed
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.DescentModuleProjective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteProjectivePullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlatShriek
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.NoetherianStratification
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit

/-!
# Descent sheaves of finite projective modules lie in `D_ctf`

Let `G` be a Galois covering of a scheme `X` with group `H`, `Λ` a ring (possibly
noncommutative) and `N` a finite projective `Λ`-module with an action of `H`. The descent sheaf
`D(N)` is constant on the covering, so it is locally constant with finite projective values.
Such a sheaf, and every inverse image of it, is constructible flat, and the complex
concentrated in one degree with it as its only term lies in `D_ctf(X_étale, Λ)`.

This is the input of the trace formula of Tag 03V3 for the sheaves
`𝒫 = D(Λ[H])` of the dévissage in Tag 03UZ, on a stratum and on its base changes to finite
extensions of the ground field.

## Main results

* `AlgebraicGeometry.EtaleGaloisCovering.isFiniteProjectiveLocallyConstant_descentSheaf`.
* `AlgebraicGeometry.isConstructibleFlatModuleSheaf_of_isFiniteProjectiveLocallyConstant`.
* `Stacks.EtaleCohomology.isCtf_single_of_isFiniteProjectiveLocallyConstant`.
* `Stacks.EtaleCohomology.isCtf_single_descentSheaf` and
  `Stacks.EtaleCohomology.isCtf_single_inverseImage_descentSheaf`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u w v r

namespace AlgebraicGeometry.EtaleGaloisCovering

variable {X : Scheme.{u}} {H : Type*} [Group H] (G : EtaleGaloisCovering X H) (Λ : Type r)
  [Ring Λ] (N : Type (max (u + 1) r)) [AddCommGroup N] [Module Λ N] (ρ : H →* Module.End Λ N)

/-- **A descent sheaf of a finite projective module is locally constant with finite projective
values**: it is constant on the covering, which covers every object of the small étale site
after base change. -/
public theorem isFiniteProjectiveLocallyConstant_descentSheaf [Module.Finite Λ N]
    [Module.Projective Λ N] :
    Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ X.smallEtaleTopology
      (EtaleGaloisCovering.descentSheaf.{u, r, _, r} G Λ N ρ) := by
  intro U
  refine ⟨PUnit, fun _ => G.fiberObj U, fun _ => G.fiberObjFst U, G.ofArrows_fiberObjFst_mem U,
    fun _ => ⟨ModuleCat.of Λ N, inferInstanceAs (Module.Finite Λ N),
      inferInstanceAs (Module.Projective Λ N), ⟨?_⟩⟩⟩
  exact Stacks.ConstantSheaf.overPullbackIsoOfMapModule X.smallEtaleTopology (G.fiberObjSnd U)
    (EtaleGaloisCovering.descentSheaf.{u, r, _, r} G Λ N ρ) (ModuleCat.of Λ N)
    (EtaleGaloisCovering.trivialization.{u, r, _, r} G Λ N ρ)

end AlgebraicGeometry.EtaleGaloisCovering

namespace AlgebraicGeometry

attribute [local instance] Stacks.EtaleCohomology.moduleCat_hasLimitsOfSize
  AlgebraicGeometry.SmallEtale.hasWeakSheafify_over_moduleCat_ring
  AlgebraicGeometry.SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [Ring Λ]

/-- **A locally constant sheaf with finite projective values is constructible flat**: on every
affine open the stratification by that open alone works, local constancy with finite projective
values surviving inverse image. -/
public theorem isConstructibleFlatModuleSheaf_of_isFiniteProjectiveLocallyConstant
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ))
    (hF : Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ
      (SmallEtale.topology B X.obj X.property) F) :
    IsConstructibleFlatModuleSheaf B X Λ F := by
  intro U
  refine ⟨ConstructibleStratification.ofPartition B X U.1
    (fun _ : Fin 1 => (U.1 : Set X.obj))
    (fun _ => U.1.isOpen.isLocallyClosed) (fun _ => subset_rfl)
    (fun _ => ?_) (fun i j hij => absurd (Subsingleton.elim i j) hij)
    (Set.iUnion_const _).symm, fun i => ?_⟩
  · have h : U.1.ι.base ⁻¹' (U.1 : Set X.obj) = Set.univ :=
      Set.preimage_eq_univ_iff.2 (by rw [Scheme.Opens.range_ι])
    rw [h]
    exact Topology.IsConstructible.univ
  · exact isFiniteProjectiveLocallyConstant_smallEtaleSheafPullback B Λ _ F hF

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

open AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  AlgebraicGeometry.SmallEtale.hasWeakSheafify_over_moduleCat_ring
  AlgebraicGeometry.SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [Ring Λ]

/-- A sheaf on Mathlib's small étale site which is locally constant with finite projective values
is constructible flat. -/
public theorem isConstructibleFlatEtaleModule_of_isFiniteProjectiveLocallyConstant
    (F : EtaleModules.{u, r} Λ X.obj)
    (hF : Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ X.obj.smallEtaleTopology F) :
    IsConstructibleFlatEtaleModule B X Λ F :=
  isConstructibleFlatModuleSheaf_of_isFiniteProjectiveLocallyConstant B X Λ _
    ((SmallEtale.isFiniteProjectiveLocallyConstant_sheafEquiv_inverse_iff B X Λ F).2 hF)

/-- The zero sheaf is locally constant with finite projective values. -/
public theorem isFiniteProjectiveLocallyConstant_of_isZero (F : EtaleModules.{u, r} Λ X.obj)
    (hF : IsZero F) :
    Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ X.obj.smallEtaleTopology F := by
  intro U
  refine ⟨PUnit, fun _ => U, fun _ => 𝟙 U, ?_, fun _ =>
    ⟨ModuleCat.of Λ PUnit, inferInstance, inferInstance, ⟨IsZero.iso ?_ ?_⟩⟩⟩
  · refine GrothendieckTopology.superset_covering _ (fun Y g _ => ?_)
      (GrothendieckTopology.top_mem _ U)
    exact ⟨U, g, 𝟙 U, Presieve.ofArrows.mk PUnit.unit, Category.comp_id g⟩
  · exact Functor.map_isZero _ (ModuleCat.isZero_of_subsingleton _)
  · exact Functor.map_isZero _ hF

/-- **A sheaf locally constant with finite projective values, placed in degree zero, lies in
`D_ctf(X_étale, Λ)`.** -/
public theorem isCtf_single_of_isFiniteProjectiveLocallyConstant (F : EtaleModules.{u, r} Λ X.obj)
    (hF : Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ X.obj.smallEtaleTopology F) :
    IsCtf B X Λ (DerivedCategory.Q.obj
      ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, r} Λ X.obj) 0).obj F).obj) := by
  have hX : ∀ i : ℤ, IsConstructibleFlatEtaleModule B X Λ
      (((CochainComplex.singleFunctor (EtaleModules.{u, r} Λ X.obj) 0).obj F).X i) := by
    intro i
    by_cases hi : i = 0
    · subst hi
      exact (isConstructibleFlatEtaleModule_of_isFiniteProjectiveLocallyConstant B X Λ F hF).of_iso
        B X Λ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).symm
    · exact isConstructibleFlatEtaleModule_of_isZero B Λ X
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)
  exact IsRepresentedByConstructibleFlatEtaleComplex.isCtf B Λ
    ⟨(CochainComplex.singleFunctor (EtaleModules.{u, r} Λ X.obj) 0).obj F, 0, 0,
      inferInstanceAs (((CochainComplex.singleFunctor _ 0).obj F).IsStrictlyGE 0),
      inferInstanceAs (((CochainComplex.singleFunctor _ 0).obj F).IsStrictlyLE 0), hX,
      ⟨Iso.refl _⟩⟩

/-- The same in the form `ι(Q(K))` of the bounded below derived category. -/
public theorem isCtf_plusι_single_of_isFiniteProjectiveLocallyConstant
    (F : EtaleModules.{u, r} Λ X.obj)
    (hF : Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ X.obj.smallEtaleTopology F) :
    IsCtf B X Λ (DerivedCategory.Plus.ι.obj (DerivedCategory.Plus.Q.obj
      ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, r} Λ X.obj) 0).obj F))) :=
  (isCtf_single_of_isFiniteProjectiveLocallyConstant B X Λ F hF).of_iso B X Λ
    ((ObjectProperty.liftCompιIso _ _ _ :
      DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.ι ≅
        CochainComplex.Plus.ι _ ⋙ DerivedCategory.Q).app _).symm

section Descent

variable {H : Type*} [Group H] (N : Type (max (u + 1) r)) [AddCommGroup N] [Module Λ N]
  [Module.Finite Λ N] [Module.Projective Λ N] (ρ : H →* Module.End Λ N)

/-- **A descent sheaf of a finite projective module, in degree zero, lies in
`D_ctf(Z_étale, Λ)`.** -/
public theorem isCtf_single_descentSheaf {Z : Scheme.{u}} (hZ : B.Contains Z)
    (G : EtaleGaloisCovering Z H) :
    IsCtf B (B.obj Z hZ) Λ (DerivedCategory.Plus.ι.obj (DerivedCategory.Plus.Q.obj
      ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, r} Λ Z) 0).obj
        (EtaleGaloisCovering.descentSheaf.{u, r, _, r} G Λ N ρ)))) :=
  isCtf_plusι_single_of_isFiniteProjectiveLocallyConstant B (B.obj Z hZ) Λ _
    (G.isFiniteProjectiveLocallyConstant_descentSheaf Λ N ρ)

/-- **The inverse image of a descent sheaf of a finite projective module along any morphism, in
degree zero, lies in `D_ctf`**; for instance along the base change `Z_{k_m} ⟶ Z` to a finite
extension of the ground field. -/
public theorem isCtf_single_inverseImage_descentSheaf {Z W : Scheme.{u}} (hW : B.Contains W)
    (G : EtaleGaloisCovering Z H) (g : W ⟶ Z) :
    IsCtf B (B.obj W hW) Λ (DerivedCategory.Plus.ι.obj (DerivedCategory.Plus.Q.obj
      ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, r} Λ W) 0).obj
        ((etaleModuleInverseImage.{u, r} Λ g).obj
          (EtaleGaloisCovering.descentSheaf.{u, r, _, r} G Λ N ρ))))) :=
  isCtf_plusι_single_of_isFiniteProjectiveLocallyConstant B (B.obj W hW) Λ _
    (isFiniteProjectiveLocallyConstant_etaleModuleInverseImage Λ g _
      (G.isFiniteProjectiveLocallyConstant_descentSheaf Λ N ρ))

end Descent

end Stacks.EtaleCohomology

end
