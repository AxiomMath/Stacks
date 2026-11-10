module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveRepresentationCoindTrace

/-!
# `H¹(C, j_! ℱ_{N[π/H]})` and `H¹(U, ℱ_{N[π/H]})` through the cover

Let `U` be a connected open, with finite complement, of a smooth proper curve `C` over an
algebraically closed field, `H` an open subgroup of `π₁(U, y)` and `N` a finite `Λ`-module.
The sheaf of the permutation module `N[π/H]` is `φ_*(N_V)` for the connected finite étale cover
`φ : V ⟶ U` with group `H` (Tag 0BND, `AlgebraicGeometry.representationSheafCoindTrivialIso`).
Hence

* `H^i(C, j_! ℱ_{N[π/H]}) ≅ H^i(V̄, j_{V!} N_V)` for the smooth projective compactification `V̄`
  of `V`, extension by zero commuting with the finite direct image `φ̄_*`;
* `H^i(U, ℱ_{N[π/H]}) ≅ H^i(V, N_V)`, the direct image being finite.

These reduce the count `#H¹_c ≤ #H¹` for `ℱ_{N[π/H]}` (Tag 03VM) to constant coefficients on a
smooth curve.

## Main results

* `AlgebraicGeometry.exists_cover_rightDerived_coindTrivial_linearEquiv`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.GroupCohomology
  Stacks.EtaleCohomology

universe u

/-- Enough injectives for sheaves of `Λ`-modules at coefficient universe `0`, pinned. -/
local instance (priority := 3000) etaleModulesEnoughInjectivesFirstCount (Λ : Type) [Ring Λ]
    (Y : Scheme.{u}) : EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

namespace AlgebraicGeometry

attribute [local instance] compactSpace_etaleFundamentalGroup

variable (B : BigEtaleSite.{u}) (U : B.Scheme) [ConnectedSpace U.1] (y : GeometricPoint U.1)
  (H : OpenSubgroup (EtaleFundamentalGroup U.1 y))
  {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} (q : C ⟶ Spec (.of K))
  [IsCurve K q] [Smooth q] [IsProper q]
  (jC : U.1 ⟶ C) [IsOpenImmersion jC]

include q in
/-- **The cover computation of `H¹_c` and `H¹` of `ℱ_{N[π/H]}`.** There are a smooth curve `V`
over `K` and an open immersion `V ⟶ V̄` into a smooth proper curve over `K` such that, for every
finite ring `Λ` and every finite `Λ`-module `N`, `H¹(C, j_! ℱ_{N[π/H]}) ≃ H¹(V̄, j_! N_V)` and
`H¹(U, ℱ_{N[π/H]}) ≃ H¹(V, N_V)`: `V` is the connected cover of `U` with group `H`, which does
not depend on the coefficients. -/
theorem exists_cover_rightDerived_coindTrivial_linearEquiv :
    ∃ (V Vb : Scheme.{u}) (qV : V ⟶ Spec (.of K)) (qb : Vb ⟶ Spec (.of K)) (jV : V ⟶ Vb)
      (_ : IsCurve K qV) (_ : Smooth qV) (_ : IsCurve K qb) (_ : Smooth qb) (_ : IsProper qb)
      (_ : IsOpenImmersion jV), ∀ (Λ : Type) [Ring Λ] [Finite Λ]
        (N : ObjectProperty.FullSubcategory (ModuleCat.isFG.{u + 1} Λ)),
      Nonempty (((etaleModuleGlobalSections.{u, 0} Λ C).rightDerived 1).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ jC).obj
            ((representationSheaf B U y Λ).obj ((finiteTypeContinuousModuleCoind Λ H).obj
              ((finiteTypeContinuousModuleTrivial Λ _).obj N)))) ≃ₗ[Λ]
        ((etaleModuleGlobalSections.{u, 0} Λ Vb).rightDerived 1).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ jV).obj
            ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
              ((ModuleCat.uliftFunctor.{0, u + 1} Λ).obj ((ModuleCat.isFG Λ).ι.obj N))))) ∧
      Nonempty (((etaleModuleGlobalSections.{u, 0} Λ U.1).rightDerived 1).obj
          ((representationSheaf B U y Λ).obj ((finiteTypeContinuousModuleCoind Λ H).obj
            ((finiteTypeContinuousModuleTrivial Λ _).obj N))) ≃ₗ[Λ]
        ((etaleModuleGlobalSections.{u, 0} Λ V).rightDerived 1).obj
          ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            ((ModuleCat.uliftFunctor.{0, u + 1} Λ).obj ((ModuleCat.isFG Λ).ι.obj N)))) := by
  obtain ⟨W, w, htrans, hstab⟩ := exists_finiteEtaleOver_transitive_stabilizer_eq y H
  have : ConnectedSpace W.left := connectedSpace_left_of_exists_smul_eq htrans
  have hf : finiteEtale W.hom := W.prop
  have : IsFinite W.hom := W.prop.1
  have : Etale W.hom := W.prop.2
  let Vb : B.Scheme := ⟨W.left, contains_of_locallyOfFiniteType_of_quasiCompact B W.hom U.2⟩
  let g : Vb ⟶ U := ObjectProperty.homMk W.hom
  have : ConnectedSpace Vb.1 := inferInstanceAs (ConnectedSpace W.left)
  have : IsFinite g.hom := inferInstanceAs (IsFinite W.hom)
  have : Etale g.hom := inferInstanceAs (Etale W.hom)
  let t : GeometricPoint Vb.1 := ⟨y.residueField, w.1⟩
  have hy : t.map g.hom = y := by
    change (⟨y.residueField, w.1 ≫ W.hom⟩ : GeometricPoint U.1) = y
    rw [w.2]
  let cc := curveCoverCompactification q jC g.hom
  have := cc.isCurve
  have := cc.smooth
  have := cc.isProper
  have := cc.isOpenImmersion
  have : Nonempty Vb.1 := ConnectedSpace.toNonempty
  have hqV := isCurve_comp_of_isOpenImmersion_of_nonempty K cc.q cc.j
  refine ⟨Vb.1, cc.Vb, cc.j ≫ cc.q, cc.q, cc.j, hqV, inferInstance, cc.isCurve, cc.smooth,
    cc.isProper, cc.isOpenImmersion, fun Λ _ _ N ↦ ?_⟩
  have : Module.Finite Λ N.obj := N.property
  have : Finite N.obj := Module.finite_of_finite Λ
  -- generalize the base point, so that it can be substituted by `t.map g`
  suffices key : ∀ (y' : GeometricPoint U.1) (_ : t.map g.hom = y')
      (H' : OpenSubgroup (EtaleFundamentalGroup U.1 y')) (w' : (finiteEtaleFiberFunctor y').obj W)
      (_ : HEq w'.1 w.1) (_ : ∀ σ : EtaleFundamentalGroup U.1 y', σ • w' = w' ↔ σ ∈ H'),
        Nonempty (((etaleModuleGlobalSections.{u, 0} Λ C).rightDerived 1).obj
            ((etaleModuleExtensionByZero.{u, 0} Λ jC).obj
              ((representationSheaf B U y' Λ).obj ((finiteTypeContinuousModuleCoind Λ H').obj
                ((finiteTypeContinuousModuleTrivial Λ _).obj N)))) ≃ₗ[Λ]
          ((etaleModuleGlobalSections.{u, 0} Λ cc.Vb).rightDerived 1).obj
            ((etaleModuleExtensionByZero.{u, 0} Λ cc.j).obj
              ((constantSheaf Vb.1.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
                ((ModuleCat.uliftFunctor.{0, u + 1} Λ).obj ((ModuleCat.isFG Λ).ι.obj N))))) ∧
        Nonempty (((etaleModuleGlobalSections.{u, 0} Λ U.1).rightDerived 1).obj
            ((representationSheaf B U y' Λ).obj ((finiteTypeContinuousModuleCoind Λ H').obj
              ((finiteTypeContinuousModuleTrivial Λ _).obj N))) ≃ₗ[Λ]
          ((etaleModuleGlobalSections.{u, 0} Λ Vb.1).rightDerived 1).obj
            ((constantSheaf Vb.1.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
              ((ModuleCat.uliftFunctor.{0, u + 1} Λ).obj ((ModuleCat.isFG Λ).ι.obj N)))) from
    key y hy H w HEq.rfl hstab
  intro y' hy' H' w' hw' hstab'
  subst hy'
  obtain rfl : w' = finiteEtaleOverSourcePoint hf t := Subtype.ext (eq_of_heq hw')
  -- `H'` is the image of `π₁(V, t)`
  have hrange := range_etaleFundamentalGroupMap_eq_stabilizer (f := g.hom) hf t
  have hmem : ∀ σ, σ ∈ (etaleFundamentalGroupMap g.hom t).toMonoidHom.range ↔ σ ∈ H' := by
    intro σ
    rw [hrange, MulAction.mem_stabilizer_iff]
    exact hstab' σ
  have hφ : ∀ τ, etaleFundamentalGroupMap g.hom t τ ∈ H' := fun τ ↦ (hmem _).mp ⟨τ, rfl⟩
  have hH : ∀ h ∈ H', ∃ τ, etaleFundamentalGroupMap g.hom t τ = h := fun h hh ↦ (hmem h).mpr hh
  let := HasDerivedCategory.standard (EtaleModules.{u, 0} Λ C)
  let := HasDerivedCategory.standard (EtaleModules.{u, 0} Λ U.1)
  let := HasDerivedCategory.standard (EtaleModules.{u, 0} Λ Vb.1)
  let := HasDerivedCategory.standard (EtaleModules.{u, 0} Λ cc.Vb)
  let := HasDerivedCategory.standard (ModuleCat.{u + 1} Λ)
  let e := (representationSheafCoindTrivialIso B g Λ t H' hφ hH).app N
  refine ⟨⟨?_⟩, ⟨?_⟩⟩
  · exact ((((etaleModuleGlobalSections.{u, 0} Λ C).rightDerived 1).mapIso
        ((etaleModuleExtensionByZero.{u, 0} Λ jC).mapIso e)) ≪≫
      (Stacks.DerivedIndexing.rightDerivedIso _ 1).app _ ≪≫
      ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((1 : ℕ) : ℤ)).mapIso
        ((extensionByZeroDirectImageIntegralIso Λ jC cc.j g.hom cc.fb cc.isPullback.flip).app _) ≪≫
      integralDirectImageCohomologyIso Λ cc.fb _ ((1 : ℕ) : ℤ) ≪≫
      ((Stacks.DerivedIndexing.rightDerivedIso _ 1).app _).symm).toLinearEquiv
  · exact ((((etaleModuleGlobalSections.{u, 0} Λ U.1).rightDerived 1).mapIso e) ≪≫
      (Stacks.DerivedIndexing.rightDerivedIso _ 1).app _ ≪≫
      integralDirectImageCohomologyIso Λ g.hom _ ((1 : ℕ) : ℤ) ≪≫
      ((Stacks.DerivedIndexing.rightDerivedIso _ 1).app _).symm).toLinearEquiv

end AlgebraicGeometry

end
