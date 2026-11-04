module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineBaseChangeCompCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeSheafHom
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMapFlatBase

/-!
# The base change map of Stacks 0DKH for affine representables at a complex flat over the base

For a cartesian square `U' = V' ×_V U` of objects of the big fppf site with affine underlying
schemes, with rings of global functions `R = Γ(V)`, `A = Γ(U)`, `R' = Γ(V')`, `A' = Γ(U')`, and
a bounded above complex `N` of `A`-modules whose terms are flat over `R`, the composite
`Lg^*Rf_*Ñ ⟶ Rf'_*L(g')^*Ñ ⟶ Rf'_*(g')^*Ñ` of Stacks 0DKH attached to the comparison of the
derived with the degreewise pullback is an isomorphism. This is the affine case of Stacks 0A1K.

## Main results

* `AlgebraicGeometry.Space.isIso_representedAffineBaseChangeComp_of_flat`: the statement for the
  associated objects `Φ_A N`, `Φ_{A'}(N ⊗_A A')` and the map induced by the comparison
  `N ⊗ᴸ_A A' ⟶ N ⊗_A A'`.
* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedBaseChangeComp_pullbackQComparison_of_flat`:
  the statement for the degreewise associated complex `Ñ` and the comparison of the derived with
  the degreewise pullback.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.CategoryTheory.BaseChange

/-- Bookkeeping for transporting a map `γ : L F ⟶ F'` along isomorphisms `a⁻¹ ≫ d⁻¹ : P ≅ F`
and `p⁻¹ ≫ M ≫ n⁻¹ : P' ≅ F'`, when `γ` factors as `L d ≫ k ≫ M ≫ n⁻¹`. -/
theorem map_comp_eq_of_transport {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D)
    {P H F : C} {H₁ P' H₂ F' : D} (a : H ≅ P) (d : F ≅ H) (k : L.obj H ⟶ H₁) (p : H₁ ≅ P')
    (M : H₁ ≅ H₂) (n : F' ≅ H₂) {γ : L.obj F ⟶ F'} {φ : L.obj P ⟶ P'}
    (hγ : γ = L.map d.hom ≫ k ≫ M.hom ≫ n.inv) (hφ : φ = L.map a.inv ≫ k ≫ p.hom) :
    L.map (a.symm ≪≫ d.symm).hom ≫ γ = φ ≫ (p.symm ≪≫ M ≪≫ n.symm).hom := by
  subst hγ hφ
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc,
    Iso.hom_inv_id_assoc]
  rw [← L.map_comp_assoc d.inv d.hom, Iso.inv_hom_id, L.map_id, Category.id_comp]

end Stacks.CategoryTheory.BaseChange

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance] additive_extendScalars_representedAffineRingHom
  additive_pullbackModules_representedSpaceMap

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {U V U' V' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V')]
  (f₀ : U ⟶ V) (g₀ : V' ⟶ V) (f₀' : U' ⟶ V') (g₀' : U' ⟶ U)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U')] in
/-- A cartesian square of affine objects of the big fppf site gives a cocartesian square of
rings of global functions. -/
theorem isPushout_representedAffineRingHom (hpb : IsPullback g₀' f₀' f₀ g₀) :
    IsPushout (CommRingCat.ofHom (representedAffineCommRingCatHom B S hS f₀).hom)
      (CommRingCat.ofHom (representedAffineCommRingCatHom B S hS g₀).hom)
      (CommRingCat.ofHom (representedAffineCommRingCatHom B S hS g₀').hom)
      (CommRingCat.ofHom (representedAffineCommRingCatHom B S hS f₀').hom) :=
  isPushout_appTop_of_isPullback (hpb.map (BigFppfOver.toScheme B S hS))

/-- **Stacks 0A1K for affine representables, at the associated objects.** For a cartesian square
of affine objects and a bounded above complex `N` of `Γ(U)`-modules with terms flat over `Γ(V)`,
the composite of Stacks 0DKH at `Φ_A N`, `Φ_{A'}(N ⊗_A A')` and the map induced by the comparison
`N ⊗ᴸ_A A' ⟶ N ⊗_A A'` is an isomorphism. -/
theorem isIso_representedAffineBaseChangeComp_of_flat (hpb : IsPullback g₀' f₀' f₀ g₀)
    (N : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) (b : ℤ)
    [N.IsStrictlyLE b]
    (hN : ∀ n, Module.Flat Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      ((ModuleCat.restrictScalars.{u} (representedAffineCommRingCatHom B S hS f₀).hom).obj
        (N.X n))) :
    IsIso (smallEtaleDerivedBaseChangeComp B S hS (representedSpaceMap B S hS f₀)
        (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
        (representedSpaceMap B S hS g₀') (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' hpb.w)
        ((representedAffineToposDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj N))
        ((representedAffineToposDerivedAssociated B S hS U').obj (DerivedCategory.Q.obj
          (((ModuleCat.extendScalars.{u, u, u}
            (representedAffineCommRingCatHom B S hS g₀').hom).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj N)))
        ((representedAffineToposDerivedBaseChangeIso B S hS g₀').hom.app (DerivedCategory.Q.obj N) ≫
          (representedAffineToposDerivedAssociated B S hS U').map
            ((representedAffineDerivedExtension B S hS g₀').comparison.app N))) :=
  (isIso_representedAffineBaseChangeComp_iff B S hS f₀ g₀ f₀' g₀' hpb.w _ _ _).2
    (RingTheory.TorIndependence.isIso_ringHomSquareComparison_comp_comparison_of_flat _ _ _ _ _
      (isPushout_representedAffineRingHom B S hS f₀ g₀ f₀' g₀' hpb) N b hN)

/-- **Stacks 0A1K for affine representables.** For a cartesian square of affine objects and a
bounded above complex `N` of `Γ(U)`-modules with terms flat over `Γ(V)`, the composite of
Stacks 0DKH at the degreewise associated complex `Ñ`, `(g')^*Ñ` and the comparison
`L(g')^*Ñ ⟶ (g')^*Ñ` of the derived with the degreewise pullback is an isomorphism. -/
theorem isIso_smallEtaleDerivedBaseChangeComp_pullbackQComparison_of_flat
    (hpb : IsPullback g₀' f₀' f₀ g₀)
    (N : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) (b : ℤ)
    [N.IsStrictlyLE b]
    (hN : ∀ n, Module.Flat Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      ((ModuleCat.restrictScalars.{u} (representedAffineCommRingCatHom B S hS f₀).hom).obj
        (N.X n))) :
    IsIso (smallEtaleDerivedBaseChangeComp B S hS (representedSpaceMap B S hS f₀)
        (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
        (representedSpaceMap B S hS g₀') (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' hpb.w)
        (DerivedCategory.Q.obj (((representedAffineToposAssociated B S hS U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N)) _
        (smallEtaleDerivedPullbackQComparison (representedSpaceMap B S hS g₀')
          (((representedAffineToposAssociated B S hS U).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj N))) := by
  let L := smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')
  let Nt := ((representedAffineToposAssociated B S hS U).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj N
  let Ne := ((ModuleCat.extendScalars.{u, u, u}
    (representedAffineCommRingCatHom B S hS g₀').hom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N
  let qU := DerivedCategory.quotientCompQhIso
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩))
  let qU' := DerivedCategory.quotientCompQhIso
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩))
  let edge := Stacks.Homology.homotopyEdgeIso (representedAffineToposPullbackIso B S hS g₀')
  let e : DerivedCategory.Q.obj Nt ≅
      (representedAffineToposDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj N) :=
    (qU.app Nt).symm ≪≫ ((representedAffineToposDerivedFactors B S hS U).app N).symm
  let e' : DerivedCategory.Q.obj
        (((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
          (X := smallEtaleRingedTopos B S hS _)
          (Y := smallEtaleRingedTopos B S hS _)
          (smallEtaleRingedToposHom B S hS
            (representedSpaceMap B S hS g₀')).toModulesHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj Nt) ≅
      (representedAffineToposDerivedAssociated B S hS U').obj (DerivedCategory.Q.obj Ne) :=
    (qU'.app _).symm ≪≫ DerivedCategory.Qh.mapIso (edge.app N) ≪≫
      ((representedAffineToposDerivedFactors B S hS U').app Ne).symm
  refine (isIso_smallEtaleDerivedBaseChangeComp_iff_of_iso B S hS _ _ _ _
    (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' hpb.w) _ _ _ _ _
    ((representedAffineToposDerivedBaseChangeIso B S hS g₀').hom.app (DerivedCategory.Q.obj N) ≫
      (representedAffineToposDerivedAssociated B S hS U').map
        ((representedAffineDerivedExtension B S hS g₀').comparison.app N)) e e' ?_).2
    (isIso_representedAffineBaseChangeComp_of_flat B S hS f₀ g₀ f₀' g₀' hpb N b hN)
  exact Stacks.CategoryTheory.BaseChange.map_comp_eq_of_transport L (qU.app Nt)
    ((representedAffineToposDerivedFactors B S hS U).app N) _ (qU'.app _)
    (DerivedCategory.Qh.mapIso (edge.app N))
    ((representedAffineToposDerivedFactors B S hS U').app Ne)
    (representedAffineToposDerivedBaseChangeIso_hom_app_comparison B S hS g₀' N)
    (smallEtaleDerivedPullbackQComparison.eq_1 _ _)

end AlgebraicGeometry.Space
