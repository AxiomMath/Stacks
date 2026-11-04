module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkCohomologyMapAffine
public import StacksFrontier.RingTheory.Dualizing.RelativeComposition

/-!
# The derived geometric stalk of `Φ(K)` on an affine representable space

Let `U` be an object of the big fppf site over `S` with affine underlying scheme, `A` its ring of
global functions, `Φ : D(A) ⥤ D(𝒪_{yoneda.obj U})` the derived associated-module functor and `x̄`
a geometric point of `yoneda.obj U`. Then `(Φ K)_{x̄} ≅ K ⊗ᴸ_A 𝒪_{x̄}`, naturally in `K`.

## Main definitions

* `AlgebraicGeometry.Space.representedAffineDerivedStalkComparison`: on a complex `M` of
  `A`-modules, `(Φ M)_{x̄} ≅ (M^~)_{x̄} ≅ 𝒪_{x̄} ⊗_A M` degreewise.
* `AlgebraicGeometry.Space.representedAffineDerivedStalkIso`: the isomorphism
  `(Φ K)_{x̄} ≅ K ⊗ᴸ_A 𝒪_{x̄}`, natural in `K`.

## Main results

* `AlgebraicGeometry.Space.representedAffineDerivedStalkIso_hom_app_comp_comparison`: on a complex,
  the isomorphism followed by the comparison of derived with degreewise extension of scalars is
  the degreewise comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Over a flat ring map the comparison of derived with degreewise extension of scalars is an
isomorphism at every complex. -/
theorem isIso_totalDerivedExtensionScalars_comparison_of_flat {R A : Type u} [CommRing R]
    [CommRing A] (f : R →+* A) (hf : f.Flat) :
    IsIso (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      f).comparison := by
  let := (Dualizing.preservesFiniteLimits_extendScalars_of_flat f hf).1
  let := (Dualizing.preservesFiniteLimits_extendScalars_of_flat f hf).2
  have : (ModuleCat.extendScalars.{u, u, u} f).PreservesHomology :=
    CochainComplex.DerivedTensor.extensionScalars_preservesHomology f hf
  exact Functor.isIso_of_isLeftDerivedFunctor_of_inverts _ _
    (W := HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) (by
      intro X Y g hg
      have : QuasiIso g := hg
      show IsIso (DerivedCategory.Q.map
        (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex _).map g))
      infer_instance)

section Stalk

variable (U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  (x : GeometricPoint B S hS (yoneda.obj U))

/-- The geometric stalk at `x̄`, as a functor out of the `𝒪`-modules of `yoneda.obj U`. -/
abbrev representedStalkFunctor :
    Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) ⥤
      ModuleCat.{u} (geometricStalkRing B S hS
        (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) x) :=
  Stacks.sheafModuleFiberOfCommRing
    (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U))
    (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O

/-- The geometric stalk functor at `x̄` is additive. -/
instance : (representedStalkFunctor B S hS U x).Additive :=
  Stacks.instAdditiveSheafModuleFiberOfCommRing
    (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U))
    (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O

/-- The geometric stalk functor at `x̄` preserves finite limits. -/
instance : PreservesFiniteLimits (representedStalkFunctor B S hS U x) :=
  Stacks.preservesFiniteLimits_sheafModuleFiberOfCommRing
    (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U))
    (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O

/-- The geometric stalk functor at `x̄` preserves finite colimits. -/
instance : PreservesFiniteColimits (representedStalkFunctor B S hS U x) :=
  Stacks.instPreservesFiniteColimitsSheafModuleFiberOfCommRing
    (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U))
    (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O

/-- Extension of scalars along `A ⟶ 𝒪_{x̄}` is additive. -/
instance :
    (ModuleCat.extendScalars.{u, u, u} (representedAffineGlobalStalkRingHom B S hS U x)).Additive :=
  (ModuleCat.extendRestrictScalarsAdj
    (representedAffineGlobalStalkRingHom B S hS U x)).left_adjoint_additive

/-- The degreewise geometric stalk of the degreewise associated module is degreewise extension
of scalars along `A ⟶ 𝒪_{x̄}`. -/
def representedAffineComplexStalkIso :
    (representedAffineAssociated B S hS U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (representedStalkFunctor B S hS U x).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (ModuleCat.extendScalars.{u, u, u}
        (representedAffineGlobalStalkRingHom B S hS U x)).mapHomologicalComplex
          (ComplexShape.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (Iso.refl (representedAffineStalk B S hS U x)) _ ≪≫
    (NatIso.mapHomologicalComplex (representedAffineStalkIso B S hS U x) _).symm

/-- In degree `n`, the component of `AlgebraicGeometry.Space.representedAffineComplexStalkIso` at
a complex `M` is the inverse of `AlgebraicGeometry.Space.representedAffineStalkIso` at `M^n`. -/
theorem representedAffineComplexStalkIso_hom_app_f
    (M : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) (n : ℤ) :
    ((representedAffineComplexStalkIso B S hS U x).hom.app M).f n =
      (representedAffineStalkIso B S hS U x).inv.app (M.X n) := by
  simp only [representedAffineComplexStalkIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    HomologicalComplex.comp_f, NatIso.mapHomologicalComplex_inv_app_f]
  exact Category.id_comp _

/-- The geometric stalk of the associated module on a complex `M` of `A`-modules, viewed in the
derived category: `(Φ M)_{x̄} ≅ (M^~)_{x̄} ≅ 𝒪_{x̄} ⊗_A M`, degreewise, naturally in `M`. -/
def representedAffineDerivedStalkComparison :
    DerivedCategory.Q ⋙ (representedAffineDerivedAssociated B S hS U ⋙
        (representedStalkFunctor B S hS U x).mapDerivedCategory) ≅
      (ModuleCat.extendScalars.{u, u, u}
        (representedAffineGlobalStalkRingHom B S hS U x)).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (representedAffineAssociated B S hS U).mapDerivedCategoryFactors
      (representedStalkFunctor B S hS U x).mapDerivedCategory ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      ((representedAffineAssociated B S hS U).mapHomologicalComplex (ComplexShape.up ℤ))
      (representedStalkFunctor B S hS U x).mapDerivedCategoryFactors ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (representedAffineComplexStalkIso B S hS U x) DerivedCategory.Q

/-- The component of `AlgebraicGeometry.Space.representedAffineDerivedStalkComparison` at a
complex `M` is the composite of the two factorization isomorphisms through the localization and
the image of `AlgebraicGeometry.Space.representedAffineComplexStalkIso` at `M`. -/
theorem representedAffineDerivedStalkComparison_hom_app
    (M : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    (representedAffineDerivedStalkComparison B S hS U x).hom.app M =
      (representedStalkFunctor B S hS U x).mapDerivedCategory.map
          ((representedAffineAssociated B S hS U).mapDerivedCategoryFactors.hom.app M) ≫
        (representedStalkFunctor B S hS U x).mapDerivedCategoryFactors.hom.app
          (((representedAffineAssociated B S hS U).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M) ≫
        DerivedCategory.Q.map ((representedAffineComplexStalkIso B S hS U x).hom.app M) := by
  simp only [representedAffineDerivedStalkComparison, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Category.id_comp]

/-- The derived geometric stalk of `Φ(K)`: for `K ∈ D(A)` and a geometric point `x̄` of
`yoneda.obj U`, `(Φ K)_{x̄} ≅ K ⊗ᴸ_A 𝒪_{x̄}`, naturally in `K`. -/
def representedAffineDerivedStalkIso :
    representedAffineDerivedAssociated B S hS U ⋙
        (representedStalkFunctor B S hS U x).mapDerivedCategory ≅
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (representedAffineGlobalStalkRingHom B S hS U x)).functor :=
  haveI := isIso_totalDerivedExtensionScalars_comparison_of_flat _
    (flat_representedAffineStalkRingHom B S hS U x)
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ (representedAffineDerivedAssociated B S hS U ⋙
      (representedStalkFunctor B S hS U x).mapDerivedCategory))
    (DerivedCategory.Q ⋙
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (representedAffineGlobalStalkRingHom B S hS U x)).functor) _ _
    (representedAffineDerivedStalkComparison B S hS U x ≪≫
      (asIso (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (representedAffineGlobalStalkRingHom B S hS U x)).comparison).symm)

/-- On a complex, `AlgebraicGeometry.Space.representedAffineDerivedStalkIso` followed by the
comparison of derived with degreewise extension of scalars is
`AlgebraicGeometry.Space.representedAffineDerivedStalkComparison`. -/
theorem representedAffineDerivedStalkIso_hom_app_comp_comparison
    (M : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    (representedAffineDerivedStalkIso B S hS U x).hom.app (DerivedCategory.Q.obj M) ≫
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (representedAffineGlobalStalkRingHom B S hS U x)).comparison.app M =
      (representedAffineDerivedStalkComparison B S hS U x).hom.app M := by
  have := isIso_totalDerivedExtensionScalars_comparison_of_flat _
    (flat_representedAffineStalkRingHom B S hS U x)
  simp only [representedAffineDerivedStalkIso, Localization.liftNatIso_hom,
    Localization.liftNatTrans_app, Localization.Lifting.iso, Iso.refl_hom,
    NatTrans.id_app, Iso.refl_inv, Category.id_comp, Category.comp_id]
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    (Iso.inv_hom_id_app
      (asIso (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (representedAffineGlobalStalkRingHom B S hS U x)).comparison) M)).trans
    (Category.comp_id _))

end Stalk

end AlgebraicGeometry.Space

end

