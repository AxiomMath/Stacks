module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkCohomologyMap
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.TorIndependentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkStructureMap
public import StacksFrontier.CategoryTheory.Localization.LeftDerivedByResolutions
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOfSize
public import StacksFrontier.CategoryTheory.Sites.Point.ModuleStalkDerived
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkColimits
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.Iso
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars

/-!
# The geometric stalk of a derived pullback of algebraic spaces

Let `g : X' ⟶ X` be a morphism of algebraic spaces, `x̄'` a geometric point of `X'` and
`x̄ = g(x̄')`.  For `K` in `D(𝒪_X)` the stalk of `Lg^*K` at `x̄'` is the derived base change of
`K_x̄` along `𝒪_{X,x̄} ⟶ 𝒪_{X',x̄'}`:

`K_x̄ ⊗ᴸ_{𝒪_{X,x̄}} 𝒪_{X',x̄'} ⟶ (Lg^*K)_x̄'`.

## Main definitions

* `AlgebraicGeometry.Space.geometricDerivedStalk`: the derived geometric stalk
  `D(𝒪_X) ⥤ D(𝒪_{X,x̄})`.
* `AlgebraicGeometry.Space.derivedPullbackGeometricStalkMap`: the comparison above, as a natural
  transformation of functors `D(𝒪_X) ⥤ D(𝒪_{X',x̄'})`, and
  `AlgebraicGeometry.Space.derivedPullbackGeometricStalkIso` the same as an isomorphism.

## Main results

* `AlgebraicGeometry.Space.isIso_derivedPullbackGeometricStalkMap`: the comparison is an
  isomorphism.
* `AlgebraicGeometry.Space.exists_kFlat_resolution_kFlat_geometricStalks`: every complex of
  `𝒪_X`-modules has a K-flat resolution with flat terms and K-flat geometric stalk complexes.

## Implementation notes

`Lg^* ⋙ (-)_x̄'` is a left derived functor of degreewise pullback followed by the stalk, because
`Lg^*` is computed on K-flat resolutions
(`CategoryTheory.LeftDerivedByResolutions.isLeftDerivedFunctor_postcomp_of_resolutions`).  The
comparison is the lift, along that left derived functor, of the comparison of derived extension
of scalars with degreewise extension of scalars followed by Stacks 05V5 at `x̄'`.  On a complex
of `𝒪_X`-modules it is therefore the composite of those two maps with the counit of `Lg^*`.

## References

* [Stacks Project, Tag 0DKE](https://stacks.math.columbia.edu/tag/0DKE)
* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (IsKFlat hasResolutions_isKFlat)

namespace AlgebraicGeometry.Space

universe u

/- A module imported here brings the global instance
`Stacks.Cohomology.SiteModules.moduleSheavesAbelian` into scope; it gives `Abelian` for these
categories of modules at a universe join that is never the one used here. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
  CategoryTheory.sheafCompose

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {B S hS} {X' X : AlgebraicSpaces B S hS}

/-- The two homomorphisms of geometric stalk rings attached to a morphism of algebraic spaces,
the fibre of its structure map and the stalk ring map of the pullback of modules, coincide: both
are the canonical homomorphism of étale local rings of Stacks 04NG. -/
theorem stalkStructureMap_hom_eq_smallEtaleStalkPullbackRingMap_derived (g : X' ⟶ X)
    (x' : GeometricPoint B S hS X'.1) :
    (stalkStructureMap B S hS g x').hom = smallEtaleStalkPullbackRingMap B S hS g x' := by
  have h₁ := stalkStructureMapAsEtaleLocalRingMap_eq B S hS g x'
  have h₂ := pointStalkRingEquiv_comp_smallEtaleStalkPullbackRingMap B S hS g x'
  refine RingHom.ext fun z => (pointStalkRingEquiv B S hS X' x').injective ?_
  have e₁ : pointStalkRingEquiv B S hS X' x' ((stalkStructureMap B S hS g x').hom z) =
      etaleLocalRingMap X'.2 g.hom x' (pointStalkRingEquiv B S hS X _ z) := by
    have := DFunLike.congr_fun h₁ (pointStalkRingEquiv B S hS X _ z)
    exact (congrArg (fun t => pointStalkRingEquiv B S hS X' x' ((stalkStructureMap B S hS g x').hom
      t)) ((pointStalkRingEquiv B S hS X _).symm_apply_apply z).symm).trans this
  have e₂ : pointStalkRingEquiv B S hS X' x' (smallEtaleStalkPullbackRingMap B S hS g x' z) =
      etaleLocalRingMap X'.2 g.hom x' (pointStalkRingEquiv B S hS X _ z) :=
    DFunLike.congr_fun h₂ z
  exact e₁.trans e₂.symm

variable (g : X' ⟶ X) (x' : GeometricPoint B S hS X'.1)

/-- The derived extension of scalars along the stalk map `𝒪_{X,g(x̄')} ⟶ 𝒪_{X',x̄'}`. -/
abbrev geometricStalkDerivedExtension :
    CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, u, u, u + 1, u + 1}
      (stalkStructureMap B S hS g x').hom :=
  CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (stalkStructureMap B S hS g x').hom

/-- Degreewise pullback along `g` of a complex of `𝒪_X`-modules, followed by the derived
geometric stalk at `x̄'`. -/
abbrev pullbackGeometricStalkOnHomotopy :
    HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
        (ComplexShape.up ℤ) ⥤
      DerivedCategory (ModuleCat.{u} (geometricStalkRing B S hS x')) :=
  smallEtaleModulePullbackOnHomotopy B S hS g ⋙ geometricDerivedStalk B S hS x'

/-- The counit of `Lg^*`, followed by the derived geometric stalk at `x̄'`. -/
abbrev derivedPullbackGeometricStalkCounit :
    DerivedCategory.Qh ⋙ (smallEtaleDerivedModulePullback B S hS g ⋙
        geometricDerivedStalk B S hS x') ⟶
      pullbackGeometricStalkOnHomotopy g x' :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (smallEtaleDerivedModulePullbackComparison B S hS g)
    (geometricDerivedStalk B S hS x')

/-- `Lg^*` followed by the derived geometric stalk at `x̄'` is a left derived functor of
degreewise pullback followed by that stalk: `Lg^*` is computed on K-flat resolutions, so it
stays a left derived functor after composition with any functor. -/
instance isLeftDerivedFunctor_derivedPullbackGeometricStalk :
    (smallEtaleDerivedModulePullback B S hS g ⋙
      geometricDerivedStalk B S hS x').IsLeftDerivedFunctor
      (derivedPullbackGeometricStalkCounit g x') (smallEtaleModuleQuasiIso B S hS X) :=
  LeftDerivedByResolutions.isLeftDerivedFunctor_postcomp_of_resolutions
    (smallEtaleModuleQuasiIso B S hS X) (smallEtaleModuleKFlat B S hS X)
    (hasResolutions_isKFlat (Y := smallEtaleRingedTopos B S hS X))
    (smallEtaleModulePullbackOnHomotopy B S hS g)
    (pullbackInvertsQuasiIso_isKFlat (smallEtaleRingedToposHom B S hS g))
    DerivedCategory.Qh (smallEtaleDerivedModulePullback B S hS g)
    (smallEtaleDerivedModulePullbackComparison B S hS g) (geometricDerivedStalk B S hS x')

/-- The derived geometric stalk at `g(x̄')`, followed by derived extension of scalars, on a
complex of `𝒪_X`-modules: the derived extension of scalars of its stalk complex. -/
def derivedExtensionGeometricStalkComplexIso :
    HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⋙
        geometricDerivedStalk B S hS (geometricPointMap g.hom x') ⋙
          (geometricStalkDerivedExtension g x').functor ≅
      (Stacks.sheafModuleFiberOfCommRing
          (etaleSitePoint B S hS X.1 (geometricPointMap g.hom x') X.2)
          (smallEtaleRingedTopos B S hS X).O).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ⋙ (geometricStalkDerivedExtension g x').functor :=
  haveI := Stacks.instAdditiveSheafModuleFiberOfCommRing
    (etaleSitePoint B S hS X.1 (geometricPointMap g.hom x') X.2) (smallEtaleRingedTopos B S hS X).O
  Functor.isoWhiskerRight
      (DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
      (geometricDerivedStalk B S hS (geometricPointMap g.hom x') ⋙
        (geometricStalkDerivedExtension g x').functor) ≪≫
    Functor.isoWhiskerRight (Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS X.1 (geometricPointMap g.hom x') X.2)
        (smallEtaleRingedTopos B S hS X).O).mapDerivedCategoryFactors
      (geometricStalkDerivedExtension g x').functor

/-- **Stacks 05V5 at `x̄'`, in the derived category.**  Degreewise extension of scalars of the
stalk complex at `g(x̄')` is the stalk complex at `x̄'` of the degreewise pullback, read in the
derived category. -/
def extensionGeometricStalkComplexIso :
    (Stacks.sheafModuleFiberOfCommRing
          (etaleSitePoint B S hS X.1 (geometricPointMap g.hom x') X.2)
          (smallEtaleRingedTopos B S hS X).O).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexGeneral.{u, u, u, u + 1}
          (stalkStructureMap B S hS g x').hom ≅
      HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙ pullbackGeometricStalkOnHomotopy g x' :=
  haveI := Stacks.instAdditiveSheafModuleFiberOfCommRing (etaleSitePoint B S hS X'.1 x' X'.2)
    (smallEtaleRingedTopos B S hS X').O
  haveI := Stacks.instAdditiveSheafModuleFiberOfCommRing
    (etaleSitePoint B S hS X.1 (geometricPointMap g.hom x') X.2) (smallEtaleRingedTopos B S hS X).O
  eqToIso (congrArg (fun φ => (Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS X.1 (geometricPointMap g.hom x') X.2)
        (smallEtaleRingedTopos B S hS X).O).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          (ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            DerivedCategory.Q)
      (stalkStructureMap_hom_eq_smallEtaleStalkPullbackRingMap_derived g x')) ≪≫
    Functor.isoWhiskerRight (pullbackStalkComplexNatIso g x').symm DerivedCategory.Q ≪≫
    Functor.isoWhiskerLeft
      ((smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules.mapHomologicalComplex
        (ComplexShape.up ℤ))
      (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X'.1 x' X'.2)
        (smallEtaleRingedTopos B S hS X').O).mapDerivedCategoryFactors.symm ≪≫
    Functor.isoWhiskerLeft
      ((smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules.mapHomologicalComplex
        (ComplexShape.up ℤ)) (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso _).symm
        (geometricDerivedStalk B S hS x')) ≪≫
    Functor.isoWhiskerRight
      ((smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules.mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).symm (DerivedCategory.Qh ⋙ geometricDerivedStalk B S hS x')

/-- The comparison, on complexes of `𝒪_X`-modules, from the derived base change of the stalk
complex at `g(x̄')` to the stalk at `x̄'` of the degreewise pullback: the comparison of derived
with degreewise extension of scalars, followed by Stacks 05V5 at `x̄'`. -/
def derivedPullbackGeometricStalkComplexMap :
    HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⋙
        geometricDerivedStalk B S hS (geometricPointMap g.hom x') ⋙
          (geometricStalkDerivedExtension g x').functor ⟶
      HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙ pullbackGeometricStalkOnHomotopy g x' :=
  (derivedExtensionGeometricStalkComplexIso g x').hom ≫
    Functor.whiskerLeft ((Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS X.1 (geometricPointMap g.hom x') X.2)
        (smallEtaleRingedTopos B S hS X).O).mapHomologicalComplex (ComplexShape.up ℤ))
      (geometricStalkDerivedExtension g x').comparison ≫
    (extensionGeometricStalkComplexIso g x').hom

/-- The comparison on complexes is invertible at a complex whose stalk complex at `g(x̄')` is
K-flat. -/
theorem isIso_derivedPullbackGeometricStalkComplexMap_app
    (P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hst : (stalkComplex (geometricPointMap g.hom x') P).KFlat) :
    IsIso ((derivedPullbackGeometricStalkComplexMap g x').app P) := by
  have := (geometricStalkDerivedExtension g x').comparison_isIso_of_kFlat _ hst
  rw [derivedPullbackGeometricStalkComplexMap, NatTrans.comp_app, NatTrans.comp_app]
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' this inferInstance)

/-- The comparison `derivedPullbackGeometricStalkComplexMap`, on the homotopy category. -/
def derivedPullbackGeometricStalkHomotopyMap :
    DerivedCategory.Qh ⋙ (geometricDerivedStalk B S hS (geometricPointMap g.hom x') ⋙
        (geometricStalkDerivedExtension g x').functor) ⟶
      pullbackGeometricStalkOnHomotopy g x' :=
  CategoryTheory.Quotient.natTransLift _ (derivedPullbackGeometricStalkComplexMap g x')

/-- **The derived pullback-stalk comparison.**  For a morphism `g : X' ⟶ X` of algebraic spaces
and a geometric point `x̄'` of `X'`, the canonical map

`K_{g(x̄')} ⊗ᴸ_{𝒪_{X,g(x̄')}} 𝒪_{X',x̄'} ⟶ (Lg^*K)_x̄'`,

natural in `K ∈ D(𝒪_X)`.  On a complex it is the comparison of derived with degreewise extension
of scalars followed by Stacks 05V5 at `x̄'`, read through the counit of `Lg^*`. -/
def derivedPullbackGeometricStalkMap :
    geometricDerivedStalk B S hS (geometricPointMap g.hom x') ⋙
        (geometricStalkDerivedExtension g x').functor ⟶
      smallEtaleDerivedModulePullback B S hS g ⋙ geometricDerivedStalk B S hS x' :=
  (smallEtaleDerivedModulePullback B S hS g ⋙ geometricDerivedStalk B S hS x').leftDerivedLift
    (derivedPullbackGeometricStalkCounit g x') (smallEtaleModuleQuasiIso B S hS X) _
    (derivedPullbackGeometricStalkHomotopyMap g x')

/-- The derived pullback-stalk comparison followed by the counit of `Lg^*` is the comparison on
complexes; this characterizes it. -/
theorem derivedPullbackGeometricStalkMap_fac
    (K : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
      (ComplexShape.up ℤ)) :
    (derivedPullbackGeometricStalkMap g x').app (DerivedCategory.Qh.obj K) ≫
        (derivedPullbackGeometricStalkCounit g x').app K =
      (derivedPullbackGeometricStalkHomotopyMap g x').app K :=
  Functor.leftDerived_fac_app _ _ _ _ _ K

/-- The comparison on the homotopy category, at the class of a complex. -/
theorem derivedPullbackGeometricStalkHomotopyMap_app
    (P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) :
    (derivedPullbackGeometricStalkHomotopyMap g x').app ((HomotopyCategory.quotient _ _).obj P) =
      (derivedPullbackGeometricStalkComplexMap g x').app P :=
  rfl

/-- The derived pullback-stalk comparison is invertible at a K-flat complex with flat terms whose
stalk complex at `g(x̄')` is K-flat. -/
theorem isIso_derivedPullbackGeometricStalkMap_app_of_kFlat
    (P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hP : smallEtaleModuleKFlat B S hS X ((HomotopyCategory.quotient _ _).obj P))
    (hst : (stalkComplex (geometricPointMap g.hom x') P).KFlat) :
    IsIso ((derivedPullbackGeometricStalkMap g x').app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P))) := by
  have hc : IsIso ((derivedPullbackGeometricStalkCounit g x').app
      ((HomotopyCategory.quotient _ _).obj P)) := by
    have := isIso_smallEtaleDerivedModulePullbackComparison_app B S hS g _ hP
    rw [derivedPullbackGeometricStalkCounit, NatTrans.comp_app, Functor.whiskerRight_app]
    infer_instance
  have hm := isIso_derivedPullbackGeometricStalkComplexMap_app g x' P hst
  rw [← derivedPullbackGeometricStalkHomotopyMap_app,
    ← derivedPullbackGeometricStalkMap_fac g x' ((HomotopyCategory.quotient _ _).obj P)] at hm
  exact IsIso.of_isIso_comp_right _ ((derivedPullbackGeometricStalkCounit g x').app _)

section Resolutions

variable (X) in
/-- **K-flat resolutions with K-flat geometric stalks.**  Every complex of `𝒪_X`-modules receives
a quasi-isomorphism from a K-flat complex with flat terms whose stalk complex at every geometric
point is K-flat: the colimit of the ladder of Stacks 06YS, a sequential colimit of bounded above
complexes of flat modules, whose stalk complexes are sequential colimits of bounded above
complexes of flat modules. -/
theorem exists_kFlat_resolution_kFlat_geometricStalks
    (M : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) :
    ∃ (P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
      (s : P ⟶ M), QuasiIso s ∧
      smallEtaleModuleKFlat B S hS X ((HomotopyCategory.quotient _ _).obj P) ∧
      ∀ x : GeometricPoint B S hS X.1, (stalkComplex x P).KFlat := by
  obtain ⟨D, s, hLE, hflat, hqis, -⟩ :=
    Stacks.SheafOfModules.KFlatResolution.exists_resolution_colimit_ofSize
      (smallEtaleRingedTopos B S hS X).O M
  have := Stacks.SheafOfModules.KFlatResolution.hasColimitsOfShape_nat_ofSize
    (smallEtaleRingedTopos B S hS X).O
  refine ⟨colimit D, s, hqis,
    ⟨Stacks.SheafOfModules.KFlatResolution.kFlat_colimit_of_isStrictlyLE_of_isFlat_ofSize _ D hLE
      hflat, Stacks.SheafOfModules.KFlatResolution.isFlat_colimit_X_ofSize _ D hflat⟩,
    fun x => ?_⟩
  have : Functor.Additive
      (C := SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
      (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O) :=
    Stacks.additive_sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
      (smallEtaleRingedTopos B S hS X).O
  have : PreservesColimitsOfSize.{0, 0}
      (C := SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
      (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O) :=
    Stacks.preservesColimits_sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
      (smallEtaleRingedTopos B S hS X).O
  have := CochainComplex.KFlat.preservesColimit_mapHomologicalComplex D
    (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
      (smallEtaleRingedTopos B S hS X).O)
  have hstage : ∀ n : ℕ, CochainComplex.KFlat.{u, u}
      ((D ⋙ (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O).mapHomologicalComplex (ComplexShape.up ℤ)).obj n) := by
    intro n
    obtain ⟨b, hb⟩ := hLE n
    exact kFlat_stalkComplex x (D.obj n) b hb (hflat n)
  exact CochainComplex.KFlat.of_iso
    (preservesColimitIso ((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
      (smallEtaleRingedTopos B S hS X).O).mapHomologicalComplex (ComplexShape.up ℤ)) D).symm
    (CochainComplex.KFlat.kFlat_colimit.{u, 0, 0, u} _ hstage)

end Resolutions

/-- **The derived pullback-stalk comparison is an isomorphism**: it is one at the resolutions
of `exists_kFlat_resolution_kFlat_geometricStalks`, which represent every object. -/
instance isIso_derivedPullbackGeometricStalkMap :
    IsIso (derivedPullbackGeometricStalkMap g x') := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  obtain ⟨M, ⟨e⟩⟩ : ∃ M : CochainComplex _ ℤ, Nonempty (DerivedCategory.Q.obj M ≅ K) :=
    ⟨_, ⟨(DerivedCategory.Q.objObjPreimageIso K)⟩⟩
  obtain ⟨P, s, hs, hP, hst⟩ := exists_kFlat_resolution_kFlat_geometricStalks X M
  have h₁ := isIso_derivedPullbackGeometricStalkMap_app_of_kFlat g x' P hP
    (hst (geometricPointMap g.hom x'))
  have e' : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P) ≅ K :=
    (DerivedCategory.quotientCompQhIso _).app P ≪≫ asIso (DerivedCategory.Q.map s) ≪≫ e
  exact (NatTrans.isIso_app_iff_of_iso _ e').1 h₁

/-- **The geometric stalk of a derived pullback.**  For a morphism `g : X' ⟶ X` of algebraic
spaces and a geometric point `x̄'` of `X'`,

`(Lg^*K)_x̄' ≅ K_{g(x̄')} ⊗ᴸ_{𝒪_{X,g(x̄')}} 𝒪_{X',x̄'}`,

naturally in `K ∈ D(𝒪_X)`. -/
def derivedPullbackGeometricStalkIso :
    geometricDerivedStalk B S hS (geometricPointMap g.hom x') ⋙
        (geometricStalkDerivedExtension g x').functor ≅
      smallEtaleDerivedModulePullback B S hS g ⋙ geometricDerivedStalk B S hS x' :=
  asIso (derivedPullbackGeometricStalkMap g x')

end AlgebraicGeometry.Space

end
