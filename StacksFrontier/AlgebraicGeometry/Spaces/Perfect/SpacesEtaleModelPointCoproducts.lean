module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedGlobalSectionsCoproducts
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelToPointPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GrothendieckAbelian
public import StacksFrontier.Homology.DerivedComplete.CompleteRestrictScalarsEquivalence

/-!
# The direct image to the point commutes with direct sums in `D_QCoh`

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S` and
`φ : R →+* Γ(X, 𝒪_X)` a ring map, that is a morphism `f : X ⟶ Spec(R)`, presented as the
morphism of ringed topoi `AlgebraicGeometry.Space.spacesEtaleModelToBaseRing` from the spaces-étale
model of `X` to the punctual ringed topos `(pt, R)`. This file shows that every right derived
functor `Rf_*` of its direct image commutes with direct sums of families whose images in
`D(𝒪_X)` have quasi-coherent cohomology. This is [Stacks, Tag 08FB] for the morphism from `X` to
a point, read on the spaces-étale model where [Stacks, Tag 08IN] is set up.

The proof transports
`AlgebraicGeometry.Space.isIso_sigmaComparison_rightDerived_baseRingGlobalSections` across the
equivalence of the modules on the model with the `𝒪_X`-modules and across the identification of
`f_*` followed by the sections at the point with global sections
(`AlgebraicGeometry.Space.pushforwardToBaseRingIso`); the passage from `R`-modules to abelian
groups is exact, conservative and commutes with direct sums.

## Main results

* `AlgebraicGeometry.Space.isRightDerivedFunctor_pointTransport`: transported, `Rf_*` followed by
  the abelian groups at the point is a right derived functor of global sections on `X`.
* `AlgebraicGeometry.Space.isIso_sigmaComparison_spacesEtaleModelToBaseRing`: the direct-sum
  statement.

## References

* [Stacks Project, Tag 08FB](https://stacks.math.columbia.edu/tag/08FB)
* [Stacks Project, Tag 08IN](https://stacks.math.columbia.edu/tag/08IN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] HasDerivedCategory.standard
attribute [-instance] SheafOfModules.hasColimitsOfShape_discrete_derivedCategory
attribute [local instance] hasCoproducts_derivedCategory_modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)
  {R : Type u} [CommRing R] (φ : R →+* modelGlobalFunctions B S hS X)

/-- The modules on the punctual ringed topos of `R` are the `R`-modules: sections at the point. -/
def baseRingPointModulesEquiv :
    (pointRingedTopos (CommRingCat.of R)).Modules ≌ ModuleCat.{u} R :=
  (Stacks.PointRingedSite.modulesEquiv (CommRingCat.of R)).trans (pointModuleCatEquiv (R := R))

/-- The abelian group underlying a module on the punctual ringed topos of `R`: its sections at
the point, as an `R`-module, forgetting the module structure. -/
abbrev pointAddCommGrp :
    (pointRingedTopos (CommRingCat.of R)).Modules ⥤ AddCommGrpCat.{u} :=
  (baseRingPointModulesEquiv (R := R)).functor ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}

/-- An additive natural isomorphism induces one on homotopy categories. -/
def mapHomotopyCategoryIsoOfIso {V W : Type*} [Category* V] [Preadditive V] [Category* W]
    [Preadditive W] {F G : V ⥤ W} [F.Additive] [G.Additive] (e : F ≅ G) :
    F.mapHomotopyCategory (ComplexShape.up ℤ) ≅ G.mapHomotopyCategory (ComplexShape.up ℤ) where
  hom := NatTrans.mapHomotopyCategory e.hom _
  inv := NatTrans.mapHomotopyCategory e.inv _
  hom_inv_id := by
    rw [← NatTrans.mapHomotopyCategory_comp, Iso.hom_inv_id, NatTrans.mapHomotopyCategory_id]
  inv_hom_id := by
    rw [← NatTrans.mapHomotopyCategory_comp, Iso.inv_hom_id, NatTrans.mapHomotopyCategory_id]

section Instances

/-- The inverse of the equivalence of the modules on the model with the `𝒪_X`-modules is left
exact. -/
instance preservesFiniteLimits_spacesEtaleModelModulesEquiv_inverse :
    PreservesFiniteLimits (spacesEtaleModelModulesEquiv B S hS X).inverse :=
  @PreservesLimitsOfSize.preservesFiniteLimits.{0, 0} _ _ _ _ _
    (spacesEtaleModelModulesEquiv B S hS X).toAdjunction.rightAdjoint_preservesLimits

/-- The inverse of the equivalence of the modules on the model with the `𝒪_X`-modules is right
exact. -/
instance preservesFiniteColimits_spacesEtaleModelModulesEquiv_inverse :
    PreservesFiniteColimits (spacesEtaleModelModulesEquiv B S hS X).inverse :=
  @PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _ _ _ _ _
    (spacesEtaleModelModulesEquiv B S hS X).symm.toAdjunction.leftAdjoint_preservesColimits

/-- The inverse of the equivalence of the modules on the model with the `𝒪_X`-modules is
additive. -/
instance additive_spacesEtaleModelModulesEquiv_inverse :
    (spacesEtaleModelModulesEquiv B S hS X).inverse.Additive :=
  haveI : PreservesBinaryBiproducts (spacesEtaleModelModulesEquiv B S hS X).inverse :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  Functor.additive_of_preservesBinaryBiproducts _

/-- The equivalence of the modules on the model with the `𝒪_X`-modules is left exact. -/
instance preservesFiniteLimits_spacesEtaleModelModulesEquiv_functor :
    PreservesFiniteLimits (spacesEtaleModelModulesEquiv B S hS X).functor :=
  @PreservesLimitsOfSize.preservesFiniteLimits.{0, 0} _ _ _ _ _
    (spacesEtaleModelModulesEquiv B S hS X).symm.toAdjunction.rightAdjoint_preservesLimits

/-- The equivalence of the modules on the model with the `𝒪_X`-modules is right exact. -/
instance preservesFiniteColimits_spacesEtaleModelModulesEquiv_functor :
    PreservesFiniteColimits (spacesEtaleModelModulesEquiv B S hS X).functor :=
  @PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _ _ _ _ _
    (spacesEtaleModelModulesEquiv B S hS X).toAdjunction.leftAdjoint_preservesColimits

/-- The equivalence of the modules on the model with the `𝒪_X`-modules is additive. -/
instance additive_spacesEtaleModelModulesEquiv_functor :
    (spacesEtaleModelModulesEquiv B S hS X).functor.Additive :=
  haveI : PreservesBinaryBiproducts (spacesEtaleModelModulesEquiv B S hS X).functor :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  Functor.additive_of_preservesBinaryBiproducts _

/-- The abelian group at the point is a left exact functor. -/
instance preservesFiniteLimits_pointAddCommGrp :
    PreservesFiniteLimits (pointAddCommGrp (R := R)) :=
  haveI : PreservesFiniteLimits (baseRingPointModulesEquiv (R := R)).functor :=
    @PreservesLimitsOfSize.preservesFiniteLimits.{0, 0} _ _ _ _ _
      (baseRingPointModulesEquiv (R := R)).symm.toAdjunction.rightAdjoint_preservesLimits
  comp_preservesFiniteLimits _ _

/-- The abelian group at the point is a right exact functor. -/
instance preservesFiniteColimits_pointAddCommGrp :
    PreservesFiniteColimits (pointAddCommGrp (R := R)) :=
  haveI : PreservesFiniteColimits (baseRingPointModulesEquiv (R := R)).functor :=
    @PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _ _ _ _ _
      (baseRingPointModulesEquiv (R := R)).toAdjunction.leftAdjoint_preservesColimits
  comp_preservesFiniteColimits _ _

/-- The abelian group at the point is additive. -/
instance additive_pointAddCommGrp : (pointAddCommGrp (R := R)).Additive :=
  haveI : PreservesBinaryBiproducts (baseRingPointModulesEquiv (R := R)).functor :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  haveI : (baseRingPointModulesEquiv (R := R)).functor.Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  inferInstance

end Instances

/-- Direct image to the point followed by the abelian group at the point is global sections of
the corresponding `𝒪_X`-module (`AlgebraicGeometry.Space.pushforwardToBaseRingIso`). -/
def pushforwardPointAddCommGrpIso :
    (spacesEtaleModelModulesEquiv B S hS X).inverse ⋙
        (spacesEtaleModelToBaseRing B S hS X φ).pushforwardTopos ⋙ pointAddCommGrp (R := R) ≅
      baseRingGlobalSectionsAddCommGrp B S hS X φ :=
  Functor.isoWhiskerLeft (spacesEtaleModelModulesEquiv B S hS X).inverse
      (Functor.isoWhiskerRight (pushforwardToBaseRingIso B S hS X φ)
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})) ≪≫
    Functor.isoWhiskerRight (spacesEtaleModelModulesEquiv B S hS X).counitIso
      (baseRingGlobalSectionsAddCommGrp B S hS X φ)

section Transport

variable (Rf : DerivedCategory (spacesEtaleModelRingedTopos B S hS X).Modules ⥤
    DerivedCategory (pointRingedTopos (CommRingCat.of R)).Modules)
  (αf : (spacesEtaleModelToBaseRing B S hS X φ).pushforwardTopos.mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf)

/-- The unit exhibiting `Rf_*`, transported to `𝒪_X`-modules and followed by the abelian groups
at the point, as a right derived functor of global sections on `X`. -/
def pointTransportUnit :
    (baseRingGlobalSectionsAddCommGrp B S hS X φ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ ((spacesEtaleModelModulesEquiv B S hS X).inverse.mapDerivedCategory ⋙
        Rf ⋙ (pointAddCommGrp (R := R)).mapDerivedCategory) :=
  Functor.whiskerRight (mapHomotopyCategoryIsoOfIso
      (pushforwardPointAddCommGrpIso B S hS X φ).symm).hom DerivedCategory.Qh ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl _)
      (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
    Functor.whiskerLeft ((spacesEtaleModelModulesEquiv B S hS X).inverse.mapHomotopyCategory
      (ComplexShape.up ℤ))
      (Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl _)
          (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
        Functor.whiskerLeft
          ((spacesEtaleModelToBaseRing B S hS X φ).pushforwardTopos.mapHomotopyCategory
            (ComplexShape.up ℤ)) (pointAddCommGrp (R := R)).mapDerivedCategoryFactorsh.inv ≫
        Functor.whiskerRight αf (pointAddCommGrp (R := R)).mapDerivedCategory) ≫
    Functor.whiskerRight
      (spacesEtaleModelModulesEquiv B S hS X).inverse.mapDerivedCategoryFactorsh.inv
      (Rf ⋙ (pointAddCommGrp (R := R)).mapDerivedCategory)

/-- **`Rf_*`, transported to `𝒪_X`-modules and followed by the abelian groups at the point, is a
right derived functor of global sections on `X`.** At a K-injective complex `I` of `𝒪_X`-modules
the unit is that of `Rf_*` at the K-injective complex `E⁻¹(I)` up to isomorphisms. -/
theorem isRightDerivedFunctor_pointTransport
    [Rf.IsRightDerivedFunctor αf (HomotopyCategory.quasiIso
      (spacesEtaleModelRingedTopos B S hS X).Modules (ComplexShape.up ℤ))] :
    ((spacesEtaleModelModulesEquiv B S hS X).inverse.mapDerivedCategory ⋙
        Rf ⋙ (pointAddCommGrp (R := R)).mapDerivedCategory).IsRightDerivedFunctor
      (pointTransportUnit B S hS X φ Rf αf)
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) := by
  have hgr : IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS X.1 X.2) :=
    isGrothendieckAbelian_modules B S hS X.1 X.2
  have hgrM : IsGrothendieckAbelian.{u} (spacesEtaleModelRingedTopos B S hS X).Modules :=
    SheafOfModules.isGrothendieckAbelianU _
  refine Stacks.Cohomology.UnboundedComplexes.isRightDerivedFunctor_of_isIso_app_isKInjective
    _ DerivedCategory.Qh _ _ fun I hI ↦ ?_
  have hEI : CochainComplex.IsKInjective
      (((spacesEtaleModelModulesEquiv B S hS X).inverse.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) :=
    have := hI
    CochainComplex.isKInjective_mapHomologicalComplex_of_exact
      (spacesEtaleModelModulesEquiv B S hS X).inverse
      (spacesEtaleModelModulesEquiv B S hS X).functor
      (spacesEtaleModelModulesEquiv B S hS X).toAdjunction I
  have : IsIso (αf.app (((spacesEtaleModelModulesEquiv B S hS X).inverse.mapHomotopyCategory
      (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := by
    obtain ⟨Rs⟩ := Stacks.Injectives.exists_functorial_quasiIso_isKInjective.{u}
      (spacesEtaleModelRingedTopos B S hS X).Modules
    exact (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      ((spacesEtaleModelToBaseRing B S hS X φ).pushforwardTopos.mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (fun K ↦ ⟨Rs.functor.obj K, Rs.inclusion.app K, Rs.isKInjective K, Rs.quasiIso K⟩)).2
        DerivedCategory.Qh Rf αf _ hEI
  simp only [pointTransportUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  infer_instance

/-- **Stacks 08FB for the morphism from a quasi-compact quasi-separated algebraic space to the
point `(pt, R)`, on the spaces-étale model.** Every right derived functor `Rf_*` of the direct
image along `AlgebraicGeometry.Space.spacesEtaleModelToBaseRing` commutes with the direct sum of
every family of objects whose images in `D(𝒪_X)` have quasi-coherent cohomology. -/
theorem isIso_sigmaComparison_spacesEtaleModelToBaseRing (hZ : B.Contains (⊤_ Scheme.{u}))
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    [Rf.IsRightDerivedFunctor αf (HomotopyCategory.quasiIso
      (spacesEtaleModelRingedTopos B S hS X).Modules (ComplexShape.up ℤ))]
    {J : Type u} (K : J → DerivedCategory (spacesEtaleModelRingedTopos B S hS X).Modules)
    (hK : ∀ j, qcohDerivedProp B S hS X
      ((spacesEtaleModelModulesEquiv B S hS X).functor.mapDerivedCategory.obj (K j))) :
    IsIso (sigmaComparison Rf K) := by
  have hgrM : IsGrothendieckAbelian.{u} (spacesEtaleModelRingedTopos B S hS X).Modules :=
    SheafOfModules.isGrothendieckAbelianU _
  have hgrP : IsGrothendieckAbelian.{u} (pointRingedTopos (CommRingCat.of R)).Modules :=
    SheafOfModules.isGrothendieckAbelianU _
  have := Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory
    (spacesEtaleModelRingedTopos B S hS X).Modules J
  have := Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory
    (pointRingedTopos (CommRingCat.of R)).Modules J
  have := Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory
    AddCommGrpCat.{u} J
  let E := spacesEtaleModelModulesEquiv B S hS X
  let Ed := E.inverse.mapDerivedCategory
  let Wd := (pointAddCommGrp (R := R)).mapDerivedCategory
  have := isRightDerivedFunctor_pointTransport B S hS X φ Rf αf
  have h₁ := isIso_sigmaComparison_rightDerived_baseRingGlobalSections B S hS hZ hXqc hXqs φ
    (Ed ⋙ Rf ⋙ Wd) (pointTransportUnit B S hS X φ Rf αf)
    (fun j ↦ E.functor.mapDerivedCategory.obj (K j)) hK
  -- `E⁻¹` is an equivalence of derived categories, so commutes with direct sums
  let Eder := Stacks.DerivedGlueing.mapDerivedCategoryEquivalence E.functor E.inverse
    E.unitIso E.counitIso
  have hEd : IsIso (sigmaComparison Ed fun j ↦ E.functor.mapDerivedCategory.obj (K j)) := by
    have : PreservesColimitsOfShape (Discrete J) Ed :=
      inferInstanceAs (PreservesColimitsOfShape (Discrete J) Eder.inverse)
    exact isIso_sigmaComparison_of_preservesColimit _ _ inferInstance
  rw [sigmaComparison_comp] at h₁
  have h₂ : IsIso (sigmaComparison (Rf ⋙ Wd)
      fun j ↦ Ed.obj (E.functor.mapDerivedCategory.obj (K j))) :=
    IsIso.of_isIso_comp_right _ ((Rf ⋙ Wd).map
      (sigmaComparison Ed fun j ↦ E.functor.mapDerivedCategory.obj (K j)))
  have h₃ : IsIso (sigmaComparison (Rf ⋙ Wd) K) := by
    have := preservesColimit_discreteFunctor_of_isIso_sigmaComparison _ _ h₂
    exact isIso_sigmaComparison_of_preservesColimit _ K
      (preservesColimit_of_iso_diagram (Rf ⋙ Wd)
        (K₁ := Discrete.functor fun j ↦ Ed.obj (E.functor.mapDerivedCategory.obj (K j)))
        (Discrete.natIso fun j ↦ (Eder.unitIso.app (K j.as)).symm))
  -- the abelian groups at the point detect isomorphisms and commute with direct sums
  have hW : PreservesColimitsOfShape (Discrete J) Wd := by
    have := Stacks.SmallDerivedCategory.derivedCategoryQ_preservesCoproducts
      (pointRingedTopos (CommRingCat.of R)).Modules J
    have := Stacks.SmallDerivedCategory.derivedCategoryQ_preservesCoproducts AddCommGrpCat.{u} J
    have : PreservesColimitsOfShape (Discrete J)
        (DerivedCategory.Q ⋙ (pointAddCommGrp (R := R)).mapDerivedCategory) :=
      (preservesColimitsOfShape_iff_of_natIso
        (pointAddCommGrp (R := R)).mapDerivedCategoryFactors).2 inferInstance
    exact preservesColimitsOfShape_discrete_of_essSurj_comp DerivedCategory.Q
      (pointAddCommGrp (R := R)).mapDerivedCategory J
  exact isIso_sigmaComparison_of_isIso_comp Rf Wd K
    (CompleteRestrictScalarsEquivalence.reflectsIsomorphisms_mapDerivedCategory _) h₃
    (isIso_sigmaComparison_of_preservesColimit _ _ inferInstance)

end Transport

end AlgebraicGeometry.Space

end
