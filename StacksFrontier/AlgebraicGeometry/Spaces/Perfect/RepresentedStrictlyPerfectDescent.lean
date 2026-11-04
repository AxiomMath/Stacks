module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationAffineRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherentCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.RingedSiteComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RetractOfAPerfectObject

/-!
# A strictly perfect complex on a represented algebraic space comes from its scheme

Let `X = h_U` be the algebraic space represented by an object `U` of the big fppf site over a
scheme `S`, with underlying scheme `T`, and let `ε^* : D(𝒪_T) ⥤ D(𝒪_{h_U})` be the comparison
functor. A globally strictly perfect complex `K` on the small étale site of `h_U` is `ε^*` of a
strictly perfect complex of `𝒪_T`-modules.

## Main results

* `SheafOfModules.isStrictlyPerfect_mapHomologicalComplex_of_additive`: an additive functor of
  sheaves of modules carrying the unit to the unit carries strictly perfect complexes to strictly
  perfect complexes.
* `AlgebraicGeometry.SmallEtale.isStrictlyPerfect_restrictModule`: restriction from the small
  étale site of a scheme to its small Zariski site preserves strictly perfect complexes.
* `AlgebraicGeometry.Space.exists_isPerfect_representedDerivedAssociatedModule_iso`: a strictly
  perfect complex on the small étale site of `h_U` is `ε^*` of a perfect object of `D(𝒪_T)`.

## References

* [Stacks Project, Tag 08HG](https://stacks.math.columbia.edu/tag/08HG)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w u₁ u₂ v₁ v₂

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D} {S : Sheaf K RingCat.{w}}
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- An additive functor of sheaves of modules carrying the unit to the unit carries strictly
perfect complexes to strictly perfect complexes. -/
theorem isStrictlyPerfect_mapHomologicalComplex_of_additive
    (F : SheafOfModules.{w} R ⥤ SheafOfModules.{w} S) [F.Additive]
    (η : unit S ≅ F.obj (unit R)) {P : CochainComplex (SheafOfModules.{w} R) ℤ}
    (hP : IsStrictlyPerfect R P) :
    IsStrictlyPerfect S ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) := by
  refine ⟨hP.bounded.subset fun i hi hz => hi (F.map_isZero hz), fun i => ?_⟩
  obtain ⟨n, j, r, hjr⟩ :=
    (isDirectSummandOfFiniteFree_iff_free R (P.X i)).mp (hP.termDirectSummand i)
  have : PreservesColimitsOfShape (Discrete (ULift.{w} (Fin n))) F :=
    preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift.symm) F
  let e := SheafOfModules.mapFreeIso F (ULift.{w} (Fin n)) η
  refine (isDirectSummandOfFiniteFree_iff_free S _).mpr ⟨n, F.map j ≫ e.inv, e.hom ≫ F.map r, ?_⟩
  rw [Category.assoc, e.inv_hom_id_assoc, ← Functor.map_comp, hjr, CategoryTheory.Functor.map_id]
  rfl

end SheafOfModules

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The comparison of structure sheaves along the inclusion of the small Zariski site of `S` into
its small étale site is an isomorphism. -/
instance isIso_structureMap :
    IsIso (C := Sheaf (Opens.grothendieckTopology S) RingCat.{u}) (structureMap B S hS) := by
  have : ∀ U, IsIso ((structureMap B S hS).hom.app U) := isIso_structureMap_hom_app B S hS
  have : IsIso ((sheafToPresheaf _ RingCat.{u}).map (structureMap B S hS)) :=
    NatIso.isIso_of_isIso_app (structureMap B S hS).hom
  exact (fullyFaithfulSheafToPresheaf _ RingCat.{u}).isIso_of_isIso_map _

/-- Restriction to the small Zariski site carries the structure sheaf to the structure sheaf. -/
def restrictModuleUnitIso :
    SheafOfModules.unit S.ringCatSheaf ≅
      (restrictModule B S hS).obj (SheafOfModules.unit (structureSheaf B S hS)) :=
  @asIso _ _ _ _ (SheafOfModules.unitToPushforwardObjUnit (structureMap B S hS))
    (Stacks.SheafOfModules.isIso_unitToPushforwardObjUnit (structureMap B S hS))

attribute [local instance] hasSheafify_smallEtale wEqualsLocallyBijective_smallEtale

/-- Restriction from the small étale site to the small Zariski site preserves strictly perfect
complexes, read as strictly perfect complexes of `𝒪_S`-modules on the ringed space `S`. -/
theorem isStrictlyPerfect_restrictModule
    {K : CochainComplex (SheafOfModules.{u} (structureSheaf B S hS)) ℤ}
    (hK : IsStrictlyPerfect (structureSheaf B S hS) K) :
    StrictlyPerfect.IsStrictlyPerfect (X := S.toRingedSpace)
      (((restrictModule B S hS).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  (RingedSpace.PseudoCoherence.isStrictlyPerfect_iff S.toRingedSpace _).2
    (SheafOfModules.isStrictlyPerfect_mapHomologicalComplex_of_additive (restrictModule B S hS)
      (restrictModuleUnitIso B S hS) hK)

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] SmallEtale.preservesFiniteLimits_associatedModule

attribute [local instance 10000] SmallEtale.hasSheafify_smallEtale
  SmallEtale.wEqualsLocallyBijective_smallEtale smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective

attribute [local instance 10000] modulesAbelianAtSchemeUniverse modulesHasDerivedCategory

/-- The transport of modules from the small étale site of `h_U` to the small étale site of its
scheme carries the structure sheaf to the structure sheaf. -/
def representedModuleRestrictionUnitIso :
    (representedModuleRestriction B S hS U).obj
        (SheafOfModules.unit (ringStructureSheaf B S hS (yoneda.obj U))) ≅
      SheafOfModules.unit (_root_.AlgebraicGeometry.SmallEtale.structureSheaf
        (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property) :=
  (@asIso _ _ _ _
    (SheafOfModules.unitToPushforwardObjUnit (representedStructureMapInverse B S hS U))
    (Stacks.SheafOfModules.isIso_unitToPushforwardObjUnit
      (representedStructureMapInverse B S hS U))).symm

/-- A strictly perfect complex on the small étale site of `h_U` is `ε^*` of a perfect object of
`D(𝒪_T)`, where `T` is the scheme underlying `U`. -/
theorem exists_isPerfect_representedDerivedAssociatedModule_iso
    (K : CochainComplex (Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)) ℤ)
    (hK : IsStrictlyPerfect (ringStructureSheaf B S hS (yoneda.obj U)) K) :
    ∃ P₀ : DerivedCategory.{u + 1} ((BigFppfOver.toScheme B S hS).obj U).Modules,
      Stacks.Cohomology.PerfectComplexes.IsPerfect
          (X := ((BigFppfOver.toScheme B S hS).obj U).toRingedSpace) P₀ ∧
        Nonempty ((representedDerivedAssociatedModule B S hS U).obj P₀ ≅
          DerivedCategory.Q.obj K) := by
  let T := (BigFppfOver.toScheme B S hS).obj U
  let eqv := representedModuleEquivalence.{u, u} B S hS U
  let R := eqv.inverse
  let G := SmallEtale.restrictModule (associatedBigEtaleSite B) T U.left.property
  let A := SmallEtale.associatedModule (associatedBigEtaleSite B) T U.left.property
  let adj := SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite B) T U.left.property
  let K' := (R.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  have : R.Additive := additive_representedModuleRestriction B S hS U
  have hK' : IsStrictlyPerfect _ K' :=
    SheafOfModules.isStrictlyPerfect_map R (representedModuleRestrictionUnitIso B S hS U) hK
  have hqc : ∀ i, (K'.X i).IsQuasicoherentOnSite := fun i =>
    SheafOfModules.IsQuasicoherentOnSite.of_isDirectSummandOfFiniteFree
      (hK'.termDirectSummand i)
  have hcounit : ∀ i, IsIso (adj.counit.app (K'.X i)) := fun i =>
    SmallEtale.isIso_counit _ T U.left.property (K'.X i) (hqc i)
      (SmallEtale.isQuasicoherent_restrictModule _ T U.left.property (K'.X i) (hqc i))
  let K₀ := (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K'
  have hK₀ : StrictlyPerfect.IsStrictlyPerfect (X := T.toRingedSpace) K₀ :=
    SmallEtale.isStrictlyPerfect_restrictModule _ T U.left.property hK'
  let adj' := adj.comp eqv.toAdjunction
  let φ := (NatTrans.mapHomologicalComplex adj'.counit (ComplexShape.up ℤ)).app K
  have (i : ℤ) : IsIso (φ.f i) := by
    show IsIso (adj'.counit.app (K.X i))
    have : IsIso (adj.counit.app (eqv.inverse.obj (K.X i))) := hcounit i
    have : IsIso (eqv.toAdjunction.counit.app (K.X i)) := (eqv.counitIso.app (K.X i)).isIso_hom
    rw [show adj'.counit.app (K.X i) = _ from
      Adjunction.comp_counit_app adj eqv.toAdjunction (K.X i)]
    exact IsIso.comp_isIso
  have : IsIso φ := HomologicalComplex.Hom.isIso_of_components φ
  let e := asIso φ ≪≫ (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).app K
  exact ⟨DerivedCategory.Q.obj K₀,
    Stacks.Cohomology.PerfectDirectSummands.isPerfect_Q_obj_of_isStrictlyPerfect K₀ hK₀,
    ⟨((representedAssociatedModule B S hS U
      (isAlgebraicSpace_yoneda B S hS U)).mapDerivedCategoryFactors.app K₀) ≪≫
        DerivedCategory.Q.mapIso e⟩⟩

end AlgebraicGeometry.Space
