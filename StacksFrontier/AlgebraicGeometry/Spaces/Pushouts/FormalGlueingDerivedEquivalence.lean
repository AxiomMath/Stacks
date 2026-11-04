module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPullbackGeometricStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.SupportedDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedDirectImage

/-!
# Stacks 0AEU and 0AFJ

Let `f : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S` and `Z ⊆ X` a closed
subspace of finite presentation such that `f⁻¹Z ⟶ Z` is an isomorphism and `f` is flat at every
point of `f⁻¹Z`. Stacks 0AEU says that the counit `Lf^*Rf_*Q ⟶ Q` is an isomorphism for every
`Q ∈ D_QCoh(𝒪_Y)` supported on `|f⁻¹Z|`; Stacks 0AFJ says that in Situation 0AEV (`f` moreover
quasi-compact and quasi-separated) `Rf_*` induces an equivalence
`D_{QCoh,|f⁻¹Z|}(𝒪_Y) ≌ D_{QCoh,|Z|}(𝒪_X)` with quasi-inverse `Lf^*`.

Both were reduced in the library to three statements about derived pullbacks and pushforwards of
algebraic spaces. This file proves them and records the two lemmas.

## Main results

All names are in the namespace `AlgebraicGeometry.Space`.

* `derivedPullbackStalkComparisonStatement_holds`: the stalk at `x̄'` of the comparison
  `Lg^*P ⟶ g^*P` is invertible where derived base change along `𝒪_{X,g(x̄')} ⟶ 𝒪_{X',x̄'}` is
  computed termwise at the stalk complex of `P`, from the stalk formula
  `derivedPullbackGeometricStalkMap_fac`.
* `exists_not_isZero_sheafModuleFiberOfCommRing_obj_of_mem`: a point in the support of a module
  has a geometric point over it at which the module fibre is nonzero.
* `cohomologySupportedOn_smallEtaleDerivedModulePullback_of_geometricStalk`: `Lg^*` carries
  supports on `T` to supports on `|g|⁻¹T`, from the geometric stalk formula
  `derivedPullbackGeometricStalkIso`.
* `derivedPushforwardQcohDerivedStatement_holds`: Stacks 08FA, part (1).
* `isIso_derivedAdjunction_counit_app_of_cohomologySupportedOn`: **Stacks 0AEU**, with `Z ⟶ X` of
  finite presentation.
* `FormalGlueingSituation.exists_supportedQuasicoherentDerived_equivalence`: **Stacks 0AFJ**.

## Implementation notes

The finite presentation of `Z ⟶ X` in Stacks 0AEU is not in the source's statement; the source's
proof uses it (through Stacks 0AET), and without it the assertion is false: the docstring of
`AlgebraicGeometry.Space.isIso_derivedAdjunction_counit_app_of_cohomologySupportedOn` gives a
counterexample over a valuation ring with divisible value group. In Stacks 0AFJ it is part of
Situation 0AEV.

## References

* [Stacks Project, Tag 0AEU](https://stacks.math.columbia.edu/tag/0AEU)
* [Stacks Project, Tag 0AFJ](https://stacks.math.columbia.edu/tag/0AFJ)
* [Stacks Project, Tag 0AEV](https://stacks.math.columbia.edu/tag/0AEV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The three inputs -/

/-- The stalk of `Lg^*P ⟶ g^*P` at `x̄'` is invertible where derived base change along the stalk
map is computed termwise at `P_{g(x̄')}`: the stalk formula
`AlgebraicGeometry.Space.derivedPullbackGeometricStalkMap_fac` factors the composite of the
isomorphism `AlgebraicGeometry.Space.derivedPullbackGeometricStalkMap` with this stalk as the
comparison of extensions of scalars between two isomorphisms. -/
theorem derivedPullbackStalkComparisonStatement_holds :
    DerivedPullbackStalkComparisonStatement B S hS := by
  intro X' X g x' P hP
  have h := derivedPullbackGeometricStalkMap_fac g x' ((HomotopyCategory.quotient _ _).obj P)
  rw [derivedPullbackGeometricStalkHomotopyMap_app] at h
  have hR : IsIso ((derivedPullbackGeometricStalkComplexMap g x').app P) := by
    rw [derivedPullbackGeometricStalkComplexMap, NatTrans.comp_app]
    exact IsIso.comp_isIso' (Iso.isIso_hom ((derivedExtensionGeometricStalkComplexIso g x').app P))
      (IsIso.comp_isIso' hP (Iso.isIso_hom ((extensionGeometricStalkComplexIso g x').app P)))
  rw [← h] at hR
  simp only [NatTrans.comp_app, Functor.associator_inv_app, Functor.whiskerRight_app,
    Category.id_comp] at hR
  exact IsIso.of_isIso_comp_left ((derivedPullbackGeometricStalkMap g x').app _) _

/-- **A point in the support of a module has a geometric point over it at which the module fibre
does not vanish.** The support of Stacks 04KA is defined by a nonzero geometric stalk at some
geometric point over the point
(`AlgebraicGeometry.Space.mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk`), and the
geometric stalk is additively isomorphic to the module fibre at the point of the small
étale site. -/
theorem exists_not_isZero_sheafModuleFiberOfCommRing_obj_of_mem (X : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS X.1 X.2) {x : points B S hS X.1}
    (hx : x ∈ supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj M)) :
    ∃ xbar : GeometricPoint B S hS X.1, xbar.LiesOver x ∧
      ¬ IsZero ((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 xbar X.2)
        (smallEtaleRingedTopos B S hS X).O).obj M) := by
  obtain ⟨xbar, hxbar, hnt⟩ :=
    (mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk B S hS X M x).1 hx
  refine ⟨xbar, hxbar, fun h ↦ ?_⟩
  have : Subsingleton (Stacks.moduleStalk (etaleSitePoint B S hS X.1 xbar X.2)
      (smallEtaleRingedTopos B S hS X).O M) := ModuleCat.isZero_iff_subsingleton.1 h
  let e₁ := Stacks.moduleStalkLargeLinearEquiv (etaleSitePoint B S hS X.1 xbar X.2)
    (smallEtaleRingedTopos B S hS X).O M
  let e₂ := geometricModuleStalkAddEquiv B S hS X xbar M
  exact not_subsingleton_iff_nontrivial.2 hnt (e₂.symm.toEquiv.trans e₁.toEquiv).subsingleton

/-- **Derived pullback preserves supports**, from the geometric stalk formula. For a morphism
`g : X' ⟶ X` of algebraic spaces and `E ∈ D(𝒪_X)` with cohomology supported on `T ⊆ |X|`, the
cohomology of `Lg^*E` is supported on `|g|⁻¹T`. At a geometric point `x̄'` of `X'` over a point
off `|g|⁻¹T`, the derived stalk of `E` at `g(x̄')` vanishes, its cohomology sheaves having zero
fibres there (`AlgebraicGeometry.Space.isZero_sheafModuleFiberOfCommRing_obj_of_not_mem`); so
does its derived base change, which is the derived stalk of `Lg^*E` at `x̄'`
(`AlgebraicGeometry.Space.derivedPullbackGeometricStalkIso`). -/
theorem cohomologySupportedOn_smallEtaleDerivedModulePullback_of_geometricStalk :
    DerivedPullbackCohomologySupportedOnStatement B S hS := by
  intro X' X g T E hE i x' hx'
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS X'.1 X'.2)
  by_contra hT
  obtain ⟨xbar, hxbar, hnz⟩ :=
    exists_not_isZero_sheafModuleFiberOfCommRing_obj_of_mem B S hS X' _ hx'
  have h₀ := (isZero_geometricDerivedStalk_iff_forall_isZero_sheafModuleFiber B S hS
    (geometricPointMap g.hom xbar) E).2 fun n ↦
      isZero_sheafModuleFiberOfCommRing_obj_of_not_mem B S hS X _ _ fun h ↦ hT (by
        rw [Set.mem_preimage, ← hxbar]
        exact hE n h)
  let := HasDerivedCategory.standard
    (ModuleCat.{u} (geometricStalkRing B S hS (geometricPointMap g.hom xbar)))
  let := HasDerivedCategory.standard (ModuleCat.{u} (geometricStalkRing B S hS xbar))
  have h₁ : IsZero ((geometricDerivedStalk B S hS xbar).obj
      ((smallEtaleDerivedModulePullback B S hS g).obj E)) :=
    ((geometricStalkDerivedExtension g xbar).functor.map_isZero h₀).of_iso
      ((derivedPullbackGeometricStalkIso g xbar).app E).symm
  exact hnz ((isZero_geometricDerivedStalk_iff_forall_isZero_sheafModuleFiber B S hS xbar _).1
    h₁ i)

/-- Stacks 08FA, part (1): this is
`AlgebraicGeometry.Space.qcohDerived_derivedModulePushforward_obj`. -/
theorem derivedPushforwardQcohDerivedStatement_holds :
    DerivedPushforwardQcohDerivedStatement B S hS :=
  fun f hfqc hfqs E hE ↦ qcohDerived_derivedModulePushforward_obj B S hS f hfqc hfqs E hE

/-! ### Stacks 0AEU -/

section Counit

open Stacks.Cohomology.DerivedPullbackOfToposHom

attribute [local instance] isGrothendieckAbelian_ringedToposModules

/-- **Stacks 0AEU.** Let `f : Y ⟶ X` be a morphism of algebraic spaces over `S` and `Z ⊆ X` a
closed subspace of finite presentation such that `f⁻¹Z ⟶ Z` is an isomorphism and `f` is flat at
every point of `f⁻¹Z`. Then for every `Q ∈ D_QCoh(𝒪_Y)` supported on `|f⁻¹Z|` the counit
`Lf^*Rf_*Q ⟶ Q` of the derived adjunction of the morphism of small étale ringed topoi is an
isomorphism.

The finite presentation of `Z ⟶ X` is not in the source's statement, but the source's proof uses
it (through Stacks 0AET and 05E9, which need the ideal of `Z` finitely generated), and the
assertion is false without it. Let `A` be a valuation ring of rank one with divisible value group,
`X = Spec A` and `Z = V(m)` for the maximal ideal `m = m²`, which is not finitely generated.
Choose `g ∈ m` of valuation `1` and `c_n ∈ A` whose valuations increase strictly to `1`, and let
`Y = Spec B` for `B = A[t/c_1, t/c_2, …] ⊂ K[t]`. Then `B` is flat over `A`, `B/mB = A/m`, so
`f⁻¹Z ⟶ Z` is an isomorphism, and `M = B/gB` is supported on `V(mB)`; but the counit
`M ⊗_A B ⟶ M` is not an isomorphism, because `t ∉ A + gB`. In Stacks 0AFJ, the application
the source makes of this lemma, `Z ⟶ X` is of finite presentation by Situation 0AEV. -/
@[stacks 0AEU "with `Z ⟶ X` of finite presentation, which the source's proof uses and without \
  which the statement fails"]
theorem isIso_derivedAdjunction_counit_app_of_cohomologySupportedOn
    {Y X : AlgebraicSpaces B S hS} (f : Y ⟶ X) (Z : Subfunctor X.1)
    (hZ : IsClosedSubspace B S hS Z) (hZfp : IsFinitePresentation B S hS Z.ι)
    (hfZ : IsIso (Z.fromPreimage f.hom))
    (hflat : ∀ y : points B S hS (Z.preimage f.hom).toFunctor,
      IsFlatAt B S hS f.hom
        (pointsMap B S hS (Z.preimage f.hom).toFunctor (Z.preimage f.hom).ι y))
    (Q : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2)
    (hQ : CohomologySupportedOn B S hS Y.1 Y.2
      (Set.range (pointsMap B S hS (Z.preimage f.hom).toFunctor (Z.preimage f.hom).ι)) Q.1) :
    IsIso ((derivedAdjunction (smallEtaleRingedToposHom B S hS f)).counit.app Q.1) :=
  supportedDerivedCounitIsIso_of_derivedPullbackStalkComparison B S hS
    (derivedPullbackStalkComparisonStatement_holds B S hS) f Z hZ hZfp hfZ hflat Q hQ

end Counit

/-! ### Stacks 0AFJ -/

section Situation

open Stacks.Cohomology.DerivedPullbackOfToposHom Stacks.Cohomology.DerivedPushforward

attribute [local instance] isGrothendieckAbelian_ringedToposModules
  hasLeftDerivedFunctor_pullbackOnHomotopy

/-- **Stacks 0AFJ.** In Situation 0AEV (`AlgebraicGeometry.Space.FormalGlueingSituation`), the
derived direct image `Rf_*` of the morphism of small étale ringed topoi of `f` induces an
equivalence `D_{QCoh,|f⁻¹Z|}(𝒪_Y) ≌ D_{QCoh,|Z|}(𝒪_X)` with quasi-inverse given by the derived
pullback `Lf^*`: there is an equivalence whose functor is the restriction of `Rf_*` and whose
inverse is the restriction of `Lf^*`. -/
@[stacks 0AFJ]
theorem FormalGlueingSituation.exists_supportedQuasicoherentDerived_equivalence
    (D : FormalGlueingSituation B S hS) :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS D.spaceX.1 D.spaceX.2)
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS D.spaceY.1 D.spaceY.2)
    ∃ e : (supportedQuasicoherentDerived B S hS D.spaceY
        (subspacePointSet B S hS D.Y (D.Z.preimage D.f))).FullSubcategory ≌
      (supportedQuasicoherentDerived B S hS D.spaceX
        (subspacePointSet B S hS D.X D.Z)).FullSubcategory,
      e.functor ⋙ (supportedQuasicoherentDerived B S hS D.spaceX
          (subspacePointSet B S hS D.X D.Z)).ι =
        (supportedQuasicoherentDerived B S hS D.spaceY
          (subspacePointSet B S hS D.Y (D.Z.preimage D.f))).ι ⋙
          derivedPushforward (X := smallEtaleRingedTopos B S hS D.spaceY)
            (Y := smallEtaleRingedTopos B S hS D.spaceX)
            (smallEtaleRingedToposHom B S hS D.ambientMorphism) ∧
      e.inverse ⋙ (supportedQuasicoherentDerived B S hS D.spaceY
          (subspacePointSet B S hS D.Y (D.Z.preimage D.f))).ι =
        (supportedQuasicoherentDerived B S hS D.spaceX
          (subspacePointSet B S hS D.X D.Z)).ι ⋙
          smallEtaleDerivedModulePullback B S hS D.ambientMorphism := by
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS D.spaceX.1 D.spaceX.2)
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS D.spaceY.1 D.spaceY.2)
  have hT : @IsClosed _ (pointTopology B S hS D.X) (subspacePointSet B S hS D.X D.Z) :=
    isClosed_range_pointsMap_of_isClosedImmersion B S hS D.algebraicSpace_X D.Z.ι D.closed_Z.2
  let Lf : DerivedCategory (Modules.{u, u} B S hS D.spaceX.1 D.spaceX.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS D.spaceY.1 D.spaceY.2) :=
    smallEtaleDerivedModulePullback B S hS D.ambientMorphism
  let : Lf.CommShift ℤ := commShift_smallEtaleDerivedModulePullback B S hS D.ambientMorphism
  have : Lf.IsTriangulated :=
    isTriangulated_smallEtaleDerivedModulePullback B S hS D.ambientMorphism
  have H : DerivedPullbackStalkComparisonStatement B S hS :=
    derivedPullbackStalkComparisonStatement_holds B S hS
  rw [subspacePointSet_preimage]
  exact ⟨supportedQuasicoherentDerivedEquivalence B S hS D.ambientMorphism
    (subspacePointSet B S hS D.X D.Z) Lf _
    (derivedAdjunction (smallEtaleRingedToposHom B S hS D.ambientMorphism))
    (derivedPushforwardQcohDerivedStatement_holds B S hS D.ambientMorphism D.quasiCompact_f
      D.quasiSeparated_f)
    (fun E hE ↦ derivedQuasicoherent_smallEtaleDerivedModulePullback B S hS D.ambientMorphism E hE)
    (fun E hE ↦ cohomologySupportedOn_smallEtaleDerivedModulePullback_of_geometricStalk B S hS
      D.ambientMorphism E hE)
    (derivedCategoryB_supportedModules_smallEtaleDerivedPushforward B S hS D.ambientMorphism _ hT)
    (isIso_derivedAdjunction_counit_app_of_supportedDerivedCounitIsIso B S hS
      (supportedDerivedCounitIsIso_of_derivedPullbackStalkComparison B S hS H)
      D.ambientMorphism D.Z D.closed_Z D.finitePresentation_Z D.iso_over_Z D.flat_at_preimage_Z)
    (isZero_of_isZero_smallEtaleDerivedModulePullback B S hS D.ambientMorphism H _
      D.exists_geometricPointMap_eq_of_mem), rfl, rfl⟩

end Situation

end AlgebraicGeometry.Space

end
