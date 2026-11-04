module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPointCoproducts
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormulaGenerated
public import StacksFrontier.CategoryTheory.Triangulated.CoproductComparison
public import StacksFrontier.Homology.KFlat.FilteredColimitShifts

/-!
# The projection formula for the morphism from an algebraic space to the point `(pt, R)`

Let `X` be a quasi-compact and quasi-separated algebraic space and `φ : R →+* Γ(X, 𝒪_X)` a ring
map, so that `f = spacesEtaleModelToBaseRing φ : (X_{spaces,étale}, 𝒪_X) ⟶ (pt, R)` is a morphism
of ringed topoi presented by a morphism of sites. The projection formula map

  `Rf_*E ⊗^L_R K ⟶ Rf_*(E ⊗^L Lf^*K)`

is an isomorphism for every `E` with quasi-coherent cohomology and every `K ∈ D(pt, R)`. Here
`Rf_* = RΓ(X, -)`.

## Main results

* `AlgebraicGeometry.Space.pointDerived_property_of_generated`: a property of objects of
  `D(pt, R)` closed under isomorphisms, shifts, direct sums and triangles, and holding for the
  structure sheaf, holds for every object.
* `AlgebraicGeometry.Space.isIso_projectionFormulaMap_spacesEtaleModelToBaseRing`: the projection
  formula for `f`.

## References

* [Stacks Project, Tag 08IN](https://stacks.math.columbia.edu/tag/08IN)
* [Stacks Project, Tag 09PB](https://stacks.math.columbia.edu/tag/09PB)
* [Stacks Project, Tag 08FB](https://stacks.math.columbia.edu/tag/08FB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] HasDerivedCategory.standard
attribute [-instance] SheafOfModules.hasColimitsOfShape_discrete_derivedCategory
attribute [local instance] hasCoproducts_derivedCategory_modules

section Point

variable {R : Type u} [CommRing R]

/-- The derived category of the modules over a ringed topos has direct sums indexed by
`Type u`. -/
private theorem hasCoproducts_derivedCategory_modules_ringedTopos (T : RingedTopos.{u, u, u}) :
    HasCoproducts.{u} (DerivedCategory T.Modules) := by
  intro J
  have : IsGrothendieckAbelian.{u} T.Modules := SheafOfModules.isGrothendieckAbelianU _
  exact Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory _ J

/-- The derived category of the punctual ringed topos of `R` has direct sums indexed by
`Type u`. -/
theorem hasCoproducts_derivedCategory_point :
    HasCoproducts.{u} (DerivedCategory (pointRingedTopos (CommRingCat.of R)).Modules) := by
  exact hasCoproducts_derivedCategory_modules_ringedTopos _

attribute [local instance] hasCoproducts_derivedCategory_point

/-- The module equivalence of the point is additive. -/
instance additive_baseRingPointModulesEquiv_functor :
    (baseRingPointModulesEquiv (R := R)).functor.Additive :=
  haveI : PreservesBinaryBiproducts (baseRingPointModulesEquiv (R := R)).functor :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  Functor.additive_of_preservesBinaryBiproducts _

/-- The inverse of the module equivalence of the point is additive. -/
instance additive_baseRingPointModulesEquiv_inverse :
    (baseRingPointModulesEquiv (R := R)).inverse.Additive :=
  haveI : PreservesBinaryBiproducts (baseRingPointModulesEquiv (R := R)).inverse :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  Functor.additive_of_preservesBinaryBiproducts _

/-- The module equivalence of the point is left exact. -/
instance preservesFiniteLimits_baseRingPointModulesEquiv_functor :
    PreservesFiniteLimits (baseRingPointModulesEquiv (R := R)).functor :=
  @PreservesLimitsOfSize.preservesFiniteLimits.{0, 0} _ _ _ _ _
    (baseRingPointModulesEquiv (R := R)).symm.toAdjunction.rightAdjoint_preservesLimits

/-- The module equivalence of the point is right exact. -/
instance preservesFiniteColimits_baseRingPointModulesEquiv_functor :
    PreservesFiniteColimits (baseRingPointModulesEquiv (R := R)).functor :=
  @PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _ _ _ _ _
    (baseRingPointModulesEquiv (R := R)).toAdjunction.leftAdjoint_preservesColimits

/-- The inverse of the module equivalence of the point is left exact. -/
instance preservesFiniteLimits_baseRingPointModulesEquiv_inverse :
    PreservesFiniteLimits (baseRingPointModulesEquiv (R := R)).inverse :=
  @PreservesLimitsOfSize.preservesFiniteLimits.{0, 0} _ _ _ _ _
    (baseRingPointModulesEquiv (R := R)).toAdjunction.rightAdjoint_preservesLimits

/-- The inverse of the module equivalence of the point is right exact. -/
instance preservesFiniteColimits_baseRingPointModulesEquiv_inverse :
    PreservesFiniteColimits (baseRingPointModulesEquiv (R := R)).inverse :=
  @PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _ _ _ _ _
    (baseRingPointModulesEquiv (R := R)).symm.toAdjunction.leftAdjoint_preservesColimits

/-- The derived equivalence `D(pt, R) ≌ D(R)` of the module equivalence. -/
def pointDerivedEquiv :
    DerivedCategory (pointRingedTopos (CommRingCat.of R)).Modules ≌
      DerivedCategory (ModuleCat.{u} R) :=
  Stacks.DerivedGlueing.mapDerivedCategoryEquivalence (baseRingPointModulesEquiv (R := R)).functor
    (baseRingPointModulesEquiv (R := R)).inverse (baseRingPointModulesEquiv (R := R)).unitIso
    (baseRingPointModulesEquiv (R := R)).counitIso

/-- Under the module equivalence, `R` corresponds to the structure sheaf of the point. -/
def baseRingPointModulesEquivUnitIso :
    (baseRingPointModulesEquiv (R := R)).functor.obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
          (pointRingedTopos (CommRingCat.of R)).O)) ≅
      ModuleCat.of R (Shrink.{u} R) :=
  (LinearEquiv.toModuleIso (LinearEquiv.refl R R)) ≪≫ (Shrink.linearEquiv R R).toModuleIso.symm

/-- A property of objects of `D(pt, R)` that is invariant under
isomorphisms and shifts, stable under direct sums and two-out-of-three in distinguished triangles,
and true for the shifts of the structure sheaf, holds for every object. -/
theorem pointDerived_property_of_generated
    (T : DerivedCategory (pointRingedTopos (CommRingCat.of R)).Modules → Prop)
    (hiso : ∀ {K K'}, (K ≅ K') → T K → T K') (hshift : ∀ K (n : ℤ), T K → T (K⟦n⟧))
    (hsum : ∀ {J : Type u} (K : J → DerivedCategory (pointRingedTopos (CommRingCat.of R)).Modules),
      (∀ j, T (K j)) → T (∐ K))
    (htri : ∀ Δ ∈ distTriang (DerivedCategory (pointRingedTopos (CommRingCat.of R)).Modules),
      (T Δ.obj₁ → T Δ.obj₂ → T Δ.obj₃) ∧ (T Δ.obj₁ → T Δ.obj₃ → T Δ.obj₂))
    (hunit : ∀ k : ℤ, T ((Stacks.DerivedTensor.RingedSite.unitObject
      ⟨(pointRingedTopos (CommRingCat.of R)).C, (pointRingedTopos (CommRingCat.of R)).J,
        (pointRingedTopos (CommRingCat.of R)).O⟩)⟦k⟧))
    (K : DerivedCategory (pointRingedTopos (CommRingCat.of R)).Modules) : T K := by
  let e := baseRingPointModulesEquiv (R := R)
  let Eq := pointDerivedEquiv (R := R)
  let Ei := e.inverse.mapDerivedCategory
  let T' : DerivedCategory (ModuleCat.{u} R) → Prop := fun L => T (Ei.obj L)
  have hT' : ∀ L, T' L := by
    refine (CochainComplex.KFlat.property_of_coproducts_of_two_out_of_three_of_shifts.{u, u}
      (R := R)).2 T' ?_ ?_ ?_
    · intro I L _ hL
      have : PreservesColimitsOfShape (Discrete I) Ei :=
        inferInstanceAs (PreservesColimitsOfShape (Discrete I) Eq.inverse)
      exact hiso (asIso (sigmaComparison Ei L)) (hsum _ hL)
    · intro Δ hΔ
      have hΔ' := Ei.map_distinguished Δ hΔ
      refine ⟨(htri _ hΔ').1, (htri _ hΔ').2, fun h₂ h₃ => ?_⟩
      exact (htri _ (Ei.map_distinguished _ (inv_rot_of_distTriang Δ hΔ))).2
        (hiso ((Ei.commShiftIso (-1 : ℤ)).app Δ.obj₃).symm (hshift _ (-1) h₃)) h₂
    · intro k
      refine hiso ?_ (hunit k)
      exact (shiftFunctor _ k).mapIso
          ((DerivedCategory.singleFunctor _ 0).mapIso
              ((e.unitIso.app _) ≪≫ e.inverse.mapIso baseRingPointModulesEquivUnitIso) ≪≫
            ((e.inverse.mapDerivedCategorySingleFunctor 0).app _).symm) ≪≫
        ((Ei.commShiftIso k).app _).symm
  exact hiso (Eq.unitIso.app K).symm (show T (Eq.inverse.obj (Eq.functor.obj K)) from
    hT' (Eq.functor.obj K))

end Point

section ProjectionFormula

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)
  {R : Type u} [CommRing R] (φ : R →+* modelGlobalFunctions B S hS X)

attribute [local instance] hasCoproducts_derivedCategory_point

/-- The morphism `(X_{spaces,étale}, 𝒪_X) ⟶ (pt, R)` is presented by a morphism of sites. -/
theorem isMorphismOfSites_spacesEtaleModelToBaseRing :
    (spacesEtaleModelToBaseRing B S hS X φ).u.IsMorphismOfSites
      (pointRingedTopos (CommRingCat.of R)).J (spacesEtaleModelRingedTopos B S hS X).J :=
  isMorphismOfSites_toPointRingedTopos _ (isTerminal_spacesEtaleModelTerminal B S hS X) _

/-- The derived category of the spaces-étale model has direct sums indexed by `Type u`. -/
theorem hasCoproducts_derivedCategory_spacesEtaleModel :
    HasCoproducts.{u} (DerivedCategory (spacesEtaleModelRingedTopos B S hS X).Modules) := by
  exact hasCoproducts_derivedCategory_modules_ringedTopos _

attribute [local instance] hasCoproducts_derivedCategory_spacesEtaleModel

/-- Let `X` be a quasi-compact and quasi-separated algebraic space, `φ : R →+* Γ(X, 𝒪_X)` and
`f = spacesEtaleModelToBaseRing φ`. For every `E` on the spaces-étale model whose image in
`D(𝒪_X)` has quasi-coherent cohomology and every `K ∈ D(pt, R)`, the projection formula map
`Rf_*E ⊗^L K ⟶ Rf_*(E ⊗^L Lf^*K)` is an isomorphism. -/
theorem isIso_projectionFormulaMap_spacesEtaleModelToBaseRing (hZ : B.Contains (⊤_ Scheme.{u}))
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (E : DerivedCategory (spacesEtaleModelRingedTopos B S hS X).Modules)
    (hE : qcohDerivedProp B S hS X
      ((spacesEtaleModelModulesEquiv B S hS X).functor.mapDerivedCategory.obj E))
    (K : DerivedCategory (pointRingedTopos (CommRingCat.of R)).Modules) :
    haveI := Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy
      (spacesEtaleModelToBaseRing B S hS X φ)
      (isMorphismOfSites_spacesEtaleModelToBaseRing B S hS X φ)
    IsIso (Stacks.Cohomology.ProjectionFormulaOnRingedTopoi.projectionFormulaMap
      (spacesEtaleModelToBaseRing B S hS X φ)
      (isMorphismOfSites_spacesEtaleModelToBaseRing B S hS X φ) E K) := by
  let f := spacesEtaleModelToBaseRing B S hS X φ
  let hmos := isMorphismOfSites_spacesEtaleModelToBaseRing B S hS X φ
  have := Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy
    f hmos
  let Ef := (spacesEtaleModelModulesEquiv B S hS X).functor.mapDerivedCategory
  let Eq := Stacks.DerivedGlueing.mapDerivedCategoryEquivalence
    (spacesEtaleModelModulesEquiv B S hS X).functor (spacesEtaleModelModulesEquiv B S hS X).inverse
    (spacesEtaleModelModulesEquiv B S hS X).unitIso
    (spacesEtaleModelModulesEquiv B S hS X).counitIso
  let Q := (qcohDerivedProp B S hS X).inverseImage Ef
  have hQsum : ∀ {J : Type u}
      (L : J → DerivedCategory (spacesEtaleModelRingedTopos B S hS X).Modules),
      (∀ j, Q (L j)) → Q (∐ L) := by
    intro J L hL
    have : PreservesColimitsOfShape (Discrete J) Ef :=
      inferInstanceAs (PreservesColimitsOfShape (Discrete J) Eq.functor)
    have : HasCoproducts.{u} (QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) :=
      hasCoproducts_quasicoherentDerivedCategory_ringUniverse B S hS X.1 X.2
    have hes : EssentiallySmall.{u} (smallEtaleRingedSite B S hS X.1 X.2).C := by
      change EssentiallySmall.{u} (SmallEtale B S hS X.1)
      infer_instance
    have : IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS X.1 X.2) :=
      SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _
    have hcl := isClosedUnderCoproducts_quasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 J
      (fun M hM => isQuasicoherentOnSite_sigma_of_h03DX B S hS X.1 X.2
        (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS X.1 X.2) M hM)
    exact (qcohDerivedProp B S hS X).prop_of_iso (asIso (sigmaComparison Ef L))
      ((qcohDerivedProp B S hS X).prop_of_isColimit
        (coproductIsCoproduct fun j => Ef.obj (L j)) fun j => hL j.as)
  refine Stacks.Cohomology.ProjectionFormulaGenerated.isIso_projectionFormulaMap_of_generated f
    hmos Q hQsum ?_ (fun T hiso hshift hsum htri hunit =>
      pointDerived_property_of_generated T hiso hshift hsum htri hunit) E hE K
  intro J L hL
  exact preservesColimit_discreteFunctor_of_isIso_sigmaComparison _ _
    (isIso_sigmaComparison_spacesEtaleModelToBaseRing B S hS X φ _
      (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPushforwardUnit f)
      hZ hXqc hXqs L hL)

end ProjectionFormula

end AlgebraicGeometry.Space
