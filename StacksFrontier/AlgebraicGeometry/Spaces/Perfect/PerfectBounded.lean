module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffinePerfectSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyDescentSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageUniformBound

/-!
# A perfect object on a quasi-compact algebraic space is bounded

Let `X` be a quasi-compact algebraic space over a scheme `S` and `E` a perfect object of
`D(𝒪_X)` (Stacks 08G5).  Then the cohomology sheaves `Hⁱ(E)` vanish for all but finitely many
`i`.

## Main results

* `AlgebraicGeometry.Space.exists_isZero_homology_of_isPerfect`: the statement above.

## References

* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A perfect object on a quasi-compact algebraic space is bounded**: its cohomology sheaves
vanish outside a finite interval of degrees. -/
theorem exists_isZero_homology_of_isPerfect (X : AlgebraicSpaces B S hS)
    (hX : IsQuasiCompactSpace B S hS X.1) (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E) :
    ∃ a b : ℤ, ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj E) := by
  obtain ⟨W, φ, hW, hsurj, het⟩ :=
    exists_affine_isSurjective_isEtale_of_isQuasiCompactSpace B S hS X hX
  let φ' : (⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ : AlgebraicSpaces B S hS) ⟶ X :=
    ObjectProperty.homMk φ
  let L := etaleModulePullback.{u, u} B S hS φ' het
  have : L.Additive := etaleModulePullback_additive B S hS _ _
  have : PreservesFiniteLimits L := preservesFiniteLimits_etaleModulePullback B S hS _ _
  have : PreservesFiniteColimits L := preservesFiniteColimits_etaleModulePullback B S hS _ _
  have hEW := isPerfect_etaleModulePullback B S hS X φ' het E hE
  obtain ⟨P, a, b, ha, hb, -, -, ⟨eP⟩⟩ :=
    isPerfect_representedAffineDerivedSections_obj B S hS W _ hEW
  have hQ := qcohDerived_of_isPerfect B S hS _ _ hEW
  have := isIso_representedAffineDerivedAdjunction_counit_app B S hS W _ hQ
  let e : L.mapDerivedCategory.obj E ≅
      (representedAffineDerivedAssociated B S hS W).obj (DerivedCategory.Q.obj P) :=
    (asIso ((representedAffineDerivedAdjunction B S hS W).counit.app _)).symm ≪≫
      (representedAffineDerivedAssociated B S hS W).mapIso eP
  refine ⟨a, b, fun i hi => ?_⟩
  refine isZero_of_isZero_etaleModulePullback_of_isSurjective B S hS φ' het hsurj _ ?_
  have hPi : IsZero ((DerivedCategory.homologyFunctor _ i).obj (DerivedCategory.Q.obj P)) := by
    rcases hi with hi | hi
    · exact DerivedCategory.isZero_of_isGE _ a i hi
    · exact DerivedCategory.isZero_of_isLE _ b i hi
  refine IsZero.of_iso ?_ ((L.mapDerivedCategoryHomologyIso i).app E).symm
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor _ i).mapIso e)
  exact IsZero.of_iso ((representedAffineAssociated B S hS W).map_isZero hPi)
    (((representedAffineAssociated B S hS W).mapDerivedCategoryHomologyIso i).app _)

end AlgebraicGeometry.Space

end
