module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPullbackGeometricStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkGerm
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedMinimalSupport
public import StacksFrontier.Homology.DerivedCategory.IsZero

/-!
# Supports of derived pullbacks of algebraic spaces

Let `g : X' ⟶ X` be a morphism of algebraic spaces and `E ∈ D(𝒪_X)` supported on `Y ⊆ |X|`
(Stacks 08GF). Then `Lg^*E` is supported on `|g|⁻¹ Y`. The proof is stalkwise: the stalk of
`Lg^*E` at a geometric point `x̄'` is the derived base change of the stalk of `E` at `g(x̄')`
(`AlgebraicGeometry.Space.derivedPullbackGeometricStalkIso`), which vanishes when `g(x̄')` lies
over a point outside `Y`.

## Main results

* `AlgebraicGeometry.Space.mem_supportOfSheaf_iff_nontrivial_moduleStalk`: a point lies in the
  support of a module exactly when the stalk at some geometric point over it is nonzero.
* `AlgebraicGeometry.Space.isZero_geometricDerivedStalk_iff`: the derived geometric stalk of `K`
  vanishes exactly when the stalks of all cohomology sheaves of `K` do.
* `AlgebraicGeometry.Space.cohomologySupportedOn_smallEtaleDerivedModulePullback`: supports and
  derived pullbacks.
-/

@[expose] public noncomputable section

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A point of an algebraic space lies in the support of an `𝒪_X`-module exactly when the stalk of
the module at the point of the small étale site of some geometric point over it is nonzero. -/
theorem mem_supportOfSheaf_iff_nontrivial_moduleStalk (X : AlgebraicSpaces B S hS)
    (F : Modules.{u, u} B S hS X.1 X.2) (x : points B S hS X.1) :
    x ∈ supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) ↔
      ∃ xbar : GeometricPoint B S hS X.1, xbar.LiesOver x ∧
        Nontrivial (Stacks.moduleStalk (etaleSitePoint B S hS X.1 xbar X.2)
          (smallEtaleRingedTopos B S hS X).O F) := by
  refine (mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk B S hS X F x).trans
    (exists_congr fun xbar => and_congr_right fun _ => ?_)
  let e := (geometricModuleStalkAddEquiv B S hS X xbar F).symm.trans
    (Stacks.moduleStalkLargeAddEquiv (etaleSitePoint B S hS X.1 xbar X.2)
      (smallEtaleRingedTopos B S hS X).O F)
  exact ⟨fun _ => e.injective.nontrivial, fun _ => e.symm.injective.nontrivial⟩

/-- The derived geometric stalk of `K` vanishes exactly when the stalks of all its cohomology
sheaves vanish. -/
theorem isZero_geometricDerivedStalk_iff {X : AlgebraicSpaces B S hS}
    (xbar : GeometricPoint B S hS X.1) (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :
    IsZero ((geometricDerivedStalk B S hS xbar).obj K) ↔
      ∀ i : ℤ, Subsingleton (Stacks.moduleStalk (etaleSitePoint B S hS X.1 xbar X.2)
        (smallEtaleRingedTopos B S hS X).O
          ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj K)) := by
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  refine forall_congr' fun i => ?_
  rw [← ModuleCat.isZero_iff_subsingleton]
  exact (((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 xbar X.2)
    (smallEtaleRingedTopos B S hS X).O).mapDerivedCategoryHomologyFunctorIso i).app K
    ).isZero_iff

/-- **Supports and derived pullbacks.** If `E ∈ D(𝒪_X)` is supported on `Y ⊆ |X|`, then for every
morphism `g : X' ⟶ X` the derived pullback `Lg^*E` is supported on `|g|⁻¹ Y`. -/
theorem cohomologySupportedOn_smallEtaleDerivedModulePullback {X' X : AlgebraicSpaces B S hS}
    (g : X' ⟶ X) {Y : Set (points B S hS X.1)} (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : CohomologySupportedOn B S hS X.1 X.2 Y E) :
    CohomologySupportedOn B S hS X'.1 X'.2 (pointsMap B S hS X'.1 g.hom ⁻¹' Y)
      ((smallEtaleDerivedModulePullback B S hS g).obj E) := by
  intro i x hx
  by_contra hxY
  obtain ⟨xbar, hxbar, hnt⟩ := (mem_supportOfSheaf_iff_nontrivial_moduleStalk X' _ x).1 hx
  have hlies : (geometricPointMap g.hom xbar).LiesOver (pointsMap B S hS X'.1 g.hom x) := by
    rw [GeometricPoint.LiesOver, geometricPointMap_image, hxbar]
  have h₀ : IsZero ((geometricDerivedStalk B S hS (geometricPointMap g.hom xbar)).obj E) := by
    refine (isZero_geometricDerivedStalk_iff _ E).2 fun j => ?_
    rw [← not_nontrivial_iff_subsingleton]
    intro hj
    exact hxY (hE j ((mem_supportOfSheaf_iff_nontrivial_moduleStalk X _ _).2 ⟨_, hlies, hj⟩))
  have h₁ : IsZero ((geometricDerivedStalk B S hS xbar).obj
      ((smallEtaleDerivedModulePullback B S hS g).obj E)) :=
    (((geometricStalkDerivedExtension g xbar).functor.map_isZero h₀)).of_iso
      ((derivedPullbackGeometricStalkIso g xbar).app E).symm
  exact (not_subsingleton_iff_nontrivial.2 hnt) ((isZero_geometricDerivedStalk_iff xbar _).1 h₁ i)

end AlgebraicGeometry.Space

end
