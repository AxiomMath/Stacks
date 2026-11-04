module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkCohomologyMapCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.TorIndependenceEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatEtaleLocalRing
import all StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkCohomologyMap

/-!
# The structure maps of geometric stalks along composites and étale morphisms

For morphisms `g₁ : X'' ⟶ X'` and `g₂ : X' ⟶ X` of algebraic spaces and a geometric point `x̄`
of `X''`, the homomorphism of geometric stalk rings of the composite is the composite of the
homomorphisms, and for an étale morphism the homomorphism of geometric stalk rings is bijective
(Stacks 04KF).

## Main results

* `AlgebraicGeometry.Space.stalkStructureMap_comp_hom`
* `AlgebraicGeometry.Space.bijective_stalkStructureMap_of_isEtale`
-/

/- Instances that come into scope here only through the base versions of imported modules,
and that would change the elaboration below (universe joins, the small model of `D(R)`). -/
attribute [-instance] Stacks.SheafOfModules.coefficientSheafification
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

@[expose] public noncomputable section

open CategoryTheory

universe u

/- A module imported on the base (`Stacks.Cohomology.SiteModules.moduleSheavesAbelian`, through
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.TorIndependentDerivedPullback`) gives `Abelian` for
these categories of modules at a universe join that is never the one used here. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X X' X'' : AlgebraicSpaces B S hS}

/-- **The homomorphisms of geometric stalk rings compose.** -/
theorem stalkStructureMap_comp_hom (g₁ : X'' ⟶ X') (g₂ : X' ⟶ X)
    (x : GeometricPoint B S hS X''.1) :
    (stalkStructureMap B S hS (g₁ ≫ g₂) x).hom =
      (stalkStructureMap B S hS g₁ x).hom.comp
        (stalkStructureMap B S hS g₂ (geometricPointMap g₁.hom x)).hom := by
  refine RingHom.ext fun z => (pointStalkRingEquiv B S hS X'' x).injective ?_
  have h12 := pointStalkRingEquiv_stalkStructureMap B S hS (g₁ ≫ g₂) x z
  have h1 := pointStalkRingEquiv_stalkStructureMap B S hS g₁ x
    ((stalkStructureMap B S hS g₂ (geometricPointMap g₁.hom x)).hom z)
  have h2 := pointStalkRingEquiv_stalkStructureMap B S hS g₂ (geometricPointMap g₁.hom x) z
  have hc := congrFun (congrArg (fun k : etaleLocalRing B S hS X.1
      (geometricPointMap g₂.hom (geometricPointMap g₁.hom x)) →+*
        etaleLocalRing B S hS X''.1 x => (k : _ → _))
    (etaleLocalRingMap_comp X''.2 X'.2 g₁.hom g₂.hom x))
    (pointStalkRingEquiv B S hS X (geometricPointMap g₂.hom (geometricPointMap g₁.hom x)) z)
  refine h12.trans (hc.symm.trans ?_)
  refine (congrArg (etaleLocalRingMap X''.2 g₁.hom x) h2.symm).trans ?_
  exact h1.symm

/-- **The homomorphism of geometric stalk rings along an étale morphism is bijective**
(Stacks 04KF). -/
theorem bijective_stalkStructureMap_of_isEtale (φ : X' ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (y : GeometricPoint B S hS X'.1) :
    Function.Bijective (stalkStructureMap B S hS φ y).hom := by
  have he : etaleLocalRingMap X'.2 φ.hom y =
      (etaleLocalRingIsoOfIsEtale B S hS φ hφ y).inv.hom :=
    (eq_etaleLocalRingMap X'.2 φ.hom y
      (isEtaleLocalRingMap_etaleLocalRingIsoOfIsEtale_inv B S hS φ hφ y)).symm
  have hb : Function.Bijective (etaleLocalRingMap X'.2 φ.hom y) := by
    rw [he]
    exact (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  have hfun : ((stalkStructureMap B S hS φ y).hom : _ → _) =
      (pointStalkRingEquiv B S hS X' y).symm ∘ etaleLocalRingMap X'.2 φ.hom y ∘
        pointStalkRingEquiv B S hS X (geometricPointMap φ.hom y) := by
    funext z
    exact ((pointStalkRingEquiv B S hS X' y).symm_apply_apply _).symm.trans
      (congrArg (pointStalkRingEquiv B S hS X' y).symm
        (pointStalkRingEquiv_stalkStructureMap B S hS φ y z))
  rw [hfun]
  exact (pointStalkRingEquiv B S hS X' y).symm.bijective.comp
    (hb.comp (pointStalkRingEquiv B S hS X (geometricPointMap φ.hom y)).bijective)

end AlgebraicGeometry.Space

end
