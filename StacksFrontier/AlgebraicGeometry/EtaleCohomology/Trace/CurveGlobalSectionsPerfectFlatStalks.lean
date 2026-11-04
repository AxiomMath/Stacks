module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveGlobalSectionsPerfectStalkExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlatStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleFlatTopos

/-!
# Stalks of constructible flat sheaves at the lifted geometric points

Let `B` be a big étale site, `Y` an object of it and `Λ` a ring, not necessarily commutative. The
terms of a complex of constructible flat sheaves of `Λ`-modules on Mathlib's small étale site of
`Y` have finite projective stalks at the universe lifts of the geometric points of `Y`, the
conservative family of points on which the proof of [Stacks, Tag 03TV] checks exactness.

## Main results

* `Stacks.SheafTwist.finite_projective_sheafFiber_of_isConstructibleFlat`: the stalks are finite
  projective.

## References

* [Stacks Project, Tag 03TV](https://stacks.math.columbia.edu/tag/03TV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u r

namespace Stacks.SheafTwist

attribute [local instance] SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

variable (B : BigEtaleSite.{u}) (Y : B.Scheme) (Λ : Type r) [Ring Λ]

/-- Finiteness and projectivity of a module transport along an isomorphism of modules. -/
private theorem finite_and_projective_of_iso {Λ : Type r} [Ring Λ]
    {M N : ModuleCat Λ} (e : M ≅ N) [Module.Finite Λ M] [Module.Projective Λ M] :
    Module.Finite Λ N ∧ Module.Projective Λ N :=
  ⟨.equiv e.toLinearEquiv, .of_equiv' e.toLinearEquiv⟩

/-- **The terms of a complex of constructible flat sheaves have finite projective stalks** at the
universe lifts of the geometric points. -/
theorem finite_projective_sheafFiber_of_isConstructibleFlat
    (C : CochainComplex (Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y.obj) ℤ)
    (hC : ∀ i, Stacks.EtaleCohomology.IsConstructibleFlatEtaleModule B Y Λ (C.X i)) (i : ℤ)
    (y : Y.obj) :
    Module.Finite Λ (((geometricSitePoint.{u, r} Y.obj y).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).obj (C.X i)) ∧
      Module.Projective Λ (((geometricSitePoint.{u, r} Y.obj y).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).obj (C.X i)) := by
  let := SmallEtale.hasSheafify_moduleCat.{u, r, r} B Y Λ
  let s := Stacks.Etale.ofPoint y
  let ρ := Stacks.EtaleCohomology.etaleModulesToSmallEtale B Y Λ
  let e : ((geometricSitePoint.{u, r} Y.obj y).sheafFiber
      (A := ModuleCat.{max (u + 1) r} Λ)).obj (C.X i) ≅
      (etaleModuleStalkFunctor.{u, max (u + 1) r, r} B Y Λ s).obj (ρ.obj (C.X i)) :=
    ((Scheme.pointSmallEtale s.hom).uliftPresheafFiberIso.{max (u + 1) r}
      (A := ModuleCat.{max (u + 1) r} Λ)).app (C.X i).obj ≪≫
      (Stacks.EtaleCohomology.etaleModuleStalkIsoTransport.{u, r} B Y Λ s).app (C.X i)
  have : Module.Finite Λ ((etaleModuleStalkFunctor.{u, max (u + 1) r, r} B Y Λ s).obj
      (ρ.obj (C.X i))) := stalk_finite B Y Λ ((ρ.mapHomologicalComplex (ComplexShape.up ℤ)).obj C)
    (fun j => isStratifiedLocallyConstantWith_isFG_of_isConstructibleFlatModuleSheaf B Y Λ (hC j))
    s i
  have := etaleModuleStalk_projective_of_isConstructibleFlatModuleSheaf B Y Λ
    (ρ.obj (C.X i)) (hC i) s
  exact finite_and_projective_of_iso e.symm

/-- Finite projective stalks at a lifted geometric point transport along isomorphisms. -/
theorem finite_projective_sheafFiber_of_iso {Λ : Type r} [Ring Λ] (Y : Scheme.{u}) (y : Y)
    {G G' : Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y} (e : G ≅ G')
    (h : Module.Finite Λ (((geometricSitePoint.{u, r} Y y).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).obj G) ∧
      Module.Projective Λ (((geometricSitePoint.{u, r} Y y).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).obj G)) :
    Module.Finite Λ (((geometricSitePoint.{u, r} Y y).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).obj G') ∧
      Module.Projective Λ (((geometricSitePoint.{u, r} Y y).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).obj G') := by
  obtain ⟨_, _⟩ := h
  exact finite_and_projective_of_iso
    (((geometricSitePoint Y y).sheafFiber (A := ModuleCat Λ)).mapIso e)

end Stacks.SheafTwist

end
