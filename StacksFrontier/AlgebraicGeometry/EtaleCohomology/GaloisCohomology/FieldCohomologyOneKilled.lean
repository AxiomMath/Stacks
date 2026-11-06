module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.EtaleGaloisCohomologyComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DegreeOneCocyclesKilled

/-!
# A bound on Galois cocycles bounds `H¹` of the spectrum of a field

Let `K` be a field, `s̄` a geometric point of `Spec K` with absolute Galois group `G`, and `F` an
abelian sheaf on Mathlib's small étale site of `Spec K`, with Galois module `M`. If `e` times
every locally constant `1`-cocycle `G → M` is a coboundary, then `e` kills
`H¹_ét(Spec K, F)`: by Stacks 03QU part (3)
(`AlgebraicGeometry.smallEtaleSheafCohomologyAddEquivContinuousGroupCohomology`) this group is
`H¹(G, M)`, which `e` kills by
`Stacks.GroupCohomology.nsmul_id_continuousGroupCohomology_one_eq_zero`.

This is the step by which a bound on the continuous cocycles of an inertia group
(`Stacks.EtaleCohomology.InertiaLevelsKilledBy`) bounds the cohomology of the spectrum of the
fraction field of a strict henselization, the stalk of `R¹j_*` at a point at infinity of a curve
(`Stacks.EtaleCohomology.LAdicSheaf.LocalTermsBoundaryStalkInput`).

The standard model `HasDerivedCategory.standard` is used because
`Stacks.ContinuousCohomology.continuousGroupCohomology` is defined there.

## Main results

* `Stacks.EtaleCohomology.nsmul_smallEtaleSheafH_one_eq_zero`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.ContinuousCohomology

universe u

namespace Stacks.EtaleCohomology

section StandardModel

attribute [local instance] HasDerivedCategory.standard
  AlgebraicGeometry.hasExt_smallEtaleSheaf_objectUniverse

/-- **A bound on Galois cocycles bounds `H¹_ét(Spec K, F)`.** For a field `K`, a geometric point
`s̄` of `Spec K` and an abelian sheaf `F` on the small étale site of `Spec K` with Galois module
`M`: if `e` times every locally constant `1`-cocycle of the absolute Galois group with values in
`M` is a coboundary, then `e` kills `H¹_ét(Spec K, F)`. -/
theorem nsmul_smallEtaleSheafH_one_eq_zero (B : BigEtaleSite.{u}) (K : Type u) [Field K]
    (hK : B.Contains (Spec (.of K))) (sbar : GeometricPoint (Spec (.of K)))
    (F : Sheaf ((Spec (.of K) : Scheme.{u})).smallEtaleTopology AddCommGrpCat.{u + 1}) (e : ℕ)
    (hM : let M := ((etaleContinuousGModuleEquivalence.{u, u + 1} B K hK sbar).functor.obj
        ((smallEtaleSheafRestriction B K hK).obj F));
      ∀ c : GeometricPoint.absoluteGaloisGroup sbar → M.obj.obj.V, IsLocallyConstant c →
        (∀ g₁ g₂, c (g₁ * g₂) = (M.obj.obj.ρ g₁).asHom.hom (c g₂) + c g₁) →
        ∃ x : M.obj.obj.V, ∀ g, (M.obj.obj.ρ g).asHom.hom x - x = e • c g)
    (x : Sheaf.H.{u + 1, u + 1} F 1) : e • x = 0 := by
  let φ := smallEtaleSheafCohomologyAddEquivContinuousGroupCohomology B K hK sbar F 1
  have h := Stacks.GroupCohomology.nsmul_id_continuousGroupCohomology_one_eq_zero.{u, u + 1}
    ((etaleContinuousGModuleEquivalence.{u, u + 1} B K hK sbar).functor.obj
      ((smallEtaleSheafRestriction B K hK).obj F)) e hM
  have h2 : e • φ x = 0 := by simpa using ConcreteCategory.congr_hom h (φ x)
  exact φ.injective ((φ.toAddMonoidHom.map_nsmul e x).trans (h2.trans φ.map_zero.symm))

end StandardModel

end Stacks.EtaleCohomology

end
