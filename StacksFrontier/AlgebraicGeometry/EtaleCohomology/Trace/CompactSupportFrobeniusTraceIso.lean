module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalCompactSupportFrobeniusNatTrans
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ShortExactTrace

/-!
# The trace of `π_X^*` on `RΓ_c(X_k̄, K)` depends only on `K` up to isomorphism

`π_X^*` is a natural endomorphism of `RΓ_c(X_k̄, -)`
(`Stacks.EtaleCohomology.canonicalCompactSupportFrobeniusNatTrans`), so an isomorphism `K ≅ K'`
of bounded below complexes induces an isomorphism of the complexes `RΓ_c` intertwining the two
actions, and perfectness and traces agree.

## Main results

* `Stacks.EtaleCohomology.isPerfect_compactSupportFrobeniusCohomology_of_iso`
* `Stacks.EtaleCohomology.perfectDerivedTrace_canonicalCompactSupportFrobenius_eq_of_iso`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.FilteredDerived AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

omit [Fintype k] in
/-- Perfectness of `RΓ_c(X_k̄, K)` depends only on `K` up to isomorphism. -/
theorem isPerfect_compactSupportFrobeniusCohomology_of_iso
    {K K' : CochainComplex.Plus (EtaleModules.{u, r} Λ X)} (e : K ≅ K')
    (hK : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, r} Λ f j kbar K))) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, r} Λ f j kbar K')) :=
  StacksDraft.Perfect.isPerfect_of_iso
    (DerivedCategory.Plus.ι.mapIso ((compactSupportFrobeniusFunctor.{u, r} Λ f j kbar).mapIso
      e.symm)) hK

/-- **`Tr(π_X^* | RΓ_c(X_k̄, K))` depends only on `K` up to isomorphism.** -/
theorem perfectDerivedTrace_canonicalCompactSupportFrobenius_eq_of_iso
    {K K' : CochainComplex.Plus (EtaleModules.{u, r} Λ X)} (e : K ≅ K')
    (hK : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, r} Λ f j kbar K)))
    (hK' : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, r} Λ f j kbar K'))) :
    perfectDerivedTrace Λ ⟨_, hK⟩ (DerivedCategory.Plus.ι.map
        (canonicalCompactSupportFrobenius.{u, r} Λ f j kbar p q hcard K)) =
      perfectDerivedTrace Λ ⟨_, hK'⟩ (DerivedCategory.Plus.ι.map
        (canonicalCompactSupportFrobenius.{u, r} Λ f j kbar p q hcard K')) := by
  refine perfectDerivedTrace_congr Λ _ _
    (DerivedCategory.Plus.ι.mapIso ((compactSupportFrobeniusFunctor.{u, r} Λ f j kbar).mapIso e))
    _ _ ?_
  simp only [Functor.mapIso_hom]
  exact (DerivedCategory.Plus.ι.map_comp _ _).symm.trans ((congrArg DerivedCategory.Plus.ι.map
    ((canonicalCompactSupportFrobeniusNatTrans.{u, r} Λ f j kbar p q hcard).naturality
      e.hom).symm).trans (DerivedCategory.Plus.ι.map_comp _ _))

end Stacks.EtaleCohomology

end
