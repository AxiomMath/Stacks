module

public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.CoinducedEffacement
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.ForgetCoefficients

/-!
# The `R`-linear δ-functor of invariants and `ℤ`-valued continuous group cohomology

For a commutative ring `R` and a compact topological group `G`, the δ-functor
`Stacks.ContinuousCohomology.invariantsDelta` (right derived functors of `G`-invariants on
continuous discrete `R`-`G`-modules, computed with injective resolutions) has, as its underlying
abelian groups, the continuous group cohomology `continuousGroupCohomology G i` of the underlying
continuous discrete `G`-module.

In particular a vanishing `Hⁱ(G, M) = 0` read on `invariantsDelta` gives the vanishing of
`continuousGroupCohomology G i M`.

## Main results

* `Stacks.ContinuousCohomology.invariantsDeltaForgetIso` — the comparison of underlying groups.
* `Stacks.ContinuousCohomology.isZero_continuousGroupCohomology_of_isZero_invariantsDelta` — the
  vanishing transfer.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe d u v w

namespace Stacks.ContinuousCohomology

variable (R : Type u) [CommRing R] {G : Type v} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G]

omit [CompactSpace G] in
/-- The degree-`i` part of `invariantsDelta` is Mathlib's right derived functor of invariants. -/
theorem invariantsDelta_functor_eq (i : ℕ) : (invariantsDelta.{u, v, w} R (G := G)).functor i =
    (continuousModuleRingInvariants.{u, v, max u v w} R G).rightDerived i := rfl

/-- The right derived functors of the two spellings of invariants agree. -/
def rightDerivedRingInvariantsIso (i : ℕ) :
    (continuousModuleRingInvariants.{u, v, max u v w} R G).rightDerived i ≅
      (continuousModuleInvariants.{u, v, max u v w} R G).rightDerived i where
  hom := NatTrans.rightDerived (continuousModuleRingInvariantsIso.{u, v, max u v w} R G).hom i
  inv := NatTrans.rightDerived (continuousModuleRingInvariantsIso.{u, v, max u v w} R G).inv i
  hom_inv_id := by rw [← NatTrans.rightDerived_comp, Iso.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by rw [← NatTrans.rightDerived_comp, Iso.inv_hom_id, NatTrans.rightDerived_id]

omit [CompactSpace G] in
/-- `cohomologyFunctor` is the derived-category right derived functor of invariants. -/
theorem cohomologyFunctor_eq_rightDerivedPlus
    [HasDerivedCategory.{d} (Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G)]
    [HasDerivedCategory.{d} (ModuleCat.{max u v w} R)] (i : ℕ) :
    (continuousModuleInvariants.{u, v, max u v w} R G).rightDerivedPlus (i : ℤ) =
      cohomologyFunctor.{d, u, v, w} R G i := rfl

/-- **The underlying abelian group of `Hⁱ(G, M)` computed by `invariantsDelta` is the continuous
group cohomology of the underlying `G`-module**, naturally in `M`. -/
def invariantsDeltaForgetIso (i : ℕ) :
    (invariantsDelta.{u, v, w} R (G := G)).functor i ⋙
        forget₂ (ModuleCat.{max u v w} R) AddCommGrpCat.{max u v w} ≅
      continuousModuleForget.{u, v, max u v w} R G ⋙
        continuousGroupCohomologyFunctor.{v, max u v w} G i :=
  letI := HasDerivedCategory.standard (Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G)
  letI := HasDerivedCategory.standard (ModuleCat.{max u v w} R)
  Functor.isoWhiskerRight (eqToIso (invariantsDelta_functor_eq.{u, v, w} R i) ≪≫
      rightDerivedRingInvariantsIso R i ≪≫ Stacks.DerivedIndexing.rightDerivedIso
        (continuousModuleInvariants.{u, v, max u v w} R G) i ≪≫
      eqToIso (cohomologyFunctor_eq_rightDerivedPlus R i))
      (forget₂ (ModuleCat.{max u v w} R) AddCommGrpCat.{max u v w}) ≪≫
    continuousModuleCohomologyForgetIso R G i

omit [CompactSpace G] in
/-- **A vanishing `Hⁱ(G, M) = 0` for `invariantsDelta` is a vanishing of continuous group
cohomology** of the underlying `G`-module. -/
theorem isZero_continuousGroupCohomology_of_isZero_invariantsDelta (i : ℕ)
    (M : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G)
    (h : IsZero (((invariantsDelta.{u, v, w} R (G := G)).functor i).obj M)) :
    IsZero (continuousGroupCohomology.{v, max u v w} G i
      ((continuousModuleForget.{u, v, max u v w} R G).obj M)) :=
  ((forget₂ (ModuleCat.{max u v w} R) AddCommGrpCat.{max u v w}).map_isZero h).of_iso
    ((invariantsDeltaForgetIso R i).app M).symm

end Stacks.ContinuousCohomology

end
