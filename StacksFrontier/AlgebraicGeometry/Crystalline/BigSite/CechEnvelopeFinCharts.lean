module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.CechEnvelopeCharts
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.CechEnvelopeRestrictOpen

/-!
# A finite cover of `X` by affine opens with smooth lifts carrying étale coordinates

For `X ⟶ S₀` smooth and `X` quasi-compact, `X` is covered by finitely many affine opens
`U_0, …, U_{k-1}`, each with a smooth lift (`Crystalline.GlobalCrystallineSituation.CechEnvelope.
SmoothLift`) carrying global étale coordinates.  This is
`CechEnvelope.exists_finite_smoothLift_etaleCoordinates` with the charts reindexed by `Fin k` and
read as opens of `X`, the lifts being transported along the isomorphisms of the charts with their
images (`CechEnvelope.SmoothLift.restrict`).

## Main results

* `CechEnvelope.exists_fin_cover_smoothLift_etaleCoordinates`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Crystalline.GlobalCrystallineSituation.CechEnvelope

variable {S : GlobalCrystallineSituation.{u}}

/-- **A finite cover of `X` by affine opens carrying smooth lifts with étale coordinates**, for
`X ⟶ S₀` smooth and `X` quasi-compact. -/
theorem exists_fin_cover_smoothLift_etaleCoordinates [IsAffine S.S.scheme] [CompactSpace S.X]
    (hsm : Smooth S.toClosedFiber) :
    ∃ (k : ℕ) (U : Fin k → S.X.Opens), (∀ i, IsAffine (U i)) ∧ (∀ x, ∃ i, x ∈ U i) ∧
      ∀ i, ∃ (L : SmoothLift S (U i).ι) (d : ℕ) (t : Fin d → L.ring),
        (MvPolynomial.aeval (R := baseSectionsRing S) t).toRingHom.Etale := by
  obtain ⟨ι, hι, V, j, hj, hV, hcov, hL⟩ := exists_finite_smoothLift_etaleCoordinates S hsm
  let e := Finite.equivFin ι
  refine ⟨Nat.card ι, fun m ↦ (j (e.symm m)).opensRange, fun m ↦ ?_, fun x ↦ ?_, fun m ↦ ?_⟩
  · have := hV (e.symm m)
    exact IsAffine.of_isIso (j (e.symm m)).isoOpensRange.inv
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov ▸ Set.mem_univ x : x ∈ ⋃ i, Set.range (j i).base)
    refine ⟨e i, ?_⟩
    change x ∈ (j (e.symm (e i))).opensRange
    rw [Equiv.symm_apply_apply]
    simpa using hi
  · obtain ⟨L, d, t, ht⟩ := hL (e.symm m)
    have := hV (e.symm m)
    have : IsAffine (j (e.symm m)).opensRange.toScheme :=
      IsAffine.of_isIso (j (e.symm m)).isoOpensRange.inv
    obtain ⟨t', ht'⟩ := L.exists_etaleCoordinates_restrict
      (i := (j (e.symm m)).isoOpensRange.inv) (Scheme.Hom.isoOpensRange_inv_comp _) ht
    exact ⟨_, d, t', ht'⟩

end Crystalline.GlobalCrystallineSituation.CechEnvelope
