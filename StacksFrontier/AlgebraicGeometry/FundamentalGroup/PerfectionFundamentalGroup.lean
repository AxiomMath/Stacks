module

public import Mathlib.FieldTheory.IsPerfectClosure
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PerfectionBaseChange
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TopologicalInvarianceFundamental.UniversalHomeomorphismEquivalence

/-!
# The étale fundamental group does not change under perfection of the base field

Let `k` be a field with perfection `k^{perf}` and let `X` be a connected scheme over `k`. Then
`X_{k^{perf}}` is connected and the projection `X_{k^{perf}} ⟶ X` induces an isomorphism
`π₁(X_{k^{perf}}) → π₁(X)` of étale fundamental groups.

## Main results

* `AlgebraicGeometry.connectedSpace_and_etaleFundamentalGroupMap_perfectClosure` — Stacks 0BTW:
  `X_{k^{perf}}` is connected, and at every geometric point the induced continuous homomorphism of
  étale fundamental groups is an isomorphism of topological groups.

## Implementation notes

As in `AlgebraicGeometry.connectedSpace_pullback_specMap_algebraMap_perfectClosure`, the
perfection is any field `kperf` with `IsPerfectClosure` for the structural map and the common
exponential characteristic `p`. It is purely inseparable over `k`, so `Spec kperf ⟶ Spec k` is a
universal homeomorphism, hence so is its base change `X_{kperf} ⟶ X`, and topological invariance
of the fundamental group (Stacks 0BQN,
`AlgebraicGeometry.fundamentalGroupContinuousMulEquivOfUniversalHomeomorphism`) applies; this is
the source's proof.

The isomorphism is a `ContinuousMulEquiv` together with the statement that its underlying map is
the canonical induced homomorphism `AlgebraicGeometry.etaleFundamentalGroupMap`, so the statement
names the map of the source and not merely an abstract isomorphism. The fundamental groups are
based at an arbitrary geometric point `x` of `X_{kperf}` and at its image in `X`; the
connectedness instance they need is the first half of the statement.

## References

* [Stacks Project, Tag 0BTW](https://stacks.math.columbia.edu/tag/0BTW)
* [Stacks Project, Tag 0BQN](https://stacks.math.columbia.edu/tag/0BQN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0BTW.** Let `k` be a field with perfection `kperf` and let `X` be a
connected scheme over `k`. Then `X_{kperf} = X ×_{Spec k} Spec kperf` is connected, and for every
geometric point `x` of `X_{kperf}` the map `π₁(X_{kperf}, x) → π₁(X, x)` induced by the
projection is an isomorphism of topological groups. -/
@[stacks 0BTW "both assertions: `X_{k^{perf}}` is connected, and the canonical map \
`π₁(X_{k^{perf}}) → π₁(X)` is an isomorphism of topological groups"]
theorem connectedSpace_and_etaleFundamentalGroupMap_perfectClosure (k kperf : Type u) [Field k]
    [Field kperf] [Algebra k kperf] (p : ℕ) [ExpChar k p] [ExpChar kperf p]
    [PerfectRing kperf p] [IsPerfectClosure (algebraMap k kperf) p] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [ConnectedSpace ↥X] :
    ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kperf)))) ∧
      ∀ x : GeometricPoint (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kperf)))),
        haveI := connectedSpace_pullback_specMap_algebraMap_perfectClosure k kperf p f
        ∃ e : EtaleFundamentalGroup _ x ≃ₜ*
            EtaleFundamentalGroup X (x.map (pullback.fst f _)),
          ∀ σ, e σ = etaleFundamentalGroupMap (pullback.fst f _) x σ := by
  have : IsPurelyInseparable k kperf := IsPRadical.isPurelyInseparable k kperf p
  have hc := connectedSpace_pullback_specMap_algebraMap_perfectClosure k kperf p f
  refine ⟨hc, fun x ↦ ?_⟩
  have : UniversalHomeomorphism
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k kperf)))) :=
    ⟨(MorphismProperty.universally_isStableUnderBaseChange
        (topologically @IsHomeomorph)).of_isPullback (IsPullback.of_hasPullback f _).flip
      (universalHomeomorphism_specMap_algebraMap k kperf).universally_isHomeomorph⟩
  obtain ⟨e, he⟩ := fundamentalGroupContinuousMulEquivOfUniversalHomeomorphism (pullback.fst f _) x
  exact ⟨e, he⟩

end AlgebraicGeometry

end
