module

public import Mathlib.FieldTheory.IsPerfectClosure
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.PurelyInseparableField

/-!
# Base change of a scheme to a purely inseparable extension of its base field

Let `K/k` be a purely inseparable extension of fields and let `X` be a scheme over `k`. The
projection `X_K ⟶ X` is a homeomorphism on underlying spaces, because `Spec K ⟶ Spec k` is a
universal homeomorphism. Hence `X_K` is connected as soon as `X` is; in particular this holds
for the perfection `k^{perf}` of `k`.

## Main results

* `AlgebraicGeometry.connectedSpace_pullback_specMap_algebraMap` — the base change of a
  connected scheme along a purely inseparable field extension is connected.
* `AlgebraicGeometry.connectedSpace_pullback_specMap_algebraMap_perfectClosure` — the same for
  the perfection of the base field.

## Implementation notes

The perfection is taken abstractly, as a field `kperf` with `IsPerfectClosure` for the structural
map and the common exponential characteristic `p`, following
`Algebra.isNormalRing_tensorProduct_tfae`; `IsPRadical.isPurelyInseparable` turns that into pure
inseparability.

Stacks 0BTW asserts two things about the perfection: that `X_{k^{perf}}` is connected, and that
`π₁(X_{k^{perf}}) → π₁(X)` is an isomorphism. Only the first is proved here, which is why the
attribute carries a clause naming it. The second needs the equivalence
`FÉt_X ⥤ FÉt_{X_{k^{perf}}}` of Stacks 0BQN, whose essential surjectivity is effectivity of
étale descent along a surjective integral morphism (Stacks 0BTP) and is not available in this
library; granted that equivalence,
`AlgebraicGeometry.fundamentalGroupContinuousMulEquivOfFiniteEtaleBaseChange` (Stacks 0BQA)
supplies the isomorphism.

## References

* [Stacks Project, Tag 0BTW](https://stacks.math.columbia.edu/tag/0BTW)
* [Stacks Project, Tag 0BQN](https://stacks.math.columbia.edu/tag/0BQN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The base change of a connected scheme over `k` along a purely inseparable extension `K/k` is
connected: the projection `X ×_{Spec k} Spec K ⟶ X` is a homeomorphism. -/
theorem connectedSpace_pullback_specMap_algebraMap (k K : Type u) [Field k] [Field K]
    [Algebra k K] [IsPurelyInseparable k K] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [ConnectedSpace ↥X] :
    ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
  ((isHomeomorph_pullbackFst_specMap_algebraMap k K f).homeomorph _).connectedSpace_iff.mpr
    inferInstance

/-- **The connectedness half of Stacks Project, Tag 0BTW.** For a field `k` with perfection
`kperf` and a connected scheme `X` over `k`, the base change `X_{kperf}` is connected.

The perfection is purely inseparable over `k`, so this is
`AlgebraicGeometry.connectedSpace_pullback_specMap_algebraMap`. -/
@[stacks 0BTW "the assertion that `X_{k^{perf}}` is connected; the asserted isomorphism \
`π₁(X_{k^{perf}}) → π₁(X)` is not proved here"]
theorem connectedSpace_pullback_specMap_algebraMap_perfectClosure (k kperf : Type u) [Field k]
    [Field kperf] [Algebra k kperf] (p : ℕ) [ExpChar k p] [ExpChar kperf p]
    [PerfectRing kperf p] [IsPerfectClosure (algebraMap k kperf) p] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [ConnectedSpace ↥X] :
    ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kperf)))) :=
  have : IsPurelyInseparable k kperf := IsPRadical.isPurelyInseparable k kperf p
  connectedSpace_pullback_specMap_algebraMap k kperf f

end AlgebraicGeometry

end
