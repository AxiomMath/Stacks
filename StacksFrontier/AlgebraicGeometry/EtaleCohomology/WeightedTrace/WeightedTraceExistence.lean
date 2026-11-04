module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceTransport
public import StacksCore.Tactic.StacksAttribute

/-!
# The weighted trace map of a locally quasi-finite morphism

Let `f : X ⟶ Y` be a locally quasi-finite morphism of schemes and let `w : X → ℤ` be a weighting
of `f`. For every abelian sheaf `F` on the small étale site of `Y` there is exactly one morphism

`Tr_{f, w, F} : f_! f^{-1}F ⟶ F`

whose effect on the stalk at every geometric point `s̄` of `Y` is, through the decomposition
`(f_! f^{-1}F)_{s̄} ≅ ⊕_{f(x̄) = s̄} (f^{-1}F)_{x̄}` of Stacks 0F5F and the identification
`(f^{-1}F)_{x̄} ≅ F_{s̄}` of Stacks 03Q1, the weighted sum `(a_{x̄})_{x̄} ↦ ∑_{x̄} w(x̄) · a_{x̄}`
over the geometric fibre. That is Stacks 0GKG, and this file states it.

## Main results

* `AlgebraicGeometry.SmallEtale.existsUnique_hasWeightedTraceStalks` — **Stacks 0GKG.** The
  trace map exists and is unique.
* `AlgebraicGeometry.SmallEtale.weightedTrace` — the trace map itself, selected by that
  statement, and `AlgebraicGeometry.SmallEtale.weightedTrace_hasWeightedTraceStalks`,
  `AlgebraicGeometry.SmallEtale.eq_weightedTrace` — its characterising property and the
  uniqueness in the form in which a consumer uses them.

## Implementation notes

**Where each half comes from.** The prescribed behaviour on geometric stalks is
`AlgebraicGeometry.SmallEtale.HasWeightedTraceStalks`, and the weighted sum it refers to is
`AlgebraicGeometry.SmallEtale.weightedTraceStalkMap`, both of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceConstruction`.
Uniqueness is `AlgebraicGeometry.SmallEtale.hasWeightedTraceStalks_unique` there: the geometric
stalk functors are jointly faithful on abelian étale sheaves (Stacks 03PU), so a morphism of
sheaves is determined by the maps it induces on stalks, and the prescription fixes each of
those. It needs no hypothesis on `w`.

Existence is `AlgebraicGeometry.SmallEtale.exists_hasWeightedTraceStalks` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceTransport`, and it is
where the weighting is used. It follows the source: the fibre integral
`AlgebraicGeometry.fibreIntegral` of a locally constant section supported on a part of `X_V`
finite over `V` is locally constant on `V` exactly because `w` is a weighting, which gives a
morphism of presheaves `f_{p!}ℤ ⟶ ℤ` (`integralTracePresheafMap`) and hence, `f_!ℤ` being the
sheafification of `f_{p!}ℤ`, a trace `f_!ℤ ⟶ ℤ` on the constant sheaf (`integralTrace`), whose
stalk is the weighted sum (`integralTrace_stalk`); the projection formula of Stacks 0GKF then
carries it to a general `F`, after the constant sheaf has been identified with the monoidal unit
of the tensor product of sheaves of `ULift ℤ`-modules
(`forgetTensorUnitIsoLocallyConstantSheafAb`) so that Stacks 0GKF applies to it.

**The hypotheses.** The source says *locally quasi-finite*; the development's `f_!`
(`AlgebraicGeometry.SmallEtale.fShriekFunctor`, Stacks 0F6R) carries both `LocallyQuasiFinite`
and `LocallyOfFiniteType` as instance hypotheses, so they appear here too — without them the
statement cannot be written, `f_!` not being defined. No other hypothesis is added: in
particular nothing is assumed about `Y`, and `w` enters only through `IsWeighting`.

**The coefficient universe.** The statement is at `AddCommGrpCat.{max (u + 1) v}` for an
arbitrary `v`, which is the universe at which `f_!`, the stalk decomposition of Stacks 0F5F and
the projection formula of Stacks 0GKF are all available; it is not restricted to `v = u + 1`.

## References

* [Stacks Project, Tag 0GKG](https://stacks.math.columbia.edu/tag/0GKG)
* [Stacks Project, Tag 0GKF](https://stacks.math.columbia.edu/tag/0GKF)
* [Stacks Project, Tag 0F5F](https://stacks.math.columbia.edu/tag/0F5F)
* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

/-- **Stacks 0GKG.** Let `f : X ⟶ Y` be a locally quasi-finite morphism of schemes and let
`w : X → ℤ` be a weighting of `f`. For every abelian sheaf `F` on the small étale site of `Y`
there exists a unique trace map `Tr_{f, w, F} : f_! f^{-1}F ⟶ F` with the prescribed behaviour
on stalks: at every geometric point `s̄` of `Y` the map it induces on stalks, read through the
decomposition of `(f_! f^{-1}F)_{s̄}` into the direct sum of the stalks of `f^{-1}F` over the
geometric fibre above `s̄`, is the weighted sum `(a_{x̄})_{x̄} ↦ ∑_{x̄} w(x̄) · a_{x̄}` over that
fibre. -/
@[stacks 0GKG]
public theorem existsUnique_hasWeightedTraceStalks {w : X.obj → ℤ}
    (hw : IsWeighting (B.inclusion.map f) w)
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v}) :
    ∃! τ : (fShriekFunctor.{u, v} B f).obj ((abPullback.{u, v} B f).obj F) ⟶ F,
      HasWeightedTraceStalks.{u, v} B f w F τ := by
  obtain ⟨τ, hτ⟩ := exists_hasWeightedTraceStalks.{u, v} B f hw F
  exact ⟨τ, hτ, fun σ hσ => hasWeightedTraceStalks_unique.{u, v} B f w F hσ hτ⟩

/-- **The trace map of Stacks 0GKG.** The unique morphism `f_! f^{-1}F ⟶ F` with the prescribed
behaviour on geometric stalks, selected by
`AlgebraicGeometry.SmallEtale.existsUnique_hasWeightedTraceStalks`. -/
@[sga "4 XVII 6.2.5" "partial"]
public def weightedTrace {w : X.obj → ℤ} (hw : IsWeighting (B.inclusion.map f) w)
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v}) :
    (fShriekFunctor.{u, v} B f).obj ((abPullback.{u, v} B f).obj F) ⟶ F :=
  (existsUnique_hasWeightedTraceStalks.{u, v} B f hw F).choose

/-- The trace map of Stacks 0GKG has the prescribed behaviour on geometric stalks. -/
public theorem weightedTrace_hasWeightedTraceStalks {w : X.obj → ℤ}
    (hw : IsWeighting (B.inclusion.map f) w)
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v}) :
    HasWeightedTraceStalks.{u, v} B f w F (weightedTrace.{u, v} B f hw F) :=
  (existsUnique_hasWeightedTraceStalks.{u, v} B f hw F).choose_spec.1

/-- Any morphism with the behaviour on geometric stalks prescribed by Stacks 0GKG is the trace
map. -/
public theorem eq_weightedTrace {w : X.obj → ℤ} (hw : IsWeighting (B.inclusion.map f) w)
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v})
    {τ : (fShriekFunctor.{u, v} B f).obj ((abPullback.{u, v} B f).obj F) ⟶ F}
    (hτ : HasWeightedTraceStalks.{u, v} B f w F τ) :
    τ = weightedTrace.{u, v} B f hw F :=
  hasWeightedTraceStalks_unique.{u, v} B f w F hτ
    (weightedTrace_hasWeightedTraceStalks.{u, v} B f hw F)

end AlgebraicGeometry.SmallEtale

end
