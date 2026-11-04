module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.JointlyRigSurjectiveEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.JointlyRigSurjectiveEtalePoint
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveClosedImmersionCharts

/-!
# Stacks 0GD5: rig-surjective closed immersions

Let `f : X ⟶ Y` be a closed immersion of locally Noetherian formal algebraic spaces over `S`.
**Stacks 0GD5** says that `f` is rig-surjective if and only if for every affine formal algebraic
space `V` and every morphism `V ⟶ Y` which is representable by algebraic spaces and étale, the
base change `X ×_Y V ⟶ V` corresponds to a surjection `B → A` of `WAdm^{Noeth}` whose kernel
`J` satisfies `I J ^ n = 0` for an ideal of definition `I` of `B` and some `n ≥ 1`.

The chart conditions and the equivalence of condition (2) with rig-surjectivity of every chart
map are in `StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveClosedImmersionCharts`. What
is proved here is the passage from the charts back to `f`, which is the source's appeal to
**Stacks 0AQV**: the Noetherian affine atlas of `Y` is jointly surjective on points, hence
jointly rig-surjective (`isJointlyRigSurjective_of_isRepresentableEtale_of_isJointlySurjective`),
so rig-surjectivity of `f` follows from that of its base changes to the members of the atlas,
each of which is a chart map.

## Main results

* `AlgebraicGeometry.FormalSpace.isRigSurjective_of_hasRigSurjectiveOnPullbackCharts`: a closed
  immersion into a locally Noetherian formal algebraic space all of whose chart maps are
  rig-surjective is rig-surjective.
* `AlgebraicGeometry.FormalSpace.isRigSurjective_iff_hasAnnihilatedKerPow_of_isClosedImmersion`:
  **Stacks 0GD5**.

## References

* [Stacks Project, Tag 0AQV](https://stacks.math.columbia.edu/tag/0AQV)
* [Stacks Project, Tag 0GD5](https://stacks.math.columbia.edu/tag/0GD5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Rig-surjectivity of a closed immersion is read off its Noetherian charts.** Let
`f : X ⟶ Y` be a closed immersion into a locally Noetherian formal algebraic space. If every
chart map of `f`, in the sense of
`AlgebraicGeometry.FormalSpace.HasRigSurjectiveOnPullbackCharts`, is rig-surjective, then `f`
is rig-surjective.

This is the source's use of **Stacks 0AQV**. The Noetherian affine atlas `{Yᵢ ⟶ Y}` of `Y` is
jointly surjective on points, its members being the charts of a surjection of sheaves, and so
jointly rig-surjective; `f` is locally of finite type, being a closed immersion; so
`AlgebraicGeometry.FormalSpace.isRigSurjective_iff_forall_pullback_snd'` reduces the claim to
the base changes `X ×_Y Yᵢ ⟶ Yᵢ`, which are rig-surjective by
`isRigSurjective_pullback_snd_of_hasRigSurjectiveOnPullbackCharts`. -/
theorem isRigSurjective_of_hasRigSurjectiveOnPullbackCharts {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (hY : IsLocallyNoetherian B S hS Y) (hf : IsClosedImmersion B S hS f)
    (h : HasRigSurjectiveOnPullbackCharts B S hS f) : IsRigSurjective B S hS f := by
  obtain ⟨-, I, Yi, g, haff, hg, hsurj, hnoeth⟩ := hY
  have hcover : IsJointlySurjective B S hS Yi g := fun q =>
    exists_pointsMapULift_eq_of_isLocallySurjective_sigmaDesc B S hS g hsurj q
  refine (isRigSurjective_iff_forall_pullback_snd' B S hS f Yi g
    (IsLocallyOfFiniteType.of_isClosedImmersion B S hS f hf) hg hcover
    fun hg' hcover' => isJointlyRigSurjective_of_isRepresentableEtale_of_isJointlySurjective
      B S hS Yi g
      (fun i => isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS (haff i)) hg'
      hcover').mpr fun i => ?_
  exact isRigSurjective_pullback_snd_of_hasRigSurjectiveOnPullbackCharts B S hS f hf (g i) (hg i)
    (hnoeth i) h

/-- **Stacks 0GD5.** Let `f : X ⟶ Y` be a closed immersion of locally Noetherian formal
algebraic spaces over `S`. Then `f` is rig-surjective if and only if for every affine formal
algebraic space `V` and every morphism `V ⟶ Y` which is representable by algebraic spaces and
étale, the base change `X ×_Y V ⟶ V` corresponds to a surjection `B → A` of `WAdm^{Noeth}`
whose kernel `J` satisfies `I J ^ n = 0` for some ideal of definition `I` of `B` and some
`n ≥ 1`.

Condition (2) is `AlgebraicGeometry.FormalSpace.HasAnnihilatedKerPowOnPullbackCharts`, asked
of every presentation of the base change by Noetherian rings with adic topologies. The
equivalence of condition (2) with rig-surjectivity of every chart map is
`AlgebraicGeometry.FormalSpace.hasAnnihilatedKerPow_iff_hasRigSurjective_of_isClosedImmersion`
(Stacks 0AQI, 0AR0 and 00PH). Rig-surjectivity of `f` gives that of the chart maps by
Stacks 0AQS, `AlgebraicGeometry.FormalSpace.hasRigSurjectiveOnPullbackCharts_of_isRigSurjective`,
and conversely by Stacks 0AQV,
`AlgebraicGeometry.FormalSpace.isRigSurjective_of_hasRigSurjectiveOnPullbackCharts`. -/
@[stacks 0GD5]
theorem isRigSurjective_iff_hasAnnihilatedKerPow_of_isClosedImmersion {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y)
    (hf : IsClosedImmersion B S hS f) :
    IsRigSurjective B S hS f ↔ HasAnnihilatedKerPowOnPullbackCharts B S hS f :=
  isRigSurjective_iff_hasAnnihilatedKerPow B S hS f hX hY hf
    (isRigSurjective_of_hasRigSurjectiveOnPullbackCharts B S hS f hY hf)

end AlgebraicGeometry.FormalSpace

end
