module

public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
public import Mathlib.Topology.Homeomorph.Lemmas
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.Basic
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.ClopenRefinement
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.ProfiniteBaseChange

/-!
# Closed points of a profinite base change of the component map

Let `X` be a w-local spectral space and let `Y = X ×_{π₀(X)} T` be the base change of its
component map along a map from a profinite space `T`. The inverse image of the closed points of
`X` maps homeomorphically onto `T`, and a point of `Y` is closed exactly when its image in `X`
is closed.

## Main results

* `AlgebraicGeometry.ProEtale.isHomeomorph_toT_closedPointPreimage`: the projection to `T`
  restricts to a homeomorphism on the inverse image of the closed points.
* `AlgebraicGeometry.ProEtale.closedPoints_pullback`: the closed points of `Y` are the inverse
  image of the closed points of `X` under the canonical projection.

## Implementation notes

The inverse image of the closed points is represented as a subtype of the categorical pullback.
Stating the closed points of `Y` as an equality of sets, rather than as a pair of implications,
is the direct form of the source's claim and is what later use sites rewrite with.

## References

* [Stacks Project, Tag 096C](https://stacks.math.columbia.edu/tag/096C)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.ProEtale

/-- In a profinite base change of the component map of a w-local space, the
inverse image of the closed points maps homeomorphically to the base. -/
theorem isHomeomorph_toT_closedPointPreimage
    (S : ProfiniteBaseChangeOfComponentMap) [WLocalSpace S.X] :
    IsHomeomorph (fun y : (S.toX : S.Y → S.X) ⁻¹' closedPoints S.X => S.toT y) := by
  have hclosedX : IsClosed (closedPoints S.X) := WLocalSpace.isClosed_closedPoints
  have hunique : ∀ x : S.X, ∃! x₀ : closedPoints S.X, Specializes x x₀.1 := fun x => by
    obtain ⟨c, hc, huniq⟩ := WLocalSpace.existsUnique_closedPoint_specializes x
    exact ⟨⟨c, hc.1⟩, hc.2, fun c' hc' ↦ Subtype.ext (huniq c'.1 ⟨c'.2, hc'⟩)⟩
  have hbijX :=
    closedPoints_to_connectedComponents_bijective_of_unique_specialization hclosedX hunique
  have hclosedY : IsClosed ((S.toX : S.Y → S.X) ⁻¹' closedPoints S.X) :=
    hclosedX.preimage S.toX.hom.continuous
  have hcompactY : CompactSpace (↥((S.toX : S.Y → S.X) ⁻¹' closedPoints S.X)) :=
    isCompact_iff_compactSpace.mp hclosedY.isCompact
  let e := TopCat.pullbackIsoProdSubtype S.componentMap S.toConnectedComponents
  refine isHomeomorph_iff_continuous_bijective.mpr
    ⟨S.toT.hom.continuous.comp continuous_subtype_val, ?_, ?_⟩
  · intro y₁ y₂ hT
    have hcond (y : S.Y) :
        ConnectedComponents.mk (S.toX y) = S.toConnectedComponents.hom (S.toT y) :=
      CategoryTheory.congr_fun CategoryTheory.Limits.pullback.condition y
    have hX : S.toX y₁ = S.toX y₂ :=
      congrArg Subtype.val (a₁ := (⟨S.toX y₁, y₁.2⟩ : closedPoints S.X)) (a₂ := ⟨S.toX y₂, y₂.2⟩)
        (hbijX.injective ((hcond y₁).trans ((congrArg _ hT).trans (hcond y₂).symm)))
    have hpair : e.hom y₁ = e.hom y₂ := by
      rw [TopCat.pullbackIsoProdSubtype_hom_apply, TopCat.pullbackIsoProdSubtype_hom_apply]
      exact Subtype.ext (Prod.ext hX hT)
    apply Subtype.ext
    simpa [e] using congrArg e.inv.hom hpair
  · intro t
    obtain ⟨x₀, hx₀⟩ := hbijX.surjective (S.toConnectedComponents.hom t)
    let p : { p : S.X × S.T // S.componentMap.hom p.1 = S.toConnectedComponents.hom p.2 } :=
      ⟨⟨x₀.1, t⟩, hx₀⟩
    let y : S.Y := e.inv p
    refine ⟨⟨y, ?_⟩, TopCat.pullbackIsoProdSubtype_inv_snd_apply _ _ p⟩
    change S.toX y ∈ closedPoints S.X
    rw [TopCat.pullbackIsoProdSubtype_inv_fst_apply S.componentMap S.toConnectedComponents p]
    exact x₀.2

/-- A point whose image under a continuous injection is closed is itself closed. -/
private theorem isClosed_singleton_of_injective_continuous
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {f : α → β} (hf : Continuous f) (hi : Function.Injective f)
    {a : α} (ha : IsClosed ({f a} : Set β)) : IsClosed ({a} : Set α) := by
  convert ha.preimage hf using 1
  ext x
  simp [hi.eq_iff]

/-- Closed points in the profinite pullback of a w-local space are precisely those lying
over closed points of the original space. -/
@[stacks 096C "pullback_closed_points"]
theorem closedPoints_pullback (S : ProfiniteBaseChangeOfComponentMap.{u})
    [WLocalSpace S.X] :
    closedPoints S.Y = S.toX ⁻¹' closedPoints S.X := by
  ext y
  constructor
  · intro hy
    have hyclosed : IsClosed ({y} : Set S.Y) := mem_closedPoints_iff.mp hy
    let t := S.toT y
    let y' : {z : S.Y // S.toT z = t} := ⟨y, rfl⟩
    let e := fiber_pullback_snd_homeomorphic_fiber
      S.componentMap S.toConnectedComponents t
    have hyfiber : IsClosed ({y'} : Set {z : S.Y // S.toT z = t}) :=
      isClosed_singleton_of_injective_continuous continuous_subtype_val
        Subtype.val_injective hyclosed
    let z := e y'
    have hzfiber :
        IsClosed ({z} : Set {x : S.X // S.componentMap x = S.toConnectedComponents t}) :=
      isClosed_singleton_of_injective_continuous e.symm.continuous
        e.symm.injective (by simpa [z] using hyfiber)
    have hzval : z.1 = S.toX y := by
      simpa [z, y', t] using
        (fiber_pullback_snd_homeomorphic_fiber_apply_coe
          S.componentMap S.toConnectedComponents t y')
    obtain ⟨c, hc⟩ := WLocalSpace.existsUnique_closedPoint_specializes z.1
    have hspecMem : c ∈ closure ({z.1} : Set S.X) := specializes_iff_mem_closure.mp hc.1.2
    have hccompX : c ∈ connectedComponent z.1 :=
      (isPreconnected_singleton.closure).subset_connectedComponent
        (subset_closure (by simp)) hspecMem
    have hccomp : S.componentMap c = S.toConnectedComponents t := by
      change ConnectedComponents.mk c = S.toConnectedComponents t
      rw [← ConnectedComponents.coe_eq_coe.mpr (connectedComponent_eq hccompX)]
      exact z.2
    let b : {x : S.X // S.componentMap x = S.toConnectedComponents t} := ⟨c, hccomp⟩
    have hspecSub : Specializes z b := by
      rw [specializes_iff_mem_closure, closure_subtype]
      simpa [b] using hspecMem
    have hcx : c = z.1 := congrArg Subtype.val (a₁ := b) (a₂ := z) <| by
      simpa using hzfiber.closure_subset (specializes_iff_mem_closure.mp hspecSub)
    change S.toX y ∈ closedPoints S.X
    rw [← hzval, ← hcx]
    exact hc.1.1
  · intro hy
    let a : (S.toX : S.Y → S.X) ⁻¹' closedPoints S.X := ⟨y, hy⟩
    let h := isHomeomorph_toT_closedPointPreimage S
    have ha : IsClosed ({a} : Set ((S.toX : S.Y → S.X) ⁻¹' closedPoints S.X)) :=
      isClosed_singleton_of_injective_continuous h.continuous h.bijective.injective
        isClosed_singleton
    apply mem_closedPoints_iff.mpr
    simpa [a] using
      (WLocalSpace.isClosed_closedPoints.preimage
        S.toX.hom.continuous).isClosedMap_subtype_val {a} ha

end AlgebraicGeometry.ProEtale
