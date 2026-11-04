module

public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Sober
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.DecentStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.SpecializationSmoothChart
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveProperties

/-!
# The points of a decent algebraic stack are Kolmogorov (Stacks 0GW7)

Let `𝒳` be a decent algebraic stack over `S`, that is, an algebraic stack each of whose points
admits a quasi-compact field-valued representative (**Stacks 0GW1**). Then the space of points
`|𝒳|` of **Stacks 04XG**, with the topology of **Stacks 04XL**, is Kolmogorov: two points with
the same neighbourhood filter are equal. Kolmogorov is Mathlib's `T0Space`.

## Main results

* `AlgebraicGeometry.Stack.t0Space_points_of_isDecent`: **Stacks 0GW7**.

## Implementation notes

The argument is not the source's. The source replaces `𝒳` by the reduced closed substack `𝒵`
with `|𝒵| = closure {x₁}` and quotes the existence of a dense open substack of `𝒵` that is an
algebraic space; reduced closed substacks are not available here. Instead the whole argument runs
inside one smooth chart `φ : |U| → |𝒳|` by a scheme `U`, which is surjective
(`AlgebraicGeometry.Stack.exists_smooth_surjective_schemeStack`, read on the algebraic space the
scheme represents) and whose source is a sober space, being homeomorphic to the topological space
of a scheme (**Stacks 03BX**, clause (1)).

Let `x₁` and `x₂` be inseparable points, so that `C := closure {x₁} = closure {x₂}`, and let `u`
be a point of the closed set `φ ⁻¹' C` maximal for specialization inside it — the generic point
of an irreducible component of `φ ⁻¹' C`, which exists because the chart is sober. Decency and
**Stacks 0GVZ** then lift any specialization `x' ⤳ φ u` with `x' ∈ C` to a specialization
`u' ⤳ u` inside `φ ⁻¹' C`, so `u' = u` by maximality and `x' = φ u`. Both `x₁` and `x₂` are such
an `x'`, since `φ u ∈ C` is simultaneously `x₁ ⤳ φ u` and `x₂ ⤳ φ u`; hence `x₁ = φ u = x₂`.

Both point spaces carry the topologies of Stacks 03BX and Stacks 04XL as local instances, so that
`⤳` and `closure` read directly; those definitions are not global instances.

## References

* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 0GVZ](https://stacks.math.columbia.edu/tag/0GVZ)
* [Stacks Project, Tag 0GW1](https://stacks.math.columbia.edu/tag/0GW1)
* [Stacks Project, Tag 0GW7](https://stacks.math.columbia.edu/tag/0GW7)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

attribute [local instance] Space.pointTopology pointTopology

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### A point of a closed set maximal for specialization -/

/-- In a Kolmogorov sober space, every nonempty closed set contains a point that no other point
of the set specializes to: the generic point of an irreducible component of the set, formed in
the subspace, which is sober because the set is closed. -/
private theorem exists_mem_forall_eq_of_specializes {α : Type*} [TopologicalSpace α] [T0Space α]
    [QuasiSober α] {T : Set α} (hT : IsClosed T) (hTne : T.Nonempty) :
    ∃ u ∈ T, ∀ u' ∈ T, u' ⤳ u → u' = u := by
  obtain ⟨u₀, hu₀⟩ := hTne
  have : QuasiSober T := hT.isClosedEmbedding_subtypeVal.quasiSober
  have hti : IsIrreducible (irreducibleComponent (⟨u₀, hu₀⟩ : T)) :=
    isIrreducible_irreducibleComponent
  have hgen : closure ({hti.genericPoint} : Set T) = irreducibleComponent (⟨u₀, hu₀⟩ : T) :=
    hti.closure_genericPoint isClosed_irreducibleComponent
  refine ⟨(hti.genericPoint : α), hti.genericPoint.2, fun u' hu' hspec => ?_⟩
  have hwv : (⟨u', hu'⟩ : T) ⤳ hti.genericPoint := (subtype_specializes_iff _ _).mpr hspec
  have hsub : irreducibleComponent (⟨u₀, hu₀⟩ : T) ⊆
      closure ({(⟨u', hu'⟩ : T)} : Set T) := by
    rw [← hgen]
    exact specializes_iff_closure_subset.mp hwv
  have heq : closure ({(⟨u', hu'⟩ : T)} : Set T) = irreducibleComponent (⟨u₀, hu₀⟩ : T) :=
    eq_irreducibleComponent isIrreducible_singleton.closure.2 hsub
  have hvw : hti.genericPoint ⤳ (⟨u', hu'⟩ : T) :=
    specializes_iff_closure_subset.mpr (by rw [heq, hgen])
  exact congrArg Subtype.val (hwv.antisymm hvw).eq

/-! ### A smooth chart of an algebraic stack by a scheme -/

/-- **Every algebraic stack over `S` has a smooth chart by the algebraic space represented by a
scheme which is surjective on points.** The smooth surjective presentation of Stacks 026O is a
1-morphism out of the algebraic stack of a scheme over `S`; composing it with the smooth
surjective comparison 1-morphism from the algebraic stack of the algebraic space that scheme
represents gives a chart of the shape Stacks 0GVZ consumes. -/
private theorem exists_smoothDiagram_schemeChart_surjective
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) :
    ∃ (U : BigFppfOver B S hS) (f : fibredCategory B S hS (yoneda.obj U) ⟶ 𝒳),
      HasPropertyOnSomeSmoothDiagram B S hS
          (fun _ _ h => Space.IsSmooth B S hS h) f ∧
        Function.Surjective (spacePointMap B S hS (yoneda.obj U) 𝒳 f.hom) := by
  obtain ⟨U, a, haSmooth, haSurj⟩ :=
    exists_smooth_surjective_schemeStack.{u, w} B S hS ⟨𝒳, h𝒳⟩
  obtain ⟨e, heSmooth, heSurj⟩ :=
    exists_smooth_surjective_algebraicSpaceStack_hom.{u, w} B S hS U
  refine ⟨U, (e ≫ a).hom,
    AlgebraicStacks.isSmooth_comp.{u, w} B S hS e a heSmooth haSmooth, ?_⟩
  exact (spacePointMap_surjective_iff_pointsMap_surjective B S hS (yoneda.obj U) 𝒳
    (e ≫ a).hom.hom).2 (isSurjective_comp.{u, w} B S hS e a heSurj haSurj)

/-! ### The Kolmogorov property -/

/-- **Stacks 0GW7.** The space of points of a decent algebraic stack over `S` is Kolmogorov: two
points of `|𝒳|` with the same open neighbourhoods are equal.

Two such points `x₁`, `x₂` have the same closure `C`, and `x₁, x₂ ∈ C`. Choose a smooth chart
`φ : |U| → |𝒳|` by a scheme, surjective on points, and inside the nonempty closed set `φ ⁻¹' C`
choose a point `u` maximal for specialization, which the sobriety of `|U|` provides. Decency
feeds **Stacks 0GVZ** the quasi-compact field-valued representative it asks for, so every
specialization `x' ⤳ φ u` with `x' ∈ C` lifts to a specialization `u' ⤳ u` with `u' ∈ φ ⁻¹' C`;
maximality of `u` forces `u' = u` and hence `x' = φ u`. Applied to `x₁` and to `x₂`, both of
which specialize to `φ u` because `φ u ∈ C`, this gives `x₁ = φ u = x₂`. -/
@[stacks 0GW7]
theorem t0Space_points_of_isDecent
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (hdecent : IsDecent B S hS 𝒳) :
    T0Space (points B S hS 𝒳.val 𝒳.property) := by
  obtain ⟨U, f, hf, hsurj⟩ := exists_smoothDiagram_schemeChart_surjective.{u, w} B S hS 𝒳 h𝒳
  have hcont : Continuous (spacePointMap B S hS (yoneda.obj U) 𝒳 f.hom) :=
    continuous_spacePointMap B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) 𝒳 f.hom
  have : T0Space (Space.points B S hS (yoneda.obj U)) :=
    (Space.schemePointsHomeomorph B S hS U).isEmbedding.t0Space
  have : QuasiSober (Space.points B S hS (yoneda.obj U)) :=
    (Space.schemePointsHomeomorph B S hS U).isOpenEmbedding.quasiSober
  refine (t0Space_iff_inseparable _).2 fun x₁ x₂ hins => ?_
  obtain ⟨h₁₂, h₂₁⟩ := inseparable_iff_specializes_and.mp hins
  have hCeq : closure ({x₂} : Set (points B S hS 𝒳.val 𝒳.property)) = closure {x₁} :=
    subset_antisymm h₁₂.closure_subset h₂₁.closure_subset
  -- the preimage of the common closure is closed and nonempty
  have hTclosed : IsClosed (spacePointMap B S hS (yoneda.obj U) 𝒳 f.hom ⁻¹'
      closure ({x₁} : Set (points B S hS 𝒳.val 𝒳.property))) :=
    isClosed_closure.preimage hcont
  obtain ⟨u₀, hu₀⟩ := hsurj x₂
  obtain ⟨u, huT, hmax⟩ := exists_mem_forall_eq_of_specializes hTclosed
    ⟨u₀, by rw [Set.mem_preimage, hu₀]; exact h₁₂.mem_closure⟩
  -- every point of the common closure specializing to the image of `u` is that image
  have key : ∀ x' : points B S hS 𝒳.val 𝒳.property,
      x' ∈ closure ({x₁} : Set (points B S hS 𝒳.val 𝒳.property)) →
      x' ⤳ spacePointMap B S hS (yoneda.obj U) 𝒳 f.hom u →
      x' = spacePointMap B S hS (yoneda.obj U) 𝒳 f.hom u := by
    intro x' hx'C hx'spec
    obtain ⟨u', hu'spec, hu'eq⟩ := exists_specializes_spacePointMap_eq.{u, w} B S hS 𝒳 h𝒳
      (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) f hf hx'spec (hdecent x') u rfl
    rw [← hu'eq, hmax u' (by rw [Set.mem_preimage, hu'eq]; exact hx'C) hu'spec]
  have hx₁ := key x₁ (subset_closure rfl) (specializes_iff_mem_closure.2 huT)
  have hx₂ := key x₂ (hCeq ▸ subset_closure rfl)
    (specializes_iff_mem_closure.2 (hCeq ▸ huT))
  exact hx₁.trans hx₂.symm

end AlgebraicGeometry.Stack

end
