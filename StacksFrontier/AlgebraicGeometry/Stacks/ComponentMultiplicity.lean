module

public import Mathlib.Topology.NoetherianSpace
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Coverings

/-!
# Irreducible components of a locally Noetherian algebraic stack

Let `f : U → 𝒳` be a smooth 1-morphism to a locally Noetherian algebraic stack over `S` from the
algebraic stack of a scheme `U` of the site. The closure of the image of any irreducible component
of `U` is an irreducible component of the space of points of Stacks 04XG and Stacks 04XL of `𝒳`,
and when `f` is surjective every irreducible component of that space arises this way.

The statements are made about `AlgebraicGeometry.Stack.AlgebraicStacks.chartPointMap`, the map on
points of the chart read as a map out of the topological space of `U` along the homeomorphism
`AlgebraicGeometry.Stack.pointsHomeomorphScheme`.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.chartPointMap`: the map from the topological space of a
  scheme `U` of the site to the points of an algebraic stack induced by a 1-morphism from the
  algebraic stack of `U`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.continuous_chartPointMap`,
  `AlgebraicGeometry.Stack.AlgebraicStacks.isOpenMap_chartPointMap` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.surjective_chartPointMap`: the chart map on points is
  continuous, is open when the 1-morphism is smooth, and is surjective when the 1-morphism is.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyNoetherianSpace_of_isSmooth`: a smooth scheme
  chart of a locally Noetherian algebraic stack has locally Noetherian topological space.
* `AlgebraicGeometry.Stack.AlgebraicStacks.closure_image_chartPointMap_mem_irreducibleComponents`:
  the closure of the image of an irreducible component of a smooth scheme chart is an irreducible
  component.
* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_mem_irreducibleComponents_closure_image_eq`: a
  surjective smooth chart gives every irreducible component.

## Implementation notes

"`𝒳` is locally Noetherian" is the existential smooth-atlas condition of Stacks 04YF and
Stacks 04YG at the property `AlgebraicGeometry.IsLocallyNoetherian` of schemes, spelled
`AlgebraicGeometry.Stack.HasPropertyOnSomeSchemeAtlas`; this is the same hypothesis Stacks 0DQI
carries, and no named predicate "locally Noetherian algebraic stack" is used because Stacks 04YG
has no library site of its own.

The space of points of an algebraic stack has two spellings of its fibred-in-groupoids witness:
`AlgebraicGeometry.Stack.AlgebraicStacks.points` reads it off the algebraic-stack condition with
`Classical.choose`, while `AlgebraicGeometry.Stack.pointTopology` and Stacks 06R7 use the witness
bundled in the underlying `CategoryTheory.CatFiberedInGroupoids`. The two are proofs of the same
`Prop`, namely `CategoryTheory.Functor.IsFiberedInGroupoids`, so definitional proof irrelevance
identifies them and the choice is immaterial; the statements here are written in the first
spelling, which is the one Stacks 04ZS is stated in.

## References

* [Stacks Project, Tag 01OZ](https://stacks.math.columbia.edu/tag/01OZ)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 04YF](https://stacks.math.columbia.edu/tag/04YF)
* [Stacks Project, Tag 04YG](https://stacks.math.columbia.edu/tag/04YG)
* [Stacks Project, Tag 04ZS](https://stacks.math.columbia.edu/tag/04ZS)
* [Stacks Project, Tag 06R7](https://stacks.math.columbia.edu/tag/06R7)
* [Stacks Project, Tag 075U](https://stacks.math.columbia.edu/tag/075U)
* [Stacks Project, Tag 0DNP](https://stacks.math.columbia.edu/tag/0DNP)
* [Stacks Project, Tag 0DQI](https://stacks.math.columbia.edu/tag/0DQI)
* [Stacks Project, Tag 0DR5](https://stacks.math.columbia.edu/tag/0DR5)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

open TopologicalSpace

universe u w

/-! ### Irreducible components under a continuous open map -/

/-- An irreducible subset which contains a nonempty open subset has closure an irreducible
component. -/
@[ega "0 2.1.6" "special case"]
private theorem closure_mem_irreducibleComponents_of_isOpen_subset
    {α : Type*} [TopologicalSpace α] {s t : Set α} (hs : IsIrreducible s)
    (ht : IsOpen t) (hne : t.Nonempty) (hts : t ⊆ s) :
    closure s ∈ irreducibleComponents α := by
  refine ⟨isIrreducible_iff_closure.mpr hs, ?_⟩
  intro u hu hsu x hx
  rw [mem_closure_iff]
  intro v hv hxv
  obtain ⟨y, hy⟩ := hne
  obtain ⟨z, hz⟩ := hu.2 v t hv ht ⟨x, hx, hxv⟩ ⟨y, hsu (subset_closure (hts hy)), hy⟩
  exact ⟨z, hz.2.1, hts hz.2.2⟩

/-- For a continuous open map, the closure of the image of an irreducible set containing a nonempty
open set is an irreducible component of the target. -/
private theorem closure_image_mem_irreducibleComponents_of_isOpenMap
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] (f : α → β)
    (hf : Continuous f) (ho : IsOpenMap f) {s t : Set α}
    (hs : IsIrreducible s) (ht : IsOpen t) (hne : t.Nonempty) (hts : t ⊆ s) :
    closure (f '' s) ∈ irreducibleComponents β := by
  refine closure_mem_irreducibleComponents_of_isOpen_subset (hs.image f hf.continuousOn)
    (ho t ht) ⟨f hne.choose, ⟨hne.choose, hne.choose_spec, rfl⟩⟩ ?_
  rintro y ⟨x, hx, rfl⟩
  exact ⟨x, hts hx, rfl⟩

/-- An irreducible component of a locally Noetherian space contains a nonempty open set. -/
private theorem exists_isOpen_nonempty_subset_of_isLocallyNoetherianSpace
    {α : Type*} [TopologicalSpace α] (hα : IsLocallyNoetherianSpace α)
    {T : Set α} (hT : T ∈ irreducibleComponents α) :
    ∃ V : Set α, IsOpen V ∧ V.Nonempty ∧ V ⊆ T := by
  obtain ⟨x, hx⟩ := hT.1.nonempty
  obtain ⟨W, hW, hxW, hWN⟩ := hα x
  have := hWN
  have hcomp : (Subtype.val : W → α) ⁻¹' T ∈ irreducibleComponents W :=
    preimage_mem_irreducibleComponents hT hW.isOpenEmbedding_subtypeVal
      ⟨x, hx, ⟨⟨x, hxW⟩, rfl⟩⟩
  obtain ⟨V, hV, hVne, hVT⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hcomp
  exact ⟨Subtype.val '' V, hW.isOpenEmbedding_subtypeVal.isOpenMap _ hV, hVne.image _, by
    rintro _ ⟨v, hv, rfl⟩
    exact hVT hv⟩

/-- For a surjective map `f` onto a locally Noetherian space such that the closure of the image of
every irreducible component of the source is an irreducible component of the target, every
irreducible component of the target is the closure of the image of an irreducible component of the
source. -/
private theorem exists_mem_irreducibleComponents_closure_image_eq_of_surjective
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (hβ : IsLocallyNoetherianSpace β) (f : α → β) (hs : Function.Surjective f)
    (hc : ∀ T ∈ irreducibleComponents α, closure (f '' T) ∈ irreducibleComponents β)
    {Z : Set β} (hZ : Z ∈ irreducibleComponents β) :
    ∃ T ∈ irreducibleComponents α, closure (f '' T) = Z := by
  obtain ⟨V, hV, ⟨y, hy⟩, hVZ⟩ := exists_isOpen_nonempty_subset_of_isLocallyNoetherianSpace hβ hZ
  obtain ⟨x, rfl⟩ := hs y
  have hT := irreducibleComponent_mem_irreducibleComponents x
  have hC := hc (irreducibleComponent x) hT
  have hsub : closure (f '' irreducibleComponent x) ⊆ Z := by
    have hmeet : (closure (f '' irreducibleComponent x) ∩ V).Nonempty :=
      ⟨f x, subset_closure ⟨x, mem_irreducibleComponent, rfl⟩, hy⟩
    exact (subset_closure_inter_of_isPreirreducible_of_isOpen hC.1.2 hV hmeet).trans
      (closure_minimal (fun _ h => hVZ h.2) (isClosed_of_mem_irreducibleComponents _ hZ))
  exact ⟨irreducibleComponent x, hT, subset_antisymm hsub (hC.2 hZ.1 hsub)⟩

/-! ### The map on points of a scheme chart -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The map on points induced by a 1-morphism to an algebraic stack over `S` from the algebraic
stack of a scheme `U` of the site, read as a map out of the topological space of `U` along the
homeomorphism `AlgebraicGeometry.Stack.pointsHomeomorphScheme` identifying the points of the
algebraic stack of `U` with `U`. -/
noncomputable def chartPointMap (U : BigFppfOver B S hS)
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
    (f : Stack.schemeStack.{u, w} B S hS U ⟶ 𝒳) :
    (BigFppfOver.toScheme B S hS).obj U → points B S hS 𝒳 :=
  letI := Stack.pointTopology B S hS (Stack.schemeFibredCategory B S hS U)
  pointsMap B S hS f ∘ (Stack.pointsHomeomorphScheme B S hS U).symm

/-- The chart map on points is continuous for the topology of Stacks 04XL. -/
theorem continuous_chartPointMap (U : BigFppfOver B S hS)
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
    (f : Stack.schemeStack.{u, w} B S hS U ⟶ 𝒳) :
    letI := Stack.pointTopology B S hS 𝒳.val
    Continuous (chartPointMap B S hS U 𝒳 f) := by
  let _ := Stack.pointTopology B S hS 𝒳.val
  let _ := Stack.pointTopology B S hS (Stack.schemeStack.{u, w} B S hS U).val
  exact (Stack.continuous_pointsMap B S hS _ _ f.hom.hom).comp
    (Stack.pointsHomeomorphScheme B S hS U).symm.continuous

/-- The chart map on points of a smooth 1-morphism from the algebraic stack of a scheme of the site
is open (Stacks 06R7). -/
theorem isOpenMap_chartPointMap (U : BigFppfOver B S hS)
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
    (f : Stack.schemeStack.{u, w} B S hS U ⟶ 𝒳) (hf : IsSmooth B S hS f) :
    letI := Stack.pointTopology B S hS 𝒳.val
    IsOpenMap (chartPointMap B S hS U 𝒳 f) := by
  let _ := Stack.pointTopology B S hS 𝒳.val
  let _ := Stack.pointTopology B S hS (Stack.schemeStack.{u, w} B S hS U).val
  exact (isOpenMap_pointsMap B S hS f (isFlat_of_isSmooth B S hS f hf)
    (isLocallyOfFinitePresentation_of_isSmooth B S hS f hf)).comp
      (Stack.pointsHomeomorphScheme B S hS U).symm.isOpenMap

/-- The chart map on points of a surjective 1-morphism of Stacks 04ZS is surjective. -/
theorem surjective_chartPointMap (U : BigFppfOver B S hS)
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
    (f : Stack.schemeStack.{u, w} B S hS U ⟶ 𝒳) (hf : Stack.IsSurjective B S hS f) :
    Function.Surjective (chartPointMap B S hS U 𝒳 f) := by
  let _ := Stack.pointTopology B S hS (Stack.schemeFibredCategory B S hS U)
  exact hf.comp (Stack.pointsHomeomorphScheme B S hS U).symm.surjective

/-- A scheme of the site carrying a smooth 1-morphism from its algebraic stack to a locally
Noetherian algebraic stack over `S` is locally Noetherian. -/
theorem isLocallyNoetherian_of_isSmooth (U : BigFppfOver B S hS)
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
    (hN : Stack.HasPropertyOnSomeSchemeAtlas B S hS
      (fun X : Scheme.{u} => IsLocallyNoetherian X) 𝒳)
    (f : Stack.schemeStack.{u, w} B S hS U ⟶ 𝒳) (hf : IsSmooth B S hS f) :
    IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U) :=
  let _ : ObjectProperty.IsLocal (fun X : Scheme.{u} => IsLocallyNoetherian X)
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})) :=
    ObjectProperty.IsLocal.of_le Scheme.smoothPrecoverage_le_fppfPrecoverage
  (Stack.exists_scheme_atlas_iff_forall_scheme B S hS
    (fun X : Scheme.{u} => IsLocallyNoetherian X) 𝒳).1 hN U f hf

/-- A scheme of the site carrying a smooth 1-morphism from its algebraic stack to a locally
Noetherian algebraic stack over `S` has locally Noetherian topological space. -/
theorem isLocallyNoetherianSpace_of_isSmooth (U : BigFppfOver B S hS)
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
    (hN : Stack.HasPropertyOnSomeSchemeAtlas B S hS
      (fun X : Scheme.{u} => IsLocallyNoetherian X) 𝒳)
    (f : Stack.schemeStack.{u, w} B S hS U ⟶ 𝒳) (hf : IsSmooth B S hS f) :
    IsLocallyNoetherianSpace ((BigFppfOver.toScheme B S hS).obj U) :=
  let _ : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U) :=
    isLocallyNoetherian_of_isSmooth B S hS U 𝒳 hN f hf
  isLocallyNoetherianSpace_of_isLocallyNoetherian _

/-! ### Stacks 0DR5 -/

/-- For a smooth 1-morphism to a locally Noetherian algebraic stack over `S` from the algebraic
stack of a scheme `U` of the site, the closure of the image of any irreducible component of `U` is
an irreducible component of the space of points of Stacks 04XL. -/
@[stacks 0DR5 "closure of the image of an irreducible component"]
theorem closure_image_chartPointMap_mem_irreducibleComponents (U : BigFppfOver B S hS)
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
    (hN : Stack.HasPropertyOnSomeSchemeAtlas B S hS
      (fun X : Scheme.{u} => IsLocallyNoetherian X) 𝒳)
    (f : Stack.schemeStack.{u, w} B S hS U ⟶ 𝒳) (hf : IsSmooth B S hS f)
    (T : Set ((BigFppfOver.toScheme B S hS).obj U))
    (hT : T ∈ irreducibleComponents ((BigFppfOver.toScheme B S hS).obj U)) :
    letI := Stack.pointTopology B S hS 𝒳.val
    closure (chartPointMap B S hS U 𝒳 f '' T) ∈ irreducibleComponents (points B S hS 𝒳) := by
  let _ := Stack.pointTopology B S hS 𝒳.val
  obtain ⟨V, hV, hVne, hVT⟩ := exists_isOpen_nonempty_subset_of_isLocallyNoetherianSpace
    (isLocallyNoetherianSpace_of_isSmooth B S hS U 𝒳 hN f hf) hT
  exact closure_image_mem_irreducibleComponents_of_isOpenMap (chartPointMap B S hS U 𝒳 f)
    (continuous_chartPointMap B S hS U 𝒳 f) (isOpenMap_chartPointMap B S hS U 𝒳 f hf)
    hT.1 hV hVne hVT

/-- For a smooth *surjective* 1-morphism to a locally Noetherian algebraic stack over `S` from the
algebraic stack of a scheme `U` of the site, every irreducible component of the space of points of
Stacks 04XL is the closure of the image of an irreducible component of `U`. -/
@[stacks 0DR5 "surjective charts give every irreducible component"]
theorem exists_mem_irreducibleComponents_closure_image_eq (U : BigFppfOver B S hS)
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
    (hN : Stack.HasPropertyOnSomeSchemeAtlas B S hS
      (fun X : Scheme.{u} => IsLocallyNoetherian X) 𝒳)
    (f : Stack.schemeStack.{u, w} B S hS U ⟶ 𝒳) (hf : IsSmooth B S hS f)
    (hfs : Stack.IsSurjective B S hS f) :
    letI := Stack.pointTopology B S hS 𝒳.val
    ∀ Z ∈ irreducibleComponents (points B S hS 𝒳),
      ∃ T ∈ irreducibleComponents ((BigFppfOver.toScheme B S hS).obj U),
        closure (chartPointMap B S hS U 𝒳 f '' T) = Z := by
  let _ := Stack.pointTopology B S hS 𝒳.val
  intro Z hZ
  exact exists_mem_irreducibleComponents_closure_image_eq_of_surjective
    (isLocallyNoetherianSpace_points_of_isLocallyNoetherian B S hS 𝒳 hN)
    (chartPointMap B S hS U 𝒳 f) (surjective_chartPointMap B S hS U 𝒳 f hfs)
    (fun T hT => closure_image_chartPointMap_mem_irreducibleComponents B S hS U 𝒳 hN f hf T hT) hZ

end AlgebraicGeometry.Stack.AlgebraicStacks

end
