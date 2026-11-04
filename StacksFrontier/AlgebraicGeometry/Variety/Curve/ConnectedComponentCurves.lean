module

public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SmoothRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcDescentProperties.NoetherianNormalDecomposition
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AmpleSmoothIrreducible
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorDisjointUnion

/-!
# The connected components of a smooth proper scheme of dimension one over a field

Let `f : Y ⟶ Spec k` be proper and smooth of relative dimension one. Then `Y` has finitely many
connected components, each open and closed, and each — as an open subscheme of `Y` over `k` — a
smooth proper curve over `k`: it is connected and normal (smooth over a field), hence integral,
and of dimension one.

## Main definitions

* `AlgebraicGeometry.componentCount`, `AlgebraicGeometry.componentOpens`,
  `AlgebraicGeometry.componentι`: an enumeration `Fin r` of the components and the open immersions.

## Main results

* `AlgebraicGeometry.pairwise_disjoint_range_componentι`,
  `AlgebraicGeometry.iUnion_range_componentι`: the components are pairwise disjoint and cover `Y`.
* `AlgebraicGeometry.isCurve_componentι_comp`: each component is a curve.
* `AlgebraicGeometry.range_comp_subset_or_disjoint`: a continuous self-map sends a component into
  itself or misses it.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k)) [IsProper f]
  [SmoothOfRelativeDimension 1 f]

section Topology

include f

omit [SmoothOfRelativeDimension 1 f] in
/-- A scheme proper over a field is Noetherian. -/
theorem isNoetherian_of_isProper_smooth : IsNoetherian Y :=
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f
  { }

omit [SmoothOfRelativeDimension 1 f] in
/-- The underlying space of `Y` is locally connected. -/
theorem locallyConnectedSpace_of_isProper_smooth : LocallyConnectedSpace Y :=
  have := isNoetherian_of_isProper_smooth f
  TopologicalSpace.IsLocallyNoetherianSpace.locallyConnectedSpace _
    (isLocallyNoetherianSpace_of_noetherianSpace Y)

omit [SmoothOfRelativeDimension 1 f] in
/-- `Y` has finitely many connected components. -/
theorem finite_connectedComponents_of_isProper_smooth : Finite (_root_.ConnectedComponents Y) := by
  have := locallyConnectedSpace_of_isProper_smooth f
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f
  have : DiscreteTopology (_root_.ConnectedComponents Y) :=
    _root_.ConnectedComponents.discreteTopology_iff.mpr fun _ => isOpen_connectedComponent
  exact finite_of_compact_of_discrete

end Topology

/-- The number of connected components of a scheme. -/
def componentCount (X : Scheme.{u}) : ℕ :=
  Nat.card (_root_.ConnectedComponents X)

/-- An enumeration of the connected components. -/
def componentEquiv : Fin (componentCount Y) ≃ _root_.ConnectedComponents Y :=
  haveI := finite_connectedComponents_of_isProper_smooth f
  (Finite.equivFin (_root_.ConnectedComponents Y)).symm

/-- A point of the `i`-th connected component. -/
def componentPoint (i : Fin (componentCount Y)) : Y :=
  (ConnectedComponents.surjective_coe (componentEquiv f i)).choose

omit [SmoothOfRelativeDimension 1 f] in
/-- `componentPoint f i` lies in the `i`-th connected component. -/
theorem componentPoint_spec (i : Fin (componentCount Y)) :
    (componentPoint f i : _root_.ConnectedComponents Y) = componentEquiv f i :=
  (ConnectedComponents.surjective_coe (componentEquiv f i)).choose_spec

/-- The `i`-th connected component, as an open subset. -/
def componentOpens (i : Fin (componentCount Y)) : Y.Opens :=
  haveI := locallyConnectedSpace_of_isProper_smooth f
  ⟨connectedComponent (componentPoint f i), isOpen_connectedComponent⟩

/-- The open immersion of the `i`-th connected component. -/
abbrev componentι (i : Fin (componentCount Y)) : (componentOpens f i).toScheme ⟶ Y :=
  (componentOpens f i).ι

omit [SmoothOfRelativeDimension 1 f] in
/-- The image of `componentι f i` is the connected component of `componentPoint f i`. -/
theorem range_componentι (i : Fin (componentCount Y)) :
    Set.range (componentι f i).base = connectedComponent (componentPoint f i) := by
  rw [Scheme.Opens.range_ι]
  rfl

omit [SmoothOfRelativeDimension 1 f] in
/-- Distinct indices give distinct connected components. -/
theorem connectedComponent_componentPoint_injective :
    Function.Injective fun i => connectedComponent (componentPoint f i) := by
  intro i j h
  apply (componentEquiv f).injective
  rwa [← componentPoint_spec, ← componentPoint_spec, ConnectedComponents.coe_eq_coe]

omit [SmoothOfRelativeDimension 1 f] in
/-- The images of the components are pairwise disjoint. -/
theorem pairwise_disjoint_range_componentι :
    Pairwise fun i j => Disjoint (Set.range (componentι f i).base)
      (Set.range (componentι f j).base) := by
  intro i j hij
  rw [range_componentι, range_componentι]
  exact connectedComponent_disjoint fun h =>
    hij (connectedComponent_componentPoint_injective f h)

omit [SmoothOfRelativeDimension 1 f] in
/-- The images of the components cover `Y`. -/
theorem iUnion_range_componentι : ⋃ i, Set.range (componentι f i).base = Set.univ := by
  refine Set.eq_univ_of_forall fun y => Set.mem_iUnion.mpr ?_
  obtain ⟨i, hi⟩ := (componentEquiv f).surjective (y : _root_.ConnectedComponents Y)
  refine ⟨i, ?_⟩
  rw [range_componentι]
  have h := componentPoint_spec f i
  rw [hi, ConnectedComponents.coe_eq_coe] at h
  rw [h]
  exact mem_connectedComponent

omit [SmoothOfRelativeDimension 1 f] in
/-- The image of each component is clopen. -/
theorem isClopen_range_componentι (i : Fin (componentCount Y)) :
    IsClopen (Set.range (componentι f i).base) := by
  have := locallyConnectedSpace_of_isProper_smooth f
  rw [range_componentι]
  exact isClopen_connectedComponent

/-- The inclusion of each component is a closed immersion. -/
instance isClosedImmersion_componentι (i : Fin (componentCount Y)) :
    IsClosedImmersion (componentι f i) :=
  IsClosedImmersion.of_isPreimmersion _ (isClopen_range_componentι f i).isClosed

/-- Each component is proper over `k`. -/
instance isProper_componentι_comp (i : Fin (componentCount Y)) :
    IsProper (componentι f i ≫ f) := inferInstance

/-- Each component is smooth of relative dimension one over `k`. -/
instance smoothOfRelativeDimension_componentι_comp (i : Fin (componentCount Y)) :
    SmoothOfRelativeDimension 1 (componentι f i ≫ f) := by
  simpa using (inferInstance : SmoothOfRelativeDimension (0 + 1) (componentι f i ≫ f))

/-- Each component is connected. -/
instance connectedSpace_component (i : Fin (componentCount Y)) :
    ConnectedSpace (componentOpens f i).toScheme := by
  change ConnectedSpace ↥(connectedComponent (componentPoint f i))
  exact isConnected_iff_connectedSpace.mp isConnected_connectedComponent

/-- **Each connected component is a smooth proper curve.** -/
instance isCurve_componentι_comp (i : Fin (componentCount Y)) :
    IsCurve k (componentι f i ≫ f) := by
  have hs : Smooth (componentι f i ≫ f) := SmoothOfRelativeDimension.smooth 1 _
  have : IsNormal (componentOpens f i).toScheme :=
    isNormal_of_smooth_over_field (componentι f i ≫ f)
  have : IsNoetherian (componentOpens f i).toScheme :=
    isNoetherian_of_isProper_smooth (componentι f i ≫ f)
  have : IrreducibleSpace (componentOpens f i).toScheme :=
    irreducibleSpace_of_isNormal_of_connectedSpace _ inferInstance
  have : IsIntegral (componentOpens f i).toScheme :=
    isIntegral_of_irreducibleSpace_of_isReduced _
  exact { toIsVariety := { }
          topologicalKrullDim_eq_one :=
            topologicalKrullDim_eq_of_smoothOfRelativeDimension (componentι f i ≫ f) 1 }

omit [SmoothOfRelativeDimension 1 f] in
/-- **A continuous self-map sends a connected component into itself or misses it.** -/
theorem range_comp_subset_or_disjoint (φ : Y ⟶ Y) (i : Fin (componentCount Y)) :
    Set.range (componentι f i ≫ φ).base ⊆ Set.range (componentι f i).base ∨
      Disjoint (Set.range (componentι f i ≫ φ).base) (Set.range (componentι f i).base) := by
  rw [range_componentι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    range_componentι]
  have hconn : _root_.IsConnected (φ.base '' connectedComponent (componentPoint f i)) :=
    isConnected_connectedComponent.image _ φ.base.hom.continuous.continuousOn
  have hsub := hconn.isPreconnected.subset_connectedComponent
    (Set.mem_image_of_mem _ (mem_connectedComponent (x := componentPoint f i)))
  by_cases h : connectedComponent (φ.base (componentPoint f i)) =
      connectedComponent (componentPoint f i)
  · exact Or.inl (h ▸ hsub)
  · exact Or.inr ((connectedComponent_disjoint h).mono_left hsub)

end AlgebraicGeometry

end
