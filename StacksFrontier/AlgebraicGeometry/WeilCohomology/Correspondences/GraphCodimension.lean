module

public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductAssociativity
public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.Base
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InverseImageDimension
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.Curves.PlaneCurveIdeal
public import StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.FlatPullbackCycles
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.CohenMacaulayRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.FieldFibreDegreeBound
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.DimensionFormula
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Formula
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.Graph
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.Transpose
public import StacksFrontier.Topology.Dimension.Codimension
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecialFibreDimension

/-!
# Preliminaries for the codimension of the graph

This file collects the topological and dimension-theoretic facts used to compute the codimension
of the graph of a morphism of smooth projective schemes over a field, together with the
construction of the graph over one equidimensional part of the target of the morphism.

## Main results

* `TopologicalSpace.IsPreirreducible.subset_of_isClopen` — an irreducible set meeting an open and
  closed set is contained in it.
* `AlgebraicGeometry.topologicalKrullDim_eq_of_forall_mem_irreducibleComponents` — a nonempty
  space all of whose irreducible components have dimension `d` has dimension `d`.
* `AlgebraicGeometry.relativeDimension_of_field_base` — a scheme over a field all of whose
  irreducible components have dimension `d` has constant fibre dimension `d`.
* `AlgebraicGeometry.topologicalKrullDimAt_eq_add_ringKrullDim_stalk` — Stacks 0A21: the local
  dimension at a point is the dimension of the closure of the point plus the dimension of the
  local ring there.
* `Stacks.WeilCohomology.graphPartMorphism` — the graph of `f` over an open and closed part of
  `X`, as a closed subscheme of the product of that part with `Y`;
  `Stacks.WeilCohomology.range_graphPartMorphism_comp_partProductι` identifies its image in
  `X ×_k Y` with the intersection `Γ_f ∩ (U × Y)`.
* `Stacks.WeilCohomology.codimension_graphPartMorphism` — **Stacks 0FG1**: that intersection has
  pure codimension `d` when `U` is equidimensional of dimension `d`.
* `Stacks.WeilCohomology.cycleAssociatedToClosedSubscheme_graphMorphism_eq_zero` and
  `Stacks.WeilCohomology.graphCorrespondence` — **Stacks 0FG1**: `[Γ_f]` is a correspondence of
  degree zero.
* `Stacks.WeilCohomology.exists_decomposition_graph_pure_codimension` — **Stacks 0FG1** in full:
  the decomposition `X = ∐_d X_d`, the purity of `Γ_f ∩ (X_d × Y)` and the degree-zero
  correspondence.

## References

* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
* [Stacks Project, Tag 02NJ](https://stacks.math.columbia.edu/tag/02NJ)
* [Stacks Project, Tag 0FG1](https://stacks.math.columbia.edu/tag/0FG1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct
open TopologicalSpace.IrreducibleCloseds (closureSingleton)

universe u

/-! ### Irreducible subsets and open and closed subsets -/

/-- An irreducible subset meeting an open and closed subset is contained in it: otherwise the two
relatively open pieces it is cut into by that subset and its complement would be disjoint and
nonempty. -/
theorem TopologicalSpace.IsPreirreducible.subset_of_isClopen {α : Type*} [TopologicalSpace α]
    {Z S : Set α} (hZ : IsPreirreducible Z) (hS : IsClopen S) {x : α} (hxZ : x ∈ Z)
    (hxS : x ∈ S) : Z ⊆ S := by
  by_contra hsub
  obtain ⟨y, hyZ, hyS⟩ := Set.not_subset.1 hsub
  obtain ⟨z, _, hzS, hzSc⟩ := hZ _ _ hS.2 hS.1.isOpen_compl ⟨x, hxZ, hxS⟩ ⟨y, hyZ, hyS⟩
  exact hzSc hzS

namespace AlgebraicGeometry

/-! ### Constant fibre dimension over a field -/

/-- **Over a field, constant fibre dimension `d` is equidimensionality of dimension `d`.** The
spectrum of a field has a single point whose residue field is the field itself, so the only
nonempty fibre is the scheme itself. -/
@[stacks 02NJ "over a field"]
theorem equidimensional_and_topologicalKrullDim_of_relativeDimension (k : Type u) [Field k]
    {T : Scheme.{u}} (q : T ⟶ Spec (.of k)) [LocallyOfFiniteType q] [Nonempty T] (d : ℕ)
    (h : AlgebraicGeometry.RelativeDimension q d) :
    TopologicalSpace.Equidimensional T ∧ topologicalKrullDim T = (d : WithBot ℕ∞) := by
  obtain ⟨t⟩ := ‹Nonempty T›
  have _ : IsIso ((Spec (CommRingCat.of k)).fromSpecResidueField (q.base t)) :=
    isIso_fromSpecResidueField_of_field k (q.base t)
  have _ : IsIso (q.fiberι (q.base t)) := inferInstanceAs (IsIso (pullback.fst _ _))
  obtain ⟨heq, hdim⟩ := h (q.base t) ⟨q.asFiber t⟩
  refine ⟨TopologicalSpace.Equidimensional.of_homeomorph
    (q.fiberι (q.base t)).homeomorph.symm heq, ?_⟩
  rw [← hdim, (q.fiberι (q.base t)).homeomorph.isHomeomorph.topologicalKrullDim_eq]

/-! ### The local dimension, the dimension of a point closure and the local ring -/

/-- **Stacks 0A21.** On a scheme locally of finite type over a field the dimension at a point is
the dimension of the closure of that point plus the dimension of the local ring there. Both
summands are read off the dimension formula of Stacks 0A21 at the same point. -/
@[stacks 0A21 "local dimension, point closure and local ring", ega "IV 10.6.3" "special case"]
theorem topologicalKrullDimAt_eq_add_ringKrullDim_stalk (k : Type u) [Field k] {T : Scheme.{u}}
    (q : T ⟶ Spec (.of k)) [LocallyOfFiniteType q] (t : T) :
    topologicalKrullDimAt T t =
      topologicalKrullDim (closure ({t} : Set T)) + ringKrullDim (T.presheaf.stalk t) := by
  rw [topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k T q t,
    topologicalKrullDim_closure_singleton_eq_trdeg k T q t]

end AlgebraicGeometry


/-! ### Codimension and the local ring -/

/-- **Stacks 02IZ.** The codimension of the closure of a point of a scheme is the dimension of
the local ring there. -/
@[ega "IV 21.6.2" "partial", sga "1 II 5.9" "partial"]
theorem codimension_closureSingleton_eq_ringKrullDim_stalk {T : Scheme.{u}} (t : T) :
    ((codimension (closureSingleton t) : ℕ∞) : WithBot ℕ∞) =
      ringKrullDim (T.presheaf.stalk t) := by
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight, codimension_eq_coheight,
    Stacks.Chow.coheight_closureSingleton_eq_coheight_point]

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k] {X Y : Scheme.{u}}

/-! ### The graph over one part of the target of the morphism -/

/-- The graph of `f : Y ⟶ X` over an open subscheme `U ⊆ X`: the morphism
`(f|_{f⁻¹U}, incl) : f⁻¹U ⟶ U ×_k Y` into the product of `U` with `Y`. Its image is the
intersection `Γ_f ∩ (U × Y)` of the graph of `f` with `U × Y`. -/
def graphPartMorphism (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) (f : Y ⟶ X)
    (hf : f ≫ sX = sY) (U : X.Opens) :
    (f ⁻¹ᵁ U).toScheme ⟶ (pullback (U.ι ≫ sX) sY : Scheme.{u}) :=
  pullback.lift (f ∣_ U) (f ⁻¹ᵁ U).ι (by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hf])

/-- The graph of `f` over `U` followed by the projection to `Y` is the inclusion of `f⁻¹U`. -/
@[simp]
theorem graphPartMorphism_snd (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) (f : Y ⟶ X)
    (hf : f ≫ sX = sY) (U : X.Opens) :
    graphPartMorphism sX sY f hf U ≫ pullback.snd (U.ι ≫ sX) sY = (f ⁻¹ᵁ U).ι :=
  pullback.lift_snd _ _ _

/-- The graph of `f` over `U` followed by the projection to `U` is the restriction
`f ∣_ U : f⁻¹U ⟶ U`. -/
@[simp]
theorem graphPartMorphism_fst (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) (f : Y ⟶ X)
    (hf : f ≫ sX = sY) (U : X.Opens) :
    graphPartMorphism sX sY f hf U ≫ pullback.fst (U.ι ≫ sX) sY = f ∣_ U :=
  pullback.lift_fst _ _ _


/-- The inclusion `U ×_k Y ⟶ X ×_k Y` of the product of an open subscheme `U ⊆ X` with `Y`. -/
def partProductι (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) (U : X.Opens) :
    (pullback (U.ι ≫ sX) sY : Scheme.{u}) ⟶ (pullback sX sY : Scheme.{u}) :=
  pullback.lift (pullback.fst (U.ι ≫ sX) sY ≫ U.ι) (pullback.snd (U.ι ≫ sX) sY)
    (by rw [Category.assoc]; exact pullback.condition)

/-- The inclusion `U ×_k Y ⟶ X ×_k Y` followed by the projection to `X` is the projection to `U`
followed by the inclusion `U ⟶ X`. -/
@[simp]
theorem partProductι_fst (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) (U : X.Opens) :
    partProductι sX sY U ≫ pullback.fst sX sY = pullback.fst (U.ι ≫ sX) sY ≫ U.ι :=
  pullback.lift_fst _ _ _

/-- The inclusion `U ×_k Y ⟶ X ×_k Y` followed by the projection to `Y` is the projection of
`U ×_k Y` to `Y`. -/
@[simp]
theorem partProductι_snd (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) (U : X.Opens) :
    partProductι sX sY U ≫ pullback.snd sX sY = pullback.snd (U.ι ≫ sX) sY :=
  pullback.lift_snd _ _ _

/-- The graph of `f` over `U`, viewed inside `X ×_k Y`, is the restriction of the graph of `f` to
the open and closed subscheme `f⁻¹U` of `Y`. -/
theorem graphPartMorphism_comp_partProductι (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    (f : Y ⟶ X) (hf : f ≫ sX = sY) (U : X.Opens) :
    graphPartMorphism sX sY f hf U ≫ partProductι sX sY U =
      (f ⁻¹ᵁ U).ι ≫ graphMorphism sX sY f hf := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, partProductι_fst, ← Category.assoc, graphPartMorphism_fst,
      morphismRestrict_ι, Category.assoc, graphMorphism_fst]
  · rw [Category.assoc, partProductι_snd, graphPartMorphism_snd, Category.assoc,
      graphMorphism_snd, Category.comp_id]

/-- **`Γ_f ∩ (U × Y)` is the image of `Stacks.WeilCohomology.graphPartMorphism`.** Inside
`X ×_k Y`, the image of the graph of `f` over `U` is the intersection of the graph `Γ_f` of `f`
with `U ×_k Y`. This is the identification which makes the codimension statement below a
statement about `Γ_f ∩ (U × Y)`. -/
theorem range_graphPartMorphism_comp_partProductι (sX : X ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k)) (f : Y ⟶ X) (hf : f ≫ sX = sY) (U : X.Opens) :
    Set.range (graphPartMorphism sX sY f hf U ≫ partProductι sX sY U).base =
      Set.range (graphMorphism sX sY f hf).base ∩ Set.range (partProductι sX sY U).base := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨w, rfl⟩
    refine ⟨?_, ⟨(graphPartMorphism sX sY f hf U).base w, rfl⟩⟩
    rw [graphPartMorphism_comp_partProductι]
    exact ⟨(f ⁻¹ᵁ U).ι.base w, rfl⟩
  · rintro x ⟨⟨y, hy⟩, ⟨w, hw⟩⟩
    have h1 : (pullback.fst sX sY).base x = f.base y := by
      rw [← hy, ← Scheme.Hom.comp_apply, graphMorphism_fst]
    have h2 : (pullback.fst sX sY).base x =
        U.ι.base ((pullback.fst (U.ι ≫ sX) sY).base w) := by
      rw [← hw, ← Scheme.Hom.comp_apply, partProductι_fst]
      rfl
    have hyV : y ∈ (f ⁻¹ᵁ U : Y.Opens) := by
      show f.base y ∈ U
      rw [← h1, h2]
      exact ((pullback.fst (U.ι ≫ sX) sY).base w).2
    refine ⟨(⟨y, hyV⟩ : (f ⁻¹ᵁ U).toScheme), ?_⟩
    rw [graphPartMorphism_comp_partProductι]
    exact hy

/-- The inclusion of an open and closed subscheme is a closed immersion. -/
@[ega "IV 4.9.6" "more general"]
theorem isClosedImmersion_ι_of_isClopen {U : X.Opens} (hU : IsClopen (U : Set X)) :
    IsClosedImmersion U.ι :=
  IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hU.1)

/-- The preimage of an open and closed subset of `X` is open and closed in `Y`. -/
private theorem isClopen_preimage (f : Y ⟶ X) {U : X.Opens} (hU : IsClopen (U : Set X)) :
    IsClopen ((f ⁻¹ᵁ U : Y.Opens) : Set Y) := by
  simpa only [Scheme.Hom.coe_preimage] using hU.preimage f.continuous

/-- The graph of `f` over an open and closed part `U` of `X` is a closed immersion: composed with
the projection to `Y` it is the inclusion of the open and closed subscheme `f⁻¹U`. -/
theorem isClosedImmersion_graphPartMorphism (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    [IsSeparated sX] (f : Y ⟶ X) (hf : f ≫ sX = sY) {U : X.Opens} (hU : IsClopen (U : Set X)) :
    IsClosedImmersion (graphPartMorphism sX sY f hf U) :=
  have : IsClosedImmersion (f ⁻¹ᵁ U).ι :=
    isClosedImmersion_ι_of_isClopen (isClopen_preimage f hU)
  have : IsClosedImmersion
      (graphPartMorphism sX sY f hf U ≫ pullback.snd (U.ι ≫ sX) sY) := by
    rw [graphPartMorphism_snd]; infer_instance
  have : IsSeparated (U.ι ≫ sX) := inferInstance
  IsClosedImmersion.of_comp _ (pullback.snd (U.ι ≫ sX) sY)

end Stacks.WeilCohomology


/-! ### Generic points of an open and closed subscheme -/

/-- A generic point of an irreducible component of an open and closed subset is, read in the
ambient space, a generic point of an irreducible component of it. -/
theorem mem_genericPoints_val_of_isClopen {α : Type*} [TopologicalSpace α] {S : Set α}
    (hS : IsClopen S) (ξ : S) (hξ : closure ({ξ} : Set S) ∈ irreducibleComponents S) :
    closure ({(ξ : α)} : Set α) ∈ irreducibleComponents α := by
  obtain ⟨C, hC, hyC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    ({(ξ : α)} : Set α) isIrreducible_singleton
  have hyC' : (ξ : α) ∈ C := hyC rfl
  have hCclosed : IsClosed C := isClosed_of_mem_irreducibleComponents C hC
  have hCS : C ⊆ S := hC.1.2.subset_of_isClopen hS hyC' ξ.2
  have hpre : (Subtype.val ⁻¹' C) ∈ irreducibleComponents S :=
    preimage_mem_irreducibleComponents hC hS.2.isOpenEmbedding_subtypeVal
      ⟨(ξ : α), hyC', ⟨ξ, rfl⟩⟩
  have hsub : closure ({ξ} : Set S) ⊆ Subtype.val ⁻¹' C :=
    closure_minimal (Set.singleton_subset_iff.2 hyC') (hCclosed.preimage continuous_subtype_val)
  have heq : closure ({ξ} : Set S) = Subtype.val ⁻¹' C :=
    Set.Subset.antisymm hsub (hξ.2 hpre.1 hsub)
  have hce : Topology.IsClosedEmbedding (Subtype.val : S → α) :=
    hS.1.isClosedEmbedding_subtypeVal
  have : closure ({(ξ : α)} : Set α) = C := by
    rw [← Set.image_singleton, hce.closure_image_eq, heq,
      Set.image_preimage_eq_of_subset (by rwa [Subtype.range_val])]
  rw [this]
  exact hC

namespace Stacks.WeilCohomology

section Purity

open Stacks.Chow

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
  (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
  [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [IsSeparated sX]
  (f : Y ⟶ X) (hf : f ≫ sX = sY) {U : X.Opens}

attribute [local instance] isClosedImmersion_graphMorphism

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] in
/-- **The delta-dimension of a point of the graph is that of the corresponding point of `Y`.**
The graph morphism is a closed immersion over the base, so it changes neither the image point in
the base nor the residue field. -/
theorem relativeDimension_graphPartMorphism (hU : IsClopen (U : Set X))
    (ξ : (f ⁻¹ᵁ U).toScheme) :
    relativeDimension (fieldChowSituation k).dimensionFunction
        (pullback.snd (U.ι ≫ sX) sY ≫ sY) ((graphPartMorphism sX sY f hf U).base ξ) =
      relativeDimension (fieldChowSituation k).dimensionFunction sY ξ.1 := by
  have hγ : IsClosedImmersion (graphPartMorphism sX sY f hf U) :=
    isClosedImmersion_graphPartMorphism sX sY f hf hU
  have hι : IsClosedImmersion (f ⁻¹ᵁ U).ι :=
    isClosedImmersion_ι_of_isClopen (isClopen_preimage f hU)
  rw [← relativeDimension_comp_closedImmersion (fieldChowSituation k).dimensionFunction
      (graphPartMorphism sX sY f hf U) (pullback.snd (U.ι ≫ sX) sY ≫ sY) ξ,
    show (graphPartMorphism sX sY f hf U ≫ pullback.snd (U.ι ≫ sX) sY ≫ sY) =
        (f ⁻¹ᵁ U).ι ≫ sY from by rw [← Category.assoc, graphPartMorphism_snd],
    relativeDimension_comp_closedImmersion (fieldChowSituation k).dimensionFunction
      (f ⁻¹ᵁ U).ι sY ξ]
  rfl

omit [IsSeparated sX] in
/-- **The delta-dimension of an irreducible component of `U ×_k Y` through a point of the
graph.** The projection `U ×_k Y ⟶ Y` is flat of relative dimension `d`, so by Stacks 02R8 the
component has delta-dimension `d` more than the component of `Y` beneath it; the latter is the
component of `Y` through the point of `Y` under the given point of the graph, because that point
is a generic point of `Y`. -/
theorem deltaDimension_irreducibleComponent_of_mem_graphPart (hU : IsClopen (U : Set X)) (d : ℕ)
    (hrel : AlgebraicGeometry.RelativeDimension (U.ι ≫ sX) d) (ξ : (f ⁻¹ᵁ U).toScheme)
    (hξ : closure ({ξ} : Set (f ⁻¹ᵁ U).toScheme) ∈ irreducibleComponents (f ⁻¹ᵁ U).toScheme)
    (T : irreducibleComponents (pullback (U.ι ≫ sX) sY : Scheme.{u}))
    (hzT : (graphPartMorphism sX sY f hf U).base ξ ∈ (T : Set _)) :
    deltaDimension (fieldChowSituation k) (pullback.snd (U.ι ≫ sX) sY ≫ sY)
        ⟨(T : Set _), T.2.1, isClosed_of_mem_irreducibleComponents _ T.2⟩ =
      relativeDimension (fieldChowSituation k).dimensionFunction sY ξ.1 + (d : ℤ) := by
  have hrel' : AlgebraicGeometry.RelativeDimension (pullback.snd (U.ι ≫ sX) sY) d :=
    relativeDimension_pullback_snd (U.ι ≫ sX) sY d hrel
  have hy : (pullback.snd (U.ι ≫ sX) sY).base ((graphPartMorphism sX sY f hf U).base ξ) = ξ.1 := by
    rw [← Scheme.Hom.comp_apply, graphPartMorphism_snd]
    rfl
  have hygen : closure ({ξ.1} : Set Y) ∈ irreducibleComponents Y :=
    mem_genericPoints_val_of_isClopen (isClopen_preimage f hU) ξ hξ
  obtain ⟨V', hV'⟩ := exists_irreducibleComponent_map_genericPoint
    (pullback.snd (U.ι ≫ sX) sY) T
  have hηz : T.2.1.genericPoint ⤳ (graphPartMorphism sX sY f hf U).base ξ :=
    (T.2.1.isGenericPoint_genericPoint
      (isClosed_of_mem_irreducibleComponents _ T.2)).specializes hzT
  have hspec : (pullback.snd (U.ι ≫ sX) sY).base T.2.1.genericPoint ⤳ ξ.1 := by
    rw [← hy]
    exact hηz.map (pullback.snd (U.ι ≫ sX) sY).continuous
  have hyV' : ξ.1 ∈ (V' : Set Y) := by
    rw [hV'] at hspec
    have h2 := hspec.mem_closure
    rwa [(genericPoints.isGenericPoint_ofComponent V').def] at h2
  have hsub : closure ({ξ.1} : Set Y) ⊆ (V' : Set Y) :=
    closure_minimal (Set.singleton_subset_iff.2 hyV')
      (isClosed_of_mem_irreducibleComponents _ V'.2)
  have hV'eq : (V' : Set Y) = closure ({ξ.1} : Set Y) :=
    Set.Subset.antisymm (hygen.2 V'.2.1 hsub) hsub
  have hgenV' : ((genericPoints.ofComponent V' : genericPoints Y) : Y) = ξ.1 :=
    (genericPoints.isGenericPoint_ofComponent V').eq (by rw [hV'eq]; exact isGenericPoint_closure)
  rw [deltaDimension_irreducibleComponent_eq_add (fieldChowSituation k)
    (pullback.snd (U.ι ≫ sX) sY) sY d hrel' T V' hV']
  congr 1
  rw [deltaDimension_eq_of_isGenericPoint (fieldChowSituation k) sY _
    ((genericPoints.ofComponent V' : genericPoints Y) : Y)
    (genericPoints.isGenericPoint_ofComponent V'), hgenV']

/-- A cancellation used to read off the codimension from the dimension formula. -/
private theorem eq_of_natCast_add_eq {m d : ℕ} {c : ℕ∞}
    (h : ((m + d : ℕ) : WithBot ℕ∞) = ((m : ℕ) : WithBot ℕ∞) + (c : WithBot ℕ∞)) :
    c = (d : ℕ∞) := by
  have h1 : ((m : ℕ∞) + (d : ℕ∞) : ℕ∞) = ((m : ℕ∞) + c : ℕ∞) := by
    have h2 : (((m : ℕ∞) + (d : ℕ∞) : ℕ∞) : WithBot ℕ∞) = (((m : ℕ∞) + c : ℕ∞) : WithBot ℕ∞) := by
      push_cast at h ⊢
      exact h
    exact_mod_cast h2
  exact (WithTop.add_left_cancel (ENat.coe_ne_top m) h1).symm

/-- **Stacks 0FG1: the intersection `Γ_f ∩ (X_d × Y)` has pure codimension `d`.**

Let `U ⊆ X` be an open and closed part of `X` which is equidimensional of dimension `d`, in the
sense that every irreducible component of `U` has dimension `d`. Then every irreducible component
of `Γ_f ∩ (U × Y)` has codimension `d` in `U × Y`; the components are indexed by the generic
points of `f⁻¹U`, because the graph morphism is a closed immersion with source `f⁻¹U`.

The proof is the dimension formula of Stacks 0A21 at the point: the local dimension of `U × Y`
there is the dimension of the point closure plus the codimension. The point closure has the
delta-dimension of the corresponding point of `Y`, since the graph is a closed immersion over
`k`; and the local dimension is the delta-dimension of an irreducible component of `U × Y`
through the point, which by Stacks 02R8 exceeds the delta-dimension of the component of `Y`
beneath it by `d`, the relative dimension of the flat projection `U × Y ⟶ Y`. The component of
`Y` beneath is the one through the point of `Y`, which is a generic point because `f⁻¹U` is open
and closed in `Y`. -/
@[stacks 0FG1 "graph_pure_codimension"]
theorem codimension_graphPartMorphism (hU : IsClopen (U : Set X)) (d : ℕ)
    (hrel : AlgebraicGeometry.RelativeDimension (U.ι ≫ sX) d) (ξ : (f ⁻¹ᵁ U).toScheme)
    (hξ : closure ({ξ} : Set (f ⁻¹ᵁ U).toScheme) ∈ irreducibleComponents (f ⁻¹ᵁ U).toScheme) :
    codimension (closureSingleton ((graphPartMorphism sX sY f hf U).base ξ)) = (d : ℕ∞) := by
  have ha0 : 0 ≤ relativeDimension (fieldChowSituation k).dimensionFunction sY ξ.1 :=
    relativeDimension_fieldChowSituation_nonneg k sY ξ.1
  have hAz : relativeDimension (fieldChowSituation k).dimensionFunction
      (pullback.snd (U.ι ≫ sX) sY ≫ sY) ((graphPartMorphism sX sY f hf U).base ξ) =
      relativeDimension (fieldChowSituation k).dimensionFunction sY ξ.1 :=
    relativeDimension_graphPartMorphism sX sY f hf hU ξ
  obtain ⟨T, hT, hzT, hTdim⟩ :=
    exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt k
      (pullback (U.ι ≫ sX) sY : Scheme.{u}) (pullback.snd (U.ι ≫ sX) sY ≫ sY)
      ((graphPartMorphism sX sY f hf U).base ξ)
  have hTdelta := deltaDimension_irreducibleComponent_of_mem_graphPart sX sY f hf hU d hrel ξ hξ
    ⟨T, hT⟩ hzT
  have hTtop : topologicalKrullDim T =
      (((relativeDimension (fieldChowSituation k).dimensionFunction sY ξ.1 + d).toNat :
        ℕ) : WithBot ℕ∞) :=
    Stacks.Intersection.CycleFlatPullback.topologicalKrullDim_coe_eq k
      (pullback.snd (U.ι ≫ sX) sY ≫ sY)
      ⟨T, hT.1, isClosed_of_mem_irreducibleComponents T hT⟩ _ (by rw [hTdelta]; omega)
  have hzclosure : topologicalKrullDim
      (closure ({(graphPartMorphism sX sY f hf U).base ξ} :
        Set (pullback (U.ι ≫ sX) sY : Scheme.{u}))) =
      (((relativeDimension (fieldChowSituation k).dimensionFunction sY ξ.1).toNat :
        ℕ) : WithBot ℕ∞) := by
    rw [Stacks.Chow.topologicalKrullDim_closure_singleton_eq k
      (pullback.snd (U.ι ≫ sX) sY ≫ sY) ((graphPartMorphism sX sY f hf U).base ξ), hAz]
  have hformula := AlgebraicGeometry.topologicalKrullDimAt_eq_add_ringKrullDim_stalk k
    (pullback.snd (U.ι ≫ sX) sY ≫ sY) ((graphPartMorphism sX sY f hf U).base ξ)
  rw [← hTdim, hTtop, hzclosure,
    ← codimension_closureSingleton_eq_ringKrullDim_stalk
      ((graphPartMorphism sX sY f hf U).base ξ)] at hformula
  refine eq_of_natCast_add_eq (m := (relativeDimension (fieldChowSituation k).dimensionFunction
    sY ξ.1).toNat) ?_
  rw [show ((relativeDimension (fieldChowSituation k).dimensionFunction sY ξ.1).toNat + d : ℕ) =
      ((relativeDimension (fieldChowSituation k).dimensionFunction sY ξ.1 + d).toNat : ℕ) from
    by omega]
  exact hformula

/-- The generic points of a scheme of constant fibre dimension `d` over a field have
delta-dimension `d`: the component through such a point has dimension `d`, and over a field the
dimension of a point closure is its delta-dimension (Stacks 02QO). -/
theorem relativeDimension_of_mem_irreducibleComponents_of_relativeDimension (k : Type u)
    [Field k] {T : Scheme.{u}} (q : T ⟶ Spec (.of k)) [LocallyOfFiniteType q] (d : ℕ)
    (h : AlgebraicGeometry.RelativeDimension q d) (z : T)
    (hz : closure ({z} : Set T) ∈ irreducibleComponents T) :
    relativeDimension (fieldChowSituation k).dimensionFunction q z = (d : ℤ) := by
  have _ : Nonempty T := ⟨z⟩
  obtain ⟨heq, hdim⟩ :=
    AlgebraicGeometry.equidimensional_and_topologicalKrullDim_of_relativeDimension k q d h
  have hC : topologicalKrullDim (closure ({z} : Set T)) = (d : WithBot ℕ∞) := by
    refine le_antisymm (hdim ▸ topologicalKrullDim_subspace_le T _) ?_
    have hle : topologicalKrullDim T ≤ topologicalKrullDim (closure ({z} : Set T)) :=
      topologicalKrullDim_le_of_forall_mem_irreducibleComponents
        fun W hW ↦ le_of_eq (heq W hW _ hz)
    rwa [hdim] at hle
  have hbridge := Stacks.Chow.topologicalKrullDim_closure_singleton_eq
    k q z
  rw [hC] at hbridge
  have h0 := relativeDimension_fieldChowSituation_nonneg k q z
  have hnat : (d : ℕ) = (relativeDimension (fieldChowSituation k).dimensionFunction q z).toNat := by
    exact_mod_cast hbridge
  omega

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] in
/-- **The delta-dimension of a point of the graph `Γ_f ⊆ X ×_k Y`** is that of the corresponding
point of `Y`: the graph morphism is a closed immersion over `k`. -/
theorem relativeDimension_graphMorphism (y : Y) :
    relativeDimension (fieldChowSituation k).dimensionFunction (pullback.fst sX sY ≫ sX)
        ((graphMorphism sX sY f hf).base y) =
      relativeDimension (fieldChowSituation k).dimensionFunction sY y := by
  rw [← relativeDimension_comp_closedImmersion (fieldChowSituation k).dimensionFunction
      (graphMorphism sX sY f hf) (pullback.fst sX sY ≫ sX) y,
    show (graphMorphism sX sY f hf ≫ pullback.fst sX sY ≫ sX) = sY from by
      rw [← Category.assoc, graphMorphism_fst]; exact hf]

/-- **Stacks 0FG1: `[Γ_f]` is a correspondence of degree zero.** If every generic point of `Y`
has delta-dimension `e` — which is what it means for `Y` to be equidimensional of dimension `e` —
then the cycle of the graph `Γ_f` on `X ×_k Y` vanishes in every delta-dimension other than `e`.
Since `Corrʳ(X, Y)` is the degree-`(e - r)` Chow group of `X ×_k Y` with rational coefficients,
this says that `[Γ_f]` lies in `Corr⁰(X, Y)` and in no other degree. -/
@[stacks 0FG1 "graph_degree_zero_correspondence"]
theorem cycleAssociatedToClosedSubscheme_graphMorphism_eq_zero (e : ℤ)
    (hY : ∀ y : Y, closure ({y} : Set Y) ∈ irreducibleComponents Y →
      relativeDimension (fieldChowSituation k).dimensionFunction sY y = e)
    (m : ℤ) (hm : m ≠ e) :
    cycleAssociatedToClosedSubscheme (fieldChowSituation k) (pullback.fst sX sY ≫ sX)
      (graphMorphism sX sY f hf) m = 0 := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
  show (cycleAssociatedToClosedSubscheme (fieldChowSituation k) (pullback.fst sX sY ≫ sX)
    (graphMorphism sX sY f hf) m).1 x = 0
  refine cycleAssociatedToClosedSubscheme_apply_eq_zero _ _ _ _ x ?_
  rintro ⟨ξ, hξ, hdim⟩
  rw [← hξ, relativeDimension_graphMorphism sX sY f hf ξ.1] at hdim
  exact hm (hdim.symm.trans (hY ξ.1 ξ.2))

/-- **Stacks 0FG1.** The graph of `f` as a correspondence of degree zero from `X` to a target
equidimensional of dimension `e`: the class of the cycle `[Γ_f]` of the graph on `X ×_k Y`, with
rational coefficients. -/
@[stacks 0FG1 "graph_degree_zero_correspondence", sga "7 XX 4.4" "partial"]
def graphCorrespondence (e : ℤ) : Correspondence (fieldChowSituation k) sX sY e 0 :=
  (1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
    (pullback.fst sX sY ≫ sX) (graphMorphism sX sY f hf) (e - 0))

/-! ### Stacks 0FG1 -/

/-- A projective morphism is separated, being proper. -/
theorem isSeparated_of_isProjectiveMorphism {S T : Scheme.{u}} (g : T ⟶ S)
    (hg : IsProjectiveMorphism g) : IsSeparated g :=
  have := isProper_of_isProjectiveMorphism g hg
  inferInstance

/-- **Stacks Project, Tag 0FG1.** Let `f : Y ⟶ X` be a morphism of smooth projective schemes
over a field `k` and let `Γ_f ⊆ X ×_k Y` be the graph of `f`, the image of the closed immersion
`(f, id_Y) : Y ⟶ X ×_k Y`. Let `X = ∐_d X_d` be the decomposition of `X` into its open and closed
parts which are equidimensional of dimension `d`, and likewise `Y = ∐_e Y_e`. Then:

* `Γ_f ∩ (X_d × Y)` has pure codimension `d` in `X_d × Y`; and
* consequently `[Γ_f]` lies in `Corr⁰(X, Y)`, i.e. it is a correspondence of degree `0` from `X`
  to `Y`.

The decomposition is the relative-dimension decomposition of Stacks 02NM: a smooth morphism is
flat and locally of finite presentation with Cohen-Macaulay fibres, so its relative dimension is
locally constant and the locus where it equals `d` is open and closed; over a field that locus is
the part of `X` which is equidimensional of dimension `d`, which is the fourth clause below.

`Γ_f ∩ (X_d × Y)` is the closed subscheme `Stacks.WeilCohomology.graphPartMorphism` of
`X_d ×_k Y`, namely the graph of `f` restricted over `X_d`; its irreducible components are
indexed by the generic points of the open and closed subscheme `f⁻¹(X_d)` of `Y`, which is the
source of that closed immersion. The fifth clause says that each of them has codimension `d`.

The last clause is the membership `[Γ_f] ∈ Corr⁰(X, Y)`. The group `Corrʳ(X, Y)` is
`⊕_d CH^{d+r}(X_d × Y) ⊗ ℚ`; in the dimension grading used by this repository's Chow groups
`CH^{d}(X_d × Y_e) = A_e(X_d × Y_e)`, so saying that `[Γ_f]` is a correspondence of degree `0` is
saying that over the part `Y_e` of `Y` the cycle `[Γ_f]` is concentrated in delta-dimension `e`
and vanishes in every other delta-dimension — which is the codimension-`d` purity of the previous
clause read in the dimension grading. -/
@[stacks 0FG1 "graph_pure_codimension_degree_zero_correspondence"]
theorem exists_decomposition_graph_pure_codimension (k : Type u) [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [Smooth sX] [Smooth sY]
    (hXproj : IsProjectiveMorphism sX) (f : Y ⟶ X) (hf : f ≫ sX = sY) :
    haveI : IsSeparated sX := isSeparated_of_isProjectiveMorphism sX hXproj
    ∃ U : ℕ → X.Opens, ∃ V : ℕ → Y.Opens,
      ((∀ d, IsClopen (U d : Set X)) ∧ (⨆ d, U d) = ⊤ ∧
        ∀ d d', d ≠ d' → Disjoint (U d) (U d')) ∧
      ((∀ e, IsClopen (V e : Set Y)) ∧ (⨆ e, V e) = ⊤ ∧
        ∀ e e', e ≠ e' → Disjoint (V e) (V e')) ∧
      (∀ d : ℕ, Nonempty (U d).toScheme →
        TopologicalSpace.Equidimensional (U d).toScheme ∧
          topologicalKrullDim (U d).toScheme = (d : WithBot ℕ∞)) ∧
      (∀ e : ℕ, Nonempty (V e).toScheme →
        TopologicalSpace.Equidimensional (V e).toScheme ∧
          topologicalKrullDim (V e).toScheme = (e : WithBot ℕ∞)) ∧
      (∀ d : ℕ, Set.range (graphPartMorphism sX sY f hf (U d) ≫
            partProductι sX sY (U d)).base =
          Set.range (graphMorphism sX sY f hf).base ∩
            Set.range (partProductι sX sY (U d)).base) ∧
      (∀ (d : ℕ) (ξ : (f ⁻¹ᵁ U d).toScheme),
        closure ({ξ} : Set (f ⁻¹ᵁ U d).toScheme) ∈ irreducibleComponents (f ⁻¹ᵁ U d).toScheme →
          codimension (closureSingleton ((graphPartMorphism sX sY f hf (U d)).base ξ)) =
            (d : ℕ∞)) ∧
      (∀ (e : ℕ) (m : ℤ), m ≠ (e : ℤ) →
        cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (pullback.fst sX ((V e).ι ≫ sY) ≫ sX)
          (graphMorphism sX ((V e).ι ≫ sY) ((V e).ι ≫ f)
            (by rw [Category.assoc, hf])) m = 0) := by
  have : IsSeparated sX := isSeparated_of_isProjectiveMorphism sX hXproj
  have hCMX : ∀ s : Spec (CommRingCat.of k), IsCohenMacaulay (sX.fiber s) := fun s ↦
    isCohenMacaulay_fiber_of_smooth sX s
  have hCMY : ∀ s : Spec (CommRingCat.of k), IsCohenMacaulay (sY.fiber s) := fun s ↦
    isCohenMacaulay_fiber_of_smooth sY s
  refine ⟨relativeDimensionOpen sX hCMX, relativeDimensionOpen sY hCMY,
    ⟨relativeDimensionOpen_isClopen sX hCMX, iSup_relativeDimensionOpen sX hCMX,
      fun d d' h ↦ pairwise_disjoint_relativeDimensionOpen sX hCMX h⟩,
    ⟨relativeDimensionOpen_isClopen sY hCMY, iSup_relativeDimensionOpen sY hCMY,
      fun e e' h ↦ pairwise_disjoint_relativeDimensionOpen sY hCMY h⟩,
    fun d hd ↦ ?_, fun e he ↦ ?_,
    fun d ↦ range_graphPartMorphism_comp_partProductι sX sY f hf _,
    fun d ξ hξ ↦ ?_, fun e m hm ↦ ?_⟩
  · exact AlgebraicGeometry.equidimensional_and_topologicalKrullDim_of_relativeDimension k
      ((relativeDimensionOpen sX hCMX d).ι ≫ sX) d
      (relativeDimensionOpen_relativeDimension sX hCMX d)
  · exact AlgebraicGeometry.equidimensional_and_topologicalKrullDim_of_relativeDimension k
      ((relativeDimensionOpen sY hCMY e).ι ≫ sY) e
      (relativeDimensionOpen_relativeDimension sY hCMY e)
  · exact codimension_graphPartMorphism sX sY f hf (relativeDimensionOpen_isClopen sX hCMX d) d
      (relativeDimensionOpen_relativeDimension sX hCMX d) ξ hξ
  · exact cycleAssociatedToClosedSubscheme_graphMorphism_eq_zero sX
      ((relativeDimensionOpen sY hCMY e).ι ≫ sY) ((relativeDimensionOpen sY hCMY e).ι ≫ f)
      (by rw [Category.assoc, hf]) (e : ℤ)
      (fun y hy ↦ relativeDimension_of_mem_irreducibleComponents_of_relativeDimension k
        ((relativeDimensionOpen sY hCMY e).ι ≫ sY) e
        (relativeDimensionOpen_relativeDimension sY hCMY e) y hy) m hm

end Purity

end Stacks.WeilCohomology

end
