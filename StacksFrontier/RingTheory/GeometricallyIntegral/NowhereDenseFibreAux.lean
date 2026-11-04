module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NowhereDenseFibres.FibreDimension
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NowhereDenseFibres.FibrePoints
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Topology.NoetherianSpace
public import StacksCore.Topology.NowhereDense.Defs
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.Purity
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NowhereDenseFibres.Topology
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibrewiseDenseRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.DenseFlatLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.GenericFlatness
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components
public import StacksFrontier.Topology.Dimension.Krull
public import StacksFrontier.Topology.Dimension.LocalKrullDim
public import StacksFrontier.Topology.Noetherian.GenericPointsDenseOpen
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Fibres, generic points and local dimension: the apparatus of Stacks 054X

Stacks 054X says that a closed subset of the source of a finite type morphism `f : X ⟶ Y` onto an
irreducible base which is nowhere dense in the fibre over the generic point `η` stays nowhere
dense in every fibre over some nonempty open of `Y`. The argument is a dimension count: if the
fibre `Z_y` of the closed subset had nonempty interior it would contain a generic point `ξ` of an
irreducible component of `X_y`, and lifting `ξ` along flatness to a point `ξ'` over `η` makes the
local dimensions of `Z` and of `X` agree at `ξ'`, which contradicts nowhere density in `X_η`.

This file collects the apparatus that count needs, and `NowhereDenseGenericFibre` runs it.
Three groups of statements:

* **generic points and dense opens.** A generic point of the whole space lies in every dense
  open, and so does a generic point of an irreducible component of a locally Noetherian scheme.
  The same statement for a Noetherian space is
  `TopologicalSpace.NoetherianSpace.mem_of_mem_genericPoints_of_dense`, and that a closed subset
  which is *not* nowhere dense contains a generic point of a component is
  `exists_mem_genericPoints_of_not_isNowhereDense`; both are imported.
* **local dimension of fibres.** The local dimension of a fibre is the constant `d` on a morphism
  of relative dimension `d`, and at a generic point of a component of a fibre is some natural
  number. Over a field the local dimension at a generic point is the dimension of the component it
  generates, so a closed immersion which is generic on both sides preserves it. That the local
  dimension is unchanged by restricting the source to an open subscheme is
  `AlgebraicGeometry.fiberDimensionAt_comp_openImmersion`, which is imported.
* **transport.** The morphism of fibres induced by a morphism of sources, the point of a fibre
  determined by a point of the source, and the invariance of nowhere density in fibres under a
  homeomorphism of the whole situation.

The dimension of an irreducible closed subset is `Order.height` of it in the lattice of
irreducible closeds, which is what makes a strict inclusion of irreducible closeds of finite
dimension strictly increase the dimension; that is the step which turns the dimension equality
into a contradiction.

## Main results

* `AlgebraicGeometry.exists_dense_open_resLE_flat_finitePresentation`: Stacks 052B for the
  structure sheaf, i.e. generic flatness for a finite type morphism onto a reduced base.
* `AlgebraicGeometry.topologicalKrullDimAt_eq_of_isClosedImmersion`: a closed immersion of
  schemes of finite type over a field preserves the local dimension at a point which is generic
  on both sides.
* `AlgebraicGeometry.isNowhereDense_fiberι_preimage_iff_of_isHomeomorph`: nowhere density in a
  fibre is invariant under a homeomorphism of the morphism.

## References

* [Stacks Project, Tag 054X](https://stacks.math.columbia.edu/tag/054X)
* [Stacks Project, Tag 052B](https://stacks.math.columbia.edu/tag/052B)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

/-! ### Generic points and dense opens -/

/-- A generic point of the whole space lies in every dense open subset: the dense open is
nonempty, and every point of the space is a specialization of the generic point. -/
@[ega "0 2.1.4" "partial"]
theorem mem_of_isGenericPoint_univ_of_dense {Y : Type*} [TopologicalSpace Y] {η : Y}
    (hη : IsGenericPoint η Set.univ) {U : Set Y} (hU : IsOpen U) (hd : Dense U) : η ∈ U := by
  have hne : U.Nonempty := by
    by_contra h
    have hηcl : η ∈ closure U := by rw [hd.closure_eq]; exact Set.mem_univ η
    rw [Set.not_nonempty_iff_eq_empty.mp h, closure_empty] at hηcl
    exact hηcl
  obtain ⟨y, hy⟩ := hne
  have hyη : y ∈ closure ({η} : Set Y) := by rw [hη.def]; exact Set.mem_univ y
  exact (specializes_iff_mem_closure.mpr hyη).mem_open hU hy

namespace AlgebraicGeometry

/-- The same statement for a locally Noetherian scheme, which need not be a Noetherian space
globally: pass to an affine open neighbourhood of the point, where it is. -/
theorem Scheme.mem_of_mem_genericPoints_of_dense (X : Scheme.{u}) [IsLocallyNoetherian X]
    {D : Set X} (hD : IsOpen D) (hd : Dense D) {x : X} (hx : x ∈ genericPoints X) : x ∈ D := by
  obtain ⟨_, ⟨V : X.Opens, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : CompactSpace V := isCompact_iff_compactSpace.mp hV.isCompact
  have : IsNoetherian V := { __ := isLocallyNoetherian_of_isOpenImmersion V.ι }
  have hcomp : V.ι ⁻¹' closure ({x} : Set X) ∈ irreducibleComponents V :=
    preimage_mem_irreducibleComponents hx V.ι.isOpenEmbedding
      ⟨x, subset_closure (Set.mem_singleton x), ⟨x, hxV⟩, rfl⟩
  have hv : (⟨x, hxV⟩ : V) ∈ genericPoints V := by
    change closure ({(⟨x, hxV⟩ : V)} : Set V) ∈ irreducibleComponents V
    convert hcomp using 1
    rw [V.ι.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage V.ι.continuous]
    congr 1
    ext z
    exact ⟨fun h => congrArg (fun t : V => t.1) h, fun h => Subtype.ext h⟩
  exact NoetherianSpace.mem_of_mem_genericPoints_of_dense (hD.preimage V.ι.continuous)
    (hd.preimage V.ι.isOpenEmbedding.isOpenMap) hv

/-! ### Generic flatness for the structure sheaf -/


/-! ### Local dimension of fibres -/


/-! ### Generic points under immersions -/



end AlgebraicGeometry

/-! ### Dimension of an irreducible closed subset -/

/-- The preimage of an irreducible subset in a larger subset it is contained in is irreducible:
it is the image of the whole of the smaller subset under the inclusion. -/
theorem isIrreducible_preimage_val_of_subset {T : Type*} [TopologicalSpace T] {s t : Set T}
    (hs : IsIrreducible s) (h : s ⊆ t) :
    IsIrreducible ((Subtype.val : t → T) ⁻¹' s) := by
  have := Subtype.irreducibleSpace hs
  have he : Set.inclusion h '' (Set.univ : Set s) = (Subtype.val : t → T) ⁻¹' s := by
    ext x
    simp only [Set.mem_image, Set.mem_univ, true_and, Set.mem_preimage]
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x.1, hx⟩, Subtype.ext rfl⟩⟩
  rw [← he]
  exact IrreducibleSpace.isIrreducible_univ s |>.image _ (by fun_prop)

/-- The topological Krull dimension of an irreducible closed subset is its `Order.height` in the
lattice of irreducible closed subsets of the ambient space. The two order embeddings between
`Set.Iic Z` and the irreducible closeds of `Z` — restrict, and take the image — give the
inequalities in both directions. -/
theorem topologicalKrullDim_irreducibleCloseds_eq_height {X : Type*} [TopologicalSpace X]
    (Z : IrreducibleCloseds X) :
    topologicalKrullDim (Z : Set X) = (Order.height Z : WithBot ℕ∞) := by
  let e₁ : Set.Iic Z ↪o IrreducibleCloseds (Z : Set X) :=
    OrderEmbedding.ofMapLEIff
      (fun W ↦ ⟨Subtype.val ⁻¹' (W.1 : Set X),
        isIrreducible_preimage_val_of_subset W.1.isIrreducible W.2,
        W.1.isClosed.preimage continuous_subtype_val⟩)
      (fun A B ↦ ⟨fun h x hx => h (show (⟨x, A.2 hx⟩ : (Z : Set X)) ∈ _ from hx),
        fun h _ hx => h hx⟩)
  let e₂ : IrreducibleCloseds (Z : Set X) ↪o Set.Iic Z :=
    OrderEmbedding.ofMapLEIff
      (fun W : IrreducibleCloseds (Z : Set X) ↦
        ⟨⟨Subtype.val '' (W : Set (Z : Set X)), W.isIrreducible'.image _
            continuous_subtype_val.continuousOn,
          Z.isClosed'.isClosedEmbedding_subtypeVal.isClosedMap _ W.isClosed'⟩,
          Set.image_subset_iff.mpr fun x _ ↦ x.2⟩)
      (by
        intro A B
        change (Subtype.val '' (A : Set (Z : Set X)) ⊆ Subtype.val '' (B : Set (Z : Set X))) ↔
          (A : Set (Z : Set X)) ⊆ B
        refine ⟨fun h x hx => ?_, fun h a ha => ?_⟩
        · obtain ⟨y, hy, hxy⟩ := h ⟨x, hx, rfl⟩
          have heq : y = x := Subtype.ext hxy
          simpa [heq] using hy
        · rcases (Set.mem_image _ _ _).mp ha with ⟨b, hb, hba⟩
          exact ⟨b, h hb, hba⟩)
  rw [topologicalKrullDim]
  refine le_antisymm ?_ ?_
  · calc
      Order.krullDim (IrreducibleCloseds (Z : Set X)) ≤ Order.krullDim (Set.Iic Z) :=
        Order.krullDim_le_of_strictMono e₂ e₂.strictMono
      _ = (Order.height Z : WithBot ℕ∞) := (Order.height_eq_krullDim_Iic Z).symm
  · calc
      (Order.height Z : WithBot ℕ∞) = Order.krullDim (Set.Iic Z) := Order.height_eq_krullDim_Iic Z
      _ ≤ Order.krullDim (IrreducibleCloseds (Z : Set X)) :=
        Order.krullDim_le_of_strictMono e₁ e₁.strictMono

/-- A strict inclusion of irreducible closed subsets strictly increases the topological Krull
dimension, provided the smaller one has finite dimension. This is
`Order.height_strictMono` through `topologicalKrullDim_irreducibleCloseds_eq_height`. -/
theorem topologicalKrullDim_lt_of_lt_irreducibleCloseds {X : Type*} [TopologicalSpace X]
    (W C : IrreducibleCloseds X) (hWC : W < C)
    (hWdim : topologicalKrullDim (W : Set X) ≠ ⊤) :
    topologicalKrullDim (W : Set X) < topologicalKrullDim (C : Set X) := by
  rw [topologicalKrullDim_irreducibleCloseds_eq_height W,
    topologicalKrullDim_irreducibleCloseds_eq_height C]
  have hWheight : Order.height W < ⊤ := by
    by_contra h
    refine hWdim ?_
    rw [topologicalKrullDim_irreducibleCloseds_eq_height W, ← WithBot.coe_top, WithBot.coe_inj]
    exact le_antisymm le_top (not_lt.mp h)
  exact_mod_cast Order.height_strictMono hWC hWheight
