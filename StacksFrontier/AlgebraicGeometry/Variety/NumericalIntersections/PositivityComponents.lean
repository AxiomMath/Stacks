module

public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Multiplicity
public import StacksFrontier.AlgebraicGeometry.CoherentDevissageGlue.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.Components
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Reducing positivity of an intersection number to its top-dimensional components

[Stacks, Tag 0BES], `AlgebraicGeometry.intersectionNumber_eq_sum_topDimComponents`, writes the
intersection number of a closed subscheme `Z ⊂ X` of dimension `d` as the length-weighted sum

`(𝓛_1 ⋯ 𝓛_d · Z) = ∑_W m_W (𝓛_1 ⋯ 𝓛_d · W)`

over the top-dimensional integral components `W` of `Z`. There is at least one such component and
each weight `m_W` is positive, so the sum is positive as soon as every summand is; this is the
reduction used in the induction of [Stacks, Tag 0BEV].

## Main results

* `AlgebraicGeometry.nonempty_topDimIntegralSubscheme`: a module whose support is closed and of
  finite dimension `d` has a top-dimensional integral component.
* `AlgebraicGeometry.sheafMultiplicity_genericPt_pos`: the multiplicity of a coherent module at
  the generic point of a top-dimensional component of its support is positive.
* `AlgebraicGeometry.intersectionNumber_pos_of_pos_topDimComponents`: the reduction of
  positivity of `(𝓛_1 ⋯ 𝓛_d · Z)` to positivity of the `(𝓛_1 ⋯ 𝓛_d · W)`.

## References

* [Stacks Project, Tag 0BES](https://stacks.math.columbia.edu/tag/0BES)
* [Stacks Project, Tag 0BEV](https://stacks.math.columbia.edu/tag/0BEV)
* [Stacks Project, Tag 02QX](https://stacks.math.columbia.edu/tag/02QX)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### A top-dimensional component exists -/

/-- A module whose support is closed and has finite Krull dimension `d` has a top-dimensional
integral component. -/
public theorem nonempty_topDimIntegralSubscheme {X : Scheme.{u}} (F : X.Modules)
    (hclosed : IsClosed (_root_.SheafOfModules.supp F)) {d : ℕ}
    (hdim : topologicalKrullDim (_root_.SheafOfModules.supp F) = (d : WithBot ℕ∞)) :
    Nonempty (TopDimIntegralSubscheme F) := by
  set S := _root_.SheafOfModules.supp F with hS
  have : FiniteDimensionalOrder (IrreducibleCloseds S) :=
    Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top.mpr (by
      refine ⟨?_, ?_⟩ <;> rw [show Order.krullDim (IrreducibleCloseds S) =
        topologicalKrullDim S from rfl, hdim]
      · simp
      · exact ne_of_lt (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top d)))
  set C := (LTSeries.longestOf (IrreducibleCloseds S)).last with hC
  have hCdim : topologicalKrullDim (C : Set S) = (d : WithBot ℕ∞) :=
    (topologicalKrullDim_irreducibleCloseds C).trans
      (LTSeries.height_last_longestOf.trans hdim)
  set D : IrreducibleCloseds X := IrreducibleCloseds.map Subtype.val continuous_subtype_val C
    with hDdef
  have hD : (D : Set X) = Subtype.val '' (C : Set S) :=
    (hclosed.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed.mp C.isClosed).closure_eq
  set I := Scheme.IdealSheafData.vanishingIdeal (⟨(D : Set X), D.isClosed⟩ : Closeds X) with hI
  have hsupp : (I.support : Set X) = (D : Set X) :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have hirr : IrreducibleSpace I.support :=
    Subtype.irreducibleSpace (hsupp.symm ▸ D.isIrreducible)
  have : IsReduced I.subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have : IrreducibleSpace I.subscheme :=
    (I.subschemeι.isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr (I.range_subschemeι))).irreducibleSpace_iff.mpr hirr
  have : IsIntegral I.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have hCsub : (D : Set X) ⊆ S := by
    rw [hD]
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  refine ⟨⟨I, inferInstance, by rw [hsupp]; exact hCsub, ?_⟩⟩
  rw [← topologicalKrullDim_support_eq, hsupp, hD, hdim]
  exact ((Topology.IsEmbedding.subtypeVal (p := fun x => x ∈ S)).homeomorphImage
    (C : Set S)).isHomeomorph.topologicalKrullDim_eq _ ▸ hCdim

/-! ### The multiplicity at a top-dimensional component is positive -/

/-- The generic point of a top-dimensional integral component of `Supp ℱ` lies in the support of
that component. -/
public theorem genericPt_mem_support {X : Scheme.{u}} {F : X.Modules}
    (W : TopDimIntegralSubscheme F) : W.genericPt ∈ (W.1.support : Set X) := by
  have := W.2.1
  rw [← W.1.range_subschemeι]
  exact ⟨_, rfl⟩

/-- The multiplicity of a coherent module at the generic point of a top-dimensional component of
its support is positive. -/
@[ega "IV 3.1.4" "partial"]
public theorem sheafMultiplicity_genericPt_pos (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (F : X.Modules) [F.IsCoherent]
    (W : TopDimIntegralSubscheme F) : 0 < Stacks.Chow.sheafMultiplicity F W.genericPt := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := W.2.1
  have hmem : W.genericPt ∈ _root_.SheafOfModules.supp F :=
    W.2.2.1 (genericPt_mem_support W)
  have himg : (Subtype.val : _root_.SheafOfModules.supp F → X) ''
      ((Subtype.val : _root_.SheafOfModules.supp F → X) ⁻¹' (W.1.support : Set X)) =
      (W.1.support : Set X) := by
    rw [Set.image_preimage_eq_inter_range, Subtype.range_coe_subtype]
    exact Set.inter_eq_left.mpr W.2.2.1
  refine Stacks.Chow.sheafMultiplicity_pos_of_mem_supp F
    (Stacks.Chow.isFiniteLength_stalk_of_isGenericPoint_component_supp F
      ⟨_, mem_irreducibleComponents_preimage_support k f F W⟩ W.genericPt ?_) hmem
  rw [himg]
  exact Stacks.AlgebraicGeometry.CoherentDevissageGlue.isGenericPoint_subschemeι_genericPoint W.1

/-! ### Positivity of a weighted sum -/

/-- A finite sum of positive terms with positive integer weights over a nonempty index type is
positive. -/
public theorem finsum_pos_of_pos_of_pos {α : Type*} [Finite α] [Nonempty α]
    (m c : α → ℤ) (hm : ∀ a, 0 < m a) (hc : ∀ a, 0 < c a) : 0 < ∑ᶠ a, m a * c a := by
  classical
  have : Fintype α := Fintype.ofFinite α
  rw [finsum_eq_sum_of_fintype]
  exact Finset.sum_pos (fun a _ => mul_pos (hm a) (hc a)) Finset.univ_nonempty

/-! ### The reduction -/

/-- **Positivity of an intersection number from positivity on the top-dimensional components.**
Let `X` be proper over a field `k` and `Z ⊆ X` a closed subscheme of dimension `d`. If
`(𝓛_1 ⋯ 𝓛_d · W) > 0` for every top-dimensional integral component `W` of `Z`, then
`(𝓛_1 ⋯ 𝓛_d · Z) > 0`. -/
public theorem intersectionNumber_pos_of_pos_topDimComponents (k : Type u) [Field k]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (d : ℕ) (hd : topologicalKrullDim Z = (d : WithBot ℕ∞)) (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    (hpos : ∀ W : TopDimIntegralSubscheme
        ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)),
        0 < intersectionNumber k f W.1.subschemeι d
          (topologicalKrullDim_subscheme_le_of_topDimIntegralSubscheme i hd W) L) :
    0 < intersectionNumber k f i d hd.le L := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  have hZcoh : (Stacks.Ample.unitModule Z).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (i ≫ f)
  have hFcoh : ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)).IsCoherent :=
    isCoherent_pushforward_of_isClosedImmersion i (Stacks.Ample.unitModule Z)
  have : Finite (TopDimIntegralSubscheme
      ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z))) :=
    finite_topDimIntegralSubscheme k f _
  have hdimF : topologicalKrullDim (_root_.SheafOfModules.supp
      ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z))) =
      (d : WithBot ℕ∞) := by
    rw [Stacks.Chow.supp_pushforwardStructureSheaf i, topologicalKrullDim_range_eq i, hd]
  have : ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)).IsFiniteType :=
    Stacks.Chow.isFiniteType_of_isCoherent _
  have : Nonempty (TopDimIntegralSubscheme
      ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z))) :=
    nonempty_topDimIntegralSubscheme _
      (_root_.SheafOfModules.isClosed_supp _) hdimF
  rw [intersectionNumber_eq_sum_topDimComponents k f i d hd L]
  exact finsum_pos_of_pos_of_pos _ _
    (fun W => sheafMultiplicity_genericPt_pos k f _ W) hpos

end AlgebraicGeometry

end
