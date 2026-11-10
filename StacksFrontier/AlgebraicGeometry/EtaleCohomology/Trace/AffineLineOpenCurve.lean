module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseCompactSupportZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.DenseOpenReduction
public import StacksFrontier.AlgebraicGeometry.AmpleCurve.Basic

/-!
# Opens of the affine line over a field

A nonempty open `W ⊆ 𝔸¹_k` (an open immersion `W ⟶ Spec k[T]`) smooth of relative dimension one
over `k` is an integral curve, and it is affine: if it were proper over `k`, the open immersion
would be universally closed, hence onto the irreducible `𝔸¹_k`, and `W ≅ 𝔸¹_k` would be a proper
affine curve. For an open immersion `V ⟶ W` with `V` nonempty, the reduced closed complement is a
finite set of closed points, finite over `k`. These are the geometric inputs of the inclusion
`H⁰_loc ⊆ H¹_c` of Weil II 1.8 ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) at a
missing point of `V ⊆ W ⊆ 𝔸¹_k`.

## Main results

* `Stacks.EtaleCohomology.isCurve_of_isOpenImmersion_affineLine`
* `Stacks.EtaleCohomology.isAffine_of_isOpenImmersion_affineLine`
* `Stacks.EtaleCohomology.isFinite_closedComplementι_comp_of_irreducibleSpace`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

section AffineLine

variable {k : Type u} [Field k] {W : Scheme.{u}} (fW : W ⟶ Spec (.of k))
  (eW : W ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion eW]

include eW in
/-- A nonempty open of `𝔸¹_k` is irreducible. -/
public theorem irreducibleSpace_of_isOpenImmersion_affineLine [Nonempty W] : IrreducibleSpace W :=
  eW.isOpenEmbedding.irreducibleSpace

include eW in
/-- A nonempty open of `𝔸¹_k` is integral. -/
public theorem isIntegral_of_isOpenImmersion_affineLine [Nonempty W] : IsIntegral W := by
  have := irreducibleSpace_of_isOpenImmersion_affineLine eW
  have : IsReduced W := isReduced_of_isOpenImmersion eW
  exact isIntegral_of_irreducibleSpace_of_isReduced W

include eW in
/-- **A nonempty open of `𝔸¹_k` smooth of relative dimension one is a curve.** -/
public theorem isCurve_of_isOpenImmersion_affineLine [Nonempty W] [LocallyOfFiniteType fW]
    [QuasiCompact fW] [IsSeparated fW] [SmoothOfRelativeDimension 1 fW] : IsCurve k fW :=
  have := isIntegral_of_isOpenImmersion_affineLine eW
  { topologicalKrullDim_eq_one := by
      rw [topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 1 fW]
      rfl }

/-- **A nonempty open of `𝔸¹_k` smooth of relative dimension one is affine**: it is not proper
over `k`, since a proper open of `𝔸¹_k` is all of `𝔸¹_k`, which is affine. -/
public theorem isAffine_of_isOpenImmersion_affineLine [Nonempty W]
    [LocallyOfFiniteType fW] [QuasiCompact fW] [IsSeparated fW] [SmoothOfRelativeDimension 1 fW]
    (heW : eW ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = fW) :
    IsAffine W := by
  have := irreducibleSpace_of_isOpenImmersion_affineLine eW
  have := isCurve_of_isOpenImmersion_affineLine fW eW
  refine isAffine_of_not_isProper_of_irreducibleSpace fW
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 1 fW).le fun hP => ?_
  have : IsProper fW := hP
  have : UniversallyClosed (eW ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))) := by
    rw [heW]
    infer_instance
  have : UniversallyClosed eW := UniversallyClosed.of_comp_of_isSeparated eW
    (Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))))
  have huniv : Set.range eW.base = Set.univ :=
    IsClopen.eq_univ ⟨eW.isClosedMap.isClosed_range, eW.isOpenEmbedding.isOpen_range⟩
      (Set.range_nonempty _)
  have : Surjective eW := ⟨Set.range_eq_univ.1 huniv⟩
  have : IsIso eW := (isIso_iff_isOpenImmersion_and_surjective eW).2 ⟨inferInstance, inferInstance⟩
  exact not_isAffine_of_isCurve k fW (IsAffine.of_isIso eW)

end AffineLine

section Complement

variable {k : Type u} [Field k] {W V : Scheme.{u}} (fW : W ⟶ Spec (.of k))
  [LocallyOfFiniteType fW] [QuasiCompact fW] (jW : V ⟶ W) [IsOpenImmersion jW]

/-- **The reduced closed complement of a nonempty open of an irreducible scheme of dimension at
most one of finite type over `k` is finite over `k`.** -/
public theorem isFinite_closedComplementι_comp_of_irreducibleSpace [IrreducibleSpace W]
    [Nonempty V] (hdim : topologicalKrullDim W ≤ 1) : IsFinite (closedComplementι jW ≫ fW) := by
  have := finite_closedComplement jW fW hdim
    (jW.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _))
  exact isFinite_closedComplementι_comp jW fW

/-- The reduced closed complement is reduced. -/
public instance isReduced_closedComplement : IsReduced (closedComplement jW) :=
  Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _

/-- A point outside the open lies on the closed complement. -/
public theorem mem_range_closedComplementι {y : W} (hy : y ∉ Set.range jW.base) :
    y ∈ Set.range (closedComplementι jW).base := by
  by_contra h
  exact hy ((range_eq_compl_range_closedComplementι jW).symm ▸ h)

end Complement

end Stacks.EtaleCohomology
