module

public import StacksFrontier.AlgebraicGeometry.Curves.CanonicalContraction.Existence
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.Components
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.AttachingPointNode
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GenusGoesDownUnconditional

/-!
# The curve obtained by contracting a rational tail

Let `k` be a field and let `X` be a proper one-dimensional scheme over `k` with at-worst-nodal
singularities and `H⁰(X, 𝒪_X) = k`. Let `C ⊆ X` be a rational tail and let `X'` be the
scheme-theoretic closure of the complement of `C`, the target of the canonical contraction
`c : X ⟶ X'` of `Stacks.Curves.canonicalContraction`. This file collects the properties of `X'`
itself: it is again proper over `k`, again of dimension one, and its only global regular
functions are the constants.

Properness is formal: `X' ⟶ X` is a closed immersion, hence finite, hence proper, and proper
morphisms compose. For the dimension, the closed embedding `X' ⟶ X` bounds
`dim X' ≤ dim X = 1`, and for the reverse bound an irreducible component of `X` meeting the
open complement of `C` is contained in `X'` — an irreducible set meeting an open set is
contained in that set's closure — and every irreducible component of `X` has dimension one.
For the global functions, the contraction `c` restricts to the identity on `X'`, so
`c*` on global sections is a split epimorphism; since it is in fact an isomorphism
(`Stacks.Curves.isIso_appTop_of_isContractionOfRationalTail`), so is the restriction map
`Γ(X, 𝒪_X) ⟶ Γ(X', 𝒪_{X'})`, and `Γ(X', 𝒪_{X'}) = k` follows from `Γ(X, 𝒪_X) = k`.

## Main results

* `Stacks.Curves.isProper_complementaryCurve` — `X'` is proper over `k`.
* `Stacks.Curves.topologicalKrullDim_complementaryCurve` — `X'` has dimension one.
* `Stacks.Curves.isIso_globalSections_complementaryCurve` — `H⁰(X', 𝒪_{X'}) = k`.
* `Stacks.Curves.genus_complementaryCurve_le` — the genus of `X'` is at most the genus of `X`.
* `Stacks.Curves.tailComplementIso` — away from `C`, the curve `X'` agrees with `X`: the open
  complement of `C` in `X` is identified with the complement in `X'` of the attaching locus.

## Implementation notes

`H⁰(X, 𝒪_X) = k` is expressed, as everywhere in this development, by asking that the
composite `k ⟶ Γ(Spec k, 𝒪) ⟶ Γ(X, 𝒪_X)` of the inverse of `Scheme.ΓSpecIso` with the
global-sections map of the structure morphism be an isomorphism; the statement for `X'` is the
same condition for the structure morphism `complementaryCurveι C ≫ (X ↘ Spec k)` of `X'`.

The genus of `X'` is in fact *equal* to that of `X`, but only the inequality
`genus X' ≤ genus X` is proved here, as the unconditional form of Tag 0CE3 applied to the
closed immersion `X' ⟶ X`. The reverse inequality is not a formal consequence of the
retraction `X' ⟶ X ⟶ X'`, which also only bounds `H¹(X', 𝒪_{X'})` by `H¹(X, 𝒪_X)`; it needs the
vanishing of the higher direct images along the contraction, which is proved downstream in
`StacksFrontier/AlgebraicGeometry/Curves/DirectImage/RationalTailAcyclic.lean`. The equality itself
is `Stacks.Curves.genus_complementaryCurve`, in
`StacksFrontier/AlgebraicGeometry/Curves/DirectImage/RationalTailCohomologyIso.lean`.

Three *scoped* `@[stacks 0E3H]` sub-labels are placed in this file. The source asserts that `X'`
inherits the properties of `X` — proper over `k`, of dimension one, with only constant global
functions, at worst nodal, and of the same genus — and the first three of those five are proved
here, at the source's own hypotheses, by `Stacks.Curves.isProper_complementaryCurve`,
`Stacks.Curves.topologicalKrullDim_complementaryCurve` and
`Stacks.Curves.isIso_globalSections_complementaryCurve`. An earlier note withheld every
attribute here on the ground that the genus clause is registered downstream and the
at-worst-nodal clause is proved only away from the attaching point, concluding that no
declaration here states the tag. Both premises are true and the conclusion does not follow from
them: it enumerates two of the five inherited properties and is silent about the three that are
proved here. The genus clause is indeed registered downstream, in
`Curves/DirectImage/RationalTailCohomologyIso.lean`, and the at-worst-nodal clause indeed is
not, carrying only the away-from-the-attaching-point sub-label in
`Curves/CanonicalContraction/NodalAwayFromAttaching.lean`.

## References

* [Stacks Project, Tag 0E3H](https://stacks.math.columbia.edu/tag/0E3H)
* [Stacks Project, Tag 0CE3](https://stacks.math.columbia.edu/tag/0CE3)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Curves

/-- **Stacks 0E3H.** The scheme-theoretic closure of the complement of a closed subscheme of a
proper scheme over a field is again proper over that field. For a rational tail this is the
assertion that `X'` is proper over `k`; no rational-tail hypothesis is needed for it. -/
@[stacks 0E3H "complementary_curve_is_proper"]
theorem isProper_complementaryCurve
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] (C : X.IdealSheafData) :
    IsProper (complementaryCurveι C ≫ (X ↘ Spec (.of k))) :=
  inferInstance

/-- A proper scheme over a field is Noetherian. -/
private theorem isNoetherian_of_isProper
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] : AlgebraicGeometry.IsNoetherian X := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  exact ⟨⟩

/-- **Stacks 0E3H.** The scheme-theoretic closure `X'` of the complement of a rational tail of
a proper one-dimensional curve over a field with only constant global functions is again of
dimension one. -/
@[stacks 0E3H "complementary_curve_has_dimension_one"]
theorem topologicalKrullDim_complementaryCurve
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (C : X.IdealSheafData) (hC : IsRationalTail k X C) :
    topologicalKrullDim (complementaryCurve C) = 1 := by
  have hXeq : Equidimensional X :=
    equidimensional_of_isIso_globalSections_of_dimension_one k (X ↘ Spec (.of k)) hdim
  -- the closed embedding of `X'` into `X` bounds the dimension above
  have hle : topologicalKrullDim (complementaryCurve C) ≤ 1 := by
    rw [← hdim]
    exact (complementaryCurveι C).isClosedEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
  have := isNoetherian_of_isProper k X
  -- `X'` is the closure of the open complement of `C`
  have hrange : Set.range (complementaryCurveι C).base = closure ((C.support : Set X)ᶜ) := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    rw [Scheme.Hom.support_ker, Scheme.Opens.range_ι]
    rfl
  -- so that complement is nonempty, `X'` being nonempty
  obtain ⟨y⟩ := hC.complementaryCurve_nonempty
  have hclne : (closure ((C.support : Set X)ᶜ)).Nonempty :=
    hrange ▸ ⟨(complementaryCurveι C).base y, y, rfl⟩
  obtain ⟨x₀, hx₀⟩ : ((C.support : Set X)ᶜ).Nonempty := closure_nonempty_iff.mp hclne
  -- the component of `X` through a point of that complement lies in `X'`
  have hW : irreducibleComponent x₀ ∈ irreducibleComponents X :=
    irreducibleComponent_mem_irreducibleComponents x₀
  have hWsub : irreducibleComponent x₀ ⊆ Set.range (complementaryCurveι C).base := by
    rw [hrange]
    intro w hw
    rw [mem_closure_iff]
    intro O hO hwO
    obtain ⟨z, -, hzO, hzc⟩ := hW.1.2 O ((C.support : Set X)ᶜ) hO
      C.support.isClosed.isOpen_compl ⟨w, hw, hwO⟩ ⟨x₀, mem_irreducibleComponent, hx₀⟩
    exact ⟨z, hzO, hzc⟩
  -- and that component has dimension one, which bounds the dimension below
  have hdimW : topologicalKrullDim (irreducibleComponent x₀) = 1 :=
    topologicalKrullDim_irreducibleComponent_eq_one (X ↘ Spec (.of k)) hXeq hdim _ hW
  have hsub : topologicalKrullDim
      ((complementaryCurveι C).base ⁻¹' irreducibleComponent x₀) = 1 :=
    (IsHomeomorph.topologicalKrullDim_eq _
      ((complementaryCurveι C).isClosedEmbedding.isEmbedding.homeomorphOfSubsetRange
        hWsub).isHomeomorph).trans hdimW
  refine le_antisymm hle ?_
  rw [← hsub]
  exact topologicalKrullDim_subspace_le _ _

/-- The restriction map `Γ(X, 𝒪_X) ⟶ Γ(X', 𝒪_{X'})` along the inclusion of the closure of the
complement of a rational tail is an isomorphism: the canonical contraction splits it, and the
contraction itself is an isomorphism on global sections. -/
theorem isIso_appTop_complementaryCurveι
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : HasAtWorstNodalSingularities k X)
    (C : X.IdealSheafData) (hC : IsRationalTail k X C) :
    IsIso (complementaryCurveι C).appTop := by
  have : IsReduced X := isReduced_of_hasAtWorstNodalSingularities k X hnodal
  have hc := isContractionOfRationalTail_canonicalContraction k X hdim hnodal C hC
  have hciso : IsIso (canonicalContraction k X hdim hnodal C hC).appTop :=
    isIso_appTop_of_isContractionOfRationalTail hC hc
  have hid : (canonicalContraction k X hdim hnodal C hC).appTop ≫
      (complementaryCurveι C).appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, hc.1]
    simp
  have : IsIso ((canonicalContraction k X hdim hnodal C hC).appTop ≫
      (complementaryCurveι C).appTop) := hid ▸ inferInstance
  exact IsIso.of_isIso_comp_left
    (canonicalContraction k X hdim hnodal C hC).appTop _

/-- **Stacks 0E3H.** The scheme-theoretic closure `X'` of the complement of a rational tail of
a proper one-dimensional nodal curve over a field with only constant global functions again has
only constant global functions: `H⁰(X', 𝒪_{X'}) = k`. -/
@[stacks 0E3H "complementary_curve_has_constant_global_functions"]
theorem isIso_globalSections_complementaryCurve
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : HasAtWorstNodalSingularities k X)
    (C : X.IdealSheafData) (hC : IsRationalTail k X C) :
    IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫
      (complementaryCurveι C ≫ (X ↘ Spec (.of k))).appTop) := by
  have := isIso_appTop_complementaryCurveι k X hdim hnodal C hC
  rw [Scheme.Hom.comp_appTop, ← Category.assoc]
  infer_instance

/-- The genus of the scheme-theoretic closure `X'` of the complement of a closed subscheme of a
proper one-dimensional curve over a field is at most the genus of the curve. This is the
unconditional form of Tag 0CE3 applied to the closed immersion `X' ⟶ X`; for a rational tail
the two genera agree, but that needs the vanishing of `R¹c_*𝒪_X`. -/
theorem genus_complementaryCurve_le
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1) (C : X.IdealSheafData) :
    genus (complementaryCurveι C ≫ (X ↘ Spec (.of k))) ≤ genus (X ↘ Spec (.of k)) :=
  genus_le_of_isFinite_of_isClosedImmersion_over_dense_open k (X ↘ Spec (.of k))
    (complementaryCurveι C) hdim.le ⊤ (by simp) inferInstance

/-! ### `X'` away from the tail

Away from `C` the curve `X'` is nothing new: the open complement of `C` in `X` sits inside
`X'` as an open subscheme, namely as the complement in `X'` of the attaching locus. This is
the geometric input for the at-worst-nodal clause of Tag 0E3H away from the attaching point,
which is `Stacks.Curves.smoothAt_or_isNode_complementaryCurve_of_notMem_support`, and for the
vanishing of `R¹c_*𝒪_X` away from that point, which is not proved in this development.
-/

/-- The open complement of a closed subscheme of a proper scheme over a field is
quasi-compact, the ambient scheme being Noetherian. -/
theorem quasiCompact_ι_support_compl
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] (C : X.IdealSheafData) :
    QuasiCompact (Scheme.Opens.ι (C.support.compl : X.Opens)) := by
  have := isNoetherian_of_isProper k X
  infer_instance

/-- The complement of a closed subscheme of a proper scheme over a field is an open subscheme
of the scheme-theoretic closure of that complement. -/
theorem isOpenImmersion_toImage_ι_support_compl
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] (C : X.IdealSheafData) :
    IsOpenImmersion (Scheme.Opens.ι (C.support.compl : X.Opens)).toImage := by
  have := quasiCompact_ι_support_compl k X C
  infer_instance

/-- As an open subscheme of the scheme-theoretic closure `X'` of the complement of `C`, the
complement of `C` in `X` is the preimage in `X'` of that complement. -/
theorem range_toImage_ι_support_compl
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    (C : X.IdealSheafData) :
    Set.range (Scheme.Opens.ι (C.support.compl : X.Opens)).toImage.base =
      ((complementaryCurveι C) ⁻¹ᵁ (C.support.compl : X.Opens) :
        Set (complementaryCurve C)) := by
  have hinj : Function.Injective (complementaryCurveι C).base :=
    (complementaryCurveι C).isClosedEmbedding.injective
  have himg : (complementaryCurveι C).base ''
      Set.range (Scheme.Opens.ι (C.support.compl : X.Opens)).toImage.base =
        ((C.support.compl : X.Opens) : Set X) := by
    rw [← Set.range_comp,
      show ((complementaryCurveι C).base ∘
          (Scheme.Opens.ι (C.support.compl : X.Opens)).toImage.base) =
        ((Scheme.Opens.ι (C.support.compl : X.Opens)).toImage ≫
          complementaryCurveι C).base from rfl,
      Scheme.Hom.toImage_imageι, Scheme.Opens.range_ι]
  rw [← Set.preimage_image_eq (Set.range _) hinj, himg]
  rfl

/-- The identification of the complement of `C` in `X` with the complement of the attaching
locus in the scheme-theoretic closure `X'` of that complement. -/
def tailComplementIso
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] (C : X.IdealSheafData) :
    ((C.support.compl : X.Opens) : Scheme.{u}) ≅
      (((complementaryCurveι C) ⁻¹ᵁ (C.support.compl : X.Opens)) : Scheme.{u}) :=
  letI := isOpenImmersion_toImage_ι_support_compl k X C
  IsOpenImmersion.isoOfRangeEq
    (Scheme.Opens.ι (C.support.compl : X.Opens)).toImage
    (Scheme.Opens.ι ((complementaryCurveι C) ⁻¹ᵁ (C.support.compl : X.Opens)))
    (by rw [range_toImage_ι_support_compl k X C, Scheme.Opens.range_ι])

/-- The identification of `Stacks.Curves.tailComplementIso` is compatible with the inclusions
of both open subschemes into `X`. -/
theorem tailComplementIso_hom_ι
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] (C : X.IdealSheafData) :
    (tailComplementIso k X C).hom ≫
        Scheme.Opens.ι ((complementaryCurveι C) ⁻¹ᵁ (C.support.compl : X.Opens)) ≫
          complementaryCurveι C =
      Scheme.Opens.ι (C.support.compl : X.Opens) := by
  let := isOpenImmersion_toImage_ι_support_compl k X C
  have h : (tailComplementIso k X C).hom ≫
      Scheme.Opens.ι ((complementaryCurveι C) ⁻¹ᵁ (C.support.compl : X.Opens)) =
        (Scheme.Opens.ι (C.support.compl : X.Opens)).toImage :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  rw [← Category.assoc, h, Scheme.Hom.toImage_imageι]

end Stacks.Curves

end
