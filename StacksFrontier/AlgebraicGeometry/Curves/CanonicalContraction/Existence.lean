module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Stalk
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.ClosedUnionPushout
public import StacksFrontier.AlgebraicGeometry.Curves.DirectImage.RationalTailContraction
public import StacksFrontier.AlgebraicGeometry.Normalization.CompletionSpecialFibrePoints

/-!
# The canonical contraction of a rational tail

Let `k` be a field and let `X` be a proper one-dimensional scheme over `k` with at-worst-nodal
singularities and `H⁰(X, 𝒪_X) = k`. Let `C ⊆ X` be a rational tail (Tag 0E3H), let `X' ⊆ X` be
the scheme-theoretic closure of the complement of `C` and let `x` be the attaching point at
which the two meet. Then there is a *unique* morphism `c : X ⟶ X'` contracting `C`, that is,
restricting to the identity on `X'` and carrying `C` to `x` through the canonical morphism
`C ⟶ Spec κ(x)`.

The construction is a pushout. The attaching point, as a closed subscheme of `X`, is cut out by
`C ⊔ 𝒥` where `𝒥` is the ideal sheaf of `X'`, and is also the scheme-theoretic image of
`Spec κ(x) ⟶ C ⟶ X`; so `Spec κ(x)` *is* that subscheme, and the inclusion of the attaching
point into `X'` is read off from it. Because `X` is reduced — nodality gives that — the two
closed subschemes `C` and `X'` cover `X` scheme-theoretically, so `C ⊓ 𝒥 = ⊥` and `X` is the
scheme-theoretic union of `C` and `X'`. The union of two closed subschemes is the pushout of
the two over their intersection, so a morphism out of `X` is exactly a pair of morphisms out of
`C` and out of `X'` agreeing on the attaching point; the pair consisting of `C ⟶ Spec κ(x) ⟶ X'`
and the identity of `X'` does agree there, and the morphism it induces is the contraction.
Uniqueness is the uniqueness half of the same pushout property.

## Main definitions

* `Stacks.Curves.canonicalContraction` — the canonical contraction of a rational tail onto the
  closure of the complement, the morphism whose existence and uniqueness is
  `Stacks.Curves.existsUnique_contractionOfRationalTail`.

## Main results

* `Stacks.Curves.existsUnique_contractionOfRationalTail` — a rational tail admits exactly one
  contraction.
* `Stacks.Curves.isContractionOfRationalTail_canonicalContraction` — the canonical contraction
  is a contraction.
* `Stacks.Curves.isIso_structureSheaf_to_pushforward_canonicalContraction` — the canonical map
  `𝒪_{X'} ⟶ c_*𝒪_X` of sheaves of rings is an isomorphism for the canonical contraction `c`.

## Implementation notes

The attaching point is identified with the subscheme cut out by `C ⊔ 𝒥` by
`AlgebraicGeometry.IsClosedImmersion.isIso_lift`: the morphism
`Spec κ(x) ⟶ C ⟶ X` is a closed immersion whose kernel is exactly that ideal sheaf, which is
what the rational-tail condition asserts. The pushout property of the union is
`AlgebraicGeometry.Scheme.IdealSheafData.isPushout_subscheme_inf`, and the identification of
the union with `X` itself is `Stacks.Curves.tail_inf_complementaryCurveIdeal_eq_bot`.

The existence-and-uniqueness clause and the direct-image clause for the canonical contraction
carry `@[stacks 0E3H]` sub-labels, distinct from `"rational_tail"` and
`"contraction_of_a_rational_tail"` used elsewhere in the covering set: the audit scanner keys
on the bare four-character tag, not on the sub-label, so each of these registrations marks the
whole tag as touched, not any single clause as the complete statement.

## References

* [Stacks Project, Tag 0E3H](https://stacks.math.columbia.edu/tag/0E3H)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Curves

/-- The attaching point of a rational tail is closed in the tail, not merely in the ambient
scheme. -/
theorem isClosed_singleton_attachingPoint_subscheme
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    {C : X.IdealSheafData} (hC : IsRationalTail k X C) :
    IsClosed ({hC.attachingPoint} : Set C.subscheme) := by
  have hpre := hC.attachingPoint_isClosed.preimage C.subschemeι.continuous
  have heq : C.subschemeι ⁻¹' ({C.subschemeι hC.attachingPoint} : Set X) =
      ({hC.attachingPoint} : Set C.subscheme) := by
    ext y
    exact C.subschemeι.isClosedEmbedding.injective.eq_iff
  rwa [← heq]

/-- The attaching point of a rational tail is closed in the tail, not merely in the ambient
scheme. -/
private alias attachingPoint_isClosed_in_tail := isClosed_singleton_attachingPoint_subscheme

/-- The canonical morphism from a rational tail to the spectrum of the residue field at its
attaching point is a retraction of the residue-field point. -/
private theorem fromSpec_comp_canonicalMap
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    {C : X.IdealSheafData} (hC : IsRationalTail k X C) :
    C.subscheme.fromSpecResidueField hC.attachingPoint ≫
      canonicalMapToAttachingPoint hC =
        𝟙 (Spec (C.subscheme.residueField hC.attachingPoint)) := by
  simp only [canonicalMapToAttachingPoint, Scheme.fromSpecResidueField,
    Category.assoc, Scheme.fromSpecStalk_toSpecΓ_assoc,
    ← AlgebraicGeometry.Spec.map_comp]
  rw [← AlgebraicGeometry.Spec.map_id, AlgebraicGeometry.Spec.map_inj]
  simp [Scheme.Γevaluation, Scheme.evaluation]

/-- The residue-field point of the attaching point of a rational tail, viewed in the ambient
scheme, is a closed immersion cutting out the reduced attaching point. -/
theorem ker_fromSpecResidueField_attachingPoint_comp_subschemeι
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    {C : X.IdealSheafData} (hC : IsRationalTail k X C) :
    (C.subscheme.fromSpecResidueField hC.attachingPoint ≫ C.subschemeι).ker =
      Scheme.IdealSheafData.vanishingIdeal
        ⟨{C.subschemeι hC.attachingPoint}, hC.attachingPoint_isClosed⟩ := by
  rw [Scheme.Hom.ker_comp,
    fromSpecResidueField_ker_eq_vanishingIdeal hC.attachingPoint
      (attachingPoint_isClosed_in_tail hC),
    Scheme.IdealSheafData.map_vanishingIdeal]
  congr 1
  apply TopologicalSpace.Closeds.ext
  change closure (C.subschemeι '' ({hC.attachingPoint} : Set C.subscheme)) =
    ({C.subschemeι hC.attachingPoint} : Set X)
  rw [Set.image_singleton, hC.attachingPoint_isClosed.closure_eq]

/-- The residue-field point of the attaching point of a rational tail, viewed in the ambient
scheme, is a closed immersion cutting out the reduced attaching point. -/
private alias attachingPoint_map_ker_eq := ker_fromSpecResidueField_attachingPoint_comp_subschemeι

/-- If two closed subschemes cut out by ideal sheaves with trivial intersection are given, a
morphism out of the ambient scheme is the same as a pair of morphisms out of the two subschemes
agreeing on the subscheme cut out by the sum of the ideals. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.existsUnique_hom_of_inf_eq_bot
    {X Y : Scheme.{u}} {I J : X.IdealSheafData} (h : I ⊓ J = ⊥)
    (f : I.subscheme ⟶ Y) (g : J.subscheme ⟶ Y)
    (w : Scheme.IdealSheafData.inclusion (le_sup_left : I ≤ I ⊔ J) ≫ f =
      Scheme.IdealSheafData.inclusion (le_sup_right : J ≤ I ⊔ J) ≫ g) :
    ∃! c : X ⟶ Y, I.subschemeι ≫ c = f ∧ J.subschemeι ≫ c = g := by
  have hpush := Scheme.IdealSheafData.isPushout_subscheme_inf I J
  have : IsIso (I ⊓ J).subschemeι := h ▸ inferInstance
  refine ⟨inv (I ⊓ J).subschemeι ≫ hpush.desc f g w, ⟨?_, ?_⟩, fun c' ⟨hf, hg⟩ => ?_⟩
  · rw [← Scheme.IdealSheafData.inclusion_subschemeι (inf_le_left : I ⊓ J ≤ I), Category.assoc,
      IsIso.hom_inv_id_assoc, hpush.inl_desc]
  · rw [← Scheme.IdealSheafData.inclusion_subschemeι (inf_le_right : I ⊓ J ≤ J), Category.assoc,
      IsIso.hom_inv_id_assoc, hpush.inr_desc]
  · rw [IsIso.eq_inv_comp]
    refine hpush.hom_ext ?_ ?_
    · rw [hpush.inl_desc, ← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι, hf]
    · rw [hpush.inr_desc, ← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι, hg]

/-- The residue-field point of the attaching point of a rational tail factors through the
closure of the complement, compatibly with the canonical morphism from the tail on the
attaching point. -/
theorem exists_fromSpecResidueField_attachingPoint_lift_complementaryCurve
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    {C : X.IdealSheafData} (hC : IsRationalTail k X C) :
    ∃ p : Spec (C.subscheme.residueField hC.attachingPoint) ⟶ complementaryCurve C,
      p ≫ complementaryCurveι C =
          C.subscheme.fromSpecResidueField hC.attachingPoint ≫ C.subschemeι ∧
        Scheme.IdealSheafData.inclusion (le_sup_left : C ≤ C ⊔ complementaryCurveIdeal C) ≫
            canonicalMapToAttachingPoint hC ≫ p =
          Scheme.IdealSheafData.inclusion
            (le_sup_right : complementaryCurveIdeal C ≤ C ⊔ complementaryCurveIdeal C) := by
  let x := hC.attachingPoint
  let J : X.IdealSheafData := complementaryCurveIdeal C
  let A : X.IdealSheafData := C ⊔ J
  let g : Spec (C.subscheme.residueField x) ⟶ X :=
    C.subscheme.fromSpecResidueField x ≫ C.subschemeι
  have hker : A.subschemeι.ker = g.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι,
      ker_fromSpecResidueField_attachingPoint_comp_subschemeι hC,
      ← hC.intersectionWithComplementaryCurveIdeal_eq]
  have : IsClosedImmersion (C.subscheme.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp (isClosed_singleton_attachingPoint_subscheme hC)
  let q : Spec (C.subscheme.residueField x) ⟶ A.subscheme :=
    IsClosedImmersion.lift A.subschemeι g hker.le
  have hq_fac : q ≫ A.subschemeι = g := IsClosedImmersion.lift_fac A.subschemeι g _
  have hqC : q ≫ Scheme.IdealSheafData.inclusion le_sup_left =
      C.subscheme.fromSpecResidueField x := by
    apply (cancel_mono C.subschemeι).1
    rw [Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι, hq_fac]
  have : IsIso q := IsClosedImmersion.isIso_lift A.subschemeι g hker
  have hpoint : Scheme.IdealSheafData.inclusion le_sup_left ≫
      canonicalMapToAttachingPoint hC ≫ q = 𝟙 A.subscheme := by
    apply (cancel_epi q).1
    rw [← Category.assoc, hqC, ← Category.assoc, fromSpec_comp_canonicalMap, Category.id_comp,
      Category.comp_id]
  refine ⟨q ≫ Scheme.IdealSheafData.inclusion le_sup_right, ?_, ?_⟩
  · dsimp [J, A]
    rw [Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι, hq_fac]
  · have h := hpoint =≫ Scheme.IdealSheafData.inclusion (le_sup_right : J ≤ A)
    rw [Category.id_comp] at h
    simpa only [Category.assoc] using h

/-- **Stacks 0E3H.** A rational tail of a proper one-dimensional nodal curve over a field with
only constant global functions admits exactly one contraction onto the scheme-theoretic closure
of its complement. -/
@[stacks 0E3H "canonical_contraction"]
theorem existsUnique_contractionOfRationalTail
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫
      (X ↘ Spec (.of k)).appTop)]
    (hnodal : HasAtWorstNodalSingularities k X)
    (C : X.IdealSheafData)
    (hC : IsRationalTail k X C) :
    ∃! c : X ⟶ complementaryCurve C, IsContractionOfRationalTail hC c := by
  obtain ⟨p, hp_fac, hglue⟩ := exists_fromSpecResidueField_attachingPoint_lift_complementaryCurve hC
  obtain ⟨c, ⟨hc_tail, hc_comp⟩, hc⟩ := Scheme.IdealSheafData.existsUnique_hom_of_inf_eq_bot
    (tail_inf_complementaryCurveIdeal_eq_bot k X hdim hnodal C hC)
    (canonicalMapToAttachingPoint hC ≫ p) (𝟙 _) (hglue.trans (Category.comp_id _).symm)
  refine ⟨c, ⟨hc_comp, p, hp_fac, hc_tail⟩, fun c' ⟨hc'comp, p', hp'fac, hp'tail⟩ => hc c' ?_⟩
  obtain rfl : p' = p := (cancel_mono (complementaryCurveι C)).1 (hp'fac.trans hp_fac.symm)
  exact ⟨hp'tail, hc'comp⟩

/-- The canonical contraction of a rational tail onto the scheme-theoretic closure of its
complement: the unique morphism supplied by
`Stacks.Curves.existsUnique_contractionOfRationalTail`. -/
def canonicalContraction
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫
      (X ↘ Spec (.of k)).appTop)]
    (hnodal : HasAtWorstNodalSingularities k X)
    (C : X.IdealSheafData)
    (hC : IsRationalTail k X C) : X ⟶ complementaryCurve C :=
  Classical.choose
    (existsUnique_contractionOfRationalTail k X hdim hnodal C hC).exists

/-- The canonical contraction restricts to the identity on the closure of the complement and
carries the rational tail to its attaching point. -/
theorem isContractionOfRationalTail_canonicalContraction
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫
      (X ↘ Spec (.of k)).appTop)]
    (hnodal : HasAtWorstNodalSingularities k X)
    (C : X.IdealSheafData)
    (hC : IsRationalTail k X C) :
    IsContractionOfRationalTail hC (canonicalContraction k X hdim hnodal C hC) :=
  Classical.choose_spec
    (existsUnique_contractionOfRationalTail k X hdim hnodal C hC).exists

/-- **Stacks 0E3H.** The canonical contraction `c : X ⟶ X'` of a rational tail induces an
isomorphism `𝒪_{X'} ⟶ c_*𝒪_X` of sheaves of rings. -/
@[stacks 0E3H "pushforward_structure_sheaf"]
theorem isIso_structureSheaf_to_pushforward_canonicalContraction
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫
      (X ↘ Spec (.of k)).appTop)]
    (hnodal : HasAtWorstNodalSingularities k X)
    (C : X.IdealSheafData)
    (hC : IsRationalTail k X C) :
    IsIso (canonicalContraction k X hdim hnodal C hC).toRingCatSheafHom :=
  isIso_structureSheaf_to_pushforward k X hdim hnodal C hC
    (isContractionOfRationalTail_canonicalContraction k X hdim hnodal C hC)

end Stacks.Curves

end
