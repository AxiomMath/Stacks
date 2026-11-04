module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.Reduced
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.RationalTail

/-!
# A closed subscheme and the closure of its complement cover a reduced scheme

Let `X` be a scheme and let `C` be a closed subscheme, given by an ideal sheaf `C` on `X`. The
scheme-theoretic closure of the complement of `C` is cut out by the ideal sheaf
`AlgebraicGeometry.complementaryCurveIdeal C`, and the scheme-theoretic union of the two closed
subschemes is cut out by the infimum `C ⊓ complementaryCurveIdeal C`. Set-theoretically the two
supports already cover `X`, so a section of the infimum vanishes at every point of `X` and is
therefore nilpotent. Hence on a reduced scheme the union is the whole of `X`, that is, the
infimum is `⊥`.

Applied to a rational tail `C` on a proper one-dimensional scheme over a field with at-worst-nodal
singularities, this is the assertion used in Tag 0E3H that `X` is the scheme-theoretic union of
`C` and the closure of its complement — which the source justifies with the parenthesis
"(as `X` is reduced)", reducedness coming from nodality.

## Main definitions

* `Stacks.Curves.tailAttachingPointIdeal` — the reduced attaching point of a rational tail as a
  closed subscheme of the ambient curve.

## Main results

* `Stacks.Curves.inf_complementaryCurveIdeal_eq_bot` — on a reduced scheme, a closed subscheme
  and the scheme-theoretic closure of its complement have scheme-theoretic union the whole
  scheme.
* `Stacks.Curves.mem_complementaryCurveIdeal_ideal_iff` — on a reduced scheme, a section lies in
  the ideal of the closure of the complement of `C` exactly when its basic open lies in the
  support of `C`.
* `Stacks.Curves.complementaryCurveIdeal_ideal_eq_annihilator` — on a reduced scheme, the ideal
  of the closure of the complement of `C` is, over every affine open, the annihilator of `C`.
* `Stacks.Curves.tail_inf_complementaryCurveIdeal_eq_bot` — the same statement for a rational
  tail on a proper nodal curve, where reducedness is supplied by the nodality hypothesis.

## Implementation notes

Closed subschemes are represented by `Scheme.IdealSheafData`, whose order is inclusion of ideal
sheaves; so the scheme-theoretic union of two closed subschemes is cut out by `⊓` and the whole
scheme by `⊥`. The proof is the Galois connection between `support` and `vanishingIdeal`: on a
reduced scheme an ideal sheaf is `⊥` exactly when its support is everything
(`Scheme.IdealSheafData.support_eq_top_iff`), the support of an infimum contains the support of
each factor, and the support of the kernel of a morphism contains its set-theoretic range
(`Scheme.Hom.range_subset_ker_support`), here the whole complement of the support of `C`. No
quasi-compactness is needed, because only that inclusion is used and not the identification of
the support of a kernel with the closure of the range.

## References

* [Stacks Project, Tag 0E3H](https://stacks.math.columbia.edu/tag/0E3H)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Curves

/-- The reduced attaching point of a rational tail, as a closed subscheme of the ambient curve:
the vanishing ideal sheaf of the closed singleton consisting of that point. -/
abbrev tailAttachingPointIdeal {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] {C : X.IdealSheafData} (hC : IsRationalTail k X C) :
    X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    ⟨{C.subschemeι hC.attachingPoint}, hC.attachingPoint_isClosed⟩

/-- On a reduced scheme, a closed subscheme and the scheme-theoretic closure of its complement
have scheme-theoretic union the whole scheme: the two supports cover `X`, so a section of the
intersection of the two ideal sheaves is nilpotent, hence zero. -/
theorem inf_complementaryCurveIdeal_eq_bot {X : Scheme.{u}} [IsReduced X]
    (C : X.IdealSheafData) :
    C ⊓ complementaryCurveIdeal C = ⊥ := by
  rw [← Scheme.IdealSheafData.support_eq_top_iff]
  refine le_antisymm le_top ?_
  have hrange : ((C.support.compl : X.Opens) : Set X) ⊆
      ((complementaryCurveIdeal C).support : Set X) := by
    rw [← Scheme.Opens.range_ι]
    exact Scheme.Hom.range_subset_ker_support _
  intro x _
  by_cases hx : x ∈ (C.support : Set X)
  · exact Scheme.IdealSheafData.support_antitone inf_le_left hx
  · exact Scheme.IdealSheafData.support_antitone inf_le_right (hrange hx)

/-- A point of an affine open lies off the support of an ideal sheaf exactly when it lies in the
basic open of some section of the ideal over that affine open. -/
theorem not_mem_support_iff_exists_mem_basicOpen {X : Scheme.{u}} {C : X.IdealSheafData}
    {U : X.affineOpens} {x : X} (hx : x ∈ U.1) :
    x ∉ C.support ↔ ∃ b ∈ C.ideal U, x ∈ X.basicOpen b := by
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hx, Scheme.mem_zeroLocus_iff]
  push Not
  exact Iff.rfl

/-- On a reduced scheme, a section whose basic open has no points is zero. -/
private theorem eq_zero_of_forall_not_mem_basicOpen {X : Scheme.{u}} [IsReduced X]
    {U : X.Opens} {a : Γ(X, U)} (h : ∀ x, x ∉ X.basicOpen a) : a = 0 := by
  refine eq_zero_of_basicOpen_eq_bot _ ?_
  ext x
  simpa using h x

/-- **A section lies in the ideal of the closure of the complement exactly when its basic open
lies in the support.** On a reduced scheme, a section over an affine open restricts to zero on
the open complement of the support of `C` exactly when it vanishes at every point off that
support. -/
theorem mem_complementaryCurveIdeal_ideal_iff {X : Scheme.{u}} [IsReduced X]
    (C : X.IdealSheafData) [QuasiCompact (Scheme.Opens.ι C.support.compl)]
    (U : X.affineOpens) (a : Γ(X, U.1)) :
    a ∈ (complementaryCurveIdeal C).ideal U ↔ ∀ x ∈ X.basicOpen a, x ∈ C.support := by
  set W : X.Opens := C.support.compl
  have hW : ∀ x : X, x ∈ W ↔ x ∉ C.support := fun x => Iff.rfl
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
  constructor
  · intro h x hxa
    by_contra hxW
    have hpre : (⟨x, (hW x).2 hxW⟩ : W.toScheme) ∈ W.ι ⁻¹ᵁ X.basicOpen a := hxa
    rwa [Scheme.preimage_basicOpen, h, Scheme.basicOpen_zero] at hpre
  · intro h
    refine eq_zero_of_forall_not_mem_basicOpen fun y hy => ?_
    rw [← Scheme.preimage_basicOpen] at hy
    exact (hW y.1).1 y.2 (h y.1 hy)

/-- **On a reduced scheme the closure of the complement of `C` is cut out by the annihilator of
`C`.** Over every affine open `U`, the ideal of the scheme-theoretic closure of the complement of
the support of `C` is the annihilator of `C(U)`: both consist of the sections whose basic open
lies in the support. -/
theorem complementaryCurveIdeal_ideal_eq_annihilator {X : Scheme.{u}} [IsReduced X]
    (C : X.IdealSheafData) [QuasiCompact (Scheme.Opens.ι C.support.compl)]
    (U : X.affineOpens) :
    (complementaryCurveIdeal C).ideal U = Submodule.annihilator (C.ideal U) := by
  ext a
  rw [mem_complementaryCurveIdeal_ideal_iff, Submodule.mem_annihilator]
  constructor
  · intro h b hb
    refine eq_zero_of_forall_not_mem_basicOpen fun x hx => ?_
    rw [smul_eq_mul, Scheme.basicOpen_mul] at hx
    exact (not_mem_support_iff_exists_mem_basicOpen (X.basicOpen_le a hx.1)).2 ⟨b, hb, hx.2⟩
      (h x hx.1)
  · intro h x hxa
    by_contra hxW
    obtain ⟨b, hb, hxb⟩ := (not_mem_support_iff_exists_mem_basicOpen
      (X.basicOpen_le a hxa)).1 hxW
    have hmem : x ∈ X.basicOpen (a * b) := by
      rw [Scheme.basicOpen_mul]
      exact ⟨hxa, hxb⟩
    rwa [← smul_eq_mul, h b hb, Scheme.basicOpen_zero] at hmem

/-- A rational tail `C` on a proper one-dimensional scheme over a field with at-worst-nodal
singularities and with only constant global functions, together with the scheme-theoretic closure
of its complement, has scheme-theoretic union the entire curve. Reducedness of the curve comes
from the nodality hypothesis. -/
@[stacks 0E3H "scheme_theoretic_union"]
theorem tail_inf_complementaryCurveIdeal_eq_bot (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    (_hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : HasAtWorstNodalSingularities k X) (C : X.IdealSheafData)
    (_hC : IsRationalTail k X C) :
    C ⊓ complementaryCurveIdeal C = ⊥ := by
  have : IsReduced X := isReduced_of_hasAtWorstNodalSingularities k X hnodal
  exact inf_complementaryCurveIdeal_eq_bot C

end Stacks.Curves

end
