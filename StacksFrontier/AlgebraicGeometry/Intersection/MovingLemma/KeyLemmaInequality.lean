module

public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.KeyLemma
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.SubvarietyIntersection
public import StacksFrontier.AlgebraicGeometry.IrreducibleComponentSubscheme.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0B0E with the source's inequality

Lemma 0B0E asserts `dim (Z_j ∩ T_i) ≤ dim (Z ∩ T_i)` for the components `Z_j` of `C · X` other
than `Z`. The construction in `StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.KeyLemma`
yields the disjunction `dim (Z_j ∩ T_i) ≤ dim (Z ∩ T_i) ∨ dim (Z_j ∩ T_i) + n ≤ d + d'`, which is
condition (4) of the source's proof. This module derives the source's inequality from it at every
`i` with `Z ∩ T_i` nonempty, by Tag 0AZP, and states the lemma with both clauses.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.add_le_add_topologicalKrullDim_inter_of_nonempty`:
  Tag 0AZP for the whole intersection, `dim Z + dim T ≤ dim X + dim (Z ∩ T)` when `Z ∩ T ≠ ∅`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_intersectProperly_torFormulaCycleIntersectionProduct_eq_and_le`:
  Tag 0B0E.

## Implementation notes

When `Z ∩ T_i = ∅` the source's inequality asks `Z_j ∩ T_i = ∅`, and that is false: on a
nonsingular quadric surface `X ⊆ 𝐏^3` take `Z` and `T_1` two distinct lines of one ruling (see the
implementation notes of `StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.KeyLemma`). The
inequality is therefore stated at each `i` with `Z ∩ T_i` nonempty, and the disjunction, which is
what the proof gives, is kept for every `i`; the strict clause is vacuous when `Z ∩ T_i = ∅`.

## References

* [Stacks Project, Tag 0B0E](https://stacks.math.columbia.edu/tag/0B0E)
* [Stacks Project, Tag 0AZP](https://stacks.math.columbia.edu/tag/0AZP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.Chow

universe u

namespace AlgebraicGeometry

namespace ProjectiveSpaceOfModule

/-- **Tag 0AZP for the whole intersection.** On a nonsingular variety over an algebraically closed
field, two closed subvarieties `Z` and `T` with nonempty intersection satisfy
`dim Z + dim T ≤ dim X + dim (Z ∩ T)`. -/
public theorem add_le_add_topologicalKrullDim_inter_of_nonempty (k : Type u) [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsVariety k f] (hX : IsRegular X)
    (Z T : IrreducibleCloseds X) (hne : ((Z : Set X) ∩ (T : Set X)).Nonempty) :
    topologicalKrullDim (Z : Set X) + topologicalKrullDim (T : Set X) ≤
      topologicalKrullDim X + topologicalKrullDim ↥((Z : Set X) ∩ (T : Set X)) := by
  set I := Scheme.IdealSheafData.vanishingIdeal (X := X) ⟨(Z : Set X), Z.isClosed⟩ with hI
  set J := Scheme.IdealSheafData.vanishingIdeal (X := X) ⟨(T : Set X), T.isClosed⟩ with hJ
  have := StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible
    ⟨(Z : Set X), Z.isClosed⟩ Z.isIrreducible
  have := StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible
    ⟨(T : Set X), T.isClosed⟩ T.isIrreducible
  have hF : ((I.support : Set X) ∩ (J.support : Set X)) = (Z : Set X) ∩ (T : Set X) := by
    rw [hI, hJ, Scheme.IdealSheafData.coe_support_vanishingIdeal,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  obtain ⟨p, hp⟩ := hne
  obtain ⟨c, hc, -⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    ({(⟨p, hF ▸ hp⟩ : ↥((I.support : Set X) ∩ (J.support : Set X)))} : Set _)
    isIrreducible_singleton
  have h0AZP :=
    Stacks.Intersection.add_topologicalKrullDim_le_add_topologicalKrullDim_of_irreducibleComponent
      f hX I J c hc
  have hIZ : topologicalKrullDim I.subscheme = topologicalKrullDim (Z : Set X) :=
    TorFormula.topologicalKrullDim_subscheme_vanishingIdeal Z
  have hJT : topologicalKrullDim J.subscheme = topologicalKrullDim (T : Set X) :=
    TorFormula.topologicalKrullDim_subscheme_vanishingIdeal T
  rw [hIZ, hJT] at h0AZP
  calc topologicalKrullDim (Z : Set X) + topologicalKrullDim (T : Set X)
      ≤ topologicalKrullDim X + topologicalKrullDim ↥c := h0AZP
    _ ≤ topologicalKrullDim X +
        topologicalKrullDim ↥((I.support : Set X) ∩ (J.support : Set X)) :=
      add_le_add_right (topologicalKrullDim_subspace_le _ c) _
    _ = topologicalKrullDim X + topologicalKrullDim ↥((Z : Set X) ∩ (T : Set X)) := by
      rw [hF]

/-- Cancellation of a natural summand in `WithBot ℕ∞`. -/
private theorem le_of_add_natCast_le_add_natCast {a b : WithBot ℕ∞} {n : ℕ}
    (h : a + (n : WithBot ℕ∞) ≤ b + (n : WithBot ℕ∞)) : a ≤ b := by
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe x =>
    induction b using WithBot.recBotCoe with
    | bot => simp at h
    | coe y =>
      have h' : x + (n : ℕ∞) ≤ y + (n : ℕ∞) := by exact_mod_cast h
      exact WithBot.coe_le_coe.mpr ((ENat.add_le_add_iff_right (ENat.coe_ne_top n)).mp h')

/-- **Stacks Project, Tag 0B0E.** Let `X ⊆ 𝐏(V)` be a nonsingular closed subvariety of dimension
`n` of the projective space of a vector space of dimension `N + 1` over an algebraically closed
field; let `Z ⊆ X` be a closed subvariety of dimension `d < n`, and let `T_i ⊆ X` be finitely
many closed subvarieties of dimension `d' < n`. Then there is a closed subvariety `C ⊆ 𝐏(V)`
whose prime cycle intersects that of `X` properly, with

`C · X = [Z] + ∑ m_j [Z_j]`

in the Tor-formula intersection product of Section 0B08, where the `Z_j ⊆ X` are irreducible
closed of dimension `d`, distinct from `Z`, with nonzero multiplicities, and where

* `dim (Z_j ∩ T_i) ≤ dim (Z ∩ T_i)` for every `i` with `Z ∩ T_i` nonempty,
* `dim (Z_j ∩ T_i) ≤ dim (Z ∩ T_i)` or `dim (Z_j ∩ T_i) + n ≤ d + d'` for every `i`, and
* `dim (Z_j ∩ T_i) < dim (Z ∩ T_i)` whenever `Z` does not intersect `T_i` properly inside `X`.

For `Z ∩ T_i = ∅` the first inequality would say `Z_j ∩ T_i = ∅`, which fails for two lines of one
ruling on a quadric surface in `𝐏^3`; there the second clause is what holds. -/
@[stacks 0B0E "the whole lemma, with the erratum that the source's inequality \
`dim (Z_j ∩ T_i) ≤ dim (Z ∩ T_i)` is stated at each `i` with `Z ∩ T_i` nonempty: for \
`Z ∩ T_i = ∅` it is false, as a nonsingular quadric surface in 𝐏^3 with Z and T_1 two distinct \
lines of one ruling shows (see the implementation notes of \
`StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.KeyLemma`). At every `i` the statement \
also carries `dim (Z_j ∩ T_i) ≤ dim (Z ∩ T_i) ∨ dim (Z_j ∩ T_i) + n ≤ d + d'`, which is \
condition (4) of the source's proof and holds in that bottom case too; the strict inequality, \
when `Z` and `T_i` do not intersect properly in `X`, is as in the source. `X ⊂ 𝐏^N` is read as \
`⊆`, so `dim X = N` is covered, with `C = Z` and no `Z_j`. Dimensions are \
`topologicalKrullDim` in `WithBot ℕ∞`, written additively."]
public theorem exists_intersectProperly_torFormulaCycleIntersectionProduct_eq_and_le
    (k V : Type u) [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Nontrivial V] [DecidableEq (projectiveSpaceOfModule k V)]
    {N n d d' : ℕ} (hV : Module.finrank k V = N + 1)
    {X : Scheme.{u}} (iX : X ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion iX]
    [IsVariety k (iX ≫ projectiveSpaceOfModuleToSpec k V)] (hXreg : IsRegular X)
    (hdimX : topologicalKrullDim X = (n : WithBot ℕ∞))
    (hd : d < n) (hd' : d' < n)
    (Z : Set X) (hZcl : IsClosed Z) (hZirr : IsIrreducible Z)
    (hZd : topologicalKrullDim ↥Z = (d : WithBot ℕ∞))
    {ι : Type*} [Finite ι] (T : ι → Set X) (hTcl : ∀ i, IsClosed (T i))
    (hTirr : ∀ i, IsIrreducible (T i))
    (hTd : ∀ i, topologicalKrullDim ↥(T i) = (d' : WithBot ℕ∞))
    (XC ZC : IrreducibleCloseds (projectiveSpaceOfModule k V))
    (TC : ι → IrreducibleCloseds (projectiveSpaceOfModule k V))
    (hXC : (XC : Set (projectiveSpaceOfModule k V)) = Set.range iX.base)
    (hZC : (ZC : Set (projectiveSpaceOfModule k V)) = iX.base '' Z)
    (hTC : ∀ i, (TC i : Set (projectiveSpaceOfModule k V)) = iX.base '' (T i)) :
    ∃ (C : IrreducibleCloseds (projectiveSpaceOfModule k V))
      (S : Finset (IrreducibleCloseds (projectiveSpaceOfModule k V)))
      (m : IrreducibleCloseds (projectiveSpaceOfModule k V) → ℤ),
      AlgebraicCycle.IntersectProperly
          (Function.locallyFinsuppWithin.single C.isIrreducible.genericPoint (1 : ℤ))
          (Function.locallyFinsuppWithin.single XC.isIrreducible.genericPoint (1 : ℤ)) ∧
        TorFormula.torFormulaCycleIntersectionProduct (fieldChowSituation k)
            (projectiveSpaceOfModuleToSpec k V) (isRegular_projectiveSpaceOfModule k V) (d : ℤ)
            (Function.locallyFinsuppWithin.single C.isIrreducible.genericPoint (1 : ℤ))
            (Function.locallyFinsuppWithin.single XC.isIrreducible.genericPoint (1 : ℤ)) =
          Function.locallyFinsuppWithin.single ZC.isIrreducible.genericPoint (1 : ℤ) +
            ∑ W ∈ S, m W • Function.locallyFinsuppWithin.single
              W.isIrreducible.genericPoint (1 : ℤ) ∧
        ZC ∉ S ∧ (∀ W ∈ S, m W ≠ 0) ∧
        (∀ W ∈ S, (W : Set (projectiveSpaceOfModule k V)) ⊆
          (XC : Set (projectiveSpaceOfModule k V))) ∧
        (∀ W ∈ S, topologicalKrullDim (W : Set (projectiveSpaceOfModule k V)) =
          (d : WithBot ℕ∞)) ∧
        (∀ W ∈ S, ∀ i,
          ((ZC : Set (projectiveSpaceOfModule k V)) ∩
              (TC i : Set (projectiveSpaceOfModule k V))).Nonempty →
            topologicalKrullDim ↥((W : Set (projectiveSpaceOfModule k V)) ∩
                (TC i : Set (projectiveSpaceOfModule k V))) ≤
              topologicalKrullDim ↥((ZC : Set (projectiveSpaceOfModule k V)) ∩
                (TC i : Set (projectiveSpaceOfModule k V)))) ∧
        (∀ W ∈ S, ∀ i,
          topologicalKrullDim ↥((W : Set (projectiveSpaceOfModule k V)) ∩
                (TC i : Set (projectiveSpaceOfModule k V))) ≤
              topologicalKrullDim ↥((ZC : Set (projectiveSpaceOfModule k V)) ∩
                (TC i : Set (projectiveSpaceOfModule k V))) ∨
            topologicalKrullDim ↥((W : Set (projectiveSpaceOfModule k V)) ∩
                  (TC i : Set (projectiveSpaceOfModule k V))) + (n : WithBot ℕ∞) ≤
              (d : WithBot ℕ∞) + (d' : WithBot ℕ∞)) ∧
        (∀ W ∈ S, ∀ i,
          ¬ (topologicalKrullDim ↥((ZC : Set (projectiveSpaceOfModule k V)) ∩
                  (TC i : Set (projectiveSpaceOfModule k V))) +
                topologicalKrullDim (XC : Set (projectiveSpaceOfModule k V)) ≤
              topologicalKrullDim (ZC : Set (projectiveSpaceOfModule k V)) +
                topologicalKrullDim (TC i : Set (projectiveSpaceOfModule k V))) →
            topologicalKrullDim ↥((W : Set (projectiveSpaceOfModule k V)) ∩
                (TC i : Set (projectiveSpaceOfModule k V))) <
              topologicalKrullDim ↥((ZC : Set (projectiveSpaceOfModule k V)) ∩
                (TC i : Set (projectiveSpaceOfModule k V)))) := by
  obtain ⟨C, S, m, hCX, heq, hZS, hm, hsub, hWd, hor, hlt⟩ :=
    exists_intersectProperly_torFormulaCycleIntersectionProduct_eq k V hV iX hXreg hdimX hd hd'
      Z hZcl hZirr hZd T hTcl hTirr hTd XC ZC TC hXC hZC hTC
  refine ⟨C, S, m, hCX, heq, hZS, hm, hsub, hWd, fun W hW i hne => ?_, hor, hlt⟩
  rcases hor W hW i with h | h
  · exact h
  have hinj : Function.Injective iX.base := iX.isClosedEmbedding.injective
  have hZT : (ZC : Set (projectiveSpaceOfModule k V)) ∩ (TC i : Set _) =
      iX.base '' (Z ∩ T i) := by
    rw [hZC, hTC i, Set.image_inter hinj]
  have hdimZT : topologicalKrullDim ↥((ZC : Set (projectiveSpaceOfModule k V)) ∩
      (TC i : Set (projectiveSpaceOfModule k V))) = topologicalKrullDim ↥(Z ∩ T i) := by
    rw [hZT]
    exact topologicalKrullDim_image_eq_of_isEmbedding iX.isClosedEmbedding.isEmbedding _
  have hne' : ((⟨Z, hZirr, hZcl⟩ : IrreducibleCloseds X) : Set X) ∩
      ((⟨T i, hTirr i, hTcl i⟩ : IrreducibleCloseds X) : Set X) |>.Nonempty := by
    rw [hZT] at hne
    exact hne.of_image
  have h0 := add_le_add_topologicalKrullDim_inter_of_nonempty k
    (iX ≫ projectiveSpaceOfModuleToSpec k V) hXreg ⟨Z, hZirr, hZcl⟩ ⟨T i, hTirr i, hTcl i⟩ hne'
  change topologicalKrullDim ↥Z + topologicalKrullDim ↥(T i) ≤
    topologicalKrullDim X + topologicalKrullDim ↥(Z ∩ T i) at h0
  rw [hZd, hTd i, hdimX, ← hdimZT, add_comm (n : WithBot ℕ∞)] at h0
  exact le_of_add_natCast_le_add_natCast (h.trans h0)

end ProjectiveSpaceOfModule

end AlgebraicGeometry

end
