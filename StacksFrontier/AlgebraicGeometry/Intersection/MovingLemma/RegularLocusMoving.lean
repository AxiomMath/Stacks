module

public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.KeyLemma
public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.RationalEquivalenceProduct.StepOpen
public import StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.IntersectionDimension
public import StacksFrontier.AlgebraicGeometry.IrreducibleComponentSubscheme.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.GenericImageFibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.SingularLocus.DimensionOne
public import StacksFrontier.AlgebraicGeometry.Morphisms.SingularLocus.JTwoStandardClasses
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
import StacksCore.Tactic.StacksAttribute

/-!
# Remark 0B61: the moving lemma on the nonsingular locus

Let `X ⊆ 𝐏^N` be a closed subvariety of dimension `n` over an algebraically closed field and let
`X^{reg} ⊆ X` be the open subset of nonsingular points. Remark 0B61 asks for the following version
of the moving lemma 0B0E: for a closed subvariety `Z ⊆ X^{reg}` of dimension `d < n` and finitely
many closed subvarieties `T_i ⊆ X^{reg}` of dimension `d' < n`, there is a subvariety `C ⊆ 𝐏^N`
intersecting `X` properly with `(C · X)|_{X^{reg}} = Z + ∑ m_j Z_j`, the `Z_j ⊆ X^{reg}`
irreducible of dimension `d` and distinct from `Z`, with `dim (Z_j ∩ T_i) ≤ dim (Z ∩ T_i)`, and
strict inequality when `Z` does not intersect `T_i` properly in `X^{reg}`.

This file states that version on `X^{reg}` itself, given as an open subscheme of `X` whose
underlying set is the regular locus (such an open exists: a scheme of finite type over a field is
J-2, so its regular locus is open, `exists_opens_coe_eq_regularLocus`). The non-strict clause is
proved as the source states it whenever `Z ∩ T_i` is nonempty; when `Z ∩ T_i` is empty the source's
inequality, read with `dim ∅ = -∞` (Tag 0055), would force `Z_j ∩ T_i = ∅`, which is false (the
quadric-surface counterexample in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.KeyLemma`, and `errata.md`), and what is
proved there is that every `Z_j` intersects `T_i` properly.

## Main results

* `Stacks.Intersection.add_topologicalKrullDim_le_add_topologicalKrullDim_inter`: Tag 0AZP for a
  nonempty intersection of two closed subvarieties, read on the intersection itself.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_opens_coe_eq_regularLocus`: the nonsingular
  locus of a closed subvariety of `𝐏(V)` is open.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_intersectProperly_cycleComap_regularLocus_eq`:
  **Remark 0B61**, the moving lemma on `X^{reg}`.

## References

* [Stacks Project, Remark 0B61](https://stacks.math.columbia.edu/tag/0B61)
* [Stacks Project, Tag 0B0E](https://stacks.math.columbia.edu/tag/0B0E)
* [Stacks Project, Tag 0AZP](https://stacks.math.columbia.edu/tag/0AZP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.Chow

universe u

namespace Stacks.Intersection

/-- **Tag 0AZP for a nonempty intersection.** Let `Y` be a nonsingular variety over an
algebraically closed field and let `Z, T ⊆ Y` be closed subvarieties with `Z ∩ T` nonempty. Then
`dim Z + dim T ≤ dim Y + dim (Z ∩ T)`: an irreducible component of `Z ∩ T` has dimension at least
`dim Z + dim T - dim Y`, and it is a subset of `Z ∩ T`. -/
theorem add_topologicalKrullDim_le_add_topologicalKrullDim_inter (k : Type u) [Field k]
    [IsAlgClosed k] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of k)) [IsVariety k p] (hY : IsRegular Y)
    (Z T : IrreducibleCloseds Y) (hZT : ((Z : Set Y) ∩ (T : Set Y)).Nonempty) :
    topologicalKrullDim (Z : Set Y) + topologicalKrullDim (T : Set Y) ≤
      topologicalKrullDim Y + topologicalKrullDim ↥((Z : Set Y) ∩ (T : Set Y)) := by
  set I := Scheme.IdealSheafData.vanishingIdeal (X := Y) ⟨(Z : Set Y), Z.isClosed⟩ with hI
  set J := Scheme.IdealSheafData.vanishingIdeal (X := Y) ⟨(T : Set Y), T.isClosed⟩ with hJ
  have := StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible
    ⟨(Z : Set Y), Z.isClosed⟩ Z.isIrreducible
  have := StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible
    ⟨(T : Set Y), T.isClosed⟩ T.isIrreducible
  have hF : ((I.support : Set Y) ∩ (J.support : Set Y)) = (Z : Set Y) ∩ (T : Set Y) := by
    rw [hI, hJ, Scheme.IdealSheafData.coe_support_vanishingIdeal,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  obtain ⟨z, hz⟩ := hZT
  have hz' : z ∈ ((I.support : Set Y) ∩ (J.support : Set Y)) := hF ▸ hz
  obtain ⟨c, hc, -⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({(⟨z, hz'⟩ : ↥((I.support : Set Y) ∩ (J.support : Set Y)))} : Set _))
    isIrreducible_singleton.closure
  have h0AZP := add_topologicalKrullDim_le_add_topologicalKrullDim_of_irreducibleComponent
    p hY I J c hc
  have eZ : topologicalKrullDim I.subscheme = topologicalKrullDim (Z : Set Y) := by
    rw [hI]; exact topologicalKrullDim_subscheme_vanishingIdeal _
  have eT : topologicalKrullDim J.subscheme = topologicalKrullDim (T : Set Y) := by
    rw [hJ]; exact topologicalKrullDim_subscheme_vanishingIdeal _
  rw [eZ, eT] at h0AZP
  refine h0AZP.trans (add_le_add le_rfl ?_)
  have hsub : topologicalKrullDim ↥c ≤
      topologicalKrullDim ↥((I.support : Set Y) ∩ (J.support : Set Y)) :=
    topologicalKrullDim_subspace_le _ c
  have heq : topologicalKrullDim ↥((I.support : Set Y) ∩ (J.support : Set Y)) =
      topologicalKrullDim ↥((Z : Set Y) ∩ (T : Set Y)) := by
    rw [hF]
  exact hsub.trans heq.le

end Stacks.Intersection

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

/-- In `WithBot ℕ∞`, a natural number can be cancelled from `a + n ≤ n + b`. -/
private theorem le_of_add_natCast_le_natCast_add {a b : WithBot ℕ∞} {n : ℕ}
    (h : a + (n : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) + b) : a ≤ b := by
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe a =>
    induction b using WithBot.recBotCoe with
    | bot =>
      rw [WithBot.add_bot] at h
      rcases WithBot.add_eq_bot.mp (le_bot_iff.mp h) with h1 | h1
      · exact absurd h1 WithBot.coe_ne_bot
      · exact absurd h1 (WithBot.natCast_ne_bot n)
    | coe b =>
      have h' : a + (n : ℕ∞) ≤ (n : ℕ∞) + b := by
        rw [← WithBot.coe_natCast, ← WithBot.coe_add, ← WithBot.coe_add] at h
        exact WithBot.coe_le_coe.mp h
      rw [add_comm (n : ℕ∞) b] at h'
      exact WithBot.coe_le_coe.mpr ((ENat.add_le_add_iff_right (ENat.natCast_ne_top n)).mp h')

/-- **The nonsingular locus of a closed subvariety of `𝐏(V)` is open.** A scheme of finite type
over a field is J-2 (Tag 07PJ, Tag 07R5), so its regular locus is open. -/
public theorem exists_opens_coe_eq_regularLocus (k V : Type u) [Field k] [AddCommGroup V]
    [Module k V] {X : Scheme.{u}}
    (iX : X ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion iX]
    [IsVariety k (iX ≫ projectiveSpaceOfModuleToSpec k V)] :
    ∃ R : X.Opens, (R : Set X) = regularLocus X := by
  set sX : X ⟶ Spec (.of k) := iX ≫ projectiveSpaceOfModuleToSpec k V
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  exact ⟨⟨regularLocus X,
    (Scheme.isJ2_of_locallyOfFiniteType_over_field k sX).isOpen_regularLocus (𝟙 X)⟩, rfl⟩

/-- An open subscheme of `X` contained in the regular locus is regular. -/
private theorem isRegular_toScheme_of_subset_regularLocus {X : Scheme.{u}} [IsLocallyNoetherian X]
    (R : X.Opens) (hR : (R : Set X) ⊆ regularLocus X) : IsRegular R.toScheme :=
  have h : IsLocallyNoetherian R.toScheme ∧
      ∀ y : R.toScheme, IsRegularLocalRing (R.toScheme.presheaf.stalk y) :=
    ⟨inferInstance, fun y => (mem_regularLocus_opens_iff R y).mpr (hR y.2)⟩
  ((isRegular_tfae R.toScheme).out 1 2).mpr h

/-- **Stacks Project, Remark 0B61: the moving lemma on the nonsingular locus.** Let `X ⊆ 𝐏(V)` be
a closed subvariety of dimension `n` of the projective space of a vector space of dimension
`N + 1` over an algebraically closed field, and let `X^{reg} ⊆ X` be the open subset of nonsingular
points (`Xreg`, an open subscheme of `X` whose underlying set is the regular locus; it exists by
`exists_opens_coe_eq_regularLocus`). Let `0 ≤ d, d' < n`, let `Z ⊆ X^{reg}` be a closed subvariety
of dimension `d` and let `T_i ⊆ X^{reg}`, `i ∈ ι`, be finitely many closed subvarieties of
dimension `d'`. Then there is a closed subvariety `C ⊆ 𝐏(V)` whose prime cycle intersects that of
`X` properly, with

`(C · X)|_{X^{reg}} = [Z] + ∑ m_j [Z_j]`

in the Tor-formula intersection product of Section 0B08 (restriction to `X^{reg}` being the
coefficientwise inverse image `Stacks.Chow.cycleComap` along `X^{reg} ⟶ X ⟶ 𝐏(V)`, and `C · X`
being supported on `C ∩ X`), where the `Z_j ⊆ X^{reg}` are irreducible closed of dimension `d`,
distinct from `Z`, with nonzero multiplicities, and, inside `X^{reg}`,

* `dim (Z_j ∩ T_i) ≤ dim (Z ∩ T_i)` whenever `Z ∩ T_i` is nonempty;
* `Z_j` intersects `T_i` properly, `dim (Z_j ∩ T_i) + n ≤ d + d'`, whenever `Z ∩ T_i` is empty;
* `dim (Z_j ∩ T_i) < dim (Z ∩ T_i)` whenever `Z` does not intersect `T_i` properly.

The source states the first clause without the nonemptiness guard. With `dim ∅ = -∞` (Tag 0055)
that would force `Z_j ∩ T_i = ∅` whenever `Z ∩ T_i = ∅`, and this is false: for `X ⊆ 𝐏^3` a
nonsingular quadric surface (so `X^{reg} = X`) and `Z`, `T_1` two distinct lines of one ruling,
every surface `C` meets `T_1` and some component of `C ∩ X` other than `Z` through such a point
occurs in `C · X`; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.KeyLemma` and `errata.md`. In that empty
case the second clause is what holds. The strict clause is vacuous exactly when `Z ∩ T_i` is
empty.

The proof is `exists_intersectProperly_cycleComap_torFormulaCycleIntersectionProduct_eq` on the
open subscheme `X^{reg}`, whose first clause `dim (Z_j ∩ T_i) ≤ dim (Z ∩ T_i) ∨
dim (Z_j ∩ T_i) + n ≤ d + d'` gives the two guarded clauses: the second disjunct gives the first
clause by Tag 0AZP on the nonsingular variety `X^{reg}`, which bounds `d + d' ≤ n + dim (Z ∩ T_i)`
when `Z ∩ T_i` is nonempty, and the first disjunct gives the second clause when `Z ∩ T_i` is
empty, since then `Z_j ∩ T_i` is empty too. -/
@[stacks 0B61 "the version of the moving lemma 0B0E that the remark states, on the open \
subscheme X^reg of nonsingular points of a closed subvariety X ⊆ 𝐏(V) (an open of X whose \
underlying set is the regular locus, which exists by exists_opens_coe_eq_regularLocus); \
(C · X)|_{X^reg} is the coefficientwise inverse image of the cycle C · X along X^reg ⟶ X ⟶ 𝐏(V). \
The inequality dim (Z_j ∩ T_i) ≤ dim (Z ∩ T_i) is proved whenever Z ∩ T_i is nonempty, and when \
Z ∩ T_i is empty Z_j is proved to meet T_i properly: the unguarded inequality is false there \
(dim ∅ = -∞ would force Z_j ∩ T_i = ∅, refuted by two lines of one ruling on a nonsingular quadric \
surface in 𝐏^3, recorded in errata.md). The strict clause is as the source has it. Together with \
the quasi-projective Lemma 0B1U and Theorem 0B1V registered under this tag, this is the whole \
remark"]
public theorem exists_intersectProperly_cycleComap_regularLocus_eq
    (k V : Type u) [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Nontrivial V] [DecidableEq (projectiveSpaceOfModule k V)]
    {N n d d' : ℕ} (hV : Module.finrank k V = N + 1)
    {X : Scheme.{u}} (iX : X ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion iX]
    [IsVariety k (iX ≫ projectiveSpaceOfModuleToSpec k V)]
    (hdimX : topologicalKrullDim X = (n : WithBot ℕ∞)) (hd : d < n) (hd' : d' < n)
    (Xreg : X.Opens) (hXreg : (Xreg : Set X) = regularLocus X) [DecidableEq Xreg.toScheme]
    (Z : IrreducibleCloseds Xreg.toScheme)
    (hZd : topologicalKrullDim (Z : Set Xreg.toScheme) = (d : WithBot ℕ∞))
    {ι : Type*} [Finite ι] (T : ι → IrreducibleCloseds Xreg.toScheme)
    (hTd : ∀ i, topologicalKrullDim (T i : Set Xreg.toScheme) = (d' : WithBot ℕ∞))
    (XC : IrreducibleCloseds (projectiveSpaceOfModule k V))
    (hXC : (XC : Set (projectiveSpaceOfModule k V)) = Set.range iX.base) :
    ∃ (C : IrreducibleCloseds (projectiveSpaceOfModule k V))
      (S : Finset (IrreducibleCloseds Xreg.toScheme)) (m : IrreducibleCloseds Xreg.toScheme → ℤ),
      AlgebraicCycle.IntersectProperly
          (Function.locallyFinsuppWithin.single C.isIrreducible.genericPoint (1 : ℤ))
          (Function.locallyFinsuppWithin.single XC.isIrreducible.genericPoint (1 : ℤ)) ∧
        cycleComap Xreg.ι Xreg.ι.isOpenEmbedding.injective
            (cycleComap iX iX.isClosedEmbedding.injective
              (TorFormula.torFormulaCycleIntersectionProduct (fieldChowSituation k)
                (projectiveSpaceOfModuleToSpec k V) (isRegular_projectiveSpaceOfModule k V)
                (d : ℤ)
                (Function.locallyFinsuppWithin.single C.isIrreducible.genericPoint (1 : ℤ))
                (Function.locallyFinsuppWithin.single XC.isIrreducible.genericPoint (1 : ℤ)))) =
          Function.locallyFinsuppWithin.single Z.isIrreducible.genericPoint (1 : ℤ) +
            ∑ W ∈ S, m W • Function.locallyFinsuppWithin.single
              W.isIrreducible.genericPoint (1 : ℤ) ∧
        (∀ p : projectiveSpaceOfModule k V,
          TorFormula.torFormulaCycleIntersectionProduct (fieldChowSituation k)
              (projectiveSpaceOfModuleToSpec k V) (isRegular_projectiveSpaceOfModule k V) (d : ℤ)
              (Function.locallyFinsuppWithin.single C.isIrreducible.genericPoint (1 : ℤ))
              (Function.locallyFinsuppWithin.single XC.isIrreducible.genericPoint (1 : ℤ)) p ≠
              0 →
            p ∈ (C : Set (projectiveSpaceOfModule k V)) ∩
              (XC : Set (projectiveSpaceOfModule k V))) ∧
        Z ∉ S ∧ (∀ W ∈ S, m W ≠ 0) ∧
        (∀ W ∈ S, topologicalKrullDim (W : Set Xreg.toScheme) = (d : WithBot ℕ∞)) ∧
        (∀ W ∈ S, ∀ i, ((Z : Set Xreg.toScheme) ∩ (T i : Set Xreg.toScheme)).Nonempty →
          topologicalKrullDim ↥((W : Set Xreg.toScheme) ∩ (T i : Set Xreg.toScheme)) ≤
            topologicalKrullDim ↥((Z : Set Xreg.toScheme) ∩ (T i : Set Xreg.toScheme))) ∧
        (∀ W ∈ S, ∀ i, (Z : Set Xreg.toScheme) ∩ (T i : Set Xreg.toScheme) = ∅ →
          topologicalKrullDim ↥((W : Set Xreg.toScheme) ∩ (T i : Set Xreg.toScheme)) +
              (n : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) + (d' : WithBot ℕ∞)) ∧
        (∀ W ∈ S, ∀ i, ¬ AlgebraicGeometry.IntersectProperly Z (T i) →
          topologicalKrullDim ↥((W : Set Xreg.toScheme) ∩ (T i : Set Xreg.toScheme)) <
            topologicalKrullDim ↥((Z : Set Xreg.toScheme) ∩ (T i : Set Xreg.toScheme))) := by
  set sX : X ⟶ Spec (.of k) := iX ≫ projectiveSpaceOfModuleToSpec k V with hsX
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have hreg : IsRegular Xreg.toScheme :=
    isRegular_toScheme_of_subset_regularLocus Xreg hXreg.le
  have hU : Set.range Xreg.ι.base ⊆ regularLocus X := by
    rw [Scheme.Opens.range_ι, hXreg]
  obtain ⟨C, S, m, hCX, hdisp, hsupp, hZS, hm, hWd, hle, hlt⟩ :=
    exists_intersectProperly_cycleComap_torFormulaCycleIntersectionProduct_eq k V hV iX hdimX hd
      Xreg.ι hU Z hZd T (d' := fun _ => d') (fun _ => hd') hTd XC hXC
  refine ⟨C, S, m, hCX, hdisp, hsupp, hZS, hm, hWd, ?_, ?_, hlt⟩
  · intro W hW i hne
    rcases hle W hW i with h | h
    · exact h
    · have : Nonempty Xreg := ⟨hne.some⟩
      have := Stacks.Intersection.RationalEquivalenceProduct.isVariety_opens_ι k sX Xreg
      have hdimU : topologicalKrullDim Xreg.toScheme = (n : WithBot ℕ∞) := by
        rw [← hdimX]
        exact Stacks.Intersection.RationalEquivalenceProduct.topologicalKrullDim_opens k sX Xreg
      have h0AZP := Stacks.Intersection.add_topologicalKrullDim_le_add_topologicalKrullDim_inter k
        (Xreg.ι ≫ sX) hreg Z (T i) hne
      rw [hZd, hTd i, hdimU] at h0AZP
      exact le_of_add_natCast_le_natCast_add (h.trans h0AZP)
  · intro W hW i hempty
    rcases hle W hW i with h | h
    · have hbot : topologicalKrullDim ↥((Z : Set Xreg.toScheme) ∩ (T i : Set Xreg.toScheme)) =
          ⊥ := by
        rw [topologicalKrullDim_eq_bot_iff_isEmpty, hempty]
        exact Set.isEmpty_coe_sort.mpr rfl
      rw [hbot, le_bot_iff] at h
      rw [h, WithBot.bot_add]
      exact bot_le
    · exact h

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
