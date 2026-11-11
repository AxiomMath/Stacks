module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.TwistFormula
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.TwistUnconditional

/-!
# Chern classes of a twist in every degree

`Stacks.WeilCohomology.IsTotalChernClassOnLocallyFree.apply_classOf_tensorObj_invertible` proves
the formula of Tag 0FI8,
`c^A_i(ℰ ⊗ ℒ) = ∑_{j=0}^{i} binom(r - i + j, j) c^A_{i-j}(ℰ) ∪ c₁^A(ℒ)^j`, for every rule with
the three properties of Tag 0FI5 and `i ≤ r`, the binomial coefficient written
`(r - i + j).choose j`. This file proves it in **every** degree `i`, with the binomial coefficient
written `(r + j - i).choose j`. The two spellings agree for `i ≤ r`. For `i > r` both sides
vanish: the Chern classes of a module of constant rank `r` vanish above `r`, and a term with
`i - j ≤ r` has `r + j - i < j`.

## Main results

* `Stacks.WeilCohomology.IsTotalChernClassOnLocallyFree.apply_classOf_of_lt`: the Chern classes
  of a module of constant rank `r` vanish in degrees above `r`.
* `Stacks.WeilCohomology.IsTotalChernClassOnLocallyFree.apply_classOf_tensorObj_invertible_of_any`:
  the formula of Tag 0FI8 in every degree.

## References

* [Stacks Project, Tag 0FI8](https://stacks.math.columbia.edu/tag/0FI8)
* [Stacks Project, Tag 0FI5](https://stacks.math.columbia.edu/tag/0FI5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v v₁ w

namespace Stacks.WeilCohomology

namespace IsTotalChernClassOnLocallyFree

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}} {𝔄 : ChernSetup.{u, v, v₁, w} C S}
  {c : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔄.A X}

/-- **The Chern classes of a module of constant rank `r` vanish above `r`.** By the splitting
principle, Tag 0FI7, after an injective pullback the class of `ℰ` is a sum of `r` classes of
invertible modules, whose total Chern class has as components the elementary symmetric functions
of `r` first Chern classes. -/
theorem apply_classOf_of_lt (hc : IsTotalChernClassOnLocallyFree 𝔄 c) (X : C)
    (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r) {n : ℕ}
    (hn : r < n) : c X (VectorBundleKZero.classOf (S.obj X) E) n = 0 := by
  classical
  obtain ⟨P, p, -, hinj, hfil⟩ :=
    𝔄.exists_injective_hasInvertibleFiltration X Unit (fun _ => E) (fun _ => r) fun _ => hE
  obtain ⟨-, Lk, hLk, hsum⟩ := (hfil ()).exists_classOf_eq_sum
  let x : Fin r → Subring.center (𝔄.A P) := fun k =>
    ⟨𝔄.c₁ P (picardClassOf (S.obj P) (Lk k) (hLk k)),
      Subring.mem_center_iff.mpr fun b => (𝔄.c₁_central P _ b).symm⟩
  refine hinj ?_
  rw [hc.map_pull p E hE.isFiniteLocallyFree n, hsum,
    hc.apply_sum_classOf_invertible P Lk hLk x (fun k => rfl) Finset.univ n,
    Multiset.esymm_of_card_lt (by simpa using hn), _root_.map_zero]
  rfl

/-- **The formula of Tag 0FI8 in every degree.** For a rule `c^A` with the three properties of
Tag 0FI5, `ℰ` finite locally free of constant rank `r` and `ℒ` invertible, for every `i`,
`c^A_i(ℰ ⊗ ℒ) = ∑_{j=0}^{i} binom(r - i + j, j) c^A_{i-j}(ℰ) ∪ c₁^A(ℒ)^j`, the binomial
coefficient written `(r + j - i).choose j`; it agrees with `binom(r - i + j, j)` whenever
`r - i + j ≥ 0`, and otherwise `i - j > r` and the factor `c^A_{i-j}(ℰ)` vanishes. -/
theorem apply_classOf_tensorObj_invertible_of_any (hc : IsTotalChernClassOnLocallyFree 𝔄 c)
    (X : C) (E L : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 L) (i : ℕ) :
    c X (VectorBundleKZero.classOf (S.obj X)
        (Scheme.Modules.tensorObjRingedSpace (S.obj X) E L)) i =
      ∑ j ∈ Finset.range (i + 1), (r + j - i).choose j •
        (c X (VectorBundleKZero.classOf (S.obj X) E) (i - j) *
          𝔄.c₁ X (picardClassOf (S.obj X) L hL) ^ j) := by
  rcases le_or_gt i r with hi | hi
  · rw [hc.apply_classOf_tensorObj_invertible X E L r hE hL i hi]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [show r - i + j = r + j - i by omega]
  · rw [hc.apply_classOf_of_lt X _ r
      (isFiniteLocallyFreeOfRank_tensorObjRingedSpace_of_isInvertible E L r hE hL) hi]
    refine (Finset.sum_eq_zero fun j hj => ?_).symm
    have hj' : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rcases lt_or_ge r (i - j) with h | h
    · rw [hc.apply_classOf_of_lt X E r hE h, zero_mul, smul_zero]
    · rw [Nat.choose_eq_zero_of_lt (by omega), zero_smul]

end IsTotalChernClassOnLocallyFree

end Stacks.WeilCohomology

end
