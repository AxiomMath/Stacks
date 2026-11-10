module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.ChernPolynomial
public import StacksFrontier.AlgebraicGeometry.Chow.SectionZeroScheme.ArbitraryRankDual
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.TensorChernClassesBivariant
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFiniteFreeSummand.OnSpace
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFiniteFreeSummand.TensorDualEndomorphism
public import Mathlib.Tactic.NoncommRing
public import StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.WhitneyChowCohomology

/-!
# The Chern class relations for modules of nonconstant rank

Let `(S, δ)` be as in Situation 02QL and let `X` be locally of finite type over `S`.
[Stacks, Tag 0FA7] observes that the equalities of Stacks 0FA5 and 0FA6 remain true for finite
locally free `𝒪_X`-modules whose rank is allowed to be nonconstant, the integer ranks being
replaced by the rank classes `r(ℰ) ∈ A^0(X)` of Stacks 0ESW, and gives as an example

  `c₂(𝓗om(ℰ, ℰ)) = P(ℰ)`,  `P = 2 r c₂ - (r - 1) c₁²`,

obtained from `𝓗om(ℰ, ℰ) = ℰ ⊗ ℰ^∨`, Stacks 0FA5 and Stacks 0FA6 by decomposing `X` into the parts
where the rank of `ℰ` is constant.

## Main definitions

* `Stacks.Chow.rankChooseTwoClass` — the class `(r(ℰ) choose 2) ∈ A^0(X)`.
* `Stacks.Chow.chernClassOfLocallyFreeChowCohomology`, `Stacks.Chow.rankChowCohomology`,
  `Stacks.Chow.rankChooseTwoChowCohomology` — `c_i(ℰ)`, `r(ℰ)` and `(r(ℰ) choose 2)` in the Chow
  cohomology ring `A^*(X)` of Stacks 0B7E.

## Main results

* `Stacks.Chow.chernClassOfLocallyFree_tensorObj_one_chowCohomology`,
  `Stacks.Chow.chernClassOfLocallyFree_tensorObj_two_chowCohomology` — **Stacks 0FA6 in
  nonconstant rank**, in `A^*(X)`: `c₁(ℰ ⊗ ℱ) = r(ℰ) c₁(ℱ) + r(ℱ) c₁(ℰ)` and
  `c₂(ℰ ⊗ ℱ) = r(ℰ) c₂(ℱ) + r(ℱ) c₂(ℰ) + (r(ℰ) choose 2) c₁(ℱ)² + (r(ℰ) r(ℱ) - 1) c₁(ℱ) c₁(ℰ)
  + (r(ℱ) choose 2) c₁(ℰ)²`; the same identities in the ring of total classes are
  `Stacks.Chow.homComponent_one_totalChernClassOfModule_tensorObj` and
  `Stacks.Chow.homComponent_two_totalChernClassOfModule_tensorObj`.
* `Stacks.Chow.homComponent_totalChernClassOfModule_dualSheaf` — **Stacks 0FA5 in nonconstant
  rank**, `c_i(ℰ^∨) = (-1)^i c_i(ℰ)`, read in the ring of total classes from
  `Stacks.Chow.SectionZeroScheme.chernClassOfLocallyFree_dualSheaf`.
* `Stacks.Chow.chernClassOfLocallyFree_sheafHom` — **the example of Stacks 0FA7**:
  `c₂(𝓗om(ℰ, ℰ)) = P(ℰ)` in `A^2(X)` for `P = 2 r c₂ - (r - 1) c₁²`.

## Implementation notes

The binomial coefficient `(r choose 2)` of Stacks 0FA6 is not a polynomial in `r` with integer
coefficients, so in nonconstant rank it is read as the degree-zero class
`Stacks.Chow.rankChooseTwoClass` which is `(r choose 2)` on the piece where the rank is `r`;
twice it is `r(ℰ) (r(ℰ) - 1)` (`Stacks.Chow.two_smul_rankChooseTwoClass`).

## References

* [Stacks Project, Tag 0FA7](https://stacks.math.columbia.edu/tag/0FA7)
* [Stacks Project, Tag 0FA5](https://stacks.math.columbia.edu/tag/0FA5)
* [Stacks Project, Tag 0FA6](https://stacks.math.columbia.edu/tag/0FA6)
* [Stacks Project, Tag 0ESW](https://stacks.math.columbia.edu/tag/0ESW)
* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf isFiniteLocallyFree_dualSheaf)

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

attribute [local instance] isFiniteLocallyFreeOfRank_tensorObj_mul

/-! ### The binomial coefficient of the rank -/

section Binomial

variable (E : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- **The class `(r(ℰ) choose 2) ∈ A^0(X)`**: `(r choose 2)` times `1` on the piece where `ℰ` has
rank `r`. -/
def rankChooseTwoClass : TotalChowClass C sX :=
  rankFunctionClass C sX E fun r ↦ (r.choose 2 : ℤ)

/-- The classes of functions of the rank subtract as the functions do. -/
theorem rankFunctionClass_sub (f g : ℕ → ℤ) :
    rankFunctionClass C sX E (f - g) = rankFunctionClass C sX E f - rankFunctionClass C sX E g := by
  rw [sub_eq_add_neg, rankFunctionClass_add, eq_sub_iff_add_eq, add_assoc,
    ← rankFunctionClass_add, neg_add_cancel, Pi.zero_def, rankFunctionClass_const, Int.cast_zero,
    add_zero]

/-- **Twice `(r(ℰ) choose 2)` is `r(ℰ) (r(ℰ) - 1)`.** -/
theorem two_smul_rankChooseTwoClass :
    rankChooseTwoClass C sX E + rankChooseTwoClass C sX E =
      rankTotalClass C sX E * rankTotalClass C sX E - rankTotalClass C sX E := by
  rw [rankChooseTwoClass, rankTotalClass, ← rankFunctionClass_add, ← rankFunctionClass_mul,
    ← rankFunctionClass_sub]
  refine rankFunctionClass_congr C sX E fun r ↦ ?_
  have h : ((r.choose 2 : ℕ) : ℚ) + (r.choose 2 : ℕ) = (r : ℚ) * r - r := by
    rw [Nat.cast_choose_two]
    ring
  simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
  exact_mod_cast h

end Binomial

/-! ### Stacks 0FA6 in nonconstant rank -/

section Tensor

variable (E F : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F]

/-- Along a morphism over which `ℰ` and `ℱ` have constant ranks `a` and `b`, the total Chern class
of `ℰ ⊗ ℱ` restricts to that of the module `h^*ℰ ⊗ h^*ℱ` of rank `a b`. -/
theorem res_totalChernClassOfModule_tensorObj_of_rank {Y' : Scheme.{u}} {sY' : Y' ⟶ C.S}
    [LocallyOfFiniteType sY'] (h : Y' ⟶ X) [LocallyOfFiniteType h] (hs : h ≫ sX = sY') (a b : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback h).obj E) a]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback h).obj F) b] :
    TotalChowClass.res h hs (totalChernClassOfModule C sX (Scheme.Modules.tensorObj E F)) =
      totalChern C sY' (Scheme.Modules.tensorObj ((Scheme.Modules.pullback h).obj E)
        ((Scheme.Modules.pullback h).obj F)) (a * b) := by
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback h).obj (Scheme.Modules.tensorObj E F)) (a * b) :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      (pullbackTensorObjIso h E F).symm inferInstance
  rw [res_totalChernClassOfModule_of_rank C sX _ h hs (a * b)]
  exact totalChern_congr C sY' (pullbackTensorObjIso h E F) rfl

/-- **Stacks 0FA6, the first identity, in nonconstant rank** (Stacks 0FA7). For `ℰ`, `ℱ` finite
locally free on `X`, of ranks not necessarily constant,

  `c₁(ℰ ⊗ ℱ) = r(ℰ) c₁(ℱ) + r(ℱ) c₁(ℰ)`

in the ring of total classes, at the rank classes and Chern classes of Stacks 0ESW. On the pieces
where both ranks are constant this is Stacks 0FA6. -/
theorem homComponent_one_totalChernClassOfModule_tensorObj :
    TotalChowClass.homComponent 1 (totalChernClassOfModule C sX (Scheme.Modules.tensorObj E F)) =
      rankTotalClass C sX E * TotalChowClass.homComponent 1 (totalChernClassOfModule C sX F) +
        rankTotalClass C sX F * TotalChowClass.homComponent 1 (totalChernClassOfModule C sX E) := by
  refine TotalChowClass.eq_of_res_eq_of_rank E F fun V a b ha hb ↦ ?_
  have := ha
  have := hb
  simp only [map_add, map_mul, TotalChowClass.res_homComponent]
  rw [res_totalChernClassOfModule_tensorObj_of_rank C sX E F V.ι rfl a b,
    res_totalChernClassOfModule_of_rank C sX E V.ι rfl a,
    res_totalChernClassOfModule_of_rank C sX F V.ι rfl b, rankTotalClass, rankTotalClass,
    res_rankFunctionClass_of_rank C sX E V.ι rfl a, res_rankFunctionClass_of_rank C sX F V.ι rfl b,
    totalChern_tensorObj_homComponent_one]
  simp only [zsmul_eq_mul, nsmul_eq_mul, mul_one, Int.cast_natCast]

/-- **Stacks 0FA6, the second identity, in nonconstant rank** (Stacks 0FA7). For `ℰ`, `ℱ` finite
locally free on `X`, of ranks not necessarily constant,

  `c₂(ℰ ⊗ ℱ) = r(ℰ) c₂(ℱ) + r(ℱ) c₂(ℰ) + (r(ℰ) choose 2) c₁(ℱ)² + (r(ℰ) r(ℱ) - 1) c₁(ℱ) c₁(ℰ)
    + (r(ℱ) choose 2) c₁(ℰ)²`

in the ring of total classes, at the rank classes and Chern classes of Stacks 0ESW, where
`(r(ℰ) choose 2)` is `Stacks.Chow.rankChooseTwoClass`. On the pieces where both ranks are
constant this is Stacks 0FA6. -/
theorem homComponent_two_totalChernClassOfModule_tensorObj :
    TotalChowClass.homComponent 2 (totalChernClassOfModule C sX (Scheme.Modules.tensorObj E F)) =
      rankTotalClass C sX E * TotalChowClass.homComponent 2 (totalChernClassOfModule C sX F) +
        rankTotalClass C sX F * TotalChowClass.homComponent 2 (totalChernClassOfModule C sX E) +
        rankChooseTwoClass C sX E *
          TotalChowClass.homComponent 1 (totalChernClassOfModule C sX F) ^ 2 +
        (rankTotalClass C sX E * rankTotalClass C sX F - 1) *
          (TotalChowClass.homComponent 1 (totalChernClassOfModule C sX F) *
            TotalChowClass.homComponent 1 (totalChernClassOfModule C sX E)) +
        rankChooseTwoClass C sX F *
          TotalChowClass.homComponent 1 (totalChernClassOfModule C sX E) ^ 2 := by
  refine TotalChowClass.eq_of_res_eq_of_rank E F fun V a b ha hb ↦ ?_
  have := ha
  have := hb
  simp only [map_add, map_mul, map_sub, map_one, map_pow, TotalChowClass.res_homComponent]
  rw [res_totalChernClassOfModule_tensorObj_of_rank C sX E F V.ι rfl a b,
    res_totalChernClassOfModule_of_rank C sX E V.ι rfl a,
    res_totalChernClassOfModule_of_rank C sX F V.ι rfl b, rankTotalClass, rankTotalClass,
    rankChooseTwoClass, rankChooseTwoClass]
  simp only [res_rankFunctionClass_of_rank C sX E V.ι rfl a,
    res_rankFunctionClass_of_rank C sX F V.ι rfl b, totalChern_tensorObj_homComponent_two]
  simp only [zsmul_eq_mul, nsmul_eq_mul, mul_one, Int.cast_natCast, Int.cast_sub, Int.cast_mul,
    Int.cast_one, pow_two]

end Tensor

/-! ### Isomorphism invariance -/

section Congr

/-- **The total Chern class of Stacks 0ESW depends only on the isomorphism class of the module.**
On the piece where `ℱ` has rank `r` so does `ℱ'`, and there both are the total Chern class of
isomorphic modules of rank `r`. -/
theorem totalChernClassOfModule_congr {F F' : X.Modules}
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F'] (e : F ≅ F') :
    totalChernClassOfModule C sX F = totalChernClassOfModule C sX F' := by
  refine TotalChowClass.eq_of_res_eq (isClopenDecomposition_rankLociFamily F) fun ρ ↦ ?_
  have := isFiniteLocallyFreeOfRank_pullback_rankLociFamily F ρ
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (rankLociFamily F ρ).ι).obj F') ρ.down :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      ((Scheme.Modules.pullback (rankLociFamily F ρ).ι).mapIso e) inferInstance
  rw [res_totalChernClassOfModule_of_rank C sX F _ rfl ρ.down,
    res_totalChernClassOfModule_of_rank C sX F' _ rfl ρ.down]
  exact totalChern_congr C _ ((Scheme.Modules.pullback (rankLociFamily F ρ).ι).mapIso e) rfl

end Congr

/-! ### Stacks 0FA5 in the ring of total classes -/

section Dual

variable (E : X.Modules) [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- **A module and its dual have the same functions of the rank**, their rank loci being equal. -/
theorem rankFunctionClass_dualSheaf (f : ℕ → ℤ) :
    haveI := isFiniteLocallyFree_dualSheaf E hE
    rankFunctionClass C sX (dualSheaf E) f = rankFunctionClass C sX E f := by
  have := isFiniteLocallyFree_dualSheaf E hE
  refine TotalChowClass.eq_of_res_eq (isClopenDecomposition_rankLociFamily E) fun ρ ↦ ?_
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (rankLociFamily E ρ).ι).obj (dualSheaf E)) ρ.down :=
    SectionZeroScheme.isFiniteLocallyFreeOfRank_pullback_rankLocus_dualSheaf E ρ.down
  have := isFiniteLocallyFreeOfRank_pullback_rankLociFamily E ρ
  rw [res_rankFunctionClass_of_rank C sX (dualSheaf E) _ rfl ρ.down,
    res_rankFunctionClass_of_rank C sX E _ rfl ρ.down]

/-- **Stacks 0FA5 in nonconstant rank, in the ring of total classes**: `c_i(ℰ^∨) = (-1)^i c_i(ℰ)`
for the Chern classes of Stacks 0ESW. This is
`Stacks.Chow.SectionZeroScheme.chernClassOfLocallyFree_dualSheaf`. -/
@[stacks 0FA7 "the identity of Tag 0FA5 for modules of nonconstant rank: c_i(E^dual) = \
(-1)^i c_i(E), at the Chern classes of Tag 0ESW, read in the ring of total classes; the same \
identity in A^i(X) is Stacks.Chow.SectionZeroScheme.chernClassOfLocallyFree_dualSheaf"]
theorem homComponent_totalChernClassOfModule_dualSheaf (i : ℕ) :
    haveI := isFiniteLocallyFree_dualSheaf E hE
    TotalChowClass.homComponent i (totalChernClassOfModule C sX (dualSheaf E)) =
      ((-1 : ℤ) ^ i) • TotalChowClass.homComponent i (totalChernClassOfModule C sX E) := by
  have := isFiniteLocallyFree_dualSheaf E hE
  refine TotalChowClass.ext fun p ↦ ?_
  change _ = ((-1 : ℤ) ^ i) • TotalChowClass.homComponent i (totalChernClassOfModule C sX E) p
  rw [TotalChowClass.homComponent_apply, TotalChowClass.homComponent_apply]
  split_ifs with hp
  · subst hp
    rw [totalChernClassOfModule_apply_eq_chernClassOfLocallyFree,
      totalChernClassOfModule_apply_eq_chernClassOfLocallyFree,
      SectionZeroScheme.chernClassOfLocallyFree_dualSheaf]
  · rw [smul_zero]

end Dual

/-! ### The example: the second Chern class of the endomorphism sheaf -/

section Endomorphism

variable (E : X.Modules) [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- **`ℰ ⊗ ℰ^∨ ≅ 𝓗om(ℰ, ℰ)`** for a finite locally free module (Stacks 0FNV): the canonical map
sending `f ⊗ λ` to `g ↦ λ(g) f` is an isomorphism. -/
def tensorObjDualSheafIsoSheafHom :
    Scheme.Modules.tensorObj E (dualSheaf E) ≅
      Stacks.SheafOfModules.OnSpace.sheafHom X.toRingedSpace E E :=
  haveI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := structureSheafRing X.toRingedSpace) E := hE
  @asIso _ _ _ _ (Stacks.SheafOfModules.OnSpace.tensorDualToEndomorphism X.toRingedSpace E)
    (Stacks.SheafOfModules.OnSpace.tensorDualToEndomorphism_isIso X.toRingedSpace E
      (Stacks.SheafOfModules.OnSpace.isLocallyFiniteFreeSummand_of_isFiniteLocallyFree
        X.toRingedSpace E))

/-- `𝓗om(ℰ, ℰ)` is finite locally free. -/
theorem isFiniteLocallyFree_sheafHom :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (Stacks.SheafOfModules.OnSpace.sheafHom X.toRingedSpace E E) :=
  have := isFiniteLocallyFree_dualSheaf E hE
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso (tensorObjDualSheafIsoSheafHom E)

/-- The polynomial `P = 2 r c₂ - (r - 1) c₁²` of Stacks 0FA7, homogeneous of degree `2`. -/
def sheafEndChernPolynomial : ChernPolynomial.homogeneousSubmodule 2 :=
  ⟨2 * MvPolynomial.X none * MvPolynomial.X (some 2) -
      (MvPolynomial.X none - 1) * MvPolynomial.X (some 1) ^ 2, by
    have hr := MvPolynomial.isWeightedHomogeneous_X ℤ chernPolynomialWeight none
    have h1 := MvPolynomial.isWeightedHomogeneous_X ℤ chernPolynomialWeight (some 1)
    have h2 := MvPolynomial.isWeightedHomogeneous_X ℤ chernPolynomialWeight (some 2)
    have hc : MvPolynomial.IsWeightedHomogeneous chernPolynomialWeight
        (2 : ChernPolynomial) 0 := by
      rw [show (2 : ChernPolynomial) = MvPolynomial.C 2 from (map_ofNat _ 2).symm]
      exact MvPolynomial.isWeightedHomogeneous_C chernPolynomialWeight 2
    have hone : MvPolynomial.IsWeightedHomogeneous chernPolynomialWeight
        (1 : ChernPolynomial) 0 := MvPolynomial.isWeightedHomogeneous_one ℤ chernPolynomialWeight
    refine Submodule.sub_mem _ ?_ ?_
    · exact (hc.mul hr).mul h2
    · rw [pow_two]
      exact (Submodule.sub_mem (MvPolynomial.weightedHomogeneousSubmodule ℤ
        chernPolynomialWeight 0) hr hone :
          MvPolynomial.IsWeightedHomogeneous chernPolynomialWeight _ 0).mul (h1.mul h1)⟩

/-- **The example of Stacks 0FA7 in the ring of total classes**: `c₂(𝓗om(ℰ, ℰ)) = P(ℰ)` for
`P = 2 r c₂ - (r - 1) c₁²`. -/
theorem homComponent_two_totalChernClassOfModule_sheafHom :
    haveI := isFiniteLocallyFree_sheafHom E
    TotalChowClass.homComponent 2 (totalChernClassOfModule C sX
        (Stacks.SheafOfModules.OnSpace.sheafHom X.toRingedSpace E E)) =
      chernPolynomialClass C sX E (sheafEndChernPolynomial : ChernPolynomial) := by
  have := isFiniteLocallyFree_sheafHom E
  have := isFiniteLocallyFree_dualSheaf E hE
  rw [← totalChernClassOfModule_congr C sX (tensorObjDualSheafIsoSheafHom E),
    homComponent_two_totalChernClassOfModule_tensorObj,
    homComponent_totalChernClassOfModule_dualSheaf, homComponent_totalChernClassOfModule_dualSheaf,
    rankTotalClass, rankTotalClass, rankChooseTwoClass, rankChooseTwoClass,
    rankFunctionClass_dualSheaf, rankFunctionClass_dualSheaf]
  have hC := two_smul_rankChooseTwoClass C sX E
  rw [rankChooseTwoClass, rankTotalClass] at hC
  simp only [sheafEndChernPolynomial, map_sub, map_mul, map_pow, map_ofNat, map_one,
    chernPolynomialClass_X_none, chernPolynomialClass_X_some, rankTotalClass, PNat.val_ofNat]
  set r := rankFunctionClass C sX E fun r ↦ (r : ℤ)
  set B := rankFunctionClass C sX E fun r ↦ (r.choose 2 : ℤ)
  set c₁ := TotalChowClass.homComponent 1 (totalChernClassOfModule C sX E)
  set c₂ := TotalChowClass.homComponent 2 (totalChernClassOfModule C sX E)
  calc r * ((-1 : ℤ) ^ 2 • c₂) + r * c₂ + B * ((-1 : ℤ) ^ 1 • c₁) ^ 2 +
        (r * r - 1) * (((-1 : ℤ) ^ 1 • c₁) * c₁) + B * c₁ ^ 2
      = 2 * r * c₂ + (B * c₁ ^ 2 + B * c₁ ^ 2) - (r * r - 1) * (c₁ * c₁) := by
        simp only [pow_one, pow_two, neg_neg, one_smul, neg_smul,
          Int.reduceNeg, neg_mul, mul_neg]
        noncomm_ring
    _ = 2 * r * c₂ - (r - 1) * c₁ ^ 2 := by
        rw [← add_mul, hC]
        noncomm_ring

/-- **The example of Stacks 0FA7**: for `ℰ` finite locally free on `X`, of rank not necessarily
constant,

  `c₂(𝓗om(ℰ, ℰ)) = P(ℰ)`,  `P = 2 r c₂ - (r - 1) c₁²`,

in `A^2(X)`, where `c₂` is the Chern class of Stacks 0ESW and `P(ℰ)` the class of Stacks 0FA7.
The proof is the source's: `𝓗om(ℰ, ℰ) ≅ ℰ ⊗ ℰ^∨` (Stacks 0FNV), and Stacks 0FA5 and 0FA6 on the
parts of `X` where the rank of `ℰ` is constant. -/
@[stacks 0FA7 "the example c_2(SheafHom(E, E)) = P(E) with P = 2 r c_2 - (r - 1) c_1^2, in A^2(X), \
for E finite locally free of rank not necessarily constant, at the Chern classes of Tag 0ESW"]
theorem chernClassOfLocallyFree_sheafHom :
    haveI := isFiniteLocallyFree_sheafHom E
    SectionZeroScheme.chernClassOfLocallyFree
        (Stacks.SheafOfModules.OnSpace.sheafHom X.toRingedSpace E E) C sX 2 =
      chernPolynomialComponent C sX E 2 sheafEndChernPolynomial := by
  have := isFiniteLocallyFree_sheafHom E
  have h := congrArg (fun c : TotalChowClass C sX ↦ c 2)
    (homComponent_two_totalChernClassOfModule_sheafHom C sX E)
  rw [TotalChowClass.homComponent_apply, ite_eq_left rfl] at h
  exact (totalChernClassOfModule_apply_eq_chernClassOfLocallyFree C sX _ 2).symm.trans h

end Endomorphism

/-! ### Stacks 0FA6 in nonconstant rank, in the Chow cohomology ring `A^*(X)` -/

section ChowCohomology

namespace TotalChowClass

variable {C sX}

/-- The truncation below `N` of a class homogeneous of degree `i < N` is its degree-`i` component,
placed in `A^*(X)`. -/
theorem toChowCohomology_of_isHomogeneous {i N : ℕ} (hi : i < N) {c : TotalChowClass C sX}
    (hc : c.IsHomogeneous i) : toChowCohomology C sX N c = DirectSum.of _ (i : ℤ) (c i) := by
  have h := toChowCohomology_homComponent C sX hi c
  rwa [isHomogeneous_iff_homComponent_eq.mp hc] at h

/-- The truncation of a product of homogeneous classes of degrees `i` and `j` is the product in
`A^*(X)` of their components. -/
theorem toChowCohomology_mul_of_isHomogeneous {i j : ℕ} {c d : TotalChowClass C sX}
    (hc : c.IsHomogeneous i) (hd : d.IsHomogeneous j) :
    letI := chowCohomologyRingOfInvertible C sX
    toChowCohomology C sX (i + j + 1) (c * d) =
      DirectSum.of _ (i : ℤ) (c i) * DirectSum.of _ (j : ℤ) (d j) := by
  let := chowCohomologyRingOfInvertible C sX
  rw [toChowCohomology_mul c d i j (fun k hk ↦ hc k (by omega)) (fun k hk ↦ hd k (by omega)),
    toChowCohomology_of_isHomogeneous (Nat.lt_succ_self i) hc,
    toChowCohomology_of_isHomogeneous (Nat.lt_succ_self j) hd]

/-- The truncation of `1` is the unit of `A^*(X)`. -/
theorem toChowCohomology_one :
    letI := chowCohomologyRingOfInvertible C sX
    toChowCohomology C sX 1 (1 : TotalChowClass C sX) = 1 := by
  rw [toChowCohomology, Finset.sum_range_one, one_apply_zero, of_bivariantClassDegreeCongr]
  rfl

end TotalChowClass

variable (E F : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F]

/-- The Chern class `c_i(ℰ) ∈ A^i(X) ⊆ A^*(X)` of Stacks 0ESW, for `ℰ` of rank not necessarily
constant. -/
def chernClassOfLocallyFreeChowCohomology (i : ℕ) :
    chowCohomology C (gysinSystemOfInvertible C) sX :=
  DirectSum.of _ (i : ℤ) (SectionZeroScheme.chernClassOfLocallyFree E C sX i)

/-- The rank `r(ℰ) ∈ A^0(X) ⊆ A^*(X)` of Stacks 0ESW. -/
def rankChowCohomology : chowCohomology C (gysinSystemOfInvertible C) sX :=
  DirectSum.of _ ((0 : ℕ) : ℤ) (rankTotalClass C sX E 0)

/-- The class `(r(ℰ) choose 2) ∈ A^0(X) ⊆ A^*(X)`. -/
def rankChooseTwoChowCohomology : chowCohomology C (gysinSystemOfInvertible C) sX :=
  DirectSum.of _ ((0 : ℕ) : ℤ) (rankChooseTwoClass C sX E 0)

/-- The degree-`i` Chern class, truncated, is `c_i(ℰ) ∈ A^*(X)`. -/
theorem toChowCohomology_homComponent_totalChernClassOfModule {i N : ℕ} (hi : i < N) :
    TotalChowClass.toChowCohomology C sX N
        (TotalChowClass.homComponent i (totalChernClassOfModule C sX E)) =
      chernClassOfLocallyFreeChowCohomology C sX E i := by
  rw [TotalChowClass.toChowCohomology_homComponent C sX hi,
    totalChernClassOfModule_apply_eq_chernClassOfLocallyFree, chernClassOfLocallyFreeChowCohomology]

/-- The product of a degree-zero class of the rank with a Chern class, truncated. -/
theorem toChowCohomology_rankFunctionClass_mul (f : ℕ → ℤ) {i : ℕ} {c : TotalChowClass C sX}
    (hc : c.IsHomogeneous i) :
    letI := chowCohomologyRingOfInvertible C sX
    TotalChowClass.toChowCohomology C sX (i + 1) (rankFunctionClass C sX E f * c) =
      DirectSum.of _ ((0 : ℕ) : ℤ) (rankFunctionClass C sX E f 0) *
        DirectSum.of _ (i : ℤ) (c i) := by
  have h := TotalChowClass.toChowCohomology_mul_of_isHomogeneous
    (isHomogeneous_rankFunctionClass C sX E f) hc
  rwa [Nat.zero_add] at h

/-- **Stacks 0FA6, the first identity, in nonconstant rank, in `A^*(X)`** (Stacks 0FA7). For `ℰ`,
`ℱ` finite locally free on `X`, of ranks not necessarily constant,

  `c₁(ℰ ⊗ ℱ) = r(ℰ) c₁(ℱ) + r(ℱ) c₁(ℰ)`

in the Chow cohomology ring `A^*(X)` of Stacks 0B7E, at the rank classes and Chern classes of
Stacks 0ESW. -/
@[stacks 0FA7 "the first identity of Tag 0FA6 for modules of nonconstant rank, in the Chow \
cohomology ring A^*(X): c_1(E tensor F) = r(E) c_1(F) + r(F) c_1(E), at the rank and Chern classes \
of Tag 0ESW"]
theorem chernClassOfLocallyFree_tensorObj_one_chowCohomology :
    letI := chowCohomologyRingOfInvertible C sX
    chernClassOfLocallyFreeChowCohomology C sX (Scheme.Modules.tensorObj E F) 1 =
      rankChowCohomology C sX E * chernClassOfLocallyFreeChowCohomology C sX F 1 +
        rankChowCohomology C sX F * chernClassOfLocallyFreeChowCohomology C sX E 1 := by
  let := chowCohomologyRingOfInvertible C sX
  have h := congrArg (TotalChowClass.toChowCohomologyHom C sX 2)
    (homComponent_one_totalChernClassOfModule_tensorObj C sX E F)
  rw [map_add] at h
  simp only [TotalChowClass.toChowCohomologyHom_apply, rankTotalClass] at h
  rw [toChowCohomology_homComponent_totalChernClassOfModule C sX _ (by omega),
    toChowCohomology_rankFunctionClass_mul C sX E _ (TotalChowClass.isHomogeneous_homComponent _ _),
    toChowCohomology_rankFunctionClass_mul C sX F _ (TotalChowClass.isHomogeneous_homComponent _ _)]
    at h
  rw [h]
  simp only [rankChowCohomology, rankTotalClass, chernClassOfLocallyFreeChowCohomology,
    TotalChowClass.homComponent_apply, ↓reduceIte,
    totalChernClassOfModule_apply_eq_chernClassOfLocallyFree]

/-- **Stacks 0FA6, the second identity, in nonconstant rank, in `A^*(X)`** (Stacks 0FA7). For `ℰ`,
`ℱ` finite locally free on `X`, of ranks not necessarily constant,

  `c₂(ℰ ⊗ ℱ) = r(ℰ) c₂(ℱ) + r(ℱ) c₂(ℰ) + (r(ℰ) choose 2) c₁(ℱ)² + (r(ℰ) r(ℱ) - 1) c₁(ℱ) c₁(ℰ)
    + (r(ℱ) choose 2) c₁(ℰ)²`

in the Chow cohomology ring `A^*(X)` of Stacks 0B7E, at the rank classes and Chern classes of
Stacks 0ESW, `(r(ℰ) choose 2)` being the class which is `(r choose 2)` where the rank is `r`. -/
@[stacks 0FA7 "the second identity of Tag 0FA6 for modules of nonconstant rank, in the Chow \
cohomology ring A^*(X): c_2(E tensor F) = r(E) c_2(F) + r(F) c_2(E) + binom(r(E),2) c_1(F)^2 + \
(r(E) r(F) - 1) c_1(F) c_1(E) + binom(r(F),2) c_1(E)^2, at the rank and Chern classes of Tag 0ESW, \
binom(r(E),2) being the class which is binom(r,2) where the rank is r"]
theorem chernClassOfLocallyFree_tensorObj_two_chowCohomology :
    letI := chowCohomologyRingOfInvertible C sX
    chernClassOfLocallyFreeChowCohomology C sX (Scheme.Modules.tensorObj E F) 2 =
      rankChowCohomology C sX E * chernClassOfLocallyFreeChowCohomology C sX F 2 +
        rankChowCohomology C sX F * chernClassOfLocallyFreeChowCohomology C sX E 2 +
        rankChooseTwoChowCohomology C sX E * chernClassOfLocallyFreeChowCohomology C sX F 1 ^ 2 +
        (rankChowCohomology C sX E * rankChowCohomology C sX F - 1) *
          (chernClassOfLocallyFreeChowCohomology C sX F 1 *
            chernClassOfLocallyFreeChowCohomology C sX E 1) +
        rankChooseTwoChowCohomology C sX F *
          chernClassOfLocallyFreeChowCohomology C sX E 1 ^ 2 := by
  let := chowCohomologyRingOfInvertible C sX
  have T := congrArg (TotalChowClass.toChowCohomologyHom C sX 3)
    (homComponent_two_totalChernClassOfModule_tensorObj C sX E F)
  simp only [map_add, TotalChowClass.toChowCohomologyHom_apply] at T
  -- bounds on the degrees of the factors
  have bd : ∀ {i : ℕ} {c : TotalChowClass C sX}, c.IsHomogeneous i → ∀ k, i < k → c k = 0 :=
    fun hc k hk ↦ hc k (by omega)
  have hρE : (rankTotalClass C sX E).IsHomogeneous 0 := isHomogeneous_rankFunctionClass C sX E _
  have hρF : (rankTotalClass C sX F).IsHomogeneous 0 := isHomogeneous_rankFunctionClass C sX F _
  have hβE : (rankChooseTwoClass C sX E).IsHomogeneous 0 :=
    isHomogeneous_rankFunctionClass C sX E _
  have hβF : (rankChooseTwoClass C sX F).IsHomogeneous 0 :=
    isHomogeneous_rankFunctionClass C sX F _
  have hh : ∀ (G : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G]
      (i : ℕ), (TotalChowClass.homComponent i (totalChernClassOfModule C sX G)).IsHomogeneous i :=
    fun G _ i ↦ TotalChowClass.isHomogeneous_homComponent i _
  have hsq : ∀ (G : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G],
      (TotalChowClass.homComponent 1 (totalChernClassOfModule C sX G) ^ 2).IsHomogeneous 2 := by
    intro G _
    rw [pow_two]
    exact (hh G 1).mul (hh G 1)
  have hρρ : (rankTotalClass C sX E * rankTotalClass C sX F - 1).IsHomogeneous 0 :=
    TotalChowClass.mem_homogeneousSubgroup.mp (AddSubgroup.sub_mem _ (hρE.mul hρF)
      TotalChowClass.isHomogeneous_one)
  have hc1c1 : (TotalChowClass.homComponent 1 (totalChernClassOfModule C sX F) *
      TotalChowClass.homComponent 1 (totalChernClassOfModule C sX E)).IsHomogeneous 2 :=
    (hh F 1).mul (hh E 1)
  -- the truncations of the pieces
  have m1 := TotalChowClass.toChowCohomology_mul _ _ 0 2 (bd hρE) (bd (hh F 2))
  have m2 := TotalChowClass.toChowCohomology_mul _ _ 0 2 (bd hρF) (bd (hh E 2))
  have m3 := TotalChowClass.toChowCohomology_mul _ _ 0 2 (bd hβE) (bd (hsq F))
  have m4 := TotalChowClass.toChowCohomology_mul _ _ 0 2 (bd hρρ) (bd hc1c1)
  have m5 := TotalChowClass.toChowCohomology_mul _ _ 0 2 (bd hβF) (bd (hsq E))
  have m6 := TotalChowClass.toChowCohomology_mul _ _ 0 0 (bd hρE) (bd hρF)
  simp only [Nat.reduceAdd] at m1 m2 m3 m4 m5 m6
  have hsub : TotalChowClass.toChowCohomology C sX 1
      (rankTotalClass C sX E * rankTotalClass C sX F - 1) =
      TotalChowClass.toChowCohomology C sX 1 (rankTotalClass C sX E * rankTotalClass C sX F) -
        TotalChowClass.toChowCohomology C sX 1 1 :=
    map_sub (TotalChowClass.toChowCohomologyHom C sX 1) _ _
  have t0 : ∀ (G : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G]
      (f : ℕ → ℤ), TotalChowClass.toChowCohomology C sX 1 (rankFunctionClass C sX G f) =
        DirectSum.of _ ((0 : ℕ) : ℤ) (rankFunctionClass C sX G f 0) :=
    fun G _ f ↦ TotalChowClass.toChowCohomology_of_isHomogeneous (by omega)
      (isHomogeneous_rankFunctionClass C sX G f)
  simp only [pow_two] at T m3 m5
  rw [m1, m2, m3, m4, m5, hsub, m6, TotalChowClass.toChowCohomology_one] at T
  simp only [TotalChowClass.toChowCohomology_three_homComponent_one_mul] at T
  rw [
    toChowCohomology_homComponent_totalChernClassOfModule C sX _ (by omega),
    toChowCohomology_homComponent_totalChernClassOfModule C sX _ (by omega),
    toChowCohomology_homComponent_totalChernClassOfModule C sX _ (by omega)] at T
  simp only [rankTotalClass, rankChooseTwoClass, t0] at T
  rw [T]
  simp only [rankChowCohomology, rankChooseTwoChowCohomology, rankTotalClass, rankChooseTwoClass,
    chernClassOfLocallyFreeChowCohomology, totalChernClassOfModule_apply_eq_chernClassOfLocallyFree,
    pow_two]

end ChowCohomology

end Stacks.Chow

end
