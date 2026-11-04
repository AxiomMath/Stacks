module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.PowerSumComplex
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.TensorPowerSums
public import StacksCore.Tactic.StacksAttribute

/-!
# Power sums of a tensor product of finite locally free modules of arbitrary rank

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let `ℰ`, `ℱ` be finite locally free `𝒪_X`-modules, of ranks which need
not be constant. [Stacks, Tag 0F9D](https://stacks.math.columbia.edu/tag/0F9D) asserts

  `P_p(ℰ ⊗ ℱ) = ∑_{p₁ + p₂ = p} C(p, p₁) · P_{p₁}(ℰ) · P_{p₂}(ℱ)`

in `A^p(X)`, for every `p ≥ 0`, where `P_p` is the power sum of Stacks 0F9B, assembled over the
rank loci of the module (Stacks 0ESW, 0FA7), so that `P_0` is the rank function. After division
by `p!` this is the multiplicativity `ch(ℰ ⊗ ℱ) = ch(ℰ) ch(ℱ)` of the Chern character.

The identity is proved here in the ring `∏_{q ≥ 0} A^q(X)` of total Chow cohomology classes
`Stacks.Chow.TotalChowClass`. Two total classes agree as soon as they agree along every morphism
`g : T ⟶ X` along which both `g^*ℰ` and `g^*ℱ` have constant rank (Stacks 0FDZ applied to the rank
loci of the two modules). Along such a `g`, of ranks `r` and `s`, restriction commutes with power
sums and `g^*(ℰ ⊗ ℱ) ≅ g^*ℰ ⊗ g^*ℱ` has rank `r s`, and the identity is the constant-rank one,
`Stacks.Chow.powerSumTotal_sheafTensor`, which is proved by the splitting principle.

## Main results

* `Stacks.Chow.powerSumOfFiniteLocallyFree_sheafTensor` — **Stacks 0F9D** for the power sums.
* `Stacks.Chow.powerSumClassOfFiniteLocallyFree_sheafTensor` — the same identity read in
  `A^p(X)`.

## References

* [Stacks Project, Tag 0F9D](https://stacks.math.columbia.edu/tag/0F9D)
* [Stacks Project, Tag 0F9B](https://stacks.math.columbia.edu/tag/0F9B)
* [Stacks Project, Tag 0ESW](https://stacks.math.columbia.edu/tag/0ESW)
* [Stacks Project, Tag 0FA7](https://stacks.math.columbia.edu/tag/0FA7)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Finset
open Stacks.SheafOfModules.Tensor (sheafTensor)

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (E F : X.Modules) [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
  [hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F]

/-- **Stacks 0F9D.** For finite locally free `𝒪_X`-modules `ℰ` and `ℱ`, of arbitrary ranks,

  `P_p(ℰ ⊗ ℱ) = ∑_{p₁ + p₂ = p} C(p, p₁) · P_{p₁}(ℰ) · P_{p₂}(ℱ)`

in the ring of total Chow cohomology classes of `X`, for every `p ≥ 0`. Along a morphism over
which both modules have constant rank this is `Stacks.Chow.powerSumTotal_sheafTensor`, and such
morphisms detect total classes (`Stacks.Chow.TotalChowClass.eq_of_res_eq_of_constantRank₂`). -/
@[stacks 0F9D "the lemma as stated, for finite locally free E_1, E_2 of arbitrary ranks and \
every p >= 0, with no further hypothesis: P_p(E_1 tensor E_2) = sum over p_1 + p_2 = p of \
C(p, p_1) P_{p_1}(E_1) P_{p_2}(E_2), in the ring TotalChowClass C sX of total Chow cohomology \
classes (whose degree-p component is A^p(X)); P_p is the power sum of Stacks 0F9B assembled over \
the rank loci, powerSumOfFiniteLocallyFree.  The form ch(E_1 tensor E_2) = ch(E_1) ch(E_2) is \
Stacks.Chow.chernCharacterOfModule_sheafTensor"]
theorem powerSumOfFiniteLocallyFree_sheafTensor (p : ℕ) :
    haveI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (R := X.ringCatSheaf) _ :=
        isFiniteLocallyFree_tensor hE hF
    powerSumOfFiniteLocallyFree C sX (((sheafTensor X.sheaf).obj E).obj F) p =
      ∑ q ∈ antidiagonal p, (p.choose q.1 : ℤ) •
        (powerSumOfFiniteLocallyFree C sX E q.1 * powerSumOfFiniteLocallyFree C sX F q.2) := by
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := X.ringCatSheaf) _ :=
      isFiniteLocallyFree_tensor hE hF
  refine TotalChowClass.eq_of_res_eq_of_constantRank₂ C sX E F
    fun {T sT _} g _ hs r s hr hs' ↦ ?_
  have := hr
  have := hs'
  have hT : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := T.ringCatSheaf) _ _ :=
      isFiniteLocallyFreeOfRank_tensor hr hs'
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback g).obj (((sheafTensor X.sheaf).obj E).obj F)) (r * s) :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      (sheafTensorPullbackIso g E F).symm hT
  refine (res_powerSumOfFiniteLocallyFree_of_rank C sX (((sheafTensor X.sheaf).obj E).obj F) g hs
    (r * s) p).trans (((powerSumTotal_eq_of_iso C sT (sheafTensorPullbackIso g E F) p).trans
      (powerSumTotal_sheafTensor C sT _ _ r s p)).trans ?_)
  rw [map_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [map_zsmul, map_mul, res_powerSumOfFiniteLocallyFree_of_rank C sX E g hs r,
    res_powerSumOfFiniteLocallyFree_of_rank C sX F g hs s]

/-- **Stacks 0F9D in `A^p(X)`**: the degree-`p` component of
`Stacks.Chow.powerSumOfFiniteLocallyFree_sheafTensor`, i.e.
`P_p(ℰ ⊗ ℱ) = ∑_{p₁ + p₂ = p} C(p, p₁) · (P_{p₁}(ℰ) · P_{p₂}(ℱ))_p`. -/
theorem powerSumClassOfFiniteLocallyFree_sheafTensor (p : ℕ) :
    haveI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (R := X.ringCatSheaf) _ :=
        isFiniteLocallyFree_tensor hE hF
    powerSumClassOfFiniteLocallyFree C sX (((sheafTensor X.sheaf).obj E).obj F) p =
      ∑ q ∈ antidiagonal p, (p.choose q.1 : ℤ) •
        (powerSumOfFiniteLocallyFree C sX E q.1 * powerSumOfFiniteLocallyFree C sX F q.2) p := by
  refine (congrArg (fun c : TotalChowClass C sX ↦ c p)
    (powerSumOfFiniteLocallyFree_sheafTensor C sX E F p)).trans ?_
  exact TotalChowClass.sum_apply _ _ p

end Stacks.Chow

end
