module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.PowerSumTensor
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.GysinChernCharacter
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.RationalIntersectionProduct
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.ChernRoots
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.DualTotalChern
public import StacksFrontier.AlgebraicGeometry.Chow.VectorBundleKZeroPullback
public import StacksCore.Tactic.StacksAttribute

/-!
# The Chern character of the second Adams operation, and Section 0FEX

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let `ψ²` be the second Adams operation of Stacks 0FEJ on
`K_0(Vect(X))`. Stacks 0FEN asserts

  `ch_p(ψ²(α)) = 2^p ch_p(α)`   in `A^p(X) ⊗ 𝐐`, for every `α ∈ K_0(Vect(X))`.

This file proves it, for the Chern character `Stacks.Chow.chernCharacterVectorBundle` of
`K_0(Vect(X))` and the operation `AlgebraicGeometry.VectorBundleKZero.secondAdamsRingHom`, with no
hypothesis. Then it proves the statement of Section 0FEX that the grading argument of the
chapter on Weil cohomology theories uses: for `X` as in Stacks 0FEY, if `α ∈ CH^i(X) ⊗ 𝐐` and
`α' ∈ K_0(Vect(X)) ⊗ 𝐐` is the class with `ch(α') ∩ [X] = α`, then `ψ²(α') = 2^i α'`.

## The proof of Stacks 0FEN

The source's proof is followed, at the level of the power sums `P_p = p! ch_p`, which are
integral classes in the ring `∏_{q ≥ 0} A^q(X)` of total Chow cohomology classes.

* Both sides are additive in `α`, so it suffices to treat the class of a finite locally free
  module `ℰ`.
* Restriction of total classes commutes with `P_p` (`Stacks.Chow.TotalChowClass.res_powerSumKHom`)
  and `ψ²` commutes with pullback (Stacks 0FEJ), so the identity may be checked after restriction.
  The rank loci of `ℰ` decompose `X` into open and closed pieces on which `ℰ` has constant rank
  (Stacks 0FDZ), and over a piece the splitting principle (Stacks 02UL, in the form
  `Stacks.Chow.TotalChowClass.eq_of_res_eq_of_hasInvertibleFiltration`) reduces to a module with
  a filtration whose successive quotients are invertible.
* For such a module the class is the sum of the classes `[ℒ_j]` of the quotients, and
  `ψ²[ℒ_j] = [ℒ_j ⊗ ℒ_j]` (Stacks 0FEJ). For an invertible `ℒ`, with `x = c₁(ℒ)`, the power sums
  are `P_q(ℒ) = x^q` and Stacks 0F9D gives
  `P_p(ℒ ⊗ ℒ) = ∑_{q} C(p, q) x^q x^{p - q} = 2^p x^p = 2^p P_p(ℒ)`.

## Main results

* `Stacks.Chow.powerSumKHom_secondAdams` — `P_p(ψ²(α)) = 2^p P_p(α)` in `∏_q A^q(X)`.
* `Stacks.Chow.chernCharacterVectorBundle_secondAdams` — **Stacks 0FEN**, the second equation.
* `Stacks.Chow.rationalSecondAdams_eq_smul_of_rationalChernCharacterCap_mem` — **Section 0FEX**:
  the class answering to a cycle class of codimension `i` is a `2^i`-eigenvector of `ψ²`.

## References

* [Stacks Project, Tag 0FEN](https://stacks.math.columbia.edu/tag/0FEN)
* [Stacks Project, Section 0FEX](https://stacks.math.columbia.edu/tag/0FEX)
* [Stacks Project, Tag 0FEJ](https://stacks.math.columbia.edu/tag/0FEJ)
* [Stacks Project, Tag 02UL](https://stacks.math.columbia.edu/tag/02UL)
* [Stacks Project, Tag 0F9D](https://stacks.math.columbia.edu/tag/0F9D)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Finset
open Stacks.SheafOfModules.Tensor (sheafTensor)
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.VectorBundleKZero

variable {X Y : Scheme.{u}}

/-- The additive pullback `VectorBundleKZero.pullback f` agrees with the pullback ring map
`pullbackRingHom f`. -/
theorem pullback_eq_pullbackRingHom (f : X ⟶ Y) (a : VectorBundleKZero Y) :
    pullback f a = pullbackRingHom f a := by
  refine DFunLike.congr_fun (addHom_ext (φ := pullback f)
    (ψ := (pullbackRingHom f).toAddMonoidHom) fun M hM => ?_) a
  change pullback f (classOf Y M) = pullbackRingHom f (classOf Y M)
  rw [pullback_classOf, pullbackRingHom_classOf f M hM]

/-- `ψ²` commutes with the pullback `VectorBundleKZero.pullback`. -/
theorem pullback_secondAdamsRingHom (f : X ⟶ Y) (a : VectorBundleKZero Y) :
    pullback f (secondAdamsRingHom (squarePowersData Y) a) =
      secondAdamsRingHom (squarePowersData X) (pullback f a) := by
  rw [pullback_eq_pullbackRingHom, pullback_eq_pullbackRingHom, ← RingHom.comp_apply,
    ← secondAdamsRingHom_comp_pullbackRingHom, RingHom.comp_apply]

end AlgebraicGeometry.VectorBundleKZero

namespace Stacks.Chow

open AlgebraicGeometry.VectorBundleKZero

/-! ### Stacks 0FEN for the power sums -/

section PowerSum

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- The identity `P_p(ψ²(α)) = 2^p P_p(α)` for one class `α`. -/
def SecondAdamsScales (p : ℕ) (a : VectorBundleKZero X) : Prop :=
  powerSumKHom C sX p (secondAdamsRingHom (squarePowersData X) a) =
    (2 ^ p : ℤ) • powerSumKHom C sX p a

variable {C sX}

/-- The scaling identity `P_p(ψ²(α)) = 2^p P_p(α)` is closed under addition of classes. -/
theorem SecondAdamsScales.add {p : ℕ} {a b : VectorBundleKZero X}
    (ha : SecondAdamsScales C sX p a) (hb : SecondAdamsScales C sX p b) :
    SecondAdamsScales C sX p (a + b) := by
  unfold SecondAdamsScales at *
  rw [map_add, map_add, ha, hb, map_add, smul_add]

/-- The scaling identity `P_p(ψ²(α)) = 2^p P_p(α)` holds for `α = 0`. -/
theorem SecondAdamsScales.zero (p : ℕ) : SecondAdamsScales C sX p 0 := by
  unfold SecondAdamsScales
  rw [map_zero, map_zero, smul_zero]

/-- **The scaling identity may be checked after restriction**, for the class of a finite locally
free module: restriction commutes with `P_p` and `ψ²` commutes with pullback. -/
theorem res_powerSumKHom_secondAdams_classOf {T : Scheme.{u}} {sT : T ⟶ C.S}
    [LocallyOfFiniteType sT] (h : T ⟶ X) [LocallyOfFiniteType h] (hs : h ≫ sX = sT)
    (M : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M] (p : ℕ) :
    TotalChowClass.res h hs (powerSumKHom C sX p
        (secondAdamsRingHom (squarePowersData X) (classOf X M))) =
      powerSumKHom C sT p (secondAdamsRingHom (squarePowersData T)
        (classOf T ((Scheme.Modules.pullback h).obj M))) := by
  rw [TotalChowClass.res_powerSumKHom C sT sX hs, pullback_secondAdamsRingHom, pullback_classOf]

/-- For a finite locally free module `ℳ` on `X` and `h : T ⟶ X`, the restriction of `P_p([ℳ])`
along `h` is `P_p([h^*ℳ])`. -/
theorem res_powerSumKHom_classOf {T : Scheme.{u}} {sT : T ⟶ C.S}
    [LocallyOfFiniteType sT] (h : T ⟶ X) [LocallyOfFiniteType h] (hs : h ≫ sX = sT)
    (M : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M] (p : ℕ) :
    TotalChowClass.res h hs (powerSumKHom C sX p (classOf X M)) =
      powerSumKHom C sT p (classOf T ((Scheme.Modules.pullback h).obj M)) := by
  rw [TotalChowClass.res_powerSumKHom C sT sX hs, pullback_classOf]

/-- Restriction transports the scaling identity for the class of a finite locally free module. -/
theorem SecondAdamsScales.of_res {T : Scheme.{u}} {sT : T ⟶ C.S}
    [LocallyOfFiniteType sT] (h : T ⟶ X) [LocallyOfFiniteType h] (hs : h ≫ sX = sT)
    (M : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M] {p : ℕ}
    (hM : SecondAdamsScales C sT p (classOf T ((Scheme.Modules.pullback h).obj M))) :
    TotalChowClass.res h hs (powerSumKHom C sX p
        (secondAdamsRingHom (squarePowersData X) (classOf X M))) =
      TotalChowClass.res h hs ((2 ^ p : ℤ) • powerSumKHom C sX p (classOf X M)) := by
  rw [res_powerSumKHom_secondAdams_classOf, map_zsmul, res_powerSumKHom_classOf]
  exact hM

/-- **The base case**: for an invertible `ℒ`, `P_p(ℒ ⊗ ℒ) = 2^p P_p(ℒ)`, from Stacks 0F9D and
`P_q(ℒ) = c₁(ℒ)^q`. -/
theorem secondAdamsScales_classOf_of_isInvertible (L : X.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (p : ℕ) : SecondAdamsScales C sX p (classOf X L) := by
  have h1 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1 :=
    isFiniteLocallyFreeOfRank_one_of_isInvertible L
  have hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1
  have : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).mpr hL
  have hT : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Scheme.Modules.tensorObjRingedSpace X L L) :=
    isFiniteLocallyFree_tensor hF hF
  unfold SecondAdamsScales
  rw [secondAdamsRingHom_apply, secondAdamsAddHom_classOf_isInvertible, powerSumKHom_classOf,
    powerSumKHom_classOf]
  refine (powerSumOfFiniteLocallyFree_sheafTensor C sX L L p).trans ?_
  simp only [powerSumOfFiniteLocallyFree_eq_powerSumTotal C sX L 1, powerSumTotal_of_rank_one]
  have hterm : ∀ q ∈ antidiagonal p, ((p.choose q.1 : ℤ) •
      (TotalChowClass.homComponent 1 (totalChern C sX L 1) ^ q.1 *
        TotalChowClass.homComponent 1 (totalChern C sX L 1) ^ q.2)) =
      (p.choose q.1 : ℤ) • TotalChowClass.homComponent 1 (totalChern C sX L 1) ^ p := by
    intro q hq
    rw [← pow_add, mem_antidiagonal.mp hq]
  have hchoose : ∑ q ∈ antidiagonal p, (p.choose q.1 : ℤ) = 2 ^ p := by
    simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    exact_mod_cast Nat.sum_range_choose p
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_smul, hchoose]

/-- **A module filtered by invertible modules**: the class is the sum of the classes of the
quotients, so the scaling identity follows from the base case. -/
theorem secondAdamsScales_classOf_of_hasInvertibleFiltration {F : X.Modules} {r : ℕ}
    (hF : Stacks.WeilCohomology.HasInvertibleFiltration X F r) (p : ℕ) :
    SecondAdamsScales C sX p (classOf X F) := by
  induction hF with
  | nil E hE =>
    have h0 : classOf X E = 0 := by
      rw [← classOf_eq_of_iso hE.isoZero.symm (VectorBundleKZero.isFiniteLocallyFree_zero X),
        classOf_zero]
    rw [h0]
    exact SecondAdamsScales.zero p
  | @step E F L r f g w hS hL hE hF ih =>
    have hFr := hF.isFiniteLocallyFreeOfRank
    have hEr : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1) :=
      (Stacks.WeilCohomology.HasInvertibleFiltration.step f g w hS hL hE
        hF).isFiniteLocallyFreeOfRank
    have hL' : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
        X.ringCatSheaf.property L := hL
    have hL1 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1 :=
      isFiniteLocallyFreeOfRank_one_of_isInvertible L
    have hstk : ∀ (M : X.Modules) (n : ℕ),
        AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M n →
          Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M :=
      fun M n hM =>
        ⟨(AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree M
          n).exists_isFiniteLocallyFreeData⟩
    have : Mono f := hS.mono_f
    have : Epi g := hS.epi_g
    rw [classOf_shortExact f g w (hstk F r hFr) (hstk E (r + 1) hEr) (hstk L 1 hL1) hS.exact]
    exact ih.add (secondAdamsScales_classOf_of_isInvertible L p)

/-- **Stacks 0FEN for the power sums**: `P_p(ψ²(α)) = 2^p P_p(α)` in `∏_q A^q(X)`, for every
`α ∈ K_0(Vect(X))`. -/
theorem powerSumKHom_secondAdams (p : ℕ) (a : VectorBundleKZero X) :
    powerSumKHom C sX p (secondAdamsRingHom (squarePowersData X) a) =
      (2 ^ p : ℤ) • powerSumKHom C sX p a := by
  change SecondAdamsScales C sX p a
  refine DFunLike.congr_fun (addHom_ext
    (φ := (powerSumKHom C sX p).comp (secondAdamsRingHom (squarePowersData X)).toAddMonoidHom)
    (ψ := (2 ^ p : ℤ) • powerSumKHom C sX p) fun M hM => ?_) a
  change SecondAdamsScales C sX p (classOf X M)
  refine TotalChowClass.eq_of_res_eq (isClopenDecomposition_rankLociFamily M) fun r => ?_
  let := isFiniteLocallyFreeOfRank_pullback_rankLociFamily M r
  refine SecondAdamsScales.of_res _ rfl M ?_
  set U := (rankLociFamily M r).toScheme
  set N := (Scheme.Modules.pullback (rankLociFamily M r).ι).obj M
  have hN : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree N r.down
  refine TotalChowClass.eq_of_res_eq_of_hasInvertibleFiltration (I := Unit) (fun _ => N)
    (fun _ => r.down) (fun _ => inferInstance) fun {T} sT _ h _ hs hfil => ?_
  exact SecondAdamsScales.of_res h hs N
    (secondAdamsScales_classOf_of_hasInvertibleFiltration (hfil ()) p)

/-- **Stacks Project, Tag 0FEN, the second equation.** Let `(S, δ)` be as in Situation 42.7.1 and
let `X` be locally of finite type over `S`. For every `α ∈ K_0(Vect(X))` and every `p ≥ 0`,

  `ch_p(ψ²(α)) = 2^p ch_p(α)`   in `A^p(X) ⊗ 𝐐`,

where `ψ²` is the second Adams operation of Stacks 0FEJ and `ch` the Chern character of
Stacks 0FEM. -/
@[stacks 0FEN "the ch_i equation: ch_p(ψ²(α)) = 2^p ch_p(α), for every α ∈ K_0(Vect(X)) \
and every X locally of finite type over S, with no further hypothesis: ψ² is \
AlgebraicGeometry.VectorBundleKZero.secondAdamsRingHom (Stacks 0FEJ) and ch is \
Stacks.Chow.chernCharacterVectorBundle (Stacks 0FEM), with values in A^p(X) ⊗ Q"]
theorem chernCharacterVectorBundle_secondAdams (a : VectorBundleKZero X) (p : ℕ) :
    chernCharacterVectorBundle C sX (secondAdamsRingHom (squarePowersData X) a) p =
      (2 ^ p : ℚ) • chernCharacterVectorBundle C sX a p := by
  let ev : TotalChowClass C sX →+ chowCohomologyComponent C (gysinSystemOfInvertible C) sX p :=
    { toFun := fun c => c p
      map_zero' := TotalChowClass.zero_apply p
      map_add' := fun c d => TotalChowClass.add_apply c d p }
  have hev : ((2 ^ p : ℤ) • powerSumKHom C sX p a) p = (2 ^ p : ℤ) • powerSumKHom C sX p a p :=
    map_zsmul ev _ _
  rw [chernCharacterVectorBundle_apply, chernCharacterVectorBundle_apply,
    powerSumKHom_secondAdams, hev, TensorProduct.tmul_smul, ← Int.cast_smul_eq_zsmul ℚ]
  push_cast
  rfl

end PowerSum

/-! ### Section 0FEX: the eigenvalues of `ψ²` on `K_0(Vect(X)) ⊗ 𝐐` -/

section Eigenvalue

/-- **The second Adams operation on `K_0(Vect(X)) ⊗ 𝐐`**, the `𝐐`-linear extension of
`AlgebraicGeometry.VectorBundleKZero.secondAdamsRingHom`. -/
def rationalSecondAdams (X : Scheme.{u}) :
    ℚ ⊗[ℤ] VectorBundleKZero X →ₗ[ℚ] ℚ ⊗[ℤ] VectorBundleKZero X :=
  (secondAdamsRingHom (squarePowersData X)).toAddMonoidHom.toIntLinearMap.baseChange ℚ

/-- On a pure tensor, `ψ²(r ⊗ α) = r ⊗ ψ²(α)`. -/
theorem rationalSecondAdams_tmul {X : Scheme.{u}} (r : ℚ) (a : VectorBundleKZero X) :
    rationalSecondAdams X (r ⊗ₜ[ℤ] a) = r ⊗ₜ[ℤ] secondAdamsRingHom (squarePowersData X) a :=
  LinearMap.baseChange_tmul _ _ _

variable {C : ChowSituation.{u}} {X : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]

/-- `ch_p(ψ²(α')) = 2^p ch_p(α')` for `α' ∈ K_0(Vect(X)) ⊗ 𝐐`, by additivity in `α'`. -/
private theorem rationalChernCharacterVectorBundle_rationalSecondAdams_aux (p : ℕ)
    (a : ℚ ⊗[ℤ] VectorBundleKZero X) :
    rationalChernCharacterVectorBundle C sX (rationalSecondAdams X a) p =
      (2 ^ p : ℚ) • rationalChernCharacterVectorBundle C sX a p := by
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, map_add, Pi.add_apply, ha, hb, map_add, Pi.add_apply, smul_add]
  | tmul r a =>
    rw [rationalSecondAdams_tmul, rationalChernCharacterVectorBundle_tmul,
      rationalChernCharacterVectorBundle_tmul, Pi.smul_apply, Pi.smul_apply,
      chernCharacterVectorBundle_secondAdams, smul_comm]

/-- **Stacks 0FEN on the operators `ch_p(-) ∩ -`**: `ch_p(ψ²(α')) ∩ - = 2^p (ch_p(α') ∩ -)` for
`α' ∈ K_0(Vect(X)) ⊗ 𝐐`. -/
theorem rationalChernCharacterComponentCap_rationalSecondAdams (p : ℕ)
    (a : ℚ ⊗[ℤ] VectorBundleKZero X) :
    rationalChernCharacterComponentCap C sX p (rationalSecondAdams X a) =
      (2 ^ p : ℚ) • rationalChernCharacterComponentCap C sX p a := by
  rw [rationalChernCharacterComponentCap_apply, rationalChernCharacterComponentCap_apply,
    rationalChernCharacterVectorBundle_rationalSecondAdams_aux, map_smul]

/-- **Stacks 0FEN on `K_0(Vect(X)) ⊗ 𝐐`**: `ch_p(ψ²(α')) = 2^p ch_p(α')`. -/
theorem rationalChernCharacterVectorBundle_rationalSecondAdams (p : ℕ)
    (a : ℚ ⊗[ℤ] VectorBundleKZero X) :
    rationalChernCharacterVectorBundle C sX (rationalSecondAdams X a) p =
      (2 ^ p : ℚ) • rationalChernCharacterVectorBundle C sX a p :=
  rationalChernCharacterVectorBundle_rationalSecondAdams_aux p a

variable [IsNoetherian X] [IsAffineHom (pullback.diagonal (terminal.from X))]

/-- **Stacks Project, Section 0FEX: the class answering to a cycle class of codimension `i` is a
`2^i`-eigenvector of `ψ²`.** Let `X` be as in Stacks 0FEY (Noetherian, equivalently quasi-compact,
regular, of finite type over `S`, with affine diagonal and `δ_{X/S}` bounded). If
`α ∈ CH^i(X) ⊗ 𝐐` and `α' ∈ K_0(Vect(X)) ⊗ 𝐐` is the (unique, by Stacks 0FEY) class with
`ch(α') ∩ [X] = α`, then `ψ²(α') = 2^i α'`. -/
@[stacks 0FEX "the eigenvalue statement of the section: for X as in 0FEY, α ∈ CH^i(X) ⊗ Q and \
α' ∈ K_0(Vect(X)) ⊗ Q with ch(α') ∩ [X] = α, ψ²(α') = 2^i α', where ψ² is the second Adams \
operation of 0FEJ extended Q-linearly (Stacks.Chow.rationalSecondAdams); proved from 0FEN \
(Stacks.Chow.chernCharacterVectorBundle_secondAdams) and the uniqueness in 0FEY, as in the source"]
theorem rationalSecondAdams_eq_smul_of_rationalChernCharacterCap_mem (hX : IsRegular X)
    (hb : ∃ lo hi : ℤ, ∀ x : X, lo ≤ relativeDimension C.dimensionFunction sX x ∧
      relativeDimension C.dimensionFunction sX x ≤ hi)
    {i : ℕ} {a : ℚ ⊗[ℤ] VectorBundleKZero X}
    (ha : rationalChernCharacterCap C sX a (rationalFundamentalClass C sX) ∈
      codimensionChowSubmodule C sX i) :
    rationalSecondAdams X a = (2 ^ i : ℚ) • a := by
  classical
  have hT := bijective_flip_rationalChernCharacterCap hX hb
  obtain ⟨lo, hi, hb'⟩ := hb
  set N : ℕ := max (hi - lo).toNat i
  have hsum := rationalChernCharacterCap_eq_sum C sX hb' (N := N) (by omega)
  have hiN : i ∈ range (N + 1) := by
    rw [mem_range]
    omega
  set e := rationalFundamentalClass C sX
  have hgr : ∀ q ∈ range (N + 1),
      rationalChernCharacterComponentCap C sX q a e ∈ codimensionChowSubmodule C sX q := by
    intro q _
    have H := rationalChowCap_mem_codimensionChowSubmodule_add C sX _
      (isCohenMacaulay_of_isRegular hX) q (rationalChernCharacterVectorBundle C sX a q)
      (directSumRight_one_tmul_totalFundamentalClass_mem_codimensionChowSubmodule_zero C sX)
    rw [zero_add] at H
    exact H
  have hα : ∑ q ∈ range (N + 1), rationalChernCharacterComponentCap C sX q a e ∈
      codimensionChowSubmodule C sX i := by
    rw [← LinearMap.sum_apply, ← LinearMap.sum_apply, ← hsum]
    exact ha
  have hcomp : ∀ q ∈ range (N + 1), q ≠ i → rationalChernCharacterComponentCap C sX q a e = 0 :=
    fun q hq hqi => iSupIndep.eq_zero_of_sum_mem
      (isInternal_codimensionChowSubmodule_of_isRegular C sX hX).submodule_iSupIndep
      (x := fun q => rationalChernCharacterComponentCap C sX q a e) hgr hα hq hqi
  refine hT.1 ?_
  simp only [LinearMap.flip_apply]
  rw [hsum]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, map_smul]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [rationalChernCharacterComponentCap_rationalSecondAdams, LinearMap.smul_apply]
  rcases eq_or_ne q i with rfl | hqi
  · rfl
  · rw [hcomp q hq hqi]
    simp

/-- **Stacks Project, Section 0FEX: the components of `ch(α')` off the codimension vanish.** For
`X` as in Stacks 0FEY, `α ∈ CH^i(X) ⊗ 𝐐` and `α' ∈ K_0(Vect(X)) ⊗ 𝐐` with `ch(α') ∩ [X] = α`, one
has `ch_j(α') = 0` in `A^j(X) ⊗ 𝐐` for every `j ≠ i`. -/
@[stacks 0FEX "the vanishing statement of the section: for X as in 0FEY, α ∈ CH^i(X) ⊗ Q and \
α' ∈ K_0(Vect(X)) ⊗ Q with ch(α') ∩ [X] = α, ch_j(α') = 0 in A^j(X) ⊗ Q for every j ≠ i, from \
ψ²(α') = 2^i α' and 0FEN, as in the source"]
theorem rationalChernCharacterVectorBundle_eq_zero_of_rationalChernCharacterCap_mem
    (hX : IsRegular X)
    (hb : ∃ lo hi : ℤ, ∀ x : X, lo ≤ relativeDimension C.dimensionFunction sX x ∧
      relativeDimension C.dimensionFunction sX x ≤ hi)
    {i : ℕ} {a : ℚ ⊗[ℤ] VectorBundleKZero X}
    (ha : rationalChernCharacterCap C sX a (rationalFundamentalClass C sX) ∈
      codimensionChowSubmodule C sX i) {j : ℕ} (hj : j ≠ i) :
    rationalChernCharacterVectorBundle C sX a j = 0 := by
  have h := rationalChernCharacterVectorBundle_rationalSecondAdams (C := C) (sX := sX) j a
  rw [rationalSecondAdams_eq_smul_of_rationalChernCharacterCap_mem hX hb ha, map_smul,
    Pi.smul_apply] at h
  have h2 : ((2 ^ i : ℚ) - 2 ^ j) • rationalChernCharacterVectorBundle C sX a j = 0 := by
    rw [sub_smul, h, sub_self]
  refine (smul_eq_zero.mp h2).resolve_left ?_
  intro h'
  rw [sub_eq_zero] at h'
  exact hj (Nat.pow_right_injective (le_refl 2) (by exact_mod_cast h'.symm))

/-- **Stacks Project, Section 0FEX: `ch_{i'}(α') ∩ [X] = 0` for `i' ≠ i` and
`ch_i(α') ∩ [X] = α`.** For `X` as in Stacks 0FEY, `α ∈ CH^i(X) ⊗ 𝐐` and
`α' ∈ K_0(Vect(X)) ⊗ 𝐐` with `ch(α') ∩ [X] = α`, the components of `ch(α')` other than the
`i`-th cap `[X]` to zero, and the `i`-th one caps `[X]` to `α`. -/
@[stacks 0FEX "the consequence the section draws from the vanishing statement: for X as in 0FEY, \
α ∈ CH^i(X) ⊗ Q and α' ∈ K_0(Vect(X)) ⊗ Q with ch(α') ∩ [X] = α, ch_{i'}(α') ∩ [X] = 0 for \
i' ≠ i and ch_i(α') ∩ [X] = α"]
theorem rationalChernCharacterComponentCap_rationalFundamentalClass_of_mem (hX : IsRegular X)
    (hb : ∃ lo hi : ℤ, ∀ x : X, lo ≤ relativeDimension C.dimensionFunction sX x ∧
      relativeDimension C.dimensionFunction sX x ≤ hi)
    {i : ℕ} {a : ℚ ⊗[ℤ] VectorBundleKZero X}
    (ha : rationalChernCharacterCap C sX a (rationalFundamentalClass C sX) ∈
      codimensionChowSubmodule C sX i) :
    (∀ j : ℕ, j ≠ i →
        rationalChernCharacterComponentCap C sX j a (rationalFundamentalClass C sX) = 0) ∧
      rationalChernCharacterComponentCap C sX i a (rationalFundamentalClass C sX) =
        rationalChernCharacterCap C sX a (rationalFundamentalClass C sX) := by
  classical
  have hvan : ∀ j : ℕ, j ≠ i →
      rationalChernCharacterComponentCap C sX j a (rationalFundamentalClass C sX) = 0 := by
    intro j hj
    rw [rationalChernCharacterComponentCap_apply,
      rationalChernCharacterVectorBundle_eq_zero_of_rationalChernCharacterCap_mem hX hb ha hj,
      map_zero, LinearMap.zero_apply]
  refine ⟨hvan, ?_⟩
  obtain ⟨lo, hi, hb'⟩ := hb
  have hsum := rationalChernCharacterCap_eq_sum C sX hb' (N := max (hi - lo).toNat i)
    (by omega)
  rw [hsum, LinearMap.sum_apply, LinearMap.sum_apply,
    Finset.sum_eq_single_of_mem i (by rw [mem_range]; omega) fun j _ hj => hvan j hj]

end Eigenvalue

end Stacks.Chow

end
