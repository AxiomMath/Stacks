module

public import StacksFrontier.AlgebraicGeometry.Chow.AdamsOperatorChernScaling
public import StacksFrontier.AlgebraicGeometry.Chow.MinusAdamsOperator
public import StacksCore.Tactic.StacksAttribute

/-!
# The Chern character of the dual of a finite locally free module

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S`, let `ℰ` be a finite locally free `𝒪_X`-module and let
`ℰ^∨ = SheafHom(ℰ, 𝒪_X)` be its dual. Assuming the sign rule `c_i(ℰ^∨) = (-1)^i c_i(ℰ)` for
Chern classes, this file proves the sign rule

  `ch_i(ℰ^∨) = (-1)^i ch_i(ℰ)`  in  `A^i(X) ⊗ 𝐐`

for the Chern character, for every class of `K_0(Vect(X))`: dualizing induces the minus-one
Adams operation `ψ^{-1}` on `K_0(Vect(X))`, which is
`AlgebraicGeometry.VectorBundleKZero.dualAddHom`, with `ψ^{-1}([ℰ]) = [ℰ^∨]`.

## Main definitions

* `Stacks.Chow.chowSeriesSignScale` — the endomorphism of `∏_{i ≥ 0} A^i(X)` scaling `A^i(X)` by
  `(-1)^i`, and `Stacks.Chow.ChowCohomologySeriesRing.unitalSeriesSignScale`, the endomorphism of
  the group of series with constant term `1` it induces.
* `Stacks.Chow.HasDualChernSignRule` — the sign rule for Chern classes as a hypothesis: the
  total Chern class of the dual of a finite locally free module is the `(-1)^i`-scaling of its
  total Chern class.
* `Stacks.Chow.NewtonPowerSums.IsSignHomogeneous` — the weighted homogeneity of `P_p` at the
  substitution `c_j ↦ (-1)^j c_j`.

## Main results

* `Stacks.Chow.ChowCohomologySeriesRing.chowSeriesSignScale_one` and
  `Stacks.Chow.ChowCohomologySeriesRing.chowSeriesSignScale_mul` — the `(-1)^i`-scaling is a ring
  endomorphism of `∏_{i ≥ 0} A^i(X)`: it fixes the unit series and preserves the Cauchy product.
* `Stacks.Chow.chernClassKGroup_dualAddHom` — `c(ψ^{-1}(α))` is the `(-1)^i`-scaling of `c(α)`
  for every `α ∈ K_0(Vect(X))`.
* `Stacks.Chow.chernCharacterKGroup_dualAddHom` — `ch_i(ψ^{-1}(α)) = (-1)^i ch_i(α)` for every
  `α ∈ K_0(Vect(X))`.
* `Stacks.Chow.chernCharacterKGroup_classOf` — at the class of a module the Chern character is
  `ch_p(ℰ) = P_p(c_1(ℰ), …, c_p(ℰ))/p!`.

## References

* [Stacks Project, Tag 0FAB](https://stacks.math.columbia.edu/tag/0FAB)
* [Stacks Project, Tag 0FA5](https://stacks.math.columbia.edu/tag/0FA5)
* [Stacks Project, Tag 0FA7](https://stacks.math.columbia.edu/tag/0FA7)
* [Stacks Project, Tag 0FV8](https://stacks.math.columbia.edu/tag/0FV8)
* [Stacks Project, Tag 0FEM](https://stacks.math.columbia.edu/tag/0FEM)
* [Stacks Project, Tag 0FEL](https://stacks.math.columbia.edu/tag/0FEL)
* [Stacks Project, Tag 0FEN](https://stacks.math.columbia.edu/tag/0FEN)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
* [Stacks Project, Tag 0F9C](https://stacks.math.columbia.edu/tag/0F9C)
* [Stacks Project, Tag 0ESX](https://stacks.math.columbia.edu/tag/0ESX)
* [Stacks Project, Tag 02UI](https://stacks.math.columbia.edu/tag/02UI)
* [Stacks Project, Tag 02UL](https://stacks.math.columbia.edu/tag/02UL)
* [Stacks Project, Tag 0B7E](https://stacks.math.columbia.edu/tag/0B7E)
* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.VectorBundleKZero
open Stacks.FiniteLocallyFree
open scoped TensorProduct

universe u

namespace Stacks.Chow

open ChowCohomologySeriesRing

variable {C : ChowSituation.{u}} {G : GysinSystem C} {X : Scheme.{u}} {sX : X ⟶ C.S}
  [LocallyOfFiniteType sX]

/-! ### The endomorphism scaling `A^i(X)` by `(-1)^i` -/

/-- The endomorphism of `∏_{i ≥ 0} A^i(X)` which scales `A^i(X)` by `(-1)^i`, that is, the
substitution `c_j ↦ (-1)^j c_j` on series. -/
def chowSeriesSignScale (a : chowCohomologySeries C G sX) : chowCohomologySeries C G sX :=
  fun i ↦ ((-1 : ℤ) ^ i) • a i

/-- The degree-`i` term of the sign-scaling of `a` is `(-1)^i • a i`. -/
@[simp] theorem chowSeriesSignScale_apply (a : chowCohomologySeries C G sX) (i : ℕ) :
    chowSeriesSignScale a i = ((-1 : ℤ) ^ i) • a i := rfl

namespace ChowCohomologySeriesRing

variable (R : ChowCohomologySeriesRing C G sX)

/-- The degreewise product is compatible with integer multiples in its first variable. -/
theorem gradedMul_zsmul_left (i j n : ℕ) (h : i + j = n) (k : ℤ)
    (x : chowCohomologyComponent C G sX (i : ℤ))
    (y : chowCohomologyComponent C G sX (j : ℤ)) :
    R.gradedMul i j n h (k • x) y = k • R.gradedMul i j n h x y :=
  map_zsmul (AddMonoidHom.mk' (fun x ↦ R.gradedMul i j n h x y)
    (fun x x' ↦ R.gradedMul_add_left i j n h x x' y)) k x

/-- The degreewise product is compatible with integer multiples in its second variable. -/
theorem gradedMul_zsmul_right (i j n : ℕ) (h : i + j = n) (k : ℤ)
    (x : chowCohomologyComponent C G sX (i : ℤ))
    (y : chowCohomologyComponent C G sX (j : ℤ)) :
    R.gradedMul i j n h x (k • y) = k • R.gradedMul i j n h x y :=
  map_zsmul (AddMonoidHom.mk' (fun y ↦ R.gradedMul i j n h x y)
    (fun y y' ↦ R.gradedMul_add_right i j n h x y y')) k y

/-- The sign-scaling map fixes the unit series. -/
theorem chowSeriesSignScale_one : chowSeriesSignScale R.one = R.one := by
  funext n
  cases n with
  | zero => rw [chowSeriesSignScale_apply, pow_zero, one_smul]
  | succ m => rw [chowSeriesSignScale_apply, R.one_apply_succ m, smul_zero]

/-- The sign-scaling map is multiplicative for the Cauchy product. -/
theorem chowSeriesSignScale_mul (a b : chowCohomologySeries C G sX) :
    chowSeriesSignScale (chowSeriesMul R.gradedMul a b) =
      chowSeriesMul R.gradedMul (chowSeriesSignScale a) (chowSeriesSignScale b) := by
  funext n
  rw [chowSeriesSignScale_apply, chowSeriesMul, chowSeriesMul, Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  rintro ⟨i, j⟩ hmem
  rw [Finset.mem_antidiagonal] at hmem
  rw [chowSeriesTerm_of_add R.gradedMul a b hmem,
    chowSeriesTerm_of_add R.gradedMul (chowSeriesSignScale a) (chowSeriesSignScale b) hmem,
    chowSeriesSignScale_apply, chowSeriesSignScale_apply, R.gradedMul_zsmul_left,
    R.gradedMul_zsmul_right, smul_smul, ← pow_add, hmem]

/-- The sign-scaling map as an endomorphism of the group of series with constant term `1`. -/
def unitalSeriesSignScale : UnitalSeries R →* UnitalSeries R :=
  MonoidHom.mk' (fun a : UnitalSeries R ↦ ⟨chowSeriesSignScale a.1, by simpa using a.2⟩)
    fun a b ↦ Subtype.ext (R.chowSeriesSignScale_mul a.1 b.1)

/-- The underlying series of the sign-scaling of a unital series. -/
@[simp] theorem unitalSeriesSignScale_val (a : UnitalSeries R) :
    (R.unitalSeriesSignScale a).1 = chowSeriesSignScale a.1 := rfl

/-- The sign-scaling map read on `Additive` of the group of unital series. -/
theorem toAdditive_unitalSeriesSignScale_ofMul (a : UnitalSeries R) :
    MonoidHom.toAdditive R.unitalSeriesSignScale (Additive.ofMul a) =
      Additive.ofMul (R.unitalSeriesSignScale a) := rfl

end ChowCohomologySeriesRing

/-! ### The Chern class sign rule for the dual, as a hypothesis -/

variable {R : ChowCohomologySeriesRing C G sX}

/-- The sign rule for the Chern classes of duals: for every finite locally free module `ℰ`, the
Chern classes of the dual satisfy `c_i(ℰ^∨) = (-1)^i c_i(ℰ)`. -/
def HasDualChernSignRule (D : TotalChernClassSeries C G sX R) : Prop :=
  ∀ E : X.Modules, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E → ∀ i : ℕ,
    D.ch (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf E) i = ((-1 : ℤ) ^ i) • D.ch E i

/-- The weighted homogeneity of the Newton power sums at the substitution `c_j ↦ (-1)^j c_j`:
scaling the degree-`j` term of a series by `(-1)^j` multiplies `P_p(c_1, …, c_p)` by `(-1)^p`. -/
def NewtonPowerSums.IsSignHomogeneous (N : NewtonPowerSums C G sX R) : Prop :=
  ∀ (p : ℕ) (a : chowCohomologySeries C G sX),
    N.powerSum p (chowSeriesSignScale a) = ((-1 : ℤ) ^ p) • N.powerSum p a

/-- The Chern class sign rule in series form: the total Chern class of the dual of a finite
locally free module is the `(-1)^i`-scaling of its total Chern class. -/
theorem ch_dualSheaf_eq_chowSeriesSignScale {D : TotalChernClassSeries C G sX R}
    (hdual : HasDualChernSignRule D) (E : X.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E) :
    D.ch (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf E) =
      chowSeriesSignScale (D.ch E) :=
  funext fun i => hdual E hE i

/-! ### The Chern classes of the minus-one Adams operation -/

/-- The Chern class map and the minus-one Adams operation: as homomorphisms, `c ∘ ψ^{-1}` is the
sign-scaling of `c` on all of `K_0(Vect(X))`. -/
theorem chernClassKGroupHom_dualAddHom {D : TotalChernClassSeries C G sX R}
    (hdual : HasDualChernSignRule D) (α : VectorBundleKZero X) :
    chernClassKGroupHom D
        (dualAddHom (dualPreservesFiniteLocallyFree X) (dualShortExact X) α) =
      MonoidHom.toAdditive R.unitalSeriesSignScale (chernClassKGroupHom D α) := by
  have key : (chernClassKGroupHom D).comp
        (dualAddHom (dualPreservesFiniteLocallyFree X) (dualShortExact X)) =
      (MonoidHom.toAdditive R.unitalSeriesSignScale).comp (chernClassKGroupHom D) := by
    refine AlgebraicGeometry.VectorBundleKZero.addHom_ext fun E hE ↦ ?_
    have hcl : dualAddHom (dualPreservesFiniteLocallyFree X) (dualShortExact X)
          (classOf X E) =
        classOf X (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf E) :=
      dualAddHom_classOf _ _ E hE
    simp only [AddMonoidHom.coe_comp, Function.comp_apply]
    rw [hcl, chernClassKGroupHom_classOf, chernClassKGroupHom_classOf,
      R.toAdditive_unitalSeriesSignScale_ofMul]
    exact congrArg Additive.ofMul (Subtype.ext (ch_dualSheaf_eq_chowSeriesSignScale hdual E hE))
  exact DFunLike.congr_fun key α

/-- The Chern class of the minus-one Adams operation: `c(ψ^{-1}(α))` is the `(-1)^i`-scaling of
`c(α)`, for every `α ∈ K_0(Vect(X))`. -/
theorem chernClassKGroup_dualAddHom {D : TotalChernClassSeries C G sX R}
    (hdual : HasDualChernSignRule D) (α : VectorBundleKZero X) :
    chernClassKGroup D
        (dualAddHom (dualPreservesFiniteLocallyFree X) (dualShortExact X) α) =
      chowSeriesSignScale (chernClassKGroup D α) :=
  congrArg Subtype.val (congrArg Additive.toMul (chernClassKGroupHom_dualAddHom hdual α))

/-! ### The Chern character of the dual -/

/-- At the class `[ℰ]` of a module the Chern character is
`ch_p(ℰ) = P_p(c_1(ℰ), …, c_p(ℰ))/p!`. -/
theorem chernCharacterKGroup_classOf {D : TotalChernClassSeries C G sX R}
    (N : NewtonPowerSums C G sX R) (E : X.Modules) (p : ℕ) :
    chernCharacterKGroup (D := D) N (classOf X E) p =
      ((Nat.factorial p : ℚ)⁻¹) ⊗ₜ[ℤ] N.powerSum p (D.ch E) := by
  rw [chernCharacterKGroup, chernClassKGroup_classOf]

/-- The Chern character of the minus-one Adams operation: `ch_i(ψ^{-1}(α)) = (-1)^i ch_i(α)` in
`A^i(X) ⊗ 𝐐` for every `α ∈ K_0(Vect(X))`. -/
theorem chernCharacterKGroup_dualAddHom {D : TotalChernClassSeries C G sX R}
    (N : NewtonPowerSums C G sX R) (hsign : N.IsSignHomogeneous)
    (hdual : HasDualChernSignRule D) (α : VectorBundleKZero X) (i : ℕ) :
    chernCharacterKGroup (D := D) N
        (dualAddHom (dualPreservesFiniteLocallyFree X) (dualShortExact X) α) i =
      ((-1 : ℤ) ^ i) • chernCharacterKGroup (D := D) N α i := by
  rw [chernCharacterKGroup, chernCharacterKGroup, chernClassKGroup_dualAddHom hdual α, hsign,
    TensorProduct.tmul_smul]

end Stacks.Chow

end
