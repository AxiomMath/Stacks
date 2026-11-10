module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerCoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerCoherent

/-!
# The exterior square sits inside the tensor square with symmetric square as quotient

Let `R` be a commutative ring and `M` an `R`-module. This file constructs the **antisymmetriser**

`⋀²(M) ⟶ T²(M)`, `x ∧ y ↦ x ⊗ y - y ⊗ x`,

identifies its range with the kernel of the canonical surjection `T²(M) ⟶ Sym²(M)`, and proves it
injective when `M` is free. Together with the surjectivity of `T²(M) ⟶ Sym²(M)` that is the
three-term sequence

`0 ⟶ ⋀²(M) ⟶ T²(M) ⟶ Sym²(M) ⟶ 0`,

exact at the middle term over **every** commutative ring and for every module, and short exact as
soon as `M` is free -- in particular with no assumption that `2` is invertible: in characteristic
two the images of the wedges `bᵢ ∧ bⱼ` of basis vectors are the symmetric tensors
`bᵢ ⊗ bⱼ + bⱼ ⊗ bᵢ` with `i < j`, which are still linearly independent.

Both powers are taken where the library already has them: `⋀²(M)` is Mathlib's `⋀[R]^2 M`, the
degree-two piece of `ExteriorAlgebra R M`, and `T²(M)` is `TensorAlgebra.gradedPiece R 2 M`, the
degree-two piece of the tensor algebra, so the quotient map `T²(M) ⟶ Sym²(M)` is
`TensorAlgebra.symQuot 2` and nothing about either power is redefined.

The same sequence is then assembled sectionwise for a presheaf of modules, and the two maps are
sheafified: the antisymmetriser commutes with base change, so the sectionwise antisymmetrisers of
a presheaf of modules are a morphism of presheaves of modules, and sheafifying gives the map
`⋀²(F) ⟶ T²(F)` of sheaves of modules.

## Main definitions

* `TensorAlgebra.commBilin`: the commutator `x ⊗ y - y ⊗ x`, as an `R`-bilinear map
  `M × M ⟶ T²(M)`. It is `TensorAlgebra.altTwo` of a product of two degree-one generators.
* `TensorAlgebra.extTwoToTensor`: **the antisymmetriser `⋀²(M) ⟶ T²(M)`**, obtained from
  `commBilin` by the universal property `exteriorPower.alternatingMapLinearEquiv` of the exterior
  power: `commBilin` is alternating because `x ⊗ x - x ⊗ x = 0`.
* `TensorAlgebra.tensorTwoCoord`: for a basis `b` of `M` indexed by a linearly ordered type and
  two indices `i`, `j`, the linear form on `T²(M)` reading off the coefficient of `bᵢ ⊗ bⱼ`.
* `PresheafOfModules.extTwoToTensorHom`: the sectionwise antisymmetriser `⋀² ⟶ T²`, as a
  morphism of presheaves of modules, and `PresheafOfModules.extSymShortComplex` the three-term
  complex `⋀² ⟶ T² ⟶ Sym²` it starts.
* `SheafOfModules.exteriorSquareToTensorPiece`: **the antisymmetriser `⋀²(F) ⟶ T²(F)` of sheaves
  of modules**, the sheafification of the sectionwise one read through
  `SheafOfModules.exteriorPowerSheafifyIso` and `SheafOfModules.tensorPieceSheafifyIso`.
* `SheafOfModules.symmetricPowerQuotHom`: the quotient map `Tⁿ(F) ⟶ Symⁿ(F)` of sheaves of
  modules, the symmetric companion of `SheafOfModules.exteriorPowerQuotHom`.

## Main results

* `TensorAlgebra.symQuot_extTwoToTensor`: the composite `⋀²(M) ⟶ T²(M) ⟶ Sym²(M)` is zero.
* `TensorAlgebra.range_extTwoToTensor`: **the range of the antisymmetriser is the kernel of
  `T²(M) ⟶ Sym²(M)`.** This is exactness at the middle term, and it holds for an arbitrary
  module over an arbitrary commutative ring.
* `TensorAlgebra.injective_extTwoToTensor_of_basis` and
  `TensorAlgebra.injective_extTwoToTensor`: **the antisymmetriser is injective on a free
  module.**
* `TensorAlgebra.extTwoToTensor_extQuot`: the antisymmetriser composed with the quotient map
  `T²(M) ⟶ ⋀²(M)` is `TensorAlgebra.altTwo`. This is what reduces every statement about the
  antisymmetriser to one about `altTwo`, which the library already has.
* `TensorAlgebra.extTwoToTensor_powMapₛₗ`: **the antisymmetriser commutes with base change**,
  which is what makes the sectionwise maps a morphism of presheaves of modules.
* `PresheafOfModules.extSymShortComplex_exact`: **the complex `⋀² ⟶ T² ⟶ Sym²` of presheaves of
  modules is exact at the middle term**, with no hypothesis on the presheaf, and
  `PresheafOfModules.epi_extSymShortComplex_g` that its second map is an epimorphism.
* `SheafOfModules.epi_symmetricPowerQuotHom` and
  `SheafOfModules.exteriorSquareToTensorPiece_comp_symmetricPowerQuotHom`: `Tⁿ(F) ⟶ Symⁿ(F)` is
  an epimorphism, and the sheafified composite `⋀²(F) ⟶ T²(F) ⟶ Sym²(F)` is zero.

## What the sequence is short exact

`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorSquareTensorShortExact` completes the
sequence: `SheafOfModules.shortExact_extSymSheafShortComplex` is the short exactness of
`0 ⟶ ⋀²(F) ⟶ T²(F) ⟶ Sym²(F) ⟶ 0` for a sheaf of modules all of whose stalks are free — in
particular for a finite locally free one. Two of the three clauses are the sectionwise ones
proved here, transported by the exactness of sheafification; the third, the monomorphy of the
first map, is *not* a sectionwise statement, because `F(U)` need not be free, and is read on
stalks there. The one lemma that route needed and that this file does not contain is the
identification of the stalk of the sectionwise antisymmetriser with `extTwoToTensor` at the
stalk, `PresheafOfModules.tensorPowStalkL_stalkMapL_extTwoToTensorHom`; it is immediate from
`TensorAlgebra.extTwoToTensor_powMapₛₗ` below, because the comparisons of Tag 01CH *are* base
change along the germ maps.

## Implementation notes

**Why the range computation is cheap.**
`StacksFrontier.LinearAlgebra.TensorAlgebra.SymmetricQuotient` already computes the kernel of
`Tᵏ(M) ⟶ Symᵏ(M)` as the degree-`k` relator submodule
`TensorAlgebra.relDeg k`, the sum over the `k - 1` adjacent slot pairs of
`Tⁱ · commSub · Tʲ`. In degree two there is one slot pair and the outer factors are `T⁰ = 1`, so
`relDeg 2` is the commutator submodule `TensorAlgebra.commSub` itself, which is by definition the
span of the elements `ι x · ι y - ι y · ι x` -- that is, of the values of `commBilin`. So no
further kernel computation is needed, and in particular the route does not pass through the
quotient map `T²(M) ⟶ ⋀²(M)` of
`StacksFrontier.LinearAlgebra.TensorAlgebra.ExteriorQuotient`.

**Why injectivity is proved by a dual family and not by a retraction.** The composite
`⋀²(M) ⟶ T²(M) ⟶ ⋀²(M)` is multiplication by `2`, so the antisymmetriser has no natural
retraction and in characteristic two no basis-free one either. What is true is that the images of
the basis `Module.Basis.exteriorPower` of `⋀²(M)` are separated by the coefficient forms
`tensorTwoCoord b i j` of `T²(M)`: for `i < j` the form `tensorTwoCoord b i j` takes the value
`1` on the image of `bᵢ ∧ bⱼ` and `0` on the image of every other basis wedge, the two terms
`[k = i][l = j]` and `[l = i][k = j]` of its value on the image of `b_k ∧ b_l` never both firing
because `i < j` and `k < l`. `LinearIndependent.of_pairwise_dual_eq_zero_one` turns that into
linear independence and `Module.Basis.injective_constr_of_linearIndependent` into injectivity.
No finiteness of the basis is used.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 00DP](https://stacks.math.columbia.edu/tag/00DP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite

open scoped TensorProduct

universe v u w

/-! ### The commutator bilinear map -/

namespace TensorAlgebra

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- **The commutator `x ⊗ y - y ⊗ x`**, as an `R`-bilinear map from `M` to the degree-two piece
`T²(M)` of the tensor algebra. It is `TensorAlgebra.altTwo` applied to the product of the two
degree-one generators. -/
def commBilin : M →ₗ[R] M →ₗ[R] gradedPiece R 2 M :=
  (LinearMap.compr₂ (TensorProduct.mk R (gradedPiece R 1 M) (gradedPiece R 1 M))
      (altTwo ∘ₗ (mulTwo (R := R) (M := M)).toLinearMap)).compl₁₂
    gradedPieceOneEquiv.toLinearMap gradedPieceOneEquiv.toLinearMap

/-- The commutator `commBilin x y` is `altTwo` of the product of the degree-one generators of `x`
and `y`. -/
theorem commBilin_apply (x y : M) :
    commBilin (R := R) x y =
      altTwo (mulTwo (gradedPieceOneEquiv x ⊗ₜ[R] gradedPieceOneEquiv (R := R) y)) := rfl

/-- In the tensor algebra, `commBilin x y` is the commutator `ι x * ι y - ι y * ι x`. -/
@[simp]
theorem coe_commBilin (x y : M) :
    (commBilin (R := R) x y : TensorAlgebra R M) = ι R x * ι R y - ι R y * ι R x := by
  rw [commBilin_apply]
  exact coe_altTwo_mulTwo _ _

/-- The commutator of an element with itself vanishes. -/
@[simp]
theorem commBilin_self (x : M) : commBilin (R := R) x x = 0 :=
  Subtype.ext (by rw [coe_commBilin, sub_self, ZeroMemClass.coe_zero])

private theorem fin_two_eq_zero_or_one : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide

private theorem fin_two_ne_cases :
    ∀ i j : Fin 2, i ≠ j → (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by decide

/-- The commutator bilinear map, read as a multilinear map on `Fin 2`-indexed families. -/
def commMultilinear : MultilinearMap R (fun _ : Fin 2 => M) (gradedPiece R 2 M) where
  toFun v := commBilin (v 0) (v 1)
  map_update_add' v i x y := by
    rcases fin_two_eq_zero_or_one i with rfl | rfl <;>
      simp only [Function.update_self, Function.update_of_ne Fin.zero_ne_one'.symm,
        Function.update_of_ne (Fin.zero_ne_one' (n := 1)), map_add, LinearMap.add_apply]
  map_update_smul' v i c x := by
    rcases fin_two_eq_zero_or_one i with rfl | rfl <;>
      simp only [Function.update_self, Function.update_of_ne Fin.zero_ne_one'.symm,
        Function.update_of_ne (Fin.zero_ne_one' (n := 1)), map_smul, LinearMap.smul_apply]

/-- `commMultilinear` evaluated at `v` is the commutator of `v 0` and `v 1`. -/
@[simp]
theorem commMultilinear_apply (v : Fin 2 → M) :
    commMultilinear (R := R) v = commBilin (v 0) (v 1) := rfl

/-- The commutator bilinear map, read as an alternating map on `Fin 2`-indexed families: it is
alternating because `x ⊗ x - x ⊗ x = 0`. -/
def commAlternating : M [⋀^Fin 2]→ₗ[R] gradedPiece R 2 M where
  toMultilinearMap := commMultilinear
  map_eq_zero_of_eq' v i j hv hij := by
    change commBilin (R := R) (v 0) (v 1) = 0
    rcases fin_two_ne_cases i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [← hv]
      exact commBilin_self (v 0)
    · rw [hv]
      exact commBilin_self (v 0)

/-- `commAlternating` evaluated at `v` is the commutator of `v 0` and `v 1`. -/
@[simp]
theorem commAlternating_apply (v : Fin 2 → M) :
    commAlternating (R := R) v = commBilin (v 0) (v 1) := rfl

/-! ### The antisymmetriser -/

/-- **The antisymmetriser `⋀²(M) ⟶ T²(M)`**, the `R`-linear map carrying `x ∧ y` to
`x ⊗ y - y ⊗ x`. It is `TensorAlgebra.commAlternating` read through the universal property of the
second exterior power. -/
def extTwoToTensor : ⋀[R]^2 M →ₗ[R] gradedPiece R 2 M :=
  exteriorPower.alternatingMapLinearEquiv commAlternating

/-- The antisymmetriser carries the wedge of `v 0` and `v 1` to their commutator. -/
@[simp]
theorem extTwoToTensor_ιMulti (v : Fin 2 → M) :
    extTwoToTensor (exteriorPower.ιMulti R 2 v) = commBilin (v 0) (v 1) :=
  (exteriorPower.alternatingMapLinearEquiv_apply_ιMulti commAlternating v).trans
    (commAlternating_apply v)

/-- The antisymmetriser carries `x ∧ y` to the commutator `commBilin x y`. -/
theorem extTwoToTensor_ιMulti_pair (x y : M) :
    extTwoToTensor (exteriorPower.ιMulti R 2 ![x, y]) = commBilin x y := by
  rw [extTwoToTensor_ιMulti]
  simp

/-- In the tensor algebra, the antisymmetriser carries `x ∧ y` to `ι x * ι y - ι y * ι x`. -/
theorem coe_extTwoToTensor_ιMulti_pair (x y : M) :
    (extTwoToTensor (exteriorPower.ιMulti R 2 ![x, y]) : TensorAlgebra R M) =
      ι R x * ι R y - ι R y * ι R x := by
  rw [extTwoToTensor_ιMulti_pair, coe_commBilin]

/-! ### Exactness at the tensor square -/

/-- The quotient map `T²(M) ⟶ Sym²(M)` kills every commutator `x ⊗ y - y ⊗ x`. -/
theorem symQuot_commBilin (x y : M) : symQuot 2 (commBilin (R := R) x y) = 0 := by
  refine (symQuot_eq_zero_iff 2 _).2 ((mem_symSub_iff _).2 ?_)
  rw [coe_commBilin, map_sub, map_mul, map_mul, mul_comm, sub_self]

/-- The composite `⋀²(M) ⟶ T²(M) ⟶ Sym²(M)` of the antisymmetriser and the quotient map is
zero. -/
theorem symQuot_comp_extTwoToTensor :
    (symQuot (R := R) (M := M) 2) ∘ₗ extTwoToTensor = 0 := by
  refine exteriorPower.linearMap_ext (AlternatingMap.ext fun v => ?_)
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply,
    extTwoToTensor_ιMulti, LinearMap.zero_apply]
  exact symQuot_commBilin _ _

/-- The quotient map `T²(M) ⟶ Sym²(M)` kills the image of every element of `⋀²(M)` under the
antisymmetriser. -/
theorem symQuot_extTwoToTensor (z : ⋀[R]^2 M) : symQuot 2 (extTwoToTensor z) = 0 :=
  LinearMap.congr_fun (symQuot_comp_extTwoToTensor (R := R) (M := M)) z

/-- The degree-two relator submodule is the commutator submodule: in degree two there is a single
adjacent slot pair, and its two outer factors are the degree-zero piece `T⁰(M) = 1`. -/
theorem relDeg_two : relDeg (R := R) (M := M) 2 = commSub R M := by
  have h : gradedPiece R 0 M * commSub R M * gradedPiece R 0 M = commSub R M := by
    rw [show gradedPiece R 0 M = 1 from pow_zero _, Submodule.one_mul, Submodule.mul_one]
  refine le_antisymm (iSup_le fun p => ?_) (le_iSup_of_le ⟨0, by omega⟩ h.ge)
  rw [show (p : ℕ) = 0 from Nat.lt_one_iff.1 p.isLt]
  exact h.le

/-- **The range of the antisymmetriser is the kernel of `T²(M) ⟶ Sym²(M)`.** This is exactness
of `⋀²(M) ⟶ T²(M) ⟶ Sym²(M)` at the middle term; it holds for every module over every
commutative ring. -/
theorem range_extTwoToTensor :
    LinearMap.range (extTwoToTensor (R := R) (M := M)) = LinearMap.ker (symQuot 2) := by
  refine le_antisymm ?_ fun t ht => ?_
  · rintro _ ⟨z, rfl⟩
    exact symQuot_extTwoToTensor z
  · have ht' : (t : TensorAlgebra R M) ∈ relDeg (R := R) (M := M) 2 :=
      mem_relDeg_of_mem_symSub ((symQuot_eq_zero_iff 2 t).1 ht) t.2
    have hle : commSub R M ≤
        Submodule.map (gradedPiece R 2 M).subtype
          (LinearMap.range (extTwoToTensor (R := R) (M := M))) := by
      rw [commSub, Submodule.span_le]
      rintro _ ⟨⟨x, y⟩, rfl⟩
      exact ⟨extTwoToTensor (exteriorPower.ιMulti R 2 ![x, y]), ⟨_, rfl⟩,
        coe_extTwoToTensor_ιMulti_pair x y⟩
    obtain ⟨s, hs, hst⟩ := hle (relDeg_two (R := R) (M := M) ▸ ht')
    rwa [show t = s from Subtype.ext hst.symm]

/-! ### Injectivity on a free module -/

section Free

variable {κ : Type*} [LinearOrder κ]

/-- For a basis `b` of `M` indexed by a linearly ordered type and two indices `i`, `j`, the
linear form on `T²(M)` reading off the coefficient of `bᵢ ⊗ bⱼ`. -/
def tensorTwoCoord (b : Module.Basis κ R M) (i j : κ) : gradedPiece R 2 M →ₗ[R] R :=
  TensorProduct.lift ((LinearMap.mul R R).compl₁₂
      (b.coord i ∘ₗ (gradedPieceOneEquiv (R := R) (M := M)).symm.toLinearMap)
      (b.coord j ∘ₗ (gradedPieceOneEquiv (R := R) (M := M)).symm.toLinearMap)) ∘ₗ
    (mulTwo (R := R) (M := M)).symm.toLinearMap

/-- Under the identification of `T²(M)` with `T¹(M) ⊗ T¹(M)`, the commutator `commBilin x y` is
`x ⊗ y - y ⊗ x`. -/
theorem symm_mulTwo_commBilin (x y : M) :
    (mulTwo (R := R) (M := M)).symm (commBilin x y) =
      gradedPieceOneEquiv x ⊗ₜ[R] gradedPieceOneEquiv (R := R) y -
        gradedPieceOneEquiv y ⊗ₜ[R] gradedPieceOneEquiv (R := R) x := by
  rw [commBilin_apply]
  simp only [altTwo, swapTwo, LinearMap.sub_apply, LinearMap.id_coe, id_eq, map_sub,
    LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, TensorProduct.comm_tmul]

omit [LinearOrder κ] in
/-- The coefficient of `bᵢ ⊗ bⱼ` in `x ⊗ y - y ⊗ x` is `xᵢ yⱼ - yᵢ xⱼ`, where `xᵢ` denotes the
`i`-th coordinate of `x` in the basis `b`. -/
theorem tensorTwoCoord_commBilin (b : Module.Basis κ R M) (i j : κ) (x y : M) :
    tensorTwoCoord b i j (commBilin x y) =
      b.coord i x * b.coord j y - b.coord i y * b.coord j x := by
  simp only [tensorTwoCoord, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    symm_mulTwo_commBilin, map_sub, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply,
    LinearMap.mul_apply', LinearEquiv.symm_apply_apply]

/-- The coefficient of `bᵢ ⊗ bⱼ` in `b_k ⊗ b_l - b_l ⊗ b_k` is
`[k = i][l = j] - [l = i][k = j]`. -/
theorem tensorTwoCoord_commBilin_basis (b : Module.Basis κ R M) (i j k l : κ) :
    tensorTwoCoord b i j (commBilin (b k) (b l)) =
      (if k = i then 1 else 0) * (if l = j then 1 else 0) -
        (if l = i then 1 else 0) * (if k = j then 1 else 0) := by
  rw [tensorTwoCoord_commBilin]
  simp [Module.Basis.coord_apply, Finsupp.single_apply]

/-- The antisymmetriser carries the basis wedge of `⋀²(M)` indexed by a two-element subset `s` to
the commutator of the two basis vectors indexed by `s`, taken in increasing order. -/
theorem extTwoToTensor_ιMulti_family (b : Module.Basis κ R M)
    (s : ↥(Set.powersetCard κ 2)) :
    extTwoToTensor (exteriorPower.ιMulti_family R 2 b s) =
      commBilin (b (Set.powersetCard.ofFinEmbEquiv.symm s 0))
        (b (Set.powersetCard.ofFinEmbEquiv.symm s 1)) := by
  have h : exteriorPower.ιMulti_family R 2 (b : κ → M) s =
      exteriorPower.ιMulti R 2 ((b : κ → M) ∘ Set.powersetCard.ofFinEmbEquiv.symm s) := rfl
  rw [h, extTwoToTensor_ιMulti]
  rfl

/-- The two elements of a two-element subset `s`, listed in increasing order, satisfy
`s₀ < s₁`. -/
theorem lt_ofFinEmbEquiv_symm (s : ↥(Set.powersetCard κ 2)) :
    Set.powersetCard.ofFinEmbEquiv.symm s 0 < Set.powersetCard.ofFinEmbEquiv.symm s 1 :=
  (Set.powersetCard.ofFinEmbEquiv.symm s).lt_iff_lt.2 (Fin.one_pos' (n := 1))

/-- Two two-element subsets with the same smaller element and the same larger element are
equal. -/
theorem eq_of_ofFinEmbEquiv_symm_eq {s t : ↥(Set.powersetCard κ 2)}
    (h0 : Set.powersetCard.ofFinEmbEquiv.symm t 0 = Set.powersetCard.ofFinEmbEquiv.symm s 0)
    (h1 : Set.powersetCard.ofFinEmbEquiv.symm t 1 = Set.powersetCard.ofFinEmbEquiv.symm s 1) :
    t = s :=
  Set.powersetCard.ofFinEmbEquiv.symm.injective
    (RelEmbedding.ext fun k => by
      rcases fin_two_eq_zero_or_one k with rfl | rfl
      · exact h0
      · exact h1)

/-- The coefficient form attached to a two-element finset `s` takes the value `1` on the image of
the wedge of the two basis vectors indexed by `s`, and `0` on the image of every other basis
wedge. -/
theorem tensorTwoCoord_extTwoToTensor_ιMulti_family (b : Module.Basis κ R M)
    (s t : ↥(Set.powersetCard κ 2)) :
    tensorTwoCoord b (Set.powersetCard.ofFinEmbEquiv.symm s 0)
        (Set.powersetCard.ofFinEmbEquiv.symm s 1)
        (extTwoToTensor (exteriorPower.ιMulti_family R 2 b t)) =
      if t = s then 1 else 0 := by
  classical
  rw [extTwoToTensor_ιMulti_family, tensorTwoCoord_commBilin_basis]
  have hs := lt_ofFinEmbEquiv_symm s
  have ht := lt_ofFinEmbEquiv_symm t
  have hcross : (if Set.powersetCard.ofFinEmbEquiv.symm t 1 =
          Set.powersetCard.ofFinEmbEquiv.symm s 0 then (1 : R) else 0) *
      (if Set.powersetCard.ofFinEmbEquiv.symm t 0 =
          Set.powersetCard.ofFinEmbEquiv.symm s 1 then (1 : R) else 0) = 0 := by
    by_cases hA : Set.powersetCard.ofFinEmbEquiv.symm t 1 =
        Set.powersetCard.ofFinEmbEquiv.symm s 0
    · have hB : Set.powersetCard.ofFinEmbEquiv.symm t 0 ≠
          Set.powersetCard.ofFinEmbEquiv.symm s 1 := by
        intro hB
        have h1 : Set.powersetCard.ofFinEmbEquiv.symm s 1 <
            Set.powersetCard.ofFinEmbEquiv.symm s 0 := by
          rw [← hB, ← hA]
          exact ht
        exact absurd (h1.trans hs) (lt_irrefl _)
      rw [ite_eq_right hB, mul_zero]
    · rw [ite_eq_right hA, zero_mul]
  rw [hcross, sub_zero]
  by_cases hst : t = s
  · subst hst
    rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_left rfl, mul_one]
  · rw [ite_eq_right hst]
    by_cases h0 : Set.powersetCard.ofFinEmbEquiv.symm t 0 =
        Set.powersetCard.ofFinEmbEquiv.symm s 0
    · have h1 : Set.powersetCard.ofFinEmbEquiv.symm t 1 ≠
          Set.powersetCard.ofFinEmbEquiv.symm s 1 := fun h1 =>
        hst (eq_of_ofFinEmbEquiv_symm_eq h0 h1)
      rw [ite_eq_right h1, mul_zero]
    · rw [ite_eq_right h0, zero_mul]

/-- The images under the antisymmetriser of the basis wedges `bᵢ ∧ bⱼ`, `i < j`, of `⋀²(M)` are
linearly independent in `T²(M)`. -/
theorem linearIndependent_extTwoToTensor_ιMulti_family (b : Module.Basis κ R M) :
    LinearIndependent R fun s : ↥(Set.powersetCard κ 2) =>
      extTwoToTensor (exteriorPower.ιMulti_family R 2 b s) := by
  classical
  refine LinearIndependent.of_pairwise_dual_eq_zero_one _
    (fun s => tensorTwoCoord b (Set.powersetCard.ofFinEmbEquiv.symm s 0)
      (Set.powersetCard.ofFinEmbEquiv.symm s 1)) (fun s t hst => ?_) fun s => ?_
  · exact (tensorTwoCoord_extTwoToTensor_ιMulti_family b s t).trans
      (ite_eq_right (Ne.symm hst))
  · exact (tensorTwoCoord_extTwoToTensor_ιMulti_family b s s).trans (ite_eq_left rfl)

/-- **The antisymmetriser is injective on a module with a basis indexed by a linearly ordered
type.** -/
theorem injective_extTwoToTensor_of_basis (b : Module.Basis κ R M) :
    Function.Injective (extTwoToTensor (R := R) (M := M)) := by
  have hkey : extTwoToTensor (R := R) (M := M) =
      (b.exteriorPower 2).constr R fun s =>
        extTwoToTensor (exteriorPower.ιMulti_family R 2 b s) :=
    (b.exteriorPower 2).ext fun s => by
      rw [Module.Basis.constr_basis, exteriorPower.basis_apply R 2 b s]
  rw [hkey]
  exact (b.exteriorPower 2).injective_constr_of_linearIndependent
    (linearIndependent_extTwoToTensor_ιMulti_family b)

end Free

/-- **The antisymmetriser `⋀²(M) ⟶ T²(M)` is injective on a free module.** Together with
`TensorAlgebra.range_extTwoToTensor` and the surjectivity of `T²(M) ⟶ Sym²(M)` this makes
`0 ⟶ ⋀²(M) ⟶ T²(M) ⟶ Sym²(M) ⟶ 0` short exact. No invertibility of `2` is used. -/
theorem injective_extTwoToTensor [Module.Free R M] :
    Function.Injective (extTwoToTensor (R := R) (M := M)) := by
  classical
  obtain ⟨κ, b⟩ := Module.Free.exists_basis (R := R) (M := M)
  let _ : LinearOrder κ := linearOrderOfSTO WellOrderingRel
  exact injective_extTwoToTensor_of_basis b

/-! ### Base change -/

section BaseChange

variable {S : Type*} [CommRing S] {N : Type*} [AddCommGroup N] [Module S N]

/-- The antisymmetriser factors the antisymmetriser `altTwo` of the tensor square through the
quotient map `T²(M) ⟶ ⋀²(M)`: both carry a product `x ⊗ y` of degree-one generators to
`x ⊗ y - y ⊗ x`. -/
theorem extTwoToTensor_extQuot (t : gradedPiece R 2 M) :
    extTwoToTensor (extQuot 2 t) = altTwo t := by
  refine two_ext (p := fun t => extTwoToTensor (extQuot 2 t) = altTwo t) ?_ ?_ t
  · intro a b ha hb
    rw [map_add, map_add, map_add, ha, hb]
  · intro x y
    obtain ⟨x₀, rfl⟩ := gradedPieceOneEquiv.surjective x
    obtain ⟨y₀, rfl⟩ := gradedPieceOneEquiv.surjective y
    have hq : extQuot 2 (mulTwo (gradedPieceOneEquiv x₀ ⊗ₜ[R]
        gradedPieceOneEquiv (R := R) y₀)) = exteriorPower.ιMulti R 2 ![x₀, y₀] := by
      refine Subtype.ext ?_
      rw [coe_extQuot, coe_mulTwo, gradedPieceOneEquiv_apply, gradedPieceOneEquiv_apply,
        map_mul, ExteriorAlgebra.algHom_ι, ExteriorAlgebra.algHom_ι,
        exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply]
      simp
    rw [hq, extTwoToTensor_ιMulti]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact commBilin_apply x₀ y₀

/-- **The antisymmetriser commutes with base change.** This is the naturality that makes the
family of sectionwise antisymmetrisers of a presheaf of modules a morphism of presheaves of
modules. -/
theorem extTwoToTensor_powMapₛₗ (φ : R →+* S) (u : M →ₛₗ[φ] N) (w : ⋀[R]^2 M) :
    extTwoToTensor (ExteriorAlgebra.powMapₛₗ 2 φ u w) =
      powMapₛₗ 2 φ u (extTwoToTensor w) := by
  obtain ⟨t, rfl⟩ := surjective_extQuot (R := R) (M := M) 2 w
  rw [ExteriorAlgebra.powMapₛₗ_extQuot, extTwoToTensor_extQuot, extTwoToTensor_extQuot]
  exact Subtype.ext (coe_altTwo_powMapₛₗ φ u t)

end BaseChange

end TensorAlgebra

/-! ### The sectionwise sequence of presheaves of modules -/

namespace PresheafOfModules

section Sectionwise

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  (F : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat))

/-- `TensorAlgebra.extTwoToTensor` with its type spelled at the sections of `extPow 2` and of
`tensorPow 2`. The two types are definitionally equal; the retyping is a separate declaration
for the reason documented in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAlgebraBundle`. -/
def extTwoToTensorApp (X : Cᵒᵖ) :
    (extPow 2 F).obj X →ₗ[(O ⋙ forget₂ _ RingCat).obj X] (tensorPow 2 F).obj X :=
  TensorAlgebra.extTwoToTensor

/-- **The sectionwise antisymmetriser `⋀² ⟶ T²`**, as a morphism of presheaves of modules. -/
def extTwoToTensorHom : extPow 2 F ⟶ tensorPow 2 F where
  app X := ModuleCat.ofHom (extTwoToTensorApp F X)
  naturality {_ _} f := ModuleCat.hom_ext (LinearMap.ext fun z =>
    TensorAlgebra.extTwoToTensor_powMapₛₗ ((O ⋙ forget₂ _ RingCat).map f).hom
      (F.restrictₛₗ f) z)

/-- On sections over `X`, `extTwoToTensorHom F` is the antisymmetriser
`TensorAlgebra.extTwoToTensor`. -/
@[simp]
theorem extTwoToTensorHom_app_apply (X : Cᵒᵖ) (z : (extPow 2 F).obj X) :
    Hom.app (extTwoToTensorHom F) X z = TensorAlgebra.extTwoToTensor z := rfl

/-- The composite `⋀² ⟶ T² ⟶ Sym²` of morphisms of presheaves of modules is zero. -/
theorem extTwoToTensorHom_comp_symQuotHom : extTwoToTensorHom F ≫ symQuotHom F 2 = 0 :=
  hom_ext fun _ => ModuleCat.hom_ext (LinearMap.ext fun z =>
    TensorAlgebra.symQuot_extTwoToTensor z)

/-- **The three-term complex `⋀² ⟶ T² ⟶ Sym²` of presheaves of modules.** -/
def extSymShortComplex :
    ShortComplex (PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat)) :=
  ShortComplex.mk (extTwoToTensorHom F) (symQuotHom F 2) (extTwoToTensorHom_comp_symQuotHom F)

/-- **The complex `⋀² ⟶ T² ⟶ Sym²` of presheaves of modules is exact at the middle term**,
because over every object the range of the antisymmetriser is the kernel of `T² ⟶ Sym²`
(`TensorAlgebra.range_extTwoToTensor`). No hypothesis on `F` is needed. -/
theorem extSymShortComplex_exact : (extSymShortComplex F).Exact := by
  refine exact_of_sectionwise _ fun X t => ⟨fun ht => ?_, fun ht => ?_⟩
  · have hmem : t ∈ LinearMap.range (TensorAlgebra.extTwoToTensor
        (R := (O ⋙ forget₂ _ RingCat).obj X) (M := F.obj X)) := by
      rw [TensorAlgebra.range_extTwoToTensor]
      exact ht
    exact hmem
  · obtain ⟨z, rfl⟩ := ht
    exact TensorAlgebra.symQuot_extTwoToTensor z

/-- The second map `T² ⟶ Sym²` of `extSymShortComplex F` is an epimorphism. -/
instance epi_extSymShortComplex_g : Epi (extSymShortComplex F).g :=
  epi_symQuotHom F 2

end Sectionwise

end PresheafOfModules

/-! ### The two maps of sheaves of modules -/

namespace SheafOfModules

section Sheafify

open PresheafOfModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {G : SheafOfModules.{w} (toRingCat J Osharp)}

/-- **The antisymmetriser `⋀²(F) ⟶ T²(F)` of sheaves of modules**: the sheafification of the
sectionwise antisymmetriser, read through `SheafOfModules.exteriorPowerSheafifyIso` and
`SheafOfModules.tensorPieceSheafifyIso`. This is the map `x ∧ y ↦ x ⊗ y - y ⊗ x`. -/
def exteriorSquareToTensorPiece (A : TensorExteriorSymmetricAlgebras J G) :
    A.exteriorPower 2 ⟶ A.tensor.piece (2 : ℤ) :=
  (exteriorPowerSheafifyIso J A 2).hom ≫
    (PresheafOfModules.moduleSheafification J (𝟙 Osharp.obj)).map
      (extTwoToTensorHom (valPresheaf J G)) ≫
    (tensorPieceSheafifyIso J A 2).inv

/-- **The quotient map `Tⁿ(F) ⟶ Symⁿ(F)` of sheaves of modules**: the sheafification of the
sectionwise quotient map, read through `SheafOfModules.tensorPieceSheafifyIso` and
`SheafOfModules.symmetricPowerSheafifyIso`. This is the symmetric companion of
`SheafOfModules.exteriorPowerQuotHom`. -/
def symmetricPowerQuotHom (A : TensorExteriorSymmetricAlgebras J G) (n : ℕ) :
    A.tensor.piece (n : ℤ) ⟶ A.symmetricPower n :=
  (tensorPieceSheafifyIso J A n).hom ≫
    (PresheafOfModules.moduleSheafification J (𝟙 Osharp.obj)).map
      (symQuotHom (valPresheaf J G) n) ≫
    (symmetricPowerSheafifyIso J A n).inv

/-- **The quotient map onto the symmetric power is an epimorphism**: the sectionwise quotient
map is surjective on sections, hence an epimorphism of presheaves of modules, and sheafification
is a left adjoint. -/
instance epi_symmetricPowerQuotHom (A : TensorExteriorSymmetricAlgebras J G) (n : ℕ) :
    Epi (symmetricPowerQuotHom J A n) := by
  have hadj : (PresheafOfModules.moduleSheafification J (𝟙 Osharp.obj)).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction
      (PresheafOfModules.sheafificationAdjunction (toRingCatMap J (𝟙 Osharp.obj)))
  rw [symmetricPowerQuotHom]
  infer_instance

/-- **The composite `⋀²(F) ⟶ T²(F) ⟶ Sym²(F)` is zero.** -/
theorem exteriorSquareToTensorPiece_comp_symmetricPowerQuotHom
    (A : TensorExteriorSymmetricAlgebras J G) :
    exteriorSquareToTensorPiece J A ≫ symmetricPowerQuotHom J A 2 = 0 := by
  rw [exteriorSquareToTensorPiece, symmetricPowerQuotHom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp_assoc,
    extTwoToTensorHom_comp_symQuotHom, Functor.map_zero, zero_comp, comp_zero]

end Sheafify

end SheafOfModules

end
