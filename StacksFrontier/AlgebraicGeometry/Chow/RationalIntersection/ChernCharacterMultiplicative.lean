module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCharacterKGroup
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.PowerSumTensor
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.RationalTotalClass
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.ChernCharacterVectorBundle
public import StacksCore.Tactic.StacksAttribute

/-!
# The Chern character is a ring map

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `X` be locally of
finite type over `S`. For a finite locally free `𝒪_X`-module `ℰ`, of a rank which need not be
constant, the Chern character is `ch(ℰ) = (ch_p(ℰ))_{p ≥ 0}` with
`ch_p(ℰ) = P_p(ℰ)/p! ∈ A^p(X) ⊗ 𝐐`, an element of the ring
`Stacks.Chow.RationalTotalChowClass C sX = ∏_{p ≥ 0} A^p(X) ⊗ 𝐐`. By
[Stacks, Tag 0F9C](https://stacks.math.columbia.edu/tag/0F9C) it is additive on short exact
sequences, and by [Stacks, Tag 0F9D](https://stacks.math.columbia.edu/tag/0F9D)

  `ch(ℰ ⊗ ℱ) = ch(ℰ) · ch(ℱ)`,

which in degree `m` is `P_m(ℰ ⊗ ℱ)/m! = ∑_{i + j = m} (P_i(ℰ)/i!) (P_j(ℱ)/j!)`, the binomial
coefficient `C(m, i)` of the power-sum identity being absorbed by `m! = C(m, i) i! j!`. Hence
[Stacks, Tag 0FEM](https://stacks.math.columbia.edu/tag/0FEM): the Chern character defines a
ring map

  `ch : K_0(Vect(X)) ⟶ ∏_{p ≥ 0} A^p(X) ⊗ 𝐐`,

the unique one sending `[ℰ]` to `ch(ℰ)`; its underlying additive map is
`Stacks.Chow.chernCharacterVectorBundle`.

The cap action of the ring `∏_p A^p(X) ⊗ 𝐐` on `CH_*(X) ⊗ 𝐐 = ⨁_k CH_k(X) ⊗ 𝐐`, `c ↦ ∑_p c_p ∩ -`,
is multiplicative as soon as `δ_{X/S}` is bounded below: in degree `p` the product of classes is
the composite of their cap operations, `(c d)_p ∩ - = ∑_{i + j = p} c_i ∩ (d_j ∩ -)`, by the
definition of the product of Chow cohomology classes (Stacks 0B75), and the bound makes the sums
over `p` finite on each `CH_k(X) ⊗ 𝐐`. Composing with the Chern character,
`ch(α β) ∩ - = ch(α) ∩ (ch(β) ∩ -)` for `α, β ∈ K_0(Vect(X))`.

## Main definitions

* `Stacks.Chow.rationalTotalChernCharacter` — `ch(ℰ) ∈ ∏_p A^p(X) ⊗ 𝐐`.
* `Stacks.Chow.rationalTotalChernCharacterRingHom` — the ring map
  `ch : K_0(Vect(X)) ⟶ ∏_p A^p(X) ⊗ 𝐐`.

## Main results

* `Stacks.Chow.rationalTotalChernCharacter_sheafTensor` — **Stacks 0F9D** for the Chern character.
* `Stacks.Chow.existsUnique_ringHom_chernCharacter` — **Stacks 0FEM**.
* `Stacks.Chow.rationalChowCap_mul_apply` — `(c d)_p ∩ - = ∑_{i + j = p} c_i ∩ (d_j ∩ -)`.
* `Stacks.Chow.totalRationalChowCap_mul`, `Stacks.Chow.totalRationalChowCap_one` — the cap
  action is multiplicative and unital, for `δ_{X/S}` bounded below.
* `Stacks.Chow.chernCharacterCap_mul`, `Stacks.Chow.rationalChernCharacterCap_mul` —
  `ch(α β) ∩ - = ch(α) ∩ (ch(β) ∩ -)`, for `δ_{X/S}` bounded below.

## References

* [Stacks Project, Tag 0FEM](https://stacks.math.columbia.edu/tag/0FEM)
* [Stacks Project, Tag 0F9D](https://stacks.math.columbia.edu/tag/0F9D)
* [Stacks Project, Tag 0F9C](https://stacks.math.columbia.edu/tag/0F9C)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0FEX](https://stacks.math.columbia.edu/tag/0FEX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Finset
open Stacks.SheafOfModules.Tensor (sheafTensor)
open scoped TensorProduct

universe u

namespace Stacks.Chow

open RationalTotalChowClass

/-! ### The Chern character of a module -/

section Module

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **The Chern character `ch(ℰ) ∈ ∏_{p ≥ 0} A^p(X) ⊗ 𝐐`** of a finite locally free module of
arbitrary rank: the family of the `ch_p(ℰ) = P_p(ℰ)/p!`. -/
def rationalTotalChernCharacter (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    RationalTotalChowClass C sX :=
  fun p ↦ chernCharacterOfFiniteLocallyFree C sX E p

/-- The degree-`p` component of `ch(ℰ)` is `ch_p(ℰ)`. -/
theorem rationalTotalChernCharacter_apply (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (p : ℕ) :
    rationalTotalChernCharacter C sX E p = chernCharacterOfFiniteLocallyFree C sX E p :=
  rfl

/-- The Chern character of a module is that of its class in `K_0(Vect(X))`. -/
theorem chernCharacterVectorBundle_classOf_eq (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    ofFamily (chernCharacterVectorBundle C sX (VectorBundleKZero.classOf X E)) =
      rationalTotalChernCharacter C sX E :=
  ext fun p ↦ chernCharacterVectorBundle_classOf C sX E p

/-- **Stacks 0F9C for the Chern character**: `ch(ℰ) = ch(ℰ₁) + ch(ℰ₂)` for a short exact
sequence `0 ⟶ ℰ₁ ⟶ ℰ ⟶ ℰ₂ ⟶ 0` of finite locally free modules. -/
theorem rationalTotalChernCharacter_eq_add_of_shortExact (S : ShortComplex X.Modules)
    (hS : S.ShortExact) [h₁ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₁]
    [h₃ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₃] :
    haveI := GenuineChern.isFiniteLocallyFree_of_shortExact S hS h₁ h₃
    rationalTotalChernCharacter C sX S.X₂ =
      rationalTotalChernCharacter C sX S.X₁ + rationalTotalChernCharacter C sX S.X₃ :=
  ext fun p ↦ chernCharacterOfFiniteLocallyFree_eq_add_of_shortExact C sX S hS p

/-- A lift of `ch(ℰ)` to `𝐐 ⊗ ∏_q A^q(X)` correct up to degree `m`: `∑_{p ≤ m} P_p(ℰ)/p!`. -/
theorem rationalComponent_sum_powerSum (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] {k m : ℕ} (hk : k ≤ m) :
    RationalTotalChowClass.rationalComponent k (∑ p ∈ range (m + 1),
        ((Nat.factorial p : ℚ)⁻¹) ⊗ₜ[ℤ] powerSumOfFiniteLocallyFree C sX E p) =
      rationalTotalChernCharacter C sX E k := by
  rw [map_sum, Finset.sum_eq_single_of_mem k (mem_range.mpr (Nat.lt_succ_of_le hk))]
  · rfl
  · intro p _ hp
    rw [RationalTotalChowClass.rationalComponent_tmul,
      isHomogeneous_powerSumOfFiniteLocallyFree C sX E p k (Ne.symm hp), TensorProduct.tmul_zero]

variable (E F : X.Modules) [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
  [hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F]

/-- **Stacks 0F9D for the Chern character**: `ch(ℰ ⊗ ℱ) = ch(ℰ) · ch(ℱ)` in
`∏_{p ≥ 0} A^p(X) ⊗ 𝐐`, for finite locally free modules of arbitrary ranks.

In degree `m` both sides are computed on the lifts `∑_{p ≤ m} P_p/p!` of the two Chern characters
to `𝐐 ⊗ ∏_q A^q(X)` (`Stacks.Chow.RationalTotalChowClass.mul_apply_eq`); `P_p(ℰ) P_q(ℱ)` is
homogeneous of degree `p + q`, and the identity is
`Stacks.Chow.powerSumOfFiniteLocallyFree_sheafTensor` divided by `m!`. -/
@[stacks 0F9D "the Chern character form ch(E_1 tensor E_2) = ch(E_1) ch(E_2), for finite locally \
free E_1, E_2 of arbitrary ranks, with no further hypothesis, in the ring \
Stacks.Chow.RationalTotalChowClass C sX = prod over p >= 0 of A^p(X) tensor Q with its Cauchy \
product; ch(E) is the family of the ch_p(E) = P_p(E)/p!"]
theorem rationalTotalChernCharacter_sheafTensor :
    haveI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (R := X.ringCatSheaf) _ :=
        isFiniteLocallyFree_tensor hE hF
    rationalTotalChernCharacter C sX (((sheafTensor X.sheaf).obj E).obj F) =
      rationalTotalChernCharacter C sX E * rationalTotalChernCharacter C sX F := by
  refine ext fun m ↦ ?_
  rw [mul_apply_eq (fun k hk ↦ rationalComponent_sum_powerSum C sX E hk)
    (fun k hk ↦ rationalComponent_sum_powerSum C sX F hk), Finset.sum_mul_sum, map_sum]
  simp only [Algebra.TensorProduct.tmul_mul_tmul, map_sum,
    RationalTotalChowClass.rationalComponent_tmul]
  refine (congrArg (fun z ↦ ((Nat.factorial m : ℚ)⁻¹) ⊗ₜ[ℤ] z)
    (powerSumClassOfFiniteLocallyFree_sheafTensor C sX E F m)).trans ?_
  rw [TensorProduct.tmul_sum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j ↦ ((Nat.factorial m : ℚ)⁻¹) ⊗ₜ[ℤ] (((m.choose i : ℕ) : ℤ) •
        (powerSumOfFiniteLocallyFree C sX E i * powerSumOfFiniteLocallyFree C sX F j) m))]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have him : i ≤ m := mem_range_succ_iff.mp hi
  rw [Finset.sum_eq_single_of_mem (m - i) (mem_range.mpr (by omega))]
  · rw [← TensorProduct.smul_tmul, zsmul_eq_mul, Int.cast_natCast]
    congr 1
    have hi : (Nat.factorial i : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
    have hj : (Nat.factorial (m - i) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    rw [Nat.cast_choose ℚ him]
    field_simp
  · intro j _ hj
    rw [((isHomogeneous_powerSumOfFiniteLocallyFree C sX E i).mul
      (isHomogeneous_powerSumOfFiniteLocallyFree C sX F j)) m (by omega),
      TensorProduct.tmul_zero]

/-- `ch(𝒪_X) = 1`, for any module isomorphic to `𝒪_X`. -/
theorem rationalTotalChernCharacter_of_iso_unit (M : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M 1]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M]
    (e : M ≅ SheafOfModules.unit X.ringCatSheaf) :
    rationalTotalChernCharacter C sX M = 1 := by
  refine ext fun p ↦ ?_
  rw [rationalTotalChernCharacter_apply, chernCharacterOfFiniteLocallyFree,
    powerSumClassOfFiniteLocallyFree, one_apply]
  rcases eq_or_ne p 0 with rfl | hp
  · rw [powerSumOfFiniteLocallyFree_eq_powerSumTotal C sX M 1, powerSumTotal_zero, Nat.cast_one,
      Nat.factorial_zero, Nat.cast_one, inv_one]
    rfl
  · rw [powerSumOfFiniteLocallyFree_eq_zero_of_iso_unit C sX M e hp, TotalChowClass.zero_apply,
      TensorProduct.tmul_zero]
    show (0 : rationalChowCohomologyComponent C _ sX p) =
      (1 : ℚ) ⊗ₜ[ℤ] (1 : TotalChowClass C sX) p
    rw [TotalChowClass.one_apply_of_ne hp, TensorProduct.tmul_zero]

end Module

/-! ### Stacks 0FEM -/

section RingHom

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- The Chern character of a module, extended by zero off the finite locally free modules: the
Chern character of its class in `K_0(Vect(X))`. -/
def chernCharacterOfClass (M : X.Modules) : RationalTotalChowClass C sX :=
  ofFamily (chernCharacterVectorBundle C sX (VectorBundleKZero.classOf X M))

/-- On a finite locally free module, the Chern character of its class is its Chern character. -/
theorem chernCharacterOfClass_eq (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    chernCharacterOfClass C sX E = rationalTotalChernCharacter C sX E :=
  chernCharacterVectorBundle_classOf_eq C sX E

/-- The Chern character, extended by zero, satisfies the hypotheses of
`AlgebraicGeometry.VectorBundleKZero.existsUnique_ringHom_of_tensorMultiplicative`: it vanishes
off the finite locally free modules, it is additive by Stacks 0F9C, multiplicative by
Stacks 0F9D (`Stacks.Chow.rationalTotalChernCharacter_sheafTensor`), and `ch(𝒪_X) = 1`. -/
theorem existsUnique_ringHom_chernCharacterOfClass :
    ∃! φ : VectorBundleKZero X →+* RationalTotalChowClass C sX,
      ∀ M : X.Modules, Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u}
        (R := X.ringCatSheaf) M → φ (VectorBundleKZero.classOf X M) =
          chernCharacterOfClass C sX M := by
  refine VectorBundleKZero.existsUnique_ringHom_of_tensorMultiplicative X
    (chernCharacterOfClass C sX) (fun M hM ↦ ?_) (fun f g w hE hF hG hf hg hfg ↦ ?_)
    (fun M N hM hN ↦ ?_) ?_
  · rw [chernCharacterOfClass, VectorBundleKZero.classOf_eq_zero_of_not_isFiniteLocallyFree M hM,
      map_zero, map_zero]
  · rw [chernCharacterOfClass, chernCharacterOfClass, chernCharacterOfClass,
      VectorBundleKZero.classOf_shortExact f g w hE hF hG hfg, map_add, map_add]
  · have := hM
    have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (R := X.ringCatSheaf) _ :=
        isFiniteLocallyFree_tensor (inferInstance : SheafOfModules.IsFiniteLocallyFree M)
      (inferInstance : SheafOfModules.IsFiniteLocallyFree N)
    refine (chernCharacterOfClass_eq C sX (((sheafTensor X.sheaf).obj M).obj N)).trans
      ((rationalTotalChernCharacter_sheafTensor C sX M N).trans ?_)
    rw [chernCharacterOfClass_eq, chernCharacterOfClass_eq]
  · have := SheafOfModules.isFiniteLocallyFreeOfRank_unit X
    have := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
      (SheafOfModules.unit X.ringCatSheaf) 1
    exact (chernCharacterOfClass_eq C sX _).trans
      (rationalTotalChernCharacter_of_iso_unit C sX _ (Iso.refl _))

/-- The ring map of `Stacks.Chow.existsUnique_ringHom_chernCharacterOfClass` has the Chern
character `Stacks.Chow.chernCharacterVectorBundle` as its underlying function. -/
theorem exists_ringHom_eq_chernCharacterVectorBundle :
    ∃ φ : VectorBundleKZero X →+* RationalTotalChowClass C sX,
      ∀ a, φ a = ofFamily (chernCharacterVectorBundle C sX a) := by
  obtain ⟨φ, hφ, -⟩ := existsUnique_ringHom_chernCharacterOfClass C sX
  have h : φ.toAddMonoidHom =
      (ofFamily (sX := sX)).toLinearMap.toAddMonoidHom.comp (chernCharacterVectorBundle C sX) :=
    VectorBundleKZero.addHom_ext fun M hM ↦ hφ M hM
  exact ⟨φ, fun a ↦ DFunLike.congr_fun h a⟩

/-- **The Chern character `ch : K_0(Vect(X)) ⟶ ∏_{p ≥ 0} A^p(X) ⊗ 𝐐`, as a ring map.** Its
underlying function is `Stacks.Chow.chernCharacterVectorBundle`; it is multiplicative and unital
because it is the ring map of `Stacks.Chow.existsUnique_ringHom_chernCharacterOfClass`. -/
def rationalTotalChernCharacterRingHom : VectorBundleKZero X →+* RationalTotalChowClass C sX where
  toFun a := ofFamily (chernCharacterVectorBundle C sX a)
  map_zero' := by rw [map_zero, map_zero]
  map_add' a b := by rw [map_add, map_add]
  map_one' := by
    obtain ⟨φ, hφ⟩ := exists_ringHom_eq_chernCharacterVectorBundle C sX
    rw [← hφ, map_one]
  map_mul' a b := by
    obtain ⟨φ, hφ⟩ := exists_ringHom_eq_chernCharacterVectorBundle C sX
    rw [← hφ, ← hφ, ← hφ, map_mul]

/-- The ring map `Stacks.Chow.rationalTotalChernCharacterRingHom` is the Chern character
`Stacks.Chow.chernCharacterVectorBundle`. -/
theorem rationalTotalChernCharacterRingHom_apply (a : VectorBundleKZero X) :
    rationalTotalChernCharacterRingHom C sX a = ofFamily (chernCharacterVectorBundle C sX a) :=
  rfl

/-- `ch([ℰ]) = ch(ℰ)`. -/
theorem rationalTotalChernCharacterRingHom_classOf (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    rationalTotalChernCharacterRingHom C sX (VectorBundleKZero.classOf X E) =
      rationalTotalChernCharacter C sX E :=
  chernCharacterVectorBundle_classOf_eq C sX E

/-- **Stacks 0FEM.** The Chern character defines a canonical ring map

  `ch : K_0(Vect(X)) ⟶ ∏_{i ≥ 0} A^i(X) ⊗ 𝐐`:

there is a unique ring homomorphism sending the class of every finite locally free `𝒪_X`-module
`ℰ`, of arbitrary rank, to its Chern character `ch(ℰ) = (P_p(ℰ)/p!)_{p ≥ 0}`. It is
`Stacks.Chow.rationalTotalChernCharacterRingHom`. -/
@[stacks 0FEM "the remark as stated: the unique ring map K_0(Vect(X)) -> prod over i >= 0 of \
A^i(X) tensor Q sending [E] to ch(E), for every X locally of finite type over S, with no further \
hypothesis; the target is the ring Stacks.Chow.RationalTotalChowClass C sX (Cauchy product of the \
products A^i(X) x A^j(X) -> A^{i+j}(X) of Stacks 0B75, tensored with Q), ch(E) is \
Stacks.Chow.rationalTotalChernCharacter (components P_p(E)/p!, E of arbitrary rank), and the map \
is Stacks.Chow.rationalTotalChernCharacterRingHom; additivity is Stacks 0F9C and multiplicativity \
Stacks 0F9D, both proved"]
theorem existsUnique_ringHom_chernCharacter :
    ∃! φ : VectorBundleKZero X →+* RationalTotalChowClass C sX,
      ∀ (E : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E],
        φ (VectorBundleKZero.classOf X E) = rationalTotalChernCharacter C sX E := by
  refine ⟨rationalTotalChernCharacterRingHom C sX,
    fun E _ ↦ rationalTotalChernCharacterRingHom_classOf C sX E, fun ψ hψ ↦ ?_⟩
  refine (existsUnique_ringHom_chernCharacterOfClass C sX).unique (fun M hM ↦ ?_)
    (fun M hM ↦ rfl)
  rw [hψ M, chernCharacterOfClass_eq]

end RingHom

/-! ### The cap action of a product -/

section Cap

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

local notation "CHQ" => DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sX j

local notation "Gy" => gysinSystemOfInvertible C

/-- **The cap operation of a product of total classes**: `(c d)_p ∩ α` is
`∑_{j ≤ p} c_{p-j} ∩ (d_j ∩ α)` in `CH_*(X) ⊗ 𝐐`, for every rational coefficient. This is the
definition of the product of Chow cohomology classes as the composite of bivariant classes
(Stacks 0B75), read on the test scheme `𝟙 X`. -/
theorem rationalChowCap_tmul_mul_apply (c d : TotalChowClass C sX) (r r' : ℚ) (p : ℕ) :
    rationalChowCap C Gy sX p ((r * r') ⊗ₜ[ℤ] (c * d) p) =
      ∑ j ∈ range (p + 1), rationalChowCap C Gy sX ((p - j : ℕ) : ℤ) (r ⊗ₜ[ℤ] c (p - j)) *
        rationalChowCap C Gy sX (j : ℤ) (r' ⊗ₜ[ℤ] d j) := by
  refine rationalChowHomology_linearMap_ext C sX fun k s α ↦ ?_
  have hcap : ∀ (i : ℕ) (b : TotalChowClass C sX) (l : ℤ) (y : chowGroup C sX l),
      chowGroupCongr C (Category.id_comp sX).symm (l - i) (chowCohomologyCap C Gy sX i (b i) l y) =
        b.op (𝟙 X) l i (chowGroupCongr C (Category.id_comp sX).symm l y) :=
    fun i b l y ↦ eq_of_heq ((chowGroupCongr_heq _ _ _ _).trans
      (chowCohomologyCap_heq_idRule_ofGysinSystem C _ sX i (b i) l y))
  have hsymm : ∀ (l : ℤ) (x : chowGroup C (𝟙 X ≫ sX) l),
      (chowGroupCongr C (Category.id_comp sX).symm l).symm x ≍ x := fun l x ↦ by
    refine (chowGroupCongr_heq C (Category.id_comp sX).symm l _).symm.trans ?_
    rw [AddEquiv.apply_symm_apply]
  have hsum : chowCohomologyCap C Gy sX p ((c * d) p) k α =
      ∑ j ∈ range (p + 1), (chowGroupCongr C (Category.id_comp sX).symm (k - p)).symm
        (convolveTerm (c.op (𝟙 X)) (d.op (𝟙 X)) k p j
          (chowGroupCongr C (Category.id_comp sX).symm k α)) := by
    rw [← map_sum, ← gradedCap_mul_apply, ← TotalChowClass.op_mul, ← hcap,
      AddEquiv.symm_apply_apply]
  rw [LinearMap.sum_apply, rationalChowCap_of_tmul, hsum, TensorProduct.tmul_sum, map_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hjp : j ≤ p := mem_range_succ_iff.mp hj
  rw [Module.End.mul_apply, rationalChowCap_of_tmul, rationalChowCap_of_tmul,
    show r * r' * s = r * (r' * s) by ring]
  refine of_tmul_eq_of_tmul_of_heq C sX (by omega) _ ?_
  refine (hsymm _ _).trans ?_
  rw [convolveTerm_of_le _ _ _ hjp, capTo_def, ← hcap j d k α, ← hcap (p - j) c (k - j)]
  exact (gradedDegreeCast_heq _ _).trans (chowGroupCongr_heq _ _ _ _)

/-- **The cap operation of a product in `∏_p A^p(X) ⊗ 𝐐`**:
`(c d)_p ∩ - = ∑_{j ≤ p} c_{p-j} ∩ (d_j ∩ -)` on `CH_*(X) ⊗ 𝐐`. Both sides are computed on the
lifts of `c` and `d` below degree `p` to `𝐐 ⊗ ∏_q A^q(X)`, and are biadditive in the lifts; on
pure tensors the identity is `Stacks.Chow.rationalChowCap_tmul_mul_apply`. -/
theorem rationalChowCap_mul_apply (c d : RationalTotalChowClass C sX) (p : ℕ) :
    rationalChowCap C Gy sX p ((c * d) p) =
      ∑ j ∈ range (p + 1), rationalChowCap C Gy sX ((p - j : ℕ) : ℤ) (c (p - j)) *
        rationalChowCap C Gy sX (j : ℤ) (d j) := by
  have key : ∀ x y : ℚ ⊗[ℤ] TotalChowClass C sX,
      rationalChowCap C Gy sX p (RationalTotalChowClass.rationalComponent p (x * y)) =
        ∑ j ∈ range (p + 1), rationalChowCap C Gy sX ((p - j : ℕ) : ℤ)
            (RationalTotalChowClass.rationalComponent (p - j) x) *
          rationalChowCap C Gy sX (j : ℤ) (RationalTotalChowClass.rationalComponent j y) := by
    intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp only [zero_mul, map_zero, Finset.sum_const_zero]
    | add x x' hx hx' =>
      simp only [add_mul, map_add, hx, hx', Finset.sum_add_distrib]
    | tmul r c =>
      induction y using TensorProduct.induction_on with
      | zero => simp only [mul_zero, map_zero, Finset.sum_const_zero]
      | add y y' hy hy' =>
        simp only [mul_add, map_add, hy, hy', Finset.sum_add_distrib]
      | tmul r' d =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, RationalTotalChowClass.rationalComponent_tmul,
          rationalChowCap_tmul_mul_apply]
        rfl
  rw [mul_apply, key]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hjp : j ≤ p := mem_range_succ_iff.mp hj
  rw [rationalComponent_truncatedLift p c (Nat.sub_le p j),
    rationalComponent_truncatedLift p d hjp]

/-- **The cap action of `∏_p A^p(X) ⊗ 𝐐` on `CH_*(X) ⊗ 𝐐` is multiplicative**, for `δ_{X/S}`
bounded below by `lo`: `(c d) ∩ - = c ∩ (d ∩ -)`, where `c ∩ - = ∑_p c_p ∩ -`.

On `CH_k(X) ⊗ 𝐐` with `N ≥ k - lo` both sides are sums over `p, j ≤ N` of `c_p ∩ (d_j ∩ -)`:
the left one over `p + j ≤ N` (`Stacks.Chow.rationalChowCap_mul_apply`), the right one over all
`p, j ≤ N`, and the terms with `p + j > N` vanish, landing in `CH_{k-p-j}(X) = 0`. -/
theorem totalRationalChowCap_mul (lo : ℤ)
    (hlo : ∀ x : X, lo ≤ relativeDimension C.dimensionFunction sX x)
    (c d : RationalTotalChowClass C sX) :
    totalRationalChowCap C Gy sX (ofFamily.symm (c * d)) =
      totalRationalChowCap C Gy sX (ofFamily.symm c) *
        totalRationalChowCap C Gy sX (ofFamily.symm d) := by
  refine DirectSum.linearMap_ext ℚ fun k ↦ LinearMap.ext fun t ↦ ?_
  set N := (k - lo).toNat
  have hN : k - lo ≤ N := Int.self_le_toNat (k - lo)
  set v := DirectSum.lof ℚ ℤ (fun j : ℤ ↦ ℚ ⊗[ℤ] chowGroup C sX j) k t
  set f : ℕ → ℕ → CHQ := fun q j ↦
    rationalChowCap C Gy sX (q : ℤ) (c q) (rationalChowCap C Gy sX (j : ℤ) (d j) v)
  -- the terms of total degree above `N` vanish
  have hf : ∀ q j, N < q + j → f q j = 0 := by
    intro q j hqj
    show rationalChowCap C Gy sX (q : ℤ) (c q) (rationalChowCap C Gy sX (j : ℤ) (d j) v) = 0
    rw [rationalChowCap_lof]
    refine rationalChowCap_lof_eq_zero C Gy sX q _ (k - j) _ fun x hx ↦ ?_
    have := hlo x
    omega
  rw [LinearMap.comp_apply, LinearMap.comp_apply, Module.End.mul_apply,
    totalRationalChowCap_lof_eq_sum_range C Gy sX lo hlo _ k t N hN,
    totalRationalChowCap_lof_eq_sum_range C Gy sX lo hlo _ k t N hN, map_sum]
  -- the left side: the sum over `p + j ≤ N`
  have hl : ∑ n ∈ range (N + 1), rationalChowCap C Gy sX (n : ℤ) ((ofFamily.symm (c * d)) n) v =
      ∑ j ∈ range (N + 1), ∑ q ∈ range (N + 1 - j), f q j := by
    simp only [ofFamily_symm_apply, rationalChowCap_mul_apply, LinearMap.sum_apply,
      Module.End.mul_apply]
    exact Finset.sum_range_diag_flip (N + 1) fun j q ↦ f q j
  -- the right side: the sum over all `p, j ≤ N`
  have hr : ∀ j ∈ range (N + 1),
      totalRationalChowCap C Gy sX (ofFamily.symm c)
          (rationalChowCap C Gy sX (j : ℤ) ((ofFamily.symm d) j) v) =
        ∑ q ∈ range (N + 1 - j), f q j := by
    intro j hj
    rw [ofFamily_symm_apply, rationalChowCap_lof,
      totalRationalChowCap_lof_eq_sum_range C Gy sX lo hlo _ (k - j) _ N (by omega),
      ← rationalChowCap_lof]
    refine (Finset.sum_subset (Finset.range_subset_range.mpr (Nat.sub_le _ _))
      fun q hq hq' ↦ ?_).symm
    refine hf q j ?_
    rw [Finset.mem_range] at hq'
    omega
  rw [hl, Finset.sum_congr rfl hr]

end Cap

/-! ### `ch(α β) ∩ - = ch(α) ∩ (ch(β) ∩ -)` -/

section ChernCharacterCap

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **`ch(α β) ∩ - = ch(α) ∩ (ch(β) ∩ -)`** on `CH_*(X) ⊗ 𝐐`, for `α, β ∈ K_0(Vect(X))` and
`δ_{X/S}` bounded below by `lo`: the Chern character is a ring map (Stacks 0FEM,
`Stacks.Chow.rationalTotalChernCharacterRingHom`) and the cap action is multiplicative
(`Stacks.Chow.totalRationalChowCap_mul`). -/
theorem chernCharacterCap_mul (lo : ℤ)
    (hlo : ∀ x : X, lo ≤ relativeDimension C.dimensionFunction sX x)
    (a b : VectorBundleKZero X) :
    chernCharacterCap C sX (a * b) = chernCharacterCap C sX a * chernCharacterCap C sX b := by
  have h : ∀ a, chernCharacterCap C sX a = totalRationalChowCap C (gysinSystemOfInvertible C) sX
      (ofFamily.symm (rationalTotalChernCharacterRingHom C sX a)) := fun _ ↦ rfl
  rw [h, h, h, map_mul, totalRationalChowCap_mul C sX lo hlo]

/-- **The cap action of `1 ∈ ∏_p A^p(X) ⊗ 𝐐` is the identity**: `1` is the Chern character of
`𝒪_X` (`Stacks.Chow.rationalTotalChernCharacterRingHom` is unital), whose cap action is the
identity (`Stacks.Chow.chernCharacterCap_one`). -/
theorem totalRationalChowCap_one :
    totalRationalChowCap C (gysinSystemOfInvertible C) sX
      (ofFamily.symm (1 : RationalTotalChowClass C sX)) = 1 := by
  rw [← map_one (rationalTotalChernCharacterRingHom C sX)]
  exact chernCharacterCap_one C sX

/-- **`ch(x y) ∩ - = ch(x) ∩ (ch(y) ∩ -)`** on `CH_*(X) ⊗ 𝐐`, for `x, y ∈ K_0(Vect(X)) ⊗ 𝐐` and
`δ_{X/S}` bounded below by `lo`. -/
theorem rationalChernCharacterCap_mul (lo : ℤ)
    (hlo : ∀ x : X, lo ≤ relativeDimension C.dimensionFunction sX x)
    (x y : ℚ ⊗[ℤ] VectorBundleKZero X) :
    rationalChernCharacterCap C sX (x * y) =
      rationalChernCharacterCap C sX x * rationalChernCharacterCap C sX y := by
  induction x using TensorProduct.induction_on with
  | zero => rw [zero_mul, map_zero, zero_mul]
  | add x x' hx hx' => rw [add_mul, map_add, map_add, hx, hx', add_mul]
  | tmul r a =>
    induction y using TensorProduct.induction_on with
    | zero => rw [mul_zero, map_zero, mul_zero]
    | add y y' hy hy' => rw [mul_add, map_add, map_add, hy, hy', mul_add]
    | tmul r' b =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, rationalChernCharacterCap_tmul,
        rationalChernCharacterCap_tmul, rationalChernCharacterCap_tmul,
        chernCharacterCap_mul C sX lo hlo, smul_mul_smul_comm]

end ChernCharacterCap


end Stacks.Chow

end
