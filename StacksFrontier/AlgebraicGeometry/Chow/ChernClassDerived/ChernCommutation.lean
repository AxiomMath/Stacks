module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.CommonRankRefinement
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.EnvelopeUniqueness
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TotalChernWhitney

/-!
# The unit degree-zero component, and the commutation, of derived Chern classes

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `Y` be locally of
finite type over `S`, let `𝓔^•` be a locally bounded complex of finite locally free
`𝒪_Y`-modules and let `E` be an object of `D(𝒪_Y)` whose Chern classes are defined. The total
Chern classes `c(𝓔^•)` of Stacks 0ESZ (`Stacks.Chow.complexChern`) and `c(E)` of Stacks 0F9E (2)
(`Stacks.Chow.perfectChernClass`) live in the ring `Stacks.Chow.TotalChowClass`, whose
multiplication is composition of bivariant classes, Stacks 0FE0. This file proves:

* their degree-`0` component is the class `1 ∈ A^0(Y)`, so they are of the shape
  `1 + c_1 + c_2 + ⋯` and in particular units; and
* their homogeneous components commute with one another, which is Stacks 0FAC (the Chern
  classes of perfect objects commute) read on total classes.

## Main definitions

* `Stacks.Chow.CommuteHomComponent` — two total classes all of whose homogeneous components
  commute.

## Main results

* `Stacks.Chow.TotalChowClass.mul_apply_zero_eq_one`,
  `Stacks.Chow.TotalChowClass.inv_apply_zero_eq_one`,
  `Stacks.Chow.TotalChowClass.zpow_apply_zero_eq_one`,
  `Stacks.Chow.TotalChowClass.val_listProd_apply_zero` — the degree-`0` component `1 ∈ A^0(Y)` is
  preserved by products, by inversion of units, by integral powers with exponent `±1` and by
  products of lists of units.
* `Stacks.Chow.TotalChowClass.homComponent_mul` — the homogeneous components of a product of
  total classes are the convolution of the components of the factors.
* `Stacks.Chow.TotalChowClass.homComponent_inv_eq` — Newton's recursion for the components of
  the inverse of a unit of shape `1 + c_1 + c_2 + ⋯`.
* `Stacks.Chow.totalChern_apply_zero` — `c_0(ℰ) = 1` for a finite locally free module.
* `Stacks.Chow.complexChern_apply_zero`, `Stacks.Chow.perfectChernClass_apply_zero` — `c_0 = 1`
  for a locally bounded complex of finite locally free modules and for an object whose Chern
  classes are defined.
* `Stacks.Chow.CommuteHomComponent.mul_right`, `Stacks.Chow.CommuteHomComponent.inv_right`,
  `Stacks.Chow.CommuteHomComponent.zpow_right`,
  `Stacks.Chow.CommuteHomComponent.listProd_right`,
  `Stacks.Chow.CommuteHomComponent.of_res` — the closure properties of componentwise
  commutation.
* `Stacks.Chow.commute_homComponent_complexChern`,
  `Stacks.Chow.commute_homComponent_perfectChernClass` — **Stacks 0FAC** on total classes: the
  homogeneous components of the total Chern classes of two locally bounded complexes, and of two
  objects whose Chern classes are defined, commute.

## References

* [Stacks Project, Tag 0FAC](https://stacks.math.columbia.edu/tag/0FAC)
* [Stacks Project, Tag 02UA](https://stacks.math.columbia.edu/tag/02UA)
* [Stacks Project, Tag 0ESZ](https://stacks.math.columbia.edu/tag/0ESZ)
* [Stacks Project, Tag 0F9E](https://stacks.math.columbia.edu/tag/0F9E)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 0GUC](https://stacks.math.columbia.edu/tag/0GUC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Finset

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

namespace TotalChowClass

variable {C : ChowSituation.{u}} {Y : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]

/-- The degree-`0` component of a product depends on the factors only through their degree-`0`
components. -/
theorem mul_apply_zero_congr {a b a' b' : TotalChowClass C sY} (ha : a 0 = a' 0)
    (hb : b 0 = b' 0) : (a * b) 0 = (a' * b') 0 := by
  rw [mul_apply, mul_apply, Finset.sum_range_one, Finset.sum_range_one]
  simp only [mulTerm, le_refl, dite_eq_left, ha, hb]

/-- A product of two total classes of degree-`0` component `1 ∈ A^0(Y)` again has degree-`0`
component `1`. -/
theorem mul_apply_zero_eq_one {a b : TotalChowClass C sY}
    (ha : a 0 = (1 : TotalChowClass C sY) 0) (hb : b 0 = (1 : TotalChowClass C sY) 0) :
    (a * b) 0 = (1 : TotalChowClass C sY) 0 := by
  rw [mul_apply_zero_congr ha hb, one_mul]

/-- The inverse of a unit whose degree-`0` component is `1 ∈ A^0(Y)` again has degree-`0`
component `1`. -/
theorem inv_apply_zero_eq_one {u : (TotalChowClass C sY)ˣ}
    (hu : (u : TotalChowClass C sY) 0 = (1 : TotalChowClass C sY) 0) :
    ((u⁻¹ : (TotalChowClass C sY)ˣ) : TotalChowClass C sY) 0 =
      (1 : TotalChowClass C sY) 0 := by
  have h := mul_apply_zero_congr (a := (u : TotalChowClass C sY))
    (b := ((u⁻¹ : (TotalChowClass C sY)ˣ) : TotalChowClass C sY)) (a' := 1)
    (b' := ((u⁻¹ : (TotalChowClass C sY)ˣ) : TotalChowClass C sY)) hu rfl
  rw [one_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one] at h
  exact h.symm

/-- An integral power with exponent `±1` of a unit whose degree-`0` component is `1 ∈ A^0(Y)`
again has degree-`0` component `1`. -/
theorem zpow_apply_zero_eq_one {u : (TotalChowClass C sY)ˣ}
    (hu : (u : TotalChowClass C sY) 0 = (1 : TotalChowClass C sY) 0) (n : ℤˣ) :
    ((u ^ ((n : ℤ)) : (TotalChowClass C sY)ˣ) : TotalChowClass C sY) 0 =
      (1 : TotalChowClass C sY) 0 := by
  rcases Int.units_eq_one_or n with hn | hn
  · rwa [hn, Units.val_one, zpow_one]
  · rw [hn, show ((-1 : ℤˣ) : ℤ) = -1 from rfl, zpow_neg, zpow_one]
    exact inv_apply_zero_eq_one hu

/-- The product of a list of units each of whose degree-`0` component is `1 ∈ A^0(Y)` again has
degree-`0` component `1`. -/
theorem val_listProd_apply_zero (l : List (TotalChowClass C sY)ˣ)
    (h : ∀ v ∈ l, (v : TotalChowClass C sY) 0 = (1 : TotalChowClass C sY) 0) :
    ((l.prod : (TotalChowClass C sY)ˣ) : TotalChowClass C sY) 0 =
      (1 : TotalChowClass C sY) 0 := by
  induction l with
  | nil => rw [List.prod_nil, Units.val_one]
  | cons v l ih =>
    rw [List.prod_cons, Units.val_mul]
    exact mul_apply_zero_eq_one (h v List.mem_cons_self)
      (ih fun w hw ↦ h w (List.mem_cons_of_mem v hw))

/-- The homogeneous components of the unit total class: `1` in degree `0` and `0` elsewhere. -/
theorem homComponent_one (j : ℕ) :
    homComponent j (1 : TotalChowClass C sY) = if j = 0 then 1 else 0 := by
  rcases eq_or_ne j 0 with rfl | hj
  · rw [ite_eq_left rfl]
    refine ext fun p ↦ ?_
    rw [homComponent_apply]
    rcases eq_or_ne p 0 with rfl | hp
    · rw [ite_eq_left rfl]
    · rw [ite_eq_right hp, one_apply_of_ne hp]
  · rw [ite_eq_right hj]
    refine ext fun p ↦ ?_
    rw [homComponent_apply]
    rcases eq_or_ne p j with rfl | hp
    · rw [ite_eq_left rfl, one_apply_of_ne hj]
      rfl
    · rw [ite_eq_right hp]
      rfl

/-- A total class whose degree-`0` component is `1 ∈ A^0(Y)` has degree-`0` homogeneous
component `1`. -/
theorem homComponent_zero_of_apply_zero {a : TotalChowClass C sY}
    (ha : a 0 = (1 : TotalChowClass C sY) 0) : homComponent 0 a = 1 := by
  refine ext fun p ↦ ?_
  rw [homComponent_apply]
  rcases eq_or_ne p 0 with rfl | hp
  · rw [ite_eq_left rfl, ha]
  · rw [ite_eq_right hp, one_apply_of_ne hp]

/-- **The homogeneous components of a product of total classes**, as the convolution of the
components of the factors: `(a b)_m = ∑_{i + j = m} a_i b_j`. -/
theorem homComponent_mul (a b : TotalChowClass C sY) (m : ℕ) :
    homComponent m (a * b) =
      ∑ j ∈ range (m + 1), homComponent (m - j) a * homComponent j b := by
  refine ext_op fun g _ ↦ ?_
  rw [op_homComponent, op_mul, Stacks.Chow.homComponent_mul, op_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [op_mul, op_homComponent, op_homComponent]

/-- **Newton's recursion for the inverse of a unit**, on homogeneous components: for `u` with
degree-`0` component `1 ∈ A^0(Y)`, the degree-`m` component of `u⁻¹` is determined by the
components of `u` and the components of `u⁻¹` in degrees below `m`. -/
theorem homComponent_inv_eq {u : (TotalChowClass C sY)ˣ}
    (hu : (u : TotalChowClass C sY) 0 = (1 : TotalChowClass C sY) 0) (m : ℕ) :
    homComponent m ((u⁻¹ : (TotalChowClass C sY)ˣ) : TotalChowClass C sY) =
      homComponent m (1 : TotalChowClass C sY) -
        ∑ j ∈ range m, homComponent (m - j) (u : TotalChowClass C sY) *
          homComponent j ((u⁻¹ : (TotalChowClass C sY)ˣ) : TotalChowClass C sY) := by
  have h := congrArg (homComponent m) u.mul_inv
  rw [homComponent_mul, Finset.sum_range_succ, Nat.sub_self,
    homComponent_zero_of_apply_zero hu, one_mul] at h
  exact eq_sub_of_add_eq' h

/-- **The glued class in a fixed degree depends only on the pieces' classes in that degree.** -/
theorem glue_apply_congr {I : Type u} {U : I → Y.Opens} (hU : IsClopenDecomposition U)
    {d d' : ∀ i, TotalChowClass C ((U i).ι ≫ sY)} (p : ℕ) (h : ∀ i, d i p = d' i p) :
    glue hU d p = glue hU d' p := by
  simp only [glue]
  exact congrArg _ (funext fun i ↦ congrArg _ (h i))

/-- **The unit total class is glued from the unit classes on the pieces.** -/
theorem one_eq_glue {I : Type u} {U : I → Y.Opens} (hU : IsClopenDecomposition U) :
    (1 : TotalChowClass C sY) = glue hU (fun _ ↦ 1) :=
  eq_glue hU fun i ↦ map_one (res (U i).ι rfl)

end TotalChowClass

/-! ### The degree-zero component of a total Chern class -/

/-- **`c_0(ℰ) = 1`**, as an identity of degree-`0` components of total classes: the degree-`0`
component of the total Chern class of a finite locally free module of rank `r` is the class
`1 ∈ A^0(Y)`. -/
theorem totalChern_apply_zero (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (F : Y.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] :
    totalChern C sY F r 0 = (1 : TotalChowClass C sY) 0 := by
  refine BivariantClass.eq_of_idRule_eq C sY _ _ _ fun g _ k α ↦ ?_
  rw [← TotalChowClass.op_apply, ← TotalChowClass.op_apply, TotalChowClass.op_one]
  let _ := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r g
  rw [gradedCap_one_apply_zero]
  refine eq_of_heq ((heq_of_eq (op_totalChern_apply C sY F r g k 0 α)).trans
    ((chowGroupCast_heq C _ (show k - ((0 : Fin (r + 1)) : ℕ) = k by simp) _).symm.trans ?_))
  rw [GenuineChern.chernCap_zero_apply]
  exact (gradedDegreeCast_heq _ α).symm

/-! ### Componentwise commutation of total classes -/

section Commute

variable {C : ChowSituation.{u}} {Y : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]

/-- Two total classes **commute componentwise** if every homogeneous component of the first
commutes with every homogeneous component of the second. -/
def CommuteHomComponent (a b : TotalChowClass C sY) : Prop :=
  ∀ i j, Commute (TotalChowClass.homComponent i a) (TotalChowClass.homComponent j b)

namespace CommuteHomComponent

/-- Componentwise commutation is symmetric. -/
theorem symm {a b : TotalChowClass C sY} (h : CommuteHomComponent a b) :
    CommuteHomComponent b a := fun i j ↦ (h j i).symm

/-- Every total class commutes componentwise with `0`. -/
theorem zero_right (a : TotalChowClass C sY) : CommuteHomComponent a 0 := fun i _ ↦ by
  rw [map_zero]
  exact Commute.zero_right (TotalChowClass.homComponent i a)

/-- Every total class commutes componentwise with `1`. -/
theorem one_right (a : TotalChowClass C sY) : CommuteHomComponent a 1 := fun i j ↦ by
  rw [TotalChowClass.homComponent_one]
  split_ifs
  · exact Commute.one_right (TotalChowClass.homComponent i a)
  · exact Commute.zero_right (TotalChowClass.homComponent i a)

/-- Componentwise commutation is additive in the right factor. -/
theorem add_right {a b b' : TotalChowClass C sY} (h : CommuteHomComponent a b)
    (h' : CommuteHomComponent a b') : CommuteHomComponent a (b + b') := fun i j ↦ by
  rw [map_add]
  exact (h i j).add_right (h' i j)

/-- Componentwise commutation passes to a difference in the right factor. -/
theorem sub_right {a b b' : TotalChowClass C sY} (h : CommuteHomComponent a b)
    (h' : CommuteHomComponent a b') : CommuteHomComponent a (b - b') := fun i j ↦ by
  rw [map_sub]
  exact (h i j).sub_right (h' i j)

/-- **Componentwise commutation passes to a product in the right factor.** -/
theorem mul_right {a b b' : TotalChowClass C sY} (h : CommuteHomComponent a b)
    (h' : CommuteHomComponent a b') : CommuteHomComponent a (b * b') := fun i j ↦ by
  rw [TotalChowClass.homComponent_mul]
  exact Commute.sum_right _ _ _ fun k _ ↦ (h i (j - k)).mul_right (h' i k)

/-- **Componentwise commutation passes to the inverse of a unit** whose degree-`0` component is
the class `1 ∈ A^0(Y)`. -/
theorem inv_right {a : TotalChowClass C sY} {u : (TotalChowClass C sY)ˣ}
    (hu : (u : TotalChowClass C sY) 0 = (1 : TotalChowClass C sY) 0)
    (h : CommuteHomComponent a (u : TotalChowClass C sY)) :
    CommuteHomComponent a ((u⁻¹ : (TotalChowClass C sY)ˣ) : TotalChowClass C sY) := by
  intro i j
  have key : ∀ m n : ℕ, n < m → Commute (TotalChowClass.homComponent i a)
      (TotalChowClass.homComponent n
        ((u⁻¹ : (TotalChowClass C sY)ˣ) : TotalChowClass C sY)) := by
    intro m
    induction m with
    | zero => exact fun n hn ↦ absurd hn (Nat.not_lt_zero n)
    | succ m ihm =>
      intro n hn
      rw [TotalChowClass.homComponent_inv_eq hu n]
      refine Commute.sub_right (one_right a i n) (Commute.sum_right _ _ _ fun k hk ↦ ?_)
      exact (h i (n - k)).mul_right
        (ihm k (lt_of_lt_of_le (mem_range.mp hk) (Nat.lt_succ_iff.mp hn)))
  exact key (j + 1) j (Nat.lt_succ_self j)

/-- **Componentwise commutation passes to an integral power with exponent `±1`** of a unit whose
degree-`0` component is the class `1 ∈ A^0(Y)`. -/
theorem zpow_right {a : TotalChowClass C sY} {u : (TotalChowClass C sY)ˣ}
    (hu : (u : TotalChowClass C sY) 0 = (1 : TotalChowClass C sY) 0)
    (h : CommuteHomComponent a (u : TotalChowClass C sY)) (n : ℤˣ) :
    CommuteHomComponent a ((u ^ ((n : ℤ)) : (TotalChowClass C sY)ˣ) : TotalChowClass C sY) := by
  rcases Int.units_eq_one_or n with hn | hn
  · rwa [hn, Units.val_one, zpow_one]
  · rw [hn, show ((-1 : ℤˣ) : ℤ) = -1 from rfl, zpow_neg, zpow_one]
    exact inv_right hu h

/-- **Componentwise commutation passes to the product of a list of units.** -/
theorem listProd_right {a : TotalChowClass C sY} (l : List (TotalChowClass C sY)ˣ)
    (h : ∀ v ∈ l, CommuteHomComponent a (v : TotalChowClass C sY)) :
    CommuteHomComponent a ((l.prod : (TotalChowClass C sY)ˣ) : TotalChowClass C sY) := by
  induction l with
  | nil =>
    rw [List.prod_nil, Units.val_one]
    exact one_right a
  | cons v l ih =>
    rw [List.prod_cons, Units.val_mul]
    exact (h v List.mem_cons_self).mul_right (ih fun w hw ↦ h w (List.mem_cons_of_mem v hw))

/-- **Componentwise commutation descends along an envelope**: if the restrictions of `a` and `b`
along an envelope `g` commute componentwise, then so do `a` and `b`. -/
theorem of_res {W : Scheme.{u}} {sW : W ⟶ C.S} [LocallyOfFiniteType sW] (g : W ⟶ Y)
    [LocallyOfFiniteType g] (hg : IsEnvelope g) (hs : g ≫ sY = sW)
    {a b : TotalChowClass C sY}
    (h : CommuteHomComponent (TotalChowClass.res g hs a) (TotalChowClass.res g hs b)) :
    CommuteHomComponent a b := by
  intro i j
  change TotalChowClass.homComponent i a * TotalChowClass.homComponent j b =
    TotalChowClass.homComponent j b * TotalChowClass.homComponent i a
  refine TotalChowClass.res_injective_of_isEnvelope g hg hs ?_
  rw [map_mul, map_mul, TotalChowClass.res_homComponent, TotalChowClass.res_homComponent]
  exact h i j

/-- **Componentwise commutation with the total Chern class of a bounded complex of constant
ranks**: a total class commuting componentwise with every factor `c(P^n)^{(-1)^n}` commutes
componentwise with the total Chern class of `P`. -/
theorem complexChernBounded_right {a : TotalChowClass C sY} (P : CochainComplex Y.Modules ℤ)
    (ρ : ℤ →₀ ℕ)
    (hP : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (ρ n))
    (hcomm : ∀ n : ℤ, CommuteHomComponent a
      ((complexChernFactor C sY P ρ hP n : (TotalChowClass C sY)ˣ) : TotalChowClass C sY)) :
    CommuteHomComponent a (complexChernBounded C sY P ρ hP) := by
  rw [complexChernBounded, complexChernProd]
  refine listProd_right _ fun v hv ↦ ?_
  obtain ⟨n, -, rfl⟩ := List.mem_map.1 hv
  exact hcomm n

end CommuteHomComponent

end Commute

/-! ### The degree-zero component of the total Chern class of a complex -/

section Zero

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]

/-- The degree-`0` component of a factor `c(P^n)^{(-1)^n}` is the class `1 ∈ A^0(Y)`. -/
theorem complexChernFactor_apply_zero (P : CochainComplex Y.Modules ℤ) (ρ : ℤ → ℕ)
    (hP : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (ρ n))
    (n : ℤ) :
    ((complexChernFactor C sY P ρ hP n : (TotalChowClass C sY)ˣ) : TotalChowClass C sY) 0 =
      (1 : TotalChowClass C sY) 0 := by
  let _ := hP n
  rw [complexChernFactor]
  exact TotalChowClass.zpow_apply_zero_eq_one
    (by rw [val_totalChernUnit]; exact totalChern_apply_zero C sY (P.X n) (ρ n)) _

/-- The degree-`0` component of the total Chern class of a bounded complex of constant ranks is
the class `1 ∈ A^0(Y)`. -/
theorem complexChernBounded_apply_zero (P : CochainComplex Y.Modules ℤ) (ρ : ℤ →₀ ℕ)
    (hP : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (ρ n)) :
    complexChernBounded C sY P ρ hP 0 = (1 : TotalChowClass C sY) 0 := by
  rw [complexChernBounded, complexChernProd]
  refine TotalChowClass.val_listProd_apply_zero _ fun v hv ↦ ?_
  obtain ⟨n, -, rfl⟩ := List.mem_map.1 hv
  exact complexChernFactor_apply_zero C sY P ρ hP n

/-- **`c_0(P) = 1` for a locally bounded complex of finite locally free modules**: the
degree-`0` component of the total Chern class `c(P)` of Stacks 0ESZ is the class `1 ∈ A^0(Y)`. -/
theorem complexChern_apply_zero {P : CochainComplex Y.Modules ℤ}
    (hP : IsLocallyBoundedFiniteLocallyFree P) :
    complexChern C sY hP 0 = (1 : TotalChowClass C sY) 0 := by
  rw [complexChern, TotalChowClass.one_eq_glue (isClopenDecomposition_complexRankLoci hP)]
  exact TotalChowClass.glue_apply_congr _ 0 fun ρ ↦
    complexChernBounded_apply_zero C _ _ ρ.down _

/-- **`c_0(E) = 1` for an object whose Chern classes are defined**: the degree-`0` component of
the total Chern class `c(E)` of Stacks 0F9E (2) is the class `1 ∈ A^0(X)`. -/
theorem perfectChernClass_apply_zero {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    {E : DerivedCategory X.Modules} (hE : HasDefinedChernClasses E) :
    perfectChernClass C sX hE 0 = (1 : TotalChowClass C sX) 0 := by
  set H := hE.some
  refine chowCohomologyRestriction_injective_of_isEnvelope C (gysinSystemOfInvertible C) sX H.f
    ((0 : ℕ) : ℤ) (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) H.envelope ?_
  rw [← TotalChowClass.res_rfl_apply, ← TotalChowClass.res_rfl_apply,
    res_perfectChernClass C sX hE H, map_one]
  exact complexChern_apply_zero C (H.f ≫ sX) H.locallyBounded

end Zero

/-! ### Componentwise commutation of the Chern classes of complexes and of perfect objects -/

section Commutation

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]

/-- The total Chern class of a finite locally free module commutes componentwise with the total
Chern class of a bounded complex of constant ranks. -/
theorem commute_homComponent_totalChern_complexChernBounded (F : Y.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    (P : CochainComplex Y.Modules ℤ) (ρ : ℤ →₀ ℕ)
    (hP : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (ρ n)) :
    CommuteHomComponent (totalChern C sY F r) (complexChernBounded C sY P ρ hP) := by
  refine CommuteHomComponent.complexChernBounded_right P ρ hP fun n ↦ ?_
  let _ := hP n
  rw [complexChernFactor]
  refine CommuteHomComponent.zpow_right ?_ ?_ _
  · rw [val_totalChernUnit]
    exact totalChern_apply_zero C sY (P.X n) (ρ n)
  · rw [val_totalChernUnit]
    exact fun i j ↦ commute_homComponent_totalChern C sY F (P.X n) r (ρ n) i j

/-- **The total Chern classes of two bounded complexes of constant ranks commute
componentwise.** -/
theorem commute_homComponent_complexChernBounded (P P' : CochainComplex Y.Modules ℤ)
    (ρ σ : ℤ →₀ ℕ)
    (hP : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (ρ n))
    (hP' : ∀ n,
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P'.X n) (σ n)) :
    CommuteHomComponent (complexChernBounded C sY P ρ hP)
      (complexChernBounded C sY P' σ hP') := by
  refine (CommuteHomComponent.complexChernBounded_right
    (a := complexChernBounded C sY P' σ hP') P ρ hP fun n ↦ ?_).symm
  let _ := hP n
  rw [complexChernFactor]
  refine CommuteHomComponent.zpow_right ?_ ?_ _
  · rw [val_totalChernUnit]
    exact totalChern_apply_zero C sY (P.X n) (ρ n)
  · rw [val_totalChernUnit]
    exact (commute_homComponent_totalChern_complexChernBounded C sY (P.X n) (ρ n) P' σ hP').symm

/-- **Stacks 0FAC for locally bounded complexes**: the homogeneous components of the total Chern
classes `c(P)` and `c(P')` of two locally bounded complexes of finite locally free modules
commute. -/
theorem commute_homComponent_complexChern {P P' : CochainComplex Y.Modules ℤ}
    (hP : IsLocallyBoundedFiniteLocallyFree P) (hP' : IsLocallyBoundedFiniteLocallyFree P')
    (i j : ℕ) :
    Commute (TotalChowClass.homComponent i (complexChern C sY hP))
      (TotalChowClass.homComponent j (complexChern C sY hP')) := by
  change TotalChowClass.homComponent i (complexChern C sY hP) *
      TotalChowClass.homComponent j (complexChern C sY hP') =
    TotalChowClass.homComponent j (complexChern C sY hP') *
      TotalChowClass.homComponent i (complexChern C sY hP)
  refine eq_of_res_eq_of_constantRanks C sY hP hP' fun Z g hg ρ σ hρ hσ ↦ ?_
  rw [map_mul, map_mul, TotalChowClass.res_homComponent, TotalChowClass.res_homComponent,
    res_complexChern_eq_complexChernBounded C sY hP g rfl ρ hρ,
    res_complexChern_eq_complexChernBounded C sY hP' g rfl σ hσ]
  exact commute_homComponent_complexChernBounded C (g ≫ sY) _ _ ρ σ hρ hσ i j

/-- **Stacks 0FAC**: the homogeneous components of the total Chern classes `c(E)` and `c(E')` of
two objects of `D(𝒪_X)` whose Chern classes are defined commute. -/
theorem commute_homComponent_perfectChernClass {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] {E E' : DerivedCategory X.Modules}
    (hE : HasDefinedChernClasses E) (hE' : HasDefinedChernClasses E') (i j : ℕ) :
    Commute (TotalChowClass.homComponent i (perfectChernClass C sX hE))
      (TotalChowClass.homComponent j (perfectChernClass C sX hE')) := by
  set H := hE.some
  set H' := hE'.some
  have hfst : IsEnvelope (pullback.fst H.f H'.f) :=
    isEnvelope_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback H.f H'.f).flip H'.envelope
  have hs : (pullback.snd H.f H'.f ≫ H'.f) ≫ sX =
      pullback.fst H.f H'.f ≫ (H.f ≫ sX) := by
    rw [← pullback.condition, Category.assoc]
  have hs2 : pullback.snd H.f H'.f ≫ (H'.f ≫ sX) =
      pullback.fst H.f H'.f ≫ (H.f ≫ sX) := by
    rw [← Category.assoc, ← pullback.condition, Category.assoc]
  refine CommuteHomComponent.of_res H.f H.envelope rfl
    (CommuteHomComponent.of_res (pullback.fst H.f H'.f) hfst rfl ?_) i j
  rw [res_perfectChernClass C sX hE H, res_complexChern, TotalChowClass.res_res,
    TotalChowClass.res_congr pullback.condition _ hs,
    ← TotalChowClass.res_res H'.f rfl _ hs2, res_perfectChernClass C sX hE' H',
    res_complexChern]
  exact commute_homComponent_complexChern C _ _ _

end Commutation

end Stacks.Chow

end
