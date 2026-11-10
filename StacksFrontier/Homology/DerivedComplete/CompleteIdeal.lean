module

public import StacksFrontier.Homology.DerivedComplete
public import StacksFrontier.Homology.DerivedComplete.PrincipalRecurrence

/-!
# The scalars along which an object is derived complete form an ideal

Let `A` be a commutative ring, let `𝒟` be an `A`-linear preadditive category with countable
products and let `K` be an object of `𝒟`. The set of `a ∈ A` with `T(K, a) = 0`, that is with
`AlgebraicGeometry.RingedSite.IsDerivedCompleteAt K a`, is an ideal of `A`.

The proof is purely algebraic and does not use triangles. Derived completeness at `a` is
invertibility of `1 - a·shift` on `∏ₙ K`; postcomposition turns that into bijectivity of the
recurrence operator `(xₙ) ↦ (xₙ - a·xₙ₊₁)` of `DerivedCompleteRecurrence.recurrence` on
sequences in the `A`-module `(∏ₙ K ⟶ K)`; and bijectivity of a recurrence operator on sequences
in an `A`-module `M` is equivalent to `1 - a·φ` being invertible for every `A`-linear
endomorphism `φ` of `ℕ → M`. The last condition is visibly an ideal in `a`.

## Main definitions

* `DerivedCompleteRecurrence.oneSubSmulUnitIdeal`: the ideal of scalars `a` of `A` such that
  `1 - a·b` is a unit of `B` for every `b : B`, for an `A`-algebra `B`.
* `derivedCompleteIdeal`: the ideal of scalars along which `K` is derived complete.

## Main results

* `DerivedCompleteRecurrence.bijective_recurrence_pi`: bijectivity of the recurrence operator
  of `a` passes from an `A`-module `M` to the `A`-module `ι → M`.
* `DerivedCompleteRecurrence.isUnit_one_sub_smul_of_bijective_recurrence`: bijectivity of the
  recurrence operator of `a` on `M` makes `1 - a·φ` a unit for every `A`-linear endomorphism
  `φ` of `M`.
* `DerivedCompleteRecurrence.isDerivedCompleteAt_iff_bijective_recurrence`: `T(K, a) = 0` is
  bijectivity of the recurrence operator of `a` on `(∏ₙ K ⟶ K)`.
* `mem_derivedCompleteIdeal_iff`: membership in `derivedCompleteIdeal K` is `T(K, a) = 0`.
* `isDerivedCompleteAt_add`, `isDerivedCompleteAt_smul`: the two closure properties, read off
  the ideal.

## Implementation notes

The recurrence operator is `DerivedCompleteRecurrence.recurrence`, which is already
used for modules in `StacksFrontier/Homology/DerivedComplete/PrincipalRecurrence.lean`; what is new
here is that it detects derived completeness in an arbitrary `A`-linear category, not only for
a module read as a complex, and that the resulting condition is an ideal.

The passage from `1 - a·φ` for endomorphisms of `ℕ → M` back to bijectivity of the recurrence
operator on `M` itself is why the ideal is stated for endomorphisms of a sequence module: the
shift `(xₙ) ↦ xₙ₊₁` is such an endomorphism, and `1 - a·shift` *is* the recurrence operator.

## References

* [Stacks Project, Tag 0998](https://stacks.math.columbia.edu/tag/0998)
* [Stacks Project, Tag 091S](https://stacks.math.columbia.edu/tag/091S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

noncomputable section

universe v u

namespace DerivedCompleteRecurrence

section Modules

variable {A : Type*} [CommRing A]

/-- Bijectivity of the recurrence operator of `a` passes from an `A`-module `M` to the module
`ι → M` of families in `M`, because the operator acts coordinatewise. -/
theorem bijective_recurrence_pi {M : Type*} [AddCommGroup M] [Module A M] {a : A}
    (h : Function.Bijective (recurrence (A := A) (M := M) a)) (ι : Type*) :
    Function.Bijective (recurrence (A := A) (M := ι → M) a) := by
  constructor
  · intro x y hxy
    funext n i
    have hi : (fun m ↦ x m i) = (fun m ↦ y m i) :=
      h.1 (funext fun m ↦ congrFun (congrFun hxy m) i)
    exact congrFun hi n
  · intro x
    choose y hy using fun i ↦ h.2 (fun n ↦ x n i)
    refine ⟨fun n i ↦ y i n, ?_⟩
    funext n i
    exact congrFun (hy i) n

/-- If the recurrence operator of `a` on sequences in `M` is bijective, then `1 - a·φ` is a unit
for every `A`-linear endomorphism `φ` of `M`.

The inverse is the geometric series: injectivity of `1 - a·φ` follows by applying the recurrence
operator to the sequence of iterates `(φⁿ x)`, and a preimage of `x` is the zeroth term of the
sequence the recurrence operator carries to `(φⁿ x)`. -/
theorem isUnit_one_sub_smul_of_bijective_recurrence {M : Type*} [AddCommGroup M] [Module A M]
    {a : A} (h : Function.Bijective (recurrence (A := A) (M := M) a))
    (φ : Module.End A M) : IsUnit (1 - a • φ) := by
  rw [Module.End.isUnit_iff]
  constructor
  · intro x y hxy
    have hit : (fun n ↦ (φ ^ n) x) = (fun n ↦ (φ ^ n) y) := by
      apply h.1
      funext n
      simpa only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
        map_sub, map_smul, recurrence_apply, pow_succ, Module.End.mul_apply] using
        congrArg (φ ^ n) hxy
    simpa using congrFun hit 0
  · intro x
    obtain ⟨y, hy⟩ := h.2 (fun n ↦ (φ ^ n) x)
    have hshift : (fun n ↦ φ (y n)) = fun n ↦ y (n + 1) := by
      apply h.1
      funext n
      change φ (y n) - a • φ (y (n + 1)) = y (n + 1) - a • y (n + 1 + 1)
      rw [← map_smul, ← map_sub, ← recurrence_apply, congrFun hy,
        ← recurrence_apply, congrFun hy, pow_succ', Module.End.mul_apply]
    refine ⟨y 0, ?_⟩
    change y 0 - a • φ (y 0) = x
    rw [congrFun hshift 0]
    simpa only [recurrence_apply, pow_zero, Module.End.one_apply] using congrFun hy 0

end Modules

section Units

variable (A : Type*) [CommSemiring A] (B : Type*) [Ring B] [Algebra A B]

/-- **The scalars `a` with `1 - a·b` invertible for every `b` form an ideal.** For `a` and `a'`
in the set and `b : B`, write `1 - a·b = u`; then
`(1 - a'·(b·u⁻¹))·u = 1 - (a + a')·b`, a product of units. -/
def oneSubSmulUnitIdeal : Ideal A where
  carrier := {a | ∀ b : B, IsUnit (1 - a • b)}
  zero_mem' := by simp
  add_mem' := by
    intro a a' ha ha' b
    obtain ⟨u, hu⟩ := ha b
    have hfac : (1 - a' • (b * ↑u⁻¹)) * ↑u = 1 - (a + a') • b := by
      rw [sub_mul, one_mul, smul_mul_assoc, mul_assoc, Units.inv_mul, mul_one, hu, add_smul]
      abel
    rw [← hfac]
    exact (ha' (b * ↑u⁻¹)).mul u.isUnit
  smul_mem' := by
    intro c a ha b
    simpa only [smul_eq_mul, mul_smul, smul_comm c a b] using ha (c • b)

/-- A scalar `a` lies in `oneSubSmulUnitIdeal A B` if and only if `1 - a • b` is a unit for every
`b : B`. -/
@[simp]
theorem mem_oneSubSmulUnitIdeal {a : A} :
    a ∈ oneSubSmulUnitIdeal A B ↔ ∀ b : B, IsUnit (1 - a • b) :=
  Iff.rfl

end Units

section Category

variable {A : Type*} [CommRing A] {C : Type u} [Category.{v} C] [Preadditive C] [Linear A C]
  [HasProductsOfShape ℕ C]

omit [Preadditive C] [HasProductsOfShape ℕ C] in
/-- An endomorphism is an isomorphism exactly when postcomposition with it is bijective on
endomorphisms of the same object. -/
theorem isIso_iff_bijective_postcomp {K : C} (u : K ⟶ K) :
    IsIso u ↔ Function.Bijective (fun w : K ⟶ K ↦ w ≫ u) := by
  refine ⟨fun hu ↦ (isIso_iff_yoneda_map_bijective u).1 hu K, fun hu ↦ ?_⟩
  obtain ⟨w, hw⟩ := hu.2 (𝟙 K)
  refine ⟨w, hu.1 ?_, hw⟩
  simp only [Category.assoc, hw, Category.comp_id, Category.id_comp]

/-- **`T(K, a) = 0` is bijectivity of the recurrence operator of `a`** on the `A`-module
`(∏ₙ K ⟶ K)` of families of endomorphisms of the countable product into `K`.

A morphism `∏ₙ K ⟶ ∏ₙ K` is the same as a sequence of morphisms `∏ₙ K ⟶ K`, and under that
identification postcomposition with `1 - a·shift` is the recurrence operator of `a`. -/
theorem isDerivedCompleteAt_iff_bijective_recurrence (K : C) (a : A) :
    IsDerivedCompleteAt K a ↔
      Function.Bijective
        (recurrence (A := A) (M := ((∏ᶜ fun _ : ℕ => K) ⟶ K)) a) := by
  set P := ∏ᶜ fun _ : ℕ => K
  set u : P ⟶ P := oneSubSmulShift K a with hu
  let e : (ℕ → (P ⟶ K)) ≃ (P ⟶ P) :=
    { toFun := Pi.lift
      invFun := fun w n ↦ w ≫ Pi.π (fun _ : ℕ => K) n
      left_inv w := funext fun n ↦ by simp
      right_inv w := Pi.hom_ext _ _ fun n ↦ by simp }
  have hcomm (w : ℕ → (P ⟶ K)) : e (recurrence a w) = e w ≫ u :=
    Pi.hom_ext _ _ fun n ↦ by simp [e, u, recurrence_apply, Preadditive.comp_sub]
  have hconj : (fun w : P ⟶ P ↦ w ≫ u) = e ∘ recurrence a ∘ e.symm := by
    funext w
    rw [Function.comp_apply, Function.comp_apply, hcomm, e.apply_symm_apply]
  rw [isDerivedCompleteAt_iff_isIso, ← hu, isIso_iff_bijective_postcomp, hconj,
    Equiv.comp_bijective, Equiv.bijective_comp]

end Category

end DerivedCompleteRecurrence

section Ideal

open DerivedCompleteRecurrence

variable {A : Type*} [CommRing A] {C : Type u} [Category.{v} C] [Preadditive C] [Linear A C]
  [HasProductsOfShape ℕ C]

/-- **The ideal of scalars along which `K` is derived complete**: the `a ∈ A` with
`T(K, a) = 0`. This is the sectionwise content of [Stacks, Tag 0998]. -/
def derivedCompleteIdeal (K : C) : Ideal A :=
  oneSubSmulUnitIdeal A (Module.End A (ℕ → ((∏ᶜ fun _ : ℕ => K) ⟶ K)))

/-- Membership in `derivedCompleteIdeal K` is derived completeness of `K` at the scalar. -/
@[simp]
theorem mem_derivedCompleteIdeal_iff {K : C} {a : A} :
    a ∈ derivedCompleteIdeal (A := A) K ↔ IsDerivedCompleteAt K a := by
  rw [isDerivedCompleteAt_iff_bijective_recurrence]
  exact ⟨fun h ↦ (Module.End.isUnit_iff _).1 (h (LinearMap.funLeft A _ Nat.succ)),
    fun h ↦ isUnit_one_sub_smul_of_bijective_recurrence (bijective_recurrence_pi h ℕ)⟩

/-- **The vanishing locus is closed under addition**: if `T(K, a) = 0` and `T(K, a') = 0` then
`T(K, a + a') = 0`. -/
theorem isDerivedCompleteAt_add {K : C} {a a' : A} (ha : IsDerivedCompleteAt K a)
    (ha' : IsDerivedCompleteAt K a') : IsDerivedCompleteAt K (a + a') :=
  mem_derivedCompleteIdeal_iff.1
    (Ideal.add_mem _ (mem_derivedCompleteIdeal_iff.2 ha) (mem_derivedCompleteIdeal_iff.2 ha'))

/-- **The vanishing locus is closed under multiplication**: if `T(K, a) = 0` then
`T(K, c·a) = 0` for every scalar `c`. -/
theorem isDerivedCompleteAt_smul {K : C} (c : A) {a : A} (ha : IsDerivedCompleteAt K a) :
    IsDerivedCompleteAt K (c * a) :=
  mem_derivedCompleteIdeal_iff.1
    (Ideal.mul_mem_left _ c (mem_derivedCompleteIdeal_iff.2 ha))

/-- `T(K, 0) = 0`. -/
theorem isDerivedCompleteAt_zero (K : C) : IsDerivedCompleteAt K (0 : A) :=
  mem_derivedCompleteIdeal_iff.1 (Ideal.zero_mem _)

end Ideal

end

end
