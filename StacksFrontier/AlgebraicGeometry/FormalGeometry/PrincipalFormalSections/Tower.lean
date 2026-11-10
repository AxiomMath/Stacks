module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalFormalSections.Sections

/-!
# The tower of quotients `M / fⁿ M`

For an element `f` of a commutative ring `A` and an `A`-module `M` this file records the tower
`⋯ → M/f³M → M/f²M → M/fM`, its transition maps, multiplication by `f` from one level to the
next, and the short exact sequence

`0 ⟶ M/fⁿM ⟶ M/fⁿ⁺¹M ⟶ M/fM ⟶ 0`

which holds whenever `f` is a nonzerodivisor on `M`. This is condition (1) of [Stacks, Tag 0H39]
for the tower, in the module-theoretic form in which the tower of quotients realizes it.

## Main definitions

* `Stacks.Algebraization.FormalSections.powSmul`: the submodule `fⁿM`.
* `Stacks.Algebraization.FormalSections.Quot`: the quotient `M/fⁿM`.
* `Stacks.Algebraization.FormalSections.quotLe`: the projections of the tower.
* `Stacks.Algebraization.FormalSections.quotUp`: multiplication by `f`, one level up.

## Main results

* `Stacks.Algebraization.FormalSections.exact_quotUp_quotLe`: exactness of the sequence above.
* `Stacks.Algebraization.FormalSections.injective_quotUp`: its left exactness, for `f` a
  nonzerodivisor.

## References

* [Stacks Project, Tag 0H39](https://stacks.math.columbia.edu/tag/0H39)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.LocalCohomology

universe u v

namespace Stacks.Algebraization.FormalSections

variable {A : Type u} [CommRing A] (f : A) (M : ModuleCat.{v} A)

/-- The submodule `fⁿ M` of `M`. -/
def powSmul (n : ℕ) : Submodule A (M : Type v) :=
  LinearMap.range (LinearMap.lsmul A (M : Type v) (f ^ n))

/-- An element `x` lies in `fⁿ M` if and only if `x = fⁿ • y` for some `y : M`. -/
theorem mem_powSmul {n : ℕ} {x : M} : x ∈ powSmul f M n ↔ ∃ y : M, f ^ n • y = x := Iff.rfl

/-- The submodules `fⁿ M` decrease in `n`: `fⁿ M ≤ fᵐ M` for `m ≤ n`. -/
theorem powSmul_le {m n : ℕ} (h : m ≤ n) : powSmul f M n ≤ powSmul f M m := by
  rintro x hx
  obtain ⟨y, hy⟩ := (mem_powSmul f M).1 hx
  refine (mem_powSmul f M).2 ⟨f ^ (n - m) • y, ?_⟩
  rwa [smul_smul, ← pow_add, show m + (n - m) = n by omega]

/-- The quotient `M / fⁿ M`. -/
abbrev Quot (n : ℕ) : ModuleCat.{v} A := ModuleCat.of A ((M : Type v) ⧸ powSmul f M n)

/-- The projection `M ⟶ M / fⁿ M`. -/
def quotMk (n : ℕ) : M ⟶ Quot f M n := ModuleCat.ofHom (powSmul f M n).mkQ

/-- The projection `M ⟶ M / fⁿ M` is surjective. -/
theorem quotMk_surjective (n : ℕ) : Function.Surjective (quotMk f M n) :=
  Submodule.mkQ_surjective _

/-- The image of `x` in `M / fⁿ M` vanishes if and only if `x = fⁿ • y` for some `y : M`. -/
theorem quotMk_eq_zero_iff {n : ℕ} {x : M} :
    quotMk f M n x = 0 ↔ ∃ y : M, f ^ n • y = x :=
  (Submodule.Quotient.mk_eq_zero _).trans (mem_powSmul f M)

/-- The projection `M / fⁿ M ⟶ M / fᵐ M` for `m ≤ n`. -/
def quotLe {m n : ℕ} (h : m ≤ n) : Quot f M n ⟶ Quot f M m :=
  ModuleCat.ofHom (Submodule.mapQ _ _ LinearMap.id (powSmul_le f M h))

/-- The projection `M / fⁿ M ⟶ M / fᵐ M` sends the class of `x` to the class of `x`. -/
@[simp]
theorem quotLe_quotMk {m n : ℕ} (h : m ≤ n) (x : M) :
    quotLe f M h (quotMk f M n x) = quotMk f M m x := rfl

/-- The projections of the tower compose: `M / fᵖ M ⟶ M / fⁿ M ⟶ M / fᵐ M` is the projection
`M / fᵖ M ⟶ M / fᵐ M`. -/
theorem quotLe_quotLe {m n p : ℕ} (h₁ : m ≤ n) (h₂ : n ≤ p) (x : Quot f M p) :
    quotLe f M h₁ (quotLe f M h₂ x) = quotLe f M (h₁.trans h₂) x := by
  obtain ⟨y, rfl⟩ := quotMk_surjective f M p x
  rfl

/-- Multiplication by `f` as a map `M / fⁿ M ⟶ M / fⁿ⁺¹ M`. -/
def quotUp (n : ℕ) : Quot f M n ⟶ Quot f M (n + 1) :=
  ModuleCat.ofHom (Submodule.mapQ _ _ (LinearMap.lsmul A (M : Type v) f) (by
    intro x hx
    obtain ⟨y, hy⟩ := (mem_powSmul f M).1 hx
    refine (mem_powSmul f M).2 ⟨y, ?_⟩
    rw [LinearMap.lsmul_apply, ← hy, smul_smul, ← pow_succ']))

/-- Multiplication by `f` sends the class of `x` in `M / fⁿ M` to the class of `f • x` in
`M / fⁿ⁺¹ M`. -/
@[simp]
theorem quotUp_quotMk (n : ℕ) (x : M) :
    quotUp f M n (quotMk f M n x) = quotMk f M (n + 1) (f • x) := rfl

/-- Multiplication by `f` into `M / fⁿ⁺¹ M` followed by the projection back to `M / fⁿ M` is
multiplication by `f` on `M / fⁿ M`. -/
theorem quotLe_quotUp (n : ℕ) (z : Quot f M n) :
    quotLe f M (Nat.le_succ n) (quotUp f M n z) = f • z := by
  obtain ⟨y, rfl⟩ := quotMk_surjective f M n z
  rfl

/-- The projection `M / fⁿ⁺¹ M ⟶ M / fⁿ M` followed by multiplication by `f` is multiplication by
`f` on `M / fⁿ⁺¹ M`. -/
theorem quotUp_quotLe (n : ℕ) (w : Quot f M (n + 1)) :
    quotUp f M n (quotLe f M (Nat.le_succ n) w) = f • w := by
  obtain ⟨y, rfl⟩ := quotMk_surjective f M (n + 1) w
  rfl

/-- The element `fⁿ` annihilates `M / fⁿ M`. -/
theorem pow_smul_quot_eq_zero (n : ℕ) (z : Quot f M n) : f ^ n • z = 0 := by
  obtain ⟨y, rfl⟩ := quotMk_surjective f M n z
  rw [← map_smul (quotMk f M n).hom]
  exact (quotMk_eq_zero_iff f M).2 ⟨y, rfl⟩

/-- If `f` is a nonzerodivisor on `M`, then multiplication by `f` as a map
`M / fⁿ M ⟶ M / fⁿ⁺¹ M` is injective. -/
theorem injective_quotUp (hf : IsSMulRegular (M : Type v) f) (n : ℕ) :
    Function.Injective (quotUp f M n).hom := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨y, rfl⟩ := quotMk_surjective f M n z
  obtain ⟨w, hw⟩ := (quotMk_eq_zero_iff f M (x := f • y)).1 hz
  refine (quotMk_eq_zero_iff f M).2 ⟨w, hf ?_⟩
  change f • (f ^ n • w) = f • y
  rwa [smul_smul, ← pow_succ']

/-- The sequence `M / fⁿ M ⟶ M / fⁿ⁺¹ M ⟶ M / f M`, given by multiplication by `f` and the
projection, is exact. -/
theorem exact_quotUp_quotLe (n : ℕ) :
    Function.Exact (quotUp f M n).hom (quotLe f M (show 1 ≤ n + 1 by omega)).hom := by
  intro w
  constructor
  · intro hw
    obtain ⟨y, rfl⟩ := quotMk_surjective f M (n + 1) w
    obtain ⟨z, hz⟩ := (quotMk_eq_zero_iff f M (n := 1) (x := y)).1 hw
    exact ⟨quotMk f M n z, by rw [← hz, pow_one]; rfl⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨y, rfl⟩ := quotMk_surjective f M n z
    change quotMk f M 1 (f • y) = 0
    exact (quotMk_eq_zero_iff f M).2 ⟨y, by rw [pow_one]⟩

/-- The projection `M / fⁿ M ⟶ M / fⁿ M` is the identity. -/
theorem quotLe_rfl (n : ℕ) : quotLe f M (le_refl n) = 𝟙 (Quot f M n) :=
  ModuleCat.hom_ext (LinearMap.ext fun z ↦ by
    obtain ⟨y, rfl⟩ := quotMk_surjective f M n z
    rfl)

/-- The composite of the projections `M / fᵖ M ⟶ M / fⁿ M ⟶ M / fᵐ M` is the projection
`M / fᵖ M ⟶ M / fᵐ M`. -/
theorem quotLe_comp_quotLe {m n p : ℕ} (h₁ : m ≤ n) (h₂ : n ≤ p) :
    quotLe f M h₂ ≫ quotLe f M h₁ = quotLe f M (h₁.trans h₂) :=
  ModuleCat.hom_ext (LinearMap.ext fun z ↦ quotLe_quotLe f M h₁ h₂ z)

/-- The projection `M / fⁿ⁺¹ M ⟶ M / fⁿ M` followed by multiplication by `f` is multiplication by
`f` on `M / fⁿ⁺¹ M`. -/
theorem quotLe_comp_quotUp (n : ℕ) :
    quotLe f M (Nat.le_succ n) ≫ quotUp f M n =
      ModuleCat.ofHom (LinearMap.lsmul A (Quot f M (n + 1) : Type v) f) :=
  ModuleCat.hom_ext (LinearMap.ext fun z ↦ quotUp_quotLe f M n z)

/-- Multiplication by `f` into `M / fⁿ⁺¹ M` followed by the projection back to `M / fⁿ M` is
multiplication by `f` on `M / fⁿ M`. -/
theorem quotUp_comp_quotLe (n : ℕ) :
    quotUp f M n ≫ quotLe f M (Nat.le_succ n) =
      ModuleCat.ofHom (LinearMap.lsmul A (Quot f M n : Type v) f) :=
  ModuleCat.hom_ext (LinearMap.ext fun z ↦ quotLe_quotUp f M n z)

/-- The submodule `f¹ M` is the submodule `(f) • M` for the principal ideal `(f)`. -/
theorem powSmul_one : powSmul f M 1 = Ideal.span {f} • (⊤ : Submodule A (M : Type v)) := by
  rw [Submodule.ideal_span_singleton_smul]
  ext x
  simp [mem_powSmul, Submodule.mem_smul_pointwise_iff_exists]

/-- The projection `M ⟶ M / fⁿ M` followed by `M / fⁿ M ⟶ M / fᵐ M` is the projection
`M ⟶ M / fᵐ M`. -/
theorem quotMk_comp_quotLe {m n : ℕ} (h : m ≤ n) :
    quotMk f M n ≫ quotLe f M h = quotMk f M m := rfl

/-- The map `M/fⁿM ⟶ P/fⁿP` induced by a map `M ⟶ P`. -/
def quotMap {M P : ModuleCat.{v} A} (u : M ⟶ P) (n : ℕ) : Quot f M n ⟶ Quot f P n :=
  ModuleCat.ofHom (Submodule.mapQ _ _ u.hom (by
    intro x hx
    obtain ⟨y, hy⟩ := (mem_powSmul f M).1 hx
    refine (mem_powSmul f P).2 ⟨u y, ?_⟩
    rw [← hy]
    exact (map_smul u.hom (f ^ n) y).symm))

/-- The map `M / fⁿ M ⟶ P / fⁿ P` induced by `u` sends the class of `x` to the class of `u x`. -/
@[simp]
theorem quotMap_quotMk {M P : ModuleCat.{v} A} (u : M ⟶ P) (n : ℕ) (x : M) :
    quotMap f u n (quotMk f M n x) = quotMk f P n (u x) := rfl

/-- The map induced by `u` on quotients commutes with the projections `M ⟶ M / fⁿ M` and
`P ⟶ P / fⁿ P`. -/
theorem quotMk_comp_quotMap {M P : ModuleCat.{v} A} (u : M ⟶ P) (n : ℕ) :
    quotMk f M n ≫ quotMap f u n = u ≫ quotMk f P n := rfl

end Stacks.Algebraization.FormalSections

end
