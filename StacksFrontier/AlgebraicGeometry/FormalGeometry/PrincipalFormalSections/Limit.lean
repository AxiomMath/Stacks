module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalFormalSections.Tower
public import StacksFrontier.RingTheory.AdicCompletion.Finiteness

/-!
# The inverse limit of the sections of the quotients `M / fⁿ M`

Let `A` be a commutative ring, `f ∈ A`, `M` an `A`-module and `U ⊆ Spec A` an open. This file
studies

`N = lim_n Γ(U, (M/fⁿM)~)`

and proves the three conclusions of [Stacks, Tag 0BLB] for it, under the hypotheses of that
tag: `f` is a nonzerodivisor on `M`, so that the tower satisfies condition (1) of
[Stacks, Tag 0H39]; `Γ(U, (M/fM)~)` is a finite `A`-module; and `A` is `f`-adically complete.

The three conclusions are that `f` is a nonzerodivisor on `N`, that the kernel of the projection
`N ⟶ Γ(U, (M/fⁿM)~)` is exactly `fⁿN` — so in particular `N/fN` embeds into
`Γ(U, (M/fM)~)` — and that `N` is a finite `A`-module.

The argument is the source's. Sections are left exact, so each level of the tower of sections
inherits the left half `0 ⟶ Γ(U, (M/fⁿM)~) ⟶ Γ(U, (M/fⁿ⁺¹M)~) ⟶ Γ(U, (M/fM)~)` of the exact
sequence of the tag; multiplication by `f` factors through the projection in both directions,
and these two facts alone give the first two conclusions by a diagram chase. Finiteness is then
[Stacks, Tag 0DRH]/[Stacks, Tag 031D]: the kernel formula at `n = 0` makes `N/fN` a submodule of
a finite module over a Noetherian ring, and at general `n` it makes `N` separated for the
`f`-adic topology.

## Main definitions

* `Stacks.Algebraization.FormalSections.formalLimit` — the inverse limit `N`.
* `Stacks.Algebraization.FormalSections.toFormalLimit` — the canonical map `M ⟶ N`.

## Main results

* `Stacks.Algebraization.FormalSections.isSMulRegular_formalLimit`
* `Stacks.Algebraization.FormalSections.exists_pow_smul_eq_of_proj_eq_zero`
* `Stacks.Algebraization.FormalSections.proj_eq_zero_of_mem_pow_smul`
* `Stacks.Algebraization.FormalSections.finite_formalLimit`

## References

* [Stacks Project, Tag 0BLB](https://stacks.math.columbia.edu/tag/0BLB)
* [Stacks Project, Tag 031D](https://stacks.math.columbia.edu/tag/031D)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.LocalCohomology

universe u v

namespace Stacks.Algebraization.FormalSections

variable {A : Type u} [CommRing A] (f : A) (M : ModuleCat.{v} A)
  (U : Opens (PrimeSpectrum.Top A))

/-- The inverse limit `lim_n Γ(U, (M/fⁿM)~)`, as the submodule of compatible families. -/
def formalLimit : Submodule A (∀ n : ℕ, moduleSections (Quot f M n) U) where
  carrier := {x | ∀ n : ℕ, moduleSectionsMap (quotLe f M (Nat.le_succ n)) U (x (n + 1)) = x n}
  add_mem' {x y} hx hy := by
    intro n
    change moduleSectionsMap (quotLe f M (Nat.le_succ n)) U (x (n + 1) + y (n + 1)) = x n + y n
    rw [map_add, hx n, hy n]
  zero_mem' := by
    intro n
    change moduleSectionsMap (quotLe f M (Nat.le_succ n)) U 0 = 0
    rw [map_zero]
  smul_mem' c x hx := by
    intro n
    change moduleSectionsMap (quotLe f M (Nat.le_succ n)) U (c • x (n + 1)) = c • x n
    rw [map_smul, hx n]

/-- A member of the limit is compatible with the transition map from level `n + 1` to level `n`. -/
@[simp]
theorem formalLimit_compat (x : formalLimit f M U) (n : ℕ) :
    moduleSectionsMap (quotLe f M (Nat.le_succ n)) U (x.1 (n + 1)) = x.1 n := x.2 n

/-- Two members of the limit agreeing at every level are equal. -/
theorem formalLimit_ext {x y : formalLimit f M U} (h : ∀ n, x.1 n = y.1 n) : x = y :=
  Subtype.ext (funext h)

/-- The projection of the limit down to any level agrees with the given family. -/
theorem formalLimit_proj (x : formalLimit f M U) {m n : ℕ} (h : m ≤ n) :
    moduleSectionsMap (quotLe f M h) U (x.1 n) = x.1 m := by
  induction n, h using Nat.le_induction with
  | base => rw [quotLe_rfl]; exact moduleSectionsMap_id U (x.1 m)
  | succ n hmn ih =>
    rw [← quotLe_comp_quotLe f M hmn (Nat.le_succ n), moduleSectionsMap_comp_apply,
      formalLimit_compat, ih]

/-- The canonical map from `M` to the inverse limit. -/
def toFormalLimit : (M : Type v) →ₗ[A] formalLimit f M U where
  toFun m := ⟨fun n ↦ moduleSectionsMk (Quot f M n) U (quotMk f M n m), fun n ↦ by
    rw [show moduleSectionsMap (quotLe f M (Nat.le_succ n)) U
        (moduleSectionsMk (Quot f M (n + 1)) U (quotMk f M (n + 1) m)) =
        moduleSectionsMk (Quot f M n) U
          (quotLe f M (Nat.le_succ n) (quotMk f M (n + 1) m)) from
      LinearMap.congr_fun
        (moduleSectionsMap_comp_moduleSectionsMk (quotLe f M (Nat.le_succ n)) U) _]
    rw [quotLe_quotMk]⟩
  map_add' x y := Subtype.ext (funext fun n ↦ by
    simp only [map_add]; rfl)
  map_smul' c x := Subtype.ext (funext fun n ↦ by
    simp only [map_smul, RingHom.id_apply]; rfl)

/-- The image of `m` in the limit has, at level `n`, the section induced by the class of `m` in
`M / fⁿ M`. -/
@[simp]
theorem toFormalLimit_apply (m : M) (n : ℕ) :
    (toFormalLimit f M U m).1 n = moduleSectionsMk (Quot f M n) U (quotMk f M n m) := rfl

/-! ### Multiplication by `f` through the tower -/

/-- For a member `x` of the limit, `f • x (n + 1)` is the image of `x n` under multiplication by
`f` from level `n` to level `n + 1`. -/
theorem smul_level (x : formalLimit f M U) (n : ℕ) :
    f • x.1 (n + 1) = moduleSectionsMap (quotUp f M n) U (x.1 n) := by
  rw [← formalLimit_compat f M U x n, ← moduleSectionsMap_comp_apply,
    quotLe_comp_quotUp, moduleSectionsMap_lsmul]

/-- Multiplication by `f` from level `n` to level `n + 1`, followed by the projection back to
level `n`, is multiplication by `f`. -/
theorem smul_level' (n : ℕ) (s : moduleSections (Quot f M n) U) :
    moduleSectionsMap (quotLe f M (Nat.le_succ n)) U
      (moduleSectionsMap (quotUp f M n) U s) = f • s := by
  rw [← moduleSectionsMap_comp_apply, quotUp_comp_quotLe, moduleSectionsMap_lsmul]

/-- A power of `f` annihilates the sections at the corresponding level of the tower. -/
theorem pow_smul_level_eq_zero (n : ℕ) (s : moduleSections (Quot f M n) U) :
    f ^ n • s = 0 :=
  smul_eq_zero_of_forall_smul_eq_zero (pow_smul_quot_eq_zero f M n) s

/-- If `s` at level `n` maps up to the level `n + 1` component of `x`, then `f • s` is the level
`n` component of `x`. -/
private theorem smul_eq_of_moduleSectionsMap_quotUp_eq (x : formalLimit f M U) (n : ℕ)
    (s : moduleSections (Quot f M n) U)
    (h : moduleSectionsMap (quotUp f M n) U s = x.1 (n + 1)) : f • s = x.1 n := by
  rw [← smul_level' f M U n s, h]
  exact formalLimit_compat f M U x n

variable (hf : IsSMulRegular (M : Type v) f)
include hf

/-- The map on sections induced by multiplication by `f` from level `n` to level `n + 1` is
injective. -/
private theorem injective_moduleSectionsMap_quotUp (n : ℕ) :
    Function.Injective (moduleSectionsMap (quotUp f M n) U) :=
  injective_moduleSectionsMap (quotUp f M n) (injective_quotUp f M hf n) U

/-! ### The conclusions of Tag 0BLB -/

/-- **`f` is a nonzerodivisor on the inverse limit.** -/
theorem isSMulRegular_formalLimit : IsSMulRegular (formalLimit f M U) f := by
  refine IsSMulRegular.of_right_eq_zero_of_smul fun z hz ↦ formalLimit_ext f M U fun n ↦ ?_
  have hzn : f • z.1 (n + 1) = 0 := congrFun (congrArg Subtype.val hz) (n + 1)
  rw [smul_level] at hzn
  exact injective_moduleSectionsMap_quotUp f M U hf n (hzn.trans (map_zero _).symm)

/-- A member of the limit vanishing at level one is `f` times a member of the limit, in a way
compatible with the tower. -/
theorem exists_smul_eq_of_level_one_eq_zero (x : formalLimit f M U) (hx : x.1 1 = 0) :
    ∃ y : formalLimit f M U, f • y = x ∧
      ∀ n, moduleSectionsMap (quotUp f M n) U (y.1 n) = x.1 (n + 1) := by
  classical
  have hlift : ∀ n : ℕ, ∃ w : moduleSections (Quot f M n) U,
      moduleSectionsMap (quotUp f M n) U w = x.1 (n + 1) := by
    intro n
    refine exists_moduleSectionsMap_eq_of_map_eq_zero (quotUp f M n)
      (quotLe f M (show 1 ≤ n + 1 by omega)) (injective_quotUp f M hf n)
      (exact_quotUp_quotLe f M n) U (x.1 (n + 1)) ?_
    rw [formalLimit_proj f M U x (show 1 ≤ n + 1 by omega), hx]
  choose y hy using hlift
  have hcompat : ∀ n : ℕ,
      moduleSectionsMap (quotLe f M (Nat.le_succ n)) U (y (n + 1)) = y n := by
    intro n
    refine injective_moduleSectionsMap_quotUp f M U hf n ?_
    rw [hy n, ← moduleSectionsMap_comp_apply, quotLe_comp_quotUp, moduleSectionsMap_lsmul]
    exact smul_eq_of_moduleSectionsMap_quotUp_eq f M U x (n + 1) (y (n + 1)) (hy (n + 1))
  refine ⟨⟨y, hcompat⟩, formalLimit_ext f M U fun n ↦ ?_, hy⟩
  show f • y n = x.1 n
  exact smul_eq_of_moduleSectionsMap_quotUp_eq f M U x n (y n) (hy n)

/-- **The kernel of the projection to level `n` is `fⁿ` times the limit.** -/
theorem exists_pow_smul_eq_of_proj_eq_zero :
    ∀ (n : ℕ) (x : formalLimit f M U), x.1 n = 0 → ∃ y : formalLimit f M U, f ^ n • y = x := by
  intro n
  induction n with
  | zero => exact fun x _ ↦ ⟨x, by rw [pow_zero, one_smul]⟩
  | succ n ih =>
    intro x hx
    have hx1 : x.1 1 = 0 := by
      rw [← formalLimit_proj f M U x (show 1 ≤ n + 1 by omega), hx, map_zero]
    obtain ⟨y, hyx, hyup⟩ := exists_smul_eq_of_level_one_eq_zero f M U hf x hx1
    have hyn : y.1 n = 0 := by
      refine injective_moduleSectionsMap_quotUp f M U hf n ?_
      rw [hyup n, hx, map_zero]
    obtain ⟨z, hz⟩ := ih y hyn
    exact ⟨z, by rw [pow_succ', mul_smul, hz, hyx]⟩

omit hf

/-- Conversely an element of `fⁿ` times the limit vanishes at level `n`. -/
theorem proj_eq_zero_of_mem_pow_smul (n : ℕ) (x y : formalLimit f M U) (h : f ^ n • y = x) :
    x.1 n = 0 := by
  subst h
  exact pow_smul_level_eq_zero f M U n (y.1 n)

/-! ### Finiteness -/

/-- The projection of the limit to level `n`. -/
def levelAt (n : ℕ) : formalLimit f M U →ₗ[A] moduleSections (Quot f M n) U where
  toFun x := x.1 n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The projection to level `n` evaluates a member of the limit at `n`. -/
@[simp]
theorem levelAt_apply (n : ℕ) (x : formalLimit f M U) : levelAt f M U n x = x.1 n := rfl

/-- The projection of the limit to level one. -/
def levelOne : formalLimit f M U →ₗ[A] moduleSections (Quot f M 1) U where
  toFun x := x.1 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

include hf in
/-- The kernel of the projection of the limit to level one is `f` times the limit. -/
theorem ker_levelOne :
    LinearMap.ker (levelOne f M U) = Ideal.span {f} • (⊤ : Submodule A (formalLimit f M U)) := by
  rw [Submodule.ideal_span_singleton_smul]
  ext x
  simp only [LinearMap.mem_ker, Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top,
    true_and]
  refine ⟨fun hx ↦ (exists_smul_eq_of_level_one_eq_zero f M U hf x hx).imp fun _ h ↦ h.1, ?_⟩
  rintro ⟨y, rfl⟩
  show f • y.1 1 = 0
  simpa using pow_smul_level_eq_zero f M U 1 (y.1 1)

include hf in
/-- **The inverse limit is a finite module**, when the base is Noetherian and `f`-adically
complete and the sections at level one are finite. -/
theorem finite_formalLimit [IsNoetherianRing A] [IsPrecomplete (Ideal.span {f}) A]
    (hfin : Module.Finite A (moduleSections (Quot f M 1) U)) :
    Module.Finite A (formalLimit f M U) := by
  have hsep : ⨅ n : ℕ, (Ideal.span {f}) ^ n • (⊤ : Submodule A (formalLimit f M U)) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    refine formalLimit_ext f M U fun n ↦ ?_
    have hxn := (Submodule.mem_iInf _).1 hx n
    rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at hxn
    obtain ⟨y, -, rfl⟩ := hxn
    exact pow_smul_level_eq_zero f M U n (y.1 n)
  have hquot : Module.Finite (A ⧸ Ideal.span {f})
      (formalLimit f M U ⧸ (Ideal.span {f}) • (⊤ : Submodule A (formalLimit f M U))) := by
    have : IsNoetherian A (moduleSections (Quot f M 1) U) :=
      isNoetherian_of_isNoetherianRing_of_finite A _
    have hrange : Module.Finite A (LinearMap.range (levelOne f M U)) :=
      Module.Finite.of_fg (IsNoetherian.noetherian _)
    have : Module.Finite A
        (formalLimit f M U ⧸ (Ideal.span {f}) • (⊤ : Submodule A (formalLimit f M U))) := by
      rw [← ker_levelOne f M U hf]
      exact Module.Finite.equiv (levelOne f M U).quotKerEquivRange.symm
    exact Module.Finite.of_restrictScalars_finite A (A ⧸ Ideal.span {f}) _
  exact Module.Finite.of_iInf_pow_smul_top_eq_bot_of_finite_quotient_smul_top
    (Ideal.span {f}) hsep hquot

end Stacks.Algebraization.FormalSections

end
