module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import StacksFrontier.Algebra.DirectSum.RangeGrading

/-!
# The total graded module of a cochain complex

A cochain complex `M` of `R`-modules has a total graded module `⨁ p, M^p`, with the tautological
grading of a direct sum and the differential assembled from the differentials of `M`. A degree-`n`
cochain of `M` assembles to an endomorphism of that total module; because the total module is used
as the carrier of a *right* differential graded module, the assembly carries the Koszul sign
`(-1)^{np}` on the degree-`p` summand.

## Main definitions

* `CochainComplex.totalModule`: the total graded module `⨁ p, M^p`.
* `CochainComplex.signedTotalCochain`: the signed endomorphism assembled from a cochain, and
  `CochainComplex.signedTotalCochainLinear`, its `R`-linearity in the cochain.
* `CochainComplex.totalDifferential`: the differential of the total module.

## Main results

* `CochainComplex.signedTotalCochain_lof`: the assembled endomorphism on a summand.
* `CochainComplex.signedTotalCochain_comp`: composition of cochains becomes composition of the
  assembled endomorphisms, in the opposite order and with the Koszul sign of the two degrees.
* `CochainComplex.signedTotalCochain_id`: the identity cochain assembles to the identity.
* `CochainComplex.totalDifferential_square`: the differential squares to zero.

## Implementation notes

The grading of the total module is the tautological one, `DirectSum.rangeGrading`, with its
pieces identified with the summands by `DirectSum.rangeGradingEquiv`, so nothing has to be
re-proved about them here.
The sign bookkeeping in `signedTotalCochain_comp` is the identity
`(-1)^{(m+n)p} = (-1)^{nm} (-1)^{m(p+n)} (-1)^{np}`, which is where the Koszul sign of the
composition comes from.

## References

* [Stacks Project, Tag 0FQ5](https://stacks.math.columbia.edu/tag/0FQ5)
-/

@[expose] public section

open CategoryTheory CochainComplex.HomComplex
open scoped DirectSum

namespace CochainComplex

universe u

variable {R : Type u} [CommRing R]

/-- The total graded module `⨁ p, M^p` of a cochain complex of `R`-modules. -/
abbrev totalModule (M : CochainComplex (ModuleCat.{u} R) ℤ) : Type u := ⨁ p, M.X p

/-- The degree-`p` piece of the total graded module. -/
abbrev totalGrading (M : CochainComplex (ModuleCat.{u} R) ℤ) (p : ℤ) :
    Submodule R (totalModule M) :=
  DirectSum.rangeGrading R (fun q => M.X q) p

/-- The identification of the degree-`p` piece of the total module with `M^p`. -/
noncomputable def totalComponentEquiv (M : CochainComplex (ModuleCat.{u} R) ℤ) (p : ℤ) :
    M.X p ≃ₗ[R] totalGrading M p :=
  (DirectSum.rangeGradingEquiv R (fun q => M.X q) p).symm

/-- The image of `x : M^p` in the total module under `totalComponentEquiv` is its inclusion
`DirectSum.lof` into the degree-`p` summand. -/
theorem totalComponentEquiv_coe (M : CochainComplex (ModuleCat.{u} R) ℤ) (p : ℤ) (x : M.X p) :
    (totalComponentEquiv M p x : totalModule M) = DirectSum.lof R ℤ (fun q => M.X q) p x := by
  have h2 : (DirectSum.rangeGradingEquiv R (fun q => M.X q) p).symm x =
      ⟨DirectSum.of (fun q => M.X q) p x,
        ⟨x, DirectSum.lof_eq_of R ℤ (fun q => M.X q) p x⟩⟩ :=
    (LinearEquiv.symm_apply_eq _).2
      (DirectSum.rangeGradingEquiv_apply_of R (fun q => M.X q) p x).symm
  rw [totalComponentEquiv, h2]
  exact (DirectSum.lof_eq_of R ℤ (fun q => M.X q) p x).symm

/-- The signed endomorphism of the total module assembled from a degree-`n` cochain: on the
degree-`p` summand it is `(-1)^{np}` times the component of the cochain. -/
def signedTotalCochain (M : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (f : Cochain M M n) : totalModule M →ₗ[R] totalModule M :=
  DirectSum.toModule R ℤ (totalModule M) fun p =>
    (((n * p).negOnePow.val : ℤ) : R) •
      ((DirectSum.lof R ℤ (fun q => M.X q) (p + n)) ∘ₗ (f.v p (p + n) (by omega)).hom)

/-- On the degree-`p` summand, `signedTotalCochain` sends `x` to `(-1)^{np}` times the component
`f^{p, p+n} x`, placed in the degree-`(p+n)` summand. -/
theorem signedTotalCochain_lof (M : CochainComplex (ModuleCat.{u} R) ℤ) (n p : ℤ)
    (f : Cochain M M n) (x : M.X p) :
    signedTotalCochain M n f (DirectSum.lof R ℤ (fun q => M.X q) p x) =
      DirectSum.lof R ℤ (fun q => M.X q) (p + n)
        ((((n * p).negOnePow.val : ℤ) : R) • ((f.v p (p + n) (by omega)).hom x)) := by
  rw [signedTotalCochain, DirectSum.toModule_lof]
  simp

/-- The differential of the total module of a cochain complex. -/
def totalDifferential (M : CochainComplex (ModuleCat.{u} R) ℤ) :
    totalModule M →ₗ[R] totalModule M :=
  DirectSum.toModule R ℤ (totalModule M) fun p =>
    (DirectSum.lof R ℤ (fun q => M.X q) (p + 1)) ∘ₗ (M.d p (p + 1)).hom

/-- On the degree-`p` summand, the total differential is the differential `d^p` of `M`, landing in
the degree-`(p+1)` summand. -/
theorem totalDifferential_lof (M : CochainComplex (ModuleCat.{u} R) ℤ) (p : ℤ) (x : M.X p) :
    totalDifferential M (DirectSum.lof R ℤ (fun q => M.X q) p x) =
      DirectSum.lof R ℤ (fun q => M.X q) (p + 1) ((M.d p (p + 1)).hom x) := by
  rw [totalDifferential, DirectSum.toModule_lof]
  simp

/-- Two linear maps out of the total module agree if they agree on every summand. -/
private theorem totalModule_linearMap_ext {M : CochainComplex (ModuleCat.{u} R) ℤ} {N : Type*}
    [AddCommGroup N] [Module R N] {f g : totalModule M →ₗ[R] N}
    (h : ∀ (p : ℤ) (x : M.X p), f (DirectSum.lof R ℤ (fun q => M.X q) p x) =
      g (DirectSum.lof R ℤ (fun q => M.X q) p x)) : f = g :=
  DirectSum.linearMap_ext R fun p => LinearMap.ext (h p)

/-- The total differential squares to zero: `d ∘ d = 0` on the total module. -/
theorem totalDifferential_square (M : CochainComplex (ModuleCat.{u} R) ℤ) :
    totalDifferential M ∘ₗ totalDifferential M = 0 := by
  refine totalModule_linearMap_ext fun p x => ?_
  rw [LinearMap.comp_apply, totalDifferential_lof, totalDifferential_lof]
  have h := congrArg ModuleCat.Hom.hom (M.d_comp_d p (p + 1) (p + 1 + 1))
  rw [ModuleCat.hom_comp] at h
  have hx := congrArg (fun f : M.X p →ₗ[R] M.X (p + 1 + 1) => f x) h
  simpa using congrArg (DirectSum.lof R ℤ (fun q => M.X q) (p + 1 + 1)) hx

/-- The signed assembly of a cochain, as an `R`-linear map on cochains. -/
noncomputable def signedTotalCochainLinear (M : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    Cochain M M n →ₗ[R] Module.End R (totalModule M) where
  toFun f := signedTotalCochain M n f
  map_add' f g := by
    refine LinearMap.ext fun x => ?_
    induction x using DirectSum.induction_on with
    | zero => simp [signedTotalCochain]
    | add x y hx hy => simp only [map_add, hx, hy]
    | of p x =>
      rw [← DirectSum.lof_eq_of R ℤ (fun q => M.X q) p x]
      simp only [signedTotalCochain_lof, Cochain.add_v, ModuleCat.hom_add, LinearMap.add_apply,
        smul_add, map_add]
  map_smul' r f := by
    refine LinearMap.ext fun x => ?_
    induction x using DirectSum.induction_on with
    | zero => simp [signedTotalCochain]
    | add x y hx hy => simp only [map_add, hx, hy]
    | of p x =>
      rw [← DirectSum.lof_eq_of R ℤ (fun q => M.X q) p x]
      simp only [signedTotalCochain_lof, Cochain.smul_v, ModuleCat.hom_smul,
        LinearMap.smul_apply, map_smul, RingHom.id_apply]
      exact smul_comm _ _ _

/-- `signedTotalCochain` commutes with scalar multiplication of the cochain. -/
theorem signedTotalCochain_smul (M : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) (r : R)
    (f : Cochain M M n) :
    signedTotalCochain M n (r • f) = r • signedTotalCochain M n f :=
  map_smul (signedTotalCochainLinear M n) r f

/-- Including a component `g^{a,b} y` of a cochain into the total module only depends on the
target index `b` up to equality. -/
private theorem lof_cochain_v_congr (M : CochainComplex (ModuleCat.{u} R) ℤ) {m : ℤ}
    (g : Cochain M M m) {a b b' : ℤ} (h : b = b') (hb : a + m = b) (y : M.X a) :
    DirectSum.lof R ℤ (fun j => M.X j) b ((g.v a b hb).hom y) =
      DirectSum.lof R ℤ (fun j => M.X j) b' ((g.v a b' (hb.trans h)).hom y) := by
  subst h
  rfl

/-- Composition of cochains becomes composition of the assembled endomorphisms, in the opposite
order and with the Koszul sign of the two degrees. -/
theorem signedTotalCochain_comp (M : CochainComplex (ModuleCat.{u} R) ℤ) (n m : ℤ)
    (f : Cochain M M n) (g : Cochain M M m) :
    signedTotalCochain M (m + n) (f.comp g (by omega)) =
      (((n * m).negOnePow.val : ℤ) : R) •
        (signedTotalCochain M m g ∘ₗ signedTotalCochain M n f) := by
  refine totalModule_linearMap_ext fun p x => ?_
  have hsign : ((m + n) * p).negOnePow =
      (n * m).negOnePow * (m * (p + n)).negOnePow * (n * p).negOnePow := by
    rw [← Int.negOnePow_add, ← Int.negOnePow_add,
      show n * m + m * (p + n) + n * p = (m + n) * p + 2 * (n * m) by ring,
      Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]
  rw [signedTotalCochain_lof, LinearMap.smul_apply, LinearMap.comp_apply,
    signedTotalCochain_lof, signedTotalCochain_lof,
    Cochain.comp_v f g (by omega) p (p + n) (p + (m + n)) (by omega) (by omega),
    ModuleCat.hom_comp, LinearMap.comp_apply]
  simp only [map_smul, smul_smul]
  rw [lof_cochain_v_congr M g (by omega : p + (m + n) = p + n + m), hsign]
  simp only [Units.val_mul, Int.cast_mul, mul_assoc]

/-- Including `x : M^p` into the total module after transporting it along `p = q` agrees with
including `x` directly. -/
theorem lof_eqToHom (M : CochainComplex (ModuleCat.{u} R) ℤ) {p q : ℤ} (h : p = q)
    (x : M.X p) :
    DirectSum.lof R ℤ (fun j => M.X j) q ((ModuleCat.Hom.hom (eqToHom (congrArg M.X h))) x) =
      DirectSum.lof R ℤ (fun j => M.X j) p x := by
  cases h
  rfl

/-- The identity cochain assembles to the identity endomorphism of the total module. -/
theorem signedTotalCochain_id (M : CochainComplex (ModuleCat.{u} R) ℤ) :
    signedTotalCochain M 0 (Cochain.ofHom (𝟙 M)) = 1 := by
  refine totalModule_linearMap_ext fun p x => ?_
  rw [signedTotalCochain_lof]
  simpa [Cochain.ofHom, Cochain.ofHoms, HomologicalComplex.id_f] using
    lof_eqToHom M (add_zero p).symm x

end CochainComplex
