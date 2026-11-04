module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import StacksFrontier.CategoryTheory.GradedObject.ModuleCatMonoidal

/-!
# Tensor products of graded modules from a bijective pairing

Let `R` be a commutative ring and let `M`, `N`, `P` be `R`-modules graded by `ℤ`, through
submodules `𝒜 p ⊆ M`, `ℬ q ⊆ N`, `𝒞 n ⊆ P` with `M = ⨁ₚ 𝒜 p` and so on
(`DirectSum.Decomposition`). Let `κ : M ⊗_R N → P` be a linear bijection sending `𝒜 p ⊗ ℬ q`
into `𝒞 (p + q)`. Then `κ` is an isomorphism of graded modules: for every `n` the map
`⨁_{p+q=n} 𝒜 p ⊗_R ℬ q → 𝒞 n` it induces is bijective. This file packages it as an isomorphism
`𝒜 ⊗ ℬ ≅ 𝒞` in the monoidal category `GradedObject ℤ (ModuleCat R)` (Stacks, Homology,
Example 0FFX). The typical case is the Künneth map `a ⊗ b ↦ pr₁^*a ∪ pr₂^*b` of a Weil
cohomology theory, axiom (B)(a) of Stacks Section 0FHA.

## Main definitions

* `CategoryTheory.GradedObject.Monoidal.gradedModule`: the graded object `n ↦ 𝒜 n`.
* `CategoryTheory.GradedObject.Monoidal.kunnethIso`: the isomorphism `𝒜 ⊗ ℬ ≅ 𝒞` induced by `κ`.

## Main results

* `CategoryTheory.GradedObject.Monoidal.kunnethIso_hom_apply`: on the summand `𝒜 p ⊗ ℬ q`,
  `kunnethIso` is `a ⊗ b ↦ κ (a ⊗ b)`.

## References

* [Stacks Project, Tag 0FFX](https://stacks.math.columbia.edu/tag/0FFX)
* [Stacks Project, Section 0FHA](https://stacks.math.columbia.edu/tag/0FHA)
-/

@[expose] public noncomputable section

namespace CategoryTheory.GradedObject.Monoidal

open CategoryTheory Category Limits MonoidalCategory DirectSum
open scoped TensorProduct

universe w

variable {R : Type w} [CommRing R]

/-- The graded module `n ↦ 𝒜 n` of a family of submodules, as an object of
`GradedObject ℤ (ModuleCat R)`. -/
abbrev gradedModule {M : Type w} [AddCommGroup M] [Module R M] (𝒜 : ℤ → Submodule R M) :
    GradedObject ℤ (ModuleCat.{w} R) :=
  fun n ↦ ModuleCat.of R (𝒜 n)

variable {M N P : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P] (𝒜 : ℤ → Submodule R M) (ℬ : ℤ → Submodule R N)
  (𝒞 : ℤ → Submodule R P) [Decomposition 𝒜] [Decomposition ℬ]
  [Decomposition 𝒞] (κ : M ⊗[R] N →ₗ[R] P)
  (hκ : ∀ (p q : ℤ) (a : M) (b : N), a ∈ 𝒜 p → b ∈ ℬ q → κ (a ⊗ₜ b) ∈ 𝒞 (p + q))

include hκ in
/-- `κ` maps `𝒜 p ⊗ ℬ q` into `𝒞 n` for `p + q = n`. -/
theorem kunnethBlock_mem (p q n : ℤ) (h : p + q = n) (t : 𝒜 p ⊗[R] ℬ q) :
    κ (TensorProduct.map (𝒜 p).subtype (ℬ q).subtype t) ∈ 𝒞 n := by
  subst h
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => exact hκ p q a b a.2 b.2
  | add t t' ht ht' => rw [map_add, map_add]; exact Submodule.add_mem _ ht ht'

/-- The map `𝒜 p ⊗ ℬ q ⟶ 𝒞 n`, `a ⊗ b ↦ κ (a ⊗ b)`, for `p + q = n`. -/
def kunnethBlock (p q n : ℤ) (h : p + q = n) :
    gradedModule 𝒜 p ⊗ gradedModule ℬ q ⟶ gradedModule 𝒞 n :=
  ModuleCat.ofHom ((κ ∘ₗ TensorProduct.map (𝒜 p).subtype (ℬ q).subtype).codRestrict (𝒞 n)
    (kunnethBlock_mem 𝒜 ℬ 𝒞 κ hκ p q n h))

/-- The degree-`n` part `(𝒜 ⊗ ℬ)ⁿ ⟶ 𝒞 n` of the map induced by `κ`. -/
def kunnethHom (n : ℤ) : (gradedModule 𝒜 ⊗ gradedModule ℬ) n ⟶ gradedModule 𝒞 n :=
  tensorObjDesc fun p q h ↦ kunnethBlock 𝒜 ℬ 𝒞 κ hκ p q n h

/-- On the summand `𝒜 p ⊗ ℬ q`, `kunnethHom` is `a ⊗ b ↦ κ (a ⊗ b)`. -/
theorem kunnethHom_apply (p q n : ℤ) (h : p + q = n) (a : 𝒜 p) (b : ℬ q) :
    (kunnethHom 𝒜 ℬ 𝒞 κ hκ n).hom
        ((ιTensorObj (gradedModule 𝒜) (gradedModule ℬ) p q n h).hom (a ⊗ₜ b)) =
      ⟨κ ((a : M) ⊗ₜ (b : N)), h ▸ hκ p q a b a.2 b.2⟩ :=
  congrArg (fun φ ↦ φ.hom (a ⊗ₜ[R] b))
    (ι_tensorObjDesc (X₁ := gradedModule 𝒜) (X₂ := gradedModule ℬ)
      (fun p q h ↦ kunnethBlock 𝒜 ℬ 𝒞 κ hκ p q n h) p q h)

/-- The degree-`n` components `M ⊗ N ⟶ (𝒜 ⊗ ℬ)ⁿ`,
`a ⊗ b ↦ ∑ₚ aₚ ⊗ b_{n-p}`, for each fixed `p`. -/
def kunnethSplitPiece (n p : ℤ) : 𝒜 p →ₗ[R] N →ₗ[R] (gradedModule 𝒜 ⊗ gradedModule ℬ) n :=
  ((TensorProduct.mk R (𝒜 p) (ℬ (n - p))).compl₂
      ((DirectSum.component R ℤ (fun q ↦ ℬ q) (n - p)).comp
        (DirectSum.decomposeLinearEquiv ℬ).toLinearMap)).compr₂
    (ιTensorObj (gradedModule 𝒜) (gradedModule ℬ) p (n - p) n (add_sub_cancel p n)).hom

/-- The splitting `M ⊗ N ⟶ (𝒜 ⊗ ℬ)ⁿ`, `a ⊗ b ↦ ∑ₚ aₚ ⊗ b_{n-p}`. -/
def kunnethSplit (n : ℤ) : M ⊗[R] N →ₗ[R] (gradedModule 𝒜 ⊗ gradedModule ℬ) n :=
  TensorProduct.lift ((DirectSum.toModule R ℤ _ (kunnethSplitPiece 𝒜 ℬ n)).comp
    (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap)

/-- For `a ∈ 𝒜 p`, `kunnethSplit` sends `a ⊗ b` to `a ⊗ b_{n-p}` in the summand
`𝒜 p ⊗ ℬ (n - p)`. -/
theorem kunnethSplit_tmul_of_mem {p : ℤ} (a : M) (ha : a ∈ 𝒜 p) (b : N) (n : ℤ) :
    kunnethSplit 𝒜 ℬ n (a ⊗ₜ b) =
      (ιTensorObj (gradedModule 𝒜) (gradedModule ℬ) p (n - p) n (add_sub_cancel p n)).hom
        (⟨a, ha⟩ ⊗ₜ DirectSum.decompose ℬ b (n - p)) := by
  simp only [kunnethSplit, TensorProduct.lift.tmul, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, DirectSum.decomposeLinearEquiv_apply]
  rw [DirectSum.decompose_of_mem 𝒜 ha, ← DirectSum.lof_eq_of R, DirectSum.toModule_lof]
  rfl

/-- The splitting is a section of the inclusions of the summands. -/
theorem kunnethSplit_tmul (p q n : ℤ) (h : p + q = n) (a : 𝒜 p) (b : ℬ q) :
    kunnethSplit 𝒜 ℬ n ((a : M) ⊗ₜ (b : N)) =
      (ιTensorObj (gradedModule 𝒜) (gradedModule ℬ) p q n h).hom (a ⊗ₜ b) := by
  obtain rfl : q = n - p := by omega
  rw [kunnethSplit_tmul_of_mem 𝒜 ℬ (a : M) a.2, DirectSum.decompose_coe]
  simp

omit [Decomposition 𝒞] in
/-- The component of `of x` in the degree of `x`, written through an equality of degrees. -/
theorem coe_component_of_eq {i j : ℤ} (h : i = j) (x : 𝒞 i) :
    ((DirectSum.component R ℤ (fun n ↦ 𝒞 n) j (DirectSum.of (fun n ↦ 𝒞 n) i x) : 𝒞 j) : P) =
      x := by
  subst h
  rw [← DirectSum.lof_eq_of R, DirectSum.component.lof_self]

include hκ in
/-- `κ` followed by the projection onto `𝒞 n` is the splitting followed by the map induced
by `κ`. -/
theorem kunnethHom_comp_kunnethSplit (n : ℤ) :
    (kunnethHom 𝒜 ℬ 𝒞 κ hκ n).hom ∘ₗ kunnethSplit 𝒜 ℬ n =
      (DirectSum.component R ℤ (fun n ↦ 𝒞 n) n).comp
        ((DirectSum.decomposeLinearEquiv 𝒞).toLinearMap ∘ₗ κ) := by
  refine TensorProduct.ext' fun a b ↦ ?_
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add a a' ha ha' => simp only [TensorProduct.add_tmul, map_add, ha, ha']
  | @homogeneous p a =>
    induction b using DirectSum.Decomposition.inductionOn ℬ with
    | zero => simp
    | add b b' hb hb' => simp only [TensorProduct.tmul_add, map_add, hb, hb']
    | @homogeneous q b =>
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        DirectSum.decomposeLinearEquiv_apply]
      have hc := hκ p q a b a.2 b.2
      rw [kunnethSplit_tmul_of_mem 𝒜 ℬ (a : M) a.2, DirectSum.decompose_of_mem 𝒞 hc]
      by_cases hq : q = n - p
      · subst hq
        rw [DirectSum.decompose_coe, DirectSum.of_eq_same]
        have := kunnethHom_apply 𝒜 ℬ 𝒞 κ hκ p (n - p) n (add_sub_cancel p n) ⟨a, a.2⟩ b
        refine this.trans (Subtype.ext ?_)
        exact (coe_component_of_eq 𝒞 (add_sub_cancel p n) ⟨κ ((a : M) ⊗ₜ (b : N)), hc⟩).symm
      · rw [DirectSum.decompose_coe, DirectSum.of_eq_of_ne _ _ _ (Ne.symm hq),
          TensorProduct.tmul_zero, map_zero, map_zero, ← DirectSum.lof_eq_of R,
          DirectSum.component.of, dif_neg (by omega)]

variable (hbij : Function.Bijective κ)

/-- The inverse of `kunnethHom`: `c ↦ split (κ⁻¹ c)`. -/
def kunnethInv (n : ℤ) : gradedModule 𝒞 n ⟶ (gradedModule 𝒜 ⊗ gradedModule ℬ) n :=
  ModuleCat.ofHom (kunnethSplit 𝒜 ℬ n ∘ₗ (LinearEquiv.ofBijective κ hbij).symm.toLinearMap ∘ₗ
    (𝒞 n).subtype)

include hbij in
/-- The composite `kunnethInv ≫ kunnethHom` is the identity of `𝒞 n`. -/
theorem kunnethHom_kunnethInv (n : ℤ) :
    kunnethInv 𝒜 ℬ 𝒞 κ hbij n ≫ kunnethHom 𝒜 ℬ 𝒞 κ hκ n = 𝟙 _ := by
  refine ModuleCat.hom_ext (LinearMap.ext fun c ↦ ?_)
  have h := LinearMap.congr_fun (kunnethHom_comp_kunnethSplit 𝒜 ℬ 𝒞 κ hκ n)
    ((LinearEquiv.ofBijective κ hbij).symm c)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    DirectSum.decomposeLinearEquiv_apply] at h
  have hκc : κ ((LinearEquiv.ofBijective κ hbij).symm c) = c :=
    (LinearEquiv.ofBijective κ hbij).apply_symm_apply c
  rwa [hκc, DirectSum.decompose_coe, ← DirectSum.lof_eq_of R, DirectSum.component.lof_self] at h

include hbij in
/-- The composite `kunnethHom ≫ kunnethInv` is the identity of `(𝒜 ⊗ ℬ)ⁿ`. -/
theorem kunnethInv_kunnethHom (n : ℤ) :
    kunnethHom 𝒜 ℬ 𝒞 κ hκ n ≫ kunnethInv 𝒜 ℬ 𝒞 κ hbij n = 𝟙 _ := by
  refine tensorObj_hom_ext fun p q h a b ↦ ?_
  change kunnethSplit 𝒜 ℬ n ((LinearEquiv.ofBijective κ hbij).symm
    ((kunnethHom 𝒜 ℬ 𝒞 κ hκ n).hom _ : P)) = _
  rw [kunnethHom_apply, LinearEquiv.ofBijective_symm_apply_apply, kunnethSplit_tmul 𝒜 ℬ p q n h]
  rfl

/-- **The isomorphism `𝒜 ⊗ ℬ ≅ 𝒞` of graded modules induced by a bijective `κ` of degree
zero.** -/
def kunnethIso : gradedModule 𝒜 ⊗ gradedModule ℬ ≅ gradedModule 𝒞 :=
  GradedObject.isoMk _ _ fun n ↦
    { hom := kunnethHom 𝒜 ℬ 𝒞 κ hκ n
      inv := kunnethInv 𝒜 ℬ 𝒞 κ hbij n
      hom_inv_id := kunnethInv_kunnethHom 𝒜 ℬ 𝒞 κ hκ hbij n
      inv_hom_id := kunnethHom_kunnethInv 𝒜 ℬ 𝒞 κ hκ hbij n }

/-- On the summand `𝒜 p ⊗ ℬ q`, `kunnethIso` is `a ⊗ b ↦ κ (a ⊗ b)`. -/
theorem kunnethIso_hom_apply (p q n : ℤ) (h : p + q = n) (a : 𝒜 p) (b : ℬ q) :
    ((kunnethIso 𝒜 ℬ 𝒞 κ hκ hbij).hom n).hom
        ((ιTensorObj (gradedModule 𝒜) (gradedModule ℬ) p q n h).hom (a ⊗ₜ b)) =
      ⟨κ ((a : M) ⊗ₜ (b : N)), h ▸ hκ p q a b a.2 b.2⟩ :=
  kunnethHom_apply 𝒜 ℬ 𝒞 κ hκ p q n h a b

end CategoryTheory.GradedObject.Monoidal

end
