module

public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.SimpleModule.Basic
public import StacksCore.RingTheory.Morita.End

/-!
# Modules over a finite simple algebra

Let `A` be a finite simple algebra over a field `k`. This file completes the statements of
Stacks 074E about the simple `A`-modules and their endomorphism algebras.

## Main results

* `exists_isSimpleModule_and_linearEquiv_of_finite_simple`: there is a simple `A`-module, and
  any two simple `A`-modules are isomorphic.
* `isSimpleModule_and_end_algEquiv_of_wedderburn`: if `A ≃ₐ[k] Mₙ(K)` with `K` a skew field
  finite over `k`, then `Kⁿ` is a simple `A`-module whose endomorphism algebra is `Kᵐᵒᵖ`.
* `centerEquivCenterEnd`: for a simple `A`-module `M`, the centers of `A` and of
  `L = Module.End A M` are isomorphic `k`-algebras.
* `end_simple_module_properties`: for a simple `A`-module `M`, `L = Module.End A M` is a skew
  field finite over `k`, `A ≃ₐ[k] Module.End L M`, the centers of `A` and `L` agree and
  `[A : k] [L : k] = dim_k(M)²`.
* `exists_algEquiv_matrix_end_simple`: for a finite `A`-module `N`, `Module.End A N` is a matrix
  algebra over `L`.
* `toEndEndAlgHom_bijective_of_finite`: for a nonzero finite `A`-module `N` and
  `B = Module.End A N`, the natural map `A → Module.End B N` is bijective.
-/

@[expose] public section

universe u v w

variable (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A] [IsSimpleRing A]
  [Module.Finite k A]

open IsSimpleRing Matrix.Module

include k in
/-- Stacks 074E (1): a finite simple algebra `A` over a field has a simple module, and any two
simple `A`-modules are isomorphic. -/
@[stacks 074E "(1): existence and uniqueness of the simple module"]
theorem exists_isSimpleModule_and_linearEquiv_of_finite_simple :
    (∃ (M : Type v) (_ : AddCommGroup M) (_ : Module A M), IsSimpleModule A M) ∧
    ∀ (M N : Type w) [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
      [IsSimpleModule A M] [IsSimpleModule A N], Nonempty (M ≃ₗ[A] N) := by
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  refine ⟨?_, fun M N _ _ _ _ _ _ ↦ linearEquiv_of_isSimpleModule_over_simple_ring A M N⟩
  obtain ⟨n, hn, D, _, _, _, ⟨wdb⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite k A
  let _ : Module A (Fin n → D) := Module.compHom _ wdb.toRingEquiv.toRingHom
  exact ⟨Fin n → D, inferInstance, inferInstance, simple_mod_of_wedderburn k A D wdb⟩

omit [IsSimpleRing A] [Module.Finite k A] in
/-- Stacks 074E (4): if `A ≃ₐ[k] Mₙ(K)` with `K` a skew field finite over `k`, then `Kⁿ` is a
simple `A`-module and `End_A(Kⁿ) ≃ₐ[k] Kᵐᵒᵖ`. -/
@[stacks 074E "(4): `Kⁿ` is simple with endomorphism algebra `Kᵐᵒᵖ`"]
theorem isSimpleModule_and_end_algEquiv_of_wedderburn (n : ℕ) [NeZero n] (K : Type w)
    [DivisionRing K] [Algebra k K] [Module.Finite k K]
    (wdb : A ≃ₐ[k] Matrix (Fin n) (Fin n) K) :
    let _ : Module A (Fin n → K) := Module.compHom _ wdb.toRingEquiv.toRingHom
    IsSimpleModule A (Fin n → K) ∧ Nonempty (Module.End A (Fin n → K) ≃ₐ[k] Kᵐᵒᵖ) :=
  ⟨simple_mod_of_wedderburn k A K wdb, ⟨endSimpleModOfWedderburn k A n K wdb⟩⟩

section center

variable (M : Type v) [AddCommGroup M] [Module A M] [IsSimpleModule A M] [Module k M]
  [IsScalarTower k A M]

/-- Multiplication by a central element `a` of `A` is an `A`-linear endomorphism of `M`. -/
@[simps]
def centerToEnd (a : Subalgebra.center k A) : Module.End A M where
  toFun m := (a : A) • m
  map_add' := smul_add _
  map_smul' b m := by
    rw [smul_smul, RingHom.id_apply, smul_smul,
      (Subalgebra.mem_center_iff.1 a.2 b).symm]

/-- Multiplication by a central element of `A` lies in the center of `Module.End A M`. -/
def centerToCenterEnd : Subalgebra.center k A →ₐ[k] Subalgebra.center k (Module.End A M) where
  toFun a := ⟨centerToEnd k A M a, Subalgebra.mem_center_iff.2 fun f ↦
    LinearMap.ext fun m ↦ f.map_smul (a : A) m⟩
  map_one' := by ext; simp
  map_mul' a b := by
    ext x
    have h : (a : A) • (b : A) • x = (b : A) • (a : A) • x := by
      rw [smul_smul, smul_smul, Subalgebra.mem_center_iff.1 a.2 b]
    simpa [mul_smul] using h
  map_zero' := by ext; simp
  map_add' a b := by ext; simp [add_smul]
  commutes' c := by ext; simp [Algebra.algebraMap_eq_smul_one, smul_assoc]

/-- Stacks 074E (5): the centers of `A` and of `L = Module.End A M` agree for a simple
`A`-module `M`. -/
@[stacks 074E "(5): the centers of `A` and `End_A(M)` agree"]
noncomputable def centerEquivCenterEnd :
    Subalgebra.center k A ≃ₐ[k] Subalgebra.center k (Module.End A M) := by
  refine AlgEquiv.ofBijective (centerToCenterEnd k A M) ⟨fun a b h ↦ ?_, fun z ↦ ?_⟩
  · refine Subtype.ext <| toEndEnd_injective k A M <| LinearMap.ext fun m ↦ ?_
    exact LinearMap.congr_fun congr(($h).1) m
  · let g : Module.End (Module.End A M) M :=
      { toFun := (z : Module.End A M)
        map_add' := map_add _
        map_smul' f m := (LinearMap.congr_fun (Subalgebra.mem_center_iff.1 z.2 f) m).symm }
    obtain ⟨a, ha⟩ := (isBalanced_of_simpleMod k A M).surj g
    have ha' (m : M) : a • m = (z : Module.End A M) m := LinearMap.congr_fun ha m
    have hc : a ∈ Subalgebra.center k A := Subalgebra.mem_center_iff.2 fun b ↦
      toEndEnd_injective k A M <| LinearMap.ext fun m ↦ by
        simp only [toEndEnd_apply, DistribSMul.toLinearMap_apply, mul_smul, ha',
          (z : Module.End A M).map_smul]
    exact ⟨⟨a, hc⟩, Subtype.ext <| LinearMap.ext fun m ↦ ha' m⟩

/-- Stacks 074E (5): for a simple module `M` over a finite simple `k`-algebra `A`, the algebra
`L = Module.End A M` is a skew field finite over `k` acting on `M`, the natural map
`A → Module.End L M` is a `k`-algebra isomorphism, the centers of `A` and `L` agree, and
`[A : k] [L : k] = dim_k(M)²`. -/
@[stacks 074E "(5)"]
theorem end_simple_module_properties :
    (∀ f : Module.End A M, f ≠ 0 → IsUnit f) ∧ Module.Finite k (Module.End A M) ∧
    Function.Bijective (toEndEndAlgHom k A M) ∧
    Nonempty (Subalgebra.center k A ≃ₐ[k] Subalgebra.center k (Module.End A M)) ∧
    Module.finrank k A * Module.finrank k (Module.End A M) = Module.finrank k M ^ 2 :=
  ⟨fun _ hf ↦ (Module.End.isUnit_iff _).2 (LinearMap.bijective_of_ne_zero hf),
    end_simple_mod_finite k A M,
    (endEndIso k A M).bijective, ⟨centerEquivCenterEnd k A M⟩, finrank_mul_finrank_end k A M⟩

end center

section finite

variable (M N : Type v) [AddCommGroup M] [Module A M] [IsSimpleModule A M]
  [AddCommGroup N] [Module A N] [Module.Finite A N] [Module k N] [IsScalarTower k A N]

/-- Stacks 074E (6): for a simple `A`-module `M` and a finite `A`-module `N`, the algebra
`Module.End A N` is a matrix algebra over the skew field `Module.End A M`. -/
@[stacks 074E "(6): `End_A(N)` is a matrix algebra over `End_A(M)`"]
theorem exists_algEquiv_matrix_end_simple [Module k M] [IsScalarTower k A M] :
    ∃ m : ℕ, Nonempty (Module.End A N ≃ₐ[k] Matrix (Fin m) (Fin m) (Module.End A M)) := by
  classical
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  obtain ⟨ι, ⟨e⟩⟩ := directSum_simple_module_over_simple_algebra' A N M
  have : Nontrivial M := IsSimpleModule.nontrivial A M
  have : Module.Finite A (ι →₀ M) := Module.Finite.equiv e
  have : Finite ι := by
    rcases isEmpty_or_nonempty ι with h | h
    · infer_instance
    · exact (((Module.finite_finsupp_iff.1 this).resolve_left
        (not_isEmpty_of_nonempty ι)).resolve_left (not_subsingleton M)).2
  have : Fintype ι := Fintype.ofFinite ι
  let e' : N ≃ₗ[A] (ι → M) := e ≪≫ₗ Finsupp.linearEquivFunOnFinite A M ι
  exact ⟨Fintype.card ι, ⟨((e'.conjAlgEquiv k).trans (endVecAlgEquivMatrixEnd ι k A M)).trans
    (Matrix.reindexAlgEquiv k (Module.End A M) (Fintype.equivFin ι))⟩⟩

/-- Stacks 074E (6): for a nonzero finite `A`-module `N` and `B = Module.End A N`, the natural map
`A → Module.End B N` is a bijective `k`-algebra map. -/
@[stacks 074E "(6): `A ≃ End_B(N)` for `N ≠ 0`; the zero module is excluded, see errata.md"]
theorem toEndEndAlgHom_bijective_of_finite [Nontrivial N] :
    Function.Bijective (toEndEndAlgHom k A N) := by
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  have : IsSemisimpleRing A := (IsSimpleRing.isSemisimpleRing_iff_isArtinianRing).2 this
  have : Module.Finite k N := Module.Finite.trans A N
  have : Module.Finite (Module.End A N) N := Module.Finite.of_restrictScalars_finite k _ N
  refine ⟨RingHom.injective (toEndEndAlgHom k A N).toRingHom, fun g ↦ ?_⟩
  obtain ⟨a, ha⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := A) (M := N) g
  exact ⟨a, LinearMap.ext fun x ↦ LinearMap.congr_fun ha x⟩

end finite
