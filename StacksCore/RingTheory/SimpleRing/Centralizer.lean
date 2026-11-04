module

public import Mathlib.Algebra.Central.End
public import Mathlib.LinearAlgebra.Basis.MulOpposite
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import StacksCore.Algebra.Algebra.Subalgebra.Conj
public import StacksCore.Algebra.Algebra.Subalgebra.Lattice
public import StacksCore.Algebra.Central.TensorProduct
public import StacksCore.RingTheory.SimpleRing.Basic
public import StacksCore.RingTheory.SimpleRing.End
public import StacksCore.RingTheory.SkolemNoether

/-!
# Centralizers in central simple algebras

Let `A` be a finite-dimensional central simple algebra over a field `F` and let `B` be a simple
subalgebra of `A`. This file proves that the centralizer of `B` in `A` is again a simple ring,
and that its dimension satisfies `dim C_A(B) * dim B = dim A`.

Both proofs embed `B` into `T := A ⊗[F] Module.End F B` twice: once as `b ↦ b ⊗ 1` and once as
`b ↦ 1 ⊗ (left multiplication by b)`. By Skolem–Noether the two embeddings are conjugate by a
unit of `T`, hence so are the centralizers of their ranges (`AlgHom.range_conj` and
`Subalgebra.conj_centralizer`). The first centralizer is `C_A(B) ⊗ End F B`, the second is
`A ⊗ Bᵐᵒᵖ` (by `Subalgebra.centralizer_range_lmul`); comparing simplicity and dimensions of
the two sides yields the results.

## Main results

* `Subalgebra.centralizer_isSimple`: the centralizer of a simple subalgebra of a
  finite-dimensional central simple algebra is simple.
* `Subalgebra.finrank_centralizer_mul_finrank`: `dim C_A(B) * dim B = dim A`.
-/

@[expose] public section

universe u v

open scoped TensorProduct

section CentralSimple

variable {F : Type u} {A : Type v} [Field F] [Ring A] [Algebra F A]

/-- Over a field, `S ⊗ C → A ⊗ C` is injective for a subalgebra `S` of `A`. -/
private lemma map_val_id_injective (S : Subalgebra F A) (C : Type*) [Ring C] [Algebra F C] :
    Function.Injective (Algebra.TensorProduct.map S.val (AlgHom.id F C)) := by
  have h : (Algebra.TensorProduct.map S.val (AlgHom.id F C)).toLinearMap =
      S.val.toLinearMap.rTensor C := TensorProduct.ext' fun _ _ ↦ by simp
  rw [← AlgHom.coe_toLinearMap, h]
  exact Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective

/-- Over a field, `A ⊗ S → A ⊗ C` is injective for a subalgebra `S` of `C`. -/
private lemma map_id_val_injective {C : Type*} [Ring C] [Algebra F C] (S : Subalgebra F C) :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id F A) S.val) := by
  have h : (Algebra.TensorProduct.map (AlgHom.id F A) S.val).toLinearMap =
      S.val.toLinearMap.lTensor A := TensorProduct.ext' fun _ _ ↦ by simp
  rw [← AlgHom.coe_toLinearMap, h]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective

/-- In `A ⊗[F] C`, the centralizer of `B ⊗ 1` is isomorphic to `C_A(B) ⊗[F] C`. -/
private lemma centralizer_includeLeft_equiv (B : Subalgebra F A) (C : Type*)
    [Ring C] [Algebra F C] :
    Nonempty ((Subalgebra.centralizer F (B : Set A) ⊗[F] C) ≃ₐ[F] Subalgebra.centralizer F
      (((Algebra.TensorProduct.includeLeft (R := F) (S := F) (B := C)).comp B.val).range :
        Set (A ⊗[F] C))) := by
  rw [AlgHom.range_comp, Subalgebra.range_val,
    Subalgebra.centralizer_coe_map_includeLeft_eq_center_tensorProduct]
  exact ⟨AlgEquiv.ofInjective _ (map_val_id_injective _ C)⟩

/-- If the centralizer of `B ⊗ 1` in `A ⊗[F] C` is simple, then so is the centralizer of `B`
in `A`: the former is isomorphic to `C_A(B) ⊗[F] C`, and simplicity descends to the left
tensor factor. -/
private lemma isSimpleRing_of_centralizer_includeLeft (B : Subalgebra F A) (C : Type*)
    [Ring C] [Algebra F C]
    (h : IsSimpleRing (Subalgebra.centralizer F
      (((Algebra.TensorProduct.includeLeft (R := F) (S := F) (B := C)).comp B.val).range :
        Set (A ⊗[F] C)))) :
    IsSimpleRing (Subalgebra.centralizer F (B : Set A)) := by
  obtain ⟨e⟩ := centralizer_includeLeft_equiv B C
  have : IsSimpleRing ((Subalgebra.centralizer F (B : Set A)) ⊗[F] C) :=
    .of_ringEquiv e.symm.toRingEquiv h
  exact IsSimpleRing.left_of_tensor (K := F)
    (A := Subalgebra.centralizer F (B : Set A)) (B := C)

/-- In `A ⊗[F] C`, the centralizer of `B ⊗ 1` is `C_A(B) ⊗ C`; in particular its dimension
is `dim C_A(B) * dim C`. -/
private lemma finrank_centralizer_includeLeft (B : Subalgebra F A) (C : Type*)
    [Ring C] [Algebra F C] :
    Module.finrank F (Subalgebra.centralizer F
      (((Algebra.TensorProduct.includeLeft (R := F) (S := F) (B := C)).comp B.val).range :
        Set (A ⊗[F] C))) =
      Module.finrank F (Subalgebra.centralizer F (B : Set A)) * Module.finrank F C := by
  obtain ⟨e⟩ := centralizer_includeLeft_equiv B C
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_tensorProduct]

/-- In `A ⊗[F] Module.End F B`, the centralizer of `B` embedded as
`b ↦ 1 ⊗ (left multiplication by b)` is isomorphic to `A ⊗ Bᵐᵒᵖ`
(by `Subalgebra.centralizer_range_lmul`). -/
private lemma centralizer_includeRight_lmul_equiv (B : Type*) [Ring B] [Algebra F B] :
    Nonempty ((A ⊗[F] Bᵐᵒᵖ) ≃ₐ[F] Subalgebra.centralizer F
      (((Algebra.TensorProduct.includeRight (R := F) (A := A)).comp
        (Algebra.lmul F B)).range : Set (A ⊗[F] Module.End F B))) := by
  rw [AlgHom.range_comp, Subalgebra.centralizer_coe_map_includeRight_eq_center_tensorProduct]
  exact ⟨(Algebra.TensorProduct.congr .refl
    ((AlgEquiv.ofInjective _ (Algebra.rmul_injective F B)).trans
      (Subalgebra.equivOfEq _ _ (Subalgebra.centralizer_range_lmul F B).symm))).trans
    (AlgEquiv.ofInjective _ (map_id_val_injective _))⟩

/-- In `A ⊗[F] Module.End F B`, the centralizer of `B` embedded as
`b ↦ 1 ⊗ (left multiplication by b)` is `A ⊗ Bᵐᵒᵖ`; in particular its dimension is
`dim A * dim B`. -/
private lemma finrank_centralizer_includeRight_lmul (B : Type*) [Ring B] [Algebra F B] :
    Module.finrank F (Subalgebra.centralizer F
      (((Algebra.TensorProduct.includeRight (R := F) (A := A)).comp
        (Algebra.lmul F B)).range : Set (A ⊗[F] Module.End F B))) =
      Module.finrank F A * Module.finrank F B := by
  obtain ⟨e⟩ := centralizer_includeRight_lmul_equiv (F := F) (A := A) B
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_tensorProduct, MulOpposite.finrank]

variable [Algebra.IsCentral F A] [IsSimpleRing A]

/-- The centralizer in `A ⊗[F] Module.End F B` of `B` embedded as
`b ↦ 1 ⊗ (left multiplication by b)` is simple: it is isomorphic to `A ⊗[F] Bᵐᵒᵖ` by
`Subalgebra.centralizer_range_lmul`. -/
private lemma isSimpleRing_centralizer_includeRight_lmul (B : Type*) [Ring B] [Algebra F B]
    [IsSimpleRing B] :
    IsSimpleRing (Subalgebra.centralizer F
      (((Algebra.TensorProduct.includeRight (R := F) (A := A)).comp
        (Algebra.lmul F B)).range : Set (A ⊗[F] Module.End F B))) := by
  obtain ⟨e⟩ := centralizer_includeRight_lmul_equiv (F := F) (A := A) B
  exact .of_ringEquiv e.toRingEquiv
    (Algebra.TensorProduct.isSimpleRing (K := F) (A := A) (B := Bᵐᵒᵖ))

/-- By Skolem–Noether, the centralizers of the two embeddings of `B` into
`A ⊗[F] Module.End F B` are conjugate. -/
private lemma exists_centralizer_includeRight_eq_conj [FiniteDimensional F A]
    (B : Subalgebra F A) [IsSimpleRing B] :
    ∃ x : (A ⊗[F] Module.End F B)ˣ,
      Subalgebra.centralizer F
        (((Algebra.TensorProduct.includeRight (R := F) (A := A)).comp
          (Algebra.lmul F B)).range : Set (A ⊗[F] Module.End F B)) =
      (Subalgebra.centralizer F
        (((Algebra.TensorProduct.includeLeft (R := F) (S := F)
          (B := Module.End F B)).comp B.val).range :
          Set (A ⊗[F] Module.End F B))).conj x := by
  obtain ⟨x, hx⟩ := skolemNoether F (A ⊗[F] Module.End F B) B
    (Algebra.TensorProduct.includeLeft.comp B.val)
    (Algebra.TensorProduct.includeRight.comp (Algebra.lmul F B))
  exact ⟨x, by rw [AlgHom.range_conj hx, Subalgebra.conj_centralizer]⟩

/-- The centralizer of a simple subalgebra of a finite-dimensional central simple algebra is
simple. -/
@[stacks 074T "first part"]
theorem Subalgebra.centralizer_isSimple [FiniteDimensional F A] (B : Subalgebra F A)
    [IsSimpleRing B] :
    IsSimpleRing (Subalgebra.centralizer F (B : Set A)) := by
  obtain ⟨x, hE⟩ := exists_centralizer_includeRight_eq_conj B
  have h1 : IsSimpleRing ((Subalgebra.centralizer F
      (((Algebra.TensorProduct.includeLeft (R := F) (S := F)
        (B := Module.End F B)).comp B.val).range :
        Set (A ⊗[F] Module.End F B))).conj x) :=
    .of_ringEquiv (Subalgebra.equivOfEq _ _ hE).toRingEquiv
      (isSimpleRing_centralizer_includeRight_lmul (F := F) (A := A) B)
  exact isSimpleRing_of_centralizer_includeLeft _ _
    ((Subalgebra.isSimpleRing_conj_iff _ x).1 h1)

/-- The dimension of the centralizer of a simple subalgebra `B` of a finite-dimensional
central simple algebra `A` satisfies `dim C_A(B) * dim B = dim A`. -/
@[stacks 074T "second part"]
theorem Subalgebra.finrank_centralizer_mul_finrank [FiniteDimensional F A]
    (B : Subalgebra F A) [IsSimpleRing B] :
    Module.finrank F (Subalgebra.centralizer F (B : Set A)) * Module.finrank F B =
      Module.finrank F A := by
  have : Nontrivial B := ⟨1, 0, fun h ↦ one_ne_zero (α := A) (congrArg Subtype.val h)⟩
  obtain ⟨x, hE⟩ := exists_centralizer_includeRight_eq_conj B
  have key := (finrank_centralizer_includeLeft B (Module.End F B)).symm.trans <|
    ((congrArg (fun S : Subalgebra F (A ⊗[F] Module.End F B) ↦ Module.finrank F ↥S) hE).trans
      (Subalgebra.finrank_conj _ x)).symm.trans <|
    finrank_centralizer_includeRight_lmul (F := F) (A := A) B
  rw [Module.finrank_linearMap, ← mul_assoc] at key
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero Module.finrank_pos.ne') key

/-- The double centralizer theorem: in a finite-dimensional central simple algebra `A`, the
centralizer of the centralizer of a simple subalgebra `B` is `B` itself. -/
@[stacks 074T "third part"]
theorem Subalgebra.centralizer_centralizer [FiniteDimensional F A] (B : Subalgebra F A)
    [IsSimpleRing B] :
    Subalgebra.centralizer F (Subalgebra.centralizer F (B : Set A) : Set A) = B := by
  have := B.centralizer_isSimple
  have : Nontrivial (Subalgebra.centralizer F (B : Set A)) :=
    ⟨1, 0, fun h ↦ one_ne_zero (α := A) (congrArg Subtype.val h)⟩
  refine (Subalgebra.eq_of_le_of_finrank_eq (Subalgebra.le_centralizer_centralizer F) ?_).symm
  have h3 := B.finrank_centralizer_mul_finrank.trans
    (Subalgebra.centralizer F (B : Set A)).finrank_centralizer_mul_finrank.symm
  rw [mul_comm] at h3
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero Module.finrank_pos.ne') h3

/-- A finite-dimensional central simple algebra decomposes as the tensor product of any
central simple subalgebra and its centralizer. -/
@[stacks 074U]
noncomputable def Subalgebra.tensorCentralizerEquiv [FiniteDimensional F A]
    (B : Subalgebra F A) [IsSimpleRing B] [Algebra.IsCentral F B] :
    A ≃ₐ[F] B ⊗[F] Subalgebra.centralizer F (B : Set A) :=
  haveI := B.centralizer_isSimple
  (AlgEquiv.ofBijective
    (Algebra.TensorProduct.lift B.val (Subalgebra.centralizer F (B : Set A)).val
      fun b c ↦ show _ = _ by simpa using c.2 b b.2)
    (AlgHom.bijective_of_finrank_eq _ (by
      rw [Module.finrank_tensorProduct, ← B.finrank_centralizer_mul_finrank, mul_comm]))).symm

@[stacks 074V "(ii) ↔ (i)", stacks 074W]
lemma Subalgebra.isMaximal_comm_iff_finrank [Module.Finite F A] (L : Subalgebra F A)
    [IsMulCommutative L] [IsSimpleRing L] :
    Subalgebra.centralizer F (L : Set A) = L ↔
      Module.finrank F A = Module.finrank F L * Module.finrank F L := by
  refine ⟨fun hL ↦ ?_, fun hL ↦ ?_⟩
  · nth_rw 1 [← (Subalgebra.equivOfEq _ _ hL).toLinearEquiv.finrank_eq]
    exact L.finrank_centralizer_mul_finrank.symm
  · have h : Module.finrank F L = Module.finrank F (Subalgebra.centralizer F (L : Set A)) := by
      simpa [ne_of_gt (Module.finrank_pos (M := L))] using
        hL.symm.trans L.finrank_centralizer_mul_finrank.symm
    apply Subalgebra.toSubmodule_injective
    refine symm <| Submodule.eq_of_le_of_finrank_eq (Subalgebra.toSubmodule.le_iff_le.2 ?_) h
    exact Subalgebra.le_centralizer_iff_isMulCommutative L|>.2 inferInstance

namespace Subalgebra

variable (L : Subalgebra F A) [IsMulCommutative L]

open scoped IsMulCommutative

/-- The centralizer of a commutative subalgebra `L` is an `L`-algebra via the inclusion
`L ≤ C_A(L)`. -/
scoped instance instAlgebraCentralizer : Algebra L (Subalgebra.centralizer F (L : Set A)) :=
  RingHom.toAlgebra' (Subalgebra.inclusion ((le_centralizer_iff_isMulCommutative L).2
    inferInstance)).toRingHom fun l c ↦ Subtype.ext <|
    (Subalgebra.mem_centralizer_iff F).1 c.2 l.1 l.2

/-- The centralizer of a commutative simple subalgebra `L` of a finite-dimensional central
simple algebra is central over `L`: by the double centralizer theorem, anything commuting
with all of `C_A(L)` already lies in `L`. -/
scoped instance isCentral_centralizer [FiniteDimensional F A] [IsSimpleRing L] :
    Algebra.IsCentral L (Subalgebra.centralizer F (L : Set A)) where
  out z hz := by
    rw [Subalgebra.mem_center_iff] at hz
    have hzA : (z : A) ∈ Subalgebra.centralizer F
        (Subalgebra.centralizer F (L : Set A) : Set A) :=
      (Subalgebra.mem_centralizer_iff F).2 fun g hg ↦ congrArg Subtype.val (hz ⟨g, hg⟩)
    rw [L.centralizer_centralizer] at hzA
    exact Algebra.mem_bot.2 ⟨⟨(z : A), hzA⟩, rfl⟩

end Subalgebra

end CentralSimple
