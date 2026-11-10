module

public import StacksFrontier.AlgebraicGeometry.Different.NoetherDifferent.Basic
public import StacksFrontier.AlgebraicGeometry.Different.NoetherDifferent.Pairing

/-!
# Products and the diagonal annihilator

On the tensor square of a product algebra the two off-diagonal blocks vanish on the diagonal
annihilator, so the two projections split it. Consequently, contracting a linear functional
against an element of the diagonal annihilator of a product is computed componentwise.

## Main definitions

* `Stacks.Discriminant.diagonalAnnihilatorProdFst` and
  `Stacks.Discriminant.diagonalAnnihilatorProdSnd` are the two projections induced on diagonal
  annihilators.

## Main results

* `Stacks.Discriminant.tensorSquare_prod_decomp` decomposes the tensor square of a product
  algebra into its four blocks.
* `Stacks.Discriminant.tensorContract_fst_prod` and
  `Stacks.Discriminant.tensorContract_snd_prod`: on the diagonal annihilator, contraction
  commutes with the two product projections.

## Implementation notes

The two off-diagonal blocks vanish because the diagonal annihilator kills the orthogonal
idempotent tensors `(1, 0) ⊗ (0, 1)` and `(0, 1) ⊗ (1, 0)`, each of which the two projections
send to `1`. That observation is isolated in a single private vanishing lemma, which the
decomposition uses twice.

## References

* [Stacks Project, Tag 0BVR](https://stacks.math.columbia.edu/tag/0BVR)
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.Discriminant

universe u v w

/-- The tensor square of a product algebra splits into its four blocks. -/
lemma tensorSquare_prod_decomp
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    (t : (B × C) ⊗[A] (B × C)) :
    t =
      TensorProduct.map (LinearMap.inl A B C) (LinearMap.inl A B C)
          (TensorProduct.map (LinearMap.fst A B C) (LinearMap.fst A B C) t) +
        TensorProduct.map (LinearMap.inl A B C) (LinearMap.inr A B C)
          (TensorProduct.map (LinearMap.fst A B C) (LinearMap.snd A B C) t) +
        TensorProduct.map (LinearMap.inr A B C) (LinearMap.inl A B C)
          (TensorProduct.map (LinearMap.snd A B C) (LinearMap.fst A B C) t) +
        TensorProduct.map (LinearMap.inr A B C) (LinearMap.inr A B C)
          (TensorProduct.map (LinearMap.snd A B C) (LinearMap.snd A B C) t) := by
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
      rcases x with ⟨x₁, x₂⟩
      rcases y with ⟨y₁, y₂⟩
      calc
        (x₁, x₂) ⊗ₜ[A] (y₁, y₂) =
            ((x₁, 0) + (0, x₂)) ⊗ₜ[A] ((y₁, 0) + (0, y₂)) := by
              congr 1 <;> ext <;> simp
        _ = (x₁, 0) ⊗ₜ[A] (y₁, 0) + (x₁, 0) ⊗ₜ[A] (0, y₂) +
            (0, x₂) ⊗ₜ[A] (y₁, 0) + (0, x₂) ⊗ₜ[A] (0, y₂) := by
              simp only [TensorProduct.add_tmul, TensorProduct.tmul_add]
              abel
        _ = _ := by simp only [TensorProduct.map_tmul]; abel
  | add t₁ t₂ h₁ h₂ =>
      exact (congrArg₂ (· + ·) h₁ h₂).trans (by simp only [map_add]; abel)

/-- Contraction against a functional on a product sends the first diagonal block to the
contraction of the restricted functional, placed in the first component. -/
private lemma tensorContract_map_inl
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    (f : Module.Dual A (B × C)) (t : B ⊗[A] B) :
    tensorContract A (B × C) f
        (TensorProduct.map (LinearMap.inl A B C) (LinearMap.inl A B C) t) =
      (tensorContract A B (f.comp (LinearMap.inl A B C)) t, 0) := by
  induction t using TensorProduct.inductionOn with
  | tmul x y => simp [tensorContract]
  | add t₁ t₂ h₁ h₂ => simp [h₁, h₂]

/-- Contraction against a functional on a product sends the second diagonal block to the
contraction of the restricted functional, placed in the second component. -/
private lemma tensorContract_map_inr
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    (f : Module.Dual A (B × C)) (t : C ⊗[A] C) :
    tensorContract A (B × C) f
        (TensorProduct.map (LinearMap.inr A B C) (LinearMap.inr A B C) t) =
      (0, tensorContract A C (f.comp (LinearMap.inr A B C)) t) := by
  induction t using TensorProduct.inductionOn with
  | tmul x y => simp [tensorContract]
  | add t₁ t₂ h₁ h₂ => simp [h₁, h₂]

/-- An element of the diagonal annihilator is killed by every element of the kernel of
multiplication, so its image under a pair of algebra maps vanishes as soon as some element of
that kernel is sent to `1`. -/
private lemma map_eq_zero_of_mem_diagonalAnnihilator
    {A : Type*} {R : Type*} {S : Type*} {T : Type*}
    [CommRing A] [CommRing R] [CommRing S] [CommRing T]
    [Algebra A R] [Algebra A S] [Algebra A T]
    (p : R →ₐ[A] S) (q : R →ₐ[A] T) (j : diagonalAnnihilator A R) (k : R ⊗[A] R)
    (hk : k ∈ RingHom.ker (Algebra.TensorProduct.lmul' A :
      R ⊗[A] R →ₐ[A] R).toRingHom)
    (hkmap : Algebra.TensorProduct.map p q k = 1) :
    Algebra.TensorProduct.map p q j.1 = 0 := by
  have hjmul : j.1 * k = 0 := by
    simpa [smul_eq_mul] using Submodule.mem_annihilator.mp j.2 k hk
  have hm := congrArg (Algebra.TensorProduct.map p q) hjmul
  rwa [map_mul, hkmap, mul_one, map_zero] at hm

/-- An element of the diagonal annihilator of a product is the sum of its two diagonal blocks:
the two off-diagonal blocks vanish, because the annihilator kills the orthogonal idempotent
tensors `(1, 0) ⊗ (0, 1)` and `(0, 1) ⊗ (1, 0)`. -/
private lemma diagonalAnnihilator_prod_decomp
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    (j : diagonalAnnihilator A (B × C)) :
    j.1 =
      TensorProduct.map (LinearMap.inl A B C) (LinearMap.inl A B C)
          (TensorProduct.map (LinearMap.fst A B C) (LinearMap.fst A B C) j.1) +
        TensorProduct.map (LinearMap.inr A B C) (LinearMap.inr A B C)
          (TensorProduct.map (LinearMap.snd A B C) (LinearMap.snd A B C) j.1) := by
  have hcross₁ : TensorProduct.map (LinearMap.fst A B C) (LinearMap.snd A B C) j.1 = 0 := by
    change Algebra.TensorProduct.map (AlgHom.fst A B C) (AlgHom.snd A B C) j.1 = 0
    refine map_eq_zero_of_mem_diagonalAnnihilator _ _ j ((1, 0) ⊗ₜ[A] (0, 1)) ?_ ?_
    · rw [RingHom.mem_ker]
      simp [Algebra.TensorProduct.lmul'_apply_tmul]
    · change (1 : B) ⊗ₜ[A] (1 : C) = 1
      exact Algebra.TensorProduct.one_def.symm
  have hcross₂ : TensorProduct.map (LinearMap.snd A B C) (LinearMap.fst A B C) j.1 = 0 := by
    change Algebra.TensorProduct.map (AlgHom.snd A B C) (AlgHom.fst A B C) j.1 = 0
    refine map_eq_zero_of_mem_diagonalAnnihilator _ _ j ((0, 1) ⊗ₜ[A] (1, 0)) ?_ ?_
    · rw [RingHom.mem_ker]
      simp [Algebra.TensorProduct.lmul'_apply_tmul]
    · change (1 : C) ⊗ₜ[A] (1 : B) = 1
      exact Algebra.TensorProduct.one_def.symm
  refine (tensorSquare_prod_decomp j.1).trans ?_
  rw [hcross₁, hcross₂, map_zero, map_zero, add_zero, add_zero]

/-- On the diagonal annihilator of a product, contraction is computed componentwise from the
two projections. -/
private lemma tensorContract_prod_eq
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    (f : Module.Dual A (B × C)) (j : diagonalAnnihilator A (B × C)) :
    tensorContract A (B × C) f j.1 =
      (tensorContract A B (f.comp (LinearMap.inl A B C))
          (Algebra.TensorProduct.map (AlgHom.fst A B C) (AlgHom.fst A B C) j.1),
        tensorContract A C (f.comp (LinearMap.inr A B C))
          (Algebra.TensorProduct.map (AlgHom.snd A B C) (AlgHom.snd A B C) j.1)) := by
  conv_lhs => rw [diagonalAnnihilator_prod_decomp j]
  rw [map_add, tensorContract_map_inl, tensorContract_map_inr, Prod.mk_add_mk, add_zero, zero_add]
  rfl

/-- On the diagonal annihilator of a product, contracting the restricted functional against the
first projection computes the first component of the contraction. -/
lemma tensorContract_fst_prod
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    (f : Module.Dual A (B × C)) (j : diagonalAnnihilator A (B × C)) :
    tensorContract A B (f.comp (LinearMap.inl A B C))
        (Algebra.TensorProduct.map (AlgHom.fst A B C) (AlgHom.fst A B C) j.1) =
      (tensorContract A (B × C) f j.1).1 := by
  rw [tensorContract_prod_eq]

/-- On the diagonal annihilator of a product, contracting the restricted functional against the
second projection computes the second component of the contraction. -/
lemma tensorContract_snd_prod
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    (f : Module.Dual A (B × C)) (j : diagonalAnnihilator A (B × C)) :
    tensorContract A C (f.comp (LinearMap.inr A B C))
        (Algebra.TensorProduct.map (AlgHom.snd A B C) (AlgHom.snd A B C) j.1) =
      (tensorContract A (B × C) f j.1).2 := by
  rw [tensorContract_prod_eq]

/-- The first projection on the annihilator of the diagonal ideal. -/
def diagonalAnnihilatorProdFst
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    (j : diagonalAnnihilator A (B × C)) :
    diagonalAnnihilator A B :=
  ⟨Algebra.TensorProduct.map (AlgHom.fst A B C) (AlgHom.fst A B C) j.1,
    (bijOn_diagonalAnnihilator_prod A B C).1 j.2 |>.1⟩

/-- The second projection on the annihilator of the diagonal ideal. -/
def diagonalAnnihilatorProdSnd
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    (j : diagonalAnnihilator A (B × C)) :
    diagonalAnnihilator A C :=
  ⟨Algebra.TensorProduct.map (AlgHom.snd A B C) (AlgHom.snd A B C) j.1,
    (bijOn_diagonalAnnihilator_prod A B C).1 j.2 |>.2⟩

/-- The first projection on diagonal annihilators is additive. -/
lemma diagonalAnnihilatorProdFst_add
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    (j k : diagonalAnnihilator A (B × C)) :
    diagonalAnnihilatorProdFst A B C (j + k) =
      diagonalAnnihilatorProdFst A B C j + diagonalAnnihilatorProdFst A B C k := by
  apply Subtype.ext
  simp [diagonalAnnihilatorProdFst, map_add]

/-- The second projection on diagonal annihilators is additive. -/
lemma diagonalAnnihilatorProdSnd_add
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    (j k : diagonalAnnihilator A (B × C)) :
    diagonalAnnihilatorProdSnd A B C (j + k) =
      diagonalAnnihilatorProdSnd A B C j + diagonalAnnihilatorProdSnd A B C k := by
  apply Subtype.ext
  simp [diagonalAnnihilatorProdSnd, map_add]

end Stacks.Discriminant
