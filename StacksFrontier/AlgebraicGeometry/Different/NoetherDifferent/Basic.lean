module

public import Mathlib.RingTheory.Ideal.Prod
public import Mathlib.RingTheory.TensorProduct.Pi
public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksCore.Tactic.StacksAttribute

/-!
# The Noether different

Let `B` be a commutative algebra over a commutative ring `A`. The *diagonal annihilator* of
`B/A` is the annihilator of the kernel of the multiplication map `B ⊗[A] B → B`, an ideal of the
enveloping algebra `B ⊗[A] B`. Its image under multiplication is the *Noether different* of
`B/A`, an ideal of `B`.

Both constructions are compatible with finite products: the diagonal annihilator of a product
algebra is carried bijectively onto the product of the diagonal annihilators by the pair of maps
induced by the two projections, and the Noether different of a product is the product of the
Noether differents.

## Main definitions

* `Stacks.Discriminant.diagonalAnnihilator` is the annihilator of the kernel of the
  multiplication map on the enveloping algebra.
* `Stacks.Discriminant.noetherDifferent` is the image of the diagonal annihilator under
  multiplication.

## Main results

* `Stacks.Discriminant.bijOn_diagonalAnnihilator_prod`: the two tensor-square projections
  identify the diagonal annihilator of a product algebra with the product of the diagonal
  annihilators.
* `Stacks.Discriminant.noetherDifferent_prod`: the Noether different of a product algebra is the
  product of the Noether differents of the factors.

## Implementation notes

The identification for a product is stated as a `Set.BijOn` rather than an equality of ideals,
because the ideal on the left lives in the tensor square of the product while the ideal on the
right lives in a product of two different tensor squares; bijectivity on the relevant carriers is
the type-correct form of the equality.

## References

* [Stacks Project, Tag 0BVL](https://stacks.math.columbia.edu/tag/0BVL)
-/

@[expose] public section

namespace Stacks.Discriminant

universe u v w

open scoped TensorProduct

/-- The *diagonal annihilator* of `B/A`: the annihilator of the kernel of the multiplication map
`B ⊗[A] B → B`. -/
def diagonalAnnihilator (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] : Ideal (B ⊗[A] B) :=
  (RingHom.ker (Algebra.TensorProduct.lmul' (R := A) (S := B)).toRingHom).annihilator

/-- The *Noether different* of a commutative `A`-algebra `B`: the image in `B` of the annihilator
of the kernel of the multiplication map on its tensor square. -/
def noetherDifferent (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] : Ideal B :=
  Ideal.map (Algebra.TensorProduct.lmul' A).toRingHom
    (diagonalAnnihilator A B)

private def tensorProdProdEquiv
    (A : Type u) (B₁ : Type v) (B₂ : Type w)
    [CommRing A] [CommRing B₁] [CommRing B₂] [Algebra A B₁] [Algebra A B₂] :
    (B₁ × B₂) ⊗[A] (B₁ × B₂) ≃ₐ[A]
      ((B₁ ⊗[A] B₁) × (B₂ ⊗[A] B₁)) ×
        ((B₁ ⊗[A] B₂) × (B₂ ⊗[A] B₂)) :=
  Algebra.TensorProduct.prodRight A A (B₁ × B₂) B₁ B₂ |>.trans <|
    AlgEquiv.prodCongr
      ((Algebra.TensorProduct.comm A (B₁ × B₂) B₁).trans
        ((Algebra.TensorProduct.prodRight A A B₁ B₁ B₂).trans
          (AlgEquiv.prodCongr (Algebra.TensorProduct.comm A B₁ B₁)
            (Algebra.TensorProduct.comm A B₁ B₂))))
      ((Algebra.TensorProduct.comm A (B₁ × B₂) B₂).trans
        ((Algebra.TensorProduct.prodRight A A B₂ B₁ B₂).trans
          (AlgEquiv.prodCongr (Algebra.TensorProduct.comm A B₂ B₁)
            (Algebra.TensorProduct.comm A B₂ B₂))))

private lemma tensorProdProdEquiv_tmul
    (A : Type u) (B₁ : Type v) (B₂ : Type w)
    [CommRing A] [CommRing B₁] [CommRing B₂] [Algebra A B₁] [Algebra A B₂]
    (x y : B₁ × B₂) :
    tensorProdProdEquiv A B₁ B₂ (x ⊗ₜ[A] y) =
      ((x.1 ⊗ₜ[A] y.1, x.2 ⊗ₜ[A] y.1), (x.1 ⊗ₜ[A] y.2, x.2 ⊗ₜ[A] y.2)) := by
  simp [tensorProdProdEquiv, Algebra.TensorProduct.prodRight_tmul]

private lemma tensorProdProdEquiv_fst_fst
    (A : Type u) (B₁ : Type v) (B₂ : Type w)
    [CommRing A] [CommRing B₁] [CommRing B₂] [Algebra A B₁] [Algebra A B₂]
    (x : (B₁ × B₂) ⊗[A] (B₁ × B₂)) :
    Algebra.TensorProduct.map (AlgHom.fst A B₁ B₂) (AlgHom.fst A B₁ B₂) x =
      (tensorProdProdEquiv A B₁ B₂ x).1.1 := by
  induction x using TensorProduct.inductionOn with
  | tmul x y => simp [tensorProdProdEquiv_tmul]
  | add x y hx hy => simp_all

private lemma tensorProdProdEquiv_snd_snd
    (A : Type u) (B₁ : Type v) (B₂ : Type w)
    [CommRing A] [CommRing B₁] [CommRing B₂] [Algebra A B₁] [Algebra A B₂]
    (x : (B₁ × B₂) ⊗[A] (B₁ × B₂)) :
    Algebra.TensorProduct.map (AlgHom.snd A B₁ B₂) (AlgHom.snd A B₁ B₂) x =
      (tensorProdProdEquiv A B₁ B₂ x).2.2 := by
  induction x using TensorProduct.inductionOn with
  | tmul x y => simp [tensorProdProdEquiv_tmul]
  | add x y hx hy => simp_all

private lemma lmul_tensorProdProdEquiv
    (A : Type u) (B₁ : Type v) (B₂ : Type w)
    [CommRing A] [CommRing B₁] [CommRing B₂] [Algebra A B₁] [Algebra A B₂]
    (x : (B₁ × B₂) ⊗[A] (B₁ × B₂)) :
    Algebra.TensorProduct.lmul' A x =
      (Algebra.TensorProduct.lmul' A (tensorProdProdEquiv A B₁ B₂ x).1.1,
        Algebra.TensorProduct.lmul' A (tensorProdProdEquiv A B₁ B₂ x).2.2) := by
  induction x using TensorProduct.inductionOn with
  | tmul x y => apply Prod.ext <;> simp [tensorProdProdEquiv_tmul]
  | add x y hx hy => simp_all

private lemma mem_diagonalAnnihilator_iff
    (A : Type u) (B₁ : Type v) (B₂ : Type w)
    [CommRing A] [CommRing B₁] [CommRing B₂] [Algebra A B₁] [Algebra A B₂]
    (x : (B₁ × B₂) ⊗[A] (B₁ × B₂)) :
    x ∈ diagonalAnnihilator A (B₁ × B₂) ↔
      (tensorProdProdEquiv A B₁ B₂ x).1.1 ∈ diagonalAnnihilator A B₁ ∧
      (tensorProdProdEquiv A B₁ B₂ x).1.2 = 0 ∧
      (tensorProdProdEquiv A B₁ B₂ x).2.1 = 0 ∧
      (tensorProdProdEquiv A B₁ B₂ x).2.2 ∈ diagonalAnnihilator A B₂ := by
  let e := tensorProdProdEquiv A B₁ B₂
  constructor
  · intro hx
    have annih : ∀ w : ((B₁ ⊗[A] B₁) × (B₂ ⊗[A] B₁)) × ((B₁ ⊗[A] B₂) × (B₂ ⊗[A] B₂)),
        Algebra.TensorProduct.lmul' A w.1.1 = 0 → Algebra.TensorProduct.lmul' A w.2.2 = 0 →
          e x * w = 0 := by
      intro w hw1 hw2
      have hz : e.symm w ∈ RingHom.ker (Algebra.TensorProduct.lmul' (R := A)
          (S := B₁ × B₂)).toRingHom := by
        change Algebra.TensorProduct.lmul' A (e.symm w) = 0
        simp [lmul_tensorProdProdEquiv, e, hw1, hw2]
      simpa [smul_eq_mul, e] using congrArg e (Submodule.mem_annihilator.mp hx _ hz)
    refine ⟨?_,
      by simpa using congrArg (fun q ↦ q.1.2) (annih ((0, 1), (0, 0)) (by simp) (by simp)),
      by simpa using congrArg (fun q ↦ q.2.1) (annih ((0, 0), (1, 0)) (by simp) (by simp)), ?_⟩
    · change (e x).1.1 ∈
        (RingHom.ker (Algebra.TensorProduct.lmul' (R := A)
          (S := B₁)).toRingHom).annihilator
      rw [Submodule.mem_annihilator]
      intro z hz
      simpa using congrArg (fun q ↦ q.1.1) (annih ((z, 0), (0, 0)) hz (by simp))
    · change (e x).2.2 ∈
        (RingHom.ker (Algebra.TensorProduct.lmul' (R := A)
          (S := B₂)).toRingHom).annihilator
      rw [Submodule.mem_annihilator]
      intro z hz
      simpa using congrArg (fun q ↦ q.2.2) (annih ((0, 0), (0, z)) (by simp) hz)
  · rintro ⟨h11, h12, h21, h22⟩
    change x ∈ (RingHom.ker (Algebra.TensorProduct.lmul' (R := A)
      (S := B₁ × B₂)).toRingHom).annihilator
    rw [Submodule.mem_annihilator]
    intro z hz
    change x * z = 0
    apply e.injective
    simp only [map_mul, map_zero]
    refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
    · change (e x).1.1 * (e z).1.1 = 0
      simpa [smul_eq_mul] using Submodule.mem_annihilator.mp h11 _ (by
        simpa [RingHom.mem_ker, lmul_tensorProdProdEquiv] using congrArg Prod.fst hz)
    · change (e x).1.2 * (e z).1.2 = 0
      rw [show (e x).1.2 = 0 from h12, zero_mul]
    · change (e x).2.1 * (e z).2.1 = 0
      rw [show (e x).2.1 = 0 from h21, zero_mul]
    · change (e x).2.2 * (e z).2.2 = 0
      simpa [smul_eq_mul] using Submodule.mem_annihilator.mp h22 _ (by
        simpa [RingHom.mem_ker, lmul_tensorProdProdEquiv] using congrArg Prod.snd hz)

/-- The canonical pair of tensor-square projections identifies the annihilator of the
kernel of multiplication for a product algebra with the product of the corresponding
annihilators. -/
@[stacks 0BVL "part (1)"]
theorem bijOn_diagonalAnnihilator_prod
    (A : Type u) (B₁ : Type v) (B₂ : Type w)
    [CommRing A] [CommRing B₁] [CommRing B₂] [Algebra A B₁] [Algebra A B₂] :
    Set.BijOn
      (fun x : (B₁ × B₂) ⊗[A] (B₁ × B₂) ↦
        (Algebra.TensorProduct.map (AlgHom.fst A B₁ B₂) (AlgHom.fst A B₁ B₂) x,
          Algebra.TensorProduct.map (AlgHom.snd A B₁ B₂) (AlgHom.snd A B₁ B₂) x))
      (diagonalAnnihilator A (B₁ × B₂) :
        Set ((B₁ × B₂) ⊗[A] (B₁ × B₂)))
      ((diagonalAnnihilator A B₁ : Set (B₁ ⊗[A] B₁)) ×ˢ
        (diagonalAnnihilator A B₂ : Set (B₂ ⊗[A] B₂))) := by
  let e := tensorProdProdEquiv A B₁ B₂
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [Set.mem_prod]
    change
      Algebra.TensorProduct.map (AlgHom.fst A B₁ B₂) (AlgHom.fst A B₁ B₂) x ∈ _ ∧
        Algebra.TensorProduct.map (AlgHom.snd A B₁ B₂) (AlgHom.snd A B₁ B₂) x ∈ _
    rw [tensorProdProdEquiv_fst_fst, tensorProdProdEquiv_snd_snd]
    exact ⟨(mem_diagonalAnnihilator_iff A B₁ B₂ x).mp hx |>.1,
      (mem_diagonalAnnihilator_iff A B₁ B₂ x).mp hx |>.2.2.2⟩
  · intro x hx y hy hxy
    refine e.injective (Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_))
    · simpa [tensorProdProdEquiv_fst_fst] using congrArg Prod.fst hxy
    · rw [(mem_diagonalAnnihilator_iff A B₁ B₂ x).mp hx |>.2.1,
        (mem_diagonalAnnihilator_iff A B₁ B₂ y).mp hy |>.2.1]
    · rw [(mem_diagonalAnnihilator_iff A B₁ B₂ x).mp hx |>.2.2.1,
        (mem_diagonalAnnihilator_iff A B₁ B₂ y).mp hy |>.2.2.1]
    · simpa [tensorProdProdEquiv_snd_snd] using congrArg Prod.snd hxy
  · rintro ⟨a, b⟩ hab
    let x := e.symm ((a, 0), (0, b))
    exact ⟨x, (mem_diagonalAnnihilator_iff A B₁ B₂ x).mpr (by simpa [x, e] using hab),
      Prod.ext (by simp [tensorProdProdEquiv_fst_fst, x, e])
        (by simp [tensorProdProdEquiv_snd_snd, x, e])⟩

/-- The Noether different of a product algebra is the product of the Noether differents
of its factors. -/
@[stacks 0BVL "part (2)"]
theorem noetherDifferent_prod
    (A : Type u) (B₁ : Type v) (B₂ : Type w)
    [CommRing A] [CommRing B₁] [CommRing B₂] [Algebra A B₁] [Algebra A B₂] :
    noetherDifferent A (B₁ × B₂) =
      Ideal.prod (noetherDifferent A B₁)
        (noetherDifferent A B₂) := by
  let e := tensorProdProdEquiv A B₁ B₂
  apply Ideal.ext
  rintro ⟨b₁, b₂⟩
  change (b₁, b₂) ∈ Ideal.map (Algebra.TensorProduct.lmul' A).toRingHom
      (diagonalAnnihilator A (B₁ × B₂)) ↔
    b₁ ∈ Ideal.map (Algebra.TensorProduct.lmul' A).toRingHom
        (diagonalAnnihilator A B₁) ∧
      b₂ ∈ Ideal.map (Algebra.TensorProduct.lmul' A).toRingHom
        (diagonalAnnihilator A B₂)
  rw [Ideal.mem_map_iff_of_surjective _ (fun b ↦ ⟨b ⊗ₜ[A] 1, by simp⟩),
    Ideal.mem_map_iff_of_surjective _ (fun b ↦ ⟨b ⊗ₜ[A] 1, by simp⟩),
    Ideal.mem_map_iff_of_surjective _ (fun b ↦ ⟨b ⊗ₜ[A] 1, by simp⟩)]
  constructor
  · rintro ⟨x, hx, hxb⟩
    refine ⟨⟨(e x).1.1, (mem_diagonalAnnihilator_iff A B₁ B₂ x).mp hx |>.1, ?_⟩,
      ⟨(e x).2.2, (mem_diagonalAnnihilator_iff A B₁ B₂ x).mp hx |>.2.2.2, ?_⟩⟩
    · simpa [lmul_tensorProdProdEquiv] using congrArg Prod.fst hxb
    · simpa [lmul_tensorProdProdEquiv] using congrArg Prod.snd hxb
  · rintro ⟨⟨x₁, hx₁, hxb₁⟩, ⟨x₂, hx₂, hxb₂⟩⟩
    let x := e.symm ((x₁, 0), (0, x₂))
    refine ⟨x, (mem_diagonalAnnihilator_iff A B₁ B₂ x).mpr
      (by simpa [x, e] using And.intro hx₁ hx₂), ?_⟩
    change Algebra.TensorProduct.lmul' A x = (b₁, b₂)
    rw [lmul_tensorProdProdEquiv]
    simpa [x, e] using congrArg₂ Prod.mk hxb₁ hxb₂

end Stacks.Discriminant
