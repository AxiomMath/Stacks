module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.TensorProduct.Pi

/-!
# A pushout square of commutative rings as a tensor product

`CommRingCat.isPushout_tensorProduct` says that the tensor product square is a pushout.  This
file reads an arbitrary pushout square `R → A`, `R → B`, `A → P`, `B → P` of commutative rings
the other way round: it produces the `R`-linear identification `A ⊗[R] B ≃ P` which multiplies
the two images together, and records its value on a pure tensor.

Also proved is that raising the universe of the rings in a pushout square again gives a pushout
square, and that in a pushout square along a surjection the kernel of the opposite map is the
extension of the kernel of the surjection.

## Main definitions

* `CommRingCat.pushoutTensorLinearEquiv`: the `R`-linear identification `A ⊗[R] B ≃ₗ[R] P`
  attached to a pushout square of commutative rings.

## Main results

* `CommRingCat.pushoutTensorLinearEquiv_tmul`: it sends `a ⊗ₜ b` to the product of the images
  of `a` and `b`.
* `CommRingCat.isPushout_ulift`: a pushout square of commutative rings stays a pushout square
  after raising the universe of all four rings.
* `CommRingCat.ker_inr_of_isPushout`: in a pushout square whose map `f : R ⟶ A` is surjective,
  the kernel of the opposite map is the image of the kernel of `f`.

## Implementation notes

The identification is built from `CategoryTheory.IsPushout.isoIsPushout` against
`CommRingCat.isPushout_tensorProduct`, so it is the canonical comparison and not an arbitrary
isomorphism.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
-/

@[expose] public section

open CategoryTheory TensorProduct

universe u v r

namespace CommRingCat

/-- The `R`-linear identification `A ⊗[R] B ≃ₗ[R] P` attached to a pushout square of commutative
rings, where `P` is an `R`-algebra through the composite `R → A → P`. -/
noncomputable def pushoutTensorLinearEquiv
    (R A B P : CommRingCat.{r}) (f : R ⟶ A) (g : R ⟶ B)
    (l : A ⟶ P) (r : B ⟶ P) (h : IsPushout f g l r) :
    letI : Algebra R A := f.hom.toAlgebra
    letI : Algebra R B := g.hom.toAlgebra
    letI : Algebra R P := (f ≫ l).hom.toAlgebra
    A ⊗[R] B ≃ₗ[R] P := by
  letI : Algebra R A := f.hom.toAlgebra
  letI : Algebra R B := g.hom.toAlgebra
  letI : Algebra R P := (f ≫ l).hom.toAlgebra
  let ht := CommRingCat.isPushout_tensorProduct R A B
  let E := ht.isoIsPushout A B h
  let e := E.commRingCatIsoToRingEquiv
  have he (a : A) (b : B) : e (a ⊗ₜ[R] b) = l.hom a * r.hom b := by
    have hl := congrArg (fun k : CommRingCat.of A ⟶ P => k.hom a) (ht.inl_isoIsPushout_hom A B h)
    have hr := congrArg (fun k : CommRingCat.of B ⟶ P => k.hom b) (ht.inr_isoIsPushout_hom A B h)
    change e (a ⊗ₜ[R] 1) = l.hom a at hl
    change e (1 ⊗ₜ[R] b) = r.hom b at hr
    rw [← hl, ← hr, ← map_mul]
    simp
  refine { e.toAddEquiv with map_smul' := ?_ }
  intro c x
  change e (c • x) = (f ≫ l).hom c * e x
  rw [Algebra.smul_def, map_mul]
  congr 1
  change e (f.hom c ⊗ₜ[R] 1) = l.hom (f.hom c)
  rw [he, map_one, mul_one]

/-- `CommRingCat.pushoutTensorLinearEquiv` sends `a ⊗ₜ b` to the product of the images of `a` and
`b` in the pushout. -/
theorem pushoutTensorLinearEquiv_tmul
    (R A B P : CommRingCat.{r}) (f : R ⟶ A) (g : R ⟶ B)
    (l : A ⟶ P) (r : B ⟶ P) (h : IsPushout f g l r) (a : A) (b : B) :
    letI : Algebra R A := f.hom.toAlgebra
    letI : Algebra R B := g.hom.toAlgebra
    letI : Algebra R P := (f ≫ l).hom.toAlgebra
    pushoutTensorLinearEquiv R A B P f g l r h (a ⊗ₜ[R] b) = l.hom a * r.hom b := by
  let _ : Algebra R A := f.hom.toAlgebra
  let _ : Algebra R B := g.hom.toAlgebra
  let _ : Algebra R P := (f ≫ l).hom.toAlgebra
  let ht := CommRingCat.isPushout_tensorProduct R A B
  let e := (ht.isoIsPushout A B h).commRingCatIsoToRingEquiv
  have hl := congrArg (fun k : CommRingCat.of A ⟶ P => k.hom a) (ht.inl_isoIsPushout_hom A B h)
  have hr := congrArg (fun k : CommRingCat.of B ⟶ P => k.hom b) (ht.inr_isoIsPushout_hom A B h)
  change e (a ⊗ₜ[R] 1) = l.hom a at hl
  change e (1 ⊗ₜ[R] b) = r.hom b at hr
  change e (a ⊗ₜ[R] b) = _
  rw [← hl, ← hr, ← map_mul]
  simp

/-- A pushout square of commutative rings stays a pushout square after raising the universe of
all four rings. -/
theorem isPushout_ulift
    {R A B P : CommRingCat.{u}} {f : R ⟶ A} {g : R ⟶ B}
    {l : A ⟶ P} {r : B ⟶ P} (h : IsPushout f g l r) :
    IsPushout (CommRingCat.ofHom f.hom.ulift.{v, v})
      (CommRingCat.ofHom g.hom.ulift.{v, v})
      (CommRingCat.ofHom l.hom.ulift.{v, v})
      (CommRingCat.ofHom r.hom.ulift.{v, v}) := by
  let _ : Algebra R A := f.hom.toAlgebra
  let _ : Algebra R B := g.hom.toAlgebra
  let _ : Algebra (ULift.{v} R) (ULift.{v} A) := ULift.algebra' R _
  let _ : Algebra (ULift.{v} R) (ULift.{v} B) := ULift.algebra' R _
  let ht := CommRingCat.isPushout_tensorProduct R A B
  let e := (ht.isoIsPushout A B h).commRingCatIsoToRingEquiv
  have he (a : A) (b : B) : e (a ⊗ₜ[R] b) = l.hom a * r.hom b :=
    pushoutTensorLinearEquiv_tmul R A B P f g l r h a b
  let el : ULift.{v} A ⊗[ULift.{v} R] ULift.{v} B ≃+* ULift.{v} P :=
    (Algebra.TensorProduct.uliftEquiv.{v, v, v, v} R R A B).symm.toRingEquiv.trans
      (ULift.ringEquiv.trans (e.trans ULift.ringEquiv.symm))
  have hel (a : ULift.{v} A) (b : ULift.{v} B) :
      el (a ⊗ₜ[ULift.{v} R] b) = ULift.up (l.hom a.down * r.hom b.down) := by
    change ULift.up (e (((Algebra.TensorProduct.uliftEquiv.{v, v, v, v} R R A B).symm
      (a ⊗ₜ[ULift.{v} R] b)).down)) = _
    rw [Algebra.TensorProduct.down_uliftEquiv_symm_tmul, he]
  apply (CommRingCat.isPushout_tensorProduct (ULift.{v} R) (ULift.{v} A) (ULift.{v} B)).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) el.toCommRingCatIso
  · rfl
  · rfl
  · ext a
    simpa using congrArg ULift.down (hel a 1)
  · ext b
    simpa using congrArg ULift.down (hel 1 b)

/-- **A pushout extends the kernel of a surjection.**  In a pushout square of commutative rings
whose map `f : R ⟶ A` is surjective, the kernel of the opposite map `b : B ⟶ T` is the image under
`g : R ⟶ B` of the kernel of `f`. -/
public theorem ker_inr_of_isPushout
    {R A B T : CommRingCat.{u}} (f : R ⟶ A) (g : R ⟶ B)
    (a : A ⟶ T) (b : B ⟶ T) (h : IsPushout f g a b)
    (hf : Function.Surjective f) :
    RingHom.ker b.hom = (RingHom.ker f.hom).map g.hom := by
  classical
  let I := (RingHom.ker f.hom).map g.hom
  let q := Ideal.Quotient.mk I
  have hkill (x : R) (hx : f x = 0) : q (g x) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem g.hom hx)
  let p : A →+* B ⧸ I := f.hom.liftOfRightInverse
    (Function.surjInv hf) (Function.rightInverse_surjInv hf) ⟨q.comp g.hom, hkill⟩
  have hw : f ≫ CommRingCat.ofHom p = g ≫ CommRingCat.ofHom q :=
    CommRingCat.hom_ext (RingHom.liftOfRightInverse_comp _ _ _ _)
  let d := h.desc (CommRingCat.ofHom p) (CommRingCat.ofHom q) hw
  apply le_antisymm
  · intro x hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have he := ConcreteCategory.congr_hom (h.inr_desc _ _ hw) x
    change d (b x) = q x at he
    rw [show b x = 0 from hx, map_zero] at he
    exact he.symm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    have he := ConcreteCategory.congr_hom h.w x
    change a (f x) = b (g x) at he
    rw [show f x = 0 from hx, map_zero] at he
    exact he.symm

end CommRingCat

end
