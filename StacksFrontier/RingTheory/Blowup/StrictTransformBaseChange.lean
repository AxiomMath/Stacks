module

public import StacksFrontier.RingTheory.Blowup.StrictTransform

/-!
# The strict transform is the base change of a chart, modulo torsion

Let `R` be a commutative ring, `I ⊆ R` an ideal, `a ∈ I`, and `A` an `R`-algebra. The affine
blowup chart of `Spec R` attached to `a` is `Spec R[I/a]`, so the chart of the base change
`Spec A ×_{Spec R} Spec R[I/a]` is `Spec (A ⊗_R R[I/a])`, and for an `A`-module `M` the sections
of the pullback of `M` to that chart are the base change `(A ⊗_R R[I/a]) ⊗_A M`.

The ring-level strict transform `strictTransform I a M` of [Stacks, Tag 053H] is instead
`R[I/a] ⊗_R M` modulo its `a`-power torsion. This file identifies the two: the base change over
`A` of the chart's base-change ring cancels, `(A ⊗_R R[I/a]) ⊗_A M ≅ R[I/a] ⊗_R M`, and the
`a`-power torsion submodules correspond, so the two quotients agree.

The linearity obtained is over `R`. The left-hand side is a module over `A ⊗_R R[I/a]` and the
right-hand side over `R[I/a]`, and neither ring acts on the other side; `R` acts on both. That is
enough for the torsion submodules to correspond, because for an `R`-algebra `B` the `B`-torsion
of a `B`-module for the powers of the image of `a` is its `R`-torsion for the powers of `a`
(`Submodule.restrictScalars_torsion'_powers_algebraMap`).

## Main results

* `Submodule.mem_torsion'_powers_iff`: membership in the torsion submodule for the powers of a
  scalar means being killed by one of those powers.
* `Submodule.map_torsion'_powers`: a linear equivalence carries that torsion to that torsion.
* `Submodule.restrictScalars_torsion'_powers_algebraMap`: the torsion submodule for the powers of
  the image of a scalar, read over the base ring.
* `quotientTorsionEquiv`: an `R`-linear equivalence of modules over two `R`-algebras induces one
  of their torsion quotients for the powers of a scalar of `R`.
* `blowupBaseChangeCancelEquiv`: `(A ⊗_R R[I/a]) ⊗_A M ≅ R[I/a] ⊗_R M`.
* `strictTransformEquivBaseChangeQuotientTorsion`: **the identification.** The base change
  `(A ⊗_R R[I/a]) ⊗_A M` modulo its `a`-power torsion is `strictTransform I a M`.

## References

* [Stacks Project, Tag 053H](https://stacks.math.columbia.edu/tag/053H)
-/

@[expose] public noncomputable section

open TensorProduct

universe u

/-! ### Torsion submodules for the powers of a scalar -/

namespace Submodule

variable {R : Type u} [CommRing R] {X Y : Type u} [AddCommGroup X] [Module R X]
  [AddCommGroup Y] [Module R Y]

/-- Membership in the torsion submodule for the powers of `r` means being killed by a power
of `r`. -/
theorem mem_torsion'_powers_iff (r : R) (x : X) :
    x ∈ Submodule.torsion' R X (Submonoid.powers r) ↔ ∃ n : ℕ, r ^ n • x = 0 :=
  (Submodule.mem_torsion'_iff _ _).trans
    ⟨fun ⟨⟨_, n, rfl⟩, hc⟩ => ⟨n, hc⟩, fun ⟨n, hn⟩ => ⟨⟨r ^ n, n, rfl⟩, hn⟩⟩

/-- **A linear equivalence carries torsion to torsion.** -/
theorem map_torsion'_powers (r : R) (e : X ≃ₗ[R] Y) :
    (Submodule.torsion' R X (Submonoid.powers r)).map e.toLinearMap =
      Submodule.torsion' R Y (Submonoid.powers r) := by
  refine SetLike.ext fun y => ?_
  rw [Submodule.mem_map_equiv, Submodule.mem_torsion'_powers_iff,
    Submodule.mem_torsion'_powers_iff]
  exact exists_congr fun n => by rw [← e.symm.map_smul, LinearEquiv.map_eq_zero_iff]

variable (R) in
/-- **The torsion for the powers of the image of a scalar, read over the base ring.** For `B` an
`R`-algebra and `X` a `B`-module, the `B`-submodule of elements killed by a power of the image of
`r : R` restricts to the `R`-submodule of elements killed by a power of `r`. -/
theorem restrictScalars_torsion'_powers_algebraMap {B : Type u} [CommRing B] [Algebra R B]
    [Module B X] [IsScalarTower R B X] (r : R) :
    (Submodule.torsion' B X (Submonoid.powers (algebraMap R B r))).restrictScalars R =
      Submodule.torsion' R X (Submonoid.powers r) := by
  refine SetLike.ext fun x => ?_
  rw [Submodule.restrictScalars_mem, Submodule.mem_torsion'_powers_iff,
    Submodule.mem_torsion'_powers_iff]
  exact exists_congr fun n => by simp only [← map_pow, algebraMap_smul]

end Submodule

/-! ### Torsion quotients over two different algebras -/

/-- **An `R`-linear equivalence induces one of the torsion quotients.** If `X` is a module over an
`R`-algebra `B` and `Y` over an `R`-algebra `C`, an `R`-linear equivalence `X ≃ Y` identifies the
quotient of `X` by its torsion for the powers of the image of `r : R` with the corresponding
quotient of `Y`. Both torsion submodules consist of the elements killed by a power of `r`, by
`Submodule.restrictScalars_torsion'_powers_algebraMap`. -/
def quotientTorsionEquiv {R : Type u} [CommRing R] {B C : Type u} [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] {X Y : Type u} [AddCommGroup X] [Module R X] [Module B X]
    [IsScalarTower R B X] [AddCommGroup Y] [Module R Y] [Module C Y] [IsScalarTower R C Y]
    (r : R) (e : X ≃ₗ[R] Y) :
    (X ⧸ Submodule.torsion' B X (Submonoid.powers (algebraMap R B r))) ≃ₗ[R]
      (Y ⧸ Submodule.torsion' C Y (Submonoid.powers (algebraMap R C r))) :=
  (Submodule.Quotient.restrictScalarsEquiv R
        (Submodule.torsion' B X (Submonoid.powers (algebraMap R B r)))).symm ≪≫ₗ
    Submodule.Quotient.equiv _ _ e (by
      rw [Submodule.restrictScalars_torsion'_powers_algebraMap R r,
        Submodule.restrictScalars_torsion'_powers_algebraMap R r,
        Submodule.map_torsion'_powers]) ≪≫ₗ
    Submodule.Quotient.restrictScalarsEquiv R
      (Submodule.torsion' C Y (Submonoid.powers (algebraMap R C r)))

/-! ### The base change of a blowup chart -/

section

variable {R : Type u} [CommRing R] (I : Ideal R) (a : R) [Fact (a ∈ I)]
  (A : Type u) [CommRing A] [Algebra R A]
  (M : Type u) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

/-- **The base change along `A → A ⊗_R R[I/a]` of an `A`-module is its base change along
`R → R[I/a]`.** For `M` an `A`-module, `(A ⊗_R R[I/a]) ⊗_A M ≅ R[I/a] ⊗_R M`; this is the
cancellation of `A` in the chart of the base change `Spec A ×_{Spec R} Spec R[I/a]`. -/
def blowupBaseChangeCancelEquiv :
    TensorProduct A (TensorProduct R A (Blowup I a)) M ≃ₗ[R] TensorProduct R (Blowup I a) M :=
  (TensorProduct.comm A (TensorProduct R A (Blowup I a)) M).restrictScalars R ≪≫ₗ
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R A A M
      (Blowup I a)).restrictScalars R ≪≫ₗ TensorProduct.comm R M (Blowup I a)

/-- The equivalence `blowupBaseChangeCancelEquiv` sends `(x ⊗ c) ⊗ m` to `c ⊗ (x • m)`. -/
@[simp]
theorem blowupBaseChangeCancelEquiv_tmul_tmul (x : A) (c : Blowup I a) (m : M) :
    blowupBaseChangeCancelEquiv I a A M ((x ⊗ₜ[R] c) ⊗ₜ[A] m) = c ⊗ₜ[R] (x • m) :=
  rfl

/-- **The strict transform is the base change of the chart, modulo torsion.** For `M` a module
over an `R`-algebra `A`, the base change `(A ⊗_R R[I/a]) ⊗_A M` modulo its `a`-power torsion is
the ring-level strict transform `strictTransform I a M` of [Stacks, Tag 053H]. -/
def strictTransformEquivBaseChangeQuotientTorsion :
    (TensorProduct A (TensorProduct R A (Blowup I a)) M ⧸
        Submodule.torsion' (TensorProduct R A (Blowup I a))
          (TensorProduct A (TensorProduct R A (Blowup I a)) M)
          (Submonoid.powers (algebraMap R (TensorProduct R A (Blowup I a)) a)))
      ≃ₗ[R] strictTransform I a M :=
  quotientTorsionEquiv a (blowupBaseChangeCancelEquiv I a A M)

end

end
