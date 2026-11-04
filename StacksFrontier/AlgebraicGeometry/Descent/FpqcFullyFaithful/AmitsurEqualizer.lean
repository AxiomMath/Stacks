module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# The equalizer at the bottom of the Amitsur complex

Let `A → B` be a ring map and `M` an `A`-module.  The two coface maps
`B ⊗[A] M → B ⊗[A] B ⊗[A] M` send `b ⊗ m` to `1 ⊗ b ⊗ m` and to `b ⊗ 1 ⊗ m`, and the
augmentation `m ↦ 1 ⊗ m` lands in the submodule on which they agree.  This file proves that
when `B` is faithfully flat over `A` the augmentation is an isomorphism onto that submodule:

`0 → M → B ⊗[A] M → B ⊗[A] B ⊗[A] M`

is exact.  These are the degrees `-1` and `0` of the extended Amitsur complex of Stacks 023K,
so this is the part of Stacks 023M that the sheaf condition of Stacks 03DT for a single
faithfully flat morphism of affine schemes uses; the full statement of 023M, exactness in every
degree, is not proved here.

The proof is the one in the source, in its two-step form.  After base change along `A → B` the
complex becomes the complex of the ring map `B → B ⊗[A] B`, which has the section
`b ⊗ b' ↦ b b'`; a section makes the complex contractible, and in these two degrees the
contracting homotopy is written down directly as `Stacks.Descent.amitsurHomotopy`.  Exactness
descends from the base change because `B` is faithfully flat, by
`Module.FaithfullyFlat.lTensor_exact_iff_exact`.

## Main definitions

* `Stacks.Descent.amitsurUnit` is the augmentation `m ↦ 1 ⊗ m`.
* `Stacks.Descent.amitsurCoface₀` and `Stacks.Descent.amitsurCoface₁` are the two coface maps,
  and `Stacks.Descent.amitsurDiff` is their difference.
* `Stacks.Descent.amitsurContract` is the multiplication `b ⊗ b' ⊗ m ↦ b b' ⊗ m`, the
  contracting homotopy of the base-changed complex.
* `Stacks.Descent.amitsurEqualizerEquiv` identifies `M` with the submodule of `B ⊗[A] M` on
  which the two coface maps agree.

## Main results

* `Stacks.Descent.exact_lTensor_amitsur`: the base-changed complex is exact for *any* ring map,
  because the section provides a contracting homotopy.
* `Stacks.Descent.injective_amitsurUnit` and `Stacks.Descent.exact_amitsurUnit_amitsurDiff`:
  for a faithfully flat `A → B` the complex `0 → M → B ⊗[A] M → B ⊗[A] B ⊗[A] M` is exact.
* `Stacks.Descent.amitsurCoface_eq_iff`: an element of `B ⊗[A] M` on which the two coface maps
  agree comes from `M`, and `Stacks.Descent.existsUnique_amitsurUnit_eq` adds uniqueness.

## Implementation notes

The three terms are `M`, `B ⊗[A] M` and `B ⊗[A] (B ⊗[A] M)`, bracketed to the right, so that
the second coface map is literally `LinearMap.lTensor B` of the augmentation and the third term
is the second term of the complex for the module `B ⊗[A] M`.  With that bracketing both halves
of the homotopy are instances of the same two declarations: the homotopy in degree `0` is
`Stacks.Descent.amitsurContract` for the module `B ⊗[A] M`, and the one in degree `-1` is
`Stacks.Descent.amitsurContract` for `M`.

`Stacks.Descent.exact_lTensor_amitsur` is stated without any flatness hypothesis; the
faithfully flat hypothesis enters only in the two theorems that descend along it.

## References

* [Stacks Project, Tag 023K](https://stacks.math.columbia.edu/tag/023K)
* [Stacks Project, Tag 023L](https://stacks.math.columbia.edu/tag/023L)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
-/

@[expose] public noncomputable section

open TensorProduct

namespace Stacks.Descent

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
  (M : Type*) [AddCommGroup M] [Module A M]

/-- The augmentation `M → B ⊗[A] M`, `m ↦ 1 ⊗ m`, of the Amitsur complex of `A → B` with
coefficients in `M`. -/
def amitsurUnit : M →ₗ[A] B ⊗[A] M := TensorProduct.mk A B M 1

/-- The augmentation `Stacks.Descent.amitsurUnit` sends `m` to `1 ⊗ m`. -/
@[simp]
lemma amitsurUnit_apply (m : M) : amitsurUnit A B M m = (1 : B) ⊗ₜ[A] m := rfl

/-- Multiplying the two algebra factors, `b ⊗ b' ⊗ m ↦ b b' ⊗ m`.  This is the contracting
homotopy of the Amitsur complex base changed along `A → B`, where the two algebra factors are
the new base and the section is multiplication. -/
def amitsurContract : B ⊗[A] (B ⊗[A] M) →ₗ[A] B ⊗[A] M :=
  (LinearMap.mul' A B).rTensor M ∘ₗ (TensorProduct.assoc A B B M).symm.toLinearMap

/-- The multiplication map `Stacks.Descent.amitsurContract` sends `b ⊗ b' ⊗ m` to `b b' ⊗ m`. -/
@[simp]
lemma amitsurContract_tmul (b b' : B) (m : M) :
    amitsurContract A B M (b ⊗ₜ[A] (b' ⊗ₜ[A] m)) = (b * b') ⊗ₜ[A] m := by
  simp [amitsurContract]

/-- The first coface map `B ⊗[A] M → B ⊗[A] B ⊗[A] M`, `b ⊗ m ↦ 1 ⊗ b ⊗ m`.  It is the
augmentation of the Amitsur complex with coefficients in `B ⊗[A] M`. -/
def amitsurCoface₀ : B ⊗[A] M →ₗ[A] B ⊗[A] (B ⊗[A] M) := amitsurUnit A B (B ⊗[A] M)

/-- The second coface map `B ⊗[A] M → B ⊗[A] B ⊗[A] M`, `b ⊗ m ↦ b ⊗ 1 ⊗ m`.  It is the
augmentation with coefficients in `M`, tensored with `B`. -/
def amitsurCoface₁ : B ⊗[A] M →ₗ[A] B ⊗[A] (B ⊗[A] M) :=
  LinearMap.lTensor B (amitsurUnit A B M)

/-- The first coface map `Stacks.Descent.amitsurCoface₀` sends `b ⊗ m` to `1 ⊗ b ⊗ m`. -/
@[simp]
lemma amitsurCoface₀_tmul (b : B) (m : M) :
    amitsurCoface₀ A B M (b ⊗ₜ[A] m) = (1 : B) ⊗ₜ[A] (b ⊗ₜ[A] m) := rfl

/-- The second coface map `Stacks.Descent.amitsurCoface₁` sends `b ⊗ m` to `b ⊗ 1 ⊗ m`. -/
@[simp]
lemma amitsurCoface₁_tmul (b : B) (m : M) :
    amitsurCoface₁ A B M (b ⊗ₜ[A] m) = b ⊗ₜ[A] ((1 : B) ⊗ₜ[A] m) := rfl

/-- The differential in degree `0` of the Amitsur complex, the difference of the two coface
maps. -/
def amitsurDiff : B ⊗[A] M →ₗ[A] B ⊗[A] (B ⊗[A] M) :=
  amitsurCoface₀ A B M - amitsurCoface₁ A B M

/-- The differential `Stacks.Descent.amitsurDiff` is the difference of the two coface maps. -/
@[simp]
lemma amitsurDiff_apply (x : B ⊗[A] M) :
    amitsurDiff A B M x = amitsurCoface₀ A B M x - amitsurCoface₁ A B M x := rfl

/-- Multiplication retracts the base change of the augmentation: this is the degree `-1` half of
the contracting homotopy of the base-changed Amitsur complex. -/
lemma amitsurContract_comp_lTensor_amitsurUnit :
    amitsurContract A B M ∘ₗ LinearMap.lTensor B (amitsurUnit A B M) = LinearMap.id := by
  ext b m
  simp

/-- The augmentation is a cycle: the two coface maps agree on its image. -/
lemma amitsurDiff_comp_amitsurUnit : amitsurDiff A B M ∘ₗ amitsurUnit A B M = 0 := by
  ext m
  simp

/-- **The contracting homotopy of the base-changed Amitsur complex.**  On
`B ⊗[A] (B ⊗[A] M)` the identity is the sum of the two composites built from multiplication,
one through the differential in degree `0` and one through the augmentation. -/
lemma amitsurHomotopy :
    amitsurContract A B (B ⊗[A] M) ∘ₗ LinearMap.lTensor B (amitsurDiff A B M) +
      LinearMap.lTensor B (amitsurUnit A B M) ∘ₗ amitsurContract A B M = LinearMap.id := by
  ext b b' m
  simp [tmul_sub]

/-- **The base change of the Amitsur complex along `A → B` is exact**, for an arbitrary ring map
`A → B`: the base-changed complex is the complex of `B → B ⊗[A] B`, which has a section, and
`Stacks.Descent.amitsurHomotopy` is the resulting contracting homotopy. -/
lemma exact_lTensor_amitsur :
    Function.Exact (LinearMap.lTensor B (amitsurUnit A B M))
      (LinearMap.lTensor B (amitsurDiff A B M)) := by
  intro y
  refine ⟨fun hy => ⟨amitsurContract A B M y, ?_⟩, ?_⟩
  · have h := LinearMap.congr_fun (amitsurHomotopy A B M) y
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply] at h
    rw [hy, map_zero, zero_add] at h
    exact h
  · rintro ⟨x, rfl⟩
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, amitsurDiff_comp_amitsurUnit]
    simp

variable [Module.FaithfullyFlat A B]

/-- **The augmentation of the Amitsur complex is injective** when `B` is faithfully flat over
`A`.  Its base change is split injective, by
`Stacks.Descent.amitsurContract_comp_lTensor_amitsurUnit`. -/
theorem injective_amitsurUnit : Function.Injective (amitsurUnit A B M) := by
  rw [← Module.FaithfullyFlat.lTensor_injective_iff_injective A B]
  refine Function.LeftInverse.injective (g := amitsurContract A B M) fun x => ?_
  simpa using LinearMap.congr_fun (amitsurContract_comp_lTensor_amitsurUnit A B M) x

/-- **The Amitsur complex of a faithfully flat ring map is exact in degree `0`.**  Together with
`Stacks.Descent.injective_amitsurUnit` this says that
`0 → M → B ⊗[A] M → B ⊗[A] B ⊗[A] M` is exact, which is the bottom of Stacks 023M. -/
theorem exact_amitsurUnit_amitsurDiff :
    Function.Exact (amitsurUnit A B M) (amitsurDiff A B M) := by
  rw [← Module.FaithfullyFlat.lTensor_exact_iff_exact A B]
  exact exact_lTensor_amitsur A B M

/-- **Descent of elements along a faithfully flat ring map.**  An element of `B ⊗[A] M` on which
the two coface maps agree is `1 ⊗ m` for some `m : M`. -/
theorem amitsurCoface_eq_iff (x : B ⊗[A] M) :
    amitsurCoface₀ A B M x = amitsurCoface₁ A B M x ↔ ∃ m, amitsurUnit A B M m = x := by
  rw [← sub_eq_zero, ← amitsurDiff_apply]
  exact exact_amitsurUnit_amitsurDiff A B M x

/-- The element of `M` descending a given invariant element of `B ⊗[A] M` is unique. -/
theorem existsUnique_amitsurUnit_eq {x : B ⊗[A] M}
    (hx : amitsurCoface₀ A B M x = amitsurCoface₁ A B M x) :
    ∃! m, amitsurUnit A B M m = x := by
  obtain ⟨m, hm⟩ := (amitsurCoface_eq_iff A B M x).1 hx
  exact ⟨m, hm, fun n hn => injective_amitsurUnit A B M (hn.trans hm.symm)⟩

/-- **`M` is the equalizer of the two coface maps** when `B` is faithfully flat over `A`: the
augmentation is an isomorphism onto the submodule of `B ⊗[A] M` on which they agree. -/
def amitsurEqualizerEquiv :
    M ≃ₗ[A] LinearMap.eqLocus (amitsurCoface₀ A B M) (amitsurCoface₁ A B M) :=
  LinearEquiv.ofBijective
    ((amitsurUnit A B M).codRestrict _ fun m => by
      have h := congrArg (fun f : M →ₗ[A] B ⊗[A] (B ⊗[A] M) => f m)
        (amitsurDiff_comp_amitsurUnit A B M)
      simp only [LinearMap.comp_apply, LinearMap.zero_apply, amitsurDiff_apply,
        sub_eq_zero] at h
      exact h)
    ⟨fun m n h => injective_amitsurUnit A B M (congrArg Subtype.val h),
      fun y => ((amitsurCoface_eq_iff A B M y.1).1 y.2).imp fun m hm => Subtype.ext hm⟩

/-- The equivalence `Stacks.Descent.amitsurEqualizerEquiv` sends `m` to the element `1 ⊗ m`. -/
@[simp]
lemma amitsurEqualizerEquiv_apply (m : M) :
    (amitsurEqualizerEquiv A B M m : B ⊗[A] M) = (1 : B) ⊗ₜ[A] m := rfl

end Stacks.Descent

end
