module

public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.FormsAlgEquiv

/-!
# Tensoring the transport of divided power forms along an isomorphism of divided power rings

An isomorphism of divided power rings `f : (B, J, δ) ≅ (C, K, ε)` over `A` induces, through
`Crystalline.differentialFormsEquivOfAlgEquiv`, an additive equivalence
`Ωⁱ_{B/A,δ} ≃+ Ωⁱ_{C/A,ε}` that is semilinear over the ring isomorphism. For a module `M`
carrying a `B`-module and a `C`-module structure that agree along `f`, it induces an additive
equivalence `M ⊗_B Ωⁱ_{B/A,δ} ≃+ M ⊗_C Ωⁱ_{C/A,ε}`.

More generally, for a ring isomorphism `f : B ≃+* C`, such a module `M`, and an additive
isomorphism `g : X ≃+ Y` of a `B`-module with a `C`-module that is semilinear over `f`, there is
an additive equivalence `M ⊗_B X ≃+ M ⊗_C Y` sending `m ⊗ x` to `m ⊗ g x`.

## Main definitions

* `Stacks.tensorCongrOfRingEquiv`: the additive equivalence `M ⊗_B X ≃+ M ⊗_C Y` induced by a ring
  isomorphism and a semilinear additive isomorphism.
* `Crystalline.tensorFormsEquivOfAlgEquiv`: the additive equivalence
  `M ⊗_B Ωⁱ_{B/A,δ} ≃+ M ⊗_C Ωⁱ_{C/A,ε}` induced by an isomorphism of divided power rings, bundled
  with its value on a pure tensor.

## Main results

* `Stacks.tensorCongrOfRingEquiv_tmul`, `Stacks.tensorCongrOfRingEquiv_symm_tmul`: the values of
  the equivalence and of its inverse on pure tensors.

## References

* [Stacks Project, Lemma 60.21.1, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Stacks

/-! ### Transporting a tensor product along a ring isomorphism -/

section TensorCongr

variable {B : Type*} {C : Type*} [CommRing B] [CommRing C] (f : B ≃+* C)
variable {M : Type*} [AddCommGroup M] [Module B M] [Module C M]
variable {X : Type*} {Y : Type*} [AddCommGroup X] [Module B X] [AddCommGroup Y] [Module C Y]

/-- The biadditive map `(m, x) ↦ m ⊗ g x` from `M × X` to `M ⊗_C Y`, in curried form. -/
def tensorCongrAux (g : X ≃+ Y) : M →+ (X →+ M ⊗[C] Y) where
  toFun m :=
    { toFun := fun x ↦ m ⊗ₜ[C] g x
      map_zero' := by rw [map_zero, TensorProduct.tmul_zero]
      map_add' := fun x y ↦ by rw [map_add, TensorProduct.tmul_add] }
  map_zero' := by ext x; simp
  map_add' m m' := by ext x; simp [TensorProduct.add_tmul]

/-- The value of `tensorCongrAux g` at `m` and `x` is `m ⊗ g x`. -/
@[simp]
theorem tensorCongrAux_apply (g : X ≃+ Y) (m : M) (x : X) :
    tensorCongrAux (C := C) (M := M) g m x = m ⊗ₜ[C] g x :=
  rfl

/-- The biadditive map `tensorCongrAux g` is `B`-balanced: its values at `(b • m, x)` and
`(m, b • x)` agree. -/
theorem tensorCongrAux_balanced (hsm : ∀ (b : B) (m : M), b • m = f b • m) (g : X ≃+ Y)
    (hg : ∀ (b : B) (x : X), g (b • x) = f b • g x) (b : B) (m : M) (x : X) :
    tensorCongrAux (C := C) (M := M) g (b • m) x =
      tensorCongrAux (C := C) (M := M) g m (b • x) := by
  rw [tensorCongrAux_apply, tensorCongrAux_apply, hsm, hg, TensorProduct.smul_tmul]

/-- The additive map `M ⊗_B X →+ M ⊗_C Y` sending `m ⊗ x` to `m ⊗ g x`. -/
def tensorCongrHom (hsm : ∀ (b : B) (m : M), b • m = f b • m) (g : X ≃+ Y)
    (hg : ∀ (b : B) (x : X), g (b • x) = f b • g x) :
    M ⊗[B] X →+ M ⊗[C] Y :=
  TensorProduct.liftAddHom (R := B) (tensorCongrAux (C := C) (M := M) g)
    (tensorCongrAux_balanced f hsm g hg)

/-- The map `tensorCongrHom` sends `m ⊗ x` to `m ⊗ g x`. -/
@[simp]
theorem tensorCongrHom_tmul (hsm : ∀ (b : B) (m : M), b • m = f b • m) (g : X ≃+ Y)
    (hg : ∀ (b : B) (x : X), g (b • x) = f b • g x) (m : M) (x : X) :
    tensorCongrHom f hsm g hg (m ⊗ₜ[B] x) = m ⊗ₜ[C] g x :=
  TensorProduct.liftAddHom_tmul (tensorCongrAux (C := C) (M := M) g)
    (tensorCongrAux_balanced f hsm g hg) m x

/-- If the two module structures on `M` agree along `f`, they agree along `f.symm`. -/
theorem smul_eq_symm_smul (hsm : ∀ (b : B) (m : M), b • m = f b • m) (c : C) (m : M) :
    c • m = f.symm c • m := by
  rw [hsm (f.symm c) m, f.apply_symm_apply]

/-- The inverse of a semilinear additive isomorphism is semilinear over the inverse ring
isomorphism. -/
theorem map_smul_symm (g : X ≃+ Y) (hg : ∀ (b : B) (x : X), g (b • x) = f b • g x) (c : C)
    (y : Y) : g.symm (c • y) = f.symm c • g.symm y :=
  g.injective <| by rw [g.apply_symm_apply, hg, f.apply_symm_apply, g.apply_symm_apply]

/-- If `M` is a module over `B` and over `C` with the two actions agreeing along `f : B ≃+* C`,
and `g : X ≃+ Y` is additive and semilinear over `f`, this is the additive equivalence
`M ⊗_B X ≃+ M ⊗_C Y` sending `m ⊗ x` to `m ⊗ g x`. -/
def tensorCongrOfRingEquiv (hsm : ∀ (b : B) (m : M), b • m = f b • m) (g : X ≃+ Y)
    (hg : ∀ (b : B) (x : X), g (b • x) = f b • g x) :
    M ⊗[B] X ≃+ M ⊗[C] Y where
  toFun := tensorCongrHom f hsm g hg
  invFun := tensorCongrHom f.symm (smul_eq_symm_smul f hsm) g.symm (map_smul_symm f g hg)
  map_add' := map_add _
  left_inv z := by
    induction z using TensorProduct.inductionOn with
    | tmul m x => rw [tensorCongrHom_tmul, tensorCongrHom_tmul, g.symm_apply_apply]
    | add z w hz hw => rw [map_add, map_add, hz, hw]
  right_inv z := by
    induction z using TensorProduct.inductionOn with
    | tmul m y => rw [tensorCongrHom_tmul, tensorCongrHom_tmul, g.apply_symm_apply]
    | add z w hz hw => rw [map_add, map_add, hz, hw]

/-- The equivalence `tensorCongrOfRingEquiv` sends `m ⊗ x` to `m ⊗ g x`. -/
@[simp]
theorem tensorCongrOfRingEquiv_tmul (hsm : ∀ (b : B) (m : M), b • m = f b • m) (g : X ≃+ Y)
    (hg : ∀ (b : B) (x : X), g (b • x) = f b • g x) (m : M) (x : X) :
    tensorCongrOfRingEquiv f hsm g hg (m ⊗ₜ[B] x) = m ⊗ₜ[C] g x :=
  tensorCongrHom_tmul f hsm g hg m x

/-- The inverse of `tensorCongrOfRingEquiv` sends `m ⊗ y` to `m ⊗ g.symm y`. -/
@[simp]
theorem tensorCongrOfRingEquiv_symm_tmul (hsm : ∀ (b : B) (m : M), b • m = f b • m) (g : X ≃+ Y)
    (hg : ∀ (b : B) (x : X), g (b • x) = f b • g x) (m : M) (y : Y) :
    (tensorCongrOfRingEquiv f hsm g hg).symm (m ⊗ₜ[C] y) = m ⊗ₜ[B] g.symm y :=
  tensorCongrHom_tmul f.symm (smul_eq_symm_smul f hsm) g.symm (map_smul_symm f g hg) m y

end TensorCongr

end Stacks

namespace Crystalline

/-! ### The divided power forms case -/

section FormsAlgEquivTensor

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable {J : Ideal B} (delta : DividedPowers J)
variable {C : Type w} [CommRing C] [Algebra A C] {K : Ideal C}
variable {M : Type*} [AddCommGroup M] [Module B M] [Module C M]

/-- An isomorphism `f` of divided power rings over `A` induces an additive equivalence
`M ⊗_B Ωⁱ_{B/A,δ} ≃+ M ⊗_C Ωⁱ_{C/A,ε}`, for a module `M` whose two module structures agree along
`f`; it is bundled with its value `m ⊗ x ↦ m ⊗ Ω^i(f) x` on pure tensors, where `Ω^i(f)` is
`Crystalline.mapDifferentialFormsOfDPMorphism`. -/
noncomputable def tensorFormsEquivOfAlgEquiv (epsilon : DividedPowers K) (f : B ≃ₐ[A] C)
    (hf : delta.IsDPMorphism epsilon f.toAlgHom.toRingHom)
    (hJ : J.map f.toAlgHom.toRingHom = K)
    (hsm : ∀ (b : B) (m : M), b • m = f b • m) (i : ℕ) :
    { E : M ⊗[B] dividedPowerDifferentialForms (A := A) delta i ≃+
        M ⊗[C] dividedPowerDifferentialForms (A := A) epsilon i //
      ∀ (m : M) (x : dividedPowerDifferentialForms (A := A) delta i),
        E (m ⊗ₜ[B] x) = m ⊗ₜ[C] mapDifferentialFormsOfDPMorphism (A := A) (J := J)
          (delta := delta) epsilon f.toAlgHom hf i x } :=
  ⟨Stacks.tensorCongrOfRingEquiv (M := M) f.toRingEquiv hsm
      (differentialFormsEquivOfAlgEquiv delta epsilon f hf hJ i).1
      fun b x ↦ by
        rw [(differentialFormsEquivOfAlgEquiv delta epsilon f hf hJ i).2,
          (differentialFormsEquivOfAlgEquiv delta epsilon f hf hJ i).2]
        exact (mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := delta) epsilon
          f.toAlgHom hf i).map_smul' b x,
    fun m x ↦ by
      rw [Stacks.tensorCongrOfRingEquiv_tmul,
        (differentialFormsEquivOfAlgEquiv delta epsilon f hf hJ i).2 x]⟩

end FormsAlgEquivTensor

end Crystalline

end
