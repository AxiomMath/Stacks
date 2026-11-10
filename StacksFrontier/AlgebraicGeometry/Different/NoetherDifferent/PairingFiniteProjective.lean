module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.RingTheory.LocalRing.Module
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.NoetherDifferent.PairingIndependence

/-!
# The Noether pairing of a finite projective algebra

For a finite projective algebra `C` over `A` the canonical pairing of the relative dualizing
module with the diagonal annihilator is perfect. Through the self factorization the dualizing
module is the linear dual `Hom_A(C, A)` and the pairing is plain contraction, so the statement
becomes that contracting against the diagonal annihilator identifies it with
`Hom_C(Hom_A(C, A), C)`. That identification is the canonical isomorphism
`C ⊗_A C ≅ Hom_A(Hom_A(C, A), C)` of a finite projective module, restricted to the annihilator.

## Main definitions

* `Stacks.Discriminant.contractionEquiv` is the canonical isomorphism of `C ⊗_A C` with
  `Hom_A(Hom_A(C, A), C)` for a finite projective algebra.
* `Stacks.Discriminant.diagonalContractionMap` is its restriction to the diagonal annihilator,
  valued in the `C`-linear maps.

## Main results

* `Stacks.Discriminant.diagonalContractionMap_bijective`: the restriction is bijective.
* `Stacks.Discriminant.noetherPairing_flip_bijective_selfFactorization`: the map induced by the
  canonical pairing is bijective for the self factorization of a finite projective algebra.
* `Stacks.Discriminant.noetherPairing_flip_bijective_selfFactorization_of_flat`: the same for a
  finite flat algebra over a Noetherian base.
* `Stacks.Discriminant.noetherPairing_flip_bijective_selfFactorization_away`: the same for an
  away localization which is finite over a Noetherian base.

## Implementation notes

Contraction of a tensor against a functional on the second factor is `C`-linear on the diagonal
annihilator, though not on the whole of `C ⊗_A C`: the two ways of multiplying a tensor by an
element of `C` agree modulo the kernel of multiplication, which the annihilator kills. That is
what makes `Stacks.Discriminant.diagonalContractionMap` well defined.

## References

* [Stacks Project, Tag 0BVS](https://stacks.math.columbia.edu/tag/0BVS)
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.Discriminant

universe u v w

attribute [local instance] algebraDualModule

section Contraction

variable {A C : Type*} [CommRing A] [CommRing C] [Algebra A C]

/-- Multiplying a tensor on the left by `a ⊗ 1` rescales the functional it is contracted
against. -/
theorem tensorContract_tmul_one_mul (f : Module.Dual A C) (a : C) (z : C ⊗[A] C) :
    tensorContract A C f ((a ⊗ₜ[A] (1 : C)) * z) = tensorContract A C (a • f) z := by
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => rw [mul_add, map_add, map_add, hz, hw]
  | tmul x y =>
      simp [tensorContract, TensorProduct.lift.tmul, algebraDualModule_smul_apply]

/-- Multiplying a tensor on the left by `1 ⊗ a` rescales its contraction. -/
theorem tensorContract_one_tmul_mul (f : Module.Dual A C) (a : C) (z : C ⊗[A] C) :
    tensorContract A C f (((1 : C) ⊗ₜ[A] a) * z) = a * tensorContract A C f z := by
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => rw [mul_add, map_add, map_add, hz, hw, mul_add]
  | tmul x y => simp [tensorContract, TensorProduct.lift.tmul]

variable [Module.Finite A C] [Module.Projective A C]

/-- For a finite projective algebra, contraction identifies `C ⊗_A C` with the `A`-linear maps
from the linear dual of `C` to `C`. -/
noncomputable def contractionEquiv :
    (C ⊗[A] C) ≃ₗ[A] (Module.Dual A C →ₗ[A] C) :=
  (TensorProduct.congr (Module.evalEquiv A C) (LinearEquiv.refl A C)).trans
    (dualTensorHomEquiv A (Module.Dual A C) C)

/-- The identification is contraction. -/
@[simp]
theorem contractionEquiv_apply (z : C ⊗[A] C) (f : Module.Dual A C) :
    contractionEquiv (A := A) (C := C) z f = tensorContract A C f z := by
  induction z using TensorProduct.inductionOn with
  | tmul x y => simp [contractionEquiv, tensorContract]
  | add x y hx hy => simp [hx, hy]

/-- Contracting a product against a functional, when the right factor represents a `C`-linear
map on the dual. -/
private theorem tensorContract_mul_map (z j : C ⊗[A] C) (h : Module.Dual A C →ₗ[A] C)
    (hh : ∀ (c : C) f, h (c • f) = c • h f)
    (hj : contractionEquiv (A := A) (C := C) j = h)
    (f : Module.Dual A C) :
    tensorContract A C f (z * j) = (Algebra.TensorProduct.lmul' A z) * h f := by
  induction z using TensorProduct.inductionOn with
  | add z₁ z₂ hz₁ hz₂ => rw [add_mul, map_add, hz₁, hz₂, map_add, add_mul]
  | tmul x y =>
      have hx : tensorContract A C (x • f) j = x * h f := by
        rw [← contractionEquiv_apply, hj]
        exact hh x f
      calc
        tensorContract A C f ((x ⊗ₜ[A] y) * j) =
            tensorContract A C f
              (((x ⊗ₜ[A] (1 : C)) * ((1 : C) ⊗ₜ[A] y)) * j) := by
              congr 1
              simp
        _ = tensorContract A C f
              ((x ⊗ₜ[A] (1 : C)) * (((1 : C) ⊗ₜ[A] y) * j)) := by rw [mul_assoc]
        _ = tensorContract A C (x • f) (((1 : C) ⊗ₜ[A] y) * j) :=
              tensorContract_tmul_one_mul f x (((1 : C) ⊗ₜ[A] y) * j)
        _ = y * tensorContract A C (x • f) j := by
              rw [tensorContract_one_tmul_mul]
        _ = y * (x * h f) := by rw [hx]
        _ = (Algebra.TensorProduct.lmul' A (x ⊗ₜ[A] y)) * h f := by
              simp [Algebra.TensorProduct.lmul'_apply_tmul, mul_assoc, mul_left_comm]

/-- Contraction against the diagonal annihilator, as a `C`-linear map to the `C`-linear maps on
the linear dual of `C`. -/
noncomputable def diagonalContractionMap :
    ↑(diagonalAnnihilator A C) →ₗ[C] (Module.Dual A C →ₗ[C] C) where
  toFun j :=
    { toFun := fun f => tensorContract A C f j.1
      map_add' := fun f g => tensorContract_add A C f g j.1
      map_smul' := fun c f => tensorContract_smul_functional A C f c j }
  map_add' := by
    intro j k
    ext f
    simp [tensorContract]
  map_smul' := by
    intro c j
    ext f
    simpa [Algebra.smul_def, smul_eq_mul] using
      tensorContract_smul_diagonal A C f c j

/-- For a finite projective algebra, contraction identifies the diagonal annihilator with the
`C`-linear maps from the relative dualizing module to `C`. -/
theorem diagonalContractionMap_bijective :
    Function.Bijective (diagonalContractionMap (A := A) (C := C)) := by
  have : IsScalarTower A C (Module.Dual A C) := by
    refine ⟨fun a c f => ?_⟩
    ext x
    simpa [Algebra.smul_def, mul_assoc] using map_smul f a (c * x)
  refine ⟨fun j k hjk => ?_, fun φ => ?_⟩
  · refine Subtype.ext ((contractionEquiv (A := A) (C := C)).injective ?_)
    ext f
    rw [contractionEquiv_apply, contractionEquiv_apply]
    exact LinearMap.congr_fun hjk f
  · let h : Module.Dual A C →ₗ[A] C := φ.restrictScalars A
    let jval := (contractionEquiv (A := A) (C := C)).symm h
    have hsmul : ∀ (c : C) f, h (c • f) = c • h f := fun c f =>
      LinearMap.map_smul_of_tower φ c f
    have hj : jval ∈ diagonalAnnihilator A C := by
      change jval ∈ (RingHom.ker (Algebra.TensorProduct.lmul' A).toRingHom).annihilator
      rw [Submodule.mem_annihilator]
      intro z hz
      have hz0 : (Algebra.TensorProduct.lmul' A) z = 0 := RingHom.mem_ker.mp hz
      have hzmul : z * jval = 0 := by
        refine (contractionEquiv (A := A) (C := C)).injective ?_
        ext f
        rw [contractionEquiv_apply,
          tensorContract_mul_map z jval h hsmul (by simp [jval]) f, hz0]
        simp
      simpa [mul_comm] using hzmul
    refine ⟨⟨jval, hj⟩, ?_⟩
    ext f
    change tensorContract A C f jval = φ f
    rw [← contractionEquiv_apply]
    exact LinearMap.congr_fun ((contractionEquiv (A := A) (C := C)).apply_symm_apply h) f

end Contraction

section SelfFactorization

variable {A C : Type*} [CommRing A] [CommRing C] [Algebra A C] [Module.Finite A C]

/-- For a finite projective algebra the map induced by the canonical pairing of the self
factorization is bijective. -/
theorem noetherPairing_flip_bijective_selfFactorization [Module.Projective A C] :
    Function.Bijective (noetherPairing (selfFactorization A C)).flip := by
  let F := selfFactorization A C
  let comm := TensorProduct.comm C (Module.Dual A C) C
  let ecomm : dualizingModule F ≃ₗ[C] C ⊗[C] Module.Dual A C := comm.toAddEquiv.linearEquiv C
  let eω := ecomm.trans (TensorProduct.lid C (Module.Dual A C))
  let eHom : (dualizingModule F →ₗ[C] C) ≃ₗ[C] (Module.Dual A C →ₗ[C] C) :=
    LinearEquiv.arrowCongr eω (LinearEquiv.refl C C)
  have hformula (j : ↑(diagonalAnnihilator A C)) (f : Module.Dual A C) :
      noetherPairing F (dualizingModule.tmul F f 1) j = tensorContract A C f j.1 := by
    simpa using noetherPairing_selfFactorization_tmul f 1 j
  have heω (f : Module.Dual A C) : eω.symm f = dualizingModule.tmul F f 1 := by
    change comm.symm ((1 : C) ⊗ₜ[C] f) = f ⊗ₜ[C] (1 : C)
    rw [TensorProduct.comm_symm_tmul]
  have hdiag := diagonalContractionMap_bijective (A := A) (C := C)
  refine ⟨fun j k hjk => hdiag.1 ?_, fun φ => ?_⟩
  · ext f
    change tensorContract A C f j.1 = tensorContract A C f k.1
    rw [← hformula j f, ← hformula k f]
    exact LinearMap.congr_fun hjk (dualizingModule.tmul F f 1)
  · obtain ⟨j, hj⟩ := hdiag.2 (eHom φ)
    refine ⟨j, eHom.injective ?_⟩
    ext f
    change noetherPairing F (eω.symm f) j = φ (eω.symm f)
    rw [heω, hformula j f]
    simpa [diagonalContractionMap, eHom, heω] using
      LinearMap.congr_fun hj f

/-- For a finite flat algebra over a Noetherian base the map induced by the canonical pairing of
the self factorization is bijective. -/
theorem noetherPairing_flip_bijective_selfFactorization_of_flat
    [IsNoetherianRing A] [Module.Flat A C] :
    Function.Bijective (noetherPairing (selfFactorization A C)).flip := by
  have : Module.FinitePresentation A C := Module.finitePresentation_of_finite A C
  have : Module.Projective A C := Module.Flat.projective_of_finitePresentation
  exact noetherPairing_flip_bijective_selfFactorization

end SelfFactorization

/-- For an away localization of a flat algebra which is itself finite over a Noetherian base,
the map induced by the canonical pairing of the self factorization is bijective. -/
theorem noetherPairing_flip_bijective_selfFactorization_away
    {A C : Type*} [CommRing A] [CommRing C] [Algebra A C]
    [IsNoetherianRing A] [Module.Flat A C] (e : C)
    (hfinite : Module.Finite A (Localization.Away e)) :
    Function.Bijective
      (noetherPairing (selfFactorization A (Localization.Away e))).flip := by
  have : Module.Finite A (Localization.Away e) := hfinite
  have : Module.Flat C (Localization.Away e) := inferInstance
  have : Module.Flat A (Localization.Away e) := Module.Flat.trans A C (Localization.Away e)
  exact noetherPairing_flip_bijective_selfFactorization_of_flat

/-- For an away localization of the base change of a flat algebra along an étale map, which is
finite over the new base, the map induced by the canonical pairing of the self factorization is
bijective. -/
theorem noetherPairing_flip_bijective_selfFactorization_baseChange_away
    {A B A' : Type*} [CommRing A] [CommRing B] [CommRing A']
    [Algebra A B] [Algebra A A'] [Module.Flat A B]
    [IsNoetherianRing A'] (e : A' ⊗[A] B)
    (hfinite : Module.Finite A' (Localization.Away e)) :
    Function.Bijective
      (noetherPairing (selfFactorization A' (Localization.Away e))).flip := by
  have : Module.Flat A' (A' ⊗[A] B) := Module.Flat.baseChange A A' B
  exact noetherPairing_flip_bijective_selfFactorization_away
    (A := A') (C := A' ⊗[A] B) e hfinite

end Stacks.Discriminant

end
