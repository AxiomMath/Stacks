module

public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Splitting a complex off its degree-zero term

Two elementary facts used in the proof of [Stacks, Tag 0E62].

* `CochainComplex.exists_iso_single_biprod_of_d_zero`: a cochain complex `K` concentrated in
  degrees `≥ 0` whose differential out of degree `0` vanishes is the direct sum, in the category
  of complexes, of its degree-zero term placed in degree `0` and a complex `T` which vanishes in
  degrees `≤ 0` and agrees with `K` in degrees `> 0`.
* `RingHom.bijective_of_linearEquiv_self`: a ring homomorphism `ρ : B →+* R` for which `R`,
  viewed as a `B`-module through `ρ`, is isomorphic to `B`, is bijective. This is how "the
  `𝒪_S`-algebra `f_*𝒪_X` is free of rank one" becomes "`𝒪_S → f_*𝒪_X` is an isomorphism".

## Implementation notes

The splitting is obtained from the degree-zero projection `π : K ⟶ K⁰[0]`, which is a split
epimorphism once `d⁰ = 0` (its section is the inclusion of `K⁰` in degree `0`). In a preadditive
category a split epimorphism with a kernel exhibits its source as the biproduct of the kernel and
the target (`CategoryTheory.Limits.isBilimitBinaryBiconeOfIsSplitEpiOfKernel`), and kernels of
complexes are computed degreewise.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CochainComplex

variable {R : Type u} [Ring R]

/-- **A complex in degrees `≥ 0` with vanishing first differential splits off its degree-zero
term.** -/
theorem exists_iso_single_biprod_of_d_zero (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : ∀ i : ℤ, i < 0 → IsZero (K.X i)) (hd : K.d 0 1 = 0) :
    ∃ T : CochainComplex (ModuleCat.{u} R) ℤ,
      (∀ i : ℤ, i ≤ 0 → IsZero (T.X i)) ∧ (∀ i : ℤ, 0 < i → Nonempty (T.X i ≅ K.X i)) ∧
        Nonempty (K ≅ (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
          (K.X 0) ⊞ T) := by
  let S := (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj (K.X 0)
  let π : K ⟶ S := HomologicalComplex.mkHomToSingle (𝟙 (K.X 0)) (fun i hi => by
    obtain rfl : i = -1 := by
      simp at hi
      omega
    exact (hK (-1) (by norm_num)).eq_of_src _ _)
  let σ : S ⟶ K := HomologicalComplex.mkHomFromSingle (𝟙 (K.X 0)) (fun k hk => by
    obtain rfl : k = 1 := by
      simp at hk
      omega
    rw [hd, comp_zero])
  have hσπ : σ ≫ π = 𝟙 S := by
    apply HomologicalComplex.from_single_hom_ext
    rw [HomologicalComplex.comp_f, HomologicalComplex.mkHomFromSingle_f,
      HomologicalComplex.mkHomToSingle_f, HomologicalComplex.id_f]
    simp
  have : IsSplitEpi π := ⟨⟨⟨σ, hσπ⟩⟩⟩
  let T := kernel π
  let hT (i : ℤ) : T.X i ≅ kernel (π.f i) :=
    PreservesKernel.iso (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) i) π
  refine ⟨T, fun i hi => ?_, fun i hi => ?_, ⟨?_⟩⟩
  · refine IsZero.of_iso ?_ (hT i)
    rcases hi.lt_or_eq with hi | rfl
    · exact IsZero.of_mono (kernel.ι (π.f i)) (hK i hi)
    · have : Mono (π.f 0) := by
        rw [HomologicalComplex.mkHomToSingle_f]
        infer_instance
      exact isZero_kernel_of_mono _
  · refine ⟨(hT i) ≪≫ ?_⟩
    rw [(HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (K.X 0) i
      (by omega)).eq_of_tgt (π.f i) 0]
    exact kernelZeroIsoSource
  · exact biprod.uniqueUpToIso _ _
      (isBilimitBinaryBiconeOfIsSplitEpiOfKernel (kernelIsKernel π)) ≪≫ biprod.braiding _ _

end CochainComplex

namespace RingHom

/-- **A ring map making the target free of rank one is bijective.** If `R`, viewed as a
`B`-module through `ρ : B →+* R`, is isomorphic to `B`, then `ρ` is bijective. -/
theorem bijective_of_linearEquiv_self {B R : Type*} [CommRing B] [CommRing R] (ρ : B →+* R)
    [Module B R] (hsmul : ∀ (c : B) (r : R), c • r = ρ c * r) (e : R ≃ₗ[B] B) :
    Function.Bijective ρ := by
  set x : R := e.symm 1 with hx
  set b : B := e 1 with hb
  have hρx : ∀ c : B, ρ c * x = e.symm c := fun c => by
    rw [← hsmul, hx, ← LinearEquiv.map_smul, smul_eq_mul, mul_one]
  have h1 : (1 : R) = ρ b * x := by simp [hρx, hb]
  set a : B := e (x * x) with ha
  have hxx : x * x = ρ a * x := by simp [hρx, ha]
  have hba : b * a = 1 := by
    have h2 : x = (b * a) • x := by
      rw [hsmul, map_mul, mul_assoc, ← hxx, ← mul_assoc, ← h1, one_mul]
    have h3 := congrArg e h2
    rw [LinearEquiv.map_smul, hx, e.apply_symm_apply, smul_eq_mul, mul_one] at h3
    exact h3.symm
  have hxρ : x = ρ a :=
    calc x = ρ (b * a) * x := by rw [hba, map_one, one_mul]
      _ = ρ a := by rw [map_mul, mul_comm (ρ b), mul_assoc, ← h1, mul_one]
  refine ⟨fun c d hcd => ?_, fun r => ⟨e r * a, ?_⟩⟩
  · have key : ∀ c : B, e (ρ c) = c * b := fun c => by
      rw [← mul_one (ρ c), ← hsmul, LinearEquiv.map_smul, smul_eq_mul]
    have := congrArg e hcd
    rw [key, key] at this
    exact (IsUnit.of_mul_eq_one a hba).mul_left_injective this
  · rw [map_mul, ← hxρ, hρx, e.symm_apply_apply]

end RingHom

end
