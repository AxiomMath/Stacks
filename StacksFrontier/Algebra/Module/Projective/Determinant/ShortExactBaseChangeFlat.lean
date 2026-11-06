module

public import Mathlib.RingTheory.Flat.Equalizer
public import StacksFrontier.Homology.TwoTermComplex.DeterminantLineHomBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flat base change of the determinant of a short exact sequence, and of a quasi-isomorphism

Let `R → A` be a flat map of commutative rings. Two things commute with that base change here.

First, the determinant isomorphism of a short exact sequence. For a surjection `f : M → N` of
finite projective `R`-modules, the sequence `0 → ker f → M → N → 0` gives the isomorphism
`det(ker f) ⊗ det(N) ≅ det(M)` of `TwoTermComplex.kernelDeterminantEquiv`. Because `A` is flat
over `R`, the base-changed sequence is again short exact and its left term is the base change of
`ker f`, so the same construction over `A` applies to `A ⊗_R f`; the comparisons of
`ProjectiveDeterminant.baseChangeEquiv` conjugate the one over `R` into the one over `A`.

Second, the determinant equivalence of a degreewise-surjective quasi-isomorphism `a : K → L` of
two-term complexes of finite projective modules. Its base change `A ⊗_R a` is again a
degreewise-surjective quasi-isomorphism, and the comparisons of
`TwoTermComplex.determinantLineBaseChange` conjugate the equivalence
`det(K) ≅ det(L)` attached to `a` into the one attached to `A ⊗_R a`.

## Main definitions

* `ProjectiveDeterminant.kerBaseChangeEquiv`: **the kernel commutes with flat base change**,
  `A ⊗_R ker f ≅ ker (A ⊗_R f)`.
* `ProjectiveDeterminant.kerDeterminantBaseChangeEquiv`: the resulting comparison
  `A ⊗_R det(ker f) ≅ det(ker (A ⊗_R f))` of determinant lines.

## Main results

* `ProjectiveDeterminant.coe_kernelDeterminantEquiv_tmul`: the determinant isomorphism of the
  short exact sequence of a surjection, read inside the exterior algebra.
* `ProjectiveDeterminant.baseChangeEquiv_kernelDeterminantEquiv_tmul`: **the
  short-exact-sequence determinant isomorphism commutes with flat base change**, on a pure
  tensor.
* `ProjectiveDeterminant.kernelDeterminantEquiv_comp_baseChangeComparison`: the same statement as
  an equality of `A`-linear maps out of `A ⊗_R (det(ker f) ⊗_R det(N))`.
* `TwoTermComplex.Hom.isQuasiIso_of_bijective_kernelDifferential`: a degreewise-surjective
  morphism whose kernel complex is acyclic is a quasi-isomorphism.
* `TwoTermComplex.Hom.isQuasiIso_baseChange`: **a degreewise-surjective quasi-isomorphism stays
  one after flat base change.**
* `TwoTermComplex.delta_kernelDifferential_kerDeterminantBaseChangeEquiv`: the canonical
  element of the determinant line of the kernel complex is compatible with flat base change.
* `TwoTermComplex.determinantEquivOfSurjectiveQuasiIso_baseChange_comp`: **the canonical
  determinant equivalence of a degreewise-surjective quasi-isomorphism is compatible with flat
  base change.**

## Implementation notes

Flatness enters in exactly one place: the canonical map `A ⊗_R ker f → ker (A ⊗_R f)` is an
isomorphism, which is Mathlib's `LinearMap.tensorKerEquiv` read at the base-change spelling
(`LinearMap.baseChange A f` is by definition `TensorProduct.AlgebraTensorModule.lTensor A A f`).
Everything else is flatness-free: the comparison `ProjectiveDeterminant.baseChangeEquiv` of
determinant lines holds for an arbitrary `R`-algebra `A`, and the finiteness and projectivity of
`ker (A ⊗_R f)` over `A` come from `TwoTermComplex.kernel_finite` and
`TwoTermComplex.kernel_projective` applied to the surjection `A ⊗_R f`; they are carried as
instance hypotheses, exactly as `TwoTermComplex.kernelDeterminantEquiv` carries them over `R`.

Both sides of the short-exact-sequence statement are computed inside `⋀_A(A ⊗_R M)` and compared
with `Subtype.ext`. The two ingredients are the defining property of the determinant isomorphism
of a short exact sequence — `det(ker f) ⊗ det(N) → det(M)` sends `x ⊗ y` to the wedge of the
image of `x` with any lift of `y`, which is
`ProjectiveDeterminant.coe_kernelDeterminantEquiv_tmul` — and the naturality of the
exterior-algebra base-change comparison in the module,
`ProjectiveDeterminant.map_baseChange_exteriorAlgebraBaseChange_symm_tmul`. Applied to the
inclusion `ker f → M` the latter computes the first factor of the wedge over `A`, and to `f` itself
it exhibits `(exteriorAlgebraBaseChange R A M).symm (1 ⊗ₜ y'')` as a lift of the chosen element
of `det(A ⊗_R N)`; the wedge of the two is then a single pure tensor because
`(exteriorAlgebraBaseChange R A M).symm` is an algebra map.

The statement for a quasi-isomorphism needs no new construction, because
`TwoTermComplex.SurjectiveQuasiIsoDeterminantData` records that the equivalence is the unique one
satisfying a single determinant diagram. What is verified is therefore that the conjugate of the
equivalence over `R` satisfies that diagram over `A`; the three ingredients are the
short-exact-sequence statement above in the two degrees,
`TwoTermComplex.delta_kernelDifferential_kerDeterminantBaseChangeEquiv` for the canonical element
of the kernel complex, and `TwoTermComplex.determinantLineBaseChange_tmul_apply` for the
evaluation of a base-changed homomorphism. Each side of the diagram is additive in its three
arguments and the three comparison maps are surjective, so the verification reduces to pure
tensors.

Quasi-isomorphy of the base change is proved through the kernel complex rather than directly: the
cokernel occurring in `TwoTermComplex.Hom.hZero` is not obviously compatible with base change,
whereas the kernel is, so `TwoTermComplex.Hom.isQuasiIso_of_bijective_kernelDifferential` moves
the question to the bijectivity of the kernel differential — the converse of the field
`kernelAcyclic` of `TwoTermComplex.determinantEquivOfSurjectiveQuasiIso`, proved here by hand in
the two degrees.

`TwoTermComplex.Hom.baseChange`, of
`StacksFrontier.Homology.TwoTermComplex.LineBaseChange`, is reducible so that instance synthesis
sees through `(a.baseChange A).neg` to `LinearMap.baseChange A a.neg`; otherwise the finiteness
instances for the kernel of a base-changed component would have to be carried in both
spellings.

## References

* [Stacks Project, Tag 0FJI](https://stacks.math.columbia.edu/tag/0FJI)
* [Stacks Project, Tag 0FJJ](https://stacks.math.columbia.edu/tag/0FJJ)
* [Stacks Project, Tag 0FJX](https://stacks.math.columbia.edu/tag/0FJX)
-/
@[expose] public noncomputable section

open scoped TensorProduct

namespace ProjectiveDeterminant

/-! ### The kernel of a base-changed map -/

section Kernel

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A] [Module.Flat R A]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]

/-- **The kernel of a linear map commutes with flat base change.** For `f : M → N` a map of
`R`-modules and `A` a flat `R`-algebra, the canonical `A`-linear map
`A ⊗_R ker f → ker (A ⊗_R f)` is an isomorphism.

This is `LinearMap.tensorKerEquiv` read at the base-change spelling: `LinearMap.baseChange A f`
is `TensorProduct.AlgebraTensorModule.lTensor A A f` by definition. -/
@[ega "0 20.6.21" "partial", ega "IV 11.2.3" "special case", sga "3 VIB 11.0" "special case"]
def kerBaseChangeEquiv (f : M →ₗ[R] N) :
    A ⊗[R] (LinearMap.ker f) ≃ₗ[A] LinearMap.ker (LinearMap.baseChange A f) :=
  LinearMap.tensorKerEquiv A A f

/-- `ProjectiveDeterminant.kerBaseChangeEquiv` sends a pure tensor to a pure tensor. -/
theorem coe_kerBaseChangeEquiv_tmul (f : M →ₗ[R] N) (a : A) (x : LinearMap.ker f) :
    ((kerBaseChangeEquiv (A := A) f (a ⊗ₜ[R] x) :
      LinearMap.ker (LinearMap.baseChange A f)) : A ⊗[R] M) = a ⊗ₜ[R] (x : M) :=
  rfl

/-- The kernel comparison is compatible with the inclusions of the kernels: composing it with
the inclusion of `ker (A ⊗_R f)` gives the base change of the inclusion of `ker f`. -/
theorem subtype_comp_kerBaseChangeEquiv (f : M →ₗ[R] N) :
    (LinearMap.ker (LinearMap.baseChange A f)).subtype ∘ₗ
        (kerBaseChangeEquiv (A := A) f).toLinearMap =
      LinearMap.baseChange A (LinearMap.ker f).subtype := by
  ext x
  rfl

end Kernel

/-! ### The determinant isomorphism of a surjection inside the exterior algebra -/

/-- **The determinant isomorphism of the short exact sequence of a surjection, computed inside
the exterior algebra.** The image of `x ⊗ y` is the wedge of the image of `x` under the inclusion
`ker f → M` with any element `z` of `⋀_R(M)` lifting `y`.

This is the defining property of
`ProjectiveDeterminant.determinantTensorDeterminantEquiv_of_exact` transported to the spelling
`TwoTermComplex.kernelDeterminantEquiv` uses. -/
theorem coe_kernelDeterminantEquiv_tmul {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f)
    [Module.Finite R (LinearMap.ker f)] [Module.Projective R (LinearMap.ker f)]
    (x : module (R := R) (M := LinearMap.ker f)) (y : module (R := R) (M := N))
    (z : ExteriorAlgebra R M) (hz : ExteriorAlgebra.map f z = (y : ExteriorAlgebra R N)) :
    ((TwoTermComplex.kernelDeterminantEquiv f hf (x ⊗ₜ[R] y) :
        module (R := R) (M := M)) : ExteriorAlgebra R M) =
      ExteriorAlgebra.map (LinearMap.ker f).subtype
        (x : ExteriorAlgebra R (LinearMap.ker f)) * z := by
  have hγ := (determinantTensorDeterminantEquiv_of_exact
    (LinearMap.ker f).subtype f (LinearMap.ker f).injective_subtype
      f.exact_subtype_ker_map hf).property
      (TwoTermComplex.determinantAnnihilatorEquiv x)
      (TwoTermComplex.determinantAnnihilatorEquiv y) z hz
  simpa [TwoTermComplex.kernelDeterminantEquiv,
    TwoTermComplex.determinantAnnihilatorEquiv] using hγ

/-! ### Flat base change of the determinant isomorphism -/

section BaseChange

universe u v

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type v} [AddCommGroup N] [Module R N]
variable (f : M →ₗ[R] N)
variable [Module.Finite R (LinearMap.ker f)] [Module.Projective R (LinearMap.ker f)]
variable [Module.Finite A (LinearMap.ker (LinearMap.baseChange A f))]
variable [Module.Projective A (LinearMap.ker (LinearMap.baseChange A f))]

/-- **The determinant line of the kernel commutes with flat base change**,
`A ⊗_R det(ker f) ≅ det(ker (A ⊗_R f))`. It is the comparison
`ProjectiveDeterminant.baseChangeEquiv` of determinant lines followed by the determinant of the
kernel comparison `ProjectiveDeterminant.kerBaseChangeEquiv`. -/
def kerDeterminantBaseChangeEquiv :
    A ⊗[R] module (R := R) (M := LinearMap.ker f) ≃ₗ[A]
      module (R := A) (M := LinearMap.ker (LinearMap.baseChange A f)) :=
  (baseChangeEquiv (R := R) (A := A) (M := LinearMap.ker f)).trans
    (mapEquiv (kerBaseChangeEquiv (A := A) f))

/-- `ProjectiveDeterminant.kerDeterminantBaseChangeEquiv` computed on a pure tensor, inside the
exterior algebra. -/
theorem coe_kerDeterminantBaseChangeEquiv_tmul (a : A)
    (x : module (R := R) (M := LinearMap.ker f)) :
    ((kerDeterminantBaseChangeEquiv (A := A) f (a ⊗ₜ[R] x) :
        module (R := A) (M := LinearMap.ker (LinearMap.baseChange A f))) :
        ExteriorAlgebra A (LinearMap.ker (LinearMap.baseChange A f))) =
      ExteriorAlgebra.map (kerBaseChangeEquiv (A := A) f).toLinearMap
        ((exteriorAlgebraBaseChange R A (LinearMap.ker f)).symm
          (a ⊗ₜ[R] (x : ExteriorAlgebra R (LinearMap.ker f)))) :=
  rfl

/-- The wedge factor coming from the kernel: the inclusion of `ker (A ⊗_R f)` carries the
base change of `x` to the base change of the inclusion of `x`. -/
theorem map_subtype_coe_kerDeterminantBaseChangeEquiv_tmul (a : A)
    (x : module (R := R) (M := LinearMap.ker f)) :
    ExteriorAlgebra.map (LinearMap.ker (LinearMap.baseChange A f)).subtype
        ((kerDeterminantBaseChangeEquiv (A := A) f (a ⊗ₜ[R] x) :
          module (R := A) (M := LinearMap.ker (LinearMap.baseChange A f))) :
          ExteriorAlgebra A (LinearMap.ker (LinearMap.baseChange A f))) =
      (exteriorAlgebraBaseChange R A M).symm
        (a ⊗ₜ[R] ExteriorAlgebra.map (LinearMap.ker f).subtype
          (x : ExteriorAlgebra R (LinearMap.ker f))) := by
  rw [coe_kerDeterminantBaseChangeEquiv_tmul, ← AlgHom.comp_apply,
    ExteriorAlgebra.map_comp_map, subtype_comp_kerBaseChangeEquiv,
    map_baseChange_exteriorAlgebraBaseChange_symm_tmul A (LinearMap.ker f).subtype]

variable [Module.Finite R M] [Module.Projective R M]
variable [Module.Finite R N] [Module.Projective R N]

/-- **The short-exact-sequence determinant isomorphism commutes with flat base change**, read on
a pure tensor.

The comparisons of `ProjectiveDeterminant.baseChangeEquiv` and
`ProjectiveDeterminant.kerDeterminantBaseChangeEquiv` carry the isomorphism
`det(ker f) ⊗_R det(N) ≅ det(M)` of the short exact sequence `0 → ker f → M → N → 0` to the
isomorphism `det(ker (A ⊗_R f)) ⊗_A det(A ⊗_R N) ≅ det(A ⊗_R M)` of its base change. -/
theorem baseChangeEquiv_kernelDeterminantEquiv_tmul (hf : Function.Surjective f) (a : A)
    (x : module (R := R) (M := LinearMap.ker f)) (y : module (R := R) (M := N)) :
    baseChangeEquiv (R := R) (A := A) (M := M)
        (a ⊗ₜ[R] TwoTermComplex.kernelDeterminantEquiv f hf (x ⊗ₜ[R] y)) =
      TwoTermComplex.kernelDeterminantEquiv (LinearMap.baseChange A f)
          (LinearMap.baseChange_surjective A hf)
        (kerDeterminantBaseChangeEquiv (A := A) f (a ⊗ₜ[R] x) ⊗ₜ[A]
          baseChangeEquiv (R := R) (A := A) (M := N) (1 ⊗ₜ[R] y)) := by
  obtain ⟨z, hz⟩ := (ExteriorAlgebra.map_surjective_iff.mpr hf) (y : ExteriorAlgebra R N)
  have hlift : ExteriorAlgebra.map (LinearMap.baseChange A f)
      ((exteriorAlgebraBaseChange R A M).symm ((1 : A) ⊗ₜ[R] z)) =
      ((baseChangeEquiv (R := R) (A := A) (M := N) (1 ⊗ₜ[R] y) :
        module (R := A) (M := A ⊗[R] N)) : ExteriorAlgebra A (A ⊗[R] N)) := by
    rw [map_baseChange_exteriorAlgebraBaseChange_symm_tmul A f, hz, coe_baseChangeEquiv_tmul]
  apply Subtype.ext
  rw [coe_baseChangeEquiv_tmul, coe_kernelDeterminantEquiv_tmul f hf x y z hz,
    coe_kernelDeterminantEquiv_tmul (LinearMap.baseChange A f)
      (LinearMap.baseChange_surjective A hf) _ _ _ hlift,
    map_subtype_coe_kerDeterminantBaseChangeEquiv_tmul, ← map_mul,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one]

/-- **The short-exact-sequence determinant isomorphism commutes with flat base change**, as an
equality of `A`-linear maps.

The square whose horizontal maps are the determinant isomorphisms of
`0 → ker f → M → N → 0` and of its base change, and whose vertical maps are the base-change
comparisons — `TensorProduct.AlgebraTensorModule.distribBaseChange` to distribute `A ⊗_R` over
the tensor product, then `ProjectiveDeterminant.kerDeterminantBaseChangeEquiv` and
`ProjectiveDeterminant.baseChangeEquiv` on the two factors — commutes. -/
theorem kernelDeterminantEquiv_comp_baseChangeComparison (hf : Function.Surjective f) :
    (TwoTermComplex.kernelDeterminantEquiv (LinearMap.baseChange A f)
          (LinearMap.baseChange_surjective A hf)).toLinearMap ∘ₗ
        ((TensorProduct.AlgebraTensorModule.distribBaseChange R A
              (module (R := R) (M := LinearMap.ker f)) (module (R := R) (M := N))).trans
            (TensorProduct.congr (kerDeterminantBaseChangeEquiv (A := A) f)
              (baseChangeEquiv (R := R) (A := A) (M := N)))).toLinearMap =
      (baseChangeEquiv (R := R) (A := A) (M := M)).toLinearMap ∘ₗ
        LinearMap.baseChange A (TwoTermComplex.kernelDeterminantEquiv f hf).toLinearMap := by
  refine LinearMap.ext fun t => ?_
  induction t using TensorProduct.induction_on with
  | zero => set_option synthInstance.maxHeartbeats 100000 in simp
  | tmul a w =>
      induction w using TensorProduct.induction_on with
      | zero => set_option synthInstance.maxHeartbeats 100000 in simp
      | tmul x y =>
          simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
            TensorProduct.AlgebraTensorModule.distribBaseChange_tmul, TensorProduct.congr_tmul,
            LinearMap.baseChange_tmul] using
            (baseChangeEquiv_kernelDeterminantEquiv_tmul f hf a x y).symm
      | add x y hx hy =>
          simp only [TensorProduct.tmul_add, map_add] at hx hy ⊢
          rw [hx, hy]
  | add w w' hw hw' =>
      simp only [map_add] at hw hw' ⊢
      rw [hw, hw']

/-! ### The two-scalar form of the comparison -/

/-- `ProjectiveDeterminant.baseChangeEquiv_kernelDeterminantEquiv_tmul` with a scalar on each
factor: the two scalars multiply, because every map in sight is `A`-linear. This is the form the
verification of the determinant diagram over `A` consumes, where the scalars arrive separately
from the two tensor factors. -/
theorem baseChangeEquiv_kernelDeterminantEquiv_tmul_tmul (hf : Function.Surjective f) (c b : A)
    (x : module (R := R) (M := LinearMap.ker f)) (y : module (R := R) (M := N)) :
    baseChangeEquiv (R := R) (A := A) (M := M)
        ((c * b) ⊗ₜ[R] TwoTermComplex.kernelDeterminantEquiv f hf (x ⊗ₜ[R] y)) =
      TwoTermComplex.kernelDeterminantEquiv (LinearMap.baseChange A f)
          (LinearMap.baseChange_surjective A hf)
        (kerDeterminantBaseChangeEquiv (A := A) f (c ⊗ₜ[R] x) ⊗ₜ[A]
          baseChangeEquiv (R := R) (A := A) (M := N) (b ⊗ₜ[R] y)) := by
  rw [TensorProduct.tmul_eq_smul_one_tmul b y, map_smul, TensorProduct.tmul_smul, map_smul,
    ← baseChangeEquiv_kernelDeterminantEquiv_tmul f hf c x y, ← map_smul,
    TensorProduct.smul_tmul', smul_eq_mul, mul_comm b c]

end BaseChange

end ProjectiveDeterminant

namespace TwoTermComplex

/-! ### Base change of a morphism of two-term complexes -/

section Morphism

variable {R : Type*} [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
variable {K₁ K₀ L₁ L₀ : Type*}
variable [AddCommGroup K₁] [Module R K₁] [AddCommGroup K₀] [Module R K₀]
variable [AddCommGroup L₁] [Module R L₁] [AddCommGroup L₀] [Module R L₀]
variable {K : K₁ →ₗ[R] K₀} {L : L₁ →ₗ[R] L₀}

/-- The degree `-1` component of a base-changed morphism. -/
theorem Hom.baseChange_neg (a : Hom K L) :
    (a.baseChange A).neg = LinearMap.baseChange A a.neg :=
  rfl

/-- The degree `0` component of a base-changed morphism. -/
theorem Hom.baseChange_zero (a : Hom K L) :
    (a.baseChange A).zero = LinearMap.baseChange A a.zero :=
  rfl

/-- **The differential of the kernel complex commutes with flat base change.** The kernel
comparisons of `ProjectiveDeterminant.kerBaseChangeEquiv` in the two degrees carry the base
change of the kernel differential of `a` to the kernel differential of `A ⊗_R a`. -/
theorem Hom.kernelDifferential_baseChange_comp [Module.Flat R A] (a : Hom K L) :
    (a.baseChange A).kernelDifferential ∘ₗ
        (ProjectiveDeterminant.kerBaseChangeEquiv (A := A) a.neg).toLinearMap =
      (ProjectiveDeterminant.kerBaseChangeEquiv (A := A) a.zero).toLinearMap ∘ₗ
        LinearMap.baseChange A a.kernelDifferential := by
  ext x
  rfl

/-- **The kernel complex of a base-changed morphism is acyclic when the kernel complex is.**
Being conjugate to the base change of a bijective map, by
`TwoTermComplex.Hom.kernelDifferential_baseChange_comp`, the base-changed kernel differential is
bijective. -/
theorem Hom.bijective_kernelDifferential_baseChange [Module.Flat R A] (a : Hom K L)
    (hd : Function.Bijective a.kernelDifferential) :
    Function.Bijective (a.baseChange A).kernelDifferential := by
  have hbc : Function.Bijective (LinearMap.baseChange A a.kernelDifferential) := by
    have h : LinearMap.baseChange A a.kernelDifferential =
        (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A A)
          (LinearEquiv.ofBijective a.kernelDifferential hd)).toLinearMap := rfl
    rw [h]
    exact (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A A)
      (LinearEquiv.ofBijective a.kernelDifferential hd)).bijective
  have hcomp : Function.Bijective
      ((a.baseChange A).kernelDifferential ∘ₗ
        (ProjectiveDeterminant.kerBaseChangeEquiv (A := A) a.neg).toLinearMap) := by
    rw [Hom.kernelDifferential_baseChange_comp]
    exact (ProjectiveDeterminant.kerBaseChangeEquiv (A := A) a.zero).bijective.comp hbc
  have hker := (ProjectiveDeterminant.kerBaseChangeEquiv (A := A) a.neg).bijective
  refine ⟨fun p q hpq => ?_, fun p => ?_⟩
  · obtain ⟨p', rfl⟩ := hker.2 p
    obtain ⟨q', rfl⟩ := hker.2 q
    exact congrArg _ (hcomp.1 hpq)
  · obtain ⟨p', hp'⟩ := hcomp.2 p
    exact ⟨_, hp'⟩

end Morphism

/-! ### An acyclic kernel complex detects quasi-isomorphy -/

section Acyclic

variable {R : Type*} [CommRing R]
variable {K₁ K₀ L₁ L₀ : Type*}
variable [AddCommGroup K₁] [Module R K₁] [AddCommGroup K₀] [Module R K₀]
variable [AddCommGroup L₁] [Module R L₁] [AddCommGroup L₀] [Module R L₀]
variable {K : K₁ →ₗ[R] K₀} {L : L₁ →ₗ[R] L₀}

/-- **A degreewise-surjective morphism with acyclic kernel complex is a quasi-isomorphism.**

This is the converse of the field `kernelAcyclic` of
`TwoTermComplex.determinantEquivOfSurjectiveQuasiIso`, and it is what makes quasi-isomorphy
visible to base change: flat base change preserves bijectivity of the kernel differential
directly, whereas the definition of a quasi-isomorphism refers to a cokernel. Both directions
are the long exact sequence of the short exact sequence of complexes
`0 → ker a → K → L → 0`, read off by hand in the two degrees. -/
theorem Hom.isQuasiIso_of_bijective_kernelDifferential (a : Hom K L)
    (ha : a.IsDegreewiseSurjective) (hd : Function.Bijective a.kernelDifferential) :
    a.IsQuasiIso := by
  have hcomm : ∀ w, a.zero (K w) = L (a.neg w) := fun w => LinearMap.congr_fun a.comm w
  constructor
  · constructor
    · intro x y hxy
      have hsub : (x : K₁) - (y : K₁) ∈ LinearMap.ker a.neg := by
        rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
        exact congrArg Subtype.val hxy
      have hzero : a.kernelDifferential ⟨(x : K₁) - (y : K₁), hsub⟩ = 0 := by
        apply Subtype.ext
        show K ((x : K₁) - (y : K₁)) = 0
        rw [map_sub, x.property, y.property, sub_self]
      have hx := congrArg Subtype.val
        (hd.1 (hzero.trans (map_zero a.kernelDifferential).symm))
      exact Subtype.ext (sub_eq_zero.mp hx)
    · intro z
      obtain ⟨w, hw⟩ := ha.1 (z : L₁)
      have hKw : K w ∈ LinearMap.ker a.zero := by
        rw [LinearMap.mem_ker, hcomm, hw, z.property]
      obtain ⟨v, hv⟩ := hd.2 ⟨K w, hKw⟩
      refine ⟨⟨w - (v : K₁), ?_⟩, ?_⟩
      · rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
        exact (congrArg Subtype.val hv).symm
      · apply Subtype.ext
        show a.neg (w - (v : K₁)) = (z : L₁)
        rw [map_sub, v.property, hw, sub_zero]
  · constructor
    · intro s t hst
      induction s using Submodule.Quotient.induction_on with | _ s =>
      induction t using Submodule.Quotient.induction_on with | _ t =>
      change Submodule.Quotient.mk (a.zero s) = Submodule.Quotient.mk (a.zero t) at hst
      rw [Submodule.Quotient.eq] at hst
      obtain ⟨u, hu⟩ := hst
      obtain ⟨p, hp⟩ := ha.1 u
      have hker : s - t - K p ∈ LinearMap.ker a.zero := by
        rw [LinearMap.mem_ker, map_sub, map_sub, hcomm, hp, hu]
        abel
      obtain ⟨q, hq⟩ := hd.2 ⟨s - t - K p, hker⟩
      have hqv : K (q : K₁) = s - t - K p := congrArg Subtype.val hq
      rw [Submodule.Quotient.eq]
      refine ⟨(q : K₁) + p, ?_⟩
      rw [map_add, hqv]
      abel
    · intro s
      induction s using Submodule.Quotient.induction_on with | _ s =>
      obtain ⟨t, ht⟩ := ha.2 s
      exact ⟨Submodule.Quotient.mk t, by
        show Submodule.Quotient.mk (a.zero t) = Submodule.Quotient.mk s
        rw [ht]⟩

end Acyclic

/-! ### Base change of a degreewise-surjective quasi-isomorphism -/

section QuasiIsoBaseChange

variable {R : Type*} [CommRing R] (A : Type*) [CommRing A] [Algebra R A] [Module.Flat R A]
variable {K₁ K₀ L₁ L₀ : Type*}
variable [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁] [Module.Projective R K₁]
variable [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀] [Module.Projective R K₀]
variable [AddCommGroup L₁] [Module R L₁] [Module.Finite R L₁] [Module.Projective R L₁]
variable [AddCommGroup L₀] [Module R L₀] [Module.Finite R L₀] [Module.Projective R L₀]
variable {K : K₁ →ₗ[R] K₀} {L : L₁ →ₗ[R] L₀}

/-- **A degreewise-surjective quasi-isomorphism stays one after flat base change.** Its kernel
complex is acyclic (`TwoTermComplex.determinantEquivOfSurjectiveQuasiIso`), flat base change
keeps it acyclic, and an acyclic kernel complex over a degreewise surjection is quasi-isomorphy
(`TwoTermComplex.Hom.isQuasiIso_of_bijective_kernelDifferential`). -/
theorem Hom.isQuasiIso_baseChange (a : Hom K L) (ha : a.IsDegreewiseSurjective)
    (hqa : a.IsQuasiIso) : (a.baseChange A).IsQuasiIso := by
  have : Module.Finite R (LinearMap.ker a.neg) := kernel_finite a.neg ha.1
  have : Module.Projective R (LinearMap.ker a.neg) := kernel_projective a.neg ha.1
  have : Module.Finite R (LinearMap.ker a.zero) := kernel_finite a.zero ha.2
  have : Module.Projective R (LinearMap.ker a.zero) := kernel_projective a.zero ha.2
  exact (a.baseChange A).isQuasiIso_of_bijective_kernelDifferential
    (ha.baseChange (A := A))
    (a.bijective_kernelDifferential_baseChange A
      (determinantEquivOfSurjectiveQuasiIso K L a ha hqa).kernelAcyclic)

end QuasiIsoBaseChange

/-! ### The canonical element of the kernel complex under base change -/

section DeltaBaseChange

universe u

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] [Module.Flat R A]
variable {K₁ K₀ L₁ L₀ : Type u}
variable [AddCommGroup K₁] [Module R K₁] [AddCommGroup K₀] [Module R K₀]
variable [AddCommGroup L₁] [Module R L₁] [AddCommGroup L₀] [Module R L₀]
variable {K : K₁ →ₗ[R] K₀} {L : L₁ →ₗ[R] L₀}

/-- **The canonical element of the determinant line of the kernel complex is compatible with
flat base change.** The comparisons `A ⊗_R det(ker a_i) ≅ det(ker (A ⊗_R a_i))` of
`ProjectiveDeterminant.kerDeterminantBaseChangeEquiv` conjugate `δ` of the kernel complex of `a`
into `δ` of the kernel complex of `A ⊗_R a`.

Both sides are read inside `⋀_A(ker (A ⊗_R a.zero))`: `δ` is `ProjectiveDeterminant.map`, whose
value there is `ExteriorAlgebra.map` of the differential, so the statement is
`TwoTermComplex.Hom.kernelDifferential_baseChange_comp` together with the naturality
`ProjectiveDeterminant.map_baseChange_exteriorAlgebraBaseChange_symm_tmul` of the
exterior-algebra comparison. -/
theorem delta_kernelDifferential_kerDeterminantBaseChangeEquiv (a : Hom K L)
    [Module.Finite R (LinearMap.ker a.neg)] [Module.Projective R (LinearMap.ker a.neg)]
    [Module.Finite R (LinearMap.ker a.zero)] [Module.Projective R (LinearMap.ker a.zero)]
    [Module.Finite A (LinearMap.ker (LinearMap.baseChange A a.neg))]
    [Module.Projective A (LinearMap.ker (LinearMap.baseChange A a.neg))]
    [Module.Finite A (LinearMap.ker (LinearMap.baseChange A a.zero))]
    [Module.Projective A (LinearMap.ker (LinearMap.baseChange A a.zero))]
    (hr : IsRankZero a.kernelDifferential)
    (hrz : IsRankZero (a.baseChange A).kernelDifferential)
    (c : A) (x : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg)) :
    delta (a.baseChange A).kernelDifferential hrz
        (ProjectiveDeterminant.kerDeterminantBaseChangeEquiv (A := A) a.neg (c ⊗ₜ[R] x)) =
      ProjectiveDeterminant.kerDeterminantBaseChangeEquiv (A := A) a.zero
        (c ⊗ₜ[R] delta a.kernelDifferential hr x) := by
  apply Subtype.ext
  have hL : ((delta (a.baseChange A).kernelDifferential hrz
        (ProjectiveDeterminant.kerDeterminantBaseChangeEquiv (A := A) a.neg (c ⊗ₜ[R] x)) :
        ProjectiveDeterminant.module (R := A)
          (M := LinearMap.ker (a.baseChange A).zero)) :
        ExteriorAlgebra A (LinearMap.ker (a.baseChange A).zero)) =
      ExteriorAlgebra.map (a.baseChange A).kernelDifferential
        ((ProjectiveDeterminant.kerDeterminantBaseChangeEquiv (A := A) a.neg (c ⊗ₜ[R] x) :
          ProjectiveDeterminant.module (R := A)
            (M := LinearMap.ker (a.baseChange A).neg)) :
          ExteriorAlgebra A (LinearMap.ker (a.baseChange A).neg)) := rfl
  have hR : ((delta a.kernelDifferential hr x :
        ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.zero)) :
        ExteriorAlgebra R (LinearMap.ker a.zero)) =
      ExteriorAlgebra.map a.kernelDifferential
        ((x : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg)) :
          ExteriorAlgebra R (LinearMap.ker a.neg)) := rfl
  rw [hL, ProjectiveDeterminant.coe_kerDeterminantBaseChangeEquiv_tmul,
    ProjectiveDeterminant.coe_kerDeterminantBaseChangeEquiv_tmul, hR,
    ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, Hom.kernelDifferential_baseChange_comp,
    ← ExteriorAlgebra.map_comp_map, AlgHom.comp_apply,
    ProjectiveDeterminant.map_baseChange_exteriorAlgebraBaseChange_symm_tmul A a.kernelDifferential]

end DeltaBaseChange

/-! ### The comparison of determinant lines on a pure tensor -/

section LineApply

universe u

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] [Module.Flat R A]
variable {K₁ K₀ L₁ L₀ : Type u}
variable [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁] [Module.Projective R K₁]
variable [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀] [Module.Projective R K₀]
variable [AddCommGroup L₁] [Module R L₁] [Module.Finite R L₁] [Module.Projective R L₁]
variable [AddCommGroup L₀] [Module R L₀] [Module.Finite R L₀] [Module.Projective R L₀]

/-- **`TwoTermComplex.determinantLineBaseChange` evaluated on pure tensors.** The comparison
sends `c ⊗ φ` to the base change of `φ` scaled by `c`, conjugated by
`ProjectiveDeterminant.baseChangeEquiv`; so on the pure tensor `b ⊗ w` of the source determinant
line the two scalars multiply. -/
theorem determinantLineBaseChange_tmul_apply (f : K₁ →ₗ[R] K₀) (c b : A)
    (φ : determinantLine f) (w : ProjectiveDeterminant.module (R := R) (M := K₁)) :
    determinantLineBaseChange A f (c ⊗ₜ[R] φ)
        (ProjectiveDeterminant.baseChangeEquiv (R := R) (A := A) (M := K₁) (b ⊗ₜ[R] w)) =
      ProjectiveDeterminant.baseChangeEquiv (R := R) (A := A) (M := K₀) ((c * b) ⊗ₜ[R] φ w) := by
  rw [TensorProduct.tmul_eq_smul_one_tmul c φ, map_smul, LinearMap.smul_apply,
    determinantLineBaseChange_one_tmul]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    LinearMap.baseChange_tmul]
  rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul]

/-- Conjugating an equivalence of determinant lines by
`TwoTermComplex.determinantLineBaseChange`, read on a pure tensor: the conjugate carries the
image of `c ⊗ φ` to the image of `c ⊗ e φ`. -/
theorem conj_determinantLineBaseChange_tmul (f : K₁ →ₗ[R] K₀) (g : L₁ →ₗ[R] L₀)
    (e : determinantLine f ≃ₗ[R] determinantLine g) (c : A) (φ : determinantLine f) :
    ((determinantLineBaseChange A f).symm ≪≫ₗ
        TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A A) e ≪≫ₗ
        determinantLineBaseChange A g) (determinantLineBaseChange A f (c ⊗ₜ[R] φ)) =
      determinantLineBaseChange A g (c ⊗ₜ[R] e φ) := by
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rfl

end LineApply

/-! ### The determinant diagram over the base change -/

section Diagram

universe u

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] [Module.Flat R A]
variable {K₁ K₀ L₁ L₀ : Type u}
variable [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁] [Module.Projective R K₁]
variable [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀] [Module.Projective R K₀]
variable [AddCommGroup L₁] [Module R L₁] [Module.Finite R L₁] [Module.Projective R L₁]
variable [AddCommGroup L₀] [Module R L₀] [Module.Finite R L₀] [Module.Projective R L₀]
variable {K : K₁ →ₗ[R] K₀} {L : L₁ →ₗ[R] L₀}
variable (a : Hom K L) (ha : a.IsDegreewiseSurjective)
variable [Module.Finite R (LinearMap.ker a.neg)] [Module.Projective R (LinearMap.ker a.neg)]
variable [Module.Finite R (LinearMap.ker a.zero)] [Module.Projective R (LinearMap.ker a.zero)]
variable [Module.Finite A (LinearMap.ker (LinearMap.baseChange A a.neg))]
variable [Module.Projective A (LinearMap.ker (LinearMap.baseChange A a.neg))]
variable [Module.Finite A (LinearMap.ker (LinearMap.baseChange A a.zero))]
variable [Module.Projective A (LinearMap.ker (LinearMap.baseChange A a.zero))]

/-- **The determinant diagram of `A ⊗_R a`, verified on pure tensors.** An equivalence `e` of the
determinant lines over `R` satisfying the defining diagram of
`TwoTermComplex.SurjectiveQuasiIsoDeterminantData` has a conjugate over `A` satisfying the
corresponding diagram for `A ⊗_R a`, on the images of pure tensors.

The three ingredients are
`TwoTermComplex.delta_kernelDifferential_kerDeterminantBaseChangeEquiv` for the `δ` of the
kernel complex, `TwoTermComplex.determinantLineBaseChange_tmul_apply` for the two evaluations of
a base-changed homomorphism, and
`ProjectiveDeterminant.baseChangeEquiv_kernelDeterminantEquiv_tmul_tmul` — the short-exact-sequence
determinant isomorphism under base change — in the two degrees. -/
theorem baseChange_determinantDiagram_tmul (hr : IsRankZero a.kernelDifferential)
    (hrz : IsRankZero (a.baseChange A).kernelDifferential)
    (e : determinantLine K ≃ₗ[R] determinantLine L)
    (hcompat : ∀ (φ : determinantLine K)
      (x : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg))
      (y : ProjectiveDeterminant.module (R := R) (M := L₁)),
      kernelDeterminantEquiv a.zero ha.2 (delta a.kernelDifferential hr x ⊗ₜ[R] e φ y) =
        φ (kernelDeterminantEquiv a.neg ha.1 (x ⊗ₜ[R] y)))
    (cφ c b : A) (φ : determinantLine K)
    (x : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg))
    (y : ProjectiveDeterminant.module (R := R) (M := L₁)) :
    kernelDeterminantEquiv (a.baseChange A).zero
          (ha.baseChange (A := A)).2
        (delta (a.baseChange A).kernelDifferential hrz
            (ProjectiveDeterminant.kerDeterminantBaseChangeEquiv (A := A) a.neg
              (c ⊗ₜ[R] x)) ⊗ₜ[A]
          determinantLineBaseChange A L (cφ ⊗ₜ[R] e φ)
            (ProjectiveDeterminant.baseChangeEquiv (R := R) (A := A) (M := L₁)
              (b ⊗ₜ[R] y))) =
      determinantLineBaseChange A K (cφ ⊗ₜ[R] φ)
        (kernelDeterminantEquiv (a.baseChange A).neg
          (ha.baseChange (A := A)).1
          (ProjectiveDeterminant.kerDeterminantBaseChangeEquiv (A := A) a.neg
              (c ⊗ₜ[R] x) ⊗ₜ[A]
            ProjectiveDeterminant.baseChangeEquiv (R := R) (A := A) (M := L₁)
              (b ⊗ₜ[R] y))) := by
  rw [determinantLineBaseChange_tmul_apply R A L cφ b (e φ) y,
    delta_kernelDifferential_kerDeterminantBaseChangeEquiv R A a hr hrz c x,
    ← ProjectiveDeterminant.baseChangeEquiv_kernelDeterminantEquiv_tmul_tmul a.zero ha.2
      c (cφ * b) (delta a.kernelDifferential hr x) (e φ y),
    ← ProjectiveDeterminant.baseChangeEquiv_kernelDeterminantEquiv_tmul_tmul a.neg ha.1 c b x y,
    determinantLineBaseChange_tmul_apply R A K cφ (c * b) φ
      (kernelDeterminantEquiv a.neg ha.1 (x ⊗ₜ[R] y)),
    hcompat φ x y, mul_left_comm]

/-- The determinant diagram of `A ⊗_R a`, verified on the images of arbitrary tensors. Each side
is additive in each of the three arguments, so this is
`TwoTermComplex.baseChange_determinantDiagram_tmul` and three tensor inductions. -/
theorem baseChange_determinantDiagram_of_tensor (hr : IsRankZero a.kernelDifferential)
    (hrz : IsRankZero (a.baseChange A).kernelDifferential)
    (e : determinantLine K ≃ₗ[R] determinantLine L)
    (hcompat : ∀ (φ : determinantLine K)
      (x : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg))
      (y : ProjectiveDeterminant.module (R := R) (M := L₁)),
      kernelDeterminantEquiv a.zero ha.2 (delta a.kernelDifferential hr x ⊗ₜ[R] e φ y) =
        φ (kernelDeterminantEquiv a.neg ha.1 (x ⊗ₜ[R] y)))
    (tφ : A ⊗[R] determinantLine K)
    (tx : A ⊗[R] ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg))
    (ty : A ⊗[R] ProjectiveDeterminant.module (R := R) (M := L₁)) :
    kernelDeterminantEquiv (a.baseChange A).zero
          (ha.baseChange (A := A)).2
        (delta (a.baseChange A).kernelDifferential hrz
            (ProjectiveDeterminant.kerDeterminantBaseChangeEquiv (A := A) a.neg tx) ⊗ₜ[A]
          ((determinantLineBaseChange A K).symm ≪≫ₗ
            TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A A) e ≪≫ₗ
            determinantLineBaseChange A L) (determinantLineBaseChange A K tφ)
            (ProjectiveDeterminant.baseChangeEquiv (R := R) (A := A) (M := L₁) ty)) =
      determinantLineBaseChange A K tφ
        (kernelDeterminantEquiv (a.baseChange A).neg
          (ha.baseChange (A := A)).1
          (ProjectiveDeterminant.kerDeterminantBaseChangeEquiv (A := A) a.neg tx ⊗ₜ[A]
            ProjectiveDeterminant.baseChangeEquiv (R := R) (A := A) (M := L₁) ty)) := by
  induction tφ using TensorProduct.induction_on with
  | zero => set_option synthInstance.maxHeartbeats 100000 in simp
  | add u v hu hv =>
      simpa only [map_add, LinearMap.add_apply, TensorProduct.tmul_add,
        TensorProduct.add_tmul] using congrArg₂ (· + ·) hu hv
  | tmul cφ φ =>
      induction tx using TensorProduct.induction_on with
      | zero => set_option synthInstance.maxHeartbeats 100000 in simp
      | add u v hu hv =>
          simpa only [map_add, LinearMap.add_apply, TensorProduct.tmul_add,
            TensorProduct.add_tmul] using congrArg₂ (· + ·) hu hv
      | tmul c x =>
          induction ty using TensorProduct.induction_on with
          | zero => set_option synthInstance.maxHeartbeats 100000 in simp only [LinearEquiv.map_zero, LinearMap.map_zero, TensorProduct.tmul_zero]
          | add u v hu hv =>
              simpa only [map_add, LinearMap.add_apply, TensorProduct.tmul_add,
                TensorProduct.add_tmul] using congrArg₂ (· + ·) hu hv
          | tmul b y =>
              rw [conj_determinantLineBaseChange_tmul R A K L e cφ φ]
              exact baseChange_determinantDiagram_tmul R A a ha hr hrz e hcompat cφ c b φ x y

/-- **The determinant diagram of `A ⊗_R a`.** The three comparison maps are surjective, so
`TwoTermComplex.baseChange_determinantDiagram_of_tensor` gives the diagram for all arguments.
This is the hypothesis of the uniqueness field of
`TwoTermComplex.SurjectiveQuasiIsoDeterminantData` for `A ⊗_R a`. -/
theorem baseChange_determinantDiagram (hr : IsRankZero a.kernelDifferential)
    (hrz : IsRankZero (a.baseChange A).kernelDifferential)
    (e : determinantLine K ≃ₗ[R] determinantLine L)
    (hcompat : ∀ (φ : determinantLine K)
      (x : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg))
      (y : ProjectiveDeterminant.module (R := R) (M := L₁)),
      kernelDeterminantEquiv a.zero ha.2 (delta a.kernelDifferential hr x ⊗ₜ[R] e φ y) =
        φ (kernelDeterminantEquiv a.neg ha.1 (x ⊗ₜ[R] y)))
    (φ' : determinantLine (LinearMap.baseChange A K))
    (x' : ProjectiveDeterminant.module (R := A) (M := LinearMap.ker (a.baseChange A).neg))
    (y' : ProjectiveDeterminant.module (R := A) (M := A ⊗[R] L₁)) :
    kernelDeterminantEquiv (a.baseChange A).zero
          (ha.baseChange (A := A)).2
        (delta (a.baseChange A).kernelDifferential hrz x' ⊗ₜ[A]
          ((determinantLineBaseChange A K).symm ≪≫ₗ
            TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A A) e ≪≫ₗ
            determinantLineBaseChange A L) φ' y') =
      φ' (kernelDeterminantEquiv (a.baseChange A).neg
        (ha.baseChange (A := A)).1 (x' ⊗ₜ[A] y')) := by
  obtain ⟨tφ, rfl⟩ := (determinantLineBaseChange A K).surjective φ'
  obtain ⟨tx, rfl⟩ := (ProjectiveDeterminant.kerDeterminantBaseChangeEquiv
    (A := A) a.neg).surjective x'
  obtain ⟨ty, rfl⟩ := (ProjectiveDeterminant.baseChangeEquiv
    (R := R) (A := A) (M := L₁)).surjective y'
  exact baseChange_determinantDiagram_of_tensor R A a ha hr hrz e hcompat tφ tx ty

end Diagram

/-! ### Base change of the canonical determinant equivalence -/

section EquivBaseChange

universe u

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] [Module.Flat R A]
variable {K₁ K₀ L₁ L₀ : Type u}
variable [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁] [Module.Projective R K₁]
variable [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀] [Module.Projective R K₀]
variable [AddCommGroup L₁] [Module R L₁] [Module.Finite R L₁] [Module.Projective R L₁]
variable [AddCommGroup L₀] [Module R L₀] [Module.Finite R L₀] [Module.Projective R L₀]
variable {K : K₁ →ₗ[R] K₀} {L : L₁ →ₗ[R] L₀}

/-- **The canonical determinant equivalence of a degreewise-surjective quasi-isomorphism is
compatible with flat base change.** The comparisons
`A ⊗_R det(K) ≅ det(A ⊗_R K)` of `TwoTermComplex.determinantLineBaseChange` conjugate the
equivalence attached to `a` into the equivalence attached to `A ⊗_R a`.

The equivalence is characterized by its determinant diagram, so there is nothing to construct:
`TwoTermComplex.baseChange_determinantDiagram` shows that the conjugate of the equivalence over
`R` satisfies the diagram over `A`, and the uniqueness field of
`TwoTermComplex.SurjectiveQuasiIsoDeterminantData` identifies it with the equivalence over
`A`. -/
theorem determinantEquivOfSurjectiveQuasiIso_baseChange_comp (a : Hom K L)
    (ha : a.IsDegreewiseSurjective) (hqa : a.IsQuasiIso) :
    letI : Module.Finite R (LinearMap.ker a.neg) := kernel_finite a.neg ha.1
    letI : Module.Projective R (LinearMap.ker a.neg) := kernel_projective a.neg ha.1
    letI : Module.Finite R (LinearMap.ker a.zero) := kernel_finite a.zero ha.2
    letI : Module.Projective R (LinearMap.ker a.zero) := kernel_projective a.zero ha.2
    letI : Module.Finite A (LinearMap.ker (a.baseChange A).neg) :=
      kernel_finite (a.baseChange A).neg (ha.baseChange (A := A)).1
    letI : Module.Projective A (LinearMap.ker (a.baseChange A).neg) :=
      kernel_projective (a.baseChange A).neg (ha.baseChange (A := A)).1
    letI : Module.Finite A (LinearMap.ker (a.baseChange A).zero) :=
      kernel_finite (a.baseChange A).zero (ha.baseChange (A := A)).2
    letI : Module.Projective A (LinearMap.ker (a.baseChange A).zero) :=
      kernel_projective (a.baseChange A).zero (ha.baseChange (A := A)).2
    let D := determinantEquivOfSurjectiveQuasiIso K L a ha hqa
    let DA := determinantEquivOfSurjectiveQuasiIso (LinearMap.baseChange A K)
      (LinearMap.baseChange A L) (a.baseChange A) (ha.baseChange (A := A))
      (a.isQuasiIso_baseChange A ha hqa)
    DA.equiv.toLinearMap ∘ₗ (determinantLineBaseChange A K).toLinearMap =
      (determinantLineBaseChange A L).toLinearMap ∘ₗ
        LinearMap.baseChange A D.equiv.toLinearMap := by
  let : Module.Finite R (LinearMap.ker a.neg) := kernel_finite a.neg ha.1
  let : Module.Projective R (LinearMap.ker a.neg) := kernel_projective a.neg ha.1
  let : Module.Finite R (LinearMap.ker a.zero) := kernel_finite a.zero ha.2
  let : Module.Projective R (LinearMap.ker a.zero) := kernel_projective a.zero ha.2
  let : Module.Finite A (LinearMap.ker (a.baseChange A).neg) :=
    kernel_finite (a.baseChange A).neg (ha.baseChange (A := A)).1
  let : Module.Projective A (LinearMap.ker (a.baseChange A).neg) :=
    kernel_projective (a.baseChange A).neg (ha.baseChange (A := A)).1
  let : Module.Finite A (LinearMap.ker (a.baseChange A).zero) :=
    kernel_finite (a.baseChange A).zero (ha.baseChange (A := A)).2
  let : Module.Projective A (LinearMap.ker (a.baseChange A).zero) :=
    kernel_projective (a.baseChange A).zero (ha.baseChange (A := A)).2
  intro D DA
  have hsq : ((determinantLineBaseChange A K).symm ≪≫ₗ
        TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A A) D.equiv ≪≫ₗ
        determinantLineBaseChange A L).toLinearMap ∘ₗ
          (determinantLineBaseChange A K).toLinearMap =
      (determinantLineBaseChange A L).toLinearMap ∘ₗ
        LinearMap.baseChange A D.equiv.toLinearMap := by
    refine LinearMap.ext fun t => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply]
    rfl
  rw [DA.unique _ (baseChange_determinantDiagram R A a ha D.kernelRankZero DA.kernelRankZero
    D.equiv D.compatibility)] at hsq
  exact hsq

end EquivBaseChange

end TwoTermComplex

end
