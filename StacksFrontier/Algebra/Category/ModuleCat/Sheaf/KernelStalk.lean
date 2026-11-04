module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# The stalk of a kernel is the kernel of the stalk

Let `(X, O_X)` be a ringed space, let `P : A ⟶ B` be a morphism of sheaves of `O_X`-modules and
let `x` be a point of `X`. The stalk at `x` of `CategoryTheory.Limits.kernel P` is the kernel of
the stalk of `P`: the germs of sections of `kernel P` are, via the stalk of `kernel.ι P`, exactly
the germs of sections of `A` killed by the stalk of `P`.

Everything here is stated in the `grpStalk`/`stalkMapL` spelling of the stalk, i.e. as an
`O_{X,x}`-module for `ringStalk X x : CommRingCat`.

## Main results

* `Stacks.SheafOfModules.TensorStalkRingedSpace.injective_stalkMapL_kernel_ι`: the stalk of
  `kernel.ι P` is injective.
* `Stacks.SheafOfModules.TensorStalkRingedSpace.range_stalkMapL_kernel_ι`: its range is the
  kernel of the stalk of `P`.
* `Stacks.SheafOfModules.TensorStalkRingedSpace.kernelStalkLinearEquiv`: the two previous
  results packaged as a linear equivalence between the stalk of `kernel P` and the kernel of
  the stalk of `P`.
* `Stacks.SheafOfModules.TensorStalkRingedSpace.span_eq_top_of_span_image_eq_ker`: a family of
  germs of sections of `kernel P` spans the stalk of `kernel P` as soon as its image spans the
  kernel of the stalk of `P`.

## Implementation notes

The stalk appears in two spellings in the library: `grpStalk X F x`, an abelian group with an
`O_{X,x}`-module structure for the `CommRingCat`-valued `ringStalk X x`, and
`(AlgebraicGeometry.SheafOfModules.stalkFunctor O x).obj F`, a `ModuleCat` over the
`RingCat`-valued stalk of the structure sheaf. Exactness of the stalk functor is available in the
second spelling only.

No bridge between the two scalar rings is needed: injectivity, `LinearMap.range` and
`LinearMap.ker` are conditions on the underlying additive map, and that map is literally the same
in both spellings — `stalkMapL`, `Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMap` and
`AlgebraicGeometry.SheafOfModules.stalkMap` are all the `TopCat.Presheaf.stalkFunctor` of the
underlying morphism of presheaves of abelian groups. So the exactness statement is turned into a
membership statement with `SetLike.ext_iff`, and transported by definitional equality.

## References

* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.SheafOfModules.TensorStalkRingedSpace

variable (X : AlgebraicGeometry.RingedSpace.{u, u})

/-- The stalk of the inclusion of a kernel is injective. -/
theorem injective_stalkMapL_kernel_ι
    {A B : SheafOfModules.{u} (structureSheafRing X)} (P : A ⟶ B) (x : X.carrier) :
    Function.Injective (stalkMapL X (kernel P).val A.val (kernel.ι P).val x) :=
  (AlgebraicGeometry.SheafOfModules.mono_iff_injective_stalkMap (kernel.ι P)).1 inferInstance x

/-- **The stalk of a kernel is the kernel of the stalk.** The germs of sections of `kernel P` are
exactly the germs killed by the stalk of `P`. -/
theorem range_stalkMapL_kernel_ι
    {A B : SheafOfModules.{u} (structureSheafRing X)} (P : A ⟶ B) (x : X.carrier) :
    LinearMap.range (stalkMapL X (kernel P).val A.val (kernel.ι P).val x)
      = LinearMap.ker (stalkMapL X A.val B.val P.val x) := by
  have h := ((AlgebraicGeometry.SheafOfModules.exact_iff_stalkFunctor_map_exact
    (ShortComplex.mk (kernel.ι P) P (by simp))).1
      (CategoryTheory.ShortComplex.exact_kernel P) x).moduleCat_range_eq_ker
  have h' := SetLike.ext_iff.1 h
  simp only [LinearMap.mem_range, LinearMap.mem_ker] at h'
  refine SetLike.ext fun m => ?_
  simp only [LinearMap.mem_range, LinearMap.mem_ker]
  exact h' m

/-- The stalk of `kernel P` as the kernel of the stalk of `P`. -/
noncomputable def kernelStalkLinearEquiv
    {A B : SheafOfModules.{u} (structureSheafRing X)} (P : A ⟶ B) (x : X.carrier) :
    grpStalk X (kernel P).val x
      ≃ₗ[ringStalk X x] LinearMap.ker (stalkMapL X A.val B.val P.val x) :=
  (LinearEquiv.ofInjective _ (injective_stalkMapL_kernel_ι X P x)).trans
    (LinearEquiv.ofEq _ _ (range_stalkMapL_kernel_ι X P x))

/-- `kernelStalkLinearEquiv` is the stalk of `kernel.ι P`, read inside `grpStalk X A.val x`. -/
@[simp]
lemma coe_kernelStalkLinearEquiv_apply
    {A B : SheafOfModules.{u} (structureSheafRing X)} (P : A ⟶ B) (x : X.carrier)
    (m : grpStalk X (kernel P).val x) :
    ((kernelStalkLinearEquiv X P x m : LinearMap.ker (stalkMapL X A.val B.val P.val x)) :
        grpStalk X A.val x)
      = stalkMapL X (kernel P).val A.val (kernel.ι P).val x m := rfl

/-- Composing `kernelStalkLinearEquiv` with the inclusion of the kernel of the stalk of `P` into
the stalk of `A` recovers the stalk of `kernel.ι P`. -/
lemma subtype_comp_kernelStalkLinearEquiv
    {A B : SheafOfModules.{u} (structureSheafRing X)} (P : A ⟶ B) (x : X.carrier) :
    (LinearMap.ker (stalkMapL X A.val B.val P.val x)).subtype ∘ₗ
        (kernelStalkLinearEquiv X P x : grpStalk X (kernel P).val x →ₗ[ringStalk X x] _)
      = stalkMapL X (kernel P).val A.val (kernel.ι P).val x :=
  LinearMap.ext fun _ => rfl

/-- A family of germs of sections of `kernel P` spans the stalk of `kernel P` as soon as its
images span the kernel of the stalk of `P`. -/
theorem span_eq_top_of_span_image_eq_ker
    {A B : SheafOfModules.{u} (structureSheafRing X)} (P : A ⟶ B) (x : X.carrier)
    {ι : Type*} (v : ι → grpStalk X (kernel P).val x)
    (hv : Submodule.span (ringStalk X x)
        (Set.range fun i ↦ stalkMapL X (kernel P).val A.val (kernel.ι P).val x (v i))
      = LinearMap.ker (stalkMapL X A.val B.val P.val x)) :
    Submodule.span (ringStalk X x) (Set.range v) = ⊤ := by
  have hinj : Function.Injective (stalkMapL X (kernel P).val A.val (kernel.ι P).val x) :=
    injective_stalkMapL_kernel_ι X P x
  refine Submodule.map_injective_of_injective hinj ?_
  rw [Submodule.map_top, range_stalkMapL_kernel_ι X P x, ← hv]
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · refine Submodule.map_le_iff_le_comap.2 (Submodule.span_le.2 ?_)
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  · rintro _ ⟨i, rfl⟩
    exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨i, rfl⟩)

end Stacks.SheafOfModules.TensorStalkRingedSpace

end
