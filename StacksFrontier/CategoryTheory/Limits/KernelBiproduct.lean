module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Kernels of biproducts of morphisms

In a preadditive category with binary biproducts, the kernel of `biprod.map a b` is the
biproduct of the kernels of `a` and of `b`: a map into `X₁ ⊞ X₂` killed by `biprod.map a b`
has both of its components killed by the corresponding factor.

## Main results

* `CategoryTheory.Limits.isLimitKernelForkBiprodMap`: the biproduct of the two kernel
  inclusions is a kernel fork of `biprod.map a b`, and is a limit.
* `CategoryTheory.Limits.kernelBiprodMapIso`: the resulting isomorphism
  `kernel a ⊞ kernel b ≅ kernel (biprod.map a b)`.
-/

@[expose] public section

namespace CategoryTheory.Limits

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {X₁ X₂ Y₁ Y₂ : C} (a : X₁ ⟶ Y₁) (b : X₂ ⟶ Y₂) [HasKernel a] [HasKernel b]

/-- The biproduct of two kernel inclusions is killed by the biproduct of the two
morphisms. -/
public theorem biprod_map_kernel_ι_comp :
    biprod.map (kernel.ι a) (kernel.ι b) ≫ biprod.map a b = 0 := by
  apply biprod.hom_ext' <;> simp

/-- The biproduct of the two kernel inclusions is a kernel of `biprod.map a b`: a morphism
`k` with `k ≫ biprod.map a b = 0` has `k ≫ biprod.fst` killed by `a` and `k ≫ biprod.snd`
killed by `b`, so it factors through the two kernels componentwise. -/
public noncomputable def isLimitKernelForkBiprodMap :
    IsLimit (KernelFork.ofι (f := biprod.map a b)
      (biprod.map (kernel.ι a) (kernel.ι b)) (biprod_map_kernel_ι_comp a b)) :=
  KernelFork.IsLimit.ofι _ _
    (fun {_} k hk => biprod.lift
      (kernel.lift a (k ≫ biprod.fst) (by
        rw [Category.assoc, ← biprod.map_fst a b, ← Category.assoc, hk, zero_comp]))
      (kernel.lift b (k ≫ biprod.snd) (by
        rw [Category.assoc, ← biprod.map_snd a b, ← Category.assoc, hk, zero_comp])))
    (fun {_} _ _ => by apply biprod.hom_ext <;> simp)
    (fun {_} _ _ m hm => by
      apply biprod.hom_ext
      · rw [← cancel_mono (kernel.ι a)]
        simp only [biprod.lift_fst, kernel.lift_ι]
        rw [Category.assoc, ← biprod.map_fst (kernel.ι a) (kernel.ι b), ← Category.assoc, hm]
      · rw [← cancel_mono (kernel.ι b)]
        simp only [biprod.lift_snd, kernel.lift_ι]
        rw [Category.assoc, ← biprod.map_snd (kernel.ι a) (kernel.ι b), ← Category.assoc, hm])

/-- The kernel of a biproduct of two morphisms is the biproduct of their kernels. -/
public noncomputable def kernelBiprodMapIso [HasKernel (biprod.map a b)] :
    kernel a ⊞ kernel b ≅ kernel (biprod.map a b) :=
  (isLimitKernelForkBiprodMap a b).conePointUniqueUpToIso
    (limit.isLimit (parallelPair (biprod.map a b) 0))

end CategoryTheory.Limits

end
