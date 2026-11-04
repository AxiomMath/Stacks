module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.RingTheory.FiniteLength

/-!
# The kernel and cokernel of a morphism of complexes in a degree

Limits and colimits of homological complexes are computed degreewise, so the term of the kernel
of a morphism of complexes in a degree is the kernel of its component in that degree, and
likewise for the cokernel. Over a ring these identify with the module-theoretic kernel and the
quotient by the range.

## Main results

* `HomologicalComplex.kernelEvalIso` and `HomologicalComplex.cokernelEvalIso`: the degreewise
  comparison in an arbitrary target category with finite limits, respectively colimits.
* `HomologicalComplex.kernelXIsoKer` and `HomologicalComplex.cokernelXIsoRangeQuotient`: the
  module-theoretic form over a ring.
* `HomologicalComplex.isFiniteLength_kernel_X` and
  `HomologicalComplex.isFiniteLength_cokernel_X`: finite length of the kernel, respectively
  cokernel, of a component passes to the complex.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace HomologicalComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι}

/-- The term of the kernel of a morphism of complexes in a degree is the kernel of its component
in that degree. -/
def kernelEvalIso [HasFiniteLimits C] {K L : HomologicalComplex C c} (F : K ⟶ L) (i : ι) :
    (kernel F).X i ≅ kernel (F.f i) :=
  PreservesKernel.iso (HomologicalComplex.eval C c i) F

/-- The term of the cokernel of a morphism of complexes in a degree is the cokernel of its
component in that degree. -/
def cokernelEvalIso [HasFiniteColimits C] {K L : HomologicalComplex C c} (F : K ⟶ L) (i : ι) :
    (cokernel F).X i ≅ cokernel (F.f i) :=
  PreservesCokernel.iso (HomologicalComplex.eval C c i) F

variable {R : Type u} [Ring R]

/-- For complexes of modules, the term of the kernel of a morphism in a degree is the kernel of
its component there. -/
def kernelXIsoKer {K L : HomologicalComplex (ModuleCat.{v} R) c} (F : K ⟶ L) (i : ι) :
    (kernel F).X i ≅ ModuleCat.of R (LinearMap.ker (F.f i).hom) :=
  (kernelEvalIso F i).trans (ModuleCat.kernelIsoKer (F.f i))

/-- For complexes of modules, the term of the cokernel of a morphism in a degree is the target
modulo the range of its component there. -/
def cokernelXIsoRangeQuotient {K L : HomologicalComplex (ModuleCat.{v} R) c} (F : K ⟶ L)
    (i : ι) :
    (cokernel F).X i ≅ ModuleCat.of R (L.X i ⧸ LinearMap.range (F.f i).hom) :=
  (cokernelEvalIso F i).trans (ModuleCat.cokernelIsoRangeQuotient (F.f i))

/-- If the kernel of the component of a morphism of complexes of modules in a degree has finite
length, so does the term of the kernel of the morphism in that degree. -/
theorem isFiniteLength_kernel_X {K L : HomologicalComplex (ModuleCat.{v} R) c} (F : K ⟶ L)
    (i : ι) (h : IsFiniteLength R (LinearMap.ker (F.f i).hom)) :
    IsFiniteLength R ((kernel F).X i) :=
  (kernelXIsoKer F i).toLinearEquiv.symm.isFiniteLength h

/-- If the target modulo the range of the component of a morphism of complexes of modules in a
degree has finite length, so does the term of the cokernel of the morphism in that degree. -/
theorem isFiniteLength_cokernel_X {K L : HomologicalComplex (ModuleCat.{v} R) c} (F : K ⟶ L)
    (i : ι) (h : IsFiniteLength R (L.X i ⧸ LinearMap.range (F.f i).hom)) :
    IsFiniteLength R ((cokernel F).X i) :=
  (cokernelXIsoRangeQuotient F i).toLinearEquiv.symm.isFiniteLength h

end HomologicalComplex

end

end
