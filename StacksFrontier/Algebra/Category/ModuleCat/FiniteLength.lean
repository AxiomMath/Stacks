module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.RingTheory.Length

/-!
# Length of module objects

This file records how `Module.length` and `IsFiniteLength` behave on the objects of
`ModuleCat R`: they are invariant under isomorphism, and the kernel and cokernel of a morphism
are controlled by its source and target. The index of a morphism — the length of its cokernel
minus the length of its kernel — is therefore an invariant of a commutative square with
isomorphic verticals.

## Main results

* `ModuleCat.length_eq_of_iso` and `ModuleCat.isFiniteLength_of_iso`: the length and the
  finite-length property are invariant under isomorphism of module objects.
* `ModuleCat.isFiniteLength_kernel_cokernel`: the kernel and cokernel of a morphism between
  finite-length module objects have finite length.
* `ModuleCat.isFiniteLength_kernel_cokernel_of_iso`: the finite-length property of the kernel
  and cokernel transfers along a commutative square whose verticals are isomorphisms.
* `ModuleCat.lengthIndex_eq_of_iso`: the index is invariant along such a square.

## Implementation notes

The kernel and cokernel are the categorical ones; they are related to the linear-algebra
kernel and range quotient by `ModuleCat.kernelIsoKer` and
`ModuleCat.cokernelIsoRangeQuotient`, which is how the statements about a commutative square
are reduced to `CategoryTheory.Limits.kernel.mapIso` and
`CategoryTheory.Limits.cokernel.mapIso`.

Lengths live in `ℕ∞` and the index is an integer, so it is formed from `ENat.toNat` of the two
lengths; a statement about the index therefore carries no finiteness hypothesis of its own and
is only informative where both lengths are finite.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace ModuleCat

variable {A : Type u} [CommRing A]

/-- Isomorphic module objects have the same length. -/
public theorem length_eq_of_iso {M N : ModuleCat.{u} A} (e : M ≅ N) :
    Module.length A M = Module.length A N :=
  e.toLinearEquiv.length_eq

/-- Finite length transports along an isomorphism of module objects. -/
public theorem isFiniteLength_of_iso {M N : ModuleCat.{u} A} (e : M ≅ N)
    (hM : IsFiniteLength A M) : IsFiniteLength A N :=
  e.toLinearEquiv.isFiniteLength hM

/-- The kernel and the cokernel of a morphism between finite-length module objects have finite
length. -/
public theorem isFiniteLength_kernel_cokernel {M N : ModuleCat.{u} A} (g : M ⟶ N)
    (hM : IsFiniteLength A M.carrier) (hN : IsFiniteLength A N.carrier) :
    IsFiniteLength A (kernel g).carrier ∧ IsFiniteLength A (cokernel g).carrier :=
  ⟨IsFiniteLength.of_injective hM
      ((ModuleCat.mono_iff_injective _).mp (inferInstance : Mono (kernel.ι g))),
    IsFiniteLength.of_surjective hN
      ((ModuleCat.epi_iff_surjective _).mp (inferInstance : Epi (cokernel.π g)))⟩

section Square

/-- Along a commutative square with isomorphic verticals, the two linear kernels agree. -/
public noncomputable def kernelKerIso {M N M' N' : ModuleCat.{u} A} (g : M ⟶ N) (g' : M' ⟶ N')
    (eM : M ≅ M') (eN : N ≅ N') (h : g ≫ eN.hom = eM.hom ≫ g') :
    ModuleCat.of A (LinearMap.ker g.hom) ≅ ModuleCat.of A (LinearMap.ker g'.hom) :=
  (ModuleCat.kernelIsoKer g).symm ≪≫ kernel.mapIso g g' eM eN h ≪≫ ModuleCat.kernelIsoKer g'

/-- Along a commutative square with isomorphic verticals, the two linear cokernels agree. -/
public noncomputable def cokernelRangeIso {M N M' N' : ModuleCat.{u} A} (g : M ⟶ N)
    (g' : M' ⟶ N') (eM : M ≅ M') (eN : N ≅ N') (h : g ≫ eN.hom = eM.hom ≫ g') :
    ModuleCat.of A (N ⧸ LinearMap.range g.hom) ≅
      ModuleCat.of A (N' ⧸ LinearMap.range g'.hom) :=
  (ModuleCat.cokernelIsoRangeQuotient g).symm ≪≫ cokernel.mapIso g g' eM eN h ≪≫
    ModuleCat.cokernelIsoRangeQuotient g'

/-- **The index is invariant along a commutative square with isomorphic verticals.** -/
public theorem lengthIndex_eq_of_iso {M N M' N' : ModuleCat.{u} A} (g : M ⟶ N) (g' : M' ⟶ N')
    (eM : M ≅ M') (eN : N ≅ N') (h : g ≫ eN.hom = eM.hom ≫ g') :
    ((Module.length A (N ⧸ LinearMap.range g.hom)).toNat : ℤ) -
        ((Module.length A (LinearMap.ker g.hom)).toNat : ℤ) =
      ((Module.length A (N' ⧸ LinearMap.range g'.hom)).toNat : ℤ) -
        ((Module.length A (LinearMap.ker g'.hom)).toNat : ℤ) := by
  rw [length_eq_of_iso (kernelKerIso g g' eM eN h),
    length_eq_of_iso (cokernelRangeIso g g' eM eN h)]

/-- **Finite length of the kernel and cokernel is invariant along a commutative square with
isomorphic verticals.** -/
public theorem isFiniteLength_kernel_cokernel_of_iso {M N M' N' : ModuleCat.{u} A}
    (g : M ⟶ N) (g' : M' ⟶ N') (eM : M ≅ M') (eN : N ≅ N')
    (h : g ≫ eN.hom = eM.hom ≫ g')
    (hk : IsFiniteLength A (LinearMap.ker g.hom))
    (hc : IsFiniteLength A (N ⧸ LinearMap.range g.hom)) :
    IsFiniteLength A (LinearMap.ker g'.hom) ∧
      IsFiniteLength A (N' ⧸ LinearMap.range g'.hom) :=
  ⟨isFiniteLength_of_iso (kernelKerIso g g' eM eN h) hk,
    isFiniteLength_of_iso (cokernelRangeIso g g' eM eN h) hc⟩

end Square

end ModuleCat

end
