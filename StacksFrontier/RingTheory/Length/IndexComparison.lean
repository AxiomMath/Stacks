module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
public import StacksFrontier.Algebra.Category.ModuleCat.FiniteLength
public import StacksFrontier.RingTheory.Length.IndexAdditivity
public import StacksFrontier.RingTheory.OrderOfVanishing.Norm

/-!
# Comparing length indices along a common refinement

For a linear map `f` whose kernel and cokernel both have finite length, the *length index* of `f`
is the length of its cokernel minus the length of its kernel. This file collects two ways of
computing such an index.

The first compares two maps `u` and `v` out of modules `M` and `N` into a common `L` which agree
after precomposition with maps `a : K ⟶ M` and `b : K ⟶ N` out of a common refinement `K`:
additivity of the index along a composition forces the indices of `u` and `v` to agree as soon as
the indices of `a` and `b` do.

The second says that multiplication by a ring element `r` contributes nothing to the index of a
map `g` that it leaves injective: the snake lemma attached to multiplication by `r` on the short
exact sequence `0 → M → N → N / im g → 0` has injective connecting map, and the kernel and
cokernel of multiplication by `r` on a finite-length module have equal length.

## Main definitions

* `Module.linearMapSnakeInput`: the snake-lemma input attached to multiplication by a ring
  element on the short exact sequence determined by an injective linear map.

## Main results

* `Module.lengthIndex_eq_of_common_refinement`: two maps into a common target that agree on a
  common refinement have the same length index.
* `Module.lengthIndex_zero_of_finiteLength_correction`: for the snake input above, the kernel and
  the cokernel of the induced map on the bottom row have equal length.
* `Module.length_ker_eq_length_coker_of_snake`: the kernel and cokernel of the bottom row of a
  snake input have equal length when the connecting map is injective and the two outer third
  terms have equal length.

## Implementation notes

These statements carry no Stacks tag. They are the module-theoretic inputs to Stacks Tag 0F25 —
the independence of the Euler characteristic of a coherent triple from the prepared extension
used to compute it — isolated here because they involve no geometry and are reusable on their
own. The geometric half of that argument, which compares two prepared extensions through a
common coherent refinement on `Spec A`, is not in the library yet; when it lands, it is
`lengthIndex_eq_of_common_refinement` that converts the comparison into the equality of indices,
and `lengthIndex_zero_of_finiteLength_correction` that discards the correction coming from
multiplication by the element `f`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Module

public theorem lengthIndex_eq_of_common_refinement
    (A : Type u) [CommRing A]
    {K M N L : Type u}
    [AddCommGroup K] [Module A K] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [AddCommGroup L] [Module A L]
    (a : K →ₗ[A] M) (b : K →ₗ[A] N)
    (u : M →ₗ[A] L) (v : N →ₗ[A] L)
    (hcomm : u.comp a = v.comp b)
    (hka : IsFiniteLength A (LinearMap.ker a))
    (hca : IsFiniteLength A (M ⧸ LinearMap.range a))
    (hkb : IsFiniteLength A (LinearMap.ker b))
    (hcb : IsFiniteLength A (N ⧸ LinearMap.range b))
    (hku : IsFiniteLength A (LinearMap.ker u))
    (hkv : IsFiniteLength A (LinearMap.ker v))
    (hkvcomp : IsFiniteLength A (LinearMap.ker (u.comp a)))
    (hcvcomp : IsFiniteLength A (L ⧸ LinearMap.range (u.comp a)))
    (hkvcomp' : IsFiniteLength A (LinearMap.ker (v.comp b)))
    (hcvcomp' : IsFiniteLength A (L ⧸ LinearMap.range (v.comp b)))
    (hindex :
      (((Module.length A (M ⧸ LinearMap.range a)).toNat : ℤ) -
          ((Module.length A (LinearMap.ker a)).toNat : ℤ)) =
        (((Module.length A (N ⧸ LinearMap.range b)).toNat : ℤ) -
          ((Module.length A (LinearMap.ker b)).toNat : ℤ))) :
    ((Module.length A (L ⧸ LinearMap.range u)).toNat : ℤ) -
        ((Module.length A (LinearMap.ker u)).toNat : ℤ) =
      ((Module.length A (L ⧸ LinearMap.range v)).toNat : ℤ) -
        ((Module.length A (LinearMap.ker v)).toNat : ℤ) := by
  have hu := Module.lengthIndex_comp a u hka hca hku hkvcomp hcvcomp
  have hv := Module.lengthIndex_comp b v hkb hcb hkv hkvcomp' hcvcomp'
  rw [hcomm] at hu
  omega

public theorem isZero_snake_L0_X2
    {A : Type u} [CommRing A]
    (S : ShortComplex.SnakeInput (ModuleCat A)) (hmono : Mono S.v₁₂.τ₂) :
    IsZero S.L₀.X₂ := by
  let e := IsLimit.conePointUniqueUpToIso S.h₀τ₂ (kernelIsKernel S.v₁₂.τ₂)
  exact IsZero.of_iso (isZero_kernel_of_mono S.v₁₂.τ₂) e

public theorem length_ker_eq_length_coker_of_snake
    (A : Type u) [CommRing A]
    (S : ShortComplex.SnakeInput (ModuleCat A))
    (hδ : Function.Injective S.δ.hom)
    (hbottom : Epi S.L₂.g)
    (hlen : Module.length A S.L₀.X₃ = Module.length A S.L₃.X₃) :
    Module.length A (LinearMap.ker S.L₃.f.hom) =
      Module.length A (S.L₃.X₂ ⧸ LinearMap.range S.L₃.f.hom) := by
  calc
    Module.length A (LinearMap.ker S.L₃.f.hom) = Module.length A S.L₀.X₃ :=
      ((LinearEquiv.ofInjective S.δ.hom hδ).trans
        (LinearEquiv.ofEq (LinearMap.range S.δ.hom) (LinearMap.ker S.L₃.f.hom)
          S.L₂'_exact.moduleCat_range_eq_ker)).length_eq.symm
    _ = Module.length A S.L₃.X₃ := hlen
    _ = _ := ((Submodule.quotEquivOfEq _ _ S.L₃_exact.moduleCat_range_eq_ker).trans
      (LinearMap.quotKerEquivOfSurjective S.L₃.g.hom
        ((ModuleCat.epi_iff_surjective _).mp S.epi_L₃_g))).length_eq.symm

public noncomputable def linearMapSnakeInput
    (A : Type u) [CommRing A]
    (M N : Type u) [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (g : M →ₗ[A] N) (hinj : Function.Injective g) (r : A) :
    ShortComplex.SnakeInput (ModuleCat A) := by
  let C := N ⧸ LinearMap.range g
  let p : N →ₗ[A] C := (LinearMap.range g).mkQ
  let S : ShortComplex (ModuleCat A) := ShortComplex.mk
    (ModuleCat.ofHom g) (ModuleCat.ofHom p) (by
      apply ModuleCat.hom_ext
      ext x
      change (LinearMap.range g).mkQ (g x) = 0
      rw [Submodule.mkQ_apply]
      exact (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self g x))
  have hExact : Function.Exact g p := by
    rw [LinearMap.exact_iff]
    change LinearMap.ker ((LinearMap.range g).mkQ) = _
    rw [Submodule.ker_mkQ]
  have : Mono S.f := (ModuleCat.mono_iff_injective _).2 hinj
  have : Epi S.g :=
    (ModuleCat.epi_iff_surjective _).2 (Submodule.mkQ_surjective _)
  have hShort : S.ShortExact := ⟨
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 hExact⟩
  let μM : M →ₗ[A] M := (LinearMap.lsmul A M) r
  let μN : N →ₗ[A] N := (LinearMap.lsmul A N) r
  let μC : C →ₗ[A] C := (LinearMap.lsmul A C) r
  let v : S ⟶ S := ShortComplex.Hom.mk
    (ModuleCat.ofHom μM) (ModuleCat.ofHom μN) (ModuleCat.ofHom μC)
    (by
      apply ModuleCat.hom_ext
      ext x
      exact map_smul g r x)
    (by
      apply ModuleCat.hom_ext
      ext x
      exact map_smul p r x)
  exact {
    L₀ := kernel v
    L₁ := S
    L₂ := S
    L₃ := cokernel v
    v₀₁ := kernel.ι v
    v₁₂ := v
    v₂₃ := cokernel.π v
    h₀ := kernelIsKernel v
    h₃ := cokernelIsCokernel v
    L₁_exact := hShort.exact
    epi_L₁_g := hShort.epi_g
    L₂_exact := hShort.exact
    mono_L₂_f := hShort.mono_f
  }

public theorem lengthIndex_zero_of_finiteLength_correction
    (A : Type u) [CommRing A]
    (M N : Type u) [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (r : A) (g : M →ₗ[A] N)
    (hinj : Function.Injective g)
    (hregN : Function.Injective ((LinearMap.lsmul A N) r))
    (hC : IsFiniteLength A (N ⧸ LinearMap.range g)) :
    Module.length A
        (LinearMap.ker (linearMapSnakeInput A M N g hinj r).L₃.f.hom) =
      Module.length A
        ((linearMapSnakeInput A M N g hinj r).L₃.X₂ ⧸
          LinearMap.range (linearMapSnakeInput A M N g hinj r).L₃.f.hom) := by
  let S := linearMapSnakeInput A M N g hinj r
  let C := N ⧸ LinearMap.range g
  let μC : C →ₗ[A] C := (LinearMap.lsmul A C) r
  have hδ : Function.Injective S.δ.hom := (ModuleCat.mono_iff_injective _).mp
    (S.mono_δ (isZero_snake_L0_X2 S ((ModuleCat.mono_iff_injective _).2 hregN)))
  have hbottom : Epi S.L₂.g :=
    (ModuleCat.epi_iff_surjective _).2 (Submodule.mkQ_surjective (LinearMap.range g))
  have eK : S.L₀.X₃ ≅ ModuleCat.of A (LinearMap.ker μC) :=
    IsLimit.conePointUniqueUpToIso S.h₀τ₃ (ModuleCat.kernelIsLimit (ModuleCat.ofHom μC))
  have eC : S.L₃.X₃ ≅ ModuleCat.of A (C ⧸ LinearMap.range μC) :=
    IsColimit.coconePointUniqueUpToIso S.h₃τ₃
      (ModuleCat.cokernelIsColimit (ModuleCat.ofHom μC))
  have hlen : Module.length A S.L₀.X₃ = Module.length A S.L₃.X₃ :=
    eK.toLinearEquiv.length_eq.trans <|
      (length_ker_eq_length_coker_finiteLength A C (Module.length_ne_top_iff.mpr hC) μC).trans
        eC.toLinearEquiv.length_eq.symm
  exact length_ker_eq_length_coker_of_snake A S hδ hbottom hlen

end Module

end
