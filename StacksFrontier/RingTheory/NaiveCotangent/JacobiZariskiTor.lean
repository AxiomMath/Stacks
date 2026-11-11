module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.Tor.KernelBaseChange
public import StacksFrontier.RingTheory.NaiveCotangent.JacobiZariskiSixTerm

/-!
# The `Tor` clause of the Jacobi-Zariski sequence

The six-term sequence of Stacks 00S2 (`NaiveCotangent.jacobiZariski_sixTerm_exact`) starts at
`H₁(NL_{B/A} ⊗_B C)`, the first homology of the base change of the naive cotangent complex of
`B` over `A`, and not at `H₁(L_{B/A}) ⊗_B C`.  The source's final assertion compares the two:
if `Tor₁^B(Ω_{B/A}, C) = 0` and `Tor₂^B(Ω_{B/A}, C) = 0`, then
`H₁(NL_{B/A} ⊗_B C) = H₁(L_{B/A}) ⊗_B C`.

Here `NL_{B/A}` is the naive cotangent complex `NL(α) = (I/I² → Ω_{A[x]/A} ⊗ B)` of a
presentation `α : A[x_s] → B`, and the identification is the canonical map
`C ⊗_B H₁(NL(α)) → H₁(NL(α) ⊗_B C)` induced by the inclusion `H₁(NL(α)) = Ker(d) ⊆ I/I²`.

## Main definitions

* `NaiveCotangent.h1BaseChangeMap`: the canonical map `C ⊗_B H₁(NL(α)) → H₁(NL(α) ⊗_B C)`.
* `NaiveCotangent.h1BaseChangeEquivOfTor`: the same map as an isomorphism, under the two `Tor`
  vanishing hypotheses.

## Main results

* `NaiveCotangent.bijective_h1BaseChangeMap_of_tor`: **the final assertion of Stacks 00S2.**

## Implementation notes

`Tor` is Mathlib's `CategoryTheory.Tor'` on `ModuleCat B`, which left-derives `- ⊗_B C` in the
first variable, so that `((Tor' (ModuleCat B) i).obj Ω_{B/A}).obj C` is `Tor_i^B(Ω_{B/A}, C)`
with its arguments in the source's order; it is defined for modules in the universe of the
ring, so `B` and `C` are taken in one universe.  The proof is the source's:
`NL(α) = (N⁻¹ → N⁰)` has `N⁰ = Ω_{A[x]/A} ⊗ B` free and cokernel `Ω_{B/A}`
(`Algebra.Extension.exact_cotangentComplex_toKaehler`), and the homological algebra is
`LinearMap.lTensor_ker_subtype_injective_and_range_eq_of_isZero_tor'`.

## References

* [Stacks Project, Tag 00S2](https://stacks.math.columbia.edu/tag/00S2), Lemma 10.134.4.
-/

@[expose] public section

universe w u₁ u

open Algebra CategoryTheory Function TensorProduct

namespace NaiveCotangent

variable {R : Type u₁} {S : Type u} [CommRing R] [CommRing S] [Algebra R S] {σ : Type w}

/-- The canonical map `C ⊗_B H₁(NL(α)) → H₁(NL(α) ⊗_B C)` for a presentation `α` of `B` over `A`
and a `B`-algebra `C`: the base change of the inclusion `H₁(NL(α)) = Ker(d) ⊆ I/I²`, which
lands in the kernel `H₁(NL(α) ⊗_B C) = Ker(C ⊗_B d)` of the base-changed differential.  Its
source and target are `C ⊗_B NaiveCotangent.H₁ (NL α)` and
`NaiveCotangent.H₁ (nlBaseChange C α)`, spelled as the kernels they are defined to be. -/
noncomputable def h1BaseChangeMap (T : Type*) [CommRing T] [Algebra S T]
    (P : Generators R S σ) :
    T ⊗[S] LinearMap.ker P.toExtension.cotangentComplex →ₗ[T]
      LinearMap.ker (P.toExtension.cotangentComplex.baseChange T) :=
  LinearMap.codRestrict _ ((LinearMap.ker P.toExtension.cotangentComplex).subtype.baseChange T)
    fun x => by
      rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
        LinearMap.comp_ker_subtype, LinearMap.baseChange_zero, LinearMap.zero_apply]

/-- On elements, `NaiveCotangent.h1BaseChangeMap` is the base change of the inclusion
`H₁(NL(α)) ⊆ I/I²`. -/
@[simp] theorem coe_h1BaseChangeMap_apply (T : Type*) [CommRing T] [Algebra S T]
    (P : Generators R S σ) (x : T ⊗[S] LinearMap.ker P.toExtension.cotangentComplex) :
    (h1BaseChangeMap T P x : T ⊗[S] P.toExtension.Cotangent) =
      (LinearMap.ker P.toExtension.cotangentComplex).subtype.baseChange T x :=
  rfl

/-- **The `Tor` clause of the Jacobi-Zariski sequence** (Stacks 00S2, final assertion).  Let
`A → B → C` be ring maps and let `α : A[x_s] → B` be a presentation of `B` over `A`.  If
`Tor₁^B(Ω_{B/A}, C) = 0` and `Tor₂^B(Ω_{B/A}, C) = 0`, then the canonical map
`C ⊗_B H₁(NL(α)) → H₁(NL(α) ⊗_B C)` is bijective, that is
`H₁(NL_{B/A} ⊗_B C) = H₁(L_{B/A}) ⊗_B C`. -/
@[stacks 00S2 "The final assertion: if `Tor₁^B(Ω_{B/A}, C)` and `Tor₂^B(Ω_{B/A}, C)` vanish \
then the canonical map `C ⊗_B H₁(NL_{B/A}) → H₁(NL_{B/A} ⊗_B C)` is an isomorphism; `Tor` is \
Mathlib's `Tor'` on `ModuleCat B`, with `B` and `C` in one universe as `Tor` requires."]
theorem bijective_h1BaseChangeMap_of_tor {T : Type u} [CommRing T] [Algebra S T]
    (P : Generators R S σ)
    (h₁ : Limits.IsZero (((Tor' (ModuleCat.{u} S) 1).obj (ModuleCat.of S Ω[S⁄R])).obj
      (ModuleCat.of S T)))
    (h₂ : Limits.IsZero (((Tor' (ModuleCat.{u} S) 2).obj (ModuleCat.of S Ω[S⁄R])).obj
      (ModuleCat.of S T))) :
    Bijective (h1BaseChangeMap T P) := by
  have : Module.Projective S P.toExtension.CotangentSpace :=
    Module.Projective.of_basis P.cotangentSpaceBasis
  obtain ⟨hinj, hrange⟩ :=
    LinearMap.lTensor_ker_subtype_injective_and_range_eq_of_isZero_tor' T
      P.toExtension.cotangentComplex P.toExtension.toKaehler
      P.toExtension.exact_cotangentComplex_toKaehler P.toExtension.toKaehler_surjective h₁ h₂
  refine ⟨fun x y hxy => hinj ?_, fun y => ?_⟩
  · have h := congrArg Subtype.val hxy
    rwa [coe_h1BaseChangeMap_apply, coe_h1BaseChangeMap_apply,
      LinearMap.baseChange_eq_ltensor] at h
  · have hy : (y : T ⊗[S] P.toExtension.Cotangent) ∈
        LinearMap.ker (P.toExtension.cotangentComplex.lTensor T) := by
      rw [LinearMap.mem_ker, ← LinearMap.baseChange_eq_ltensor]
      exact y.2
    rw [← hrange] at hy
    obtain ⟨x, hx⟩ := hy
    refine ⟨x, Subtype.ext ?_⟩
    rw [coe_h1BaseChangeMap_apply, LinearMap.baseChange_eq_ltensor]
    exact hx

/-- **The `Tor` clause of the Jacobi-Zariski sequence as an isomorphism**: under
`Tor₁^B(Ω_{B/A}, C) = 0` and `Tor₂^B(Ω_{B/A}, C) = 0`, the canonical map
`NaiveCotangent.h1BaseChangeMap` is an isomorphism `C ⊗_B H₁(NL(α)) ≃ H₁(NL(α) ⊗_B C)`. -/
noncomputable def h1BaseChangeEquivOfTor {T : Type u} [CommRing T] [Algebra S T]
    (P : Generators R S σ)
    (h₁ : Limits.IsZero (((Tor' (ModuleCat.{u} S) 1).obj (ModuleCat.of S Ω[S⁄R])).obj
      (ModuleCat.of S T)))
    (h₂ : Limits.IsZero (((Tor' (ModuleCat.{u} S) 2).obj (ModuleCat.of S Ω[S⁄R])).obj
      (ModuleCat.of S T))) :
    T ⊗[S] LinearMap.ker P.toExtension.cotangentComplex ≃ₗ[T]
      LinearMap.ker (P.toExtension.cotangentComplex.baseChange T) :=
  LinearEquiv.ofBijective (h1BaseChangeMap T P) (bijective_h1BaseChangeMap_of_tor P h₁ h₂)

end NaiveCotangent

end
