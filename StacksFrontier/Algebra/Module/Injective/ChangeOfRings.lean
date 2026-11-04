module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksCore.Tactic.StacksAttribute

/-! # Injectivity of a module under restriction of scalars along a flat ring map

Let `R → S` be a flat ring map and let `E` be an `S`-module. If `E` is injective as an
`S`-module, then `E` is injective as an `R`-module: an `R`-linear map `g : X →ₗ[R] E` to be
extended along an injective `R`-linear map `f : X →ₗ[R] Y` is the same datum as the `S`-linear
map `S ⊗[R] X →ₗ[S] E` it induces, flatness makes `S ⊗[R] f` injective, and injectivity of `E`
over `S` extends that map over `S ⊗[R] Y`; restricting the extension along `y ↦ 1 ⊗ y` gives
the required extension of `g`.

## Main results

* `Module.Injective.restrictScalars_of_flat`: an injective module over `S` is injective over `R`
  when `R → S` is flat.

## Implementation notes

`Module.Injective R E` tests injectivity against the `R`-modules living in the universe of `E`,
so the base changes `S ⊗[R] X` appearing in the proof are legitimate test objects over `S` only
once `S` fits into that universe; that is the hypothesis `Small.{v} S`, which is automatic when
`S` and `E` live in the same universe. It is the same hypothesis Mathlib's
`Module.Injective.extension_property` carries.

## References

* [Stacks Project, Tag 08XQ](https://stacks.math.columbia.edu/tag/08XQ)
-/

@[expose] public section

open TensorProduct

universe v

namespace Module.Injective

/-- Let `R → S` be a flat ring map and let `E` be an `S`-module whose sections live in a
universe `v` for which `S` is `v`-small. If `E` is an injective `S`-module, then `E` is
injective as an `R`-module. This is the cross-universe form; see
`Module.Injective.restrictScalars_of_flat'` for the statement of Stacks 08XQ itself. -/
theorem restrictScalars_of_flat (R : Type*) {S : Type*} {E : Type v} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Flat R S] [AddCommGroup E] [Module R E] [Module S E]
    [IsScalarTower R S E] [Small.{v} S] (h : Module.Injective S E) : Module.Injective R E where
  out X Y _ _ _ _ f hf g := by
    have := h
    have hinj : Function.Injective (f.baseChange S) := by
      simpa only [LinearMap.baseChange_eq_ltensor] using
        Module.Flat.lTensor_preserves_injective_linearMap (R := R) (M := S) f hf
    obtain ⟨φ, hφ⟩ := Module.Injective.extension_property S E (S ⊗[R] X) (S ⊗[R] Y)
      (f.baseChange S) hinj (g.liftBaseChange S)
    refine ⟨φ.restrictScalars R ∘ₗ TensorProduct.mk R S Y 1, fun x => ?_⟩
    simpa using LinearMap.congr_fun hφ ((1 : S) ⊗ₜ[R] x)

/-- **Stacks 08XQ.** Let `R → S` be a flat ring map. If `E` is an injective `S`-module, then
`E` is injective as an `R`-module. -/
@[stacks 08XQ]
theorem restrictScalars_of_flat' (R : Type*) {S E : Type v} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Flat R S] [AddCommGroup E] [Module R E] [Module S E]
    [IsScalarTower R S E] (h : Module.Injective S E) : Module.Injective R E :=
  restrictScalars_of_flat R h

end Module.Injective
