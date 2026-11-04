module

public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import StacksFrontier.RingTheory.CohenMacaulay.Defs
public import StacksFrontier.RingTheory.Depth.SemilinearEquiv

/-!
# Maximal Cohen–Macaulayness across a semilinear isomorphism of modules

`Module.depth_eq_of_ringEquiv` transports the depth of a ring *along itself* across a ring
isomorphism `e : A ≃+* B`. What is wanted when a local ring is presented in two ways is the
same fact for an arbitrary module: the module over `A` and the module over `B` are then not the
same module over the same ring, and all that relates them is an additive isomorphism
`f : M ≃+ N` with `f (a • m) = e a • f m`, that is, a semilinear isomorphism over `e`.

This is exactly the shape in which the stalk of a quasi-coherent module on an affine open is
presented: `AlgebraicGeometry.IsAffineOpen.isLocalization_stalk` identifies the local ring
`𝒪_{X, x}` with `Γ(X, U)_𝔭` only up to a ring isomorphism, and
`Stacks.ModuleStalkSpecialization.isLocalizedModule_germₗ` identifies the stalk `ℱ_x` with
`Γ(U, ℱ)_𝔭` only up to an additive isomorphism semilinear over it.

## Main results

* `Module.smul_top_eq_top_congr_of_semilinearEquiv`: a semilinear isomorphism matches the
  condition `I • M = M` with `(I·B) • N = N`, which is the first branch of `Module.depth`.
  The depth equality `depth_I(M) = depth_{I·B}(N)` itself is `Module.depth_eq_of_semilinearEquiv`,
  imported from `StacksFrontier.RingTheory.Depth.SemilinearEquiv`.
* `Module.depth_maximalIdeal_eq_of_semilinearEquiv`: the same at the maximal ideals of two local
  rings, which is the form a transport between two presentations of one local ring takes.
* `Module.isMaximalCohenMacaulay_of_semilinearEquiv`: being maximal Cohen–Macaulay
  ([Stacks, Tag 00NF]) transports.
* `Module.min_supportDim_le_depth_of_isMaximalCohenMacaulay`: a maximal Cohen–Macaulay module
  satisfies Serre's condition `(S_k)` at the closed point for every `k`, since the dimension of
  its support is at most the dimension of the ring.

## Implementation notes

The semilinearity is written as an `AddEquiv` together with the hypothesis
`∀ a m, f (a • m) = e a • f m`, rather than as a `≃ₛₗ`, following
`Module.IsReflexive.of_ringEquiv` in `StacksFrontier/Algebra/Module/Reflexive/RingEquiv.lean`: the
type of a `≃ₛₗ` mentions `RingHomInvPair` instances which a caller would have to bring into
scope, whereas the two data above are what a caller actually has. Mathlib's
`AddEquiv.isRegular_congr` is stated over two different rings against precisely this
compatibility, so the regular sequences transport with no further work; only the saturation
branch `I • M = M` has to be handled by hand, and it is the image of a submodule under a
semilinear map, which `Submodule.smul_induction_on` gives directly.

Depth is the only numerical ingredient transported here. `Module.supportDim` is *not*: the
`(S_k)` consequence above needs only `Module.supportDim_le_ringKrullDim`, so a transport of the
support dimension — which would be the homeomorphism `PrimeSpectrum.comap e` together with the
matching of the two supports — is not needed for maximal Cohen–Macaulayness and is not proved.

## References

* [Stacks Project, Tag 00LI](https://stacks.math.columbia.edu/tag/00LI)
* [Stacks Project, Tag 00NF](https://stacks.math.columbia.edu/tag/00NF)
-/

@[expose] public section

namespace Module

variable {A B : Type*} [CommRing A] [CommRing B] {M N : Type*}
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]

/-- The inverse of a semilinear isomorphism over `e` is semilinear over `e.symm`. -/
public theorem symm_smul_of_semilinearEquiv (e : A ≃+* B) (f : M ≃+ N)
    (hf : ∀ (a : A) (m : M), f (a • m) = e a • f m) (b : B) (n : N) :
    f.symm (b • n) = e.symm b • f.symm n := by
  apply f.injective
  rw [AddEquiv.apply_symm_apply, hf, e.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- Pushing an ideal forward along `e` and pulling it back along `e.symm` returns it. -/
public theorem ideal_map_map_symm (e : A ≃+* B) (I : Ideal A) :
    (I.map (e : A →+* B)).map (e.symm : B →+* A) = I :=
  Ideal.map_of_equiv e

/-- **Saturation is a semilinear invariant**, in both directions. -/
public theorem smul_top_eq_top_congr_of_semilinearEquiv (e : A ≃+* B) (f : M ≃+ N)
    (hf : ∀ (a : A) (m : M), f (a • m) = e a • f m) (I : Ideal A) :
    I • (⊤ : Submodule A M) = ⊤ ↔ (I.map (e : A →+* B)) • (⊤ : Submodule B N) = ⊤ :=
  ⟨smul_top_eq_top_of_semilinearEquiv e I f hf, fun h => ideal_map_map_symm e I ▸
    smul_top_eq_top_of_semilinearEquiv e.symm _ f.symm (symm_smul_of_semilinearEquiv e f hf) h⟩

/-- **Depth at the closed point is a semilinear invariant.** This is the form taken by a
transport between two presentations of one local ring: a ring isomorphism carries the maximal
ideal to the maximal ideal, by `IsLocalRing.map_ringEquiv_maximalIdeal`. -/
public theorem depth_maximalIdeal_eq_of_semilinearEquiv [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) (f : M ≃+ N) (hf : ∀ (a : A) (m : M), f (a • m) = e a • f m) :
    Module.depth A (IsLocalRing.maximalIdeal A) M =
      Module.depth B (IsLocalRing.maximalIdeal B) N :=
  (depth_eq_of_semilinearEquiv e _ f hf).trans
    (congrArg (Module.depth B · N) (IsLocalRing.map_ringEquiv_maximalIdeal e))

/-- **Maximal Cohen–Macaulayness is a semilinear invariant.** Both sides of
`depth_𝔪(M) = dim(A)` transport: the depth by
`Module.depth_maximalIdeal_eq_of_semilinearEquiv` and the Krull dimension by
`ringKrullDim_eq_of_ringEquiv`. -/
public theorem isMaximalCohenMacaulay_of_semilinearEquiv [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) (f : M ≃+ N) (hf : ∀ (a : A) (m : M), f (a • m) = e a • f m)
    (h : Module.IsMaximalCohenMacaulay A M) : Module.IsMaximalCohenMacaulay B N := by
  rwa [Module.IsMaximalCohenMacaulay, ← depth_maximalIdeal_eq_of_semilinearEquiv e f hf,
    ← ringKrullDim_eq_of_ringEquiv e]

/-- **A maximal Cohen–Macaulay module satisfies Serre's condition `(S_k)` at the closed point,
for every `k`**: the dimension of its support is at most the dimension of the ring
(`Module.supportDim_le_ringKrullDim`), which maximal Cohen–Macaulayness equates with the depth.
This is the inequality that [Stacks, Tag 0341] part (3) asks for at a single point. -/
public theorem min_supportDim_le_depth_of_isMaximalCohenMacaulay [IsLocalRing A]
    (h : Module.IsMaximalCohenMacaulay A M) (k : ℕ) :
    min (k : WithBot ℕ∞) (Module.supportDim A M) ≤
      (Module.depth A (IsLocalRing.maximalIdeal A) M : WithBot ℕ∞) :=
  (min_le_right _ _).trans ((Module.supportDim_le_ringKrullDim A M).trans_eq h.symm)

end Module

end
