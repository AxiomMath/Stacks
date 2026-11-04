module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupFreeCohomology
import StacksCore.Tactic.StacksAttribute

/-!
# The two short exact sequences the proof of Tag 0GAA splits a presentation into

Let `A` be a commutative ring, `I ⊆ A` an ideal and `p : X → Spec(A)` the blowup of `Spec(A)` in
`I`. The proof of [Stacks, Tag 0GAA] starts from a finite free presentation
`0 → K → (A/Iⁿ)^{⊕r} → M → 0` of an `(A, n, c)`-module, pulls it back to

`p^*K(q) → (𝒪_{Yₙ})^{⊕r}(q) → p^*M(q) → 0`,

which is no longer left exact, and splits that into the two short exact sequences

`0 → 𝒢 → (𝒪_{Yₙ})^{⊕r}(q) → p^*M(q) → 0`   and   `0 → ℱ → p^*K(q) → 𝒢 → 0`

whose long exact cohomology sequences are the fields `exact_pullback` and `exact_image` of
`Stacks.LocalCohomology.UniformityIII.ModuleSituation`. This file builds those two sequences, for
an arbitrary short exact sequence of `A`-modules in place of a presentation.

## What makes them exist

The twisted pullback `Stacks.Blowup.twistedGeometricFactor` is right exact but not left exact: it
is sheafification, then the inverse image along `p`, then tensoring with `𝒪_X(q)`, and the middle
factor is a left adjoint. So the three facts needed are

* that it preserves finite colimits — `preservesFiniteColimits_twistedPullbackFunctor`, which is
  `Stacks.AlgebraicGeometry.TopDegreeBaseChange.preservesFiniteColimits_geometricFactorFormula`
  with its term supplied by hand rather than by instance search;
* that the image of a short exact sequence is exact in the middle —
  `exact_map_twistedPullbackFunctor`, from `CategoryTheory.ShortComplex.Exact`'s
  `map_of_epi_of_preservesCokernel`, which asks exactly for right exactness and an epi on the
  right; and
* that the right-hand map stays epi — `epi_map_g_twistedPullbackFunctor`.

`𝒢` is then `CategoryTheory.ShortComplex.cycles` of the image complex, i.e. the kernel of
`(𝒪_{Yₙ})^{⊕r}(q) → p^*M(q)`, which by the exactness in the middle *is* the image of
`p^*K(q) → (𝒪_{Yₙ})^{⊕r}(q)` that the source names; and `ℱ` is the kernel of
`p^*K(q) → 𝒢`, which is the kernel of `p^*K(q) → (𝒪_{Yₙ})^{⊕r}(q)` because
`CategoryTheory.ShortComplex.iCycles` is a monomorphism.

## Why the term for right exactness is supplied by hand

`Stacks.LocalCohomology.UniformityIII.twistedPullbackFunctor` is the twisted pullback read at the
`CategoryTheory.SheafOfModules` view of the category of sheaves of modules on the blowup rather
than at the `AlgebraicGeometry.Scheme.Modules` view, because the right derived functors of
`blowupΓmod` are elaborated there. The two views are definitionally equal but carry *different*
`CategoryTheory.Category` and `CategoryTheory.Abelian` instances, and instance search sees
through neither — the same reason
`Stacks.LocalCohomology.UniformityIII.additive_twistedPullbackFunctor` exists. Supplying the term
works because the views are definitionally equal.

The monomorphism of the second sequence is for the same reason given as
`CategoryTheory.Limits.mono_of_isLimit_fork` applied to `limit.isLimit` and not as an instance:
`CategoryTheory.Limits.kernel.ι` is a `limit.π`, and the `Mono` of a kernel inclusion is not
found here by instance search.

## What this does not give

A `ModuleSituation` on the blowup needs, besides these two sequences and the field `freeIso`
(`Stacks.LocalCohomology.UniformityIII.blowupFreeIsoSituationOf`), the quasi-coherence of
`𝒢` and of `ℱ` — the vanishing fields `vanishing_HG` and `vanishing_HF` ask for
`Hⁱ(X, 𝒢(q)) = Hⁱ(X, ℱ(q)) = 0` above the invariant `d`, and
`Stacks.LocalCohomology.UniformityIII.exists_forall_subsingleton_blowupH` gives that only for a
*quasi-coherent* sheaf — and the vanishing `𝒪_{Y₀} = 0` of the field
`subsingleton_Hdiv_zero`. Both are in
`BitUniformityIII/BlowupTwistedPullbackModuleSituation.lean`, which assembles the witness
`Stacks.LocalCohomology.UniformityIII.blowupModuleSituationOf` out of them and these sequences.
The quasi-coherence is no more than
`Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel`, the kernel half of
[Stacks, Tag 01LB], which holds on an **arbitrary** scheme; the one that carries `[IsAffine X]`
is `Stacks.AffineTilde.isQuasicoherent_kernel`, the affine [Stacks, Tag 01IC], and it is not
what is needed.

## Main results

* `Stacks.LocalCohomology.UniformityIII.preservesFiniteColimits_twistedPullbackFunctor`:
  **the twisted pullback is right exact**, at the `SheafOfModules` view.
* `Stacks.LocalCohomology.UniformityIII.shortExact_twistedPullbackFreeSequence`:
  **`0 → 𝒢 → (𝒪_{Yₙ})^{⊕r}(q) → p^*M(q) → 0`.**
* `Stacks.LocalCohomology.UniformityIII.shortExact_twistedPullbackKernelSequence`:
  **`0 → ℱ → p^*K(q) → 𝒢 → 0`.**

## References

* [Stacks Project, Tag 0GAA](https://stacks.math.columbia.edu/tag/0GAA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry

universe u

namespace Stacks.LocalCohomology.UniformityIII

attribute [local instance] modulesMonoidal modulesMonoidal' modulesEnoughInjectives
attribute [local instance] sheafSectionsPreservesFiniteLimits secFPreservesFiniteLimits
attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] (I : Ideal A)

open Stacks.AlgebraicGeometry.TopDegreeBaseChange in
/-- **The twisted pullback `N ↦ 𝒪_X(q) ⊗ p^*Ñ` is right exact.** Sheafification and the inverse
image along `p` are left adjoints and tensoring with a fixed module commutes with colimits, so
all three factors preserve colimits.

The term is `preservesFiniteColimits_geometricFactorFormula` supplied by hand: the statement is
at the `CategoryTheory.SheafOfModules` view of the category, where instance search does not find
the instance that holds at the `AlgebraicGeometry.Scheme.Modules` view, the two views carrying
different `CategoryTheory.Category` instances. -/
theorem preservesFiniteColimits_twistedPullbackFunctor (q : ℤ) :
    PreservesFiniteColimits (twistedPullbackFunctor I q) :=
  preservesFiniteColimits_geometricFactorFormula A
    (Stacks.Blowup.blowUpOver I) (Stacks.Blowup.blowUpTwist I q)

variable {S : ShortComplex (ModuleCat.{u} A)} (q : ℤ)

/-- **The twisted pullback of a short exact sequence of `A`-modules is exact in the middle**:
`𝒪_X(q) ⊗ p^*K̃ → 𝒪_X(q) ⊗ p^*F̃ → 𝒪_X(q) ⊗ p^*M̃` is exact.

It is not exact on the left — that is what forces the splitting into two short exact sequences in
the proof of [Stacks, Tag 0GAA] — but a right exact functor carries the cokernel presentation of
`M` to a cokernel presentation of `p^*M`, and the kernel of a cokernel is the image. -/
theorem exact_map_twistedPullbackFunctor (hS : S.ShortExact) :
    (S.map (twistedPullbackFunctor I q)).Exact := by
  let := preservesFiniteColimits_twistedPullbackFunctor I q
  exact hS.exact.map_of_epi_of_preservesCokernel (twistedPullbackFunctor I q) hS.epi_g
    inferInstance

/-- **The twisted pullback of a surjection is a surjection**: a right exact functor preserves
epimorphisms. -/
theorem epi_map_g_twistedPullbackFunctor (hS : S.ShortExact) :
    Epi ((twistedPullbackFunctor I q).map S.g) := by
  let := preservesFiniteColimits_twistedPullbackFunctor I q
  let : (twistedPullbackFunctor I q).PreservesEpimorphisms := inferInstance
  have := hS.epi_g
  infer_instance

/-- **The sheaf `𝒢` of the proof of [Stacks, Tag 0GAA]**: the kernel of
`(𝒪_{Yₙ})^{⊕r}(q) → p^*M(q)`.

The source names it as the *image* of `p^*K(q) → (𝒪_{Yₙ})^{⊕r}(q)`; the two agree by
`exact_map_twistedPullbackFunctor`, and the kernel is the spelling that makes the first of the
two short exact sequences immediate. -/
abbrev twistedPullbackImage :
    _root_.SheafOfModules.{u} (blowupScheme I).ringCatSheaf :=
  (S.map (twistedPullbackFunctor I q)).cycles

/-- **`0 → 𝒢 → (𝒪_{Yₙ})^{⊕r}(q) → p^*M(q) → 0`**, the first of the two short exact sequences the
proof of [Stacks, Tag 0GAA] splits the pulled-back presentation into. Its long exact cohomology
sequence is the field `exact_pullback` of
`Stacks.LocalCohomology.UniformityIII.ModuleSituation`. -/
abbrev twistedPullbackFreeSequence :
    ShortComplex (_root_.SheafOfModules.{u} (blowupScheme I).ringCatSheaf) :=
  ShortComplex.mk (S.map (twistedPullbackFunctor I q)).iCycles
    (S.map (twistedPullbackFunctor I q)).g
    (S.map (twistedPullbackFunctor I q)).iCycles_g

/-- `twistedPullbackFreeSequence` is short exact: its first map is the kernel of its second by
construction, and its second map is epi by `epi_map_g_twistedPullbackFunctor`. -/
theorem shortExact_twistedPullbackFreeSequence (hS : S.ShortExact) :
    (twistedPullbackFreeSequence I q (S := S)).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ (S.map (twistedPullbackFunctor I q)).cyclesIsKernel
  mono_f := inferInstanceAs (Mono (S.map (twistedPullbackFunctor I q)).iCycles)
  epi_g := epi_map_g_twistedPullbackFunctor I q hS

/-- **The sheaf `ℱ` of the proof of [Stacks, Tag 0GAA]**: the kernel of `p^*K(q) → 𝒢`, which is
the kernel of `p^*K(q) → (𝒪_{Yₙ})^{⊕r}(q)` because
`CategoryTheory.ShortComplex.iCycles` is a monomorphism. -/
abbrev twistedPullbackSupported :
    _root_.SheafOfModules.{u} (blowupScheme I).ringCatSheaf :=
  kernel (S.map (twistedPullbackFunctor I q)).toCycles

/-- **`0 → ℱ → p^*K(q) → 𝒢 → 0`**, the second of the two short exact sequences. Its long exact
cohomology sequence is the field `exact_image` of
`Stacks.LocalCohomology.UniformityIII.ModuleSituation`. -/
abbrev twistedPullbackKernelSequence :
    ShortComplex (_root_.SheafOfModules.{u} (blowupScheme I).ringCatSheaf) :=
  ShortComplex.mk (kernel.ι (S.map (twistedPullbackFunctor I q)).toCycles)
    (S.map (twistedPullbackFunctor I q)).toCycles (kernel.condition _)

/-- `twistedPullbackKernelSequence` is short exact: its second map is epi exactly because the
image complex is exact in the middle, which is `exact_map_twistedPullbackFunctor`. -/
theorem shortExact_twistedPullbackKernelSequence (hS : S.ShortExact) :
    (twistedPullbackKernelSequence I q (S := S)).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _
    (kernelIsKernel (S.map (twistedPullbackFunctor I q)).toCycles)
  mono_f := mono_of_isLimit_fork (limit.isLimit
    (parallelPair (S.map (twistedPullbackFunctor I q)).toCycles 0))
  epi_g := (exact_map_twistedPullbackFunctor I q hS).epi_toCycles

end Stacks.LocalCohomology.UniformityIII

end
