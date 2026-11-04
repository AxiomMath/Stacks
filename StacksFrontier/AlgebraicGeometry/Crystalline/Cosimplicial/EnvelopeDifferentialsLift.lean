module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CompletedDifferentials

/-!
# The canonical map from the universal differentials of `D(n)` to `Ω_{D(n)}`

Work in an affine crystalline situation `(A, I, γ)` with target `C`, choose a polynomial algebra
`P = A[x_i]` over `A` and a surjection `P → C`, let `E(n)` be the divided power envelope of the
kernel of the `(n + 1)`-fold tensor power `P ⊗_A ⋯ ⊗_A P → C`, and let `D(n)` be its `p`-adic
completion.

Two modules of differentials are attached to `D(n)`, and the proof of [Stacks, Tag 07LF] meets
both:

* `Ω_{D(n)/A,γ̄(n)}`, the **universal** divided power differentials of `D(n)` with its own
  completed divided powers — the object `Crystalline.tensorFormsLevelEquiv` of
  `ModuleDifferentials/QuotientForms.lean` produces; and
* `Ω̂_{E(n)/A,δ(n)}` — `Crystalline.completedTensorPowerDifferentials` — the `p`-adic completion
  of the differentials of the *uncompleted* envelope `E(n)`, which is the degreewise value of the
  cosimplicial module `Ω_{D(*)}` of [Stacks, Tag 07L1] and therefore the object
  [Stacks, Tag 07L9] and [Stacks, Tag 07LA] are read over.

They are not isomorphic: the universal one is not `p`-adically complete.  But there is a canonical
map from the first to the second, and it is the universal property that provides it.  The second
carries a divided power `A`-derivation out of `D(n)` — `Crystalline.tensorPowerDerivation`, the
`d : D(n) → Ω_{D(n)}` of [Stacks, Tag 07L1] — and `Crystalline.dividedPowerDifferentials_lift`,
which is [Stacks, Tag 07HZ], turns any such derivation into a unique `D(n)`-linear map out of the
universal object.  `Crystalline.tensorPowerDifferentialsToCompleted` is that map.

This is what carries `Crystalline.tensorPowerDifferentialsLevelLinearEquiv` of
`Cosimplicial/EnvelopeDifferentialsLevel.lean` — the identification of the two shapes modulo
`pᵏ`, which is stated for the degree-one modules only — up the exterior powers: an exterior power
is a functor on linear maps, not on identifications of quotients, so a comparison of `⋀^i` of the
two shapes has to come from a map of the modules themselves, and this is the only candidate.
`Crystalline.tensorPowerDifferentialsToCompleted_unique` says so: the map is pinned by sending
the universal differential of a section to that section's derivation, and no second `D(n)`-linear
map does that.

## Main definitions

* `Crystalline.tensorPowerDifferentialsToCompleted` — **the canonical `D(n)`-linear map
  `Ω_{D(n)/A,γ̄(n)} → Ω̂_{E(n)/A,δ(n)}`**, from the universal divided power differentials of
  `D(n)` to the degree `n` of the cosimplicial module `Ω_{D(*)}`.

## Main results

* `Crystalline.tensorPowerDifferentialsToCompleted_d` — it carries the universal differential of
  a section of `D(n)` to the derivation of that section.
* `Crystalline.tensorPowerDifferentialsToCompleted_unique` — that equation pins it: it is the
  only `D(n)`-linear map satisfying it.

## Implementation notes

`Crystalline.dividedPowerDifferentials_lift` is an `ExistsUnique` statement rather than a bundled
construction, so the map is `Classical.choose` of it and the two results above are the two halves
of its `Classical.choose_spec` — the pattern the private lifts of
`StacksFrontier/AlgebraicGeometry/Crystalline/Differentials.lean` already use.  No `Algebra` instance
has to be introduced: `Crystalline.completedTensorPowerDividedPowerRing` is the divided power ring
whose carrier is `Crystalline.pAdicCompletedTensorPowerEnvelope`, and the `A`-algebra structure on
that carrier is the one `Crystalline.tensorPowerDerivation` is already stated over.

## What is and is not proved

Everything here is proved and nothing is assumed.  **No tag attribute is placed and
[Stacks, Tag 07LF] is not proved**; this is one input of its remaining step.

## References

* [Stacks Project, Lemma 60.6.5, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
* [Stacks Project, Tag 07L1](https://stacks.math.columbia.edu/tag/07L1)
* [Stacks Project, Lemma 60.21.1, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
-/

@[expose] public section

universe u v w

namespace Crystalline

variable (s : AffineCrystallineSituation.{u, v}) {ι : Type w}
  (f : MvPolynomial ι s.A →ₐ[s.A] s.C) (hf : Function.Surjective f)

/-- **The canonical `D(n)`-linear map from the universal divided power differentials of `D(n)` to
the completed differentials `Ω_{D(n)}` of the envelope `E(n)`.**

`Ω_{D(n)}` carries the divided power `A`-derivation `d : D(n) → Ω_{D(n)}` of [Stacks, Tag 07L1],
namely `Crystalline.tensorPowerDerivation`; the universal property [Stacks, Tag 07HZ] of the
divided power differentials of `D(n)` therefore produces a unique `D(n)`-linear map out of them
compatible with that derivation.  This is it. -/
public noncomputable def tensorPowerDifferentialsToCompleted (n : ℕ) :
    dividedPowerDifferentials (A := (s.A : Type u))
        (completedTensorPowerDividedPowerRing s f hf n).dividedPowers →ₗ[
          pAdicCompletedTensorPowerEnvelope s f hf n]
      completedTensorPowerDifferentials s f n :=
  Classical.choose (dividedPowerDifferentials_lift
    (completedTensorPowerDividedPowerRing s f hf n) (tensorPowerDerivation s f hf n))

/-- **The canonical map carries `d b` to `d b`.**  The universal divided power differential of a
section `b` of `D(n)` goes to the value at `b` of the derivation `d : D(n) → Ω_{D(n)}` of
[Stacks, Tag 07L1]. -/
public theorem tensorPowerDifferentialsToCompleted_d (n : ℕ)
    (b : pAdicCompletedTensorPowerEnvelope s f hf n) :
    tensorPowerDifferentialsToCompleted s f hf n
        (dividedPowerDifferential (A := (s.A : Type u))
          (completedTensorPowerDividedPowerRing s f hf n).dividedPowers b) =
      tensorPowerDerivation s f hf n b :=
  (Classical.choose_spec (dividedPowerDifferentials_lift
    (completedTensorPowerDividedPowerRing s f hf n) (tensorPowerDerivation s f hf n))).1 b

/-- **That equation pins the canonical map.**  No second `D(n)`-linear map
`Ω_{D(n)/A,γ̄(n)} → Ω̂_{E(n)/A,δ(n)}` carries the universal differential of every section to that
section's derivation — the universal differentials are generated by those elements. -/
public theorem tensorPowerDifferentialsToCompleted_unique (n : ℕ)
    (psi : dividedPowerDifferentials (A := (s.A : Type u))
        (completedTensorPowerDividedPowerRing s f hf n).dividedPowers
          →ₗ[pAdicCompletedTensorPowerEnvelope s f hf n] completedTensorPowerDifferentials s f n)
    (hpsi : ∀ b : pAdicCompletedTensorPowerEnvelope s f hf n,
      psi (dividedPowerDifferential (A := (s.A : Type u))
        (completedTensorPowerDividedPowerRing s f hf n).dividedPowers b) =
          tensorPowerDerivation s f hf n b) :
    psi = tensorPowerDifferentialsToCompleted s f hf n :=
  (Classical.choose_spec (dividedPowerDifferentials_lift
    (completedTensorPowerDividedPowerRing s f hf n) (tensorPowerDerivation s f hf n))).2 psi hpsi

end Crystalline

end
