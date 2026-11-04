module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsComplete
public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.PrincipalPowerSubscheme
public import StacksCore.Tactic.StacksAttribute

/-!
# `i_{n*} ℱ_n` is `ℱ / I ⁿ ℱ` for the infinitesimal neighbourhoods over an affine base

Let `A` be a ring, `I ⊆ A` an ideal, `f : X ⟶ Spec A` a morphism of schemes and `ℱ` a
quasi-coherent sheaf of modules on `X`. The `n`-th infinitesimal neighbourhood of the closed
subscheme of `X` cut out by `I` is the fibre product

`X_n = X ×_{Spec A} Spec (A / I ⁿ)`,

with projection `i_n : X_n ⟶ X`, and `ℱ_n = i_n ^* ℱ`. This file identifies the direct image of
`ℱ_n` with the ideal-power quotient:

`i_{n*} ℱ_n ≅ ℱ / (I · 𝒪_X) ⁿ ℱ`.

That is the second step of the proof of [Stacks, Tag 02OD] — the one the source performs with the
Leray spectral sequence for `i_n` together with [Stacks, Tag 01Y6]. In degree `p = 0` no spectral
sequence is involved: a direct image does not change global sections, so taking global sections of
this isomorphism already gives `H⁰(X_n, ℱ_n) ≅ H⁰(X, ℱ / (I · 𝒪_X) ⁿ ℱ)`, which is the group the
theorem on formal functions [Stacks, Tag 02OC] takes the limit of.

## What is new here

**Only the instantiation.** The underlying statement is [Stacks, Tag 0EL1] and it is already
proved in the library, for an arbitrary closed immersion presented by its ideal sheaf:
`Stacks.Algebraization.idealQuotientPushforwardIso` of
`FormalGeometry/CompletionFullyFaithful/SectionsComplete.lean` gives `ℱ / I ⁿ ℱ ≅ v_* v ^* ℱ` for
every closed immersion `v` with `v.ker = I ^ n` and every quasi-coherent `ℱ`. What this file adds
is that the fibre product `X ×_{Spec A} Spec (A / I ⁿ)` is such a presentation — its projection to
`X` is a closed immersion with kernel ideal sheaf `(I · 𝒪_X) ⁿ`, by
`Stacks.PuncturedSpectrumPicard.baseIdealSheaf_eq_ker_pullback_fst` and
`Stacks.Cohomology.FormalFunctions.baseIdealSheaf_pow` — and the resulting isomorphism, in the
shape [Stacks, Tag 02OD] draws its diagram in.

It also records the case `v = (I ^ n).subschemeι`, which closes the gap the implementation note of
`FormalGeometry/QuotientComparison/Basic.lean` records as open: the canonical comparison
`Stacks.Algebraization.quotientSubschemeComparisonMap` is an isomorphism for a quasi-coherent
sheaf. The two comparisons agree because both are normalised by the pullback–pushforward unit and
the quotient projection is an epimorphism.

## Main definitions

* `Stacks.Cohomology.FormalFunctions.baseNeighbourhood` and
  `Stacks.Cohomology.FormalFunctions.baseNeighbourhoodι` — the fibre product `X_n` and its
  projection `i_n : X_n ⟶ X`.
* `Stacks.Cohomology.FormalFunctions.pushforwardPullbackBaseIdealIso` — the isomorphism
  `i_{n*} ℱ_n ≅ ℱ / (I · 𝒪_X) ⁿ ℱ`.

## Main results

* `Stacks.Cohomology.FormalFunctions.ker_baseNeighbourhoodι` — `i_n` is a closed immersion whose
  kernel ideal sheaf is `(I · 𝒪_X) ⁿ`.
* `Stacks.Cohomology.FormalFunctions.pushforwardPullbackBaseIdealIso_π` — the isomorphism is
  normalised by the quotient projection, so it is the canonical identification and not merely some
  isomorphism between the two sheaves.
* `Stacks.Algebraization.isIso_quotientSubschemeComparisonMap` and
  `Stacks.Algebraization.quotientSubschemeComparisonOfIsQuasicoherent` — [Stacks, Tag 0EL1] in the
  `(I ^ n).subschemeι` presentation the library already names.

## Implementation notes

`Stacks.Algebraization.idealQuotientPushforwardIso` takes the hypothesis `v.ker = I ^ n` on the
nose, so both instantiations are a computation of a kernel ideal sheaf and nothing more. For the
fibre product that computation goes through `baseIdealSheaf A (I ⁿ) f`, the ideal sheaf `I ⁿ 𝒪_X`,
and `baseIdealSheaf_pow` rewrites it as the `n`-th power of `I 𝒪_X` — the form the ideal-power
quotient `Stacks.Algebraization.idealPowerQuotient` and the theorem on formal functions both use.
For `(I ^ n).subschemeι` it is Mathlib's
`AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι`.

The isomorphism is stated with the direct image on the left, which is the direction
[Stacks, Tag 02OD] reads it in; its inverse is the comparison out of the quotient, which is why
the normalisation lemma is about `.inv`.

## References

* [Stacks Project, Tag 02OD](https://stacks.math.columbia.edu/tag/02OD)
* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 02OC](https://stacks.math.columbia.edu/tag/02OC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

variable {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ) (F : X.Modules)

/-- **The comparison `Stacks.Algebraization.quotientSubschemeComparisonMap` of [Stacks, Tag 0EL1]
is an isomorphism** for a quasi-coherent sheaf, closing the gap recorded in the implementation
note of `FormalGeometry/QuotientComparison/Basic.lean`.

It is `Stacks.Algebraization.idealQuotientPushforwardMap` at the closed immersion
`(I ^ n).subschemeι`, whose kernel ideal sheaf is `I ^ n` by Mathlib's `ker_subschemeι`; the two
comparisons agree because both are normalised by the pullback–pushforward unit and the quotient
projection is an epimorphism. -/
public instance isIso_quotientSubschemeComparisonMap [F.IsQuasicoherent] :
    IsIso (quotientSubschemeComparisonMap I n F) := by
  rw [← quotientSubschemeComparisonMap_unique I n F _
    (idealQuotientPushforwardMap_π I n F (I ^ n).subschemeι
      (Scheme.IdealSheafData.ker_subschemeι (I ^ n)))]
  exact isIso_idealQuotientPushforwardMap I n F (I ^ n).subschemeι
    (Scheme.IdealSheafData.ker_subschemeι (I ^ n))

/-- The comparison data of [Stacks, Tag 0EL1], unconditionally for a quasi-coherent sheaf. -/
public def quotientSubschemeComparisonOfIsQuasicoherent [F.IsQuasicoherent] :
    QuotientSubschemeComparison I n F :=
  QuotientSubschemeComparison.ofIsIso I n F

end Stacks.Algebraization

namespace Stacks.Cohomology.FormalFunctions

open Stacks.Algebraization Stacks.PuncturedSpectrumPicard

variable (A : Type u) [CommRing A] (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (n : ℕ)

/-- The `n`-th infinitesimal neighbourhood `X_n = X ×_{Spec A} Spec (A / I ⁿ)` of the closed
subscheme of `X` cut out by `I`, as the diagram of [Stacks, Tag 02OD] draws it. -/
public abbrev baseNeighbourhood : Scheme.{u} :=
  pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n))))

/-- The projection `i_n : X_n ⟶ X`. -/
public abbrev baseNeighbourhoodι : baseNeighbourhood A I f n ⟶ X :=
  pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n))))

/-- `i_n` is a closed immersion, being the base change of the closed immersion
`Spec (A / I ⁿ) ⟶ Spec A`. -/
public instance isClosedImmersion_baseNeighbourhoodι :
    IsClosedImmersion (baseNeighbourhoodι A I f n) :=
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)))) :=
    IsClosedImmersion.spec_of_quotient_mk (R := .of A) (I ^ n)
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n))))).flip inferInstance

/-- **`i_n` cuts out the `n`-th power of `I · 𝒪_X`.** Its kernel ideal sheaf is `I ⁿ 𝒪_X`, because
`i_n` is the base change of `Spec (A / I ⁿ) ⟶ Spec A`, and that is `(I 𝒪_X) ⁿ`. -/
public theorem ker_baseNeighbourhoodι :
    (baseNeighbourhoodι A I f n).ker = baseIdealSheaf A I f ^ n := by
  rw [← baseIdealSheaf_eq_ker_pullback_fst, baseIdealSheaf_pow]

variable (F : X.Modules) [F.IsQuasicoherent]

/-- **`i_{n*} ℱ_n ≅ ℱ / I ⁿ ℱ`.** The direct image of the restriction of `ℱ` to the infinitesimal
neighbourhood `X_n = X ×_{Spec A} Spec (A / I ⁿ)` is the quotient of `ℱ` by the `n`-th power of
the ideal sheaf `I · 𝒪_X`.

This is the **second step of the proof of [Stacks, Tag 02OD]**, not its conclusion: the source
derives `H ᵖ (X_n, ℱ_n) = H ᵖ (X, ℱ / 𝔪 ⁿ ℱ)` from it by the Leray spectral sequence for `i_n`
together with [Stacks, Tag 01Y6]. At `p = 0` no spectral sequence is needed, because a direct
image does not change global sections, so the global sections of this isomorphism are that
identification. The tag's conclusion — that the completed stalk of `R ᵖ f_* ℱ` at `y` is the limit
of the `H ᵖ (X_n, ℱ_n)` — is **not** asserted here: it needs in addition [Stacks, Tag 02OC], which
rests on [Stacks, Tag 02O8], and flat base change [Stacks, Tag 02KH] to reduce `Y` to
`Spec 𝒪_{Y,y}`, which is the reduction that makes `i_n` a closed immersion in the first place.

The underlying mathematics is [Stacks, Tag 0EL1], already proved in the library as
`Stacks.Algebraization.idealQuotientPushforwardIso`; what is asserted here is that the fibre
product of the source's diagram is a presentation it applies to. -/
@[stacks 02OD "the second step of the tag's proof: the identification i_{n*} ℱ_n ≅ ℱ / 𝔪ⁿ ℱ, \
  over an affine base and for the quotient by the n-th power of the ideal sheaf generated by an \
  ideal of that base. The tag's conclusion is NOT asserted: that needs Tag 02OC, which rests on \
  Tag 02O8, together with Tag 02KH"]
public def pushforwardPullbackBaseIdealIso :
    (Scheme.Modules.pushforward (baseNeighbourhoodι A I f n)).obj
        ((Scheme.Modules.pullback (baseNeighbourhoodι A I f n)).obj F) ≅
      idealPowerQuotient (baseIdealSheaf A I f) n F :=
  (idealQuotientPushforwardIso (baseIdealSheaf A I f) n F (baseNeighbourhoodι A I f n)
    (ker_baseNeighbourhoodι A I f n)).symm

/-- The identification `Stacks.Cohomology.FormalFunctions.pushforwardPullbackBaseIdealIso` is the
canonical one: its inverse, composed with the quotient projection `ℱ ⟶ ℱ / I ⁿ ℱ`, is the unit of
`i_n ^* ⊣ i_{n*}`. Since that projection is an epimorphism, this pins the identification down. -/
@[simp]
public theorem pushforwardPullbackBaseIdealIso_π :
    cokernel.π (C := X.Modules) (idealPowerMultiple (baseIdealSheaf A I f) n F).ι ≫
        (pushforwardPullbackBaseIdealIso A I f n F).inv =
      (Scheme.Modules.pullbackPushforwardAdjunction (baseNeighbourhoodι A I f n)).unit.app F :=
  idealQuotientPushforwardMap_π (baseIdealSheaf A I f) n F (baseNeighbourhoodι A I f n)
    (ker_baseNeighbourhoodι A I f n)

end Stacks.Cohomology.FormalFunctions

end
