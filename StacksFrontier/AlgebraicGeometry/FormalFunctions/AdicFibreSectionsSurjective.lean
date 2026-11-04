module

public import StacksFrontier.AlgebraicGeometry.FormalFunctions.AdicQuotientDevissage
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.ReesFiniteConsequence

/-!
# Clause (2) of [Stacks, Tag 0D2M] over a local base, from the vanishing on the graded layers

Let `A` be a Noetherian ring, `f : X ⟶ Spec A` proper, `I ⊆ A` an ideal, `ℱ` a coherent
`𝒪_X`-module and `𝓘 = I · 𝒪_X`. This file proves

`H⁰(X, ℱ) ⟶ H⁰(X, ℱ / 𝓘 ℱ)` is surjective

from the single hypothesis that `H¹(X, 𝓘 ⁿ ℱ / 𝓘 ⁿ⁺¹ ℱ)` vanishes for every `n`.

That is the last sentence of the proof of [Stacks, Tag 0D2M]: "For `p = 0` we deduce from
Lemma 30.20.4 part (3) that `H⁰(X, ℱ ⊗ ℒ ^⊗ d) ⟶ H⁰(X_y, ℱ_y ⊗ ℒ_y ^⊗ d)` is surjective, which
gives the final statement of the lemma." Over a local base `(A, 𝔪)` with `y` the closed point,
`ℱ / 𝔪 ℱ` is the direct image of `ℱ_y` along the closed immersion `X_y ⟶ X` and
`R⁰ f_*(ℱ)_y = H⁰(X, ℱ)`, so the display above is clause (2) in the form the source's first
paragraph reduces it to, and the *only* thing [Stacks, Tag 0D2N] takes from
[Stacks, Tag 0D2M].

## Main results

* `Stacks.Cohomology.FormalFunctions.surjective_adicCohomologyProj_one_of_isZero_kernel` — the
  statement above.

## The two inputs

The argument is three lines of the source and needs no ampleness, no twist and no fibre.

* Clause (3) of [Stacks, Tag 02OB] in degree `0`: there is a `c` such that for `k ≥ 1 + c` the
  image of `H⁰(X, ℱ / 𝓘 ᵏ ℱ)` in `H⁰(X, ℱ / 𝓘 ℱ)` is exactly the image of `H⁰(X, ℱ)`. This is
  `Stacks.Cohomology.FormalFunctions`
  `.exists_uniform_bound_cohomology_idealPowerQuotient_unconditional`, which carries no
  hypothesis beyond the source's.
* The adic dévissage in degree `0`:
  `Stacks.Cohomology.FormalFunctions`
  `.epi_rightDerived_map_idealPowerQuotientDrop_of_isZero_kernel` makes
  `H⁰(X, ℱ / 𝓘 ᵏ ℱ) ⟶ H⁰(X, ℱ / 𝓘 ℱ)` surjective for every `k ≥ 1`, out of the vanishing of
  `H¹` on the layers.

The first image is therefore everything, so the second is, and that is the surjectivity wanted.
Note which way the two combine: the dévissage alone gives surjectivity *along the tower*, which
says nothing about `H⁰(X, ℱ)` itself; it is the Artin--Rees bound of [Stacks, Tag 02OB] that
identifies the image of `H⁰(X, ℱ)` with the image of a high enough stage of the tower.

## What remains for clause (2) proper

The hypothesis is what the fibre-side instance of part (2) of [Stacks, Tag 0897] would supply,
applied to the twist `ℱ ⊗ ℒ ^⊗ d` with one exponent serving every `n`; the route to it is
recorded in the module documentation of
`StacksFrontier/AlgebraicGeometry/AmpleFibreNeighbourhood/Basic.lean`. Two further steps separate
the display above from clause (2) as [Stacks, Tag 0D2M] states it: the identification of
`H⁰(X, ℱ / 𝔪 ℱ)` with `H⁰(X_y, ℱ_y)` along the closed immersion `X_y ⟶ X`
([Stacks, Tag 089W] and [Stacks, Tag 087T]), and the reduction of a general Noetherian base to
`𝒪_{Y, y}` by flat base change ([Stacks, Tag 02KH]). Neither is done here, and no `@[stacks]`
attribute is attached.

## Implementation notes

Cohomology is `Stacks.Cohomology.FormalFunctions.cohomologyOverBase`, `H ᵖ(X, −)` as an
`A`-module, and the map is `Stacks.Cohomology.FormalFunctions.adicCohomologyProj`, the one whose
kernel clause (1) of [Stacks, Tag 02OB] bounds. Restriction of scalars along `A ⟶ Γ(X, ⊤)`
changes neither carriers nor maps, so surjectivity of the `A`-linear map and of the underlying
`Γ(X, ⊤)`-linear map are the same statement, and the two inputs are used in the spelling each
already has.

## References

* [Stacks Project, Tag 0D2M](https://stacks.math.columbia.edu/tag/0D2M)
* [Stacks Project, Tag 0D2N](https://stacks.math.columbia.edu/tag/0D2N)
* [Stacks Project, Tag 02OB](https://stacks.math.columbia.edu/tag/02OB)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Cohomology.FormalFunctions

open Stacks.Cohomology.AffineBase Stacks.Algebraization

/-- **Sections lift off the first adic quotient when `H¹` of the graded layers vanishes.** For
`A` Noetherian, `f : X ⟶ Spec A` proper, `I ⊆ A` an ideal, `ℱ` coherent and `𝓘 = I · 𝒪_X`, if
`H¹(X, 𝓘 ⁿ ℱ / 𝓘 ⁿ⁺¹ ℱ) = 0` for every `n`, then

`H⁰(X, ℱ) ⟶ H⁰(X, ℱ / 𝓘 ℱ)`

is surjective.

The dévissage makes `H⁰(X, ℱ / 𝓘 ᵏ ℱ) ⟶ H⁰(X, ℱ / 𝓘 ℱ)` surjective for every `k`; clause (3) of
[Stacks, Tag 02OB] says that for `k ≥ 1 + c` its image is the image of `H⁰(X, ℱ)`. This is the
last sentence of the proof of [Stacks, Tag 0D2M], and over a local base — where `ℱ / 𝔪 ℱ` is
the direct image of `ℱ_y` — it is clause (2) of that tag, the only part of it
[Stacks, Tag 0D2N] uses. -/
public theorem surjective_adicCohomologyProj_one_of_isZero_kernel
    (A : Type u) [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (hX : AlgebraicGeometry.IsProper f) (I : Ideal A) (F : X.Modules)
    (hF : SheafOfModules.IsCoherent F)
    (hgr : ∀ n : ℕ,
      IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived 1).obj
        (kernel (idealPowerQuotientDrop (baseIdealSheaf A I f) (Nat.le_succ n) F)))) :
    Function.Surjective (adicCohomologyProj A f I F 0 1) := by
  obtain ⟨c, -, -, h3⟩ :=
    exists_uniform_bound_cohomology_idealPowerQuotient_unconditional A f hX I F hF 0
  have hepi := epi_rightDerived_map_idealPowerQuotientDrop_of_isZero_kernel
    (baseIdealSheaf A I f) F 0 (fun n => hgr n)
    ((Nat.le_add_right 1 c).trans (le_refl (1 + c)))
  have htop : LinearMap.range
      (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived 0).map
      (cokernel.π (C := X.Modules)
        (idealPowerMultiple (baseIdealSheaf A I f) 1 F).ι)).hom = ⊤ := by
    rw [← h3 1 (1 + c) (le_refl (1 + c)), LinearMap.range_eq_top]
    exact (ModuleCat.epi_iff_surjective _).1 hepi
  exact fun y => LinearMap.range_eq_top.1 htop y

end Stacks.Cohomology.FormalFunctions

end
