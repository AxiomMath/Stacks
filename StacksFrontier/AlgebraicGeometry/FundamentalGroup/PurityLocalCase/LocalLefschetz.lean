module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.LocalRing.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.LocalCohomology.Deps.PuncturedSpectrumAffine

/-!
# The local Lefschetz situation

Let `A` be a Noetherian local ring with maximal ideal `𝔪` and let `f ∈ 𝔪`. Write
`X = Spec A` and `X₀ = Spec (A / fA)`, and let `U = X ∖ {𝔪}` and `U₀ = X₀ ∖ {𝔪}` be the
punctured spectra of `A` and of `A / fA`. Comparing finite étale covers of `U` with finite
étale covers of `U₀` is the local Lefschetz problem, and this file packages the standing data
it is phrased in.

## Main definitions

* `AlgebraicGeometry.LocalLefschetzSituation` — the standing data `(A, f)` together with its
  hypotheses.
* `AlgebraicGeometry.LocalLefschetzSituation.X` and
  `AlgebraicGeometry.LocalLefschetzSituation.X₀` — the two spectra, with the closed immersion
  `X₀ToX` between them.
* `AlgebraicGeometry.LocalLefschetzSituation.U` and
  `AlgebraicGeometry.LocalLefschetzSituation.U₀` — the two punctured spectra, with the
  morphism `U₀ToU` between them.

## Main results

* `AlgebraicGeometry.LocalLefschetzSituation.U₀Open_eq_puncturedSpectrumOpen` — the inverse
  image of the punctured spectrum of `A` in `X₀` is the punctured spectrum of `A / fA`.
* `AlgebraicGeometry.LocalLefschetzSituation.isPullback_U₀ToU` — `U₀` is the base change of
  `U` along `X₀ ⟶ X`.

## Implementation notes

The maximal ideal is Mathlib's `IsLocalRing.maximalIdeal` and the punctured spectrum is
`Stacks.Divisors.puncturedSpectrum`, the open complement of the closed point. The open
subscheme `U₀` is *defined* as the inverse image of `U` under `X₀ ⟶ X`, which makes the
pullback square true by construction; that this inverse image really is the punctured spectrum
of `A / fA` is the content of `U₀Open_eq_puncturedSpectrumOpen` and uses `f ∈ 𝔪`.

## References

* [Stacks Project, Tag 0BLF](https://stacks.math.columbia.edu/tag/0BLF)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The standing data of the local Lefschetz situation: a Noetherian local ring `A` together
with an element `f` of its maximal ideal. -/
@[stacks 0BLF]
structure LocalLefschetzSituation where
  /-- The Noetherian local ring. -/
  A : Type u
  /-- The commutative-ring structure on `A`. -/
  [commRing : CommRing A]
  /-- The Noetherian hypothesis on `A`. -/
  [isNoetherianRing : IsNoetherianRing A]
  /-- The local-ring hypothesis on `A`. -/
  [isLocalRing : IsLocalRing A]
  /-- The distinguished element. -/
  f : A
  /-- The distinguished element belongs to the maximal ideal. -/
  f_mem_maximalIdeal : f ∈ IsLocalRing.maximalIdeal A

attribute [instance] LocalLefschetzSituation.commRing
  LocalLefschetzSituation.isNoetherianRing LocalLefschetzSituation.isLocalRing

namespace LocalLefschetzSituation

variable (S : LocalLefschetzSituation.{u})

/-- The principal ideal `fA` cut out by the distinguished element. -/
abbrev principalIdeal : Ideal S.A :=
  Ideal.span {S.f}

/-- The quotient ring `A / fA`. -/
abbrev quotientRing : Type u :=
  S.A ⧸ S.principalIdeal

/-- The quotient by `fA` is nontrivial because `f` lies in the maximal ideal. -/
instance quotientRing_nontrivial : Nontrivial S.quotientRing :=
  Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top
    (IsLocalRing.maximalIdeal.isMaximal S.A).ne_top
    (Ideal.span_le.mpr (by simpa using S.f_mem_maximalIdeal)))

/-- The quotient of the local ring `A` by `fA` is again local. -/
instance quotientRing_isLocalRing : IsLocalRing S.quotientRing :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk S.principalIdeal)
    Ideal.Quotient.mk_surjective

/-- The quotient map `A ⟶ A / fA` is a local homomorphism. -/
instance quotientMap_isLocalHom : IsLocalHom (Ideal.Quotient.mk S.principalIdeal) :=
  IsLocalHom.of_surjective (Ideal.Quotient.mk S.principalIdeal)
    Ideal.Quotient.mk_surjective

/-- The affine scheme `X = Spec A`. -/
abbrev X : Scheme.{u} :=
  Spec (.of S.A)

/-- The closed subscheme `X₀ = Spec (A / fA)`. -/
abbrev X₀ : Scheme.{u} :=
  Spec (.of S.quotientRing)

/-- The closed immersion `X₀ ⟶ X` induced by the quotient map `A ⟶ A / fA`. -/
def X₀ToX : S.X₀ ⟶ S.X :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk S.principalIdeal))

/-- The punctured spectrum of `A`, as an open subscheme of `X`. -/
abbrev UOpen : S.X.Opens :=
  Stacks.Divisors.puncturedSpectrum S.A

/-- The punctured spectrum `U = X ∖ {𝔪}`. -/
abbrev U : Scheme.{u} :=
  S.UOpen.toScheme

/-- The inverse image in `X₀` of the punctured spectrum of `A`. It is the punctured spectrum
of `A / fA`, by `U₀Open_eq_puncturedSpectrumOpen`. -/
abbrev U₀Open : S.X₀.Opens :=
  S.X₀ToX ⁻¹ᵁ S.UOpen

/-- The inverse image in `Spec (A / fA)` of the punctured spectrum of `A` is the punctured
spectrum of `A / fA`: the quotient map is local, so it identifies the closed point of
`Spec (A / fA)` with the closed point of `Spec A`. -/
@[simp]
lemma U₀Open_eq_puncturedSpectrumOpen :
    S.U₀Open = Stacks.Divisors.puncturedSpectrum S.quotientRing := by
  ext x
  change PrimeSpectrum.comap (Ideal.Quotient.mk S.principalIdeal) x ≠
      IsLocalRing.closedPoint S.A ↔
    x ≠ IsLocalRing.closedPoint S.quotientRing
  rw [← IsLocalRing.comap_closedPoint (Ideal.Quotient.mk S.principalIdeal)]
  exact not_congr ((PrimeSpectrum.comap_injective_of_surjective
    (Ideal.Quotient.mk S.principalIdeal) Ideal.Quotient.mk_surjective).eq_iff)

/-- The punctured spectrum `U₀ = X₀ ∖ {𝔪}` of `A / fA`. -/
abbrev U₀ : Scheme.{u} :=
  S.U₀Open.toScheme

/-- The morphism `U₀ ⟶ U` of punctured spectra induced by `A ⟶ A / fA`. -/
def U₀ToU : S.U₀ ⟶ S.U :=
  S.X₀ToX ∣_ S.UOpen

/-- The morphism of punctured spectra commutes with the two open immersions. -/
@[reassoc]
lemma U₀ToU_comp_immersion : S.U₀ToU ≫ S.UOpen.ι = S.U₀Open.ι ≫ S.X₀ToX :=
  morphismRestrict_ι S.X₀ToX S.UOpen

/-- The punctured spectrum of `A / fA` is the base change of the punctured spectrum of `A`
along `X₀ ⟶ X`. -/
lemma isPullback_U₀ToU : IsPullback S.U₀ToU S.U₀Open.ι S.UOpen.ι S.X₀ToX :=
  isPullback_morphismRestrict S.X₀ToX S.UOpen

end LocalLefschetzSituation

end AlgebraicGeometry

end
