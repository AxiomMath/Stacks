module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.LocalRing.Quotient
public import StacksFrontier.RingTheory.LocalCohomology.Deps.PuncturedSpectrumAffine
public import StacksCore.Tactic.StacksAttribute

/-!
# The local Lefschetz situation

Let `(A, 𝔪)` be a Noetherian local ring and let `f ∈ 𝔪`.  Write `X = Spec A` and
`X₀ = Spec (A / fA)`, and let `U = X ∖ {𝔪}` and `U₀ = X₀ ∖ {𝔪}` be the punctured spectra of
`A` and of `A / fA`.  This is the standing data for the Lefschetz-style comparison of finite
étale covers of `X`, `X₀`, `U` and `U₀`.

The arithmetic content of the setup is that `U₀` really is the punctured spectrum of the
quotient: the closed immersion `X₀ ⟶ X` carries the closed point of `A / fA` to the closed
point of `A` and is injective on primes, so the inverse image of `U` is exactly the complement
of the closed point of `X₀`.  Describing `U₀` as an inverse image rather than as a punctured
spectrum in its own right is what makes `U₀ ⟶ U` a base change of `X₀ ⟶ X`, recorded here as a
cartesian square.

## Main definitions

* `Stacks.FundamentalGroup.LocalLefschetzSituation` — the standing data and hypotheses.
* `Stacks.FundamentalGroup.LocalLefschetzSituation.X` and `…X₀` — the schemes `Spec A` and
  `Spec (A / fA)`, with `…X₀ToX` the morphism between them.
* `Stacks.FundamentalGroup.LocalLefschetzSituation.U` and `…U₀` — the punctured spectra, with
  `…U₀ToU` the morphism between them.

## Main results

* `Stacks.FundamentalGroup.LocalLefschetzSituation.U₀Open_eq_puncturedSpectrumOpen` identifies
  the inverse image of `U` in `X₀` with the punctured spectrum of `A / fA`.
* `Stacks.FundamentalGroup.LocalLefschetzSituation.isPullback_U₀ToU` exhibits `U₀` as the base
  change of `U` along `X₀ ⟶ X`.

## Implementation notes

The maximal ideal is Mathlib's canonical `IsLocalRing.maximalIdeal`, and the punctured spectrum
is `Stacks.Divisors.puncturedSpectrum`, the open complement of `IsLocalRing.closedPoint`.  The
open subscheme `U₀` is *defined* as the inverse image of `U` under `Spec (A / fA) ⟶ Spec A`,
so that the cartesian square comes from `isPullback_morphismRestrict` rather than having to be
produced by hand; the identification with the punctured spectrum of `A / fA` is then a lemma.

## References

* [Stacks Project, Tag 0BLF](https://stacks.math.columbia.edu/tag/0BLF)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.FundamentalGroup

/-- The standing data and hypotheses of the local Lefschetz situation. -/
@[stacks 0BLF]
public structure LocalLefschetzSituation where
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

/-- The principal ideal `fA`. -/
public abbrev principalIdeal (S : LocalLefschetzSituation) : Ideal S.A :=
  Ideal.span {S.f}

/-- The quotient ring `A / fA`. -/
public abbrev quotientRing (S : LocalLefschetzSituation) : Type u :=
  S.A ⧸ S.principalIdeal

/-- The quotient by `fA` is nontrivial because `f` lies in the maximal ideal. -/
public instance quotientRing_nontrivial (S : LocalLefschetzSituation) :
    Nontrivial S.quotientRing :=
  Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top
    (IsLocalRing.maximalIdeal.isMaximal S.A).ne_top
    (Ideal.span_le.mpr (by simpa using S.f_mem_maximalIdeal)))

/-- The quotient of the local ring `A` by `fA` is local. -/
public instance quotientRing_isLocalRing (S : LocalLefschetzSituation) :
    IsLocalRing S.quotientRing :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk S.principalIdeal)
    Ideal.Quotient.mk_surjective

/-- The quotient map `A ⟶ A / fA` is local. -/
public instance quotientMap_isLocalHom (S : LocalLefschetzSituation) :
    IsLocalHom (Ideal.Quotient.mk S.principalIdeal) :=
  IsLocalHom.of_surjective (Ideal.Quotient.mk S.principalIdeal)
    Ideal.Quotient.mk_surjective

/-- The affine scheme `X = Spec(A)`. -/
public abbrev X (S : LocalLefschetzSituation) : Scheme.{u} :=
  Scheme.Spec.obj (op (CommRingCat.of S.A))

/-- The closed subscheme `X₀ = Spec(A / fA)`. -/
public abbrev X₀ (S : LocalLefschetzSituation) : Scheme.{u} :=
  Scheme.Spec.obj (op (CommRingCat.of S.quotientRing))

/-- The canonical quotient-induced morphism `X₀ ⟶ X`. -/
public def X₀ToX (S : LocalLefschetzSituation) : S.X₀ ⟶ S.X :=
  Scheme.Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk S.principalIdeal)).op

/-- The open complement of the closed point of `X`. -/
public abbrev UOpen (S : LocalLefschetzSituation) : S.X.Opens :=
  Stacks.Divisors.puncturedSpectrum S.A

/-- The punctured spectrum `U = X ∖ {𝔪}`. -/
public abbrev U (S : LocalLefschetzSituation) : Scheme.{u} :=
  S.UOpen.toScheme

/-- The inverse image in `X₀` of the punctured spectrum of `A`.  It is the
punctured spectrum of `A / fA`. -/
public abbrev U₀Open (S : LocalLefschetzSituation) : S.X₀.Opens :=
  S.X₀ToX ⁻¹ᵁ S.UOpen

/-- The inverse-image description of `U₀` is the complement of the closed
point in `Spec(A / fA)`. -/
@[simp]
public lemma U₀Open_eq_puncturedSpectrumOpen (S : LocalLefschetzSituation) :
    S.U₀Open = Stacks.Divisors.puncturedSpectrum S.quotientRing := by
  ext x
  show PrimeSpectrum.comap (Ideal.Quotient.mk S.principalIdeal) x ≠
      IsLocalRing.closedPoint S.A ↔
    x ≠ IsLocalRing.closedPoint S.quotientRing
  rw [← IsLocalRing.comap_closedPoint (Ideal.Quotient.mk S.principalIdeal)]
  exact not_congr ((PrimeSpectrum.comap_injective_of_surjective
    (Ideal.Quotient.mk S.principalIdeal) Ideal.Quotient.mk_surjective).eq_iff)

/-- The punctured spectrum `U₀` of `A / fA`. -/
public abbrev U₀ (S : LocalLefschetzSituation) : Scheme.{u} :=
  S.U₀Open.toScheme

/-- The canonical morphism `U₀ ⟶ U` induced by `A ⟶ A / fA`. -/
public def U₀ToU (S : LocalLefschetzSituation) : S.U₀ ⟶ S.U :=
  S.X₀ToX ∣_ S.UOpen

/-- The morphism of punctured spectra commutes with the two open immersions. -/
@[reassoc]
public lemma U₀ToU_comp_immersion (S : LocalLefschetzSituation) :
    S.U₀ToU ≫ S.UOpen.ι = S.U₀Open.ι ≫ S.X₀ToX :=
  morphismRestrict_ι S.X₀ToX S.UOpen

/-- The punctured spectrum of `A / fA` is the base change of `U` to `X₀`. -/
public lemma isPullback_U₀ToU (S : LocalLefschetzSituation) :
    IsPullback S.U₀ToU S.U₀Open.ι S.UOpen.ι S.X₀ToX :=
  isPullback_morphismRestrict S.X₀ToX S.UOpen

end LocalLefschetzSituation

end Stacks.FundamentalGroup

end
