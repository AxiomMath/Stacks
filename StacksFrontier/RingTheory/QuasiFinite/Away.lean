module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

@[expose] public section

universe u v w u' w'

/-!
# Producing a finite ring map by inverting one element of the base

Let `R → S → T` be ring maps with `R → S` integral and `R → T` of finite type, and let `g ∈ S` be
an element such that `S[1/g] → T[1/g]` is onto. If `g` is invertible in the fibre `κ(p) ⊗[R] S` at
a prime `p` of `R`, then the image `Z ⊆ Spec R` of the closed set `V(g) ⊆ Spec S` misses `p`, and
`Z` is closed because `R → S` is integral (Stacks 00HZ), so some basic open `D(r)` with `r ∉ p`
misses `Z`. For such an `r` the element `g` becomes invertible in `S[1/r]`, hence `S[1/r] → T[1/r]`
is onto and `T[1/r]` is at once integral and of finite type over `R[1/r]`, that is, finite.

## Main results

* `Stacks.QuasiFinite.FiniteAfterInverting.solution`: Stacks 00UI, the proof of
  `IsLocalization.Away.exists_notMem_and_finite_map_of_surjective_awayMapₐ`.

## Implementation notes

*The mathematics above is Mathlib's, and is not reproved here.* The case of the model
localizations `R[1/r] = Localization.Away r` and `T[1/r] = Localization.Away (algebraMap R T r)`
is `Localization.exists_finite_awayMapₐ_of_surjective_awayMapₐ`, which already carries the
`@[stacks 00UI]` attribute; its proof is exactly the argument recalled above, with the closedness
of `Z` supplied by `PrimeSpectrum.isClosedMap_comap_of_isIntegral`. What this file adds is the
passage from those two models to an arbitrary pair of rings satisfying `IsLocalization.Away`,
which is what a caller who did not choose `r` has in hand.

*That passage is `IsLocalization.finite_map_congr` below:* finiteness of the map `S → Q` induced
on localizations by `g : R →+* P` depends only on `g` and on the two submonoids, not on which
rings realize the two localizations. Stated for an arbitrary submonoid rather than for
`Submonoid.powers r`, it is the statement this file owns, and 00UI is one instantiation of it.
It rests on two facts Mathlib does not have:

* `IsLocalization.map_comp_algEquiv`, the naturality of `IsLocalization.map` in the choice of
  models — a commuting square of the two canonical `IsLocalization.algEquiv`s with the induced
  maps, which commutes by `IsLocalization.ringHom_ext` because both composites with
  `algebraMap R S` are `(algebraMap P Q').comp g`;
* `RingHom.Finite.of_equiv_equiv`, transport of `RingHom.Finite` across such a square, the
  `RingHom.Finite` shadow of `Module.Finite.of_equiv_equiv`. Mathlib's `RingHom.finite_respectsIso`
  says the same thing but only for rings in a *single* universe, whereas here `R` and `Rᵣ` are
  independently quantified, so the `Module.Finite` version — which is universe polymorphic — is
  the one that applies.

## References

* [StacksProject 00UI](https://stacks.math.columbia.edu/tag/00UI)
* [StacksProject 00HZ](https://stacks.math.columbia.edu/tag/00HZ)
-/

@[expose] public section

open TensorProduct

namespace Stacks.QuasiFinite.FiniteAfterInverting

/-- Finiteness of a ring map is transported along a commuting square of ring equivalences.
This is the `RingHom.Finite` form of `Module.Finite.of_equiv_equiv`, and unlike
`RingHom.finite_respectsIso` it does not require the four rings to lie in one universe. -/
private theorem RingHom.Finite.of_equiv_equiv {A B A' B' : Type*} [CommRing A] [CommRing B]
    [CommRing A'] [CommRing B'] {φ : A →+* B} {ψ : A' →+* B'} (e₁ : A ≃+* A') (e₂ : B ≃+* B')
    (h : ψ.comp e₁.toRingHom = (e₂ : B →+* B').comp φ) (hφ : φ.Finite) : ψ.Finite := by
  let _ := φ.toAlgebra
  let _ := ψ.toAlgebra
  have : Module.Finite A B := hφ
  exact Module.Finite.of_equiv_equiv e₁ e₂ h

/-- The map induced on localizations by `g : R →+* P` is natural in the choice of the rings
realizing them: the two canonical `IsLocalization.algEquiv`s and the two induced maps form a
commuting square. -/
private theorem IsLocalization.map_comp_algEquiv {R P : Type*} [CommSemiring R] [CommSemiring P]
    {M : Submonoid R} {N : Submonoid P} {g : R →+* P} (hy : M ≤ N.comap g)
    (S S' : Type*) [CommSemiring S] [CommSemiring S'] [Algebra R S] [Algebra R S']
    [IsLocalization M S] [IsLocalization M S'] (Q Q' : Type*) [CommSemiring Q] [CommSemiring Q']
    [Algebra P Q] [Algebra P Q'] [IsLocalization N Q] [IsLocalization N Q'] :
    (IsLocalization.map (S := S') Q' g hy).comp (IsLocalization.algEquiv M S S' : S →+* S')
      = (IsLocalization.algEquiv N Q Q' : Q →+* Q').comp (IsLocalization.map (S := S) Q g hy) :=
  IsLocalization.ringHom_ext M (RingHom.ext fun x => by simp [IsLocalization.map_eq])

/-- Whether the map induced on localizations by `g : R →+* P` is finite does not depend on which
rings realize the two localizations: it may be tested on any convenient pair of models. -/
private theorem IsLocalization.finite_map_congr {R P : Type*} [CommRing R] [CommRing P]
    {M : Submonoid R} {N : Submonoid P} {g : R →+* P} (hy : M ≤ N.comap g)
    (S S' : Type*) [CommRing S] [CommRing S'] [Algebra R S] [Algebra R S']
    [IsLocalization M S] [IsLocalization M S'] (Q Q' : Type*) [CommRing Q] [CommRing Q']
    [Algebra P Q] [Algebra P Q'] [IsLocalization N Q] [IsLocalization N Q'] :
    (IsLocalization.map (S := S) Q g hy).Finite ↔ (IsLocalization.map (S := S') Q' g hy).Finite :=
  ⟨Stacks.QuasiFinite.FiniteAfterInverting.RingHom.Finite.of_equiv_equiv _ _
      (IsLocalization.map_comp_algEquiv hy S S' Q Q'),
    Stacks.QuasiFinite.FiniteAfterInverting.RingHom.Finite.of_equiv_equiv _ _
        (IsLocalization.map_comp_algEquiv hy S' S Q' Q)⟩

/-- Stacks 00UI: for `R`-algebras `S` integral and `T` of finite type, an `R`-algebra map
`f : S →ₐ[R] T` and `g ∈ S` with `S[1/g] → T[1/g]` onto, and a prime `p` of `R` in whose fibre
`κ(p) ⊗[R] S` the image of `g` is a unit, there is `r ∉ p` such that the induced map `Rᵣ → Tᵣ` is
finite for every pair of localizations `Rᵣ` of `R` away from `r` and `Tᵣ` of `T` away from its
image. -/
public theorem solution {R : Type*} {S : Type*}
    {T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [Algebra.IsIntegral R S] [Algebra.FiniteType R T] (f : S →ₐ[R] T) (g : S)
    (hg : Function.Surjective (Localization.awayMapₐ f g)) (p : Ideal R) [p.IsPrime]
    (hgp : IsUnit (M := p.Fiber S) (1 ⊗ₜ g)) :
    ∃ r ∉ p, ∀ (Rᵣ : Type*) (Tᵣ : Type*) [CommRing Rᵣ] [CommRing Tᵣ] [Algebra R Rᵣ]
      [Algebra T Tᵣ] [IsLocalization.Away r Rᵣ] [IsLocalization.Away (algebraMap R T r) Tᵣ],
      (IsLocalization.Away.map Rᵣ Tᵣ (algebraMap R T) r).Finite := by
  -- The model case, `Rᵣ = R[1/r]` and `Tᵣ = T[1/r]`, is Mathlib's; the rest is model-independence.
  obtain ⟨r, hpr, hfin⟩ :=
    Localization.exists_finite_awayMapₐ_of_surjective_awayMapₐ f g hg p (hgp := hgp)
  exact ⟨r, hpr, fun Rᵣ Tᵣ _ _ _ _ _ _ =>
    (IsLocalization.finite_map_congr (M := .powers r) (N := .powers (algebraMap R T r)) _
      (Localization.Away r) Rᵣ (Localization.Away (algebraMap R T r)) Tᵣ).mp hfin⟩

end Stacks.QuasiFinite.FiniteAfterInverting

/-!
# Producing a finite ring map by inverting one element of the base

Let `R → S → T` be ring maps with `R → S` integral and `R → T` of finite type, and let `g ∈ S` be
an element such that the induced map `S[1/g] → T[1/g]` is onto. Let `p` be a prime of `R` in whose
fibre `κ(p) ⊗[R] S` the image of `g` is invertible. Then `p` avoids the image `Z` of the closed
set `V(g) ⊆ Spec S` under `Spec S → Spec R`, and `Z` is closed because `R → S` is integral, so some
basic open `D(r)` with `r ∉ p` misses `Z`. For such an `r` the element `g` becomes invertible in
`S[1/r]`, whence `S[1/r] → T[1/r]` is onto and `T[1/r]` is at once integral and of finite type over
`R[1/r]`, that is, finite.

## Main results

* `IsLocalization.Away.exists_notMem_and_finite_map_of_surjective_awayMapₐ`: Stacks 00UI, with the
  conclusion asserted of an arbitrary pair of localizations of `R` and of `T` away from the element
  the lemma produces.

## Implementation notes

*The tower `R → S' → S` is an `R`-algebra map `f : S →ₐ[R] T`.* The source's data is a pair of
ring maps whose composite is the given `R`-algebra structure on the last ring; that is exactly an
`R`-algebra homomorphism `f : S →ₐ[R] T` between an integral and a finite type `R`-algebra, and it
is more general, since no `Algebra S T` instance or scalar tower need be present. The source's
`S'` and `S` are here `S` and `T`, following Mathlib's convention that the letters run along the
tower.

*Hypothesis (3) is weakened from an isomorphism to a surjection.* The source assumes
`S'_g ≅ S_g`; only surjectivity of the canonical `S[1/g] → T[1/g]` is used, and it is what carries
integrality from `S` to `T[1/r]`. Injectivity is automatic in the source's situation anyway
(`IsLocalization.map_injective_of_injective` for an inclusion `S' ⊆ S`), so nothing is lost, and
the surjective form is what Zariski's Main Theorem 00Q9 hands its consumers, as
`Algebra.ZariskisMainProperty.exists_fg_and_exists_notMem_and_awayMap_bijective`.

*The fibre ring.* `κ(p) ⊗[R] S` is `Ideal.Fiber p S`, and the image of `g` in it is `1 ⊗ₜ g`. The
source writes the fibre as `S' ⊗_R κ(p)`; the two are exchanged by `Algebra.TensorProduct.comm`,
and Mathlib's order puts the base field first, as `Ideal.Fiber` does.

*The localizations in the conclusion are arbitrary, those in the hypothesis are the models.* The
element `r` is produced by the lemma, so a caller cannot choose beforehand which rings realize
`R[1/r]` and `T[1/r]`; the rings it has in hand are pinned only by `IsLocalization.Away`, and
transporting the conclusion across `IsLocalization.algEquiv` is work better done once here than at
every call site. Hence `Rᵣ` and `Tᵣ` are quantified after `r`, and the map whose finiteness is
asserted is the canonical `IsLocalization.Away.map Rᵣ Tᵣ (algebraMap R T) r`, a `RingHom.Finite`
as in `RingHom.localization_away_map_finite` — there is no `Algebra Rᵣ Tᵣ` instance to hang a
`Module.Finite` on. In the hypothesis `g` is given by the caller, so the model `S[1/g]` is
available and is the form 00Q9 produces; abstracting there would buy nothing.

*The model case is Mathlib's.* Mathlib proves the case `Rᵣ = Localization.Away r`,
`Tᵣ = Localization.Away (algebraMap R T r)` as
`Localization.exists_finite_awayMapₐ_of_surjective_awayMapₐ`, already carrying the `@[stacks 00UI]`
tag; since `Localization.awayMapₐ f a` unfolds to `IsLocalization.Away.mapₐ _ _ f a`, that lemma is
this one applied to the two models. Conversely this one follows from it by
`Module.Finite.of_equiv_equiv` along `IsLocalization.algEquiv`, the square commuting by
`IsLocalization.ringHom_ext` on `Submonoid.powers r`; the mathematics is not to be reproved here.

*No hypothesis is idle.* `Algebra.IsIntegral R S` and the surjectivity of `S[1/g] → T[1/g]`
together give integrality of `R[1/r] → T[1/r]`, `Algebra.FiniteType R T` gives its finite type,
and finite is the conjunction of the two (`RingHom.finite_iff_isIntegral_and_finiteType`).
Invertibility of `g` in the fibre at `p` is what puts `p` in the open set from which `r` is drawn,
and it cannot be dropped: for `R = ℤ`, `S = ℤ`, `g = 2`, `T = ℤ[1/2]` and `p = (2)` the other
three hypotheses hold, while `ℤ[1/2][1/r] = ℤ[1/2r]` is finite over `ℤ[1/r]` for no odd `r`.

## References

* [StacksProject 00UI](https://stacks.math.columbia.edu/tag/00UI)
* [StacksProject 00HZ](https://stacks.math.columbia.edu/tag/00HZ)
* [StacksProject 00Q9](https://stacks.math.columbia.edu/tag/00Q9)

## Tags

integral ring map, finite type ring map, finite ring map, localization, fibre ring
-/

@[expose] public section

open TensorProduct



namespace IsLocalization.Away

/-- **Stacks 00UI.** Let `f : S →ₐ[R] T` be a map of `R`-algebras with `S` integral over `R` and
`T` of finite type over `R`, and let `g : S` be an element such that the induced map
`S[1/g] → T[1/g]` is surjective. If `p` is a prime of `R` in whose fibre `κ(p) ⊗[R] S` the image
`1 ⊗ₜ g` of `g` is invertible, then there is an `r ∉ p` such that `T[1/r]` is finite over `R[1/r]`,
for every pair of rings `Rᵣ`, `Tᵣ` realizing those two localizations. -/
public theorem exists_notMem_and_finite_map_of_surjective_awayMapₐ {R : Type u} {S : Type v}
    {T : Type w} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [Algebra.IsIntegral R S] [Algebra.FiniteType R T] (f : S →ₐ[R] T) (g : S)
    (hg : Function.Surjective (Localization.awayMapₐ f g)) (p : Ideal R) [p.IsPrime]
    (hgp : IsUnit (M := p.Fiber S) (1 ⊗ₜ g)) :
    ∃ r ∉ p, ∀ (Rᵣ : Type u') (Tᵣ : Type w') [CommRing Rᵣ] [CommRing Tᵣ] [Algebra R Rᵣ]
      [Algebra T Tᵣ] [IsLocalization.Away r Rᵣ] [IsLocalization.Away (algebraMap R T r) Tᵣ],
      (IsLocalization.Away.map Rᵣ Tᵣ (algebraMap R T) r).Finite :=
  -- `S` does not occur in the conclusion, so it has to be pinned by passing `f` explicitly:
  -- `apply` would leave it a metavariable and fail to synthesize `Algebra.IsIntegral R ?S`.
  Stacks.QuasiFinite.FiniteAfterInverting.solution f g hg p hgp

end IsLocalization.Away
