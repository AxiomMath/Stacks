module

public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.ConductorLocalization
public import StacksFrontier.RingTheory.Derivation.IntegralClosureUnique
public import StacksFrontier.RingTheory.Derivation.Localization
public import StacksFrontier.RingTheory.IntegralClosure.LocalizationMembership

/-!
# Extending a derivation to the integral closure is a local problem

Let `k` be a field, let `A` be a reduced `k`-algebra with finitely many minimal primes, let `L`
be its total ring of fractions and let `A' = integralClosure A L` be its normalization. A
`k`-derivation `D` of `A` extends to `A'` in at most one way
(`Stacks.DerivationExtension.extend_integralClosure_unique`), and it extends at all exactly when
the canonical extension of `D` to `L` carries `A'` into itself
(`Stacks.DerivationExtension.existsUnique_extend_integralClosure_of_stable`). The content of this
file is that the latter condition may be checked one maximal ideal at a time: if every
`k`-derivation of every local ring `A_P` extends to the normalization of `A_P`, then `D` extends
to `A'`.

The reason is that stability of the canonical extension `D̃` of `D` to `L` is a statement about
membership in the `A`-submodule `A'` of `L`, and such a membership is detected at the maximal
ideals of `A` (`Stacks.IntegralClosureLocal.isIntegral_of_forall_maximal_exists_smul_isIntegral`).
Fix a maximal ideal `P`, write `C = A_P`, and let `Lp` be the localization of `L` at the image of
`P.primeCompl`. Then `Lp` is at the same time a localization of `A` — so the image of `D̃` in
`Lp` is the canonical extension of `D` to `Lp`, by the naturality
`Stacks.DerivationExtension.algHom_locDeriv` — and the total ring of fractions of `C`, so the
hypothesis provides a derivation of the integral closure `B` of `C` in `Lp` extending the
localized derivation. The canonical extension to `Lp` of that derivation of `B` agrees with the
canonical extension of `D`, because the two agree on the image of `A` and `Lp` is a localization
of `A`; since the first carries `B` into `B`, the image of `D̃ z` in `Lp` is integral over `C` for
every `z : A'`. Clearing denominators twice — once for the coefficients of an integral equation
over `C`, once for the kernel of `L → Lp` — produces an element of `A` outside `P` carrying `D̃ z`
into `A'`, which is what the local criterion asks for.

Finiteness of the set of minimal primes enters only through `Lp`: it makes `L` Artinian, which is
what identifies `Lp` with the total ring of fractions of `C`.

## Main results

* `Stacks.DerivationExtension.existsUnique_extend_integralClosure_of_forall_maximal` —
  **extending a `k`-derivation to the integral closure in the total ring of fractions is a local
  problem.**

## References

* [Stacks Project, Tag 07PE](https://stacks.math.columbia.edu/tag/07PE)
* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
* [Stacks Project, Tag 0E68](https://stacks.math.columbia.edu/tag/0E68)
-/

@[expose] public noncomputable section

universe u v w

namespace Stacks.DerivationExtension

section Transport

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- Conjugation of a derivation by an algebra equivalence: for `e : S ≃ₐ[R] T` and an
`R`-derivation `D` of `T`, the map `s ↦ e.symm (D (e s))` is an `R`-derivation of `S`. -/
private def congrDerivationOfAlgEquiv (e : S ≃ₐ[R] T) (D : Derivation R T T) :
    Derivation R S S where
  toFun s := e.symm (D (e s))
  map_add' s₁ s₂ := by simp
  map_smul' r s := by simp
  map_one_eq_zero' := by simp
  leibniz' s₁ s₂ := by
    change e.symm (D (e (s₁ * s₂))) = s₁ • e.symm (D (e s₂)) + s₂ • e.symm (D (e s₁))
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, AlgEquiv.symm_apply_apply]

/-- The conjugated derivation of `S`, read through the equivalence, is the given derivation of
`T`. -/
private lemma congrDerivationOfAlgEquiv_apply (e : S ≃ₐ[R] T) (D : Derivation R T T) (s : S) :
    e (congrDerivationOfAlgEquiv e D s) = D (e s) :=
  e.apply_symm_apply _

end Transport

section Intermediate

/-- **A localization is a localization of every intermediate subalgebra.** If `Lp` is the
localization of `C` at a submonoid `M` and `S` is a `C`-subalgebra of `Lp`, then `Lp` is also the
localization of `S` at the image of `M`: the denominators are already there, every element of
`Lp` is a fraction whose numerator may be taken in the image of `C`, and `S → Lp` is injective
because `S` is a subobject of `Lp`. -/
private lemma isLocalization_of_subalgebra {C Lp : Type*} [CommRing C] [CommRing Lp]
    [Algebra C Lp] (M : Submonoid C) [IsLocalization M Lp] (S : Subalgebra C Lp) :
    IsLocalization (Algebra.algebraMapSubmonoid ↥S M) Lp where
  map_units y := by
    obtain ⟨c, hc, hcy⟩ := Submonoid.mem_map.mp y.2
    have h : algebraMap ↥S Lp (y : ↥S) = algebraMap C Lp c := by
      rw [← hcy, ← IsScalarTower.algebraMap_apply]
    rw [h]
    exact IsLocalization.map_units Lp ⟨c, hc⟩
  surj x := by
    obtain ⟨⟨a, c⟩, hac⟩ := IsLocalization.surj M x
    refine ⟨⟨algebraMap C ↥S a, ⟨algebraMap C ↥S (c : C),
      Algebra.mem_algebraMapSubmonoid_of_mem c⟩⟩, ?_⟩
    simpa only [← IsScalarTower.algebraMap_apply C ↥S Lp] using hac
  exists_of_eq {x y} h := by
    refine ⟨1, ?_⟩
    rw [Subtype.ext (h : (x : Lp) = (y : Lp))]

end Intermediate

section Realization

/-- **A derivation of the integral closure of `C` in its total ring of fractions transports to
any other realization of that ring of fractions.** If `Lp` is a localization of `C` at its
nonzerodivisors, the integral closures of `C` in `Lp` and in `FractionRing C` are isomorphic as
`C`-algebras, hence as `k`-algebras, and a derivation of the second extending `D₀` conjugates to
one of the first. -/
private lemma exists_derivation_integralClosure {k : Type*} {C : Type*} [Field k] [CommRing C]
    [Algebra k C] (D₀ : Derivation k C C) (Lp : Type*) [CommRing Lp] [Algebra C Lp]
    [Algebra k Lp] [IsScalarTower k C Lp] [IsLocalization (nonZeroDivisors C) Lp]
    (E : Derivation k ↥(integralClosure C (FractionRing C))
      ↥(integralClosure C (FractionRing C)))
    (hE : ∀ c : C, E (algebraMap C ↥(integralClosure C (FractionRing C)) c)
      = algebraMap C ↥(integralClosure C (FractionRing C)) (D₀ c)) :
    ∃ E' : Derivation k ↥(integralClosure C Lp) ↥(integralClosure C Lp),
      ∀ c : C, E' (algebraMap C ↥(integralClosure C Lp) c)
        = algebraMap C ↥(integralClosure C Lp) (D₀ c) := by
  have eC : ↥(integralClosure C Lp) ≃ₐ[C] ↥(integralClosure C (FractionRing C)) :=
    AlgEquiv.mapIntegralClosure
      (IsLocalization.algEquiv (nonZeroDivisors C) Lp (FractionRing C))
  have hcomm : ∀ c : C, (eC.restrictScalars k) (algebraMap C ↥(integralClosure C Lp) c)
      = algebraMap C ↥(integralClosure C (FractionRing C)) c := fun c => eC.commutes c
  refine ⟨congrDerivationOfAlgEquiv (eC.restrictScalars k) E, fun c => ?_⟩
  refine (eC.restrictScalars k).injective ?_
  rw [hcomm, congrDerivationOfAlgEquiv_apply, hcomm]
  exact hE c

end Realization

section Localized

variable {k : Type u} {A : Type v} {L : Type w} [Field k] [CommRing A] [Algebra k A]
  [CommRing L] [Algebra A L] [IsLocalization (nonZeroDivisors A) L]
  (P : Ideal A) [P.IsPrime]
  (C : Type*) [CommRing C] [Algebra A C] [IsLocalization P.primeCompl C]
  [Algebra k C] [IsScalarTower k A C]
  (Lp : Type*) [CommRing Lp] [Algebra L Lp] [Algebra A Lp] [Algebra C Lp] [Algebra k Lp]
  [IsScalarTower A L Lp] [IsScalarTower A C Lp] [IsScalarTower k A Lp]

/-- **The canonical extension of `D` to `Lp`, evaluated at an element coming from an intermediate
ring that carries a derivation over `C`.** Let `B` be a `C`-algebra mapping to `Lp` in such a way
that `Lp` is the localization of `B` at the image of the nonzerodivisors of `C`, and let `E` be a
derivation of `B` extending the localization of `D` to `C`. Then the image in `Lp` of `D̃ x`, for
`D̃` the canonical extension of `D` to `L`, is the image of `E w`, whenever `x : L` and `w : B`
have the same image in `Lp`.

Both derivations of `Lp` in play — the canonical extension of `D` and the canonical extension of
`E` — agree on the image of `A`, and `Lp` is a localization of `A` at `T`, so they are equal; the
naturality of the canonical extension identifies the image of `D̃ x` with the value of the first
one at the image of `x`. -/
private lemma algebraMap_locDeriv_eq (D : Derivation k A A) (T : Submonoid A)
    [IsLocalization T Lp] (B : Type*) [CommRing B] [Algebra C B] [Algebra B Lp] [Algebra k B]
    [IsScalarTower C B Lp] [IsScalarTower k B Lp]
    [IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors C)) Lp]
    (E : Derivation k B B)
    (hE : ∀ c : C, E (algebraMap C B c) = algebraMap C B (D.localization P.primeCompl C c))
    (x : L) (w : B) (hw : algebraMap B Lp w = algebraMap L Lp x) :
    algebraMap L Lp (locDeriv (D.restrictScalars ℤ) (nonZeroDivisors A) L x)
      = algebraMap B Lp (E w) := by
  have h1 : ∀ a : A,
      algebraMap A Lp a = algebraMap B Lp (algebraMap C B (algebraMap A C a)) := fun a => by
    rw [← IsScalarTower.algebraMap_apply C B Lp, ← IsScalarTower.algebraMap_apply A C Lp]
  have hagree : ∀ a : A,
      E.localization (Algebra.algebraMapSubmonoid B (nonZeroDivisors C)) Lp (algebraMap A Lp a)
        = algebraMap A Lp (D a) := fun a => by
    rw [h1 a, Derivation.localization_algebraMap, hE, Derivation.localization_algebraMap,
      ← h1]
  have heq : E.localization (Algebra.algebraMapSubmonoid B (nonZeroDivisors C)) Lp
      = D.localization T Lp :=
    Derivation.eq_localization D T Lp _ hagree
  have hval : D.localization T Lp (algebraMap L Lp x)
      = locDeriv (D.restrictScalars ℤ) T Lp (algebraMap L Lp x) :=
    congrFun (Derivation.coe_localization D T Lp) (algebraMap L Lp x)
  have hnat : algebraMap L Lp (locDeriv (D.restrictScalars ℤ) (nonZeroDivisors A) L x)
      = locDeriv (D.restrictScalars ℤ) T Lp (algebraMap L Lp x) := by
    simpa using algHom_locDeriv (S := nonZeroDivisors A) (T := T) (D.restrictScalars ℤ) L Lp
      (IsScalarTower.toAlgHom A L Lp) x
  rw [hnat, ← hval, ← heq, ← hw, Derivation.localization_algebraMap]

/-- **The local criterion at one prime.** If the localization `D₀` of `D` at `P` extends to a
derivation of the integral closure of `C = A_P` in its total ring of fractions, then for every
element `x` of `L` integral over `A` some element of `A` outside `P` carries `D̃ x` into the
integral closure of `A` in `L`.

The image of `D̃ x` in `Lp` is integral over `C` by
`Stacks.DerivationExtension.algebraMap_locDeriv_eq`; clearing the denominators of an integral
equation over `C` makes a multiple of it integral over `A`, and clearing the denominators of the
localization map `L → Lp` brings that multiple back from `Lp` to `L`. Both denominators lie
outside `P`, and so does their product because `P` is prime. -/
private lemma exists_smul_mem_integralClosure (D : Derivation k A A) (T : Submonoid A)
    [IsLocalization T Lp] [IsLocalization (nonZeroDivisors C) Lp]
    [IsLocalization (Algebra.algebraMapSubmonoid L P.primeCompl) Lp]
    (E : Derivation k ↥(integralClosure C (FractionRing C))
      ↥(integralClosure C (FractionRing C)))
    (hE : ∀ c : C, E (algebraMap C ↥(integralClosure C (FractionRing C)) c)
      = algebraMap C ↥(integralClosure C (FractionRing C))
        (D.localization P.primeCompl C c))
    (x : L) (hx : IsIntegral A x) :
    ∃ a ∈ (P : Set A)ᶜ, a • locDeriv (D.restrictScalars ℤ) (nonZeroDivisors A) L x
      ∈ Subalgebra.toSubmodule (integralClosure A L) := by
  have : IsScalarTower k C Lp := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply k A C r, ← IsScalarTower.algebraMap_apply A C Lp]
    exact IsScalarTower.algebraMap_apply k A Lp r
  have := isLocalization_of_subalgebra (nonZeroDivisors C) (integralClosure C Lp)
  obtain ⟨E', hE'⟩ := exists_derivation_integralClosure (D.localization P.primeCompl C) Lp E hE
  have hxA : IsIntegral A (algebraMap L Lp x) := by
    simpa using hx.map (IsScalarTower.toAlgHom A L Lp)
  have hxB : algebraMap L Lp x ∈ integralClosure C Lp := hxA.tower_top (R := A)
  have hkey := algebraMap_locDeriv_eq P C Lp D T ↥(integralClosure C Lp) E' hE' x
    ⟨algebraMap L Lp x, hxB⟩ rfl
  have hint : IsIntegral C (algebraMap L Lp
      (locDeriv (D.restrictScalars ℤ) (nonZeroDivisors A) L x)) := by
    rw [hkey]
    exact (E' _).2
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (Rₘ := C)
    P.primeCompl _ hint
  rw [Submonoid.smul_def] at hm
  obtain ⟨m', hm'P, hm'⟩ := IsLocalization.exists_isIntegral_smul_of_isIntegral_map
    (Sₘ := Lp) P.primeCompl
    (x := (m : A) • locDeriv (D.restrictScalars ℤ) (nonZeroDivisors A) L x)
    (by simpa [Algebra.smul_def, ← IsScalarTower.algebraMap_apply] using hm)
  refine ⟨m' * (m : A), mul_mem hm'P m.2, ?_⟩
  rw [Subalgebra.mem_toSubmodule, mul_smul]
  exact hm'

end Localized

section Main

/-- **Extending a `k`-derivation to the integral closure in the total ring of fractions is a
local problem.** Let `A` be a reduced `k`-algebra with finitely many minimal primes and let `D`
be a `k`-derivation of `A`. If, for every maximal ideal `P` of `A`, every `k`-derivation of the
local ring `A_P` extends to the integral closure of `A_P` in its total ring of fractions, then
`D` extends, uniquely, to the integral closure of `A` in its own total ring of fractions.

Only the derivations obtained from `D` by localization are used, so the hypothesis could be
weakened to those; it is stated for all derivations of `A_P` because that is the shape in which
the local computations at a node and at a smooth point produce it. -/
public theorem existsUnique_extend_integralClosure_of_forall_maximal
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsReduced A] [Algebra k A]
    (hmin : (minimalPrimes A).Finite)
    (hloc : ∀ (P : Ideal A) (_ : P.IsMaximal)
      (D₀ : Derivation k (Localization.AtPrime P) (Localization.AtPrime P)),
      ∃ E : Derivation k
          ↥(integralClosure (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)))
          ↥(integralClosure (Localization.AtPrime P) (FractionRing (Localization.AtPrime P))),
        ∀ a : Localization.AtPrime P,
          E (algebraMap _ _ a) = algebraMap _ _ (D₀ a))
    (D : Derivation k A A) :
    ∃! D' : Derivation k ↥(integralClosure A (FractionRing A))
        ↥(integralClosure A (FractionRing A)),
      ∀ a : A, D' (algebraMap A ↥(integralClosure A (FractionRing A)) a)
        = algebraMap A ↥(integralClosure A (FractionRing A)) (D a) := by
  classical
  refine existsUnique_extend_integralClosure_of_stable D fun z => ?_
  refine Stacks.IntegralClosureLocal.isIntegral_of_forall_maximal_exists_smul_isIntegral _
    fun P hP => ?_
  have : P.IsPrime := hP.isPrime
  have : IsArtinianRing (FractionRing A) := Stacks.Curves.isArtinianRing_fractionRing A hmin
  have : IsFractionRing (Localization.AtPrime P)
      (Localization (Algebra.algebraMapSubmonoid (FractionRing A) P.primeCompl)) :=
    isFractionRing_localization_of_artinian (Q := FractionRing A) P.primeCompl
  have : IsLocalization (IsLocalization.localizationLocalizationSubmodule (nonZeroDivisors A)
      (Algebra.algebraMapSubmonoid (FractionRing A) P.primeCompl))
      (Localization (Algebra.algebraMapSubmonoid (FractionRing A) P.primeCompl)) :=
    IsLocalization.localization_localization_isLocalization _ _ _
  obtain ⟨E, hE⟩ := hloc P hP (D.localization P.primeCompl (Localization.AtPrime P))
  exact exists_smul_mem_integralClosure P (Localization.AtPrime P)
    (Localization (Algebra.algebraMapSubmonoid (FractionRing A) P.primeCompl)) D
    (IsLocalization.localizationLocalizationSubmodule (nonZeroDivisors A)
      (Algebra.algebraMapSubmonoid (FractionRing A) P.primeCompl))
    E hE (z : FractionRing A) z.2

end Main

end Stacks.DerivationExtension

end
