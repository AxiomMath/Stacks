module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.Prod
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import StacksFrontier.RingTheory.Localization.IntegralMaximalIdeals

/-!
# The maximal spectrum of an integral extension, fibred over the base

Let `R → T` be an integral ring map and let `p` be a maximal ideal of `R`. The *semilocalization*
of `T` at `p` is the localization `L` of `T` at the image of the complement of `p`; it is an
algebra over `R_p`, finite over `R_p` whenever `T` is finite over `R`, and its maximal ideals are
exactly the maximal ideals of `T` lying over `p`. The local ring of `L` at such a maximal ideal is
the local ring of `T` at the prime below it.

Consequently, for an integral extension `B → C` the maximal spectrum of `C` is the disjoint union,
over the maximal ideals `𝔮` of `B`, of the maximal spectra of the semilocalizations `C_𝔮`, and a
product over the maximal ideals of `C` factors as an iterated product over the fibres.

## Main definitions

* `Stacks.Localization.maximalSpectrumUnder` — the maximal ideal of `B` below a maximal ideal of
  an integral extension.
* `Stacks.Localization.maximalSpectrumEquiv` — the maximal ideals of the semilocalization at `p`
  are the maximal ideals of `T` lying over `p`.
* `Stacks.Localization.maximalSpectrumSigmaEquiv` — the resulting fibred decomposition of
  `MaximalSpectrum C`.
* `Stacks.Localization.localizationAtPrimeUnderAlgEquivOfIsLocalization` — for any model of the
  localization of the semilocalization at a prime, the identification with the localization of `T`
  at the prime below it, as `T`-algebras.
* `Stacks.Localization.localizationAtPrimeUnderAlgEquiv` — the local ring of the semilocalization
  at a maximal ideal is the local ring of `C` at the prime below it.

## Main results

* `Stacks.Localization.isMaximal_under_of_isMaximal` — a maximal ideal of the semilocalization
  contracts to a maximal ideal of `T`.
* `Stacks.Localization.isLocalization_atPrime_under` — localizing the semilocalization at a prime
  localizes `T` at the prime below it.
* `Stacks.Localization.finite_maximalSpectrum_semilocalization` — a semilocalization of a finite
  extension has finitely many maximal ideals.
* `Stacks.Localization.krullDimLE_one_localizationAtPrime` — localizing a ring of Krull dimension
  at most one at a prime leaves the dimension at most one.
* `Stacks.Localization.prod_maximalSpectrum_eq_prod_prod` — a product over the maximal ideals of
  `C` as an iterated product over the fibres.
* `Stacks.Localization.nontrivial_maximalSpectrum_prod` — a fibre can have more than one element:
  over a maximal ideal `𝔮` of `B` the split extension `B × B` has the two distinct maximal ideals
  `𝔮 × B` and `B × 𝔮`.

## Implementation notes

Finiteness of the semilocalization over `R_p` is a Mathlib `Module.Finite` instance for
`Localization (Algebra.algebraMapSubmonoid T p.primeCompl)` over `Localization.AtPrime p`, and is
not restated here. The two halves of the maximal-ideal correspondence are
`IsLocalization.isMaximal_map_of_under_eq` and `IsLocalization.under_under_eq_of_isMaximal`; what
is added is the maximality in `T` of the contracted ideal, which needs `p` maximal rather than
merely prime, and the assembly of the two halves into a bijection.

## References

* [Stacks Project, Tag 00GS](https://stacks.math.columbia.edu/tag/00GS)
* [Stacks Project, Tag 02M0](https://stacks.math.columbia.edu/tag/02M0)
-/

@[expose] public section

namespace Stacks.Localization

section Semilocalization

variable {R T L : Type*} [CommRing R] [CommRing T] [CommRing L]
  [Algebra R T] [Algebra T L] [Algebra R L] [IsScalarTower R T L]
  (p : Ideal R) [p.IsMaximal]
  [IsLocalization (Algebra.algebraMapSubmonoid T p.primeCompl) L]
  [Algebra.IsIntegral R T]

include p in
/-- A maximal ideal of the semilocalization of `T` at a maximal ideal `p` of `R` contracts to a
maximal ideal of `T`: the contraction lies over `p`, which is maximal, and `T` is integral
over `R`. -/
theorem isMaximal_under_of_isMaximal (Q : Ideal L) [Q.IsMaximal] : (Q.under T).IsMaximal := by
  have h : Ideal.under R (Q.under T) = p := IsLocalization.under_under_eq_of_isMaximal p Q
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) (Q.under T)
    (h ▸ ‹p.IsMaximal› : (Ideal.under R (Q.under T)).IsMaximal)

/-- **The maximal ideals of a semilocalization.** For an integral extension `R → T` and a maximal
ideal `p` of `R`, the maximal ideals of the localization `L` of `T` at the image of the complement
of `p` are exactly the maximal ideals of `T` lying over `p`. -/
def maximalSpectrumEquiv :
    MaximalSpectrum L ≃ {r : MaximalSpectrum T // r.asIdeal.under R = p} where
  toFun Q := ⟨⟨Q.asIdeal.under T, isMaximal_under_of_isMaximal p Q.asIdeal⟩,
    IsLocalization.under_under_eq_of_isMaximal p Q.asIdeal⟩
  invFun r :=
    letI : r.1.asIdeal.IsPrime := r.1.isMaximal.isPrime
    ⟨r.1.asIdeal.map (algebraMap T L), IsLocalization.isMaximal_map_of_under_eq p r.2⟩
  left_inv Q := MaximalSpectrum.ext
    (IsLocalization.map_under (Algebra.algebraMapSubmonoid T p.primeCompl) L Q.asIdeal)
  right_inv r := Subtype.ext (MaximalSpectrum.ext
    (IsLocalization.under_map_of_isPrime_disjoint
      (Algebra.algebraMapSubmonoid T p.primeCompl) L r.1.isMaximal.isPrime
      (IsLocalization.disjoint_algebraMapSubmonoid_of_under_eq p r.2)))

/-- The maximal ideal of `T` corresponding to a maximal ideal `Q` of the semilocalization is the
contraction of `Q` to `T`. -/
@[simp]
theorem maximalSpectrumEquiv_apply_asIdeal (Q : MaximalSpectrum L) :
    ((maximalSpectrumEquiv p Q : {r : MaximalSpectrum T // r.asIdeal.under R = p}) :
      MaximalSpectrum T).asIdeal = Q.asIdeal.under T := rfl

end Semilocalization

section LocalRing

variable {R T L : Type*} [CommRing R] [CommRing T] [CommRing L]
  [Algebra R T] [Algebra T L] (p : Ideal R) [p.IsPrime]
  [IsLocalization (Algebra.algebraMapSubmonoid T p.primeCompl) L]

include p in
/-- **Localizing a semilocalization at a prime localizes the base at the prime below it.** The
localization of `L` at a prime `Q` is the localization of `T` at `Q ∩ T`. -/
theorem isLocalization_atPrime_under (Q : Ideal L) [Q.IsPrime] (W : Type*) [CommRing W]
    [Algebra T W] [Algebra L W] [IsScalarTower T L W] [IsLocalization.AtPrime W Q] :
    IsLocalization.AtPrime W (Q.under T) :=
  IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (Algebra.algebraMapSubmonoid T p.primeCompl) W Q

include p in
/-- **The local ring of a semilocalization at a prime, as an algebra over the base.** For any
model `W` of the localization of `L` at a prime `Q` the canonical map identifies `W` with the
localization of `T` at `Q ∩ T`, as `T`-algebras. No integrality is needed: the only input is that
`L` is a localization of `T` at the image of the complement of `p`. -/
noncomputable def localizationAtPrimeUnderAlgEquivOfIsLocalization (Q : Ideal L) [Q.IsPrime]
    (W : Type*) [CommRing W] [Algebra T W] [Algebra L W] [IsScalarTower T L W]
    [IsLocalization.AtPrime W Q] :
    Localization.AtPrime (Q.under T) ≃ₐ[T] W :=
  letI := isLocalization_atPrime_under (T := T) p Q W
  IsLocalization.algEquiv (Q.under T).primeCompl (Localization.AtPrime (Q.under T)) W

end LocalRing

section KrullDimension

/-- **Localizing does not raise the Krull dimension bound.** The localization of a ring of Krull
dimension at most one at a prime has Krull dimension at most one, that dimension being the height
of the prime. -/
theorem krullDimLE_one_localizationAtPrime {R : Type*} [CommRing R] [Ring.KrullDimLE 1 R]
    (p : Ideal R) [p.IsPrime] : Ring.KrullDimLE 1 (Localization.AtPrime p) := by
  rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p)]
  exact le_trans Ideal.height_le_ringKrullDim_of_isPrime
    (Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 R))

end KrullDimension

section Fibre

variable (B : Type*) [CommRing B] (C : Type*) [CommRing C] [Algebra B C]
  [Algebra.IsIntegral B C]

/-- The maximal ideal of `B` below a maximal ideal of an integral extension `C`. -/
def maximalSpectrumUnder (r : MaximalSpectrum C) : MaximalSpectrum B :=
  ⟨r.asIdeal.under B, Ideal.isMaximal_under_of_isIntegral_of_isMaximal r.asIdeal⟩

/-- The maximal ideal of `B` below a maximal ideal `r` of `C` is the contraction of `r` to `B`. -/
@[simp]
theorem maximalSpectrumUnder_asIdeal (r : MaximalSpectrum C) :
    (maximalSpectrumUnder B C r).asIdeal = r.asIdeal.under B := rfl

/-- **A semilocalization of a finite extension is semilocal.** Its maximal ideals are the maximal
ideals of `C` lying over `𝔮`, and a finite extension has only finitely many primes over a given
prime. -/
theorem finite_maximalSpectrum_semilocalization [Module.Finite B C] (q : MaximalSpectrum B) :
    Finite (MaximalSpectrum
      (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))) := by
  let := q.isMaximal
  let := (Algebra.QuasiFinite.finite_primesOver (S := C) q.asIdeal).to_subtype
  have hsub : Finite {r : MaximalSpectrum C // r.asIdeal.under B = q.asIdeal} :=
    Finite.of_injective
      (fun r => (⟨r.1.asIdeal, r.1.isMaximal.isPrime, ⟨r.2.symm⟩⟩ :
        q.asIdeal.primesOver C))
      fun r r' h => Subtype.ext (MaximalSpectrum.ext (congrArg Subtype.val h))
  exact Finite.of_equiv _ (maximalSpectrumEquiv (T := C)
    (L := Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)) q.asIdeal).symm

/-- **The fibred decomposition of the maximal spectrum of an integral extension.** The maximal
ideals of `C` are the disjoint union, over the maximal ideals `𝔮` of `B`, of the maximal ideals of
the semilocalization of `C` at `𝔮`. -/
def maximalSpectrumSigmaEquiv :
    (Σ q : MaximalSpectrum B,
        MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))) ≃
      MaximalSpectrum C :=
  (Equiv.sigmaCongrRight fun q =>
      letI := q.isMaximal
      (maximalSpectrumEquiv (T := C)
          (L := Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))
          q.asIdeal).trans
        (Equiv.subtypeEquivRight fun _ =>
          ⟨fun h => MaximalSpectrum.ext h, fun h => congrArg MaximalSpectrum.asIdeal h⟩)).trans
    (Equiv.sigmaFiberEquiv (maximalSpectrumUnder B C))

/-- The maximal ideal of `C` corresponding to a maximal ideal `v` of the semilocalization of `C`
at `q` is the contraction of `v` to `C`. -/
@[simp]
theorem maximalSpectrumSigmaEquiv_asIdeal (q : MaximalSpectrum B)
    (v : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))) :
    (maximalSpectrumSigmaEquiv B C ⟨q, v⟩).asIdeal = v.asIdeal.under C := rfl

/-- **A product over the maximal ideals of `C` as an iterated product over the fibres.** -/
theorem prod_maximalSpectrum_eq_prod_prod {M : Type*} [CommMonoid M]
    [Fintype (MaximalSpectrum B)] [Fintype (MaximalSpectrum C)]
    [∀ q : MaximalSpectrum B,
      Fintype (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C
        q.asIdeal.primeCompl)))]
    (f : MaximalSpectrum C → M) :
    ∏ r : MaximalSpectrum C, f r =
      ∏ q : MaximalSpectrum B,
        ∏ v : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C
          q.asIdeal.primeCompl)), f (maximalSpectrumSigmaEquiv B C ⟨q, v⟩) := by
  rw [← Fintype.prod_equiv (maximalSpectrumSigmaEquiv B C)
    (fun x => f (maximalSpectrumSigmaEquiv B C x)) f fun _ => rfl]
  exact Fintype.prod_sigma _

omit [Algebra.IsIntegral B C] in
/-- **The local ring of a semilocalization at a maximal ideal.** It is the local ring of `C` at the
prime of `C` below that maximal ideal. Integrality of `C` over `B` plays no part: this is
`Stacks.Localization.localizationAtPrimeUnderAlgEquivOfIsLocalization` for the canonical model of
the semilocalization. -/
noncomputable def localizationAtPrimeUnderAlgEquiv (q : MaximalSpectrum B)
    (v : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))) :
    Localization.AtPrime (v.asIdeal.under C) ≃ₐ[C] Localization.AtPrime v.asIdeal :=
  letI := q.isMaximal
  localizationAtPrimeUnderAlgEquivOfIsLocalization (R := B) (T := C)
    (p := q.asIdeal) (Q := v.asIdeal) (W := Localization.AtPrime v.asIdeal)

end Fibre

section SplitFibre

variable {B : Type*} [CommRing B] (q : Ideal B) [q.IsMaximal]

private theorem comap_prod_top (J : Ideal B) :
    (Ideal.prod J (⊤ : Ideal B)).comap (algebraMap B (B × B)) = J := by
  ext b; simp [Ideal.mem_prod]

private theorem comap_top_prod (J : Ideal B) :
    (Ideal.prod (⊤ : Ideal B) J).comap (algebraMap B (B × B)) = J := by
  ext b; simp [Ideal.mem_prod]

/-- In the split extension `B → B × B` the ideal `𝔮 × B` is maximal: it is prime, and it
contracts to the maximal ideal `𝔮` along the diagonal. -/
theorem isMaximal_prod_top : (Ideal.prod q (⊤ : Ideal B)).IsMaximal := by
  let : (Ideal.prod q (⊤ : Ideal B)).IsPrime := Ideal.isPrime_ideal_prod_top
  refine Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := B) _ ?_
  rw [Ideal.under_def, comap_prod_top q]; infer_instance

/-- In the split extension `B → B × B` the ideal `B × 𝔮` is maximal. -/
theorem isMaximal_top_prod : (Ideal.prod (⊤ : Ideal B) q).IsMaximal := by
  let : (Ideal.prod (⊤ : Ideal B) q).IsPrime := Ideal.isPrime_ideal_prod_top'
  refine Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := B) _ ?_
  rw [Ideal.under_def, comap_top_prod q]; infer_instance

/-- **A fibre of the decomposition can have more than one element.** Over a maximal ideal `𝔮` of
`B` the split extension `B × B` has the two distinct maximal ideals `𝔮 × B` and `B × 𝔮`, so the
semilocalization of `B × B` at `𝔮` has at least two maximal ideals. -/
theorem nontrivial_maximalSpectrum_prod :
    Nontrivial (MaximalSpectrum
      (Localization (Algebra.algebraMapSubmonoid (B × B) q.primeCompl))) := by
  set e := maximalSpectrumEquiv (R := B) (T := B × B)
    (L := Localization (Algebra.algebraMapSubmonoid (B × B) q.primeCompl)) q with he
  have hqtop : q ≠ ⊤ := ‹q.IsMaximal›.ne_top
  refine ⟨e.symm ⟨⟨_, isMaximal_prod_top q⟩, comap_prod_top q⟩,
    e.symm ⟨⟨_, isMaximal_top_prod q⟩, comap_top_prod q⟩, ?_⟩
  intro hcontra
  have h := congrArg MaximalSpectrum.asIdeal
    (congrArg Subtype.val (e.symm.injective hcontra))
  exact hqtop (Ideal.prod_inj.mp h).2.symm

end SplitFibre

end Stacks.Localization

end
