module

public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import StacksFrontier.RingTheory.Length.RingEquiv

/-!
# Transporting the data of a chart along a ring isomorphism

The colength drop of [Stacks, Tag 0AGT] is proved in the sibling file
`CartierDescent.Colength.ColengthChain` for the chart read as a subalgebra
`Algebra.adjoin R {y / x}` of the fraction field of `R`, because that is where the two charts can
be compared with one another. The scheme-theoretic chart, by contrast, is the spectrum of the
affine blowup algebra `affineBlowup I x`, a subalgebra of the away-localization `R_x`. The two
are isomorphic as `R`-algebras by
`Stacks.ResolutionOfSurfaces.CartierDescent.affineBlowupSpanPairEquivAdjoin`, and this file
carries the data of a chart along such an isomorphism: the residual ideal, the chart equation,
the Artinian hypothesis on the residual quotient, non-invertibility of the chart generator, the
finite set of primes above the residual ideal, and — the only one that is not formal — the
colength of the residual ideal in a local ring.

## Main results

* `Module.quotient_length_eq_of_ringEquiv_commutes`: the length over a fixed base ring of the
  quotient by an ideal is unchanged by an isomorphism of algebras over that base.
* `Stacks.ResolutionOfSurfaces.CartierDescent.length_localization_quotient_eq_of_ringEquiv`: the
  local colength of an ideal at a prime equals the local colength of its image at the
  corresponding prime.
* `Stacks.ResolutionOfSurfaces.CartierDescent.length_localization_quotient_eq_of_commutes`: the
  same with the ring of scalars held fixed at a common base ring, for an isomorphism of algebras
  over it.
* `Stacks.ResolutionOfSurfaces.CartierDescent.sum_length_localization_quotient_map_eq_of_commutes`:
  the same summed over a finite family of primes and its image.
* `Stacks.ResolutionOfSurfaces.CartierDescent.mem_map_comapEquiv_iff`: the primes above the
  image of an ideal are the images of the primes above it.
* `Stacks.ResolutionOfSurfaces.CartierDescent.span_pow_mul_map_eq_map_of_commutes`: the chart
  equation `(ξ ^ d)·Rx = L·B` transports.
* `Stacks.ResolutionOfSurfaces.CartierDescent.not_isUnit_algebraMap_of_commutes`: so does
  non-invertibility of the chart generator.
* `Stacks.ResolutionOfSurfaces.CartierDescent.isArtinianRing_quotient_map_of_ringEquiv`: so does
  the Artinian hypothesis on the residual quotient.

## Implementation notes

The prime of `B₂` matching a prime `w` of `B₁` is written `PrimeSpectrum.comapEquiv e w` rather
than `Ideal.map e w.asIdeal`: that spelling is a prime on the nose, with no instance to supply,
and `Ideal.map_le_iff_le_comap` is then the only fact needed to compare the two sets of primes
above an ideal. The matching of finite families is `Finset.map` along the induced equivalence of
spectra, which needs no `DecidableEq` on either spectrum.

The colength transport is the composite of two Mathlib facts. The isomorphism `e` carries the
prime complement of `w` to that of the matching prime, so
`IsLocalization.ringEquivOfRingEquiv` produces an isomorphism of the two local rings commuting
with the structure maps; `Ideal.map_map` then identifies the two extended ideals, and
`Module.quotient_length_eq_of_ringEquiv` transports the length, the base ring moving with it.

## References

* [Stacks Project, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
-/

@[expose] public noncomputable section

universe u

namespace Module

/-- **The colength of an ideal over a fixed base ring is unchanged by an isomorphism of algebras
over that base.** If `e : S₁ ≃+* S₂` commutes with the structure maps of a common base ring `R`,
then the `R`-lengths of the quotients by an ideal and by its image agree, the base ring staying
put.

Unlike `Module.quotient_length_eq_of_ringEquiv`, which carries the base ring along with the
module, this is a statement about one fixed ring of scalars acting on both quotients through
`e`. -/
public theorem quotient_length_eq_of_ringEquiv_commutes {R S₁ S₂ : Type*} [CommRing R]
    [CommRing S₁] [CommRing S₂] [Algebra R S₁] [Algebra R S₂] (e : S₁ ≃+* S₂)
    (he : ∀ r : R, e (algebraMap R S₁ r) = algebraMap R S₂ r) (I : Ideal S₁) :
    Module.length R (S₁ ⧸ I) = Module.length R (S₂ ⧸ Ideal.map (e : S₁ →+* S₂) I) := by
  let eQ := Ideal.quotientEquiv I (Ideal.map (e : S₁ →+* S₂) I) e rfl
  let f : (S₁ ⧸ I) ≃ₗ[R] (S₂ ⧸ Ideal.map (e : S₁ →+* S₂) I) :=
    { toFun := eQ
      map_add' := eQ.map_add
      map_smul' := by
        intro r z
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
        show eQ (r • Ideal.Quotient.mk I a) = r • eQ (Ideal.Quotient.mk I a)
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        refine congrArg (· * eQ (Ideal.Quotient.mk I a)) ?_
        show eQ (Ideal.Quotient.mk I (algebraMap R S₁ r)) =
          Ideal.Quotient.mk (Ideal.map (e : S₁ →+* S₂) I) (algebraMap R S₂ r)
        rw [Ideal.quotientEquiv_mk, he r]
      invFun := eQ.symm
      left_inv := eQ.left_inv
      right_inv := eQ.right_inv }
  exact f.length_eq

end Module

namespace Stacks.ResolutionOfSurfaces.CartierDescent

variable {B₁ B₂ : Type u} [CommRing B₁] [CommRing B₂]

/-- A ring isomorphism carries the prime complement of a prime to the prime complement of the
matching prime. -/
private theorem map_primeCompl (e : B₁ ≃+* B₂) (w : PrimeSpectrum B₁) :
    Submonoid.map e.toMonoidHom w.asIdeal.primeCompl =
      (Ideal.comap (e.symm : B₂ →+* B₁) w.asIdeal).primeCompl := by
  ext z
  simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff, Ideal.mem_comap]
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa using hu
  · intro h
    exact ⟨e.symm z, h, by simp⟩

/-- A ring isomorphism induces an isomorphism of the local rings at matching primes, compatible
with the maps from `B₁` and `B₂` and carrying extended ideals to extended ideals. -/
private theorem exists_localization_ringEquiv_map_eq (e : B₁ ≃+* B₂) (w : PrimeSpectrum B₁) :
    ∃ φ : Localization.AtPrime w.asIdeal ≃+*
        Localization.AtPrime (PrimeSpectrum.comapEquiv e w).asIdeal,
      (∀ z : B₁, φ (algebraMap B₁ (Localization.AtPrime w.asIdeal) z) =
        algebraMap B₂ (Localization.AtPrime (PrimeSpectrum.comapEquiv e w).asIdeal) (e z)) ∧
      ∀ I : Ideal B₁, Ideal.map (φ : Localization.AtPrime w.asIdeal →+*
            Localization.AtPrime (PrimeSpectrum.comapEquiv e w).asIdeal)
          (Ideal.map (algebraMap B₁ (Localization.AtPrime w.asIdeal)) I) =
        Ideal.map (algebraMap B₂ (Localization.AtPrime (PrimeSpectrum.comapEquiv e w).asIdeal))
          (Ideal.map (e : B₁ →+* B₂) I) := by
  have hH : Submonoid.map e.toMonoidHom w.asIdeal.primeCompl =
      (PrimeSpectrum.comapEquiv e w).asIdeal.primeCompl := map_primeCompl e w
  let φ := IsLocalization.ringEquivOfRingEquiv (M := w.asIdeal.primeCompl)
    (Localization.AtPrime w.asIdeal)
    (Localization.AtPrime (PrimeSpectrum.comapEquiv e w).asIdeal) e hH
  have hcomp : ∀ z : B₁, φ (algebraMap B₁ (Localization.AtPrime w.asIdeal) z) =
      algebraMap B₂ (Localization.AtPrime (PrimeSpectrum.comapEquiv e w).asIdeal) (e z) :=
    IsLocalization.ringEquivOfRingEquiv_eq hH
  refine ⟨φ, hcomp, fun I => ?_⟩
  rw [Ideal.map_map, Ideal.map_map]
  exact congrArg (Ideal.map · I) (RingHom.ext hcomp)

/-- **The local colength of an ideal is unchanged by a ring isomorphism.** For `e : B₁ ≃+* B₂`,
an ideal `I` of `B₁` and a prime `w` of `B₁`, the colength of `I` in the local ring of `B₁` at
`w` is the colength of the image of `I` in the local ring of `B₂` at the matching prime. -/
public theorem length_localization_quotient_eq_of_ringEquiv (e : B₁ ≃+* B₂) (I : Ideal B₁)
    (w : PrimeSpectrum B₁) :
    Module.length (Localization.AtPrime w.asIdeal)
        (Localization.AtPrime w.asIdeal ⧸
          Ideal.map (algebraMap B₁ (Localization.AtPrime w.asIdeal)) I) =
      Module.length (Localization.AtPrime (PrimeSpectrum.comapEquiv e w).asIdeal)
        (Localization.AtPrime (PrimeSpectrum.comapEquiv e w).asIdeal ⧸
          Ideal.map (algebraMap B₂
              (Localization.AtPrime (PrimeSpectrum.comapEquiv e w).asIdeal))
            (Ideal.map (e : B₁ →+* B₂) I)) := by
  obtain ⟨φ, -, hmap⟩ := exists_localization_ringEquiv_map_eq e w
  rw [Module.quotient_length_eq_of_ringEquiv φ
    (Ideal.map (algebraMap B₁ (Localization.AtPrime w.asIdeal)) I)]
  exact congrArg (fun J => Module.length _ (_ ⧸ J)) (hmap I)

/-- **The local colength of an ideal over a base ring is unchanged by an isomorphism of algebras
over that base.** For an isomorphism `e : B₁ ≃+* B₂` of `R`-algebras commuting with the structure
maps, an ideal `I` of `B₁` and a prime `w` of `B₁`, the `R`-length of the quotient of the local
ring of `B₁` at `w` by `I` is the `R`-length of the corresponding quotient for the image of `I` at
the matching prime.

This is `Stacks.ResolutionOfSurfaces.CartierDescent.length_localization_quotient_eq_of_ringEquiv`
with the ring of scalars held fixed at `R` on both sides, which is what a colength computation
over the base of the two charts needs. -/
public theorem length_localization_quotient_eq_of_commutes {R : Type u} [CommRing R]
    [Algebra R B₁] [Algebra R B₂] (e : B₁ ≃+* B₂)
    (hc : ∀ r : R, e (algebraMap R B₁ r) = algebraMap R B₂ r) (I : Ideal B₁)
    (w : PrimeSpectrum B₁) :
    Module.length R (Localization.AtPrime w.asIdeal ⧸
        Ideal.map (algebraMap B₁ (Localization.AtPrime w.asIdeal)) I) =
      Module.length R (Localization.AtPrime (PrimeSpectrum.comapEquiv e w).asIdeal ⧸
        Ideal.map (algebraMap B₂
            (Localization.AtPrime (PrimeSpectrum.comapEquiv e w).asIdeal))
          (Ideal.map (e : B₁ →+* B₂) I)) := by
  obtain ⟨φ, hcomp, hmap⟩ := exists_localization_ringEquiv_map_eq e w
  have hcommutes : ∀ r : R, φ (algebraMap R (Localization.AtPrime w.asIdeal) r) =
      algebraMap R (Localization.AtPrime (PrimeSpectrum.comapEquiv e w).asIdeal) r := by
    intro r
    rw [IsScalarTower.algebraMap_apply R B₁ (Localization.AtPrime w.asIdeal), hcomp, hc r,
      ← IsScalarTower.algebraMap_apply R B₂]
  rw [Module.quotient_length_eq_of_ringEquiv_commutes φ hcommutes
    (Ideal.map (algebraMap B₁ (Localization.AtPrime w.asIdeal)) I), hmap I]

/-- **A family of local colengths over a base ring transports along an isomorphism of algebras
over that base.** The sum over a family of primes of `B₁` equals the sum over the matching family
of primes of `B₂`, for the image ideal.

The statement is recorded for abstract `B₁`, `B₂` because that is where it can be *used*: at the
chart of a blowup the modules carry the prime through `PrimeSpectrum.comapEquiv`, and
synthesising the base-ring module structure on a localization at such a prime exhausts the
instance budget, whereas here the prime is a variable. -/
public theorem sum_length_localization_quotient_map_eq_of_commutes {R : Type u} [CommRing R]
    [Algebra R B₁] [Algebra R B₂] (e : B₁ ≃+* B₂)
    (hc : ∀ r : R, e (algebraMap R B₁ r) = algebraMap R B₂ r) (I : Ideal B₁)
    (S : Finset (PrimeSpectrum B₁)) :
    ∑ v ∈ S, Module.length R (Localization.AtPrime v.asIdeal ⧸
        Ideal.map (algebraMap B₁ (Localization.AtPrime v.asIdeal)) I) =
      ∑ w ∈ S.map (PrimeSpectrum.comapEquiv e).toEquiv.toEmbedding,
        Module.length R (Localization.AtPrime w.asIdeal ⧸
          Ideal.map (algebraMap B₂ (Localization.AtPrime w.asIdeal))
            (Ideal.map (e : B₁ →+* B₂) I)) := by
  rw [Finset.sum_map]
  exact Finset.sum_congr rfl fun v _ => length_localization_quotient_eq_of_commutes e hc I v

/-- **The primes above the image of an ideal are the images of the primes above it.** For
`e : B₁ ≃+* B₂` and an ideal `I` of `B₁`, a prime `p` of `B₂` contains `Ideal.map e I` exactly
when it is the image of a prime of `B₁` containing `I` under the induced equivalence of
spectra. -/
public theorem mem_map_comapEquiv_iff (e : B₁ ≃+* B₂) (I : Ideal B₁)
    (Sx : Finset (PrimeSpectrum B₁))
    (hSx : ∀ w : PrimeSpectrum B₁, w ∈ Sx ↔ I ≤ w.asIdeal) (p : PrimeSpectrum B₂) :
    p ∈ Sx.map (PrimeSpectrum.comapEquiv e).toEquiv.toEmbedding ↔
      Ideal.map (e : B₁ →+* B₂) I ≤ p.asIdeal := by
  have hcomap : ∀ q : PrimeSpectrum B₂, ((PrimeSpectrum.comapEquiv e).symm q).asIdeal =
      Ideal.comap (e : B₁ →+* B₂) q.asIdeal := fun _ => rfl
  rw [Finset.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine Ideal.map_le_iff_le_comap.2 ?_
    have hback : ((PrimeSpectrum.comapEquiv e).symm
        ((PrimeSpectrum.comapEquiv e).toEquiv.toEmbedding w)) = w :=
      (PrimeSpectrum.comapEquiv e).symm_apply_apply w
    rw [← hcomap, hback]
    exact (hSx w).1 hw
  · exact fun hp => ⟨(PrimeSpectrum.comapEquiv e).symm p,
      (hSx _).2 (Ideal.map_le_iff_le_comap.1 hp), (PrimeSpectrum.comapEquiv e).apply_symm_apply p⟩

/-- **The chart equation transports along an isomorphism of `R`-algebras.** If
`(ξ ^ d)·I = L·B₁` with `ξ` the image of `x : R`, then the same holds for the image of `I` in
`B₂`. -/
public theorem span_pow_mul_map_eq_map_of_commutes {R : Type u} [CommRing R] [Algebra R B₁]
    [Algebra R B₂] (e : B₁ ≃+* B₂)
    (hc : ∀ r : R, e (algebraMap R B₁ r) = algebraMap R B₂ r) (x : R) (d : ℕ) (I : Ideal B₁)
    (L : Ideal R)
    (h : Ideal.span {algebraMap R B₁ x ^ d} * I = Ideal.map (algebraMap R B₁) L) :
    Ideal.span {algebraMap R B₂ x ^ d} * Ideal.map (e : B₁ →+* B₂) I =
      Ideal.map (algebraMap R B₂) L := by
  have hgen : (e : B₁ →+* B₂) (algebraMap R B₁ x ^ d) = algebraMap R B₂ x ^ d := by
    rw [map_pow]
    exact congrArg (· ^ d) (hc x)
  have halg : (e : B₁ →+* B₂).comp (algebraMap R B₁) = algebraMap R B₂ :=
    RingHom.ext hc
  calc Ideal.span {algebraMap R B₂ x ^ d} * Ideal.map (e : B₁ →+* B₂) I
      = Ideal.map (e : B₁ →+* B₂) (Ideal.span {algebraMap R B₁ x ^ d} * I) := by
        rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton, hgen]
    _ = Ideal.map (e : B₁ →+* B₂) (Ideal.map (algebraMap R B₁) L) := congrArg _ h
    _ = Ideal.map (algebraMap R B₂) L := by rw [Ideal.map_map, halg]

/-- **Non-invertibility of the chart generator transports.** -/
public theorem not_isUnit_algebraMap_of_commutes {R : Type u} [CommRing R] [Algebra R B₁]
    [Algebra R B₂] (e : B₁ ≃+* B₂)
    (hc : ∀ r : R, e (algebraMap R B₁ r) = algebraMap R B₂ r) (x : R)
    (h : ¬ IsUnit (algebraMap R B₁ x)) : ¬ IsUnit (algebraMap R B₂ x) := by
  rwa [← hc x, isUnit_map_iff]

/-- **The Artinian hypothesis on a residual quotient transports.** -/
public theorem isArtinianRing_quotient_map_of_ringEquiv (e : B₁ ≃+* B₂) (I : Ideal B₁)
    [IsArtinianRing (B₁ ⧸ I)] : IsArtinianRing (B₂ ⧸ Ideal.map (e : B₁ →+* B₂) I) :=
  (Ideal.quotientEquiv I (Ideal.map (e : B₁ →+* B₂) I) e rfl).isArtinianRing

end Stacks.ResolutionOfSurfaces.CartierDescent

end
