module

public import StacksFrontier.RingTheory.Artinian.TFAE
public import StacksFrontier.RingTheory.KrullDimension.DimensionOneNoetherianLocal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Characterizations of Artinian rings, in the source's literal form

Let `R` be a commutative ring. The ten conditions of [StackProject 00KJ] are equivalent: `R` is
Artinian; `R` is Noetherian of dimension zero; `R` has finite length over itself; `R` is a finite
product of Artinian local rings; `R` is Noetherian with finite discrete prime spectrum; `R` is a
finite product of Noetherian local rings of dimension `0`; `R` is a finite product of Noetherian
local rings `R_i` with `d(R_i) = 0`; `R` is a finite product of Noetherian local rings with
nilpotent maximal ideals; `R` is Noetherian with finitely many maximal ideals and nilpotent
Jacobson radical; and `R` is Noetherian with no strict inclusions among its primes.

## Main results

* `isArtinianRing_tfae_hilbertSamuelDegree`: the ten conditions, each in the source's form, are
  equivalent.
* `isArtinianRing_iff_isNoetherianRing_and_ringKrullDim_eq_zero`: for a nonzero ring, being
  Artinian is being Noetherian with `ringKrullDim R = 0`, the literal `dim(R) = 0`.

## Implementation notes

The equivalence is deduced from `isArtinianRing_tfae`, whose items (1)-(4) and (8)-(10) are
taken over unchanged, by three equivalences of conditions:

* item (5) is `Spec(R)` *finite* and discrete; a discrete prime spectrum is finite because it is
  quasi-compact (`PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero`);
* item (6) asks `ringKrullDim (S i) = 0` of each factor; a local ring is nonzero, and for a
  nonzero ring this is `Ring.KrullDimLE 0` (`ringKrullDimZero_iff_ringKrullDim_eq_zero`);
* item (7) asks of each factor that it be Noetherian with `d(S i) = 0`, where
  `d = Module.hilbertSamuelDegree` is the invariant of Definition [StackProject 00KA]; for a
  Noetherian local ring this is dimension zero by Lemma [StackProject 00KI]
  (`IsLocalRing.ringKrullDim_eq_zero_iff_hilbertSamuelDegree_eq_zero`), hence Artinianness.

Item (2) is `IsNoetherianRing R ∧ Ring.KrullDimLE 0 R`, that is `ringKrullDim R ≤ 0`. The source's
`dim(R) = 0` is this for every nonzero ring
(`isArtinianRing_iff_isNoetherianRing_and_ringKrullDim_eq_zero`); for the zero ring the source's
own convention (Topology, Definition 0055) gives `dim = -∞`, so the literal equality would make
item (2) fail for the zero ring while item (1) holds. The `≤ 0` form is the correction.

## References

* [StackProject 00KJ](https://stacks.math.columbia.edu/tag/00KJ)
-/

@[expose] public section

universe u

namespace Stacks.Artinian.Characterizations

/-- A local ring has Krull dimension at most zero exactly when its Krull dimension is zero. -/
private theorem krullDimLE_zero_iff_ringKrullDim_eq_zero (S : Type*) [CommRing S]
    [IsLocalRing S] : Ring.KrullDimLE 0 S ↔ ringKrullDim S = 0 :=
  ringKrullDimZero_iff_ringKrullDim_eq_zero

/-- A local ring is Artinian exactly when it is Noetherian with Hilbert–Samuel degree
`d(S) = 0`. -/
private theorem isArtinianRing_iff_isNoetherianRing_and_hilbertSamuelDegree_eq_zero (S : Type*)
    [CommRing S] [IsLocalRing S] :
    IsArtinianRing S ↔ IsNoetherianRing S ∧ Module.hilbertSamuelDegree S S = 0 := by
  constructor
  · intro h
    have hd := (isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.mp h).2
    exact ⟨inferInstance, IsLocalRing.ringKrullDim_eq_zero_iff_hilbertSamuelDegree_eq_zero.mp
      ((krullDimLE_zero_iff_ringKrullDim_eq_zero S).mp hd)⟩
  · rintro ⟨hN, hd⟩
    exact isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.mpr ⟨hN,
      (krullDimLE_zero_iff_ringKrullDim_eq_zero S).mpr
        (IsLocalRing.ringKrullDim_eq_zero_iff_hilbertSamuelDegree_eq_zero.mpr hd)⟩

end Stacks.Artinian.Characterizations

open Stacks.Artinian.Characterizations

/-- A nonzero commutative ring is Artinian if and only if it is Noetherian of Krull dimension
`0`. -/
theorem isArtinianRing_iff_isNoetherianRing_and_ringKrullDim_eq_zero (R : Type*) [CommRing R]
    [Nontrivial R] : IsArtinianRing R ↔ IsNoetherianRing R ∧ ringKrullDim R = 0 :=
  isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.trans
    (and_congr_right' ringKrullDimZero_iff_ringKrullDim_eq_zero)

/-- Item (2) of Tag 00KJ read with the literal `dim(R) = 0` is false: the zero ring is Artinian,
but its Krull dimension is `⊥ = -∞`. -/
theorem not_forall_isArtinianRing_imp_ringKrullDim_eq_zero :
    ¬ ∀ (R : Type) [CommRing R], IsArtinianRing R → ringKrullDim R = 0 := by
  intro h
  have h0 := h PUnit inferInstance
  rw [ringKrullDim_eq_bot_of_subsingleton] at h0
  exact WithBot.bot_ne_zero h0

/-- **Characterizations of Artinian rings.** For a commutative ring `R` the following are
equivalent: (1) `R` is Artinian; (2) `R` is Noetherian of Krull dimension at most zero; (3) `R`
has finite length as a module over itself; (4) `R` is a finite product of Artinian local rings;
(5) `R` is Noetherian and `Spec(R)` is a finite discrete space; (6) `R` is a finite product of
Noetherian local rings of Krull dimension `0`; (7) `R` is a finite product of Noetherian local
rings `R_i` with Hilbert–Samuel degree `d(R_i) = 0`; (8) `R` is a finite product of Noetherian
local rings with nilpotent maximal ideals; (9) `R` is Noetherian with finitely many maximal
ideals and nilpotent Jacobson radical; and (10) `R` is Noetherian with no strict inclusions among
its prime ideals. -/
@[stacks 00KJ "Items (1)-(10) in the source's order. Item (2) reads `dim(R) = 0` as
`ringKrullDim R ≤ 0` (`Ring.KrullDimLE 0 R`), which is the literal equality for every nonzero
ring (`isArtinianRing_iff_isNoetherianRing_and_ringKrullDim_eq_zero`) and the correct form for
the zero ring, whose dimension is `-∞` by Topology, Definition 0055. In (7), `d(R_i)` is
`Module.hilbertSamuelDegree` of Definition 00KA. A finite product of local rings is a finite
index type and a ring isomorphism `R ≃+* ∀ i, S i`."]
theorem isArtinianRing_tfae_hilbertSamuelDegree (R : Type u) [CommRing R] :
    List.TFAE
      [ IsArtinianRing R,
        IsNoetherianRing R ∧ Ring.KrullDimLE 0 R,
        IsFiniteLength R R,
        ∃ (ι : Type u) (_ : Finite ι) (S : ι → Type u) (_ : ∀ i, CommRing (S i))
          (_ : ∀ i, IsLocalRing (S i)), (∀ i, IsArtinianRing (S i)) ∧ Nonempty (R ≃+* ∀ i, S i),
        IsNoetherianRing R ∧ Finite (PrimeSpectrum R) ∧ DiscreteTopology (PrimeSpectrum R),
        ∃ (ι : Type u) (_ : Finite ι) (S : ι → Type u) (_ : ∀ i, CommRing (S i))
          (_ : ∀ i, IsLocalRing (S i)), (∀ i, IsNoetherianRing (S i) ∧ ringKrullDim (S i) = 0) ∧
            Nonempty (R ≃+* ∀ i, S i),
        ∃ (ι : Type u) (_ : Finite ι) (S : ι → Type u) (_ : ∀ i, CommRing (S i))
          (_ : ∀ i, IsLocalRing (S i)),
          (∀ i, IsNoetherianRing (S i) ∧ Module.hilbertSamuelDegree (S i) (S i) = 0) ∧
            Nonempty (R ≃+* ∀ i, S i),
        ∃ (ι : Type u) (_ : Finite ι) (S : ι → Type u) (_ : ∀ i, CommRing (S i))
          (_ : ∀ i, IsLocalRing (S i)),
          (∀ i, IsNoetherianRing (S i) ∧ IsNilpotent (IsLocalRing.maximalIdeal (S i))) ∧
            Nonempty (R ≃+* ∀ i, S i),
        IsNoetherianRing R ∧ Finite (MaximalSpectrum R) ∧ IsNilpotent (Ring.jacobson R),
        IsNoetherianRing R ∧ ∀ p q : Ideal R, p.IsPrime → q.IsPrime → p ≤ q → p = q ] := by
  have e5 : (IsNoetherianRing R ∧ Finite (PrimeSpectrum R) ∧
      DiscreteTopology (PrimeSpectrum R)) =
      (IsNoetherianRing R ∧ DiscreteTopology (PrimeSpectrum R)) :=
    propext <| and_congr_right' ⟨fun hd ↦ hd.2, fun hd ↦
      ⟨(PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mp hd).1, hd⟩⟩
  have e6 : (∃ (ι : Type u) (_ : Finite ι) (S : ι → Type u) (_ : ∀ i, CommRing (S i))
      (_ : ∀ i, IsLocalRing (S i)), (∀ i, IsNoetherianRing (S i) ∧ ringKrullDim (S i) = 0) ∧
        Nonempty (R ≃+* ∀ i, S i)) =
      (∃ (ι : Type u) (_ : Finite ι) (S : ι → Type u) (_ : ∀ i, CommRing (S i))
        (_ : ∀ i, IsLocalRing (S i)), (∀ i, IsNoetherianRing (S i) ∧ Ring.KrullDimLE 0 (S i)) ∧
          Nonempty (R ≃+* ∀ i, S i)) :=
    propext <| exists_pi_isLocalRing_congr
      (fun S _ _ ↦ IsNoetherianRing S ∧ ringKrullDim S = 0)
      (fun S _ _ ↦ IsNoetherianRing S ∧ Ring.KrullDimLE 0 S)
      fun S _ _ ↦ and_congr_right' (krullDimLE_zero_iff_ringKrullDim_eq_zero S).symm
  have e7 : (∃ (ι : Type u) (_ : Finite ι) (S : ι → Type u) (_ : ∀ i, CommRing (S i))
      (_ : ∀ i, IsLocalRing (S i)),
      (∀ i, IsNoetherianRing (S i) ∧ Module.hilbertSamuelDegree (S i) (S i) = 0) ∧
        Nonempty (R ≃+* ∀ i, S i)) =
      (∃ (ι : Type u) (_ : Finite ι) (S : ι → Type u) (_ : ∀ i, CommRing (S i))
        (_ : ∀ i, IsLocalRing (S i)), (∀ i, IsFiniteLength (S i) (S i)) ∧
          Nonempty (R ≃+* ∀ i, S i)) :=
    propext <| exists_pi_isLocalRing_congr
      (fun S _ _ ↦ IsNoetherianRing S ∧ Module.hilbertSamuelDegree S S = 0)
      (fun S _ _ ↦ IsFiniteLength S S)
      fun S _ _ ↦ (isArtinianRing_iff_isNoetherianRing_and_hilbertSamuelDegree_eq_zero S).symm.trans
        (isArtinianRing_iff_isFiniteLength S)
  rw [e5, e6, e7]
  exact isArtinianRing_tfae R
