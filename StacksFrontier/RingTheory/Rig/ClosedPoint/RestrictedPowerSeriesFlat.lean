module

public import Mathlib.RingTheory.Flat.Localization
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.FlatLocalSquare
public import StacksFrontier.RingTheory.Flat.MvPolynomialAway
public import StacksFrontier.RingTheory.Rig.ClosedPoint.RestrictedPowerSeries
public import StacksFrontier.RingTheory.Rig.Flat
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.RestrictedPowerSeriesMapAdic
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOverAdic

/-!
# Flatness of a restricted power series extension at a rig-closed point

Let `A → B` be a homomorphism of Noetherian adic topological rings, adic for a finitely
generated ideal of definition `I` of `A` and its extension `J = I · B`, and assume `B[1/g]` is
flat over `A` for every topologically nilpotent `g : B`.  Let `q` be a prime of `B{σ}` which is
rig-closed, and such that the three primes it contracts to in `B`, in `A{σ}` and in `A` are
rig-closed as well.  Then `B{σ}_q` is flat over `A{σ}`.

The argument is the square

```
A[σ]_{q ∩ A[σ]} ⟶ A{σ}_{q ∩ A{σ}}
      ↓                  ↓
B[σ]_{q ∩ B[σ]} ⟶ B{σ}_q
```

of local homomorphisms of Noetherian local rings.  Its horizontal arrows induce bijections on
the completions at the maximal ideals, and its left vertical arrow is flat because inverting a
topologically nilpotent element of `B` which is a unit at `q` makes `B[σ]` flat over `A[σ]`; so
the right vertical arrow is flat.

## Main results

* `Rig.flat_atPrime_of_flat_away`: flatness after inverting an element of the target descends
  to flatness after localizing at a prime not containing it.
* `Rig.localRingHom_square`: a commuting square of ring homomorphisms induces a commuting
  square of the local homomorphisms at a prime and its contractions.
* `Rig.flat_localRingHom_mvPolynomialMap`: the left vertical arrow of the square is flat.
* `Rig.flat_atPrime_restrictedPowerSeriesMap`: `B{σ}_q` is flat over `A{σ}`.

## Implementation notes

Flatness is Mathlib's `RingHom.Flat`, so the module structure is the one determined by the
homomorphism; rig-closedness is `Rig.Ideal.IsClosedPointAwayFrom` taken with respect to the
relevant ideal of definition.  The flatness hypothesis on `A → B` is condition (2) of Tag 0GGL,
equivalent to the flatness clause of naive rig-flatness.

## References

* [Stacks Project, Tag 0GGR](https://stacks.math.columbia.edu/tag/0GGR)
* [Stacks Project, Tag 0GGH](https://stacks.math.columbia.edu/tag/0GGH)
* [Stacks Project, Tag 0C4G](https://stacks.math.columbia.edu/tag/0C4G)
* [Stacks Project, Tag 00HI](https://stacks.math.columbia.edu/tag/00HI)
-/

@[expose] public section

namespace RestrictedPowerSeries

/-- A constant polynomial is the corresponding constant restricted power series. -/
public theorem polynomialRingHom_C {A : Type*} [CommRing A] (I : Ideal A) (σ : Type*) (a : A) :
    polynomialRingHom I σ (MvPolynomial.C a) = coefficientRingHom I σ a := rfl

end RestrictedPowerSeries

namespace Rig

section Localization

/-- **Flatness after inverting an element of the target descends to flatness at a prime not
containing it.** -/
public theorem flat_atPrime_of_flat_away {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) (g : B) (q : Ideal B) [hq : q.IsPrime] (hg : g ∉ q)
    (h : _root_.RingHom.Flat ((algebraMap B (Localization.Away g)).comp φ)) :
    _root_.RingHom.Flat ((algebraMap B (Localization.AtPrime q)).comp φ) := by
  let S := Localization.Away g
  let T := Localization.AtPrime q
  have hMN : Submonoid.powers g ≤ q.primeCompl := Submonoid.powers_le.2 hg
  let : Algebra S T := IsLocalization.localizationAlgebraOfSubmonoidLe S T
    (Submonoid.powers g) q.primeCompl hMN
  let : IsScalarTower B S T := IsLocalization.localization_isScalarTower_of_submonoid_le S T
    (Submonoid.powers g) q.primeCompl hMN
  have : IsLocalization (q.primeCompl.map (algebraMap B S)) T :=
    IsLocalization.isLocalization_of_submonoid_le S T (Submonoid.powers g) q.primeCompl hMN
  have hflatST : _root_.RingHom.Flat (algebraMap S T) :=
    _root_.RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat T (q.primeCompl.map (algebraMap B S)))
  have heq : (algebraMap S T).comp ((algebraMap B S).comp φ) = (algebraMap B T).comp φ :=
    RingHom.ext fun x => (IsScalarTower.algebraMap_apply B S T (φ x)).symm
  exact heq ▸ h.comp hflatST

/-- Equal ring homomorphisms induce the same homomorphism of local rings. -/
public theorem localRingHom_congr {R P : Type*} [CommRing R] [CommRing P] {f g : R →+* P}
    (I : Ideal R) [I.IsPrime] (J : Ideal P) [J.IsPrime] (hf : I = J.comap f)
    (hg : I = J.comap g) (h : f = g) :
    Localization.localRingHom I J f hf = Localization.localRingHom I J g hg := by
  subst h
  rfl

/-- A commuting square of ring homomorphisms induces a commuting square of the homomorphisms of
local rings at a prime of the final ring and its contractions. -/
public theorem localRingHom_square {P Q R S : Type*} [CommRing P] [CommRing Q] [CommRing R]
    [CommRing S] (u : P →+* R) (v : Q →+* S) (w : P →+* Q) (z : R →+* S)
    (hsq : z.comp u = v.comp w) (s : Ideal S) [s.IsPrime] (r : Ideal R) [r.IsPrime]
    (p : Ideal P) [p.IsPrime] (t : Ideal Q) [t.IsPrime]
    (hr : r = s.comap z) (hp : p = r.comap u) (ht : t = s.comap v) (hpt : p = t.comap w) :
    (Localization.localRingHom r s z hr).comp (Localization.localRingHom p r u hp) =
      (Localization.localRingHom t s v ht).comp (Localization.localRingHom p t w hpt) := by
  have h₁ : p = s.comap (z.comp u) := by rw [hp, hr, Ideal.comap_comap]
  have h₂ : p = s.comap (v.comp w) := by rw [hpt, ht, Ideal.comap_comap]
  rw [← Localization.localRingHom_comp p r s u hp z hr,
    ← Localization.localRingHom_comp p t s w hpt v ht]
  exact localRingHom_congr p s h₁ h₂ hsq

end Localization

section Polynomial

universe u

/-- **The polynomial extension is flat at a prime at which an element is a unit.**  If the
localization of `B` away from `g` is flat over `A`, then `B[σ]` localized at a prime not
containing the constant `g` is flat over `A[σ]` localized at the contracted prime. -/
public theorem flat_localRingHom_mvPolynomialMap {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (σ : Type u) (g : B) (q : Ideal (MvPolynomial σ B)) [q.IsPrime]
    (hg : (MvPolynomial.C g : MvPolynomial σ B) ∉ q)
    (h : _root_.RingHom.Flat ((algebraMap B (Localization.Away g)).comp φ))
    (p : Ideal (MvPolynomial σ A)) [p.IsPrime] (hpq : p = q.comap (MvPolynomial.map φ)) :
    _root_.RingHom.Flat (Localization.localRingHom p q (MvPolynomial.map φ) hpq) := by
  classical
  have hflatq : _root_.RingHom.Flat
      ((algebraMap (MvPolynomial σ B) (Localization.AtPrime q)).comp (MvPolynomial.map φ)) :=
    flat_atPrime_of_flat_away _ _ q hg (MvPolynomial.flat_away_C_of_flat_away φ g σ h)
  let PA := MvPolynomial σ A
  let PAp := Localization.AtPrime p
  let PBq := Localization.AtPrime q
  let w : PAp →+* PBq := Localization.localRingHom p q (MvPolynomial.map φ) hpq
  let : Algebra PA PBq :=
    ((algebraMap (MvPolynomial σ B) PBq).comp (MvPolynomial.map φ)).toAlgebra
  let : Algebra PAp PBq := w.toAlgebra
  let : IsScalarTower PA PAp PBq := IsScalarTower.of_algebraMap_eq fun x =>
    (Localization.localRingHom_to_map p q (MvPolynomial.map φ) hpq x).symm
  have hmod : Module.Flat PA PBq := _root_.RingHom.flat_algebraMap_iff.mp hflatq
  show _root_.RingHom.Flat w
  rw [← w.algebraMap_toAlgebra, _root_.RingHom.flat_algebraMap_iff]
  exact (Module.flat_iff_of_isLocalization PAp p.primeCompl PBq).mpr hmod

end Polynomial

section RestrictedPowerSeries

universe u

open RestrictedPowerSeries

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- **Flatness of a restricted power series extension at a rig-closed point.**  Let `A → B` be
adic for a Noetherian adic topological ring `A` complete along an ideal of definition `I` and
its extension `J = I · B`, with `B[1/g]` flat over `A` for every topologically nilpotent `g`.
If a prime `q` of `B{σ}` and the primes it contracts to in `B`, in `A{σ}` and in `A` are all
rig-closed, then `B{σ}_q` is flat over `A{σ}`. -/
public theorem flat_atPrime_restrictedPowerSeriesMap
    [TopologicalSpace A] [IsTopologicalRing A] [IsNoetherianRing A]
    [TopologicalSpace B] [IsTopologicalRing B] [IsNoetherianRing B]
    (I : Ideal A) (hI : IsAdic I) [IsAdicComplete I A]
    (hJ : IsAdic (I.map (algebraMap A B)))
    [IsAdicComplete (I.map (algebraMap A B)) B]
    (σ : Type u) [Finite σ]
    (hflat : ∀ g : B, IsTopologicallyNilpotent g →
      _root_.RingHom.Flat ((algebraMap B (Localization.Away g)).comp (algebraMap A B)))
    (q : Ideal (RestrictedPowerSeries (I.map (algebraMap A B)) σ)) [q.IsPrime]
    (hq : Ideal.IsClosedPointAwayFrom
      ((I.map (algebraMap A B)).map (coefficientRingHom (I.map (algebraMap A B)) σ)) q)
    (hqB : Ideal.IsClosedPointAwayFrom (I.map (algebraMap A B))
      (q.comap (coefficientRingHom (I.map (algebraMap A B)) σ)))
    (hp : Ideal.IsClosedPointAwayFrom (I.map (coefficientRingHom I σ))
      (q.comap (TopologicalRing.restrictedPowerSeriesMap (B := B) I σ)))
    (hpA : Ideal.IsClosedPointAwayFrom I
      ((q.comap (TopologicalRing.restrictedPowerSeriesMap (B := B) I σ)).comap
        (coefficientRingHom I σ))) :
    _root_.RingHom.Flat
      ((algebraMap (RestrictedPowerSeries (I.map (algebraMap A B)) σ)
        (Localization.AtPrime q)).comp
          (TopologicalRing.restrictedPowerSeriesMap (B := B) I σ)) := by
  classical
  let J : Ideal B := I.map (algebraMap A B)
  let m := TopologicalRing.restrictedPowerSeriesMap (B := B) I σ
  let fA := polynomialRingHom I σ
  let fB := polynomialRingHom J σ
  let mp : MvPolynomial σ A →+* MvPolynomial σ B := MvPolynomial.map (algebraMap A B)
  have hsq : m.comp fA = fB.comp mp := RingHom.ext fun x =>
    TopologicalRing.restrictedPowerSeriesMap_polynomialRingHom I σ x
  let p : Ideal (RestrictedPowerSeries I σ) := q.comap m
  let : p.IsPrime := Ideal.comap_isPrime m q
  let q' : Ideal (MvPolynomial σ B) := q.comap fB
  let : q'.IsPrime := Ideal.comap_isPrime fB q
  let p' : Ideal (MvPolynomial σ A) := p.comap fA
  let : p'.IsPrime := Ideal.comap_isPrime fA p
  have hp't : p' = q'.comap mp := by
    show (q.comap m).comap fA = (q.comap fB).comap mp
    rw [Ideal.comap_comap, Ideal.comap_comap, hsq]
  let : IsNoetherianRing (RestrictedPowerSeries I σ) := isNoetherianRing_restrictedPowerSeries I σ
  let : IsNoetherianRing (RestrictedPowerSeries J σ) := isNoetherianRing_restrictedPowerSeries J σ
  have hnotle : ¬ J.map (coefficientRingHom J σ) ≤ q := by
    intro hle
    exact hq.1 ((PrimeSpectrum.mem_zeroLocus _ _).2 (SetLike.coe_subset_coe.2 hle))
  obtain ⟨g, hgJ, hgq⟩ := SetLike.not_le_iff_exists.mp
    (fun hle => hnotle (Ideal.map_le_iff_le_comap.mpr hle))
  have hgnil : IsTopologicallyNilpotent g :=
    TopologicalRing.CompletionOver.isTopologicallyNilpotent_of_mem_isIdealOfDefinition
      ((isIdealOfDefinition_iff_isAdic ⟨J, hJ⟩ J).2 hJ) hgJ
  have hCg : (MvPolynomial.C g : MvPolynomial σ B) ∉ q' := hgq
  have hwflat : _root_.RingHom.Flat (Localization.localRingHom p' q' mp hp't) :=
    flat_localRingHom_mvPolynomialMap (algebraMap A B) σ g q' hCg (hflat g hgnil) p' hp't
  have hbA := adicCompletionMap_localRingHom_bijective I hI σ p hp hpA
  have hbB := adicCompletionMap_localRingHom_bijective J hJ σ q hq hqB
  have hsqloc :
      (Localization.localRingHom p q m rfl).comp (Localization.localRingHom p' p fA rfl) =
        (Localization.localRingHom q' q fB rfl).comp
          (Localization.localRingHom p' q' mp hp't) :=
    localRingHom_square fA fB mp m hsq q p p' q' rfl rfl rfl hp't
  have hzflat : _root_.RingHom.Flat (Localization.localRingHom p q m rfl) :=
    flat_of_flat_of_bijective_adicCompletionMap hsqloc hbA hbB hwflat
  have hloc : _root_.RingHom.Flat
      (algebraMap (RestrictedPowerSeries I σ) (Localization.AtPrime p)) :=
    _root_.RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ p.primeCompl)
  have heq : (Localization.localRingHom p q m rfl).comp
      (algebraMap (RestrictedPowerSeries I σ) (Localization.AtPrime p)) =
      (algebraMap (RestrictedPowerSeries J σ) (Localization.AtPrime q)).comp m :=
    RingHom.ext fun x => Localization.localRingHom_to_map p q m rfl x
  exact heq ▸ hloc.comp hzflat

/-- **A naively rig-flat homomorphism stays flat at rig-closed points after passing to
restricted power series.**  Let `A → B` be a continuous adic homomorphism of weakly admissible
Noetherian adic topological rings, complete along an ideal of definition `I` and its extension
`J = I · B`, which is naively rig-flat.  If a prime `q` of `B{σ}` and the primes it contracts to
in `B`, in `A{σ}` and in `A` are all rig-closed, then `B{σ}_q` is flat over `A{σ}`. -/
public theorem flat_atPrime_restrictedPowerSeriesMap_of_isNaivelyRigFlat
    [TopologicalSpace A] [IsTopologicalRing A] [IsNoetherianRing A] [IsLinearTopology A A]
    [TopologicalSpace B] [IsTopologicalRing B] [IsNoetherianRing B] [IsLinearTopology B B]
    (I : Ideal A) (hI : IsAdic I) [IsAdicComplete I A]
    (hJ : IsAdic (I.map (algebraMap A B)))
    [IsAdicComplete (I.map (algebraMap A B)) B]
    (σ : Type u) [Finite σ]
    (hcont : Continuous (algebraMap A B))
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hB : TopologicalRing.IsWeaklyAdmissible B)
    (hadic : _root_.RingHom.IsAdic (algebraMap A B))
    (hflat : RingHom.IsNaivelyRigFlat (algebraMap A B))
    (q : Ideal (RestrictedPowerSeries (I.map (algebraMap A B)) σ)) [q.IsPrime]
    (hq : Ideal.IsClosedPointAwayFrom
      ((I.map (algebraMap A B)).map (coefficientRingHom (I.map (algebraMap A B)) σ)) q)
    (hqB : Ideal.IsClosedPointAwayFrom (I.map (algebraMap A B))
      (q.comap (coefficientRingHom (I.map (algebraMap A B)) σ)))
    (hp : Ideal.IsClosedPointAwayFrom (I.map (coefficientRingHom I σ))
      (q.comap (TopologicalRing.restrictedPowerSeriesMap (B := B) I σ)))
    (hpA : Ideal.IsClosedPointAwayFrom I
      ((q.comap (TopologicalRing.restrictedPowerSeriesMap (B := B) I σ)).comap
        (coefficientRingHom I σ))) :
    _root_.RingHom.Flat
      ((algebraMap (RestrictedPowerSeries (I.map (algebraMap A B)) σ)
        (Localization.AtPrime q)).comp
          (TopologicalRing.restrictedPowerSeriesMap (B := B) I σ)) := by
  refine flat_atPrime_restrictedPowerSeriesMap I hI hJ σ ?_ q hq hqB hp hpA
  exact ((naivelyRigFlat_tfae (algebraMap A B) hcont hA hB
    ⟨I, hI, Ideal.fg_of_isNoetherianRing I⟩
    ⟨I.map (algebraMap A B), hJ, Ideal.fg_of_isNoetherianRing _⟩ hadic).out 1 2).mp hflat.2.2

end RestrictedPowerSeries

end Rig

end
