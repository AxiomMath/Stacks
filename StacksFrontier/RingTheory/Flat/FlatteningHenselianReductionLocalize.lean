module

public import StacksFrontier.RingTheory.Flat.CompleteDevissagePoints
public import StacksFrontier.RingTheory.Flat.DevissageLocalize
public import StacksFrontier.RingTheory.Flat.CompleteDevissageSpecTransport
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The primes of a complete dévissage under localization and change of base

`Module.CompleteDevissage.localizeAtPrime` localizes a complete dévissage over a prime `r` of the
base at the complement of `r`, and `Module.CompleteDevissage.ofRingEquiv` transports one along an
isomorphism of the base. This file carries the primes of the stages
(`Module.CompleteDevissage.Points`) along both operations. Under localization a prime of a stage
lying over `r` is replaced by its extension; the compatibilities survive because every map of the
localized dévissage is the localization of the original one, and the uniqueness of the prime of
the upper algebra survives because a prime of the localized upper algebra is the extension of its
contraction.

## Main definitions

* `Module.CompleteDevissage.Points.localizeAtPrime`: the primes of the localized dévissage.
* `Module.CompleteDevissage.Points.ofRingEquiv`: the primes of the transported dévissage.

## References

* [Stacks Project, Tag 05HZ](https://stacks.math.columbia.edu/tag/05HZ)
* [Stacks Project, Tag 05PG](https://stacks.math.columbia.edu/tag/05PG)
-/

@[expose] public section

universe u v w

namespace IsLocalization

/-- Let `f' : X' → Y'` be the localization of a ring map `f : X → Y`. For a prime `P` of `Y`
missing the inverted submonoid, the contraction along `f'` of the extension of `P` is the
extension of the contraction of `P` along `f`. -/
theorem comap_map_eq_map_comap_of_comm {X Y X' Y' : Type*} [CommRing X] [CommRing Y]
    [CommRing X'] [CommRing Y'] [Algebra X X'] [Algebra Y Y'] (MX : Submonoid X)
    (MY : Submonoid Y) [IsLocalization MX X'] [IsLocalization MY Y'] (f : X →+* Y)
    (f' : X' →+* Y') (hf : ∀ x, f' (algebraMap X X' x) = algebraMap Y Y' (f x))
    (P : Ideal Y) [P.IsPrime] (hP : Disjoint (MY : Set Y) P) :
    (P.map (algebraMap Y Y')).comap f' = (P.comap f).map (algebraMap X X') := by
  have h1 : ((P.map (algebraMap Y Y')).comap f').comap (algebraMap X X') = P.comap f := by
    rw [Ideal.comap_comap,
      show f'.comp (algebraMap X X') = (algebraMap Y Y').comp f from RingHom.ext hf,
      ← Ideal.comap_comap]
    exact congrArg (Ideal.comap f) (IsLocalization.under_map_of_isPrime_disjoint MY Y' ‹_› hP)
  rw [← h1]
  exact (IsLocalization.map_under MX X' _).symm

/-- An ideal of a localization is the extension of its contraction. -/
@[ega "0 1.2.6" "partial"]
theorem eq_map_of_comap_eq {Y Y' : Type*} [CommRing Y] [CommRing Y'] [Algebra Y Y']
    (MY : Submonoid Y) [IsLocalization MY Y'] {P'' : Ideal Y'} {P : Ideal Y}
    (h : P''.comap (algebraMap Y Y') = P) : P'' = P.map (algebraMap Y Y') := by
  rw [← h]
  exact (IsLocalization.map_under MY Y' P'').symm

/-- A prime lying over `r` misses the image of the complement of `r`. -/
theorem disjoint_algebraMapSubmonoid_primeCompl {R B : Type*} [CommRing R] [CommRing B]
    [Algebra R B] {r : Ideal R} [r.IsPrime] {p : Ideal B} (h : p.comap (algebraMap R B) = r) :
    Disjoint ((Algebra.algebraMapSubmonoid B r.primeCompl : Submonoid B) : Set B) p := by
  rw [Set.disjoint_left]
  rintro _ ⟨s, hs, rfl⟩ hp
  exact hs (h ▸ Ideal.mem_comap.mpr hp)

end IsLocalization

namespace Module.CompleteDevissage.Points

open IsLocalization

section Localize

variable {R S N : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
  [AddCommGroup N] [Module S N] [Module.Finite S N] {r : Ideal R} [r.IsPrime]
  {D : CompleteDevissage R S N r} {q : Ideal S}

/-- The prime of an upper algebra lies over the base prime. -/
theorem comap_P_algebraMap (pts : D.Points q) (i : Fin (D.stepCount + 1)) :
    (pts.P i).comap (algebraMap R (D.A i)) = r := by
  have h : algebraMap R (D.A i) = (D.toLeft i).toRingHom.comp (algebraMap R (D.B i)) :=
    ((D.toLeft i).comp_algebraMap).symm
  rw [h, ← Ideal.comap_comap, pts.comap_P, pts.comap_p]

/-- The transition compatibility of the localized primes. -/
theorem localizeAtPrime_transition (pts : D.Points q) (j : Fin D.stepCount) :
    ((pts.P j.succ).map (algebraMap (D.A j.succ) (D.locA j.succ))).comap
      (D.locToRight j).toRingHom =
      (pts.p j.castSucc).map (algebraMap (D.B j.castSucc) (D.locB j.castSucc)) := by
  have := pts.isPrime_P j.succ
  rw [comap_map_eq_map_comap_of_comm (Algebra.algebraMapSubmonoid (D.B j.castSucc) r.primeCompl)
    (Algebra.algebraMapSubmonoid (D.A j.succ) r.primeCompl) (D.toRight j).toRingHom
    (D.locToRight j).toRingHom (fun x => D.locToRight_algebraMap j x) (pts.P j.succ)
    (disjoint_algebraMapSubmonoid_primeCompl (pts.comap_P_algebraMap j.succ)), pts.transition]

/-- **The primes of the localization of a complete dévissage at its base prime.** The primes of
the stages of `D.localizeAtPrime` are the extensions of the primes of the stages of `D`. -/
noncomputable def localizeAtPrime (pts : D.Points q) :
    D.localizeAtPrime.Points
      (q.map (algebraMap S (Localization (Algebra.algebraMapSubmonoid S r.primeCompl)))) where
  p := fun (i : Fin (D.stepCount + 1)) =>
    ((pts.p i).map (algebraMap (D.B i) (D.locB i)) : Ideal (D.locB i))
  isPrime_p := fun (i : Fin (D.stepCount + 1)) => by
    have := pts.isPrime_p i
    exact isPrime_of_isPrime_disjoint (Algebra.algebraMapSubmonoid (D.B i) r.primeCompl)
      (D.locB i) (pts.p i) inferInstance (disjoint_algebraMapSubmonoid_primeCompl (pts.comap_p i))
  comap_p := fun (i : Fin (D.stepCount + 1)) => by
    have := pts.isPrime_p i
    change ((pts.p i).map (algebraMap (D.B i) (D.locB i))).comap
      (algebraMap (Localization r.primeCompl) (D.locB i)) = _
    rw [comap_map_eq_map_comap_of_comm r.primeCompl
      (Algebra.algebraMapSubmonoid (D.B i) r.primeCompl) (algebraMap R (D.B i))
      (algebraMap (Localization r.primeCompl) (D.locB i)) (fun x => by
        rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply])
      (pts.p i) (disjoint_algebraMapSubmonoid_primeCompl (pts.comap_p i)), pts.comap_p i]
  P := fun (i : Fin (D.stepCount + 1)) =>
    ((pts.P i).map (algebraMap (D.A i) (D.locA i)) : Ideal (D.locA i))
  isPrime_P := fun (i : Fin (D.stepCount + 1)) => by
    have := pts.isPrime_P i
    exact isPrime_of_isPrime_disjoint (Algebra.algebraMapSubmonoid (D.A i) r.primeCompl)
      (D.locA i) (pts.P i) inferInstance
      (disjoint_algebraMapSubmonoid_primeCompl (pts.comap_P_algebraMap i))
  comap_P := fun (i : Fin (D.stepCount + 1)) => by
    have := pts.isPrime_P i
    change ((pts.P i).map (algebraMap (D.A i) (D.locA i))).comap (D.locToLeft i).toRingHom = _
    rw [comap_map_eq_map_comap_of_comm (Algebra.algebraMapSubmonoid (D.B i) r.primeCompl)
      (Algebra.algebraMapSubmonoid (D.A i) r.primeCompl) (D.toLeft i).toRingHom
      (D.locToLeft i).toRingHom (fun x => D.locToLeft_algebraMap i x) (pts.P i)
      (disjoint_algebraMapSubmonoid_primeCompl (pts.comap_P_algebraMap i)), pts.comap_P]
  unique_P := fun (i : Fin (D.stepCount + 1)) (P'' : Ideal (D.locA i)) hP'' h => by
    have := pts.isPrime_p i
    change P''.comap (D.locToLeft i).toRingHom = (pts.p i).map (algebraMap (D.B i) (D.locB i))
      at h
    change P'' = (pts.P i).map (algebraMap (D.A i) (D.locA i))
    refine eq_map_of_comap_eq (Algebra.algebraMapSubmonoid (D.A i) r.primeCompl)
      (pts.unique_P i _ (Ideal.comap_isPrime (algebraMap (D.A i) (D.locA i)) P'' (H := hP'')) ?_)
    rw [Ideal.comap_comap,
      show (algebraMap (D.A i) (D.locA i)).comp (D.toLeft i).toRingHom =
          (D.locToLeft i).toRingHom.comp (algebraMap (D.B i) (D.locB i)) from
        RingHom.ext fun x => (D.locToLeft_algebraMap i x).symm,
      ← Ideal.comap_comap, h]
    exact under_map_of_isPrime_disjoint (Algebra.algebraMapSubmonoid (D.B i) r.primeCompl) _
      inferInstance (disjoint_algebraMapSubmonoid_primeCompl (pts.comap_p i))
  initial := by
    have := pts.isPrime_P 0
    change ((pts.P 0).map (algebraMap (D.A 0) (D.locA 0))).comap
      (D.locToA₀ (Localization (Algebra.algebraMapSubmonoid S r.primeCompl))).toRingHom = _
    rw [comap_map_eq_map_comap_of_comm (Algebra.algebraMapSubmonoid S r.primeCompl)
      (Algebra.algebraMapSubmonoid (D.A 0) r.primeCompl) D.toA₀.toRingHom
      (D.locToA₀ (Localization (Algebra.algebraMapSubmonoid S r.primeCompl))).toRingHom
      (fun x => D.locToA₀_algebraMap _ x) (pts.P 0)
      (disjoint_algebraMapSubmonoid_primeCompl (pts.comap_P_algebraMap 0)), pts.initial]
  transition := pts.localizeAtPrime_transition

end Localize

section Transport

variable {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N]
  {R' : Type u} {S' : Type v} {N' : Type w} [CommRing R'] [CommRing S'] [Algebra R' S']
  [Algebra.FiniteType R' S'] [AddCommGroup N'] [Module S' N'] [Module.Finite S' N']

/-- **The primes of a complete dévissage transported along isomorphisms of the data.** The stage
algebras are unchanged, so the primes are the old ones. -/
noncomputable def ofRingEquiv (eR : R ≃+* R') (eS : S ≃+* S') (eN : N ≃+ N')
    (halg : ∀ x : R, algebraMap R' S' (eR x) = eS (algebraMap R S x))
    (hsmul : ∀ (s : S) (n : N), eN (s • n) = eS s • eN n)
    {r : Ideal R} [r.IsPrime] {r' : Ideal R'} [r'.IsPrime]
    (hr : r = Ideal.comap eR.toRingHom r') {D : CompleteDevissage R S N r} {q : Ideal S}
    (pts : D.Points q) {q' : Ideal S'} (hq : q.comap eS.symm.toRingHom = q') :
    (D.ofRingEquiv eR eS eN halg hsmul hr).Points q' where
  p := pts.p
  isPrime_p := pts.isPrime_p
  comap_p i := by
    change (pts.p i).comap ((algebraMap R (D.B i)).comp eR.symm.toRingHom) = r'
    rw [← Ideal.comap_comap, pts.comap_p, hr, Ideal.comap_comap,
      RingEquiv.toRingHom_comp_symm_toRingHom, Ideal.comap_id]
  P := pts.P
  isPrime_P := pts.isPrime_P
  comap_P := pts.comap_P
  unique_P := pts.unique_P
  initial := by
    change (pts.P 0).comap (D.toA₀.toRingHom.comp eS.symm.toRingHom) = q'
    rw [← Ideal.comap_comap, pts.initial, hq]
  transition := pts.transition

end Transport

end Module.CompleteDevissage.Points

end
