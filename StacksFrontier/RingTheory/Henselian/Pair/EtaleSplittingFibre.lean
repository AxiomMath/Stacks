module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import StacksFrontier.RingTheory.Henselian.Pair.EtaleSplitting
public import StacksFrontier.RingTheory.Spectrum.Prime.QuotientFibre
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The bijection on the closed fibre which splits an étale algebra

`StacksFrontier.RingTheory.Henselian.Pair.EtaleSplitting` splits an étale algebra `A'` over an
algebra `A` integral over a henselian local ring `C` as soon as `A ⧸ J → A' ⧸ J'` is bijective,
where `J = √(m A)` is the radical of the extension of the maximal ideal of `C` and `J'` is any
ideal of `A'` above `J`. This file produces that bijectivity from data about the *fibre*: a
bijection of the two sets of primes `V(J') → V(J)` together with surjectivity of the residue
field extensions.

Every prime of `A` above `J` is maximal, being a prime of an integral algebra lying over the
maximal ideal of `C` ([Stacks Project, Tag 00GA]), and `J` is radical, so
`RingHom.bijective_quotientMap_of_bijective_comapRestrict` applies; surjectivity of the residue
field maps matches every element of `A'` with one of `A` modulo each prime of `V(J')`. The
bijection of fibres is the first half of the "Claim" of [Stacks Project, Tag 0DT9].

## Main results

* `Ideal.exists_sub_mem_of_surjective_residueFieldMap`: a surjective residue field map at a prime
  with maximal contraction lets every element be matched modulo that prime.
* `Ideal.isMaximal_of_radical_map_isMaximal_le`: every prime above `√(m A)` is maximal.
* `bijective_quotientMapₐ_of_bijective_comapRestrict`: `A ⧸ J → A' ⧸ J'` is bijective when
  `V(J)` is finite, `V(J') → V(J)` is bijective and the residue field maps are surjective.
* `exists_algEquiv_prod_of_etale_of_bijective_comapRestrict`: the resulting splitting, which is
  the second half of the "Claim" of [Stacks Project, Tag 0DT9].

## References

* [Stacks Project, Tag 00GA](https://stacks.math.columbia.edu/tag/00GA)
* [Stacks Project, Tag 0DT9](https://stacks.math.columbia.edu/tag/0DT9)
-/

@[expose] public section

universe u

/-- **Surjectivity of a residue field map matches elements modulo the prime.** If `q` is a prime
of `A'` whose contraction `m` to `A` is maximal and `κ(m) → κ(q)` is surjective, then every
element of `A'` differs from an element of the image of `φ` by an element of `q`. -/
theorem Ideal.exists_sub_mem_of_surjective_residueFieldMap {A A' : Type*} [CommRing A]
    [CommRing A'] (φ : A →+* A') {q : Ideal A'} [q.IsPrime] (hm : (q.comap φ).IsMaximal)
    (hsurj : Function.Surjective (Ideal.ResidueField.map (q.comap φ) q φ rfl)) (y : A') :
    ∃ x : A, y - φ x ∈ q := by
  have := hm
  obtain ⟨z, hz⟩ := hsurj (algebraMap A' q.ResidueField y)
  obtain ⟨x, rfl⟩ := Ideal.algebraMap_residueField_surjective (q.comap φ) z
  refine ⟨x, ?_⟩
  rw [← Ideal.algebraMap_residueField_eq_zero, map_sub, sub_eq_zero]
  exact ((Ideal.ResidueField.map_algebraMap _ q φ rfl x).symm.trans hz).symm

/-- **A prime of an integral algebra above the radical of an extended maximal ideal is maximal.**
If `A` is integral over `C` and `m` is a maximal ideal of `C`, every prime of `A` containing
`√(m A)` is maximal. This is a case of [Stacks Project, Tag 00GA]. -/
theorem Ideal.isMaximal_of_radical_map_isMaximal_le {C A : Type*} [CommRing C] [CommRing A]
    [Algebra C A] [Algebra.IsIntegral C A] {m : Ideal C} (hm : m.IsMaximal) (p : Ideal A)
    [p.IsPrime] (hp : (m.map (algebraMap C A)).radical ≤ p) : p.IsMaximal := by
  have := hm
  rw [Ideal.IsPrime.radical_le_iff ‹p.IsPrime›, Ideal.map_le_iff_le_comap] at hp
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := C) p
    (show (p.comap (algebraMap C A)).IsMaximal from
      (hm.eq_of_le (fun htop => ‹p.IsPrime›.ne_top (by simpa [Ideal.comap_eq_top_iff] using htop))
        hp ▸ hm))

/-- **The bijectivity hypothesis of
`exists_algEquiv_prod_of_etale_of_isIntegral_of_henselianLocal_of_le`, from the fibre.**

Let `C` be a local ring with maximal ideal `m`, let `A` be a `C`-algebra integral over `C`, put
`J = √(m A)`, and let `J'` be a radical ideal of an `A`-algebra `A'` above `J`. If the fibre
`V(J) ⊆ Spec A` is finite, contraction along `A → A'` is a bijection `V(J') → V(J)`, and the
residue field map at every prime of `V(J')` is surjective, then `A ⧸ J → A' ⧸ J'` is bijective.
-/
theorem bijective_quotientMapₐ_of_bijective_comapRestrict {C : Type u} [CommRing C]
    [IsLocalRing C] (A : Type u) [CommRing A] [Algebra C A] [Algebra.IsIntegral C A]
    (A' : Type u) [CommRing A'] [Algebra A A'] {J' : Ideal A'} (hJ'rad : J'.IsRadical)
    (hJ' : ((IsLocalRing.maximalIdeal C).map (algebraMap C A)).radical ≤
      J'.comap (algebraMap A A'))
    (hfin : Finite {p : PrimeSpectrum A //
      ((IsLocalRing.maximalIdeal C).map (algebraMap C A)).radical ≤ p.asIdeal})
    (hfib : Function.Bijective (PrimeSpectrum.comapRestrict (algebraMap A A') hJ'))
    (hres : ∀ q : PrimeSpectrum A', J' ≤ q.asIdeal → Function.Surjective
      (Ideal.ResidueField.map (q.asIdeal.comap (algebraMap A A')) q.asIdeal
        (algebraMap A A') rfl)) :
    Function.Bijective (Ideal.quotientMapₐ J' (Algebra.ofId A A') hJ') := by
  have hmax : ∀ p : PrimeSpectrum A,
      ((IsLocalRing.maximalIdeal C).map (algebraMap C A)).radical ≤ p.asIdeal →
        p.asIdeal.IsMaximal := fun p hp =>
    Ideal.isMaximal_of_radical_map_isMaximal_le
      (IsLocalRing.maximalIdeal.isMaximal C) p.asIdeal hp
  refine RingHom.bijective_quotientMap_of_bijective_comapRestrict (algebraMap A A') hJ'
    (Ideal.radical_isRadical _) hJ'rad hfin hmax hfib fun q hq =>
      Ideal.exists_sub_mem_of_surjective_residueFieldMap (algebraMap A A')
        (hmax (PrimeSpectrum.comap (algebraMap A A') q) (hJ'.trans (Ideal.comap_mono hq)))
        (hres q hq)

/-- **The second half of the "Claim" of [Stacks Project, Tag 0DT9].** Let `C` be a henselian local
ring with maximal ideal `m`, let `A` be a `C`-algebra integral over `C`, put `J = √(m A)`, and let
`A'` be an étale `A`-algebra with a radical ideal `J'` above `J` — in the application, the ideal
cutting out the fibre `U'_{p'}` of a single point `p'`. If the fibre `V(J)` is finite, contraction
along `A → A'` is a bijection `V(J') → V(J)`, and the residue field maps along `V(J') → V(J)` are
surjective, then `A'` splits as `A × A''`, with the first projection reducing to the inverse of
the bijection `A ⧸ J → A' ⧸ J'`.

The bijection of fibres is the first half of the Claim, and the surjectivity of the residue field
maps is the input "as `U' → U` is étale, `U'_{p'} → U_p` induces isomorphisms on residue fields".
-/
@[sga "3 X 4.5" "special case"]
theorem exists_algEquiv_prod_of_etale_of_bijective_comapRestrict {C : Type u} [CommRing C]
    [HenselianLocalRing C] (A : Type u) [CommRing A] [Algebra C A] [Algebra.IsIntegral C A]
    (A' : Type u) [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] {J' : Ideal A'}
    (hJ'rad : J'.IsRadical)
    (hJ' : ((IsLocalRing.maximalIdeal C).map (algebraMap C A)).radical ≤
      J'.comap (algebraMap A A'))
    (hfin : Finite {p : PrimeSpectrum A //
      ((IsLocalRing.maximalIdeal C).map (algebraMap C A)).radical ≤ p.asIdeal})
    (hfib : Function.Bijective (PrimeSpectrum.comapRestrict (algebraMap A A') hJ'))
    (hres : ∀ q : PrimeSpectrum A', J' ≤ q.asIdeal → Function.Surjective
      (Ideal.ResidueField.map (q.asIdeal.comap (algebraMap A A')) q.asIdeal
        (algebraMap A A') rfl)) :
    ∃ (A'' : Type u) (_ : CommRing A'') (_ : Algebra A A'') (τ : A' →ₐ[A] A)
      (e : A' ≃ₐ[A] A × A''),
      (∀ x : A', (e x).1 = τ x) ∧
        ∀ x : A', Ideal.quotientMapₐ J' (Algebra.ofId A A') hJ'
            (Ideal.Quotient.mk
              (((IsLocalRing.maximalIdeal C).map (algebraMap C A)).radical) (τ x)) =
          Ideal.Quotient.mk J' x :=
  exists_algEquiv_prod_of_etale_of_isIntegral_of_henselianLocal_of_le A A' hJ'
    (bijective_quotientMapₐ_of_bijective_comapRestrict A A' hJ'rad hJ' hfin hfib hres)

end
