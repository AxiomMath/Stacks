module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Prod
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Lemmas
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.TensorProduct.Pi
public import Mathlib.RingTheory.Unramified.LocalRing
public import StacksFrontier.RingTheory.Etale.LocalStructure
public import StacksFrontier.RingTheory.Localization.Idempotent

/-!
# Trivialising a finite unramified algebra after one localisation

This file collects the ring-theoretic steps of the finite case of property (B) for the étale
topology, [Stacks, Tag 04DQ]. The situation produced there by the étale local structure theorem
[Stacks, Tag 00UL] is a base ring `A` with a prime `p`, a finite `A`-algebra `R` with a prime `t`
over `p`, and an `R`-algebra `S` which is étale over `R` and finite over `A`, with a prime `s`
over `t`. The local structure theorem supplies two further facts: `s` is the *only* prime of `S`
over `t`, and both residue field extensions `κ(t)/κ(p)` and `κ(s)/κ(p)` are purely inseparable.
The content of this file is that these facts force `R → S` to become an isomorphism after
inverting a single element of `R` outside `t`, which is what produces the section of the étale
covering that property (B) asks for.

## Main results

* `Stacks.EtaleCohomology.bijective_algebraMap_of_isSeparable_of_isPurelyInseparable`: a field
  extension that is separable over an intermediate field and purely inseparable over the base is
  equal to that intermediate field.
* `Stacks.EtaleCohomology.bijective_algebraMap_residueField_of_isPurelyInseparable`: the residue
  field extension `κ(s)/κ(t)` of an algebra unramified at `s` is trivial as soon as `κ(s)/κ(p)` is
  purely inseparable, for any prime `p` of a base ring below `t`.
* `Stacks.EtaleCohomology.exists_notMem_algebraMap_eq_zero_of_forall_not_liesOver`: an integral
  algebra with no prime over `p` becomes the zero ring after inverting one element outside `p`.
* `Stacks.EtaleCohomology.moduleFinite_left_of_prod`: a factor of a module-finite product algebra
  is module-finite.
* `Stacks.EtaleCohomology.quasiFiniteAt_prod_top` and
  `Stacks.EtaleCohomology.quasiFiniteAt_top_prod`: a prime of a product of two algebras coming from
  a prime of a factor at which that factor is quasi-finite is quasi-finite over the base; in
  particular this holds when the factor is module-finite.
* `Stacks.EtaleCohomology.forall_mem_of_forall_not_quasiFiniteAt_prod_top`: if no prime of a
  product of two algebras over `p` avoiding an element is quasi-finite, then the component of that
  element in a module-finite factor lies in every prime of that factor over `p`.
* `Stacks.EtaleCohomology.exists_notMem_mul_algebraMap_eq_zero_of_forall_mem`: if an idempotent
  lies in every prime over `p` of an integral algebra, then it annihilates the image of some
  element outside `p`.
* `Stacks.EtaleCohomology.exists_notMem_basicOpen_subset_range_comap`: if `Spec S → Spec R` has
  open image and hits a prime `t`, then it is surjective over a basic open neighbourhood of `t`.
* `Stacks.EtaleCohomology.exists_notMem_bijective_awayMap`: a finite flat algebra, unramified at
  the unique prime `s` over `t`, surjective on spectra and with trivial residue field extension at
  `s`, becomes an isomorphism after inverting a single element outside `t`.
* `Stacks.EtaleCohomology.exists_notMem_bijective_awayMap_of_isPurelyInseparable`: the combination
  of the previous two, in the form the local structure theorem delivers.
* `Stacks.EtaleCohomology.moduleFinite_away_of_surjective`: localizing away from the image of an
  idempotent under a surjection preserves module-finiteness over the base.
* `Stacks.EtaleCohomology.isPurelyInseparable_residueField_of_surjectiveOnStalks`: pure
  inseparability of a residue field extension over `κ(p)` passes along a map surjective on stalks
  to the contracted prime; `Stacks.EtaleCohomology.isPurelyInseparable_residueField_of_surjective`
  is the case of a surjection.
* `Stacks.EtaleCohomology.localStructure_image_of_surjective`: the conclusions of
  [Stacks, Tag 00UL] transported along a surjection onto a factor.
* `Stacks.EtaleCohomology.exists_etale_completeOrthogonalIdempotents_prod`: [Stacks, Tag 00UL]
  applied to a product algebra `B × C`, with its decomposition split across the two factors.
* `Stacks.EtaleCohomology.exists_notMem_forall_dvd_of_forall_exists`: finitely many shrinkings of
  the base, each valid for every multiple of the element it produces, are performed at once by
  taking the product of those elements.
* `Stacks.EtaleCohomology.exists_notMem_forall_mul_algebraMap_eq_zero`: finitely many idempotents
  of an integral algebra, each lying in every prime over `p`, are annihilated simultaneously by one
  element outside `p`;
  `Stacks.EtaleCohomology.exists_notMem_forall_dvd_forall_mul_algebraMap_eq_zero` is the form of it
  that holds for every multiple of that element.
* `Stacks.EtaleCohomology.completeOrthogonalIdempotents_comp_of_eq_zero`: a complete orthogonal
  family of idempotents stays complete when the members that vanish are dropped.
* `Stacks.EtaleCohomology.exists_notMem_completeOrthogonalIdempotents_comp` and
  `Stacks.EtaleCohomology.exists_notMem_forall_dvd_completeOrthogonalIdempotents_comp`: the
  simultaneous shrinking of the base that discards the factors of a decomposition with no point
  over `p`, at the element produced and at every multiple of it.
* `Stacks.EtaleCohomology.exists_castSucc_notMem_of_quasiFiniteAt`: a prime at which an algebra is
  quasi-finite lies in one of the finite factors of such a decomposition, not in the last one.
* `Stacks.EtaleCohomology.exists_notMem_completeOrthogonalIdempotents_liesOver` and
  `Stacks.EtaleCohomology.exists_notMem_forall_dvd_completeOrthogonalIdempotents_liesOver`: after
  one localisation of the base, such a decomposition of a module-finite algebra is indexed exactly
  by the primes lying over `p`.
* `Stacks.EtaleCohomology.exists_liesOver_notMem_castSucc`: every prime of the module-finite side
  over `p'` is hit by a prime of the étale covering lying in one of the finite factors of the
  covering's own decomposition.
* `Stacks.EtaleCohomology.forall_ne_mem_of_forall_eq`,
  `Stacks.EtaleCohomology.exists_notMem_algebraMap_eq_one` and
  `Stacks.EtaleCohomology.exists_notMem_forall_dvd_algebraMap_eq_one`: at a factor carrying only
  one prime over `p'`, one localisation of the base — and every further one — turns the surviving
  idempotent of a complete orthogonal family into the unit.
* `Stacks.EtaleCohomology.finiteType_prod_of_etale`: the product `B × C` of a module-finite
  `A`-algebra `B` and an étale `B`-algebra `C` is of finite type over `A`.
* `Stacks.EtaleCohomology.tensorCancelMid`: the canonical isomorphism
  `(A' ⊗[A] B) ⊗[B] C ≃ₐ[A'] A' ⊗[A] C`.
* `Stacks.EtaleCohomology.surjective_comap_tensorBaseChange`: an étale algebra surjective on
  spectra stays so after base change of the base ring.
* `Stacks.EtaleCohomology.exists_etale_completeOrthogonalIdempotents_tensorBaseChange`:
  [Stacks, Tag 00UL] for the pair `(B, C)`, with both halves of the decomposition carried on
  `A' ⊗[A] B` and on its base change `(A' ⊗[A] B) ⊗[B] C`.
* `Stacks.EtaleCohomology.completeOrthogonalIdempotentsAlgEquivPi`: the decomposition of an algebra
  as the product of the quotients cut out by a complete orthogonal family of idempotents.
* `Stacks.EtaleCohomology.awayAlgEquiv`: localizing away from the image of an element of the base
  agrees with localizing at the image of its powers.
* `Stacks.EtaleCohomology.tensorLocalizationAwayEquiv`: inverting an element of the base commutes
  with base change, `A'[1/a] ⊗[A] B ≃ₐ[A'[1/a]] (A' ⊗[A] B)[1/a]`.

## Implementation notes

The scalar towers between residue fields are threaded through the algebra instances
`Localization.AtPrime.algebraOfLiesOver` and the predicate
`Localization.AtPrime.IsLiesOverAlgebra`, taken as instance arguments rather than installed with
`letI` in the statements. This is Mathlib's own convention for such statements (see
`Algebra.isUnramifiedAt_iff_map_eq`) and it is what lets the three residue fields `κ(p)`, `κ(t)`
and `κ(s)` be recognised as a tower by instance search.

The surjectivity of `Spec S → Spec R` is a hypothesis rather than a conclusion: it is what makes
`R → S` faithfully flat, hence injective, and `exists_notMem_basicOpen_subset_range_comap` is the
statement that it can always be arranged by shrinking the base, since an étale morphism has open
image.

## References

* [Stacks Project, Tag 04DQ](https://stacks.math.columbia.edu/tag/04DQ)
* [Stacks Project, Tag 00UL](https://stacks.math.columbia.edu/tag/00UL)
-/

@[expose] public section

universe u v w

namespace Stacks.EtaleCohomology

/-- A field extension `E / F` which is separable and which is purely inseparable over a subfield
`K` of `F` has `F = E`. This is the mechanism by which the two purely inseparable residue field
extensions supplied by [Stacks, Tag 00UL] force the residue field extension of an étale map
between two of its factors to be trivial. -/
theorem bijective_algebraMap_of_isSeparable_of_isPurelyInseparable
    (K : Type u) (F : Type v) (E : Type w) [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
    [Algebra.IsSeparable F E] [IsPurelyInseparable K E] :
    Function.Bijective (algebraMap F E) :=
  have := IsPurelyInseparable.tower_top K F E
  IsPurelyInseparable.bijective_algebraMap_of_isSeparable F E

variable {A : Type u} {R : Type v} {S : Type w} [CommRing A] [CommRing R] [CommRing S]

section ResidueField

variable [Algebra A R] [Algebra A S] [Algebra R S] [IsScalarTower A R S]
  (p : Ideal A) [p.IsPrime] (t : Ideal R) [t.IsPrime] [t.LiesOver p]
  (s : Ideal S) [s.IsPrime] [s.LiesOver t] [s.LiesOver p]
  [Algebra (Localization.AtPrime p) (Localization.AtPrime t)]
  [Localization.AtPrime.IsLiesOverAlgebra p t]
  [Algebra (Localization.AtPrime t) (Localization.AtPrime s)]
  [Localization.AtPrime.IsLiesOverAlgebra t s]
  [Algebra (Localization.AtPrime p) (Localization.AtPrime s)]
  [Localization.AtPrime.IsLiesOverAlgebra p s]

/-- If `S` is unramified over `R` at a prime `s`, and the residue field extension `κ(s)/κ(p)` is
purely inseparable for some prime `p` of a base ring `A` below `s`, then the residue field
extension `κ(s)/κ(t)` at the prime `t = s ∩ R` is trivial.

Unramifiedness makes `κ(s)/κ(t)` separable, while `κ(s)/κ(p)` purely inseparable makes it purely
inseparable; a separable purely inseparable extension is trivial. -/
theorem bijective_algebraMap_residueField_of_isPurelyInseparable
    [Algebra.EssFiniteType R S] [Algebra.IsUnramifiedAt R s]
    (h : IsPurelyInseparable p.ResidueField s.ResidueField) :
    Function.Bijective (algebraMap t.ResidueField s.ResidueField) :=
  bijective_algebraMap_of_isSeparable_of_isPurelyInseparable
    p.ResidueField t.ResidueField s.ResidueField

end ResidueField

/-- An integral algebra with no prime lying over `p` dies after inverting a single element outside
`p`: there is an `a ∉ p` whose image in the algebra is already zero.

[Stacks, Tag 00UL] produces one factor of its decomposition that is quasi-finite at no prime over
`p`; when that factor is in addition integral over the base — as the factors coming from the
finite part of the decomposition are — every one of its primes *would* be quasi-finite, so it has
no prime over `p` at all and this lemma removes it from the decomposition. -/
theorem exists_notMem_algebraMap_eq_zero_of_forall_not_liesOver
    {T : Type w} [CommRing T] [Algebra A T] [Algebra.IsIntegral A T]
    (p : Ideal A) [p.IsPrime] (h : ∀ q : Ideal T, q.IsPrime → ¬ q.LiesOver p) :
    ∃ a ∉ p, algebraMap A T a = 0 := by
  by_cases hker : RingHom.ker (algebraMap A T) ≤ p
  · obtain ⟨Q, -, hQ, hQ'⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p (⊥ : Ideal T)
      (by simpa [← RingHom.ker_eq_comap_bot] using hker)
    exact absurd ((Ideal.liesOver_iff Q p).mpr hQ'.symm) (h Q hQ)
  · obtain ⟨a, ha, hap⟩ := SetLike.not_le_iff_exists.mp hker
    exact ⟨a, hap, ha⟩

/-- **Swapping the two factors of a product of algebras.** The ring isomorphism
`RingEquiv.prodComm` is an isomorphism of algebras over any common base, because the structure map
of a product is the pair of the structure maps. -/
def prodCommAlgEquiv (A R S : Type*) [CommSemiring A] [Semiring R] [Semiring S]
    [Algebra A R] [Algebra A S] : (R × S) ≃ₐ[A] (S × R) :=
  { RingEquiv.prodComm with commutes' := fun _ => rfl }

/-- Quasi-finiteness at a prime only depends on the prime. This transports it along an equality of
ideals, which `rw` cannot do because the predicate carries the primality instance. -/
theorem quasiFiniteAt_congr [Algebra A R] {q q' : Ideal R} [q.IsPrime] [q'.IsPrime] (h : q = q')
    (H : Algebra.QuasiFiniteAt A q) : Algebra.QuasiFiniteAt A q' := by
  cases h
  exact H

/-- A prime of the first factor contracts from the product along the first projection. -/
theorem comap_fst_eq_prod_top (q : Ideal R) :
    q.comap (RingHom.fst R S) = q.prod (⊤ : Ideal S) := by
  simp [Ideal.prod]

/-- A prime of the second factor contracts from the product along the second projection. -/
theorem comap_snd_eq_top_prod (q : Ideal S) :
    q.comap (RingHom.snd R S) = (⊤ : Ideal R).prod q := by
  simp [Ideal.prod]

section Prod

variable [Algebra A R] [Algebra A S]

/-- **A factor of a module-finite product algebra is module-finite.** The projection
`R × S → R` is a surjective `A`-algebra map, so finiteness descends to the factor.

This is how 00UL's finiteness assertion about a factor `(B × C)[1/e]` of its decomposition is read
on each of the two halves `B[1/e.1]` and `C[1/e.2]` separately. -/
theorem moduleFinite_left_of_prod [Module.Finite A (R × S)] : Module.Finite A R :=
  Module.Finite.of_surjective (AlgHom.fst A R S).toLinearMap Prod.fst_surjective

/-- A prime of a product of rings coming from the first factor lies over whatever that prime lies
over: the two primes have the same contraction to the base, because the second factor contributes
nothing to the contraction. -/
theorem liesOver_prod_top (p : Ideal A) (q : Ideal R) [q.LiesOver p] :
    (q.prod (⊤ : Ideal S)).LiesOver p := by
  refine ⟨(q.over_def p).trans (Ideal.ext fun a => ?_)⟩
  simp [Ideal.under, Ideal.mem_comap, Ideal.mem_prod]

/-- **A prime of a product of algebras coming from a quasi-finite prime of a factor is
quasi-finite.** Localizing `R × S` at the prime `q × S` inverts `(1, 0)`, which kills the second
factor, so that local ring is the local ring of `R` at `q`; quasi-finiteness at `q × S` is
therefore exactly quasi-finiteness at `q`.

In particular this applies when `R` is module-finite over `A`, since a module-finite algebra is
quasi-finite at every prime. That is the mechanism by which the factor of the decomposition of
[Stacks, Tag 00UL] that is quasi-finite at no prime over `p` acquires no prime from the finite side
of a product: see `forall_mem_of_forall_not_quasiFiniteAt_prod_top`. -/
theorem quasiFiniteAt_prod_top (q : Ideal R) [q.IsPrime] [Algebra.QuasiFiniteAt A q]
    [(q.prod (⊤ : Ideal S)).IsPrime] :
    Algebra.QuasiFiniteAt A (q.prod (⊤ : Ideal S)) := by
  let : Algebra (R × S) (Localization.AtPrime q) :=
    ((algebraMap R (Localization.AtPrime q)).comp (RingHom.fst R S)).toAlgebra
  have hmap : ∀ x : R × S, algebraMap (R × S) (Localization.AtPrime q) x =
      algebraMap R (Localization.AtPrime q) x.1 := fun _ => rfl
  have hcompl : ∀ s : R × S,
      s ∈ (q.prod (⊤ : Ideal S)).primeCompl ↔ s.1 ∈ q.primeCompl := by
    intro s
    simp [Ideal.primeCompl]
  have : IsLocalization (q.prod (⊤ : Ideal S)).primeCompl (Localization.AtPrime q) := by
    refine ⟨?_, ?_, ?_⟩
    · intro s
      rw [hmap]
      exact IsLocalization.map_units (M := q.primeCompl) _
        ⟨(s : R × S).1, (hcompl (s : R × S)).mp s.2⟩
    · intro z
      obtain ⟨⟨x, s⟩, hs⟩ := IsLocalization.surj (M := q.primeCompl) z
      refine ⟨⟨(x, 0), ⟨((s : R), (1 : S)), (hcompl ((s : R), (1 : S))).mpr s.2⟩⟩, ?_⟩
      rw [hmap, hmap]
      exact hs
    · intro x y h
      rw [hmap, hmap] at h
      obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists q.primeCompl _).mp h
      exact ⟨⟨((c : R), (0 : S)), (hcompl ((c : R), (0 : S))).mpr c.2⟩, Prod.ext hc (by simp)⟩
  let : IsScalarTower A (R × S) (Localization.AtPrime q) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [hmap]
      exact IsScalarTower.algebraMap_apply A R (Localization.AtPrime q) a
  exact (Algebra.QuasiFinite.iff_of_algEquiv
    ((IsLocalization.algEquiv (q.prod (⊤ : Ideal S)).primeCompl
      (Localization.AtPrime (q.prod (⊤ : Ideal S)))
      (Localization.AtPrime q)).restrictScalars A)).mpr inferInstance

/-- **A prime of a product of algebras coming from a quasi-finite prime of the second factor is
quasi-finite.** This is `quasiFiniteAt_prod_top` read through the isomorphism `prodCommAlgEquiv`
that exchanges the two factors. -/
theorem quasiFiniteAt_top_prod (q : Ideal S) [q.IsPrime]
    [Algebra.QuasiFiniteAt A q] [((⊤ : Ideal R).prod q).IsPrime] :
    Algebra.QuasiFiniteAt A ((⊤ : Ideal R).prod q) := by
  have hp : (q.prod (⊤ : Ideal R)).IsPrime := Ideal.isPrime_ideal_prod_top
  have h₁ : Algebra.QuasiFiniteAt A (q.prod (⊤ : Ideal R)) := quasiFiniteAt_prod_top q
  have hswap : (q.prod (⊤ : Ideal R)).comap (prodCommAlgEquiv A R S).toRingHom =
      (⊤ : Ideal R).prod q := by
    ext x
    simp [Ideal.mem_prod, prodCommAlgEquiv, RingEquiv.prodComm]
  exact quasiFiniteAt_congr hswap
    (Algebra.QuasiFiniteAt.comap_algEquiv _ (prodCommAlgEquiv A R S))

/-- **The nowhere quasi-finite factor of [Stacks, Tag 00UL] has no prime on a module-finite side.**
If no prime of `R × S` lying over `p` and avoiding `x` is quasi-finite over `A`, and `R` is
module-finite over `A`, then the first component of `x` lies in *every* prime of `R` over `p` —
equivalently, `Spec R[1/x.1]` has no point over `p`.

Applied with `x` the idempotent cutting out the last factor of the decomposition of
[Stacks, Tag 00UL], this is what deletes that factor from the finite half of the product. -/
theorem forall_mem_of_forall_not_quasiFiniteAt_prod_top [Module.Finite A R]
    (p : Ideal A) [p.IsPrime] (x : R × S)
    (h : ∀ Q : Ideal (R × S), ∀ _ : Q.IsPrime, Q.LiesOver p → x ∉ Q →
      ¬ Algebra.QuasiFiniteAt A Q)
    (q : Ideal R) [q.IsPrime] [q.LiesOver p] : x.1 ∈ q := by
  by_contra hx
  have hprime : (q.prod (⊤ : Ideal S)).IsPrime := Ideal.isPrime_ideal_prod_top
  have : (q.prod (⊤ : Ideal S)).LiesOver p := liesOver_prod_top p q
  refine h _ hprime inferInstance ?_ (quasiFiniteAt_prod_top q)
  simpa [Ideal.mem_prod] using hx

end Prod

/-- **An idempotent in every prime over `p` of an integral algebra annihilates a unit of `κ(p)`.**
If `b` is idempotent and lies in every prime of `R` over `p`, then `Spec R[1/b]` has no point over
`p`, so by `exists_notMem_algebraMap_eq_zero_of_forall_not_liesOver` applied to the quotient
`R ⧸ (1 - b)` — which is `R[1/b]` — there is an `a ∉ p` with `b · a = 0` in `R`.

Together with `forall_mem_of_forall_not_quasiFiniteAt_prod_top` this removes the factor of
[Stacks, Tag 00UL] that is quasi-finite at no prime over `p` from the finite half of the product
it is applied to, at the cost of shrinking the base by inverting `a`. -/
theorem exists_notMem_mul_algebraMap_eq_zero_of_forall_mem [Algebra A R]
    [Algebra.IsIntegral A R] (p : Ideal A) [p.IsPrime] {b : R} (hb : IsIdempotentElem b)
    (h : ∀ q : Ideal R, q.IsPrime → q.LiesOver p → b ∈ q) :
    ∃ a ∉ p, b * algebraMap A R a = 0 := by
  have hnone : ∀ Q : Ideal (R ⧸ Ideal.span {(1 : R) - b}), Q.IsPrime → ¬ Q.LiesOver p := by
    intro Q hQ hQp
    have hqp : (Q.comap (Ideal.Quotient.mk (Ideal.span {(1 : R) - b}))).IsPrime := hQ.comap _
    have : (Q.comap (Ideal.Quotient.mk (Ideal.span {(1 : R) - b}))).LiesOver p := by
      refine ⟨hQp.over.trans (Ideal.ext fun c => ?_)⟩
      simp [Ideal.under, Ideal.mem_comap]
    have hb' : b ∈ Q.comap (Ideal.Quotient.mk (Ideal.span {(1 : R) - b})) :=
      h _ hqp inferInstance
    have h1b : (1 : R) - b ∈ Q.comap (Ideal.Quotient.mk (Ideal.span {(1 : R) - b})) := by
      refine Ideal.mem_comap.mpr ?_
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)]
      exact Q.zero_mem
    exact hqp.ne_top ((Ideal.eq_top_iff_one _).mpr (by
      simpa using (Q.comap (Ideal.Quotient.mk (Ideal.span {(1 : R) - b}))).add_mem h1b hb'))
  obtain ⟨a, hap, ha⟩ := exists_notMem_algebraMap_eq_zero_of_forall_not_liesOver
    (T := R ⧸ Ideal.span {(1 : R) - b}) p hnone
  refine ⟨a, hap, ?_⟩
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp ha)
  rw [← hr, show b * (r * ((1 : R) - b)) = r * (b - b * b) by ring, hb.eq]
  simp

variable [Algebra R S]

/-- If `Spec S → Spec R` has open image and some prime `s` of `S` lies over `t`, then its image
contains a basic open neighbourhood of `t`. Equivalently: after inverting a single element outside
`t`, the map `Spec S → Spec R` becomes surjective.

The image is open for instance when `R → S` is flat and of finite presentation, so in particular
when it is étale. -/
theorem exists_notMem_basicOpen_subset_range_comap
    {t : Ideal R} [t.IsPrime] {s : Ideal S} [s.IsPrime] [s.LiesOver t]
    (h : IsOpen (Set.range (PrimeSpectrum.comap (algebraMap R S)))) :
    ∃ a ∉ t, (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum R)) ⊆
      Set.range (PrimeSpectrum.comap (algebraMap R S)) := by
  have hmem : (⟨t, ‹t.IsPrime›⟩ : PrimeSpectrum R) ∈
      Set.range (PrimeSpectrum.comap (algebraMap R S)) := by
    refine ⟨⟨s, ‹s.IsPrime›⟩, ?_⟩
    ext : 1
    exact (s.over_def t).symm
  obtain ⟨-, ⟨a, rfl⟩, ha, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hmem h
  exact ⟨a, ha, hsub⟩

/-- **A finite flat algebra with a single prime over `t` and trivial residue field extension there
is trivial after one localisation.** Let `R → S` be finite, flat and unramified at a prime `s`,
let `t` be the prime of `R` below `s`, and assume that `s` is the only prime of `S` over `t`, that
`Spec S → Spec R` is surjective, and that `κ(t) → κ(s)` is surjective. Then there is an `r ∉ t`
such that `R[1/r'] → S[1/r']` is an isomorphism for every multiple `r'` of `r`.

This is `Localization.exists_awayMap_bijective_of_residueField_surjective` with the hypothesis
`FaithfulSMul R S` replaced by surjectivity of `Spec S → Spec R`, which yields it: a flat algebra
surjective on spectra is faithfully flat, hence its structure map is injective. Surjectivity is
the form the hypothesis takes in practice, because it is what
`exists_notMem_basicOpen_subset_range_comap` produces. -/
theorem exists_notMem_bijective_awayMap
    {t : Ideal R} [t.IsPrime] {s : Ideal S} [s.IsPrime] [s.LiesOver t]
    [Algebra (Localization.AtPrime t) (Localization.AtPrime s)]
    [Localization.AtPrime.IsLiesOverAlgebra t s]
    [Module.Finite R S] [Module.Flat R S] [Algebra.IsUnramifiedAt R s]
    (hs : t.primesOver S = {s})
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R S)))
    (h : Function.Surjective (algebraMap t.ResidueField s.ResidueField)) :
    ∃ r ∉ t, ∀ r', r ∣ r' → Function.Bijective (Localization.awayMap (algebraMap R S) r') := by
  have : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_comap_surjective hsurj
  exact Localization.exists_awayMap_bijective_of_residueField_surjective hs h

/-- **The trivialisation step of the finite case of property (B).** In the situation delivered by
[Stacks, Tag 00UL] — a base ring `A` with a prime `p`, a finite `A`-algebra `R` with a prime `t`
over `p`, and an `R`-algebra `S` which is finite and flat over `R` and unramified at a prime `s`
over `t`, where `s` is the only prime of `S` over `t` and `κ(s)/κ(p)` is purely inseparable — the
map `R → S` becomes an isomorphism after inverting a single element of `R` outside `t`, provided
`Spec S → Spec R` is surjective.

The purely inseparable residue field extension is what replaces any assumption on `κ(t) → κ(s)`:
by `bijective_algebraMap_residueField_of_isPurelyInseparable` it is automatically trivial. -/
theorem exists_notMem_bijective_awayMap_of_isPurelyInseparable
    [Algebra A R] [Algebra A S] [IsScalarTower A R S]
    (p : Ideal A) [p.IsPrime] (t : Ideal R) [t.IsPrime] [t.LiesOver p]
    (s : Ideal S) [s.IsPrime] [s.LiesOver t] [s.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime t)]
    [Localization.AtPrime.IsLiesOverAlgebra p t]
    [Algebra (Localization.AtPrime t) (Localization.AtPrime s)]
    [Localization.AtPrime.IsLiesOverAlgebra t s]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime s)]
    [Localization.AtPrime.IsLiesOverAlgebra p s]
    [Module.Finite R S] [Module.Flat R S] [Algebra.IsUnramifiedAt R s]
    (hs : t.primesOver S = {s})
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R S)))
    (h : IsPurelyInseparable p.ResidueField s.ResidueField) :
    ∃ r ∉ t, ∀ r', r ∣ r' → Function.Bijective (Localization.awayMap (algebraMap R S) r') := by
  have hres : Function.Surjective (algebraMap t.ResidueField s.ResidueField) :=
    (bijective_algebraMap_residueField_of_isPurelyInseparable p t s h).2
  exact exists_notMem_bijective_awayMap hs hsurj hres

section LocalStructureTransport

open TensorProduct

/-- **A ring homomorphism out of a residue field is determined by its restriction to the ring.**
The residue field `κ(I)` is the fraction field of `R ⧸ I`, so a homomorphism out of it is
determined by its restriction to `R ⧸ I`, and hence — `R → R ⧸ I` being surjective — by its
restriction to `R`. -/
theorem ringHom_ext_residueField {R F : Type*} [CommRing R] [Field F] (I : Ideal R) [I.IsPrime]
    {φ ψ : I.ResidueField →+* F}
    (h : ∀ x : R, φ (algebraMap R I.ResidueField x) = ψ (algebraMap R I.ResidueField x)) :
    φ = ψ := by
  refine IsLocalization.ringHom_ext (M := nonZeroDivisors (R ⧸ I)) (RingHom.ext fun x => ?_)
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  simpa [Ideal.algebraMap_quotient_residueField_mk] using h y

/-- The contraction of a prime along a homomorphism of algebras lies over whatever the prime lies
over, because the homomorphism commutes with the structure maps. -/
theorem liesOver_comap {A R S : Type*} [CommRing A] [CommRing R] [CommRing S]
    [Algebra A R] [Algebra A S] (f : R →ₐ[A] S) (p : Ideal A) (q : Ideal S) [q.LiesOver p] :
    (q.comap f.toRingHom).LiesOver p := by
  refine ⟨?_⟩
  rw [Ideal.under_def, Ideal.comap_comap]
  show p = Ideal.comap ((f : R →+* S).comp (algebraMap A R)) q
  rw [AlgHom.comp_algebraMap]
  exact q.over_def p

/-- **Module-finiteness of a localization away from an idempotent passes to a quotient algebra.**
If `f : R → S` is a surjection of `A`-algebras and `f x` is idempotent, then `S[1/f x]` is a
quotient of `R[1/x]`, hence module-finite over `A` as soon as `R[1/x]` is.

The map `R[1/x] → S[1/f x]` exists because `f x` becomes `1` in `S[1/f x]`, and it is surjective
because `S → S[1/f x]` already is: inverting an idempotent is a quotient. This is how the
module-finiteness of the factors of the decomposition of [Stacks, Tag 00UL] is read on the image of
that decomposition under a projection. -/
theorem moduleFinite_away_of_surjective
    {A R S : Type*} [CommRing A] [CommRing R] [CommRing S] [Algebra A R] [Algebra A S]
    (f : R →ₐ[A] S) (hf : Function.Surjective f) (x : R) {y : S} (hxy : f x = y)
    (hy : IsIdempotentElem y) [Module.Finite A (Localization.Away x)] :
    Module.Finite A (Localization.Away y) := by
  have hone : algebraMap S (Localization.Away y) y = 1 :=
    IsLocalization.Away.algebraMap_eq_one_of_isIdempotentElem hy
  let F : R →ₐ[A] Localization.Away y := (IsScalarTower.toAlgHom A S _).comp f
  have hF : ∀ r, F r = algebraMap S (Localization.Away y) (f r) := fun _ => rfl
  have hunit : ∀ z : Submonoid.powers x, IsUnit (F z) := by
    rintro ⟨-, n, rfl⟩
    rw [hF, map_pow, map_pow, hxy, hone, one_pow]
    exact isUnit_one
  let g : Localization.Away x →ₐ[A] Localization.Away y := IsLocalization.liftAlgHom hunit
  refine Module.Finite.of_surjective g.toLinearMap fun z => ?_
  obtain ⟨s, rfl⟩ := IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem
    (S := Localization.Away y) y hy z
  obtain ⟨r, rfl⟩ := hf s
  exact ⟨algebraMap R _ r, IsLocalization.lift_eq hunit r⟩

/-- **Pure inseparability of a residue field extension passes along a map surjective on stalks.**
Let `f : R → S` be a homomorphism of `A`-algebras which is surjective on stalks, let `p` be a prime
of `A`, let `q₂` be a prime of `S` over `p` and let `q₁ = f⁻¹(q₂)`. If `κ(q₁)/κ(p)` is purely
inseparable then so is `κ(q₂)/κ(p)`.

Surjectivity on stalks makes `κ(q₁) → κ(q₂)` bijective, and the resulting isomorphism is
automatically one of `κ(p)`-algebras: it is a homomorphism of `A`-algebras, and by
`ringHom_ext_residueField` a homomorphism out of `κ(p)` is determined by its restriction to `A`.

Two kinds of map are surjective on stalks and both occur in the finite case of property (B),
[Stacks, Tag 04DQ]: a surjection, which is
`isPurelyInseparable_residueField_of_surjective` below, and a localisation, by
`RingHom.surjectiveOnStalks_of_isLocalization` — the latter is what transports the residue field
information of [Stacks, Tag 00UL] through the shrinkings of the base. -/
theorem isPurelyInseparable_residueField_of_surjectiveOnStalks
    {A R S : Type*} [CommRing A] [CommRing R] [CommRing S] [Algebra A R] [Algebra A S]
    (p : Ideal A) [p.IsPrime] (f : R →ₐ[A] S) (hf : (f : R →+* S).SurjectiveOnStalks)
    (q₁ : Ideal R) [q₁.IsPrime] [q₁.LiesOver p]
    (q₂ : Ideal S) [q₂.IsPrime] [q₂.LiesOver p]
    (hq : q₁ = q₂.comap f.toRingHom)
    (h : letI := Localization.AtPrime.algebraOfLiesOver p q₁
      IsPurelyInseparable p.ResidueField q₁.ResidueField) :
    letI := Localization.AtPrime.algebraOfLiesOver p q₂
    IsPurelyInseparable p.ResidueField q₂.ResidueField := by
  let := Localization.AtPrime.algebraOfLiesOver p q₁
  let := Localization.AtPrime.algebraOfLiesOver p q₂
  have hbij : Function.Bijective (Ideal.ResidueField.map q₁ q₂ f.toRingHom hq) :=
    hf.residueFieldMap_bijective q₁ q₂ hq
  have key : (Ideal.ResidueField.map q₁ q₂ f.toRingHom hq).comp
      (algebraMap p.ResidueField q₁.ResidueField) =
      algebraMap p.ResidueField q₂.ResidueField := by
    refine ringHom_ext_residueField p fun x => ?_
    simp only [RingHom.comp_apply,
      ← IsScalarTower.algebraMap_apply A p.ResidueField q₁.ResidueField,
      ← IsScalarTower.algebraMap_apply A p.ResidueField q₂.ResidueField,
      IsScalarTower.algebraMap_apply A R q₁.ResidueField,
      IsScalarTower.algebraMap_apply A S q₂.ResidueField,
      Ideal.ResidueField.map_algebraMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.commutes]
  exact AlgEquiv.isPurelyInseparable
    ({ RingEquiv.ofBijective _ hbij with
        commutes' := fun x => RingHom.congr_fun key x } :
      q₁.ResidueField ≃ₐ[p.ResidueField] q₂.ResidueField)

/-- **Pure inseparability of a residue field extension passes along a surjection.** Let
`f : R → S` be a surjection of `A`-algebras, let `p` be a prime of `A`, let `q₂` be a prime of `S`
over `p` and let `q₁ = f⁻¹(q₂)`. If `κ(q₁)/κ(p)` is purely inseparable then so is `κ(q₂)/κ(p)`.

Surjectivity makes `κ(q₁) → κ(q₂)` bijective, and the resulting isomorphism is automatically one of
`κ(p)`-algebras: it is a homomorphism of `A`-algebras, and by `ringHom_ext_residueField` a
homomorphism out of `κ(p)` is determined by its restriction to `A`. This is
`isPurelyInseparable_residueField_of_surjectiveOnStalks` for a surjection. -/
theorem isPurelyInseparable_residueField_of_surjective
    {A R S : Type*} [CommRing A] [CommRing R] [CommRing S] [Algebra A R] [Algebra A S]
    (p : Ideal A) [p.IsPrime] (f : R →ₐ[A] S) (hf : Function.Surjective f)
    (q₁ : Ideal R) [q₁.IsPrime] [q₁.LiesOver p]
    (q₂ : Ideal S) [q₂.IsPrime] [q₂.LiesOver p]
    (hq : q₁ = q₂.comap f.toRingHom)
    (h : letI := Localization.AtPrime.algebraOfLiesOver p q₁
      IsPurelyInseparable p.ResidueField q₁.ResidueField) :
    letI := Localization.AtPrime.algebraOfLiesOver p q₂
    IsPurelyInseparable p.ResidueField q₂.ResidueField :=
  isPurelyInseparable_residueField_of_surjectiveOnStalks p f
    (RingHom.surjectiveOnStalks_of_surjective hf) q₁ q₂ hq h

/-- **The conclusions of [Stacks, Tag 00UL] transported along a surjection onto a factor.** Let
`T` be an `A'`-algebra carrying the data the étale local structure theorem produces at a prime `p'`
of `A'`: complete orthogonal idempotents `e 0, …, e n`, with the first `n` factors `T[1/e i]`
module-finite over `A'` and carrying a unique prime `r i` over `p'` whose residue field is purely
inseparable over `κ(p')`, and with the last factor quasi-finite at no prime over `p'`. Let
`π : T → D` be a surjection of `A'`-algebras which carries quasi-finiteness at a prime of `D` to
quasi-finiteness at its contraction. Then the images `π (e i)` have the same four properties on
`D`:

* each `D[1/π (e i)]` is module-finite over `A'`;
* each has *at most* one prime over `p'`;
* the residue field of such a prime is purely inseparable over `κ(p')`;
* the last factor `D[1/π (e n)]` is quasi-finite at no prime over `p'`.

Uniqueness becomes "at most one" because the unique prime `r i` of `T[1/e i]` over `p'` need not
come from `D` at all; when it does not, `D[1/π (e i)]` simply has no prime over `p'`. The
quasi-finiteness hypothesis on `π` is what rules out a prime of `D` over `p'` landing in the last
factor; for a projection of a product it is `quasiFiniteAt_prod_top`. -/
theorem localStructure_image_of_surjective
    {A' T D : Type*} [CommRing A'] [CommRing T] [CommRing D] [Algebra A' T] [Algebra A' D]
    (p' : Ideal A') [p'.IsPrime] {n : ℕ} (e : Fin (n + 1) → T)
    (hidem : ∀ i, IsIdempotentElem (e i))
    (r : Fin n → Ideal T) (hrp : ∀ i, (r i).IsPrime) (hro : ∀ i, (r i).LiesOver p')
    (hfin : ∀ i : Fin n, Module.Finite A' (Localization.Away (e i.castSucc)))
    (huniq : ∀ (i : Fin n) (q : Ideal T), q.IsPrime → q.LiesOver p' → e i.castSucc ∉ q → q = r i)
    (hres : ∀ i : Fin n, letI := Localization.AtPrime.algebraOfLiesOver p' (r i)
      IsPurelyInseparable p'.ResidueField (r i).ResidueField)
    (hlast : ∀ q : Ideal T, ∀ _ : q.IsPrime, q.LiesOver p' → e (Fin.last n) ∉ q →
      ¬ Algebra.QuasiFiniteAt A' q)
    (π : T →ₐ[A'] D) (hπ : Function.Surjective π)
    (hqf : ∀ q : Ideal D, ∀ _ : q.IsPrime, Algebra.QuasiFiniteAt A' q →
      Algebra.QuasiFiniteAt A' (q.comap π.toRingHom)) :
    (∀ i : Fin n, Module.Finite A' (Localization.Away (π (e i.castSucc)))) ∧
    (∀ (i : Fin n) (q₁ q₂ : Ideal D), ∀ _ : q₁.IsPrime, ∀ _ : q₂.IsPrime,
      q₁.LiesOver p' → q₂.LiesOver p' →
      π (e i.castSucc) ∉ q₁ → π (e i.castSucc) ∉ q₂ → q₁ = q₂) ∧
    (∀ (i : Fin n) (q : Ideal D), ∀ _ : q.IsPrime, ∀ _ : q.LiesOver p', π (e i.castSucc) ∉ q →
      letI := Localization.AtPrime.algebraOfLiesOver p' q
      IsPurelyInseparable p'.ResidueField q.ResidueField) ∧
    (∀ q : Ideal D, ∀ _ : q.IsPrime, q.LiesOver p' → π (e (Fin.last n)) ∉ q →
      ¬ Algebra.QuasiFiniteAt A' q) := by
  refine ⟨fun i => ?_, fun i q₁ q₂ h₁ h₂ ho₁ ho₂ hn₁ hn₂ => ?_, fun i q hq hqo hn => ?_,
    fun q hq hqo hn hqfa => ?_⟩
  · have := hfin i
    exact moduleFinite_away_of_surjective π hπ (e i.castSucc) rfl ((hidem _).map π.toRingHom)
  · have k₁ : q₁.comap π.toRingHom = r i :=
      huniq i _ inferInstance (liesOver_comap π p' q₁) (by simpa using hn₁)
    have k₂ : q₂.comap π.toRingHom = r i :=
      huniq i _ inferInstance (liesOver_comap π p' q₂) (by simpa using hn₂)
    exact Ideal.comap_injective_of_surjective (π : T →+* D) hπ (k₁.trans k₂.symm)
  · have := hrp i
    have := hro i
    have hri : r i = q.comap π.toRingHom :=
      (huniq i _ inferInstance (liesOver_comap π p' q) (by simpa using hn)).symm
    exact isPurelyInseparable_residueField_of_surjective p' π hπ (r i) q hri (hres i)
  · exact hlast (q.comap π.toRingHom) inferInstance (liesOver_comap π p' q)
      (by simpa using hn) (hqf q hq hqfa)

/-- A quasi-finite prime of `X` contracts along the first projection of a decomposition
`T ≃ₐ X × Y` to a quasi-finite prime. -/
private theorem quasiFiniteAt_comap_fst_comp {A' T X Y : Type*} [CommRing A'] [CommRing T]
    [CommRing X] [CommRing Y] [Algebra A' T] [Algebra A' X] [Algebra A' Y] (ι : T ≃ₐ[A'] X × Y)
    (q : Ideal X) [q.IsPrime] [Algebra.QuasiFiniteAt A' q] :
    Algebra.QuasiFiniteAt A' (q.comap ((AlgHom.fst A' X Y).comp ι.toAlgHom).toRingHom) := by
  have : (q.prod (⊤ : Ideal Y)).IsPrime := Ideal.isPrime_ideal_prod_top
  have : Algebra.QuasiFiniteAt A' (q.prod (⊤ : Ideal Y)) := quasiFiniteAt_prod_top q
  have h : q.comap ((AlgHom.fst A' X Y).comp ι.toAlgHom).toRingHom =
      (q.prod (⊤ : Ideal Y)).comap ι.toRingHom := by
    ext x
    simp [Ideal.mem_comap]
  exact quasiFiniteAt_congr h.symm (Algebra.QuasiFiniteAt.comap_algEquiv _ ι)

/-- A quasi-finite prime of `Y` contracts along the second projection of a decomposition
`T ≃ₐ X × Y` to a quasi-finite prime. -/
private theorem quasiFiniteAt_comap_snd_comp {A' T X Y : Type*} [CommRing A'] [CommRing T]
    [CommRing X] [CommRing Y] [Algebra A' T] [Algebra A' X] [Algebra A' Y] (ι : T ≃ₐ[A'] X × Y)
    (q : Ideal Y) [q.IsPrime] [Algebra.QuasiFiniteAt A' q] :
    Algebra.QuasiFiniteAt A' (q.comap ((AlgHom.snd A' X Y).comp ι.toAlgHom).toRingHom) := by
  have : ((⊤ : Ideal X).prod q).IsPrime := Ideal.isPrime_ideal_prod_top'
  have : Algebra.QuasiFiniteAt A' ((⊤ : Ideal X).prod q) := quasiFiniteAt_top_prod q
  have h : q.comap ((AlgHom.snd A' X Y).comp ι.toAlgHom).toRingHom =
      ((⊤ : Ideal X).prod q).comap ι.toRingHom := by
    ext x
    simp [Ideal.mem_comap]
  exact quasiFiniteAt_congr h.symm (Algebra.QuasiFiniteAt.comap_algEquiv _ ι)

/-- **[Stacks, Tag 00UL] for a product algebra, split across the two factors.** Let `B` and `C` be
`A`-algebras whose product is of finite type over `A`, and let `p` be a prime of `A`. There are an
étale `A`-algebra `A'`, a prime `p'` of `A'` over `p` and complete orthogonal idempotents
`b 0, …, b n` of `A' ⊗[A] B` and `c 0, …, c n` of `A' ⊗[A] C` — the two components of the
idempotents the local structure theorem produces on `A' ⊗[A] (B × C)` — such that on each side:

* the factors `[1/b i]`, `[1/c i]` with `i < n` are module-finite over `A'`;
* each of them has at most one prime over `p'`;
* the residue field of such a prime is purely inseparable over `κ(p')`;
* the last factors `[1/b n]`, `[1/c n]` are quasi-finite at no prime over `p'`.

This is the single application of [Stacks, Tag 00UL] on which the finite case of property (B),
[Stacks, Tag 04DQ], rests: `B` is the ring of the fibre product `X ×ₗᵧ V₀` and `C` the ring of a
single affine étale surjection onto it obtained from the given covering, so that `B` is
module-finite over `A` and `C` is étale over `B`. Splitting the decomposition across the two
factors is what lets the pieces of the `B`-side be matched with pieces of the `C`-side, which is
where the covering gets refined.

The decomposition of `A' ⊗[A] (B × C)` is recovered from the two halves through
`Algebra.TensorProduct.prodRight`, whose components the idempotents `b` and `c` are. -/
theorem exists_etale_completeOrthogonalIdempotents_prod
    {A : Type u} {B C : Type v} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra.FiniteType A (B × C)] (p : Ideal A) [p.IsPrime] :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Algebra.Etale A A')
      (p' : Ideal A') (_ : p'.IsPrime) (_ : p'.LiesOver p) (n : ℕ)
      (b : Fin (n + 1) → A' ⊗[A] B) (c : Fin (n + 1) → A' ⊗[A] C)
      (_ : CompleteOrthogonalIdempotents b) (_ : CompleteOrthogonalIdempotents c),
      ((∀ i : Fin n, Module.Finite A' (Localization.Away (b i.castSucc))) ∧
        (∀ (i : Fin n) (q₁ q₂ : Ideal (A' ⊗[A] B)), ∀ _ : q₁.IsPrime, ∀ _ : q₂.IsPrime,
          q₁.LiesOver p' → q₂.LiesOver p' → b i.castSucc ∉ q₁ → b i.castSucc ∉ q₂ → q₁ = q₂) ∧
        (∀ (i : Fin n) (q : Ideal (A' ⊗[A] B)), ∀ _ : q.IsPrime, ∀ _ : q.LiesOver p',
          b i.castSucc ∉ q →
          letI := Localization.AtPrime.algebraOfLiesOver p' q
          IsPurelyInseparable p'.ResidueField q.ResidueField) ∧
        (∀ q : Ideal (A' ⊗[A] B), ∀ _ : q.IsPrime, q.LiesOver p' → b (Fin.last n) ∉ q →
          ¬ Algebra.QuasiFiniteAt A' q)) ∧
      ((∀ i : Fin n, Module.Finite A' (Localization.Away (c i.castSucc))) ∧
        (∀ (i : Fin n) (q₁ q₂ : Ideal (A' ⊗[A] C)), ∀ _ : q₁.IsPrime, ∀ _ : q₂.IsPrime,
          q₁.LiesOver p' → q₂.LiesOver p' → c i.castSucc ∉ q₁ → c i.castSucc ∉ q₂ → q₁ = q₂) ∧
        (∀ (i : Fin n) (q : Ideal (A' ⊗[A] C)), ∀ _ : q.IsPrime, ∀ _ : q.LiesOver p',
          c i.castSucc ∉ q →
          letI := Localization.AtPrime.algebraOfLiesOver p' q
          IsPurelyInseparable p'.ResidueField q.ResidueField) ∧
        (∀ q : Ideal (A' ⊗[A] C), ∀ _ : q.IsPrime, q.LiesOver p' → c (Fin.last n) ∉ q →
          ¬ Algebra.QuasiFiniteAt A' q)) := by
  obtain ⟨A', _, _, _, p', _, _, n, e, hco, r, hrp, hro, hfin, hnot, huniq, hres, hlast⟩ :=
    Algebra.exists_etale_completeOrthogonalIdempotents_finite_isPurelyInseparable
      (R := A) (S := B × C) p
  let ι : A' ⊗[A] (B × C) ≃ₐ[A'] (A' ⊗[A] B) × (A' ⊗[A] C) :=
    Algebra.TensorProduct.prodRight A A' A' B C
  let πB : A' ⊗[A] (B × C) →ₐ[A'] A' ⊗[A] B := (AlgHom.fst A' _ _).comp ι.toAlgHom
  let πC : A' ⊗[A] (B × C) →ₐ[A'] A' ⊗[A] C := (AlgHom.snd A' _ _).comp ι.toAlgHom
  have hBsurj : Function.Surjective πB := Prod.fst_surjective.comp ι.surjective
  have hCsurj : Function.Surjective πC := Prod.snd_surjective.comp ι.surjective
  refine ⟨A', ‹_›, ‹_›, ‹_›, p', ‹_›, ‹_›, n, fun i => πB (e i), fun i => πC (e i),
    hco.map πB.toRingHom, hco.map πC.toRingHom, ?_, ?_⟩
  · refine localStructure_image_of_surjective p' e hco.idem r hrp hro hfin huniq
      (fun i => (hres i).2) hlast πB hBsurj ?_
    intro q hq hqfa
    exact quasiFiniteAt_comap_fst_comp ι q
  · refine localStructure_image_of_surjective p' e hco.idem r hrp hro hfin huniq
      (fun i => (hres i).2) hlast πC hCsurj ?_
    intro q hq hqfa
    exact quasiFiniteAt_comap_snd_comp ι q

end LocalStructureTransport

section Shrinking

/-- An element annihilated by `x` becomes zero once `x` is inverted. -/
theorem algebraMap_eq_zero_of_mul_eq_zero {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]
    (x : R) [IsLocalization.Away x T] {y : R} (h : y * x = 0) : algebraMap R T y = 0 := by
  have hu : IsUnit (algebraMap R T x) := IsLocalization.Away.algebraMap_isUnit x
  refine hu.mul_left_eq_zero.mp ?_
  rw [← map_mul, h, map_zero]

/-- **Finitely many shrinkings of the base are performed at once.** Let `p` be a prime of `A` and
let `Q i` be a property of elements of `A` which, for each of finitely many indices `i`, holds of
every multiple of some element outside `p`. Then a single element outside `p` — and indeed every
multiple of it — has all the properties `Q i` at once.

The element is the product of the ones supplied for the individual indices, which stays outside
`p` because `p` is prime and is a multiple of each factor. This is the mechanism by which the
finite case of property (B), [Stacks, Tag 04DQ], performs the finitely many shrinkings of its base
demanded by the finitely many pieces of its decomposition in one step: the étale neighbourhood it
produces must be a single scheme. It is the reason the shrinking steps below are stated for every
multiple of the element they produce rather than for that element alone — only in that form do
they compose. -/
theorem exists_notMem_forall_dvd_of_forall_exists {A : Type*} [CommRing A] (p : Ideal A)
    [p.IsPrime] {ι : Type*} [Finite ι] (Q : ι → A → Prop)
    (h : ∀ i, ∃ a ∉ p, ∀ a' : A, a ∣ a' → Q i a') :
    ∃ a ∉ p, ∀ a' : A, a ∣ a' → ∀ i, Q i a' := by
  classical
  cases nonempty_fintype ι
  choose a hap ha using h
  refine ⟨∏ i, a i, Submonoid.prod_mem p.primeCompl fun i _ => hap i, fun a' hdvd i => ?_⟩
  exact ha i a' ((Finset.dvd_prod_of_mem a (Finset.mem_univ i)).trans hdvd)

/-- **Finitely many empty factors are removed by a single localisation, stably under further
shrinking.** If each of finitely many idempotents `b i` of an algebra `R` integral over `A` lies in
every prime of `R` over `p` — that is, if `Spec R[1/b i]` has no point over `p` — then a single
element `a ∉ p` annihilates all of them at once, and so does every multiple of `a`.

Each index contributes one element by
`exists_notMem_mul_algebraMap_eq_zero_of_forall_mem`, and annihilating is stable under passing to
a multiple; `exists_notMem_forall_dvd_of_forall_exists` combines them. -/
theorem exists_notMem_forall_dvd_forall_mul_algebraMap_eq_zero
    {A R : Type*} [CommRing A] [CommRing R] [Algebra A R] [Algebra.IsIntegral A R]
    (p : Ideal A) [p.IsPrime] {ι : Type*} [Finite ι] (b : ι → R)
    (hb : ∀ i, IsIdempotentElem (b i))
    (h : ∀ (i : ι) (q : Ideal R), q.IsPrime → q.LiesOver p → b i ∈ q) :
    ∃ a ∉ p, ∀ a' : A, a ∣ a' → ∀ i, b i * algebraMap A R a' = 0 := by
  refine exists_notMem_forall_dvd_of_forall_exists p
    (fun i a => b i * algebraMap A R a = 0) fun i => ?_
  obtain ⟨a, hap, ha⟩ := exists_notMem_mul_algebraMap_eq_zero_of_forall_mem p (hb i) (h i)
  refine ⟨a, hap, fun a' hdvd => ?_⟩
  obtain ⟨k, rfl⟩ := hdvd
  rw [map_mul, ← mul_assoc, ha, zero_mul]

/-- **Finitely many empty factors are removed by a single localisation.** This is
`exists_notMem_forall_dvd_forall_mul_algebraMap_eq_zero` at the element it produces. -/
theorem exists_notMem_forall_mul_algebraMap_eq_zero
    {A R : Type*} [CommRing A] [CommRing R] [Algebra A R] [Algebra.IsIntegral A R]
    (p : Ideal A) [p.IsPrime] {ι : Type*} [Finite ι] (b : ι → R)
    (hb : ∀ i, IsIdempotentElem (b i))
    (h : ∀ (i : ι) (q : Ideal R), q.IsPrime → q.LiesOver p → b i ∈ q) :
    ∃ a ∉ p, ∀ i, b i * algebraMap A R a = 0 :=
  let ⟨a, hap, ha⟩ := exists_notMem_forall_dvd_forall_mul_algebraMap_eq_zero p b hb h
  ⟨a, hap, ha a dvd_rfl⟩

/-- **Dropping the vanishing members of a complete orthogonal family.** If every index outside the
range of an embedding `f` carries a zero idempotent, then the subfamily indexed by `f` is still
complete: the sum over the range of `f` is the sum over everything. -/
theorem completeOrthogonalIdempotents_comp_of_eq_zero
    {R : Type*} [CommRing R] {I J : Type*} [Fintype I] [Fintype J]
    {e : I → R} (he : CompleteOrthogonalIdempotents e) (f : J ↪ I)
    (h : ∀ i, i ∉ Set.range f → e i = 0) :
    CompleteOrthogonalIdempotents (e ∘ f) := by
  classical
  refine ⟨he.1.embedding f, ?_⟩
  have h₁ : ∑ i ∈ Finset.univ.image f, e i = ∑ i : I, e i :=
    Finset.sum_subset (Finset.subset_univ _)
      fun i _ hi => h i (by simpa [Finset.mem_image, Set.mem_range] using hi)
  have h₂ : ∑ j : J, (e ∘ f) j = ∑ i ∈ Finset.univ.image f, e i :=
    (Finset.sum_image fun x _ y _ hxy => f.injective hxy).symm
  exact h₂.trans (h₁.trans he.complete)

/-- **The simultaneous shrinking of the base in the finite case of property (B).** Let
`e 0, …, e (n - 1)` be complete orthogonal idempotents of an algebra `R` integral over `A`, let `p`
be a prime of `A`, and let an embedding `f` pick out a set of indices outside which the factor
`R[1/e i]` has no prime over `p`. Then there is a single `a ∉ p` such that in `R[1/a]` the
subfamily `e ∘ f` is *still* a complete orthogonal family of idempotents: all the discarded factors
have become zero, so the decomposition of `R[1/a]` is indexed by the chosen set alone.

This is the shrinking step of [Stacks, Tag 04DQ]: applied on the `B`-side of
`exists_etale_completeOrthogonalIdempotents_prod`, with the chosen indices those whose factor does
carry a prime over `p'`, it turns the decomposition of `A' ⊗[A] B` produced by the local structure
theorem into one indexed exactly by the primes of `A' ⊗[A] B` over `p'`. The discarded indices
include the last one, by
`forall_mem_of_forall_not_quasiFiniteAt_prod_top`. -/
theorem exists_notMem_forall_dvd_completeOrthogonalIdempotents_comp
    {A R : Type*} [CommRing A] [CommRing R] [Algebra A R] [Algebra.IsIntegral A R]
    (p : Ideal A) [p.IsPrime] {n : ℕ} {e : Fin n → R} (he : CompleteOrthogonalIdempotents e)
    {J : Type*} [Fintype J] (f : J ↪ Fin n)
    (hout : ∀ i, i ∉ Set.range f → ∀ q : Ideal R, q.IsPrime → q.LiesOver p → e i ∈ q) :
    ∃ a ∉ p, ∀ a' : A, a ∣ a' → CompleteOrthogonalIdempotents
      (fun j : J => algebraMap R (Localization.Away (algebraMap A R a')) (e (f j))) := by
  classical
  obtain ⟨a, hap, ha⟩ := exists_notMem_forall_dvd_forall_mul_algebraMap_eq_zero p
    (ι := {i : Fin n // i ∉ Set.range f}) (fun i => e i.1) (fun i => he.idem i.1)
    (fun i => hout i.1 i.2)
  refine ⟨a, hap, fun a' hdvd => ?_⟩
  exact completeOrthogonalIdempotents_comp_of_eq_zero
    (he.map (algebraMap R (Localization.Away (algebraMap A R a')))) f
    fun i hi => algebraMap_eq_zero_of_mul_eq_zero _ (ha a' hdvd ⟨i, hi⟩)

/-- **The simultaneous shrinking of the base, at the element it produces.** This is
`exists_notMem_forall_dvd_completeOrthogonalIdempotents_comp` with the conclusion read at the
element produced rather than at all of its multiples. -/
theorem exists_notMem_completeOrthogonalIdempotents_comp
    {A R : Type*} [CommRing A] [CommRing R] [Algebra A R] [Algebra.IsIntegral A R]
    (p : Ideal A) [p.IsPrime] {n : ℕ} {e : Fin n → R} (he : CompleteOrthogonalIdempotents e)
    {J : Type*} [Fintype J] (f : J ↪ Fin n)
    (hout : ∀ i, i ∉ Set.range f → ∀ q : Ideal R, q.IsPrime → q.LiesOver p → e i ∈ q) :
    ∃ a ∉ p, CompleteOrthogonalIdempotents
      (fun j : J => algebraMap R (Localization.Away (algebraMap A R a)) (e (f j))) :=
  let ⟨a, hap, ha⟩ :=
    exists_notMem_forall_dvd_completeOrthogonalIdempotents_comp p he f hout
  ⟨a, hap, ha a dvd_rfl⟩

/-- **A quasi-finite prime lies in one of the finite factors of the decomposition.** Let
`c 0, …, c n` be complete orthogonal idempotents of an algebra `D` over `A'` such that the last
factor `D[1/c n]` is quasi-finite over `A'` at no prime over `p'`, and let `s` be a prime of `D`
over `p'` at which `D` *is* quasi-finite over `A'`. Then `s` avoids one of the first `n`
idempotents, that is, `s` is a prime of one of the factors `D[1/c i]` with `i < n`.

Some idempotent is avoided because they sum to `1` and `s` is a proper ideal; it cannot be the last
one, because `s` is quasi-finite. In the finite case of property (B), [Stacks, Tag 04DQ], this is
what places a prime of the étale covering chosen over a point of the finite side into one of the
*finite* factors of the decomposition of [Stacks, Tag 00UL], which is where the residue field
information lives. -/
theorem exists_castSucc_notMem_of_quasiFiniteAt
    {A' D : Type*} [CommRing A'] [CommRing D] [Algebra A' D] (p' : Ideal A') [p'.IsPrime]
    {n : ℕ} {c : Fin (n + 1) → D} (hc : CompleteOrthogonalIdempotents c)
    (hlast : ∀ q : Ideal D, ∀ _ : q.IsPrime, q.LiesOver p' → c (Fin.last n) ∉ q →
      ¬ Algebra.QuasiFiniteAt A' q)
    (s : Ideal D) [s.IsPrime] [s.LiesOver p'] [Algebra.QuasiFiniteAt A' s] :
    ∃ i : Fin n, c i.castSucc ∉ s := by
  by_contra hall
  simp only [not_exists, not_not] at hall
  refine hlast s inferInstance inferInstance (fun hmem => ?_) inferInstance
  refine ‹s.IsPrime›.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
  have hsum : (∑ i : Fin n, c i.castSucc) + c (Fin.last n) = 1 := by
    rw [← Fin.sum_univ_castSucc]
    exact hc.complete
  rw [← hsum]
  exact s.add_mem (Ideal.sum_mem _ fun i _ => hall i) hmem

open Classical in
/-- **Shrinking the base so that the decomposition is indexed by the primes over `p'`.** Let
`b 0, …, b n` be complete orthogonal idempotents of a module-finite `A'`-algebra `P`, and suppose
the last factor `P[1/b n]` is quasi-finite over `A'` at no prime over `p'`. Then there is a single
`a ∉ p'` such that, in `P[1/a]`, the subfamily of those `b i` with `i < n` whose factor really does
carry a prime over `p'` is *still* a complete orthogonal family: all the other factors have become
zero.

Since `P` is module-finite over `A'` it is quasi-finite at every prime, so the hypothesis forces
`b n` itself to lie in every prime over `p'`; the remaining discarded indices are exactly those
`i < n` for which `P[1/b i]` has no prime over `p'`. This is the step of [Stacks, Tag 04DQ] that
turns the decomposition supplied by the étale local structure theorem into one indexed precisely by
the primes of `P` over `p'`. -/
theorem exists_notMem_forall_dvd_completeOrthogonalIdempotents_liesOver
    {A' P : Type*} [CommRing A'] [CommRing P] [Algebra A' P] [Module.Finite A' P]
    (p' : Ideal A') [p'.IsPrime] {n : ℕ} {b : Fin (n + 1) → P}
    (hb : CompleteOrthogonalIdempotents b)
    (hlast : ∀ q : Ideal P, ∀ _ : q.IsPrime, q.LiesOver p' → b (Fin.last n) ∉ q →
      ¬ Algebra.QuasiFiniteAt A' q) :
    ∃ a ∉ p', ∀ a' : A', a ∣ a' → CompleteOrthogonalIdempotents
      (fun l : {i : Fin n // ∃ q : Ideal P, ∃ _ : q.IsPrime, q.LiesOver p' ∧ b i.castSucc ∉ q} =>
        algebraMap P (Localization.Away (algebraMap A' P a')) (b l.1.castSucc)) := by
  refine exists_notMem_forall_dvd_completeOrthogonalIdempotents_comp p' hb
    ((Function.Embedding.subtype _).trans Fin.castSuccEmb) ?_
  intro i
  induction i using Fin.lastCases with
  | last =>
    intro _ q hq hqp
    by_contra hmem
    exact hlast q hq hqp hmem inferInstance
  | cast k =>
    intro hi q hq hqp
    by_contra hmem
    exact hi ⟨⟨k, q, hq, hqp, hmem⟩, rfl⟩

open Classical in
/-- **Shrinking the base so that the decomposition is indexed by the primes over `p'`, at the
element produced.** This is `exists_notMem_forall_dvd_completeOrthogonalIdempotents_liesOver` with
the conclusion read at the element produced rather than at all of its multiples. -/
theorem exists_notMem_completeOrthogonalIdempotents_liesOver
    {A' P : Type*} [CommRing A'] [CommRing P] [Algebra A' P] [Module.Finite A' P]
    (p' : Ideal A') [p'.IsPrime] {n : ℕ} {b : Fin (n + 1) → P}
    (hb : CompleteOrthogonalIdempotents b)
    (hlast : ∀ q : Ideal P, ∀ _ : q.IsPrime, q.LiesOver p' → b (Fin.last n) ∉ q →
      ¬ Algebra.QuasiFiniteAt A' q) :
    ∃ a ∉ p', CompleteOrthogonalIdempotents
      (fun l : {i : Fin n // ∃ q : Ideal P, ∃ _ : q.IsPrime, q.LiesOver p' ∧ b i.castSucc ∉ q} =>
        algebraMap P (Localization.Away (algebraMap A' P a)) (b l.1.castSucc)) :=
  let ⟨a, hap, ha⟩ :=
    exists_notMem_forall_dvd_completeOrthogonalIdempotents_liesOver p' hb hlast
  ⟨a, hap, ha a dvd_rfl⟩

/-- **Matching a prime of the finite side with a factor of the covering side.** Let `P` be
module-finite over `A'` and let `E` be étale over `P` with `Spec E → Spec P` surjective, and let
`c 0, …, c n` be complete orthogonal idempotents of `E` whose last factor `E[1/c n]` is
quasi-finite over `A'` at no prime over `p'`. Then every prime `t` of `P` over `p'` is the
contraction of a prime `s` of `E` avoiding one of the first `n` idempotents.

Surjectivity produces the prime `s` over `t`; it is quasi-finite over `A'` because `E` is
quasi-finite over `P` — being étale — and `P` is quasi-finite over `A'` — being module-finite — so
`exists_castSucc_notMem_of_quasiFiniteAt` places it in one of the finite factors. This is the step
of [Stacks, Tag 04DQ] that pairs each piece of the finite side with a piece of the étale covering,
which is where the residue fields of the two sides are compared. -/
theorem exists_liesOver_notMem_castSucc
    {A' P E : Type*} [CommRing A'] [CommRing P] [CommRing E] [Algebra A' P] [Algebra A' E]
    [Algebra P E] [IsScalarTower A' P E] [Module.Finite A' P] [Algebra.Etale P E]
    (p' : Ideal A') [p'.IsPrime] {n : ℕ} {c : Fin (n + 1) → E}
    (hc : CompleteOrthogonalIdempotents c)
    (hlast : ∀ q : Ideal E, ∀ _ : q.IsPrime, q.LiesOver p' → c (Fin.last n) ∉ q →
      ¬ Algebra.QuasiFiniteAt A' q)
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap P E)))
    (t : Ideal P) [t.IsPrime] [t.LiesOver p'] :
    ∃ (s : Ideal E) (_ : s.IsPrime), s.LiesOver t ∧ ∃ i : Fin n, c i.castSucc ∉ s := by
  obtain ⟨s, hs⟩ := hsurj ⟨t, ‹t.IsPrime›⟩
  have hsp : s.asIdeal.IsPrime := s.2
  have hover : s.asIdeal.LiesOver t :=
    ⟨show t = Ideal.comap (algebraMap P E) s.asIdeal from (congrArg PrimeSpectrum.asIdeal hs).symm⟩
  have : Algebra.QuasiFinite A' E := Algebra.QuasiFinite.trans A' P E
  have hop : s.asIdeal.LiesOver p' := Ideal.LiesOver.trans s.asIdeal t p'
  exact ⟨s.asIdeal, hsp, hover, exists_castSucc_notMem_of_quasiFiniteAt p' hc hlast s.asIdeal⟩

/-- **At a prime that is the only one over `p'`, all but one member of a complete orthogonal family
lies in every prime over `p'`.** If `q` is forced to equal the prime `s`, and `b l₀ ∉ s`, then
orthogonality `b l · b l₀ = 0` and primality of `s` put every other `b l` inside it.
-/
theorem forall_ne_mem_of_forall_eq
    {A' D : Type*} [CommRing A'] [CommRing D] [Algebra A' D]
    (p' : Ideal A') [p'.IsPrime] {L : Type*} {b : L → D} (hb : OrthogonalIdempotents b)
    (huniq : ∀ q₁ q₂ : Ideal D, q₁.IsPrime → q₂.IsPrime → q₁.LiesOver p' → q₂.LiesOver p' →
      q₁ = q₂)
    (s : Ideal D) [s.IsPrime] [s.LiesOver p'] {l₀ : L} (hl₀ : b l₀ ∉ s)
    (l : L) (hl : l ≠ l₀) (q : Ideal D) (hq : q.IsPrime) (hqo : q.LiesOver p') : b l ∈ q := by
  have hqs : q = s := huniq q s hq inferInstance hqo inferInstance
  subst hqs
  rcases (‹q.IsPrime›.mem_or_mem (show b l * b l₀ ∈ q from hb.ortho hl ▸ q.zero_mem)) with h | h
  · exact h
  · exact absurd h hl₀

/-- **Isolating one factor of a decomposition at a single prime.** Let `D` be integral over `A'`
with at most one prime over `p'`, let `b` be a finite complete orthogonal family of idempotents of
`D`, and let `s` be a prime over `p'` avoiding `b l₀`. Then a single `a ∉ p'` makes `b l₀` equal to
`1` in `D[1/a]`. -/
theorem exists_notMem_forall_dvd_algebraMap_eq_one
    {A' D : Type*} [CommRing A'] [CommRing D] [Algebra A' D] [Algebra.IsIntegral A' D]
    (p' : Ideal A') [p'.IsPrime] {L : Type*} [Fintype L] {b : L → D}
    (hb : CompleteOrthogonalIdempotents b)
    (huniq : ∀ q₁ q₂ : Ideal D, q₁.IsPrime → q₂.IsPrime → q₁.LiesOver p' → q₂.LiesOver p' →
      q₁ = q₂)
    (s : Ideal D) [s.IsPrime] [s.LiesOver p'] {l₀ : L} (hl₀ : b l₀ ∉ s) :
    ∃ a ∉ p', ∀ a' : A', a ∣ a' →
      algebraMap D (Localization.Away (algebraMap A' D a')) (b l₀) = 1 := by
  classical
  obtain ⟨a, hap, ha⟩ := exists_notMem_forall_dvd_forall_mul_algebraMap_eq_zero p'
    (ι := {l : L // l ≠ l₀}) (fun l => b l.1) (fun l => hb.idem l.1)
    (fun l q hq hqo => forall_ne_mem_of_forall_eq p' hb.1 huniq s hl₀ l.1 l.2 q hq hqo)
  refine ⟨a, hap, fun a' hdvd => ?_⟩
  have hzero : ∀ l : L, l ≠ l₀ →
      algebraMap D (Localization.Away (algebraMap A' D a')) (b l) = 0 := fun l hl =>
    algebraMap_eq_zero_of_mul_eq_zero _ (ha a' hdvd ⟨l, hl⟩)
  have hsum : ∑ l : L, algebraMap D (Localization.Away (algebraMap A' D a')) (b l) = 1 := by
    rw [← map_sum, hb.complete, map_one]
  rw [← hsum, Finset.sum_eq_single l₀ (fun l _ hl => hzero l hl) (by simp)]

/-- **Isolating one factor of a decomposition at a single prime, at the element produced.** This is
`exists_notMem_forall_dvd_algebraMap_eq_one` with the conclusion read at the element produced
rather than at all of its multiples. -/
theorem exists_notMem_algebraMap_eq_one
    {A' D : Type*} [CommRing A'] [CommRing D] [Algebra A' D] [Algebra.IsIntegral A' D]
    (p' : Ideal A') [p'.IsPrime] {L : Type*} [Fintype L] {b : L → D}
    (hb : CompleteOrthogonalIdempotents b)
    (huniq : ∀ q₁ q₂ : Ideal D, q₁.IsPrime → q₂.IsPrime → q₁.LiesOver p' → q₂.LiesOver p' →
      q₁ = q₂)
    (s : Ideal D) [s.IsPrime] [s.LiesOver p'] {l₀ : L} (hl₀ : b l₀ ∉ s) :
    ∃ a ∉ p', algebraMap D (Localization.Away (algebraMap A' D a)) (b l₀) = 1 :=
  let ⟨a, hap, ha⟩ := exists_notMem_forall_dvd_algebraMap_eq_one p' hb huniq s hl₀
  ⟨a, hap, ha a dvd_rfl⟩

end Shrinking

section BaseChange

open TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **The pair the local structure theorem is applied to is of finite type.** If `B` is
module-finite over `A` and `C` is étale over `B`, then `B × C` is of finite type over `A`.

This is the hypothesis `Algebra.FiniteType A (B × C)` of
`exists_etale_completeOrthogonalIdempotents_prod` in the situation of the finite case of
property (B), [Stacks, Tag 04DQ]: `B` is the ring of the fibre product `X ×ₗᵧ V₀`, which is finite
over the ring `A` of `V₀`, and `C` is the ring of a single affine étale surjection onto it. -/
theorem finiteType_prod_of_etale {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    [Module.Finite A B] [Algebra.Etale B C] :
    Algebra.FiniteType A (B × C) := by
  have : Algebra.FiniteType A C := .trans (S := B) inferInstance inferInstance
  infer_instance

/-- **Cancelling the middle ring of a base change.** For an `A`-algebra `A'`, the ring
`(A' ⊗[A] B) ⊗[B] C` — the base change of `C` along `B → A' ⊗[A] B` — is `A' ⊗[A] C`, as
`A'`-algebras. -/
noncomputable def tensorCancelMid (A B C A' : Type*) [CommRing A] [CommRing B] [CommRing C]
    [CommRing A'] [Algebra A B] [Algebra A C] [Algebra A A'] [Algebra B C]
    [IsScalarTower A B C] :
    ((A' ⊗[A] B) ⊗[B] C) ≃ₐ[A'] A' ⊗[A] C :=
  AlgEquiv.ofRingEquiv (f :=
    ((((Algebra.TensorProduct.comm B (A' ⊗[A] B) C).trans
        (Algebra.TensorProduct.congr AlgEquiv.refl
          (Algebra.TensorProduct.commRight A B A').symm)).trans
      (Algebra.TensorProduct.cancelBaseChange A B B C A')).toRingEquiv).trans
      (Algebra.TensorProduct.commRight A A' C).symm.toRingEquiv)
    (fun x => by simp)

/-- `tensorCancelMid` sends `(a' ⊗ₜ b) ⊗ₜ c` to `a' ⊗ₜ (b • c)`. -/
@[simp]
theorem tensorCancelMid_tmul (A B C A' : Type*) [CommRing A] [CommRing B] [CommRing C]
    [CommRing A'] [Algebra A B] [Algebra A C] [Algebra A A'] [Algebra B C]
    [IsScalarTower A B C] (a' : A') (b : B) (c : C) :
    tensorCancelMid A B C A' ((a' ⊗ₜ b) ⊗ₜ c) = a' ⊗ₜ (b • c) := by
  simp [tensorCancelMid]

/-- The inverse of `tensorCancelMid` sends `a' ⊗ₜ c` to `(a' ⊗ₜ 1) ⊗ₜ c`. -/
@[simp]
theorem tensorCancelMid_symm_tmul (A B C A' : Type*) [CommRing A] [CommRing B] [CommRing C]
    [CommRing A'] [Algebra A B] [Algebra A C] [Algebra A A'] [Algebra B C]
    [IsScalarTower A B C] (a' : A') (c : C) :
    (tensorCancelMid A B C A').symm (a' ⊗ₜ c) = (a' ⊗ₜ (1 : B)) ⊗ₜ c := by
  simp [tensorCancelMid]

/-- **An étale covering surjective on spectra stays surjective after base change of the base.**
If `Spec C → Spec B` is surjective and `C` is étale over `B`, then `Spec ((A' ⊗[A] B) ⊗[B] C) →
Spec (A' ⊗[A] B)` is surjective for every `A`-algebra `A'`.

The mechanism is faithful flatness: a flat algebra surjective on spectra is faithfully flat,
faithful flatness is stable under base change, and a faithfully flat algebra is surjective on
spectra. This is what guarantees that every prime of `A' ⊗[A] B` over the chosen prime of `A'` is
hit by a prime of the covering, which is where the pieces of the decomposition come from in the
finite case of property (B), [Stacks, Tag 04DQ]. -/
theorem surjective_comap_tensorBaseChange {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra.Etale B C] (A' : Type u) [CommRing A'] [Algebra A A']
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap B C))) :
    Function.Surjective
      (PrimeSpectrum.comap (algebraMap (A' ⊗[A] B) ((A' ⊗[A] B) ⊗[B] C))) := by
  have : Module.FaithfullyFlat B C := Module.FaithfullyFlat.of_comap_surjective hsurj
  exact PrimeSpectrum.comap_surjective_of_faithfullyFlat

/-- **[Stacks, Tag 00UL] for the pair `(B, C)` of the finite case, both sides on one ring.** This
is `exists_etale_completeOrthogonalIdempotents_prod` with the `C`-side decomposition carried on
`(A' ⊗[A] B) ⊗[B] C` instead of `A' ⊗[A] C`, the two being identified by `tensorCancelMid`.

Stating the `C`-side on `(A' ⊗[A] B) ⊗[B] C` is what makes the two halves comparable: that ring is
visibly étale over `A' ⊗[A] B`, and by `surjective_comap_tensorBaseChange` its spectrum surjects
onto `Spec (A' ⊗[A] B)`. So every prime of `A' ⊗[A] B` over `p'` carried by one of the `b`-factors
is hit by a prime carried by one of the `c`-factors, and the residue field information attached to
the two factors can be compared. This is the single application of the étale local structure
theorem on which the finite case of property (B), [Stacks, Tag 04DQ], rests. -/
theorem exists_etale_completeOrthogonalIdempotents_tensorBaseChange
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    [Module.Finite A B] [Algebra.Etale B C] (p : Ideal A) [p.IsPrime] :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Algebra.Etale A A')
      (p' : Ideal A') (_ : p'.IsPrime) (_ : p'.LiesOver p) (n : ℕ)
      (b : Fin (n + 1) → A' ⊗[A] B) (c : Fin (n + 1) → (A' ⊗[A] B) ⊗[B] C)
      (_ : CompleteOrthogonalIdempotents b) (_ : CompleteOrthogonalIdempotents c),
      ((∀ i : Fin n, Module.Finite A' (Localization.Away (b i.castSucc))) ∧
        (∀ (i : Fin n) (q₁ q₂ : Ideal (A' ⊗[A] B)), ∀ _ : q₁.IsPrime, ∀ _ : q₂.IsPrime,
          q₁.LiesOver p' → q₂.LiesOver p' → b i.castSucc ∉ q₁ → b i.castSucc ∉ q₂ → q₁ = q₂) ∧
        (∀ (i : Fin n) (q : Ideal (A' ⊗[A] B)), ∀ _ : q.IsPrime, ∀ _ : q.LiesOver p',
          b i.castSucc ∉ q →
          letI := Localization.AtPrime.algebraOfLiesOver p' q
          IsPurelyInseparable p'.ResidueField q.ResidueField) ∧
        (∀ q : Ideal (A' ⊗[A] B), ∀ _ : q.IsPrime, q.LiesOver p' → b (Fin.last n) ∉ q →
          ¬ Algebra.QuasiFiniteAt A' q)) ∧
      ((∀ i : Fin n, Module.Finite A' (Localization.Away (c i.castSucc))) ∧
        (∀ (i : Fin n) (q₁ q₂ : Ideal ((A' ⊗[A] B) ⊗[B] C)), ∀ _ : q₁.IsPrime, ∀ _ : q₂.IsPrime,
          q₁.LiesOver p' → q₂.LiesOver p' → c i.castSucc ∉ q₁ → c i.castSucc ∉ q₂ → q₁ = q₂) ∧
        (∀ (i : Fin n) (q : Ideal ((A' ⊗[A] B) ⊗[B] C)), ∀ _ : q.IsPrime, ∀ _ : q.LiesOver p',
          c i.castSucc ∉ q →
          letI := Localization.AtPrime.algebraOfLiesOver p' q
          IsPurelyInseparable p'.ResidueField q.ResidueField) ∧
        (∀ q : Ideal ((A' ⊗[A] B) ⊗[B] C), ∀ _ : q.IsPrime, q.LiesOver p' →
          c (Fin.last n) ∉ q → ¬ Algebra.QuasiFiniteAt A' q)) := by
  have : Algebra.FiniteType A (B × C) := finiteType_prod_of_etale
  obtain ⟨A', _, _, _, p', _, _, n, e, hco, r, hrp, hro, hfin, hnot, huniq, hres, hlast⟩ :=
    Algebra.exists_etale_completeOrthogonalIdempotents_finite_isPurelyInseparable
      (R := A) (S := B × C) p
  let ι : A' ⊗[A] (B × C) ≃ₐ[A'] (A' ⊗[A] B) × (A' ⊗[A] C) :=
    Algebra.TensorProduct.prodRight A A' A' B C
  let ε : (A' ⊗[A] C) ≃ₐ[A'] ((A' ⊗[A] B) ⊗[B] C) := (tensorCancelMid A B C A').symm
  let πB : A' ⊗[A] (B × C) →ₐ[A'] A' ⊗[A] B := (AlgHom.fst A' _ _).comp ι.toAlgHom
  let πC : A' ⊗[A] (B × C) →ₐ[A'] ((A' ⊗[A] B) ⊗[B] C) :=
    ε.toAlgHom.comp ((AlgHom.snd A' _ _).comp ι.toAlgHom)
  have hBsurj : Function.Surjective πB := Prod.fst_surjective.comp ι.surjective
  have hCsurj : Function.Surjective πC :=
    ε.surjective.comp (Prod.snd_surjective.comp ι.surjective)
  refine ⟨A', ‹_›, ‹_›, ‹_›, p', ‹_›, ‹_›, n, fun i => πB (e i), fun i => πC (e i),
    hco.map πB.toRingHom, hco.map πC.toRingHom, ?_, ?_⟩
  · refine localStructure_image_of_surjective p' e hco.idem r hrp hro hfin huniq
      (fun i => (hres i).2) hlast πB hBsurj ?_
    intro q hq hqfa
    exact quasiFiniteAt_comap_fst_comp ι q
  · refine localStructure_image_of_surjective p' e hco.idem r hrp hro hfin huniq
      (fun i => (hres i).2) hlast πC hCsurj ?_
    intro q hq hqfa
    have : (q.comap ε.toRingHom).IsPrime := hq.comap _
    have : Algebra.QuasiFiniteAt A' (q.comap ε.toRingHom) :=
      Algebra.QuasiFiniteAt.comap_algEquiv _ ε
    exact quasiFiniteAt_comap_snd_comp ι (q.comap ε.toRingHom)


end BaseChange

section Decomposition

/-- **A complete orthogonal family of idempotents decomposes an algebra.** The quotients
`R ⧸ (1 - e l)` cut out by a finite complete orthogonal family of idempotents of an `A`-algebra `R`
have `R` as their product, as `A`-algebras.

Each factor is the localization of `R` away from `e l`, by
`IsLocalization.Away.quotient_of_isIdempotentElem`, so this is the ring-theoretic form of the
decomposition of `Spec R` into the clopen pieces `Spec R[1/e l]` that the finite case of property
(B), [Stacks, Tag 04DQ], produces. -/
noncomputable def completeOrthogonalIdempotentsAlgEquivPi {A R : Type*} [CommRing A] [CommRing R]
    [Algebra A R] {L : Type*} [Fintype L] {e : L → R} (he : CompleteOrthogonalIdempotents e) :
    R ≃ₐ[A] (∀ l, R ⧸ Ideal.span {1 - e l}) :=
  AlgEquiv.ofBijective (AlgHom.pi fun l => Ideal.Quotient.mkₐ A (Ideal.span {1 - e l}))
    he.bijective_pi

/-- The decomposition of `completeOrthogonalIdempotentsAlgEquivPi` is given on each factor by the
quotient map. -/
@[simp]
theorem completeOrthogonalIdempotentsAlgEquivPi_apply {A R : Type*} [CommRing A] [CommRing R]
    [Algebra A R] {L : Type*} [Fintype L] {e : L → R} (he : CompleteOrthogonalIdempotents e)
    (x : R) (l : L) :
    completeOrthogonalIdempotentsAlgEquivPi (A := A) he x l = Ideal.Quotient.mk _ x := rfl

end Decomposition

section LocalizationBaseChange

open TensorProduct

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (a : R)

/-- Localizing `S` away from the image of `a : R` is localizing it at the image of the powers of
`a`, because taking powers commutes with taking images. -/
instance isLocalization_away_algebraMap :
    IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers a))
      (Localization.Away (algebraMap R S a)) := by
  rw [Algebra.algebraMapSubmonoid_powers]; infer_instance

/-- `S` localized away from the image of `a : R` is an algebra over `R` localized away from `a`. -/
noncomputable instance awayAlgebra :
    Algebra (Localization.Away a) (Localization.Away (algebraMap R S a)) :=
  localizationAlgebra (Submonoid.powers a) S

/-- The three rings `R`, `R[1/a]` and `S[1/a]` form a scalar tower. -/
instance isScalarTower_away :
    IsScalarTower R (Localization.Away a) (Localization.Away (algebraMap R S a)) :=
  isScalarTower_localizationAlgebra (Submonoid.powers a) S

/-- **The two descriptions of `S[1/a]` for `a` in the base agree.** `Localization.Away` of the
image of `a` and the localization of `S` at the image of the powers of `a` are the same
localization of `S`, as algebras over `R[1/a]`. -/
noncomputable def awayAlgEquiv :
    Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers a)) ≃ₐ[Localization.Away a]
      Localization.Away (algebraMap R S a) :=
  AlgEquiv.ofRingEquiv (f := (IsLocalization.algEquiv
      (Algebra.algebraMapSubmonoid S (Submonoid.powers a))
      (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers a)))
      (Localization.Away (algebraMap R S a))).toRingEquiv) <| fun x => by
    refine RingHom.congr_fun (IsLocalization.ringHom_ext (Submonoid.powers a)
      (j := (IsLocalization.algEquiv (Algebra.algebraMapSubmonoid S (Submonoid.powers a))
          (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers a)))
          (Localization.Away (algebraMap R S a))).toRingEquiv.toRingHom.comp
        (algebraMap (Localization.Away a)
          (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers a)))))
      (k := algebraMap (Localization.Away a) (Localization.Away (algebraMap R S a)))
      (RingHom.ext fun y => ?_)) x
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      AlgEquiv.coe_ringEquiv, RingHom.coe_coe]
    rw [← IsScalarTower.algebraMap_apply R (Localization.Away a)
        (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers a))),
      ← IsScalarTower.algebraMap_apply R (Localization.Away a)
        (Localization.Away (algebraMap R S a)),
      IsScalarTower.algebraMap_apply R S
        (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers a))),
      AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply R S (Localization.Away (algebraMap R S a))]

/-- `awayAlgEquiv` is the identity on the image of `S`. -/
@[simp]
theorem awayAlgEquiv_algebraMap (s : S) :
    awayAlgEquiv R S a (algebraMap S _ s) = algebraMap S (Localization.Away (algebraMap R S a)) s :=
  (IsLocalization.algEquiv (Algebra.algebraMapSubmonoid S (Submonoid.powers a)) _ _).commutes s

/-- **Inverting an element of the base commutes with base change.** For an `A`-algebra `A'`, an
`A`-algebra `B` and `a : A'`, the ring `A'[1/a] ⊗[A] B` is `(A' ⊗[A] B)[1/a]`, as
`A'[1/a]`-algebras. -/
noncomputable def tensorLocalizationAwayEquiv (A A' B : Type*) [CommRing A] [CommRing A']
    [CommRing B] [Algebra A A'] [Algebra A B] (a : A') :
    (Localization.Away a ⊗[A] B) ≃ₐ[Localization.Away a]
      Localization.Away (algebraMap A' (A' ⊗[A] B) a) :=
  (Algebra.TensorProduct.cancelBaseChange A A' (Localization.Away a)
      (Localization.Away a) B).symm.trans
    ((Localization.tensorRightAlgEquiv (Submonoid.powers a) (A' ⊗[A] B)).trans
      (awayAlgEquiv A' (A' ⊗[A] B) a))

/-- `tensorLocalizationAwayEquiv` carries `1 ⊗ x` to the image of `1 ⊗ x`. -/
@[simp]
theorem tensorLocalizationAwayEquiv_one_tmul (A A' B : Type*) [CommRing A] [CommRing A']
    [CommRing B] [Algebra A A'] [Algebra A B] (a : A') (x : B) :
    tensorLocalizationAwayEquiv A A' B a ((1 : Localization.Away a) ⊗ₜ[A] x) =
      algebraMap (A' ⊗[A] B) (Localization.Away (algebraMap A' (A' ⊗[A] B) a))
        (Algebra.TensorProduct.includeRight x) := by
  simp only [tensorLocalizationAwayEquiv, AlgEquiv.trans_apply,
    Algebra.TensorProduct.cancelBaseChange_symm_tmul,
    Localization.tensorRightAlgEquiv_apply_one_tmul, awayAlgEquiv_algebraMap,
    Algebra.TensorProduct.includeRight_apply]

/-- The inverse of `tensorLocalizationAwayEquiv` carries the image of `1 ⊗ x` to `1 ⊗ x`. -/
@[simp]
theorem tensorLocalizationAwayEquiv_symm_algebraMap (A A' B : Type*) [CommRing A] [CommRing A']
    [CommRing B] [Algebra A A'] [Algebra A B] (a : A') (x : B) :
    (tensorLocalizationAwayEquiv A A' B a).symm
        (algebraMap (A' ⊗[A] B) (Localization.Away (algebraMap A' (A' ⊗[A] B) a))
          (Algebra.TensorProduct.includeRight x)) =
      (1 : Localization.Away a) ⊗ₜ[A] x :=
  (AlgEquiv.symm_apply_eq _).2 (tensorLocalizationAwayEquiv_one_tmul A A' B a x).symm

/-- The value of `tensorLocalizationAwayEquiv` on a general generator. -/
theorem tensorLocalizationAwayEquiv_tmul (A A' B : Type*) [CommRing A] [CommRing A']
    [CommRing B] [Algebra A A'] [Algebra A B] (a : A') (t : Localization.Away a) (x : B) :
    tensorLocalizationAwayEquiv A A' B a (t ⊗ₜ[A] x) =
      algebraMap (Localization.Away a) (Localization.Away (algebraMap A' (A' ⊗[A] B) a)) t *
        algebraMap (A' ⊗[A] B) (Localization.Away (algebraMap A' (A' ⊗[A] B) a))
          (Algebra.TensorProduct.includeRight x) := by
  have h : t ⊗ₜ[A] x = algebraMap (Localization.Away a) (Localization.Away a ⊗[A] B) t *
      ((1 : Localization.Away a) ⊗ₜ[A] x) := by
    simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
  rw [h, map_mul, AlgEquiv.commutes, tensorLocalizationAwayEquiv_one_tmul]

end LocalizationBaseChange


end Stacks.EtaleCohomology

end
