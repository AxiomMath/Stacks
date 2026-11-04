module

public import Mathlib.Algebra.Category.Ring.Under.Property
public import Mathlib.RingTheory.Etale.Descent
public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.Finite
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleColimits

/-!
# The equalizer of two maps of finite étale algebras

Let `R` be a commutative ring and let `B` and `C` be finite étale `R`-algebras. For two
`R`-algebra maps `α, β : B ⟶ C` the equalizer `A = {b ∈ B | α b = β b}` is again a finite étale
`R`-algebra: this is the content of the right-exactness half of Stacks Tag 0BN9 over an affine
base, since writing two finite étale covers of `Spec R` as `Spec B` and `Spec C` the coequalizer
of the two induced morphisms is `Spec A`. Consequently the category of finite étale `R`-algebras
has finite limits, so the category of finite étale covers of `Spec R` has finite colimits.

The proof is the one of the source: the statement is local on `Spec R`, so one may assume that
`B` and `C` have constant rank, and then there is a faithfully flat finite étale `R`-algebra `T`
over which both become split, that is, isomorphic to a finite product of copies of `T`
(`Algebra.IsFiniteSplit.exists_tensorProduct_of_etale`). Formation of the equalizer commutes with
flat base change and both finiteness and étaleness descend along a faithfully flat base change,
so everything reduces to the split case.

The split case is proved by one further localization. A `T`-algebra map `(ι → T) ⟶ (κ → T)` is
given by a complete orthogonal family of idempotents `e j i` of `T` for each `j : κ`, through
`α x j = ∑ i, e j i * x i`, and the difference of two such maps is
`α x j - β x j = ∑ (i₀, i₁), e j i₀ * f j i₁ * (x i₀ - x i₁)`. The products
`∏ j, e j (s j).1 * f j (s j).2`, indexed by the choices `s : κ → ι × ι` of one pair of indices
for each `j`, form a complete orthogonal family of idempotents of `T`, hence span `T`; over the
localization of `T` away from one of them both maps are induced by maps of index types, where the
equalizer is the algebra of functions on the coequalizer of those maps of index types, which is
finite étale. The localization of the equalizer at such an idempotent is the equalizer of the
localized maps because an element of the localized equalizer lifts to `ι → T` and multiplying the
lift by the idempotent lands it in the equalizer.

## Main definitions

* `RingHom.FiniteEtale` — being finite and étale, as a property of ring homomorphisms.
* `Stacks.FundamentalGroup.piIdem`, `Stacks.FundamentalGroup.piPairIdem` and
  `Stacks.FundamentalGroup.piRefineIdem` — the idempotents of a map of split algebras, their
  pairwise products, and the complete orthogonal family these generate.
* `Stacks.FundamentalGroup.pieceEqualizer` — the equalizer over the localization at one member of
  that family, where both maps are induced by maps of index types.

## Main results

* `Stacks.FundamentalGroup.etale_equalizer_pi` and
  `Stacks.FundamentalGroup.moduleFinite_equalizer_pi` — the equalizer of two `T`-algebra maps
  between finite products of copies of `T` is finite étale over `T`.
* `Stacks.FundamentalGroup.etale_and_moduleFinite_equalizer_of_isFiniteSplit`,
  `…_of_faithfullyFlat`, `…_of_rankAtStalk` — the same for split algebras, for algebras split
  after a faithfully flat base change, and for finite étale algebras of constant rank.
* `Stacks.FundamentalGroup.etale_and_moduleFinite_equalizer` — **the equalizer of two maps of
  finite étale algebras is finite étale**, with no further hypotheses.
* `RingHom.FiniteEtale.hasEqualizers`, `RingHom.FiniteEtale.hasFiniteProducts` — the two
  stability properties of the class of finite étale algebras that Mathlib's
  `CommRingCat.Under.hasFiniteLimits` consumes.
* `Stacks.FundamentalGroup.hasFiniteLimits_finiteEtaleUnder` and
  `Stacks.FundamentalGroup.hasFiniteColimits_finiteEtaleUnder_op` — the category of finite étale
  `R`-algebras has finite limits, and its opposite has finite colimits.

## Implementation notes

The localization at one member of the generating family of idempotents is taken as an abstract
`IsLocalization.Away`, and the algebra structure of the piece over the equalizer is an abstract
instance characterized by the hypothesis `halg` that it is the reduction map. Both choices are
forced by the application: in `RingHom.OfLocalizationSpan` the element of the spanning set is a
subtype element, so the idempotent cannot be assumed syntactically equal to a product of pair
idempotents, and the algebra structure of the piece over the equalizer only exists once the
reduction map is known to land in the piece, which is where the idempotent is used.

The finite-colimit statement for the category `AlgebraicGeometry.FiniteEtaleOver X` of finite
étale covers of a scheme `X` needs, on top of the results here, the equalizer of a pair of
quasi-coherent algebras on `X` and its relative spectrum; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/FundamentalGroup/FiniteEtaleColimits.lean`.

## References

* [Stacks Project, Tag 0BN9](https://stacks.math.columbia.edu/tag/0BN9)
-/

@[expose] public section

universe u

namespace Stacks.FundamentalGroup

/-- Being finite and étale, as a property of ring homomorphisms: the property that cuts the
category of finite étale algebras out of the category of algebras. -/
def _root_.RingHom.FiniteEtale {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  RingHom.Finite f ∧ RingHom.Etale f

section Split

variable {T : Type u} [CommRing T] {ι κ : Type u} [DecidableEq ι]

/-- The idempotents of a `T`-algebra map `(ι → T) ⟶ (κ → T)`: the `j`-th component of the
image of the `i`-th standard idempotent. -/
def piIdem (α : (ι → T) →ₐ[T] (κ → T)) (j : κ) (i : ι) : T := α (Pi.single i 1) j

/-- The pair idempotents of two `T`-algebra maps `(ι → T) ⟶ (κ → T)`. -/
def piPairIdem (α β : (ι → T) →ₐ[T] (κ → T)) (j : κ) (p : ι × ι) : T :=
  piIdem α j p.1 * piIdem β j p.2

section Sums

variable [Fintype ι]

/-- For each `j : κ`, the idempotents `piIdem α j i`, `i : ι`, form a complete orthogonal
family. -/
lemma completeOrthogonalIdempotents_piIdem (α : (ι → T) →ₐ[T] (κ → T)) (j : κ) :
    CompleteOrthogonalIdempotents (piIdem α j) :=
  (CompleteOrthogonalIdempotents.single (I := ι) (R := fun _ : ι ↦ T)).map
    ((Pi.evalRingHom (fun _ : κ ↦ T) j).comp α.toRingHom)

/-- A `T`-algebra map `α : (ι → T) ⟶ (κ → T)` is given by `α x j = ∑ i, piIdem α j i * x i`. -/
lemma apply_eq_sum_piIdem (α : (ι → T) →ₐ[T] (κ → T)) (x : ι → T) (j : κ) :
    α x j = ∑ i, piIdem α j i * x i := by
  conv_lhs => rw [show x = ∑ i, x i • Pi.single i (1 : T) by
    ext i'; simp [Finset.sum_apply, Pi.single_apply]]
  rw [map_sum]
  simp [piIdem, mul_comm]

variable (α β : (ι → T) →ₐ[T] (κ → T))

/-- For each `j : κ`, the pair idempotents `piPairIdem α β j p`, `p : ι × ι`, form a complete
orthogonal family. -/
lemma completeOrthogonalIdempotents_piPairIdem (j : κ) :
    CompleteOrthogonalIdempotents (piPairIdem α β j) := by
  have he := completeOrthogonalIdempotents_piIdem α j
  have hf := completeOrthogonalIdempotents_piIdem β j
  rw [CompleteOrthogonalIdempotents.iff_ortho_complete]
  refine ⟨fun p q hpq ↦ ?_, ?_⟩
  · simp only [piPairIdem]
    rw [show piIdem α j p.1 * piIdem β j p.2 * (piIdem α j q.1 * piIdem β j q.2)
        = piIdem α j p.1 * piIdem α j q.1 * (piIdem β j p.2 * piIdem β j q.2) by ring]
    rcases not_and_or.mp (Prod.ext_iff.not.mp hpq) with h | h
    · rw [he.ortho h, zero_mul]
    · rw [hf.ortho h, mul_zero]
  · simp only [piPairIdem, Fintype.sum_prod_type]
    rw [show (∑ i : ι, ∑ i' : ι, piIdem α j i * piIdem β j i')
        = (∑ i : ι, piIdem α j i) * ∑ i' : ι, piIdem β j i' by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ ↦ (Finset.mul_sum ..).symm]
    rw [he.complete, hf.complete, one_mul]

/-- The difference of two `T`-algebra maps `(ι → T) ⟶ (κ → T)` is the idempotent-weighted sum of
the differences of pairs of coordinates. -/
lemma sub_apply_eq_sum_piPairIdem (x : ι → T) (j : κ) :
    α x j - β x j = ∑ p : ι × ι, piPairIdem α β j p * (x p.1 - x p.2) := by
  have h₁ : ∀ i : ι, ∑ i' : ι, piIdem α j i * piIdem β j i' * x i = piIdem α j i * x i :=
    fun i ↦ by rw [← Finset.sum_mul, ← Finset.mul_sum,
      (completeOrthogonalIdempotents_piIdem β j).complete, mul_one]
  have h₂ : ∀ i' : ι, ∑ i : ι, piIdem α j i * piIdem β j i' * x i' = piIdem β j i' * x i' :=
    fun i' ↦ by rw [← Finset.sum_mul, ← Finset.sum_mul,
      (completeOrthogonalIdempotents_piIdem α j).complete, one_mul]
  rw [apply_eq_sum_piIdem α x j, apply_eq_sum_piIdem β x j]
  simp only [piPairIdem, Fintype.sum_prod_type, mul_sub, Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl fun i _ ↦ h₁ i, Finset.sum_comm,
    Finset.sum_congr rfl fun i' _ ↦ h₂ i']

end Sums

section Refine

variable [Fintype κ]

/-- The complete orthogonal family of idempotents of `T` generated by all the pair idempotents of
two `T`-algebra maps `(ι → T) ⟶ (κ → T)`, indexed by the choices of one pair for each `j : κ`.
Over the localization of `T` at one of these idempotents every pair idempotent is `0` or `1`, so
both maps become induced by maps of index types. -/
def piRefineIdem (α β : (ι → T) →ₐ[T] (κ → T)) (s : κ → ι × ι) : T :=
  ∏ j, piPairIdem α β j (s j)

variable [Finite ι] (α β : (ι → T) →ₐ[T] (κ → T))

omit [Finite ι] in
/-- The idempotents `piRefineIdem α β s`, `s : κ → ι × ι`, form a complete orthogonal family. -/
lemma completeOrthogonalIdempotents_piRefineIdem [Fintype ι] [DecidableEq κ] :
    CompleteOrthogonalIdempotents (piRefineIdem α β) := by
  rw [CompleteOrthogonalIdempotents.iff_ortho_complete]
  refine ⟨fun s s' hss ↦ ?_, ?_⟩
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp hss
    simp only [piRefineIdem, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_zero (Finset.mem_univ j)
      ((completeOrthogonalIdempotents_piPairIdem α β j).ortho hj)
  · have h1 : ∏ j : κ, (∑ p : ι × ι, piPairIdem α β j p) = 1 :=
      Finset.prod_eq_one fun j _ ↦ (completeOrthogonalIdempotents_piPairIdem α β j).complete
    rw [← h1, Finset.prod_univ_sum, Fintype.piFinset_univ]
    rfl

/-- The refined idempotent of `s` is fixed by multiplication with the pair idempotent at `s j`. -/
lemma piRefineIdem_mul_piPairIdem_self (s : κ → ι × ι) (j : κ) :
    piRefineIdem α β s * piPairIdem α β j (s j) = piRefineIdem α β s := by
  classical
  cases nonempty_fintype ι
  rw [piRefineIdem, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j), mul_right_comm,
    ((completeOrthogonalIdempotents_piPairIdem α β j).idem (s j)).eq]

/-- The refined idempotent of `s` annihilates the pair idempotent at `j` of any pair `p ≠ s j`. -/
lemma piRefineIdem_mul_piPairIdem_of_ne (s : κ → ι × ι) (j : κ) {p : ι × ι} (hp : p ≠ s j) :
    piRefineIdem α β s * piPairIdem α β j p = 0 := by
  classical
  cases nonempty_fintype ι
  rw [piRefineIdem, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j), mul_right_comm,
    (completeOrthogonalIdempotents_piPairIdem α β j).ortho hp.symm, zero_mul]

/-- Each refined idempotent `piRefineIdem α β s` is idempotent. -/
lemma isIdempotentElem_piRefineIdem (s : κ → ι × ι) :
    IsIdempotentElem (piRefineIdem α β s) := by
  classical
  cases nonempty_fintype ι
  exact (completeOrthogonalIdempotents_piRefineIdem α β).idem s

/-- A coordinate difference of an element of the equalizer of `α` and `β` is annihilated by the
refined idempotent of a piece, at the pair that the piece selects. -/
lemma piRefineIdem_mul_sub_eq_zero (s : κ → ι × ι) (a : AlgHom.equalizer α β) (j : κ) :
    piRefineIdem α β s * ((a : ι → T) (s j).1 - (a : ι → T) (s j).2) = 0 := by
  classical
  cases nonempty_fintype ι
  have h0 : α (a : ι → T) j - β (a : ι → T) j = 0 := by
    rw [(AlgHom.mem_equalizer α β _).mp a.2]; ring
  have h2 : piRefineIdem α β s *
      ∑ p : ι × ι, piPairIdem α β j p * ((a : ι → T) p.1 - (a : ι → T) p.2) = 0 := by
    rw [← sub_apply_eq_sum_piPairIdem α β _ j, h0, mul_zero]
  rwa [Finset.mul_sum, Finset.sum_eq_single_of_mem (s j) (Finset.mem_univ _) (fun p _ hp ↦ by
    rw [← mul_assoc, piRefineIdem_mul_piPairIdem_of_ne α β s j hp, zero_mul]),
    ← mul_assoc, piRefineIdem_mul_piPairIdem_self] at h2

end Refine

end Split

section Idempotent

variable {T : Type u} [CommRing T] {e : T} (he : IsIdempotentElem e)
  (T' : Type u) [CommRing T'] [Algebra T T'] [IsLocalization.Away e T']

include he in
/-- An idempotent becomes `1` in the localization away from it. -/
lemma algebraMap_eq_one_of_isIdempotentElem : algebraMap T T' e = 1 := by
  have hu := IsLocalization.map_units (M := Submonoid.powers e) T' ⟨e, Submonoid.mem_powers e⟩
  refine hu.mul_left_cancel ?_
  show algebraMap T T' e * algebraMap T T' e = algebraMap T T' e * 1
  rw [← map_mul, he.eq, mul_one]

include he in
/-- The localization of a ring away from an idempotent is a quotient of it. -/
lemma surjective_algebraMap_of_isIdempotentElem : Function.Surjective (algebraMap T T') := by
  intro z
  obtain ⟨⟨x, m⟩, h⟩ := IsLocalization.surj (Submonoid.powers e) z
  obtain ⟨n, hn⟩ := m.2
  refine ⟨x, ?_⟩
  rw [← h, show ((m : T)) = e ^ n from hn.symm, map_pow,
    algebraMap_eq_one_of_isIdempotentElem he T', one_pow, mul_one]

include he in
/-- An element vanishes in the localization away from an idempotent `e` if and only if `e`
annihilates it. -/
lemma algebraMap_eq_zero_iff_of_isIdempotentElem (x : T) :
    algebraMap T T' x = 0 ↔ e * x = 0 := by
  rw [IsLocalization.map_eq_zero_iff (Submonoid.powers e)]
  refine ⟨fun ⟨m, hm⟩ ↦ ?_, fun h ↦ ⟨⟨e, Submonoid.mem_powers e⟩, h⟩⟩
  obtain ⟨n, hn⟩ := m.2
  rw [show ((m : T)) = e ^ n from hn.symm] at hm
  rcases n with _ | n
  · rw [pow_zero, one_mul] at hm
    rw [hm, mul_zero]
  · rwa [he.pow_succ_eq n] at hm

end Idempotent

section Piece

variable {T : Type u} [CommRing T] {ι κ : Type u} [DecidableEq ι] [Fintype κ]

/-- The piece of the equalizer selected by `s`: the equalizer, over a localization `T'` of `T`
away from the refined idempotent of `s`, of the two morphisms of split algebras induced by the
index maps `j ↦ (s j).1` and `j ↦ (s j).2`. -/
abbrev pieceEqualizer (T' : Type u) [CommRing T'] (s : κ → ι × ι) : Subalgebra T' (ι → T') :=
  AlgHom.equalizer (piPrecompAlgHom T' fun j ↦ (s j).1) (piPrecompAlgHom T' fun j ↦ (s j).2)

/-- The reduction of the equalizer of `α` and `β` along `T ⟶ T'`, as a map to `ι → T'`. -/
def pieceMap (T' : Type u) [CommRing T'] [Algebra T T'] (α β : (ι → T) →ₐ[T] (κ → T)) :
    AlgHom.equalizer α β →ₐ[T] (ι → T') :=
  (AlgHom.pi fun i ↦ (Algebra.ofId T T').comp (Pi.evalAlgHom T (fun _ : ι ↦ T) i)).comp
    (AlgHom.equalizer α β).val

variable [Finite ι] (T' : Type u) [CommRing T'] [Algebra T T'] (α β : (ι → T) →ₐ[T] (κ → T))
  (s : κ → ι × ι) {e : T} (hes : e = piRefineIdem α β s) [IsLocalization.Away e T']

omit [DecidableEq ι] [Finite ι] [Fintype κ] in
/-- The `i`-th coordinate of `pieceMap T' α β a` is the image in `T'` of the `i`-th coordinate
of `a`. -/
@[simp]
lemma pieceMap_apply (a : AlgHom.equalizer α β) (i : ι) :
    pieceMap T' α β a i = algebraMap T T' ((a : ι → T) i) := rfl

include hes in
/-- The reduction of an element of the equalizer of `α` and `β` to the localization away from the
refined idempotent of `s` lies in the piece `pieceEqualizer T' s`. -/
lemma pieceMap_mem (a : AlgHom.equalizer α β) :
    pieceMap T' α β a ∈ pieceEqualizer T' s := by
  classical
  subst hes
  rw [mem_equalizer_piPrecompAlgHom]
  intro j
  have h2 : algebraMap T T' ((a : ι → T) (s j).1 - (a : ι → T) (s j).2) = 0 :=
    (algebraMap_eq_zero_iff_of_isIdempotentElem (isIdempotentElem_piRefineIdem α β s) T' _).mpr
      (piRefineIdem_mul_sub_eq_zero α β s a j)
  rwa [map_sub, sub_eq_zero] at h2

/-- The reduction of the equalizer of `α` and `β` to a piece, as a ring homomorphism onto the
piece. -/
def pieceMapCod : AlgHom.equalizer α β →+* pieceEqualizer T' s where
  toFun a := ⟨pieceMap T' α β a, pieceMap_mem T' α β s hes a⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul ..)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add ..)

/-- The `i`-th coordinate of `pieceMapCod T' α β s hes a` is the image in `T'` of the `i`-th
coordinate of `a`. -/
@[simp]
lemma pieceMapCod_coe_apply (a : AlgHom.equalizer α β) (i : ι) :
    ((pieceMapCod T' α β s hes a : ι → T') i) = algebraMap T T' ((a : ι → T) i) := rfl

variable [Algebra (AlgHom.equalizer α β) (pieceEqualizer T' s)]
  (halg : ∀ (a : AlgHom.equalizer α β) (i : ι),
    ((algebraMap (AlgHom.equalizer α β) (pieceEqualizer T' s) a : ι → T') i)
      = algebraMap T T' ((a : ι → T) i))

include hes halg in
/-- **The piece is a localization of the equalizer.** If the algebra structure of the piece
`pieceEqualizer T' s` over the equalizer of `α` and `β` is the reduction map, then the piece is
the localization of that equalizer away from the refined idempotent of `s`.

Surjectivity is the point: an element of the piece lifts coordinatewise to `ι → T`, and
multiplying the lift by the refined idempotent lands it in the equalizer, because the identity
`sub_apply_eq_sum_piPairIdem` expresses `α - β` through the pair idempotents, all of which the
refined idempotent annihilates except the one that `s` selects. -/
lemma isLocalizationAway_pieceEqualizer :
    IsLocalization.Away (algebraMap T (AlgHom.equalizer α β) e) (pieceEqualizer T' s) := by
  classical
  cases nonempty_fintype ι
  subst hes
  have hE := isIdempotentElem_piRefineIdem α β s
  have hone : algebraMap T T' (piRefineIdem α β s) = 1 :=
    algebraMap_eq_one_of_isIdempotentElem hE T'
  have hsurj : Function.Surjective (algebraMap T T') :=
    surjective_algebraMap_of_isIdempotentElem hE T'
  have hzero := algebraMap_eq_zero_iff_of_isIdempotentElem hE T'
  have hmapone : algebraMap (AlgHom.equalizer α β) (pieceEqualizer T' s)
      (algebraMap T (AlgHom.equalizer α β) (piRefineIdem α β s)) = 1 := by
    refine Subtype.ext (funext fun i ↦ ?_)
    rw [halg]
    simpa using hone
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · rintro ⟨y, n, rfl⟩
    rw [show ((⟨_, n, rfl⟩ : Submonoid.powers
        (algebraMap T (AlgHom.equalizer α β) (piRefineIdem α β s))) :
        AlgHom.equalizer α β) = _ ^ n from rfl, map_pow, hmapone, one_pow]
    exact isUnit_one
  · intro z
    choose w hw using fun i ↦ hsurj ((z : ι → T') i)
    have hmem : (fun i ↦ piRefineIdem α β s * w i) ∈ AlgHom.equalizer α β := by
      rw [AlgHom.mem_equalizer]
      refine funext fun j ↦ ?_
      have hz : piRefineIdem α β s * (w (s j).1 - w (s j).2) = 0 := by
        refine (hzero _).mp ?_
        rw [map_sub, hw, hw, sub_eq_zero]
        exact (mem_equalizer_piPrecompAlgHom T' _ _ _).mp z.2 j
      have hsum := sub_apply_eq_sum_piPairIdem α β (fun i ↦ piRefineIdem α β s * w i) j
      rw [Finset.sum_eq_single_of_mem (s j) (Finset.mem_univ _) (fun p _ hp ↦ by
        rw [show piPairIdem α β j p * (piRefineIdem α β s * w p.1 - piRefineIdem α β s * w p.2)
            = piRefineIdem α β s * piPairIdem α β j p * (w p.1 - w p.2) by ring,
          piRefineIdem_mul_piPairIdem_of_ne α β s j hp, zero_mul]),
        show piPairIdem α β j (s j) *
            (piRefineIdem α β s * w (s j).1 - piRefineIdem α β s * w (s j).2)
            = piRefineIdem α β s * piPairIdem α β j (s j) * (w (s j).1 - w (s j).2) by ring,
        piRefineIdem_mul_piPairIdem_self, hz] at hsum
      rw [← sub_eq_zero]
      exact hsum
    refine ⟨(⟨_, hmem⟩, 1), ?_⟩
    rw [OneMemClass.coe_one, map_one, mul_one]
    refine Subtype.ext (funext fun i ↦ ?_)
    rw [halg]
    show (z : ι → T') i = algebraMap T T' (piRefineIdem α β s * w i)
    rw [map_mul, hone, one_mul, hw]
  · intro x y hxy
    refine ⟨⟨algebraMap T (AlgHom.equalizer α β) (piRefineIdem α β s), Submonoid.mem_powers _⟩, ?_⟩
    refine Subtype.ext (funext fun i ↦ ?_)
    have h1 : algebraMap T T' ((x : ι → T) i) = algebraMap T T' ((y : ι → T) i) := by
      have h := congrArg (fun d : pieceEqualizer T' s ↦ (d : ι → T') i) hxy
      rwa [halg, halg] at h
    have h2 : piRefineIdem α β s * ((x : ι → T) i - (y : ι → T) i) = 0 :=
      (hzero _).mp (by rw [map_sub, h1, sub_self])
    show ((algebraMap T (AlgHom.equalizer α β) (piRefineIdem α β s) : ι → T) i)
        * (x : ι → T) i
      = ((algebraMap T (AlgHom.equalizer α β) (piRefineIdem α β s) : ι → T) i) * (y : ι → T) i
    have h3 : ((algebraMap T (AlgHom.equalizer α β) (piRefineIdem α β s) : ι → T) i)
        = piRefineIdem α β s := rfl
    rw [h3]
    linear_combination h2

include halg in
omit [DecidableEq ι] [Finite ι] [Fintype κ] in
/-- The localization map of the equalizer at a piece *is* the structure map of the piece over the
localized base. -/
lemma awayMap_eq_algebraMap_pieceEqualizer
    [IsLocalization.Away (algebraMap T (AlgHom.equalizer α β) e) (pieceEqualizer T' s)] :
    IsLocalization.Away.map T' (pieceEqualizer T' s) (algebraMap T (AlgHom.equalizer α β)) e
      = algebraMap T' (pieceEqualizer T' s) := by
  refine IsLocalization.ringHom_ext (Submonoid.powers e) ?_
  simp only [IsLocalization.Away.map, IsLocalization.map_comp]
  refine RingHom.ext fun t ↦ Subtype.ext (funext fun i ↦ ?_)
  rw [RingHom.comp_apply, RingHom.comp_apply, halg]
  rfl

end Piece

section Conclusion

variable {T : Type u} [CommRing T] {ι κ : Type u}

section Spanning

variable [DecidableEq ι] [Finite ι] [Fintype κ] (α β : (ι → T) →ₐ[T] (κ → T))

/-- The refined idempotents `piRefineIdem α β s` generate the unit ideal of `T`. -/
lemma span_range_piRefineIdem : Ideal.span (Set.range (piRefineIdem α β)) = ⊤ := by
  classical
  cases nonempty_fintype ι
  rw [Ideal.eq_top_iff_one, ← (completeOrthogonalIdempotents_piRefineIdem α β).complete]
  exact Ideal.sum_mem _ fun s _ ↦ Ideal.subset_span ⟨s, rfl⟩

end Spanning

/-- The data of the localization of the equalizer at the idempotent `r` of the family
`piRefineIdem α β`: the piece `s` it selects, with its algebra structure over the equalizer, is a
localization of the equalizer and the localization map is its structure map. -/
private lemma exists_piece_localization [DecidableEq ι] [Fintype κ] [Finite ι]
    (α β : (ι → T) →ₐ[T] (κ → T)) (r : Set.range (piRefineIdem α β)) :
    ∃ s : κ → ι × ι, ∃ _ : Algebra (AlgHom.equalizer α β)
        (pieceEqualizer (Localization.Away (r : T)) s),
      ∃ _ : IsLocalization.Away (algebraMap T (AlgHom.equalizer α β) (r : T))
        (pieceEqualizer (Localization.Away (r : T)) s),
      IsLocalization.Away.map (Localization.Away (r : T))
        (pieceEqualizer (Localization.Away (r : T)) s) (algebraMap T (AlgHom.equalizer α β)) (r : T)
        = algebraMap (Localization.Away (r : T))
          (pieceEqualizer (Localization.Away (r : T)) s) := by
  obtain ⟨s, hs⟩ := r.2
  let inst : Algebra (AlgHom.equalizer α β) (pieceEqualizer (Localization.Away (r : T)) s) :=
    (pieceMapCod (Localization.Away (r : T)) α β s hs.symm).toAlgebra
  have halg : ∀ (a : AlgHom.equalizer α β) (i : ι),
      ((algebraMap (AlgHom.equalizer α β) (pieceEqualizer (Localization.Away (r : T)) s) a
        : ι → Localization.Away (r : T)) i)
      = algebraMap T (Localization.Away (r : T)) ((a : ι → T) i) := fun _ _ ↦ rfl
  have := isLocalizationAway_pieceEqualizer (Localization.Away (r : T)) α β s hs.symm halg
  exact ⟨s, inst, this,
    awayMap_eq_algebraMap_pieceEqualizer (Localization.Away (r : T)) α β s halg⟩

variable [Finite ι] [Finite κ] (α β : (ι → T) →ₐ[T] (κ → T))

/-- **The equalizer of two maps of split algebras is étale.** For two `T`-algebra maps
`(ι → T) ⟶ (κ → T)` between finite products of copies of `T`, their equalizer is an étale
`T`-algebra.

The two maps are given by two complete orthogonal families of idempotents of `T`, and over the
localization of `T` at one of the idempotents generated by all their products both maps are
induced by maps of index types, where the equalizer is computed by
`Stacks.FundamentalGroup.indexCoeqPiAlgEquiv`. Since those idempotents span, étaleness follows
by `RingHom.Etale.ofLocalizationSpan`. -/
theorem etale_equalizer_pi : Algebra.Etale T (AlgHom.equalizer α β) := by
  classical
  cases nonempty_fintype ι
  cases nonempty_fintype κ
  rw [← RingHom.etale_algebraMap]
  refine RingHom.Etale.ofLocalizationSpan (algebraMap T (AlgHom.equalizer α β))
    (Set.range (piRefineIdem α β)) (span_range_piRefineIdem α β) ?_
  intro r
  obtain ⟨s, _, _, hmap⟩ := exists_piece_localization α β r
  rw [RingHom.Etale.respectsIso.isLocalization_away_iff (Localization.Away (r : T))
      (pieceEqualizer (Localization.Away (r : T)) s), hmap,
    RingHom.etale_algebraMap]
  exact etale_equalizer_piPrecompAlgHom _ _ _

/-- **The equalizer of two maps of split algebras is module-finite.** For two `T`-algebra maps
`(ι → T) ⟶ (κ → T)` between finite products of copies of `T`, their equalizer is a finite
`T`-module. The proof is that of `Stacks.FundamentalGroup.etale_equalizer_pi`. -/
theorem moduleFinite_equalizer_pi : Module.Finite T (AlgHom.equalizer α β) := by
  classical
  cases nonempty_fintype ι
  cases nonempty_fintype κ
  rw [← RingHom.finite_algebraMap]
  refine RingHom.finite_ofLocalizationSpan (algebraMap T (AlgHom.equalizer α β))
    (Set.range (piRefineIdem α β)) (span_range_piRefineIdem α β) ?_
  intro r
  obtain ⟨s, _, _, hmap⟩ := exists_piece_localization α β r
  rw [RingHom.finite_respectsIso.isLocalization_away_iff (Localization.Away (r : T))
      (pieceEqualizer (Localization.Away (r : T)) s), hmap,
    RingHom.finite_algebraMap]
  exact moduleFinite_equalizer_piPrecompAlgHom _ _ _

end Conclusion

section Transport

/-- Being étale and module-finite transfers along an algebra equivalence. -/
private lemma etale_and_moduleFinite_of_algEquiv {R A A' : Type*} [CommRing R] [CommRing A]
    [CommRing A'] [Algebra R A] [Algebra R A'] [Algebra.Etale R A] [Module.Finite R A]
    (E : A ≃ₐ[R] A') : Algebra.Etale R A' ∧ Module.Finite R A' :=
  ⟨Algebra.Etale.of_equiv E, Module.Finite.equiv E.toLinearEquiv⟩

variable {R : Type u} [CommRing R] {B C : Type u} [CommRing B] [CommRing C]
  [Algebra R B] [Algebra R C]

/-- The equalizer of two algebra maps is carried to the equalizer of the conjugated maps by an
algebra equivalence of the source. -/
lemma map_equalizer_eq {B' C' : Type u} [CommRing B'] [CommRing C'] [Algebra R B'] [Algebra R C']
    (e₁ : B ≃ₐ[R] B') (e₂ : C ≃ₐ[R] C') (α β : B →ₐ[R] C) :
    Subalgebra.map e₁.toAlgHom (AlgHom.equalizer α β)
      = AlgHom.equalizer (e₂.toAlgHom.comp (α.comp e₁.symm.toAlgHom))
        (e₂.toAlgHom.comp (β.comp e₁.symm.toAlgHom)) := by
  ext x
  simp only [Subalgebra.mem_map, AlgHom.mem_equalizer, AlgHom.comp_apply]
  refine ⟨fun ⟨y, hy, hyx⟩ ↦ ?_, fun h ↦ ⟨e₁.symm x, ?_, e₁.apply_symm_apply x⟩⟩
  · rw [← hyx]
    simp [hy]
  · exact e₂.injective h

/-- **The equalizer of two maps of split algebras is finite étale.** If `B` and `C` are finite
split `R`-algebras then the equalizer of any two `R`-algebra maps `B ⟶ C` is a finite étale
`R`-algebra.

This is `Stacks.FundamentalGroup.etale_equalizer_pi` after transporting along the splittings;
the index types are lifted to the universe of `R`, since the equalizer and `R` must lie in the
same universe for `RingHom.Etale.ofLocalizationSpan`. -/
theorem etale_and_moduleFinite_equalizer_of_isFiniteSplit [Algebra.IsFiniteSplit R B]
    [Algebra.IsFiniteSplit R C] (α β : B →ₐ[R] C) :
    Algebra.Etale R (AlgHom.equalizer α β) ∧ Module.Finite R (AlgHom.equalizer α β) := by
  classical
  obtain ⟨n, ⟨f₁⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun R B
  obtain ⟨m, ⟨f₂⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun R C
  let e₁ : B ≃ₐ[R] (ULift.{u} (Fin n) → R) :=
    f₁.trans (AlgEquiv.piCongrLeft' R (fun _ : Fin n ↦ R) Equiv.ulift.symm)
  let e₂ : C ≃ₐ[R] (ULift.{u} (Fin m) → R) :=
    f₂.trans (AlgEquiv.piCongrLeft' R (fun _ : Fin m ↦ R) Equiv.ulift.symm)
  let E : AlgHom.equalizer α β ≃ₐ[R]
      AlgHom.equalizer (e₂.toAlgHom.comp (α.comp e₁.symm.toAlgHom))
        (e₂.toAlgHom.comp (β.comp e₁.symm.toAlgHom)) :=
    (Subalgebra.equivMapOfInjective _ e₁.toAlgHom e₁.injective).trans
      (Subalgebra.equivOfEq _ _ (map_equalizer_eq e₁ e₂ α β))
  have := etale_equalizer_pi (e₂.toAlgHom.comp (α.comp e₁.symm.toAlgHom))
    (e₂.toAlgHom.comp (β.comp e₁.symm.toAlgHom))
  have := moduleFinite_equalizer_pi (e₂.toAlgHom.comp (α.comp e₁.symm.toAlgHom))
    (e₂.toAlgHom.comp (β.comp e₁.symm.toAlgHom))
  exact etale_and_moduleFinite_of_algEquiv E.symm

end Transport

section Descent

open TensorProduct

variable {R : Type u} [CommRing R] {B C : Type u} [CommRing B] [CommRing C]
  [Algebra R B] [Algebra R C]

/-- **Descent of the equalizer along a faithfully flat splitting.** If `B` and `C` become finite
split after base change to a faithfully flat `R`-algebra `T`, then the equalizer of any two
`R`-algebra maps `B ⟶ C` is a finite étale `R`-algebra.

Base change along a flat algebra commutes with the equalizer
(`AlgHom.tensorEqualizerEquiv`), the base-changed equalizer is finite étale by
`Stacks.FundamentalGroup.etale_and_moduleFinite_equalizer_of_isFiniteSplit`, and both finiteness
and étaleness descend along a faithfully flat base change. -/
theorem etale_and_moduleFinite_equalizer_of_faithfullyFlat (T : Type u) [CommRing T] [Algebra R T]
    [Module.FaithfullyFlat R T] [Algebra.IsFiniteSplit T (T ⊗[R] B)]
    [Algebra.IsFiniteSplit T (T ⊗[R] C)] (α β : B →ₐ[R] C) :
    Algebra.Etale R (AlgHom.equalizer α β) ∧ Module.Finite R (AlgHom.equalizer α β) := by
  obtain ⟨hetale, hfinite⟩ := etale_and_moduleFinite_equalizer_of_isFiniteSplit
    (Algebra.TensorProduct.map (AlgHom.id T T) α) (Algebra.TensorProduct.map (AlgHom.id T T) β)
  have E := AlgHom.tensorEqualizerEquiv T T α β
  obtain ⟨h1, h2⟩ := etale_and_moduleFinite_of_algEquiv E.symm
  exact ⟨Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat T,
    Module.Finite.of_finite_tensorProduct_of_faithfullyFlat T⟩

end Descent

section ConstantRank

open TensorProduct

variable {R : Type u} [CommRing R] {B C : Type u} [CommRing B] [CommRing C]
  [Algebra R B] [Algebra R C]

/-- **The equalizer of two maps of finite étale algebras of constant rank is finite étale.**
For `B` and `C` finite étale over `R` of constant rank, the equalizer of any two `R`-algebra maps
`B ⟶ C` is a finite étale `R`-algebra.

This is the affine form of the right-exactness half of Stacks Tag 0BN9: writing the two covers as
`Spec B` and `Spec C` over `Spec R`, the coequalizer is the spectrum of this equalizer. A finite
étale algebra of constant rank becomes split over a faithfully flat finite étale extension
(`Algebra.IsFiniteSplit.exists_tensorProduct_of_etale`); over such an extension the equalizer is
computed by `Stacks.FundamentalGroup.etale_equalizer_pi`, and it descends. -/
theorem etale_and_moduleFinite_equalizer_of_rankAtStalk [Module.Finite R B] [Algebra.Etale R B]
    [Module.Finite R C] [Algebra.Etale R C] {n m : ℕ}
    (hn : Module.rankAtStalk (R := R) B = n) (hm : Module.rankAtStalk (R := R) C = m)
    (α β : B →ₐ[R] C) :
    Algebra.Etale R (AlgHom.equalizer α β) ∧ Module.Finite R (AlgHom.equalizer α β) := by
  obtain ⟨T₁, _, _, _, _, _, hB⟩ :=
    Algebra.IsFiniteSplit.exists_tensorProduct_of_etale (R := R) (S := B) hn
  have : Algebra.Etale T₁ (T₁ ⊗[R] C) := Algebra.Etale.baseChange R C T₁
  have hmT : Module.rankAtStalk (R := T₁) (T₁ ⊗[R] C) = m := by
    funext p
    rw [Module.rankAtStalk_baseChange]
    exact congrFun hm _
  obtain ⟨T₂, _, _, _, _, _, hC⟩ :=
    Algebra.IsFiniteSplit.exists_tensorProduct_of_etale (R := T₁) (S := T₁ ⊗[R] C) hmT
  algebraize [(algebraMap T₁ T₂).comp (algebraMap R T₁)]
  have : Module.FaithfullyFlat R T₂ := Module.FaithfullyFlat.trans R T₁ T₂
  have : Algebra.IsFiniteSplit T₂ (T₂ ⊗[R] B) :=
    Algebra.IsFiniteSplit.of_algEquiv (Algebra.TensorProduct.cancelBaseChange R T₁ T₂ T₂ B)
  have : Algebra.IsFiniteSplit T₂ (T₂ ⊗[R] C) :=
    Algebra.IsFiniteSplit.of_algEquiv (Algebra.TensorProduct.cancelBaseChange R T₁ T₂ T₂ C)
  exact etale_and_moduleFinite_equalizer_of_faithfullyFlat T₂ α β

end ConstantRank

section General

open TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (R : Type u) [CommRing R] (B C : Type u) [CommRing B] [CommRing C]
  [Algebra R B] [Algebra R C]

/-- The set of elements of `R` away from which both `B` and `C` have constant rank. -/
def rankConstantAway : Set R :=
  {r | ∃ n m : ℕ,
    Module.rankAtStalk (R := Localization.Away r) (Localization.Away r ⊗[R] B) = (n : _) ∧
    Module.rankAtStalk (R := Localization.Away r) (Localization.Away r ⊗[R] C) = (m : _)}

variable [Module.Finite R B] [Algebra.Etale R B] [Module.Finite R C] [Algebra.Etale R C]

/-- Every point of the spectrum lies in a basic open away from which both `B` and `C` have
constant rank: the rank of a finitely presented flat module is locally constant. -/
lemma exists_mem_rankConstantAway (p : PrimeSpectrum R) :
    ∃ r ∈ rankConstantAway R B C, r ∉ p.asIdeal := by
  have : Module.FinitePresentation R B :=
    Module.FinitePresentation.of_finite_of_finitePresentation R B
  have : Module.FinitePresentation R C :=
    Module.FinitePresentation.of_finite_of_finitePresentation R C
  have hU : IsOpen ({q | Module.rankAtStalk (R := R) B q = Module.rankAtStalk (R := R) B p} ∩
      {q | Module.rankAtStalk (R := R) C q = Module.rankAtStalk (R := R) C p}) :=
    (Module.isLocallyConstant_rankAtStalk.isOpen_fiber _).inter
      (Module.isLocallyConstant_rankAtStalk.isOpen_fiber _)
  have hpU : p ∈ ({q | Module.rankAtStalk (R := R) B q = Module.rankAtStalk (R := R) B p} ∩
      {q | Module.rankAtStalk (R := R) C q = Module.rankAtStalk (R := R) C p}) := ⟨rfl, rfl⟩
  obtain ⟨V, ⟨r, rfl⟩, hpV, hVU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hpU hU
  have hcomap : ∀ q : PrimeSpectrum (Localization.Away r),
      PrimeSpectrum.comap (algebraMap R (Localization.Away r)) q ∈ PrimeSpectrum.basicOpen r := by
    intro q
    rw [← SetLike.mem_coe, ← PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
    exact Set.mem_range_self q
  refine ⟨r, ⟨Module.rankAtStalk (R := R) B p, Module.rankAtStalk (R := R) C p, ?_, ?_⟩, hpV⟩
  · funext q
    rw [Module.rankAtStalk_baseChange]
    exact (hVU (hcomap q)).1
  · funext q
    rw [Module.rankAtStalk_baseChange]
    exact (hVU (hcomap q)).2

/-- The elements of `R` away from which both `B` and `C` have constant rank generate the unit
ideal of `R`. -/
lemma span_rankConstantAway_eq_top : Ideal.span (rankConstantAway R B C) = ⊤ := by
  by_contra h
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
  obtain ⟨r, hr, hrm⟩ := exists_mem_rankConstantAway R B C (⟨m, hm.isPrime⟩ : PrimeSpectrum R)
  exact hrm (hle (Ideal.subset_span hr))

/-- **The equalizer of two maps of finite étale algebras is finite étale.** This is the affine
form of the right-exactness half of Stacks Tag 0BN9: for `B` and `C` finite étale over `R`, the
equalizer of any two `R`-algebra maps `B ⟶ C` is finite étale over `R`, and its spectrum is the
coequalizer of the two induced maps of finite étale covers of `Spec R`.

Being finite étale is local on `Spec R`, and by local constancy of the rank the ranks of `B` and
`C` are constant after localizing away from the elements of a spanning set
(`Stacks.FundamentalGroup.span_rankConstantAway_eq_top`); there
`Stacks.FundamentalGroup.etale_and_moduleFinite_equalizer_of_rankAtStalk` applies, and the
localization of the equalizer at such an element is the equalizer of the localized maps because
localization is flat. -/
theorem etale_and_moduleFinite_equalizer (α β : B →ₐ[R] C) :
    Algebra.Etale R (AlgHom.equalizer α β) ∧ Module.Finite R (AlgHom.equalizer α β) := by
  have hand : RingHom.OfLocalizationSpan @RingHom.FiniteEtale := by
    intro R' S' _ _ f t ht h
    exact ⟨RingHom.finite_ofLocalizationSpan f t ht fun r ↦ (h r).1,
      RingHom.Etale.ofLocalizationSpan f t ht fun r ↦ (h r).2⟩
  suffices h : RingHom.FiniteEtale (algebraMap R (AlgHom.equalizer α β)) from
    ⟨RingHom.etale_algebraMap.mp h.2, RingHom.finite_algebraMap.mp h.1⟩
  refine hand (algebraMap R (AlgHom.equalizer α β)) (rankConstantAway R B C)
    (span_rankConstantAway_eq_top R B C) ?_
  intro r
  obtain ⟨n, m, hn, hm⟩ := r.2
  have hbase : Algebra.Etale (Localization.Away (r : R))
      (Localization.Away (r : R) ⊗[R] B) := Algebra.Etale.baseChange R B _
  have hbase' : Algebra.Etale (Localization.Away (r : R))
      (Localization.Away (r : R) ⊗[R] C) := Algebra.Etale.baseChange R C _
  obtain ⟨he, hf⟩ := etale_and_moduleFinite_equalizer_of_rankAtStalk hn hm
    (Algebra.TensorProduct.map (AlgHom.id (Localization.Away (r : R)) _) α)
    (Algebra.TensorProduct.map (AlgHom.id (Localization.Away (r : R)) _) β)
  have E := AlgHom.tensorEqualizerEquiv (Localization.Away (r : R)) (Localization.Away (r : R)) α β
  obtain ⟨h1, h2⟩ := etale_and_moduleFinite_of_algEquiv E.symm
  have hloc : IsLocalization.Away (algebraMap R (AlgHom.equalizer α β) (r : R))
      (Localization.Away (r : R) ⊗[R] AlgHom.equalizer α β) := by
    show IsLocalization (Submonoid.powers (algebraMap R (AlgHom.equalizer α β) (r : R))) _
    rw [← Submonoid.map_powers (algebraMap R (AlgHom.equalizer α β)) (r : R)]
    infer_instance
  have hmap : IsLocalization.Away.map (Localization.Away (r : R))
        (Localization.Away (r : R) ⊗[R] AlgHom.equalizer α β)
        (algebraMap R (AlgHom.equalizer α β)) (r : R)
      = algebraMap (Localization.Away (r : R))
        (Localization.Away (r : R) ⊗[R] AlgHom.equalizer α β) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (r : R)) ?_
    simp only [IsLocalization.Away.map, IsLocalization.map_comp]
    refine RingHom.ext fun t ↦ ?_
    show (1 : Localization.Away (r : R)) ⊗ₜ[R] (algebraMap R (AlgHom.equalizer α β) t)
      = algebraMap R (Localization.Away (r : R)) t ⊗ₜ[R] 1
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  refine ⟨?_, ?_⟩
  · rw [RingHom.finite_respectsIso.isLocalization_away_iff (Localization.Away (r : R))
      (Localization.Away (r : R) ⊗[R] AlgHom.equalizer α β), hmap, RingHom.finite_algebraMap]
    exact h2
  · rw [RingHom.Etale.respectsIso.isLocalization_away_iff (Localization.Away (r : R))
      (Localization.Away (r : R) ⊗[R] AlgHom.equalizer α β), hmap, RingHom.etale_algebraMap]
    exact h1

end General

section Category

open CategoryTheory CategoryTheory.Limits

/-- Being finite étale is stable under composition with isomorphisms. -/
lemma _root_.RingHom.FiniteEtale.respectsIso : RingHom.RespectsIso @RingHom.FiniteEtale :=
  RingHom.finite_respectsIso.and RingHom.Etale.respectsIso

/-- A finite product of finite étale algebras is finite étale. -/
lemma _root_.RingHom.FiniteEtale.hasFiniteProducts :
    RingHom.HasFiniteProducts @RingHom.FiniteEtale := by
  intro R _ ι _ S _ _ h
  have hfin : ∀ i, Module.Finite R (S i) := fun i ↦ RingHom.finite_algebraMap.mp (h i).1
  have het : ∀ i, Algebra.Etale R (S i) := fun i ↦ RingHom.etale_algebraMap.mp (h i).2
  exact ⟨RingHom.finite_algebraMap.mpr inferInstance, RingHom.etale_algebraMap.mpr inferInstance⟩

/-- **Stacks 0BN9**, the ring-theoretic form of right exactness: the property of being finite
étale has equalizers, that is, the equalizer of two maps of finite étale algebras is again a
finite étale algebra. -/
lemma _root_.RingHom.FiniteEtale.hasEqualizers : RingHom.HasEqualizers @RingHom.FiniteEtale := by
  intro R S T _ _ _ _ _ f g hS hT
  have : Module.Finite R S := RingHom.finite_algebraMap.mp hS.1
  have : Algebra.Etale R S := RingHom.etale_algebraMap.mp hS.2
  have : Module.Finite R T := RingHom.finite_algebraMap.mp hT.1
  have : Algebra.Etale R T := RingHom.etale_algebraMap.mp hT.2
  obtain ⟨h1, h2⟩ := etale_and_moduleFinite_equalizer R S T f g
  exact ⟨RingHom.finite_algebraMap.mpr h2, RingHom.etale_algebraMap.mpr h1⟩

/-- **The category of finite étale algebras over a commutative ring has finite limits.** This is
the affine, algebraic form of the right-exactness half of Stacks Tag 0BN9: the opposite of this
category is the category of finite étale covers of `Spec R`, so this says that finite étale
covers of an affine scheme have finite colimits.

Finite limits are assembled from finite products and equalizers by Mathlib's
`CommRingCat.Under.hasFiniteLimits`; the equalizers are
`RingHom.FiniteEtale.hasEqualizers`. -/
theorem hasFiniteLimits_finiteEtaleUnder (R : CommRingCat.{u}) :
    HasFiniteLimits ((RingHom.toMorphismProperty @RingHom.FiniteEtale).Under ⊤ R) :=
  CommRingCat.Under.hasFiniteLimits RingHom.FiniteEtale.respectsIso
    RingHom.FiniteEtale.hasFiniteProducts RingHom.FiniteEtale.hasEqualizers R

/-- **Finite colimits of finite étale covers of an affine scheme**, as the opposite of the
category of finite étale algebras. -/
theorem hasFiniteColimits_finiteEtaleUnder_op (R : CommRingCat.{u}) :
    HasFiniteColimits ((RingHom.toMorphismProperty @RingHom.FiniteEtale).Under ⊤ R)ᵒᵖ :=
  have := hasFiniteLimits_finiteEtaleUnder R
  hasFiniteColimits_opposite

end Category

end Stacks.FundamentalGroup

end
