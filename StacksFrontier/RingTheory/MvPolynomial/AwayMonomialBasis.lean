module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.MonoidAlgebra.Grading
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The Laurent monomial basis of a polynomial ring with some variables inverted

Let `R` be a commutative ring and let `f = Tᵟ` be a monomial in `R[Tᵢ]`. This file identifies
the localization `R[Tᵢ][1/f]` with the monoid algebra of `R` on the additive monoid

`exponentMonoid S = {e : ι →₀ ℤ | 0 ≤ e i for every i ∉ S}`,

where `S` is the set of variables occurring in `f`, and reads off the two consequences that
consumers need: `R[Tᵢ][1/f]` is **free over `R` on the Laurent monomials `Tᵉ`** for `e` in that
monoid, and it is **graded by the weight `e`**, the weight-`e` piece being the `R`-line spanned
by `Tᵉ`.

Specialized to `f = T_{i₀} ⋯ T_{i_p}` a product of homogeneous coordinates of `R[T₀, …, Tₙ]`,
this is the `ℤ^{n+1}`-graded monomial basis of

`R[T₀, …, Tₙ, 1/(T_{i₀} ⋯ T_{i_p})]`

used in the proof of [Stacks, Tag 01XT], whose degree parts the Čech computation there is about.

## Main definitions

* `Stacks.PartialLaurent.exponentMonoid`: the monoid of Laurent exponent vectors that are
  nonnegative outside a set `S` of variables.
* `Stacks.PartialLaurent.ofMvPolynomial`: the comparison map `R[Tᵢ] → R[exponentMonoid S]`.
* `Stacks.PartialLaurent.awayAlgEquiv`: any localization of `R[Tᵢ]` away from a monomial is the
  monoid algebra on `exponentMonoid S`.
* `Stacks.PartialLaurent.basis`, `Stacks.PartialLaurent.basisProdX`: the Laurent monomial basis.
* `Stacks.PartialLaurent.weight`: the weight-`e` part.

## Main results

* `Stacks.PartialLaurent.isLocalization`: **the monoid algebra on `exponentMonoid S` is the
  localization of `R[Tᵢ]` at the monomial `Tᵟ`**, for `S` the support of `δ`.
* `Stacks.PartialLaurent.basisProdX`, `Stacks.PartialLaurent.freeProdX`: **the localization of
  `R[T₀, …, Tₙ]` at a product of coordinates is free over `R` on the Laurent monomials `Tᵉ`
  with `0 ≤ e i` for every coordinate `i` that was not inverted.**
* `Stacks.PartialLaurent.weightDecomposition`,
  `Stacks.PartialLaurent.weightDecompositionLocalizedModuleProdX`: **that localization is
  `ℤ^{n+1}`-graded by Laurent weight.**
* `Stacks.PartialLaurent.weight_coe` and `Stacks.PartialLaurent.weight_eq_bot` describe each
  weight piece: it is the `R`-line spanned by the Laurent monomial of that weight, and it
  vanishes at a weight that is negative on a variable which was not inverted.

## Implementation notes

The localization is compared with a monoid algebra rather than built by iterating the
one-variable construction `LaurentPolynomial.isLocalization` over the inverted variables,
because Mathlib already knows that a monoid algebra is free on its monoid
(`AddMonoidAlgebra.basis`) and graded by it (`AddMonoidAlgebra.gradeBy.gradedAlgebra`), so both
conclusions are transports along one ring isomorphism. The isomorphism itself is the three
clauses of `IsLocalization`: the comparison map is `Finsupp.mapDomain` along the inclusion of
exponent vectors, hence injective, and the only real content is that multiplying by a high
enough power of the monomial clears denominators (`exists_nsmul_add_eq`).

Mathlib's `MvPolynomial.prod_X_pow_eq_monomial` writes a product of variable powers indexed by
the support of the exponent as a monomial; `prod_X_eq_monomial` below is the form needed here,
a product over an arbitrary index family which may repeat a variable.

The weight piece is indexed by the *ambient* group of exponent vectors rather than by
`exponentMonoid S`, which is what `AddMonoidAlgebra.gradeBy` along `AddSubmonoid.subtype`
provides, so that the index is the weight the source speaks of.

## References

* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public noncomputable section

open AddMonoidAlgebra

namespace Stacks.PartialLaurent

section ExponentMonoid

variable {ι : Type*}

/-- The additive monoid of Laurent exponent vectors that are nonnegative outside `S`. -/
def exponentMonoid (S : Set ι) : AddSubmonoid (ι →₀ ℤ) where
  carrier := {e | ∀ i ∉ S, 0 ≤ e i}
  add_mem' {a b} ha hb i hi := by simpa using add_nonneg (ha i hi) (hb i hi)
  zero_mem' i _ := by simp

/-- Membership in `exponentMonoid S`: nonnegativity outside `S`. -/
theorem mem_exponentMonoid {S : Set ι} {e : ι →₀ ℤ} :
    e ∈ exponentMonoid S ↔ ∀ i ∉ S, 0 ≤ e i := Iff.rfl

/-- The exponent vector of a monomial, read as a Laurent exponent vector. -/
def natToInt : (ι →₀ ℕ) →+ (ι →₀ ℤ) :=
  Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ)

/-- The coordinates of `natToInt d` are those of `d`, cast to `ℤ`. -/
@[simp] theorem natToInt_apply (d : ι →₀ ℕ) (i : ι) : natToInt d i = (d i : ℤ) := rfl

/-- `natToInt` is injective. -/
theorem natToInt_injective : Function.Injective (natToInt (ι := ι)) :=
  Finsupp.mapRange_injective _ (by simp) Nat.cast_injective

/-- The exponent vector of a monomial lies in `exponentMonoid S`. -/
theorem natToInt_mem (S : Set ι) (d : ι →₀ ℕ) : natToInt d ∈ exponentMonoid S :=
  fun i _ => by simp

/-- The exponent vector of a monomial, as an element of `exponentMonoid S`. -/
def ofNat (S : Set ι) : (ι →₀ ℕ) →+ exponentMonoid S :=
  natToInt.codRestrict (exponentMonoid S) (natToInt_mem S)

/-- `ofNat S d`, as a Laurent exponent vector, is `natToInt d`. -/
@[simp] theorem coe_ofNat (S : Set ι) (d : ι →₀ ℕ) :
    ((ofNat S d : exponentMonoid S) : ι →₀ ℤ) = natToInt d := rfl

/-- `ofNat S` is injective. -/
theorem ofNat_injective (S : Set ι) : Function.Injective (ofNat S) := fun _ _ h =>
  natToInt_injective (Subtype.ext_iff.mp h)

section Of

variable (R : Type*) [CommSemiring R]

/-- The canonical map from the polynomial ring to the partial Laurent ring. -/
def ofMvPolynomial (S : Set ι) :
    MvPolynomial ι R →ₐ[R] AddMonoidAlgebra R (exponentMonoid S) :=
  AddMonoidAlgebra.mapDomainAlgHom R R (ofNat S)

/-- `ofMvPolynomial R S` sends the monomial `c • Tᵈ` to `single (ofNat S d) c`. -/
@[simp] theorem ofMvPolynomial_monomial (S : Set ι) (d : ι →₀ ℕ) (c : R) :
    ofMvPolynomial R S (MvPolynomial.monomial d c) = single (ofNat S d) c :=
  AddMonoidAlgebra.mapDomain_single

/-- `ofMvPolynomial R S` is injective. -/
theorem ofMvPolynomial_injective (S : Set ι) :
    Function.Injective (ofMvPolynomial R S) :=
  AddMonoidAlgebra.mapDomain_injective (ofNat_injective S)

end Of

end ExponentMonoid

section Localization

variable {ι : Type*} (R : Type*) [CommSemiring R]

/-- The monoid algebra on `exponentMonoid S` as an algebra over `R[Tᵢ]`, via `ofMvPolynomial`. -/
instance algebra (S : Set ι) :
    Algebra (MvPolynomial ι R) (AddMonoidAlgebra R (exponentMonoid S)) :=
  (ofMvPolynomial R S).toRingHom.toAlgebra

/-- The algebra map of `R[exponentMonoid S]` over `R[Tᵢ]` is `ofMvPolynomial R S`. -/
theorem algebraMap_eq (S : Set ι) :
    algebraMap (MvPolynomial ι R) (AddMonoidAlgebra R (exponentMonoid S)) =
      (ofMvPolynomial R S).toRingHom := rfl

/-- The scalar tower `R → R[Tᵢ] → R[exponentMonoid S]`. -/
instance isScalarTower (S : Set ι) :
    IsScalarTower R (MvPolynomial ι R) (AddMonoidAlgebra R (exponentMonoid S)) :=
  ⟨fun r p z => by
    change (ofMvPolynomial R S) (r • p) * z = r • ((ofMvPolynomial R S) p * z)
    rw [map_smul, smul_mul_assoc]⟩

variable {R}
variable (δ : ι →₀ ℕ)

/-- Every `e` in `exponentMonoid δ.support` becomes the exponent vector of a monomial after
adding a multiple of `δ`. -/
theorem exists_nsmul_add_eq {e : ι →₀ ℤ} (he : e ∈ exponentMonoid (↑δ.support : Set ι)) :
    ∃ (m : ℕ) (d : ι →₀ ℕ), e + m • natToInt δ = natToInt d := by
  classical
  set m : ℕ := e.support.sup fun i => (-(e i)).toNat with hm
  have key : ∀ i, 0 ≤ e i + (m : ℤ) * (δ i : ℤ) := by
    intro i
    rcases le_or_gt 0 (e i) with h | h
    · have h2 : (0 : ℤ) ≤ (m : ℤ) * (δ i : ℤ) := by positivity
      linarith
    · have hi : i ∈ e.support := Finsupp.mem_support_iff.mpr (by omega)
      have hmi : (-(e i)).toNat ≤ m := Finset.le_sup (f := fun i => (-(e i)).toNat) hi
      have hiδ : i ∈ δ.support := by
        by_contra hc
        exact absurd (he i (by simpa using hc)) (by omega)
      have hδ : 1 ≤ (δ i : ℤ) := by have := Finsupp.mem_support_iff.mp hiδ; omega
      have hm1 : (m : ℤ) * 1 ≤ (m : ℤ) * (δ i : ℤ) :=
        mul_le_mul_of_nonneg_left hδ (by positivity)
      have : -(e i) ≤ (m : ℤ) := by omega
      linarith
  refine ⟨m, Finsupp.mapRange Int.toNat (by simp) (e + m • natToInt δ), ?_⟩
  ext i
  have hk := key i
  simp only [natToInt_apply, Finsupp.mapRange_apply, Finsupp.add_apply, Finsupp.smul_apply,
    nsmul_eq_mul]
  omega

/-- `-δ` lies in `exponentMonoid δ.support`. -/
theorem neg_natToInt_mem : -(natToInt δ) ∈ exponentMonoid (↑δ.support : Set ι) := by
  intro i hi
  have : δ i = 0 := Finsupp.notMem_support_iff.mp (by simpa using hi)
  simp [this]

variable (R)

/-- The image `single δ 1` of the monomial `Tᵟ` is a unit of `R[exponentMonoid δ.support]`. -/
theorem isUnit_single_ofNat :
    IsUnit (single (ofNat (↑δ.support : Set ι) δ) (1 : R)) := by
  set a : exponentMonoid (↑δ.support : Set ι) := ofNat (↑δ.support : Set ι) δ with ha
  set b : exponentMonoid (↑δ.support : Set ι) := ⟨-(natToInt δ), neg_natToInt_mem δ⟩ with hb
  have hab : a + b = 0 := Subtype.ext (by simp [ha, hb])
  exact IsUnit.of_mul_eq_one (single b 1) (by rw [single_mul_single, mul_one, hab, ← one_def])

/-- Elements of the partial Laurent ring that some power of the inverted monomial carries
into the polynomial ring. -/
def clearDenominator :
    Submodule R (AddMonoidAlgebra R (exponentMonoid (↑δ.support : Set ι))) where
  carrier := {z | ∃ (m : ℕ) (p : MvPolynomial ι R),
    z * ofMvPolynomial R _ (MvPolynomial.monomial δ 1) ^ m = ofMvPolynomial R _ p}
  add_mem' := by
    rintro x y ⟨m₁, p₁, h₁⟩ ⟨m₂, p₂, h₂⟩
    refine ⟨m₁ + m₂,
      p₁ * MvPolynomial.monomial δ 1 ^ m₂ + p₂ * MvPolynomial.monomial δ 1 ^ m₁, ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, ← h₁, ← h₂, pow_add]
    ring
  zero_mem' := ⟨0, 0, by simp⟩
  smul_mem' := by
    rintro r x ⟨m, p, h⟩
    exact ⟨m, r • p, by rw [map_smul, ← h, smul_mul_assoc]⟩

/-- Every element of `R[exponentMonoid δ.support]` is carried into the image of `R[Tᵢ]` by
some power of `Tᵟ`. -/
theorem clearDenominator_eq_top : clearDenominator R δ = ⊤ := by
  rw [eq_top_iff, ← (AddMonoidAlgebra.basis (exponentMonoid (↑δ.support : Set ι)) R).span_eq,
    Submodule.span_le]
  rintro x ⟨e, rfl⟩
  obtain ⟨m, d, hmd⟩ := exists_nsmul_add_eq δ e.2
  refine ⟨m, MvPolynomial.monomial d 1, ?_⟩
  rw [AddMonoidAlgebra.basis_apply, ofMvPolynomial_monomial, ofMvPolynomial_monomial,
    single_pow, one_pow, single_mul_single, one_mul]
  congr 1
  exact Subtype.ext (by simpa using hmd)

/-- Every `z` in `R[exponentMonoid δ.support]` satisfies `z * Tᵟ ^ m = p` for some `m : ℕ`
and some polynomial `p`. -/
theorem exists_mul_pow_eq
    (z : AddMonoidAlgebra R (exponentMonoid (↑δ.support : Set ι))) :
    ∃ (m : ℕ) (p : MvPolynomial ι R),
      z * ofMvPolynomial R _ (MvPolynomial.monomial δ 1) ^ m = ofMvPolynomial R _ p := by
  have h : z ∈ clearDenominator R δ := clearDenominator_eq_top R δ ▸ Submodule.mem_top
  exact h

/-- The monoid algebra on `exponentMonoid δ.support` is a localization of `R[Tᵢ]` away from
the monomial `Tᵟ`. -/
instance isLocalization :
    IsLocalization.Away (MvPolynomial.monomial δ (1 : R))
      (AddMonoidAlgebra R (exponentMonoid (↑δ.support : Set ι))) := by
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨t, n, rfl⟩
    rw [algebraMap_eq]
    change IsUnit (ofMvPolynomial R _ (MvPolynomial.monomial δ 1 ^ n))
    rw [map_pow, ofMvPolynomial_monomial]
    exact (isUnit_single_ofNat R δ).pow n
  · intro z
    obtain ⟨m, p, h⟩ := exists_mul_pow_eq R δ z
    refine ⟨(p, ⟨MvPolynomial.monomial δ 1 ^ m, m, rfl⟩), ?_⟩
    rw [algebraMap_eq]
    change z * ofMvPolynomial R _ (MvPolynomial.monomial δ 1 ^ m) = ofMvPolynomial R _ p
    rwa [map_pow]
  · intro x y h
    rw [algebraMap_eq] at h
    exact ⟨1, by simp [ofMvPolynomial_injective R _ h]⟩

end Localization

section Comparison

variable {ι : Type*} (R : Type*) [CommSemiring R] (δ : ι →₀ ℕ)
variable (T : Type*) [CommSemiring T] [Algebra (MvPolynomial ι R) T]
  [IsLocalization.Away (MvPolynomial.monomial δ (1 : R)) T]

/-- Any localization of `R[T_i]` away from a monomial is the partial Laurent ring. -/
def awayAlgEquiv :
    T ≃ₐ[MvPolynomial ι R] AddMonoidAlgebra R (exponentMonoid (↑δ.support : Set ι)) :=
  IsLocalization.algEquiv (Submonoid.powers (MvPolynomial.monomial δ (1 : R))) T _

variable [Module R T] [IsScalarTower R (MvPolynomial ι R) T]

/-- The comparison of a localization away from a monomial with the partial Laurent ring,
as an `R`-linear equivalence. -/
def awayLinearEquiv :
    T ≃ₗ[R] AddMonoidAlgebra R (exponentMonoid (↑δ.support : Set ι)) :=
  ((awayAlgEquiv R δ T).toLinearEquiv).restrictScalars R

/-- **The Laurent monomial basis.** -/
def basis : Module.Basis (exponentMonoid (↑δ.support : Set ι)) R T :=
  (AddMonoidAlgebra.basis (exponentMonoid (↑δ.support : Set ι)) R).map
    (awayLinearEquiv R δ T).symm

/-- The basis vector at `e` is the preimage of `single e 1` under `awayAlgEquiv`. -/
theorem basis_apply (e : exponentMonoid (↑δ.support : Set ι)) :
    basis R δ T e = (awayAlgEquiv R δ T).symm (single e 1) := by
  simp only [basis, Module.Basis.map_apply, AddMonoidAlgebra.basis_apply]
  rfl

include δ in
/-- A localization of `R[Tᵢ]` away from a monomial is a free `R`-module. -/
theorem free : Module.Free R T := Module.Free.of_basis (basis R δ T)

/-- The basis vector at the exponent vector of a monomial `Tᵈ` is the image of `Tᵈ`. -/
theorem basis_ofNat (d : ι →₀ ℕ) :
    basis R δ T (ofNat (↑δ.support : Set ι) d) =
      algebraMap (MvPolynomial ι R) T (MvPolynomial.monomial d 1) := by
  rw [basis_apply, ← ofMvPolynomial_monomial R (↑δ.support : Set ι) d 1]
  exact (awayAlgEquiv R δ T).symm.commutes _

/-- The product of the basis vectors at `e` and `e'` is the basis vector at `e + e'`. -/
theorem basis_mul_basis (e e' : exponentMonoid (↑δ.support : Set ι)) :
    basis R δ T e * basis R δ T e' = basis R δ T (e + e') := by
  rw [basis_apply, basis_apply, basis_apply, ← map_mul, single_mul_single, mul_one]

end Comparison

section Weight

variable {ι : Type*} [DecidableEq ι] (R : Type*) [CommRing R] (δ : ι →₀ ℕ)
variable (T : Type*) [CommRing T] [Algebra (MvPolynomial ι R) T]
  [IsLocalization.Away (MvPolynomial.monomial δ (1 : R)) T]
  [Module R T] [IsScalarTower R (MvPolynomial ι R) T]

/-- The weight-`e` part of a localization of `R[T_i]` away from a monomial. -/
def weight (e : ι →₀ ℤ) : Submodule R T :=
  (AddMonoidAlgebra.gradeBy R ⇑(exponentMonoid (↑δ.support : Set ι)).subtype e).map
    (awayLinearEquiv R δ T).symm.toLinearMap

omit [DecidableEq ι] in
/-- The weight pieces span the localization. -/
theorem iSup_weight_eq_top : (⨆ e, weight R δ T e) = ⊤ := by
  classical
  have h := (DirectSum.Decomposition.isInternal (AddMonoidAlgebra.gradeBy R
    ⇑(exponentMonoid (↑δ.support : Set ι)).subtype)).submodule_iSup_eq_top
  simp only [weight]
  rw [← Submodule.map_iSup, h, Submodule.map_top]
  exact (awayLinearEquiv R δ T).symm.range

omit [DecidableEq ι] in
/-- The weight pieces are independent. -/
theorem iSupIndep_weight : iSupIndep (weight R δ T) := by
  classical
  have h : iSupIndep (AddMonoidAlgebra.gradeBy R
      ⇑(exponentMonoid (↑δ.support : Set ι)).subtype) :=
    (DirectSum.Decomposition.isInternal _).submodule_iSupIndep
  exact h.map_orderIso (Submodule.orderIsoMapComap (awayLinearEquiv R δ T).symm)

/-- The localization is the internal direct sum of its weight pieces. -/
theorem isInternal_weight : DirectSum.IsInternal (weight R δ T) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_weight R δ T) (iSup_weight_eq_top R δ T)

/-- **The `ℤ^ι`-grading by Laurent weight.** -/
@[instance_reducible]
def weightDecomposition : DirectSum.Decomposition (weight R δ T) :=
  (isInternal_weight R δ T).chooseDecomposition

end Weight

section Grade

/-- A grade of a monoid algebra is the `R`-line spanned by the corresponding monomial. -/
theorem grade_eq_span_single {M : Type*} [AddMonoid M] (R : Type*) [CommSemiring R] (m : M) :
    AddMonoidAlgebra.grade R m = Submodule.span R {single m (1 : R)} := by
  rw [AddMonoidAlgebra.grade_eq_lsingle_range]
  refine le_antisymm ?_ ?_
  · rintro x ⟨c, rfl⟩
    refine Submodule.mem_span_singleton.mpr ⟨c, ?_⟩
    rw [AddMonoidAlgebra.smul_single, AddMonoidAlgebra.lsingle_apply, smul_eq_mul, mul_one]
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact ⟨1, rfl⟩

variable {ι : Type*} (R : Type*) [CommSemiring R] (S : Set ι)

/-- Grading an `AddSubmonoid`-indexed monoid algebra by the ambient monoid: at a weight that
lies in the submonoid, the piece is the `R`-line of that monomial. -/
theorem gradeBy_subtype_coe (x : exponentMonoid S) :
    AddMonoidAlgebra.gradeBy R ⇑(exponentMonoid S).subtype (x : ι →₀ ℤ) =
      Submodule.span R {single x (1 : R)} := by
  rw [← grade_eq_span_single R x]
  exact Submodule.ext fun a => ⟨fun ha m hm => Subtype.coe_injective (ha m hm),
    fun ha m hm => congrArg _ (ha m hm)⟩

/-- At a weight outside the submonoid the graded piece vanishes. -/
theorem gradeBy_subtype_eq_bot {e : ι →₀ ℤ} (he : e ∉ exponentMonoid S) :
    AddMonoidAlgebra.gradeBy R ⇑(exponentMonoid S).subtype e = ⊥ := by
  refine le_antisymm (fun a ha => ?_) bot_le
  simp only [AddMonoidAlgebra.mem_gradeBy_iff] at ha
  have hsupp : a.coeff.support = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro m hm
    exact he (ha hm ▸ m.2)
  rw [Submodule.mem_bot, ← AddMonoidAlgebra.coeff_inj, AddMonoidAlgebra.coeff_zero]
  exact Finsupp.support_eq_empty.mp hsupp

end Grade

section WeightConcrete

variable {ι : Type*} [DecidableEq ι] (R : Type*) [CommRing R] (δ : ι →₀ ℕ)
variable (T : Type*) [CommRing T] [Algebra (MvPolynomial ι R) T]
  [IsLocalization.Away (MvPolynomial.monomial δ (1 : R)) T]
  [Module R T] [IsScalarTower R (MvPolynomial ι R) T]

omit [DecidableEq ι] in
/-- **Each weight piece is the `R`-line spanned by its Laurent monomial.** -/
theorem weight_coe (e : exponentMonoid (↑δ.support : Set ι)) :
    weight R δ T (e : ι →₀ ℤ) = Submodule.span R {basis R δ T e} := by
  rw [basis_apply, weight, gradeBy_subtype_coe, Submodule.map_span, Set.image_singleton]
  rfl

omit [DecidableEq ι] in
/-- At a weight that is negative on a variable which was not inverted, the piece vanishes. -/
theorem weight_eq_bot {e : ι →₀ ℤ} (he : e ∉ exponentMonoid (↑δ.support : Set ι)) :
    weight R δ T e = ⊥ := by
  rw [weight, gradeBy_subtype_eq_bot R _ he, Submodule.map_bot]

end WeightConcrete

section ProdX

variable {σ κ : Type*} (R : Type*) [CommSemiring R]

/-- A product of variables is a monomial. -/
theorem prod_X_eq_monomial (t : Finset κ) (s : κ → σ) :
    (∏ j ∈ t, MvPolynomial.X (s j) : MvPolynomial σ R) =
      MvPolynomial.monomial (∑ j ∈ t, Finsupp.single (s j) 1) 1 := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a u ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih,
      show (MvPolynomial.X (s a) : MvPolynomial σ R) =
        MvPolynomial.monomial (Finsupp.single (s a) 1) 1 from rfl,
      MvPolynomial.monomial_mul_monomial, one_mul]

/-- The variables occurring in a product of variables. -/
theorem support_sum_single [DecidableEq σ] (t : Finset κ) (s : κ → σ) :
    (∑ j ∈ t, Finsupp.single (s j) (1 : ℕ)).support = t.image s := by
  classical
  ext i
  simp only [Finsupp.mem_support_iff, Finset.mem_image, ne_eq, Finsupp.finsetSum_apply,
    Finsupp.single_apply, Finset.sum_eq_zero_iff, not_forall]
  simp

variable {n r : ℕ}

/-- The coordinates occurring in `∑ j, single (s j) 1` form the range of `s`. -/
theorem coe_support_sum_single (s : Fin (r + 1) → Fin (n + 1)) :
    (↑(∑ j, Finsupp.single (s j) (1 : ℕ)).support : Set (Fin (n + 1))) = Set.range s := by
  simp [support_sum_single]

/-- The index set of the Laurent monomial basis: exponent vectors `e : Fin (n+1) → ℤ` that
are nonnegative outside the inverted coordinates. -/
def prodXIndexEquiv (s : Fin (r + 1) → Fin (n + 1)) :
    exponentMonoid (↑(∑ j, Finsupp.single (s j) (1 : ℕ)).support : Set (Fin (n + 1))) ≃
      {e : Fin (n + 1) → ℤ // ∀ i ∉ Set.range s, 0 ≤ e i} :=
  Equiv.subtypeEquiv Finsupp.equivFunOnFinite fun e => by
    rw [mem_exponentMonoid, coe_support_sum_single]
    exact Iff.rfl

variable (s : Fin (r + 1) → Fin (n + 1)) (T : Type*) [CommSemiring T]
  [Algebra (MvPolynomial (Fin (n + 1)) R) T]
  [IsLocalization.Away (∏ j, MvPolynomial.X (s j) : MvPolynomial (Fin (n + 1)) R) T]

/-- Inverting a product of coordinates is inverting the corresponding monomial. -/
instance away_prod_X :
    IsLocalization.Away
      (MvPolynomial.monomial (∑ j, Finsupp.single (s j) (1 : ℕ)) (1 : R)) T := by
  rw [← prod_X_eq_monomial R Finset.univ s]
  infer_instance

variable [Module R T] [IsScalarTower R (MvPolynomial (Fin (n + 1)) R) T]

/-- **The Laurent monomial basis of `R[T₀,…,Tₙ][1/(T_{i₀}⋯T_{i_p})]`.** The localization of
the polynomial ring at a product of coordinates is free over `R` on the Laurent monomials
`T^e` with `e i ≥ 0` for every coordinate `i` that was not inverted. -/
def basisProdX : Module.Basis {e : Fin (n + 1) → ℤ // ∀ i ∉ Set.range s, 0 ≤ e i} R T :=
  (basis R (∑ j, Finsupp.single (s j) (1 : ℕ)) T).reindex (prodXIndexEquiv s)

include s in
/-- A localization of `R[T₀, …, Tₙ]` at a product of coordinates is a free `R`-module. -/
theorem freeProdX : Module.Free R T := Module.Free.of_basis (basisProdX R s T)

end ProdX

section ModuleLocalization

variable {n r : ℕ} (R : Type*) [CommRing R] (s : Fin (r + 1) → Fin (n + 1))

/-- **The Laurent monomial basis of `R[T₀,…,Tₙ][1/(T_{i₀}⋯T_{i_p})]`**, at the module
localization in which the degree parts of a twist are built. -/
def basisLocalizedModuleProdX :
    Module.Basis {e : Fin (n + 1) → ℤ // ∀ i ∉ Set.range s, 0 ≤ e i} R
      (LocalizedModule.Away (∏ j, MvPolynomial.X (s j) : MvPolynomial (Fin (n + 1)) R)
        (MvPolynomial (Fin (n + 1)) R)) :=
  basisProdX R s _

/-- **The `ℤ^{n+1}`-grading of `R[T₀,…,Tₙ][1/(T_{i₀}⋯T_{i_p})]` by Laurent weight**, at the
module localization in which the degree parts of a twist are built. -/
@[instance_reducible]
def weightDecompositionLocalizedModuleProdX :
    DirectSum.Decomposition (weight R (∑ j, Finsupp.single (s j) (1 : ℕ))
      (LocalizedModule.Away (∏ j, MvPolynomial.X (s j) : MvPolynomial (Fin (n + 1)) R)
        (MvPolynomial (Fin (n + 1)) R))) :=
  weightDecomposition R _ _

end ModuleLocalization

end Stacks.PartialLaurent

end
