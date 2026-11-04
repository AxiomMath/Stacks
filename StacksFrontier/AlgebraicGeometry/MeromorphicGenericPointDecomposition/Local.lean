module

public import Mathlib.AlgebraicGeometry.Stalk
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.StalksWeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Affine
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.GenericPoints
public import StacksFrontier.RingTheory.Branches.MinimalPrimes
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local rings at generic points, and the total quotient ring of an affine open

Let `X` be a scheme whose weakly associated points are all generic points of irreducible
components and whose quasi-compact opens have finitely many irreducible components. This file
collects the local input for the decomposition of the sheaf of meromorphic functions on such a
scheme into the contributions of the generic points.

Two things happen here. First, the spectrum of the local ring at a generic point `η` has `η` as
its only image point, so that local ring has a unique prime ideal and every nonzerodivisor in
it is a unit. Second, on an affine open `U` the zerodivisors of `Γ(X, U)` are exactly the union
of the minimal primes, so the product of the local rings at the generic points lying in `U` is
the total ring of fractions of `Γ(X, U)`.

## Main results

* `AlgebraicGeometry.range_fromSpecStalk_eq_singleton_of_mem_genericPoints`: the canonical
  morphism from the spectrum of the local ring at a generic point has that point as its image.
* `AlgebraicGeometry.fromSpecStalk_preimage_eq_top`,
  `AlgebraicGeometry.fromSpecStalk_preimage_eq_bot`: consequently the preimage of an open is
  everything or nothing, according to whether it contains the generic point.
* `AlgebraicGeometry.isUnit_of_mem_nonZeroDivisors_stalk_of_mem_genericPoints`: nonzerodivisors
  in the local ring at a generic point are units.
* `AlgebraicGeometry.exists_minimalPrimes_mem_of_notMem_nonZeroDivisors`: on an affine open,
  every zerodivisor lies in a minimal prime.
* `AlgebraicGeometry.isLocalization_pi_stalk_genericPoints`: the product of the local rings at
  the generic points lying in an affine open is the total ring of fractions of its ring of
  sections.
* `isLocalization_pi_of_bijOn_minimalPrimes`: the ring-theoretic form of the last statement.
* `piSubtypeAlgEquivOfSubsingleton`: a product of algebras is unchanged by discarding trivial
  factors.

## Implementation notes

The ring-theoretic core is tag 02LX,
`total_fraction_ring_isoProd_localization_atPrime`, which is stated for an injective
enumeration of the minimal primes by a `Fin t`; `isLocalization_pi_of_bijOn_minimalPrimes`
restates it as an `IsLocalization` statement for an arbitrary finite indexing of the minimal
primes and an arbitrary choice of localization in each factor, which is what the geometric
application needs: there the index set is the set of generic points lying in the affine open
and the factors are the stalks.

That a zerodivisor lies in a minimal prime is the only place the hypothesis on the weakly
associated points is used: a minimal prime over the annihilator of a witness is a weakly
associated prime, hence a generic point, hence a minimal prime.

## References

* [Stacks Project, Tag 0EMF](https://stacks.math.columbia.edu/tag/0EMF)
* [Stacks Project, Tag 02LX](https://stacks.math.columbia.edu/tag/02LX)
* [Stacks Project, Tag 05C3](https://stacks.math.columbia.edu/tag/05C3)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u v w

/-- Restricting a product of algebras to a subfamily of the factors is an isomorphism when all
the discarded factors are trivial. -/
noncomputable def piSubtypeAlgEquivOfSubsingleton {A : Type u} [CommRing A] {ι : Type v}
    (P : ι → Prop) (C : ι → Type w) [∀ i, CommRing (C i)] [∀ i, Algebra A (C i)]
    (h : ∀ i, ¬ P i → Subsingleton (C i)) :
    (∀ i, C i) ≃ₐ[A] (∀ i : {i // P i}, C i.1) := by
  classical
  refine AlgEquiv.ofBijective
    { toFun := fun f i => f i.1
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl } ⟨?_, ?_⟩
  · intro f g hfg
    funext i
    by_cases hi : P i
    · exact congrFun hfg ⟨i, hi⟩
    · exact (h i hi).elim _ _
  · intro g
    refine ⟨fun i => if hi : P i then g ⟨i, hi⟩ else 0, ?_⟩
    funext i
    change (if hi : P i.1 then g ⟨i.1, hi⟩ else 0) = g i
    rw [dite_eq_left_of_eq_true (by simp [i.2])]

/-- **Stacks 02LX, as an `IsLocalization` statement.** Let `A` be a commutative ring whose
zerodivisors all lie in minimal primes, and let `q : ι → Ideal A` be a finite enumeration
without repetition of all the minimal primes of `A`. Then any family of localizations of `A` at
those primes has product the total ring of fractions of `A`. -/
theorem isLocalization_pi_of_bijOn_minimalPrimes
    {A : Type u} [CommRing A]
    (hzd : ∀ x : A, x ∉ nonZeroDivisors A → ∃ p ∈ minimalPrimes A, x ∈ p)
    {ι : Type v} [Finite ι] (q : ι → Ideal A) [∀ i, (q i).IsPrime]
    (hmem : ∀ i, q i ∈ minimalPrimes A) (hinj : Function.Injective q)
    (hsurj : ∀ p ∈ minimalPrimes A, ∃ i, q i = p)
    (B : ι → Type w) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
    [∀ i, IsLocalization (q i).primeCompl (B i)] :
    IsLocalization (nonZeroDivisors A) (∀ i, B i) := by
  let e : Fin (Nat.card ι) ≃ ι := (Finite.equivFin ι).symm
  have hzd' : zeroDivisorsSet A = ⋃ k, ((q (e k) : Ideal A) : Set A) := by
    ext x
    simp only [zeroDivisorsSet, Set.mem_ofPred_eq, Set.mem_iUnion, SetLike.mem_coe]
    constructor
    · intro hx
      obtain ⟨p, hp, hxp⟩ := hzd x hx
      obtain ⟨i, rfl⟩ := hsurj p hp
      exact ⟨e.symm i, by rwa [Equiv.apply_symm_apply]⟩
    · rintro ⟨k, hk⟩
      exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hk (hmem (e k))
  obtain ⟨f⟩ := total_fraction_ring_isoProd_localization_atPrime
    (Nat.card ι) (fun k => q (e k)) (fun k => hmem _) (hinj.comp e.injective) hzd'
  have h1 : IsLocalization (nonZeroDivisors A) (∀ k, Localization.AtPrime (q (e k))) :=
    IsLocalization.isLocalization_of_algEquiv _ f
  have h2 : IsLocalization (nonZeroDivisors A) (∀ i, Localization.AtPrime (q i)) :=
    IsLocalization.isLocalization_of_algEquiv _
      (AlgEquiv.piCongrLeft A (fun i => Localization.AtPrime (q i)) e)
  exact IsLocalization.isLocalization_of_algEquiv _
    (AlgEquiv.piCongrRight (R := A) fun i =>
      IsLocalization.algEquiv (q i).primeCompl (Localization.AtPrime (q i)) (B i))

/-- In a local ring with a unique prime ideal every nonzerodivisor is a unit: the maximal ideal
is then the nilradical, and a nilpotent nonzerodivisor would force the ring to be trivial. -/
theorem isUnit_of_mem_nonZeroDivisors_of_subsingleton_primeSpectrum
    (R : Type u) [CommRing R] [IsLocalRing R] [Subsingleton (PrimeSpectrum R)]
    {a : R} (ha : a ∈ nonZeroDivisors R) : IsUnit a := by
  rw [← IsLocalRing.notMem_maximalIdeal]
  intro hmem
  have hnil : IsNilpotent a := by
    rw [← mem_nilradical, nilradical_eq_sInf, Submodule.mem_sInf]
    intro J hJ
    have hJp : Ideal.IsPrime J := hJ
    have hsub : (⟨J, hJp⟩ : PrimeSpectrum R) =
        ⟨IsLocalRing.maximalIdeal R, Ideal.IsMaximal.isPrime inferInstance⟩ :=
      Subsingleton.elim _ _
    have hJeq : J = IsLocalRing.maximalIdeal R := congrArg PrimeSpectrum.asIdeal hsub
    exact hJeq ▸ hmem
  obtain ⟨n, hn⟩ := hnil
  have h0 : (0 : R) ∈ nonZeroDivisors R := by rw [← hn]; exact pow_mem ha n
  exact one_ne_zero ((mem_nonZeroDivisors_iff_right.mp h0) 1 (by simp))

namespace AlgebraicGeometry

/-- A generic point of an irreducible component has no proper generalization. -/
private lemma eq_of_specializes_genericPoint {T : Type*} [TopologicalSpace T] [T0Space T]
    {x : T} (hx : x ∈ genericPoints T) {x' : T} (h : x' ⤳ x) : x' = x := by
  have hback : closure ({x'} : Set T) ⊆ closure ({x} : Set T) :=
    (genericPoints.component ⟨x, hx⟩).2.2 isIrreducible_singleton.closure
      (specializes_iff_closure_subset.mp h)
  exact (h.antisymm (specializes_iff_closure_subset.mpr hback)).eq

/-- The spectrum of the local ring at a generic point of an irreducible component maps onto
that point alone. -/
lemma range_fromSpecStalk_eq_singleton_of_mem_genericPoints {X : Scheme.{u}} {x : X}
    (hx : x ∈ genericPoints X) : Set.range (X.fromSpecStalk x) = {x} := by
  rw [Scheme.range_fromSpecStalk]
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  exact ⟨fun hz ↦ eq_of_specializes_genericPoint hx hz, fun h ↦ h ▸ specializes_rfl⟩

/-- Every point of the spectrum of the local ring at a generic point is sent to that point. -/
lemma fromSpecStalk_base_eq {X : Scheme.{u}} {x : X} (hx : x ∈ genericPoints X)
    (p : Spec (X.presheaf.stalk x)) : (X.fromSpecStalk x) p = x := by
  have h : (X.fromSpecStalk x) p ∈ Set.range (X.fromSpecStalk x) := ⟨p, rfl⟩
  rw [range_fromSpecStalk_eq_singleton_of_mem_genericPoints hx] at h
  exact h

/-- The preimage of an open containing a generic point, under the canonical morphism from the
spectrum of the local ring there, is everything. -/
lemma fromSpecStalk_preimage_eq_top {X : Scheme.{u}} {x : X} (hx : x ∈ genericPoints X)
    {U : X.Opens} (hxU : x ∈ U) : X.fromSpecStalk x ⁻¹ᵁ U = ⊤ := by
  apply Opens.ext
  refine Set.eq_univ_of_forall fun p ↦ ?_
  show (X.fromSpecStalk x) p ∈ U
  rw [fromSpecStalk_base_eq hx p]
  exact hxU

/-- The preimage of an open not containing a generic point, under the canonical morphism from
the spectrum of the local ring there, is empty. -/
lemma fromSpecStalk_preimage_eq_bot {X : Scheme.{u}} {x : X} (hx : x ∈ genericPoints X)
    {U : X.Opens} (hxU : x ∉ U) : X.fromSpecStalk x ⁻¹ᵁ U = ⊥ := by
  apply Opens.ext
  refine Set.eq_empty_of_forall_notMem fun p hp ↦ ?_
  exact hxU (fromSpecStalk_base_eq hx p ▸ hp)

/-- The spectrum of the local ring at a generic point of an irreducible component is a single
point, so that local ring has a unique prime ideal. -/
instance subsingleton_primeSpectrum_stalk_of_mem_genericPoints {X : Scheme.{u}}
    (η : genericPoints X) : Subsingleton (PrimeSpectrum (X.presheaf.stalk η.1)) := by
  constructor
  intro p q
  apply (X.fromSpecStalk η.1).isEmbedding.injective
  rw [fromSpecStalk_base_eq η.2 p, fromSpecStalk_base_eq η.2 q]

/-- A nonzerodivisor in the local ring at a generic point of an irreducible component is a
unit: that local ring has dimension zero. -/
lemma isUnit_of_mem_nonZeroDivisors_stalk_of_mem_genericPoints {X : Scheme.{u}} {x : X}
    (hx : x ∈ genericPoints X) {a : X.presheaf.stalk x}
    (ha : a ∈ nonZeroDivisors (X.presheaf.stalk x)) : IsUnit a :=
  have := subsingleton_primeSpectrum_stalk_of_mem_genericPoints (X := X) ⟨x, hx⟩
  isUnit_of_mem_nonZeroDivisors_of_subsingleton_primeSpectrum _ ha

/-- If every weakly associated point of `X` is a generic point of an irreducible component,
then on an affine open every zerodivisor lies in a minimal prime of the ring of sections. -/
@[ega "IV 20.1.3.1" "special case"]
lemma exists_minimalPrimes_mem_of_notMem_nonZeroDivisors
    {X : Scheme.{u}} (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    {U : X.Opens} (hU : IsAffineOpen U) {x : Γ(X, U)} (hx : x ∉ nonZeroDivisors Γ(X, U)) :
    ∃ p ∈ minimalPrimes Γ(X, U), x ∈ p := by
  rw [mem_nonZeroDivisors_iff_left] at hx
  push Not at hx
  obtain ⟨z, hxz, hz0⟩ := hx
  have hproper : (Γ(X, U) ∙ z).annihilator ≠ ⊤ := by
    intro h
    have h1 : (1 : Γ(X, U)) ∈ (Γ(X, U) ∙ z).annihilator := by rw [h]; trivial
    exact hz0 (by simpa using (Submodule.mem_annihilator_span_singleton z 1).mp h1)
  obtain ⟨q, hq⟩ := Ideal.nonempty_minimalPrimes hproper
  let p : PrimeSpectrum Γ(X, U) := ⟨q, hq.1.1⟩
  have hpU : hU.fromSpec p ∈ U := hU.range_fromSpec.subset ⟨p, rfl⟩
  let y : U := ⟨hU.fromSpec p, hpU⟩
  have hyp : hU.primeIdealOf y = p :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf y)
  have hw : Stacks.Divisors.IsWeaklyAssociatedPoint (SheafOfModules.unit X.ringCatSheaf) y := by
    apply (AlgebraicGeometry.isWeaklyAssociatedPrime_iff_isWeaklyAssociatedPoint
      (SheafOfModules.unit X.ringCatSheaf) U hU y y.2).mp
    show IsWeaklyAssociatedPrime Γ(X, U) Γ(X, U) (hU.primeIdealOf y).asIdeal
    rw [hyp]; exact ⟨z, hq⟩
  have hgen : (y : X) ∈ genericPoints X := hass hw
  have hmin := (genericPointsInOpenEquivMinimalPrimes hU ⟨⟨(y : X), hgen⟩, y.2⟩).2
  rw [genericPointsInOpenEquivMinimalPrimes_asIdeal hU ⟨⟨(y : X), hgen⟩, y.2⟩] at hmin
  refine ⟨q, ?_, ?_⟩
  · convert hmin using 1
    rw [show (⟨(y : X), y.2⟩ : U) = y from rfl, hyp]
  · exact hq.1.2 ((Submodule.mem_annihilator_span_singleton z x).mpr
      (by simpa [smul_eq_mul] using hxz))

/-- Only finitely many generic points of `X` lie in an affine open, when every quasi-compact
open of `X` has finitely many irreducible components. -/
lemma finite_genericPoints_mem_of_isCompact (X : Scheme.{u}) (U : X.Opens)
    (hUc : IsCompact (U : Set X))
    (hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite) :
    Finite {η : genericPoints X // η.1 ∈ U} :=
  have : Finite (genericPoints (U : Set X)) := (genericPoints.finite (hfinite U hUc)).to_subtype
  Finite.of_injective (Scheme.genericPointsInOpenEquiv X U)
    (Scheme.genericPointsInOpenEquiv X U).injective

/-- **The affine case of Stacks 0EMF.** On an affine open of a scheme whose weakly associated
points are generic points of irreducible components and whose quasi-compact opens have finitely
many irreducible components, the product of the local rings at the generic points lying in that
open is the total ring of fractions of the ring of sections. -/
lemma isLocalization_pi_stalk_genericPoints {X : Scheme.{u}}
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    {U : X.Opens} (hU : IsAffineOpen U) :
    letI : ∀ η : {η : genericPoints X // η.1 ∈ U},
        Algebra Γ(X, U) (X.presheaf.stalk η.1.1) := fun η =>
      X.presheaf.algebra_section_stalk ⟨η.1.1, η.2⟩
    IsLocalization (nonZeroDivisors Γ(X, U))
      (∀ η : {η : genericPoints X // η.1 ∈ U}, X.presheaf.stalk η.1.1) := by
  let _ : ∀ η : {η : genericPoints X // η.1 ∈ U},
      Algebra Γ(X, U) (X.presheaf.stalk η.1.1) := fun η =>
    X.presheaf.algebra_section_stalk ⟨η.1.1, η.2⟩
  have hfinι : Finite {η : genericPoints X // η.1 ∈ U} :=
    finite_genericPoints_mem_of_isCompact X U hU.isCompact hfinite
  let E := genericPointsInOpenEquivMinimalPrimes hU
  let q : {η : genericPoints X // η.1 ∈ U} → Ideal Γ(X, U) :=
    fun η => (hU.primeIdealOf ⟨η.1.1, η.2⟩).asIdeal
  have hqE : ∀ η, q η = ((E η : minimalPrimes Γ(X, U)) : Ideal Γ(X, U)) := fun η =>
    (genericPointsInOpenEquivMinimalPrimes_asIdeal hU η).symm
  have hmem : ∀ η, q η ∈ minimalPrimes Γ(X, U) := fun η => hqE η ▸ (E η).2
  have hinj : Function.Injective q := by
    intro a b hab
    apply E.injective
    apply Subtype.ext
    rw [← hqE, ← hqE, hab]
  have hsurj : ∀ p ∈ minimalPrimes Γ(X, U), ∃ η, q η = p := by
    intro p hp
    refine ⟨E.symm ⟨p, hp⟩, ?_⟩
    rw [hqE, E.apply_symm_apply]
  have hlocstalk : ∀ η : {η : genericPoints X // η.1 ∈ U},
      IsLocalization (q η).primeCompl (X.presheaf.stalk η.1.1) := fun η =>
    hU.isLocalization_stalk ⟨η.1.1, η.2⟩
  exact isLocalization_pi_of_bijOn_minimalPrimes
    (fun x hx => exists_minimalPrimes_mem_of_notMem_nonZeroDivisors hass hU hx)
    q hmem hinj hsurj _

end AlgebraicGeometry
