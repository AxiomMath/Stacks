module

public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.ResidueField
public import Mathlib.RingTheory.Polynomial.Ideal
public import StacksFrontier.RingTheory.UniversalHomeomorphism.Examples
public import StacksCore.Tactic.StacksAttribute

/-!
# A universal homeomorphism obtained from a prime-power relation

Let `A` be a ring and let `x, y ∈ A`. If `p` is prime and `p ^ p * x = y ^ p`, adjoining an
element `t` subject to the relations `t ^ p = x` and `p * t = y` induces a universal
homeomorphism on spectra. This is the second of the two standard examples of a universal
homeomorphism that is not an isomorphism.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.universalHomeomorphism_spec_quotient_of_pPower_mul` states that the map
  on spectra induced by this extension is a universal homeomorphism.

## Implementation notes

The algebra `A[t] / (t ^ p - x, p * t - y)` is represented as the quotient of `Polynomial A`
by the ideal spanned by the two displayed relations. Integrality and the kernel bound are
checked directly; the topological content is supplied by the ring-theoretic study of such
extensions, and the purely inseparable residue-field extensions are transported across the
comparison between scheme-theoretic and algebraic residue fields.

## References

* [Stacks Project, Tag 0EUI](https://stacks.math.columbia.edu/tag/0EUI)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

private abbrev pPowerAlgebra (A : Type u) [CommRing A] (x y : A) (p : ℕ) :=
  Polynomial A ⧸ Ideal.span
    {Polynomial.X ^ p - Polynomial.C x,
      Polynomial.C (p : A) * Polynomial.X - Polynomial.C y}

private theorem adjoin_quotient_polynomial_generator {A : Type u} [CommRing A]
    (I : Ideal (Polynomial A)) :
    Algebra.adjoin A ({Ideal.Quotient.mk I Polynomial.X} : Set (Polynomial A ⧸ I)) = ⊤ := by
  rw [eq_top_iff]
  rintro z -
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
      rw [map_add]
      exact add_mem hf hg
  | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
        ← Polynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]
      exact mul_mem (algebraMap_mem _ a) (pow_mem (Algebra.subset_adjoin (Set.mem_singleton _)) n)

/-- In an algebraically closed field, if `p ^ p * a = b ^ p` for a prime `p`, then there is `t`
with `t ^ p = a` and `p * t = b`. -/
private theorem _root_.IsAlgClosed.exists_pow_eq_and_natCast_mul_eq {L : Type*} [Field L]
    [IsAlgClosed L] {p : ℕ} (hp : p.Prime) {a b : L} (h : (p : L) ^ p * a = b ^ p) :
    ∃ t, t ^ p = a ∧ (p : L) * t = b := by
  by_cases hp0 : (p : L) = 0
  · obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq a hp.pos
    rw [hp0, zero_pow hp.ne_zero, zero_mul] at h
    exact ⟨t, ht, by rw [hp0, zero_mul, (pow_eq_zero_iff hp.ne_zero).mp h.symm]⟩
  · refine ⟨b / p, ?_, mul_div_cancel₀ _ hp0⟩
    rw [div_pow]
    apply (div_eq_iff (pow_ne_zero _ hp0)).2
    simpa [mul_comm] using h.symm

private theorem ker_algebraMap_pPowerAlgebra_le_nilradical
    {A : Type u} [CommRing A] (x y : A) (p : ℕ) (hp : p.Prime)
    (hxy : (p : A) ^ p * x = y ^ p) :
    RingHom.ker (algebraMap A (pPowerAlgebra A x y p)) ≤ nilradical A := by
  classical
  intro a ha
  rw [nilradical_eq_sInf, Ideal.mem_sInf]
  intro P hP
  have : P.IsPrime := hP
  let K := P.ResidueField
  let L := AlgebraicClosure K
  let g : A →+* L := (algebraMap K L).comp (algebraMap A K)
  have hxy' : (p : L) ^ p * g x = g y ^ p := by
    simpa only [map_mul, map_pow, map_natCast] using congrArg g hxy
  obtain ⟨t, ht₁, ht₂⟩ := IsAlgClosed.exists_pow_eq_and_natCast_mul_eq hp hxy'
  let φ : Polynomial A →+* L := Polynomial.eval₂RingHom g t
  have h₁ : φ (Polynomial.X ^ p - Polynomial.C x) = 0 := by simp [φ, ht₁]
  have h₂ : φ (Polynomial.C (p : A) * Polynomial.X - Polynomial.C y) = 0 := by simp [φ, ht₂]
  have hI : ∀ f ∈ (Ideal.span
      {Polynomial.X ^ p - Polynomial.C x,
        Polynomial.C (p : A) * Polynomial.X - Polynomial.C y} : Ideal (Polynomial A)),
      φ f = 0 := fun f hf => RingHom.mem_ker.mp <| (Ideal.span_le.mpr fun z hz => by
        rcases hz with rfl | rfl
        exacts [h₁, h₂]) hf
  let F : pPowerAlgebra A x y p →+* L := Ideal.Quotient.lift _ φ hI
  have hcomp : F.comp (algebraMap A (pPowerAlgebra A x y p)) = g := by
    ext b
    change (Ideal.Quotient.lift _ φ hI) (Ideal.Quotient.mk _ (Polynomial.C b)) = g b
    simp [φ, Polynomial.eval₂_C]
  have hga : g a = 0 := by
    rw [← hcomp]
    simpa using congrArg F (RingHom.mem_ker.mp ha)
  exact Ideal.algebraMap_residueField_eq_zero.mp
    ((algebraMap K L).injective (by simpa [g] using hga))

/-- The class of `X` generates `pPowerAlgebra A x y p` and satisfies the defining relations. -/
private theorem exists_generator_pPowerAlgebra {A : Type u} [CommRing A] (x y : A) (p : ℕ) :
    ∃ t : pPowerAlgebra A x y p, Algebra.adjoin A {t} = ⊤ ∧
      t ^ p = algebraMap A _ x ∧ (p : pPowerAlgebra A x y p) * t = algebraMap A _ y := by
  let I : Ideal (Polynomial A) := Ideal.span
    {Polynomial.X ^ p - Polynomial.C x,
      Polynomial.C (p : A) * Polynomial.X - Polynomial.C y}
  refine ⟨Ideal.Quotient.mk I Polynomial.X, adjoin_quotient_polynomial_generator I, ?_, ?_⟩
  · exact Ideal.Quotient.eq.mpr (Ideal.subset_span (by simp))
  · calc
      (p : pPowerAlgebra A x y p) * Ideal.Quotient.mk I Polynomial.X
          = Ideal.Quotient.mk I (Polynomial.C (p : A) * Polynomial.X) := by simp
      _ = Ideal.Quotient.mk I (Polynomial.C y) :=
        Ideal.Quotient.eq.mpr (Ideal.subset_span (by simp))
      _ = algebraMap A _ y := rfl

private theorem pPowerAlgebra_adjoin_powNsmulSet_eq_top
    {A : Type u} [CommRing A] (x y : A) (p : ℕ) :
    Algebra.adjoin A
      {z : pPowerAlgebra A x y p | ∃ n > 0,
        z ^ p ^ n ∈ (algebraMap A (pPowerAlgebra A x y p)).range ∧
        p ^ n • z ∈ (algebraMap A (pPowerAlgebra A x y p)).range} = ⊤ := by
  obtain ⟨t, ht, hpow, hmul⟩ := exists_generator_pPowerAlgebra x y p
  exact eq_top_mono (Algebra.adjoin_mono (Set.singleton_subset_iff.mpr
    ⟨1, Nat.one_pos, ⟨x, by simpa using hpow.symm⟩, ⟨y, by simpa [nsmul_eq_mul] using hmul.symm⟩⟩))
    ht

private theorem pPowerAlgebra_isIntegral
    {A : Type u} [CommRing A] (x y : A) (p : ℕ) (hp : p.Prime) :
    Algebra.IsIntegral A (pPowerAlgebra A x y p) := by
  obtain ⟨t, ht, hpow, -⟩ := exists_generator_pPowerAlgebra x y p
  have hroot : _root_.IsIntegral A t :=
    IsIntegral.of_pow hp.pos (hpow ▸ isIntegral_algebraMap)
  exact ⟨fun z => (mem_integralClosure_iff A _).mp
    (adjoin_le_integralClosure hroot (ht ▸ Algebra.mem_top))⟩

/-- The residue-field maps of `Spec.map f` are purely inseparable whenever the corresponding
maps of algebraic residue fields are. -/
private theorem specResidueFieldMap_isPurelyInseparable_of_idealResidueFieldMap
    {R S : CommRingCat.{u}} (f : R ⟶ S) (q : Spec S)
    (hpq : (Spec.map f q).asIdeal = q.asIdeal.comap f.hom)
    (hf : (Ideal.ResidueField.map _ _ f.hom hpq).IsPurelyInseparable) :
    ((Spec.map f).residueFieldMap q).hom.IsPurelyInseparable := by
  let ePiso := Scheme.Spec.residueFieldIso R (Spec.map f q)
  let eQiso := Scheme.Spec.residueFieldIso S q
  let eP := ePiso.commRingCatIsoToRingEquiv
  let eQ := eQiso.commRingCatIsoToRingEquiv
  have hP : eP.symm.toRingHom = ePiso.inv.hom := rfl
  have hQ : eQ.toRingHom = eQiso.hom.hom := rfl
  have hbridge : eQ.toRingHom.comp (((Spec.map f).residueFieldMap q).hom.comp
      eP.symm.toRingHom) = Ideal.ResidueField.map _ _ f.hom hpq := by
    rw [← RingHom.comp_assoc, hQ, hP]
    simpa only [CommRingCat.hom_comp] using specResidueFieldMap_bridge f q
  have hmap : ((Spec.map f).residueFieldMap q).hom =
      eQ.symm.toRingHom.comp ((Ideal.ResidueField.map _ _ f.hom hpq).comp eP.toRingHom) := by
    ext a
    apply eQ.injective
    have heval' : eQ.toRingHom (((Spec.map f).residueFieldMap q).hom a) =
        Ideal.ResidueField.map _ _ f.hom hpq (eP a) := by
      simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply] using
        congrArg (fun g => g (eP a)) hbridge
    change eQ.toRingHom (((Spec.map f).residueFieldMap q).hom a) =
      eQ.toRingHom (eQ.symm.toRingHom (Ideal.ResidueField.map _ _ f.hom hpq (eP.toRingHom a)))
    exact heval'.trans (eQ.apply_symm_apply _).symm
  rw [hmap]
  exact RingHom.isPurelyInseparable_congr eP eQ _ hf

open _root_.PrimeSpectrum in
/-- If `p` is prime and `p ^ p * x = y ^ p`, adjoining a common prime-power root as in
Stacks Project, Tag 0EUI, induces a universal homeomorphism on spectra. -/
@[stacks 0EUI "p_power_multiple"]
theorem universalHomeomorphism_spec_quotient_of_pPower_mul
    {A : Type u} [CommRing A] (x y : A) (p : ℕ) (hp : p.Prime)
    (hxy : (p : A) ^ p * x = y ^ p) :
    let B := Polynomial A ⧸ Ideal.span
      {Polynomial.X ^ p - Polynomial.C x,
        Polynomial.C (p : A) * Polynomial.X - Polynomial.C y}
    UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op) := by
  classical
  let B := pPowerAlgebra A x y p
  let f := Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op
  change UniversalHomeomorphism f
  have : Algebra.IsIntegral A B := pPowerAlgebra_isIntegral x y p hp
  have hdata :=
    @isHomeomorph_comap_and_isPurelyInseparable_and_baseChange_of_adjoin_pow_eq_top.{u,
      u, u, u} A B _ _ _ p hp (ker_algebraMap_pPowerAlgebra_le_nilradical x y p hp hxy)
      (pPowerAlgebra_adjoin_powNsmulSet_eq_top x y p)
  have hfinj : Function.Injective f := by
    intro z w hzw
    change PrimeSpectrum.comap (algebraMap A B) z =
      PrimeSpectrum.comap (algebraMap A B) w at hzw
    exact hdata.1.bijective.injective hzw
  have hres : ∀ z : Spec (CommRingCat.of B),
      (f.residueFieldMap z).hom.IsPurelyInseparable := by
    intro z
    have hpq : (Spec.map (CommRingCat.ofHom (algebraMap A B)) z).asIdeal =
        z.asIdeal.comap (algebraMap A B) := by
      simpa [Spec.map_apply] using PrimeSpectrum.comap_asIdeal (algebraMap A B) z
    refine specResidueFieldMap_isPurelyInseparable_of_idealResidueFieldMap _ z hpq ?_
    have : (Spec.map (CommRingCat.ofHom (algebraMap A B)) z).asIdeal.IsPrime :=
      (Spec.map (CommRingCat.ofHom (algebraMap A B)) z).isPrime
    have : (z.asIdeal : Ideal B).IsPrime := z.isPrime
    rcases hdata.2.1 _ _ hpq with hsurj | ⟨_, hpure⟩
    · exact RingHom.isPurelyInseparable_of_surjective _ hsurj
    · exact hpure
  exact (universalHomeomorphism_iff_integral_universallyInjective_surjective f).mpr
    ⟨IsIntegralHom.SpecMap_iff.mpr (algebraMap_isIntegral_iff.mpr inferInstance),
      ((tfae_universallyInjective f).out 1 3).mpr (by exact ⟨hfinj, hres⟩),
      ⟨hdata.1.bijective.2⟩⟩

end AlgebraicGeometry

end
