module

public import Mathlib.Algebra.Ring.ULift
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Finiteness.NilpotentKer
public import Mathlib.RingTheory.RingHom.Finite
public import Mathlib.RingTheory.Unramified.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.Finiteness
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing

/-!
# Flat and formally unramified is not formally étale

The canonical map from a Noetherian local ring to its maximal-ideal-adic completion is flat, and
in prime characteristic `p` with finite residue-field imperfection degree it is also formally
unramified. It is nevertheless not formally étale in general, so flatness together with formal
unramifiedness does not imply formal étaleness.

Flatness is the completion theorem for a Noetherian ring at any ideal. Formal unramifiedness is
proved by showing that the module of relative Kähler differentials of the completion vanishes:
over a characteristic-`p` ring, finiteness of the ring over the image of Frobenius makes the
differentials a finite module, every differential of an element of the completion lies in every
power of the completed maximal ideal (approximate the element from the base ring and use linearity
of the universal derivation), and Krull's intersection theorem for a finite module over a local
ring kills it.

## Main results

* `Stacks.Examples.formallyUnramified_adicCompletion_maximalIdeal`: the completion of a Noetherian
  local ring of prime characteristic with finite residue-field imperfection degree is formally
  unramified over the ring.

Flatness is Mathlib's instance `AdicCompletion.flat_of_isNoetherian`, the completion theorem for an
arbitrary ideal of an arbitrary Noetherian ring. The whole of Lemma `0G66`, including the failure
of formal étaleness for a regular non-excellent ring, is
`Stacks.Examples.flat_formallyUnramified_adicCompletion_and_not_formallyEtale`.

## Implementation notes

The condition `[κ : κᵖ] < ∞` is expressed as finiteness of `κ` as a module over the field range of
Frobenius at its exponential characteristic, which equals `p`. The canonical completion map is the
algebra map into `AdicCompletion (IsLocalRing.maximalIdeal A) A`.

`AdicCompletion.flat_of_isNoetherian` is stronger than the local, positive-characteristic case the
source states, and in particular does not use the residue-field finiteness condition.

## References

* [Stacks Project, Tag 0G66](https://stacks.math.columbia.edu/tag/0G66)
-/

@[expose] public section

open IsLocalRing

universe u

namespace Stacks.Examples

/-- A separated algebra over an adically precomplete ring is finite if its closed fibre is
a nilpotent thickening of a finite residue field. -/
private theorem finite_of_complete_local
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing S] [IsNoetherianRing S] (I : Ideal R)
    [IsPrecomplete I R]
    [IsHausdorff I S]
    [Module.Finite R (ResidueField S)]
    (hle : I.map (algebraMap R S) ≤ maximalIdeal S)
    (hrad : maximalIdeal S ≤ (I.map (algebraMap R S)).radical) :
    Module.Finite R S := by
  let J := I.map (algebraMap R S)
  let f : (S ⧸ J) →ₐ[R] ResidueField S :=
    (Ideal.Quotient.factorₐ S hle).restrictScalars R
  have hf : Function.Surjective f := Ideal.Quotient.factor_surjective hle
  have hk : RingHom.ker f ≤ nilradical (S ⧸ J) := by
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hy : y ∈ maximalIdeal S := (Ideal.Quotient.eq_zero_iff_mem).mp hx
    obtain ⟨n, hn⟩ := hrad hy
    exact mem_nilradical.mpr ⟨n, by rwa [← map_pow, Ideal.Quotient.eq_zero_iff_mem]⟩
  have : Module.Finite R (S ⧸ J) :=
    Module.finite_of_surjective_of_ker_le_nilradical f hf hk
      (RingHom.ker f).fg_of_isNoetherianRing
  have hfin : Module.Finite R (S ⧸ I • (⊤ : Submodule R S)) := by
    rw [Ideal.smul_top_eq_map]
    exact Module.Finite.equiv (Submodule.Quotient.restrictScalarsEquiv R J).symm
  have : Module.Finite (R ⧸ I)
      (S ⧸ I • (⊤ : Submodule R S)) :=
    Module.Finite.of_restrictScalars_finite R _ _
  exact Module.Finite.of_iInf_pow_smul_top_eq_bot_of_finite_quotient_smul_top
    I (IsHausdorff.iInf_pow_smul inferInstance) inferInstance

/-- Frobenius on a complete Noetherian local ring is finite if it is finite on the residue
field. Its closed fibre has nilpotent maximal ideal, so finiteness lifts from the residue field. -/
private theorem finite_frobenius_of_finite_residueField
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsPrecomplete (maximalIdeal R) R]
    (p : ℕ) [ExpChar R p] [ExpChar (ResidueField R) p]
    (hκ : (frobenius (ResidueField R) p).Finite) :
    (frobenius R p).Finite := by
  let S := ULift.{0} R
  let e : R ≃+* S := ULift.ringEquiv.symm
  let f : R →+* S := e.toRingHom.comp (frobenius R p)
  let : Algebra R S := f.toAlgebra
  let : Module R S := Algebra.toModule
  have : IsLocalRing S := e.isLocalRing
  have : IsNoetherianRing S := isNoetherianRing_of_ringEquiv R e
  let eκ := ResidueField.mapEquiv e
  have hres : (algebraMap R (ResidueField S)).Finite := by
    have heq : algebraMap R (ResidueField S) =
        eκ.toRingHom.comp ((frobenius (ResidueField R) p).comp (residue R)) := by
      ext x
      show residue S (e (x ^ p)) = eκ ((residue R x) ^ p)
      simp [eκ, ResidueField.mapEquiv_apply, ResidueField.map_residue]
    rw [heq]
    exact eκ.finite.comp (hκ.comp (.of_surjective _ residue_surjective))
  have : Module.Finite R (ResidueField S) := RingHom.finite_algebraMap.mp hres
  have hle : (maximalIdeal R).map f ≤ maximalIdeal S := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    show e (x ^ p) ∈ maximalIdeal S
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal e]
    exact Ideal.mem_map_of_mem e (Ideal.pow_mem_of_mem _ hx p (expChar_pos R p))
  have hrad : maximalIdeal S ≤ ((maximalIdeal R).map f).radical := by
    intro x hx
    have hy : e.symm x ∈ maximalIdeal R := by
      rw [← IsLocalRing.map_ringEquiv_maximalIdeal e.symm]
      exact Ideal.mem_map_of_mem e.symm hx
    refine ⟨p, ?_⟩
    convert Ideal.mem_map_of_mem f hy using 1
    simp [f, frobenius_def]
  have : IsHausdorff (maximalIdeal R) S := IsHausdorff.of_map hle
  have : Module.Finite R S := finite_of_complete_local R S (maximalIdeal R) hle hrad
  have hf : f.Finite := RingHom.finite_algebraMap.mpr ‹Module.Finite R S›
  convert e.symm.finite.comp hf using 1
  ext x
  exact (e.symm_apply_apply _).symm

/-- Finiteness over the field of Frobenius powers is finiteness of the Frobenius map. -/
private theorem finite_frobenius_of_fieldRange
    (k : Type*) [Field k] (p : ℕ) [ExpChar k p]
    [Module.Finite (frobenius k p).fieldRange k] : (frobenius k p).Finite := by
  have h : (frobenius k p).range.subtype.Finite :=
    RingHom.finite_algebraMap.mpr (inferInstance : Module.Finite (frobenius k p).fieldRange k)
  exact h.comp (.of_surjective _ (frobenius k p).rangeRestrict_surjective)

/-- A finite Frobenius map makes the ring finite over its subring of Frobenius powers. -/
private theorem finite_frobenius_range
    (R : Type*) [CommRing R] (p : ℕ) [ExpChar R p]
    (h : (frobenius R p).Finite) : Module.Finite (frobenius R p).range R := by
  have h' : (frobenius R p).range.subtype.Finite :=
    RingHom.Finite.of_comp_finite (f := (frobenius R p).rangeRestrict) h
  exact RingHom.finite_algebraMap.mp h'

/-- Finiteness of Frobenius is invariant under ring isomorphisms. -/
private theorem finite_frobenius_of_equiv
    {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    (p : ℕ) [ExpChar R p] [ExpChar S p] (h : (frobenius R p).Finite) :
    (frobenius S p).Finite := by
  convert e.finite.comp (h.comp e.symm.finite) using 1
  ext x
  simp [frobenius_def]

/-- If Frobenius on a characteristic-`p` algebra has finite image module, its relative
Kähler differentials are finite: a finite module generating set for the algebra over the
Frobenius image differentiates to a finite generating set for the differentials. -/
private theorem finite_kaehlerDifferential_of_finite_frobenius_range
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (p : ℕ) [Fact p.Prime] [CharP S p]
    (hF : Module.Finite (frobenius S p).range S) :
    Module.Finite S Ω[S⁄R] := by
  classical
  let T := (frobenius S p).range
  let d : Derivation R S Ω[S⁄R] := KaehlerDifferential.D R S
  obtain ⟨s, hs⟩ := hF.fg_top
  let Q : Submodule S Ω[S⁄R] := Submodule.span S (d '' (s : Set S))
  have dpow (a : S) : d (a ^ p) = 0 := by
    rw [d.leibniz_pow, ← Nat.cast_smul_eq_nsmul S]
    simp
  have dsmul (c : T) (x : S) : d ((c : S) * x) = (c : S) • d x := by
    obtain ⟨a, ha⟩ := c.2
    rw [← ha, frobenius_def, d.leibniz]
    simp [dpow]
  have hDx (x : S) : d x ∈ Q := by
    have hx : x ∈ Submodule.span T (s : Set S) := by
      show x ∈ Submodule.span (frobenius S p).range (s : Set S)
      rw [hs]
      trivial
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (Set.mem_image_of_mem d hy)
    | zero => exact d.map_zero ▸ Q.zero_mem
    | add x y _ _ hx hy => simpa [d.map_add] using Q.add_mem hx hy
    | smul c x _ hx =>
        show d ((c : S) * x) ∈ Q
        rw [dsmul]
        exact Q.smul_mem (c : S) hx
  have hQ : Q = ⊤ := by
    rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation R S, Submodule.span_le]
    exact Set.range_subset_iff.mpr hDx
  exact ⟨hQ ▸ Submodule.fg_span (s.finite_toSet.image d)⟩

/-- Every element of the adic completion is represented modulo `I ^ n` by an element of the
original ring. This is the density bridge used to force relative differentials into every power
of the completed maximal ideal. -/
private theorem adicCompletion_approximation
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (n : ℕ) (x : AdicCompletion (IsLocalRing.maximalIdeal A) A) :
    ∃ a : A, x - algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) a ∈
      IsLocalRing.maximalIdeal A ^ n • (⊤ : Submodule A
        (AdicCompletion (IsLocalRing.maximalIdeal A) A)) := by
  let I := IsLocalRing.maximalIdeal A
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (x.val n)
  refine ⟨a, ?_⟩
  show x - algebraMap A (AdicCompletion I A) a ∈
    I ^ n • (⊤ : Submodule A (AdicCompletion I A))
  rw [AdicCompletion.pow_smul_top_eq_ker_eval I.fg_of_isNoetherianRing, LinearMap.mem_ker]
  have hv : AdicCompletion.eval I A n x =
      AdicCompletion.eval I A n (algebraMap A (AdicCompletion I A) a) := by
    rw [AdicCompletion.eval_apply, AdicCompletion.algebraMap_apply,
      AdicCompletion.eval_of]
    exact ha.symm
  rw [map_sub, sub_eq_zero.mpr hv]

/-- Relative differentials of completion elements lie in every power of the completed maximal
ideal: approximate from the base and use linearity of the universal derivation. -/
private theorem adicCompletion_differential_mem_maximalIdeal_pow
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (n : ℕ) (x : AdicCompletion (IsLocalRing.maximalIdeal A) A) :
    KaehlerDifferential.D A (AdicCompletion (IsLocalRing.maximalIdeal A) A) x ∈
      IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A) ^ n •
        (⊤ : Submodule (AdicCompletion (IsLocalRing.maximalIdeal A) A)
          Ω[AdicCompletion (IsLocalRing.maximalIdeal A) A ⁄ A]) := by
  let I := IsLocalRing.maximalIdeal A
  let S := AdicCompletion I A
  let d : Derivation A S Ω[S⁄A] := KaehlerDifferential.D A S
  have hmap : I.map (algebraMap A S) = IsLocalRing.maximalIdeal S := by
    simpa [I, S] using (AdicCompletion.maximalIdeal_eq_map (R := A)).symm
  obtain ⟨a, ha⟩ := adicCompletion_approximation A n x
  have hderiv {z : S} (hz : z ∈ I ^ n • (⊤ : Submodule A S)) :
      d z ∈ IsLocalRing.maximalIdeal S ^ n • (⊤ : Submodule S Ω[S⁄A]) := by
    refine Submodule.smul_induction_on' hz (fun r hr y _ => ?_) (fun y _ z _ hdy hdz => ?_)
    · have hrS : algebraMap A S r ∈ IsLocalRing.maximalIdeal S ^ n := by
        rw [← hmap, ← Ideal.map_pow]
        exact Ideal.mem_map_of_mem (algebraMap A S) hr
      rw [d.map_smul, ← IsScalarTower.algebraMap_smul (R := A) S r (d y)]
      exact Submodule.smul_mem_smul hrS trivial
    · simpa only [d.map_add] using add_mem hdy hdz
  rw [show d x = d (x - algebraMap A S a) by simp [map_sub]]
  exact hderiv ha

/-- The completion map is formally unramified once Frobenius on the completion has finite image
module. The preceding bridges give finite differentials, density, and Krull intersection. -/
private theorem formallyUnramified_adicCompletion_of_finite_frobenius
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (p : ℕ) [Fact p.Prime] [CharP A p]
    [CharP (AdicCompletion (IsLocalRing.maximalIdeal A) A) p]
    (hF : Module.Finite
      (frobenius (AdicCompletion (IsLocalRing.maximalIdeal A) A) p).range
      (AdicCompletion (IsLocalRing.maximalIdeal A) A)) :
    Algebra.FormallyUnramified A (AdicCompletion (IsLocalRing.maximalIdeal A) A) := by
  let S := AdicCompletion (IsLocalRing.maximalIdeal A) A
  have : Module.Finite S Ω[S⁄A] := finite_kaehlerDifferential_of_finite_frobenius_range A S p hF
  have hsep : (⨅ n : ℕ,
      IsLocalRing.maximalIdeal S ^ n • (⊤ : Submodule S Ω[S⁄A])) = ⊥ :=
    Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (maximalIdeal S)
      (inferInstance : (IsLocalRing.maximalIdeal S).IsMaximal).ne_top
  have hD (x : S) : KaehlerDifferential.D A S x = 0 := by
    have hx : KaehlerDifferential.D A S x ∈ ⨅ n : ℕ,
        IsLocalRing.maximalIdeal S ^ n • (⊤ : Submodule S Ω[S⁄A]) := by
      rw [Submodule.mem_iInf]
      exact fun n => adicCompletion_differential_mem_maximalIdeal_pow A n x
    rw [hsep] at hx
    simpa using hx
  refine ⟨(subsingleton_iff_forall_eq 0).mpr fun x => ?_⟩
  have hx : x ∈ Submodule.span S (Set.range (KaehlerDifferential.D A S)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  have hle : Submodule.span S (Set.range (KaehlerDifferential.D A S)) ≤ ⊥ :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr fun y => by simp [hD y])
  simpa using hle hx

/-- The completion of a Noetherian local ring of prime characteristic and finite residue-field
imperfection degree is formally unramified over the ring. -/
public theorem formallyUnramified_adicCompletion_maximalIdeal
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (p : ℕ) [Fact p.Prime] [CharP A p]
    [Module.Finite (frobenius (ResidueField A) (ringExpChar (ResidueField A))).fieldRange
      (ResidueField A)] :
    Algebra.FormallyUnramified A (AdicCompletion (maximalIdeal A) A) := by
  let B := AdicCompletion (maximalIdeal A) A
  have : CharP B p := charP_of_injective_algebraMap
    (AdicCompletion.of_injective (maximalIdeal A) A) p
  have : CharP (ResidueField A) p := (CharP.charP_iff_prime_eq_zero Fact.out).mpr
    (by rw [← map_natCast (residue A), CharP.cast_eq_zero, map_zero])
  have : CharP (ResidueField B) p := (CharP.charP_iff_prime_eq_zero Fact.out).mpr
    (by rw [← map_natCast (residue B), CharP.cast_eq_zero, map_zero])
  have hκ : (frobenius (ResidueField A) p).Finite := by
    have heq : frobenius (ResidueField A) (ringExpChar (ResidueField A)) =
        frobenius (ResidueField A) p := by
      ext x
      simp only [frobenius_def, ringExpChar.eq (ResidueField A) p]
    rw [← heq]
    exact finite_frobenius_of_fieldRange (ResidueField A) (ringExpChar (ResidueField A))
  let e : ResidueField A ≃+* ResidueField B := RingEquiv.ofBijective
    (ResidueField.map (algebraMap A B)) (AdicCompletion.residueField_map_bijective A)
  exact formallyUnramified_adicCompletion_of_finite_frobenius A p <| finite_frobenius_range B p <|
    finite_frobenius_of_finite_residueField B p (finite_frobenius_of_equiv e p hκ)

end Stacks.Examples

end
