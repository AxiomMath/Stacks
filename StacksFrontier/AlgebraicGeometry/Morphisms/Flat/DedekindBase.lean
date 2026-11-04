module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Flat.TorsionFree
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.IntegralSchemes
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Affine
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flatness over a Dedekind domain

Let `A` be a Dedekind domain. A morphism `q : Z ⟶ Spec A` from a reduced scheme all of whose
irreducible components dominate `Spec A` is flat.

## Main results

* `AlgebraicGeometry.flat_of_genericPoint_map_eq` — a morphism from an integral scheme to the
  spectrum of a Dedekind domain carrying the generic point to the generic point is flat.
* `AlgebraicGeometry.flat_of_forall_genericPoint_map_eq` — a morphism from a reduced scheme to
  the spectrum of a Dedekind domain carrying the generic point of every irreducible component to
  the generic point is flat.

## Implementation notes

The hypothesis that every irreducible component of `Z` dominates `Spec A` is expressed as: every
point whose closure is an irreducible component is carried to the generic point of `Spec A`. No
Noetherian hypothesis on `Z` is needed.

## References

* [Stacks Project, Tag 0AUW](https://stacks.math.columbia.edu/tag/0AUW)
* [Stacks Project, Tag 0CC1](https://stacks.math.columbia.edu/tag/0CC1)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- On an integral scheme the comparison map from the local ring at a point to the local ring at
a generalization of it is injective. -/
@[ega "I 8.2.1" "more general"]
theorem stalkSpecializes_injective_of_isIntegral {X : Scheme.{u}} [IsIntegral X] {x y : X}
    (h : x ⤳ y) : Function.Injective (X.presheaf.stalkSpecializes h) := by
  rw [show ⇑(X.presheaf.stalkSpecializes h) = ⇑(X.presheaf.stalkSpecializes h).hom from rfl,
    injective_iff_map_eq_zero]
  intro s hs
  obtain ⟨U, hU, a, rfl⟩ := X.presheaf.exists_germ_eq s
  rw [← ConcreteCategory.comp_apply, X.presheaf.germ_stalkSpecializes hU h] at hs
  simp [germ_injective_of_isIntegral X x _ (hs.trans (map_zero _).symm)]

/-- On a reduced scheme a nonzero element of the local ring at a point stays nonzero in the local
ring at the generic point of a suitable irreducible component through that point. -/
theorem exists_genericPoint_stalkSpecializes_ne_zero {Z : Scheme.{u}} [IsReduced Z] (z : Z)
    {b : Z.presheaf.stalk z} (hb : b ≠ 0) :
    ∃ (η : Z) (_ : closure {η} ∈ irreducibleComponents Z) (h : η ⤳ z),
      (Z.presheaf.stalkSpecializes h) b ≠ 0 := by
  obtain ⟨-, ⟨U, hU, rfl⟩, hzU, -⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  let _ : Algebra Γ(Z, U) (Z.presheaf.stalk z) := Z.presheaf.algebra_section_stalk ⟨z, hzU⟩
  have hlocz : IsLocalization.AtPrime (Z.presheaf.stalk z) (hU.primeIdealOf ⟨z, hzU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨z, hzU⟩
  obtain ⟨Q, hQ, hbQ⟩ : ∃ Q : Ideal (Z.presheaf.stalk z), Q.IsPrime ∧ b ∉ Q := by
    by_contra hcon
    push Not at hcon
    exact hb (IsNilpotent.eq_zero (mem_nilradical.mp
      (by rw [nilradical_eq_sInf, Ideal.mem_sInf]; exact fun I hI => hcon I hI)))
  obtain ⟨⟨s, t⟩, hst⟩ :=
    IsLocalization.surj (hU.primeIdealOf ⟨z, hzU⟩).asIdeal.primeCompl b
  have htu : IsUnit (algebraMap Γ(Z, U) (Z.presheaf.stalk z) (t : Γ(Z, U))) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff _ _ _).mpr t.2
  have hsQ : s ∉ Ideal.under Γ(Z, U) Q := fun hs =>
    (hQ.mem_or_mem (show b * algebraMap Γ(Z, U) (Z.presheaf.stalk z) (t : Γ(Z, U)) ∈ Q from
      hst ▸ hs)).elim hbQ fun h => hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ h htu)
  have hple : Ideal.under Γ(Z, U) Q ≤ (hU.primeIdealOf ⟨z, hzU⟩).asIdeal := by
    rw [← IsLocalization.AtPrime.under_maximalIdeal (Z.presheaf.stalk z)
      (hU.primeIdealOf ⟨z, hzU⟩).asIdeal]
    exact Ideal.comap_mono (IsLocalRing.le_maximalIdeal hQ.ne_top)
  obtain ⟨p, hpmin, hple'⟩ := Ideal.exists_minimalPrimes_le
    (I := (⊥ : Ideal Γ(Z, U))) (J := Ideal.under Γ(Z, U) Q) bot_le
  obtain ⟨η, hηp⟩ : ∃ η : {η : genericPoints Z // η.1 ∈ U},
      (hU.primeIdealOf ⟨η.1.1, η.2⟩).asIdeal = p :=
    ⟨(genericPointsInOpenEquivMinimalPrimes hU).symm ⟨p, hpmin⟩, by
      rw [← genericPointsInOpenEquivMinimalPrimes_asIdeal hU, Equiv.apply_symm_apply]⟩
  have hxU : (η.1.1 : Z) ∈ U := η.2
  let _ : Algebra Γ(Z, U) (Z.presheaf.stalk η.1.1) :=
    Z.presheaf.algebra_section_stalk ⟨η.1.1, hxU⟩
  have hlocx : IsLocalization.AtPrime (Z.presheaf.stalk η.1.1)
      (hU.primeIdealOf ⟨η.1.1, hxU⟩).asIdeal := hU.isLocalization_stalk ⟨η.1.1, hxU⟩
  have hsu : IsUnit (algebraMap Γ(Z, U) (Z.presheaf.stalk η.1.1) s) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff _ _ _).mpr fun h => hsQ (hple' (hηp ▸ h))
  have hle : (hU.primeIdealOf ⟨η.1.1, hxU⟩).asIdeal ≤ (hU.primeIdealOf ⟨z, hzU⟩).asIdeal :=
    hηp ▸ hple'.trans hple
  have hspec : (η.1.1 : Z) ⤳ z := by
    have h := ((PrimeSpectrum.le_iff_specializes (hU.primeIdealOf ⟨η.1.1, hxU⟩)
      (hU.primeIdealOf ⟨z, hzU⟩)).mp hle).map hU.fromSpec.continuous
    rwa [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf] at h
  refine ⟨η.1.1, η.1.2, hspec, fun h0 => hsu.ne_zero ?_⟩
  have hcomm : (Z.presheaf.stalkSpecializes hspec)
      (algebraMap Γ(Z, U) (Z.presheaf.stalk z) s) =
      algebraMap Γ(Z, U) (Z.presheaf.stalk η.1.1) s := by
    show (Z.presheaf.germ U z hzU ≫ Z.presheaf.stalkSpecializes hspec) s = _
    rw [Z.presheaf.germ_stalkSpecializes hzU hspec]
    rfl
  rw [← hcomm, ← hst, map_mul, h0, zero_mul]

variable {A : Type u} [CommRing A] [IsDedekindDomain A] {Z : Scheme.{u}}

/-- A morphism to the spectrum of a Dedekind domain is flat as soon as, at every point, the
product of the image of an element of the local ring of the base with an element of the local
ring upstairs vanishes only when one of the two factors does. -/
private theorem flat_of_forall_stalkMap_mul_eq_zero (q : Z ⟶ Spec (.of A))
    (h : ∀ (z : Z) (a : (Spec (.of A)).presheaf.stalk (q z)) (b : Z.presheaf.stalk z),
      (q.stalkMap z) a * b = 0 → a = 0 ∨ b = 0) : Flat q := by
  rw [Flat.iff_flat_stalkMap]
  intro z
  have hp : (q z).asIdeal.IsPrime := (q z).isPrime
  let L := Localization.AtPrime (q z).asIdeal
  let e : (Spec (.of A)).presheaf.stalk (q z) ≃+* L :=
    (Spec.stalkIso (.of A) (q z)).commRingCatIsoToRingEquiv
  have : IsDedekindDomain L :=
    IsLocalization.isDedekindDomain A (q z).asIdeal.primeCompl_le_nonZeroDivisors L
  let φ : (Spec (.of A)).presheaf.stalk (q z) →+* Z.presheaf.stalk z := (q.stalkMap z).hom
  let ψ : L →+* Z.presheaf.stalk z := φ.comp e.symm.toRingHom
  let _ : Algebra L (Z.presheaf.stalk z) := ψ.toAlgebra
  have : Module.IsTorsionFree L (Z.presheaf.stalk z) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r m hrm => ?_
    have hrm' : φ (e.symm r) * m = 0 := by
      simpa [Algebra.smul_def, RingHom.algebraMap_toAlgebra, ψ] using hrm
    exact (h z (e.symm r) m hrm').imp_left fun hr => by simpa using congrArg e hr
  have hψ : ψ.Flat := (inferInstance : Module.Flat L (Z.presheaf.stalk z))
  show φ.Flat
  rw [show φ = ψ.comp e.toRingHom by ext a; simp [ψ]]
  exact RingHom.Flat.comp (RingHom.Flat.of_bijective e.bijective) hψ

/-- A morphism from an integral scheme to the spectrum of a Dedekind domain which carries the
generic point to the generic point is flat. -/
theorem flat_of_genericPoint_map_eq (q : Z ⟶ Spec (.of A)) [IsIntegral Z]
    (hη : q (genericPoint Z) = genericPoint (Spec (.of A))) : Flat q := by
  have hinj : ∀ z : Z, Function.Injective (q.stalkMap z) :=
    ((tfae_isDominant_of_isIntegral q).out 1 6).mp
      (((tfae_isDominant_of_isIntegral q).out 2 1).mp hη)
  exact flat_of_forall_stalkMap_mul_eq_zero q fun z a b hab =>
    (mul_eq_zero.mp hab).imp_left (map_eq_zero_iff _ (hinj z)).mp

/-- A morphism from a reduced scheme to the spectrum of a Dedekind domain which carries the
generic point of every irreducible component to the generic point is flat. -/
theorem flat_of_forall_genericPoint_map_eq (q : Z ⟶ Spec (.of A)) [IsReduced Z]
    (hgen : ∀ η : Z, closure {η} ∈ irreducibleComponents Z →
      q η = genericPoint (Spec (.of A))) : Flat q := by
  refine flat_of_forall_stalkMap_mul_eq_zero q fun z a b hab =>
    or_iff_not_imp_right.mpr fun hb => ?_
  obtain ⟨η, hη, hspec, hσb⟩ := exists_genericPoint_stalkSpecializes_ne_zero z hb
  by_contra ha
  have h0 : (q.stalkMap η) ((Spec (.of A)).presheaf.stalkSpecializes
      (q.base.hom.map_specializes hspec) a) * (Z.presheaf.stalkSpecializes hspec) b = 0 := by
    rw [Scheme.Hom.stalkSpecializes_stalkMap_apply q η z hspec a, ← map_mul, hab, map_zero]
  have hfield : IsField ((Spec (.of A)).presheaf.stalk (q η)) :=
    isField_stalk_of_closure_mem_irreducibleComponents (Spec (.of A)) (q η) (by
      rw [hgen η hη, irreducibleComponents_eq_singleton, Set.mem_singleton_iff]
      exact (genericPoint_spec (Spec (.of A))).def)
  obtain ⟨c, hc⟩ := hfield.mul_inv_cancel
    (show (Spec (.of A)).presheaf.stalkSpecializes (q.base.hom.map_specializes hspec) a ≠ 0 from
      fun h => ha ((map_eq_zero_iff _ (stalkSpecializes_injective_of_isIntegral _)).mp h))
  exact hσb (((isUnit_iff_exists_inv.mpr ⟨c, hc⟩).map
    (q.stalkMap η).hom).mul_right_eq_zero.mp h0)

end AlgebraicGeometry

end
