module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.TorsionVanishingBound
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.KummerProcyclicFieldVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.MaximalProEllVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.StrictlyHenselianMaximalProEllFixedField
public import StacksFrontier.Topology.Algebra.Group.ProPGroupMaximalExists
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# The fraction field of a strictly henselian discrete valuation ring has `cd_n ≤ 1`

Let `B` be a strictly henselian discrete valuation ring with fraction field `K`, and let `n` be
an integer invertible in `B`. Then `H^q_ét(Spec K, 𝓖) = 0` for every abelian sheaf `𝓖` on the
small étale site of `Spec K` killed by `n` and every `q ≥ 2`; that is, `cd_n(Spec K) ≤ 1`. This
is the base case in dimension one of Gabber's bound on the étale cohomological dimension
(Travaux de Gabber, Exposé XVIII-A, Theorem 1.1); no completeness or excellence of `B` and no
perfectness of its residue field is assumed, and the characteristic may be mixed.

The proof follows Serre (Cohomologie galoisienne, II §3.3): for a prime `ℓ ∣ n`, a maximal
pro-`ℓ` subgroup `H` of `Gal(Kˢᵉᵖ/K)` is `ℤ_ℓ(1)`. In terms of fields, the fixed field `L` of `H`
has the Kummer data of `AlgebraicGeometry.subsingleton_sheafH_spec_of_kummer`
(`AlgebraicGeometry.StrictlyHenselianKummer.fixedField_kummerData`), so
`H²_ét(Spec L, ℤ/ℓℤ) = 0`, and Stacks 0DV9
(`AlgebraicGeometry.tfae_subsingleton_sheafH_of_isMaximalProPSubgroup`) gives the vanishing in
degrees `≥ 2` for sheaves killed by `ℓ`. A sheaf killed by `n = ℓ m` is an extension of one
killed by `m` by one killed by `ℓ`, and the long exact sequence finishes the induction.

## Main results

* `AlgebraicGeometry.Scheme.subsingleton_sheafH_fractionRing_of_nsmul_id_eq_zero_of_prime`: the
  vanishing for sheaves killed by a prime `ℓ` invertible in `B`.
* `AlgebraicGeometry.Scheme.subsingleton_sheafH_fractionRing_of_nsmul_id_eq_zero`: the vanishing
  for sheaves killed by an integer invertible in `B`.
* `AlgebraicGeometry.Scheme.isTorsionVanishingBound_spec_fractionRing_of_isDiscreteValuationRing`:
  `cd_n(Spec K) ≤ 1`.

## References

* J.-P. Serre, *Cohomologie galoisienne*, II §3.3; *Corps locaux*, IV §2.
* L. Illusie, *Cohomological dimension: first results*, in Travaux de Gabber, Exposé XVIII-A,
  Astérisque 363–364 (2014).
* [Stacks Project, Tag 0DV9](https://stacks.math.columbia.edu/tag/0DV9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IntermediateField

universe u

namespace AlgebraicGeometry.Scheme

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

variable (B : Type u) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [StrictlyHenselianLocalRing B]

/-- **Vanishing above degree one for sheaves killed by a prime `ℓ` invertible in `B`**, on the
spectrum of the fraction field of a strictly henselian discrete valuation ring `B`. -/
theorem subsingleton_sheafH_fractionRing_of_nsmul_id_eq_zero_of_prime {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓB : IsUnit (ℓ : B)) (q : ℕ) (hq : 2 ≤ q)
    (G : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : ℓ • 𝟙 G = 0) : Subsingleton (Sheaf.H.{u + 1} G q) := by
  set K := FractionRing B
  set Ksep := SeparableClosure K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨H, hH⟩ := exists_isMaximalProPSubgroup ℓ Gal(Ksep/K)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B
  obtain ⟨hζ, hπ, hgen, hdeg⟩ :=
    StrictlyHenselianKummer.fixedField_kummerData K Ksep hℓ hℓB hH hϖ
  -- `H²_ét(Spec L, ℤ/ℓℤ) = 0`
  set L := fixedField H
  set Z : Sheaf (Spec (.of L)).smallEtaleTopology AddCommGrpCat.{u + 1} :=
    (constantSheaf (Spec (.of L)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)))
  have hZℓ : ℓ • 𝟙 Z = 0 := by
    have : (constantSheaf (Spec (.of L)).smallEtaleTopology AddCommGrpCat.{u + 1}).Additive :=
      Functor.additive_of_preserves_binary_products _
    refine nsmul_id_obj_eq_zero _ ?_
    ext x
    simp
  have hZtor : Stacks.Torsion.torsionSheafProperty (Spec (.of L)).smallEtaleTopology Z :=
    torsionSheafProperty_of_forall_nsmul_eq_zero hℓ.pos
      ((forall_nsmul_eq_zero_iff_nsmul_id_eq_zero Z).2 hZℓ)
  have h3 : Subsingleton (Sheaf.H.{u + 1} Z 2) :=
    subsingleton_sheafH_spec_of_kummer L hℓ hζ hπ hgen hdeg Z hZtor 2 le_rfl
  -- Stacks 0DV9
  have h2 := (forall_le_subsingleton_sheafH_iff_of_isMaximalProPSubgroup.{0} K Ksep hℓ 2 hH).2 h3
  exact h2 q hq G (Stacks.Torsion.isPrimePowerTorsion_of_nsmul_id_eq_zero _ hG)

/-- **Ext out of a fixed object vanishes on the middle term of a short exact sequence** when it
vanishes on the two outer terms. -/
theorem subsingleton_ext_X₂_of_shortExact_of_subsingleton {A : Type*} [Category A] [Abelian A]
    [HasExt.{u + 1} A] (T : A) {S : ShortComplex A} (hS : S.ShortExact) (q : ℕ)
    (h₁ : Subsingleton (Abelian.Ext.{u + 1} T S.X₁ q))
    (h₃ : Subsingleton (Abelian.Ext.{u + 1} T S.X₃ q)) :
    Subsingleton (Abelian.Ext.{u + 1} T S.X₂ q) := by
  refine subsingleton_of_forall_eq 0 fun e => ?_
  obtain ⟨y, hy⟩ := Abelian.Ext.covariant_sequence_exact₂ T hS e (h₃.elim _ _)
  rw [← hy, h₁.elim y 0, Abelian.Ext.zero_comp]

/-- **Vanishing above degree one for sheaves killed by an integer `n` invertible in `B`**, on the
spectrum of the fraction field of a strictly henselian discrete valuation ring `B`: by induction
on `n`, along the extension `0 → 𝓖[ℓ] → 𝓖 → 𝓖/𝓖[ℓ] → 0` for a prime `ℓ ∣ n`. -/
theorem subsingleton_sheafH_fractionRing_of_nsmul_id_eq_zero (n : ℕ) (hn : IsUnit (n : B))
    (q : ℕ) (hq : 2 ≤ q)
    (G : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : n • 𝟙 G = 0) : Subsingleton (Sheaf.H.{u + 1} G q) := by
  induction n using Nat.strong_induction_on generalizing G with
  | _ n ih =>
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · interval_cases n
    · exact absurd hn (by simp)
    · rw [one_smul] at hG
      refine subsingleton_of_forall_eq 0 fun e => ?_
      rw [← Abelian.Ext.comp_mk₀_id e, hG, Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero]
  · set ℓ := n.minFac
    have hℓ : ℓ.Prime := Nat.minFac_prime (by omega)
    obtain ⟨m, hm⟩ := Nat.minFac_dvd n
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; omega)
    have hmn : m < n := by
      rw [hm]
      exact lt_mul_left hm0 hℓ.one_lt
    have hnB : IsUnit ((ℓ : B) * (m : B)) := by rwa [← Nat.cast_mul, ← hm]
    have hℓB : IsUnit (ℓ : B) := isUnit_of_mul_isUnit_left hnB
    have hmB : IsUnit (m : B) := isUnit_of_mul_isUnit_right hnB
    set φ : G ⟶ G := ℓ • 𝟙 G with hφ
    let S : ShortComplex (Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology
        AddCommGrpCat.{u + 1}) :=
      ShortComplex.mk (kernel.ι φ) (cokernel.π (kernel.ι φ)) (cokernel.condition _)
    have hS : S.ShortExact := ShortComplex.ShortExact.mk'
      (ShortComplex.exact_of_g_is_cokernel S (cokernelIsCokernel _)) inferInstance
      inferInstance
    have key {k : ℕ} {X Y : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology
        AddCommGrpCat.{u + 1}} (f : X ⟶ Y) : (k • 𝟙 X) ≫ f = f ≫ (k • 𝟙 Y) := by simp
    have h₁ : ℓ • 𝟙 S.X₁ = 0 := by
      refine (cancel_mono (kernel.ι φ)).1 ?_
      rw [key, zero_comp]
      exact kernel.condition φ
    have h₃ : m • 𝟙 S.X₃ = 0 := by
      refine (cancel_epi (cokernel.π (kernel.ι φ))).1 ?_
      rw [← key, ← kernel.lift_ι φ (m • 𝟙 G)
        (by rw [Preadditive.nsmul_comp, Category.id_comp, hφ, smul_smul, mul_comm, ← hm, hG]),
        Category.assoc, cokernel.condition, comp_zero, comp_zero]
    exact subsingleton_ext_X₂_of_shortExact_of_subsingleton _ hS q
      (subsingleton_sheafH_fractionRing_of_nsmul_id_eq_zero_of_prime B hℓ hℓB q hq S.X₁ h₁)
      (ih m hmn hmB S.X₃ h₃)

/-- **The fraction field of a strictly henselian discrete valuation ring has `n`-cohomological
dimension at most one** for every `n` invertible in the ring (Serre, Cohomologie galoisienne,
II §3.3; the base case in dimension one of Gabber's bound, Travaux de Gabber XVIII-A, 1.1). -/
theorem isTorsionVanishingBound_spec_fractionRing_of_isDiscreteValuationRing {n : ℕ}
    (hn : IsUnit (n : B)) : IsTorsionVanishingBound (Spec (.of (FractionRing B))) n 1 := by
  intro G hG p hp
  have hp2 : 2 ≤ p := by
    have : ((1 : ℕ) : WithBot ℕ∞) < (p : WithBot ℕ∞) := hp
    have : (1 : ℕ) < p := by exact_mod_cast this
    omega
  exact subsingleton_sheafH_fractionRing_of_nsmul_id_eq_zero B n hn p hp2 G
    ((forall_nsmul_eq_zero_iff_nsmul_id_eq_zero G).1 hG)

end AlgebraicGeometry.Scheme

end
