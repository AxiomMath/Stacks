module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.AffineCurve
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.TorsionVanishingBound

/-!
# Affine curves: the vanishing bound for coefficients killed by an integer

Let `K` be a field, `X` an affine scheme of finite type over `K` of dimension at most one, and
`n` a positive integer. If the étale cohomology of `Spec K` with coefficients killed by `n`
vanishes above degree `c`, then that of `X` vanishes above degree `1 + c`. This is Stacks 0F0S
(`AlgebraicGeometry.Scheme.etaleCohomologicalDimension_le_one_add`) with the class of torsion
sheaves replaced by the class of sheaves killed by `n`, the form used in the proof of Stacks 0DC6.

## Main results

* `Scheme.isZero_rightDerived_smallEtaleDirectImageAb_of_topologicalKrullDim_le_one`:
  for `g : X ⟶ Spec K` as above and a torsion sheaf `𝓕` on `X_ét`, `R^qg_*𝓕 = 0` for `q ≥ 2`.
* `Scheme.isTorsionVanishingBound_one_add_of_topologicalKrullDim_le_one`:
  the bound `1 + c` for `X` from the bound `c` for `Spec K`, with coefficients killed by `n`.

## Implementation notes

The proof is that of `AlgebraicGeometry.Scheme.etaleCohomologicalDimension_le_one_add`. The
vanishing of the higher direct images in degrees `≥ 2` only needs the sheaf to be torsion, and a
sheaf killed by `n > 0` is torsion. In degrees `q ≤ 1` the sheaf `R^qg_*𝓕` is killed by `n` because
`R^qg_*` is additive and `𝓕` being killed by `n` is the equation `n • 𝟙 𝓕 = 0`.

## References

* [Stacks Project, Tag 0F0S](https://stacks.math.columbia.edu/tag/0F0S)
* [Stacks Project, Tag 0DC6](https://stacks.math.columbia.edu/tag/0DC6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry.Scheme

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology
  Stacks.EtaleCohomology.smallEtaleGlobalSectionsAb_additive

/-- **The higher direct images of a torsion sheaf from an affine curve over a field vanish in
degrees at least two.** Let `K` be a field, `X` an affine scheme of finite type over `K` of
dimension at most one, and `𝓕` a torsion sheaf on `X_ét`. Then `R^qg_*𝓕 = 0` for `q ≥ 2`.

The stalk of `R^qg_*𝓕` at a geometric point is the cohomology of the base change of `X` to the
strict henselization (Stacks 03Q9), which is a separable closure `Ω` of `K`, and `X_Ω` is an
affine curve over a separably closed field, of cohomological dimension at most one by
`etaleCohomologicalDimension_le_one_of_isSepClosed`. -/
theorem isZero_rightDerived_smallEtaleDirectImageAb_of_topologicalKrullDim_le_one
    {K : Type u} [Field K] {X : Scheme.{u}} [IsAffine X] (g : X ⟶ Spec (.of K))
    [LocallyOfFiniteType g] (hX : topologicalKrullDim X ≤ 1)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) {q : ℕ} (hq : 2 ≤ q) :
    IsZero (((Stacks.EtaleCohomology.smallEtaleDirectImageAb.{u + 1} g).rightDerived q).obj F) := by
  let B := BigEtaleSite.containing (Spec (.of K))
  have hS : B.Contains (Spec (.of K)) := BigEtaleSite.contains_containing _
  let G := ((Stacks.EtaleCohomology.smallEtaleDirectImageAb.{u + 1} g).rightDerived q).obj F
  have hiso : IsIso (0 : G ⟶ G) := by
    refine (Stacks.EtaleCohomology.isIso_iff_forall_isIso_smallEtaleStalkAb _).2 fun s => ?_
    have hsrc : IsZero ((Stacks.EtaleCohomology.smallEtaleStalkAb s.hom).obj G) := by
      refine (isZero_stalk_rightDerived_iff_subsingleton_sheafH B hS g s F q).2 ?_
      have hfield := isField_etaleLocalRing_of_isField_stalk B (Spec (.of K)) hS s (by
        obtain ⟨x, hx⟩ : ∃ x, x = s.hom (IsLocalRing.closedPoint s.residueField) := ⟨_, rfl⟩
        rw [← hx]
        obtain rfl : x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
        exact (stalkClosedPointIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
          (Field.toIsField K))
      let := hfield.toField
      have := isSepClosed_etaleLocalRing_of_isField B (Spec (.of K)) hS s hfield
      have := isIntegralHom_strictHenselizationToBase_of_field B hS s
      have hdim : topologicalKrullDim (strictHenselizationBaseChange B hS g s) ≤ 1 :=
        (topologicalKrullDim_le_of_isIntegralHom
          (strictHenselizationBaseChangeToSource B hS g s)).trans hX
      have hcd := etaleCohomologicalDimension_le_one_of_isSepClosed
        (Ω := ↥(etaleLocalRing B (Spec (.of K)) hS s))
        (strictHenselizationBaseChangeToStrictHenselization B hS g s) hdim
      exact isEtaleCohomologyBound_etaleCohomologicalDimension _ _
        (Stacks.Torsion.torsionSheafProperty_of_iso _
          ((Stacks.EtaleCohomology.smallEtalePullbackAbIsoEtaleAbelianInverseImage
            (strictHenselizationBaseChangeToSource B hS g s)).app F).symm
          (Stacks.EtaleCohomology.torsionSheafProperty_etaleAbelianInverseImage.{u, 0} _ F hF)) q
        (lt_of_le_of_lt hcd (by exact_mod_cast hq))
    exact ⟨⟨0, hsrc.eq_of_src _ _, hsrc.eq_of_src _ _⟩⟩
  refine (IsZero.iff_id_eq_zero G).2 ?_
  rw [← IsIso.hom_inv_id (0 : G ⟶ G), zero_comp]

/-- The degree bookkeeping of the Leray argument: if `p > 1 + c` and `q ≤ 1`, then `p - q > c`
(also when `c = ⊥`). -/
theorem lt_natCast_sub_of_one_add_lt {c : WithBot ℕ∞} {p q : ℕ} (hq : q ≤ 1)
    (hp : 1 + c < (p : WithBot ℕ∞)) : c < ((p - q : ℕ) : WithBot ℕ∞) := by
  induction c using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe e =>
    rw [← WithBot.coe_one, ← WithBot.coe_add, ← WithBot.coe_natCast, WithBot.coe_lt_coe] at hp
    rw [← WithBot.coe_natCast, WithBot.coe_lt_coe]
    induction e using ENat.recTopCoe with
    | top => exact absurd hp (by simp)
    | coe m =>
      have h : 1 + m < p := by exact_mod_cast hp
      exact_mod_cast (by omega : m < p - q)

/-- **Stacks 0F0S with coefficients killed by `n`.** Let `K` be a field, `X` an affine scheme of
finite type over `K` of dimension at most one, and `n` a positive integer. If the étale cohomology
of `Spec K` with coefficients killed by `n` vanishes above degree `c`, then that of `X` vanishes
above degree `1 + c`.

Let `𝓕` be a sheaf on `X_ét` killed by `n` and `p > 1 + c`. By the Leray spectral sequence for
`g : X ⟶ Spec K` it suffices that `H^{p-q}(Spec K, R^qg_*𝓕) = 0` for `q ≤ p`. For `q ≥ 2` the
sheaf `R^qg_*𝓕` vanishes
(`isZero_rightDerived_smallEtaleDirectImageAb_of_topologicalKrullDim_le_one`), `𝓕` being torsion.
For `q ≤ 1` the sheaf `R^qg_*𝓕` is killed by `n`, as `R^qg_*` is additive, and `p - q > c`. -/
theorem isTorsionVanishingBound_one_add_of_topologicalKrullDim_le_one
    {K : Type u} [Field K] {X : Scheme.{u}} [IsAffine X] (g : X ⟶ Spec (.of K))
    [LocallyOfFiniteType g] (hX : topologicalKrullDim X ≤ 1) {n : ℕ} (hn : 0 < n)
    {c : WithBot ℕ∞} (hK : IsTorsionVanishingBound (Spec (.of K)) n c) :
    IsTorsionVanishingBound X n (1 + c) := by
  intro F hF p hp
  refine LerayVanishing.subsingleton_sheafH_of_forall_subsingleton_sheafH_rightDerived
    g F p fun q hq => ?_
  rcases lt_or_ge q 2 with hq2 | hq2
  · have hR : n • 𝟙 (((Stacks.EtaleCohomology.smallEtaleDirectImageAb.{u + 1} g).rightDerived
        q).obj F) = 0 :=
      nsmul_id_obj_eq_zero _ ((forall_nsmul_eq_zero_iff_nsmul_id_eq_zero F).1 hF)
    exact hK _ ((forall_nsmul_eq_zero_iff_nsmul_id_eq_zero _).2 hR) (p - q)
      (lt_natCast_sub_of_one_add_lt (by omega) hp)
  · exact Sheaf.subsingleton_H_of_isZero
      (isZero_rightDerived_smallEtaleDirectImageAb_of_topologicalKrullDim_le_one g hX F
        (torsionSheafProperty_of_forall_nsmul_eq_zero hn hF) hq2) _

end AlgebraicGeometry.Scheme

end
