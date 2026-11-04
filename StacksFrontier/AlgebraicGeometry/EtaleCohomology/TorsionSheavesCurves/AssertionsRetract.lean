module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.PrimeKilledTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AlgClosedCase

/-!
# The eight assertions pass to retracts

If `A` is a retract of `G`, through `ι : A ⟶ G` and `p : G ⟶ A` with `ι ≫ p = 𝟙 A`, the
cohomology of `A` is a retract of that of `G`, compatibly with every restriction map. So the eight
assertions of Stacks Tag 03SC for `G` give them for `A`, once the constructibility and torsion
conditions on `A` pass to `G`. This is the step of Tag 03SD that replaces a finite locally
constant sheaf `𝒢` by `f_* f⁻¹ 𝒢`, of which it is a retract by the trace (Tag 03SE).

## Main results

* `Stacks.EtaleCohomology.TorsionCurveAssertions.of_retract`.
* `Stacks.EtaleCohomology.TorsionCurveAssertions.of_retract_of_nsmul`: for sheaves killed by a
  prime, with the torsion side conditions discharged.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

namespace TorsionCurveAssertions

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

omit [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})] in
/-- Postcomposition with `ι` is injective on `Ext` when `ι` has a retraction. -/
theorem injective_comp_mk₀_of_retract {C : Type*} [Category C] [Abelian C] [HasExt.{u + 1} C]
    {A G M : C} (ι : A ⟶ G) (p : G ⟶ A) (hip : ι ≫ p = 𝟙 A) (q : ℕ) :
    Function.Injective (fun x : Ext.{u + 1} M A q => x.comp (Ext.mk₀ ι) (add_zero q)) := by
  intro x y hxy
  have := congrArg (fun z : Ext.{u + 1} M G q => z.comp (Ext.mk₀ p) (add_zero q)) hxy
  simpa [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, hip] using this

/-- **The eight assertions pass to a retract**, given that the constructibility and torsion
conditions on the retract pass to the ambient sheaf. -/
theorem of_retract {A G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (ι : A ⟶ G)
    (p : G ⟶ A) (hip : ι ≫ p = 𝟙 A) (h : TorsionCurveAssertions f G)
    (hc : IsConstructibleSmallEtaleSheaf A → IsConstructibleSmallEtaleSheaf G)
    (hp : ∀ p : ℕ, Stacks.Torsion.IsPrimePowerTorsion X.smallEtaleTopology p A →
      Stacks.Torsion.IsPrimePowerTorsion X.smallEtaleTopology p G)
    (ht : Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology (ringExpChar k) A →
      Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology (ringExpChar k) G) :
    TorsionCurveAssertions f A := by
  have hinj := fun q => injective_comp_mk₀_of_retract ι p hip (M :=
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) q
  refine
    { vanishing := fun q hq => have := h.vanishing q hq; (hinj q).subsingleton
      vanishing_of_isAffine := fun hX q hq =>
        have := h.vanishing_of_isAffine hX q hq; (hinj q).subsingleton
      vanishing_of_isPrimePowerTorsion := fun p' hp' hp0 hF q hq =>
        have := h.vanishing_of_isPrimePowerTorsion p' hp' hp0 (hp p' hF) q hq
        (hinj q).subsingleton
      finite_of_isPrimeToCharacteristicTorsion := fun hcA htA q =>
        have := h.finite_of_isPrimeToCharacteristicTorsion (hc hcA) (ht htA) q
        Finite.of_injective _ (hinj q)
      finite_of_isProper := fun hf hcA q =>
        have := h.finite_of_isProper hf (hc hcA) q
        Finite.of_injective _ (hinj q)
      bijective_of_isPrimeToCharacteristicTorsion := fun htA k' _ _ _ _ q =>
        etaleCohomologyRestrictionMap_bijective_of_retract.{u, u + 1, u + 1} _ ι p hip
          (h.bijective_of_isPrimeToCharacteristicTorsion (ht htA) k' q)
      bijective_of_isProper := fun hf k' _ _ _ _ q =>
        etaleCohomologyRestrictionMap_bijective_of_retract.{u, u + 1, u + 1} _ ι p hip
          (h.bijective_of_isProper hf k' q)
      surjective_restriction := fun U _ y => by
        obtain ⟨x, hx⟩ := h.surjective_restriction U
          (y.comp (Ext.mk₀ ((etaleAbelianInverseImage.{u, u + 1} U.ι).map ι)) (add_zero 2))
        refine ⟨x.comp (Ext.mk₀ p) (add_zero 2), ?_⟩
        rw [etaleCohomologyRestrictionMap_comp_mk₀.{u, u + 1, u + 1}, hx,
          Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, ← CategoryTheory.Functor.map_comp,
          hip, CategoryTheory.Functor.map_id, Ext.comp_mk₀_id] }

/-- **The eight assertions pass to a retract**, for sheaves killed by a prime. -/
theorem of_retract_of_nsmul {ℓ : ℕ} (hℓ : ℓ.Prime)
    {A G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (ι : A ⟶ G)
    (p : G ⟶ A) (hip : ι ≫ p = 𝟙 A) (hA : ℓ • 𝟙 A = 0) (hG : ℓ • 𝟙 G = 0)
    (h : TorsionCurveAssertions f G)
    (hc : IsConstructibleSmallEtaleSheaf A → IsConstructibleSmallEtaleSheaf G) :
    TorsionCurveAssertions f A := by
  by_cases hz : IsZero A
  · exact of_isZero f hz
  exact of_retract f ι p hip h hc
    (fun p' => isPrimePowerTorsion_of_nsmul_id_eq_zero_of_not_isZero hℓ hA hG hz p')
    (isPrimeToCharacteristicTorsion_of_nsmul_id_eq_zero_of_not_isZero hℓ hA hG hz _)

end TorsionCurveAssertions

end Stacks.EtaleCohomology

end
