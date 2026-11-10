module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.ProjectionLowerShriekAcyclic
public import StacksFrontier.CategoryTheory.Localization.LeftDerivedByResolutions

/-!
# Derived lower shriek of a bounded above complex of free abelian sheaves

`Lπ_!` for the projection of a fibred category is constructed (Stacks 07AC, by the criterion of
Stacks 0794) from resolutions by `P`-cellular complexes, `P` the class of direct sums of the
`j_{x!} ℤ_x`. A bounded above complex with terms in `P` is itself `P`-cellular, so the comparison
`Lπ_!(K) ⟶ π_!(K)` is an isomorphism on it.

## Main results

* `CochainComplex.isPCellular_of_isStrictlyLE`: a bounded above complex with terms satisfying `P`
  is `P`-cellular.
* `FibredCategorySituation.isIso_derivedAbelianLowerShriekComparison_app`: the comparison
  `Lπ_!(K) ⟶ π_!(K)` is an isomorphism on a bounded above complex of direct sums of the
  `j_{x!} ℤ_x`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uD vD uC vC w

namespace CochainComplex

variable {A : Type*} [Category* A] [Abelian A]

omit [Abelian A] in
/-- The functor `ℕ ⥤ A` all of whose transition maps are `𝟙 K` sends every morphism to `𝟙 K`. -/
lemma ofSequence_id_map (K : A) {i j : ℕ} (h : i ⟶ j) :
    (Functor.ofSequence (fun _ : ℕ => 𝟙 K)).map h = 𝟙 K := by
  obtain ⟨⟨hij⟩⟩ := h
  change Functor.OfSequence.map (fun _ : ℕ => 𝟙 K) i j hij = 𝟙 K
  induction j with
  | zero =>
    obtain rfl : i = 0 := by lia
    exact Functor.OfSequence.map_id _ _
  | succ j ih =>
    rcases Nat.lt_or_ge j i with h | h
    · obtain rfl : i = j + 1 := by lia
      exact Functor.OfSequence.map_id _ _
    · rw [Functor.OfSequence.map_comp _ i j (j + 1) h (by lia), ih h,
        Functor.OfSequence.map_le_succ, Category.comp_id]

/-- **A bounded above complex with terms satisfying `P` is `P`-cellular.** -/
lemma isPCellular_of_isStrictlyLE (P : ObjectProperty A) (K : CochainComplex A ℤ)
    [K.IsStrictlyLE 0] (hK : ∀ n, P (K.X n)) :
    StacksDraft.UnboundedLeftDerivedFunctor.IsPCellular P K := by
  let c : Cocone (Functor.ofSequence (fun _ : ℕ => 𝟙 K)) :=
    { pt := K
      ι := { app := fun _ => 𝟙 K
             naturality := fun _ _ h => by
              rw [ofSequence_id_map]
              rfl } }
  have hc : IsColimit c :=
    { desc := fun s => s.ι.app 0
      fac := fun s j => by
        change 𝟙 K ≫ s.ι.app 0 = s.ι.app j
        have h := s.w (homOfLE (Nat.zero_le j))
        rw [ofSequence_id_map] at h
        exact (Category.id_comp _).trans (h.symm.trans (Category.id_comp _))
      uniq := fun s m hm => (Category.id_comp m).symm.trans (hm 0) }
  refine ⟨fun _ => K, fun _ => 𝟙 K, c, hc, Iso.refl _,
    fun n => CochainComplex.isStrictlyLE_of_le K 0 n (by lia), fun _ i => hK i,
    fun n i _ => ?_⟩
  change QuasiIsoAt (𝟙 K ≫ 𝟙 K) i
  rw [Category.comp_id]
  infer_instance

end CochainComplex

namespace Stacks.Sites.FibredCategory.FibredCategorySituation

variable (s : FibredCategorySituation.{uD, vD, uC, vC, w})

attribute [local instance] HasDerivedCategory.standard

/-- **`Lπ_!` is computed degreewise on a bounded above complex of direct sums of the
`j_{x!} ℤ_x`**: the comparison `Lπ_!(K) ⟶ π_!(K)` is an isomorphism at such a complex `K`. -/
lemma isIso_derivedAbelianLowerShriekComparison_app
    (K : CochainComplex (Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC}) ℤ) [K.IsStrictlyLE 0]
    (hK : ∀ n, Stacks.Cohomology.DerivedLowerShriek.IsSumOfExtensionByZeroUnitsAb.{max w uD vD uC}
      s.topology (K.X n)) :
    IsIso
      ((Stacks.Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekComparison.{max w uD vD uC,
        vC, uC, vD, uD} s.topology s.base.J s.p).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) := by
  have :=
    Stacks.Cohomology.DerivedLowerShriek.hasExactColimitsOfShape_nat_sheafAb.{max w uD vD uC vC}
      s.topology
  have :=
    Stacks.Cohomology.DerivedLowerShriek.hasExactColimitsOfShape_nat_sheafAb.{max w uD vD uC vC}
      s.base.J
  have : PreservesColimitsOfShape ℕ s.abelianLowerShriek :=
    (Adjunction.leftAdjoint_preservesColimits.{0, 0}
      s.abelianLowerShriekAdjunction).preservesColimitsOfShape
  have h := StacksDraft.UnboundedLeftDerivedFunctor.derives_cellularLocalizerMorphism
    s.abelianLowerShriek
    (Stacks.Cohomology.DerivedLowerShriek.IsSumOfExtensionByZeroUnitsAb.{max w uD vD uC} s.topology)
    (fun _ _ =>
      Stacks.Cohomology.DerivedLowerShriek.isSumOfExtensionByZeroUnitsAb_biprod.{max w uD vD uC}
        s.topology)
    (fun F =>
      Stacks.Cohomology.DerivedLowerShriek.exists_epi_isSumOfExtensionByZeroUnitsAb.{max w uD vD uC}
        s.topology F)
    s.abelianLowerShriekAcyclic
  have hres := StacksDraft.UnboundedLeftDerivedFunctor.hasLeftResolutions_cellularLocalizerMorphism
    (Stacks.Cohomology.DerivedLowerShriek.IsSumOfExtensionByZeroUnitsAb.{max w uD vD uC} s.topology)
    (fun _ _ =>
      Stacks.Cohomology.DerivedLowerShriek.isSumOfExtensionByZeroUnitsAb_biprod.{max w uD vD uC}
        s.topology)
    (fun F =>
      Stacks.Cohomology.DerivedLowerShriek.exists_epi_isSumOfExtensionByZeroUnitsAb.{max w uD vD uC}
        s.topology F)
  have :=
    StacksDraft.UnboundedLeftDerivedFunctor.isLeftDerivabilityStructure_cellularLocalizerMorphism
      _ hres
  exact CategoryTheory.LeftDerivedByResolutions.isIso_app_of_derives _ _ h DerivedCategory.Qh _ _
    ⟨(HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K,
      ⟨K, CochainComplex.isPCellular_of_isStrictlyLE _ K hK, ⟨Iso.refl _⟩⟩⟩

end Stacks.Sites.FibredCategory.FibredCategorySituation
