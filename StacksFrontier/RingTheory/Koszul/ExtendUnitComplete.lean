module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticConstantUnit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticMilnorGlobalSections
public import StacksFrontier.RingTheory.Koszul.ExtendSectionsCoefficientTower
public import StacksFrontier.Homology.DerivedComplete.AdicDerivedCompletionKoszul
public import StacksFrontier.Homology.DerivedComplete.PrincipalRecurrence

/-!
# The unit of `F' ⊣ RΓ` is invertible on derived complete complexes

Let `R` be a commutative ring, `f₁, …, f_r ∈ R` and `ℬ` the sheaf `n ↦ K_{n+1}` of Koszul
algebras on `f₁^{n+1}, …, f_r^{n+1}` on the chaotic site of the natural numbers. Extension of
scalars `F' : D(R) ⥤ D(ℬ, d)`, `K ↦ K ⊗_R ℬ`, is left adjoint to the derived global sections
`RΓ`. This file shows that the unit `K ⟶ RΓ(K ⊗_R ℬ)` is the derived completion of `K` along
`I = (f₁, …, f_r)`: on the class of a complex `K` it is the class of the strict unit
`K ⟶ Γ(K ⊗_R ℬ)` followed by the augmentation of `Γ(K ⊗_R ℬ)` into the Milnor model of the tower
of sections `n ↦ K ⊗_R K_{n+1}`, and that tower is the coefficient Koszul tower of Tag 091Z, so
the composite is the strict coefficient completion `K ⟶ K^∧`. In particular the unit is invertible
at every derived complete object. This is the step `K ≅ Rf_* Lf^* K` for `K ∈ D_comp(R, I)` of
the proof of Proposition 0GZK.

## Main results

* `Koszul.extendUnit_milnorAug`: the strict unit followed by the Milnor augmentation is the
  strict coefficient completion, up to the identification of towers.
* `Koszul.isIso_derivedExtendAdjunction_unit_app`: **the unit of `F' ⊣ RΓ` is invertible at
  every derived complete object of `D(R)`.**

## References

* [Stacks Project, Proposition 24.35.4 (Tag 0GZK)](https://stacks.math.columbia.edu/tag/0GZK)
* [Stacks Project, Lemma 15.93.17 (Tag 091Z)](https://stacks.math.columbia.edu/tag/091Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.PresheafOfModules Stacks.ChaoticSite
  CountableMilnorTower KoszulCoefficientTower KoszulCompletion

universe u

namespace Koszul

open _root_.SheafOfModules _root_.SheafOfModules.DifferentialGradedModule

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.SheafOfModules.botWEqualsLocallyBijective

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)

/-- The augmentation `K ⟶ (K ⊗_R ℬ)(n)` of the tower of sections by the strict unit
`K ⟶ Γ(K ⊗_R ℬ)` followed by the projections of the limit cone. -/
def extendUnitAugmentation (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    TowerAugmentation (extendSectionsTower f K) where
  source := K
  app n := extendUnit (liftedPowAlg f) K ≫
    (sectionsTowerCone R ((extendFunctor (liftedPowAlg f)).obj K).complex).π.app (op n)
  naturality _ := (Category.assoc _ _ _).trans (congrArg (extendUnit (liftedPowAlg f) K ≫ ·)
    ((sectionsTowerCone R ((extendFunctor (liftedPowAlg f)).obj K).complex).w _))

/-- **The strict unit followed by the Milnor augmentation of the global sections** is the
augmentation of the Milnor model by the strict unit. -/
theorem extendUnit_milnorAug (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    extendUnit (liftedPowAlg f) K ≫
        milnorAug R (liftedPowSheafAlgebra f) ((extendFunctor (liftedPowAlg f)).obj K) =
      TowerAugmentation.augmentationMap (extendUnitAugmentation f K) := by
  have h := TowerAugmentation.augmentationMap_naturality (extendUnitAugmentation f K)
    (TowerAugmentation.ofCone (sectionsTowerCone R
      ((extendFunctor (liftedPowAlg f)).obj K).complex))
    (extendUnit (liftedPowAlg f) K) (𝟙 _) (fun n => (Category.comp_id _).symm)
  exact h.trans ((congrArg (TowerAugmentation.augmentationMap (extendUnitAugmentation f K) ≫ ·)
    (countableMilnorFunctor.map_id (extendSectionsTower f K))).trans (Category.comp_id _))

/-- The augmentation by the strict unit, read through the identification of the tower of sections
with the coefficient Koszul tower, is the augmentation of the coefficient Koszul tower. -/
theorem augmentationMap_extendUnitAugmentation (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    TowerAugmentation.augmentationMap (extendUnitAugmentation f K) ≫
        countableMilnorFunctor.map (extendSectionsTowerIso f K).hom =
      (coefficientCompletionUnit f).app K := by
  refine (TowerAugmentation.augmentationMap_naturality (extendUnitAugmentation f K)
    (({ source := K
        app n := (coefficientKoszulAugmentation f n).app K
        naturality n := coefficientKoszulAugmentation_transition f K (n + 1) n (Nat.le_succ n) } :
      TowerAugmentation ((coefficientKoszulTower f).obj K)))
    (𝟙 K) (extendSectionsTowerIso f K).hom (fun n => ?_)).symm.trans (Category.id_comp _)
  refine HomologicalComplex.hom_ext _ _ fun p => ?_
  refine (Category.id_comp _).trans ?_
  refine Eq.trans ?_ (congrArg (fun g => g ≫ ((extendSectionsTowerIso f K).hom.app (op n)).f p)
    (extendUnit_f_π (liftedPowAlg f) K p (stage n))).symm
  exact (extendUnit_extendSectionsTowerIso f K n p).symm

variable {f}

/-- **The unit of `F' ⊣ RΓ` at the class of a derived complete complex is invertible.** -/
theorem isIso_derivedExtendAdjunction_unit_app_Qh
    (hB : ExtendInvertsQuasiIso (liftedPowSheafAlgebra f)) (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : IsDerivedComplete (Ideal.span (Set.range f)) (DerivedCategory.Q.obj K)) :
    IsIso ((derivedExtendAdjunction hB).unit.app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K))) := by
  rw [isIso_derivedExtendAdjunction_unit_app_Qh_iff hB]
  obtain ⟨ψ, hψ⟩ := exists_milnorIso R (liftedPowSheafAlgebra f)
    ((extendFunctor (liftedPowAlg f)).obj K)
  have hq : QuasiIso (extendUnit (liftedPowAlg f) K ≫
      milnorAug R (liftedPowSheafAlgebra f) ((extendFunctor (liftedPowAlg f)).obj K)) := by
    have h1 : QuasiIso ((coefficientCompletionUnit f).app K) :=
      coefficientCompletionUnit_quasiIso_of_complete f K hK
    rw [← augmentationMap_extendUnitAugmentation, ← extendUnit_milnorAug] at h1
    have hm : QuasiIso (countableMilnorFunctor.map (extendSectionsTowerIso f K).hom) := by
      have := (countableMilnorFunctor.mapIso (extendSectionsTowerIso f K)).isIso_hom
      exact quasiIso_of_isIso _
    exact (quasiIso_iff_comp_right (hφ' := hm) _ _).1 h1
  have hQ : IsIso (DerivedCategory.Q.map (extendUnit (liftedPowAlg f) K ≫
      milnorAug R (liftedPowSheafAlgebra f) ((extendFunctor (liftedPowAlg f)).obj K))) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hq
  have hnat := DerivedCategory.quotientCompQhIso_hom_naturality
    (extendUnit (liftedPowAlg f) K)
  have key : (DerivedCategory.Qh.map ((homotopyExtendAdjunction (liftedPowSheafAlgebra f)).unit.app
        ((HomotopyCategory.quotient _ _).obj K)) ≫
      (globalUnit (liftedPowSheafAlgebra f)).app
        ((homotopyExtend' (liftedPowSheafAlgebra f)).obj ((HomotopyCategory.quotient _ _).obj K))) ≫
        ψ.hom =
      (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.app K ≫
        DerivedCategory.Q.map (extendUnit (liftedPowAlg f) K ≫
          milnorAug R (liftedPowSheafAlgebra f) ((extendFunctor (liftedPowAlg f)).obj K)) := by
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
      (extendUnit (liftedPowAlg f) K)) ≫ ·) hψ).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ DerivedCategory.Q.map (milnorAug R (liftedPowSheafAlgebra f)
      ((extendFunctor (liftedPowAlg f)).obj K))) hnat).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    exact congrArg (_ ≫ ·) (DerivedCategory.Q.map_comp _ _).symm
  have : IsIso ((DerivedCategory.Qh.map ((homotopyExtendAdjunction
        (liftedPowSheafAlgebra f)).unit.app ((HomotopyCategory.quotient _ _).obj K)) ≫
      (globalUnit (liftedPowSheafAlgebra f)).app
        ((homotopyExtend' (liftedPowSheafAlgebra f)).obj ((HomotopyCategory.quotient _ _).obj K))) ≫
        ψ.hom) := by
    rw [key]
    infer_instance
  exact (isIso_comp_right_iff _ ψ.hom).1 this

/-- **The unit of `F' ⊣ RΓ` is invertible at every derived complete object of `D(R)`**: on a
derived complete `K` it is the derived completion `K ⟶ K^∧`, an isomorphism by Tag 091Z. -/
theorem isIso_derivedExtendAdjunction_unit_app
    (hB : ExtendInvertsQuasiIso (liftedPowSheafAlgebra f)) (X : DerivedCategory (ModuleCat.{u} R))
    (hX : IsDerivedComplete (Ideal.span (Set.range f)) X) :
    IsIso ((derivedExtendAdjunction hB).unit.app X) := by
  let e : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj
      (DerivedCategory.Q.objPreimage X)) ≅ X :=
    (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app _ ≪≫
      DerivedCategory.Q.objObjPreimageIso X
  refine (isIso_derivedExtendAdjunction_unit_app_iff_of_iso hB e).1 ?_
  exact isIso_derivedExtendAdjunction_unit_app_Qh hB _
    (DerivedCompleteRecurrence.isDerivedComplete_of_iso
      (DerivedCategory.Q.objObjPreimageIso X).symm hX)

end Koszul

end
