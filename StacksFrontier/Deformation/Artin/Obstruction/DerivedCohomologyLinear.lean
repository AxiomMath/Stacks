module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Monoidal.Linear
public import StacksFrontier.Deformation.Artin.Obstruction.DualSituation
public import StacksFrontier.Homology.DerivedComplete.CompleteAdic

/-!
# `H^n(K ⊗ᴸ_A −)` is an `A`-linear functor

For `K` in `D(A)`, the functor `M ↦ H^n(K ⊗ᴸ_A M)` of `Deformation.Artin.derivedCohomology` is
`A`-linear: it is the composite of the inclusion of modules in degree `0`, the derived tensor
product with `K`, and the derived homology functor, and each of the three is `A`-linear. In
particular `r : A` acts on `H^n(K ⊗ᴸ_A M)` through `H^n(K ⊗ᴸ_A (r • 𝟙_M))`.

## Main results

* `TotalTensorComplex.trightCochain_linear`, `TotalTensorComplex.tright_linear`: `F ↦ Tot(F ⊗ G)`
  is `R`-linear on cochain complexes and on the homotopy category, for a monoidal-linear `C`.
* `ModuleCat.liftedModuleMonoidalLinear`: the tensor product of `ModuleCat.{max u v} R` is
  `R`-linear in each variable.
* `CochainComplex.DerivedTensor.derivedTensorProduct_linear`: `K ⊗ᴸ −` is `R`-linear on `D(R)`.
* `Deformation.Artin.derivedCohomology_linear` and
  `Deformation.Artin.derivedCohomology_map_smul_apply`.

## Implementation notes

The derived tensor product is a `Localization.lift` of `Tright K ⋙ Qh` along `Qh`, so its
linearity follows from that of `Tright K` by `Localization.functor_linear_iff`; the same lemma
along `Q` gives the linearity of the derived homology functor
(`derivedHomologyFunctorLinear`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits

universe u v w

namespace TotalTensorComplex

section Linear

variable (R : Type*) [Ring R] {C : Type*} [Category C] [Preadditive C] [Linear R C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear R C] [HasZeroObject C]
  [HasBinaryBiproducts C]
  [(curriedTensor C).Additive] [∀ X₁ : C, ((curriedTensor C).obj X₁).Additive]
  [∀ (K₁ K₂ : CochainComplex C ℤ),
      HomologicalComplex.HasMapBifunctor K₁ K₂ (curriedTensor C) (ComplexShape.up ℤ)]

omit [HasZeroObject C] [HasBinaryBiproducts C] in
/-- The right tensor–total functor `F ↦ Tot(F ⊗ G)` on cochain complexes is `R`-linear. -/
theorem trightCochain_linear (G : CochainComplex C ℤ) : (TrightCochain G).Linear R where
  map_smul {X Y} f r := by
    change HomologicalComplex.mapBifunctorMap (r • f) (𝟙 G) (curriedTensor C) (ComplexShape.up ℤ)
      = r • HomologicalComplex.mapBifunctorMap f (𝟙 G) (curriedTensor C) (ComplexShape.up ℤ)
    ext n i₁ i₂ h
    rw [HomologicalComplex.smul_f_apply,
      HomologicalComplex.ι_mapBifunctorMap _ _ _ _ i₁ i₂ n h, Linear.comp_smul,
      HomologicalComplex.ι_mapBifunctorMap _ _ _ _ i₁ i₂ n h]
    simp [MonoidalLinear.smul_whiskerRight]

omit [HasZeroObject C] [HasBinaryBiproducts C] in
/-- The right tensor–total functor `F ↦ Tot(F ⊗ G)` on the homotopy category is `R`-linear. -/
theorem tright_linear (G : CochainComplex C ℤ) : (Tright G).Linear R where
  map_smul {X Y} f r := by
    have := trightCochain_linear R G
    have key : ∀ (X' Y' : CochainComplex C ℤ) (g : X' ⟶ Y'),
        (Tright G).map (r • (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map g) =
          r • (Tright G).map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map g) := by
      intro X' Y' g
      rw [← Functor.map_smul]
      exact (congrArg (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        ((TrightCochain G).map_smul r g)).trans
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_smul r _)
    obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective
      (X := X.as) (Y := Y.as) f
    exact key X.as Y.as g

end Linear

end TotalTensorComplex

namespace ModuleCat

attribute [local instance] ModuleCat.liftedModuleMonoidalStruct
  ModuleCat.liftedModuleMonoidal ModuleCat.liftedModuleMonoidalPreadditive

/-- The tensor product of `ModuleCat.{max u v} R` is `R`-linear in each variable. -/
theorem liftedModuleMonoidalLinear (R : Type u) [CommRing R] :
    MonoidalLinear R (ModuleCat.{max u v} R) where
  whiskerLeft_smul M _ _ r f := ModuleCat.hom_ext (LinearMap.lTensor_smul (M := M) r f.hom)
  smul_whiskerRight r _ _ f M := ModuleCat.hom_ext (LinearMap.rTensor_smul (M := M) r f.hom)

end ModuleCat

namespace CochainComplex.DerivedTensor

attribute [local instance] ModuleCat.liftedModuleMonoidalStruct
  ModuleCat.liftedModuleMonoidal ModuleCat.liftedModuleMonoidalPreadditive
  ModuleCat.liftedModuleMonoidalLinear

/-- A lift of an `R`-linear functor along an `R`-linear localization functor is `R`-linear. -/
private theorem linear_localizationLift {R : Type*} [Ring R] {C D E : Type*} [Category C]
    [Category D] [Category E] [Preadditive C] [Preadditive D] [Preadditive E] [Linear R C]
    [Linear R D] [Linear R E] (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    [L.Linear R] (F : C ⥤ E) (hF : W.IsInvertedBy F) (hlin : F.Linear R) :
    (Localization.lift F hF L).Linear R :=
  (Localization.functor_linear_iff L W R F _).mp hlin

/-- **The derived tensor product `K ⊗ᴸ −` on `D(R)` is `R`-linear.** -/
theorem derivedTensorProduct_linear {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (M : DerivedCategory (ModuleCat.{max u v} R)) :
    (derivedTensorProduct M).Linear R := by
  unfold derivedTensorProduct
  dsimp only
  refine linear_localizationLift DerivedCategory.Qh
    (HomotopyCategory.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)) _ _
    ?_
  have := TotalTensorComplex.tright_linear R (C := ModuleCat.{max u v} R)
  infer_instance

end CochainComplex.DerivedTensor

namespace Deformation.Artin

attribute [local instance] HasDerivedCategory.standard derivedHomologyFunctorLinear
  CochainComplex.DerivedTensor.derivedTensorProduct_linear

/-- **`H^n(K ⊗ᴸ_A −)` is `A`-linear.** -/
theorem derivedCohomology_linear (A : Type u) [CommRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    (derivedCohomology A K n).Linear A := by
  unfold derivedCohomology
  infer_instance

/-- **`r : A` acts on `H^n(K ⊗ᴸ_A M)` through `H^n(K ⊗ᴸ_A (r • 𝟙_M))`.** -/
theorem derivedCohomology_map_smul_apply (A : Type u) [CommRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) (M : ModuleCat.{u} A) (r : A)
    (y : (derivedCohomology A K n).obj M) :
    (derivedCohomology A K n).map (r • 𝟙 M) y = r • y := by
  have := derivedCohomology_linear A K n
  rw [Functor.map_smul, CategoryTheory.Functor.map_id]
  rfl

end Deformation.Artin

end
