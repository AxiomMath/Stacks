module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleEquivalence

/-!
# A split section of an invertible module is a trivialization

In any monoidal category, a morphism `σ : 𝟙 ⟶ L` with a retraction `ρ` is an isomorphism as soon
as tensoring by `L` is full: the idempotent `ρ ≫ σ` of `L` is `L ◁ a` for an endomorphism `a` of
the unit, and moving `a` across `ρ` shows `a = 𝟙`. For invertible modules on an algebraic space
tensoring is an equivalence, so a split section `𝒪 ⟶ L` of an invertible module is an
isomorphism. This is the step "`σ` and `τ` with `στ = 1` give `𝒪 ≅ L`" of the proof of
Stacks 0D23.

## Main results

* `CategoryTheory.MonoidalCategory.isIso_of_comp_eq_id_of_full_tensorLeft`: a split morphism
  `𝟙 ⟶ L` is an isomorphism when tensoring by `L` is full.
* `AlgebraicGeometry.Space.isIso_of_comp_eq_id_of_isInvertibleModule`: a split section of an
  invertible module on an algebraic space is an isomorphism.

## References

* [Stacks Project, Tag 0D23](https://stacks.math.columbia.edu/tag/0D23)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace CategoryTheory.MonoidalCategory

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- **A split morphism `𝟙 ⟶ L` is an isomorphism when tensoring by `L` is full.** If `σ ≫ ρ = 𝟙`
then the idempotent `ρ ≫ σ` of `L` is, by fullness, `L ◁ a` for an endomorphism `a` of the unit;
moving `a` across `ρ` shows `a = σ ≫ (ρ ≫ σ) ≫ ρ = 𝟙`, so `ρ ≫ σ = 𝟙`. -/
theorem isIso_of_comp_eq_id_of_full_tensorLeft {L : C} [(tensorLeft L).Full]
    (σ : 𝟙_ C ⟶ L) (ρ : L ⟶ 𝟙_ C) (h : σ ≫ ρ = 𝟙 _) : IsIso σ := by
  obtain ⟨a, ha⟩ := (tensorLeft L).map_surjective ((ρ_ L).hom ≫ (ρ ≫ σ) ≫ (ρ_ L).inv)
  change L ◁ a = _ at ha
  have e1 : ρ ≫ σ = (ρ_ L).inv ≫ L ◁ a ≫ (ρ_ L).hom := by
    rw [ha]; simp
  have hmove : (ρ ≫ σ) ≫ ρ = ρ ≫ a := by
    rw [e1]
    simp only [Category.assoc]
    rw [← rightUnitor_naturality ρ, whisker_exchange_assoc, ← unitors_equal,
      leftUnitor_naturality, unitors_equal, rightUnitor_naturality_assoc,
      Iso.inv_hom_id_assoc]
  have ha1 : a = 𝟙 _ := by
    have h2 := congrArg (fun z => σ ≫ z) hmove
    simp only [Category.assoc, reassoc_of% h] at h2
    rw [h] at h2
    exact h2.symm
  subst ha1
  refine ⟨⟨ρ, h, ?_⟩⟩
  rw [e1]
  simp

end CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] modulesMonoidalCategory

/-- **A split section of an invertible module is an isomorphism.** If `σ : 𝒪_Z ⟶ L` has a
retraction and `L` is invertible, then `σ` is an isomorphism: tensoring by `L` is an
equivalence, in particular full. -/
theorem isIso_of_comp_eq_id_of_isInvertibleModule (Z : AlgebraicSpaces B S hS)
    {L : Modules.{u, u} B S hS Z.1 Z.2} (hL : IsInvertibleModule Z L)
    (σ : SheafOfModules.unit _ ⟶ L) (ρ : L ⟶ SheafOfModules.unit _) (h : σ ≫ ρ = 𝟙 _) :
    IsIso σ := by
  have hZ₁ : HasWeakSheafify (SmallEtale.topology B S hS Z.1) AddCommGrpCat.{u} :=
    inferInstance
  have hZ₂ : (SmallEtale.topology B S hS Z.1).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstance
  have hK : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (structureSheaf B S hS Z.1 Z.2)).obj L).IsEquivalence :=
    (Stacks.SheafOfModules.isInvertible_iff_tensorLeftFunctor_isEquivalence _ _ L).mp hL
  have : (tensorLeft L).IsEquivalence :=
    (Stacks.SheafOfModules.isEquivalence_tensorLeft_iff _ _ L).mpr hK
  exact isIso_of_comp_eq_id_of_full_tensorLeft σ ρ h

end AlgebraicGeometry.Space

end
