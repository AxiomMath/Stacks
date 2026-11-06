module

public import StacksFrontier.Homology.DerivedCategory.InverseSystem.EpiTowerLimit

/-!
# Milnor limits of epimorphic towers of abelian groups

`StacksFrontier/Homology/DerivedCategory/InverseSystem/EpiTowerLimit.lean` proves that a tower of
complexes with epimorphic transition maps has its ordinary inverse limit for a derived inverse
limit, in any abelian category with exact `ℕ`-indexed products in which the difference map
`(x_n) ↦ (x_n - t_n x_{n+1})` of an epimorphic tower of objects is an epimorphism, and discharges
that last hypothesis for `ModuleCat A`.  This file discharges it for `AddCommGrpCat`.

The argument is the same one: an epimorphism of abelian groups is a surjection, the product of a
family of abelian groups is the dependent function type by
`AddCommGrpCat.HasLimit.productLimitCone`, and on dependent functions the difference map is
surjective by `Stacks.InverseSystem.surjective_pi_sub_shift`, which builds a preimage upwards one
transition map at a time.

## Main results

* `DerivedCategory.isDerivedLimit_of_limit_cone_of_epi_addCommGrpCat` — **a tower of complexes
  of abelian groups with epimorphic transition maps has `Q` of its ordinary inverse limit for a
  derived inverse limit.**

## Why `AddCommGrpCat`

This is the shape the derived limit of [Stacks, Tag 07MV] is taken in: the tower
`Crystalline.pAdicLevelDerivedGlobalSectionsTower` of
`StacksFrontier/AlgebraicGeometry/Crystalline/FiniteLevelTowerArrows.lean` is a functor
`ℕᵒᵖ ⥤ D⁺(Ab)`, its terms being derived global sections of *abelian* sheaves on the crystalline
sites of the finite divided power levels.

**Nothing here is any part of the conclusion of that remark**, and no tag attribute is placed
below.  Applying this theorem there needs the two inputs the remark's own hints are, neither of
which the library has: that `Γ(Cris(X/S), F)` is the limit of the tower of finite-level global
sections, and that the transition maps of that tower are surjective on an injective sheaf.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace DerivedCategory

/-- The product of a countable family of abelian groups is the group of dependent functions.
This is `AddCommGrpCat.HasLimit.productLimitCone` read as an isomorphism with `∏ᶜ`. -/
private def piIsoPiAddCommGrpCat (X : ℕ → AddCommGrpCat.{u}) :
    (∏ᶜ X : AddCommGrpCat.{u}) ≅ AddCommGrpCat.of (∀ n, X n) :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _)
    (AddCommGrpCat.HasLimit.productLimitCone X).isLimit

private theorem piIsoPiAddCommGrpCat_inv_apply (X : ℕ → AddCommGrpCat.{u}) (n : ℕ)
    (x : ∀ n, X n) : Pi.π X n ((piIsoPiAddCommGrpCat X).inv x) = x n :=
  congrArg (fun (f : _ ⟶ _) ↦ (ConcreteCategory.hom f) x)
    (IsLimit.conePointUniqueUpToIso_inv_comp (limit.isLimit _)
      (AddCommGrpCat.HasLimit.productLimitCone X).isLimit (Discrete.mk n))

private theorem piIsoPiAddCommGrpCat_hom_apply (X : ℕ → AddCommGrpCat.{u}) (n : ℕ)
    (z : (∏ᶜ X : AddCommGrpCat.{u})) : (piIsoPiAddCommGrpCat X).hom z n = Pi.π X n z := by
  simpa using (piIsoPiAddCommGrpCat_inv_apply X n ((piIsoPiAddCommGrpCat X).hom z)).symm

/-- The difference map of a tower of abelian groups with epimorphic transition maps is an
epimorphism.  This is the hypothesis `hB` of
`DerivedCategory.isDerivedLimit_of_limit_cone_of_epi_of_epi_pi_sub_shift` for `AddCommGrpCat`. -/
private theorem epi_pi_sub_shift_of_epi_addCommGrpCat (X : ℕ → AddCommGrpCat.{u})
    (t : ∀ n, X (n + 1) ⟶ X n) (ht : ∀ n, Epi (t n)) :
    Epi (Pi.lift fun n ↦ Pi.π X n - Pi.π X (n + 1) ≫ t n) := by
  apply (AddCommGrpCat.epi_iff_surjective _).mpr
  intro y
  obtain ⟨x, hx⟩ := Stacks.InverseSystem.surjective_pi_sub_shift
    (M := fun n ↦ (X n : Type u)) (fun n ↦ ⇑(ConcreteCategory.hom (t n)))
    (fun n ↦ (AddCommGrpCat.epi_iff_surjective (t n)).mp (ht n))
    ((piIsoPiAddCommGrpCat X).hom y)
  refine ⟨(piIsoPiAddCommGrpCat X).inv x, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso (piIsoPiAddCommGrpCat X).hom).injective
  funext n
  rw [piIsoPiAddCommGrpCat_hom_apply, piIsoPiAddCommGrpCat_hom_apply]
  have hπ : Pi.π X n ((Pi.lift fun n ↦ Pi.π X n - Pi.π X (n + 1) ≫ t n)
        ((piIsoPiAddCommGrpCat X).inv x)) =
      ((Pi.lift fun n ↦ Pi.π X n - Pi.π X (n + 1) ≫ t n) ≫ Pi.π X n)
        ((piIsoPiAddCommGrpCat X).inv x) := rfl
  rw [hπ, Pi.lift_comp_π]
  show Pi.π X n ((piIsoPiAddCommGrpCat X).inv x) -
    (t n) (Pi.π X (n + 1) ((piIsoPiAddCommGrpCat X).inv x)) =
      (piIsoPiAddCommGrpCat X).hom y n
  rw [piIsoPiAddCommGrpCat_inv_apply, piIsoPiAddCommGrpCat_inv_apply]
  exact congrFun hx n

/-- **A tower of complexes of abelian groups whose transition maps are epimorphisms has `Q` of
its ordinary inverse limit for a derived inverse limit.**  At index `n` the transition is the
map from `n + 1` to `n`, so a tower indexed by positive powers has level `n` for power `n + 1`.

This is `DerivedCategory.isDerivedLimit_of_limit_cone_of_epi_of_epi_pi_sub_shift` with its one
non-formal hypothesis discharged for `AddCommGrpCat` by
`DerivedCategory.epi_pi_sub_shift_of_epi_addCommGrpCat`. -/
public theorem isDerivedLimit_of_limit_cone_of_epi_addCommGrpCat
    (F : ℕᵒᵖ ⥤ CochainComplex AddCommGrpCat.{u} ℤ)
    [∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op)]
    (s : Cone F) (hs : IsLimit s) :
    letI : HasProductsOfShape ℕ (DerivedCategory AddCommGrpCat.{u}) :=
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    CategoryTheory.Pretriangulated.IsDerivedLimit (F ⋙ DerivedCategory.Q)
      (DerivedCategory.Q.obj s.pt) :=
  isDerivedLimit_of_limit_cone_of_epi_of_epi_pi_sub_shift (B := AddCommGrpCat.{u})
    epi_pi_sub_shift_of_epi_addCommGrpCat F s hs

end DerivedCategory

end
