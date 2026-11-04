module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTripleVeroneseTransition

/-!
# The comparison `(j^*L) ^⊗ n ≅ j^*(L ^⊗ n)` is multiplicative

Let `j : Y' ⟶ Y` be a morphism of schemes and `L` an invertible `𝒪_Y`-module.
`Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullbackNatTensorPowIso` compares the tensor
powers of `j^*L` with the inverse images of the tensor powers of `L`. This file proves that
comparison **multiplicative**: it carries the multiplication isomorphism
`L ^⊗ p ⊗ L ^⊗ q ≅ L ^⊗ (p + q)` of the power system of iterated powers to that of `j^*L`, the
two inverse images being related by the cotensorator `j^*(A ⊗ B) ⟶ j^*A ⊗ j^*B`.

This is the morphism-level statement that the section-level
`Stacks.AlgebraicGeometry.ProjChartPullbackCotensorator.pullSection_mulSections` could not
replace: a section of a tensor power is not a product of sections, so a statement about all
morphisms out of a tensor power does not follow from one about products of sections.

## Main results

* `Stacks.GradedSections.natPowerSystem_mulIso_zero_hom` and `natPowerSystem_mulIso_succ_hom`:
  the two arms of the recursion defining the multiplication isomorphisms of the iterated tensor
  powers, with the identity comparisons of `Stacks.GradedSections.natPowerSystem` cancelled.
* `Stacks.AlgebraicGeometry.ProjTriplePullbackPowMul.mulIso_pullbackNatTensorPowIso`: **the
  comparison of the tensor powers is multiplicative.**

## Implementation notes

The induction is on the second exponent, and it runs on exactly the oplax monoidal structure of
`j^*` for the monoidal structure the tensor powers are read in: the base case is the right unit
law `Stacks.TensorSheafSpellingIso.pullbackCotensorator_rightUnitor` together with
`Stacks.AlgebraicGeometry.ProjChartSectionPullback.pullbackNatTensorPowIso_inv_zero`, which
identifies the comparison in degree zero with the structure-sheaf comparison, and the step is the
associativity law `Stacks.TensorSheafSpellingIso.pullbackCotensorator_assoc` together with the
naturality of the cotensorator in its first variable and the successor recursion
`Stacks.AlgebraicGeometry.ProjChartPullbackCotensorator.pullbackNatTensorPowIso_inv_succ`.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Section 01N4](https://stacks.math.columbia.edu/tag/01N4)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open AlgebraicGeometry
open Stacks.Ample (IsInvertibleModule)
open Stacks.GradedSections (natPowerSystem)
open Stacks.Monoidal (PowerSystem)
open Stacks.TensorPowers (natTensorPow)
open Stacks.AlgebraicGeometry.ProjChartRatioPullback (pullbackNatTensorPowIso)
open Stacks.AlgebraicGeometry.ProjChartPullbackCotensorator (pullbackCotensorator
  pullbackCotensorator_whiskerRight pullbackNatTensorPowIso_inv_succ)
open Stacks.AlgebraicGeometry.ProjChartSectionPullback (pullbackNatTensorPowIso_inv_zero)
open Stacks.PullbackUnitSection (unitPullbackHom)

namespace Stacks.GradedSections

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The multiplication isomorphism of the iterated tensor powers at second exponent zero is the
right unitor: the zeroth-power comparison of `Stacks.GradedSections.natPowerSystem` is the
identity. -/
theorem natPowerSystem_mulIso_zero_hom (L : C) (p : ℕ) :
    ((natPowerSystem L).mulIso p 0).hom = (ρ_ (natTensorPow L p)).hom := by
  show (natTensorPow L p ◁ 𝟙 (𝟙_ C)) ≫ (ρ_ (natTensorPow L p)).hom = _
  rw [MonoidalCategory.whiskerLeft_id, Category.id_comp]

/-- The multiplication isomorphism of the iterated tensor powers at a successor second exponent
splits the last factor off by the associator: both comparisons of
`Stacks.GradedSections.natPowerSystem` are the identity. -/
theorem natPowerSystem_mulIso_succ_hom (L : C) (p q : ℕ) :
    ((natPowerSystem L).mulIso p (q + 1)).hom
      = (α_ (natTensorPow L p) (natTensorPow L q) L).inv ≫
          (((natPowerSystem L).mulIso p q).hom ▷ L) := by
  show (natTensorPow L p ◁ 𝟙 (natTensorPow L q ⊗ L)) ≫
      (α_ (natTensorPow L p) (natTensorPow L q) L).inv ≫
      (((natPowerSystem L).mulIso p q).hom ▷ L) ≫
        𝟙 ((natPowerSystem L).obj (p + q) ⊗ L) = _
  rw [MonoidalCategory.whiskerLeft_id, Category.id_comp, Category.comp_id]

end Stacks.GradedSections

namespace Stacks.AlgebraicGeometry.ProjTriplePullbackPowMul

universe u

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {Y Y' : Scheme.{u}} (j : Y' ⟶ Y) (L : Y.Modules) [IsInvertibleModule Y L]

/-- The right unit bookkeeping of the base case, isolated in a bare monoidal category: a
comparison in the first factor crosses the right unitor. -/
private theorem rightUnitor_aux {D : Type*} [Category D] [MonoidalCategory D] {S T : D}
    {U : D} (c : S ⟶ T) (u : U ⟶ 𝟙_ D) :
    (S ◁ u) ≫ (ρ_ S).hom ≫ c = (c ⊗ₘ u) ≫ (ρ_ T).hom := by
  rw [tensorHom_def', Category.assoc, MonoidalCategory.rightUnitor_naturality]

/-- The associativity bookkeeping of the inductive step, isolated in a bare monoidal category:
a comparison of the middle factor can be pushed through the inverse associator. -/
private theorem associator_aux {D : Type*} [Category D] [MonoidalCategory D]
    {S M M' G Tp Tq : D} (cp : S ⟶ Tp) (cq : M' ⟶ Tq) (e : M ⟶ M' ⊗ G) :
    (S ◁ e) ≫ (α_ S M' G).inv ≫ ((cp ⊗ₘ cq) ▷ G)
      = (cp ⊗ₘ (e ≫ (cq ▷ G))) ≫ (α_ Tp Tq G).inv := by
  have h1 : (cp ⊗ₘ (e ≫ (cq ▷ G))) = (S ◁ e) ≫ (cp ⊗ₘ (cq ▷ G)) := by
    rw [← MonoidalCategory.id_tensorHom S e, MonoidalCategory.tensorHom_comp_tensorHom,
      Category.id_comp]
  have h2 : (cp ⊗ₘ (cq ▷ G)) ≫ (α_ Tp Tq G).inv
      = (α_ S M' G).inv ≫ ((cp ⊗ₘ cq) ▷ G) := by
    rw [← MonoidalCategory.tensorHom_id cq G,
      ← MonoidalCategory.tensorHom_id (cp ⊗ₘ cq) G,
      MonoidalCategory.associator_inv_naturality]
  rw [h1, Category.assoc, h2]

/-- **The inductive step, in a bare monoidal category with the cotensorator as free data.**
Given an oplax structure `δ` on a functor `F` — natural in its first variable and associative —
and comparisons of the two multiplications in degrees `(p, q)`, the comparison in degree
`(p, q + 1)` follows: the extra factor is split off by the associator on both sides.

Stating it with `F`, `δ` and the two multiplications free keeps every rewrite below inside one
spelling; a goal naming `Stacks.Monoidal.PowerSystem.mulIso` at two different exponents is not
type-correct at the transparency the rewriting tactics check their motives at. -/
private theorem step_aux {C D : Type*} [Category C] [MonoidalCategory C]
    [Category D] [MonoidalCategory D] (F : C ⥤ D)
    (δ : ∀ X Z : C, F.obj (X ⊗ Z) ⟶ F.obj X ⊗ F.obj Z)
    (hδnat : ∀ {X X' : C} (h : X ⟶ X') (Z : C),
      F.map (h ▷ Z) ≫ δ X' Z = δ X Z ≫ (F.map h ▷ F.obj Z))
    (hδassoc : ∀ X Z W : C,
      F.map (α_ X Z W).hom ≫ δ X (Z ⊗ W) ≫ (F.obj X ◁ δ Z W)
        = δ (X ⊗ Z) W ≫ (δ X Z ▷ F.obj W) ≫ (α_ (F.obj X) (F.obj Z) (F.obj W)).hom)
    {A B G E : C} {TA TB TE : D} (m : A ⊗ B ⟶ E) (m' : TA ⊗ TB ⟶ TE)
    (cA : F.obj A ⟶ TA) (cB : F.obj B ⟶ TB) (cE : F.obj E ⟶ TE)
    (ih : F.map m ≫ cE = δ A B ≫ (cA ⊗ₘ cB) ≫ m') :
    F.map ((α_ A B G).inv ≫ (m ▷ G)) ≫ δ E G ≫ (cE ▷ F.obj G)
      = δ A (B ⊗ G) ≫ (cA ⊗ₘ (δ B G ≫ (cB ▷ F.obj G))) ≫
          (α_ TA TB (F.obj G)).inv ≫ (m' ▷ F.obj G) := by
  have hassoc' : F.map (α_ A B G).inv ≫ δ (A ⊗ B) G ≫ (δ A B ▷ F.obj G)
      = δ A (B ⊗ G) ≫ (F.obj A ◁ δ B G) ≫ (α_ (F.obj A) (F.obj B) (F.obj G)).inv := by
    rw [← Category.assoc (δ A (B ⊗ G)), Iso.eq_comp_inv, Category.assoc, Category.assoc,
      ← hδassoc A B G, ← F.map_comp_assoc, Iso.inv_hom_id, F.map_id, Category.id_comp]
  rw [F.map_comp, Category.assoc, reassoc_of% (hδnat m G), ← MonoidalCategory.comp_whiskerRight,
    ih, MonoidalCategory.comp_whiskerRight, MonoidalCategory.comp_whiskerRight,
    reassoc_of% hassoc', reassoc_of% (associator_aux cA cB (δ B G))]

/-- **The comparison `(j^*L) ^⊗ n ≅ j^*(L ^⊗ n)` is multiplicative**: the inverse image of the
multiplication isomorphism of the iterated tensor powers of `L`, read through the comparison,
is the multiplication isomorphism for `j^*L` preceded by the cotensorator and by the comparison
in each factor.

By induction on the second exponent: the base case is the right unit law of the cotensorator
with the degree-zero comparison identified as the structure-sheaf comparison, and the step is
its associativity law together with its naturality in the first variable. -/
theorem mulIso_pullbackNatTensorPowIso (p : ℕ) : ∀ q : ℕ,
    (Scheme.Modules.pullback j).map ((natPowerSystem L).mulIso p q).hom ≫
        (pullbackNatTensorPowIso j L (p + q)).inv
      = pullbackCotensorator j (natTensorPow L p) (natTensorPow L q) ≫
        ((pullbackNatTensorPowIso j L p).inv ⊗ₘ (pullbackNatTensorPowIso j L q).inv) ≫
          ((natPowerSystem ((Scheme.Modules.pullback j).obj L)).mulIso p q).hom
  | 0 => by
      have h : (Scheme.Modules.pullback j).map (ρ_ (natTensorPow L p)).hom ≫
            (pullbackNatTensorPowIso j L p).inv
          = pullbackCotensorator j (natTensorPow L p) (𝟙_ Y.Modules) ≫
            ((pullbackNatTensorPowIso j L p).inv ⊗ₘ unitPullbackHom j) ≫
              (ρ_ (natTensorPow ((Scheme.Modules.pullback j).obj L) p)).hom := by
        rw [Stacks.TensorSheafSpellingIso.pullbackCotensorator_rightUnitor Y j (natTensorPow L p),
          Category.assoc, Category.assoc]
        exact congrArg (fun z => pullbackCotensorator j (natTensorPow L p) (𝟙_ Y.Modules) ≫ z)
          (rightUnitor_aux (pullbackNatTensorPowIso j L p).inv (unitPullbackHom j))
      rw [Stacks.GradedSections.natPowerSystem_mulIso_zero_hom,
        Stacks.GradedSections.natPowerSystem_mulIso_zero_hom, pullbackNatTensorPowIso_inv_zero]
      exact h
  | q + 1 => by
      have key := step_aux (Scheme.Modules.pullback j) (pullbackCotensorator j)
        (pullbackCotensorator_whiskerRight j)
        (Stacks.TensorSheafSpellingIso.pullbackCotensorator_assoc Y j)
        (G := L) ((natPowerSystem L).mulIso p q).hom
        ((natPowerSystem ((Scheme.Modules.pullback j).obj L)).mulIso p q).hom
        (pullbackNatTensorPowIso j L p).inv (pullbackNatTensorPowIso j L q).inv
        (pullbackNatTensorPowIso j L (p + q)).inv
        (mulIso_pullbackNatTensorPowIso p q)
      simp only [Stacks.GradedSections.natPowerSystem_obj] at key
      rw [← Stacks.GradedSections.natPowerSystem_mulIso_succ_hom L p q,
        ← pullbackNatTensorPowIso_inv_succ j L (p + q),
        ← pullbackNatTensorPowIso_inv_succ j L q,
        ← Stacks.GradedSections.natPowerSystem_mulIso_succ_hom
          ((Scheme.Modules.pullback j).obj L) p q] at key
      exact key

end Stacks.AlgebraicGeometry.ProjTriplePullbackPowMul

end
