module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeDifferentialGradedModuleClosedSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedSetsConstantDegreeFiber

/-!
# The free differential graded module on a sheaf of sets in a single degree

Tag 0FSF's free differential graded module `D[S]` on a sheaf of graded sets `S` corepresents
`Q ↦ ∀ i, Hom(S_i, Z_i Q)`, a product over all degrees. When `S = Stacks.constDeg F k` is a sheaf
of sets `F` placed in the single degree `k`, every factor but the `k`-th is a morphism out of an
initial sheaf, so the product collapses:

`Hom_D(D[constDeg F k], Q) ≃ Hom_{Sh}(F, Z_k Q)`.

## Main definitions

* `SheafOfModules.constDegFamily`: the family of generator maps attached to a morphism
  `F ⟶ Z_k Q`, which is the given morphism in degree `k` and the unique morphism out of an
  initial sheaf in every other degree.
* `SheafOfModules.freeDGModuleConstDegHomEquiv`: the displayed bijection.

## Main results

* `SheafOfModules.freeDGModuleConstDegHomEquiv_comp`: the bijection is natural in `Q`.

## Implementation notes

The off-degree factors are not empty: `Stacks.isInitial_degreeFiberSheaf_constDeg` shows they are
*initial*, which is what makes the morphism out of them unique. That is the only input beyond
Tag 0FSF's universal property `SheafOfModules.freeDGModuleHomEquiv`.

## References

* [Stacks Project, Tag 0FSF](https://stacks.math.columbia.edu/tag/0FSF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open Stacks Stacks.SheafOfGradedSets

universe t m v u

namespace SheafOfModules

open DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

section SingleDegree

variable [HasSheafify J (Type m)] [HasWeakSheafify J AddCommGrpCat.{m}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  (F : Sheaf J (Type m)) (D : DifferentialGradedAlgebra.{t, m} R) (k : ℤ)
  (Q : DifferentialGradedModule.{t, m, m} D)

/-- **The family of generator maps attached to a morphism `F ⟶ Z_k Q`.** In degree `k` it is the
given morphism, read through the identification of the degree-`k` fibre of `constDeg F k` with
`F`; in every other degree the source is initial and there is nothing to choose. -/
noncomputable def constDegFamily (g : F ⟶ closedSectionSheaf Q k) (i : ℤ) :
    degreeFiberSheaf (constDeg.{v, u, m} F k) i ⟶ closedSectionSheaf Q i :=
  if h : k = i then h ▸ ((constDegSelfIso F k).hom ≫ g)
  else (isInitial_degreeFiberSheaf_constDeg F h).to _

omit [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- In the distinguished degree `k` the family is the given morphism, precomposed with the
identification of the degree-`k` fibre of `constDeg F k` with `F`. -/
@[simp]
theorem constDegFamily_self (g : F ⟶ closedSectionSheaf Q k) :
    constDegFamily F D k Q g k = (constDegSelfIso F k).hom ≫ g :=
  dite_eq_left rfl

omit [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- Away from the distinguished degree the family is the only possible morphism. -/
theorem constDegFamily_ne (g : F ⟶ closedSectionSheaf Q k) {i : ℤ} (h : k ≠ i)
    (a : degreeFiberSheaf (constDeg.{v, u, m} F k) i ⟶ closedSectionSheaf Q i) :
    constDegFamily F D k Q g i = a :=
  hom_degreeFiberSheaf_constDeg_ext F h _ a

/-- **A morphism out of `D[constDeg F k]` is a morphism from `F` to the closed degree-`k`
sections.** -/
noncomputable def freeDGModuleConstDegHomEquiv :
    (freeDGModule (constDeg.{v, u, m} F k) D ⟶ Q) ≃ (F ⟶ closedSectionSheaf Q k) where
  toFun h := (constDegSelfIso F k).inv ≫
    freeDGModuleHomEquiv (constDeg.{v, u, m} F k) D Q h k
  invFun g := (freeDGModuleHomEquiv (constDeg.{v, u, m} F k) D Q).symm (constDegFamily F D k Q g)
  left_inv h := by
    dsimp only
    refine (freeDGModuleHomEquiv (constDeg.{v, u, m} F k) D Q).injective ?_
    rw [Equiv.apply_symm_apply]
    refine funext fun i => ?_
    by_cases hik : k = i
    · subst hik
      rw [constDegFamily_self, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    · exact constDegFamily_ne F D k Q _ hik _
  right_inv g := by
    dsimp only
    rw [Equiv.apply_symm_apply, constDegFamily_self, ← Category.assoc, Iso.inv_hom_id,
      Category.id_comp]

/-- The bijection sends `h` to its degree-`k` component, precomposed with the identification of
`F` with the degree-`k` fibre of `constDeg F k`. -/
@[simp]
theorem freeDGModuleConstDegHomEquiv_apply (h : freeDGModule (constDeg.{v, u, m} F k) D ⟶ Q) :
    freeDGModuleConstDegHomEquiv F D k Q h =
      (constDegSelfIso F k).inv ≫ freeDGModuleHomToClosed (constDeg.{v, u, m} F k) D Q h k :=
  rfl

/-- **The bijection is natural in `Q`.** -/
theorem freeDGModuleConstDegHomEquiv_comp {Q' : DifferentialGradedModule.{t, m, m} D}
    (j : Q ⟶ Q') (h : freeDGModule (constDeg.{v, u, m} F k) D ⟶ Q) :
    freeDGModuleConstDegHomEquiv F D k Q' (h ≫ j) =
      freeDGModuleConstDegHomEquiv F D k Q h ≫ closedSectionMap j k := by
  rw [freeDGModuleConstDegHomEquiv_apply, freeDGModuleConstDegHomEquiv_apply,
    freeDGModuleHomToClosed_comp, Category.assoc]

/-- **The bijection is natural in `Q`**, read backwards. -/
theorem freeDGModuleConstDegHomEquiv_symm_comp {Q' : DifferentialGradedModule.{t, m, m} D}
    (j : Q ⟶ Q') (g : F ⟶ closedSectionSheaf Q k) :
    (freeDGModuleConstDegHomEquiv F D k Q').symm (g ≫ closedSectionMap j k) =
      (freeDGModuleConstDegHomEquiv F D k Q).symm g ≫ j := by
  refine (freeDGModuleConstDegHomEquiv F D k Q').injective ?_
  rw [Equiv.apply_symm_apply, freeDGModuleConstDegHomEquiv_comp, Equiv.apply_symm_apply]

end SingleDegree

end SheafOfModules

end
