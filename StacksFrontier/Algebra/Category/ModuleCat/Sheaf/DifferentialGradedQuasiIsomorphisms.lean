module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedCategory
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetRightAdjoint

/-!
# The quasi-isomorphisms of `K(A)` as a multiplicative system

Let `R` be a sheaf of rings on a site admitting sheafification and let `A` be a sheaf of
differential graded `R`-algebras. The quasi-isomorphisms of the homotopy category `K(A)` of
right differential graded `A`-modules are *saturated*: a morphism which becomes a
quasi-isomorphism after composing with a morphism on either side is one already. They are also
exactly the arrows which the functor forgetting the action of `A` sends to isomorphisms of the
derived category `D(R)` of sheaves of `R`-modules.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.homotopyForget` and
  `SheafOfModules.DifferentialGradedModule.derivedForget`: forgetting the action of `A`, read
  on the homotopy category and on the derived category `D(A, d)`, with values in the derived
  category of sheaves of `R`-modules.

## Main results

* `SheafOfModules.DifferentialGradedModule.quasiIsomorphisms_mem_of_comp_mem_comp`: the
  saturation axiom MS4 for the quasi-isomorphisms of `K(A)`.
* `SheafOfModules.DifferentialGradedModule.quasiIsomorphisms_iff_isIso_homotopyForget`: a
  morphism of `K(A)` is a quasi-isomorphism exactly when it becomes invertible in `D(R)`.
* `SheafOfModules.DifferentialGradedModule.toDerivedCategory_comp_derivedForget`: forgetting
  the action factors through the derived category of `(A, d)`.

## References

* [Stacks Project, Tag 0FT4](https://stacks.math.columbia.edu/tag/0FT4)
* [Stacks Project, Tag 0FT5](https://stacks.math.columbia.edu/tag/0FT5)
* [Stacks Project, Tag 0FS7](https://stacks.math.columbia.edu/tag/0FS7)
-/

@[expose] public section

open CategoryTheory

add_to_stacks 0FT4 "the class Qis of quasi-isomorphisms of K(A)"
  SheafOfModules.DifferentialGradedModule.quasiIsomorphisms

add_to_stacks 0FT4 "well-definedness: Qis may be read off any representing morphism"
  SheafOfModules.DifferentialGradedModule.quasiIsomorphisms_quotient_map_iff

add_to_stacks 0FT4 "axiom MS1: Qis contains the identities and is stable under composition"
  SheafOfModules.DifferentialGradedModule.quasiIsomorphisms_isMultiplicative

universe w t a m v u

namespace SheafOfModules

namespace DifferentialGradedModule

/-- A morphism which becomes invertible after composing with a morphism on either side is
itself invertible. -/
private theorem isIso_of_comp_isIso_of_isIso_comp {D : Type*} [Category D] {X Y Z T : D}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) (h₁ : IsIso (f ≫ g)) (h₂ : IsIso (g ≫ h)) :
    IsIso g := by
  have : IsSplitEpi g := ⟨⟨inv (f ≫ g) ≫ f, by simp⟩⟩
  have : IsSplitMono g := ⟨⟨h ≫ inv (g ≫ h), by rw [← Category.assoc, IsIso.hom_inv_id]⟩⟩
  exact isIso_of_mono_of_isSplitEpi g

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  (A : DifferentialGradedAlgebra.{t, a} R)

/-! ### Saturation -/

/-- Axiom MS4, the saturation axiom: an arrow of the homotopy category of right differential
graded `A`-modules which becomes a quasi-isomorphism after composing with an arrow on either side
is a quasi-isomorphism already. -/
@[stacks 0FT4 "axiom MS4: saturation of Qis"]
theorem quasiIsomorphisms_mem_of_comp_mem_comp {X Y Z T : HomotopyCategory.{t, a, m} A}
    (φ : X ⟶ Y) (ψ : Y ⟶ Z) (χ : Z ⟶ T)
    (hφψ : quasiIsomorphisms.{t, a, m} A (φ ≫ ψ))
    (hψχ : quasiIsomorphisms.{t, a, m} A (ψ ≫ χ)) :
    quasiIsomorphisms.{t, a, m} A ψ := by
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient A).map_surjective φ
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient A).map_surjective ψ
  obtain ⟨h, rfl⟩ := (HomotopyCategory.quotient A).map_surjective χ
  rw [← Functor.map_comp, quasiIsomorphisms_quotient_map_iff,
    quasiIso_iff_isIso_homologyMap] at hφψ hψχ
  rw [quasiIsomorphisms_quotient_map_iff, quasiIso_iff_isIso_homologyMap]
  intro i
  refine isIso_of_comp_isIso_of_isIso_comp
    (HomologicalComplex.homologyMap f.toHomologicalComplex i) _
    (HomologicalComplex.homologyMap h.toHomologicalComplex i) ?_ ?_ <;>
    rw [← HomologicalComplex.homologyMap_comp]
  exacts [hφψ i, hψχ i]

/-- An isomorphism of the homotopy category of right differential graded `A`-modules is a
quasi-isomorphism. -/
theorem quasiIsomorphisms_of_isIso {X Y : HomotopyCategory.{t, a, m} A} (φ : X ⟶ Y) [IsIso φ] :
    quasiIsomorphisms.{t, a, m} A φ := by
  refine quasiIsomorphisms_mem_of_comp_mem_comp A (inv φ) φ (inv φ) ?_ ?_
  · rw [IsIso.inv_hom_id]
    exact (quasiIsomorphisms_isMultiplicative.{t, a, m} A).id_mem _
  · rw [IsIso.hom_inv_id]
    exact (quasiIsomorphisms_isMultiplicative.{t, a, m} A).id_mem _

/-- The class of quasi-isomorphisms of the homotopy category of right differential graded
`A`-modules is stable under composition with isomorphisms on either side. -/
instance quasiIsomorphisms_respectsIso : (quasiIsomorphisms.{t, a, m} A).RespectsIso :=
  MorphismProperty.RespectsIso.mk _
    (fun e _f hf => (quasiIsomorphisms_isMultiplicative.{t, a, m} A).comp_mem _ _
      (quasiIsomorphisms_of_isIso A e.hom) hf)
    (fun e _f hf => (quasiIsomorphisms_isMultiplicative.{t, a, m} A).comp_mem _ _ hf
      (quasiIsomorphisms_of_isIso A e.hom))

/-! ### Forgetting the action -/

section Forget

variable [HasDerivedCategory.{w} (SheafOfModules.{m} R)]

/-- The functor from the homotopy category of right differential graded `A`-modules to the
derived category of sheaves of `R`-modules sending a module to its underlying complex. -/
noncomputable def homotopyForget :
    HomotopyCategory.{t, a, m} A ⥤ DerivedCategory (SheafOfModules.{m} R) :=
  CategoryTheory.Quotient.lift _ (toCochainComplex A ⋙ DerivedCategory.Q)
    (fun _ _ _ _ h => DerivedCategory.Q_map_eq_of_homotopy _ h.some.toComplexHomotopy)

/-- `homotopyForget` sends the class of a morphism `f` of right differential graded `A`-modules
to the image of its underlying morphism of complexes in the derived category. -/
@[simp]
theorem homotopyForget_quotient_map {M N : DifferentialGradedModule.{t, a, m} A} (f : M ⟶ N) :
    (homotopyForget.{w, t, a, m} A).map ((HomotopyCategory.quotient A).map f) =
      DerivedCategory.Q.map f.toHomologicalComplex := rfl

/-- An arrow of the homotopy category of right differential graded `A`-modules is a
quasi-isomorphism exactly when its image under `homotopyForget` is an isomorphism in the derived
category of sheaves of `R`-modules. -/
@[stacks 0FT4 "Qis is the class of arrows inverted by K(A) ⟶ D(R)"]
theorem quasiIsomorphisms_iff_isIso_homotopyForget {X Y : HomotopyCategory.{t, a, m} A}
    (φ : X ⟶ Y) :
    quasiIsomorphisms.{t, a, m} A φ ↔ IsIso ((homotopyForget.{w, t, a, m} A).map φ) := by
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient A).map_surjective φ
  rw [quasiIsomorphisms_quotient_map_iff]
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ f.toHomologicalComplex).symm

/-- The functor `homotopyForget` sends every quasi-isomorphism to an isomorphism. -/
theorem quasiIsomorphisms_isInvertedBy_homotopyForget :
    (quasiIsomorphisms.{t, a, m} A).IsInvertedBy (homotopyForget.{w, t, a, m} A) :=
  fun _ _ φ hφ => (quasiIsomorphisms_iff_isIso_homotopyForget.{w} A φ).mp hφ

/-- The functor from the derived category `D(A, d)` to the derived category of sheaves of
`R`-modules induced by `homotopyForget` on the localization at the quasi-isomorphisms. -/
noncomputable def derivedForget :
    derivedCategory.{t, a, m} A ⥤ DerivedCategory (SheafOfModules.{m} R) :=
  Localization.Construction.lift (homotopyForget.{w, t, a, m} A)
    (quasiIsomorphisms_isInvertedBy_homotopyForget.{w} A)

/-- The composite of the localization functor `toDerivedCategory` with `derivedForget` is
`homotopyForget`. -/
theorem toDerivedCategory_comp_derivedForget :
    toDerivedCategory.{t, a, m} A ⋙ derivedForget.{w, t, a, m} A =
      homotopyForget.{w, t, a, m} A :=
  Localization.Construction.fac _ _

end Forget

end DifferentialGradedModule

end SheafOfModules

end
