module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LeftDualRetract

/-!
# An exact functor on a morphism of the derived category written as a left fraction

Let `R : A ⥤ B` be an exact additive functor of abelian categories with derived categories, and
let `α : Q(E) ⟶ Q(F)` be a morphism of `D(A)` written as a left fraction `Q(γ) ∘ Q(f)⁻¹` for
maps of complexes `γ : E ⟶ G` and `f : F ⟶ G` with `Q(f)` invertible. Then a map of complexes
`β : R(E) ⟶ R(F)` induces `R(α)` — in the precise sense that the square formed with
`CategoryTheory.Functor.mapDerivedCategoryFactors` commutes — as soon as `β ∘ R(f)` and `R(γ)`
agree in the derived category of `B`, for instance because they are homotopic.

This is how a *local* chain-level representative of a derived morphism, produced by a lifting
statement at the level of complexes such as [Stacks, Tag 08FQ], is converted into the derived
statement that the morphism becomes the image of a map of complexes, which is the form
[Stacks, Tag 08FR] is stated in and the form its consumers use.

Nothing here is a clause of a tag: it is a lemma about derived categories with no site and no
space in it.

## Main results

* `CategoryTheory.Functor.mapDerivedCategory_map_eq_of_Q_eq`: the statement above. It is declared
  in `StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LeftDualRetract`, which this
  module imports; it is not restated here.
* `CategoryTheory.Functor.Q_map_eq_of_mapDerivedCategory_map_eq`: its converse — the square
  determines the derived-category identity it was built from, so the two conditions on `β` are
  equivalent. This is what lets a chain-level representative be *transported*: the square at one
  place is turned back into a derived-category identity between maps of complexes, the identity is
  pushed along a functor, and the square is rebuilt at the other place.
* `CategoryTheory.Functor.Q_map_mapHomologicalComplex_eq_of_Q_map_eq`: an exact additive functor
  preserves equality in the derived category of two maps of complexes. Such maps need not be
  homotopic, so this is not `CategoryTheory.Functor.mapHomotopy`; it is naturality of
  `mapDerivedCategoryFactors` together with the invertibility of its components.

## Implementation notes

The proof is the calculus of left fractions and nothing else: `R` carries the fraction to a
fraction, because `Q(R(f))` is invertible once `Q(f)` is — `R` being exact it preserves
quasi-isomorphisms — and `mapDerivedCategoryFactors` is natural, so both sides are determined by
their composites with `Q(R(f))`.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe w₁ w₂ v₁ v₂ u₁ u₂

/-- **The converse of `CategoryTheory.Functor.mapDerivedCategory_map_eq_of_Q_eq`.** If `β`
induces `R(α)` through the comparison of `R`, and `α = Q(γ) ∘ Q(f)⁻¹`, then `β ∘ R(f)` and `R(γ)`
agree in the derived category. So the square and the derived-category identity are equivalent
conditions on `β`, which is what allows the square to be transported along a functor. -/
theorem CategoryTheory.Functor.Q_map_eq_of_mapDerivedCategory_map_eq {A : Type u₁}
    [Category.{v₁} A] [Abelian A]
    [HasDerivedCategory.{w₁} A] {B : Type u₂} [Category.{v₂} B] [Abelian B]
    [HasDerivedCategory.{w₂} B] (R : A ⥤ B) [R.Additive] [PreservesFiniteLimits R]
    [PreservesFiniteColimits R] {E F G : CochainComplex A ℤ}
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F) (γ : E ⟶ G) (f : F ⟶ G)
    (hf : IsIso (DerivedCategory.Q.map f))
    (hαfac : α = DerivedCategory.Q.map γ ≫ CategoryTheory.inv (DerivedCategory.Q.map f))
    (β : (R.mapHomologicalComplex (ComplexShape.up ℤ)).obj E ⟶
      (R.mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
    (h : R.mapDerivedCategory.map α ≫ R.mapDerivedCategoryFactors.hom.app F =
      R.mapDerivedCategoryFactors.hom.app E ≫ DerivedCategory.Q.map β) :
    DerivedCategory.Q.map (β ≫ (R.mapHomologicalComplex (ComplexShape.up ℤ)).map f) =
      DerivedCategory.Q.map ((R.mapHomologicalComplex (ComplexShape.up ℤ)).map γ) := by
  have hiso : IsIso (R.mapDerivedCategoryFactors.hom.app E) := inferInstance
  have hαf : α ≫ DerivedCategory.Q.map f = DerivedCategory.Q.map γ := by
    rw [hαfac, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hnatf := R.mapDerivedCategoryFactors_hom_naturality f
  have hnatγ := R.mapDerivedCategoryFactors_hom_naturality γ
  refine (cancel_epi (R.mapDerivedCategoryFactors.hom.app E)).1 ?_
  rw [DerivedCategory.Q.map_comp, ← Category.assoc, ← h, Category.assoc, ← hnatf,
    ← Category.assoc, ← R.mapDerivedCategory.map_comp, hαf, hnatγ]

/-- **An exact additive functor preserves equality in the derived category of two maps of
complexes.** The two maps need not be homotopic — equality in `D(A)` is weaker — so this is not
the image of a homotopy; it is naturality of
`CategoryTheory.Functor.mapDerivedCategoryFactors` together with the invertibility of its
components. -/
theorem CategoryTheory.Functor.Q_map_mapHomologicalComplex_eq_of_Q_map_eq {A : Type u₁}
    [Category.{v₁} A] [Abelian A]
    [HasDerivedCategory.{w₁} A] {B : Type u₂} [Category.{v₂} B] [Abelian B]
    [HasDerivedCategory.{w₂} B] (R : A ⥤ B) [R.Additive] [PreservesFiniteLimits R]
    [PreservesFiniteColimits R] {P P' : CochainComplex A ℤ} {x y : P ⟶ P'}
    (h : DerivedCategory.Q.map x = DerivedCategory.Q.map y) :
    DerivedCategory.Q.map ((R.mapHomologicalComplex (ComplexShape.up ℤ)).map x) =
      DerivedCategory.Q.map ((R.mapHomologicalComplex (ComplexShape.up ℤ)).map y) := by
  have hiso : IsIso (R.mapDerivedCategoryFactors.hom.app P) := inferInstance
  have hx := R.mapDerivedCategoryFactors_hom_naturality x
  have hy := R.mapDerivedCategoryFactors_hom_naturality y
  refine (cancel_epi (R.mapDerivedCategoryFactors.hom.app P)).1 ?_
  rw [← hx, ← hy, h]

end
