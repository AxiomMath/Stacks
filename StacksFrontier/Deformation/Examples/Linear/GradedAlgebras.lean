module

public import Mathlib.RingTheory.GradedAlgebra.TensorProduct
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Examples.Linear.ResidueFieldBase
public import StacksFrontier.Deformation.Predeformation.Basic

/-!
# Deformations of a graded algebra

Fix a commutative graded `k`-algebra `P` which is finite-dimensional in each degree. A
deformation of `P` over an object `A` of `𝒞_Λ` is a commutative graded `A`-algebra, finite
projective in each degree, together with an identification of its reduction with `P`. This file
builds the ambient category — objects are such graded algebras over varying base, morphisms are
graded ring maps exhibiting the target as an extension of scalars of the source — and the
deformation category of `P` as the category of objects over `(k, P)`.

## Main definitions

* `Deformation.Examples.ProjectiveGradedAlgebra`: a commutative graded algebra, finite
  projective in every degree, over an object of `𝒞_Λ`.
* `Deformation.Examples.ProjectiveGradedAlgebra.Hom`: its base-change morphisms.
* `Deformation.Examples.ProjectiveGradedAlgebra.instCategory`: the category structure.
* `Deformation.Examples.ProjectiveGradedAlgebra.projection`: the functor to `𝒞_Λ`.
* `Deformation.Examples.ProjectiveGradedAlgebra.specialFiber`: the object `(k, P)`.
* `Deformation.Examples.ProjectiveGradedAlgebra.deformationCategory`: the category of objects
  over `(k, P)`.

## Implementation notes

The base-change condition is expressed by `IsBaseChange` for the underlying module map. For a
graded ring map this is equivalent to the induced graded algebra map being an isomorphism after
extension of scalars, and it is the form that composes. `deformationCategory` is an abbreviation
so that the standard API of `CategoryTheory.Over` applies directly.

## References

* [Stacks Project, Tag 0D3L](https://stacks.math.columbia.edu/tag/0D3L)
-/

@[expose] public section

open CategoryTheory IsLocalRing

namespace Deformation.Examples

universe u v w m

/-- A commutative graded algebra, finite projective in every degree, over an object of the
category `𝒞_Λ` of Artinian local `Λ`-algebras with residue field `k`. -/
@[stacks 0D3L "graded_algebra_deformation_category: objects"]
public structure ProjectiveGradedAlgebra (Λ : Type u) (k : Type w)
    [CommRing Λ] [Field k] [Algebra Λ k] where
  /-- The base algebra, an object of `𝒞_Λ`. -/
  base : ArtinianLocalAlgCat.{u, v, w} Λ k
  /-- The underlying type of the algebra. -/
  carrier : Type m
  [commRing : CommRing carrier]
  [algebra : Algebra base carrier]
  /-- The grading, by submodules over the base algebra. -/
  grading : ℕ → Submodule base carrier
  [graded : GradedAlgebra grading]
  [finite : ∀ d, Module.Finite base (grading d)]
  [projective : ∀ d, Module.Projective base (grading d)]

namespace ProjectiveGradedAlgebra

attribute [instance] commRing algebra graded finite projective

/-- A base-change morphism between graded algebras over varying base algebras: a graded ring
map, semilinear over a morphism of base algebras, exhibiting the target as an extension of
scalars of the source. -/
@[ext, stacks 0D3L "graded_algebra_deformation_category: morphisms"]
public structure Hom {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (X Y : ProjectiveGradedAlgebra.{u, v, w, m} Λ k) where
  /-- The morphism of base algebras. -/
  base : X.base ⟶ Y.base
  /-- The ring map of underlying algebras. -/
  map : X.carrier →+* Y.carrier
  /-- Semilinearity along the morphism of base algebras. -/
  map_smul : ∀ (r : X.base) (x : X.carrier), map (r • x) = base.hom r • map x
  /-- The ring map respects the gradings. -/
  map_mem : ∀ (d : ℕ) (x : X.carrier), x ∈ X.grading d → map x ∈ Y.grading d
  /-- The target algebra is obtained from the source algebra by extension of scalars. -/
  isBaseChange :
    letI : Algebra X.base Y.base := base.hom.toAlgebra
    letI : Module X.base Y.carrier := Module.compHom Y.carrier base.hom.toRingHom
    letI : IsScalarTower X.base Y.base Y.carrier :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    IsBaseChange Y.base
      ({ map.toAddMonoidHom with map_smul' := map_smul } : X.carrier →ₗ[X.base] Y.carrier)

/-- The category structure on graded algebras over the algebras of `𝒞_Λ`. -/
@[stacks 0D3L "graded_algebra_deformation_category: category structure"]
public instance instCategory {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k] :
    Category (ProjectiveGradedAlgebra.{u, v, w, m} Λ k) where
  Hom := Hom
  id X :=
    { base := 𝟙 X.base
      map := RingHom.id X.carrier
      map_smul := fun _ _ ↦ rfl
      map_mem := fun _ _ h ↦ h
      isBaseChange := IsBaseChange.ofEquiv (LinearEquiv.refl X.base X.carrier) }
  comp := fun {X Y Z} f g ↦
    { base := f.base ≫ g.base
      map := g.map.comp f.map
      map_smul := fun r x ↦ by
        change g.map (f.map (r • x)) = _
        rw [f.map_smul, g.map_smul]
        rfl
      map_mem := fun d x hx ↦ g.map_mem d (f.map x) (f.map_mem d x hx)
      isBaseChange := by
        let : Algebra X.base Y.base := f.base.hom.toAlgebra
        let : Algebra Y.base Z.base := g.base.hom.toAlgebra
        let : Algebra X.base Z.base := (g.base.hom.comp f.base.hom).toAlgebra
        let : IsScalarTower X.base Y.base Z.base :=
          IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
        let : Module X.base Y.carrier := Module.compHom Y.carrier f.base.hom.toRingHom
        let : Module Y.base Z.carrier := Module.compHom Z.carrier g.base.hom.toRingHom
        let : Module X.base Z.carrier :=
          Module.compHom Z.carrier (g.base.hom.comp f.base.hom).toRingHom
        let : IsScalarTower X.base Y.base Y.carrier :=
          IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
        let : IsScalarTower Y.base Z.base Z.carrier :=
          IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
        let : IsScalarTower X.base Z.base Z.carrier :=
          IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
        let : IsScalarTower X.base Y.base Z.carrier :=
          IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
        change IsBaseChange Z.base
          (({ g.map.toAddMonoidHom with map_smul' := g.map_smul } :
            Y.carrier →ₗ[Y.base] Z.carrier).restrictScalars X.base ∘ₗ
            ({ f.map.toAddMonoidHom with map_smul' := f.map_smul } :
              X.carrier →ₗ[X.base] Y.carrier))
        exact f.isBaseChange.comp g.isBaseChange }
  id_comp := by intros; ext <;> rfl
  comp_id := by intros; ext <;> rfl
  assoc := by intros; apply Hom.ext <;> rfl

/-- The base-algebra projection. -/
@[stacks 0D3L "graded_algebra_deformation_category: projection", implicit_reducible]
public def projection {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k] :
    ProjectiveGradedAlgebra.{u, v, w, m} Λ k ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k where
  obj X := X.base
  map f := f.base
  map_id _ := rfl
  map_comp _ _ := rfl

/-- A graded algebra over `k` viewed as the distinguished special-fibre object. -/
@[stacks 0D3L "graded_algebra_deformation_category: special fiber"]
public noncomputable def specialFiber {Λ : Type u} {k : Type w}
    [CommRing Λ] [Field k] [Algebra Λ k]
    (P : Type m) [CommRing P] [Algebra k P]
    (grading : ℕ → Submodule k P) [GradedAlgebra grading]
    [∀ d, Module.Finite k (grading d)] : ProjectiveGradedAlgebra.{u, w, w, m} Λ k where
  base := residueFieldBase Λ k
  carrier := P
  grading := grading

/-- Deformations of a fixed graded `k`-algebra. -/
@[stacks 0D3L "graded_algebra_deformation_category",
  stacks 0D3L "graded_algebra_deformation_category: deformation category"]
public abbrev deformationCategory {Λ : Type u} {k : Type w}
    [CommRing Λ] [Field k] [Algebra Λ k]
    (P : Type m) [CommRing P] [Algebra k P]
    (grading : ℕ → Submodule k P) [GradedAlgebra grading]
    [∀ d, Module.Finite k (grading d)] :=
  Over (specialFiber (Λ := Λ) P grading)

end ProjectiveGradedAlgebra

end Deformation.Examples
