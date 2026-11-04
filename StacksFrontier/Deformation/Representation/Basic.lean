module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.IsTensorProduct
public import StacksFrontier.Deformation.Examples.Geometric.Base
public import StacksFrontier.Deformation.RestrictScalars
public import StacksFrontier.Deformation.Terminal

/-!
# Deformations of a representation of a group (Stacks 0D3J)

Let `Γ` be a group. The category `ℱ` of Stacks Project, Tag 0D3J has as objects the
triples `(A, M, ρ)` consisting of an object `A` of `𝒞_Λ`, a finite projective `A`-module
`M` and a homomorphism `ρ : Γ → GL_A(M)`; a morphism `(B, N, τ) ⟶ (A, M, ρ)` is a morphism
`f : B ⟶ A` of `𝒞_Λ` together with an `f`-semilinear `Γ`-equivariant map `N → M` inducing
an isomorphism `N ⊗_{B, f} A ≅ M`. The functor `ℱ ⥤ 𝒞_Λ` remembers only the coefficient
algebra.

Given a finite-dimensional representation `ρ₀ : Γ → GL_k(V)` over the residue field, the
object `x₀ = (k, V, ρ₀)` lies in the fibre over `k`, and the deformation category of
`(V, ρ₀)` is the slice category `ℱ_{x₀}` of objects over `x₀`.

## Main definitions

* `Deformation.RepresentationCategory`: the category `ℱ`, with its morphisms and category
  structure.
* `Deformation.representationProjection`: the functor `ℱ ⥤ 𝒞_Λ`.
* `Deformation.RepresentationCategory.specialFiber`: the object `x₀ = (k, V, ρ₀)`.
* `Deformation.RepresentationCategory.deformationCategory`: the slice category `ℱ_{x₀}`.
* `Deformation.deformationCategoryProjection`: its structure functor to `𝒞_Λ`.

## Implementation notes

The condition that a semilinear module map induce an isomorphism after extension of
scalars is expressed by Mathlib's `IsBaseChange`. This is equivalent to the displayed
isomorphism `N ⊗_B A ≅ M`, but is substantially better behaved under composition.

The module universe is kept independent of the ring universe, as in Stacks, and the
special fibre uses the object of `𝒞_Λ` with underlying ring exactly `k`, so that the
`k`-module `V` is literally a module over the coefficient algebra of `x₀`.

## References

* [Stacks Project, Tag 0D3J](https://stacks.math.columbia.edu/tag/0D3J)
-/

@[expose] public section

open CategoryTheory

namespace Deformation

universe u v w m x

/-- A finite projective representation of `Γ` over an Artinian local `Λ`-algebra with
residue field `k`. -/
@[stacks 0D3J "second presentation: representation_category, objects"]
structure RepresentationCategory.{u', v', w', m', x'}
    (Λ : Type u') (k : Type w') (Γ : Type x') [CommRing Λ] [Field k] [Algebra Λ k]
    [Group Γ] where
  /-- The coefficient algebra. -/
  base : ArtinianLocalAlgCat.{u', v', w'} Λ k
  /-- The underlying module. -/
  carrier : Type m'
  [addCommGroup : AddCommGroup carrier]
  [module : Module base carrier]
  [finite : Module.Finite base carrier]
  [projective : Module.Projective base carrier]
  /-- The group action. -/
  action : Representation base Γ carrier

namespace RepresentationCategory

attribute [instance] addCommGroup module finite projective

/-- A morphism of finite projective representations with varying coefficient ring. -/
@[ext, stacks 0D3J "second presentation: representation_category, morphisms"]
structure Hom {Λ : Type u} {k : Type w} {Γ : Type x} [CommRing Λ] [Field k] [Algebra Λ k]
    [Group Γ] (X Y : RepresentationCategory.{u, v, w, m, x} Λ k Γ) where
  /-- The map of coefficient algebras. -/
  base : X.base ⟶ Y.base
  /-- The semilinear map of underlying modules. -/
  map : X.carrier →+ Y.carrier
  /-- Semilinearity along the map of coefficient algebras. -/
  map_smul : ∀ (r : X.base) (xx : X.carrier),
    map (r • xx) = base.hom r • map xx
  /-- Equivariance for the group actions. -/
  equivariant : ∀ (γ : Γ) (xx : X.carrier),
    map (X.action γ xx) = Y.action γ (map xx)
  /-- The module over the target is obtained from the source module by extension of
  scalars. -/
  isBaseChange :
    letI : Algebra X.base Y.base := base.hom.toRingHom.toAlgebra
    letI : Module X.base Y.carrier := Module.compHom Y.carrier base.hom.toRingHom
    letI : IsScalarTower X.base Y.base Y.carrier :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    IsBaseChange Y.base (restrictAddHom base.hom.toRingHom map map_smul)

/-- A morphism of the category of finite projective representations, presented by a base
change equivalence instead of by `IsBaseChange`. -/
noncomputable def Hom.ofEquiv {Λ : Type u} {k : Type w} {Γ : Type x} [CommRing Λ]
    [Field k] [Algebra Λ k] [Group Γ]
    {X Y : RepresentationCategory.{u, v, w, m, x} Λ k Γ} (base : X.base ⟶ Y.base)
    (map : X.carrier →+ Y.carrier)
    (map_smul : ∀ (r : X.base) (xx : X.carrier), map (r • xx) = base.hom r • map xx)
    (equivariant : ∀ (γ : Γ) (xx : X.carrier),
      map (X.action γ xx) = Y.action γ (map xx))
    (e : letI : Algebra X.base Y.base := base.hom.toRingHom.toAlgebra
      TensorProduct X.base Y.base X.carrier ≃ₗ[Y.base] Y.carrier)
    (he : letI : Algebra X.base Y.base := base.hom.toRingHom.toAlgebra
      ∀ xx : X.carrier, e ((1 : Y.base) ⊗ₜ[X.base] xx) = map xx) :
    Hom X Y where
  base := base
  map := map
  map_smul := map_smul
  equivariant := equivariant
  isBaseChange := by
    let : Algebra X.base Y.base := base.hom.toRingHom.toAlgebra
    let : Module X.base Y.carrier := Module.compHom Y.carrier base.hom.toRingHom
    let : IsScalarTower X.base Y.base Y.carrier :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    exact IsBaseChange.of_equiv e he

/-- The category structure on finite projective representations with varying coefficient
algebra. -/
@[stacks 0D3J "second presentation: representation_category"]
instance instCategory {Λ : Type u} {k : Type w} {Γ : Type x} [CommRing Λ] [Field k]
    [Algebra Λ k] [Group Γ] : Category (RepresentationCategory.{u, v, w, m, x} Λ k Γ) where
  Hom := Hom
  id X :=
    { base := 𝟙 X.base
      map :=
        { toFun := id
          map_add' := fun _ _ ↦ rfl
          map_zero' := rfl }
      map_smul := fun _ _ ↦ rfl
      equivariant := fun _ _ ↦ rfl
      isBaseChange := IsBaseChange.ofEquiv (LinearEquiv.refl X.base X.carrier) }
  comp := fun {X Y Z} f g ↦
    { base := f.base ≫ g.base
      map := g.map.comp f.map
      map_smul := fun r xx ↦ by
        change g.map (f.map (r • xx)) = _
        rw [f.map_smul, g.map_smul]
        rfl
      equivariant := fun γ xx ↦ by
        change g.map (f.map (X.action γ xx)) = Z.action γ (g.map (f.map xx))
        rw [f.equivariant, g.equivariant]
      isBaseChange := by
        let : Algebra X.base Y.base := f.base.hom.toRingHom.toAlgebra
        let : Algebra Y.base Z.base := g.base.hom.toRingHom.toAlgebra
        let : Algebra X.base Z.base :=
          (g.base.hom.comp f.base.hom).toRingHom.toAlgebra
        let : IsScalarTower X.base Y.base Z.base :=
          IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
        let : Module X.base Y.carrier := Module.compHom Y.carrier f.base.hom.toRingHom
        let : IsScalarTower X.base Y.base Y.carrier :=
          IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
        let : Module Y.base Z.carrier := Module.compHom Z.carrier g.base.hom.toRingHom
        let : IsScalarTower Y.base Z.base Z.carrier :=
          IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
        let : Module X.base Z.carrier :=
          Module.compHom Z.carrier (g.base.hom.comp f.base.hom).toRingHom
        let : IsScalarTower X.base Y.base Z.carrier :=
          IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
        let : IsScalarTower X.base Z.base Z.carrier :=
          IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
        have hf : IsBaseChange Y.base
            (restrictAddHom f.base.hom.toRingHom f.map f.map_smul) := f.isBaseChange
        have hg : IsBaseChange Z.base
            (restrictAddHom g.base.hom.toRingHom g.map g.map_smul) := g.isBaseChange
        change IsBaseChange Z.base
          ((restrictAddHom g.base.hom.toRingHom g.map g.map_smul).restrictScalars X.base ∘ₗ
            restrictAddHom f.base.hom.toRingHom f.map f.map_smul)
        exact hf.comp hg }
  id_comp := by intros; ext <;> rfl
  comp_id := by intros; ext <;> rfl
  assoc := by
    intro W X Y Z f g h
    ext xx <;> simp

end RepresentationCategory

/-- The coefficient algebra underlying a finite projective representation, as a
functor. -/
@[stacks 0D3J "second presentation: representation_category"]
def representationProjection {Λ : Type u} {k : Type w} {Γ : Type x} [CommRing Λ]
    [Field k] [Algebra Λ k] [Group Γ] :
    RepresentationCategory.{u, v, w, m, x} Λ k Γ ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k where
  obj X := X.base
  map f := f.base
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The image of a representation under `representationProjection` is its coefficient algebra. -/
@[simp]
theorem representationProjection_obj {Λ : Type u} {k : Type w} {Γ : Type x} [CommRing Λ]
    [Field k] [Algebra Λ k] [Group Γ] (X : RepresentationCategory.{u, v, w, m, x} Λ k Γ) :
    representationProjection.obj X = X.base := rfl

/-- The image of a morphism under `representationProjection` is its map of coefficient
algebras. -/
@[simp]
theorem representationProjection_map {Λ : Type u} {k : Type w} {Γ : Type x} [CommRing Λ]
    [Field k] [Algebra Λ k] [Group Γ]
    {X Y : RepresentationCategory.{u, v, w, m, x} Λ k Γ} (f : X ⟶ Y) :
    representationProjection.map f = (f : RepresentationCategory.Hom X Y).base := rfl

namespace RepresentationCategory

/-- The representation `(V, ρ₀)` over the residue field `k`, viewed as the special-fibre
object of the category `ℱ`. -/
@[stacks 0D3J "second presentation: representation_deformation_category"]
noncomputable def specialFiber {Λ : Type u} {k : Type w} {Γ : Type x} [CommRing Λ]
    [Field k] [Algebra Λ k] [Group Γ] (V : Type m) [AddCommGroup V] [Module k V]
    [Module.Finite k V] (ρ₀ : Representation k Γ V) :
    RepresentationCategory.{u, w, w, m, x} Λ k Γ where
  base := Examples.residueFieldBase Λ k
  carrier := V
  action := ρ₀

/-- The category of deformations of a finite-dimensional representation of `Γ`. -/
@[stacks 0D3J "second presentation: representation_deformation_category"]
abbrev deformationCategory {Λ : Type u} {k : Type w} {Γ : Type x} [CommRing Λ] [Field k]
    [Algebra Λ k] [Group Γ] (V : Type m) [AddCommGroup V] [Module k V]
    [Module.Finite k V] (ρ₀ : Representation k Γ V) :=
  Over (specialFiber (Λ := Λ) V ρ₀)

end RepresentationCategory

/-- The coefficient algebra of a deformation of `ρ₀`, as a functor from the deformation
category of `ρ₀` to `𝒞_Λ`. -/
@[stacks 0D3J "second presentation: representation_deformation_category"]
noncomputable def deformationCategoryProjection {Λ : Type u} {k : Type w} {Γ : Type x}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ] (V : Type m) [AddCommGroup V]
    [Module k V] [Module.Finite k V] (ρ₀ : Representation k Γ V) :
    RepresentationCategory.deformationCategory (Λ := Λ) V ρ₀ ⥤
      ArtinianLocalAlgCat.{u, w, w} Λ k :=
  Over.forget _ ⋙ representationProjection

end Deformation

end
