module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.IsTensorProduct
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Examples.Linear.ResidueFieldBase
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.RestrictScalars

/-!
# Deformations of a representation of a group

Fix a group `Γ` and a finite-dimensional representation `ρ₀` of `Γ` on a `k`-vector space `V`.
A deformation of `ρ₀` over an object `A` of `𝒞_Λ` is a finite projective `A`-module with a
`Γ`-action, together with an identification of its special fibre with `(V, ρ₀)`. This file
builds the ambient category — objects are finite projective representations of `Γ` with varying
coefficient algebra, morphisms are equivariant semilinear maps exhibiting the target module as
an extension of scalars of the source — and the deformation category of `ρ₀` as the category of
objects over `(k, V, ρ₀)`.

## Main definitions

* `Deformation.Examples.FiniteProjectiveRepresentation`: a finite projective representation of
  `Γ` over an object of `𝒞_Λ`.
* `Deformation.Examples.FiniteProjectiveRepresentation.Hom`: its morphisms.
* `Deformation.Examples.FiniteProjectiveRepresentation.instCategory`: the category structure.
* `Deformation.Examples.FiniteProjectiveRepresentation.specialFiber`: the object `(k, V, ρ₀)`.
* `Deformation.Examples.FiniteProjectiveRepresentation.deformationCategory`: the category of
  objects over `(k, V, ρ₀)`.

## Implementation notes

The condition that the semilinear module map induce an isomorphism after tensoring is expressed
by Mathlib's `IsBaseChange` rather than by a displayed isomorphism `M ⊗_A B ≃ N`. The two are
equivalent, but `IsBaseChange` composes, which is what makes the category structure available
without transporting an explicit equivalence through each composite.

The distinguished coefficient algebra is `Deformation.Examples.residueFieldBase`, the object of
`𝒞_Λ` whose carrier is `k` itself; the deformation category is an abbreviation so clients can
use the standard API of `CategoryTheory.Over` directly.

## References

* [Stacks Project, Tag 0D3J](https://stacks.math.columbia.edu/tag/0D3J)
-/

@[expose] public section

open CategoryTheory

namespace Deformation.Examples

universe u v w m

/-- A finite projective representation of `Γ` over an Artinian local `Λ`-algebra with residue
field `k`. -/
@[stacks 0D3J "representation_category: objects"]
public structure FiniteProjectiveRepresentation
    (Λ : Type u) (k : Type w) (Γ : Type*) [CommRing Λ] [Field k] [Algebra Λ k]
    [Group Γ] where
  /-- The coefficient algebra, an object of `𝒞_Λ`. -/
  base : ArtinianLocalAlgCat.{u, v, w} Λ k
  /-- The underlying module. -/
  carrier : Type m
  [addCommGroup : AddCommGroup carrier]
  [module : Module base carrier]
  [finite : Module.Finite base carrier]
  [projective : Module.Projective base carrier]
  /-- The group action. -/
  action : Representation base Γ carrier

namespace FiniteProjectiveRepresentation

attribute [instance] addCommGroup module finite projective

/-- A morphism of finite projective representations with varying coefficient ring. -/
@[ext, stacks 0D3J "representation_category: morphisms"]
public structure Hom
    {Λ : Type u} {k : Type w} {Γ : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    [Group Γ] (X Y : FiniteProjectiveRepresentation.{u, v, w, m} Λ k Γ) where
  /-- The map of coefficient algebras. -/
  base : X.base ⟶ Y.base
  /-- The semilinear map of underlying modules. -/
  map : X.carrier →+ Y.carrier
  /-- Semilinearity along the map of coefficient algebras. -/
  map_smul : ∀ (r : X.base) (x : X.carrier),
    map (r • x) = base.hom r • map x
  /-- Equivariance for the group actions. -/
  equivariant : ∀ (γ : Γ) (x : X.carrier), map (X.action γ x) = Y.action γ (map x)
  /-- The module over the target is obtained from the source module by extension of scalars. -/
  isBaseChange :
    letI : Algebra X.base Y.base := base.hom.toAlgebra
    letI : Module X.base Y.carrier := Module.compHom Y.carrier base.hom.toRingHom
    letI : IsScalarTower X.base Y.base Y.carrier :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    IsBaseChange Y.base (restrictAddHom base.hom.toRingHom map map_smul)

/-- The category structure on finite projective representations with varying coefficient
algebra. -/
@[stacks 0D3J "representation_category"]
public instance instCategory
    {Λ : Type u} {k : Type w} {Γ : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    [Group Γ] : Category (FiniteProjectiveRepresentation.{u, v, w, m} Λ k Γ) where
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
      map_smul := fun r x ↦ by
        change g.map (f.map (r • x)) = _
        rw [f.map_smul, g.map_smul]
        rfl
      equivariant := fun γ x ↦ by
        change g.map (f.map (X.action γ x)) = Z.action γ (g.map (f.map x))
        rw [f.equivariant, g.equivariant]
      isBaseChange := by
        let : Algebra X.base Y.base := f.base.hom.toAlgebra
        let : Algebra Y.base Z.base := g.base.hom.toAlgebra
        let : Algebra X.base Z.base :=
          (g.base.hom.comp f.base.hom).toAlgebra
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
    ext x <;> simp

/-- The representation `(V, ρ₀)` over `k`, viewed as the special-fibre object. -/
@[stacks 0D3J "representation_deformation_category"]
public noncomputable def specialFiber
    {Λ : Type u} {k : Type w} {Γ : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    [Group Γ] (V : Type m) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V) : FiniteProjectiveRepresentation.{u, w, w, m} Λ k Γ where
  base := residueFieldBase Λ k
  carrier := V
  action := ρ₀

/-- The category of deformations of a finite-dimensional representation of `Γ`. -/
@[stacks 0D3J "representation_deformation_category"]
public abbrev deformationCategory
    {Λ : Type u} {k : Type w} {Γ : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    [Group Γ] (V : Type m) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V) := Over (specialFiber (Λ := Λ) V ρ₀)

end FiniteProjectiveRepresentation

end Deformation.Examples
