module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Finiteness.Small
public import Mathlib.RingTheory.LocalRing.Module
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Examples.Linear.ResidueFieldBase
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.Smallness

/-!
# Deformations of a finite projective module

Fix a finite-dimensional vector space `V` over `k`. A deformation of `V` over an object `A` of
`𝒞_Λ` is a finite projective `A`-module `M` together with an identification of `M ⊗_A k` with
`V`. This file builds the ambient category: its objects are pairs `(A, M)` with `A` in `𝒞_Λ`
and `M` a finite projective `A`-module, and a morphism `(A, M) → (B, N)` is a morphism
`A → B` of `𝒞_Λ` together with a semilinear map `M → N` exhibiting `N` as `M ⊗_A B`. The
deformation category of `V` is then the category of objects over the pair `(k, V)`.

## Main definitions

* `Deformation.Examples.FiniteProjectiveModule`: a finite projective module over an object
  of `𝒞_Λ`.
* `Deformation.Examples.FiniteProjectiveModule.Hom`: a base-change morphism between two such.
* `Deformation.Examples.FiniteProjectiveModule.Family`: the category structure on these
  objects together with its projection to `𝒞_Λ` and the formulas computing both.
* `Deformation.Examples.FiniteProjectiveModule.family`: the chosen such family.
* `Deformation.Examples.FiniteProjectiveModule.specialFiber`: the object `(k, V)`.
* `Deformation.Examples.FiniteProjectiveModule.deformationCategory`: the category of objects
  over `(k, V)`.

## Main results

* `Deformation.Examples.FiniteProjectiveModule.Hom.ext_of_base_eq`: two morphisms agreeing on
  base morphisms and pointwise on modules are equal.
* `Deformation.Examples.FiniteProjectiveModule.small_residueField_of_nontrivial`: a nontrivial
  object forces `k` to be small in the module universe.
* `Deformation.Examples.FiniteProjectiveModule.small_carrier`: the module of an object is small
  in the universe of `k`.
* `Deformation.Examples.FiniteProjectiveModule.nonempty_family`: the category structure and
  projection exist, with the stated formulas.
* `Deformation.Examples.FiniteProjectiveModule.Family.projection_map_eq`: the projection of a
  family computes a morphism's base morphism.

## Implementation notes

The base-change condition on a morphism is recorded as the existence of a linear equivalence
`M ⊗_A B ≃ₗ[B] N` whose value on `1 ⊗ m` is the given semilinear map, which is exactly the
isomorphism induced by that map. The category structure, its projection, and the formulas
computing identities, composition and the projection are bundled into one structure
`Family` rather than installed as a global instance: the objects form a type whose morphisms
have to be transported across the `Algebra` instance induced by each base morphism, and
bundling keeps those transports inside the existence proof. Clients use `family`, and read
off identities, composition and the projection through its fields.

The module carrier lives in a universe independent of the base ring, so that `(k, V)` can be
formed for a `V` of any size. The special-fibre object is the pair with underlying ring exactly
`k` and underlying module exactly `V`, built on `Deformation.Examples.residueFieldBase`.

## References

* [Stacks Project, Tag 0D3I](https://stacks.math.columbia.edu/tag/0D3I)
-/

@[expose] public section

open CategoryTheory

namespace Deformation.Examples

universe u v w t

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- A finite projective module over an Artinian local `Λ`-algebra with residue field `k`. -/
public structure FiniteProjectiveModule where
  /-- The base algebra, an object of `𝒞_Λ`. -/
  base : ArtinianLocalAlgCat.{u, v, w} Λ k
  /-- The underlying type of the module. -/
  carrier : Type t
  [addCommGroup : AddCommGroup carrier]
  [module : Module base carrier]
  [finite : Module.Finite base carrier]
  [projective : Module.Projective base carrier]

namespace FiniteProjectiveModule

attribute [instance] addCommGroup module finite projective

/-- A morphism of finite projective modules with varying base: a morphism of base algebras
together with a semilinear map of modules whose induced map after extension of scalars is an
isomorphism. -/
public structure Hom (X Y : FiniteProjectiveModule.{u, v, w, t} (Λ := Λ) (k := k)) where
  /-- The morphism of base algebras. -/
  base : X.base ⟶ Y.base
  /-- The semilinear map of underlying modules. -/
  linear : X.carrier →ₛₗ[base.hom.toRingHom] Y.carrier
  /-- The target module is obtained from the source module by extension of scalars, and the
  semilinear map is the induced map on `1 ⊗ m`. -/
  baseChange :
    letI : Algebra X.base Y.base := base.hom.toRingHom.toAlgebra;
    ∃ e : (TensorProduct X.base Y.base X.carrier) ≃ₗ[Y.base] Y.carrier,
      ∀ m : X.carrier, e (TensorProduct.tmul X.base (1 : Y.base) m) = linear m

/-- Two morphisms of finite projective modules are equal as soon as their base morphisms are
equal and their semilinear maps agree pointwise. The base-change condition is a proposition, so
it imposes nothing further. -/
public theorem Hom.ext_of_base_eq
    {X Y : FiniteProjectiveModule.{u, v, w, t} (Λ := Λ) (k := k)}
    (f g : FiniteProjectiveModule.Hom X Y) (hb : f.base = g.base)
    (hl : ∀ m, f.linear m = g.linear m) : f = g := by
  cases f with
  | mk fb fl fc =>
    cases g with
    | mk gb gl gc =>
      dsimp at hb hl
      cases hb
      have hlin : fl = gl := by ext m; exact hl m
      cases hlin
      rfl

/-- A nontrivial finite projective module over an object of `𝒞_Λ` forces the residue field `k`
to be small in the module's universe: the module is free over the local base with a nonempty
basis, so the base ring injects into it, and `k` is a quotient of the base ring. -/
public theorem small_residueField_of_nontrivial
    (X : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k)) [Nontrivial X.carrier] :
    Small.{t} k := by
  have : Module.Free X.base X.carrier := Module.free_of_flat_of_isLocalRing
  let b := Module.Free.chooseBasis X.base X.carrier
  have : Finite (Module.Free.ChooseBasisIndex X.base X.carrier) :=
    Module.Finite.finite_basis b
  obtain ⟨i⟩ : Nonempty (Module.Free.ChooseBasisIndex X.base X.carrier) := by
    by_contra h
    have : IsEmpty (Module.Free.ChooseBasisIndex X.base X.carrier) := not_nonempty_iff.mp h
    have : Subsingleton X.carrier := b.repr.toEquiv.subsingleton
    exact not_nontrivial X.carrier ‹_›
  have : Small.{t} X.base := small_of_injective (f := fun a : X.base => a • b i) (by
    intro a a' haa
    simpa using congrArg (fun x => b.repr x i) haa)
  have : Small.{t} (IsLocalRing.ResidueField X.base) :=
    small_of_surjective (f := IsLocalRing.residue X.base) IsLocalRing.residue_surjective
  exact small_map X.base.residueEquiv.toEquiv.symm

/-- The carrier of a finite projective module over an object of `𝒞_Λ` is small in the universe
of the residue field: the base ring is small there, and the module is finite over it. -/
public theorem small_carrier (X : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k)) :
    Small.{w, t} X.carrier := by
  let : Small.{w} k := UnivLE.small k
  let : Small.{w} X.base := ArtinianLocalAlgCat.small X.base
  exact Module.Finite.small.{w, w, t} X.base X.carrier

/-- The pair `(k, V)` consisting of the residue field and a finite-dimensional `k`-vector
space: the special-fibre object whose deformations are studied. -/
@[stacks 0D3I "finite_projective_deformation_category"]
public noncomputable def specialFiber (V : Type t) [AddCommGroup V] [Module k V]
    [Module.Finite k V] : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k) where
  base := residueFieldBase Λ k
  carrier := V

/-- The category of finite projective modules over the algebras of `𝒞_Λ`, together with its
projection to `𝒞_Λ` and the formulas computing identities, composition and the projection in
terms of `FiniteProjectiveModule.Hom`. -/
public structure Family where
  /-- The category structure on the objects. -/
  category : Category.{max w t} (FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k))
  /-- Its morphisms are the base-change morphisms. -/
  homEquiv :
    letI := category
    ∀ X Y : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k),
      (X ⟶ Y) ≃ FiniteProjectiveModule.Hom X Y
  /-- The identity has identity base morphism. -/
  id_base :
    letI := category
    ∀ X : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k),
      (homEquiv X X (𝟙 X)).base = 𝟙 X.base
  /-- The identity has identity semilinear map. -/
  id_linear :
    letI := category
    ∀ (X : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k))
      (m : X.carrier), (homEquiv X X (𝟙 X)).linear m = m
  /-- Composition composes base morphisms. -/
  comp_base :
    letI := category
    ∀ {X Y Z : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k)}
      (f : X ⟶ Y) (g : Y ⟶ Z),
      (homEquiv X Z (f ≫ g)).base = (homEquiv X Y f).base ≫ (homEquiv Y Z g).base
  /-- Composition composes semilinear maps. -/
  comp_linear :
    letI := category
    ∀ {X Y Z : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k)}
      (f : X ⟶ Y) (g : Y ⟶ Z) (m : X.carrier),
      (homEquiv X Z (f ≫ g)).linear m =
        (homEquiv Y Z g).linear ((homEquiv X Y f).linear m)
  /-- The projection to `𝒞_Λ`. -/
  projection :
    letI := category
    FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k) ⥤
      ArtinianLocalAlgCat.{u, w, w} Λ k
  /-- The projection forgets the module. -/
  projection_obj :
    letI := category
    ∀ X : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k),
      projection.obj X = X.base
  /-- The projection takes a morphism to its base morphism. -/
  projection_map :
    letI := category
    ∀ {X Y : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k)} (f : X ⟶ Y),
      eqToHom (projection_obj X).symm ≫ projection.map f ≫
        eqToHom (projection_obj Y) = (homEquiv X Y f).base

/-- The category of finite projective modules over the algebras of `𝒞_Λ` exists, with the
morphisms, identities, composition and projection stated in `Family`. -/
public theorem nonempty_family :
    Nonempty (Family.{u, w, t} (Λ := Λ) (k := k)) := by
  classical
  let : Quiver (FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k)) :=
    ⟨FiniteProjectiveModule.Hom⟩
  let : CategoryStruct (FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k)) := {
    id X :=
      { base := 𝟙 X.base
        linear := LinearMap.id
        baseChange := by
          let : Algebra X.base X.base := (AlgHom.id X.base X.base).toRingHom.toAlgebra
          refine ⟨TensorProduct.lid X.base X.carrier, ?_⟩
          intro m
          change (TensorProduct.lid X.base X.carrier) (1 ⊗ₜ[X.base] m) = m
          simp }
    comp {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z) :=
      { base := f.base ≫ g.base
        linear := g.linear.comp f.linear
        baseChange := by
          let : Algebra X.base Y.base := f.base.hom.toRingHom.toAlgebra
          let : Algebra Y.base Z.base := g.base.hom.toRingHom.toAlgebra
          let : Algebra X.base Z.base := (f.base ≫ g.base).hom.toRingHom.toAlgebra
          let : IsScalarTower X.base Y.base Z.base := ⟨by
            intro x y z
            simp only [Algebra.smul_def, map_mul]
            rw [show algebraMap X.base Z.base x =
              algebraMap Y.base Z.base (algebraMap X.base Y.base x) by rfl]
            ac_rfl⟩
          rcases f.baseChange with ⟨e₁, he₁⟩
          rcases g.baseChange with ⟨e₂, he₂⟩
          let e₁' := LinearEquiv.baseChange Y.base Z.base _ _ e₁
          refine ⟨((TensorProduct.AlgebraTensorModule.cancelBaseChange
            X.base Y.base Z.base Z.base X.carrier).symm.trans e₁').trans e₂, ?_⟩
          intro m
          simp [e₁', he₁, he₂]
          rfl }
  }
  let : Category.{max w t} (FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k)) := {
    id_comp f := Hom.ext_of_base_eq _ _ (Category.id_comp f.base) fun _ => rfl
    comp_id f := Hom.ext_of_base_eq _ _ (Category.comp_id f.base) fun _ => rfl
    assoc f g h := Hom.ext_of_base_eq _ _ (Category.assoc f.base g.base h.base) fun _ => rfl
  }
  let homEquiv : ∀ X Y : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k),
      (X ⟶ Y) ≃ FiniteProjectiveModule.Hom X Y := fun X Y => Equiv.refl _
  let projection : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k) ⥤
      ArtinianLocalAlgCat.{u, w, w} Λ k := {
    obj X := X.base
    map f := f.base
    map_id := by intro X; rfl
    map_comp := by intro X Y Z f g; rfl
  }
  refine ⟨{
    category := inferInstance
    homEquiv := homEquiv
    id_base := ?_
    id_linear := ?_
    comp_base := ?_
    comp_linear := ?_
    projection := projection
    projection_obj := ?_
    projection_map := ?_ }⟩
  all_goals intros; rfl

/-- The projection of a family takes a morphism to its base morphism, up to the
identifications of `Family.projection_obj`. -/
public theorem Family.projection_map_eq (𝓕 : Family.{u, w, t} (Λ := Λ) (k := k))
    {X Y : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k)} :
    letI := 𝓕.category
    ∀ (f : X ⟶ Y), 𝓕.projection.map f =
      eqToHom (𝓕.projection_obj X) ≫
        (𝓕.homEquiv X Y f).base ≫ eqToHom (𝓕.projection_obj Y).symm := by
  let := 𝓕.category
  intro f
  calc
    𝓕.projection.map f =
        eqToHom (𝓕.projection_obj X) ≫
          (eqToHom (𝓕.projection_obj X).symm ≫ 𝓕.projection.map f ≫
            eqToHom (𝓕.projection_obj Y)) ≫
            eqToHom (𝓕.projection_obj Y).symm := by simp [Category.assoc]
    _ = eqToHom (𝓕.projection_obj X) ≫
          (𝓕.homEquiv X Y f).base ≫ eqToHom (𝓕.projection_obj Y).symm := by
            rw [𝓕.projection_map f]

/-- The chosen category of finite projective modules over the algebras of `𝒞_Λ`. -/
@[stacks 0D3I "finite_projective_deformation_category"]
public noncomputable def family : Family.{u, w, t} (Λ := Λ) (k := k) :=
  Classical.choice nonempty_family

/-- Deformations of a finite-dimensional `k`-vector space `V`: the objects of the category of
finite projective modules lying over the special-fibre object `(k, V)`. -/
@[stacks 0D3I "finite_projective_deformation_category"]
public abbrev deformationCategory (V : Type t) [AddCommGroup V] [Module k V]
    [Module.Finite k V] :=
  letI := (family (Λ := Λ) (k := k)).category
  Over (specialFiber (Λ := Λ) (k := k) V)

end FiniteProjectiveModule

end Deformation.Examples
