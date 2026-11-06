module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# The interchange `(N ⊗_S P) ⊗_R T ≅ N ⊗_S (P ⊗_R T)` as a natural isomorphism of functors

Let `R` be a commutative ring, let `S` be a commutative `R`-algebra, let `P` be an `S`-module
whose `S`-action extends an `R`-action (`IsScalarTower R S P`) and let `T` be an `R`-module.
For a single `S`-module `N` the interchange

`(N ⊗[S] P) ⊗[R] T ≃ₗ[S] N ⊗[S] (P ⊗[R] T)`

is `TensorProduct.AlgebraTensorModule.assoc R S S N P T`. Here the two sides are the values at
`N` of two functors `ModuleCat S ⥤ ModuleCat R`, and the interchange is a natural isomorphism
between them; `CategoryTheory.Functor.mapHomologicalComplex` carries it to complexes of
`S`-modules.

Both functors are composites of `tensorRight` on `ModuleCat` and
`ModuleCat.restrictScalars (algebraMap R S)`, and the isomorphism is
`TensorProduct.AlgebraTensorModule.assoc` with its scalars restricted to `R`. The `R`-module
structure on an `S`-module `N` is the one restriction of scalars puts there,
`ModuleCat.moduleRestrictScalars`, a local instance.

The interchange is functorial in `P`: an `S`-linear `u : P' →ₗ[S] P` induces a natural
transformation of each of the two functors, and the isomorphism intertwines the two
(`ModuleCat.tensorRightTensorRightMap_comp_tensorRightAssoc`), both on `ModuleCat S` and on
complexes.

## Main definitions

* `ModuleCat.tensorRightTensorRight`: the functor `N ↦ (N ⊗[S] P) ⊗[R] T`.
* `ModuleCat.tensorRightTensorProduct`: the functor `N ↦ N ⊗[S] (P ⊗[R] T)`.
* `ModuleCat.tensorRightAssoc`: **the interchange**, a natural isomorphism between the two.
* `ModuleCat.tensorRightTensorRightMap`, `ModuleCat.tensorRightTensorProductMap`: the natural
  transformations induced by an `S`-linear map `u : P' →ₗ[S] P`.
* `ModuleCat.tensorRightAssocMapHomologicalComplex`: the interchange on cochain complexes.

## Main results

* `ModuleCat.tensorRightTensorRightMap_comp_tensorRightAssoc`: the interchange intertwines the
  two natural transformations induced by `u : P' →ₗ[S] P`.
* `ModuleCat.tensorRightTensorRightMap_comp_tensorRightAssoc_mapHomologicalComplex`: the same
  compatibility after `CategoryTheory.NatTrans.mapHomologicalComplex`.

## References

* [Stacks Project, Tag 08RF](https://stacks.math.columbia.edu/tag/08RF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory TensorProduct

universe u

namespace ModuleCat

variable (R : Type u) [CommRing R] (S : Type u) [CommRing S] [Algebra R S]

/-! ### Restriction of scalars as an instance on the objects of `ModuleCat S` -/

variable {R S} in
/-- The `R`-module structure that `ModuleCat.restrictScalars (algebraMap R S)` puts on an object
`N` of `ModuleCat S`, namely `r • n = algebraMap R S r • n`. -/
abbrev moduleRestrictScalars (N : ModuleCat.{u} S) : Module R (N : Type u) :=
  ((ModuleCat.restrictScalars (algebraMap R S)).obj N).isModule

attribute [local instance] moduleRestrictScalars

variable {R S} in
/-- The `R`-action of `ModuleCat.moduleRestrictScalars` is the `S`-action read through
`algebraMap R S`, so it is a tower with it. -/
theorem isScalarTower_moduleRestrictScalars (N : ModuleCat.{u} S) :
    IsScalarTower R S (N : Type u) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

attribute [local instance] isScalarTower_moduleRestrictScalars

variable (P : Type u) [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P]
    (T : ModuleCat.{u} R)

/-! ### The two functors -/

/-- The functor `ModuleCat S ⥤ ModuleCat R` sending `N` to `(N ⊗[S] P) ⊗[R] T`: tensor on the
right with `P` over `S`, restrict the scalars to `R`, tensor on the right with `T` over `R`. -/
def tensorRightTensorRight : ModuleCat.{u} S ⥤ ModuleCat.{u} R :=
  tensorRight (ModuleCat.of S P) ⋙ ModuleCat.restrictScalars (algebraMap R S) ⋙ tensorRight T

/-- The functor `ModuleCat S ⥤ ModuleCat R` sending `N` to `N ⊗[S] (P ⊗[R] T)`: tensor on the
right with the `S`-module `P ⊗[R] T` of `TensorProduct.AlgebraTensorModule`, then restrict the
scalars to `R`. -/
def tensorRightTensorProduct : ModuleCat.{u} S ⥤ ModuleCat.{u} R :=
  tensorRight (ModuleCat.of S (P ⊗[R] T)) ⋙ ModuleCat.restrictScalars (algebraMap R S)

/-- The functor `ModuleCat.tensorRightTensorRight R S P T` is additive. -/
instance : (tensorRightTensorRight R S P T).Additive :=
  inferInstanceAs (Functor.Additive (tensorRight (ModuleCat.of S P) ⋙
    ModuleCat.restrictScalars (algebraMap R S) ⋙ tensorRight T))

/-- The functor `ModuleCat.tensorRightTensorProduct R S P T` is additive. -/
instance : (tensorRightTensorProduct R S P T).Additive :=
  inferInstanceAs (Functor.Additive (tensorRight (ModuleCat.of S (P ⊗[R] T)) ⋙
    ModuleCat.restrictScalars (algebraMap R S)))

/-! ### The interchange isomorphism -/

/-- The interchange `(N ⊗[S] P) ⊗[R] T ≅ N ⊗[S] (P ⊗[R] T)` at a single object `N`, namely
`TensorProduct.AlgebraTensorModule.assoc R S S N P T` with its scalars restricted to `R`. -/
def tensorRightAssocApp (N : ModuleCat.{u} S) :
    (tensorRightTensorRight R S P T).obj N ≅ (tensorRightTensorProduct R S P T).obj N :=
  LinearEquiv.toModuleIso
    ((AlgebraTensorModule.assoc R S S (N : Type u) P (T : Type u)).restrictScalars R)

/-- The interchange `ModuleCat.tensorRightAssocApp` sends `(n ⊗ₜ p) ⊗ₜ t` to `n ⊗ₜ (p ⊗ₜ t)`. -/
@[simp]
theorem tensorRightAssocApp_hom_apply (N : ModuleCat.{u} S) (n : N) (p : P) (t : T) :
    (tensorRightAssocApp R S P T N).hom ((n ⊗ₜ[S] p) ⊗ₜ[R] t) = n ⊗ₜ[S] (p ⊗ₜ[R] t) :=
  rfl

/-- The inverse of `ModuleCat.tensorRightAssocApp` sends `n ⊗ₜ (p ⊗ₜ t)` to `(n ⊗ₜ p) ⊗ₜ t`. -/
@[simp]
theorem tensorRightAssocApp_inv_apply (N : ModuleCat.{u} S) (n : N) (p : P) (t : T) :
    (tensorRightAssocApp R S P T N).inv (n ⊗ₜ[S] (p ⊗ₜ[R] t)) = (n ⊗ₜ[S] p) ⊗ₜ[R] t :=
  rfl

/-- **The interchange along a functor of `ModuleCat`**: the natural isomorphism
`(- ⊗[S] P) ⊗[R] T ≅ - ⊗[S] (P ⊗[R] T)` of functors `ModuleCat S ⥤ ModuleCat R`, with components
`TensorProduct.AlgebraTensorModule.assoc`. -/
def tensorRightAssoc : tensorRightTensorRight R S P T ≅ tensorRightTensorProduct R S P T :=
  NatIso.ofComponents (tensorRightAssocApp R S P T) fun {N N'} f => by
    have key :
        ((AlgebraTensorModule.assoc R S S (N' : Type u) P (T : Type u)).restrictScalars
              R).toLinearMap ∘ₗ ((f.hom.rTensor P).restrictScalars R).rTensor (T : Type u) =
          (f.hom.rTensor (P ⊗[R] (T : Type u))).restrictScalars R ∘ₗ
            ((AlgebraTensorModule.assoc R S S (N : Type u) P (T : Type u)).restrictScalars
              R).toLinearMap := by
      refine TensorProduct.ext' fun y t => ?_
      refine TensorProduct.inductionOn y (fun n p => rfl) fun a b ha hb => ?_
      simp only [TensorProduct.add_tmul, map_add, ha, hb]
    exact ModuleCat.hom_ext key

/-- The component of `ModuleCat.tensorRightAssoc` at `N` is `ModuleCat.tensorRightAssocApp`. -/
@[simp]
theorem tensorRightAssoc_hom_app (N : ModuleCat.{u} S) :
    (tensorRightAssoc R S P T).hom.app N = (tensorRightAssocApp R S P T N).hom :=
  rfl

/-- The component at `N` of the inverse of `ModuleCat.tensorRightAssoc` is the inverse of
`ModuleCat.tensorRightAssocApp`. -/
@[simp]
theorem tensorRightAssoc_inv_app (N : ModuleCat.{u} S) :
    (tensorRightAssoc R S P T).inv.app N = (tensorRightAssocApp R S P T N).inv :=
  rfl

/-! ### Functoriality in `P` -/

variable {P' : Type u} [AddCommGroup P'] [Module R P'] [Module S P'] [IsScalarTower R S P']

/-- The natural transformation `(- ⊗[S] P') ⊗[R] T ⟶ (- ⊗[S] P) ⊗[R] T` induced by an `S`-linear
map `u : P' →ₗ[S] P`. -/
def tensorRightTensorRightMap (u : P' →ₗ[S] P) :
    tensorRightTensorRight R S P' T ⟶ tensorRightTensorRight R S P T :=
  Functor.whiskerRight ((tensoringRight (ModuleCat.{u} S)).map (ofHom u))
    (ModuleCat.restrictScalars (algebraMap R S) ⋙ tensorRight T)

/-- The natural transformation `- ⊗[S] (P' ⊗[R] T) ⟶ - ⊗[S] (P ⊗[R] T)` induced by an `S`-linear
map `u : P' →ₗ[S] P`. -/
def tensorRightTensorProductMap (u : P' →ₗ[S] P) :
    tensorRightTensorProduct R S P' T ⟶ tensorRightTensorProduct R S P T :=
  Functor.whiskerRight ((tensoringRight (ModuleCat.{u} S)).map
      (ofHom (AlgebraTensorModule.map u (LinearMap.id (R := R) (M := (T : Type u))))))
    (ModuleCat.restrictScalars (algebraMap R S))

omit [Module R P] [IsScalarTower R S P] [Module R P'] [IsScalarTower R S P'] in
/-- The component at `N` of `ModuleCat.tensorRightTensorRightMap` sends `(n ⊗ₜ p) ⊗ₜ t` to
`(n ⊗ₜ u p) ⊗ₜ t`. -/
@[simp]
theorem tensorRightTensorRightMap_app_apply (u : P' →ₗ[S] P) (N : ModuleCat.{u} S) (n : N)
    (p : P') (t : T) :
    (tensorRightTensorRightMap R S P T u).app N ((n ⊗ₜ[S] p) ⊗ₜ[R] t) =
      (n ⊗ₜ[S] u p) ⊗ₜ[R] t :=
  rfl

/-- The component at `N` of `ModuleCat.tensorRightTensorProductMap` sends `n ⊗ₜ (p ⊗ₜ t)` to
`n ⊗ₜ (u p ⊗ₜ t)`. -/
@[simp]
theorem tensorRightTensorProductMap_app_apply (u : P' →ₗ[S] P) (N : ModuleCat.{u} S) (n : N)
    (p : P') (t : T) :
    (tensorRightTensorProductMap R S P T u).app N (n ⊗ₜ[S] (p ⊗ₜ[R] t)) =
      n ⊗ₜ[S] (u p ⊗ₜ[R] t) :=
  rfl

/-- **The interchange is functorial in `P`**: for an `S`-linear `u : P' →ₗ[S] P` the square

`(- ⊗[S] P') ⊗[R] T ⟶ (- ⊗[S] P) ⊗[R] T`,  `- ⊗[S] (P' ⊗[R] T) ⟶ - ⊗[S] (P ⊗[R] T)`

whose vertical maps are the interchange isomorphisms commutes, as an equality of natural
transformations `(- ⊗[S] P') ⊗[R] T ⟶ - ⊗[S] (P ⊗[R] T)`. -/
theorem tensorRightTensorRightMap_comp_tensorRightAssoc (u : P' →ₗ[S] P) :
    tensorRightTensorRightMap R S P T u ≫ (tensorRightAssoc R S P T).hom =
      (tensorRightAssoc R S P' T).hom ≫ tensorRightTensorProductMap R S P T u := by
  refine NatTrans.ext (funext fun N => ModuleCat.hom_ext ?_)
  have key :
      ((AlgebraTensorModule.assoc R S S (N : Type u) P (T : Type u)).restrictScalars
            R).toLinearMap ∘ₗ
          (((LinearMap.lTensor (N : Type u) u).restrictScalars R).rTensor (T : Type u)) =
        (LinearMap.lTensor (N : Type u)
            (AlgebraTensorModule.map u
              (LinearMap.id (R := R) (M := (T : Type u))))).restrictScalars R ∘ₗ
          ((AlgebraTensorModule.assoc R S S (N : Type u) P' (T : Type u)).restrictScalars
            R).toLinearMap := by
    refine TensorProduct.ext' fun y t => ?_
    refine TensorProduct.inductionOn y (fun n p => rfl) fun a b ha hb => ?_
    simp only [TensorProduct.add_tmul, map_add, ha, hb]
  exact key

/-! ### The interchange on complexes -/

/-- **The interchange on cochain complexes**: the natural isomorphism of the two functors
`CochainComplex (ModuleCat S) ℤ ⥤ CochainComplex (ModuleCat R) ℤ` obtained from
`ModuleCat.tensorRightAssoc` by `CategoryTheory.Functor.mapHomologicalComplex`. -/
def tensorRightAssocMapHomologicalComplex :
    (tensorRightTensorRight R S P T).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (tensorRightTensorProduct R S P T).mapHomologicalComplex (ComplexShape.up ℤ) :=
  NatIso.mapHomologicalComplex (tensorRightAssoc R S P T) (ComplexShape.up ℤ)

/-- `ModuleCat.tensorRightTensorRightMap_comp_tensorRightAssoc` on complexes: the interchange of
complexes intertwines the two natural transformations that an `S`-linear `u : P' →ₗ[S] P` induces
on the complex-level functors. -/
theorem tensorRightTensorRightMap_comp_tensorRightAssoc_mapHomologicalComplex (u : P' →ₗ[S] P) :
    NatTrans.mapHomologicalComplex (tensorRightTensorRightMap R S P T u) (ComplexShape.up ℤ) ≫
        (tensorRightAssocMapHomologicalComplex R S P T).hom =
      (tensorRightAssocMapHomologicalComplex R S P' T).hom ≫
        NatTrans.mapHomologicalComplex (tensorRightTensorProductMap R S P T u)
          (ComplexShape.up ℤ) := by
  show NatTrans.mapHomologicalComplex (tensorRightTensorRightMap R S P T u) (ComplexShape.up ℤ) ≫
      NatTrans.mapHomologicalComplex (tensorRightAssoc R S P T).hom (ComplexShape.up ℤ) =
    NatTrans.mapHomologicalComplex (tensorRightAssoc R S P' T).hom (ComplexShape.up ℤ) ≫
      NatTrans.mapHomologicalComplex (tensorRightTensorProductMap R S P T u) (ComplexShape.up ℤ)
  rw [← NatTrans.mapHomologicalComplex_comp, ← NatTrans.mapHomologicalComplex_comp,
    tensorRightTensorRightMap_comp_tensorRightAssoc]

end ModuleCat

end
