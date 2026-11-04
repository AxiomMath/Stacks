module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import StacksFrontier.Homology.HomComplex.DerivedAdjunction
public import StacksFrontier.Homology.PseudoCoherent.Basic

/-!
# Comparisons for the scalar transport between `D(ULift A)` and `D(A)`

Let `A` be a commutative ring. The canonical ring isomorphism `A ≃+* ULift A` induces, by
restriction of scalars, an equivalence `D(ULift A) ≌ D(A)` of derived categories, the transport
`StacksDraft.DerivedHom.derivedScalarEquivalence` along which the tensor--Hom adjunction over
`ULift A` is moved to one over `A`. This file records the two comparisons that make the transport
usable on cohomology: it commutes with the cohomology functors, both as an isomorphism of
`A`-modules and as a natural additive bijection of the underlying groups.

It also records the elementary fact that an additive equivalence of categories is an additive
bijection on each group of morphisms, which is what turns such a transport into a comparison of
Ext groups.

## Main definitions

* `StacksDraft.DerivedHom.scalarTransportHomologyIso` — the isomorphism of `A`-modules
  `Hⁿ(E X) ≅ (restriction of scalars of) Hⁿ(X)`, where `E` is the scalar transport.
* `StacksDraft.DerivedHom.scalarHomologyAddEquiv` — the same comparison read on carriers, as an
  additive bijection.
* `StacksDraft.DerivedHom.equivalenceHomAddEquiv` — the additive bijection `(X ⟶ Y) ≃+
  (F X ⟶ F Y)` attached to an additive equivalence of preadditive categories `F`.

## Main results

* `StacksDraft.DerivedHom.scalarHomologyAddEquiv_naturality` — the additive bijection on
  cohomology groups is natural in the object of `D(ULift A)`.
* `StacksDraft.DerivedHom.equivalenceHomAddEquiv_comp` — the additive bijection on morphism
  groups is compatible with composition on the right.

## Implementation notes

Restriction of scalars along a ring isomorphism does not change the underlying additive group of
a module, so the carrier form of the cohomology comparison is the module form read through the
identity on carriers: its two directions are the two directions of the isomorphism, and its
naturality is the naturality of the underlying natural isomorphism, evaluated on an element.

The derived categories are the standard model, so the transport is used at the universe
instantiation `derivedScalarEquivalence.{u, v, max u v + 1}`.
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace StacksDraft.DerivedHom

/-! ### Cohomology and the scalar transport -/

section Homology

variable (A : Type u) [CommRing A]

/-- Cohomology in each degree commutes with the scalar transport between the derived categories
of modules over a ring and over its canonical lift. -/
public def scalarTransportHomologyIso
    (X : DerivedCategory (ModuleCat.{max u v} (ULift.{v} A))) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) n).obj
        ((derivedScalarEquivalence.{u, v, max u v + 1} A).functor.obj X) ≅
      (uliftModuleEquivalence.{u, max u v, v} A).functor.obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} A)) n).obj X) :=
  (StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso
    (uliftModuleEquivalence.{u, max u v, v} A).functor n).app X

/-- Cohomology commutes with the scalar transport, as an additive bijection of the underlying
groups. -/
public def scalarHomologyAddEquiv (X : DerivedCategory (ModuleCat.{max u v} (ULift.{v} A)))
    (n : ℤ) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) n).obj
        ((derivedScalarEquivalence.{u, v, max u v + 1} A).functor.obj X) : Type (max u v)) ≃+
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} A)) n).obj X :
        Type (max u v)) where
  toFun a := (scalarTransportHomologyIso.{u, v} A X n).hom a
  invFun a := (scalarTransportHomologyIso.{u, v} A X n).inv a
  left_inv a := ConcreteCategory.congr_hom (scalarTransportHomologyIso.{u, v} A X n).hom_inv_id a
  right_inv a := ConcreteCategory.congr_hom (scalarTransportHomologyIso.{u, v} A X n).inv_hom_id a
  map_add' a b := ((scalarTransportHomologyIso.{u, v} A X n).hom).hom.map_add a b

/-- The additive bijection of cohomology groups induced by the scalar transport is natural. -/
public theorem scalarHomologyAddEquiv_naturality
    {X Y : DerivedCategory (ModuleCat.{max u v} (ULift.{v} A))} (f : X ⟶ Y) (n : ℤ)
    (a : (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) n).obj
      ((derivedScalarEquivalence.{u, v, max u v + 1} A).functor.obj X)) :
    scalarHomologyAddEquiv A Y n
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) n).map
          ((derivedScalarEquivalence.{u, v, max u v + 1} A).functor.map f) a) =
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} A)) n).map f
        (scalarHomologyAddEquiv A X n a) := by
  have h := ConcreteCategory.congr_hom
    ((StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso
      (uliftModuleEquivalence.{u, max u v, v} A).functor n).hom.naturality f) a
  exact h

end Homology

/-! ### Morphism groups and an additive equivalence -/

section Equivalence

/-- An additive equivalence of categories is an additive bijection on each group of
morphisms. -/
public def equivalenceHomAddEquiv {C : Type*} {D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] (F : C ≌ D) [F.functor.Additive] (X Y : C) :
    (X ⟶ Y) ≃+ (F.functor.obj X ⟶ F.functor.obj Y) :=
  AddEquiv.ofBijective F.functor.mapAddHom (F.fullyFaithfulFunctor.map_bijective X Y)

/-- It is compatible with composition on the right. -/
public theorem equivalenceHomAddEquiv_comp {C : Type*} {D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] (F : C ≌ D) [F.functor.Additive] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    equivalenceHomAddEquiv F X Z (f ≫ g) =
      equivalenceHomAddEquiv F X Y f ≫ F.functor.map g :=
  F.functor.map_comp f g

end Equivalence

end StacksDraft.DerivedHom

end
