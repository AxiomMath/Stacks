module

public import StacksFrontier.CategoryTheory.Localization.EquivalenceAdjunction
public import StacksFrontier.Homology.HomComplex.RHom.BaseChange

/-!
# The two `ULift` conjugations of derived internal Hom are one conjugation

Derived internal Hom at a module universe independent of the ring's is obtained in two ways, by
conjugating the fixed-universe construction `StacksDraft.DerivedHom.derivedHomAdjunction` along a
restriction-of-scalars equivalence for the canonical isomorphism `ULift.{v} R ≃+* R`:

* `StacksDraft.DerivedHom.derivedScalarEquivalence R :
  D(ModuleCat (ULift.{v} R)) ≌ D(ModuleCat R)` is the derived form of
  `StacksDraft.DerivedHom.uliftModuleEquivalence`, which is
  `ModuleCat.restrictScalarsEquivalenceOfRingEquiv` of `ULift.ringEquiv.symm`. Transporting the
  tensor-Hom bundle along it gives `StacksDraft.DerivedHom.derivedHomAdjunctionOverRing`, the
  bundle of [stacks 0A63].
* `Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence R :
  D(ModuleCat R) ≌ D(ModuleCat (ULift.{v} R))` is built from `ULift.ringEquiv`. Conjugating the
  internal-Hom bifunctor along it gives `Stacks.DerivedHom.ScalarTransportedInternalHom.hom`, the
  bifunctor with which [stacks 0E1W] and [stacks 0E1X] are stated.

The two equivalences have interchanged functors and inverses definitionally, so the two
internal-Hom bifunctors are equal. Their adjunctions are also identified: the adjunction of the
first is the adjunction of the opposite of the second.

## Main results

* `Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence_functor` and
  `Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence_inverse`: the two
  equivalences have interchanged functors and inverses.
* `Stacks.DerivedHom.ScalarTransportedInternalHom.hom_eq`: the two internal-Hom bifunctors are
  equal.
* `Stacks.DerivedHom.ScalarTransportedInternalHom.homEquiv`: the bifunctor of [stacks 0E1W] is
  right adjoint, in its second variable, to the tensor product of [stacks 0A63].
* `Stacks.DerivedHom.ScalarTransportedInternalHom.homScalarTransportIso`: the comparison is
  compatible with the two scalar equivalences.
* `Stacks.DerivedHom.ScalarTransportedInternalHom.derivedScalarEquivalence_toAdjunction_eq_symm`:
  the adjunction of the equivalence of [stacks 0A63] is the adjunction of the opposite of the
  equivalence of [stacks 0E1W]. Hence `derivedScalarEquivalence_counit_app` and
  `derivedScalarEquivalence_symm_counit_app`: the two counits of the one are the inverse unit and
  the counit of the other.
* `Stacks.DerivedHom.ScalarTransportedInternalHom.derivedScalarEquivalence_counit_app_Q` and
  `derivedScalarEquivalence_symm_counit_app_Q`: both counits at a localized complex, in terms of
  the components of `CategoryTheory.Functor.mapDerivedCategoryFactors` and the localization of
  the counit, resp. the inverse unit, of the equivalence of complexes.
* `Stacks.DerivedHom.ScalarTransportedInternalHom.derivedScalarEquivalence_counit_app_of_iso` and
  `derivedScalarEquivalence_symm_counit_app_of_iso`: the same two values at an object isomorphic
  to a localized complex.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0E1X](https://stacks.math.columbia.edu/tag/0E1X)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace Stacks.DerivedHom.ScalarTransportedInternalHom

open StacksDraft.DerivedHom

attribute [local instance] HasDerivedCategory.standard

section ModuleLevel

variable (R : Type u) [CommRing R]

/-- The restriction-of-scalars equivalence for `ULift.ringEquiv` is the opposite of
`StacksDraft.DerivedHom.uliftModuleEquivalence`, the one for `ULift.ringEquiv.symm`. -/
theorem restrictScalarsEquivalence_uliftRingEquiv_symm :
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
        (ULift.ringEquiv : ULift.{v} R ≃+* R)).symm =
      uliftModuleEquivalence.{u, max u v, v} R :=
  rfl

/-- The functor of the equivalence for `ULift.ringEquiv` is the inverse of
`StacksDraft.DerivedHom.uliftModuleEquivalence`. -/
theorem restrictScalarsEquivalence_uliftRingEquiv_functor :
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
        (ULift.ringEquiv : ULift.{v} R ≃+* R)).functor =
      (uliftModuleEquivalence.{u, max u v, v} R).inverse :=
  rfl

/-- The inverse of the equivalence for `ULift.ringEquiv` is the functor of
`StacksDraft.DerivedHom.uliftModuleEquivalence`. -/
theorem restrictScalarsEquivalence_uliftRingEquiv_inverse :
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
        (ULift.ringEquiv : ULift.{v} R ≃+* R)).inverse =
      (uliftModuleEquivalence.{u, max u v, v} R).functor :=
  rfl

end ModuleLevel

variable (R : Type u) [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]

/-- The scalar equivalence of
`Stacks.DerivedHom.ScalarTransportedInternalHom`, which restricts along `ULift.ringEquiv`, has as
its functor the inverse of `StacksDraft.DerivedHom.derivedScalarEquivalence`, which restricts along
`ULift.ringEquiv.symm`. -/
theorem scalarEquivalence_functor :
    (scalarEquivalence.{u, v, w} R).functor = (derivedScalarEquivalence.{u, v, w} R).inverse :=
  rfl

/-- The inverse of the scalar equivalence of
`Stacks.DerivedHom.ScalarTransportedInternalHom` is the functor of
`StacksDraft.DerivedHom.derivedScalarEquivalence`. -/
theorem scalarEquivalence_inverse :
    (scalarEquivalence.{u, v, w} R).inverse = (derivedScalarEquivalence.{u, v, w} R).functor :=
  rfl

/-- The internal-Hom bifunctor of [stacks 0E1W] and [stacks 0E1X], obtained by conjugating the
fixed-universe construction along
`Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence`, is the internal-Hom
bifunctor of the tensor-Hom bundle of [stacks 0A63], obtained by conjugating the same
construction along `StacksDraft.DerivedHom.derivedScalarEquivalence`. -/
theorem hom_eq :
    hom.{u, v, w} R = (derivedHomAdjunctionOverRing.{u, v, w} R).hom :=
  rfl

/-- `Stacks.DerivedHom.ScalarTransportedInternalHom.hom_eq` at an object. -/
theorem hom_obj (L M : DerivedCategory (ModuleCat.{max u v} R)) :
    (hom.{u, v, w} R).obj (Opposite.op L, M) =
      (derivedHomAdjunctionOverRing.{u, v, w} R).hom.obj (Opposite.op L, M) :=
  rfl

/-- `Stacks.DerivedHom.ScalarTransportedInternalHom.hom_eq` on morphisms. -/
theorem hom_map {L L' M M' : DerivedCategory (ModuleCat.{max u v} R)} (l : L' ⟶ L) (m : M ⟶ M') :
    (hom.{u, v, w} R).map ((l.op, m) : (Opposite.op L, M) ⟶ (Opposite.op L', M')) =
      (derivedHomAdjunctionOverRing.{u, v, w} R).hom.map
        ((l.op, m) : (Opposite.op L, M) ⟶ (Opposite.op L', M')) :=
  rfl

/-- The bifunctor of [stacks 0E1W] is right adjoint, in its second variable, to the tensor
product of [stacks 0A63]: morphisms `K ⟶ RHom(L, M)` correspond additively to morphisms
`K ⊗ᴸ L ⟶ M`. -/
noncomputable def homEquiv (K L M : DerivedCategory (ModuleCat.{max u v} R)) :
    (K ⟶ (hom.{u, v, w} R).obj (Opposite.op L, M)) ≃+
      ((derivedHomAdjunctionOverRing.{u, v, w} R).tensor.obj (K, L) ⟶ M) :=
  (derivedHomAdjunctionOverRing.{u, v, w} R).homEquiv K L M

/-- Conjugating the fixed-universe internal Hom back along the inverse of
`Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence` returns the bifunctor of
[stacks 0E1W]. -/
noncomputable def homScalarTransportIso :
    (scalarEquivalence.{u, v, w} R).inverse.op.prod (scalarEquivalence.{u, v, w} R).inverse ⋙
        hom.{u, v, w} R ≅
      (derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)).hom ⋙
        (scalarEquivalence.{u, v, w} R).inverse :=
  derivedHomULiftIso.{u, v, w} R

section Adjunctions

/-- The equivalence of complexes that both scalar equivalences localize: the one induced by
`StacksDraft.DerivedHom.uliftModuleEquivalence`, that is by restriction of scalars along
`ULift.ringEquiv.symm`. -/
noncomputable abbrev uliftComplexEquivalence :=
  (uliftModuleEquivalence.{u, max u v, v} R).mapHomologicalComplex (ComplexShape.up ℤ)

/-- `StacksDraft.DerivedHom.derivedScalarEquivalence` is the localization of the adjunction of
`Stacks.DerivedHom.ScalarTransportedInternalHom.uliftComplexEquivalence`, along the two
components of `CategoryTheory.Functor.mapDerivedCategoryFactors`. -/
theorem derivedScalarEquivalence_toAdjunction_eq :
    (derivedScalarEquivalence.{u, v, w} R).toAdjunction =
      _root_.Stacks.Localization.adjunctionOfSquares (uliftComplexEquivalence.{u, v} R)
        DerivedCategory.Q
        (HomologicalComplex.quasiIso (ModuleCat.{max u v} (ULift.{v} R)) (ComplexShape.up ℤ))
        DerivedCategory.Q
        (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ))
        (uliftModuleEquivalence.{u, max u v, v} R).functor.mapDerivedCategory
        (uliftModuleEquivalence.{u, max u v, v} R).inverse.mapDerivedCategory
        (uliftModuleEquivalence.{u, max u v, v} R).functor.mapDerivedCategoryFactors
        (uliftModuleEquivalence.{u, max u v, v} R).inverse.mapDerivedCategoryFactors :=
  _root_.Stacks.Localization.equivalence_toAdjunction _ _ _ _ _ _ _ _ _ _

/-- `Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence` is the localization of the
adjunction of the *opposite* of
`Stacks.DerivedHom.ScalarTransportedInternalHom.uliftComplexEquivalence`, along the two
components of `CategoryTheory.Functor.mapDerivedCategoryFactors` interchanged. -/
theorem scalarEquivalence_toAdjunction_eq :
    (scalarEquivalence.{u, v, w} R).toAdjunction =
      _root_.Stacks.Localization.adjunctionOfSquares (uliftComplexEquivalence.{u, v} R).symm
        DerivedCategory.Q
        (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ))
        DerivedCategory.Q
        (HomologicalComplex.quasiIso (ModuleCat.{max u v} (ULift.{v} R)) (ComplexShape.up ℤ))
        (uliftModuleEquivalence.{u, max u v, v} R).inverse.mapDerivedCategory
        (uliftModuleEquivalence.{u, max u v, v} R).functor.mapDerivedCategory
        (uliftModuleEquivalence.{u, max u v, v} R).inverse.mapDerivedCategoryFactors
        (uliftModuleEquivalence.{u, max u v, v} R).functor.mapDerivedCategoryFactors :=
  _root_.Stacks.Localization.equivalence_toAdjunction (uliftComplexEquivalence.{u, v} R).symm
    _ _ _ _ _ _ _ _ _

/-- The adjunction of `StacksDraft.DerivedHom.derivedScalarEquivalence`, the equivalence along
which the tensor-Hom bundle of [stacks 0A63] is conjugated, is the adjunction of the opposite of
`Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence`, the equivalence with which
[stacks 0E1W] is stated. -/
theorem derivedScalarEquivalence_toAdjunction_eq_symm :
    (derivedScalarEquivalence.{u, v, w} R).toAdjunction =
      (scalarEquivalence.{u, v, w} R).symm.toAdjunction := by
  have key := _root_.Stacks.Localization.adjunctionOfSquares_unit_comp_symm_counit
    (uliftComplexEquivalence.{u, v} R)
    DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} (ULift.{v} R)) (ComplexShape.up ℤ))
    DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ))
    (uliftModuleEquivalence.{u, max u v, v} R).functor.mapDerivedCategory
    (uliftModuleEquivalence.{u, max u v, v} R).inverse.mapDerivedCategory
    (uliftModuleEquivalence.{u, max u v, v} R).functor.mapDerivedCategoryFactors
    (uliftModuleEquivalence.{u, max u v, v} R).inverse.mapDerivedCategoryFactors
  rw [← congrArg Adjunction.unit (derivedScalarEquivalence_toAdjunction_eq.{u, v, w} R),
    ← congrArg Adjunction.counit (scalarEquivalence_toAdjunction_eq.{u, v, w} R)] at key
  exact Adjunction.ext ((Iso.comp_hom_eq_id (scalarEquivalence.{u, v, w} R).counitIso).1 key)

/-- The counit of the scalar equivalence of [stacks 0A63] is the inverse unit of the scalar
equivalence of [stacks 0E1W]. -/
theorem derivedScalarEquivalence_counit_app (M : DerivedCategory (ModuleCat.{max u v} R)) :
    (derivedScalarEquivalence.{u, v, w} R).toAdjunction.counit.app M =
      (scalarEquivalence.{u, v, w} R).unitIso.inv.app M :=
  congrFun (congrArg NatTrans.app
    (congrArg Adjunction.counit
      (derivedScalarEquivalence_toAdjunction_eq_symm.{u, v, w} R))) M

/-- The unit isomorphism of [stacks 0A63]'s scalar equivalence is the inverse counit isomorphism
of [stacks 0E1W]'s. -/
theorem derivedScalarEquivalence_unitIso :
    (derivedScalarEquivalence.{u, v, w} R).unitIso =
      (scalarEquivalence.{u, v, w} R).counitIso.symm :=
  Iso.ext (congrArg Adjunction.unit
    (derivedScalarEquivalence_toAdjunction_eq_symm.{u, v, w} R))

/-- The counit of the opposite of the scalar equivalence of [stacks 0A63] is the counit of the
scalar equivalence of [stacks 0E1W]. -/
theorem derivedScalarEquivalence_symm_counit_app
    (Z : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))) :
    (derivedScalarEquivalence.{u, v, w} R).symm.toAdjunction.counit.app Z =
      (scalarEquivalence.{u, v, w} R).counitIso.hom.app Z :=
  congrFun (congrArg NatTrans.app
    (congrArg Iso.inv (derivedScalarEquivalence_unitIso.{u, v, w} R))) Z

/-- At a localized complex, the counit of the scalar equivalence of [stacks 0A63] is the
composite of the two components of `CategoryTheory.Functor.mapDerivedCategoryFactors` and the
localization of the counit of the equivalence of complexes. -/
theorem derivedScalarEquivalence_counit_app_Q
    (Y : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    (derivedScalarEquivalence.{u, v, w} R).toAdjunction.counit.app
        (DerivedCategory.Q.obj Y) =
      (uliftModuleEquivalence.{u, max u v, v} R).functor.mapDerivedCategory.map
          ((uliftModuleEquivalence.{u, max u v,
            v} R).inverse.mapDerivedCategoryFactors.hom.app Y) ≫
        (uliftModuleEquivalence.{u, max u v, v} R).functor.mapDerivedCategoryFactors.hom.app
            ((uliftComplexEquivalence.{u, v} R).inverse.obj Y) ≫
          DerivedCategory.Q.map ((uliftComplexEquivalence.{u, v} R).counitIso.hom.app Y) := by
  rw [derivedScalarEquivalence_toAdjunction_eq.{u, v, w} R]
  exact _root_.Stacks.Localization.adjunctionOfSquares_counit_app _ _ _ _ _ _ _ _ _ Y

/-- At a localized complex, the counit of the opposite of the scalar equivalence of
[stacks 0A63] is the composite of the two components of
`CategoryTheory.Functor.mapDerivedCategoryFactors`, in the other order, and the localization of
the inverse unit of the equivalence of complexes. -/
theorem derivedScalarEquivalence_symm_counit_app_Q
    (X : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ) :
    (derivedScalarEquivalence.{u, v, w} R).symm.toAdjunction.counit.app
        (DerivedCategory.Q.obj X) =
      (uliftModuleEquivalence.{u, max u v, v} R).inverse.mapDerivedCategory.map
          ((uliftModuleEquivalence.{u, max u v,
            v} R).functor.mapDerivedCategoryFactors.hom.app X) ≫
        (uliftModuleEquivalence.{u, max u v, v} R).inverse.mapDerivedCategoryFactors.hom.app
            ((uliftComplexEquivalence.{u, v} R).functor.obj X) ≫
          DerivedCategory.Q.map ((uliftComplexEquivalence.{u, v} R).unitIso.inv.app X) := by
  rw [derivedScalarEquivalence_symm_counit_app.{u, v, w} R,
    show (scalarEquivalence.{u, v, w} R).counitIso.hom =
      (scalarEquivalence.{u, v, w} R).toAdjunction.counit from rfl,
    scalarEquivalence_toAdjunction_eq.{u, v, w} R]
  exact _root_.Stacks.Localization.adjunctionOfSquares_counit_app _ _ _ _ _ _ _ _ _ X

/-- The counit of the scalar equivalence of [stacks 0A63] at an object `M` with an isomorphism
`e : M ≅ Q(Y)`, in terms of
`Stacks.DerivedHom.ScalarTransportedInternalHom.derivedScalarEquivalence_counit_app_Q`. -/
theorem derivedScalarEquivalence_counit_app_of_iso
    (M : DerivedCategory (ModuleCat.{max u v} R))
    (Y : CochainComplex (ModuleCat.{max u v} R) ℤ) (e : M ≅ DerivedCategory.Q.obj Y) :
    (derivedScalarEquivalence.{u, v, w} R).toAdjunction.counit.app M =
      (derivedScalarEquivalence.{u, v, w} R).functor.map
            ((derivedScalarEquivalence.{u, v, w} R).inverse.map e.hom) ≫
          ((uliftModuleEquivalence.{u, max u v, v} R).functor.mapDerivedCategory.map
                ((uliftModuleEquivalence.{u, max u v,
                  v} R).inverse.mapDerivedCategoryFactors.hom.app Y) ≫
              (uliftModuleEquivalence.{u, max u v,
                  v} R).functor.mapDerivedCategoryFactors.hom.app
                  ((uliftComplexEquivalence.{u, v} R).inverse.obj Y) ≫
                DerivedCategory.Q.map ((uliftComplexEquivalence.{u, v} R).counitIso.hom.app Y)) ≫
        e.inv := by
  rw [_root_.Stacks.Adjunction.counit_app_of_iso
    (derivedScalarEquivalence.{u, v, w} R).toAdjunction e,
    derivedScalarEquivalence_counit_app_Q.{u, v, w} R]
  rfl

/-- The counit of the opposite of the scalar equivalence of [stacks 0A63] at an object `Z` with
an isomorphism `e : Z ≅ Q(X)`, in terms of
`Stacks.DerivedHom.ScalarTransportedInternalHom.derivedScalarEquivalence_symm_counit_app_Q`. -/
theorem derivedScalarEquivalence_symm_counit_app_of_iso
    (Z : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R)))
    (X : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ)
    (e : Z ≅ DerivedCategory.Q.obj X) :
    (derivedScalarEquivalence.{u, v, w} R).symm.toAdjunction.counit.app Z =
      (derivedScalarEquivalence.{u, v, w} R).inverse.map
            ((derivedScalarEquivalence.{u, v, w} R).functor.map e.hom) ≫
          ((uliftModuleEquivalence.{u, max u v, v} R).inverse.mapDerivedCategory.map
                ((uliftModuleEquivalence.{u, max u v,
                  v} R).functor.mapDerivedCategoryFactors.hom.app X) ≫
              (uliftModuleEquivalence.{u, max u v,
                  v} R).inverse.mapDerivedCategoryFactors.hom.app
                  ((uliftComplexEquivalence.{u, v} R).functor.obj X) ≫
                DerivedCategory.Q.map ((uliftComplexEquivalence.{u, v} R).unitIso.inv.app X)) ≫
        e.inv := by
  rw [_root_.Stacks.Adjunction.counit_app_of_iso
    (derivedScalarEquivalence.{u, v, w} R).symm.toAdjunction e,
    derivedScalarEquivalence_symm_counit_app_Q.{u, v, w} R]
  rfl

end Adjunctions

end Stacks.DerivedHom.ScalarTransportedInternalHom

end
