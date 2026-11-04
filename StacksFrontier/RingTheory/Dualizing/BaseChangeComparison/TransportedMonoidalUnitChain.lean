module

public import StacksFrontier.Homology.Tor.BaseChangeTensorMonoidalTransport
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ScalarLiftExtendComparisonValue

/-!
# The transported monoidality inverse, moved across the degreewise unit

`CochainComplex.DerivedTensor.transportedMonoidalInv` is the inverse of the monoidality
isomorphism of degreewise extension of scalars over the lifted ring map, written in the two
scalar-lift comparisons and one tensor base-change isomorphism of total complexes over `f`.  The
[stacks 0GMT] side of the keystone at a K-flat pair carries it under a restriction of scalars,
preceded by the degreewise unit of extension of scalars along the lifted ring map:

`η(K' ⊗ L') ≫ restrict(transportedMonoidalInv ≫ u)`.

Its leading factor is itself an extension of scalars, of the comparison of restriction of scalars
with the total tensor product, and so it can be moved to the front: naturality of the unit turns
`η(X) ≫ restrict(extend(g))` into `g ≫ η(Y)`.  What is then left behind the unit is the
scalar-lift comparison `CochainComplex.DerivedTensor.extendScalarsLiftChainIso` at the total
tensor complex, and
`Stacks.DerivedHom.BaseChange.scalarLiftExtendUnitChain_eq` recognises the unit followed by its
restriction as `Stacks.DerivedHom.BaseChange.scalarLiftExtendUnitChain` -- which is the
vocabulary the [stacks 0E1W] prefix of the keystone already speaks, through the `hc₀` its valued
form carries.

So the composite is rewritten with no monoidality comparison in front of the unit at all: a
comparison of restriction of scalars with the total tensor product, then the canonical unit chain
map of the scalar lift, then the restriction of everything that is left.

**What is not done here.**  Nothing is registered and no caveat is lifted.  Both hypotheses of
`Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` remain open; in particular the
comparison identity `h` is untouched, and its frontier remains
`Dualizing.tensorComparisonCompatibility_of_kFlat_tail`.  The tensor base-change isomorphism is
not cancelled here: it is still present, inside the tail that remains under the restriction.
What this file changes is where in the composite it sits.

## Main definitions

* `CochainComplex.DerivedTensor.transportedMonoidalInvTail` -- the part of the transported
  monoidality inverse after its leading extension of scalars.

## Main results

* `CochainComplex.DerivedTensor.transportedMonoidalInv_eq_comp_tail` -- the transported
  monoidality inverse is its leading two factors followed by that tail.
* `CochainComplex.DerivedTensor.unit_comp_restrict_transportedMonoidalInv` -- **the step**: the
  degreewise unit followed by the restriction of the transported monoidality inverse and anything
  after it is the comparison of restriction of scalars with the total tensor product, then
  `Stacks.DerivedHom.BaseChange.scalarLiftExtendUnitChain`, then the restriction of the tail.

## References

* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open CochainComplex.ExtendScalars

universe uR uA v

namespace CochainComplex.DerivedTensor

attribute [local instance] Dualizing.extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)

/-- **Moving an extension of scalars across the unit of the adjunction.**

The unit at `X`, followed by the right adjoint of a composite whose first factor is the left
adjoint applied to `g : X ⟶ Y`, is `g` followed by the unit at `Y`.  The value of the unit at `Y`
composed with the right adjoint of the next factor is passed as data, so that a consumer may
supply its own name for it.

Stated over variable categories: the concrete composite is spelled with two definitionally but
not syntactically equal presentations of degreewise restriction of scalars, so instantiating an
abstract lemma with `exact` -- which checks at default transparency -- succeeds where a rewrite
in place does not. -/
private theorem unitMapCompTail {C : Type*} {D : Type*} [Category* C] [Category* D]
    {φ : C ⥤ D} {ψ : D ⥤ C} (adj : φ ⊣ ψ) {X Y : C} (g : X ⟶ Y) {P P' Z : D}
    (c : φ.obj Y ⟶ P) (tl : P ⟶ P') (u : P' ⟶ Z) {s : Y ⟶ ψ.obj P}
    (hs : adj.unit.app Y ≫ ψ.map c = s) :
    adj.unit.app X ≫ ψ.map (((φ.map g ≫ c) ≫ tl) ≫ u) = g ≫ s ≫ ψ.map (tl ≫ u) := by
  subst hs
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc, adj.unit_naturality g, Category.assoc]

/-- **The tail of the transported monoidality inverse.**

`CochainComplex.DerivedTensor.transportedMonoidalInv` without its leading extension of scalars of
the comparison of restriction of scalars with the total tensor product and without the scalar-lift
comparison at the total tensor complex: the lifted tensor base-change isomorphism inverted, the
comparison of restriction of scalars with the total tensor product over `A` inverted, and the
tensor of the two scalar-lift comparisons inverted.

It is named so that the step
`CochainComplex.DerivedTensor.unit_comp_restrict_transportedMonoidalInv` can state what is left
under the restriction of scalars without unfolding five nested comparisons. -/
public def transportedMonoidalInvTail (K L : CochainComplex (ModuleCat.{max uR uA v} R) ℤ)
    (e : tensorComplex.{uA, max uR v}
        ((extensionOfScalarsCochain.{uR, uA, v} f).obj K)
        ((extensionOfScalarsCochain.{uR, uA, v} f).obj L) ≅
      (extensionOfScalarsCochain.{uR, uA, v} f).obj (tensorComplex.{uR, max uA v} K L)) :
    ((scalarLiftFunctor.{uA, max uR v} A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((extensionOfScalarsCochain.{uR, uA, v} f).obj (tensorComplex.{uR, max uA v} K L)) ⟶
      (mapCochainComplex.{max uR uA v} (liftRingHom.{uR, uA, v} f)).obj
          (((scalarLiftFunctor.{uR, max uA v} R).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ⊗
        (mapCochainComplex.{max uR uA v} (liftRingHom.{uR, uA, v} f)).obj
          (((scalarLiftFunctor.{uR, max uA v} R).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj L) :=
  (((scalarLiftFunctor.{uA, max uR v} A).mapHomologicalComplex
      (ComplexShape.up ℤ)).mapIso e).inv ≫
    (restrictScalarsTensorComplexIso
        (ULift.ringEquiv : ULift.{max uR uA v} A ≃+* A)
        ((extensionOfScalarsCochain.{uR, uA, v} f).obj K)
        ((extensionOfScalarsCochain.{uR, uA, v} f).obj L)).inv ≫
      (MonoidalCategory.tensorIso (extendScalarsLiftChainIso.{uR, uA, v} f K)
        (extendScalarsLiftChainIso.{uR, uA, v} f L)).inv

/-- **Splitting the leading factors off the transported monoidality inverse.**

`CochainComplex.DerivedTensor.transportedMonoidalInv` is the extension of scalars along the lifted
ring map of the comparison of restriction of scalars with the total tensor product, then the
scalar-lift comparison at the total tensor complex, then
`CochainComplex.DerivedTensor.transportedMonoidalInvTail`.  This holds by definition; it is stated
so that the association the step needs is available by name. -/
public theorem transportedMonoidalInv_eq_comp_tail
    (K L : CochainComplex (ModuleCat.{max uR uA v} R) ℤ)
    (e : tensorComplex.{uA, max uR v}
        ((extensionOfScalarsCochain.{uR, uA, v} f).obj K)
        ((extensionOfScalarsCochain.{uR, uA, v} f).obj L) ≅
      (extensionOfScalarsCochain.{uR, uA, v} f).obj (tensorComplex.{uR, max uA v} K L)) :
    transportedMonoidalInv.{uR, uA, v} f K L e =
      ((mapCochainComplex.{max uR uA v} (liftRingHom.{uR, uA, v} f)).map
            (restrictScalarsTensorComplexIso
              (ULift.ringEquiv : ULift.{max uR uA v} R ≃+* R) K L).hom ≫
          (extendScalarsLiftChainIso.{uR, uA, v} f (tensorComplex.{uR, max uA v} K L)).hom) ≫
        transportedMonoidalInvTail.{uR, uA, v} f K L e := rfl

/-- **The transported monoidality inverse, moved across the degreewise unit.**

The degreewise unit of extension of scalars along the lifted ring map at the tensor of the two
scalar lifts, followed by the restriction along the lifted ring map of
`CochainComplex.DerivedTensor.transportedMonoidalInv` and of anything composed after it, is:

* the comparison of restriction of scalars along `ULift.ringEquiv` over `R` with the total tensor
  product, which is no longer under any restriction;
* `Stacks.DerivedHom.BaseChange.scalarLiftExtendUnitChain` at the total tensor complex, the
  canonical unit chain map of the scalar lift -- the right-hand side of the equation `hc₀` that
  the valued [stacks 0E1W] prefix of the keystone carries; and
* the restriction of `CochainComplex.DerivedTensor.transportedMonoidalInvTail` and the rest.

No monoidality comparison of degreewise extension of scalars stands in front of the unit any
more.  The two steps are naturality of the unit and
`Stacks.DerivedHom.BaseChange.scalarLiftExtendUnitChain_eq`, which identifies the unit followed
by the restriction of the scalar-lift comparison with the canonical unit chain map. -/
public theorem unit_comp_restrict_transportedMonoidalInv
    (K L : CochainComplex (ModuleCat.{max uR uA v} R) ℤ)
    (e : tensorComplex.{uA, max uR v}
        ((extensionOfScalarsCochain.{uR, uA, v} f).obj K)
        ((extensionOfScalarsCochain.{uR, uA, v} f).obj L) ≅
      (extensionOfScalarsCochain.{uR, uA, v} f).obj (tensorComplex.{uR, max uA v} K L))
    {Z : CochainComplex (ModuleCat.{max uR uA v} (ULift.{max uR uA v} A)) ℤ}
    (u : (mapCochainComplex.{max uR uA v} (liftRingHom.{uR, uA, v} f)).obj
          (((scalarLiftFunctor.{uR, max uA v} R).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ⊗
        (mapCochainComplex.{max uR uA v} (liftRingHom.{uR, uA, v} f)).obj
          (((scalarLiftFunctor.{uR, max uA v} R).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj L) ⟶ Z) :
    ((ModuleCat.extendRestrictScalarsAdj.{max uR uA v}
            (liftRingHom.{uR, uA, v} f)).mapHomologicalComplex (ComplexShape.up ℤ)).unit.app
          ((((scalarLiftFunctor.{uR, max uA v} R).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K) ⊗
            (((scalarLiftFunctor.{uR, max uA v} R).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj L)) ≫
        ((ModuleCat.restrictScalars.{max uR uA v}
            (liftRingHom.{uR, uA, v} f)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (transportedMonoidalInv.{uR, uA, v} f K L e ≫ u) =
      (restrictScalarsTensorComplexIso
            (ULift.ringEquiv : ULift.{max uR uA v} R ≃+* R) K L).hom ≫
        _root_.Stacks.DerivedHom.BaseChange.scalarLiftExtendUnitChain.{uR, uA, v} f
            (tensorComplex.{uR, max uA v} K L) ≫
          ((ModuleCat.restrictScalars.{max uR uA v}
              (liftRingHom.{uR, uA, v} f)).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (transportedMonoidalInvTail.{uR, uA, v} f K L e ≫ u) :=
  unitMapCompTail _ _ _ _ _
    (_root_.Stacks.DerivedHom.BaseChange.scalarLiftExtendUnitChain_eq.{uR, uA, v} f
      (tensorComplex.{uR, max uA v} K L))

end CochainComplex.DerivedTensor

end
