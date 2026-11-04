module

public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquareAction
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.AlgebraActionKFlat
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ExtensionSquareMateUnitSquare

/-!
# The two algebra actions, reduced to one identity about the lax monoidal structure map

`StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquareAction` proves, for an arbitrary square of
adjunctions with projection formulas on the two horizontal edges, that **the Beck--Chevalley mate
is a morphism of actions**; the form
`Stacks.CategoryTheory.BaseChange.action_comp_eq_of_tensorComparisonOfIso` needs only a 2-cell
identified with its mate and one identity relating a lax structure map to the comparison
`Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso` of the two endofunctors.

This file instantiates that statement at the square

```
  R ---→ A
  |      |
  v      v
  R' --→ A ⊗_R R'
```

of derived categories, at four arbitrary models of derived extension of scalars.  Under the
instantiation

* the two actions of `Stacks.CategoryTheory.BaseChange.action` are `Dualizing.algebraActionLeft`
  and `Dualizing.algebraActionRight` of
  `StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.AlgebraActionReduction`;
* the 2-cell is the inverse of `Dualizing.derivedBaseChangeSquareIso` and its mate is the inverse
  comparison `Dualizing.restrictionBaseChangeIsoGeneral` of [stacks 0661], which is
  `Dualizing.derivedBaseChangeSquareIso_mate_eq'` — unconditional;
* the lax structure map is `Dualizing.derivedTensorBaseChange`, the lax monoidal structure map `μ`
  of derived base change along `R → R'`, and the transformation of endofunctors is tensoring with
  `Dualizing.derivedBaseChangeAlgebraIso`.

So the projection-formula compatibility of [stacks 0E2A] — `Dualizing.KFlatAlgebraActionEq`, and
with it `Dualizing.UnitBridgeCompatibility` — follows from one identity, recorded here as
`Dualizing.TensorComparisonCompatibility`:

`μ_{X, A} ≫ tensorComparisonOfIso X = 𝟙_{X ⊗ᴸ_R R'} ⊗ derivedBaseChangeAlgebraIso`,

for `X` an object of `D(R)`.  Both sides of it are natural in `X`, and the variable `X` it has
to be checked at is a variable of `D(R)`, where a K-flat representative over `R` is available —
unlike in the earlier reductions of this directory, which asked for a K-flat representative over
`A`.  Two reductions of that variable are proved elsewhere and compose:
`Dualizing.tensorComparisonCompatibility_of_kFlat` restricts it to the classes of K-flat complexes
of `R`-modules, and `Dualizing.tensorComparisonCompatibility_of_restrict_extend` restricts it to
the objects `(Ff X)|_R` restricted from `D(A)`.

**What cannot be done.** The obligation is *not* reducible to its value at the regular module in
degree zero, although both of its sides are components of natural isomorphisms of two exact
direct-sum-preserving functors of `X` and `R[0]` is a compact generator of `D(R)`.  The dévissage
of `StacksFrontier/Homology/Devissage/CompactGeneratedNatTrans.lean` propagates *invertibility* of one
morphism of functors along the cell presentation of [stacks 09SN], and
`StacksFrontier/Homology/Devissage/CompactGeneratedNatTransEquality.lean` records why its analogue for
an *equality* of two morphisms of functors does not exist: the agreement locus of two such
morphisms is closed under isomorphisms, shifts and direct sums, but not under extension in a
distinguished triangle, since every sandwich through the two connecting morphisms satisfies the
whole of what agreement at the other two vertices imposes.  That both sides here are invertible
does not help — a morphism of functors that is invertible at a compact generator is invertible
everywhere, so adding a phantom to one of the two sides produces another invertible morphism
agreeing with it at `R[0]`.

**What is not done here.** `Dualizing.TensorComparisonCompatibility` is not proved.  What this
file changes is the shape of the remaining obligation: neither of the two units of [stacks 0A70],
neither bridge `Dualizing.derivedHomRestrictScalarsInternalHomIsoOfModel` of [stacks 0E2A], and
no derived-Hom base-change morphism of [stacks 0E1X] occurs in it — the factors are the two
projection formulas, the comparison of [stacks 0661], the square isomorphism, `μ`, and the base
change of the algebra.

## Main definitions

* `Dualizing.TensorComparisonCompatibility` — the remaining obligation, at an object of `D(R)`.

## Main results

* `Dualizing.algebraAction_app_eq_of_tensorComparisonCompatibility` — **the instantiation**: the
  two algebra actions agree at an object `W` of `D(A)` as soon as the obligation holds at `W|_R`.
* `Dualizing.algebraActionCanonical_app_eq_of_tensorComparisonCompatibility` — the same at the
  canonical models, which is the form `Dualizing.KFlatAlgebraActionEq`, the hypothesis `hAct` of
  the library's [stacks 0BZM] and [stacks 0BZN], quantifies over.

## Implementation notes

The two algebra actions are read through `Dualizing.algebraActionLeft_app` and
`Dualizing.algebraActionRight_app`, which present them as explicit composites, and the abstract
statement is used in the form
`Stacks.CategoryTheory.BaseChange.comp_counit_eq_of_tensorComparisonOfIso`, whose two sides are
already bracketed the way those composites are: the bracketing is the one thing that is *not*
definitional here, associativity of composition being a field of `CategoryTheory.Category` rather
than a reduction.  The abstract statement is also the pointwise one — its lax structure map and
its transformation of the two tensor endofunctors are plain morphisms, not natural
transformations — because unifying the functors `Lg ⋙ TensM` and `Tens ⋙ Lg` against the
derived-category instantiation forces the elaborator to unfold
`StacksDraft.DerivedHom.derivedHomAdjunction`, which is not exposed.

`Dualizing.derivedExtendRestrictScalarsTensorFunctor_map` is the one unfolding that has to be
named: it rewrites the action of the projection formula's target on morphisms into the tensor
bifunctor of [stacks 0A63], which is what the naturality hypothesis of the abstract statement is
checked against.

The four `IsLeftDerivedFunctor` arguments are instance binders, as in
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ExtensionSquareMateUnitSquare`, so that the
comparison of [stacks 0661] built here agrees on the nose with the one
`Dualizing.derivedBaseChangeSquareIso_mate_eq'` is stated for; `Dualizing.algebraActionLeft` and
`Dualizing.algebraActionRight` take the two over `R` and over `A` explicitly, and the section
instances are passed to them.

No `@[stacks]` attribute is placed here: the obligation is still open, so nothing in this file
covers a tag.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0BZM](https://stacks.math.columbia.edu/tag/0BZM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits StacksDraft.DerivedHom
open CochainComplex.DerivedExtensionScalars
open scoped ChangeOfRings

attribute [local instance] HasDerivedCategory.standard

namespace Dualizing

universe uR uA uRp uS uT w v

/-- Tensoring with the algebra computes its action on morphisms off the tensor bifunctor: the
projection formula's target `Dualizing.derivedExtendRestrictScalarsTensorFunctor` is the partial
application `StacksDraft.DerivedHom.DerivedHomAdjunction.tensorAt` of the bifunctor of
[stacks 0A63] at `Dualizing.derivedAlgebraSingle`, so this is one unfolding. -/
theorem derivedExtendRestrictScalarsTensorFunctor_map {S : Type uS} {T : Type uT} [CommRing S]
    [CommRing T] (g : S →+* T)
    {X Y : DerivedCategory (ModuleCat.{max w uS uT} S)} (h : X ⟶ Y) :
    (derivedExtendRestrictScalarsTensorFunctor.{uS, uT, w} g).map h =
      (derivedHomAdjunctionOverRing.{uS, max w uS uT, max w uS uT + 1} S).tensor.map
        ((h, 𝟙 (derivedAlgebraSingle.{uS, uT, w} g)) :
          (X, derivedAlgebraSingle.{uS, uT, w} g) ⟶
            (Y, derivedAlgebraSingle.{uS, uT, w} g)) :=
  rfl

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} {R' : Type uRp} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']
  (hTor : RingTheory.TorIndependence.TorIndependent R A R')
  (baseChangeR :
    DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} R'))
  (comparisonR :
    DerivedCategory.Q ⋙ baseChangeR ⟶
      (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (baseChangeA :
    DerivedCategory (ModuleCat.{max v uR uA uRp} A) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (comparisonA :
    DerivedCategory.Q ⋙ baseChangeA ⟶
      (ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
        (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (Ff : DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp} A))
  (alphaf : DerivedCategory.Q ⋙ Ff ⟶
    (ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
      (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (Fi : DerivedCategory (ModuleCat.{max v uR uA uRp} R') ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (alphai : DerivedCategory.Q ⋙ Fi ⟶
    (ModuleCat.extendScalars.{uRp, max uA uRp, max v uR uA uRp}
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)

variable [hf : Ff.IsLeftDerivedFunctor alphaf
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]
  [hA : baseChangeA.IsLeftDerivedFunctor comparisonA
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} A) (ComplexShape.up ℤ))]
  [hR : baseChangeR.IsLeftDerivedFunctor comparisonR
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]
  [hi : Fi.IsLeftDerivedFunctor alphai
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R') (ComplexShape.up ℤ))]

include hf hA hR hi in
/-- **The remaining obligation of [stacks 0E2A], in the tensor-comparison form.** At an object `X`
of `D(R)`, the lax monoidal structure map `Dualizing.derivedTensorBaseChange` of derived base
change along `R → R'` at `(X, A)`, followed by the comparison
`Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso` of the two derived tensor products across
the square — built from the two projection formulas
`Dualizing.derivedExtendRestrictScalarsTensorIso`, the square isomorphism
`Dualizing.derivedBaseChangeSquareIso` and the comparison
`Dualizing.restrictionBaseChangeIsoGeneral` of [stacks 0661] — is tensoring the identity of
`X ⊗ᴸ_R R'` with the base change `Dualizing.derivedBaseChangeAlgebraIso` of the algebra.

Neither unit of [stacks 0A70], neither bridge of [stacks 0E2A] and no derived-Hom base-change
morphism of [stacks 0E1X] occurs: this is an identity between the two canonical comparisons of
`(X ⊗ᴸ_R A) ⊗ᴸ_R R'` with `(X ⊗ᴸ_R R') ⊗ᴸ_{R'} (A ⊗_R R')`.

It is not proved. -/
def TensorComparisonCompatibility
    (X : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) : Prop :=
  derivedTensorBaseChange.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR X
        (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) ≫
      Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso
        (derivedExtendRestrictScalarsTensorIso.{uR, uA, max v uRp} (algebraMap R A) Ff alphaf)
        (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
          (Algebra.TensorProduct.includeRight :
            R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai)
        (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR comparisonR
          Fi alphai)
        (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR hR baseChangeA
          comparisonA hA) X =
    (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
      ((𝟙 (baseChangeR.obj X),
          (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR hR baseChangeA
            comparisonA hA).hom) :
        (baseChangeR.obj X,
            baseChangeR.obj
              (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) ⟶
          (baseChangeR.obj X,
            derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom))

include hf hA hR hi in
/-- **The two algebra actions agree at an object, granted
`Dualizing.TensorComparisonCompatibility` at its restriction.** This is
`Stacks.CategoryTheory.BaseChange.action_comp_eq_of_tensorComparisonOfIso` at the base-change
square: the 2-cell is the inverse of `Dualizing.derivedBaseChangeSquareIso`, its mate is the
inverse comparison of [stacks 0661] by `Dualizing.derivedBaseChangeSquareIso_mate_eq'`, the two
projection formulas are the two instances of
`Dualizing.derivedExtendRestrictScalarsTensorIso`, and the lax structure map is the lax monoidal
structure map of derived base change along `R → R'`. -/
theorem algebraAction_app_eq_of_tensorComparisonCompatibility
    (W : DerivedCategory (ModuleCat.{max v uR uA uRp} A))
    (h : TensorComparisonCompatibility hTor baseChangeR comparisonR baseChangeA comparisonA
      Ff alphaf Fi alphai
      ((ModuleCat.restrictScalars.{max v uR uA uRp}
        (algebraMap R A)).mapDerivedCategory.obj W)) :
    (algebraActionLeft hTor baseChangeR comparisonR hR baseChangeA comparisonA hA Fi alphai).app
        W =
      (algebraActionRight hTor baseChangeR comparisonR hR baseChangeA comparisonA hA Ff
        alphaf).app W := by
  rw [algebraActionLeft_app hTor baseChangeR comparisonR hR baseChangeA comparisonA hA Fi alphai W,
    algebraActionRight_app hTor baseChangeR comparisonR hR baseChangeA comparisonA hA Ff alphaf W]
  exact Stacks.CategoryTheory.BaseChange.comp_counit_eq_of_tensorComparisonOfIso
    (derivedExtensionScalarsAdjunction.{uR, uA, max v uRp} (algebraMap R A) Ff alphaf)
    (derivedExtensionScalarsAdjunction.{uRp, max uA uRp, max v uR}
      (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai)
    (derivedExtendRestrictScalarsTensorIso.{uR, uA, max v uRp} (algebraMap R A) Ff alphaf)
    (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
      (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai)
    (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR comparisonR
      Fi alphai)
    (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR hR baseChangeA comparisonA hA)
    (derivedBaseChangeSquareIso_mate_eq' hTor baseChangeR comparisonR baseChangeA comparisonA
      Ff alphaf Fi alphai)
    W
    ((derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
      (((restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR hR baseChangeA
              comparisonA hA).hom.app W,
          𝟙 (baseChangeR.obj (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))) :
        ((ModuleCat.restrictScalars
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
              (baseChangeA.obj W),
            baseChangeR.obj (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) ⟶
          (baseChangeR.obj
              ((ModuleCat.restrictScalars.{max v uR uA uRp}
                (algebraMap R A)).mapDerivedCategory.obj W),
            baseChangeR.obj (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))))
    ((derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
      ((𝟙 (baseChangeR.obj
              ((ModuleCat.restrictScalars.{max v uR uA uRp}
                (algebraMap R A)).mapDerivedCategory.obj W)),
          (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR hR baseChangeA
            comparisonA hA).hom) :
        (baseChangeR.obj
              ((ModuleCat.restrictScalars.{max v uR uA uRp}
                (algebraMap R A)).mapDerivedCategory.obj W),
            baseChangeR.obj (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) ⟶
          (baseChangeR.obj
              ((ModuleCat.restrictScalars.{max v uR uA uRp}
                (algebraMap R A)).mapDerivedCategory.obj W),
            derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom)))
    ((derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
      ((𝟙 ((ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
              (baseChangeA.obj W)),
          (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR hR baseChangeA
            comparisonA hA).hom) :
        ((ModuleCat.restrictScalars
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
              (baseChangeA.obj W),
            baseChangeR.obj (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) ⟶
          ((ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
              (baseChangeA.obj W),
            derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom)))
    (derivedTensorBaseChange.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR
      ((ModuleCat.restrictScalars.{max v uR uA uRp} (algebraMap R A)).mapDerivedCategory.obj W)
      (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))
    (by
      rw [derivedExtendRestrictScalarsTensorFunctor_map]
      refine Eq.trans ((derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
          max v uR uA uRp + 1} R').tensor_map_comp _ _ _ _) (Eq.trans ?_
        ((derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
          max v uR uA uRp + 1} R').tensor_map_comp _ _ _ _).symm)
      exact congrArg _ (Prod.ext ((Category.comp_id _).trans (Category.id_comp _).symm)
        ((Category.id_comp _).trans (Category.comp_id _).symm)))
    h

include hA hR in
/-- **The two algebra actions at the canonical models agree, granted
`Dualizing.TensorComparisonCompatibility` there.**
`Dualizing.algebraAction_app_eq_of_tensorComparisonCompatibility` read at the models of derived
extension of scalars along `R → A` and `R' → A ⊗_R R'` chosen by
`Dualizing.canonicalExtensionModel` and `Dualizing.canonicalExtensionModelIncludeRight`, which are
the ones `Dualizing.algebraActionLeftCanonical` and `Dualizing.algebraActionRightCanonical` use and
hence the ones `Dualizing.KFlatAlgebraActionEq` quantifies over.  So the hypothesis `hAct` carried
by the library's [stacks 0BZM] and [stacks 0BZN] follows from the obligation at every
Tor-independent square. -/
theorem algebraActionCanonical_app_eq_of_tensorComparisonCompatibility
    (W : DerivedCategory (ModuleCat.{max v uR uA uRp} A))
    (h : @TensorComparisonCompatibility R A R' _ _ _ _ _ hTor baseChangeR comparisonR
      baseChangeA comparisonA
      (canonicalExtensionModel.{uR, uA, max v uRp} R A).functor
      (canonicalExtensionModel.{uR, uA, max v uRp} R A).comparison
      (canonicalExtensionModelIncludeRight.{uR, uA, uRp, max v uR} R A R').functor
      (canonicalExtensionModelIncludeRight.{uR, uA, uRp, max v uR} R A R').comparison
      (canonicalExtensionModel.{uR, uA, max v uRp} R A).isLeftDerived hA hR
      (canonicalExtensionModelIncludeRight.{uR, uA, uRp, max v uR} R A R').isLeftDerived
      ((ModuleCat.restrictScalars.{max v uR uA uRp}
        (algebraMap R A)).mapDerivedCategory.obj W)) :
    (algebraActionLeftCanonical hTor baseChangeR comparisonR hR baseChangeA
        comparisonA hA).app W =
      (algebraActionRightCanonical hTor baseChangeR comparisonR hR baseChangeA
        comparisonA hA).app W :=
  @algebraAction_app_eq_of_tensorComparisonCompatibility R A R' _ _ _ _ _ hTor baseChangeR
    comparisonR baseChangeA comparisonA
    (canonicalExtensionModel.{uR, uA, max v uRp} R A).functor
    (canonicalExtensionModel.{uR, uA, max v uRp} R A).comparison
    (canonicalExtensionModelIncludeRight.{uR, uA, uRp, max v uR} R A R').functor
    (canonicalExtensionModelIncludeRight.{uR, uA, uRp, max v uR} R A R').comparison
    (canonicalExtensionModel.{uR, uA, max v uRp} R A).isLeftDerived hA hR
    (canonicalExtensionModelIncludeRight.{uR, uA, uRp, max v uR} R A R').isLeftDerived W h

end Dualizing

end
