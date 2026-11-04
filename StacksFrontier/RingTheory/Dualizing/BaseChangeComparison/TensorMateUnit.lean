module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorMateFormula

/-!
# The lax monoidal structure map of derived base change, characterized by the unit

`Dualizing.derivedTensorBaseChange` is the lax monoidal structure map
`μ_{X,Y} : F X ⊗ᴸ_A F Y ⟶ F (X ⊗ᴸ_R Y)` of a model `F` of derived extension of scalars along
`f : R → A`, built in
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorMate` as a *double* adjoint transpose
through the derived-Hom base-change morphism of [stacks 0E1X].  Being a double transpose through a
morphism that is itself a mate, it is opaque, and in particular it is not known to be invertible:
the note in `…BaseChangeComparison.TensorMate` records that invertibility "would have to come from
Stacks 068I through the missing bridge", the monoidality isomorphism of derived base change being
`CochainComplex.DerivedTensor.derivedExtensionScalarsTensorIso`.

This file supplies the *specification* that bridge has to meet.  It records one equation which
determines `μ` and in which **the morphism of [stacks 0E1X] does not occur**: transposing `μ` over
the tensor--Hom adjunction of [stacks 0A63] over `A`, and then over the extension-of-scalars
adjunction of [stacks 0GMT] along `f`, gives the transpose of the unit of [stacks 0GMT] at
`X ⊗ᴸ_R Y` followed by the change-of-rings isomorphism
`Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso` of [stacks 0E1W].  Both transposes
are bijections, so the equation characterizes `μ` outright.

What this buys: a second construction of a lax monoidal structure map — the monoidality
isomorphism of [stacks 068I], transported into the vocabulary of [stacks 0A63] — can be identified
with `μ`, and hence shown to be `μ`'s inverse-bearing twin, by checking this single equation, with
no unfolding of either double transpose.  Three facts make that a finite task rather than an open
one, and none of them was visible from `…BaseChangeComparison.TensorMate`:

* `CochainComplex.DerivedTensor.canonicalDerivedTensorProductGeneral` supplies
  `CochainComplex.DerivedTensor.DerivedTensorProductGeneral.{u, v}` data at an *arbitrary* module
  universe, so [stacks 068I] can be read at the two universes
  `DerivedExtensionScalarsTensorIso` asks for.  The note in `…BaseChangeComparison.TensorMate` that
  the library has no such instance "at independent ring and module universes" is accurate only for
  the free-universe shape of the [stacks 0A63] bundle, not for the module universe.
* `CochainComplex.DerivedTensor.derivedTensor_comparison` computes the tensor bifunctor of
  `StacksDraft.DerivedHom.derivedHomAdjunctionOverRing` on K-flat representatives, which is the
  same level at which `DerivedExtensionScalarsTensorIso.comparison` characterizes [stacks 068I].
* `Dualizing.derivedHomAdjunctionTensorIso` already identifies the canonical derived tensor product
  with the tensor of the [stacks 0A63] bundle at equal universes, which is the model both sides are
  transported from along `StacksDraft.DerivedHom.derivedScalarEquivalence`.

**What is not done here.** The bridge itself is not built: nothing in this file constructs a
monoidality isomorphism or proves `μ` invertible, and the projection-formula compatibility of
[stacks 0E2A] — `Dualizing.KFlatAlgebraActionEq`, and with it
`Dualizing.UnitBridgeCompatibility` — remains open.

## Main results

* `Dualizing.unit_comp_homEquiv_symm_derivedTensorBaseChange` — **the characterization**: the
  double transpose of `μ` is the transpose of the unit of [stacks 0GMT], followed by the
  change-of-rings isomorphism of [stacks 0E1W].
* `Dualizing.eq_derivedTensorBaseChange_of_unit` — it *is* a characterization: a morphism
  satisfying that equation is `μ`.

## Implementation notes

The proof is adjunction yoga and uses no universe lift, no K-flat representative and no universal
property of a derived functor: the closed formula `Dualizing.derivedTensorBaseChange_eq`, the
naturality of the unit of [stacks 0GMT], the computation
`Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange_homEquiv` of the transpose of
[stacks 0E1X], and `StacksDraft.DerivedHom.DerivedHomAdjunction.tensorHomUnit_comp_hom_map`
("coevaluation detects transposition"), which is what cancels the coevaluation that the double
transpose leaves behind.

The chain is written with `Eq.trans` and `congrArg` rather than `rw`.  Three of the steps have
left-hand sides that `rw` reports as absent although they are displayed identically to the subterm
they should match — the pair-morphism and `Functor.map` arguments of the bifunctors of
[stacks 0A63] are elaborated against the product category's `Quiver.Hom`, the obstruction already
recorded in `…BaseChangeComparison.TensorMateFormula`.  Definitional unification crosses it.

`CategoryTheory.Adjunction.homEquiv_unit` is applied with its three explicit arguments rather than
rewritten with, for the same reason.

No `@[stacks]` attribute is placed here: this is a characterization of a construction, and the
statement of [stacks 068I] it is meant to be matched against is formalized elsewhere.

## References

* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 0E1X](https://stacks.math.columbia.edu/tag/0E1X)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor StacksDraft.DerivedHom
open CochainComplex.DerivedExtensionScalars
open scoped ChangeOfRings

attribute [local instance] HasDerivedCategory.standard

universe uR uA uM

namespace Dualizing

attribute [local instance] extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
  (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
    DerivedCategory (ModuleCat.{max uR uA uM} A))
  (comparison : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]

/-- **The lax monoidal structure map of derived base change, characterized by the unit of
Stacks 0GMT and the change-of-rings isomorphism of Stacks 0E1W — with Stacks 0E1X eliminated.**

`Dualizing.derivedTensorBaseChange` is a double adjoint transpose through the derived-Hom
base-change morphism of [stacks 0E1X], which makes it opaque.  This equation determines it
without mentioning that morphism at all: transposing `μ_{X,Y}` over the tensor--Hom adjunction of
[stacks 0A63] over `A` and then over the extension-of-scalars adjunction of [stacks 0GMT] along
`f` gives the transpose of the unit of [stacks 0GMT] at `X ⊗ᴸ_R Y`, followed by the
change-of-rings isomorphism of [stacks 0E1W].

Both transposes are bijections, so this *characterizes* `μ`; see
`Dualizing.eq_derivedTensorBaseChange_of_unit`.  Since the right-hand side mentions only the unit
of [stacks 0GMT], the Hom equivalence of [stacks 0A63] over `R` and the isomorphism of
[stacks 0E1W], this is the equation a *different* construction of the lax monoidal structure map —
in particular the monoidality isomorphism of [stacks 068I] — has to be checked against in order to
be identified with `μ`. -/
theorem unit_comp_homEquiv_symm_derivedTensorBaseChange
    (X Y : DerivedCategory (ModuleCat.{max uR uA uM} R)) :
    (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app X ≫
        (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map
          (((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).homEquiv (F.obj
              X) (F.obj Y)
              (F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1}
                  R).tensor.obj (X, Y)))).symm
            (derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y)) =
      ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv X Y
            ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj (F.obj
                ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.obj
                    (X, Y))))).symm
          ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app
              ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.obj (X,
                  Y))) ≫
        (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
            comparison).hom.app
          (Opposite.op Y, F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1}
              R).tensor.obj (X, Y))) := by
  have hmu : (((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).homEquiv
      (F.obj X) (F.obj Y)
        (F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.obj
            (X, Y)))).symm
      (derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y)) =
      F.map ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensorHomUnit X
          Y) ≫
        Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR, uA, uM} f F comparison Y
            ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.obj (X,
                Y)) := by
    rw [derivedTensorBaseChange_eq.{uR, uA, uM} f F comparison X Y, AddEquiv.symm_apply_apply]
    rfl
  have hnat : (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app X ≫
        (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map (F.map
            ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensorHomUnit X
                Y)) =
      (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensorHomUnit X Y ≫
        (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app
          ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).hom.obj
              (Opposite.op Y, (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1}
                  R).tensor.obj (X, Y))) :=
    ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.naturality
        ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensorHomUnit X
            Y)).symm
  have hbch : (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app
          ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).hom.obj
              (Opposite.op Y, (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1}
                  R).tensor.obj (X, Y))) ≫
        (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map
            (Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR, uA, uM} f F comparison
                Y ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.obj
                    (X, Y))) =
      (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).hom.map
          ((𝟙 (Opposite.op Y), (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F
              comparison).unit.app ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM +
                  1} R).tensor.obj (X, Y))) :
            (Opposite.op Y, (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1}
                R).tensor.obj (X, Y)) ⟶
              (Opposite.op Y, (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
                  (F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1}
                      R).tensor.obj (X, Y))))) ≫
        (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
            comparison).hom.app (Opposite.op Y, F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA
                uM, max uR uA uM + 1} R).tensor.obj (X, Y))) :=
    ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).homEquiv_unit
      _ _ _).symm.trans
      (Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange_homEquiv.{uR, uA, uM} f F
        comparison Y
        ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
          max uR uA uM + 1} R).tensor.obj (X, Y)))
  have hsplit : (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map
        (F.map ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
            max uR uA uM + 1} R).tensorHomUnit X Y) ≫
          Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR, uA, uM} f F comparison Y
              ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.obj (X,
                  Y))) =
      (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map
          (F.map ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
            max uR uA uM + 1} R).tensorHomUnit X Y)) ≫
        (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map
            (Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR, uA, uM} f F comparison
                Y ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.obj
                    (X, Y))) :=
    Functor.map_comp _ _ _
  refine Eq.trans (congrArg (fun z => _ ≫ (ModuleCat.restrictScalars.{max uR uA uM}
      f).mapDerivedCategory.map z) hmu) ?_
  refine Eq.trans (congrArg (fun z => _ ≫ z) hsplit) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫ _) hnat) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun z => _ ≫ z) hbch) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact congrArg (fun z => z ≫ _)
    (DerivedHomAdjunction.tensorHomUnit_comp_hom_map (derivedHomAdjunctionOverRing.{uR, max uR uA
        uM, max uR uA uM + 1} R) X Y _ _)

/-- **The characterization of `Dualizing.derivedTensorBaseChange` is a characterization.** A
morphism `F X ⊗ᴸ_A F Y ⟶ F (X ⊗ᴸ_R Y)` satisfying the equation of
`Dualizing.unit_comp_homEquiv_symm_derivedTensorBaseChange` is the lax monoidal structure map of
derived base change.  Both transposes involved are bijections, so there is exactly one such
morphism. -/
theorem eq_derivedTensorBaseChange_of_unit
    (X Y : DerivedCategory (ModuleCat.{max uR uA uM} R))
    (g : (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensor.obj (F.obj X,
        F.obj Y) ⟶ F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1}
            R).tensor.obj (X, Y)))
    (hg : (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app X ≫
        (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map
          (((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).homEquiv (F.obj
              X) (F.obj Y)
              (F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1}
                  R).tensor.obj (X, Y)))).symm g) =
      ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv X Y
            ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj (F.obj
                ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.obj
                    (X, Y))))).symm
          ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app
              ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.obj (X,
                  Y))) ≫
        (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
            comparison).hom.app
          (Opposite.op Y, F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1}
              R).tensor.obj (X, Y)))) :
    g = derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y := by
  refine ((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).homEquiv (F.obj X)
      (F.obj Y)
    (F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.obj (X,
        Y)))).symm.injective ?_
  refine ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).homEquiv X
    ((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).hom.obj
      (Opposite.op (F.obj Y),
        F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
          max uR uA uM + 1} R).tensor.obj (X, Y))))).injective ?_
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, hg,
    unit_comp_homEquiv_symm_derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y]

end Dualizing

end
