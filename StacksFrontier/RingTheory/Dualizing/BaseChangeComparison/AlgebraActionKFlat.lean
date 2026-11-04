module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.RestrictionIsoComputation
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorMateFormula

/-!
# The two algebra actions, transposed: the obligation with the projection formulas removed

`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.AlgebraActionReduction` reduces the
projection-formula compatibility of [stacks 0E2A] to one equation between two natural
transformations

`baseChangeA(W)|_{R'} ⊗ᴸ_{R'} (A ⊗ᴸ_R R') ⟶ (W|_R) ⊗ᴸ_R R'`,

`Dualizing.algebraActionLeft` and `Dualizing.algebraActionRight`, evaluated at the classes of
K-flat complexes of `A`-modules.  Both are composites of whiskerings, so their components are
explicit; but each of them contains a *projection formula* — the identification
`Dualizing.derivedExtendRestrictScalarsTensorIso` of restricted derived extension of scalars with
derived tensoring by the algebra, which is itself a transport across a universe lift — and a
counit of derived extension of scalars, and the right-hand side also contains the lax monoidal
structure map `Dualizing.derivedTensorBaseChange` of derived base change, a double adjoint
transpose.  Nothing in that shape is amenable to a diagram chase.

This file transposes the equation under the tensor--Hom adjunction of [stacks 0A63] over `R'`, and
in the transposed form **none of those three factors survives**.  What makes this possible is one
observation, proved here in the abstract: *the transpose of an algebra action is a unit*.  For a
ring homomorphism `f : S → T` and a model `F` of derived extension of scalars along it, the action

`(W|_S) ⊗ᴸ_S T ⟶ (F (W|_S))|_S ⟶ W|_S`

— the inverse projection formula followed by the counit — transposes to

`W|_S ⟶ RHom_S(T, W|_S)`

equal to the restriction of the unit of the derived restriction/Hom adjunction of [stacks 0A70]
followed by the bridge `Dualizing.derivedHomRestrictScalarsInternalHomIsoOfModel` of
[stacks 0E2A].  That is an identity about adjunctions only: the projection formula enters the
bridge as the isomorphism of left adjoints, and uniqueness of right adjoints does the rest.

Transposing each side with this identity, with the dinaturality of the Hom equivalence in the
internal-Hom variable (which absorbs `Dualizing.derivedBaseChangeAlgebraIso`), and — on the right
— with the closed formula `Dualizing.derivedTensorBaseChange_comp_map` for the lax monoidal
structure map, turns the obligation into `Dualizing.UnitBridgeCompatibility`: an equation between
two morphisms `baseChangeA(W)|_{R'} ⟶ RHom_{R'}(A ⊗ᴸ_R R', (W|_R) ⊗ᴸ_R R')` whose only factors are
the two units of [stacks 0A70], the two bridges of [stacks 0E2A], the comparison of [stacks 0661],
the base change `Dualizing.derivedBaseChangeAlgebraIso` of the algebra, and the derived-Hom
base-change morphism of [stacks 0E1X].  The equivalence is an `Iff`, not an implication: the Hom
equivalence is a bijection, so nothing is weakened.

**What is not done here.** `Dualizing.UnitBridgeCompatibility` is *not* proved here; this file
only changes the shape of what has to be proved.  The projection-formula compatibility of
[stacks 0E2A] that it reformulates, `Dualizing.KFlatAlgebraActionEq`, is proved by another route
as `Dualizing.kFlatAlgebraActionEq` in
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ProjectionCompatibilityResolved`.

## Main definitions

* `Dualizing.UnitBridgeCompatibility` — the obligation in transposed form.

## Main results

* `CategoryTheory.Adjunction.homEquiv_comp_rightAdjointUniq` — two adjunctions with the same left
  adjoint have transposes that differ by the canonical isomorphism of their right adjoints.
* `CategoryTheory.Adjunction.homEquiv_isoLeft_comp_counit` — **the abstract transpose identity**:
  for `L ⊣ Rr`, `Rr ⊣ H` and `Tens ⊣ Hm` with `pf : L ⋙ Rr ≅ Tens`, the transpose of
  `pf⁻¹ ≫ Rr(ε)` is `Rr(η)` followed by the comparison of the two right adjoints of `L ⋙ Rr`.
* `StacksDraft.DerivedHom.DerivedHomAdjunction.homEquiv_tensorHomAdjunctionAt` — the Hom
  equivalence of the adjunction of [stacks 0A63] at a fixed object is the inverse of the structure
  field.
* `Dualizing.homEquiv_symm_algebraAction`, `Dualizing.algebraAction_eq_homEquiv` — **the transpose
  of the algebra action is the unit of [stacks 0A70] through the bridge of [stacks 0E2A]**.
* `Dualizing.algebraActionLeft_app`, `Dualizing.algebraActionRight_app` — the two components as
  explicit composites, at an arbitrary object of `D(A)`.
* `Dualizing.algebraActionLeft_app_eq_homEquiv`,
  `Dualizing.algebraActionRight_app_eq_homEquiv` — each component as a transpose.
* `Dualizing.algebraAction_app_eq_iff_unitBridgeCompatibility` and its canonical form — **the
  reduction**: the two algebra actions agree at an object precisely when
  `Dualizing.UnitBridgeCompatibility` holds there.

## Implementation notes

`Dualizing.algebraActionLeft_app` and `Dualizing.algebraActionRight_app` are `rfl`: both
transformations are composites of whiskerings, every one of which computes its components by
definition.  They are stated at an arbitrary object of `D(A)` rather than at `RHom_R(A, K)`, which
is where `Dualizing.projectionFormulaCompatibility_of_algebraActionSquare` reads them.

The two transposition proofs are written with `Eq.trans` and `congrArg` rather than `rw`: the
pair-morphism arguments of the tensor and internal-Hom bifunctors are elaborated at the product
category's `Quiver.Hom`, against which keyed matching does not fire — the same obstruction recorded
in `StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorMateFormula`.  Definitional
unification crosses it.

`StacksDraft.DerivedHom.DerivedHomAdjunction.tensorHomAdjunctionAt` is built by
`CategoryTheory.Adjunction.mkOfHomEquiv` inside a tactic block, so its Hom equivalence is reached
through `CategoryTheory.Adjunction.mkOfHomEquiv_homEquiv`; the two naturality fields it is given
are propositions and need not be reproduced.

No `@[stacks]` attribute is placed here: nothing in this file covers a tag.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 0E1X](https://stacks.math.columbia.edu/tag/0E1X)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
* [Stacks Project, Tag 0BZM](https://stacks.math.columbia.edu/tag/0BZM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits StacksDraft.DerivedHom
open CochainComplex.DerivedExtensionScalars
open scoped ChangeOfRings

attribute [local instance] HasDerivedCategory.standard

universe uR uA uRp uS v w

namespace CategoryTheory.Adjunction

/-- **Transposing along two adjunctions with the same left adjoint.** If `G` and `G'` are both
right adjoint to `F`, the transpose of a morphism along the second adjunction is its transpose
along the first followed by the canonical isomorphism `G ≅ G'`. -/
theorem homEquiv_comp_rightAdjointUniq {C D : Type*} [Category* C] [Category* D]
    {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') (X : C) (Y : D) (k : F.obj X ⟶ Y) :
    adj2.homEquiv X Y k = adj1.homEquiv X Y k ≫ (rightAdjointUniq adj1 adj2).hom.app Y := by
  rw [homEquiv_unit, homEquiv_unit, Category.assoc,
    (rightAdjointUniq adj1 adj2).hom.naturality k, ← Category.assoc,
    unit_rightAdjointUniq_hom_app]

/-- **The transpose of an action is a unit.** Let `adj1 : L ⊣ Rr` and `adj2 : Rr ⊣ H`, so that
`L ⋙ Rr` is left adjoint to `H ⋙ Rr`, let `adjT : Tens ⊣ Hm` be a second adjunction and let
`pf : L ⋙ Rr ≅ Tens` identify the two left adjoints.  Then the transpose along `adjT` of

`Tens (Rr W) ⟶ Rr (L (Rr W)) ⟶ Rr W`,

the inverse of `pf` followed by `Rr` applied to the counit of `adj1`, is `Rr` applied to the unit
of `adj2` followed by the canonical isomorphism `H ⋙ Rr ≅ Hm` of the two right adjoints of
`L ⋙ Rr`.

This is the one input of the transposition carried out in this file, and it uses nothing but the
triangle identity of `adj1`, the naturality of the unit of `adj2` and uniqueness of right
adjoints. -/
theorem homEquiv_isoLeft_comp_counit {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {Rr : D ⥤ C} {H : C ⥤ D} {Tens Hm : C ⥤ C}
    (adj1 : L ⊣ Rr) (adj2 : Rr ⊣ H) (adjT : Tens ⊣ Hm) (pf : L ⋙ Rr ≅ Tens) (W : D) :
    adjT.homEquiv (Rr.obj W) (Rr.obj W)
        (pf.inv.app (Rr.obj W) ≫ Rr.map (adj1.counit.app W)) =
      Rr.map (adj2.unit.app W) ≫
        (rightAdjointUniq (adj1.comp adj2) (adjT.ofNatIsoLeft pf.symm)).hom.app (Rr.obj W) := by
  have h3 : (adj1.comp adj2).homEquiv (Rr.obj W) (Rr.obj W) (Rr.map (adj1.counit.app W)) =
      Rr.map (adj2.unit.app W) := by
    rw [comp_homEquiv]
    simp [homEquiv_unit]
  rw [← h3]
  exact (homEquiv_ofNatIsoLeft_apply adjT pf.symm (Rr.map (adj1.counit.app W))).symm.trans
    (homEquiv_comp_rightAdjointUniq (adj1.comp adj2) (adjT.ofNatIsoLeft pf.symm)
      (Rr.obj W) (Rr.obj W) (Rr.map (adj1.counit.app W)))

end CategoryTheory.Adjunction

namespace StacksDraft.DerivedHom.DerivedHomAdjunction

variable {S : Type uS} [CommRing S] [HasDerivedCategory.{w} (ModuleCat.{v} S)]
  (d : DerivedHomAdjunction S)

/-- The Hom equivalence of the adjunction `- ⊗ᴸ L ⊣ RHom(L, -)` of [stacks 0A63] is the inverse
of the Hom equivalence carried by the tensor--Hom structure.  The adjunction is assembled by
`CategoryTheory.Adjunction.mkOfHomEquiv`, which preserves the equivalence it is given. -/
theorem homEquiv_tensorHomAdjunctionAt (L X Y : DerivedCategory (ModuleCat.{v} S)) :
    (d.tensorHomAdjunctionAt L).homEquiv X Y = (d.homEquiv X L Y).symm.toEquiv := by
  have h : (d.tensorHomAdjunctionAt L).homEquiv =
      fun (K M : DerivedCategory (ModuleCat.{v} S)) => (d.homEquiv K L M).symm.toEquiv := by
    simp only [DerivedHomAdjunction.tensorHomAdjunctionAt, Adjunction.mkOfHomEquiv_homEquiv]
    rfl
  rw [h]

end StacksDraft.DerivedHom.DerivedHomAdjunction

namespace Dualizing

attribute [local instance] extendScalarsAdditiveOfRingHom

section Transpose

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
  (F : DerivedCategory (ModuleCat.{max v uR uA} R) ⥤
    DerivedCategory (ModuleCat.{max v uR uA} A))
  (comparison : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} R) (ComplexShape.up ℤ))]

/-- **The transpose of the algebra action is the unit of [stacks 0A70] through the bridge of
[stacks 0E2A].** For `f : R → A` and a model `F` of derived extension of scalars along `f`, the
`A`-action

`(W|_R) ⊗ᴸ_R A ⟶ (F (W|_R))|_R ⟶ W|_R`

on the restriction of an object `W` of `D(A)` — the inverse projection formula
`Dualizing.derivedExtendRestrictScalarsTensorIso` followed by the counit of derived extension of
scalars — transposes, under the tensor--Hom adjunction of [stacks 0A63] over `R`, to the
restriction of the unit of the derived restriction/Hom adjunction of [stacks 0A70] followed by
`Dualizing.derivedHomRestrictScalarsInternalHomIsoOfModel`.

Neither the projection formula nor the counit occurs on the right-hand side; this is what removes
them from the projection-formula compatibility. -/
theorem homEquiv_symm_algebraAction (W : DerivedCategory (ModuleCat.{max v uR uA} A)) :
    ((derivedHomAdjunctionOverRing.{uR, max v uR uA, max v uR uA + 1} R).homEquiv
          ((ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory.obj W)
          (derivedAlgebraSingle.{uR, uA, v} f)
          ((ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory.obj W)).symm
        ((derivedExtendRestrictScalarsTensorIso.{uR, uA, v} f F comparison).inv.app
            ((ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory.obj W) ≫
          (ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory.map
            ((derivedExtensionScalarsAdjunction.{uR, uA, v} f F comparison).counit.app W)) =
      (ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory.map
          ((derivedHomAdjunction.{uR, uA, v} f).unit.app W) ≫
        (derivedHomRestrictScalarsInternalHomIsoOfModel.{uR, uA, v} f F comparison).hom.app
          ((ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory.obj W) := by
  have h := Adjunction.homEquiv_isoLeft_comp_counit
    (derivedExtensionScalarsAdjunction.{uR, uA, v} f F comparison)
    (derivedHomAdjunction.{uR, uA, v} f)
    ((derivedHomAdjunctionOverRing.{uR, max v uR uA, max v uR uA + 1} R).tensorHomAdjunctionAt
      (derivedAlgebraSingle.{uR, uA, v} f))
    (derivedExtendRestrictScalarsTensorIso.{uR, uA, v} f F comparison) W
  rwa [DerivedHomAdjunction.homEquiv_tensorHomAdjunctionAt] at h

/-- `Dualizing.homEquiv_symm_algebraAction` solved for the action itself. -/
theorem algebraAction_eq_homEquiv (W : DerivedCategory (ModuleCat.{max v uR uA} A)) :
    (derivedExtendRestrictScalarsTensorIso.{uR, uA, v} f F comparison).inv.app
          ((ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory.obj W) ≫
        (ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory.map
          ((derivedExtensionScalarsAdjunction.{uR, uA, v} f F comparison).counit.app W) =
      (derivedHomAdjunctionOverRing.{uR, max v uR uA, max v uR uA + 1} R).homEquiv
        ((ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory.obj W)
        (derivedAlgebraSingle.{uR, uA, v} f)
        ((ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory.obj W)
        ((ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory.map
            ((derivedHomAdjunction.{uR, uA, v} f).unit.app W) ≫
          (derivedHomRestrictScalarsInternalHomIsoOfModel.{uR, uA, v} f F comparison).hom.app
            ((ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory.obj W)) :=
  (AddEquiv.symm_apply_eq _).mp (homEquiv_symm_algebraAction f F comparison W)

end Transpose

section Square

variable {R : Type uR} {A : Type uA} {R' : Type uRp} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']
  (hTor : RingTheory.TorIndependence.TorIndependent R A R')
  (baseChangeR :
    DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} R'))
  (comparisonR :
    DerivedCategory.Q ⋙ baseChangeR ⟶
      (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (isLeftDerivedR : baseChangeR.IsLeftDerivedFunctor comparisonR
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ)))
  (baseChangeA :
    DerivedCategory (ModuleCat.{max v uR uA uRp} A) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (comparisonA :
    DerivedCategory.Q ⋙ baseChangeA ⟶
      (ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
        (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (isLeftDerivedA : baseChangeA.IsLeftDerivedFunctor comparisonA
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} A) (ComplexShape.up ℤ)))

variable
  (Ff : DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp} A))
  (alphaf : DerivedCategory.Q ⋙ Ff ⟶
    (ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
      (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [Ff.IsLeftDerivedFunctor alphaf
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]

variable
  (Fi : DerivedCategory (ModuleCat.{max v uR uA uRp} R') ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (alphai : DerivedCategory.Q ⋙ Fi ⟶
    (ModuleCat.extendScalars.{uRp, max uA uRp, max v uR uA uRp}
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [Fi.IsLeftDerivedFunctor alphai
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R') (ComplexShape.up ℤ))]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **The component of `Dualizing.algebraActionLeft`.** The transformation is a composite of
whiskerings, so its component at an object `W` of `D(A)` is the composite of their components:
the base change `Dualizing.derivedBaseChangeAlgebraIso` of the algebra in the tensor factor, the
inverse projection formula along `R' → A ⊗_R R'`, the counit of derived extension of scalars along
`R' → A ⊗_R R'`, and the comparison of [stacks 0661]. -/
theorem algebraActionLeft_app (W : DerivedCategory (ModuleCat.{max v uR uA uRp} A)) :
    (algebraActionLeft hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
        comparisonA isLeftDerivedA Fi alphai).app W =
      (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
          ((𝟙 ((ModuleCat.restrictScalars
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
                (baseChangeA.obj W)),
              (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR isLeftDerivedR
                baseChangeA comparisonA isLeftDerivedA).hom) :
            ((ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
                (baseChangeA.obj W),
              baseChangeR.obj
                (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) ⟶
              ((ModuleCat.restrictScalars
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
                  (baseChangeA.obj W),
                derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom)) ≫
        (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).inv.app
            ((ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
              (baseChangeA.obj W)) ≫
          (ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map
              ((derivedExtensionScalarsAdjunction.{uRp, max uA uRp, max v uR}
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).counit.app
                (baseChangeA.obj W)) ≫
            (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR isLeftDerivedR
              baseChangeA comparisonA isLeftDerivedA).hom.app W :=
  rfl

/-- **The component of `Dualizing.algebraActionRight`.** The comparison of [stacks 0661] in the
first tensor factor, the lax monoidal structure map `Dualizing.derivedTensorBaseChange` of derived
base change along `R → R'`, and the derived base change of the `A`-action on `W|_R`. -/
theorem algebraActionRight_app (W : DerivedCategory (ModuleCat.{max v uR uA uRp} A)) :
    (algebraActionRight hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
        comparisonA isLeftDerivedA Ff alphaf).app W =
      (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
          (((restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR isLeftDerivedR
                baseChangeA comparisonA isLeftDerivedA).hom.app W,
              𝟙 (baseChangeR.obj
                (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))) :
            ((ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
                (baseChangeA.obj W),
              baseChangeR.obj
                (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) ⟶
              (baseChangeR.obj
                  ((ModuleCat.restrictScalars.{max v uR uA uRp}
                      (algebraMap R A)).mapDerivedCategory.obj W),
                baseChangeR.obj
                  (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))) ≫
        derivedTensorBaseChange.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR
            ((ModuleCat.restrictScalars.{max v uR uA uRp}
                (algebraMap R A)).mapDerivedCategory.obj W)
            (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) ≫
          baseChangeR.map
            ((derivedExtendRestrictScalarsTensorIso.{uR, uA, max v uRp} (algebraMap R A) Ff
                  alphaf).inv.app
                ((ModuleCat.restrictScalars.{max v uR uA uRp}
                    (algebraMap R A)).mapDerivedCategory.obj W) ≫
              (ModuleCat.restrictScalars.{max v uR uA uRp}
                  (algebraMap R A)).mapDerivedCategory.map
                ((derivedExtensionScalarsAdjunction.{uR, uA, max v uRp} (algebraMap R A) Ff
                  alphaf).counit.app W)) :=
  rfl

/-- **The component of `Dualizing.algebraActionLeft` as a transpose.** Under the tensor--Hom
adjunction of [stacks 0A63] over `R'` it is the transpose of: the restricted unit of [stacks 0A70]
along `R' → A ⊗_R R'`, the bridge of [stacks 0E2A] there, the comparison of [stacks 0661] in the
target variable, and the base change of the algebra in the internal-Hom variable.  Neither the
projection formula nor the counit of derived extension of scalars survives. -/
theorem algebraActionLeft_app_eq_homEquiv
    (W : DerivedCategory (ModuleCat.{max v uR uA uRp} A)) :
    (algebraActionLeft hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
        comparisonA isLeftDerivedA Fi alphai).app W =
      (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').homEquiv
        ((ModuleCat.restrictScalars
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
            (baseChangeA.obj W))
        (baseChangeR.obj (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))
        (baseChangeR.obj
          ((ModuleCat.restrictScalars.{max v uR uA uRp}
            (algebraMap R A)).mapDerivedCategory.obj W))
        ((((ModuleCat.restrictScalars
                      (Algebra.TensorProduct.includeRight :
                        R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map
                    ((derivedHomAdjunction.{uRp, max uA uRp, max v uR}
                      (Algebra.TensorProduct.includeRight :
                        R' →ₐ[R] TensorProduct R A R').toRingHom).unit.app
                      (baseChangeA.obj W)) ≫
                  (derivedHomRestrictScalarsInternalHomIsoOfModel.{uRp, max uA uRp, max v uR}
                      (Algebra.TensorProduct.includeRight :
                        R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).hom.app
                    ((ModuleCat.restrictScalars
                        (Algebra.TensorProduct.includeRight :
                          R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
                      (baseChangeA.obj W))) ≫
                (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
                    max v uR uA uRp + 1} R').hom.map
                  ((𝟙 (Opposite.op (derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
                          (Algebra.TensorProduct.includeRight :
                            R' →ₐ[R] TensorProduct R A R').toRingHom)),
                      (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR
                        isLeftDerivedR baseChangeA comparisonA isLeftDerivedA).hom.app W) :
                    (Opposite.op (derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
                        (Algebra.TensorProduct.includeRight :
                          R' →ₐ[R] TensorProduct R A R').toRingHom),
                      ((ModuleCat.restrictScalars
                          (Algebra.TensorProduct.includeRight :
                            R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
                        (baseChangeA.obj W))) ⟶
                      (Opposite.op (derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
                          (Algebra.TensorProduct.includeRight :
                            R' →ₐ[R] TensorProduct R A R').toRingHom),
                        (baseChangeR.obj
                          ((ModuleCat.restrictScalars.{max v uR uA uRp}
                            (algebraMap R A)).mapDerivedCategory.obj W))))) ≫
              (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
                  max v uR uA uRp + 1} R').hom.map
                (((derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR isLeftDerivedR
                        baseChangeA comparisonA isLeftDerivedA).hom.op,
                    𝟙 (baseChangeR.obj
                      ((ModuleCat.restrictScalars.{max v uR uA uRp}
                        (algebraMap R A)).mapDerivedCategory.obj W))) :
                  (Opposite.op (derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
                      (Algebra.TensorProduct.includeRight :
                        R' →ₐ[R] TensorProduct R A R').toRingHom),
                    (baseChangeR.obj
                      ((ModuleCat.restrictScalars.{max v uR uA uRp}
                        (algebraMap R A)).mapDerivedCategory.obj W))) ⟶
                    (Opposite.op (baseChangeR.obj
                        (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))),
                      (baseChangeR.obj
                        ((ModuleCat.restrictScalars.{max v uR uA uRp}
                          (algebraMap R A)).mapDerivedCategory.obj W))))) := by
  refine (algebraActionLeft_app hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
    comparisonA isLeftDerivedA Fi alphai W).trans ?_
  refine Eq.trans ?_ ((derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
      max v uR uA uRp + 1} R').homEquiv_dinaturality
    (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA).hom _).symm
  refine congrArg (fun z => _ ≫ z) ?_
  refine Eq.trans ?_ ((derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
      max v uR uA uRp + 1} R').homEquiv_naturality_right
    ((restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA).hom.app W) _).symm
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ _)
    (algebraAction_eq_homEquiv.{uRp, max uA uRp, max v uR}
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai (baseChangeA.obj W)))

/-- **The component of `Dualizing.algebraActionRight` as a transpose.** Under the same adjunction
it is the transpose of: the comparison of [stacks 0661], the derived base change of the restricted
unit of [stacks 0A70] along `R → A` followed by the bridge of [stacks 0E2A] there, and the
derived-Hom base-change morphism of [stacks 0E1X].  Neither the projection formula, nor the counit
of derived extension of scalars, nor the lax monoidal structure map survives. -/
theorem algebraActionRight_app_eq_homEquiv
    (W : DerivedCategory (ModuleCat.{max v uR uA uRp} A)) :
    (algebraActionRight hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
        comparisonA isLeftDerivedA Ff alphaf).app W =
      (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').homEquiv
        ((ModuleCat.restrictScalars
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
            (baseChangeA.obj W))
        (baseChangeR.obj (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))
        (baseChangeR.obj
          ((ModuleCat.restrictScalars.{max v uR uA uRp}
            (algebraMap R A)).mapDerivedCategory.obj W))
        ((restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR isLeftDerivedR
              baseChangeA comparisonA isLeftDerivedA).hom.app W ≫
          baseChangeR.map
              ((ModuleCat.restrictScalars.{max v uR uA uRp}
                    (algebraMap R A)).mapDerivedCategory.map
                  ((derivedHomAdjunction.{uR, uA, max v uRp} (algebraMap R A)).unit.app W) ≫
                (derivedHomRestrictScalarsInternalHomIsoOfModel.{uR, uA, max v uRp}
                    (algebraMap R A) Ff alphaf).hom.app
                  ((ModuleCat.restrictScalars.{max v uR uA uRp}
                    (algebraMap R A)).mapDerivedCategory.obj W)) ≫
            Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR, uRp, max v uA}
              (algebraMap R R') baseChangeR comparisonR
              (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))
              ((ModuleCat.restrictScalars.{max v uR uA uRp}
                (algebraMap R A)).mapDerivedCategory.obj W)) := by
  refine (algebraActionRight_app hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
    comparisonA isLeftDerivedA Ff alphaf W).trans ?_
  refine Eq.trans ?_ ((derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
      max v uR uA uRp + 1} R').homEquiv_naturality_left
    ((restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA).hom.app W) _).symm
  refine congrArg (fun z => _ ≫ z) ?_
  refine Eq.trans (derivedTensorBaseChange_comp_map.{uR, uRp, max v uA} (algebraMap R R')
    baseChangeR comparisonR
    ((ModuleCat.restrictScalars.{max v uR uA uRp} (algebraMap R A)).mapDerivedCategory.obj W)
    (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))
    ((ModuleCat.restrictScalars.{max v uR uA uRp} (algebraMap R A)).mapDerivedCategory.obj W)
    _) ?_
  rw [homEquiv_symm_algebraAction.{uR, uA, max v uRp} (algebraMap R A) Ff alphaf W]
  rfl

/-- **The projection-formula compatibility of [stacks 0E2A], transposed.** The equation between
the two transposes of `Dualizing.algebraActionLeft` and `Dualizing.algebraActionRight` at an
object `W` of `D(A)`, as morphisms

`baseChangeA(W)|_{R'} ⟶ RHom_{R'}(A ⊗ᴸ_R R', (W|_R) ⊗ᴸ_R R')`.

Its factors are the units of the derived restriction/Hom adjunction of [stacks 0A70] along
`R' → A ⊗_R R'` and along `R → A`, the two bridges
`Dualizing.derivedHomRestrictScalarsInternalHomIsoOfModel` of [stacks 0E2A], the comparison
`Dualizing.restrictionBaseChangeIsoGeneral` of [stacks 0661], the base change
`Dualizing.derivedBaseChangeAlgebraIso` of the algebra, and the derived-Hom base-change morphism
of [stacks 0E1X].  Neither projection formula, neither counit of derived extension of scalars and
no lax monoidal structure map occurs.

This is *equivalent* to the equality of the two actions at `W`, by
`Dualizing.algebraAction_app_eq_iff_unitBridgeCompatibility`, so taking it as the obligation
weakens nothing.  It is not proved. -/
def UnitBridgeCompatibility (W : DerivedCategory (ModuleCat.{max v uR uA uRp} A)) : Prop :=
    ((((ModuleCat.restrictScalars
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map
                ((derivedHomAdjunction.{uRp, max uA uRp, max v uR}
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom).unit.app
                  (baseChangeA.obj W)) ≫
              (derivedHomRestrictScalarsInternalHomIsoOfModel.{uRp, max uA uRp, max v uR}
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).hom.app
                ((ModuleCat.restrictScalars
                    (Algebra.TensorProduct.includeRight :
                      R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
                  (baseChangeA.obj W))) ≫
            (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
                max v uR uA uRp + 1} R').hom.map
              ((𝟙 (Opposite.op (derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
                      (Algebra.TensorProduct.includeRight :
                        R' →ₐ[R] TensorProduct R A R').toRingHom)),
                  (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR
                    isLeftDerivedR baseChangeA comparisonA isLeftDerivedA).hom.app W) :
                (Opposite.op (derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
                    (Algebra.TensorProduct.includeRight :
                      R' →ₐ[R] TensorProduct R A R').toRingHom),
                  ((ModuleCat.restrictScalars
                      (Algebra.TensorProduct.includeRight :
                        R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
                    (baseChangeA.obj W))) ⟶
                  (Opposite.op (derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
                      (Algebra.TensorProduct.includeRight :
                        R' →ₐ[R] TensorProduct R A R').toRingHom),
                    (baseChangeR.obj
                      ((ModuleCat.restrictScalars.{max v uR uA uRp}
                        (algebraMap R A)).mapDerivedCategory.obj W))))) ≫
          (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
              max v uR uA uRp + 1} R').hom.map
            (((derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR isLeftDerivedR
                    baseChangeA comparisonA isLeftDerivedA).hom.op,
                𝟙 (baseChangeR.obj
                  ((ModuleCat.restrictScalars.{max v uR uA uRp}
                    (algebraMap R A)).mapDerivedCategory.obj W))) :
              (Opposite.op (derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom),
                (baseChangeR.obj
                  ((ModuleCat.restrictScalars.{max v uR uA uRp}
                    (algebraMap R A)).mapDerivedCategory.obj W))) ⟶
                (Opposite.op (baseChangeR.obj
                    (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))),
                  (baseChangeR.obj
                    ((ModuleCat.restrictScalars.{max v uR uA uRp}
                      (algebraMap R A)).mapDerivedCategory.obj W))))) =
      ((restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR isLeftDerivedR
            baseChangeA comparisonA isLeftDerivedA).hom.app W ≫
        baseChangeR.map
            ((ModuleCat.restrictScalars.{max v uR uA uRp}
                  (algebraMap R A)).mapDerivedCategory.map
                ((derivedHomAdjunction.{uR, uA, max v uRp} (algebraMap R A)).unit.app W) ≫
              (derivedHomRestrictScalarsInternalHomIsoOfModel.{uR, uA, max v uRp}
                  (algebraMap R A) Ff alphaf).hom.app
                ((ModuleCat.restrictScalars.{max v uR uA uRp}
                  (algebraMap R A)).mapDerivedCategory.obj W)) ≫
          Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR, uRp, max v uA}
            (algebraMap R R') baseChangeR comparisonR
            (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))
            ((ModuleCat.restrictScalars.{max v uR uA uRp}
              (algebraMap R A)).mapDerivedCategory.obj W))

/-- **The reduction.** The two algebra actions agree at an object `W` of `D(A)` if and only if
`Dualizing.UnitBridgeCompatibility` holds at `W`.  The Hom equivalence of [stacks 0A63] is a
bijection, so this is an equivalence and not merely a sufficient condition; in particular the
hypothesis of `Dualizing.algebraAction_eq_of_kFlat` may be replaced by
`Dualizing.UnitBridgeCompatibility` at the classes of K-flat complexes with nothing lost. -/
theorem algebraAction_app_eq_iff_unitBridgeCompatibility
    (W : DerivedCategory (ModuleCat.{max v uR uA uRp} A)) :
    (algebraActionLeft hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
          comparisonA isLeftDerivedA Fi alphai).app W =
        (algebraActionRight hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
          comparisonA isLeftDerivedA Ff alphaf).app W ↔
      UnitBridgeCompatibility hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
        comparisonA isLeftDerivedA Ff alphaf Fi alphai W := by
  rw [algebraActionLeft_app_eq_homEquiv, algebraActionRight_app_eq_homEquiv]
  exact ((derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
    max v uR uA uRp + 1} R').homEquiv _ _ _).injective.eq_iff

section Canonical

/-- **The reduction at the canonical models.**
`Dualizing.algebraAction_app_eq_iff_unitBridgeCompatibility` read at the models of derived
extension of scalars along `R → A` and `R' → A ⊗_R R'` chosen by
`Dualizing.canonicalExtensionModel` and `Dualizing.canonicalExtensionModelIncludeRight`, which are
the ones `Dualizing.algebraActionLeftCanonical` and `Dualizing.algebraActionRightCanonical` use and
hence the ones `Dualizing.KFlatAlgebraActionEq` quantifies over. -/
theorem algebraActionCanonical_app_eq_iff_unitBridgeCompatibility
    (W : DerivedCategory (ModuleCat.{max v uR uA uRp} A)) :
    (algebraActionLeftCanonical hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
          comparisonA isLeftDerivedA).app W =
        (algebraActionRightCanonical hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
          comparisonA isLeftDerivedA).app W ↔
      @UnitBridgeCompatibility R A R' _ _ _ _ _ hTor baseChangeR comparisonR isLeftDerivedR
        baseChangeA comparisonA isLeftDerivedA
        (canonicalExtensionModel.{uR, uA, max v uRp} R A).functor
        (canonicalExtensionModel.{uR, uA, max v uRp} R A).comparison
        (canonicalExtensionModel.{uR, uA, max v uRp} R A).isLeftDerived
        (canonicalExtensionModelIncludeRight.{uR, uA, uRp, max v uR} R A R').functor
        (canonicalExtensionModelIncludeRight.{uR, uA, uRp, max v uR} R A R').comparison
        (canonicalExtensionModelIncludeRight.{uR, uA, uRp, max v uR} R A R').isLeftDerived W :=
  @algebraAction_app_eq_iff_unitBridgeCompatibility R A R' _ _ _ _ _ hTor baseChangeR comparisonR
    isLeftDerivedR baseChangeA comparisonA isLeftDerivedA
    (canonicalExtensionModel.{uR, uA, max v uRp} R A).functor
    (canonicalExtensionModel.{uR, uA, max v uRp} R A).comparison
    (canonicalExtensionModel.{uR, uA, max v uRp} R A).isLeftDerived
    (canonicalExtensionModelIncludeRight.{uR, uA, uRp, max v uR} R A R').functor
    (canonicalExtensionModelIncludeRight.{uR, uA, uRp, max v uR} R A R').comparison
    (canonicalExtensionModelIncludeRight.{uR, uA, uRp, max v uR} R A R').isLeftDerived W

end Canonical

end Square

end Dualizing

end
