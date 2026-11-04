module

public import StacksFrontier.Homology.HomComplex.DerivedAdjunctionTensorPrefix
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeScalarLift

/-!
# The keystone with no tensor bifunctor left on either side

`Dualizing.tensorBaseChangeMor_eq_iff_scalarLift` states the [stacks 068I] identification as an
equation of `D(ULift R)` whose left-hand side is the fixed-universe tensor bifunctor applied to a
pair `(u, 𝟙)` followed by the presentation `b` of the [stacks 0A63] transpose `ψ` of the inverse
component of [stacks 0E1W].  The value of `ψ`,
`Stacks.DerivedHom.BaseChange.homEquiv_derivedHomRestrictScalarsNatIso_inv_app_scalarEquivalence`,
*begins with a morphism of that same bifunctor at a pair `(v, 𝟙)` with the same identity in the
second variable*, and what follows it is one `StacksDraft.DerivedHom.DerivedInternalHom.Model`
transpose.

So the two prefixes merge by functoriality, and the merged one is absorbed into that transpose by
naturality of the transpose in its source variable
(`StacksDraft.DerivedHom.DerivedHomAdjunction.tensor_map_id_comp_homEquiv_eq_iff`).  The equation
that comes out has **no tensor bifunctor in either side**: its left-hand side is the plain
composite `u ≫ v ≫ a` of morphisms of `D(ULift R)` landing in an internal Hom, and its right-hand
side is the fixed-universe transpose of what was the right-hand side before, the inverse counit of
the scalar equivalence followed by `E.functor` of the unit of [stacks 0GMT].

Naturality in the source is available at arbitrary objects, which is why this step goes through
where the evaluation lemmas do not: the obstruction recorded in
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeTensorTranspose` is that
`StacksDraft.DerivedHom.DerivedInternalHom.Model.homEquiv_map_uncurry` and `…homEquiv_composition`
unwind a transpose only at a localized complex in each of the three variables, and of the three
objects occurring here only `E.functor.obj Y` is presented as one.  Absorbing a prefix needs no
presentation of any of them, so that obstruction does not apply to this step.

**What is not done here.**  The identification is not proved,
`Dualizing.TensorComparisonCompatibility` stays open, `Dualizing.KFlatAlgebraActionEq` with it,
and no tag loses its conditional caveat.  In particular the companion hypothesis `h` of
`Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` is untouched -- it is independent
of this one and its frontier remains `Dualizing.tensorComparisonCompatibility_of_kFlat_tail`.
What changes is that the one remaining equation is now a composite in the internal-Hom variable
rather than a comparison of two morphisms out of a tensor product.

## Main results

* `Dualizing.eq_derivedTensorBaseChange_iff_scalarLiftTranspose` -- a morphism is the lax monoidal
  structure map of derived base change exactly when a composite of three morphisms of `D(ULift R)`
  equals the fixed-universe transpose of the unit side.
* `Dualizing.tensorBaseChangeMor_eq_iff_scalarLiftTranspose` -- **the keystone in that shape**: the
  same at the [stacks 068I] candidate.
* `Dualizing.exists_scalarLiftSplitPresentation` -- the split presentation the two above ask for
  always exists, the value of `ψ` having exactly that shape, so the reduction is
  unconditional.

## Implementation notes

The split presentation is passed as data rather than substituted, for the reason recorded in
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeScalarLift`: `ψ`'s value is
large and a consumer may hold it in more than one shape, the all-objects one or the one at the
keystone's K-flat pair with the content factor at the chain level, and passing it in keeps the
reduction independent of which.  The two shapes agree on the prefix `v` and the identity beside
it, and differ only in the transpose's argument `a`, which is what makes one hypothesis list serve
both.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor StacksDraft.DerivedHom
open CochainComplex.DerivedExtensionScalars

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
  [hF : F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]

include hF in
/-- **A morphism is the lax monoidal structure map of derived base change exactly when a composite
of three morphisms of the scalar-lift world equals the transpose of the unit side.**

`Dualizing.eq_derivedTensorBaseChange_iff_scalarLift` with the presentation `b` of the
[stacks 0A63] transpose `ψ` of the inverse component of [stacks 0E1W] taken apart into the shape
its value has: a morphism `(v, 𝟙)` of the fixed-universe tensor bifunctor followed by the
fixed-universe transpose of some `a`.  The left-hand side of the equation then carries two
morphisms of that bifunctor with the same identity in the second variable, which merge by
functoriality, and the merged prefix is absorbed into the transpose by naturality in its source
variable.

What results is an equation with no tensor bifunctor on either side: the composite
`E.functor.map (η_X ≫ (transpose of the candidate)|_R) ≫ v ≫ a` of morphisms of `D(ULift R)`,
against the fixed-universe transpose of the inverse counit of the scalar equivalence followed by
`E.functor` of the unit of [stacks 0GMT].  The transpose being a bijection, this says exactly what
the equation of `Dualizing.eq_derivedTensorBaseChange_iff_scalarLift` says. -/
theorem eq_derivedTensorBaseChange_iff_scalarLiftTranspose
    (X Y : DerivedCategory (ModuleCat.{max uR uA uM} R)) :
    let E := _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
      max uR uA uM} R
    let U := (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory
    let dR := derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R
    let dA := derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A
    let W := dR.tensor.obj (X, Y)
    let HR := DerivedInternalHom.Model.hom (ULift.{max uR uA uM} R)
    ∀ (g : dA.tensor.obj (F.obj X, F.obj Y) ⟶ F.obj W)
      (P : DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)))
      (v : E.functor.obj (U.obj (dA.hom.obj (Opposite.op (F.obj Y), F.obj W))) ⟶ P)
      (a : P ⟶ HR.obj (Opposite.op (E.functor.obj Y), E.functor.obj (U.obj (F.obj W))))
      (_hb : dR.homEquiv (U.obj (dA.hom.obj (Opposite.op (F.obj Y), F.obj W))) Y
            (U.obj (F.obj W))
            ((_root_.Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA,
              uM} f F comparison).inv.app (Opposite.op Y, F.obj W)) =
          E.inverse.map
              ((DerivedInternalHom.Model.tensor (ULift.{max uR uA uM} R)).map
                  ((v, 𝟙 (E.functor.obj Y)) :
                    ((E.functor.obj (U.obj (dA.hom.obj (Opposite.op (F.obj Y), F.obj W))),
                        E.functor.obj Y) :
                      DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ×
                        DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R))) ⟶
                      (P, E.functor.obj Y)) ≫
                DerivedInternalHom.Model.homEquiv P (E.functor.obj Y)
                  (E.functor.obj (U.obj (F.obj W))) a) ≫
            E.unitIso.inv.app (U.obj (F.obj W))),
    g = derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y ↔
      E.functor.map ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app X ≫
              U.map ((dA.homEquiv (F.obj X) (F.obj Y) (F.obj W)).symm g)) ≫
            v ≫ a =
        (DerivedInternalHom.Model.homEquiv (E.functor.obj X) (E.functor.obj Y)
            (E.functor.obj (U.obj (F.obj W)))).symm
          (E.counitIso.inv.app ((DerivedInternalHom.Model.tensor
                (ULift.{max uR uA uM} R)).obj (E.functor.obj X, E.functor.obj Y)) ≫
            E.functor.map ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F
              comparison).unit.app W)) := by
  intro E U dR dA W HR g P v a hb
  refine (eq_derivedTensorBaseChange_iff_scalarLift.{uR, uA, uM} f F comparison X Y g _ hb).trans
    ?_
  exact (DerivedInternalHom.Model.adjunction
    (ULift.{max uR uA uM} R)).toDerivedHomAdjunction.tensor_map_id_comp_homEquiv_eq_iff _ v a _

include hF in
/-- **The keystone with no tensor bifunctor left on either side.**

`Dualizing.eq_derivedTensorBaseChange_iff_scalarLiftTranspose` at the [stacks 068I] candidate
`Dualizing.tensorBaseChangeMor`, so this is the same statement as
`Dualizing.tensorBaseChangeMor_eq_iff`,
`Dualizing.tensorBaseChangeMor_eq_iff_tensorTranspose` and
`Dualizing.tensorBaseChangeMor_eq_iff_scalarLift`; what it adds is that the remaining equation is
a composite of three morphisms of `D(ULift R)` landing in an internal Hom, against the
fixed-universe transpose of the unit side.

Both sides are now where their chain-level values live.  The [stacks 068I] side carries exactly
one chain map, `CochainComplex.ExtendScalars.extendScalarsMonoidalIso`, and the [stacks 0E1W] side
exactly one, `Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap` -- the latter inside `a`,
by
`Stacks.DerivedHom.BaseChange.homEquiv_derivedHomRestrictScalarsNatIso_inv_app_tensorKFlat`. -/
theorem tensorBaseChangeMor_eq_iff_scalarLiftTranspose
    (D : TotalDerivedExtensionScalars.{uR, max uR uA uM, uA, max uR uA uM + 1,
      max uR uA uM + 1} f)
    (X Y : DerivedCategory (ModuleCat.{max uR uA uM} R)) :
    let E := _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
      max uR uA uM} R
    let U := (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory
    let dR := derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R
    let dA := derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A
    let W := dR.tensor.obj (X, Y)
    let HR := DerivedInternalHom.Model.hom (ULift.{max uR uA uM} R)
    ∀ (P : DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)))
      (v : E.functor.obj (U.obj (dA.hom.obj (Opposite.op (F.obj Y), F.obj W))) ⟶ P)
      (a : P ⟶ HR.obj (Opposite.op (E.functor.obj Y), E.functor.obj (U.obj (F.obj W))))
      (_hb : dR.homEquiv (U.obj (dA.hom.obj (Opposite.op (F.obj Y), F.obj W))) Y
            (U.obj (F.obj W))
            ((_root_.Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA,
              uM} f F comparison).inv.app (Opposite.op Y, F.obj W)) =
          E.inverse.map
              ((DerivedInternalHom.Model.tensor (ULift.{max uR uA uM} R)).map
                  ((v, 𝟙 (E.functor.obj Y)) :
                    ((E.functor.obj (U.obj (dA.hom.obj (Opposite.op (F.obj Y), F.obj W))),
                        E.functor.obj Y) :
                      DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ×
                        DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R))) ⟶
                      (P, E.functor.obj Y)) ≫
                DerivedInternalHom.Model.homEquiv P (E.functor.obj Y)
                  (E.functor.obj (U.obj (F.obj W))) a) ≫
            E.unitIso.inv.app (U.obj (F.obj W))),
    tensorBaseChangeMor.{uR, uA, uM} f F comparison D X Y =
          derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y ↔
      E.functor.map ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app X ≫
              U.map ((dA.homEquiv (F.obj X) (F.obj Y) (F.obj W)).symm
                (tensorBaseChangeMor.{uR, uA, uM} f F comparison D X Y))) ≫
            v ≫ a =
        (DerivedInternalHom.Model.homEquiv (E.functor.obj X) (E.functor.obj Y)
            (E.functor.obj (U.obj (F.obj W)))).symm
          (E.counitIso.inv.app ((DerivedInternalHom.Model.tensor
                (ULift.{max uR uA uM} R)).obj (E.functor.obj X, E.functor.obj Y)) ≫
            E.functor.map ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F
              comparison).unit.app W)) := by
  intro E U dR dA W HR P v a hb
  exact eq_derivedTensorBaseChange_iff_scalarLiftTranspose.{uR, uA, uM} f F comparison X Y
    (tensorBaseChangeMor.{uR, uA, uM} f F comparison D X Y) P v a hb

include hF in
/-- **The split presentation of `ψ` that the reduction asks for always exists.**

`Dualizing.exists_scalarLiftPresentation` produces the presentation
`Dualizing.eq_derivedTensorBaseChange_iff_scalarLift` asks for; this refines it to the shape
`Dualizing.eq_derivedTensorBaseChange_iff_scalarLiftTranspose` asks for, namely with the morphism
of `D(ULift R)` itself split as a morphism of the fixed-universe tensor bifunctor at a pair whose
second component is the identity, followed by one fixed-universe transpose.

The value
`Stacks.DerivedHom.BaseChange.homEquiv_derivedHomRestrictScalarsNatIso_inv_app_scalarEquivalence`
is already in that shape, with `v` the scalar equivalence of the scalar-restriction comparison
followed by a counit and `a` the three-factor composite carrying the comparison `eF` of the two
derived extensions of scalars, the inverse component of the descended comparison of [stacks 0E1W]
and the transported restriction comparison `τ`.  So the reduction is unconditional. -/
theorem exists_scalarLiftSplitPresentation
    (X Y : DerivedCategory (ModuleCat.{max uR uA uM} R)) :
    let E := _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
      max uR uA uM} R
    let U := (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory
    let dR := derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R
    let dA := derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A
    let W := dR.tensor.obj (X, Y)
    let HR := DerivedInternalHom.Model.hom (ULift.{max uR uA uM} R)
    ∃ (P : DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)))
      (v : E.functor.obj (U.obj (dA.hom.obj (Opposite.op (F.obj Y), F.obj W))) ⟶ P)
      (a : P ⟶ HR.obj (Opposite.op (E.functor.obj Y), E.functor.obj (U.obj (F.obj W)))),
      dR.homEquiv (U.obj (dA.hom.obj (Opposite.op (F.obj Y), F.obj W))) Y (U.obj (F.obj W))
          ((_root_.Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA,
            uM} f F comparison).inv.app (Opposite.op Y, F.obj W)) =
        E.inverse.map
            ((DerivedInternalHom.Model.tensor (ULift.{max uR uA uM} R)).map
                ((v, 𝟙 (E.functor.obj Y)) :
                  ((E.functor.obj (U.obj (dA.hom.obj (Opposite.op (F.obj Y), F.obj W))),
                      E.functor.obj Y) :
                    DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ×
                      DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R))) ⟶
                    (P, E.functor.obj Y)) ≫
              DerivedInternalHom.Model.homEquiv P (E.functor.obj Y)
                (E.functor.obj (U.obj (F.obj W))) a) ≫
          E.unitIso.inv.app (U.obj (F.obj W)) := by
  intro E U dR dA W HR
  open _root_.Stacks.DerivedHom.BaseChange in
  exact ⟨_, _, _, homEquiv_derivedHomRestrictScalarsNatIso_inv_app_scalarEquivalence.{uR, uA,
    uM} f F comparison (Opposite.op Y) (F.obj W)⟩

end Dualizing

end
