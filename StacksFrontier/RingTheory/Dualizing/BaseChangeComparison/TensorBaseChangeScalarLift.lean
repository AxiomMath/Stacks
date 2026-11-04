module

public import StacksFrontier.CategoryTheory.Equivalence.InverseMapTranspose
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.HomRestrictScalarsTranspose
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeTensorTranspose

/-!
# The keystone as an equation of the scalar-lift world

`Dualizing.tensorBaseChangeMor_eq_iff_tensorTranspose` states the [stacks 068I] identification as
an equation of `D(R)` in three factors: the tensor bifunctor of [stacks 0A63] applied to a pair,
then the [stacks 0A63] transpose `ψ` of the inverse component of [stacks 0E1W], against the unit
of [stacks 0GMT].

Neither side of that equation can be compared where its factors are valued.  `ψ`'s value
`Stacks.DerivedHom.BaseChange.homEquiv_derivedHomRestrictScalarsNatIso_inv_app_scalarEquivalence`
is `E.inverse.map b` followed by the inverse unit of the scalar equivalence `E` of [stacks 0E1W],
and the other factor is an `E.inverse.map` too: the tensor bifunctor of [stacks 0A63] *is*
`StacksDraft.DerivedHom.DerivedHomAdjunction.transportTensor` of the fixed-universe one, so on
morphisms it is `E.inverse` of the fixed-universe tensor's, by
`StacksDraft.DerivedHom.DerivedHomAdjunction.transportTensor_map`.  Meanwhile every chain-level
value the comparison has to meet — `StacksDraft.DerivedHom.DerivedInternalHom.Model.tensor`, its
transpose, and `CochainComplex.ExtendScalars.extendScalarsMonoidalIso`, the one chain map the
[stacks 068I] side carries — lives in the scalar-lift world `D(ULift R)`.

This file moves the equation there.  The whole left-hand side is one `E.inverse.map` of a
composite of `D(ULift R)` followed by one inverse unit, so
`CategoryTheory.Equivalence.inverse_map_comp_comp_unitIso_inv_eq_iff` transposes it: the equation
of `D(R)` holds exactly when an equation of `D(ULift R)` does, in which no `E.inverse` and no unit
occurs and the prefix survives as a precomposition.  `E.functor` is faithful, so the transposition
is a bijection and nothing is weakened.

The presentation `b` of `ψ` is taken as *data*, with the equation presenting it as a hypothesis,
rather than substituted: `ψ`'s value is large, a consumer may hold it in more than one shape — the
all-objects one, or the one at the keystone's K-flat pair with the content factor at the chain
level — and passing it in keeps the reduction independent of which.  That the canonical
presentation does exist, and is exactly the value of `ψ`, is
`Dualizing.exists_scalarLiftPresentation`, so the reduction is unconditional.

**What is not done here.**  The identification is not proved,
`Dualizing.TensorComparisonCompatibility` stays open, `Dualizing.KFlatAlgebraActionEq` with it,
and no tag loses its conditional caveat.  Nor is the companion hypothesis `h` of
`Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` touched: it is independent of
this one, and its frontier remains
`Dualizing.tensorComparisonCompatibility_of_kFlat_tail`.  What changes is the category the one
remaining equation is read in.

## Main results

* `Dualizing.eq_derivedTensorBaseChange_iff_scalarLift` — a morphism is the lax monoidal structure
  map of derived base change exactly when an equation of `D(ULift R)` holds, given a presentation
  of `ψ` in the shape its value has.
* `Dualizing.tensorBaseChangeMor_eq_iff_scalarLift` — **the keystone in the scalar-lift world**:
  the same at the [stacks 068I] candidate.
* `Dualizing.exists_scalarLiftPresentation` — the presentation the two above ask for always
  exists, being the value of `ψ`.

## Implementation notes

The identification of the transported tensor on morphisms holds by `rfl`, but only after the
identity of the second variable has been replaced by `E.functor` of the identity: the two differ
by `CategoryTheory.Functor.map_id`, which is a field of the functor and not a reduction.  So the
step is a rewrite by that one equation followed by `rfl` at default transparency — `rfl` being
needed explicitly, since the reduction crosses the three `Functor.comp` and `Functor.prod`
projections separating the transported bifunctor from the fixed-universe one and the automatic
`rfl` of `rw` runs below that.

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
/-- **A morphism is the lax monoidal structure map of derived base change exactly when an equation
of the scalar-lift world holds.**

`Dualizing.eq_derivedTensorBaseChange_iff_tensorTranspose` states the condition as an equation of
`D(R)` whose left-hand side is the tensor bifunctor of [stacks 0A63] applied to a pair, followed
by the [stacks 0A63] transpose `ψ` of the inverse component of [stacks 0E1W].  Given a
presentation of `ψ` as `E.inverse.map b` followed by the inverse unit of the scalar equivalence of
[stacks 0E1W] — the shape its value
`Stacks.DerivedHom.BaseChange.homEquiv_derivedHomRestrictScalarsNatIso_inv_app_scalarEquivalence`
has, and which always exists by `Dualizing.exists_scalarLiftPresentation` — the whole left-hand
side is `E.inverse` of a composite of `D(ULift R)` followed by that one inverse unit, because the
tensor bifunctor of [stacks 0A63] is the transport of the fixed-universe one.

So the condition transposes into `D(ULift R)` by
`CategoryTheory.Equivalence.inverse_map_comp_comp_unitIso_inv_eq_iff`: the fixed-universe tensor
applied to the scalar lift of the pair, followed by `b`, is the inverse counit followed by the
scalar lift of the unit of [stacks 0GMT].  `E.functor` is faithful, so this says exactly what the
equation of `D(R)` says, and it is read where the chain-level values of both sides live. -/
theorem eq_derivedTensorBaseChange_iff_scalarLift
    (X Y : DerivedCategory (ModuleCat.{max uR uA uM} R)) :
    let E := _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
      max uR uA uM} R
    let U := (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory
    let dR := derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R
    let dA := derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A
    let W := dR.tensor.obj (X, Y)
    ∀ (g : dA.tensor.obj (F.obj X, F.obj Y) ⟶ F.obj W)
      (b : (DerivedInternalHom.Model.tensor (ULift.{max uR uA uM} R)).obj
          (E.functor.obj (U.obj (dA.hom.obj (Opposite.op (F.obj Y), F.obj W))),
            E.functor.obj Y) ⟶
        E.functor.obj (U.obj (F.obj W)))
      (_hb : dR.homEquiv (U.obj (dA.hom.obj (Opposite.op (F.obj Y), F.obj W))) Y
            (U.obj (F.obj W))
            ((_root_.Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA,
              uM} f F comparison).inv.app (Opposite.op Y, F.obj W)) =
          E.inverse.map b ≫ E.unitIso.inv.app (U.obj (F.obj W))),
    g = derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y ↔
      (DerivedInternalHom.Model.tensor (ULift.{max uR uA uM} R)).map
            ((E.functor.map ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F
                    comparison).unit.app X ≫
                  U.map ((dA.homEquiv (F.obj X) (F.obj Y) (F.obj W)).symm g)),
              𝟙 (E.functor.obj Y)) :
                ((E.functor.obj X, E.functor.obj Y) :
                    DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ×
                      DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R))) ⟶
                  (E.functor.obj (U.obj (dA.hom.obj (Opposite.op (F.obj Y), F.obj W))),
                    E.functor.obj Y)) ≫
          b =
        E.counitIso.inv.app ((DerivedInternalHom.Model.tensor
              (ULift.{max uR uA uM} R)).obj (E.functor.obj X, E.functor.obj Y)) ≫
          E.functor.map ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F
            comparison).unit.app W) := by
  intro E U dR dA W g b hb
  have hid : 𝟙 (E.functor.obj Y) = E.functor.map (𝟙 Y) := (E.functor.map_id Y).symm
  have hmap : dR.tensor.map
        (((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app X ≫
            U.map ((dA.homEquiv (F.obj X) (F.obj Y) (F.obj W)).symm g), 𝟙 Y) :
          ((X, Y) : DerivedCategory (ModuleCat.{max uR uA uM} R) ×
              DerivedCategory (ModuleCat.{max uR uA uM} R)) ⟶
            (U.obj (dA.hom.obj (Opposite.op (F.obj Y), F.obj W)), Y)) =
      E.inverse.map ((DerivedInternalHom.Model.tensor (ULift.{max uR uA uM} R)).map
        ((E.functor.map ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F
                comparison).unit.app X ≫
              U.map ((dA.homEquiv (F.obj X) (F.obj Y) (F.obj W)).symm g)),
          𝟙 (E.functor.obj Y)) :
            ((E.functor.obj X, E.functor.obj Y) :
                DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ×
                  DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R))) ⟶
              (E.functor.obj (U.obj (dA.hom.obj (Opposite.op (F.obj Y), F.obj W))),
                E.functor.obj Y))) := by
    rw [hid]
    rfl
  refine (eq_derivedTensorBaseChange_iff_tensorTranspose.{uR, uA, uM} f F comparison X Y
    g).trans ?_
  rw [hb, hmap]
  exact E.inverse_map_comp_comp_unitIso_inv_eq_iff _ b _

include hF in
/-- **The keystone in the scalar-lift world.**
`Dualizing.eq_derivedTensorBaseChange_iff_scalarLift` at the [stacks 068I] candidate
`Dualizing.tensorBaseChangeMor`, so this is the same statement as
`Dualizing.tensorBaseChangeMor_eq_iff`,
`Dualizing.tensorBaseChangeMor_eq_iff_section_comp`,
`Dualizing.tensorBaseChangeMor_eq_iff_natIso_inv` and
`Dualizing.tensorBaseChangeMor_eq_iff_tensorTranspose`; what it adds is that the equation is an
equation of `D(ULift R)`, which is where the chain-level values of both of its sides live.

The [stacks 068I] side carries exactly one chain map,
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso`, by
`CochainComplex.DerivedTensor.IsTensorBaseChangeIso.hom_eq_extendScalarsMonoidalIso_hom`, and the
[stacks 0E1W] side exactly one, `Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap`, by
`Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso_inv_app_tensorKFlat_changeOfRingsMap`.
Both are maps of complexes of `ULift R`- and `ULift A`-modules, and so is everything the equation
is now written with. -/
theorem tensorBaseChangeMor_eq_iff_scalarLift
    (D : TotalDerivedExtensionScalars.{uR, max uR uA uM, uA, max uR uA uM + 1,
      max uR uA uM + 1} f)
    (X Y : DerivedCategory (ModuleCat.{max uR uA uM} R)) :
    let E := _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
      max uR uA uM} R
    let U := (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory
    let dR := derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R
    let dA := derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A
    let W := dR.tensor.obj (X, Y)
    ∀ (b : (DerivedInternalHom.Model.tensor (ULift.{max uR uA uM} R)).obj
          (E.functor.obj (U.obj (dA.hom.obj (Opposite.op (F.obj Y), F.obj W))),
            E.functor.obj Y) ⟶
        E.functor.obj (U.obj (F.obj W)))
      (_hb : dR.homEquiv (U.obj (dA.hom.obj (Opposite.op (F.obj Y), F.obj W))) Y
            (U.obj (F.obj W))
            ((_root_.Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA,
              uM} f F comparison).inv.app (Opposite.op Y, F.obj W)) =
          E.inverse.map b ≫ E.unitIso.inv.app (U.obj (F.obj W))),
    tensorBaseChangeMor.{uR, uA, uM} f F comparison D X Y =
          derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y ↔
      (DerivedInternalHom.Model.tensor (ULift.{max uR uA uM} R)).map
            ((E.functor.map ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F
                    comparison).unit.app X ≫
                  U.map ((dA.homEquiv (F.obj X) (F.obj Y) (F.obj W)).symm
                    (tensorBaseChangeMor.{uR, uA, uM} f F comparison D X Y))),
              𝟙 (E.functor.obj Y)) :
                ((E.functor.obj X, E.functor.obj Y) :
                    DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ×
                      DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R))) ⟶
                  (E.functor.obj (U.obj (dA.hom.obj (Opposite.op (F.obj Y), F.obj W))),
                    E.functor.obj Y)) ≫
          b =
        E.counitIso.inv.app ((DerivedInternalHom.Model.tensor
              (ULift.{max uR uA uM} R)).obj (E.functor.obj X, E.functor.obj Y)) ≫
          E.functor.map ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F
            comparison).unit.app W) := by
  intro E U dR dA W b hb
  exact eq_derivedTensorBaseChange_iff_scalarLift.{uR, uA, uM} f F comparison X Y
    (tensorBaseChangeMor.{uR, uA, uM} f F comparison D X Y) b hb

include hF in
/-- **The presentation of `ψ` that the reduction asks for always exists.**

`Dualizing.eq_derivedTensorBaseChange_iff_scalarLift` takes as data a morphism `b` of
`D(ULift R)` presenting the [stacks 0A63] transpose of the inverse component of [stacks 0E1W] as
`E.inverse.map b` followed by the inverse unit of the scalar equivalence.  That is precisely the
shape of the value
`Stacks.DerivedHom.BaseChange.homEquiv_derivedHomRestrictScalarsNatIso_inv_app_scalarEquivalence`,
so the datum exists at every pair and the reduction to `D(ULift R)` is unconditional.

Its witness is the value itself: the fixed-universe tensor applied to the scalar equivalence of
the scalar-restriction comparison followed by a counit, then the fixed-universe transpose of the
comparison `eF` of the two derived extensions of scalars, the inverse component of the descended
comparison of [stacks 0E1W], and the transported restriction comparison `τ`. -/
theorem exists_scalarLiftPresentation
    (X Y : DerivedCategory (ModuleCat.{max uR uA uM} R)) :
    let E := _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
      max uR uA uM} R
    let U := (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory
    let dR := derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R
    let dA := derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A
    let W := dR.tensor.obj (X, Y)
    ∃ b : (DerivedInternalHom.Model.tensor (ULift.{max uR uA uM} R)).obj
        (E.functor.obj (U.obj (dA.hom.obj (Opposite.op (F.obj Y), F.obj W))),
          E.functor.obj Y) ⟶
      E.functor.obj (U.obj (F.obj W)),
      dR.homEquiv (U.obj (dA.hom.obj (Opposite.op (F.obj Y), F.obj W))) Y (U.obj (F.obj W))
          ((_root_.Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA,
            uM} f F comparison).inv.app (Opposite.op Y, F.obj W)) =
        E.inverse.map b ≫ E.unitIso.inv.app (U.obj (F.obj W)) := by
  intro E U dR dA W
  open _root_.Stacks.DerivedHom.BaseChange in
  exact ⟨_, homEquiv_derivedHomRestrictScalarsNatIso_inv_app_scalarEquivalence.{uR, uA, uM} f F
    comparison (Opposite.op Y) (F.obj W)⟩

end Dualizing

end
