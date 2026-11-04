module

public import StacksFrontier.Homology.HomComplex.DerivedAdjunctionHomMapTail
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeScalarLiftTranspose

/-!
# The keystone with no transpose left on either side

`Dualizing.tensorBaseChangeMor_eq_iff_scalarLiftTranspose` states the [stacks 068I] identification
as an equation of `D(ULift R)` between a composite `u ≫ v ≫ a` landing in an internal Hom and the
[stacks 0A63] transpose of the unit side.  Its two sides carry one transpose each, and **the two
sit at unrelated triples**: the one on the left is the transpose at a pair of localized complexes,
a K-flat Hom-source and a K-injective Hom-target, because those are the representatives at which
the chain-level map of [stacks 0E1W] exists; the one on the right is at the pair the comparison is
natural at.  Two transposes at unrelated triples cancel against nothing.

This file brings them to one triple.  What sits between them in the left-hand side is, in the
shape the keystone's value has, a prefix of the source variable and a tail
`hom.map (lam.op, rho)` of the internal Hom -- `lam` the K-flat presentation of the Hom-source and
`rho` the composite of the K-injective presentation of the Hom-target with the transported
restriction comparison.  Both are absorbed into the left transpose by
`StacksDraft.DerivedHom.DerivedHomAdjunction.comp_homEquiv_symm_comp_hom_map`, which moves all
three variables at once; the two transposes then sit at the triple the tail reaches and cancel.

The equation that comes out has **no transpose in either side**.  Both are morphisms out of
`E X ⊗ᴸ E Y`: the left-hand side is the tensoring of the whole prefix with `lam`, followed by the
transposed map `c` of the [stacks 0E1W] side and by `rho`; the right-hand side is the inverse
counit of the scalar equivalence followed by `E.functor` of the unit of [stacks 0GMT].

**What is not done here.**  The identification is not proved,
`Dualizing.TensorComparisonCompatibility` stays open, `Dualizing.KFlatAlgebraActionEq` with it,
and no tag loses its conditional caveat.  In particular the companion hypothesis `h` of
`Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` is untouched -- it is independent
of this one and its frontier remains `Dualizing.tensorComparisonCompatibility_of_kFlat_tail`.
What changes is that the one remaining equation is an equation of morphisms out of a derived
tensor product, with the chain content of both sides exposed and no [stacks 0A63] transpose
standing between them.

## Main results

* `Dualizing.eq_derivedTensorBaseChange_iff_scalarLiftEvaluation` -- a morphism is the lax
  monoidal structure map of derived base change exactly when an equation of morphisms out of
  `E X ⊗ᴸ E Y` holds, with no transpose on either side.
* `Dualizing.tensorBaseChangeMor_eq_iff_scalarLiftEvaluation` -- **the keystone in that shape**:
  the same at the [stacks 068I] candidate.

## Implementation notes

The presentation of `a` is passed as data in the split shape rather than substituted, for the
reason recorded in
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeScalarLift`: a consumer may
hold the value of the transpose of the inverse component of [stacks 0E1W] in more than one shape,
and all of them agree on the prefix and on the tail.

The absorption is `StacksDraft.DerivedHom.DerivedHomAdjunction.comp_homEquiv_symm_comp_hom_map`,
at the adjunction underlying `StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction`, which
is where the fixed-universe transposes of the scalar-lift world live.  It needs no object to be
presented as a localized complex, which is why it applies here and the evaluation lemmas
`StacksDraft.DerivedHom.DerivedInternalHom.Model.homEquiv_map_uncurry` and `…homEquiv_composition`
do not.

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
of morphisms out of `E X ⊗ᴸ E Y` holds.**

`Dualizing.eq_derivedTensorBaseChange_iff_scalarLiftTranspose` with the morphism `a` of that
reduction taken apart into the shape the keystone's value has: a prefix `p` of the source
variable, one fixed-universe [stacks 0A63] transpose at a triple `(P', L', M')` of its own, and a
tail `hom.map (lam.op, rho)` of the internal Hom it lands in.

`StacksDraft.DerivedHom.DerivedHomAdjunction.comp_homEquiv_symm_comp_hom_map_eq_iff` absorbs the
prefix and the tail into that transpose, which brings it to the triple
`(E X, E Y, E (U (F W)))` of the transpose on the other side, where the two cancel.  What is left
is an equation of morphisms out of `E X ⊗ᴸ E Y`: the tensoring of the whole prefix
`E.functor.map (η_X ≫ (transpose of the candidate)|_R) ≫ v ≫ p` with `lam`, followed by the
transposed map `c` and by `rho`, against the inverse counit of the scalar equivalence followed by
`E.functor` of the unit of [stacks 0GMT].

The transposes being bijections, this says exactly what the equation of
`Dualizing.eq_derivedTensorBaseChange_iff_scalarLift` says; nothing is weakened in either
direction. -/
theorem eq_derivedTensorBaseChange_iff_scalarLiftEvaluation
    (X Y : DerivedCategory (ModuleCat.{max uR uA uM} R)) :
    let E := _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
      max uR uA uM} R
    let U := (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory
    let dR := derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R
    let dA := derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A
    let W := dR.tensor.obj (X, Y)
    let HR := DerivedInternalHom.Model.hom (ULift.{max uR uA uM} R)
    let TR := DerivedInternalHom.Model.tensor (ULift.{max uR uA uM} R)
    ∀ (g : dA.tensor.obj (F.obj X, F.obj Y) ⟶ F.obj W)
      (P P' L' M' : DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)))
      (v : E.functor.obj (U.obj (dA.hom.obj (Opposite.op (F.obj Y), F.obj W))) ⟶ P)
      (p : P ⟶ P') (lam : E.functor.obj Y ⟶ L')
      (rho : M' ⟶ E.functor.obj (U.obj (F.obj W))) (c : TR.obj (P', L') ⟶ M')
      (_hb : dR.homEquiv (U.obj (dA.hom.obj (Opposite.op (F.obj Y), F.obj W))) Y
            (U.obj (F.obj W))
            ((_root_.Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA,
              uM} f F comparison).inv.app (Opposite.op Y, F.obj W)) =
          E.inverse.map
              (TR.map
                  ((v, 𝟙 (E.functor.obj Y)) :
                    ((E.functor.obj (U.obj (dA.hom.obj (Opposite.op (F.obj Y), F.obj W))),
                        E.functor.obj Y) :
                      DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ×
                        DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R))) ⟶
                      (P, E.functor.obj Y)) ≫
                DerivedInternalHom.Model.homEquiv P (E.functor.obj Y)
                  (E.functor.obj (U.obj (F.obj W)))
                  (p ≫ (DerivedInternalHom.Model.homEquiv P' L' M').symm c ≫
                    HR.map ((lam.op, rho) :
                      ((Opposite.op L', M') :
                        (DerivedCategory (ModuleCat.{max uR uA uM}
                          (ULift.{max uR uA uM} R)))ᵒᵖ ×
                          DerivedCategory (ModuleCat.{max uR uA uM}
                            (ULift.{max uR uA uM} R))) ⟶
                        (Opposite.op (E.functor.obj Y),
                          E.functor.obj (U.obj (F.obj W)))))) ≫
            E.unitIso.inv.app (U.obj (F.obj W))),
    g = derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y ↔
      TR.map ((E.functor.map ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F
                comparison).unit.app X ≫
                U.map ((dA.homEquiv (F.obj X) (F.obj Y) (F.obj W)).symm g)) ≫ v ≫ p, lam) :
            ((E.functor.obj X, E.functor.obj Y) :
              DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ×
                DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R))) ⟶
              (P', L')) ≫ c ≫ rho =
        E.counitIso.inv.app (TR.obj (E.functor.obj X, E.functor.obj Y)) ≫
          E.functor.map ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F
            comparison).unit.app W) := by
  intro E U dR dA W HR TR g P P' L' M' v p lam rho c hb
  refine (eq_derivedTensorBaseChange_iff_scalarLiftTranspose.{uR, uA, uM} f F comparison X Y g
    P v _ hb).trans ?_
  conv_lhs => rw [← Category.assoc, ← Category.assoc, Category.assoc _ v p]
  exact (DerivedInternalHom.Model.adjunction
    (ULift.{max uR uA uM} R)).toDerivedHomAdjunction.comp_homEquiv_symm_comp_hom_map_eq_iff _
      lam rho c _

include hF in
/-- **The keystone with no transpose left on either side.**

`Dualizing.eq_derivedTensorBaseChange_iff_scalarLiftEvaluation` at the [stacks 068I] candidate
`Dualizing.tensorBaseChangeMor`, so this is the same statement as
`Dualizing.tensorBaseChangeMor_eq_iff`,
`Dualizing.tensorBaseChangeMor_eq_iff_tensorTranspose`,
`Dualizing.tensorBaseChangeMor_eq_iff_scalarLift` and
`Dualizing.tensorBaseChangeMor_eq_iff_scalarLiftTranspose`; what it adds is that the remaining
equation is between two morphisms out of `E X ⊗ᴸ E Y`, with no [stacks 0A63] transpose on either
side.

Both sides are now where their chain-level values live, and nothing stands between them: the
[stacks 068I] side carries exactly one chain map,
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso`, and the [stacks 0E1W] side exactly one,
the restricted evaluation of
`Stacks.DerivedHom.BaseChange.Q_map_homComplexChangeOfRingsMap_scalarLift_evaluation`, inside
`c`. -/
theorem tensorBaseChangeMor_eq_iff_scalarLiftEvaluation
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
    let TR := DerivedInternalHom.Model.tensor (ULift.{max uR uA uM} R)
    ∀ (P P' L' M' : DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)))
      (v : E.functor.obj (U.obj (dA.hom.obj (Opposite.op (F.obj Y), F.obj W))) ⟶ P)
      (p : P ⟶ P') (lam : E.functor.obj Y ⟶ L')
      (rho : M' ⟶ E.functor.obj (U.obj (F.obj W))) (c : TR.obj (P', L') ⟶ M')
      (_hb : dR.homEquiv (U.obj (dA.hom.obj (Opposite.op (F.obj Y), F.obj W))) Y
            (U.obj (F.obj W))
            ((_root_.Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA,
              uM} f F comparison).inv.app (Opposite.op Y, F.obj W)) =
          E.inverse.map
              (TR.map
                  ((v, 𝟙 (E.functor.obj Y)) :
                    ((E.functor.obj (U.obj (dA.hom.obj (Opposite.op (F.obj Y), F.obj W))),
                        E.functor.obj Y) :
                      DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ×
                        DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R))) ⟶
                      (P, E.functor.obj Y)) ≫
                DerivedInternalHom.Model.homEquiv P (E.functor.obj Y)
                  (E.functor.obj (U.obj (F.obj W)))
                  (p ≫ (DerivedInternalHom.Model.homEquiv P' L' M').symm c ≫
                    HR.map ((lam.op, rho) :
                      ((Opposite.op L', M') :
                        (DerivedCategory (ModuleCat.{max uR uA uM}
                          (ULift.{max uR uA uM} R)))ᵒᵖ ×
                          DerivedCategory (ModuleCat.{max uR uA uM}
                            (ULift.{max uR uA uM} R))) ⟶
                        (Opposite.op (E.functor.obj Y),
                          E.functor.obj (U.obj (F.obj W)))))) ≫
            E.unitIso.inv.app (U.obj (F.obj W))),
    tensorBaseChangeMor.{uR, uA, uM} f F comparison D X Y =
          derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y ↔
      TR.map ((E.functor.map ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F
                comparison).unit.app X ≫
                U.map ((dA.homEquiv (F.obj X) (F.obj Y) (F.obj W)).symm
                  (tensorBaseChangeMor.{uR, uA, uM} f F comparison D X Y))) ≫ v ≫ p, lam) :
            ((E.functor.obj X, E.functor.obj Y) :
              DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ×
                DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R))) ⟶
              (P', L')) ≫ c ≫ rho =
        E.counitIso.inv.app (TR.obj (E.functor.obj X, E.functor.obj Y)) ≫
          E.functor.map ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F
            comparison).unit.app W) := by
  intro E U dR dA W HR TR P P' L' M' v p lam rho c hb
  exact eq_derivedTensorBaseChange_iff_scalarLiftEvaluation.{uR, uA, uM} f F comparison X Y
    (tensorBaseChangeMor.{uR, uA, uM} f F comparison D X Y) P P' L' M' v p lam rho c hb

end Dualizing

end
