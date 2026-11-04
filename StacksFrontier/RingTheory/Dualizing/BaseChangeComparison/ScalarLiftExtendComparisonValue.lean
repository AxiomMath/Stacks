module

public import StacksFrontier.Homology.Tor.BaseChangeExtendScalarsLift
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ScalarLiftUnitChain

/-!
# The scalar-lift comparison of [stacks 0E1W] is the explicit isomorphism

Two descriptions of the degreewise comparison of "lift scalars, then extend" with "extend, then
lift scalars" across the scalar lift of [stacks 0E1W] coexisted in the library, and nothing related
them.  `Stacks.DerivedHom.BaseChange.exists_scalarLiftExtendComparison` produces a chain map as a
transpose and characterizes it only by the equation it satisfies, and every consumer of the fourth
factor of [stacks 0E1W] speaks that chain map, while
`CochainComplex.DerivedTensor.extendScalarsLiftChainIso` is an explicit isomorphism, obtained
degreewise from uniqueness of left adjoints and evaluated on pure tensors.

This file identifies them.  The characterizing equation holds for the explicit isomorphism, and the
proof is degreewise element chasing: both sides are maps out of the scalar lift of `L`, which is
not an extension of scalars, and on an element `m` both sides are `1 ⊗ m`.  The unit of the
degreewise adjunction along the lifted ring map sends `m` to `1 ⊗ m`, the explicit isomorphism
carries `1 ⊗ m` to `1 ⊗ m` by
`CochainComplex.DerivedTensor.extendScalarsLiftNatIso_hom_app_one_tmul`, and every remaining factor
of the transpose's characterization -- the inverse counit
`Stacks.DerivedHom.BaseChange.scalarLiftCounitInv` of the scalar-lift equivalence over `A`, and
the collapse `Stacks.DerivedHom.BaseChange.scalarRestrictionChainComparison` of the two
descriptions of the twice-restricted complex -- is the identity on carriers.

Uniqueness of a transpose then pins the chain map down: a chain map satisfying the characterizing
equation *is* the explicit isomorphism, so the comparison of [stacks 0E1W] may be taken to be an
isomorphism, and the two vocabularies are interchangeable.

**What is not done here.**  Nothing is registered and no caveat is lifted.  Both hypotheses of
`Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` remain open; in particular the
comparison identity `h` is untouched, and its frontier remains
`Dualizing.tensorComparisonCompatibility_of_kFlat_tail`.  Nothing downstream is rewritten to speak
the explicit isomorphism: the identification is supplied here, not propagated.

## Main results

* `Stacks.DerivedHom.BaseChange.scalarLiftExtendUnitChain_eq` -- the explicit isomorphism
  satisfies the equation characterizing the comparison of [stacks 0E1W].
* `Stacks.DerivedHom.BaseChange.eq_extendScalarsLiftChainIso` -- and it is the only chain map
  that does.
* `Stacks.DerivedHom.BaseChange.scalarLiftExtendComparison_eq_extendScalarsLiftChainIso` -- the
  transpose that `Stacks.DerivedHom.BaseChange.exists_scalarLiftExtendComparison` exhibits is
  the explicit isomorphism.
* `Stacks.DerivedHom.BaseChange.exists_isIso_scalarLiftExtendComparison` -- the comparison may
  therefore be taken to be invertible.

## References

* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex.DerivedTensor

namespace Stacks.DerivedHom.BaseChange

universe uR uA uM

attribute [local instance] Dualizing.extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)

/-- **The explicit comparison satisfies the characterizing equation of [stacks 0E1W].**

The degreewise unit of extension of scalars along the lifted ring map at the scalar lift of `L`,
followed by the restriction along the lifted ring map of
`CochainComplex.DerivedTensor.extendScalarsLiftChainIso`, is
`Stacks.DerivedHom.BaseChange.scalarLiftExtendUnitChain`: that is, the explicit isomorphism is a
chain map of the kind `Stacks.DerivedHom.BaseChange.exists_scalarLiftExtendComparison` asserts to
exist.

Both sides are maps out of the scalar lift of `L`, so this is a degreewise element identity, and on
an element `m` both sides are `1 ⊗ m`. -/
public theorem scalarLiftExtendUnitChain_eq (L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ) :
    ((ModuleCat.extendRestrictScalarsAdj.{max uR uA uM}
            (liftRingHom.{uR, uA, uM} f)).mapHomologicalComplex (ComplexShape.up ℤ)).unit.app
          (((scalarLiftFunctor.{uR, max uA uM} R).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj L) ≫
        ((ModuleCat.restrictScalars.{max uR uA uM}
            (liftRingHom.{uR, uA, uM} f)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (extendScalarsLiftChainIso.{uR, uA, uM} f L).hom =
      scalarLiftExtendUnitChain.{uR, uA, uM} f L := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  refine ModuleCat.hom_ext (LinearMap.ext (fun m => ?_))
  exact extendScalarsLiftNatIso_hom_app_one_tmul.{uR, uA, uM} f (L.X n) m

/-- **The characterizing equation of [stacks 0E1W] has only one solution.**

A transpose is unique, so a chain map satisfying the equation that characterizes the comparison of
[stacks 0E1W] is the explicit isomorphism
`CochainComplex.DerivedTensor.extendScalarsLiftChainIso`.  This is what lets a consumer stated in
terms of the chain map produced by
`Stacks.DerivedHom.BaseChange.exists_scalarLiftExtendComparison` be read in the explicit
vocabulary. -/
public theorem eq_extendScalarsLiftChainIso (L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (c₀ : ((ModuleCat.extendScalars.{max uR uA uM, max uR uA uM, max uR uA uM}
            (liftRingHom.{uR, uA, uM} f)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((scalarLiftFunctor.{uR, max uA uM} R).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj L) ⟶
        ((scalarLiftFunctor.{uA, max uR uM} A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((extensionOfScalarsCochain.{uR, uA, uM} f).obj L))
    (hc : ((ModuleCat.extendRestrictScalarsAdj.{max uR uA uM}
              (liftRingHom.{uR, uA, uM} f)).mapHomologicalComplex (ComplexShape.up ℤ)).unit.app
            (((scalarLiftFunctor.{uR, max uA uM} R).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj L) ≫
          ((ModuleCat.restrictScalars.{max uR uA uM}
              (liftRingHom.{uR, uA, uM} f)).mapHomologicalComplex (ComplexShape.up ℤ)).map c₀ =
        scalarLiftExtendUnitChain.{uR, uA, uM} f L) :
    c₀ = (extendScalarsLiftChainIso.{uR, uA, uM} f L).hom := by
  refine (((ModuleCat.extendRestrictScalarsAdj.{max uR uA uM}
      (liftRingHom.{uR, uA, uM} f)).mapHomologicalComplex
    (ComplexShape.up ℤ)).homEquiv _ _).injective ?_
  refine (Adjunction.homEquiv_unit _ _ _ _).trans (hc.trans ?_)
  exact (scalarLiftExtendUnitChain_eq.{uR, uA, uM} f L).symm.trans
    (Adjunction.homEquiv_unit _ _ _ _).symm

/-- **The transpose of the scalar-lifted unit is the explicit comparison.**

`Stacks.DerivedHom.BaseChange.exists_scalarLiftExtendComparison` exhibits its chain map as the
transpose of `Stacks.DerivedHom.BaseChange.scalarLiftExtendUnitChain` under the degreewise
extension--restriction adjunction along the lifted ring map; that transpose is
`CochainComplex.DerivedTensor.extendScalarsLiftChainIso`. -/
public theorem scalarLiftExtendComparison_eq_extendScalarsLiftChainIso
    (L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ) :
    (((ModuleCat.extendRestrictScalarsAdj.{max uR uA uM}
          (liftRingHom.{uR, uA, uM} f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).homEquiv _ _).symm (scalarLiftExtendUnitChain.{uR, uA, uM} f L) =
      (extendScalarsLiftChainIso.{uR, uA, uM} f L).hom :=
  eq_extendScalarsLiftChainIso.{uR, uA, uM} f L _
    ((Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _))

/-- **The comparison of [stacks 0E1W] may be taken to be invertible.**

`Stacks.DerivedHom.BaseChange.exists_scalarLiftExtendComparison` with its chain map evaluated:
the chain map it produces is the explicit isomorphism, hence an isomorphism.  The witness is
`CochainComplex.DerivedTensor.extendScalarsLiftChainIso`. -/
public theorem exists_isIso_scalarLiftExtendComparison
    (L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ) :
    ∃ c₀ : ((ModuleCat.extendScalars.{max uR uA uM, max uR uA uM, max uR uA uM}
            (liftRingHom.{uR, uA, uM} f)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((scalarLiftFunctor.{uR, max uA uM} R).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj L) ⟶
        ((scalarLiftFunctor.{uA, max uR uM} A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((extensionOfScalarsCochain.{uR, uA, uM} f).obj L),
      IsIso c₀ ∧
        ((ModuleCat.extendRestrictScalarsAdj.{max uR uA uM}
                (liftRingHom.{uR, uA, uM} f)).mapHomologicalComplex (ComplexShape.up ℤ)).unit.app
              (((scalarLiftFunctor.{uR, max uA uM} R).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj L) ≫
            ((ModuleCat.restrictScalars.{max uR uA uM}
                (liftRingHom.{uR, uA, uM} f)).mapHomologicalComplex (ComplexShape.up ℤ)).map c₀ =
          scalarLiftExtendUnitChain.{uR, uA, uM} f L :=
  ⟨(extendScalarsLiftChainIso.{uR, uA, uM} f L).hom, inferInstance,
    scalarLiftExtendUnitChain_eq.{uR, uA, uM} f L⟩

end Stacks.DerivedHom.BaseChange

end
