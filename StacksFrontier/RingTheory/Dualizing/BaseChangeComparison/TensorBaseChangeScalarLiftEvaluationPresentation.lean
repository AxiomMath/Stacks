module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.HomRestrictScalarsTransposeSplit
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeScalarLiftEvaluation

/-!
# The split presentation the keystone asks for, at the keystone's K-flat pair

`Dualizing.tensorBaseChangeMor_eq_iff_scalarLiftEvaluation` reduces the [stacks 068I]
identification to an equation of morphisms out of `E X ⊗ᴸ E Y` with no [stacks 0A63] transpose on
either side, but only given a presentation `hb` of the uncurried inverse component of
[stacks 0E1W] in a particular split shape: a prefix, one fixed-universe transpose, and a tail
which is the internal-Hom bifunctor at a pair.

`Stacks.DerivedHom.BaseChange.homEquiv_derivedHomRestrictScalarsNatIso_inv_app_tensorKFlat_split`
produces exactly that value at the keystone's K-flat pair, with the two counits it mentions passed
as data.  This file supplies them and so wires the two together: the presentation the keystone
asks for exists at every pair of K-flat complexes and every choice of the two K-injective
resolutions the chain-level map of [stacks 0E1W] is read at.

The only step is the identification of the trailing counit.  The split lemma states it as the
counit of `StacksDraft.DerivedHom.derivedScalarEquivalence`, the equivalence
`Dualizing.derivedHomAdjunctionOverRing` is transported along, while the keystone states it as the
inverse unit of `Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence`, the
equivalence [stacks 0E1W] is stated with.  The two agree by
`Stacks.DerivedHom.ScalarTransportedInternalHom.derivedScalarEquivalence_counit_app`, and the
leading one likewise by `…derivedScalarEquivalence_symm_counit_app`.

**What is not done here.**  No tag is registered and no caveat is lifted.  Both hypotheses of
`Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` remain open; in particular the
comparison identity `h` is untouched, and its frontier remains
`Dualizing.tensorComparisonCompatibility_of_kFlat_tail`.  What this file changes is that the
hypothesis `hb` of the keystone no longer has to be carried by a consumer: it is discharged, and
the whole remaining content of the [stacks 068I] identification at a K-flat pair is the one
equation of `Dualizing.tensorBaseChangeMor_eq_iff_exists_scalarLiftEvaluation`.

## Main results

* `Dualizing.exists_scalarLiftEvaluationPresentation` -- the split presentation
  `Dualizing.tensorBaseChangeMor_eq_iff_scalarLiftEvaluation` asks for always exists at a K-flat
  pair, so that reduction is unconditional there.
* `Dualizing.tensorBaseChangeMor_eq_iff_exists_scalarLiftEvaluation` -- the [stacks 068I]
  identification at a K-flat pair holds exactly when there is such a presentation whose
  no-transpose equation holds.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.MonoidalCategory StacksDraft.DerivedHom
open CochainComplex.DerivedTensor
open CochainComplex.DerivedExtensionScalars
open CochainComplex.ExtendScalars

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
/-- **The split presentation the keystone asks for exists at a K-flat pair.**

`Dualizing.tensorBaseChangeMor_eq_iff_scalarLiftEvaluation` takes the uncurried inverse component
of [stacks 0E1W] presented as a prefix, one fixed-universe [stacks 0A63] transpose and a tail
which is the internal-Hom bifunctor at a pair.
`Stacks.DerivedHom.BaseChange.homEquiv_derivedHomRestrictScalarsNatIso_inv_app_tensorKFlat_split`
is that value at the keystone's K-flat pair, once the two counits it carries as data are supplied:
the leading one is the counit isomorphism of
`Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence` and the trailing one its
inverse unit, by
`Stacks.DerivedHom.ScalarTransportedInternalHom.derivedScalarEquivalence_symm_counit_app` and
`…derivedScalarEquivalence_counit_app`.

So the reduction of `Dualizing.tensorBaseChangeMor_eq_iff_scalarLiftEvaluation` is unconditional
at a K-flat pair: no consumer has to carry `hb`. -/
theorem exists_scalarLiftEvaluationPresentation
    (K L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (hK : IsKFlat.{uR, max uR uA uM} K) (hL : IsKFlat.{uR, max uR uA uM} L) :
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    let X₃ := ((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
            ((CochainComplex.DerivedTensor.extensionOfScalarsCochain.{uR, uA,
              max uR uA uM} f).obj (CochainComplex.DerivedTensor.tensorComplex.{uR,
                max uR uA uM} K L))
    ∀ (J : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)) ℤ)
      (I : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ℤ)
      [J.IsKInjective] [I.IsKInjective]
      (q : (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM}
        f').obj J ⟶ I) [QuasiIso q]
      (n : X₃ ⟶ J) [QuasiIso n],
    let E := _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
      max uR uA uM} R
    let U := (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory
    let dR := derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R
    let dA := derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A
    let W := dR.tensor.obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)
    let HR := DerivedInternalHom.Model.hom (ULift.{max uR uA uM} R)
    let TR := DerivedInternalHom.Model.tensor (ULift.{max uR uA uM} R)
    ∃ (P P' L' M' : DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)))
      (v : E.functor.obj (U.obj (dA.hom.obj
        (Opposite.op (F.obj (DerivedCategory.Q.obj L)), F.obj W))) ⟶ P)
      (p : P ⟶ P') (lam : E.functor.obj (DerivedCategory.Q.obj L) ⟶ L')
      (rho : M' ⟶ E.functor.obj (U.obj (F.obj W))) (c : TR.obj (P', L') ⟶ M'),
      dR.homEquiv (U.obj (dA.hom.obj
            (Opposite.op (F.obj (DerivedCategory.Q.obj L)), F.obj W)))
          (DerivedCategory.Q.obj L) (U.obj (F.obj W))
          ((_root_.Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA,
            uM} f F comparison).inv.app
              (Opposite.op (DerivedCategory.Q.obj L), F.obj W)) =
        E.inverse.map
            (TR.map
                ((v, 𝟙 (E.functor.obj (DerivedCategory.Q.obj L))) :
                  ((E.functor.obj (U.obj (dA.hom.obj
                        (Opposite.op (F.obj (DerivedCategory.Q.obj L)), F.obj W))),
                      E.functor.obj (DerivedCategory.Q.obj L)) :
                    DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ×
                      DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R))) ⟶
                    (P, E.functor.obj (DerivedCategory.Q.obj L))) ≫
              DerivedInternalHom.Model.homEquiv P
                (E.functor.obj (DerivedCategory.Q.obj L))
                (E.functor.obj (U.obj (F.obj W)))
                (p ≫ (DerivedInternalHom.Model.homEquiv P' L' M').symm c ≫
                  HR.map ((lam.op, rho) :
                    ((Opposite.op L', M') :
                      (DerivedCategory (ModuleCat.{max uR uA uM}
                        (ULift.{max uR uA uM} R)))ᵒᵖ ×
                        DerivedCategory (ModuleCat.{max uR uA uM}
                          (ULift.{max uR uA uM} R))) ⟶
                      (Opposite.op (E.functor.obj (DerivedCategory.Q.obj L)),
                        E.functor.obj (U.obj (F.obj W)))))) ≫
          E.unitIso.inv.app (U.obj (F.obj W)) := by
  intro f' X₃ J I hJ hI q hq n hn E U dR dA W HR TR
  open _root_.Stacks.DerivedHom.BaseChange
    _root_.Stacks.DerivedHom.ScalarTransportedInternalHom in
  exact ⟨_, _, _, _, _, _, _, _, _,
    homEquiv_derivedHomRestrictScalarsNatIso_inv_app_tensorKFlat_split.{uR, uA, uM}
      f F comparison K L hK hL J I q n _ _
      (derivedScalarEquivalence_symm_counit_app.{uR, max uR uA uM, max uR uA uM + 1} R _)
      (derivedScalarEquivalence_counit_app.{uR, max uR uA uM, max uR uA uM + 1} R _)⟩

include hF in
/-- **The [stacks 068I] identification at a K-flat pair, with the presentation discharged.**

`Dualizing.tensorBaseChangeMor_eq_iff_scalarLiftEvaluation` with its hypothesis `hb` folded into
the right-hand side as an existential, which
`Dualizing.exists_scalarLiftEvaluationPresentation` makes harmless: a presentation always exists at
a K-flat pair, so the forward direction loses nothing, and the backward direction is the keystone
applied to the presentation the witness carries.

This is the whole remaining content of the [stacks 068I] identification at a K-flat pair -- which
by `Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` is the hypothesis `hmu` of the
chapter's keystone -- as **one equation of morphisms out of `E (Q K) ⊗ᴸ E (Q L)`** with no
[stacks 0A63] transpose on either side and no side condition.

The companion hypothesis `h` of that reduction is untouched and remains open; its frontier is
`Dualizing.tensorComparisonCompatibility_of_kFlat_tail`. -/
theorem tensorBaseChangeMor_eq_iff_exists_scalarLiftEvaluation
    (D : TotalDerivedExtensionScalars.{uR, max uR uA uM, uA, max uR uA uM + 1,
      max uR uA uM + 1} f)
    (K L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (hK : IsKFlat.{uR, max uR uA uM} K) (hL : IsKFlat.{uR, max uR uA uM} L) :
    let E := _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
      max uR uA uM} R
    let U := (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory
    let dR := derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R
    let dA := derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A
    let W := dR.tensor.obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)
    let HR := DerivedInternalHom.Model.hom (ULift.{max uR uA uM} R)
    let TR := DerivedInternalHom.Model.tensor (ULift.{max uR uA uM} R)
    (tensorBaseChangeMor.{uR, uA, uM} f F comparison D (DerivedCategory.Q.obj K)
            (DerivedCategory.Q.obj L) =
          derivedTensorBaseChange.{uR, uA, uM} f F comparison (DerivedCategory.Q.obj K)
            (DerivedCategory.Q.obj L) ↔
        ∃ (P P' L' M' : DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)))
          (v : E.functor.obj (U.obj (dA.hom.obj
            (Opposite.op (F.obj (DerivedCategory.Q.obj L)), F.obj W))) ⟶ P)
          (p : P ⟶ P') (lam : E.functor.obj (DerivedCategory.Q.obj L) ⟶ L')
          (rho : M' ⟶ E.functor.obj (U.obj (F.obj W))) (c : TR.obj (P', L') ⟶ M'),
          (dR.homEquiv (U.obj (dA.hom.obj
                  (Opposite.op (F.obj (DerivedCategory.Q.obj L)), F.obj W)))
                (DerivedCategory.Q.obj L) (U.obj (F.obj W))
                ((_root_.Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA,
                  uM} f F comparison).inv.app
                    (Opposite.op (DerivedCategory.Q.obj L), F.obj W)) =
              E.inverse.map
                  (TR.map
                      ((v, 𝟙 (E.functor.obj (DerivedCategory.Q.obj L))) :
                        ((E.functor.obj (U.obj (dA.hom.obj
                              (Opposite.op (F.obj (DerivedCategory.Q.obj L)), F.obj W))),
                            E.functor.obj (DerivedCategory.Q.obj L)) :
                          DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ×
                            DerivedCategory (ModuleCat.{max uR uA uM}
                              (ULift.{max uR uA uM} R))) ⟶
                          (P, E.functor.obj (DerivedCategory.Q.obj L))) ≫
                    DerivedInternalHom.Model.homEquiv P
                      (E.functor.obj (DerivedCategory.Q.obj L))
                      (E.functor.obj (U.obj (F.obj W)))
                      (p ≫ (DerivedInternalHom.Model.homEquiv P' L' M').symm c ≫
                        HR.map ((lam.op, rho) :
                          ((Opposite.op L', M') :
                            (DerivedCategory (ModuleCat.{max uR uA uM}
                              (ULift.{max uR uA uM} R)))ᵒᵖ ×
                              DerivedCategory (ModuleCat.{max uR uA uM}
                                (ULift.{max uR uA uM} R))) ⟶
                              (Opposite.op (E.functor.obj (DerivedCategory.Q.obj L)),
                                E.functor.obj (U.obj (F.obj W)))))) ≫
                E.unitIso.inv.app (U.obj (F.obj W))) ∧
            TR.map ((E.functor.map ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F
                      comparison).unit.app (DerivedCategory.Q.obj K) ≫
                      U.map ((dA.homEquiv (F.obj (DerivedCategory.Q.obj K))
                        (F.obj (DerivedCategory.Q.obj L)) (F.obj W)).symm
                        (tensorBaseChangeMor.{uR, uA, uM} f F comparison D
                          (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)))) ≫ v ≫ p, lam) :
                  ((E.functor.obj (DerivedCategory.Q.obj K),
                      E.functor.obj (DerivedCategory.Q.obj L)) :
                    DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ×
                      DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R))) ⟶
                    (P', L')) ≫ c ≫ rho =
              E.counitIso.inv.app (TR.obj (E.functor.obj (DerivedCategory.Q.obj K),
                  E.functor.obj (DerivedCategory.Q.obj L))) ≫
                E.functor.map ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F
                  comparison).unit.app W)) := by
  intro E U dR dA W HR TR
  have key := tensorBaseChangeMor_eq_iff_scalarLiftEvaluation.{uR, uA, uM} f F comparison D
    (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
  refine ⟨fun heq => ?_, fun ⟨_, _, _, _, _, _, _, _, _, hb, hev⟩ =>
    (key _ _ _ _ _ _ _ _ _ hb).mpr hev⟩
  obtain ⟨J, n, hn, hJ⟩ := CochainComplex.exists_quasiIso_isKInjective
    (((ModuleCat.restrictScalars.{max uR uA uM}
      (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj
          (tensorComplex.{uR, max uR uA uM} K L)))
  obtain ⟨I, q, hq, hI⟩ := CochainComplex.exists_quasiIso_isKInjective
    ((CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM}
      (((ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom :
        ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A))).obj J)
  obtain ⟨P, P', L', M', v, p, lam, rho, c, hb⟩ :=
    exists_scalarLiftEvaluationPresentation.{uR, uA, uM} f F comparison K L hK hL J I q n
  exact ⟨P, P', L', M', v, p, lam, rho, c, hb, (key _ _ _ _ _ _ _ _ _ hb).mp heq⟩

end Dualizing

end
