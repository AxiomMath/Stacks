module

public import StacksFrontier.Homology.HomComplex.RHom.RestrictScalarsLaxTensorResidue
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangePrefixChainMap
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeScalarLiftEvaluationPresentation

/-!
# The [stacks 068I] identification at a K-flat pair, as two chain-level statements

`Dualizing.tensorBaseChangeMor_eq_iff_exists_scalarLiftEvaluation` turns the [stacks 068I]
identification at a pair of K-flat complexes into one equation of morphisms out of a derived
tensor product, with the split presentation of the inverse component of [stacks 0E1W] discharged.
`Stacks.DerivedHom.BaseChange.prefix_eq_scalarLiftQObjIso_comp_Q_map` values the first entry of
the pair that equation applies the derived tensor bifunctor to, as the scalar-lift presentation of
`K` followed by a localized chain map.  And
`Stacks.DerivedHom.BaseChangeIso.tensor_map_comp_homEquiv_comp_eq_of_uncurry` closes the equation
once that entry is a localized chain map and the other side is the uncurrying of that chain map
with the chain-level map of [stacks 0E1W].

This file performs the assembly.  What is left of the [stacks 068I] identification at a K-flat
pair is exactly two statements about one chain map `w` over the lift of `R`:

* the [stacks 068I] prefix -- the scalar lift of the unit of [stacks 0GMT] and the restricted
  [stacks 0A63] transpose over `A` of the candidate, read through the five comparison factors of
  [stacks 0E1W] -- is the scalar-lift presentation of `K` followed by `w` localized;
* the [stacks 0GMT] side is the derived tensor bifunctor at the two scalar-lift presentations, the
  K-flat representation of the derived tensor product, and the localized uncurrying of `w`
  composed with the chain-level map of [stacks 0E1W].

Neither mentions the split presentation of [stacks 0E1W].  The first is what
`Stacks.DerivedHom.BaseChange.prefix_eq_scalarLiftQObjIso_comp_Q_map` reduces to one hypothesis on
the transpose.

**What is not done here.**  Nothing is registered and no caveat is lifted.  Both hypotheses of
`Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` remain open; in particular the
comparison identity `h` is untouched, and its frontier remains
`Dualizing.tensorComparisonCompatibility_of_kFlat_tail`.  What this file changes is that the other
hypothesis, at a K-flat pair, is two chain-level equations in a single chain map.

## Main results

* `Dualizing.tensorBaseChangeMor_eq_of_prefix_chain_map` -- the [stacks 068I] identification at a
  pair of K-flat complexes, from a chain map presenting the [stacks 068I] prefix and the uncurried
  form of the [stacks 0GMT] side.

## Implementation notes

Every data argument of the lemmas chained here is passed as a named metavariable and filled in by
`case` once the conclusion has been unified.  The goal carries the comparison `alphaB` of the
canonical change of rings at a type that is not the one the transported adjunction expects, so
eager elaboration of a data argument against it costs more than the heartbeat budget allows, while
unification of the conclusion alone is immediate.

The internal Hom complex and the scalar lift of `K` are written out rather than named: a `let` in
the statement becomes a local definition, and the elaborator does not unfold one while inferring
the middle object of a composition, so a composite written with the abbreviation on one side and
its unfolding on the other fails to typecheck even though the two are definitionally equal.

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
/-- **The [stacks 068I] identification at a K-flat pair, from two chain-level equations.**

Let `K`, `L` be K-flat, let `J` be a K-injective complex of modules over the lift of `A` carrying
a quasi-isomorphism `n` from the lift of `A ⊗_R (K ⊗_R L)`, let `I` be a K-injective complex over
the lift of `R` carrying a quasi-isomorphism `q` from the restriction of `J`, and let `w` be a
chain map from the scalar lift of `K` to the restriction of the internal Hom complex
`Hom_{A'}(A' ⊗ L', J)`.

The hypothesis `_ha` says that the [stacks 068I] prefix is the scalar-lift presentation of `K`
followed by `w` localized.

The hypothesis `_hrhs` says that the [stacks 0GMT] side -- the inverse counit of the scalar lift at
the derived tensor product, then the scalar lift of the unit at `Q K ⊗ᴸ Q L` -- is the derived
tensor bifunctor at the two scalar-lift presentations, the K-flat representation of the derived
tensor product, the localized uncurrying of `w` followed by the chain-level map of [stacks 0E1W],
and the tail.

Together they give the identification, which by
`Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` is the first of the chapter's two
keystone hypotheses. -/
theorem tensorBaseChangeMor_eq_of_prefix_chain_map
    (D : TotalDerivedExtensionScalars.{uR, max uR uA uM, uA, max uR uA uM + 1,
      max uR uA uM + 1} f)
    (K L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (hK : IsKFlat.{uR, max uR uA uM} K) (hL : IsKFlat.{uR, max uR uA uM} L) :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    letI : (ModuleCat.extendScalars.{max uR uA uM, max uR uA uM, max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    let adj := derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison
    let E := _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
      max uR uA uM} R
    let S := _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uA,
      max uR uA uM} A
    let U := (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory
    let V := (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory
    let T := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings f'
      (HomologicalComplex.zero : CochainComplex (ModuleCat.{max uR uA uM}
        (ULift.{max uR uA uM} A)) ℤ)
    let adj' := @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction
      _ _ _ _ f' _ _ T.B T.alphaB T.isLeftDerivedB
    let δ : S.inverse ⋙ U ≅ V ⋙ E.inverse :=
      _root_.Stacks.DerivedHom.BaseChange.scalarRestrictionIso.{uR, uA, uM} f
    let τ : U ⋙ E.functor ≅ S.functor ⋙ V :=
      Iso.compInverseIso (H := E.symm)
        ((Iso.inverseCompIso (G := S.symm) δ.symm).symm ≪≫
          (Functor.associator _ _ _).symm)
    let eF : E.functor ⋙ T.B ≅ F ⋙ S.functor :=
      (E.toAdjunction.comp adj').leftAdjointUniq ((adj.comp S.toAdjunction).ofNatIsoRight δ)
    let HA := DerivedInternalHom.Model.hom (ULift.{max uR uA uM} A)
    let dA := derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A
    let W := (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.obj
      (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)
    let M := F.obj W
    let K₀ := ((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L
    let X₃ := ((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj
        (tensorComplex.{uR, max uR uA uM} K L))
    ∀ (J : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)) ℤ)
      (I : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ℤ)
      [J.IsKInjective] [I.IsKInjective]
      (q : (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM}
        f').obj J ⟶ I) [QuasiIso q]
      (n : X₃ ⟶ J) [QuasiIso n],
    letI : IsIso (T.alphaB.app K₀) :=
      _root_.Stacks.DerivedHom.BaseChange.isIso_extendScalarsCounit_app_of_kFlat f'
        T.B T.alphaB K₀
        (_root_.Stacks.DerivedHom.BaseChange.kFlat_scalarLift.{uR, max uR uA uM} R L hL)
    let eX := _root_.Stacks.DerivedHom.BaseChange.scalarLiftQObjIso.{uR, max uR uA uM} R L
    let eY := _root_.Stacks.DerivedHom.BaseChange.tensorKFlatKInjectiveLift.{uR, uA, uM} f F
      comparison K L hK hL J n
    ∀ (w : ((ModuleCat.restrictScalars.{max uR uA uM}
            (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K ⟶
        (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM} f').obj
          (CochainComplex.HomComplexR (ULift.{max uR uA uM} A)
            ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM,
              max uR uA uM} f').obj K₀) J))
      (_ha : E.functor.map (adj.unit.app (DerivedCategory.Q.obj K) ≫
                U.map ((dA.homEquiv (F.obj (DerivedCategory.Q.obj K))
                    (F.obj (DerivedCategory.Q.obj L)) M).symm
                  (tensorBaseChangeMor.{uR, uA, uM} f F comparison D
                    (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)))) ≫
              (E.functor.map (δ.hom.app (HA.obj
                      (Opposite.op (S.functor.obj (F.obj (DerivedCategory.Q.obj L))),
                        S.functor.obj M))) ≫
                  E.counitIso.hom.app (V.obj (HA.obj
                    (Opposite.op (S.functor.obj (F.obj (DerivedCategory.Q.obj L))),
                      S.functor.obj M)))) ≫
                V.map (HA.map (CategoryTheory.Prod.mkHom
                      (eF.hom.app (DerivedCategory.Q.obj L)).op (𝟙 (S.functor.obj M)))) ≫
                  (_root_.Stacks.DerivedHom.BaseChange.homRestrictTarget f' T.B).map
                      (CategoryTheory.Prod.mkHom eX.inv.op eY.hom) ≫
                    V.map (_root_.Stacks.DerivedHom.BaseChange.homModelIso
                        ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM,
                          max uR uA uM} f').obj K₀) J (asIso (T.alphaB.app K₀))
                        (Iso.refl (DerivedCategory.Q.obj J))).hom ≫
                      ((ModuleCat.restrictScalars.{max uR uA uM}
                            f').mapDerivedCategoryFactors.app
                        (CochainComplex.HomComplexR (ULift.{max uR uA uM} A)
                          ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM,
                            max uR uA uM} f').obj K₀) J)).hom =
          (_root_.Stacks.DerivedHom.BaseChange.scalarLiftQObjIso.{uR, max uR uA uM} R K).hom ≫
            DerivedCategory.Q.map w)
      (_hrhs : E.counitIso.inv.app ((DerivedInternalHom.Model.tensor
                  (ULift.{max uR uA uM} R)).obj
                (E.functor.obj (DerivedCategory.Q.obj K),
                  E.functor.obj (DerivedCategory.Q.obj L))) ≫
              E.functor.map (adj.unit.app W) =
            (DerivedInternalHom.Model.adjunction (ULift.{max uR uA uM} R)).tensor.map
                (((_root_.Stacks.DerivedHom.BaseChange.scalarLiftQObjIso.{uR,
                        max uR uA uM} R K).hom, eX.hom) :
                  ((E.functor.obj (DerivedCategory.Q.obj K),
                        E.functor.obj (DerivedCategory.Q.obj L)) :
                      DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ×
                        DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R))) ⟶
                    (DerivedCategory.Q.obj (((ModuleCat.restrictScalars.{max uR uA uM}
                          (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+*
                            R).toRingHom).mapHomologicalComplex (ComplexShape.up ℤ)).obj K),
                      DerivedCategory.Q.obj K₀)) ≫
              ((DerivedInternalHom.Model.adjunction (ULift.{max uR uA uM} R)).tensorIso
                  (((ModuleCat.restrictScalars.{max uR uA uM}
                      (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+*
                        R).toRingHom).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) K₀
                  (_root_.Stacks.DerivedHom.BaseChange.kFlat_scalarLift.{uR,
                    max uR uA uM} R L hL)).hom ≫
                DerivedCategory.Q.map (DerivedInternalHom.Model.uncurry
                    (w ≫ _root_.Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f' K₀ J I
                      q)) ≫
                  (((ModuleCat.restrictScalars.{max uR uA uM}
                              f').mapDerivedCategoryFactors.app J ≪≫
                          @asIso _ _ _ _ (DerivedCategory.Q.map q)
                            ((DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2
                              inferInstance)).inv ≫
                    V.map eY.inv ≫ τ.inv.app M)),
    tensorBaseChangeMor.{uR, uA, uM} f F comparison D (DerivedCategory.Q.obj K)
        (DerivedCategory.Q.obj L) =
      derivedTensorBaseChange.{uR, uA, uM} f F comparison (DerivedCategory.Q.obj K)
        (DerivedCategory.Q.obj L) := by
  intro f' adj E S U V T adj' δ τ eF HA dA W M K₀ X₃ J I hJ hI q hq n hn eX eY w ha hrhs
  refine (tensorBaseChangeMor_eq_iff_exists_scalarLiftEvaluation.{uR, uA, uM} f F comparison D
    K L hK hL).mpr ?_
  open _root_.Stacks.DerivedHom.BaseChange
    _root_.Stacks.DerivedHom.ScalarTransportedInternalHom in
  refine ⟨_, _, _, _, _, _, _, _, _,
    homEquiv_derivedHomRestrictScalarsNatIso_inv_app_tensorKFlat_split.{uR, uA, uM}
      f F comparison K L hK hL J I q n _ _
      (derivedScalarEquivalence_symm_counit_app.{uR, max uR uA uM, max uR uA uM + 1} R _)
      (derivedScalarEquivalence_counit_app.{uR, max uR uA uM, max uR uA uM + 1} R _), ?_⟩
  refine _root_.Stacks.DerivedHom.BaseChangeIso.tensor_map_comp_homEquiv_comp_eq_of_uncurry.{max uR
      uA uM} ?g ?XK ?XL ?MM ?Kc ?Pc ?hP J I ?q ?w ?eK ?lam ?a ?c ?rho ?rhs ?ha ?hc ?hrhs
  case Kc =>
    exact ((ModuleCat.restrictScalars.{max uR uA uM}
      (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K
  case hP =>
    exact _root_.Stacks.DerivedHom.BaseChange.kFlat_scalarLift.{uR, max uR uA uM} R L hL
  case q => exact q
  case eK =>
    exact _root_.Stacks.DerivedHom.BaseChange.scalarLiftQObjIso.{uR, max uR uA uM} R K
  case w => exact w
  case hc =>
    open _root_.Stacks.DerivedHom.BaseChange in
    exact Q_map_homComplexChangeOfRingsMap_scalarLift_evaluation.{uR, uA, uM} f L hL J I q
  case ha => exact ha
  case hrhs => exact hrhs

end Dualizing

end
