module

public import StacksFrontier.Algebra.DifferentialGraded.Module.HomEvaluationDerivedIso

/-!
# The descent of Tag 09LK's comparison `ν`, computed on a complex

`CochainComplex.homEvaluationDerivedIso` is obtained by descent along `DGCategory.compToK`: it is
`CategoryTheory.Functor.preimageIso` of an explicit isomorphism

`α : ev_K(h_-) ⋙ Q ≅ Hom^•(K, -) ⋙ Q` of functors on `Comp(Comp^dg(A))`

under the fully faithful functor `W = (- ∘ compToK)`.

This file records that `W` carries both directions of `CochainComplex.homEvaluationDerivedIso` to
the corresponding directions of `α`. Since `DGCategory.compToK` is the identity on objects, both
directions of `CochainComplex.homEvaluationDerivedIso` at a complex are then the composites of the
three factors of `α`: `DerivedCategory.quotientCompQhIso`, the unlocalized comparison
`CochainComplex.homEvaluationComparisonIso`, and `DGCategory.HomRepresentation.forgetSquareIso`.
The inverse of the comparison `ν` in the proof of [Stacks, Tag 09LK] is decomposed into the
inverses of its three factors.

## Main results

* `CochainComplex.map_homEvaluationDerivedIso_hom` and
  `CochainComplex.map_homEvaluationDerivedIso_inv`: restricted along `compToK`, the two directions
  of `CochainComplex.homEvaluationDerivedIso` are those of `α`.
* `CochainComplex.homEvaluationDerivedIso_hom_app` and
  `CochainComplex.homEvaluationDerivedIso_inv_app`: both directions at a complex, as composites of
  the factors of `α`.
* `CochainComplex.homDerivedLiftForgetIso_inv`: the inverse of the comparison `ν` as the composite
  of the inverses of its three factors, the middle one being
  `CochainComplex.homDerivedLiftForgetIsoMid`.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK);
  [Tag 09LE](https://stacks.math.columbia.edu/tag/09LE), the functor `Hom(K, -)`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe w u

namespace CochainComplex

variable (A : Type u) [Category.{0} A] [Preadditive A] (K : CochainComplex A ℤ)
  [HasDerivedCategory.{w} (ModuleCat.{0} ℤ)]

/-- **The forward direction of the descent, characterised.** Restricting
`CochainComplex.homEvaluationDerivedIso` along `DGCategory.compToK` returns the explicit
isomorphism it is a preimage of. -/
theorem map_homEvaluationDerivedIso_hom :
    ((Functor.whiskeringLeft (dgCategory A).Comp (dgCategory A).K
          (DerivedCategory (ModuleCat.{0} ℤ))).obj
        (DGCategory.compToK (dgCategory A))).map (homEvaluationDerivedIso A K).hom =
      ((Functor.isoWhiskerLeft (homEvaluationComplexFunctor A K)
            (DerivedCategory.quotientCompQhIso (ModuleCat.{0} ℤ)) ≪≫
          Functor.isoWhiskerRight (homEvaluationComparisonIso A K).symm DerivedCategory.Q) ≪≫
        ((DGCategory.homRepresentation (dgCategory A) K).forgetSquareIso).symm).hom :=
  Functor.map_preimage _ _

/-- **The inverse direction of the descent, characterised.** Restricting the inverse of
`CochainComplex.homEvaluationDerivedIso` along `DGCategory.compToK` returns the inverse of the
explicit isomorphism it is a preimage of. -/
theorem map_homEvaluationDerivedIso_inv :
    ((Functor.whiskeringLeft (dgCategory A).Comp (dgCategory A).K
          (DerivedCategory (ModuleCat.{0} ℤ))).obj
        (DGCategory.compToK (dgCategory A))).map (homEvaluationDerivedIso A K).inv =
      ((Functor.isoWhiskerLeft (homEvaluationComplexFunctor A K)
            (DerivedCategory.quotientCompQhIso (ModuleCat.{0} ℤ)) ≪≫
          Functor.isoWhiskerRight (homEvaluationComparisonIso A K).symm DerivedCategory.Q) ≪≫
        ((DGCategory.homRepresentation (dgCategory A) K).forgetSquareIso).symm).inv :=
  Functor.map_preimage _ _

/-- **The descent, computed on a complex.** At a complex `Y` the forward direction of
`CochainComplex.homEvaluationDerivedIso` is the composite of its three factors: the comparison of
the two localizations of complexes of `ℤ`-modules, the image under `DerivedCategory.Q` of the
unlocalized comparison of the two readings of `Hom^•(K, Y)`, and the identification of the
differential-graded-module side with the underlying complex of `Hom(K, -)`. -/
theorem homEvaluationDerivedIso_hom_app (Y : (dgCategory A).Comp) :
    (homEvaluationDerivedIso A K).hom.app ((DGCategory.compToK (dgCategory A)).obj Y) =
      (DerivedCategory.quotientCompQhIso (ModuleCat.{0} ℤ)).hom.app
          ((homEvaluationComplexFunctor A K).obj Y) ≫
        DerivedCategory.Q.map ((homEvaluationComparisonIso A K).inv.app Y) ≫
          ((DGCategory.homRepresentation (dgCategory A) K).forgetSquareIso).inv.app Y :=
  (NatTrans.congr_app (map_homEvaluationDerivedIso_hom A K) Y).trans (Category.assoc _ _ _)

/-- **The descent, computed on a complex, inversely.** The inverse of
`CochainComplex.homEvaluationDerivedIso` at a complex is the composite of the inverses of the three
factors, in the opposite order. -/
theorem homEvaluationDerivedIso_inv_app (Y : (dgCategory A).Comp) :
    (homEvaluationDerivedIso A K).inv.app ((DGCategory.compToK (dgCategory A)).obj Y) =
      ((DGCategory.homRepresentation (dgCategory A) K).forgetSquareIso).hom.app Y ≫
        DerivedCategory.Q.map ((homEvaluationComparisonIso A K).hom.app Y) ≫
          (DerivedCategory.quotientCompQhIso (ModuleCat.{0} ℤ)).inv.app
            ((homEvaluationComplexFunctor A K).obj Y) :=
  NatTrans.congr_app (map_homEvaluationDerivedIso_inv A K) Y

/-- **The middle factor of `ν`: reading `h_-` evaluated at `K` as `Hom_dg(K, -)`.** The second
factor of `CochainComplex.homDerivedLiftForgetIso`, the transport along the equality of functors
`DGCategory.homDGFunctor_onK`. -/
def homDerivedLiftForgetIsoMid :
    (yonedaHomotopyFunctor A ⋙ DGCategory.evaluationOnK (dgCategory A) K) ⋙
        (DGCategory.RightModule.cochainComplexOnK PUnit.unit ⋙ DerivedCategory.Qh) ≅
      (homotopyCategoryEquivalence A).functor ⋙
        ((DGCategory.homDGFunctor (dgCategory A) K).onK ⋙
          DGCategory.RightModule.cochainComplexOnK PUnit.unit ⋙ DerivedCategory.Qh) :=
  eqToIso (by rw [DGCategory.homDGFunctor_onK]; rfl)

/-- **The comparison `ν` of [Stacks, Tag 09LK], decomposed.** The inverse of
`CochainComplex.homDerivedLiftForgetIso` is the composite of the inverses of its three factors: the
descent `CochainComplex.homEvaluationDerivedIso`, the transport
`CochainComplex.homDerivedLiftForgetIsoMid`, and the identification of the derived evaluation with
evaluation on homotopy categories `DGCategory.RightModule.derivedEvaluationForgetCompIso`. -/
theorem homDerivedLiftForgetIso_inv :
    (homDerivedLiftForgetIso A K).inv =
      ((Functor.isoWhiskerLeft (homotopyCategoryEquivalence A).functor
              (homEvaluationDerivedIso A K)).inv ≫
            (homDerivedLiftForgetIsoMid A K).inv) ≫
        (Functor.isoWhiskerLeft
            (yonedaHomotopyFunctor A ⋙ DGCategory.evaluationOnK (dgCategory A) K)
            (DGCategory.RightModule.derivedEvaluationForgetCompIso
              (DGCategory.endDGCategory (dgCategory A) K) PUnit.unit)).inv :=
  rfl

end CochainComplex

end
