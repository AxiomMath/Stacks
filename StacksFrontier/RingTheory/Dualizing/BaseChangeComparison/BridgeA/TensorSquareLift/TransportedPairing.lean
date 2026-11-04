module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.BridgeA.TensorSquareLift.ScalarLift

/-!
# The transported pairing of a pushout square at four independent ring universes

The transport prefix and tail of the independent-universe projection formula, their transports
along a comparison with the lifted complex, and the projection formula at the two ring maps of a
pushout square, `Dualizing.derivedExtendRestrictScalarsTensorIso_square`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.MonoidalCategory
open StacksDraft.DerivedHom
open StacksDraft.DerivedExtensionScalarsModelComp

universe w u₁ u₂ v uR uA uS uT uSp uTp

namespace Dualizing

attribute [local instance] extendScalarsAdditiveOfRingHom

section Component

attribute [local instance] HasDerivedCategory.standard

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)

/-- **The transport prefix of the independent-universe projection formula.**  The first six
factors of `Dualizing.derivedExtendRestrictScalarsTensorIso_hom_app_q_obj`: the unit of the
scalar lift over `A`, the uniqueness `CategoryTheory.Adjunction.leftAdjointUniq` of the two
derived extensions of scalars across the lift,
`Stacks.DerivedHom.BaseChange.scalarRestrictionIso`, the universe-lift comparison at `K`, and the
comparison morphism of the lifted model at the lifted complex.  Every factor is invertible when
`K` is K-flat, but none of that is needed here.

Isolated as a definition because the statement of
`Dualizing.derivedExtendRestrictScalarsTensorIso_square` mentions it, and the cluster of
`let`-bound adjunctions it is built from — two composites of adjunctions and one
`CategoryTheory.Adjunction.leftAdjointUniq` — costs more heartbeats to elaborate than a single
declaration is allowed. -/
def liftTransportPrefix (f : R →+* A)
    (F : DerivedCategory (ModuleCat.{max v uR uA} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} R) (ComplexShape.up ℤ))]
    (K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ) :=
  let E := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, max v uR uA} R
  let S := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uA, max v uR uA} A
  let f' : ULift.{max v uR uA} R →+* ULift.{max v uR uA} A :=
    (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
  let U := (ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory
  let V := (ModuleCat.restrictScalars.{max v uR uA} f').mapDerivedCategory
  let δ : S.inverse ⋙ U ≅ V ⋙ E.inverse :=
    Stacks.DerivedHom.BaseChange.scalarRestrictionIso.{uR, uA, v} f
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings.{max v uR uA,
    max v uR uA, max v uR uA} f'
      (HomologicalComplex.zero :
        CochainComplex (ModuleCat.{max v uR uA} (ULift.{max v uR uA} A)) ℤ)
  let a := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uA, v}
    f F comparison
  let a' := @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{
    max v uR uA, max v uR uA, max v uR uA} _ _ _ _ f' _ _ T.B T.alphaB T.isLeftDerivedB
  let eF : E.functor ⋙ T.B ≅ F ⋙ S.functor :=
    (E.toAdjunction.comp a').leftAdjointUniq ((a.comp S.toAdjunction).ofNatIsoRight δ)
  let Kt := ((ModuleCat.restrictScalars
      (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K
  let ψ : E.functor.obj (DerivedCategory.Q.obj K) ≅ DerivedCategory.Q.obj Kt :=
    (ModuleCat.restrictScalars
      (ULift.ringEquiv : ULift.{max v uR uA} R ≃+*
        R).toRingHom).mapDerivedCategoryFactors.app K
  (Functor.leftUnitor U).inv.app (F.obj (DerivedCategory.Q.obj K)) ≫
    U.map (S.unitIso.hom.app (F.obj (DerivedCategory.Q.obj K))) ≫
      U.map (S.inverse.map (eF.inv.app (DerivedCategory.Q.obj K))) ≫
        δ.hom.app (T.B.obj (E.functor.obj (DerivedCategory.Q.obj K))) ≫
          E.inverse.map ((T.B ⋙ V).map ψ.hom) ≫
            E.inverse.map (V.map (T.alphaB.app Kt))

/-- **The factor between the transport prefix and the chain-level projection formula.**  Derived
restriction of scalars along the lifted ring map, read through its own
`CategoryTheory.Functor.mapDerivedCategoryFactors` at the extension of scalars of the lifted
complex, and carried back along the scalar lift over `R`.  It is the seventh factor of
`Dualizing.derivedExtendRestrictScalarsTensorIso_hom_app_q_obj`, the one that follows
`Dualizing.liftTransportPrefix`.

Isolated as a definition for the reason the prefix itself is: writing it out reconciles
`CochainComplex.extendScalarsLarge` at the lifted map with the degreewise extension of scalars
the lift is spelled with, and a statement that does so while also naming the four comparisons of
a square exceeds the per-declaration heartbeat budget. -/
def liftTransportFactors (f : R →+* A) (L : CochainComplex (ModuleCat.{max v uR uA} R) ℤ) :=
  let E := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, max v uR uA} R
  let f' : ULift.{max v uR uA} R →+* ULift.{max v uR uA} A :=
    (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
  let Lt := ((ModuleCat.restrictScalars
      (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj L
  E.inverse.map
    ((ModuleCat.restrictScalars.{max v uR uA} f').mapDerivedCategoryFactors.app
      ((CochainComplex.extendScalarsLarge f').obj Lt)).hom

/-- The scalar lift read on the coefficient object of the tensor bifunctor:
`CategoryTheory.Functor.flipObjConjugate` at the universe-lift equivalence over `R` and at the
algebra. -/
def liftFlipConjugate (f : R →+* A) :=
  Functor.flipObjConjugate
    (uliftDerivedEquivalence.{uR, max v uR uA, max v uR uA, max v uR uA + 1,
      max v uR uA + 1} R)
    (DerivedInternalHom.Model.tensor (ULift.{max v uR uA} R))
    (derivedAlgebraSingle.{uR, uA, v} f)

/-- The coefficient transport of the scalar lift: the symmetry of the derived tensor product
over the lifted ring, `CategoryTheory.Functor.curryObjSwapFlip`, and
`Dualizing.derivedAlgebraSingleLiftIso`. -/
def liftCoeffIso (f : R →+* A) :=
  let f' : ULift.{max v uR uA} R →+* ULift.{max v uR uA} A :=
    (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
  let Bd := (DerivedCategory.singleFunctor
    (ModuleCat.{max v uR uA} (ULift.{max v uR uA} R)) 0).obj
    ((ModuleCat.restrictScalars f').obj
      (ModuleCat.of (ULift.{max v uR uA} A) (ULift.{max v uR uA} A)))
  (Functor.curry.mapIso
      (DerivedInternalHom.Model.adjunction
        (ULift.{max v uR uA} R)).toDerivedHomAdjunction.tensorSymmetry).app Bd ≪≫
    Functor.curryObjSwapFlip _ _ ≪≫
    ((Functor.curry.obj
      (DerivedInternalHom.Model.tensor
        (ULift.{max v uR uA} R))).flip.mapIso
      (derivedAlgebraSingleLiftIso.{uR, uA, max v uA} f)).symm

/-- The universe-lift comparison at `K`, tensored into the lifted algebra. -/
def liftTensorPsi (f : R →+* A) (K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ) :=
  let f' : ULift.{max v uR uA} R →+* ULift.{max v uR uA} A :=
    (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
  let Bd := (DerivedCategory.singleFunctor
    (ModuleCat.{max v uR uA} (ULift.{max v uR uA} R)) 0).obj
    ((ModuleCat.restrictScalars f').obj
      (ModuleCat.of (ULift.{max v uR uA} A) (ULift.{max v uR uA} A)))
  Functor.mapIso ((Functor.curry.obj
      (DerivedInternalHom.Model.tensor (ULift.{max v uR uA} R))).obj Bd)
    ((ModuleCat.restrictScalars
      (ULift.ringEquiv : ULift.{max v uR uA} R ≃+*
        R).toRingHom).mapDerivedCategoryFactors.app K)

/-- The tensor comparison of the K-flat model over the lifted ring, at the lifted algebra and the
lifted complex, which is invertible because the lift of a K-flat complex is K-flat
(`Dualizing.kFlat_restrictScalars_uliftRingEquiv`). -/
def liftKFlatTensorIso (f : R →+* A) (K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ)
    (hK : CochainComplex.KFlat.{uR, max v uA} K) :
    let f' : ULift.{max v uR uA} R →+* ULift.{max v uR uA} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    let Bc := (CochainComplex.singleFunctor
      (ModuleCat.{max v uR uA} (ULift.{max v uR uA} R)) 0).obj
      ((ModuleCat.restrictScalars f').obj
        (ModuleCat.of (ULift.{max v uR uA} A) (ULift.{max v uR uA} A)))
    let Kt := ((ModuleCat.restrictScalars
        (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K
    (DerivedInternalHom.Model.adjunction (ULift.{max v uR uA} R)).tensor.obj
        (DerivedCategory.Q.obj Bc, DerivedCategory.Q.obj Kt) ≅
      DerivedCategory.Q.obj ((MonoidalCategory.tensorLeft Bc).obj Kt) :=
  let f' : ULift.{max v uR uA} R →+* ULift.{max v uR uA} A :=
    (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
  let Bc := (CochainComplex.singleFunctor
    (ModuleCat.{max v uR uA} (ULift.{max v uR uA} R)) 0).obj
    ((ModuleCat.restrictScalars f').obj
      (ModuleCat.of (ULift.{max v uR uA} A) (ULift.{max v uR uA} A)))
  let Kt := ((ModuleCat.restrictScalars
      (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K
  (DerivedInternalHom.Model.adjunction (ULift.{max v uR uA} R)).tensorIso Bc Kt
    (kFlat_restrictScalars_uliftRingEquiv.{uR, max v uA} K hK)

/-- **The transport tail of the independent-universe projection formula.**  The four isomorphisms
of `Dualizing.liftFlipConjugate`, `Dualizing.liftCoeffIso`, `Dualizing.liftTensorPsi` and
`Dualizing.liftKFlatTensorIso` composed in the direction that retracts the tail of
`Dualizing.derivedExtendRestrictScalarsTensorIso_hom_app_q_obj`. -/
def liftTransportTail (f : R →+* A) (K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ)
    (hK : CochainComplex.KFlat.{uR, max v uA} K) :=
  let E := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, max v uR uA} R
  (liftFlipConjugate.{v, uR, uA} f).hom.app (DerivedCategory.Q.obj K) ≫
    E.inverse.map ((liftCoeffIso.{v, uR, uA} f).inv.app
      (E.functor.obj (DerivedCategory.Q.obj K))) ≫
    E.inverse.map (liftTensorPsi.{v, uR, uA} f K).hom ≫
    E.inverse.map (liftKFlatTensorIso.{v, uR, uA} f K hK).hom

/-- The universe-lift comparison between a complex over the lifted ring and the lift of a complex
over the ring, tensored into the lifted algebra.  At the square it is
`Dualizing.uliftExtendScalarsCommUpComplex`, comparing the lifted extension of scalars along the
lifted left edge with the lift of the extension of scalars along the left edge. -/
def liftSquareTensorTransport (f : R →+* A)
    (L : CochainComplex (ModuleCat.{max v uR uA} R) ℤ)
    (X : CochainComplex (ModuleCat.{max v uR uA} (ULift.{max v uR uA} R)) ℤ)
    (θ : X ≅ ((ModuleCat.restrictScalars
        (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L) :=
  let E := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, max v uR uA} R
  let f' : ULift.{max v uR uA} R →+* ULift.{max v uR uA} A :=
    (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
  let Bc := (CochainComplex.singleFunctor
    (ModuleCat.{max v uR uA} (ULift.{max v uR uA} R)) 0).obj
    ((ModuleCat.restrictScalars f').obj
      (ModuleCat.of (ULift.{max v uR uA} A) (ULift.{max v uR uA} A)))
  Functor.mapIso (DerivedCategory.Q ⋙ E.inverse)
    (Functor.mapIso (MonoidalCategory.tensorLeft Bc) θ)

/-- **The retraction of the transport prefix at the far edge of the square.**  By
`Dualizing.derivedExtendRestrictScalarsTensorIso_hom_app_q_obj_chainPairing` the transport prefix
at `f` is the chain-level projection formula read against the projection formula and the
transport tail, all three of which are invertible at a K-flat complex; so the prefix itself need
never be written down on the side of the square at which only its retraction occurs.  This is
that retraction, carried along the comparison `θ` onto the complex the chain-level pairing of the
square reads the formula at. -/
def liftSquareRetraction (f : R →+* A)
    (F : DerivedCategory (ModuleCat.{max v uR uA} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} R) (ComplexShape.up ℤ))]
    (L : CochainComplex (ModuleCat.{max v uR uA} R) ℤ)
    (hL : CochainComplex.KFlat.{uR, max v uA} L)
    (X : CochainComplex (ModuleCat.{max v uR uA} (ULift.{max v uR uA} R)) ℤ)
    (θ : X ≅ ((ModuleCat.restrictScalars
        (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L) :=
  let E := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, max v uR uA} R
  let f' : ULift.{max v uR uA} R →+* ULift.{max v uR uA} A :=
    (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
  (DerivedCategory.Q ⋙ E.inverse).map
      ((extendRestrictScalarsComplexIso f').hom.app X) ≫
    ((liftSquareTensorTransport.{v, uR, uA} f L X θ).hom ≫
      (E.inverse.map (liftKFlatTensorIso.{v, uR, uA} f L hL).inv ≫
        E.inverse.map (liftTensorPsi.{v, uR, uA} f L).inv ≫
        E.inverse.map ((liftCoeffIso.{v, uR, uA} f).hom.app
          (E.functor.obj (DerivedCategory.Q.obj L))) ≫
        (liftFlipConjugate.{v, uR, uA} f).inv.app (DerivedCategory.Q.obj L))) ≫
    (derivedExtendRestrictScalarsTensorIso.{uR, uA, v} f F comparison).inv.app
      (DerivedCategory.Q.obj L)

/-- The transport tail at the far edge of the square, carried along `θ`: the tail
`Dualizing.liftTransportTail` followed by the inverse of
`Dualizing.liftSquareTensorTransport`. -/
def liftSquareTailTransported (f : R →+* A)
    (L : CochainComplex (ModuleCat.{max v uR uA} R) ℤ)
    (hL : CochainComplex.KFlat.{uR, max v uA} L)
    (X : CochainComplex (ModuleCat.{max v uR uA} (ULift.{max v uR uA} R)) ℤ)
    (θ : X ≅ ((ModuleCat.restrictScalars
        (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L) :=
  liftTransportTail.{v, uR, uA} f L hL ≫ (liftSquareTensorTransport.{v, uR, uA} f L X θ).inv

/-- **The independent-universe projection formula, read as a chain-level pairing at the lifted
ring map.**  `Dualizing.derivedExtendRestrictScalarsTensorIso_hom_app_q_obj` presents the
component of the independent-universe projection formula at the class of a K-flat complex `K` as
a seven-factor composite through the two scalar-lift equivalences, whose one non-transport factor
is `DerivedCategory.Q` of the *equal-universe* chain-level projection formula
`Dualizing.extendRestrictScalarsComplexIso` at the lifted ring map `f'` and the lifted complex
`Kt`.  Four of those factors are isomorphisms: the tensor comparison of the K-flat model at `Kt`,
the tensor bifunctor applied to the universe-lift comparison `ψ`, the coefficient transport built
from `tensorSymmetry`, `CategoryTheory.Functor.curryObjSwapFlip` and
`Dualizing.derivedAlgebraSingleLiftIso`, and `CategoryTheory.Functor.flipObjConjugate`.  This
reads the component against the inverse of that four-factor tail, so that the equation becomes

`pf.hom.app (Q K) ≫ tail⁻¹ = (transport prefix) ≫ (Q ⋙ E.inverse).map (κ_{f'}.hom.app Kt)`,

which is exactly the second hypothesis of
`Stacks.CategoryTheory.comp_eq_of_chain_pairing` with `Q ⋙ E.inverse` for its localization
functor: the chain-level object is a complex over the **lifted** ring, where
`Dualizing.extendRestrictScalarsComplexIso_square` is available, while the derived morphism is
the independent-universe projection formula at the universes the keystone's assembly reads it
at.

Every transport isomorphism of the lift occurs: `scalarEquivalence` over `R` and over `A`,
`Stacks.DerivedHom.BaseChange.scalarRestrictionIso`, the uniqueness
`CategoryTheory.Adjunction.leftAdjointUniq` of the two derived extensions of scalars across the
lift, `Dualizing.derivedAlgebraSingleLiftIso`, the symmetry of the derived tensor product and
`CategoryTheory.Functor.flipObjConjugate`.  The first four are in the prefix and the last three
in the tail. -/
theorem derivedExtendRestrictScalarsTensorIso_hom_app_q_obj_chainPairing
    (F : DerivedCategory (ModuleCat.{max v uR uA} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} R) (ComplexShape.up ℤ))]
    (K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ)
    (hK : CochainComplex.KFlat.{uR, max v uA} K) :
    let E := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, max v uR uA} R
    let f' : ULift.{max v uR uA} R →+* ULift.{max v uR uA} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    let i := derivedAlgebraSingleLiftIso.{uR, uA, max v uA} f
    let Bc := (CochainComplex.singleFunctor
      (ModuleCat.{max v uR uA} (ULift.{max v uR uA} R)) 0).obj
      ((ModuleCat.restrictScalars f').obj
        (ModuleCat.of (ULift.{max v uR uA} A) (ULift.{max v uR uA} A)))
    let Bd := (DerivedCategory.singleFunctor
      (ModuleCat.{max v uR uA} (ULift.{max v uR uA} R)) 0).obj
      ((ModuleCat.restrictScalars f').obj
        (ModuleCat.of (ULift.{max v uR uA} A) (ULift.{max v uR uA} A)))
    let Kt := ((ModuleCat.restrictScalars
        (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K
    let ψ : E.functor.obj (DerivedCategory.Q.obj K) ≅ DerivedCategory.Q.obj Kt :=
      (ModuleCat.restrictScalars
        (ULift.ringEquiv : ULift.{max v uR uA} R ≃+*
          R).toRingHom).mapDerivedCategoryFactors.app K
    (derivedExtendRestrictScalarsTensorIso.{uR, uA, v} f F comparison).hom.app
            (DerivedCategory.Q.obj K) ≫
          ((Functor.flipObjConjugate
              (uliftDerivedEquivalence.{uR, max v uR uA, max v uR uA, max v uR uA + 1,
                max v uR uA + 1} R)
              (DerivedInternalHom.Model.tensor (ULift.{max v uR uA} R))
              (derivedAlgebraSingle.{uR, uA, v} f)).hom.app (DerivedCategory.Q.obj K) ≫
            E.inverse.map
              (((Functor.curry.mapIso
                  (DerivedInternalHom.Model.adjunction
                    (ULift.{max v uR uA} R)).toDerivedHomAdjunction.tensorSymmetry).app Bd ≪≫
                Functor.curryObjSwapFlip _ _ ≪≫
                ((Functor.curry.obj
                  (DerivedInternalHom.Model.tensor
                    (ULift.{max v uR uA} R))).flip.mapIso i).symm).inv.app
                  (E.functor.obj (DerivedCategory.Q.obj K))) ≫
            E.inverse.map
              (((Functor.curry.obj (DerivedInternalHom.Model.tensor
                (ULift.{max v uR uA} R))).obj Bd).map ψ.hom) ≫
            E.inverse.map ((DerivedInternalHom.Model.adjunction
              (ULift.{max v uR uA} R)).tensorIso Bc Kt
                (kFlat_restrictScalars_uliftRingEquiv.{uR, max v uA} K hK)).hom) =
      liftTransportPrefix.{v, uR, uA} f F comparison K ≫
        E.inverse.map
            ((ModuleCat.restrictScalars.{max v uR uA} f').mapDerivedCategoryFactors.app
              ((CochainComplex.extendScalarsLarge f').obj Kt)).hom ≫
          E.inverse.map
            (DerivedCategory.Q.map ((extendRestrictScalarsComplexIso f').hom.app Kt)) := by
  intro E f' i Bc Bd Kt ψ
  exact Stacks.CategoryTheory.comp_cancel_last_through
    E.inverse _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (derivedExtendRestrictScalarsTensorIso_hom_app_q_obj.{uR, uA, v} f F comparison K hK)
    (Stacks.CategoryTheory.comp_retraction_four E.inverse _ _ _ _ _ _ _ _
      (Iso.inv_hom_id _)
      (Functor.mapIso ((Functor.curry.obj (DerivedInternalHom.Model.tensor
        (ULift.{max v uR uA} R))).obj Bd) ψ).inv_hom_id
      (Iso.hom_inv_id_app _ _) (Iso.inv_hom_id_app _ _))

/-- The prefix of `Dualizing.derivedExtendRestrictScalarsTensorIso_hom_app_q_obj_chainPairing`
carried along the comparison `θ` onto the complex the chain-level pairing of a square reads the
projection formula at. -/
def liftSquarePrefixTransported (f : R →+* A)
    (F : DerivedCategory (ModuleCat.{max v uR uA} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} R) (ComplexShape.up ℤ))]
    (L : CochainComplex (ModuleCat.{max v uR uA} R) ℤ)
    (X : CochainComplex (ModuleCat.{max v uR uA} (ULift.{max v uR uA} R)) ℤ)
    (θ : X ≅ ((ModuleCat.restrictScalars
        (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L) :=
  let E := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, max v uR uA} R
  let f' : ULift.{max v uR uA} R →+* ULift.{max v uR uA} A :=
    (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
  let Lt := ((ModuleCat.restrictScalars
      (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj L
  (liftTransportPrefix.{v, uR, uA} f F comparison L ≫
      E.inverse.map
        ((ModuleCat.restrictScalars.{max v uR uA} f').mapDerivedCategoryFactors.app
          ((CochainComplex.extendScalarsLarge f').obj Lt)).hom) ≫
    (DerivedCategory.Q ⋙ E.inverse).map
      ((CochainComplex.extendScalarsLarge f' ⋙
        CochainComplex.restrictScalarsLarge f').map θ.inv)

/-- **The transport tail is a retraction.**  Each of the four factors of
`Dualizing.liftTransportTail` is invertible at a K-flat complex, so the reversed composite of
their inverses retracts it.

Recorded as a declaration of its own rather than inlined where it is used: the four factors are
`Dualizing.liftKFlatTensorIso`, `Dualizing.liftTensorPsi`, `Dualizing.liftCoeffIso` and
`Dualizing.liftFlipConjugate`, whose types mention the two scalar-lift equivalences, and the
heartbeat budget is per declaration. -/
theorem liftTransportTail_retraction (f : R →+* A)
    (L : CochainComplex (ModuleCat.{max v uR uA} R) ℤ)
    (hL : CochainComplex.KFlat.{uR, max v uA} L) :
    let E := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, max v uR uA} R
    (E.inverse.map (liftKFlatTensorIso.{v, uR, uA} f L hL).inv ≫
          E.inverse.map (liftTensorPsi.{v, uR, uA} f L).inv ≫
          E.inverse.map ((liftCoeffIso.{v, uR, uA} f).hom.app
            (E.functor.obj (DerivedCategory.Q.obj L))) ≫
          (liftFlipConjugate.{v, uR, uA} f).inv.app (DerivedCategory.Q.obj L)) ≫
        liftTransportTail.{v, uR, uA} f L hL = 𝟙 _ := by
  intro E
  exact Stacks.CategoryTheory.inv_comp_four _ _ _ _ _ _ _ _
    (Iso.inv_hom_id_app _ _)
    (Stacks.CategoryTheory.map_comp_eq_id _ _ _ (Iso.hom_inv_id_app _ _))
    (Stacks.CategoryTheory.map_comp_eq_id _ _ _ (Iso.inv_hom_id _))
    (Stacks.CategoryTheory.map_comp_eq_id _ _ _ (Iso.inv_hom_id _))

/-- **The transported transport tail is a retraction.**
`Dualizing.liftTransportTail_retraction` carried along the comparison `θ`, which is the shape in
which the tail at the far edge of a square is cancelled. -/
theorem liftSquareTailTransported_retraction (f : R →+* A)
    (L : CochainComplex (ModuleCat.{max v uR uA} R) ℤ)
    (hL : CochainComplex.KFlat.{uR, max v uA} L)
    (X : CochainComplex (ModuleCat.{max v uR uA} (ULift.{max v uR uA} R)) ℤ)
    (θ : X ≅ ((ModuleCat.restrictScalars
        (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L) :
    let E := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, max v uR uA} R
    ((liftSquareTensorTransport.{v, uR, uA} f L X θ).hom ≫
          (E.inverse.map (liftKFlatTensorIso.{v, uR, uA} f L hL).inv ≫
            E.inverse.map (liftTensorPsi.{v, uR, uA} f L).inv ≫
            E.inverse.map ((liftCoeffIso.{v, uR, uA} f).hom.app
              (E.functor.obj (DerivedCategory.Q.obj L))) ≫
            (liftFlipConjugate.{v, uR, uA} f).inv.app (DerivedCategory.Q.obj L))) ≫
        liftSquareTailTransported.{v, uR, uA} f L hL X θ = 𝟙 _ := by
  intro E
  exact Stacks.CategoryTheory.comp_retraction_pair _ _ _ _
    (liftTransportTail_retraction.{v, uR, uA} f L hL) (Iso.hom_inv_id _)

/-- **The transported prefix of the independent-universe projection formula, read against the
chain-level formula.**
`Dualizing.derivedExtendRestrictScalarsTensorIso_hom_app_q_obj_chainPairing` carried along the
comparison `θ` by `Stacks.CategoryTheory.comp_eq_of_transport`: the transported prefix, followed
by the equal-universe chain-level projection formula at `X` rather than at the lift of `L`, is the
component of the independent-universe projection formula followed by the transported tail. -/
theorem liftSquarePrefixTransported_comp (f : R →+* A)
    (F : DerivedCategory (ModuleCat.{max v uR uA} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} R) (ComplexShape.up ℤ))]
    (L : CochainComplex (ModuleCat.{max v uR uA} R) ℤ)
    (hL : CochainComplex.KFlat.{uR, max v uA} L)
    (X : CochainComplex (ModuleCat.{max v uR uA} (ULift.{max v uR uA} R)) ℤ)
    (θ : X ≅ ((ModuleCat.restrictScalars
        (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L) :
    let E := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, max v uR uA} R
    let f' : ULift.{max v uR uA} R →+* ULift.{max v uR uA} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    liftSquarePrefixTransported.{v, uR, uA} f F comparison L X θ ≫
        (DerivedCategory.Q ⋙ E.inverse).map
          ((extendRestrictScalarsComplexIso f').hom.app X) =
      (derivedExtendRestrictScalarsTensorIso.{uR, uA, v} f F comparison).hom.app
          (DerivedCategory.Q.obj L) ≫
        liftSquareTailTransported.{v, uR, uA} f L hL X θ := by
  intro E f'
  exact Stacks.CategoryTheory.comp_eq_of_transport _ _ _ _ _ _ _
    ((Category.assoc _ _ _).trans
      (derivedExtendRestrictScalarsTensorIso_hom_app_q_obj_chainPairing.{v, uR, uA}
        f F comparison L hL).symm)
    (Stacks.CategoryTheory.map_comp_square (DerivedCategory.Q ⋙ E.inverse) _ _ _ _
      ((extendRestrictScalarsComplexIso f').hom.naturality θ.inv))

/-- **The retraction of the transport prefix, verified.**
`Dualizing.liftSquareRetraction` is a retraction of `Dualizing.liftSquarePrefixTransported`: by
`Dualizing.liftSquarePrefixTransported_comp` the prefix factors as an invertible composite, and
`Stacks.CategoryTheory.retraction_of_comp_eq` reads the retraction off that factorization.

This is the fourth hypothesis of `Stacks.CategoryTheory.comp_eq_of_chain_pairing` at the far edge
of a square, and it is what lets the seven-factor transport prefix stay out of the statement of
the transported pairing.

Every morphism is left to unification: writing the chain-level projection formula at the lifted
ring map out a second time, to name the inverse the retraction is read against, elaborates the
lifted ring map twice, and reconciling the two costs more heartbeats than a declaration is
allowed. -/
theorem liftSquareRetraction_comp (f : R →+* A)
    (F : DerivedCategory (ModuleCat.{max v uR uA} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} R) (ComplexShape.up ℤ))]
    (L : CochainComplex (ModuleCat.{max v uR uA} R) ℤ)
    (hL : CochainComplex.KFlat.{uR, max v uA} L)
    (X : CochainComplex (ModuleCat.{max v uR uA} (ULift.{max v uR uA} R)) ℤ)
    (θ : X ≅ ((ModuleCat.restrictScalars
        (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L) :
    liftSquareRetraction.{v, uR, uA} f F comparison L hL X θ ≫
        liftSquarePrefixTransported.{v, uR, uA} f F comparison L X θ = 𝟙 _ :=
  Stacks.CategoryTheory.retraction_of_comp_eq _ _ _ _ _ _ _
    (liftSquarePrefixTransported_comp.{v, uR, uA} f F comparison L hL X θ)
    (Stacks.CategoryTheory.map_comp_eq_id _ _ _ (Iso.hom_inv_id_app _ _))
    (Iso.inv_hom_id_app _ _)
    (liftSquareTailTransported_retraction.{v, uR, uA} f L hL X θ)

end Component

section Square

attribute [local instance] HasDerivedCategory.standard

variable {S : Type uS} {T : Type uT} {S' : Type uSp} {T' : Type uTp}
  [CommRing S] [CommRing T] [CommRing S'] [CommRing T']

/-- **The far edge of the lifted square, followed by the two comparisons after it.**  The
retraction `Dualizing.liftSquareRetraction` of the transport prefix at `h`, the component of the
independent-universe projection formula at the class of `S' ⊗_S K`, the transported transport
tail, the lifted algebra in the tensor factor, and the monoidality of degreewise extension of
scalars along the lifted left edge: the last five factors of the right-hand side of
`Dualizing.derivedExtendRestrictScalarsTensorIso_square`.

Isolated as a definition, and nested inside `Dualizing.liftSquareConjugate` rather than written
there, because the per-declaration heartbeat budget does not hold the whole conjugation at once.
The composite is right-associated throughout and is the last factor of the definition that
mentions it, so the nesting does not regroup it: the conjugation stays definitionally the tail of
the composite `Stacks.CategoryTheory.comp_eq_of_chain_pairing` produces. -/
def liftSquareConjugateTail
    (g : S →+* T) (p : S →+* S') (w : T →+* T') (h : S' →+* T')
    (comm : w.comp g = h.comp p) (hp : MilnorPatching.IsPushoutSquare g p w h comm)
    (H : DerivedCategory (ModuleCat.{max v uS uT uSp uTp} S') ⥤
      DerivedCategory (ModuleCat.{max v uS uT uSp uTp} T'))
    (betaH : DerivedCategory.Q ⋙ H ⟶
      (ModuleCat.extendScalars.{uSp, uTp, max v uS uT uSp uTp} h).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [H.IsLeftDerivedFunctor betaH
      (HomologicalComplex.quasiIso (ModuleCat.{max v uS uT uSp uTp} S') (ComplexShape.up ℤ))]
    (K : CochainComplex (ModuleCat.{max v uS uT uSp uTp} S) ℤ)
    (hKp : CochainComplex.KFlat.{uSp, max v uS uT uTp}
      (((ModuleCat.extendScalars.{uS, uSp, max v uS uT uSp uTp} p).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K)) :=
  let ESp := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uSp,
    max v uS uT uSp uTp} S'
  let g' : ULift.{max v uS uT uSp uTp} S →+* ULift.{max v uS uT uSp uTp} T :=
    (ULift.ringEquiv.symm.toRingHom.comp g).comp ULift.ringEquiv.toRingHom
  let p' : ULift.{max v uS uT uSp uTp} S →+* ULift.{max v uS uT uSp uTp} S' :=
    (ULift.ringEquiv.symm.toRingHom.comp p).comp ULift.ringEquiv.toRingHom
  let w' : ULift.{max v uS uT uSp uTp} T →+* ULift.{max v uS uT uSp uTp} T' :=
    (ULift.ringEquiv.symm.toRingHom.comp w).comp ULift.ringEquiv.toRingHom
  let h' : ULift.{max v uS uT uSp uTp} S' →+* ULift.{max v uS uT uSp uTp} T' :=
    (ULift.ringEquiv.symm.toRingHom.comp h).comp ULift.ringEquiv.toRingHom
  let comm' := uliftSquareComm.{v, uS, uT, uSp, uTp} g p w h comm
  let hp' := uliftIsPushoutSquare.{v, uS, uT, uSp, uTp} g p w h comm hp comm'
  let Kt := ((ModuleCat.restrictScalars
      (ULift.ringEquiv : ULift.{max v uS uT uSp uTp} S ≃+* S).toRingHom).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K
  let Ep' := (ModuleCat.extendScalars.{max v uS uT uSp uTp, max v uS uT uSp uTp,
    max v uS uT uSp uTp} p').mapHomologicalComplex (ComplexShape.up ℤ)
  let L := ((ModuleCat.extendScalars.{uS, uSp, max v uS uT uSp uTp} p).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K
  let Bcg := (CochainComplex.singleFunctor
      (ModuleCat.{max v uS uT uSp uTp} (ULift.{max v uS uT uSp uTp} S)) 0).obj
    ((ModuleCat.restrictScalars g').obj
      (ModuleCat.of (ULift.{max v uS uT uSp uTp} T) (ULift.{max v uS uT uSp uTp} T)))
  let X := Ep'.obj Kt
  let θ := uliftExtendScalarsCommUpApp.{max v uT uTp, uS, uSp} p K
  liftSquareRetraction.{max v uS uT, uSp, uTp} h H betaH L hKp X θ ≫
    (derivedExtendRestrictScalarsTensorIso.{uSp, uTp, max v uS uT} h H betaH).hom.app
        (DerivedCategory.Q.obj L) ≫
      liftSquareTailTransported.{max v uS uT, uSp, uTp} h L hKp X θ ≫
        (DerivedCategory.Q ⋙ ESp.inverse).map
          ((pushoutAlgebraIsoComplex g' p' w' h' comm' hp').inv ▷ X) ≫
          (DerivedCategory.Q ⋙ ESp.inverse).map
            (CochainComplex.ExtendScalars.extendScalarsMonoidalIso p' Bcg Kt).hom

/-- **The projection formula at `h`, conjugated by the four comparisons of the lifted square.**
The pushout comparison of the lifted square, the identification of its two extensions of scalars
along the diagonal, and then `Dualizing.liftSquareConjugateTail`: the whole right-hand side of
`Dualizing.derivedExtendRestrictScalarsTensorIso_square` after the base-changed transport prefix.

This is `Dualizing.derivedExtendRestrictScalarsTensorIsoEqualUniverse_square`'s conjugating
composite, read at the lifted square and carried back along the scalar lift over `S'`. -/
def liftSquareConjugate
    (g : S →+* T) (p : S →+* S') (w : T →+* T') (h : S' →+* T')
    (comm : w.comp g = h.comp p) (hp : MilnorPatching.IsPushoutSquare g p w h comm)
    (H : DerivedCategory (ModuleCat.{max v uS uT uSp uTp} S') ⥤
      DerivedCategory (ModuleCat.{max v uS uT uSp uTp} T'))
    (betaH : DerivedCategory.Q ⋙ H ⟶
      (ModuleCat.extendScalars.{uSp, uTp, max v uS uT uSp uTp} h).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [H.IsLeftDerivedFunctor betaH
      (HomologicalComplex.quasiIso (ModuleCat.{max v uS uT uSp uTp} S') (ComplexShape.up ℤ))]
    (K : CochainComplex (ModuleCat.{max v uS uT uSp uTp} S) ℤ)
    (hKp : CochainComplex.KFlat.{uSp, max v uS uT uTp}
      (((ModuleCat.extendScalars.{uS, uSp, max v uS uT uSp uTp} p).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K)) :=
  let ESp := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uSp,
    max v uS uT uSp uTp} S'
  let g' : ULift.{max v uS uT uSp uTp} S →+* ULift.{max v uS uT uSp uTp} T :=
    (ULift.ringEquiv.symm.toRingHom.comp g).comp ULift.ringEquiv.toRingHom
  let p' : ULift.{max v uS uT uSp uTp} S →+* ULift.{max v uS uT uSp uTp} S' :=
    (ULift.ringEquiv.symm.toRingHom.comp p).comp ULift.ringEquiv.toRingHom
  let w' : ULift.{max v uS uT uSp uTp} T →+* ULift.{max v uS uT uSp uTp} T' :=
    (ULift.ringEquiv.symm.toRingHom.comp w).comp ULift.ringEquiv.toRingHom
  let h' : ULift.{max v uS uT uSp uTp} S' →+* ULift.{max v uS uT uSp uTp} T' :=
    (ULift.ringEquiv.symm.toRingHom.comp h).comp ULift.ringEquiv.toRingHom
  let comm' := uliftSquareComm.{v, uS, uT, uSp, uTp} g p w h comm
  let hp' := uliftIsPushoutSquare.{v, uS, uT, uSp, uTp} g p w h comm hp comm'
  let Kt := ((ModuleCat.restrictScalars
      (ULift.ringEquiv : ULift.{max v uS uT uSp uTp} S ≃+* S).toRingHom).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K
  (DerivedCategory.Q ⋙ ESp.inverse).map
      ((pushoutBaseChangeComplex g' p' w' h' comm' hp').inv.app
        (((ModuleCat.extendScalars.{max v uS uT uSp uTp, max v uS uT uSp uTp,
          max v uS uT uSp uTp} g').mapHomologicalComplex (ComplexShape.up ℤ)).obj Kt)) ≫
    (DerivedCategory.Q ⋙ ESp.inverse).map
        (((ModuleCat.restrictScalars.{max v uS uT uSp uTp} h').mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          ((extendScalarsSquareIsoComplex g' p' w' h' comm').inv.app Kt)) ≫
      liftSquareConjugateTail.{v, uS, uT, uSp, uTp} g p w h comm hp H betaH K hKp

/-- **The right-hand side of the transported pairing.**  The transport prefix of the
independent-universe projection formula at `g`, the factor
`Dualizing.liftTransportFactors` after it, both base changed along `p`, the comparison morphism
`Dualizing.liftedBaseChangeComparison` of the model `Bp` at the chain-level source of the
projection formula at the lifted edge, and then the conjugated formula at `h`,
`Dualizing.liftSquareConjugate`.

Isolated as a definition because the junction at its last factor — the source of the lifted
square's pushout comparison against the extension along `p'` of the composite of the two functors
of the projection formula at `g'` — is definitional and not syntactic, and crossing it inside the
statement of `Dualizing.derivedExtendRestrictScalarsTensorIso_square` exceeds the
per-declaration heartbeat budget.  The composite is right-associated throughout, so unfolding
this definition and the two nested inside it gives exactly the composite
`Stacks.CategoryTheory.comp_eq_of_chain_pairing` produces. -/
def liftSquareConjugatedFormula
    (g : S →+* T) (p : S →+* S') (w : T →+* T') (h : S' →+* T')
    (comm : w.comp g = h.comp p) (hp : MilnorPatching.IsPushoutSquare g p w h comm)
    (G : DerivedCategory (ModuleCat.{max v uS uT uSp uTp} S) ⥤
      DerivedCategory (ModuleCat.{max v uS uT uSp uTp} T))
    (betaG : DerivedCategory.Q ⋙ G ⟶
      (ModuleCat.extendScalars.{uS, uT, max v uS uT uSp uTp} g).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [G.IsLeftDerivedFunctor betaG
      (HomologicalComplex.quasiIso (ModuleCat.{max v uS uT uSp uTp} S) (ComplexShape.up ℤ))]
    (H : DerivedCategory (ModuleCat.{max v uS uT uSp uTp} S') ⥤
      DerivedCategory (ModuleCat.{max v uS uT uSp uTp} T'))
    (betaH : DerivedCategory.Q ⋙ H ⟶
      (ModuleCat.extendScalars.{uSp, uTp, max v uS uT uSp uTp} h).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [H.IsLeftDerivedFunctor betaH
      (HomologicalComplex.quasiIso (ModuleCat.{max v uS uT uSp uTp} S') (ComplexShape.up ℤ))]
    (Bp : DerivedCategory (ModuleCat.{max v uS uT uSp uTp} S) ⥤
      DerivedCategory (ModuleCat.{max v uS uT uSp uTp} S'))
    (betaP : DerivedCategory.Q ⋙ Bp ⟶
      (ModuleCat.extendScalars.{uS, uSp, max v uS uT uSp uTp} p).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (K : CochainComplex (ModuleCat.{max v uS uT uSp uTp} S) ℤ)
    (hKp : CochainComplex.KFlat.{uSp, max v uS uT uTp}
      (((ModuleCat.extendScalars.{uS, uSp, max v uS uT uSp uTp} p).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K)) :=
  let g' : ULift.{max v uS uT uSp uTp} S →+* ULift.{max v uS uT uSp uTp} T :=
    (ULift.ringEquiv.symm.toRingHom.comp g).comp ULift.ringEquiv.toRingHom
  let Kt := ((ModuleCat.restrictScalars
      (ULift.ringEquiv : ULift.{max v uS uT uSp uTp} S ≃+* S).toRingHom).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K
  Bp.map (liftTransportPrefix.{max v uSp uTp, uS, uT} g G betaG K) ≫
    Bp.map (liftTransportFactors.{max v uSp uTp, uS, uT} g K) ≫
      (liftedBaseChangeComparison.{max v uT uTp, uS, uSp} p Bp betaP).app
          ((CochainComplex.extendScalarsLarge g' ⋙
            CochainComplex.restrictScalarsLarge g').obj Kt) ≫
        liftSquareConjugate.{v, uS, uT, uSp, uTp} g p w h comm hp H betaH K hKp

/-- **The projection formula at the two ring maps of a pushout square, at four independent ring
universes.**  For a pushout square `w ∘ g = h ∘ p` of commutative rings in four independent
universes, arbitrary models `G`, `H` of derived extension of scalars along `g` and `h`, and an
arbitrary model `Bp` of derived base change along `p` with comparison morphism `betaP`: the base
change along `p` of the component of `Dualizing.derivedExtendRestrictScalarsTensorIso` at `g`,
read at the class of a K-flat complex `K` and against the transport tail
`Dualizing.liftTransportTail` of the scalar lift, is
`Dualizing.liftSquareConjugatedFormula` — the base-changed transport prefix at `g` followed by
the same formula at `h`, read at the class of `S' ⊗_S K` and conjugated by the three comparisons
of the **lifted** square and the monoidality of degreewise extension of scalars along the lifted
left edge.

This is `Dualizing.derivedExtendRestrictScalarsTensorIsoEqualUniverse_square` carried across the
universe lift, which is what `Dualizing.tensorComparisonCompatibility_of_kFlat_tail` needs: its
two sides read the projection formula at `R → A` and at `R' → A ⊗_R R'`, whose four rings occupy
four universes that do not collapse.  The chain-level input is
`Dualizing.extendRestrictScalarsComplexIso_square` at the lifted square, available because
`Dualizing.uliftIsPushoutSquare` makes the lift a pushout square; the derived input at the near
edge is `Dualizing.derivedExtendRestrictScalarsTensorIso_hom_app_q_obj_chainPairing`, and at the
far edge the same read through `Dualizing.uliftExtendScalarsCommUpApp` by
`Dualizing.liftSquarePrefixTransported_comp`, whose prefix
`Dualizing.liftSquareRetraction_comp` retracts.  The edge base changed along contributes only
`Dualizing.liftedBaseChangeComparison`, so `Bp` carries no universal property; the two models `G`
and `H` are total left derived functors, which is what makes their component equations
available.

The right-hand side is named rather than written out: crossing the junctions it contains
inside this statement exceeds the per-declaration heartbeat budget.
`Dualizing.liftSquareConjugatedFormula`,
`Dualizing.liftSquareConjugate` and `Dualizing.liftSquareConjugateTail` are right-associated
composites nested one inside the next, so unfolding them gives the composite
`Stacks.CategoryTheory.comp_eq_of_chain_pairing` produces, factor for factor. -/
theorem derivedExtendRestrictScalarsTensorIso_square
    (g : S →+* T) (p : S →+* S') (w : T →+* T') (h : S' →+* T')
    (comm : w.comp g = h.comp p) (hp : MilnorPatching.IsPushoutSquare g p w h comm)
    (G : DerivedCategory (ModuleCat.{max v uS uT uSp uTp} S) ⥤
      DerivedCategory (ModuleCat.{max v uS uT uSp uTp} T))
    (betaG : DerivedCategory.Q ⋙ G ⟶
      (ModuleCat.extendScalars.{uS, uT, max v uS uT uSp uTp} g).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [G.IsLeftDerivedFunctor betaG
      (HomologicalComplex.quasiIso (ModuleCat.{max v uS uT uSp uTp} S) (ComplexShape.up ℤ))]
    (H : DerivedCategory (ModuleCat.{max v uS uT uSp uTp} S') ⥤
      DerivedCategory (ModuleCat.{max v uS uT uSp uTp} T'))
    (betaH : DerivedCategory.Q ⋙ H ⟶
      (ModuleCat.extendScalars.{uSp, uTp, max v uS uT uSp uTp} h).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [H.IsLeftDerivedFunctor betaH
      (HomologicalComplex.quasiIso (ModuleCat.{max v uS uT uSp uTp} S') (ComplexShape.up ℤ))]
    (Bp : DerivedCategory (ModuleCat.{max v uS uT uSp uTp} S) ⥤
      DerivedCategory (ModuleCat.{max v uS uT uSp uTp} S'))
    (betaP : DerivedCategory.Q ⋙ Bp ⟶
      (ModuleCat.extendScalars.{uS, uSp, max v uS uT uSp uTp} p).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (K : CochainComplex (ModuleCat.{max v uS uT uSp uTp} S) ℤ)
    (hK : CochainComplex.KFlat.{uS, max v uT uSp uTp} K)
    (hKp : CochainComplex.KFlat.{uSp, max v uS uT uTp}
      (((ModuleCat.extendScalars.{uS, uSp, max v uS uT uSp uTp} p).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K)) :
    let g' : ULift.{max v uS uT uSp uTp} S →+* ULift.{max v uS uT uSp uTp} T :=
      (ULift.ringEquiv.symm.toRingHom.comp g).comp ULift.ringEquiv.toRingHom
    let Kt := ((ModuleCat.restrictScalars
        (ULift.ringEquiv : ULift.{max v uS uT uSp uTp} S ≃+* S).toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K
    let Bcg := (CochainComplex.singleFunctor
        (ModuleCat.{max v uS uT uSp uTp} (ULift.{max v uS uT uSp uTp} S)) 0).obj
      ((ModuleCat.restrictScalars g').obj
        (ModuleCat.of (ULift.{max v uS uT uSp uTp} T) (ULift.{max v uS uT uSp uTp} T)))
    Bp.map ((derivedExtendRestrictScalarsTensorIso.{uS, uT, max v uSp uTp} g G betaG).hom.app
            (DerivedCategory.Q.obj K)) ≫
        Bp.map (liftTransportTail.{max v uSp uTp, uS, uT} g K hK) ≫
          (liftedBaseChangeComparison.{max v uT uTp, uS, uSp} p Bp betaP).app
            ((MonoidalCategory.tensorLeft Bcg).obj Kt) =
      liftSquareConjugatedFormula.{v, uS, uT, uSp, uTp}
        g p w h comm hp G betaG H betaH Bp betaP K hKp := by
  intro g' Kt Bcg
  exact Stacks.CategoryTheory.comp_eq_of_chain_pairing _ _ _ _
    (liftedBaseChangeComparison.{max v uT uTp, uS, uSp} p Bp betaP)
    ((extendRestrictScalarsComplexIso g').hom.app Kt) _ _ _ _ _
    (extendRestrictScalarsComplexIso_square.{max v uS uT uSp uTp} _ _ _ _
      (uliftSquareComm.{v, uS, uT, uSp, uTp} g p w h comm)
      (uliftIsPushoutSquare.{v, uS, uT, uSp, uTp} g p w h comm hp _) _)
    _ _ _ _
    (derivedExtendRestrictScalarsTensorIso_hom_app_q_obj_chainPairing.{max v uSp uTp, uS, uT}
      g G betaG K hK)
    _ _ _ _
    (liftSquareRetraction_comp.{max v uS uT, uSp, uTp} h H betaH _ hKp _
      (uliftExtendScalarsCommUpApp.{max v uT uTp, uS, uSp} p K))
    (liftSquarePrefixTransported_comp.{max v uS uT, uSp, uTp} h H betaH _ hKp _ _)

end Square

end Dualizing

end
