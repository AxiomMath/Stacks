module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Monoidal.LargeUniverse
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimits
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.HomComplex.Basic
public import StacksFrontier.Homology.HomComplex.DerivedAdjunction
public import StacksFrontier.Homology.HomComplex.DerivedInternalHom
public import StacksFrontier.Homology.KFlat.LargeUniverse
public import StacksFrontier.Homology.TensorComplex.ExactFunctor
public import StacksFrontier.Homology.Tor.DerivedChangeOfRings
public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunction
public import StacksFrontier.Homology.Tor.DerivedTensor
public import StacksFrontier.Homology.TorAmplitude.Comparison
public import StacksFrontier.Algebra.Homology.PseudoCoherent
public import StacksFrontier.Homology.HomComplex.Currying
public import StacksFrontier.Homology.HomComplex.DerivedTensorHom
public import StacksFrontier.Homology.HomComplex.Evaluation.TensorHom
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.KFlat.ScalarBaseChange
public import StacksFrontier.Homology.Perfect.Defs
public import StacksFrontier.Homology.PseudoCoherent.Basic
public import StacksFrontier.Homology.TensorComplex.Monoidal
public import StacksFrontier.Homology.TorAmplitude.KFlatRepresentative
public import StacksFrontier.Homology.TensorComplex.TensorUnitIso
public import StacksFrontier.Homology.HomComplex.RHom.BaseChange.ModelRestrictScalars
import all StacksFrontier.Homology.HomComplex.RHom.BaseChange.HomComplexChangeOfRings
import all StacksFrontier.Homology.HomComplex.RHom.BaseChange.ModelRestrictScalars

/-!
# The derived-Hom base-change map

Transposing the change-of-rings isomorphism for derived Hom along `f : R → A` under the derived
extension--restriction adjunction produces the base-change map
`RHom_R(K, M) ⊗ᴸ_R A ⟶ RHom_A(K ⊗ᴸ_R A, M ⊗ᴸ_R A)` (Stacks 0E1X).

## Main definitions

* `Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange` is the canonical derived-module
  base-change map for derived Hom, the mate of the unit-induced map under derived extension of
  scalars.
* `Stacks.DerivedHom.ExtensionOfScalars.internalHomBaseChange` is the underlying closed-monoidal
  construction: the internal-Hom comparison of a lax monoidal functor, as the mate of its tensor
  comparison.

## Main results

* `Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_hom_app` expresses the components
  of the change-of-rings isomorphism as the scalar transport of
  `Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso`.
* `Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange_homEquiv` characterizes the
  base-change map by its mate, and
  `Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange_naturality` records functoriality in
  both arguments; `Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChangeNatTrans` packages it
  as a natural transformation of bifunctors.

The file also contains the coefficient transport along `ULift` ring equivalences used for the
invertibility of the base-change map, and the chain-level tensor--Hom adjunction of the diagonal
model.

## Implementation notes

The `letI` bindings in the statements supply proved scalar-change instances at the common module
universe; they add no hypotheses.

## References

* [Stacks Project, Tag 0E1X](https://stacks.math.columbia.edu/tag/0E1X)
-/

open StacksDraft.DerivedHom.Construction (KInjectiveObjects Q_map_surjective_of_isKInjective
    postcomp_bijective postcomp_quasiIso_of_homotopyEquivalence precomp_bijective
    precomp_quasiIso_of_homotopyEquivalence)

section ChangeOfRingsIsoComponents

open CategoryTheory StacksDraft.DerivedHom

namespace Stacks.DerivedHom.BaseChange

universe uR uA uM

attribute [local instance] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency false in
/-- The components of the tagged change-of-rings isomorphism are the scalar transport of the
descended model comparison over the lifted rings: the transported restriction comparison `τ`,
the model comparison `modelRestrictScalarsNatIso`, the canonical comparison `eF` of derived
extensions of scalars, and the inverse scalar-restriction isomorphism `δ`. -/
public theorem derivedHomRestrictScalarsNatIso_hom_app
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A) :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    ∀ (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
      DerivedCategory (ModuleCat.{max uR uA uM} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]
    (K : (DerivedCategory (ModuleCat.{max uR uA uM} R))ᵒᵖ)
    (M : DerivedCategory (ModuleCat.{max uR uA uM} A)),
    let a :=
      CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uA, uM}
        f F comparison
    let E := _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, max uR uA
      uM} R
    let S := _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uA, max uR uA
      uM} A
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    letI : (ModuleCat.extendScalars.{max uR uA uM, max uR uA uM, max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    let U := (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory
    let V := (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory
    let T := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings f'
      (HomologicalComplex.zero : CochainComplex (ModuleCat.{max uR uA uM}
        (ULift.{max uR uA uM} A)) ℤ)
    let a' :=
      CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction f' T.B T.alphaB
    let δ : S.inverse ⋙ U ≅ V ⋙ E.inverse := scalarRestrictionIso.{uR, uA, uM} f
    let τ : U ⋙ E.functor ≅ S.functor ⋙ V :=
      Iso.compInverseIso (H := E.symm)
        ((Iso.inverseCompIso (G := S.symm) δ.symm).symm ≪≫
          (Functor.associator _ _ _).symm)
    let eF : E.functor ⋙ T.B ≅ F ⋙ S.functor :=
      (E.toAdjunction.comp a').leftAdjointUniq ((a.comp S.toAdjunction).ofNatIsoRight δ)
    let HR := DerivedInternalHom.Model.hom (ULift.{max uR uA uM} R)
    let HA := DerivedInternalHom.Model.hom (ULift.{max uR uA uM} A)
    (derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F comparison).hom.app (K, M) =
      E.inverse.map (HR.map (CategoryTheory.Prod.mkHom (𝟙 (Opposite.op (E.functor.obj K.unop)))
          (τ.hom.app M))) ≫
        E.inverse.map ((modelRestrictScalarsNatIso f' T.B T.alphaB).hom.app
          (Opposite.op (E.functor.obj K.unop), S.functor.obj M)) ≫
        E.inverse.map (V.map (HA.map (CategoryTheory.Prod.mkHom (eF.inv.app K.unop).op
          (𝟙 (S.functor.obj M))))) ≫
        δ.inv.app (HA.obj (Opposite.op (S.functor.obj (F.obj K.unop)), S.functor.obj M)) := by
  intro _ _ _ F comparison _ K M
  rfl


end Stacks.DerivedHom.BaseChange

end ChangeOfRingsIsoComponents

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory StacksDraft.DerivedHom

namespace Stacks.DerivedHom.ExtensionOfScalars

open Stacks.DerivedHom.BaseChange

section Monoidal

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [MonoidalClosed C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [MonoidalClosed D]

/-- The tensor comparison with a fixed left factor, regarded as a square of functors. -/
public def tensorLeftComparison (F : C ⥤ D) [F.LaxMonoidal] (K : C) :
    TwoSquare F (tensorLeft K) (tensorLeft (F.obj K)) F where
  app M := Functor.LaxMonoidal.μ F K M
  naturality {M N} f := by
    change (F.obj K ◁ F.map f) ≫ Functor.LaxMonoidal.μ F K N =
      Functor.LaxMonoidal.μ F K M ≫ F.map (K ◁ f)
    exact Functor.LaxMonoidal.μ_natural_right F K f

/-- The internal-Hom comparison for a lax monoidal functor between closed monoidal
categories, defined as the mate of its tensor comparison. -/
public noncomputable def internalHomBaseChange (F : C ⥤ D) [F.LaxMonoidal] (K : C) :
    TwoSquare (ihom K) F F (ihom (F.obj K)) :=
  mateEquiv (ihom.adjunction K) (ihom.adjunction (F.obj K))
    (tensorLeftComparison F K)

/-- The abstract internal-Hom comparison is contravariantly natural in its first argument. -/
public theorem internalHomBaseChange_whiskerLeft (F : Functor C D) [F.LaxMonoidal]
    {K K' : C} (f : K' ⟶ K) :
    (internalHomBaseChange F K).whiskerBottom (MonoidalClosed.pre (F.map f)) =
      (internalHomBaseChange F K').whiskerTop (MonoidalClosed.pre f) := by
  unfold internalHomBaseChange MonoidalClosed.pre
  rw [← mateEquiv_conjugateEquiv_vcomp, ← conjugateEquiv_mateEquiv_vcomp]
  congr 1
  ext M
  exact Functor.LaxMonoidal.μ_natural_left F f M

end Monoidal

section DerivedModules

universe uR uA uM

attribute [local instance] HasDerivedCategory.standard

/-- The natural transformation induced by the unit on the second derived-Hom argument,
followed by the canonical change-of-rings isomorphism of Stacks 0E1W. -/
public def derivedHomBaseChangeMate
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A) :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    ∀ (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
      DerivedCategory (ModuleCat.{max uR uA uM} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))],
    _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{uR, max uR uA uM} R ⟶
      Functor.prod F.op F ⋙ _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{uA, max uR uA
        uM} A ⋙
        (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory := by
  intro F comparison _
  exact Functor.whiskerRight
      (NatTrans.prod (𝟙 (𝟭 (DerivedCategory (ModuleCat.{max uR uA uM} R))ᵒᵖ))
        (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uA, uM}
          f F comparison).unit)
      (_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{uR, max uR uA uM} R) ≫
    Functor.whiskerLeft (Functor.prod (𝟭 _) F)
      (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F comparison).hom

/-- **Stacks 0E1X.** The canonical derived-module base-change map
`RHom_R(K, M) ⊗ᴸ_R A ⟶ RHom_A(K ⊗ᴸ_R A, M ⊗ᴸ_R A)`.
It is the mate of the unit-induced map under the adjunction of Stacks 0GMT, using
exactly the change-of-rings identification of Stacks 0E1W. -/
@[stacks 0E1V "the derived base-change map for derived hom", stacks 0E1X]
public def derivedHomBaseChange
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A) :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    ∀ (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
      DerivedCategory (ModuleCat.{max uR uA uM} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]
    (K M : DerivedCategory (ModuleCat.{max uR uA uM} R)),
    F.obj ((_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{uR, max uR uA uM} R).obj
      (Opposite.op K, M)) ⟶
      (_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{uA, max uR uA uM} A).obj
        (Opposite.op (F.obj K), F.obj M) := by
  intro F comparison _ K M
  exact ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uA, uM}
    f F comparison).homEquiv _ _).symm
    ((derivedHomBaseChangeMate.{uR, uA, uM} f F comparison).app (Opposite.op K, M))

/-- The adjoint of the canonical base-change map is derived Hom applied to the unit,
followed by the isomorphism of Stacks 0E1W. -/
public theorem derivedHomBaseChange_homEquiv
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A) :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    ∀ (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
      DerivedCategory (ModuleCat.{max uR uA uM} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]
    (K M : DerivedCategory (ModuleCat.{max uR uA uM} R)),
    (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uA, uM}
        f F comparison).homEquiv _ _
        (derivedHomBaseChange.{uR, uA, uM} f F comparison K M) =
      (_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{uR, max uR uA uM} R).map
          (𝟙 (Opposite.op K),
            (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uA, uM}
              f F comparison).unit.app M) ≫
        (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
          comparison).hom.app
          (Opposite.op K, F.obj M) := by
  intro F comparison _ K M
  exact Equiv.apply_symm_apply _ _

/-- Functoriality of the canonical map, contravariantly in `K` and covariantly in `M`. -/
@[reassoc]
public theorem derivedHomBaseChange_naturality
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A) :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    ∀ (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
      DerivedCategory (ModuleCat.{max uR uA uM} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]
    {K K' M M' : DerivedCategory (ModuleCat.{max uR uA uM} R)}
    (k : K' ⟶ K) (m : M ⟶ M'),
    F.map ((_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{uR, max uR uA uM} R).map
      (k.op, m)) ≫
        derivedHomBaseChange.{uR, uA, uM} f F comparison K' M' =
      derivedHomBaseChange.{uR, uA, uM} f F comparison K M ≫
        (_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{uA, max uR uA uM} A).map ((F.map
          k).op, F.map m) := by
  intro F comparison _ K K' M M' k m
  exact (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uA, uM}
    f F comparison).homEquiv_naturality_right_square _ _ _ _
      ((derivedHomBaseChangeMate.{uR, uA, uM} f F comparison).naturality
        (CategoryTheory.Prod.mkHom k.op m))

/-- The canonical comparison as a natural transformation of the two derived-Hom bifunctors. -/
public def derivedHomBaseChangeNatTrans
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A) :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    ∀ (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
      DerivedCategory (ModuleCat.{max uR uA uM} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))],
    _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{uR, max uR uA uM} R ⋙ F ⟶
      Functor.prod F.op F ⋙ _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{uA, max uR uA
        uM} A := by
  intro F comparison _
  exact {
    app X := derivedHomBaseChange.{uR, uA, uM} f F comparison X.1.unop X.2
    naturality {X Y} g := derivedHomBaseChange_naturality.{uR, uA, uM} f F comparison g.1.unop g.2 }

end DerivedModules

end Stacks.DerivedHom.ExtensionOfScalars

end

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex CochainComplex.HomComplex StacksDraft.DerivedHom

namespace Stacks.DerivedHom.BaseChangeIso

universe uR uA uM

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

open scoped TensorProduct ChangeOfRings

section CoefficientTransport

universe u v

/-- The coefficient equivalence that lifts the ring into the module universe, restriction of
scalars along `ULift.ringEquiv`. This is the transport used to state Tor-amplitude conditions
at a module universe independent of the ring's. -/
public noncomputable abbrev moduleUniverseEquiv (R : Type uR) [CommRing R] :
    ModuleCat.{max uR v} R ≌ ModuleCat.{max uR v} (ULift.{v} R) :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv (ULift.ringEquiv : ULift.{v} R ≃+* R)

/-- Tensoring with a module placed in degree zero, in the canonical derived tensor product of
Stacks 0BYI, read as a functor of the complex. -/
public noncomputable abbrev canonTensorMod {R : Type u} [CommRing R] (N : ModuleCat.{u} R) :
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R) :=
  (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor.flip.obj
    ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)

/-- The same canonical derived tensor product read as a functor of the module variable. -/
public noncomputable abbrev canonTensorObj {R : Type u} [CommRing R]
    (X : DerivedCategory (ModuleCat.{u} R)) :
    ModuleCat.{u} R ⥤ DerivedCategory (ModuleCat.{u} R) :=
  DerivedCategory.singleFunctor (ModuleCat.{u} R) 0 ⋙
    (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor.obj X

/-- The cochain `Φ^n(β)` sends `y` to the image of `β ⊗ y` in the total complex. -/
private lemma Phiv_v_apply (R : Type u) [CommRing R]
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) (β : K.X n)
    (p q : ℤ) (hpq : p + n = q) (y : L.X p) :
    ((Stacks.HomComplex.TensorHomMap.Phiv R K L n β).v p q hpq).hom y =
      (HomologicalComplex.ιTensorObj K L n p q (by omega)).hom (β ⊗ₜ[R] y) := by
  rw [Stacks.HomComplex.TensorHomMap.Phiv_v]
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
  congr 1

/-- Restriction along a ring isomorphism preserves the underlying additive group. -/
private abbrev restrictScalarsRingEquiv
    {R S : Type*} [Ring R] [Ring S] (e : S ≃+* R) (M : ModuleCat R) :
    LinearEquiv (σ' := (e : S →+* R)) (e.symm : R →+* S) M
      ((ModuleCat.restrictScalars e.toRingHom).obj M) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    change r • x = e (e.symm r) • x
    rw [e.apply_symm_apply]

/-- Restriction along a ring isomorphism preserves finite modules. -/
private theorem finite_restrictScalars_ringEquiv
    {R S : Type*} [Ring R] [Ring S] (e : S ≃+* R) (M : ModuleCat R) [Module.Finite R M] :
    Module.Finite S ((ModuleCat.restrictScalars e.toRingHom).obj M) :=
  Module.Finite.of_surjective (restrictScalarsRingEquiv e M).toLinearMap
    (restrictScalarsRingEquiv e M).surjective

/-- Restriction along a ring isomorphism preserves perfect complexes. -/
private theorem isPerfect_restrictScalars_ringEquiv
    {R S : Type*} [Ring R] [Ring S]
    (e : S ≃+* R) (K : DerivedCategory (ModuleCat R))
    (hK : StacksDraft.Perfect.IsPerfect K) :
    StacksDraft.Perfect.IsPerfect
      ((ModuleCat.restrictScalars e.toRingHom).mapDerivedCategory.obj K) := by
  let G := ModuleCat.restrictScalars e.toRingHom
  have : G.IsEquivalence := ModuleCat.restrictScalars_isEquivalence_of_ringEquiv e
  obtain ⟨P, a, b, ha, hb, hf, hp, ⟨i⟩⟩ := hK
  have := ha
  have := hb
  have := hf
  have := hp
  exact ⟨(G.mapHomologicalComplex (.up ℤ)).obj P, a, b, inferInstance, inferInstance,
    fun n ↦ finite_restrictScalars_ringEquiv e (P.X n),
    fun n ↦ Module.Projective.of_equiv (restrictScalarsRingEquiv e (P.X n)),
    ⟨G.mapDerivedCategory.mapIso i ≪≫ G.mapDerivedCategoryFactors.app P⟩⟩

/-- Restriction along a ring isomorphism preserves pseudo-coherent complexes. -/
private theorem isPseudoCoherent_restrictScalars_ringEquiv
    {R S : Type*} [Ring R] [Ring S]
    (e : S ≃+* R) (K : DerivedCategory (ModuleCat R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((ModuleCat.restrictScalars e.toRingHom).mapDerivedCategory.obj K) := by
  let G := ModuleCat.restrictScalars e.toRingHom
  have : G.IsEquivalence := ModuleCat.restrictScalars_isEquivalence_of_ringEquiv e
  obtain ⟨P, ⟨⟨b, hb⟩, hf⟩, ⟨i⟩⟩ := hK
  have := hb
  refine ⟨(G.mapHomologicalComplex (.up ℤ)).obj P, ⟨⟨b, inferInstance⟩, fun n ↦ ?_⟩,
    ⟨(G.mapDerivedCategoryFactors.app P).symm ≪≫ G.mapDerivedCategory.mapIso i⟩⟩
  have := (hf n).1
  have := (hf n).2
  exact ⟨finite_restrictScalars_ringEquiv e (P.X n),
    Module.Free.of_equiv (restrictScalarsRingEquiv e (P.X n))⟩

/-- Exact functors preserve lower cohomological bounds. -/
private theorem isGE_mapDerivedCategory
    {R : Type*} {A : Type*} [Ring R] [Ring A]
    (G : ModuleCat.{u} R ⥤ ModuleCat.{v} A) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (X : DerivedCategory (ModuleCat.{u} R)) (n : ℤ) [DerivedCategory.IsGE X n] :
    DerivedCategory.IsGE (G.mapDerivedCategory.obj X) n := by
  rw [DerivedCategory.isGE_iff]
  intro i hi
  exact (G.map_isZero ((DerivedCategory.isGE_iff X n).mp inferInstance i hi)).of_iso
    ((StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso G i).app X)

/-- If an exact functor detects isomorphisms, so does its derived functor. -/
private theorem isIso_of_mapDerivedCategory
    {R : Type*} {A : Type*} [Ring R] [Ring A]
    (G : ModuleCat.{u} R ⥤ ModuleCat.{v} A) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [G.ReflectsIsomorphisms] {X Y : DerivedCategory (ModuleCat.{u} R)} (g : X ⟶ Y)
    [IsIso (G.mapDerivedCategory.map g)] : IsIso g := by
  rw [DerivedCategory.isIso_iff]
  intro n
  let e := StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso G n
  have : IsIso (G.map ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map g)) := by
    have h := e.hom.naturality g
    dsimp only [Functor.comp_map] at h
    rw [← isIso_comp_left_iff (e.hom.app X), ← h]
    infer_instance
  exact isIso_of_reflects_iso _ G

/-- Every term of a single complex of a flat module is flat. -/
private theorem flat_single_X
    {R : Type*} [CommRing R] (M : ModuleCat R) [Module.Flat R M]
    {ι : Type*} [DecidableEq ι] (c : ComplexShape ι) (a i : ι) :
    Module.Flat R (((HomologicalComplex.single _ c a).obj M).X i) := by
  by_cases hi : i = a
  · subst i
    exact Module.Flat.of_linearEquiv (HomologicalComplex.singleObjXSelf c a M).toLinearEquiv
  · have := ModuleCat.isZero_iff_subsingleton.mp
      (HomologicalComplex.isZero_single_obj_X c a M i hi)
    infer_instance

/-- A flat module in degree `a` has no derived tensor cohomology below `a`. -/
private theorem hasTorAmplitudeAbove_single_of_flat
    {R : Type u} [CommRing R] (M : ModuleCat.{u} R) [Module.Flat R M] (a : ℤ) :
    ∀ (N : ModuleCat.{u} R) (i : ℤ), i < a →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
        ((canonTensorMod N).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) a).obj M))) := by
  apply
    (StacksDraft.TorAmplitude.hasTorAmplitudeAbove_iff_exists_kFlat_flat_representative_canonical
      _ a).2
  let P := (CochainComplex.singleFunctor (ModuleCat.{u} R) a).obj M
  have : ∀ i, Module.Flat R (P.X i) := flat_single_X M (.up ℤ) a
  exact ⟨P, CochainComplex.KFlat.kFlat_of_flat P a, inferInstance, inferInstance, ⟨Iso.refl _⟩⟩

/-- The natural comparison identifying the scalar transport of derived internal Hom with the
fixed K-injective construction over the lifted ring; its components are the counit of the
scalar equivalence. -/
private def homLiftIso (R : Type uR) [CommRing R] :
    Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{uR, v} R ⋙
        (Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, v} R).functor ≅
      Functor.prod (Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, v}
        R).functor.op
          (Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, v} R).functor ⋙
        (StacksDraft.DerivedHom.derivedHomAdjunction (R := ULift.{v} R)).hom :=
  NatIso.ofComponents
    (fun _ ↦ (Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, v}
      R).counitIso.app _)
    (fun _ ↦
      (Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, v}
        R).counitIso.hom.naturality _)

/-- The degree-zero case of the currying isomorphism, evaluated on a tensor summand. This is
the specialization of `Stacks.HomComplex.Currying.curryIso_hom_apply` at `n = 0` used by the model
  comparisons. -/
private theorem curryIso_zero_apply {R : Type u} [CommRing R]
    (K L M : CochainComplex (ModuleCat.{u} R) ℤ)
    (φ : K ⟶ CochainComplex.HomComplexR R L M) (r s t : ℤ) (hrs : r + s = t)
    (x : K.X r) (y : L.X s) :
    ((((Stacks.HomComplex.Currying.curryIso K L M).hom.f 0).hom
        (CochainComplex.HomComplex.Cochain.ofHom φ)).v t t (add_zero t)).hom
        ((HomologicalComplex.ιTensorObj K L r s t hrs).hom (x ⊗ₜ[R] y)) =
      ((((CochainComplex.HomComplex.Cochain.ofHom φ).v r (r + 0)
        (by omega)).hom x).v s t (by omega)).hom y :=
  Stacks.HomComplex.Currying.curryIso_hom_apply K L M 0 r s t t hrs (add_zero t) _ x y

end CoefficientTransport

section DiagonalModel

/-! ### The diagonal on a K-flat tensor factor and a K-injective target -/

open CategoryTheory.MonoidalCategory Pretriangulated ZeroObject

namespace DiagonalModel

universe u

variable {R : Type u} [CommRing R]

open CochainComplex HomComplex HomologicalComplex TensorProduct

section ChainAdjunction
set_option backward.isDefEq.respectTransparency false

private lemma chainTensorHomEquiv_naturality_left
    {K K' L M : CochainComplex (ModuleCat R) ℤ} (f : K' ⟶ K)
    (g : K ⟶ CochainComplex.HomComplexR R L M) :
    Stacks.DerivedTensorHomDiagonal.chainTensorHomEquiv K' L M (f ≫ g) =
      f ▷ L ≫ Stacks.DerivedTensorHomDiagonal.chainTensorHomEquiv K L M g := by
  apply Cochain.ofHom_injective
  rw [Stacks.DerivedTensorHomDiagonal.ofHom_chainTensorHomEquiv,
    ← Stacks.HomComplex.MonoidalClosed.precomp_ofHom f g,
    ← Stacks.HomComplex.MonoidalClosed.precomp_ofHom (f ▷ L)
      (Stacks.DerivedTensorHomDiagonal.chainTensorHomEquiv K L M g),
    Stacks.DerivedTensorHomDiagonal.ofHom_chainTensorHomEquiv]
  exact congrArg (fun k => (k.f 0).hom (Cochain.ofHom g))
    (Stacks.HomComplex.Currying.curryIso_naturality_left f)

private lemma chainTensorHomEquiv_naturality_right
    {K L M M' : CochainComplex (ModuleCat R) ℤ}
    (g : K ⟶ CochainComplex.HomComplexR R L M) (f : M ⟶ M') :
    Stacks.DerivedTensorHomDiagonal.chainTensorHomEquiv K L M'
        (g ≫ Stacks.HomComplex.TensorHomMap.postcomp R L M M' f) =
      Stacks.DerivedTensorHomDiagonal.chainTensorHomEquiv K L M g ≫ f := by
  apply Cochain.ofHom_injective
  rw [Stacks.DerivedTensorHomDiagonal.ofHom_chainTensorHomEquiv,
    ← Stacks.HomComplex.MonoidalClosed.postcomp_ofHom g,
    ← Stacks.HomComplex.MonoidalClosed.postcomp_ofHom
      (Stacks.DerivedTensorHomDiagonal.chainTensorHomEquiv K L M g) f,
    Stacks.DerivedTensorHomDiagonal.ofHom_chainTensorHomEquiv]
  exact congrArg (fun k => (k.f 0).hom (Cochain.ofHom g))
    (Stacks.HomComplex.Currying.curryIso_naturality_right f)

private noncomputable def chainTensorHomAdjunction
    (M : CochainComplex (ModuleCat R) ℤ) :
    tensorRight M ⊣ Stacks.DerivedTensorHomDiagonal.chainHomFunctor M :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun K L => (Stacks.DerivedTensorHomDiagonal.chainTensorHomEquiv K M L).symm
      homEquiv_naturality_left_symm := chainTensorHomEquiv_naturality_left
      homEquiv_naturality_right := by
        intro K L L' f g
        change (Stacks.DerivedTensorHomDiagonal.chainTensorHomEquiv K M L').symm (f ≫ g) =
          (Stacks.DerivedTensorHomDiagonal.chainTensorHomEquiv K M L).symm f ≫
            Stacks.HomComplex.TensorHomMap.postcomp R M L L' g
        apply (Stacks.DerivedTensorHomDiagonal.chainTensorHomEquiv K M L').injective
        rw [Equiv.apply_symm_apply, chainTensorHomEquiv_naturality_right,
          Equiv.apply_symm_apply] }

private theorem transpose_theta (K L M : CochainComplex (ModuleCat R) ℤ) :
    Stacks.DerivedTensorHomDiagonal.chainTensorHomEquiv (K ⊗ HomComplexR R M L) M (K ⊗ L)
      (Stacks.HomComplex.TensorHomComparison.theta K L M) =
      (α_ K (HomComplexR R M L) M).hom ≫
        K ◁ Stacks.DerivedTensorHomDiagonal.chainTensorHomEquiv (HomComplexR R M L) M L (𝟙 _) := by
  ext n : 1
  apply GradedObject.Monoidal.tensorObj₃'_ext
  intro p q r h
  rw [GradedObject.Monoidal.ιTensorObj₃'_eq _ _ _ p q r n h (p + q) rfl]
  change (ιTensorObj K (HomComplexR R M L) p q (p + q) rfl ▷ M.X r) ≫
      ιTensorObj (K ⊗ HomComplexR R M L) M (p + q) r n h ≫ _ =
    (ιTensorObj K (HomComplexR R M L) p q (p + q) rfl ▷ M.X r) ≫
      ιTensorObj (K ⊗ HomComplexR R M L) M (p + q) r n h ≫
        ((α_ K (HomComplexR R M L) M).hom.f n ≫
          (K ◁ Stacks.DerivedTensorHomDiagonal.chainTensorHomEquiv
            (HomComplexR R M L) M L (𝟙 _)).f n)
  rw [reassoc_of% (CochainComplex.LeftDual.ι_associator_hom K (HomComplexR R M L) M
    p q r (p + q) (q + r) n rfl rfl h)]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro z m
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simpa [TensorProduct.add_tmul] using congrArg₂ (· + ·) hx hy
  | tmul x φ =>
    change Cochain M L q at φ
    change (Stacks.DerivedTensorHomDiagonal.chainTensorHomEquiv (K ⊗ HomComplexR R M L) M (K ⊗ L)
      (Stacks.HomComplex.TensorHomComparison.theta K L M)).f n
      ((ιTensorObj (K ⊗ HomComplexR R M L) M (p + q) r n h)
        ((ιTensorObj K (HomComplexR R M L) p q (p + q) rfl (x ⊗ₜ[R] φ)) ⊗ₜ[R] m)) = _
    rw [Stacks.DerivedTensorHomDiagonal.chainTensorHomEquiv_apply]
    change ((Stacks.HomComplex.TensorHomComparison.thetaDeg K L M (p + q))
      ((ιTensorObj K (HomComplexR R M L) p q (p + q) rfl).hom (x ⊗ₜ[R] φ))).v r n (by omega) m = _
    rw [Stacks.HomComplex.TensorHomComparison.theta_apply]
    change (ιTensorObj K L p (n - p) n (by omega)) (x ⊗ₜ[R] φ.v r (n - p) (by omega) m) =
      (K ◁ Stacks.DerivedTensorHomDiagonal.chainTensorHomEquiv (HomComplexR R M L) M L (𝟙 _)).f n
        ((ιTensorObj K (HomComplexR R M L ⊗ M) p (q + r) n (by omega))
          (x ⊗ₜ[R] (ιTensorObj (HomComplexR R M L) M q r (q + r) rfl (φ ⊗ₜ[R] m))))
    rw [← id_tensorHom, StacksDraft.DerivedHom.DerivedInternalHom.Model.tensorHom_apply,
      Stacks.DerivedTensorHomDiagonal.chainTensorHomEquiv_apply]
    have hn : n - p = q + r := by omega
    simp only [HomologicalComplex.id_f, ModuleCat.id_apply]
    change (ιTensorObj K L p (n - p) n (by omega)).hom
      (x ⊗ₜ[R] (φ.v r (n - p) (by omega)).hom m) =
        (ιTensorObj K L p (q + r) n (by omega)).hom
          (x ⊗ₜ[R] (φ.v r (q + r) (by omega)).hom m)
    have he (s t : ℤ) (hs : p + s = n) (ht : p + t = n)
        (hsr : r + q = s) (htr : r + q = t) (hst : s = t) :
        (ιTensorObj K L p s n hs).hom (x ⊗ₜ[R] (φ.v r s hsr).hom m) =
          (ιTensorObj K L p t n ht).hom (x ⊗ₜ[R] (φ.v r t htr).hom m) := by
      cases hst
      rfl
    exact he (n - p) (q + r) (by omega) (by omega) (by omega) (by omega) hn


end ChainAdjunction

end DiagonalModel

end DiagonalModel

end Stacks.DerivedHom.BaseChangeIso

end
