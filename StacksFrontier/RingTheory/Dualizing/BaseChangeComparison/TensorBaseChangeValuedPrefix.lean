module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ScalarLiftExtendComparison
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeMonoidalChainLevel
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeTransposeKFlat

/-!
# The keystone at a K-flat pair, with both factors of the prefix valued

`Dualizing.tensorBaseChangeMor_eq_of_monoidal_chain_level` reduces the [stacks 068I]
identification at a pair of K-flat complexes to one hypothesis `ha`, which pins the localization
of the chain map presenting the prefix.  Two things stand in that hypothesis for which `ha`
offers no handle: the [stacks 0A63] transpose over `A` of the [stacks 068I] candidate
`Dualizing.tensorBaseChangeMor`, and the component at the class of `L` of the fourth factor of
[stacks 0E1W], which is a `CategoryTheory.Adjunction.leftAdjointUniq` and so carries no
description of its own.

Both are already valued, independently and in different files, and until now neither valuation
had a consumer:

* `Dualizing.tensorBaseChangeMor_transpose_eq_q_obj` gives the transpose as the [stacks 0A63]
  transpose of the tensor of the two degreewise comparisons followed by the K-flat tensor model
  over `A` and the localization of a chain isomorphism `e` satisfying
  `CochainComplex.DerivedTensor.IsTensorBaseChangeIso`, composed with the internal Hom of the
  inverse of `Stacks.DerivedHom.BaseChange.tensorKFlatComparisonIso`.
* `Stacks.DerivedHom.BaseChange.derivedExtensionScalarsLiftIso_hom_app_of_kFlat` gives the
  [stacks 0E1W] component as the scalar-lift presentation of `L`, the specified counit
  `T.alphaB` of the canonical model over the lifted rings, the localization of the chain map
  `c₀` of `Stacks.DerivedHom.BaseChange.exists_scalarLiftExtendComparison`, the inverted
  scalar-lift presentation of `A ⊗_R L`, and the inverse of `comparison.app L`.

This file substitutes both into `ha`.  In the hypothesis of
`Dualizing.tensorBaseChangeMor_eq_of_valued_prefix` the prefix enters only through the two
`let`-bound values `trV` and `eFv`: neither the [stacks 068I] candidate nor the [stacks 0E1W]
comparison is named, and the preamble no longer builds
`CategoryTheory.Adjunction.leftAdjointUniq` at all.  Every factor of the prefix is now a
degreewise comparison, a specified counit, a localized chain map, or an isomorphism of
presentations.

**What is not done here.**  Nothing is registered and no caveat is lifted.  Both hypotheses of
`Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` remain open; in particular the
comparison identity `h` is untouched, and its frontier remains
`Dualizing.tensorComparisonCompatibility_of_kFlat_tail`.  No step of the surviving equation is
discharged: what changes is only which data that equation is written in.

## Main results

* `Dualizing.tensorBaseChangeMor_eq_of_valued_prefix` -- the [stacks 068I] identification at a
  pair of K-flat complexes, from one equation whose [stacks 068I] side carries the two valued
  terms in place of the candidate's transpose and the [stacks 0E1W] component.

## Implementation notes

The two valuations are existential in the data they produce -- a K-flatness proof `hFL` and a
chain isomorphism `e` on one side, a chain map `c₀` and its defining equation `_hc₀` on the other
-- so that data is quantified inside the hypothesis, where the proof can instantiate it from the
two lemmas, rather than in front of the conclusion the way `J`, `I`, `q` and `n` are.

The goal is hostile to `rw`: it is not type-correct at `implicit` transparency, so a rewrite of a
visibly present pattern reports that it found no occurrence.  The substitution is therefore
performed by `Dualizing.comp_congr_head` and `Dualizing.comp_congr_slot`, stated over a variable
category with the slot presented as a function of the term being replaced, and instantiated by
`exact`.  The value of the transpose needs a type ascription on its `let`: its own last factor
is `dA.hom.map` at a pair of objects that nothing else determines, and `dA.hom` cannot be
unfolded.

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

/-- **Replacing the first factor of a four-factor composite.**

The slot is presented as a function `p` of the term being replaced, and the equation `hz` comes
first, so that the type of that term is known before `p` is elaborated; the remaining factors and
the right-hand side are left to unification. -/
theorem comp_congr_head {C : Type*} [Category* C] {W X Z : C}
    {α : Sort*} {z z' : α} (hz : z = z') (p : α → (W ⟶ X)) {r : X ⟶ Z} {g : W ⟶ Z}
    (h : p z ≫ r = g) : p z' ≫ r = g := by
  subst hz
  exact h

/-- **Replacing the third factor of a four-factor composite.**

As `Dualizing.comp_congr_head`, with the two factors before the slot given explicitly so that the
composite is parsed at the association the slot sits in. -/
theorem comp_congr_slot {C : Type*} [Category* C] {W X₁ X₂ X₃ Z : C}
    {α : Sort*} {z z' : α} (hz : z = z') (a : W ⟶ X₁) (b : X₁ ⟶ X₂) (p : α → (X₂ ⟶ X₃))
    {r : X₃ ⟶ Z} {g : W ⟶ Z} (h : a ≫ b ≫ p z ≫ r = g) : a ≫ b ≫ p z' ≫ r = g := by
  subst hz
  exact h

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
  (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
    DerivedCategory (ModuleCat.{max uR uA uM} A))
  (comparison : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [hF : F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]

include hF in
/-- **The keystone at a K-flat pair, with both factors of the prefix valued.**

`Dualizing.tensorBaseChangeMor_eq_of_monoidal_chain_level` with the two terms in `ha` that had no
description replaced by their values, so that the hypothesis names neither
`Dualizing.tensorBaseChangeMor` nor the [stacks 0E1W] comparison.

`trV` is the value `Dualizing.tensorBaseChangeMor_transpose_eq_q_obj` gives for the
[stacks 0A63] transpose over `A` of the [stacks 068I] candidate, and `eFv` the value
`Stacks.DerivedHom.BaseChange.derivedExtensionScalarsLiftIso_hom_app_of_kFlat` gives for the
component of the fourth factor of [stacks 0E1W] at the class of `L`.  Both lemmas produce data:
the K-flatness `hFL` of `A ⊗_R L` and a chain isomorphism `e` satisfying
`CochainComplex.DerivedTensor.IsTensorBaseChangeIso` for the first, the chain map `c₀` of
`Stacks.DerivedHom.BaseChange.exists_scalarLiftExtendComparison` and its defining equation `_hc₀`
for the second.  Both are supplied by those lemmas for every `K` and `L`, so quantifying over
them inside the hypothesis costs nothing, exactly as the quantifier over `w` and `t` costs
nothing in `Dualizing.tensorBaseChangeMor_eq_of_monoidal_chain_level`. -/
theorem tensorBaseChangeMor_eq_of_valued_prefix
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
    let δ : S.inverse ⋙ U ≅ V ⋙ E.inverse :=
      _root_.Stacks.DerivedHom.BaseChange.scalarRestrictionIso.{uR, uA, uM} f
    let τ : U ⋙ E.functor ≅ S.functor ⋙ V :=
      Iso.compInverseIso (H := E.symm)
        ((Iso.inverseCompIso (G := S.symm) δ.symm).symm ≪≫
          (Functor.associator _ _ _).symm)
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
    let YP := ((ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L
    let ZZ := ((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj YP
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
    letI : IsIso (comparison.app (tensorComplex.{uR, max uR uA uM} K L)) :=
      CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat.{uR, uA, uM} f F
        comparison (tensorComplex.{uR, max uR uA uM} K L)
        (_root_.Stacks.DerivedHom.BaseChange.kFlat_tensorComplex.{uR, uA, uM} K L hK hL)
    letI : IsIso (comparison.app L) :=
      CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat.{uR, uA, uM} f F
        comparison L hL
    (∀ (hFL : IsKFlat.{uA, max uR uA uM}
          ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj L))
      (e : tensorComplex.{uA, max uR uA uM}
          ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj K)
          ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj L) ≅
        (extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj
          (tensorComplex.{uR, max uR uA uM} K L))
      (_he : IsTensorBaseChangeIso.{uR, uA, max uR uA uM} f K L e)
      (c₀ : ((ModuleCat.extendScalars.{max uR uA uM, max uR uA uM,
          max uR uA uM} f').mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀ ⟶ ZZ)
      (_hc₀ : ((ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').mapHomologicalComplex
              (ComplexShape.up ℤ)).unit.app K₀ ≫
          ((ModuleCat.restrictScalars.{max uR uA uM} f').mapHomologicalComplex
            (ComplexShape.up ℤ)).map c₀ =
        (_root_.Stacks.DerivedHom.BaseChange.scalarLiftExtendUnitChain.{uR, uA, uM} f L :
          K₀ ⟶ ((ModuleCat.restrictScalars.{max uR uA uM} f').mapHomologicalComplex
            (ComplexShape.up ℤ)).obj ZZ)),
    let trV : F.obj (DerivedCategory.Q.obj K) ⟶
        dA.hom.obj (Opposite.op (F.obj (DerivedCategory.Q.obj L)), M) :=
      (dA.homEquiv (F.obj (DerivedCategory.Q.obj K)) (F.obj (DerivedCategory.Q.obj L))
            (DerivedCategory.Q.obj ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj
              (tensorComplex.{uR, max uR uA uM} K L)))).symm
          (dA.tensor.map
                ((CategoryTheory.Prod.mkHom (comparison.app K) (comparison.app L) :
                    ((F.obj (DerivedCategory.Q.obj K), F.obj (DerivedCategory.Q.obj L)) :
                      DerivedCategory (ModuleCat.{max uR uA uM} A) ×
                        DerivedCategory (ModuleCat.{max uR uA uM} A)) ⟶
                    (DerivedCategory.Q.obj ((extensionOfScalarsCochain.{uR, uA,
                        max uR uA uM} f).obj K),
                      DerivedCategory.Q.obj ((extensionOfScalarsCochain.{uR, uA,
                        max uR uA uM} f).obj L)))) ≫
              (derivedTensor_comparison.{uA, max uR uA uM} A
                  ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj K)
                  ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj L) hFL).hom ≫
                DerivedCategory.Q.map e.hom) ≫
        dA.hom.map (𝟙 (Opposite.op (F.obj (DerivedCategory.Q.obj L))),
          (_root_.Stacks.DerivedHom.BaseChange.tensorKFlatComparisonIso.{uR, uA, uM} f F
            comparison K L hK hL).inv)
    let eFv :=
      ((T.B.map (_root_.Stacks.DerivedHom.BaseChange.scalarLiftQObjIso.{uR,
                max uR uA uM} R L).hom ≫
            (T.alphaB.app K₀ ≫ DerivedCategory.Q.map c₀)) ≫
          (_root_.Stacks.DerivedHom.BaseChange.scalarLiftQObjIso.{uA,
            max uR uA uM} A YP).inv) ≫
        S.functor.map (inv (comparison.app L))
      ∀ (w : ((ModuleCat.restrictScalars.{max uR uA uM}
            (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K ⟶
        (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM} f').obj
          (CochainComplex.HomComplexR (ULift.{max uR uA uM} A)
            ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM,
              max uR uA uM} f').obj K₀) J))
      (t : (CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM} f').obj
          (((ModuleCat.restrictScalars.{max uR uA uM}
            (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ⟶
        CochainComplex.HomComplexR (ULift.{max uR uA uM} A)
          ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM,
            max uR uA uM} f').obj K₀) J)
      (_hw : w = ((ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app (((ModuleCat.restrictScalars.{max uR uA uM}
            (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ≫
          (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM,
            max uR uA uM} f').map t)
      (_ha : E.functor.map (adj.unit.app (DerivedCategory.Q.obj K) ≫ U.map trV) ≫
              (E.functor.map (δ.hom.app (HA.obj
                      (Opposite.op (S.functor.obj (F.obj (DerivedCategory.Q.obj L))),
                        S.functor.obj M))) ≫
                  E.counitIso.hom.app (V.obj (HA.obj
                    (Opposite.op (S.functor.obj (F.obj (DerivedCategory.Q.obj L))),
                      S.functor.obj M)))) ≫
                V.map (HA.map (CategoryTheory.Prod.mkHom eFv.op (𝟙 (S.functor.obj M)))) ≫
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
            DerivedCategory.Q.map w),
      ((derivedTensor_comparison.{uR, max uR uA uM} R K L hL).inv ≫
              (E.inverse.map
                      ((DerivedInternalHom.Model.adjunction (ULift.{max uR uA uM} R)).tensor.map
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
                DerivedCategory.Q.map
                    (((ModuleCat.extendRestrictScalarsAdj.{max uR uA uM}
                            f').mapHomologicalComplex (ComplexShape.up ℤ)).unit.app
                        ((((ModuleCat.restrictScalars.{max uR uA uM}
            (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ⊗ K₀) ≫
                      (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM,
                          max uR uA uM} f').map
                          ((CochainComplex.ExtendScalars.extendScalarsMonoidalIso f'
                            (((ModuleCat.restrictScalars.{max uR uA uM}
            (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) K₀).inv ≫
                            DerivedInternalHom.Model.uncurry t) ≫
                        q) ≫
                  (((ModuleCat.restrictScalars.{max uR uA uM}
                              f').mapDerivedCategoryFactors.app J ≪≫
                          @asIso _ _ _ _ (DerivedCategory.Q.map q)
                            ((DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2
                              inferInstance)).inv ≫
                    V.map eY.inv ≫ τ.inv.app M)) ≫
                  E.unitIso.inv.app (U.obj M)) ≫
            U.map (F.map (derivedTensor_comparison.{uR, max uR uA uM} R K L hL).hom)) ≫
          U.map (comparison.app (tensorComplex.{uR, max uR uA uM} K L)) =
        DerivedCategory.Q.map
            (((ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).unit.app (tensorComplex.{uR, max uR uA uM} K L)) ≫
          (ModuleCat.restrictScalars.{max uR uA uM, uR,
              uA} f).mapDerivedCategoryFactors.inv.app
            (((ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj (tensorComplex.{uR, max uR uA uM} K L))) →
    tensorBaseChangeMor.{uR, uA, uM} f F comparison D (DerivedCategory.Q.obj K)
        (DerivedCategory.Q.obj L) =
      derivedTensorBaseChange.{uR, uA, uM} f F comparison (DerivedCategory.Q.obj K)
        (DerivedCategory.Q.obj L) := by
  intro f' adj E S U V T δ τ HA dA W M K₀ X₃ YP ZZ J I hJ hI q hq n hn eX eY hunit
  have := hJ
  have := hI
  have := hq
  have := hn
  refine tensorBaseChangeMor_eq_of_monoidal_chain_level.{uR, uA, uM} f F comparison D K L hK hL
    J I q n ?_
  intro w t hw ha
  obtain ⟨hFL, e, he, h1⟩ :=
    tensorBaseChangeMor_transpose_eq_q_obj.{uR, uA, uM} f D F comparison K L hK hL
  obtain ⟨c₀, hc₀⟩ :=
    _root_.Stacks.DerivedHom.BaseChange.exists_scalarLiftExtendComparison.{uR, uA, uM} f L
  have h2 :=
    _root_.Stacks.DerivedHom.BaseChange.derivedExtensionScalarsLiftIso_hom_app_of_kFlat.{uR,
      uA, uM} f L hL F comparison c₀ hc₀
  exact hunit hFL e he c₀ hc₀ w t hw
    (comp_congr_head h1
      (fun z => E.functor.map (adj.unit.app (DerivedCategory.Q.obj K) ≫ U.map z))
      (comp_congr_slot h2 _ _
        (fun z => V.map (HA.map (CategoryTheory.Prod.mkHom (Quiver.Hom.op z)
          (𝟙 (S.functor.obj M))))) ha))

end Dualizing

end
