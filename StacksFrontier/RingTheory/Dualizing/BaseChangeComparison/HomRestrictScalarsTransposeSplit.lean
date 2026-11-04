module

public import StacksFrontier.Homology.HomComplex.DerivedAdjunctionHomMapTail
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.HomRestrictScalarsTransposeCollapse
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorHomTransposeScalarLiftEvaluation

/-!
# The uncurried inverse component of [stacks 0E1W] at the keystone's pair, split for absorption

`Stacks.DerivedHom.BaseChange.homEquiv_derivedHomRestrictScalarsNatIso_inv_app_tensorKFlat_q_map`
values the [stacks 0A63] transpose of the inverse component of [stacks 0E1W] at the keystone's
K-flat pair with the chain-level map of [stacks 0E1W] localized and nothing around it, between a
prefix of five comparison factors and a tail of three.

`Dualizing.eq_derivedTensorBaseChange_iff_scalarLiftEvaluation` needs that value in a particular
shape: a prefix, one fixed-universe transpose, and a tail which is the internal-Hom bifunctor
applied to a pair.  This file puts it in that shape by two substitutions.

The first is
`Stacks.DerivedHom.BaseChange.Q_map_homComplexChangeOfRingsMap_scalarLift_evaluation`: the
localized chain map **is** a transpose, of the restricted evaluation of the internal Hom complex
over `ULift A`, followed by the K-injective Hom comparison
`StacksDraft.DerivedHom.DerivedHomData.homIso`.  The second is that the comparison so produced
cancels against the first factor of the tail -- `Stacks.DerivedHom.BaseChange.homModelIso` at a
reflexive Hom-source presentation is that same comparison followed by the internal Hom of the
Hom-target presentation, which is
`Stacks.DerivedHom.BaseChange.homIso_hom_comp_homModelIso_inv`.  The three remaining tail factors
are then all the internal-Hom bifunctor at a pair, and merge into one by
`StacksDraft.DerivedHom.DerivedHomAdjunction.hom_map_comp_hom_map`.

What comes out is the whole tail as `hom.map (lam.op, rho)` with `lam` the K-flat presentation
`Stacks.DerivedHom.BaseChange.scalarLiftQObjIso` of the Hom-source and `rho` the composite of the
K-injective presentation of the Hom-target with the transported restriction comparison -- which is
exactly the data
`Dualizing.tensorBaseChangeMor_eq_iff_scalarLiftEvaluation` asks for.

**What is not done here.**  No tag is registered and no caveat is lifted.  Both hypotheses of
`Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` remain open, and in particular
the comparison identity `h` is untouched; its frontier remains
`Dualizing.tensorComparisonCompatibility_of_kFlat_tail`.  What this file changes is the shape of
one factor of the other hypothesis.

## Main results

* `Stacks.DerivedHom.BaseChange.homIso_hom_comp_homModelIso_inv` -- the K-injective Hom comparison
  cancels against `Stacks.DerivedHom.BaseChange.homModelIso` at a reflexive Hom-source
  presentation, leaving the internal Hom of the Hom-target presentation.
* `Stacks.DerivedHom.BaseChange.comp_homModelIso_inv_of_eq_comp_homIso_hom` -- the same
  cancellation read on a morphism known to factor through that comparison, which is how the
  keystone's value presents it.
* `Stacks.DerivedHom.BaseChange.homRestrictSource_map_eq` -- the Hom-source functor of the
  change-of-rings comparison is the internal-Hom bifunctor with restriction of scalars in the
  covariant variable.
* `Stacks.DerivedHom.BaseChange.homEquiv_derivedHomRestrictScalarsNatIso_inv_app_tensorKFlat_split`
  -- the same value as `…_tensorKFlat_q_map`, in the shape
  `Dualizing.eq_derivedTensorBaseChange_iff_scalarLiftEvaluation` asks for: a prefix of four
  factors, one fixed-universe transpose of the restricted evaluation, and a tail which is the
  internal-Hom bifunctor at a pair.

## Implementation notes

The substitution is a single `congrArg` whose motive stops at the transposed morphism, so neither
the old nor the new value of that morphism has to be written out inside the proof; what is left is
an equation between the two, closed by
`StacksDraft.DerivedHom.DerivedHomAdjunction.comp_homEquiv_symm_comp_nested_hom_map` at the
nesting the value has.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory StacksDraft.DerivedHom
open CochainComplex.DerivedTensor
open CochainComplex.DerivedExtensionScalars
open CochainComplex.ExtendScalars

attribute [local instance] HasDerivedCategory.standard

universe uR uA uM

namespace Stacks.DerivedHom.BaseChange

/-- **The K-injective Hom comparison cancels against `homModelIso` at a reflexive Hom-source
presentation.**

`Stacks.DerivedHom.BaseChange.homModelIso` is the internal-Hom bifunctor applied to the two
presentations followed by the K-injective comparison
`StacksDraft.DerivedHom.DerivedHomData.homIso`, so at a reflexive presentation of the Hom-source
its inverse is that comparison's inverse followed by the internal Hom of the inverse presentation
of the Hom-target.  Composing with the comparison itself leaves the latter alone. -/
@[reassoc] public theorem homIso_hom_comp_homModelIso_inv {R : Type uR} [CommRing R]
    {Y : DerivedCategory (ModuleCat.{uR} R)} (K I : CochainComplex (ModuleCat.{uR} R) ℤ)
    [I.IsKInjective] (eI : Y ≅ DerivedCategory.Q.obj I) :
    ((DerivedInternalHom.Model.adjunction R).homIso K I).hom ≫
        (homModelIso K I (Iso.refl (DerivedCategory.Q.obj K)) eI).inv =
      (DerivedInternalHom.Model.hom R).map
        (((𝟙 (DerivedCategory.Q.obj K)).op, eI.inv) :
          ((Opposite.op (DerivedCategory.Q.obj K), DerivedCategory.Q.obj I) :
            (DerivedCategory (ModuleCat.{uR} R))ᵒᵖ × DerivedCategory (ModuleCat.{uR} R)) ⟶
            (Opposite.op (DerivedCategory.Q.obj K), Y)) := by
  rw [homModelIso, Iso.trans_inv, Functor.mapIso_inv, Iso.hom_inv_id_assoc]
  rfl

/-- **The Hom-source functor of the change-of-rings comparison is the internal-Hom bifunctor with
restriction of scalars in the covariant variable.**

`Stacks.DerivedHom.BaseChange.homRestrictSource` is the identity on the contravariant variable and
restriction of scalars on the covariant one, followed by the internal-Hom bifunctor, so a morphism
of it is the bifunctor at the same contravariant morphism and the restriction of the covariant
one. -/
public theorem homRestrictSource_map_eq {R A : Type uR} [CommRing R] [CommRing A] (g : R →+* A)
    {X X' : DerivedCategory (ModuleCat.{uR} R)} {Y Y' : DerivedCategory (ModuleCat.{uR} A)}
    (u : X' ⟶ X) (w : Y ⟶ Y') :
    letI : (ModuleCat.restrictScalars.{uR, uR, uR} g).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{uR, uR, uR} g).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{uR, uR, uR} g).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{uR, uR, uR} g).isLeftAdjoint
    (homRestrictSource g).map (CategoryTheory.Prod.mkHom u.op w) =
      (DerivedInternalHom.Model.hom R).map (CategoryTheory.Prod.mkHom u.op
        ((ModuleCat.restrictScalars.{uR, uR, uR} g).mapDerivedCategory.map w)) :=
  rfl

/-- **A morphism known to factor through the K-injective Hom comparison, followed by
`homModelIso` at a reflexive Hom-source presentation.**

`Stacks.DerivedHom.BaseChange.homIso_hom_comp_homModelIso_inv` composed on the left: a morphism
presented as `w` followed by the comparison becomes `w` followed by the internal Hom of the
inverse presentation of the Hom-target.  This is the form the keystone's value is consumed in,
where `w` is the fixed-universe transpose of the restricted evaluation. -/
public theorem comp_homModelIso_inv_of_eq_comp_homIso_hom {R : Type uR} [CommRing R]
    {X Y : DerivedCategory (ModuleCat.{uR} R)} (K I : CochainComplex (ModuleCat.{uR} R) ℤ)
    [I.IsKInjective] (u : X ⟶ DerivedCategory.Q.obj (CochainComplex.HomComplexR R K I))
    (w : X ⟶ (DerivedInternalHom.Model.hom R).obj
      (Opposite.op (DerivedCategory.Q.obj K), DerivedCategory.Q.obj I))
    (h : u = w ≫ ((DerivedInternalHom.Model.adjunction R).homIso K I).hom)
    (eI : Y ≅ DerivedCategory.Q.obj I) :
    u ≫ (homModelIso K I (Iso.refl (DerivedCategory.Q.obj K)) eI).inv =
      w ≫ (DerivedInternalHom.Model.hom R).map
        (((𝟙 (DerivedCategory.Q.obj K)).op, eI.inv) :
          ((Opposite.op (DerivedCategory.Q.obj K), DerivedCategory.Q.obj I) :
            (DerivedCategory (ModuleCat.{uR} R))ᵒᵖ × DerivedCategory (ModuleCat.{uR} R)) ⟶
            (Opposite.op (DerivedCategory.Q.obj K), Y)) := by
  rw [h, Category.assoc, homIso_hom_comp_homModelIso_inv]

/-- **The uncurried inverse component of [stacks 0E1W] at the keystone's pair, split for
absorption.**

`Stacks.DerivedHom.BaseChange.homEquiv_derivedHomRestrictScalarsNatIso_inv_app_tensorKFlat_q_map`
with the localized chain map of [stacks 0E1W] replaced by its value
`Stacks.DerivedHom.BaseChange.Q_map_homComplexChangeOfRingsMap_scalarLift_evaluation` and the
K-injective Hom comparison it produces cancelled into the tail.

The result is the shape `Dualizing.eq_derivedTensorBaseChange_iff_scalarLiftEvaluation` asks for:
a prefix of four factors -- the comparison `eF` of the two derived extensions of scalars, the two
K-flat/K-injective presentations through the change-of-rings Hom comparison, one `homModelIso` and
one component of `CategoryTheory.Functor.mapDerivedCategoryFactors` -- then one fixed-universe
[stacks 0A63] transpose of the restricted evaluation of the internal Hom complex over `ULift A`,
then the internal-Hom bifunctor at the pair `(eX.hom, rho)` with `rho` the K-injective
presentation of the Hom-target followed by the transported restriction comparison `tau`. -/
public theorem homEquiv_derivedHomRestrictScalarsNatIso_inv_app_tensorKFlat_split
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A) :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).Additive :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).left_adjoint_additive
    ∀ (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
      DerivedCategory (ModuleCat.{max uR uA uM} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]
    (K L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (hK : IsKFlat.{uR, max uR uA uM} K) (hL : IsKFlat.{uR, max uR uA uM} L),
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
    let a' := @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction
      _ _ _ _ f' _ _ T.B T.alphaB T.isLeftDerivedB
    let δ : S.inverse ⋙ U ≅ V ⋙ E.inverse := scalarRestrictionIso.{uR, uA, uM} f
    let τ : U ⋙ E.functor ≅ S.functor ⋙ V :=
      Iso.compInverseIso (H := E.symm)
        ((Iso.inverseCompIso (G := S.symm) δ.symm).symm ≪≫
          (Functor.associator _ _ _).symm)
    let eF : E.functor ⋙ T.B ≅ F ⋙ S.functor :=
      (E.toAdjunction.comp a').leftAdjointUniq ((a.comp S.toAdjunction).ofNatIsoRight δ)
    let HR := DerivedInternalHom.Model.hom (ULift.{max uR uA uM} R)
    let HA := DerivedInternalHom.Model.hom (ULift.{max uR uA uM} A)
    let M := F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
      max uR uA uM + 1} R).tensor.obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L))
    let X₃ := ((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
            ((CochainComplex.DerivedTensor.extensionOfScalarsCochain.{uR, uA,
              max uR uA uM} f).obj (CochainComplex.DerivedTensor.tensorComplex.{uR,
                max uR uA uM} K L))
    let K₀ := ((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L
    ∀ (J : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)) ℤ)
      (I : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ℤ)
      [J.IsKInjective] [I.IsKInjective]
      (q : (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM}
        f').obj J ⟶ I) [QuasiIso q]
      (n : X₃ ⟶ J) [QuasiIso n],
    letI : IsIso (T.alphaB.app K₀) :=
      isIso_extendScalarsCounit_app_of_kFlat f' T.B T.alphaB K₀
        (kFlat_scalarLift.{uR, max uR uA uM} R L hL)
    letI := quasiIso_homComplexChangeOfRingsMap_of_kFlat f' K₀ J I q T.B T.alphaB
      (kFlat_scalarLift.{uR, max uR uA uM} R L hL)
    let eX := scalarLiftQObjIso.{uR, max uR uA uM} R L
    let eY := tensorKFlatKInjectiveLift.{uR, uA, uM} f F comparison K L hK hL J n
    let Z := CochainComplex.HomComplexR (ULift.{max uR uA uM} A)
      ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM} f').obj K₀) J
    ∀ (c₁ : E.functor.obj (E.inverse.obj (V.obj (HA.obj
            (Opposite.op (S.functor.obj (F.obj (DerivedCategory.Q.obj L))),
              S.functor.obj M)))) ⟶
          V.obj (HA.obj (Opposite.op (S.functor.obj (F.obj (DerivedCategory.Q.obj L))),
            S.functor.obj M)))
    (c₂ : E.inverse.obj (E.functor.obj (U.obj M)) ⟶ U.obj M)
    (_hc₁ : (derivedScalarEquivalence.{uR, max uR uA uM,
          max uR uA uM + 1} R).symm.toAdjunction.counit.app
        (V.obj (HA.obj (Opposite.op (S.functor.obj (F.obj (DerivedCategory.Q.obj L))),
          S.functor.obj M))) = c₁)
    (_hc₂ : (derivedScalarEquivalence.{uR, max uR uA uM,
          max uR uA uM + 1} R).toAdjunction.counit.app (U.obj M) = c₂),
    (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv
        (U.obj (S.inverse.obj (HA.obj
          (Opposite.op (S.functor.obj (F.obj (DerivedCategory.Q.obj L))), S.functor.obj M))))
        (DerivedCategory.Q.obj L) (U.obj M)
        ((derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F comparison).inv.app
          (Opposite.op (DerivedCategory.Q.obj L), M)) =
      E.inverse.map
          ((DerivedInternalHom.Model.tensor (ULift.{max uR uA uM} R)).map
              ((E.functor.map (δ.hom.app (HA.obj
                      (Opposite.op (S.functor.obj (F.obj (DerivedCategory.Q.obj L))),
                        S.functor.obj M))) ≫
                  c₁,
                𝟙 (E.functor.obj (DerivedCategory.Q.obj L))) :
                  ((E.functor.obj (U.obj (S.inverse.obj (HA.obj
                        (Opposite.op (S.functor.obj (F.obj (DerivedCategory.Q.obj L))),
                          S.functor.obj M)))),
                      E.functor.obj (DerivedCategory.Q.obj L)) :
                    DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ×
                      DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R))) ⟶
                    (V.obj (HA.obj
                        (Opposite.op (S.functor.obj (F.obj (DerivedCategory.Q.obj L))),
                          S.functor.obj M)),
                      E.functor.obj (DerivedCategory.Q.obj L))) ≫
            DerivedInternalHom.Model.homEquiv
              (V.obj (HA.obj (Opposite.op (S.functor.obj (F.obj (DerivedCategory.Q.obj L))),
                S.functor.obj M)))
              (E.functor.obj (DerivedCategory.Q.obj L)) (E.functor.obj (U.obj M))
              ((V.map (HA.map (CategoryTheory.Prod.mkHom
                    (eF.hom.app (DerivedCategory.Q.obj L)).op (𝟙 (S.functor.obj M)))) ≫
                  (homRestrictTarget f' T.B).map
                      (CategoryTheory.Prod.mkHom eX.inv.op eY.hom) ≫
                    V.map (homModelIso ((CochainComplex.extendScalarsLarge.{max uR uA uM,
                          max uR uA uM, max uR uA uM} f').obj K₀) J
                        (asIso (T.alphaB.app K₀)) (Iso.refl _)).hom ≫
                      ((ModuleCat.restrictScalars.{max uR uA uM}
                          f').mapDerivedCategoryFactors.app Z).hom) ≫
                (DerivedInternalHom.Model.homEquiv
                      (DerivedCategory.Q.obj ((CochainComplex.restrictScalarsLarge.{max uR uA uM,
                        max uR uA uM, max uR uA uM} f').obj Z))
                      (DerivedCategory.Q.obj K₀) (DerivedCategory.Q.obj I)).symm
                    (((DerivedInternalHom.Model.adjunction
                            (ULift.{max uR uA uM} R)).tensorIso
                          ((CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM,
                            max uR uA uM} f').obj Z) K₀
                          (kFlat_scalarLift.{uR, max uR uA uM} R L hL)).hom ≫
                      DerivedCategory.Q.map
                        ((𝟙 ((CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM,
                              max uR uA uM} f').obj Z) ⊗ₘ
                            ((ModuleCat.extendRestrictScalarsAdj.{max uR uA uM}
                              f').mapHomologicalComplex (ComplexShape.up ℤ)).unit.app K₀) ≫
                          restrictScalarsLaxTensor f' Z
                              ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM,
                                max uR uA uM} f').obj K₀) ≫
                            (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM,
                                max uR uA uM} f').map
                                (DerivedInternalHom.Model.evaluationMor
                                  ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM,
                                    max uR uA uM} f').obj K₀) J) ≫ q)) ≫
                  HR.map (CategoryTheory.Prod.mkHom eX.hom.op
                    (((ModuleCat.restrictScalars.{max uR uA uM}
                            f').mapDerivedCategoryFactors.app J ≪≫
                          @asIso _ _ _ _ (DerivedCategory.Q.map q)
                            ((DerivedCategory.isIso_Q_map_iff_quasiIso _
                              q).2 inferInstance)).inv ≫
                      V.map eY.inv ≫ τ.inv.app M)))) ≫
        c₂ := by
  intro F comparison hF K L hK hL a E S f' U V T a' δ τ eF HR HA M X₃ K₀ J I hJ hI q hq n hn
    eX eY Z c₁ c₂ hc₁ hc₂
  refine (homEquiv_derivedHomRestrictScalarsNatIso_inv_app_tensorKFlat_q_map.{uR, uA, uM} f F
    comparison K L hK hL J I q n c₁ c₂ hc₁ hc₂).trans ?_
  congr 4
  have : IsIso (T.alphaB.app K₀) :=
    isIso_extendScalarsCounit_app_of_kFlat f' T.B T.alphaB K₀
      (kFlat_scalarLift.{uR, max uR uA uM} R L hL)
  refine Eq.trans (congrArg (fun z =>
          (V.map (HA.map (CategoryTheory.Prod.mkHom
              (eF.hom.app (DerivedCategory.Q.obj L)).op (𝟙 (S.functor.obj M)))) ≫
            ((homRestrictTarget f' T.B).map
                  (CategoryTheory.Prod.mkHom eX.inv.op eY.hom) ≫
                (V.map (homModelIso ((CochainComplex.extendScalarsLarge.{max uR uA uM,
                        max uR uA uM, max uR uA uM} f').obj K₀) J
                      (asIso (T.alphaB.app K₀)) (Iso.refl _)).hom ≫
                    ((ModuleCat.restrictScalars.{max uR uA uM}
                        f').mapDerivedCategoryFactors.app Z).hom ≫
                      z) ≫
                  (homRestrictSource f').map
                    (CategoryTheory.Prod.mkHom eX.hom.op eY.inv)) ≫
              HR.map (CategoryTheory.Prod.mkHom
                (𝟙 (Opposite.op (E.functor.obj (DerivedCategory.Q.obj L))))
                (τ.inv.app M))))
    (comp_homModelIso_inv_of_eq_comp_homIso_hom K₀ I _ _
      (Q_map_homComplexChangeOfRingsMap_scalarLift_evaluation.{uR, uA, uM} f L hL J I q)
      _)) ?_
  exact (DerivedInternalHom.Model.adjunction
    (ULift.{max uR uA uM} R)).toDerivedHomAdjunction.comp_homEquiv_symm_comp_nested_hom_map
    _ _ _ _ _ _ eX.hom _ _ _ _ _ rfl (homRestrictSource_map_eq f' eX.hom eY.inv) rfl

end Stacks.DerivedHom.BaseChange

end
