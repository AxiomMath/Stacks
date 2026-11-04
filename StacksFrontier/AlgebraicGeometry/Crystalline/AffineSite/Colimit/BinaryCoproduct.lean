module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineSite.Colimit.TensorEnvelope

/-!
# Binary coproducts in the affine crystalline site

Given divided power thickenings `X` and `Y` in `CRIS(C/A)`, this file builds the thickening
`tensorThickening X Y` on the divided power envelope of the pushout of `X` and `Y` along the
image of the base, with its two coprojections, and shows that it is a binary coproduct of `X`
and `Y` whose quotient is the tensor product over `C` of the two quotients.

## Main results

* `Crystalline.binaryCoproductWithTensorProductQuotient` — a binary coproduct in `CRIS(C/A)`
  whose quotient is the tensor product over `C` of the two quotients.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v w

namespace Crystalline

section BinaryCoproduct

private noncomputable def tensorThickening
    {S : AffineCrystallineSituation.{u, v}}
    (X Y : DividedPowerThickening.{u, v, w} S) :
    DividedPowerThickening.{u, v, w} S := by
  letI : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
  letI : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
  let E := tensorEnvelope X Y
  let e := tensorEnvelopeQuotientEquiv X Y
  let H : DividedPowers.DPMorphism S.A.dividedPowers E.object.dividedPowers :=
    E.structureMap.comp ((imageToPushout X Y).comp (baseToImage X Y))
  let c : S.C →+* (E.object ⧸ E.object.ideal) :=
    e.symm.toRingHom.comp (algebraMap S.C
      ((X.ring ⧸ X.ring.ideal) ⊗[S.C] (Y.ring ⧸ Y.ring.ideal)))
  refine { ring := E.object, fromBase := H,
           prime_nilpotent := ?_, toQuotient := c, commutes := ?_ }
  · have hp : IsNilpotent (S.p : imagePushout X Y) := by
      unfold imagePushout
      simpa only [map_natCast] using X.prime_nilpotent.map
        (pushout.inl (baseImageToLeft X Y) (baseImageToRight X Y)).toRingHom
    simpa only [map_natCast] using hp.map E.structureMap.toRingHom
  · refine RingHom.ext fun a => e.injective ?_
    change e (Ideal.Quotient.mk E.object.ideal (H a)) =
      e (c (algebraMap S.A S.C a))
    have hL : e (Ideal.Quotient.mk E.object.ideal (H a)) =
        algebraMap S.C ((X.ring ⧸ X.ring.ideal) ⊗[S.C]
          (Y.ring ⧸ Y.ring.ideal)) (algebraMap S.A S.C a) := by
      change e (Ideal.Quotient.mk E.object.ideal
        (E.structureMap ((imageToPushout X Y) ((baseToImage X Y) a)))) = _
      exact (tensorEnvelopeQuotientEquiv_apply_structureMap X Y _).trans
        (imagePushoutToTensor_base X Y a)
    have hR : e (c (algebraMap S.A S.C a)) =
        algebraMap S.C ((X.ring ⧸ X.ring.ideal) ⊗[S.C]
          (Y.ring ⧸ Y.ring.ideal)) (algebraMap S.A S.C a) := by
      change e (e.symm (algebraMap S.C
        ((X.ring ⧸ X.ring.ideal) ⊗[S.C]
          (Y.ring ⧸ Y.ring.ideal)) (algebraMap S.A S.C a))) = _
      exact e.apply_symm_apply _
    exact hL.trans hR.symm

private noncomputable def tensorInlRing
    {S : AffineCrystallineSituation.{u, v}}
    (X Y : DividedPowerThickening.{u, v, w} S) :
    X.ring ⟶ (tensorEnvelope X Y).object :=
  (tensorEnvelope X Y).structureMap.comp
    (pushout.inl (baseImageToLeft X Y) (baseImageToRight X Y))

private noncomputable def tensorInrRing
    {S : AffineCrystallineSituation.{u, v}}
    (X Y : DividedPowerThickening.{u, v, w} S) :
    Y.ring ⟶ (tensorEnvelope X Y).object :=
  (tensorEnvelope X Y).structureMap.comp
    (pushout.inr (baseImageToLeft X Y) (baseImageToRight X Y))

private noncomputable def tensorInlQuotientMap
    {S : AffineCrystallineSituation.{u, v}}
    (X Y : DividedPowerThickening.{u, v, w} S) :
    (X.ring ⧸ X.ring.ideal) →+*
      ((tensorEnvelope X Y).object ⧸ (tensorEnvelope X Y).object.ideal) :=
  Ideal.quotientMap (tensorEnvelope X Y).object.ideal
    (tensorInlRing X Y).toRingHom
    (Ideal.map_le_iff_le_comap.mp (tensorInlRing X Y).ideal_comp)

private lemma tensorInlQuotientMap_comp
    {S : AffineCrystallineSituation.{u, v}}
    (X Y : DividedPowerThickening.{u, v, w} S) :
    letI : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
    letI : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
    (tensorEnvelopeQuotientEquiv X Y).toRingHom.comp
      (tensorInlQuotientMap X Y) =
      Algebra.TensorProduct.includeLeftRingHom (R := S.C) := by
  let _ : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
  let _ : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
  apply Ideal.Quotient.ringHom_ext
  ext a
  show tensorEnvelopeQuotientEquiv X Y
    (Ideal.Quotient.mk (tensorEnvelope X Y).object.ideal
      ((tensorEnvelope X Y).structureMap
        ((pushout.inl (baseImageToLeft X Y) (baseImageToRight X Y)) a))) = _
  exact (tensorEnvelopeQuotientEquiv_apply_structureMap X Y _).trans
    (imagePushoutToTensor_left X Y a)

private noncomputable def tensorInrQuotientMap
    {S : AffineCrystallineSituation.{u, v}}
    (X Y : DividedPowerThickening.{u, v, w} S) :
    (Y.ring ⧸ Y.ring.ideal) →+*
      ((tensorEnvelope X Y).object ⧸ (tensorEnvelope X Y).object.ideal) :=
  Ideal.quotientMap (tensorEnvelope X Y).object.ideal
    (tensorInrRing X Y).toRingHom
    (Ideal.map_le_iff_le_comap.mp (tensorInrRing X Y).ideal_comp)

private lemma tensorInrQuotientMap_comp
    {S : AffineCrystallineSituation.{u, v}}
    (X Y : DividedPowerThickening.{u, v, w} S) :
    letI : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
    letI : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
    (tensorEnvelopeQuotientEquiv X Y).toRingHom.comp
      (tensorInrQuotientMap X Y) =
      (Algebra.TensorProduct.includeRight (R := S.C)).toRingHom := by
  let _ : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
  let _ : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
  apply Ideal.Quotient.ringHom_ext
  ext a
  show tensorEnvelopeQuotientEquiv X Y
    (Ideal.Quotient.mk (tensorEnvelope X Y).object.ideal
      ((tensorEnvelope X Y).structureMap
        ((pushout.inr (baseImageToLeft X Y) (baseImageToRight X Y)) a))) = _
  exact (tensorEnvelopeQuotientEquiv_apply_structureMap X Y _).trans
    (imagePushoutToTensor_right X Y a)

/-- The left coprojection of the base image agrees with `fromBase` on `X`. -/
private lemma baseImageToLeft_baseToImage
    {S : AffineCrystallineSituation.{u, v}}
    (X Y : DividedPowerThickening.{u, v, w} S) (a : S.A) :
    (baseImageToLeft X Y) ((baseToImage X Y) a) = X.fromBase a := rfl

/-- The right coprojection of the base image agrees with `fromBase` on `Y`. -/
private lemma baseImageToRight_baseToImage
    {S : AffineCrystallineSituation.{u, v}}
    (X Y : DividedPowerThickening.{u, v, w} S) (a : S.A) :
    (baseImageToRight X Y) ((baseToImage X Y) a) = Y.fromBase a := rfl

/-- A morphism of thickenings commutes with the maps from the base. -/
private lemma hom_fromBase
    {S : AffineCrystallineSituation.{u, v}}
    {X Z : DividedPowerThickening.{u, v, w} S} (f : X ⟶ Z) (a : S.A) :
    f.hom (X.fromBase a) = Z.fromBase a :=
  congrArg (fun h : DividedPowers.DPMorphism S.A.dividedPowers Z.ring.dividedPowers => h a)
    f.fromBase_comp

/-- The quotient equivalence of `tensorEnvelope X Y` is compatible with the maps from `C`. -/
private lemma tensorEnvelopeQuotientEquiv_toQuotient
    {S : AffineCrystallineSituation.{u, v}}
    (X Y : DividedPowerThickening.{u, v, w} S) (c : S.C) :
    letI : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
    letI : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
    tensorEnvelopeQuotientEquiv X Y ((tensorThickening X Y).toQuotient c) =
      algebraMap S.C ((X.ring ⧸ X.ring.ideal) ⊗[S.C] (Y.ring ⧸ Y.ring.ideal)) c :=
  (tensorEnvelopeQuotientEquiv X Y).apply_symm_apply _

private noncomputable def tensorInl
    {S : AffineCrystallineSituation.{u, v}}
    (X Y : DividedPowerThickening.{u, v, w} S) :
    X ⟶ tensorThickening X Y := by
  letI : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
  letI : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
  refine { hom := tensorInlRing X Y,
           fromBase_comp := ?_, toQuotient_comp := ?_ }
  · ext a
    change (tensorEnvelope X Y).structureMap
      ((pushout.inl (baseImageToLeft X Y) (baseImageToRight X Y)) (X.fromBase a)) =
      (tensorEnvelope X Y).structureMap ((imageToPushout X Y) ((baseToImage X Y) a))
    rw [← baseImageToLeft_baseToImage]
    rfl
  · refine RingHom.ext fun c => (tensorEnvelopeQuotientEquiv X Y).injective ?_
    exact (congrArg (fun f : (X.ring ⧸ X.ring.ideal) →+*
        ((X.ring ⧸ X.ring.ideal) ⊗[S.C] (Y.ring ⧸ Y.ring.ideal)) => f (X.toQuotient c))
      (tensorInlQuotientMap_comp X Y)).trans
      (tensorEnvelopeQuotientEquiv_toQuotient X Y c).symm

private noncomputable def tensorInr
    {S : AffineCrystallineSituation.{u, v}}
    (X Y : DividedPowerThickening.{u, v, w} S) :
    Y ⟶ tensorThickening X Y := by
  letI : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
  letI : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
  refine { hom := tensorInrRing X Y,
           fromBase_comp := ?_, toQuotient_comp := ?_ }
  · ext a
    change (tensorEnvelope X Y).structureMap
      ((pushout.inr (baseImageToLeft X Y) (baseImageToRight X Y)) (Y.fromBase a)) =
      (tensorEnvelope X Y).structureMap ((imageToPushout X Y) ((baseToImage X Y) a))
    rw [← baseImageToRight_baseToImage]
    exact congrArg (fun f : baseImage X Y ⟶ imagePushout X Y =>
      (tensorEnvelope X Y).structureMap (f ((baseToImage X Y) a)))
      (show baseImageToRight X Y ≫
        pushout.inr (baseImageToLeft X Y) (baseImageToRight X Y) = imageToPushout X Y from
        pushout.condition.symm)
  · refine RingHom.ext fun c => (tensorEnvelopeQuotientEquiv X Y).injective ?_
    exact (congrArg (fun f : (Y.ring ⧸ Y.ring.ideal) →+*
        ((X.ring ⧸ X.ring.ideal) ⊗[S.C] (Y.ring ⧸ Y.ring.ideal)) => f (Y.toQuotient c))
      (tensorInrQuotientMap_comp X Y)).trans
      ((Algebra.TensorProduct.algebraMap_apply' c).symm.trans
        (tensorEnvelopeQuotientEquiv_toQuotient X Y c).symm)

private lemma baseImage_pair_compatible
    {S : AffineCrystallineSituation.{u, v}}
    {X Y Z : DividedPowerThickening.{u, v, w} S}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    baseImageToLeft X Y ≫ f.hom = baseImageToRight X Y ≫ g.hom := by
  ext x
  obtain ⟨a, rfl⟩ := baseToImage_surjective X Y x
  change f.hom ((baseImageToLeft X Y) ((baseToImage X Y) a)) =
    g.hom ((baseImageToRight X Y) ((baseToImage X Y) a))
  rw [baseImageToLeft_baseToImage, baseImageToRight_baseToImage, hom_fromBase, hom_fromBase]

private noncomputable def imagePushoutCoconeMap
    {S : AffineCrystallineSituation.{u, v}}
    {X Y Z : DividedPowerThickening.{u, v, w} S}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    imagePushout X Y ⟶ Z.ring :=
  pushout.desc f.hom g.hom (baseImage_pair_compatible f g)

private noncomputable def quotientAlgHom
    {S : AffineCrystallineSituation.{u, v}}
    {X Z : DividedPowerThickening.{u, v, w} S}
    (f : X ⟶ Z) :
    letI : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
    letI : Algebra S.C (Z.ring ⧸ Z.ring.ideal) := Z.toQuotient.toAlgebra
    (X.ring ⧸ X.ring.ideal) →ₐ[S.C] (Z.ring ⧸ Z.ring.ideal) := by
  letI : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
  letI : Algebra S.C (Z.ring ⧸ Z.ring.ideal) := Z.toQuotient.toAlgebra
  exact { DividedPowerRing.quotientRingHom f.hom with
    commutes' := fun c => congrArg
      (fun k : S.C →+* (Z.ring ⧸ Z.ring.ideal) => k c) f.toQuotient_comp }

private noncomputable def tensorToTargetQuotient
    {S : AffineCrystallineSituation.{u, v}}
    {X Y Z : DividedPowerThickening.{u, v, w} S}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    letI : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
    letI : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
    letI : Algebra S.C (Z.ring ⧸ Z.ring.ideal) := Z.toQuotient.toAlgebra
    ((X.ring ⧸ X.ring.ideal) ⊗[S.C] (Y.ring ⧸ Y.ring.ideal)) →ₐ[S.C]
      (Z.ring ⧸ Z.ring.ideal) := by
  letI : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
  letI : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
  letI : Algebra S.C (Z.ring ⧸ Z.ring.ideal) := Z.toQuotient.toAlgebra
  exact Algebra.TensorProduct.lift (quotientAlgHom f) (quotientAlgHom g)
    (fun _ _ => Commute.all _ _)

private noncomputable def imagePushoutToTargetQuotient
    {S : AffineCrystallineSituation.{u, v}}
    {X Y Z : DividedPowerThickening.{u, v, w} S}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    imagePushout X Y ⟶ zeroDividedPowerRing (Z.ring ⧸ Z.ring.ideal) := by
  let h : (imagePushout X Y) →+* (Z.ring ⧸ Z.ring.ideal) :=
    (Ideal.Quotient.mk Z.ring.ideal).comp
      (imagePushoutCoconeMap f g).toRingHom
  have hh : ∀ x ∈ (imagePushout X Y).ideal, h x = 0 := fun x hx =>
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.map_le_iff_le_comap.mp (imagePushoutCoconeMap f g).ideal_comp hx)
  exact dpMorphismToBot (imagePushout X Y).dividedPowers h hh

private lemma imagePushoutToTargetQuotient_left
    {S : AffineCrystallineSituation.{u, v}}
    {X Y Z : DividedPowerThickening.{u, v, w} S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (x : X.ring) :
    (imagePushoutToTargetQuotient f g)
      ((pushout.inl (baseImageToLeft X Y) (baseImageToRight X Y)) x) =
      Ideal.Quotient.mk Z.ring.ideal (f.hom x) := by
  unfold imagePushoutToTargetQuotient
  show Ideal.Quotient.mk Z.ring.ideal
    ((imagePushoutCoconeMap f g)
      ((pushout.inl (baseImageToLeft X Y) (baseImageToRight X Y)) x)) = _
  exact congrArg (Ideal.Quotient.mk Z.ring.ideal)
    (pushoutDescLeft (baseImageToLeft X Y) (baseImageToRight X Y)
      f.hom g.hom (baseImage_pair_compatible f g) x)

private lemma imagePushoutToTargetQuotient_right
    {S : AffineCrystallineSituation.{u, v}}
    {X Y Z : DividedPowerThickening.{u, v, w} S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (y : Y.ring) :
    (imagePushoutToTargetQuotient f g)
      ((pushout.inr (baseImageToLeft X Y) (baseImageToRight X Y)) y) =
      Ideal.Quotient.mk Z.ring.ideal (g.hom y) := by
  unfold imagePushoutToTargetQuotient
  show Ideal.Quotient.mk Z.ring.ideal
    ((imagePushoutCoconeMap f g)
      ((pushout.inr (baseImageToLeft X Y) (baseImageToRight X Y)) y)) = _
  exact congrArg (Ideal.Quotient.mk Z.ring.ideal)
    (pushoutDescRight (baseImageToLeft X Y) (baseImageToRight X Y)
      f.hom g.hom (baseImage_pair_compatible f g) y)

private noncomputable def tensorToTargetDPMorphism
    {S : AffineCrystallineSituation.{u, v}}
    {X Y Z : DividedPowerThickening.{u, v, w} S}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    letI : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
    letI : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
    zeroDividedPowerRing
      ((X.ring ⧸ X.ring.ideal) ⊗[S.C] (Y.ring ⧸ Y.ring.ideal)) ⟶
    zeroDividedPowerRing (Z.ring ⧸ Z.ring.ideal) := by
  letI : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
  letI : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
  letI : Algebra S.C (Z.ring ⧸ Z.ring.ideal) := Z.toQuotient.toAlgebra
  exact dpMorphismToBot (zeroDividedPowerRing _).dividedPowers
    (tensorToTargetQuotient f g).toRingHom (by simp)

private lemma imagePushoutToTargetQuotient_comp
    {S : AffineCrystallineSituation.{u, v}}
    {X Y Z : DividedPowerThickening.{u, v, w} S}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    letI : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
    letI : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
    imagePushoutToTargetQuotient f g =
      (tensorToTargetDPMorphism f g).comp (imagePushoutToTensor X Y) := by
  let _ : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
  let _ : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
  apply pushout.hom_ext
  · ext x
    show (imagePushoutToTargetQuotient f g)
      ((pushout.inl (baseImageToLeft X Y) (baseImageToRight X Y)) x) =
      (tensorToTargetDPMorphism f g)
        ((imagePushoutToTensor X Y)
          ((pushout.inl (baseImageToLeft X Y) (baseImageToRight X Y)) x))
    calc
      _ = Ideal.Quotient.mk Z.ring.ideal (f.hom x) :=
        imagePushoutToTargetQuotient_left f g x
      _ = (tensorToTargetDPMorphism f g)
          ((Ideal.Quotient.mk X.ring.ideal x) ⊗ₜ[S.C]
            (1 : Y.ring ⧸ Y.ring.ideal)) := by
        show Ideal.Quotient.mk Z.ring.ideal (f.hom x) =
          (tensorToTargetQuotient f g)
            ((Ideal.Quotient.mk X.ring.ideal x) ⊗ₜ[S.C]
              (1 : Y.ring ⧸ Y.ring.ideal))
        simp [tensorToTargetQuotient, quotientAlgHom,
          DividedPowerRing.quotientRingHom_mk]
      _ = _ := congrArg (tensorToTargetDPMorphism f g)
        (imagePushoutToTensor_left X Y x).symm
  · ext y
    show (imagePushoutToTargetQuotient f g)
      ((pushout.inr (baseImageToLeft X Y) (baseImageToRight X Y)) y) =
      (tensorToTargetDPMorphism f g)
        ((imagePushoutToTensor X Y)
          ((pushout.inr (baseImageToLeft X Y) (baseImageToRight X Y)) y))
    calc
      _ = Ideal.Quotient.mk Z.ring.ideal (g.hom y) :=
        imagePushoutToTargetQuotient_right f g y
      _ = (tensorToTargetDPMorphism f g)
          ((1 : X.ring ⧸ X.ring.ideal) ⊗ₜ[S.C]
            (Ideal.Quotient.mk Y.ring.ideal y)) := by
        show Ideal.Quotient.mk Z.ring.ideal (g.hom y) =
          (tensorToTargetQuotient f g)
            ((1 : X.ring ⧸ X.ring.ideal) ⊗ₜ[S.C]
              (Ideal.Quotient.mk Y.ring.ideal y))
        simp [tensorToTargetQuotient, quotientAlgHom,
          DividedPowerRing.quotientRingHom_mk]
      _ = _ := congrArg (tensorToTargetDPMorphism f g)
        (imagePushoutToTensor_right X Y y).symm

private lemma imagePushoutKer_mapsToIdeal
    {S : AffineCrystallineSituation.{u, v}}
    {X Y Z : DividedPowerThickening.{u, v, w} S}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    letI : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
    letI : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
    (RingHom.ker (imagePushoutToTensor X Y).toRingHom).map
      (imagePushoutCoconeMap f g).toRingHom ≤ Z.ring.ideal := by
  let _ : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
  let _ : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
  rw [Ideal.map_le_iff_le_comap]
  intro p hp
  show (imagePushoutCoconeMap f g).toRingHom p ∈ Z.ring.ideal
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have h := congrArg
    (fun k : imagePushout X Y ⟶ zeroDividedPowerRing
      (Z.ring ⧸ Z.ring.ideal) => k p)
      (imagePushoutToTargetQuotient_comp f g)
  change Ideal.Quotient.mk Z.ring.ideal
      ((imagePushoutCoconeMap f g) p) =
    (tensorToTargetDPMorphism f g) ((imagePushoutToTensor X Y) p) at h
  have hpq : (imagePushoutToTensor X Y).toRingHom p = 0 :=
    RingHom.mem_ker.mp hp
  show Ideal.Quotient.mk Z.ring.ideal
    ((imagePushoutCoconeMap f g) p) = 0
  change Ideal.Quotient.mk Z.ring.ideal
      ((imagePushoutCoconeMap f g) p) =
    (tensorToTargetDPMorphism f g).toRingHom
      ((imagePushoutToTensor X Y).toRingHom p) at h
  rw [hpq] at h
  simpa only [map_zero] using h

private noncomputable def envelopeLift
    (A C : DividedPowerRing.{w}) (J : Ideal A)
    (hJ : A.ideal.map (RingHom.id A) ≤ J)
    (E : DividedPowerEnvelope A (RingHom.id A) J hJ)
    (a : A ⟶ C) (ha : J.map a.toRingHom ≤ C.ideal) :
    E.object ⟶ C :=
  ((E.homEquiv C a).symm
    ⟨IdealPair.Hom.ofRingHom a.toRingHom ha, IdealPair.Hom.ext_toRingHom _ _ rfl⟩).1

private lemma envelopeLift_comp_structureMap
    (A C : DividedPowerRing.{w}) (J : Ideal A)
    (hJ : A.ideal.map (RingHom.id A) ≤ J)
    (E : DividedPowerEnvelope A (RingHom.id A) J hJ)
    (a : A ⟶ C) (ha : J.map a.toRingHom ≤ C.ideal) :
    (envelopeLift A C J hJ E a ha).comp E.structureMap = a :=
  ((E.homEquiv C a).symm
    ⟨IdealPair.Hom.ofRingHom a.toRingHom ha, IdealPair.Hom.ext_toRingHom _ _ rfl⟩).2

/-- The augmentation ideal of `imagePushout X Y` lies in the kernel of `imagePushoutToTensor`. -/
private lemma imagePushout_ideal_le_ker
    {S : AffineCrystallineSituation.{u, v}}
    (X Y : DividedPowerThickening.{u, v, w} S) :
    letI : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
    letI : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
    (imagePushout X Y).ideal.map (RingHom.id _) ≤
      RingHom.ker (imagePushoutToTensor X Y).toRingHom := by
  rw [Ideal.map_id, RingHom.ker_eq_comap_bot]
  exact Ideal.map_le_iff_le_comap.mp (imagePushoutToTensor X Y).ideal_comp

private noncomputable def tensorEnvelopeLiftRing
    {S : AffineCrystallineSituation.{u, v}}
    {X Y Z : DividedPowerThickening.{u, v, w} S}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    (tensorEnvelope X Y).object ⟶ Z.ring := by
  letI : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
  letI : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
  exact envelopeLift (imagePushout X Y) Z.ring
    (RingHom.ker (imagePushoutToTensor X Y).toRingHom) (imagePushout_ideal_le_ker X Y)
    (tensorEnvelope X Y) (imagePushoutCoconeMap f g) (imagePushoutKer_mapsToIdeal f g)

private lemma tensorEnvelopeLiftRing_comp_structureMap
    {S : AffineCrystallineSituation.{u, v}}
    {X Y Z : DividedPowerThickening.{u, v, w} S}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    (tensorEnvelopeLiftRing f g).comp
      (tensorEnvelope X Y).structureMap = imagePushoutCoconeMap f g := by
  unfold tensorEnvelopeLiftRing
  exact envelopeLift_comp_structureMap _ _ _ _ _ _ _

/-- The lift of `f` and `g` to the envelope extends `imagePushoutCoconeMap f g`. -/
private lemma tensorEnvelopeLiftRing_structureMap
    {S : AffineCrystallineSituation.{u, v}}
    {X Y Z : DividedPowerThickening.{u, v, w} S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (p : imagePushout X Y) :
    (tensorEnvelopeLiftRing f g) ((tensorEnvelope X Y).structureMap p) =
      (imagePushoutCoconeMap f g) p :=
  congrArg (fun k : imagePushout X Y ⟶ Z.ring => k p)
    (tensorEnvelopeLiftRing_comp_structureMap f g)

private noncomputable def tensorEnvelopeLiftQuotientMap
    {S : AffineCrystallineSituation.{u, v}}
    {X Y Z : DividedPowerThickening.{u, v, w} S}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    ((tensorEnvelope X Y).object ⧸ (tensorEnvelope X Y).object.ideal) →+*
      (Z.ring ⧸ Z.ring.ideal) :=
  Ideal.quotientMap Z.ring.ideal (tensorEnvelopeLiftRing f g).toRingHom
    (Ideal.map_le_iff_le_comap.mp (tensorEnvelopeLiftRing f g).ideal_comp)

private lemma tensorEnvelopeLiftQuotientMap_apply
    {S : AffineCrystallineSituation.{u, v}}
    {X Y Z : DividedPowerThickening.{u, v, w} S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (p : imagePushout X Y) :
    let _ : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
    let _ : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
    let _ : Algebra S.C (Z.ring ⧸ Z.ring.ideal) := Z.toQuotient.toAlgebra
    tensorEnvelopeLiftQuotientMap f g
        (((Ideal.Quotient.mk (tensorEnvelope X Y).object.ideal).comp
          (tensorEnvelope X Y).structureMap.toRingHom) p) =
      ((tensorToTargetQuotient f g).toRingHom.comp
          (tensorEnvelopeQuotientEquiv X Y).toRingHom)
        (((Ideal.Quotient.mk (tensorEnvelope X Y).object.ideal).comp
          (tensorEnvelope X Y).structureMap.toRingHom) p) := by
  let _ : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
  let _ : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
  let _ : Algebra S.C (Z.ring ⧸ Z.ring.ideal) := Z.toQuotient.toAlgebra
  have hA := tensorEnvelopeLiftRing_structureMap f g p
  have hB := congrArg
    (fun k : imagePushout X Y ⟶ zeroDividedPowerRing
      (Z.ring ⧸ Z.ring.ideal) => k p)
      (imagePushoutToTargetQuotient_comp f g)
  change Ideal.Quotient.mk Z.ring.ideal
      ((imagePushoutCoconeMap f g) p) =
    (tensorToTargetQuotient f g) ((imagePushoutToTensor X Y) p) at hB
  have hE := tensorEnvelopeQuotientEquiv_apply_structureMap X Y p
  calc
    tensorEnvelopeLiftQuotientMap f g
        (((Ideal.Quotient.mk (tensorEnvelope X Y).object.ideal).comp
          (tensorEnvelope X Y).structureMap.toRingHom) p) =
        Ideal.Quotient.mk Z.ring.ideal
          ((tensorEnvelopeLiftRing f g)
            ((tensorEnvelope X Y).structureMap p)) := rfl
    _ = Ideal.Quotient.mk Z.ring.ideal ((imagePushoutCoconeMap f g) p) :=
      congrArg (Ideal.Quotient.mk Z.ring.ideal) hA
    _ = (tensorToTargetQuotient f g) ((imagePushoutToTensor X Y) p) := hB
    _ = _ := congrArg (tensorToTargetQuotient f g) hE.symm

private lemma tensorEnvelope_structureMap_quotient_surjective
    {S : AffineCrystallineSituation.{u, v}}
    (X Y : DividedPowerThickening.{u, v, w} S) :
    Function.Surjective
      ((Ideal.Quotient.mk (tensorEnvelope X Y).object.ideal).comp
        (tensorEnvelope X Y).structureMap.toRingHom) := by
  exact envelopeStructureQuotient_surjective (imagePushout X Y)
    (RingHom.ker (imagePushoutToTensor X Y).toRingHom) (imagePushout_ideal_le_ker X Y)
    (tensorEnvelope X Y)

private lemma tensorEnvelopeLiftQuotientMap_comp
    {S : AffineCrystallineSituation.{u, v}}
    {X Y Z : DividedPowerThickening.{u, v, w} S}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    let _ : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
    let _ : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
    let _ : Algebra S.C (Z.ring ⧸ Z.ring.ideal) := Z.toQuotient.toAlgebra
    tensorEnvelopeLiftQuotientMap f g =
      (tensorToTargetQuotient f g).toRingHom.comp
        (tensorEnvelopeQuotientEquiv X Y).toRingHom := by
  let _ : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
  let _ : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
  let _ : Algebra S.C (Z.ring ⧸ Z.ring.ideal) := Z.toQuotient.toAlgebra
  exact RingHom.ext <| (tensorEnvelope_structureMap_quotient_surjective X Y).forall.mpr
    fun p => tensorEnvelopeLiftQuotientMap_apply f g p

private noncomputable def tensorCoconeLift
    {S : AffineCrystallineSituation.{u, v}}
    {X Y Z : DividedPowerThickening.{u, v, w} S}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    tensorThickening X Y ⟶ Z := by
  letI : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
  letI : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
  letI : Algebra S.C (Z.ring ⧸ Z.ring.ideal) := Z.toQuotient.toAlgebra
  refine { hom := tensorEnvelopeLiftRing f g,
           fromBase_comp := ?_, toQuotient_comp := ?_ }
  · ext a
    exact (tensorEnvelopeLiftRing_structureMap f g _).trans
      ((pushoutDescLeft _ _ _ _ _ _).trans (hom_fromBase f a))
  · refine RingHom.ext fun c => ?_
    exact (congrArg (fun k : ((tensorEnvelope X Y).object ⧸ (tensorEnvelope X Y).object.ideal) →+*
        (Z.ring ⧸ Z.ring.ideal) => k ((tensorThickening X Y).toQuotient c))
        (tensorEnvelopeLiftQuotientMap_comp f g)).trans
      ((congrArg (tensorToTargetQuotient f g) (tensorEnvelopeQuotientEquiv_toQuotient X Y c)).trans
        ((tensorToTargetQuotient f g).commutes c))

private lemma tensorCoconeLift_inl
    {S : AffineCrystallineSituation.{u, v}}
    {X Y Z : DividedPowerThickening.{u, v, w} S}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    tensorInl X Y ≫ tensorCoconeLift f g = f := by
  apply DividedPowerThickening.Hom.ext
  ext x
  exact (tensorEnvelopeLiftRing_structureMap f g _).trans (pushoutDescLeft _ _ _ _ _ x)

private lemma tensorCoconeLift_inr
    {S : AffineCrystallineSituation.{u, v}}
    {X Y Z : DividedPowerThickening.{u, v, w} S}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    tensorInr X Y ≫ tensorCoconeLift f g = g := by
  apply DividedPowerThickening.Hom.ext
  ext y
  exact (tensorEnvelopeLiftRing_structureMap f g _).trans (pushoutDescRight _ _ _ _ _ y)

private lemma envelopeHom_ext_of_comp_structureMap
    (A C : DividedPowerRing.{w}) (J : Ideal A)
    (hJ : A.ideal.map (RingHom.id A) ≤ J)
    (E : DividedPowerEnvelope A (RingHom.id A) J hJ)
    (r s : E.object ⟶ C)
    (h : r.comp E.structureMap = s.comp E.structureMap) : r = s := by
  apply envelope_ext A (RingHom.id A) J hJ E C
    (r.comp E.structureMap) r s rfl h.symm
  have he := E.algebraMap_comp
  change E.algebraMap.toRingHom = E.structureMap.toRingHom at he
  rw [he]
  exact congrArg DividedPowers.DPMorphism.toRingHom h

private lemma tensorHom_ext
    {S : AffineCrystallineSituation.{u, v}}
    {X Y Z : DividedPowerThickening.{u, v, w} S}
    (r s : tensorThickening X Y ⟶ Z)
    (hl : tensorInl X Y ≫ r = tensorInl X Y ≫ s)
    (hr : tensorInr X Y ≫ r = tensorInr X Y ≫ s) : r = s := by
  apply DividedPowerThickening.Hom.ext
  let E := tensorEnvelope X Y
  have h : r.hom.comp E.structureMap = s.hom.comp E.structureMap := by
    refine pushout.hom_ext (f := baseImageToLeft X Y) (g := baseImageToRight X Y) ?_ ?_
    · ext x
      exact congrArg (fun k : X ⟶ Z => k.hom x) hl
    · ext y
      exact congrArg (fun k : Y ⟶ Z => k.hom y) hr
  exact envelopeHom_ext_of_comp_structureMap
    (imagePushout X Y) Z.ring
    (RingHom.ker (imagePushoutToTensor X Y).toRingHom) (imagePushout_ideal_le_ker X Y)
    E r.hom s.hom h

/-- Two divided power thickenings have a binary coproduct, and the quotient of that coproduct is
canonically the tensor product over `C` of their quotients. -/
public theorem binaryCoproductWithTensorProductQuotient
    {S : AffineCrystallineSituation.{u, v}}
    (X Y : DividedPowerThickening.{u, v, w} S) :
    ∃ (t : BinaryCofan X Y) (_ht : IsColimit t),
      letI : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
      letI : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
      letI : Algebra S.C (t.pt.ring ⧸ t.pt.ring.ideal) := t.pt.toQuotient.toAlgebra
      ∃ e : (t.pt.ring ⧸ t.pt.ring.ideal) ≃ₐ[S.C]
          (X.ring ⧸ X.ring.ideal) ⊗[S.C] (Y.ring ⧸ Y.ring.ideal),
        (∀ x : X.ring ⧸ X.ring.ideal,
            e (DividedPowerRing.quotientRingHom t.inl.hom x) =
              x ⊗ₜ[S.C] (1 : Y.ring ⧸ Y.ring.ideal)) ∧
          (∀ y : Y.ring ⧸ Y.ring.ideal,
            e (DividedPowerRing.quotientRingHom t.inr.hom y) =
              (1 : X.ring ⧸ X.ring.ideal) ⊗ₜ[S.C] y) := by
  let D := tensorThickening X Y
  let t : BinaryCofan X Y := BinaryCofan.mk (tensorInl X Y) (tensorInr X Y)
  refine ⟨t, ?_, ?_⟩
  · exact BinaryCofan.IsColimit.mk t (fun f g => tensorCoconeLift f g)
      (fun f g => tensorCoconeLift_inl f g) (fun f g => tensorCoconeLift_inr f g)
      fun f g m hm₁ hm₂ => tensorHom_ext m (tensorCoconeLift f g)
        (hm₁.trans (tensorCoconeLift_inl f g).symm) (hm₂.trans (tensorCoconeLift_inr f g).symm)
  · let _ : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
    let _ : Algebra S.C (Y.ring ⧸ Y.ring.ideal) := Y.toQuotient.toAlgebra
    let _ : Algebra S.C (D.ring ⧸ D.ring.ideal) := D.toQuotient.toAlgebra
    let eR := tensorEnvelopeQuotientEquiv X Y
    let e : (D.ring ⧸ D.ring.ideal) ≃ₐ[S.C]
        (X.ring ⧸ X.ring.ideal) ⊗[S.C]
          (Y.ring ⧸ Y.ring.ideal) := by
      exact { eR with commutes' := tensorEnvelopeQuotientEquiv_toQuotient X Y }
    refine ⟨e, ?_, ?_⟩
    · exact fun x => congrArg (fun k : (X.ring ⧸ X.ring.ideal) →+*
        ((X.ring ⧸ X.ring.ideal) ⊗[S.C] (Y.ring ⧸ Y.ring.ideal)) => k x)
        (tensorInlQuotientMap_comp X Y)
    · exact fun y => congrArg (fun k : (Y.ring ⧸ Y.ring.ideal) →+*
        ((X.ring ⧸ X.ring.ideal) ⊗[S.C] (Y.ring ⧸ Y.ring.ideal)) => k y)
        (tensorInrQuotientMap_comp X Y)

end BinaryCoproduct

end Crystalline
