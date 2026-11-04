module

public import StacksFrontier.Homology.HomComplex.DerivedAdjunctionModelBridge
public import StacksFrontier.Homology.HomComplex.RHom.ScalarTransportReconciliation
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorHomTransposeScalarLift

/-!
# The keystone's model comparison, read in the [stacks 0A63] bundle over the ring

`Stacks.DerivedHom.BaseChange.derivedHomChangeOfRingsModelIso_hom_scalarLift_transpose` evaluates
the representative model comparison of [stacks 0E1W] at the keystone's contravariant complex with
no Hom-complex change-of-rings map left in it — but every [stacks 0A63] factor of that value is
taken in the model bundle `StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction` at the
lifted ring `ULift R`, because that is the bundle whose K-flat and K-injective comparisons
`DerivedHomData.tensorIso` and `DerivedHomData.homIso` exist.

The other half of the keystone speaks the other bundle.
`Dualizing.tensorBaseChangeMor_comp_eq_q_obj` states `μ'` in
`StacksDraft.DerivedHom.derivedHomAdjunctionOverRing`, the bundle of [stacks 0A63] on `D(R)` and
`D(A)` themselves.  The two are not independent — the second is *defined* as the transport of the
first along `StacksDraft.DerivedHom.derivedScalarEquivalence` — and
`StacksFrontier.Homology.HomComplex.DerivedAdjunctionModelBridge` carries transposes across.

This file applies that bridge at the keystone's data.  Its content is one rewrite; what it buys
is that the `ν` side and the `μ'` side are now stated in *one* [stacks 0A63] bundle.

**What is not done here.**  The keystone equation `ν ≫ μ' = 𝟙` of
`Dualizing.tensorBaseChangeMor_eq_iff_section_comp` is not proved and no caveat is lifted.

## Main results

* `Stacks.DerivedHom.BaseChange.derivedHomChangeOfRingsModelIso_hom_scalarLift_overRing` —
  **the bundle bridge at the keystone's data**: the scalar transport of the representative model
  comparison of [stacks 0E1W], with its two [stacks 0A63] factors replaced by
  `StacksDraft.DerivedHom.derivedHomModelIso` and the inverted transpose of
  `StacksDraft.DerivedHom.derivedHomAdjunctionOverRing R`.
* `Stacks.DerivedHom.BaseChange.derivedHomChangeOfRingsModelIso_hom_scalarLift_overRing'` — the
  same with the scalar transport spelled as the inverse of
  `Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence`, which is how it occurs in
  `Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_hom_app_tensorKFlat`.
* `Stacks.DerivedHom.BaseChange.derivedHomModelIso_inv_comp_inv_homEquiv_symm_scalarEquivalence`
  — the inverted bridge of
  `StacksDraft.DerivedHom.derivedHomModelIso_inv_comp_inv_homEquiv_symm` restated with the
  scalar transport spelled as the inverse of
  `Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence`, which is the spelling the
  component of [stacks 0E1W] is written in, so that the substitution can be made at the use
  site rather than by duplicating a hundred-line statement.

## Implementation notes

`StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction (ULift.{v} R)` and
`StacksDraft.DerivedHom.derivedHomAdjunctionULift (R := R)` are the same term — both are
reducible abbreviations of `StacksDraft.DerivedHom.derivedHomAdjunction` at the lifted ring —
but they are *spelled* differently, and `rw` matches syntactically.  The bridge is therefore
restated as a local `have` in the keystone's spelling, where it is accepted by definitional
unfolding, before being rewritten with.

The scalar transport is written with `StacksDraft.DerivedHom.derivedScalarEquivalence`, the
equivalence the bundle over the ring is conjugated along.  The component of [stacks 0E1W] in
`Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_hom_app_tensorKFlat` writes the
same functor as the *inverse* of
`Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence`, the two being equal on the
nose by `Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence_inverse`.

At that spelling, instance search does not find the invertibility of the transported transpose:
`StacksDraft.DerivedHom.isIso_homEquiv_symm_derivedTensorModelIso` is not found there, and neither
is a copy of it declared with the conclusion written in that spelling, so `inv` cannot even be
elaborated.
`Stacks.DerivedHom.BaseChange.derivedHomModelIso_inv_comp_inv_homEquiv_symm_scalarEquivalence`
therefore passes the instance explicitly, through `@CategoryTheory.inv`; since `IsIso` is a
proposition this is the same morphism, and `rw` matches it against a synthesized occurrence.

No `@[stacks]` attribute is placed here: this file transports one identity between two readings
of one bundle, and covers no tag.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory StacksDraft.DerivedHom
open CochainComplex.DerivedTensor
open CochainComplex.ExtendScalars

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Dualizing.extendScalarsAdditiveOfRingHom

universe uR uA uM

namespace Stacks.DerivedHom.BaseChange

/-- **The keystone's model comparison of [stacks 0E1W], read in the [stacks 0A63] bundle over
`R`.**  This is
`Stacks.DerivedHom.BaseChange.derivedHomChangeOfRingsModelIso_hom_scalarLift_transpose`
transported along `StacksDraft.DerivedHom.derivedScalarEquivalence`, the equivalence
`StacksDraft.DerivedHom.derivedHomAdjunctionOverRing` is defined by conjugating along.

The two factors of the value that lived in the model bundle at `ULift R` — the K-injective
representation `DerivedHomData.homIso` of derived internal Hom and the inverted [stacks 0A63]
transpose — have become `StacksDraft.DerivedHom.derivedHomModelIso` and the inverted transpose of
`StacksDraft.DerivedHom.derivedHomAdjunctionOverRing R`, which is the bundle
`Dualizing.tensorBaseChangeMor_comp_eq_q_obj` states the other half of the keystone in.  The
remaining factors are localization comparisons and representation isomorphisms
`Stacks.DerivedHom.BaseChange.homModelIso`, which no bundle enters. -/
theorem derivedHomChangeOfRingsModelIso_hom_scalarLift_overRing
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
    (L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (hL : IsKFlat.{uR, max uR uA uM} L) :
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    let T := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings f'
      (HomologicalComplex.zero : CochainComplex (ModuleCat.{max uR uA uM}
        (ULift.{max uR uA uM} A)) ℤ)
    let K₀ := ((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L
    ∀ (J : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)) ℤ)
      (I : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ℤ)
      [J.IsKInjective] [I.IsKInjective]
      (q : (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM}
        f').obj J ⟶ I) [QuasiIso q],
    letI : IsIso (T.alphaB.app K₀) :=
      isIso_extendScalarsCounit_app_of_kFlat f' T.B T.alphaB K₀
        (kFlat_scalarLift.{uR, max uR uA uM} R L hL)
    letI := quasiIso_homComplexChangeOfRingsMap_of_kFlat f' K₀ J I q T.B T.alphaB
      (kFlat_scalarLift.{uR, max uR uA uM} R L hL)
    let adj := (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').mapHomologicalComplex
      (ComplexShape.up ℤ)
    let Z := CochainComplex.HomComplexR (ULift.{max uR uA uM} A)
      ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM} f').obj K₀) J
    let P := (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM}
      f').obj Z
    let W := adj.homEquiv (P ⊗ K₀) J
        ((extendScalarsMonoidalIso f' P K₀).inv ≫
          DerivedInternalHom.Model.uncurry (adj.counit.app Z)) ≫ q
    letI : IsIso ((DerivedInternalHom.Model.homEquiv (DerivedCategory.Q.obj P)
        (DerivedCategory.Q.obj K₀) (DerivedCategory.Q.obj I)).symm
          (((DerivedInternalHom.Model.adjunction (ULift.{max uR uA uM} R)).tensorIso P K₀
              (kFlat_scalarLift.{uR, max uR uA uM} R L hL)).hom ≫
            DerivedCategory.Q.map W)) :=
      Stacks.DerivedHom.BaseChangeIso.isIso_homEquiv_symm_tensorIso f' K₀ J I q
        (kFlat_scalarLift.{uR, max uR uA uM} R L hL)
    letI : IsIso (((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv
        ((derivedScalarEquivalence.{uR, max uR uA uM, max uR uA uM + 1} R).functor.obj
          (DerivedCategory.Q.obj P))
        ((derivedScalarEquivalence.{uR, max uR uA uM, max uR uA uM + 1} R).functor.obj
          (DerivedCategory.Q.obj K₀))
        ((derivedScalarEquivalence.{uR, max uR uA uM, max uR uA uM + 1} R).functor.obj
          (DerivedCategory.Q.obj I))).symm
      ((derivedTensorModelIso.{uR, max uR uA uM, max uR uA uM + 1} R P K₀
            (kFlat_scalarLift.{uR, max uR uA uM} R L hL)).hom ≫
        (derivedScalarEquivalence.{uR, max uR uA uM, max uR uA uM + 1} R).functor.map
          (DerivedCategory.Q.map W))) :=
      isIso_homEquiv_symm_derivedTensorModelIso.{uR, max uR uA uM, max uR uA uM + 1} P K₀ I
        (kFlat_scalarLift.{uR, max uR uA uM} R L hL) W
    (derivedScalarEquivalence.{uR, max uR uA uM, max uR uA uM + 1} R).functor.map
        (derivedHomChangeOfRingsModelIso f' T.B T.alphaB K₀ J I q
          (kFlat_scalarLift.{uR, max uR uA uM} R L hL)).hom =
      (derivedScalarEquivalence.{uR, max uR uA uM, max uR uA uM + 1} R).functor.map
          (homModelIso K₀ I (Iso.refl _)
            ((ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategoryFactors.app J ≪≫
              @asIso _ _ _ _ (DerivedCategory.Q.map q)
                ((DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2 inferInstance))).hom ≫
        (derivedHomModelIso.{uR, max uR uA uM, max uR uA uM + 1} R K₀ I).inv ≫
          inv (((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv
              ((derivedScalarEquivalence.{uR, max uR uA uM, max uR uA uM + 1} R).functor.obj
                (DerivedCategory.Q.obj P))
              ((derivedScalarEquivalence.{uR, max uR uA uM, max uR uA uM + 1} R).functor.obj
                (DerivedCategory.Q.obj K₀))
              ((derivedScalarEquivalence.{uR, max uR uA uM, max uR uA uM + 1} R).functor.obj
                (DerivedCategory.Q.obj I))).symm
            ((derivedTensorModelIso.{uR, max uR uA uM, max uR uA uM + 1} R P K₀
                  (kFlat_scalarLift.{uR, max uR uA uM} R L hL)).hom ≫
              (derivedScalarEquivalence.{uR, max uR uA uM, max uR uA uM + 1} R).functor.map
                (DerivedCategory.Q.map W))) ≫
            (derivedScalarEquivalence.{uR, max uR uA uM, max uR uA uM + 1} R).functor.map
                (((ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategoryFactors.app
                    (CochainComplex.HomComplexR (ULift.{max uR uA uM} A)
                      ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM,
                        max uR uA uM} f').obj K₀) J)).inv ≫
                  (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory.map
                    (homModelIso ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM,
                        max uR uA uM} f').obj K₀) J
                      (asIso (T.alphaB.app K₀)) (Iso.refl _)).inv) := by
  intro f' T K₀ J I hJ hI q hq adj Z P W
  have := hJ
  have := hI
  have := hq
  let : IsIso (T.alphaB.app K₀) :=
    isIso_extendScalarsCounit_app_of_kFlat f' T.B T.alphaB K₀
      (kFlat_scalarLift.{uR, max uR uA uM} R L hL)
  let := quasiIso_homComplexChangeOfRingsMap_of_kFlat f' K₀ J I q T.B T.alphaB
    (kFlat_scalarLift.{uR, max uR uA uM} R L hL)
  let : IsIso ((DerivedInternalHom.Model.homEquiv (DerivedCategory.Q.obj P)
      (DerivedCategory.Q.obj K₀) (DerivedCategory.Q.obj I)).symm
        (((DerivedInternalHom.Model.adjunction (ULift.{max uR uA uM} R)).tensorIso P K₀
            (kFlat_scalarLift.{uR, max uR uA uM} R L hL)).hom ≫
          DerivedCategory.Q.map W)) :=
    Stacks.DerivedHom.BaseChangeIso.isIso_homEquiv_symm_tensorIso f' K₀ J I q
      (kFlat_scalarLift.{uR, max uR uA uM} R L hL)
  let : IsIso (((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv
      ((derivedScalarEquivalence.{uR, max uR uA uM, max uR uA uM + 1} R).functor.obj
        (DerivedCategory.Q.obj P))
      ((derivedScalarEquivalence.{uR, max uR uA uM, max uR uA uM + 1} R).functor.obj
        (DerivedCategory.Q.obj K₀))
      ((derivedScalarEquivalence.{uR, max uR uA uM, max uR uA uM + 1} R).functor.obj
        (DerivedCategory.Q.obj I))).symm
    ((derivedTensorModelIso.{uR, max uR uA uM, max uR uA uM + 1} R P K₀
          (kFlat_scalarLift.{uR, max uR uA uM} R L hL)).hom ≫
      (derivedScalarEquivalence.{uR, max uR uA uM, max uR uA uM + 1} R).functor.map
        (DerivedCategory.Q.map W))) :=
    isIso_homEquiv_symm_derivedTensorModelIso.{uR, max uR uA uM, max uR uA uM + 1} P K₀ I
      (kFlat_scalarLift.{uR, max uR uA uM} R L hL) W
  have hbridge :
      (derivedScalarEquivalence.{uR, max uR uA uM, max uR uA uM + 1} R).functor.map
          (((DerivedInternalHom.Model.adjunction (ULift.{max uR uA uM} R)).homIso K₀ I).inv) ≫
        (derivedScalarEquivalence.{uR, max uR uA uM, max uR uA uM + 1} R).functor.map
          (inv ((DerivedInternalHom.Model.homEquiv (DerivedCategory.Q.obj P)
            (DerivedCategory.Q.obj K₀) (DerivedCategory.Q.obj I)).symm
              (((DerivedInternalHom.Model.adjunction (ULift.{max uR uA uM} R)).tensorIso P K₀
                  (kFlat_scalarLift.{uR, max uR uA uM} R L hL)).hom ≫
                DerivedCategory.Q.map W))) =
      (derivedHomModelIso.{uR, max uR uA uM, max uR uA uM + 1} R K₀ I).inv ≫
        inv (((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv
            ((derivedScalarEquivalence.{uR, max uR uA uM, max uR uA uM + 1} R).functor.obj
              (DerivedCategory.Q.obj P))
            ((derivedScalarEquivalence.{uR, max uR uA uM, max uR uA uM + 1} R).functor.obj
              (DerivedCategory.Q.obj K₀))
            ((derivedScalarEquivalence.{uR, max uR uA uM, max uR uA uM + 1} R).functor.obj
              (DerivedCategory.Q.obj I))).symm
          ((derivedTensorModelIso.{uR, max uR uA uM, max uR uA uM + 1} R P K₀
                (kFlat_scalarLift.{uR, max uR uA uM} R L hL)).hom ≫
            (derivedScalarEquivalence.{uR, max uR uA uM, max uR uA uM + 1} R).functor.map
              (DerivedCategory.Q.map W))) := by
    rw [← Functor.map_comp]
    exact derivedHomModelIso_inv_comp_inv_homEquiv_symm.{uR, max uR uA uM, max uR uA uM + 1}
      P K₀ I (kFlat_scalarLift.{uR, max uR uA uM} R L hL) W
  rw [derivedHomChangeOfRingsModelIso_hom_scalarLift_transpose.{uR, uA, uM} f L hL J I q,
    Functor.map_comp, Functor.map_comp, Functor.map_comp, reassoc_of% hbridge]


/-- `Stacks.DerivedHom.BaseChange.derivedHomChangeOfRingsModelIso_hom_scalarLift_overRing` with
the scalar transport spelled as the inverse of
`Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence`, which is how it occurs in
`Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_hom_app_tensorKFlat`: this is the
form in which the substitution is made at that use site, without duplicating its statement.  The
two functors are equal on the nose by
`Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence_inverse`; the invertibility of
the transported transpose is passed explicitly, not synthesized. -/
theorem derivedHomChangeOfRingsModelIso_hom_scalarLift_overRing'
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
    (L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (hL : IsKFlat.{uR, max uR uA uM} L) :
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    let T := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings f'
      (HomologicalComplex.zero : CochainComplex (ModuleCat.{max uR uA uM}
        (ULift.{max uR uA uM} A)) ℤ)
    let K₀ := ((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L
    ∀ (J : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)) ℤ)
      (I : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ℤ)
      [J.IsKInjective] [I.IsKInjective]
      (q : (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM}
        f').obj J ⟶ I) [QuasiIso q],
    letI : IsIso (T.alphaB.app K₀) :=
      isIso_extendScalarsCounit_app_of_kFlat f' T.B T.alphaB K₀
        (kFlat_scalarLift.{uR, max uR uA uM} R L hL)
    letI := quasiIso_homComplexChangeOfRingsMap_of_kFlat f' K₀ J I q T.B T.alphaB
      (kFlat_scalarLift.{uR, max uR uA uM} R L hL)
    let adj := (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').mapHomologicalComplex
      (ComplexShape.up ℤ)
    let Z := CochainComplex.HomComplexR (ULift.{max uR uA uM} A)
      ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM} f').obj K₀) J
    let P := (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM}
      f').obj Z
    let W := adj.homEquiv (P ⊗ K₀) J
        ((extendScalarsMonoidalIso f' P K₀).inv ≫
          DerivedInternalHom.Model.uncurry (adj.counit.app Z)) ≫ q
    letI : IsIso ((DerivedInternalHom.Model.homEquiv (DerivedCategory.Q.obj P)
        (DerivedCategory.Q.obj K₀) (DerivedCategory.Q.obj I)).symm
          (((DerivedInternalHom.Model.adjunction (ULift.{max uR uA uM} R)).tensorIso P K₀
              (kFlat_scalarLift.{uR, max uR uA uM} R L hL)).hom ≫
            DerivedCategory.Q.map W)) :=
      Stacks.DerivedHom.BaseChangeIso.isIso_homEquiv_symm_tensorIso f' K₀ J I q
        (kFlat_scalarLift.{uR, max uR uA uM} R L hL)
    (Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
      max uR uA uM, max uR uA uM + 1} R).inverse.map
        (derivedHomChangeOfRingsModelIso f' T.B T.alphaB K₀ J I q
          (kFlat_scalarLift.{uR, max uR uA uM} R L hL)).hom =
      (Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
      max uR uA uM, max uR uA uM + 1} R).inverse.map
          (homModelIso K₀ I (Iso.refl _)
            ((ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategoryFactors.app J ≪≫
              @asIso _ _ _ _ (DerivedCategory.Q.map q)
                ((DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2 inferInstance))).hom ≫
        (derivedHomModelIso.{uR, max uR uA uM, max uR uA uM + 1} R K₀ I).inv ≫
          @inv _ _ _ _
            (((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv
              ((Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
      max uR uA uM, max uR uA uM + 1} R).inverse.obj
                (DerivedCategory.Q.obj P))
              ((Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
      max uR uA uM, max uR uA uM + 1} R).inverse.obj
                (DerivedCategory.Q.obj K₀))
              ((Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
      max uR uA uM, max uR uA uM + 1} R).inverse.obj
                (DerivedCategory.Q.obj I))).symm
            ((derivedTensorModelIso.{uR, max uR uA uM, max uR uA uM + 1} R P K₀
                  (kFlat_scalarLift.{uR, max uR uA uM} R L hL)).hom ≫
              (Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
      max uR uA uM, max uR uA uM + 1} R).inverse.map
                (DerivedCategory.Q.map W)))
            (isIso_homEquiv_symm_derivedTensorModelIso.{uR, max uR uA uM, max uR uA uM + 1} P K₀ I
              (kFlat_scalarLift.{uR, max uR uA uM} R L hL) W) ≫
            (Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
      max uR uA uM, max uR uA uM + 1} R).inverse.map
                (((ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategoryFactors.app
                    (CochainComplex.HomComplexR (ULift.{max uR uA uM} A)
                      ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM,
                        max uR uA uM} f').obj K₀) J)).inv ≫
                  (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory.map
                    (homModelIso ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM,
                        max uR uA uM} f').obj K₀) J
                      (asIso (T.alphaB.app K₀)) (Iso.refl _)).inv) :=
  derivedHomChangeOfRingsModelIso_hom_scalarLift_overRing.{uR, uA, uM} f L hL

section ScalarEquivalenceSpelling

open Stacks.DerivedHom.ScalarTransportedInternalHom

universe u v w

variable {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]

/-- **The inverted bundle bridge in the spelling of [stacks 0E1W].**
`StacksDraft.DerivedHom.derivedHomModelIso_inv_comp_inv_homEquiv_symm` with the scalar transport
written as the inverse of
`Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence`, which is how the component of
[stacks 0E1W] in
`Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_hom_app_tensorKFlat` is written.
The two functors are equal on the nose. -/
theorem derivedHomModelIso_inv_comp_inv_homEquiv_symm_scalarEquivalence
    (K L I : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ)
    (hL : L.KFlat) [I.IsKInjective] (h : K ⊗ L ⟶ I)
    [IsIso (((derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)).homEquiv
        (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj I)).symm
      (((derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)).tensorIso K L hL).hom ≫
        DerivedCategory.Q.map h))] :
    (scalarEquivalence.{u, v, w} R).inverse.map
        (((derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)).homIso L I).inv ≫
          inv (((derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)).homEquiv
              (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
              (DerivedCategory.Q.obj I)).symm
            (((derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)).tensorIso K L hL).hom ≫
              DerivedCategory.Q.map h))) =
      (derivedHomModelIso.{u, v, w} R L I).inv ≫
        @inv _ _ _ _ (((derivedHomAdjunctionOverRing.{u, v, w} R).homEquiv
            ((scalarEquivalence.{u, v, w} R).inverse.obj (DerivedCategory.Q.obj K))
            ((scalarEquivalence.{u, v, w} R).inverse.obj (DerivedCategory.Q.obj L))
            ((scalarEquivalence.{u, v, w} R).inverse.obj (DerivedCategory.Q.obj I))).symm
          ((derivedTensorModelIso.{u, v, w} R K L hL).hom ≫
            (scalarEquivalence.{u, v, w} R).inverse.map (DerivedCategory.Q.map h)))
          (isIso_homEquiv_symm_derivedTensorModelIso.{u, v, w} K L I hL h) :=
  derivedHomModelIso_inv_comp_inv_homEquiv_symm.{u, v, w} K L I hL h

end ScalarEquivalenceSpelling

end Stacks.DerivedHom.BaseChange

end
