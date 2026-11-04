module

public import StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormulaMateLeft
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormulaMateRight

/-!
# The first residue of [stacks 0E2H] with no abstract comparison left in it

`StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormulaMateLeft` and
`…ProjectionFormulaMateRight` value the two sides of the mate identity that
`Dualizing.ProjectionFormula.ProjCounitCompat` -- the first of the three things the module
documentation of `StacksFrontier.RingTheory.Dualizing.RelativeCompositionTag` records [stacks 0E2H]
as owing -- has been reduced to.  This file substitutes those values into the identity, so that
what is left mentions no abstract comparison at all.

After `Dualizing.ProjectionFormula.projCounitCompat_of_mate_Q_value` the equation contains no
`Dualizing.ProjectionFormula.homRestrictComponent`, no change-of-rings isomorphism of
[stacks 0E1W], no internal Hom of [stacks 0A63] and no evaluation of [stacks 0A63]; after
`…_laxTensor_presentations` it also contains no component of an abstract equivalence, the two
counits of `StacksDraft.DerivedHom.derivedScalarEquivalence` that the right-hand side carries
having been valued through presentations as well.  What remains on the left is the chain-level
projection formula, read through
`CochainComplex.ExtendScalars.baseChange_tensor_iso_inv_eq` as the unit whiskered into the second
variable followed by `CochainComplex.ExtendScalars.restrictScalarsLaxTensor`, together with the
chain-level evaluation `StacksDraft.DerivedHom.DerivedInternalHom.Model.evaluationMor`; and on the
right, `Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso` and the universe-transport
bookkeeping around it.

## Main results

Each concludes `Dualizing.ProjectionFormula.ProjCounitCompat` at **every** object of `D(A)`, for
an arbitrary ring homomorphism, model and adjunction, from one equation.

* `Dualizing.ProjectionFormula.projCounitCompat_of_mate_Q_split` -- the presentation carried out
  of the [stacks 0A63] transpose, so that the transpose of `homRestrictComponent` stands alone.
* `Dualizing.ProjectionFormula.projCounitCompat_of_mate_Q_value` -- that transpose replaced by its
  unconditional value
  `Dualizing.ProjectionFormula.homEquiv_homRestrictComponent_scalarEquivalence`.
* `Dualizing.ProjectionFormula.projCounitCompat_of_mate_Q_value_exists` -- the same with the
  K-flat model of `Ext Q(P)` existentially quantified rather than universally, so one instance per
  pair suffices.
* `Dualizing.ProjectionFormula.projCounitCompat_of_mate_Q_laxTensor_value` and
  `…_laxTensor_value_exists` -- the same at the equal-universe `ModuleCat.{u}`, where the
  chain-level projection formula may be rewritten by
  `CochainComplex.ExtendScalars.baseChange_tensor_iso_inv_eq`.
* `Dualizing.ProjectionFormula.projCounitCompat_of_mate_Q_laxTensor_presentations` -- **the
  sharpest form**, with the two remaining counits of the scalar equivalence valued too.

## What closing it still needs

One piece of chain-level infrastructure that the library does not have, and it is identified:
`Stacks.DerivedHom.BaseChangeIso.restrictedEvaluation_eq_tensorHom_evaluationMor` -- which is the
chain-level identity the whole reduction is aimed at -- values
`(𝟙 ⊗ₘ η_K) ≫ ρ ≫ (ev_B)|_A` only when the first tensor factor is literally an internal Hom
complex `Hom_B(B ⊗_A K, J)`.  On the left-hand side above that factor is
`Dualizing.ProjectionFormula.homModelComplex`, the `ULift` transport of
`Hom_{ULift B}(X, I)`.  So what is missing is the compatibility of
`StacksDraft.DerivedHom.DerivedInternalHom.Model.evaluationMor` with the `ULift`
ring-equivalence transport of complexes: that the transport of an evaluation is the evaluation of
the transports.  The Hom-complex half of that transport exists,
`StacksDraft.ScalarTransport.homComplexRelabelIso`, and K-flatness transports by
`kFlat_scalarLift`; the evaluation half, and the monoidal comparison for the transport functor
that the source of `evaluationMor` needs, do not.

No `@[stacks]` attribute is placed here: nothing in this file is unconditional about a tag.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0E2H](https://stacks.math.columbia.edu/tag/0E2H)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Dualizing.ProjectionFormula

open CochainComplex CochainComplex.DerivedTensor CochainComplex.KFlat.ScalarBaseChange
open CochainComplex.DerivedExtensionScalars
open StacksDraft.DerivedHom
open CategoryTheory.MonoidalCategory

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Dualizing.extendScalarsAdditiveOfRingHom

universe u v

variable {A B : Type u} [CommRing A] [CommRing B]

universe w₁ w₂

/-- Postcomposition respects an equality of the second factor. -/
theorem comp_congr_right {C : Type w₁} [Category.{w₂} C] {X Y Z : C} (a : X ⟶ Y) {f g : Y ⟶ Z}
    (hfg : f = g) : a ≫ f = a ≫ g := by
  subst hfg
  rfl

/-- **The first residue of [stacks 0E2H] with the presentation carried out of the transpose.**
`Dualizing.ProjectionFormula.projCounitCompat_of_mate_Q_evaluationMor` with its right-hand side
rewritten by `Dualizing.ProjectionFormula.homEquiv_restrict_comp_homRestrictComponent`: the
presentation `Dualizing.ProjectionFormula.homModelQIso` of the internal Hom is tensored with the
identity of `Q P` outside the [stacks 0A63] transpose, so that the transpose of
`Dualizing.ProjectionFormula.homRestrictComponent` stands alone and the unconditional values of
`StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormulaMateRight` apply to it. -/
theorem projCounitCompat_of_mate_Q_split (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (adj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, max u v, u} φ)
    (h : ∀ P : CochainComplex (ModuleCat.{max u v} A) ℤ,
      ∀ hP : CochainComplex.DerivedTensor.IsKFlat.{u, max u v} P,
      ∀ X I : CochainComplex (ModuleCat.{max u v} (ULift.{max u v} B)) ℤ,
      ∀ hX : X.KFlat, ∀ _hI : I.IsKInjective,
      ∀ g : E.functor.obj (DerivedCategory.Q.obj P) ≅
        (derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
          (DerivedCategory.Q.obj X),
        (tensorRightDerived.{u, max u v} A (DerivedCategory.Q.obj P)).map
            ((leftAdjointIsoRestrictScalarsDerived.{u, max u v} φ _ adj).hom.app
              (DerivedCategory.Q.obj (homModelComplex.{u, v} B X I))) ≫
          (tensorRightDerived.{u, max u v} A (DerivedCategory.Q.obj P)).map
              ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategoryFactors.hom.app
                (homModelComplex.{u, v} B X I)) ≫
            (derivedTensor_comparison.{u, max u v} A
                ((restrictScalarsLarge.{max u v, u, u} φ).obj
                  (homModelComplex.{u, v} B X I)) P hP).hom ≫
              DerivedCategory.Q.map (baseChange_tensor_iso.{u, u, max u v} φ P
                (homModelComplex.{u, v} B X I)).inv ≫
                (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategoryFactors.inv.app
                    ((tensorRightLarge.{u, max u v}
                      ((extendScalarsLarge.{max u v, u, u} φ).obj P)).obj
                      (homModelComplex.{u, v} B X I)) ≫
                  (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
                      (derivedTensor_comparison.{u, max u v} B
                        (homModelComplex.{u, v} B X I)
                        ((extendScalarsLarge.{max u v, u, u} φ).obj P)
                        (isKFlat_extendScalarsLarge.{u, max u v} φ P hP)).inv ≫
                    (leftAdjointIsoRestrictScalarsDerived.{u, max u v} φ _ adj).inv.app
                        ((tensorRightDerived.{u, max u v} B
                          (DerivedCategory.Q.obj
                            ((extendScalarsLarge.{max u v, u, u} φ).obj P))).obj
                          (DerivedCategory.Q.obj (homModelComplex.{u, v} B X I))) ≫
                      (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
                        ((((Functor.curry.obj
                              (derivedHomAdjunctionOverRing.{u, max u v,
                                max u v + 1} B).tensor).flip.mapIso
                          (@asIso _ _ _ _ (E.comparison.app P)
                            (E.comparison_isIso_of_kFlat P
                              ((isKFlat_iff_kFlat.{u, max u v} P).mp hP)))).inv.app
                          (DerivedCategory.Q.obj (homModelComplex.{u, v} B X I))) ≫
                          modelEvaluation.{u, v} φ E P X I hX g) =
          (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.map
              (X := ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
                  (DerivedCategory.Q.obj (homModelComplex.{u, v} B X I)),
                DerivedCategory.Q.obj P))
              (Y := ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
                  ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.obj
                    (Opposite.op (E.functor.obj (DerivedCategory.Q.obj P)),
                      (derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
                        (DerivedCategory.Q.obj I))),
                DerivedCategory.Q.obj P))
              ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
                (homModelQIso.{u, v} φ E P X I g).hom, 𝟙 (DerivedCategory.Q.obj P)) ≫
            (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).homEquiv
              ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
                ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.obj
                  (Opposite.op (E.functor.obj (DerivedCategory.Q.obj P)),
                    (derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
                      (DerivedCategory.Q.obj I))))
              (DerivedCategory.Q.obj P)
              ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
                ((derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
                  (DerivedCategory.Q.obj I)))
              (homRestrictComponent.{u, v} φ E (DerivedCategory.Q.obj P)
                ((derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
                  (DerivedCategory.Q.obj I))))
    (N : DerivedCategory (ModuleCat.{max u v} A)) :
    ProjCounitCompat.{u, v} φ E adj N :=
  projCounitCompat_of_mate_Q_evaluationMor.{u, v} φ E adj
    (fun P hP X I hX hI g =>
      (h P hP X I hX hI g).trans
        (homEquiv_restrict_comp_homRestrictComponent.{u, v} φ E (DerivedCategory.Q.obj P)
          ((derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
            (DerivedCategory.Q.obj I))
          (DerivedCategory.Q.obj (homModelComplex.{u, v} B X I))
          (homModelQIso.{u, v} φ E P X I g).hom).symm) N

/-- **The first residue of [stacks 0E2H] with the change-of-rings isomorphism of [stacks 0E1W]
eliminated.**  `Dualizing.ProjectionFormula.projCounitCompat_of_mate_Q_split` with the
[stacks 0A63] transpose of `Dualizing.ProjectionFormula.homRestrictComponent` replaced by its
unconditional value
`Dualizing.ProjectionFormula.homEquiv_homRestrictComponent_scalarEquivalence`: neither the
projection formula, nor the internal Hom of [stacks 0A63], nor the change-of-rings isomorphism of
[stacks 0E1W] occurs in the remaining equation. -/
theorem projCounitCompat_of_mate_Q_value (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (adj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, max u v, u} φ)
    (h : ∀ P : CochainComplex (ModuleCat.{max u v} A) ℤ,
      ∀ hP : CochainComplex.DerivedTensor.IsKFlat.{u, max u v} P,
      ∀ X I : CochainComplex (ModuleCat.{max u v} (ULift.{max u v} B)) ℤ,
      ∀ hX : X.KFlat, ∀ _hI : I.IsKInjective,
      ∀ _g : E.functor.obj (DerivedCategory.Q.obj P) ≅
        (derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
          (DerivedCategory.Q.obj X),
      let Esc := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{u, max u v} A
      let S := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{u, max u v} B
      let φ' : ULift.{max u v} A →+* ULift.{max u v} B :=
        (ULift.ringEquiv.symm.toRingHom.comp φ).comp ULift.ringEquiv.toRingHom
      letI : (ModuleCat.extendScalars.{max u v, max u v, max u v} φ').IsLeftAdjoint :=
        (ModuleCat.extendRestrictScalarsAdj.{max u v} φ').isLeftAdjoint
      letI : (ModuleCat.restrictScalars.{max u v} φ').IsRightAdjoint :=
        (ModuleCat.extendRestrictScalarsAdj.{max u v} φ').isRightAdjoint
      letI : (ModuleCat.restrictScalars.{max u v} φ').IsLeftAdjoint :=
        (ModuleCat.restrictCoextendScalarsAdj.{max u v} φ').isLeftAdjoint
      let U := (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory
      let V := (ModuleCat.restrictScalars.{max u v} φ').mapDerivedCategory
      let T := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings φ'
        (HomologicalComplex.zero : CochainComplex (ModuleCat.{max u v} (ULift.{max u v} B)) ℤ)
      let a' := @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction
        _ _ _ _ φ' _ _ T.B T.alphaB T.isLeftDerivedB
      let δ : S.inverse ⋙ U ≅ V ⋙ Esc.inverse :=
        Stacks.DerivedHom.BaseChange.scalarRestrictionIso.{u, u, v} φ
      let τ : U ⋙ Esc.functor ≅ S.functor ⋙ V :=
        Iso.compInverseIso (H := Esc.symm)
          ((Iso.inverseCompIso (G := S.symm) δ.symm).symm ≪≫
            (Functor.associator _ _ _).symm)
      let eF : Esc.functor ⋙ T.B ≅ E.functor ⋙ S.functor :=
        (Esc.toAdjunction.comp a').leftAdjointUniq
          (((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, v} φ
            E.functor (modelComparison.{u, v} φ E)).comp S.toAdjunction).ofNatIsoRight δ)
      let HR := DerivedInternalHom.Model.hom (ULift.{max u v} A)
      let HB := DerivedInternalHom.Model.hom (ULift.{max u v} B)
      let NN := DerivedCategory.Q.obj P
      let WW := (derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
        (DerivedCategory.Q.obj I)
      (tensorRightDerived.{u, max u v} A NN).map
          ((leftAdjointIsoRestrictScalarsDerived.{u, max u v} φ _ adj).hom.app
            (DerivedCategory.Q.obj (homModelComplex.{u, v} B X I))) ≫
        (tensorRightDerived.{u, max u v} A NN).map
            ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategoryFactors.hom.app
              (homModelComplex.{u, v} B X I)) ≫
          (derivedTensor_comparison.{u, max u v} A
              ((restrictScalarsLarge.{max u v, u, u} φ).obj
                (homModelComplex.{u, v} B X I)) P hP).hom ≫
            DerivedCategory.Q.map (baseChange_tensor_iso.{u, u, max u v} φ P
              (homModelComplex.{u, v} B X I)).inv ≫
              (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategoryFactors.inv.app
                  ((tensorRightLarge.{u, max u v}
                    ((extendScalarsLarge.{max u v, u, u} φ).obj P)).obj
                    (homModelComplex.{u, v} B X I)) ≫
                U.map
                    (derivedTensor_comparison.{u, max u v} B
                      (homModelComplex.{u, v} B X I)
                      ((extendScalarsLarge.{max u v, u, u} φ).obj P)
                      (isKFlat_extendScalarsLarge.{u, max u v} φ P hP)).inv ≫
                  (leftAdjointIsoRestrictScalarsDerived.{u, max u v} φ _ adj).inv.app
                      ((tensorRightDerived.{u, max u v} B
                        (DerivedCategory.Q.obj
                          ((extendScalarsLarge.{max u v, u, u} φ).obj P))).obj
                        (DerivedCategory.Q.obj (homModelComplex.{u, v} B X I))) ≫
                    U.map
                      ((((Functor.curry.obj
                            (derivedHomAdjunctionOverRing.{u, max u v,
                              max u v + 1} B).tensor).flip.mapIso
                        (@asIso _ _ _ _ (E.comparison.app P)
                          (E.comparison_isIso_of_kFlat P
                            ((isKFlat_iff_kFlat.{u, max u v} P).mp hP)))).inv.app
                        (DerivedCategory.Q.obj (homModelComplex.{u, v} B X I))) ≫
                        modelEvaluation.{u, v} φ E P X I hX _g) =
        (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.map
            (X := (U.obj (DerivedCategory.Q.obj (homModelComplex.{u, v} B X I)), NN))
            (Y := (U.obj ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.obj
                (Opposite.op (E.functor.obj NN), WW)), NN))
            (U.map (homModelQIso.{u, v} φ E P X I _g).hom, 𝟙 NN) ≫
          (Esc.inverse.map
              ((DerivedInternalHom.Model.tensor (ULift.{max u v} A)).map
                  ((Esc.functor.map (δ.hom.app (HB.obj
                          (Opposite.op (S.functor.obj (E.functor.obj NN)), S.functor.obj WW))) ≫
                      Esc.counitIso.hom.app
                        (V.obj (HB.obj (Opposite.op (S.functor.obj (E.functor.obj NN)),
                          S.functor.obj WW))),
                    𝟙 (Esc.functor.obj NN)) :
                      ((Esc.functor.obj (U.obj (S.inverse.obj (HB.obj
                            (Opposite.op (S.functor.obj (E.functor.obj NN)),
                              S.functor.obj WW)))),
                          Esc.functor.obj NN) :
                        DerivedCategory (ModuleCat.{max u v} (ULift.{max u v} A)) ×
                          DerivedCategory (ModuleCat.{max u v} (ULift.{max u v} A))) ⟶
                        (V.obj (HB.obj (Opposite.op (S.functor.obj (E.functor.obj NN)),
                            S.functor.obj WW)),
                          Esc.functor.obj NN)) ≫
                DerivedInternalHom.Model.homEquiv
                  (V.obj (HB.obj (Opposite.op (S.functor.obj (E.functor.obj NN)),
                    S.functor.obj WW)))
                  (Esc.functor.obj NN) (Esc.functor.obj (U.obj WW))
                  (V.map (HB.map (CategoryTheory.Prod.mkHom (eF.hom.app NN).op
                      (𝟙 (S.functor.obj WW)))) ≫
                    (Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso φ' T.B
                          T.alphaB).inv.app
                        (Opposite.op (Esc.functor.obj NN), S.functor.obj WW) ≫
                      HR.map (CategoryTheory.Prod.mkHom (𝟙 (Opposite.op (Esc.functor.obj NN)))
                        (τ.inv.app WW)))) ≫
            Esc.unitIso.inv.app (U.obj WW)))
    (N : DerivedCategory (ModuleCat.{max u v} A)) :
    ProjCounitCompat.{u, v} φ E adj N := by
  refine projCounitCompat_of_mate_Q_split.{u, v} φ E adj (fun P hP X I hX hI g => ?_) N
  exact (h P hP X I hX hI g).trans
    (comp_congr_right _
      (homEquiv_homRestrictComponent_scalarEquivalence.{u, v} φ E (DerivedCategory.Q.obj P)
        ((derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
          (DerivedCategory.Q.obj I))).symm)

/-- **The first residue of [stacks 0E2H] at general universes, with the K-flat model chosen by
the prover.**  `Dualizing.ProjectionFormula.projCounitCompat_of_mate_Q_value` with the universal
quantifier over the K-flat complex `X` and the comparison `g` weakened to an existential, by
`Dualizing.ProjectionFormula.projCounitCompat_of_mate_model`: one instance of the equation per
pair `(P, I)` suffices, at any single K-flat model of `Ext Q(P)`. -/
theorem projCounitCompat_of_mate_Q_value_exists (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (adj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, max u v, u} φ)
    (h : ∀ P : CochainComplex (ModuleCat.{max u v} A) ℤ,
      ∀ hP : CochainComplex.DerivedTensor.IsKFlat.{u, max u v} P,
      ∀ I : CochainComplex (ModuleCat.{max u v} (ULift.{max u v} B)) ℤ,
      ∀ _hI : I.IsKInjective,
      ∃ (X : CochainComplex (ModuleCat.{max u v} (ULift.{max u v} B)) ℤ) (hX : X.KFlat)
        (_g : E.functor.obj (DerivedCategory.Q.obj P) ≅
          (derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
            (DerivedCategory.Q.obj X)),
      let Esc := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{u, max u v} A
      let S := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{u, max u v} B
      let φ' : ULift.{max u v} A →+* ULift.{max u v} B :=
        (ULift.ringEquiv.symm.toRingHom.comp φ).comp ULift.ringEquiv.toRingHom
      letI : (ModuleCat.extendScalars.{max u v, max u v, max u v} φ').IsLeftAdjoint :=
        (ModuleCat.extendRestrictScalarsAdj.{max u v} φ').isLeftAdjoint
      letI : (ModuleCat.restrictScalars.{max u v} φ').IsRightAdjoint :=
        (ModuleCat.extendRestrictScalarsAdj.{max u v} φ').isRightAdjoint
      letI : (ModuleCat.restrictScalars.{max u v} φ').IsLeftAdjoint :=
        (ModuleCat.restrictCoextendScalarsAdj.{max u v} φ').isLeftAdjoint
      let U := (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory
      let V := (ModuleCat.restrictScalars.{max u v} φ').mapDerivedCategory
      let T := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings φ'
        (HomologicalComplex.zero : CochainComplex (ModuleCat.{max u v} (ULift.{max u v} B)) ℤ)
      let a' := @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction
        _ _ _ _ φ' _ _ T.B T.alphaB T.isLeftDerivedB
      let δ : S.inverse ⋙ U ≅ V ⋙ Esc.inverse :=
        Stacks.DerivedHom.BaseChange.scalarRestrictionIso.{u, u, v} φ
      let τ : U ⋙ Esc.functor ≅ S.functor ⋙ V :=
        Iso.compInverseIso (H := Esc.symm)
          ((Iso.inverseCompIso (G := S.symm) δ.symm).symm ≪≫
            (Functor.associator _ _ _).symm)
      let eF : Esc.functor ⋙ T.B ≅ E.functor ⋙ S.functor :=
        (Esc.toAdjunction.comp a').leftAdjointUniq
          (((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, v} φ
            E.functor (modelComparison.{u, v} φ E)).comp S.toAdjunction).ofNatIsoRight δ)
      let HR := DerivedInternalHom.Model.hom (ULift.{max u v} A)
      let HB := DerivedInternalHom.Model.hom (ULift.{max u v} B)
      let NN := DerivedCategory.Q.obj P
      let WW := (derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
        (DerivedCategory.Q.obj I)
      (tensorRightDerived.{u, max u v} A NN).map
          ((leftAdjointIsoRestrictScalarsDerived.{u, max u v} φ _ adj).hom.app
            (DerivedCategory.Q.obj (homModelComplex.{u, v} B X I))) ≫
        (tensorRightDerived.{u, max u v} A NN).map
            ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategoryFactors.hom.app
              (homModelComplex.{u, v} B X I)) ≫
          (derivedTensor_comparison.{u, max u v} A
              ((restrictScalarsLarge.{max u v, u, u} φ).obj
                (homModelComplex.{u, v} B X I)) P hP).hom ≫
            DerivedCategory.Q.map (baseChange_tensor_iso.{u, u, max u v} φ P
              (homModelComplex.{u, v} B X I)).inv ≫
              (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategoryFactors.inv.app
                  ((tensorRightLarge.{u, max u v}
                    ((extendScalarsLarge.{max u v, u, u} φ).obj P)).obj
                    (homModelComplex.{u, v} B X I)) ≫
                U.map
                    (derivedTensor_comparison.{u, max u v} B
                      (homModelComplex.{u, v} B X I)
                      ((extendScalarsLarge.{max u v, u, u} φ).obj P)
                      (isKFlat_extendScalarsLarge.{u, max u v} φ P hP)).inv ≫
                  (leftAdjointIsoRestrictScalarsDerived.{u, max u v} φ _ adj).inv.app
                      ((tensorRightDerived.{u, max u v} B
                        (DerivedCategory.Q.obj
                          ((extendScalarsLarge.{max u v, u, u} φ).obj P))).obj
                        (DerivedCategory.Q.obj (homModelComplex.{u, v} B X I))) ≫
                    U.map
                      ((((Functor.curry.obj
                            (derivedHomAdjunctionOverRing.{u, max u v,
                              max u v + 1} B).tensor).flip.mapIso
                        (@asIso _ _ _ _ (E.comparison.app P)
                          (E.comparison_isIso_of_kFlat P
                            ((isKFlat_iff_kFlat.{u, max u v} P).mp hP)))).inv.app
                        (DerivedCategory.Q.obj (homModelComplex.{u, v} B X I))) ≫
                        modelEvaluation.{u, v} φ E P X I hX _g) =
        (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.map
            (X := (U.obj (DerivedCategory.Q.obj (homModelComplex.{u, v} B X I)), NN))
            (Y := (U.obj ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.obj
                (Opposite.op (E.functor.obj NN), WW)), NN))
            (U.map (homModelQIso.{u, v} φ E P X I _g).hom, 𝟙 NN) ≫
          (Esc.inverse.map
              ((DerivedInternalHom.Model.tensor (ULift.{max u v} A)).map
                  ((Esc.functor.map (δ.hom.app (HB.obj
                          (Opposite.op (S.functor.obj (E.functor.obj NN)), S.functor.obj WW))) ≫
                      Esc.counitIso.hom.app
                        (V.obj (HB.obj (Opposite.op (S.functor.obj (E.functor.obj NN)),
                          S.functor.obj WW))),
                    𝟙 (Esc.functor.obj NN)) :
                      ((Esc.functor.obj (U.obj (S.inverse.obj (HB.obj
                            (Opposite.op (S.functor.obj (E.functor.obj NN)),
                              S.functor.obj WW)))),
                          Esc.functor.obj NN) :
                        DerivedCategory (ModuleCat.{max u v} (ULift.{max u v} A)) ×
                          DerivedCategory (ModuleCat.{max u v} (ULift.{max u v} A))) ⟶
                        (V.obj (HB.obj (Opposite.op (S.functor.obj (E.functor.obj NN)),
                            S.functor.obj WW)),
                          Esc.functor.obj NN)) ≫
                DerivedInternalHom.Model.homEquiv
                  (V.obj (HB.obj (Opposite.op (S.functor.obj (E.functor.obj NN)),
                    S.functor.obj WW)))
                  (Esc.functor.obj NN) (Esc.functor.obj (U.obj WW))
                  (V.map (HB.map (CategoryTheory.Prod.mkHom (eF.hom.app NN).op
                      (𝟙 (S.functor.obj WW)))) ≫
                    (Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso φ' T.B
                          T.alphaB).inv.app
                        (Opposite.op (Esc.functor.obj NN), S.functor.obj WW) ≫
                      HR.map (CategoryTheory.Prod.mkHom (𝟙 (Opposite.op (Esc.functor.obj NN)))
                        (τ.inv.app WW)))) ≫
            Esc.unitIso.inv.app (U.obj WW)))
    (N : DerivedCategory (ModuleCat.{max u v} A)) :
    ProjCounitCompat.{u, v} φ E adj N := by
  refine projCounitCompat_of_mate_model.{u, v} φ E adj (fun P hP I hI => ?_) N
  have := hI
  obtain ⟨X, hX, g, heq⟩ := h P hP I hI
  refine ⟨_, homModelQIso.{u, v} φ E P X I g, ?_⟩
  refine (derivedProjNatIso_inv_app_Q_comp.{u, v} φ E _ adj P hP
    (homModelComplex.{u, v} B X I) _).trans ?_
  refine (Functor.comp_eight_map_comp_last
    (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory _ _ _ _ _ _ _ _
    (homEquiv_homModelQIso_hom.{u, v} φ E P X I hX g)).trans ?_
  exact heq.trans
    (homEquiv_restrict_comp_homRestrictComponent_eq.{u, v} φ E _ _ _ _ _
      (homEquiv_homRestrictComponent_scalarEquivalence.{u, v} φ E (DerivedCategory.Q.obj P)
        ((derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
          (DerivedCategory.Q.obj I)))).symm

/-- **The first residue of [stacks 0E2H], at the equal-universe `ModuleCat.{u}`, with both sides
at chain level.**  `Dualizing.ProjectionFormula.projCounitCompat_of_mate_Q_value` with the
chain-level projection formula
`CochainComplex.KFlat.ScalarBaseChange.baseChange_tensor_iso` on the left replaced, by
`CochainComplex.ExtendScalars.baseChange_tensor_iso_inv_eq`, with the unit of degreewise
extension--restriction of scalars whiskered into the second variable followed by the lax monoidal
structure map `CochainComplex.ExtendScalars.restrictScalarsLaxTensor` of restriction of scalars.

So at `ModuleCat.{u}` the whole of `Dualizing.ProjectionFormula.ProjCounitCompat`, at every object
of `D(A)`, follows from one equation in which neither the projection formula of [stacks 0E9L], nor
the internal Hom of [stacks 0A63], nor its evaluation, nor the change-of-rings isomorphism of
[stacks 0E1W] occurs: the left-hand side is the seven bookkeeping legs of
`Dualizing.ProjectionFormula.derivedProjNatIso_inv_app_Q` around
`(𝟙 ⊗ₘ η_P) ≫ ρ` and the chain-level evaluation
`StacksDraft.DerivedHom.DerivedInternalHom.Model.evaluationMor`, and the right-hand side is the
value of the [stacks 0E1W] transpose
`Dualizing.ProjectionFormula.homEquiv_homRestrictComponent_scalarEquivalence`.  The two chain-level
morphisms are exactly the two sides of
`Stacks.DerivedHom.BaseChangeIso.restrictedEvaluation_eq_tensorHom_evaluationMor`. -/
theorem projCounitCompat_of_mate_Q_laxTensor_value (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, u, u, u + 1, u + 1} φ)
    (adj : (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, u, u} φ)
    (h : ∀ P : CochainComplex (ModuleCat.{u} A) ℤ,
      ∀ hP : CochainComplex.DerivedTensor.IsKFlat.{u, u} P,
      ∀ X I : CochainComplex (ModuleCat.{u} (ULift.{u} B)) ℤ,
      ∀ hX : X.KFlat, ∀ _hI : I.IsKInjective,
      ∀ _g : E.functor.obj (DerivedCategory.Q.obj P) ≅
        (derivedScalarEquivalence.{u, u, u + 1} B).functor.obj
          (DerivedCategory.Q.obj X),
      let Esc := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{u, u} A
      let S := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{u, u} B
      let φ' : ULift.{u} A →+* ULift.{u} B :=
        (ULift.ringEquiv.symm.toRingHom.comp φ).comp ULift.ringEquiv.toRingHom
      letI : (ModuleCat.extendScalars.{u, u, u} φ').IsLeftAdjoint :=
        (ModuleCat.extendRestrictScalarsAdj.{u} φ').isLeftAdjoint
      letI : (ModuleCat.restrictScalars.{u} φ').IsRightAdjoint :=
        (ModuleCat.extendRestrictScalarsAdj.{u} φ').isRightAdjoint
      letI : (ModuleCat.restrictScalars.{u} φ').IsLeftAdjoint :=
        (ModuleCat.restrictCoextendScalarsAdj.{u} φ').isLeftAdjoint
      let U := (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory
      let V := (ModuleCat.restrictScalars.{u} φ').mapDerivedCategory
      let T := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings φ'
        (HomologicalComplex.zero : CochainComplex (ModuleCat.{u} (ULift.{u} B)) ℤ)
      let a' := @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction
        _ _ _ _ φ' _ _ T.B T.alphaB T.isLeftDerivedB
      let δ : S.inverse ⋙ U ≅ V ⋙ Esc.inverse :=
        Stacks.DerivedHom.BaseChange.scalarRestrictionIso.{u, u, u} φ
      let τ : U ⋙ Esc.functor ≅ S.functor ⋙ V :=
        Iso.compInverseIso (H := Esc.symm)
          ((Iso.inverseCompIso (G := S.symm) δ.symm).symm ≪≫
            (Functor.associator _ _ _).symm)
      let eF : Esc.functor ⋙ T.B ≅ E.functor ⋙ S.functor :=
        (Esc.toAdjunction.comp a').leftAdjointUniq
          (((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, u} φ
            E.functor (modelComparison.{u, u} φ E)).comp S.toAdjunction).ofNatIsoRight δ)
      let HR := DerivedInternalHom.Model.hom (ULift.{u} A)
      let HB := DerivedInternalHom.Model.hom (ULift.{u} B)
      let NN := DerivedCategory.Q.obj P
      let WW := (derivedScalarEquivalence.{u, u, u + 1} B).functor.obj
        (DerivedCategory.Q.obj I)
      (tensorRightDerived.{u, u} A NN).map
          ((leftAdjointIsoRestrictScalarsDerived.{u, u} φ _ adj).hom.app
            (DerivedCategory.Q.obj (homModelComplex.{u, u} B X I))) ≫
        (tensorRightDerived.{u, u} A NN).map
            ((ModuleCat.restrictScalars.{u} φ).mapDerivedCategoryFactors.hom.app
              (homModelComplex.{u, u} B X I)) ≫
          (derivedTensor_comparison.{u, u} A
              ((restrictScalarsLarge.{u, u, u} φ).obj
                (homModelComplex.{u, u} B X I)) P hP).hom ≫
            DerivedCategory.Q.map
                ((𝟙 ((CochainComplex.restrictScalarsLarge.{u, u, u} φ).obj
                      (homModelComplex.{u, u} B X I)) ⊗ₘ
                    (CochainComplex.ExtendScalars.extendRestrictScalarsComplexAdj φ).unit.app P) ≫
                  CochainComplex.ExtendScalars.restrictScalarsLaxTensor φ
                    (homModelComplex.{u, u} B X I)
                    ((CochainComplex.ExtendScalars.mapCochainComplex φ).obj P)) ≫
              (ModuleCat.restrictScalars.{u} φ).mapDerivedCategoryFactors.inv.app
                  ((tensorRightLarge.{u, u}
                    ((extendScalarsLarge.{u, u, u} φ).obj P)).obj
                    (homModelComplex.{u, u} B X I)) ≫
                U.map
                    (derivedTensor_comparison.{u, u} B
                      (homModelComplex.{u, u} B X I)
                      ((extendScalarsLarge.{u, u, u} φ).obj P)
                      (isKFlat_extendScalarsLarge.{u, u} φ P hP)).inv ≫
                  (leftAdjointIsoRestrictScalarsDerived.{u, u} φ _ adj).inv.app
                      ((tensorRightDerived.{u, u} B
                        (DerivedCategory.Q.obj
                          ((extendScalarsLarge.{u, u, u} φ).obj P))).obj
                        (DerivedCategory.Q.obj (homModelComplex.{u, u} B X I))) ≫
                    U.map
                      ((((Functor.curry.obj
                            (derivedHomAdjunctionOverRing.{u, u,
                              u + 1} B).tensor).flip.mapIso
                        (@asIso _ _ _ _ (E.comparison.app P)
                          (E.comparison_isIso_of_kFlat P
                            ((isKFlat_iff_kFlat.{u, u} P).mp hP)))).inv.app
                        (DerivedCategory.Q.obj (homModelComplex.{u, u} B X I))) ≫
                        modelEvaluation.{u, u} φ E P X I hX _g) =
        (derivedHomAdjunctionOverRing.{u, u, u + 1} A).tensor.map
            (X := (U.obj (DerivedCategory.Q.obj (homModelComplex.{u, u} B X I)), NN))
            (Y := (U.obj ((derivedHomAdjunctionOverRing.{u, u, u + 1} B).hom.obj
                (Opposite.op (E.functor.obj NN), WW)), NN))
            (U.map (homModelQIso.{u, u} φ E P X I _g).hom, 𝟙 NN) ≫
          (Esc.inverse.map
              ((DerivedInternalHom.Model.tensor (ULift.{u} A)).map
                  ((Esc.functor.map (δ.hom.app (HB.obj
                          (Opposite.op (S.functor.obj (E.functor.obj NN)), S.functor.obj WW))) ≫
                      Esc.counitIso.hom.app
                        (V.obj (HB.obj (Opposite.op (S.functor.obj (E.functor.obj NN)),
                          S.functor.obj WW))),
                    𝟙 (Esc.functor.obj NN)) :
                      ((Esc.functor.obj (U.obj (S.inverse.obj (HB.obj
                            (Opposite.op (S.functor.obj (E.functor.obj NN)),
                              S.functor.obj WW)))),
                          Esc.functor.obj NN) :
                        DerivedCategory (ModuleCat.{u} (ULift.{u} A)) ×
                          DerivedCategory (ModuleCat.{u} (ULift.{u} A))) ⟶
                        (V.obj (HB.obj (Opposite.op (S.functor.obj (E.functor.obj NN)),
                            S.functor.obj WW)),
                          Esc.functor.obj NN)) ≫
                DerivedInternalHom.Model.homEquiv
                  (V.obj (HB.obj (Opposite.op (S.functor.obj (E.functor.obj NN)),
                    S.functor.obj WW)))
                  (Esc.functor.obj NN) (Esc.functor.obj (U.obj WW))
                  (V.map (HB.map (CategoryTheory.Prod.mkHom (eF.hom.app NN).op
                      (𝟙 (S.functor.obj WW)))) ≫
                    (Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso φ' T.B
                          T.alphaB).inv.app
                        (Opposite.op (Esc.functor.obj NN), S.functor.obj WW) ≫
                      HR.map (CategoryTheory.Prod.mkHom (𝟙 (Opposite.op (Esc.functor.obj NN)))
                        (τ.inv.app WW)))) ≫
            Esc.unitIso.inv.app (U.obj WW)))
    (N : DerivedCategory (ModuleCat.{u} A)) :
    ProjCounitCompat.{u, u} φ E adj N := by
  refine projCounitCompat_of_mate_Q.{u, u} φ E adj (fun P hP X I hX hI g => ?_) N
  refine (derivedProjNatIso_inv_app_Q_comp_laxTensor.{u} φ E _ adj P hP
    (homModelComplex.{u, u} B X I) _).trans ?_
  refine (Functor.comp_eight_map_comp_last
    (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory _ _ _ _ _ _ _ _
    (homEquiv_homModelQIso_hom.{u, u} φ E P X I hX g)).trans ?_
  exact (h P hP X I hX hI g).trans
    (homEquiv_restrict_comp_homRestrictComponent_eq.{u, u} φ E _ _ _ _ _
      (homEquiv_homRestrictComponent_scalarEquivalence.{u, u} φ E (DerivedCategory.Q.obj P)
        ((derivedScalarEquivalence.{u, u, u + 1} B).functor.obj
          (DerivedCategory.Q.obj I)))).symm

/-- **The sharpest form reached here: the first residue of [stacks 0E2H] at `ModuleCat.{u}` with
the K-flat model of `Ext Q(P)` chosen by the prover.**
`Dualizing.ProjectionFormula.projCounitCompat_of_mate_Q_laxTensor_value` with the universal
quantifier over the K-flat complex `X` and the comparison `g` weakened to an existential: the
whole of `Dualizing.ProjectionFormula.ProjCounitCompat`, at every object of `D(A)`, follows from
**one** instance of the equation for each K-flat complex `P` of `A`-modules and each K-injective
complex `I` of `ULift B`-modules, at any single K-flat model of `Ext Q(P)` the prover cares to
produce.

This is the form in which the chain-level input
`Stacks.DerivedHom.BaseChangeIso.restrictedEvaluation_eq_tensorHom_evaluationMor` can be brought
to bear: the restricted evaluation it values sits at a pair whose first entry is the internal Hom
complex of `B ⊗_A P`, so the model `X` must be chosen to be a presentation of `B ⊗_A P` rather
than an arbitrary K-flat complex. -/
theorem projCounitCompat_of_mate_Q_laxTensor_value_exists (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, u, u, u + 1, u + 1} φ)
    (adj : (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, u, u} φ)
    (h : ∀ P : CochainComplex (ModuleCat.{u} A) ℤ,
      ∀ hP : CochainComplex.DerivedTensor.IsKFlat.{u, u} P,
      ∀ I : CochainComplex (ModuleCat.{u} (ULift.{u} B)) ℤ,
      ∀ _hI : I.IsKInjective,
      ∃ (X : CochainComplex (ModuleCat.{u} (ULift.{u} B)) ℤ) (hX : X.KFlat)
        (_g : E.functor.obj (DerivedCategory.Q.obj P) ≅
          (derivedScalarEquivalence.{u, u, u + 1} B).functor.obj (DerivedCategory.Q.obj X)),
      let Esc := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{u, u} A
      let S := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{u, u} B
      let φ' : ULift.{u} A →+* ULift.{u} B :=
        (ULift.ringEquiv.symm.toRingHom.comp φ).comp ULift.ringEquiv.toRingHom
      letI : (ModuleCat.extendScalars.{u, u, u} φ').IsLeftAdjoint :=
        (ModuleCat.extendRestrictScalarsAdj.{u} φ').isLeftAdjoint
      letI : (ModuleCat.restrictScalars.{u} φ').IsRightAdjoint :=
        (ModuleCat.extendRestrictScalarsAdj.{u} φ').isRightAdjoint
      letI : (ModuleCat.restrictScalars.{u} φ').IsLeftAdjoint :=
        (ModuleCat.restrictCoextendScalarsAdj.{u} φ').isLeftAdjoint
      let U := (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory
      let V := (ModuleCat.restrictScalars.{u} φ').mapDerivedCategory
      let T := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings φ'
        (HomologicalComplex.zero : CochainComplex (ModuleCat.{u} (ULift.{u} B)) ℤ)
      let a' := @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction
        _ _ _ _ φ' _ _ T.B T.alphaB T.isLeftDerivedB
      let δ : S.inverse ⋙ U ≅ V ⋙ Esc.inverse :=
        Stacks.DerivedHom.BaseChange.scalarRestrictionIso.{u, u, u} φ
      let τ : U ⋙ Esc.functor ≅ S.functor ⋙ V :=
        Iso.compInverseIso (H := Esc.symm)
          ((Iso.inverseCompIso (G := S.symm) δ.symm).symm ≪≫
            (Functor.associator _ _ _).symm)
      let eF : Esc.functor ⋙ T.B ≅ E.functor ⋙ S.functor :=
        (Esc.toAdjunction.comp a').leftAdjointUniq
          (((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, u} φ
            E.functor (modelComparison.{u, u} φ E)).comp S.toAdjunction).ofNatIsoRight δ)
      let HR := DerivedInternalHom.Model.hom (ULift.{u} A)
      let HB := DerivedInternalHom.Model.hom (ULift.{u} B)
      let NN := DerivedCategory.Q.obj P
      let WW := (derivedScalarEquivalence.{u, u, u + 1} B).functor.obj
        (DerivedCategory.Q.obj I)
      (tensorRightDerived.{u, u} A NN).map
          ((leftAdjointIsoRestrictScalarsDerived.{u, u} φ _ adj).hom.app
            (DerivedCategory.Q.obj (homModelComplex.{u, u} B X I))) ≫
        (tensorRightDerived.{u, u} A NN).map
            ((ModuleCat.restrictScalars.{u} φ).mapDerivedCategoryFactors.hom.app
              (homModelComplex.{u, u} B X I)) ≫
          (derivedTensor_comparison.{u, u} A
              ((restrictScalarsLarge.{u, u, u} φ).obj
                (homModelComplex.{u, u} B X I)) P hP).hom ≫
            DerivedCategory.Q.map
                ((𝟙 ((CochainComplex.restrictScalarsLarge.{u, u, u} φ).obj
                      (homModelComplex.{u, u} B X I)) ⊗ₘ
                    (CochainComplex.ExtendScalars.extendRestrictScalarsComplexAdj φ).unit.app P) ≫
                  CochainComplex.ExtendScalars.restrictScalarsLaxTensor φ
                    (homModelComplex.{u, u} B X I)
                    ((CochainComplex.ExtendScalars.mapCochainComplex φ).obj P)) ≫
              (ModuleCat.restrictScalars.{u} φ).mapDerivedCategoryFactors.inv.app
                  ((tensorRightLarge.{u, u}
                    ((extendScalarsLarge.{u, u, u} φ).obj P)).obj
                    (homModelComplex.{u, u} B X I)) ≫
                U.map
                    (derivedTensor_comparison.{u, u} B
                      (homModelComplex.{u, u} B X I)
                      ((extendScalarsLarge.{u, u, u} φ).obj P)
                      (isKFlat_extendScalarsLarge.{u, u} φ P hP)).inv ≫
                  (leftAdjointIsoRestrictScalarsDerived.{u, u} φ _ adj).inv.app
                      ((tensorRightDerived.{u, u} B
                        (DerivedCategory.Q.obj
                          ((extendScalarsLarge.{u, u, u} φ).obj P))).obj
                        (DerivedCategory.Q.obj (homModelComplex.{u, u} B X I))) ≫
                    U.map
                      ((((Functor.curry.obj
                            (derivedHomAdjunctionOverRing.{u, u,
                              u + 1} B).tensor).flip.mapIso
                        (@asIso _ _ _ _ (E.comparison.app P)
                          (E.comparison_isIso_of_kFlat P
                            ((isKFlat_iff_kFlat.{u, u} P).mp hP)))).inv.app
                        (DerivedCategory.Q.obj (homModelComplex.{u, u} B X I))) ≫
                        modelEvaluation.{u, u} φ E P X I hX _g) =
        (derivedHomAdjunctionOverRing.{u, u, u + 1} A).tensor.map
            (X := (U.obj (DerivedCategory.Q.obj (homModelComplex.{u, u} B X I)), NN))
            (Y := (U.obj ((derivedHomAdjunctionOverRing.{u, u, u + 1} B).hom.obj
                (Opposite.op (E.functor.obj NN), WW)), NN))
            (U.map (homModelQIso.{u, u} φ E P X I _g).hom, 𝟙 NN) ≫
          (Esc.inverse.map
              ((DerivedInternalHom.Model.tensor (ULift.{u} A)).map
                  ((Esc.functor.map (δ.hom.app (HB.obj
                          (Opposite.op (S.functor.obj (E.functor.obj NN)), S.functor.obj WW))) ≫
                      Esc.counitIso.hom.app
                        (V.obj (HB.obj (Opposite.op (S.functor.obj (E.functor.obj NN)),
                          S.functor.obj WW))),
                    𝟙 (Esc.functor.obj NN)) :
                      ((Esc.functor.obj (U.obj (S.inverse.obj (HB.obj
                            (Opposite.op (S.functor.obj (E.functor.obj NN)),
                              S.functor.obj WW)))),
                          Esc.functor.obj NN) :
                        DerivedCategory (ModuleCat.{u} (ULift.{u} A)) ×
                          DerivedCategory (ModuleCat.{u} (ULift.{u} A))) ⟶
                        (V.obj (HB.obj (Opposite.op (S.functor.obj (E.functor.obj NN)),
                            S.functor.obj WW)),
                          Esc.functor.obj NN)) ≫
                DerivedInternalHom.Model.homEquiv
                  (V.obj (HB.obj (Opposite.op (S.functor.obj (E.functor.obj NN)),
                    S.functor.obj WW)))
                  (Esc.functor.obj NN) (Esc.functor.obj (U.obj WW))
                  (V.map (HB.map (CategoryTheory.Prod.mkHom (eF.hom.app NN).op
                      (𝟙 (S.functor.obj WW)))) ≫
                    (Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso φ' T.B
                          T.alphaB).inv.app
                        (Opposite.op (Esc.functor.obj NN), S.functor.obj WW) ≫
                      HR.map (CategoryTheory.Prod.mkHom (𝟙 (Opposite.op (Esc.functor.obj NN)))
                        (τ.inv.app WW)))) ≫
            Esc.unitIso.inv.app (U.obj WW)))
    (N : DerivedCategory (ModuleCat.{u} A)) :
    ProjCounitCompat.{u, u} φ E adj N := by
  refine projCounitCompat_of_mate_model.{u, u} φ E adj (fun P hP I hI => ?_) N
  have := hI
  obtain ⟨X, hX, g, heq⟩ := h P hP I hI
  refine ⟨_, homModelQIso.{u, u} φ E P X I g, ?_⟩
  refine (derivedProjNatIso_inv_app_Q_comp_laxTensor.{u} φ E _ adj P hP
    (homModelComplex.{u, u} B X I) _).trans ?_
  refine (Functor.comp_eight_map_comp_last
    (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory _ _ _ _ _ _ _ _
    (homEquiv_homModelQIso_hom.{u, u} φ E P X I hX g)).trans ?_
  exact heq.trans
    (homEquiv_restrict_comp_homRestrictComponent_eq.{u, u} φ E _ _ _ _ _
      (homEquiv_homRestrictComponent_scalarEquivalence.{u, u} φ E (DerivedCategory.Q.obj P)
        ((derivedScalarEquivalence.{u, u, u + 1} B).functor.obj
          (DerivedCategory.Q.obj I)))).symm

/-- **The first residue of [stacks 0E2H] at `ModuleCat.{u}` with every piece of equivalence data
on the right valued too.**
`Dualizing.ProjectionFormula.projCounitCompat_of_mate_Q_laxTensor_value` with the two counits of
`StacksDraft.DerivedHom.derivedScalarEquivalence` that
`Dualizing.ProjectionFormula.homEquiv_homRestrictComponent_scalarEquivalence` leaves replaced by
their values at presentations, by
`Dualizing.ProjectionFormula.homEquiv_homRestrictComponent_of_presentations`.

After this nothing on either side of the remaining equation is a component of an abstract
equivalence or of the change-of-rings isomorphism of [stacks 0E1W] itself: the left-hand side is
seven bookkeeping legs around `(𝟙 ⊗ₘ η_P) ≫ ρ` and the chain-level evaluation
`StacksDraft.DerivedHom.DerivedInternalHom.Model.evaluationMor`, and the right-hand side is built
from `CategoryTheory.Functor.mapDerivedCategoryFactors`, localizations of the unit and counit of
the `ULift` equivalence of complexes, the two presentations, the comparison `eF` of the two
derived extensions of scalars, the representative model comparison
`Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso`, and the two components `δ` and `τ` of
the scalar-restriction comparison. -/
theorem projCounitCompat_of_mate_Q_laxTensor_presentations (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, u, u, u + 1, u + 1} φ)
    (adj : (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, u, u} φ)
    (h : ∀ P : CochainComplex (ModuleCat.{u} A) ℤ,
      ∀ hP : CochainComplex.DerivedTensor.IsKFlat.{u, u} P,
      ∀ I : CochainComplex (ModuleCat.{u} (ULift.{u} B)) ℤ,
      ∀ _hI : I.IsKInjective,
      ∃ (X : CochainComplex (ModuleCat.{u} (ULift.{u} B)) ℤ) (hX : X.KFlat)
        (_g : E.functor.obj (DerivedCategory.Q.obj P) ≅
          (derivedScalarEquivalence.{u, u, u + 1} B).functor.obj (DerivedCategory.Q.obj X)),
      let Esc := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{u, u} A
      let S := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{u, u} B
      let φ' : ULift.{u} A →+* ULift.{u} B :=
        (ULift.ringEquiv.symm.toRingHom.comp φ).comp ULift.ringEquiv.toRingHom
      letI : (ModuleCat.extendScalars.{u, u, u} φ').IsLeftAdjoint :=
        (ModuleCat.extendRestrictScalarsAdj.{u} φ').isLeftAdjoint
      letI : (ModuleCat.restrictScalars.{u} φ').IsRightAdjoint :=
        (ModuleCat.extendRestrictScalarsAdj.{u} φ').isRightAdjoint
      letI : (ModuleCat.restrictScalars.{u} φ').IsLeftAdjoint :=
        (ModuleCat.restrictCoextendScalarsAdj.{u} φ').isLeftAdjoint
      let U := (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory
      let V := (ModuleCat.restrictScalars.{u} φ').mapDerivedCategory
      let T := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings φ'
        (HomologicalComplex.zero : CochainComplex (ModuleCat.{u} (ULift.{u} B)) ℤ)
      let a' := @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction
        _ _ _ _ φ' _ _ T.B T.alphaB T.isLeftDerivedB
      let δ : S.inverse ⋙ U ≅ V ⋙ Esc.inverse :=
        Stacks.DerivedHom.BaseChange.scalarRestrictionIso.{u, u, u} φ
      let τ : U ⋙ Esc.functor ≅ S.functor ⋙ V :=
        Iso.compInverseIso (H := Esc.symm)
          ((Iso.inverseCompIso (G := S.symm) δ.symm).symm ≪≫
            (Functor.associator _ _ _).symm)
      let eF : Esc.functor ⋙ T.B ≅ E.functor ⋙ S.functor :=
        (Esc.toAdjunction.comp a').leftAdjointUniq
          (((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, u} φ
            E.functor (modelComparison.{u, u} φ E)).comp S.toAdjunction).ofNatIsoRight δ)
      let HR := DerivedInternalHom.Model.hom (ULift.{u} A)
      let HB := DerivedInternalHom.Model.hom (ULift.{u} B)
      let dse := derivedScalarEquivalence.{u, u, u + 1} A
      let ulm := uliftModuleEquivalence.{u, u, u} A
      let ulc := Stacks.DerivedHom.ScalarTransportedInternalHom.uliftComplexEquivalence.{u, u} A
      let NN := DerivedCategory.Q.obj P
      let WW := (derivedScalarEquivalence.{u, u, u + 1} B).functor.obj
        (DerivedCategory.Q.obj I)
      ∃ (Zc : CochainComplex (ModuleCat.{u} (ULift.{u} A)) ℤ)
        (e₁ : V.obj (HB.obj (Opposite.op (S.functor.obj (E.functor.obj NN)),
          S.functor.obj WW)) ≅ DerivedCategory.Q.obj Zc)
        (Wc : CochainComplex (ModuleCat.{u} A) ℤ) (e₂ : U.obj WW ≅ DerivedCategory.Q.obj Wc),
      (tensorRightDerived.{u, u} A NN).map
          ((leftAdjointIsoRestrictScalarsDerived.{u, u} φ _ adj).hom.app
            (DerivedCategory.Q.obj (homModelComplex.{u, u} B X I))) ≫
        (tensorRightDerived.{u, u} A NN).map
            ((ModuleCat.restrictScalars.{u} φ).mapDerivedCategoryFactors.hom.app
              (homModelComplex.{u, u} B X I)) ≫
          (derivedTensor_comparison.{u, u} A
              ((restrictScalarsLarge.{u, u, u} φ).obj
                (homModelComplex.{u, u} B X I)) P hP).hom ≫
            DerivedCategory.Q.map
                ((𝟙 ((CochainComplex.restrictScalarsLarge.{u, u, u} φ).obj
                      (homModelComplex.{u, u} B X I)) ⊗ₘ
                    (CochainComplex.ExtendScalars.extendRestrictScalarsComplexAdj φ).unit.app P) ≫
                  CochainComplex.ExtendScalars.restrictScalarsLaxTensor φ
                    (homModelComplex.{u, u} B X I)
                    ((CochainComplex.ExtendScalars.mapCochainComplex φ).obj P)) ≫
              (ModuleCat.restrictScalars.{u} φ).mapDerivedCategoryFactors.inv.app
                  ((tensorRightLarge.{u, u}
                    ((extendScalarsLarge.{u, u, u} φ).obj P)).obj
                    (homModelComplex.{u, u} B X I)) ≫
                U.map
                    (derivedTensor_comparison.{u, u} B
                      (homModelComplex.{u, u} B X I)
                      ((extendScalarsLarge.{u, u, u} φ).obj P)
                      (isKFlat_extendScalarsLarge.{u, u} φ P hP)).inv ≫
                  (leftAdjointIsoRestrictScalarsDerived.{u, u} φ _ adj).inv.app
                      ((tensorRightDerived.{u, u} B
                        (DerivedCategory.Q.obj
                          ((extendScalarsLarge.{u, u, u} φ).obj P))).obj
                        (DerivedCategory.Q.obj (homModelComplex.{u, u} B X I))) ≫
                    U.map
                      ((((Functor.curry.obj
                            (derivedHomAdjunctionOverRing.{u, u,
                              u + 1} B).tensor).flip.mapIso
                        (@asIso _ _ _ _ (E.comparison.app P)
                          (E.comparison_isIso_of_kFlat P
                            ((isKFlat_iff_kFlat.{u, u} P).mp hP)))).inv.app
                        (DerivedCategory.Q.obj (homModelComplex.{u, u} B X I))) ≫
                        modelEvaluation.{u, u} φ E P X I hX _g) =
        (derivedHomAdjunctionOverRing.{u, u, u + 1} A).tensor.map
            (X := (U.obj (DerivedCategory.Q.obj (homModelComplex.{u, u} B X I)), NN))
            (Y := (U.obj ((derivedHomAdjunctionOverRing.{u, u, u + 1} B).hom.obj
                (Opposite.op (E.functor.obj NN), WW)), NN))
            (U.map (homModelQIso.{u, u} φ E P X I _g).hom, 𝟙 NN) ≫
          (Esc.inverse.map
              ((DerivedInternalHom.Model.tensor (ULift.{u} A)).map
                  ((Esc.functor.map (δ.hom.app (HB.obj
                          (Opposite.op (S.functor.obj (E.functor.obj NN)), S.functor.obj WW))) ≫
                      (dse.inverse.map (dse.functor.map e₁.hom) ≫
                          (ulm.inverse.mapDerivedCategory.map
                                (ulm.functor.mapDerivedCategoryFactors.hom.app Zc) ≫
                              ulm.inverse.mapDerivedCategoryFactors.hom.app
                                  (ulc.functor.obj Zc) ≫
                                DerivedCategory.Q.map (ulc.unitIso.inv.app Zc)) ≫
                        e₁.inv),
                    𝟙 (Esc.functor.obj NN)) :
                      ((Esc.functor.obj (U.obj (S.inverse.obj (HB.obj
                            (Opposite.op (S.functor.obj (E.functor.obj NN)),
                              S.functor.obj WW)))),
                          Esc.functor.obj NN) :
                        DerivedCategory (ModuleCat.{u} (ULift.{u} A)) ×
                          DerivedCategory (ModuleCat.{u} (ULift.{u} A))) ⟶
                        (V.obj (HB.obj (Opposite.op (S.functor.obj (E.functor.obj NN)),
                            S.functor.obj WW)),
                          Esc.functor.obj NN)) ≫
                DerivedInternalHom.Model.homEquiv
                  (V.obj (HB.obj (Opposite.op (S.functor.obj (E.functor.obj NN)),
                    S.functor.obj WW)))
                  (Esc.functor.obj NN) (Esc.functor.obj (U.obj WW))
                  (V.map (HB.map (CategoryTheory.Prod.mkHom (eF.hom.app NN).op
                      (𝟙 (S.functor.obj WW)))) ≫
                    (Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso φ' T.B
                          T.alphaB).inv.app
                        (Opposite.op (Esc.functor.obj NN), S.functor.obj WW) ≫
                      HR.map (CategoryTheory.Prod.mkHom (𝟙 (Opposite.op (Esc.functor.obj NN)))
                        (τ.inv.app WW)))) ≫
            (dse.functor.map (dse.inverse.map e₂.hom) ≫
                (ulm.functor.mapDerivedCategory.map
                      (ulm.inverse.mapDerivedCategoryFactors.hom.app Wc) ≫
                    ulm.functor.mapDerivedCategoryFactors.hom.app (ulc.inverse.obj Wc) ≫
                      DerivedCategory.Q.map (ulc.counitIso.hom.app Wc)) ≫
              e₂.inv)))
    (N : DerivedCategory (ModuleCat.{u} A)) :
    ProjCounitCompat.{u, u} φ E adj N := by
  refine projCounitCompat_of_mate_model.{u, u} φ E adj (fun P hP I hI => ?_) N
  have := hI
  obtain ⟨X, hX, g, Zc, e₁, Wc, e₂, heq⟩ := h P hP I hI
  refine ⟨_, homModelQIso.{u, u} φ E P X I g, ?_⟩
  refine (derivedProjNatIso_inv_app_Q_comp_laxTensor.{u} φ E _ adj P hP
    (homModelComplex.{u, u} B X I) _).trans ?_
  refine (Functor.comp_eight_map_comp_last
    (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory _ _ _ _ _ _ _ _
    (homEquiv_homModelQIso_hom.{u, u} φ E P X I hX g)).trans ?_
  exact heq.trans
    (homEquiv_restrict_comp_homRestrictComponent_eq.{u, u} φ E _ _ _ _ _
      (homEquiv_homRestrictComponent_of_presentations.{u, u} φ E (DerivedCategory.Q.obj P)
        ((derivedScalarEquivalence.{u, u, u + 1} B).functor.obj (DerivedCategory.Q.obj I))
        Zc e₁ Wc e₂)).symm

end Dualizing.ProjectionFormula

end
