module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeKeystoneChainLevel

/-!
# The [stacks 068I] prefix of the keystone is always a localized chain map

`Dualizing.tensorBaseChangeMor_eq_of_prefix_chain_map` closes the [stacks 068I] identification at a
pair of K-flat complexes from two hypotheses about a single chain map `w` over the lift of `R`: the
hypothesis `ha`, that the [stacks 068I] prefix is the scalar-lift presentation of `K` followed by
`w` localized, and the hypothesis `hrhs`, that the [stacks 0GMT] side is the uncurrying of `w` with
the chain-level map of [stacks 0E1W].

This file discharges the first of the two, for every K-flat pair and every choice of the two
resolutions, with no hypothesis at all.

The reason is that `w` is not constrained beyond being a chain map into the restriction of the
internal Hom complex `Hom_{A'}(A' ⊗ L', J)`, and that complex is **K-injective**: its target `J`
is, and its source is the extension of scalars of the scalar lift of the K-flat complex `L`, which
is K-flat again.  A morphism of the derived category into the class of a K-injective complex is the
class of a chain map, by [stacks 070G]; and the model comparison is invertible at the K-flat
complex `K`, so the [stacks 0A63] transpose over `A` of the [stacks 068I] candidate, read through
the five comparison factors of [stacks 0E1W], is the comparison at `K` followed by a localized
chain map for a chain map that simply exists.  Feeding that chain map to
`Stacks.DerivedHom.BaseChange.prefix_eq_scalarLiftQObjIso_comp_Q_map` produces `ha`.

**What is not done here.**  Nothing is registered and no caveat is lifted.  Both hypotheses of
`Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` remain open; in particular the
comparison identity `h` is untouched, and its frontier remains
`Dualizing.tensorComparisonCompatibility_of_kFlat_tail`.  What this file changes is that the other
hypothesis, at a K-flat pair, is now a single equation: the [stacks 0GMT] side, against the
uncurrying of whichever chain map presents the prefix.  That equation is
`Dualizing.tensorBaseChangeMor_eq_of_uncurried_tensor_side`'s one hypothesis, and it is the whole
of what the keystone still needs.

## Main results

* `Stacks.DerivedHom.BaseChange.isKInjective_restrictScalars_ringEquiv` -- K-injectivity survives
  restriction of scalars along a ring isomorphism, the two restriction functors of an isomorphism
  being an adjoint pair of exact functors.
* `Stacks.DerivedHom.BaseChange.exists_eq_comparison_app_comp_Q_map` -- at a K-flat complex `K` and
  a K-injective complex `Y`, every morphism `F (Q K) ⟶ Q Y` is the model comparison at `K`
  followed by a localized chain map.
* `Dualizing.exists_prefix_chain_map` -- **the discharge**: the hypothesis `ha` of
  `Dualizing.tensorBaseChangeMor_eq_of_prefix_chain_map` is satisfiable, for some chain map `w`.
* `Dualizing.tensorBaseChangeMor_eq_of_uncurried_tensor_side` -- the [stacks 068I] identification
  at a K-flat pair from the [stacks 0GMT] side alone, the prefix hypothesis having been discharged.

## Implementation notes

The statement of `Dualizing.exists_prefix_chain_map` is the hypothesis `ha` of
`Dualizing.tensorBaseChangeMor_eq_of_prefix_chain_map` with its chain map existentially quantified,
and the statement of `Dualizing.tensorBaseChangeMor_eq_of_uncurried_tensor_side` is that theorem
with the two hypotheses merged into one implication.  Both therefore repeat that theorem's prelude
of local definitions verbatim; the repetition is what lets the proofs apply it with no rewriting.

`Stacks.DerivedHom.BaseChange.prefix_eq_scalarLiftQObjIso_comp_Q_map` is applied by `exact` rather
than `refine`: the goal names the five comparison factors through the prelude's local definitions,
and those are not unfolded while the elaborator infers the middle object of a composition, so the
application has to be checked at a transparency that unfolds them.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 070G](https://stacks.math.columbia.edu/tag/070G)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.MonoidalCategory StacksDraft.DerivedHom
open CochainComplex.DerivedTensor
open CochainComplex.DerivedExtensionScalars
open CochainComplex.ExtendScalars

attribute [local instance] HasDerivedCategory.standard

universe v u₁ u₂ uR uA uM

namespace Stacks.DerivedHom.BaseChange

/-- **K-injectivity survives restriction of scalars along a ring isomorphism.**

For a ring isomorphism `e : B ≃+* C`, restriction of scalars along `e` carries a K-injective
complex of `C`-modules to a K-injective complex of `B`-modules. This is the K-injective companion
of `CochainComplex.DerivedTensor.isKFlat_restrictScalars_of_ringEquiv`. -/
public theorem isKInjective_restrictScalars_ringEquiv {B : Type u₁} {C : Type u₂} [CommRing B]
    [CommRing C] (e : B ≃+* C) (I : CochainComplex (ModuleCat.{v} C) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((ModuleCat.restrictScalars.{v} e.toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) :=
  CochainComplex.isKInjective_mapHomologicalComplex_of_exact
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u₁, u₂, v} e).functor
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u₁, u₂, v} e).inverse
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u₁, u₂, v} e).symm.toAdjunction I

attribute [local instance] Dualizing.extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
  (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
    DerivedCategory (ModuleCat.{max uR uA uM} A))
  (comparison : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [hF : F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]

include hF in
/-- **A morphism out of a model of extension of scalars at a K-flat complex, into the class of a
K-injective complex, is the comparison followed by a localized chain map.**

For a K-flat complex `K` and a K-injective complex `Y`, every morphism `F (Q K) ⟶ Q Y` is the
comparison of `F` with degreewise extension of scalars at `K`, followed by the localization of a
chain map `A ⊗ K ⟶ Y`.

The chain map is not canonical -- only its class is -- so the statement is existential. -/
public theorem exists_eq_comparison_app_comp_Q_map
    (K : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (hK : CochainComplex.KFlat.{uR, max uM uA} K)
    (Y : CochainComplex (ModuleCat.{max uR uA uM} A) ℤ) (hY : Y.IsKInjective)
    (u : F.obj (DerivedCategory.Q.obj K) ⟶ DerivedCategory.Q.obj Y) :
    ∃ m : ((ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K ⟶ Y,
      u = comparison.app K ≫ DerivedCategory.Q.map m := by
  have := hY
  have : IsIso (comparison.app K) :=
    isIso_comparison_app_of_kFlat.{uR, uA, uM} f F comparison K hK
  obtain ⟨m, hm⟩ := StacksDraft.DerivedHom.Construction.Q_map_surjective_of_isKInjective
    (((ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K) Y (inv (comparison.app K) ≫ u)
  exact ⟨m, by rw [hm, IsIso.hom_inv_id_assoc]⟩

end Stacks.DerivedHom.BaseChange

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
/-- **The [stacks 068I] prefix of the keystone is a localized chain map, unconditionally.**

This is the hypothesis `ha` of `Dualizing.tensorBaseChangeMor_eq_of_prefix_chain_map` with its
chain map `w` existentially quantified: for every pair of K-flat complexes and every choice of the
K-injective resolutions `J` and `I`, there is a chain map from the scalar lift of `K` to the
restriction of `Hom_{A'}(A' ⊗ L', J)` whose localization, after the scalar-lift presentation of
`K`, is the [stacks 068I] prefix. -/
theorem exists_prefix_chain_map
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
    let _τ : U ⋙ E.functor ≅ S.functor ⋙ V :=
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
    ∃ (w : ((ModuleCat.restrictScalars.{max uR uA uM}
            (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K ⟶
        (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM} f').obj
          (CochainComplex.HomComplexR (ULift.{max uR uA uM} A)
            ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM,
              max uR uA uM} f').obj K₀) J)),
      E.functor.map (adj.unit.app (DerivedCategory.Q.obj K) ≫
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
            DerivedCategory.Q.map w
    := by
  intro f' adj E S U V T adj' δ τ eF HA dA W M K₀ X₃ J I hJ hI q hq n hn eX eY
  have hL' := _root_.Stacks.DerivedHom.BaseChange.kFlat_scalarLift.{uR, max uR uA uM} R L hL
  have hal : IsIso (T.alphaB.app K₀) :=
    _root_.Stacks.DerivedHom.BaseChange.isIso_extendScalarsCounit_app_of_kFlat f'
      T.B T.alphaB K₀ hL'
  have hK' := (isKFlat_iff_kFlat.{uR, max uR uA uM} K).mp hK
  have hZ : (CochainComplex.HomComplexR (ULift.{max uR uA uM} A)
      ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM,
        max uR uA uM} f').obj K₀) J).IsKInjective :=
    homComplex_isKInjective_of_kFlat _ _
      (CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{max uR uA uM, max uR uA uM,
        max uR uA uM} f' K₀ hL')
  obtain ⟨m, hm⟩ := _root_.Stacks.DerivedHom.BaseChange.exists_eq_comparison_app_comp_Q_map.{uR,
      uA, uM} f F comparison K hK' _
    (_root_.Stacks.DerivedHom.BaseChange.isKInjective_restrictScalars_ringEquiv
      (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).symm _)
    ((dA.homEquiv (F.obj (DerivedCategory.Q.obj K)) (F.obj (DerivedCategory.Q.obj L)) M).symm
        (tensorBaseChangeMor.{uR, uA, uM} f F comparison D (DerivedCategory.Q.obj K)
          (DerivedCategory.Q.obj L)) ≫
      S.inverse.map (HA.map (CategoryTheory.Prod.mkHom
              (eF.hom.app (DerivedCategory.Q.obj L)).op (𝟙 (S.functor.obj M))) ≫
            HA.map (CategoryTheory.Prod.mkHom (T.B.map eX.inv).op eY.hom) ≫
          (_root_.Stacks.DerivedHom.BaseChange.homModelIso
            ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM,
              max uR uA uM} f').obj K₀) J (asIso (T.alphaB.app K₀))
            (Iso.refl (DerivedCategory.Q.obj J))).hom) ≫
        (_root_.Stacks.DerivedHom.BaseChange.scalarEquivalenceInverseFactors.{uA,
          max uR uA uM} A).hom.app (CochainComplex.HomComplexR (ULift.{max uR uA uM} A)
            ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM,
              max uR uA uM} f').obj K₀) J))
  have hp : V.map (HA.map (CategoryTheory.Prod.mkHom
            (eF.hom.app (DerivedCategory.Q.obj L)).op (𝟙 (S.functor.obj M)))) ≫
        (_root_.Stacks.DerivedHom.BaseChange.homRestrictTarget f' T.B).map
            (CategoryTheory.Prod.mkHom eX.inv.op eY.hom) ≫
          V.map (_root_.Stacks.DerivedHom.BaseChange.homModelIso
              ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM,
                max uR uA uM} f').obj K₀) J (asIso (T.alphaB.app K₀))
              (Iso.refl (DerivedCategory.Q.obj J))).hom ≫
            (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategoryFactors.hom.app
              (CochainComplex.HomComplexR (ULift.{max uR uA uM} A)
                ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM,
                  max uR uA uM} f').obj K₀) J) =
      V.map (HA.map (CategoryTheory.Prod.mkHom
                (eF.hom.app (DerivedCategory.Q.obj L)).op (𝟙 (S.functor.obj M))) ≫
              HA.map (CategoryTheory.Prod.mkHom (T.B.map eX.inv).op eY.hom) ≫
            (_root_.Stacks.DerivedHom.BaseChange.homModelIso
              ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM,
                max uR uA uM} f').obj K₀) J (asIso (T.alphaB.app K₀))
              (Iso.refl (DerivedCategory.Q.obj J))).hom) ≫
        (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategoryFactors.hom.app
          (CochainComplex.HomComplexR (ULift.{max uR uA uM} A)
            ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM,
              max uR uA uM} f').obj K₀) J) := by
    rw [show (_root_.Stacks.DerivedHom.BaseChange.homRestrictTarget f' T.B).map
          (CategoryTheory.Prod.mkHom eX.inv.op eY.hom) =
        V.map (HA.map (CategoryTheory.Prod.mkHom (T.B.map eX.inv).op eY.hom)) from rfl]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  exact ⟨_, _root_.Stacks.DerivedHom.BaseChange.prefix_eq_scalarLiftQObjIso_comp_Q_map.{uR, uA,
    uM} f F comparison K hK' _ _ _ _ _ m hp hm⟩

include hF in
/-- **The [stacks 068I] identification at a K-flat pair, from the [stacks 0GMT] side alone.**

`Dualizing.tensorBaseChangeMor_eq_of_prefix_chain_map` with its prefix hypothesis discharged by
`Dualizing.exists_prefix_chain_map`.  What is left is one implication: for every chain map `w`
presenting the [stacks 068I] prefix, the [stacks 0GMT] side -- the inverse counit of the scalar
lift at the derived tensor product, then the scalar lift of the unit of [stacks 0GMT] at
`Q K ⊗ᴸ Q L` -- is the derived tensor bifunctor at the two scalar-lift presentations, the K-flat
representation of the derived tensor product, the localized uncurrying of `w` followed by the
chain-level map of [stacks 0E1W], and the tail.

The quantifier over `w` costs nothing: the hypothesis `ha` determines `w` up to homotopy, and the
conclusion depends on `w` only through its localization, so the implication is equivalent to the
single equation obtained by substituting the prefix for `Q w`.

This is the whole of what the [stacks 068I] identification at a K-flat pair still needs, and hence
-- through `Dualizing.tensorBaseChangeMor_eq_of_kFlat` and
`Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` -- the whole of what the first of
the chapter's two keystone hypotheses still needs. -/
theorem tensorBaseChangeMor_eq_of_uncurried_tensor_side
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
    (∀ (w : ((ModuleCat.restrictScalars.{max uR uA uM}
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
            DerivedCategory.Q.map w),
      E.counitIso.inv.app ((DerivedInternalHom.Model.tensor
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
                    V.map eY.inv ≫ τ.inv.app M)) →
    tensorBaseChangeMor.{uR, uA, uM} f F comparison D (DerivedCategory.Q.obj K)
        (DerivedCategory.Q.obj L) =
      derivedTensorBaseChange.{uR, uA, uM} f F comparison (DerivedCategory.Q.obj K)
        (DerivedCategory.Q.obj L) := by
  intro f' adj E S U V T adj' δ τ eF HA dA W M K₀ X₃ J I hJ hI q hq n hn eX eY hrhs
  obtain ⟨w, ha⟩ := exists_prefix_chain_map.{uR, uA, uM} f F comparison D K L hK hL J I q n
  exact tensorBaseChangeMor_eq_of_prefix_chain_map.{uR, uA, uM} f F comparison D K L hK hL
    J I q n w ha (hrhs w ha)

end Dualizing

end
