module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Perfect.Coherator.AffineDerivedPushforwardAcyclic

/-!
# The comparison square for derived pushforward along an affine morphism

Let `f : X ⟶ Y` be an affine morphism of schemes. Pushforward of quasi-coherent modules is
exact, so it induces a functor `D(QCoh(𝒪_X)) ⥤ D(QCoh(𝒪_Y))` by applying it termwise, and the
derived direct image restricts to a functor `D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`. The square formed by
these two functors and the comparison functors `D(QCoh) ⥤ D_QCoh` of [Stacks, Tag 06VT]
commutes, up to a unique natural isomorphism pinned down by the derivation unit.

The isomorphism exists because both composites are right derived functors of one and the same
functor `K(QCoh(𝒪_X)) ⥤ D(𝒪_Y)`: the left-hand composite because the derivation unit is
invertible on complexes of quasi-coherent modules
(`AlgebraicGeometry.affineRightDerivedPushforward_unit_isIso`), and the right-hand composite
because termwise pushforward inverts quasi-isomorphisms of such complexes. Uniqueness is the
uniqueness of a map out of a left Kan extension.

Termwise application of an exact functor to complexes, and its comparison with the induced
functor of derived categories, are Mathlib's `CategoryTheory.Functor.mapDerivedCategory` and
`CategoryTheory.Functor.mapDerivedCategoryFactorsh`; nothing of the kind is constructed here.

## Main results

* `AlgebraicGeometry.affineDerivedPushforward_comparison`: the comparison square, as the unique
  natural isomorphism compatible with the derivation unit.

## References

* [Stacks Project, Tag 08D7](https://stacks.math.columbia.edu/tag/08D7)
* [Stacks Project, Tag 06VT](https://stacks.math.columbia.edu/tag/06VT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry

universe u

/-- A rearrangement of a composite of two maps against three isomorphisms, used to match the two
descriptions of the comparison square on a homotopy complex. -/
private lemma iso_comparison_component {C : Type*} [Category* C]
    {S T U V W Z : C} (a : S ⟶ T) (b : T ⟶ U)
    (i : V ≅ U) (j : W ≅ S) (k : Z ≅ W) :
    a ≫ b ≫ 𝟙 U ≫ i.inv ≫ 𝟙 V ≫ i.hom =
      j.inv ≫ 𝟙 W ≫ k.inv ≫ 𝟙 Z ≫ k.hom ≫ j.hom ≫ a ≫ b := by
  simp

/-- **Stacks Project, Tag 08D7.** Comparison with an arbitrary right derived pushforward of all
sheaves of modules. This is the commutative square of the source, up to the unique natural
isomorphism whose inverse agrees with the derivation unit `α` on every homotopy complex of
quasi-coherent modules, after the canonical termwise identifications. -/
@[stacks 08D7 "comparison square"]
public theorem affineDerivedPushforward_comparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffineHom f]
    (RF : DerivedCategory X.Modules ⥤ DerivedCategory Y.Modules)
    (α : (Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))] :
    let I : Scheme.QuasicoherentModules X ⥤ X.Modules :=
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι
    let J : Scheme.QuasicoherentModules Y ⥤ Y.Modules :=
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι
    letI : I.Additive := CategoryTheory.Functor.fullSubcategoryInclusion_additive _
    letI : J.Additive := CategoryTheory.Functor.fullSubcategoryInclusion_additive _
    letI : PreservesFiniteLimits I :=
      Stacks.AlgebraicGeometry.QuasicoherentDerived.isQuasicoherent_ι_preservesFiniteLimits X
    letI : PreservesFiniteColimits I :=
      Stacks.AlgebraicGeometry.QuasicoherentDerived.isQuasicoherent_ι_preservesFiniteColimits X
    letI : PreservesFiniteLimits J :=
      Stacks.AlgebraicGeometry.QuasicoherentDerived.isQuasicoherent_ι_preservesFiniteLimits Y
    letI : PreservesFiniteColimits J :=
      Stacks.AlgebraicGeometry.QuasicoherentDerived.isQuasicoherent_ι_preservesFiniteColimits Y
    let F := quasicoherentPushforward f
    let G := Scheme.Modules.pushforward f
    ∃! e : (Stacks.AlgebraicGeometry.QuasicoherentDerived.derivedQuasicoherentComparison X ⋙
          affineRightDerivedPushforward f RF α) ≅
        (F.mapDerivedCategory ⋙
          Stacks.AlgebraicGeometry.QuasicoherentDerived.derivedQuasicoherentComparison Y),
      ∀ K : HomotopyCategory (Scheme.QuasicoherentModules X) (ComplexShape.up ℤ),
        (e.inv.app (DerivedCategory.Qh.obj K)).hom ≫
            RF.map (I.mapDerivedCategoryFactorsh.hom.app K) =
          J.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
            J.mapDerivedCategoryFactorsh.hom.app
              ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
            DerivedCategory.Qh.map
              ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ J))
                  (ComplexShape.up ℤ)).hom.app K ≫
                (Functor.mapHomotopyCategoryCompIso (Iso.refl (I ⋙ G))
                  (ComplexShape.up ℤ)).inv.app K) ≫
            α.app ((I.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) := by
  classical
  let P := SheafOfModules.isQuasicoherent X.ringCatSheaf
  let Q := SheafOfModules.isQuasicoherent Y.ringCatSheaf
  let C := Scheme.QuasicoherentModules X
  let D := Scheme.QuasicoherentModules Y
  let I : C ⥤ X.Modules := P.ι
  let J : D ⥤ Y.Modules := Q.ι
  let F : C ⥤ D := quasicoherentPushforward f
  let G : X.Modules ⥤ Y.Modules := Scheme.Modules.pushforward f
  let : HasDerivedCategory C := HasDerivedCategory.standard C
  let : HasDerivedCategory D := HasDerivedCategory.standard D
  let : I.Additive := CategoryTheory.Functor.fullSubcategoryInclusion_additive _
  let : J.Additive := CategoryTheory.Functor.fullSubcategoryInclusion_additive _
  let : PreservesFiniteLimits I :=
    Stacks.AlgebraicGeometry.QuasicoherentDerived.isQuasicoherent_ι_preservesFiniteLimits X
  let : PreservesFiniteColimits I :=
    Stacks.AlgebraicGeometry.QuasicoherentDerived.isQuasicoherent_ι_preservesFiniteColimits X
  let : PreservesFiniteLimits J :=
    Stacks.AlgebraicGeometry.QuasicoherentDerived.isQuasicoherent_ι_preservesFiniteLimits Y
  let : PreservesFiniteColimits J :=
    Stacks.AlgebraicGeometry.QuasicoherentDerived.isQuasicoherent_ι_preservesFiniteColimits Y
  let : PreservesFiniteLimits F := affinePushforwardPreservesFiniteLimits f
  let : PreservesFiniteColimits F := affinePushforwardPreservesFiniteColimits f
  let : F.Additive := quasicoherentPushforward_additive f
  let c := ComplexShape.up ℤ
  let W := HomotopyCategory.quasiIso C c
  let QC := DerivedCategory.Qh (C := C)
  let QD := DerivedCategory.Qh (C := D)
  let QX := DerivedCategory.Qh (C := X.Modules)
  let QY := DerivedCategory.Qh (C := Y.Modules)
  let ByP := DerivedCategoryB.derivedCategoryB Q
  let L : DerivedCategory C ⥤ DerivedCategory Y.Modules := I.mapDerivedCategory ⋙ RF
  let R : DerivedCategory C ⥤ DerivedCategory Y.Modules :=
    F.mapDerivedCategory ⋙ J.mapDerivedCategory
  let FH := F.mapHomotopyCategory c
  let JH := J.mapHomotopyCategory c
  let IH := I.mapHomotopyCategory c
  let GH := G.mapHomotopyCategory c
  let eSourceHC : FH ⋙ JH ≅ IH ⋙ GH :=
    Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ J)) c ≪≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (I ⋙ G)) c).symm
  let eSource : (FH ⋙ JH) ⋙ QY ≅ (IH ⋙ GH) ⋙ QY :=
    Functor.isoWhiskerRight eSourceHC QY
  let αL : (FH ⋙ JH) ⋙ QY ⟶ QC ⋙ L :=
    eSource.hom ≫
      (Functor.associator IH GH QY).hom ≫
      Functor.whiskerLeft IH α ≫
      (Functor.associator IH QX RF).inv ≫
      Functor.whiskerRight I.mapDerivedCategoryFactorsh.inv RF ≫
      (Functor.associator QC I.mapDerivedCategory RF).hom
  let αR : (FH ⋙ JH) ⋙ QY ⟶ QC ⋙ R :=
    (Functor.associator FH JH QY).hom ≫
      Functor.whiskerLeft FH J.mapDerivedCategoryFactorsh.inv ≫
      (Functor.associator FH QD J.mapDerivedCategory).inv ≫
      Functor.whiskerRight F.mapDerivedCategoryFactorsh.inv J.mapDerivedCategory ≫
      (Functor.associator QC F.mapDerivedCategory J.mapDerivedCategory).hom
  have : IsIso αL := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    obtain ⟨K₀, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    have : IsIso (α.app (IH.obj ((HomotopyCategory.quotient C c).obj K₀))) :=
      (NatTrans.isIso_app_iff_of_iso α ((Functor.mapHomotopyCategoryFactors I c).app K₀)).1
        (affineRightDerivedPushforward_unit_isIso f RF α ((I.mapHomologicalComplex c).obj K₀)
          fun n => (K₀.X n).property)
    dsimp [αL]
    infer_instance
  have : IsIso αR := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    dsimp [αR]
    infer_instance
  have hS : W.IsInvertedBy ((FH ⋙ JH) ⋙ QY) := by
    rw [MorphismProperty.IsInvertedBy.iff_of_iso W (asIso αR)]
    exact MorphismProperty.IsInvertedBy.of_comp W QC (Localization.inverts QC W) R
  let : L.IsRightDerivedFunctor αL W :=
    Functor.isRightDerivedFunctor_of_inverts W L (asIso αL).symm
  let : R.IsRightDerivedFunctor αR W :=
    Functor.isRightDerivedFunctor_of_inverts W R (asIso αR).symm
  let eAmbient : L ≅ R := Functor.rightDerivedUnique L R αL αR W
  let e : Stacks.AlgebraicGeometry.QuasicoherentDerived.derivedQuasicoherentComparison X ⋙
      affineRightDerivedPushforward f RF α ≅
      F.mapDerivedCategory ⋙
        Stacks.AlgebraicGeometry.QuasicoherentDerived.derivedQuasicoherentComparison Y :=
    NatIso.ofComponents (fun T => ByP.isoMk (eAmbient.app T))
      (fun g => ByP.ι.map_injective (eAmbient.hom.naturality g))
  have he (K : HomotopyCategory C c) :
      αR.app K ≫ (e.inv.app (QC.obj K)).hom = αL.app K := by
    change αR.app K ≫ eAmbient.inv.app (QC.obj K) = αL.app K
    simpa only [eAmbient, Functor.rightDerivedUnique,
      Functor.rightDerivedNatIso_inv, Iso.refl_inv,
      NatTrans.id_app, Category.id_comp] using
      Functor.rightDerivedNatTrans_app R L αR αL W (𝟙 _) K
  have heprop : ∀ K : HomotopyCategory C c,
      (e.inv.app (QC.obj K)).hom ≫ RF.map (I.mapDerivedCategoryFactorsh.hom.app K) =
        J.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
          J.mapDerivedCategoryFactorsh.hom.app (FH.obj K) ≫
          QY.map (eSourceHC.hom.app K) ≫ α.app (IH.obj K) := by
    intro K
    apply (cancel_epi (αR.app K)).1
    calc
      αR.app K ≫ ((e.inv.app (QC.obj K)).hom ≫
          RF.map (I.mapDerivedCategoryFactorsh.hom.app K)) =
          αL.app K ≫ RF.map (I.mapDerivedCategoryFactorsh.hom.app K) :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (fun t => t ≫ RF.map (I.mapDerivedCategoryFactorsh.hom.app K)) (he K))
      _ = _ := by
        simp only [Functor.comp_obj, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
          Functor.whiskerRight_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
          Functor.associator_inv_app, Category.id_comp, Category.assoc, αL, eSource, αR]
        exact iso_comparison_component (QY.map (eSourceHC.hom.app K))
          (α.app (IH.obj K)) (RF.mapIso (I.mapDerivedCategoryFactorsh.app K))
          (J.mapDerivedCategoryFactorsh.app (FH.obj K))
          (J.mapDerivedCategory.mapIso (F.mapDerivedCategoryFactorsh.app K))
  refine ⟨e, heprop, fun e' he' => ?_⟩
  apply Iso.ext_inv
  apply Localization.natTrans_ext QC W
  intro K
  apply ByP.ι.map_injective
  apply (cancel_mono (RF.map (I.mapDerivedCategoryFactorsh.hom.app K))).1
  exact (he' K).trans (heprop K).symm

end AlgebraicGeometry

end
