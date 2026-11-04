module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeModules
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackBaseChange

/-!
# Inverse images of modules across the relocalization of algebraic spaces

Let `g : T ⟶ S` be a morphism of a big fppf site and `φ : Y ⟶ Z` a representable morphism of
algebraic spaces over `T`. Viewing everything over `S` gives the morphism `Λ φ : Λ Y ⟶ Λ Z` of
lower-shriek extensions. Base change of étale charts along `φ` and along `Λ φ` correspond under
the equivalences of small étale sites of `AlgebraicGeometry.Space.SmallEtale.relocalize`, because
`Λ` preserves fibre products; hence the inverse images of modules along `φ` and along `Λ φ`
correspond under the equivalences `Mod(𝒪_Y) ≌ Mod(𝒪_{Λ Y})` and `Mod(𝒪_Z) ≌ Mod(𝒪_{Λ Z})`.

## Main definitions

* `AlgebraicGeometry.Space.relocalizeSpace`, `AlgebraicGeometry.Space.relocalizeHom`: the
  lower-shriek extension as a functor on algebraic spaces.
* `AlgebraicGeometry.Space.relocalizeBaseChangeIso`: base change of charts commutes with the
  equivalences of small étale sites.

## Main results

* `AlgebraicGeometry.Space.relocalizePushforwardIso`: direct images along `φ` and `Λ φ`
  correspond.
* `AlgebraicGeometry.Space.relocalizeModulePullbackIso`: inverse images along `φ` and `Λ φ`
  correspond, `φ^* ⋙ E_Y ≅ E_Z ⋙ (Λ φ)^*`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) {T S : Scheme.{u}} (hT : B.Contains T) (hS : B.Contains S)
  (g : B.obj hT ⟶ B.obj hS)

/-- The lower-shriek extension of an algebraic space over `T` to `S`. -/
noncomputable abbrev relocalizeSpace (Y : AlgebraicSpaces B T hT) : AlgebraicSpaces B S hS :=
  ⟨(OverShriek.relocalizePresheafFunctor g).obj Y.1, isAlgebraicSpace_relocalize' B hT hS g Y.1 Y.2⟩

/-- The lower-shriek extension of a morphism of algebraic spaces over `T` to `S`. -/
noncomputable abbrev relocalizeHom {Y Z : AlgebraicSpaces B T hT} (φ : Y ⟶ Z) :
    relocalizeSpace B hT hS g Y ⟶ relocalizeSpace B hT hS g Z :=
  ObjectProperty.homMk ((OverShriek.relocalizePresheafFunctor g).map φ.hom)

/-- The lower-shriek extension of a representable morphism is representable. -/
theorem relativelyRepresentable_relocalizeHom {Y Z : AlgebraicSpaces B T hT} (φ : Y ⟶ Z)
    (hφ : yoneda.relativelyRepresentable φ.hom) :
    yoneda.relativelyRepresentable (relocalizeHom B hT hS g φ).hom :=
  (OverShriek.presheaf_map_relocalize g (P₁ := ⊤) (P₂ := ⊤) (fun _ _ => trivial)
    ⟨hφ, fun _ _ _ _ _ _ => trivial⟩).rep

/-- The chart of `Λ X` attached to a chart of `X` is `Λ` of the chart read through
`h_{j U} ≅ Λ h_U`. -/
theorem relocalizeChart_hom_eq (X : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u)
    (A : CostructuredArrow yoneda X) :
    yonedaEquiv.symm (OverShriek.relocalizeChartSection g X A) =
      (OverShriek.relocalizeYonedaIso g).inv.app A.left ≫
        (OverShriek.relocalizePresheafFunctor g).map A.hom := by
  rw [OverShriek.relocalizeChart_hom, ← OverShriek.relocalizeYonedaFactorIso_hom]
  congr 1

variable {Y Z : AlgebraicSpaces B T hT} (φ : Y ⟶ Z) (hφ : yoneda.relativelyRepresentable φ.hom)

/-- `Λ` of the base change square of a chart `V` of `Z` along `φ`, read with representable
corners: a base change of `Λ φ` along the chart of `Λ Z` attached to `V`. -/
theorem isPullback_relocalize_baseChange (V : SmallEtale B T hT Z.1) :
    IsPullback
      ((OverShriek.relocalizeYonedaIso g).inv.app (hφ.pullback V.obj.hom) ≫
        (OverShriek.relocalizePresheafFunctor g).map (hφ.fst V.obj.hom))
      (yoneda.map ((Over.map g).map (hφ.snd V.obj.hom)))
      (relocalizeHom B hT hS g φ).hom
      ((OverShriek.relocalizeYonedaIso g).inv.app V.obj.left ≫
        (OverShriek.relocalizePresheafFunctor g).map V.obj.hom) := by
  refine ((hφ.isPullback V.obj.hom).map (OverShriek.relocalizePresheafFunctor g)).of_iso
    ((OverShriek.relocalizeYonedaIso g).app _) (Iso.refl _)
    ((OverShriek.relocalizeYonedaIso g).app _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · exact (OverShriek.relocalizeYonedaIso g).hom.naturality (hφ.snd V.obj.hom)
  · simp
  · simp

/-- The same square, with the charts of `Λ Y` and `Λ Z` read through the equivalences of small
étale sites. -/
theorem isPullback_relocalize_baseChange' (V : SmallEtale B T hT Z.1) :
    IsPullback
      ((SmallEtale.relocalize B hT hS g Y.1 Y.2).functor.obj
        ((smallBaseChange B T hT φ hφ).obj V)).obj.hom
      (yoneda.map ((Over.map g).map (hφ.snd V.obj.hom)))
      (relocalizeHom B hT hS g φ).hom
      ((SmallEtale.relocalize B hT hS g Z.1 Z.2).functor.obj V).obj.hom :=
  (isPullback_relocalize_baseChange B hT hS g φ hφ V).of_iso (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (Iso.refl _)
    ((Category.comp_id _).trans ((relocalizeChart_hom_eq B hT hS g Y.1
      ((smallBaseChange B T hT φ hφ).obj V).obj).symm.trans (Category.id_comp _).symm))
    (by cat_disch) (by cat_disch)
    ((Category.comp_id _).trans
      ((relocalizeChart_hom_eq B hT hS g Z.1 V.obj).symm.trans (Category.id_comp _).symm))

/-- The representability of `Λ φ`. -/
abbrev relocalizeRep := relativelyRepresentable_relocalizeHom B hT hS g φ hφ

/-- The comparison of the two base changes of a chart `V` of `Z`, on objects of the big fppf
site of `S`: the base change of the chart of `Λ Z` along `Λ φ` is the relocalization of the base
change of `V` along `φ`. -/
noncomputable def relocalizeBaseChangeOverIso (V : SmallEtale B T hT Z.1) :
    (relocalizeRep B hT hS g φ hφ).pullback
        ((SmallEtale.relocalize B hT hS g Z.1 Z.2).functor.obj V).obj.hom ≅
      (Over.map g).obj (hφ.pullback V.obj.hom) :=
  Yoneda.fullyFaithful.preimageIso
    (((relocalizeRep B hT hS g φ hφ).isPullback _).isoIsPullback _ _
      (isPullback_relocalize_baseChange' B hT hS g φ hφ V))

/-- The comparison `relocalizeBaseChangeOverIso` followed by the chart of `Λ Y` is the first
projection of the base change of the chart of `Λ Z` along `Λ φ`. -/
theorem relocalizeBaseChangeOverIso_hom_fst (V : SmallEtale B T hT Z.1) :
    yoneda.map (relocalizeBaseChangeOverIso B hT hS g φ hφ V).hom ≫
        ((SmallEtale.relocalize B hT hS g Y.1 Y.2).functor.obj
          ((smallBaseChange B T hT φ hφ).obj V)).obj.hom =
      (relocalizeRep B hT hS g φ hφ).fst
        ((SmallEtale.relocalize B hT hS g Z.1 Z.2).functor.obj V).obj.hom := by
  show yoneda.map ((Yoneda.fullyFaithful (C := BigFppfOver B S hS)).preimage _) ≫ _ = _
  rw [(Yoneda.fullyFaithful (C := BigFppfOver B S hS)).map_preimage]
  exact ((relocalizeRep B hT hS g φ hφ).isPullback _).isoIsPullback_hom_fst _ _
    (isPullback_relocalize_baseChange' B hT hS g φ hφ V)

/-- The comparison `relocalizeBaseChangeOverIso` followed by the relocalized second projection of
the base change of `V` along `φ` is the second projection of the base change along `Λ φ`. -/
theorem relocalizeBaseChangeOverIso_hom_snd (V : SmallEtale B T hT Z.1) :
    (relocalizeBaseChangeOverIso B hT hS g φ hφ V).hom ≫ (Over.map g).map (hφ.snd V.obj.hom) =
      (relocalizeRep B hT hS g φ hφ).snd
        ((SmallEtale.relocalize B hT hS g Z.1 Z.2).functor.obj V).obj.hom := by
  refine (Yoneda.fullyFaithful (C := BigFppfOver B S hS)).map_injective ?_
  show yoneda.map ((Yoneda.fullyFaithful (C := BigFppfOver B S hS)).preimage _ ≫ _) = _
  rw [Functor.map_comp, (Yoneda.fullyFaithful (C := BigFppfOver B S hS)).map_preimage]
  exact ((relocalizeRep B hT hS g φ hφ).isPullback _).isoIsPullback_hom_snd _ _
    (isPullback_relocalize_baseChange' B hT hS g φ hφ V)

/-- **Base change of charts commutes with relocalization**, on objects. -/
noncomputable def relocalizeBaseChangeObjIso (V : SmallEtale B T hT Z.1) :
    (smallBaseChange B S hS (relocalizeHom B hT hS g φ) (relocalizeRep B hT hS g φ hφ)).obj
        ((SmallEtale.relocalize B hT hS g Z.1 Z.2).functor.obj V) ≅
      (SmallEtale.relocalize B hT hS g Y.1 Y.2).functor.obj
        ((smallBaseChange B T hT φ hφ).obj V) :=
  ObjectProperty.isoMk _ (CostructuredArrow.isoMk (relocalizeBaseChangeOverIso B hT hS g φ hφ V)
    (relocalizeBaseChangeOverIso_hom_fst B hT hS g φ hφ V))

/-- **Base change of charts commutes with relocalization**: the two functors from the small
étale site of `Z` to that of `Λ Y` — relocalize, then base change along `Λ φ`; base change along
`φ`, then relocalize — are isomorphic. -/
noncomputable def relocalizeBaseChangeIso :
    (SmallEtale.relocalize B hT hS g Z.1 Z.2).functor ⋙
        smallBaseChange B S hS (relocalizeHom B hT hS g φ) (relocalizeRep B hT hS g φ hφ) ≅
      smallBaseChange B T hT φ hφ ⋙ (SmallEtale.relocalize B hT hS g Y.1 Y.2).functor :=
  NatIso.ofComponents (relocalizeBaseChangeObjIso B hT hS g φ hφ) (by
    intro V V' k
    refine ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ ?_)
    let k₁ := ((SmallEtale.relocalize B hT hS g Z.1 Z.2).functor ⋙
      smallBaseChange B S hS (relocalizeHom B hT hS g φ) (relocalizeRep B hT hS g φ hφ)).map k
    let k₂ := (smallBaseChange B T hT φ hφ ⋙
      (SmallEtale.relocalize B hT hS g Y.1 Y.2).functor).map k
    have e1 := relocalizeBaseChangeOverIso_hom_fst B hT hS g φ hφ V'
    have e2 := relocalizeBaseChangeOverIso_hom_fst B hT hS g φ hφ V
    have e3 := relocalizeBaseChangeOverIso_hom_snd B hT hS g φ hφ V'
    have e4 := relocalizeBaseChangeOverIso_hom_snd B hT hS g φ hφ V
    have w1 := CostructuredArrow.w k₁.hom
    have w2 := CostructuredArrow.w k₂.hom
    have m1 := smallBaseChange_map_snd B S hS (relocalizeHom B hT hS g φ)
      (relocalizeRep B hT hS g φ hφ) ((SmallEtale.relocalize B hT hS g Z.1 Z.2).functor.map k)
    have m0 := smallBaseChange_map_snd B T hT φ hφ k
    have hsnd : (k₁.hom.left ≫ (relocalizeBaseChangeOverIso B hT hS g φ hφ V').hom) ≫
          (Over.map g).map (hφ.snd V'.obj.hom) =
        ((relocalizeBaseChangeOverIso B hT hS g φ hφ V).hom ≫ k₂.hom.left) ≫
          (Over.map g).map (hφ.snd V'.obj.hom) :=
      (Category.assoc _ _ _).trans ((congrArg (k₁.hom.left ≫ ·) e3).trans (m1.trans
        ((congrArg (· ≫ _) e4.symm).trans ((Category.assoc _ _ _).trans
          ((congrArg (_ ≫ ·) ((Functor.map_comp (Over.map g) _ _).symm.trans
            ((congrArg (Over.map g).map m0.symm).trans (Functor.map_comp (Over.map g) _ _)))).trans
            (Category.assoc _ _ _).symm)))))
    refine (Yoneda.fullyFaithful (C := BigFppfOver B S hS)).map_injective
      ((isPullback_relocalize_baseChange' B hT hS g φ hφ V').hom_ext ?_ ?_)
    · exact (congrArg (· ≫ _) (Functor.map_comp _ _ _)).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) e1).trans (w1.trans (e2.symm.trans ((congrArg (_ ≫ ·) w2.symm).trans
          ((Category.assoc _ _ _).symm.trans
            (congrArg (· ≫ _) (Functor.map_comp _ _ _).symm)))))))
    · exact (Functor.map_comp _ _ _).symm.trans ((congrArg yoneda.map hsnd).trans
        (Functor.map_comp _ _ _)))

/-- The comparison of charts is inverse to the base change of `V` on underlying morphisms. -/
theorem relocalizeBaseChangeOverIso_inv_snd (V : SmallEtale B T hT Z.1) :
    (relocalizeBaseChangeOverIso B hT hS g φ hφ V).inv ≫ (relocalizeRep B hT hS g φ hφ).snd
        ((SmallEtale.relocalize B hT hS g Z.1 Z.2).functor.obj V).obj.hom =
      (Over.map g).map (hφ.snd V.obj.hom) :=
  (congrArg (_ ≫ ·) (relocalizeBaseChangeOverIso_hom_snd B hT hS g φ hφ V).symm).trans
    (Iso.inv_hom_id_assoc _ _)

/-- **Direct images commute with relocalization**: for a representable `φ`, the direct image
along `Λ φ` followed by the equivalence for `Z` is the equivalence for `Y` followed by the direct
image along `φ`. -/
noncomputable def relocalizePushforwardIso :
    smallBaseChangeModulePushforward B S hS (relocalizeHom B hT hS g φ)
        (relocalizeRep B hT hS g φ hφ) ⋙ (relocalizeModulesEquivalence B hT hS g Z.1 Z.2).inverse ≅
      (relocalizeModulesEquivalence B hT hS g Y.1 Y.2).inverse ⋙
        smallBaseChangeModulePushforward B T hT φ hφ :=
  haveI := isContinuous_smallBaseChange B S hS (relocalizeHom B hT hS g φ)
    (relocalizeRep B hT hS g φ hφ)
  haveI := isContinuous_smallBaseChange B T hT φ hφ
  haveI : (smallBaseChange B T hT φ hφ ⋙
      (SmallEtale.relocalize B hT hS g Y.1 Y.2).functor).IsContinuous
      (SmallEtale.topology B T hT Z.1) (SmallEtale.topology B S hS _) :=
    Functor.isContinuous_comp _ _ _ (SmallEtale.topology B T hT Y.1) _
  haveI : ((SmallEtale.relocalize B hT hS g Z.1 Z.2).functor ⋙ smallBaseChange B S hS
      (relocalizeHom B hT hS g φ) (relocalizeRep B hT hS g φ hφ)).IsContinuous
      (SmallEtale.topology B T hT Z.1) (SmallEtale.topology B S hS _) :=
    Functor.isContinuous_comp _ _ _ (SmallEtale.topology B S hS _) _
  SheafOfModules.pushforwardComp _ _ ≪≫
    SheafOfModules.pushforwardCongr₂ _ (relocalizeBaseChangeIso B hT hS g φ hφ).symm (by
    refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun U => ?_))
    exact ((forget₂ CommRingCat RingCat).map_comp _ _).symm.trans
      (congrArg (forget₂ CommRingCat RingCat).map ((Scheme.Γ.map_comp _ _).symm.trans
        (congrArg Scheme.Γ.map (congrArg Quiver.Hom.op
          (((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans
            (congrArg (BigFppfOver.toScheme B S hS).map
              (relocalizeBaseChangeOverIso_inv_snd B hT hS g φ hφ U.unop)))))))) ≪≫
    (SheafOfModules.pushforwardComp _ _).symm

/-- **Inverse images commute with relocalization**: for a representable morphism `φ : Y ⟶ Z`
of algebraic spaces over `T`, the inverse image along `φ` followed by the equivalence
`Mod(𝒪_Y) ≌ Mod(𝒪_{Λ Y})` is the equivalence for `Z` followed by the inverse image along `Λ φ`. -/
noncomputable def relocalizeModulePullbackIso :
    modulePullback B T hT φ ⋙ (relocalizeModulesEquivalence B hT hS g Y.1 Y.2).functor ≅
      (relocalizeModulesEquivalence B hT hS g Z.1 Z.2).functor ⋙
        modulePullback B S hS (relocalizeHom B hT hS g φ) :=
  Adjunction.leftAdjointUniq
    ((((modulePullbackAdjunction B T hT φ).ofNatIsoRight
        (modulePushforwardChartIso B T hT φ hφ)).comp
      (relocalizeModulesEquivalence B hT hS g Y.1 Y.2).toAdjunction))
    (((relocalizeModulesEquivalence B hT hS g Z.1 Z.2).toAdjunction.comp
      ((modulePullbackAdjunction B S hS (relocalizeHom B hT hS g φ)).ofNatIsoRight
        (modulePushforwardChartIso B S hS (relocalizeHom B hT hS g φ)
          (relocalizeRep B hT hS g φ hφ)))).ofNatIsoRight
      (relocalizePushforwardIso B hT hS g φ hφ))

end AlgebraicGeometry.Space

end
