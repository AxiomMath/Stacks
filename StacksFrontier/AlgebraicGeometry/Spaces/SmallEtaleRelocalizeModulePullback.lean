module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRelocalizeModules
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Extension
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback

/-!
# Inverse images of modules across the relocalization of algebraic spaces

Let `h : W ⟶ S` be a morphism of a big fppf site and `φ : Y ⟶ Z` a representable morphism of
algebraic spaces over `W`.  Viewing everything over `S` gives the morphism `Λ φ : Λ Y ⟶ Λ Z` of
lower-shriek extensions.  Base change of étale charts along `φ` and along `Λ φ` correspond under
the equivalences of small étale sites `AlgebraicGeometry.Space.SmallEtale.relocalizeEquivalence`,
because `Λ` preserves fibre products; hence the direct and the inverse images of modules along
`φ` and along `Λ φ` correspond under the equivalences `Mod(𝒪_Y) ≌ Mod(𝒪_{Λ Y})` and
`Mod(𝒪_Z) ≌ Mod(𝒪_{Λ Z})` of `AlgebraicGeometry.Space.relocalizeModulesEquivalenceSE`.

## Main definitions

* `AlgebraicGeometry.Space.relocalizeSpaceSE`, `AlgebraicGeometry.Space.relocalizeHomSE`: the
  lower-shriek extension on algebraic spaces and their morphisms.
* `AlgebraicGeometry.Space.relocalizeBaseChangeIsoSE`: base change of charts commutes with the
  equivalences of small étale sites.

## Main results

* `AlgebraicGeometry.Space.relocalizePushforwardIsoSE`: direct images along `φ` and `Λ φ`
  correspond.
* `AlgebraicGeometry.Space.relocalizeModulePullbackIsoSE`: **inverse images along `φ` and `Λ φ`
  correspond**, `φ^* ⋙ E_Y ≅ E_Z ⋙ (Λ φ)^*`.

## References

* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

namespace Stacks.SheafOfModules

section Square

variable {C C' D D' : Type*} [Category* C] [Category* C'] [Category* D] [Category* D']
  {J : GrothendieckTopology C} {J' : GrothendieckTopology C'} {K : GrothendieckTopology D}
  {K' : GrothendieckTopology D'} {F : C ⥤ C'} {G : D ⥤ D'} {E : C ⥤ D} {E' : C' ⥤ D'}
  [F.IsContinuous J J'] [G.IsContinuous K K'] [E.IsContinuous J K] [E'.IsContinuous J' K']
  [(E ⋙ G).IsContinuous J K'] [(F ⋙ E').IsContinuous J K']
  {R : Sheaf J RingCat.{u}} {R' : Sheaf J' RingCat.{u}} {T : Sheaf K RingCat.{u}}
  {T' : Sheaf K' RingCat.{u}}

/-- **The direct images round a square of continuous functors.**  For a square of continuous
functors `E ⋙ G ≅ F ⋙ E'` and morphisms of sheaves of rings along its four sides compatible
with it, the two composite direct images of sheaves of modules are isomorphic: both send a
sheaf of modules `M` to the sheaf `V ↦ M(E(G V)) ≅ M(E'(F V))`, the isomorphism being
restriction along the square. -/
noncomputable def pushforwardSquareIsoOfIso
    (f : R ⟶ (F.sheafPushforwardContinuous RingCat.{u} J J').obj R')
    (g : T ⟶ (G.sheafPushforwardContinuous RingCat.{u} K K').obj T')
    (ι : R ⟶ (E.sheafPushforwardContinuous RingCat.{u} J K).obj T)
    (ι' : R' ⟶ (E'.sheafPushforwardContinuous RingCat.{u} J' K').obj T')
    (e : E ⋙ G ≅ F ⋙ E')
    (he : (ι ≫ (E.sheafPushforwardContinuous RingCat.{u} J K).map g) ≫
        (Functor.sheafPushforwardContinuousNatTrans e.symm.hom RingCat.{u} J K').app T' =
      f ≫ (F.sheafPushforwardContinuous RingCat.{u} J J').map ι') :
    SheafOfModules.pushforward.{u} g ⋙ SheafOfModules.pushforward.{u} ι ≅
      SheafOfModules.pushforward.{u} ι' ⋙ SheafOfModules.pushforward.{u} f :=
  SheafOfModules.pushforwardComp ι g ≪≫ SheafOfModules.pushforwardCongr₂ _ e.symm he ≪≫
    (SheafOfModules.pushforwardComp f ι').symm

end Square

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (W S : Scheme.{u}) (hW : B.Contains W) (hS : B.Contains S)
  (h : B.obj hW ⟶ B.obj hS)

/-- The lower-shriek extension of an algebraic space over `W` to `S`. -/
abbrev relocalizeSpaceSE (Y : AlgebraicSpaces B W hW) : AlgebraicSpaces B S hS :=
  ⟨(OverShriek.relocalizePresheafFunctor h).obj Y.1,
    isAlgebraicSpace_viewOver B W S hW hS h Y.1 Y.2⟩

/-- The lower-shriek extension of a morphism of algebraic spaces over `W` to `S`. -/
abbrev relocalizeHomSE {Y Z : AlgebraicSpaces B W hW} (φ : Y ⟶ Z) :
    relocalizeSpaceSE B W S hW hS h Y ⟶ relocalizeSpaceSE B W S hW hS h Z :=
  ObjectProperty.homMk ((OverShriek.relocalizePresheafFunctor h).map φ.hom)

/-- The lower-shriek extension of a representable morphism is representable. -/
theorem relativelyRepresentable_relocalizeHomSE {Y Z : AlgebraicSpaces B W hW} (φ : Y ⟶ Z)
    (hφ : yoneda.relativelyRepresentable φ.hom) :
    yoneda.relativelyRepresentable (relocalizeHomSE B W S hW hS h φ).hom :=
  (OverShriek.presheaf_map_relocalize h (P₁ := ⊤) (P₂ := ⊤) (fun _ _ => trivial)
    ⟨hφ, fun _ _ _ _ _ _ => trivial⟩).rep

/-- The two identifications of the extension of a representable presheaf with a representable
presheaf agree. -/
theorem relocalizedYonedaIso_eq (U : BigFppfOver B W hW) :
    relocalizedYonedaIso B (B.obj hW) (B.obj hS) h U =
      (OverShriek.relocalizeYonedaIso h).app U := by
  ext V p
  exact Over.OverMorphism.ext rfl

/-- The chart of `Λ X` attached to a chart of `X` is `Λ` of the chart read through
`h_{j U} ≅ Λ h_U`. -/
theorem relocalizeChart_eq (X : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u) {U : BigFppfOver B W hW}
    (a : yoneda.obj U ⟶ X) :
    relocalizeChart B W S hW hS h a =
      (OverShriek.relocalizeYonedaIso h).inv.app U ≫
        (OverShriek.relocalizePresheafFunctor h).map a := by
  rw [relocalizeChart, relocalizedYonedaIso_eq]
  rfl

section Restriction

variable (Y : AlgebraicSpaces B W hW)

/-- The structure sheaf of `Y` is the direct image of the structure sheaf of `Λ Y` along the
equivalence of small étale sites: the two agree on every chart, the underlying scheme of a chart
being unchanged by relocalization. -/
def relocalizeRingMap :
    smallEtaleRingSheaf B W hW Y.1 Y.2 ⟶
      ((SmallEtale.relocalizeEquivalence B W S hW hS h Y.1).functor.sheafPushforwardContinuous
          RingCat.{u} (SmallEtale.topology B W hW Y.1)
          (SmallEtale.topology B S hS (relocalizeSpaceSE B W S hW hS h Y).1)).obj
        (smallEtaleRingSheaf B S hS (relocalizeSpaceSE B W S hW hS h Y).1
          (relocalizeSpaceSE B W S hW hS h Y).2) :=
  𝟙 _

/-- Reading a module on `Λ Y` back on `Y`: the direct image along the equivalence of small étale
sites, in the spelling of the structure sheaves. -/
def relocalizeModulesRestriction :
    SheafOfModules.{u} (smallEtaleRingSheaf B S hS (relocalizeSpaceSE B W S hW hS h Y).1
        (relocalizeSpaceSE B W S hW hS h Y).2) ⥤
      SheafOfModules.{u} (smallEtaleRingSheaf B W hW Y.1 Y.2) :=
  SheafOfModules.pushforward.{u} (relocalizeRingMap B W S hW hS h Y)

/-- The inverse of `AlgebraicGeometry.Space.relocalizeModulesEquivalenceSE` is
`AlgebraicGeometry.Space.relocalizeModulesRestriction`. -/
theorem relocalizeModulesEquivalence_inverse_eq_restriction :
    (relocalizeModulesEquivalenceSE B W S hW hS h Y.2
      (relocalizeSpaceSE B W S hW hS h Y).2).inverse =
      relocalizeModulesRestriction B W S hW hS h Y :=
  rfl

/-- The adjunction of the equivalence `Mod(𝒪_Y) ≌ Mod(𝒪_{Λ Y})`, with its right adjoint
written as `AlgebraicGeometry.Space.relocalizeModulesRestriction`. -/
def relocalizeModulesAdjunction :
    (relocalizeModulesEquivalenceSE B W S hW hS h Y.2
      (relocalizeSpaceSE B W S hW hS h Y).2).functor ⊣
      relocalizeModulesRestriction B W S hW hS h Y :=
  (relocalizeModulesEquivalenceSE B W S hW hS h Y.2
    (relocalizeSpaceSE B W S hW hS h Y).2).toAdjunction

end Restriction

variable {Y Z : AlgebraicSpaces B W hW} (φ : Y ⟶ Z) (hφ : yoneda.relativelyRepresentable φ.hom)

/-- `Λ` of the base change square of a chart `V` of `Z` along `φ`, read with representable
corners: a base change of `Λ φ` along the chart of `Λ Z` attached to `V`. -/
theorem isPullback_relocalize_baseChangeSE (V : SmallEtale B W hW Z.1) :
    IsPullback
      ((OverShriek.relocalizeYonedaIso h).inv.app (hφ.pullback V.obj.hom) ≫
        (OverShriek.relocalizePresheafFunctor h).map (hφ.fst V.obj.hom))
      (yoneda.map ((Over.map h).map (hφ.snd V.obj.hom)))
      (relocalizeHomSE B W S hW hS h φ).hom
      ((OverShriek.relocalizeYonedaIso h).inv.app V.obj.left ≫
        (OverShriek.relocalizePresheafFunctor h).map V.obj.hom) := by
  refine ((hφ.isPullback V.obj.hom).map (OverShriek.relocalizePresheafFunctor h)).of_iso
    ((OverShriek.relocalizeYonedaIso h).app _) (Iso.refl _)
    ((OverShriek.relocalizeYonedaIso h).app _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · exact (OverShriek.relocalizeYonedaIso h).hom.naturality (hφ.snd V.obj.hom)
  · simp
  · simp

/-- The same square, with the charts of `Λ Y` and `Λ Z` read through the equivalences of small
étale sites. -/
theorem isPullback_relocalize_baseChangeSE' (V : SmallEtale B W hW Z.1) :
    IsPullback
      ((SmallEtale.relocalizeEquivalence B W S hW hS h Y.1).functor.obj
        ((smallBaseChange B W hW φ hφ).obj V)).obj.hom
      (yoneda.map ((Over.map h).map (hφ.snd V.obj.hom)))
      (relocalizeHomSE B W S hW hS h φ).hom
      ((SmallEtale.relocalizeEquivalence B W S hW hS h Z.1).functor.obj V).obj.hom := by
  have h1 := relocalizeChart_eq B W S hW hS h Y.1 ((smallBaseChange B W hW φ hφ).obj V).obj.hom
  have h2 := relocalizeChart_eq B W S hW hS h Z.1 V.obj.hom
  refine (isPullback_relocalize_baseChangeSE B W S hW hS h φ hφ V).of_iso (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact h1.symm.trans (Category.id_comp _).symm
  · exact (Category.id_comp _).symm
  · exact (Category.id_comp _).symm
  · exact h2.symm.trans (Category.id_comp _).symm

/-- The representability of `Λ φ`. -/
abbrev relocalizeRepSE := relativelyRepresentable_relocalizeHomSE B W S hW hS h φ hφ

/-- The comparison of the two base changes of a chart `V` of `Z`, on objects of the big fppf
site of `S`: the base change of the chart of `Λ Z` along `Λ φ` is the relocalization of the base
change of `V` along `φ`. -/
noncomputable def relocalizeBaseChangeOverIsoSE (V : SmallEtale B W hW Z.1) :
    (relocalizeRepSE B W S hW hS h φ hφ).pullback
        ((SmallEtale.relocalizeEquivalence B W S hW hS h Z.1).functor.obj V).obj.hom ≅
      (Over.map h).obj (hφ.pullback V.obj.hom) :=
  Yoneda.fullyFaithful.preimageIso
    (((relocalizeRepSE B W S hW hS h φ hφ).isPullback _).isoIsPullback _ _
      (isPullback_relocalize_baseChangeSE' B W S hW hS h φ hφ V))

/-- The comparison `relocalizeBaseChangeOverIsoSE` followed by the structure map of the relocalized
base change of `V` along `φ` is the first projection of the base change along `Λ φ`. -/
theorem relocalizeBaseChangeOverIso_hom_fstSE (V : SmallEtale B W hW Z.1) :
    yoneda.map (relocalizeBaseChangeOverIsoSE B W S hW hS h φ hφ V).hom ≫
        ((SmallEtale.relocalizeEquivalence B W S hW hS h Y.1).functor.obj
          ((smallBaseChange B W hW φ hφ).obj V)).obj.hom =
      (relocalizeRepSE B W S hW hS h φ hφ).fst
        ((SmallEtale.relocalizeEquivalence B W S hW hS h Z.1).functor.obj V).obj.hom := by
  change yoneda.map ((Yoneda.fullyFaithful (C := BigFppfOver B S hS)).preimage _) ≫ _ = _
  rw [(Yoneda.fullyFaithful (C := BigFppfOver B S hS)).map_preimage]
  exact ((relocalizeRepSE B W S hW hS h φ hφ).isPullback _).isoIsPullback_hom_fst _ _
    (isPullback_relocalize_baseChangeSE' B W S hW hS h φ hφ V)

/-- The comparison `relocalizeBaseChangeOverIsoSE` followed by the relocalized second projection of
the base change of `V` along `φ` is the second projection of the base change along `Λ φ`. -/
theorem relocalizeBaseChangeOverIso_hom_sndSE (V : SmallEtale B W hW Z.1) :
    (relocalizeBaseChangeOverIsoSE B W S hW hS h φ hφ V).hom ≫ (Over.map h).map (hφ.snd V.obj.hom) =
      (relocalizeRepSE B W S hW hS h φ hφ).snd
        ((SmallEtale.relocalizeEquivalence B W S hW hS h Z.1).functor.obj V).obj.hom := by
  refine (Yoneda.fullyFaithful (C := BigFppfOver B S hS)).map_injective ?_
  change yoneda.map ((Yoneda.fullyFaithful (C := BigFppfOver B S hS)).preimage _ ≫ _) = _
  rw [Functor.map_comp, (Yoneda.fullyFaithful (C := BigFppfOver B S hS)).map_preimage]
  exact ((relocalizeRepSE B W S hW hS h φ hφ).isPullback _).isoIsPullback_hom_snd _ _
    (isPullback_relocalize_baseChangeSE' B W S hW hS h φ hφ V)

/-- **Base change of charts commutes with relocalization**, on objects. -/
noncomputable def relocalizeBaseChangeObjIsoSE (V : SmallEtale B W hW Z.1) :
    (smallBaseChange B S hS (relocalizeHomSE B W S hW hS h φ)
          (relocalizeRepSE B W S hW hS h φ hφ)).obj
        ((SmallEtale.relocalizeEquivalence B W S hW hS h Z.1).functor.obj V) ≅
      (SmallEtale.relocalizeEquivalence B W S hW hS h Y.1).functor.obj
        ((smallBaseChange B W hW φ hφ).obj V) :=
  ObjectProperty.isoMk _
    (CostructuredArrow.isoMk (relocalizeBaseChangeOverIsoSE B W S hW hS h φ hφ V)
      (relocalizeBaseChangeOverIso_hom_fstSE B W S hW hS h φ hφ V))

/-- **Base change of charts commutes with relocalization**: the two functors from the small
étale site of `Z` to that of `Λ Y` — relocalize, then base change along `Λ φ`; base change along
`φ`, then relocalize — are isomorphic. -/
noncomputable def relocalizeBaseChangeIsoSE :
    (SmallEtale.relocalizeEquivalence B W S hW hS h Z.1).functor ⋙
        smallBaseChange B S hS (relocalizeHomSE B W S hW hS h φ)
          (relocalizeRepSE B W S hW hS h φ hφ) ≅
      smallBaseChange B W hW φ hφ ⋙ (SmallEtale.relocalizeEquivalence B W S hW hS h Y.1).functor :=
  NatIso.ofComponents (relocalizeBaseChangeObjIsoSE B W S hW hS h φ hφ) (by
    intro V V' k
    refine ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ ?_)
    let k₁ := ((SmallEtale.relocalizeEquivalence B W S hW hS h Z.1).functor ⋙
      smallBaseChange B S hS (relocalizeHomSE B W S hW hS h φ)
        (relocalizeRepSE B W S hW hS h φ hφ)).map k
    let k₂ := (smallBaseChange B W hW φ hφ ⋙
      (SmallEtale.relocalizeEquivalence B W S hW hS h Y.1).functor).map k
    have e1 := relocalizeBaseChangeOverIso_hom_fstSE B W S hW hS h φ hφ V'
    have e2 := relocalizeBaseChangeOverIso_hom_fstSE B W S hW hS h φ hφ V
    have e3 := relocalizeBaseChangeOverIso_hom_sndSE B W S hW hS h φ hφ V'
    have e4 := relocalizeBaseChangeOverIso_hom_sndSE B W S hW hS h φ hφ V
    have w1 := CostructuredArrow.w k₁.hom
    have w2 := CostructuredArrow.w k₂.hom
    have m1 := smallBaseChange_map_snd B S hS (relocalizeHomSE B W S hW hS h φ)
      (relocalizeRepSE B W S hW hS h φ hφ)
      ((SmallEtale.relocalizeEquivalence B W S hW hS h Z.1).functor.map k)
    have m0 := smallBaseChange_map_snd B W hW φ hφ k
    have hsnd : (k₁.hom.left ≫ (relocalizeBaseChangeOverIsoSE B W S hW hS h φ hφ V').hom) ≫
          (Over.map h).map (hφ.snd V'.obj.hom) =
        ((relocalizeBaseChangeOverIsoSE B W S hW hS h φ hφ V).hom ≫ k₂.hom.left) ≫
          (Over.map h).map (hφ.snd V'.obj.hom) :=
      (Category.assoc _ _ _).trans ((congrArg (k₁.hom.left ≫ ·) e3).trans (m1.trans
        ((congrArg (· ≫ _) e4.symm).trans ((Category.assoc _ _ _).trans
          ((congrArg (_ ≫ ·) ((Functor.map_comp (Over.map h) _ _).symm.trans
            ((congrArg (Over.map h).map m0.symm).trans (Functor.map_comp (Over.map h) _ _)))).trans
            (Category.assoc _ _ _).symm)))))
    refine (Yoneda.fullyFaithful (C := BigFppfOver B S hS)).map_injective
      ((isPullback_relocalize_baseChangeSE' B W S hW hS h φ hφ V').hom_ext ?_ ?_)
    · exact (congrArg (· ≫ _) (Functor.map_comp _ _ _)).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) e1).trans (w1.trans (e2.symm.trans ((congrArg (_ ≫ ·) w2.symm).trans
          ((Category.assoc _ _ _).symm.trans
            (congrArg (· ≫ _) (Functor.map_comp _ _ _).symm)))))))
    · exact (Functor.map_comp _ _ _).symm.trans ((congrArg yoneda.map hsnd).trans
        (Functor.map_comp _ _ _)))

/-- The comparison of charts is inverse to the base change of `V` on underlying morphisms. -/
theorem relocalizeBaseChangeOverIso_inv_sndSE (V : SmallEtale B W hW Z.1) :
    (relocalizeBaseChangeOverIsoSE B W S hW hS h φ hφ V).inv ≫
      (relocalizeRepSE B W S hW hS h φ hφ).snd
        ((SmallEtale.relocalizeEquivalence B W S hW hS h Z.1).functor.obj V).obj.hom =
      (Over.map h).map (hφ.snd V.obj.hom) :=
  (congrArg (_ ≫ ·) (relocalizeBaseChangeOverIso_hom_sndSE B W S hW hS h φ hφ V).symm).trans
    (Iso.inv_hom_id_assoc _ _)

section PushforwardSquare

/-- Base change of charts along `φ` followed by relocalization is continuous. -/
theorem isContinuous_smallBaseChange_comp_relocalizeEquivalence_functor :
    (smallBaseChange B W hW φ hφ ⋙
      (SmallEtale.relocalizeEquivalence B W S hW hS h Y.1).functor).IsContinuous
      (SmallEtale.topology B W hW Z.1) (SmallEtale.topology B S hS _) :=
  have := isContinuous_smallBaseChange B W hW φ hφ
  Functor.isContinuous_comp _ _ _ (SmallEtale.topology B W hW Y.1) _

/-- Relocalization followed by base change of charts along `Λ φ` is continuous. -/
theorem isContinuous_relocalizeEquivalence_functor_comp_smallBaseChange :
    ((SmallEtale.relocalizeEquivalence B W S hW hS h Z.1).functor ⋙ smallBaseChange B S hS
      (relocalizeHomSE B W S hW hS h φ) (relocalizeRepSE B W S hW hS h φ hφ)).IsContinuous
      (SmallEtale.topology B W hW Z.1) (SmallEtale.topology B S hS _) :=
  have := isContinuous_smallBaseChange B S hS (relocalizeHomSE B W S hW hS h φ)
    (relocalizeRepSE B W S hW hS h φ hφ)
  Functor.isContinuous_comp _ _ _ (SmallEtale.topology B S hS _) _

/-- The structure maps of the sheaves of rings round the square of
`AlgebraicGeometry.Space.relocalizeBaseChangeIsoSE` are compatible: both are pulling regular
functions back along the cartesian projection of a base-changed chart. -/
theorem relocalizeSharp_compat :
    haveI := isContinuous_smallBaseChange B S hS (relocalizeHomSE B W S hW hS h φ)
      (relocalizeRepSE B W S hW hS h φ hφ)
    haveI := isContinuous_smallBaseChange B W hW φ hφ
    haveI := isContinuous_smallBaseChange_comp_relocalizeEquivalence_functor B W S hW hS h φ hφ
    haveI := isContinuous_relocalizeEquivalence_functor_comp_smallBaseChange B W S hW hS h φ hφ
    (relocalizeRingMap B W S hW hS h Z ≫
        ((SmallEtale.relocalizeEquivalence B W S hW hS h Z.1).functor.sheafPushforwardContinuous
          RingCat.{u} (SmallEtale.topology B W hW Z.1) (SmallEtale.topology B S hS _)).map
          (smallBaseChangeSharp B S hS (relocalizeHomSE B W S hW hS h φ)
            (relocalizeRepSE B W S hW hS h φ hφ))) ≫
      (Functor.sheafPushforwardContinuousNatTrans
          (relocalizeBaseChangeIsoSE B W S hW hS h φ hφ).symm.hom RingCat.{u}
          (SmallEtale.topology B W hW Z.1) (SmallEtale.topology B S hS _)).app
          (smallEtaleRingSheaf B S hS (relocalizeSpaceSE B W S hW hS h Y).1
            (relocalizeSpaceSE B W S hW hS h Y).2) =
      smallBaseChangeSharp B W hW φ hφ ≫
        ((smallBaseChange B W hW φ hφ).sheafPushforwardContinuous RingCat.{u}
          (SmallEtale.topology B W hW Z.1) (SmallEtale.topology B W hW Y.1)).map
          (relocalizeRingMap B W S hW hS h Y) := by
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun U => ?_))
  exact ((forget₂ CommRingCat RingCat).map_comp _ _).symm.trans
    (congrArg (forget₂ CommRingCat RingCat).map ((Scheme.Γ.map_comp _ _).symm.trans
      (congrArg Scheme.Γ.map (congrArg Quiver.Hom.op
        (((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans
          (congrArg (BigFppfOver.toScheme B S hS).map
            (relocalizeBaseChangeOverIso_inv_sndSE B W S hW hS h φ hφ U.unop)))))))

/-- **Direct images commute with relocalization**: for a representable `φ`, the direct image
along `Λ φ` followed by the equivalence for `Z` is the equivalence for `Y` followed by the direct
image along `φ`. -/
noncomputable def relocalizePushforwardIsoSE :
    smallBaseChangeModulePushforward B S hS (relocalizeHomSE B W S hW hS h φ)
        (relocalizeRepSE B W S hW hS h φ hφ) ⋙ relocalizeModulesRestriction B W S hW hS h Z ≅
      relocalizeModulesRestriction B W S hW hS h Y ⋙ smallBaseChangeModulePushforward B W hW φ hφ :=
  haveI := isContinuous_smallBaseChange B S hS (relocalizeHomSE B W S hW hS h φ)
    (relocalizeRepSE B W S hW hS h φ hφ)
  haveI := isContinuous_smallBaseChange B W hW φ hφ
  haveI := isContinuous_smallBaseChange_comp_relocalizeEquivalence_functor B W S hW hS h φ hφ
  haveI := isContinuous_relocalizeEquivalence_functor_comp_smallBaseChange B W S hW hS h φ hφ
  Stacks.SheafOfModules.pushforwardSquareIsoOfIso (smallBaseChangeSharp B W hW φ hφ)
    (smallBaseChangeSharp B S hS (relocalizeHomSE B W S hW hS h φ)
      (relocalizeRepSE B W S hW hS h φ hφ))
    (relocalizeRingMap B W S hW hS h Z) (relocalizeRingMap B W S hW hS h Y)
    (relocalizeBaseChangeIsoSE B W S hW hS h φ hφ) (relocalizeSharp_compat B W S hW hS h φ hφ)

end PushforwardSquare

/-- **Inverse images commute with relocalization**: for a representable morphism `φ : Y ⟶ Z`
of algebraic spaces over `T`, the inverse image along `φ` followed by the equivalence
`Mod(𝒪_Y) ≌ Mod(𝒪_{Λ Y})` is the equivalence for `Z` followed by the inverse image along `Λ φ`. -/
noncomputable def relocalizeModulePullbackIsoSE :
    modulePullback B W hW φ ⋙
        (relocalizeModulesEquivalenceSE B W S hW hS h Y.2
          (relocalizeSpaceSE B W S hW hS h Y).2).functor ≅
      (relocalizeModulesEquivalenceSE B W S hW hS h Z.2
          (relocalizeSpaceSE B W S hW hS h Z).2).functor ⋙
        modulePullback B S hS (relocalizeHomSE B W S hW hS h φ) :=
  Adjunction.leftAdjointUniq
    ((((modulePullbackAdjunction B W hW φ).ofNatIsoRight
        (modulePushforwardChartIso B W hW φ hφ)).comp
      (relocalizeModulesAdjunction B W S hW hS h Y)))
    (((relocalizeModulesAdjunction B W S hW hS h Z).comp
      ((modulePullbackAdjunction B S hS (relocalizeHomSE B W S hW hS h φ)).ofNatIsoRight
        (modulePushforwardChartIso B S hS (relocalizeHomSE B W S hW hS h φ)
          (relocalizeRepSE B W S hW hS h φ hφ)))).ofNatIsoRight
      (relocalizePushforwardIsoSE B W S hW hS h φ hφ))


end AlgebraicGeometry.Space

end
