module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Unramified

/-!
# Descent of an étale-local property along a scheme chart of the target

Let `S` be a scheme contained in a big fppf site `B` and let `P` be a property of morphisms of
schemes which is étale local on the source and target in the sense of Stacks 04QZ. For a morphism
`f : F ⟶ G` of algebraic spaces over `S` and a surjective étale scheme chart `a : h_T ⟶ G` of its
target, the every-chart condition `AlgebraicGeometry.Space.HoldsOnEveryEtaleChart` of Stacks 03MJ
*descends* along `a`: if it holds for the base change `F ×_G h_T ⟶ h_T`, it holds for `f`.
This applies in particular to `AlgebraicGeometry.Space.IsUnramified` (Stacks 03ZH, part (1)).

## Main results

* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_of_etaleChart`: the descent.
* `AlgebraicGeometry.Space.isUnramified_of_etaleChart`: its instance at unramifiedness.
* `AlgebraicGeometry.Space.unramifiedMorphismProperty`: unramifiedness as a property of
  morphisms of the category of algebraic spaces over `S`, with its `RespectsIso` and
  `IsStableUnderComposition` instances.
* `AlgebraicGeometry.Space.unramifiedMorphismProperty_of_pullbackSnd_atlas`: the descent
  hypothesis of `AlgebraicGeometry.Stack.prop_comp_of_atlasDescent` at unramifiedness.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (P : MorphismProperty Scheme.{u}) {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- If `P` is étale local on the source and target, `a : h_T ⟶ G` is a surjective étale chart of
the target of a morphism `f : F ⟶ G` of algebraic spaces over `S`, and `P` holds on every étale
chart of the base change of `f` along `a`, then `P` holds on every étale chart of `f`. -/
theorem holdsOnEveryEtaleChart_of_etaleChart (hP : IsEtaleLocalOnSourceAndTarget P)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G)
    {T : BigFppfOver B S hS} {a : yoneda.obj T ⟶ G}
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (h : HoldsOnEveryEtaleChart B S hS P (pullback.snd f a)) :
    HoldsOnEveryEtaleChart B S hS P f := by
  have hbc (Q : MorphismProperty Scheme.{u}) :
      (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf
        |>.IsStableUnderBaseChange := MorphismProperty.relative_isStableUnderBaseChange _
  have hmulE := Space.isMultiplicative_presheaf_etale B S hS
  have := hmulE.toIsStableUnderComposition
  have := hmulE.toContainsIdentities
  have hcs : MorphismProperty.IsStableUnderComposition
      ((MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf) := by
    have : MorphismProperty.IsStableUnderComposition (@AlgebraicGeometry.Surjective.{u}) :=
      MorphismProperty.IsMultiplicative.toIsStableUnderComposition
    have : MorphismProperty.IsStableUnderComposition
        (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)) :=
      MorphismProperty.IsStableUnderComposition.inverseImage _
    infer_instance
  have hT : IsAlgebraicSpace B S hS (yoneda.obj T) := isAlgebraicSpace_yoneda B S hS T
  have hPB : IsAlgebraicSpace B S hS (pullback f a) :=
    isAlgebraicSpace_pullback B S hS f a hF hT hG
  obtain ⟨U, b, hbsurj, hbetale⟩ := hPB.exists_atlas
  have hsq : IsPullback (pullback.fst f a) (pullback.snd f a) f a := IsPullback.of_hasPullback f a
  have hfst : ∀ Q : MorphismProperty Scheme.{u},
      (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf a →
        (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf
          (pullback.fst f a) := fun Q hQ =>
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip hQ
  set m : U ⟶ T := yoneda.preimage (b ≫ pullback.snd f a) with hm
  have hmap : yoneda.map m = b ≫ pullback.snd f a := yoneda.map_preimage _
  refine (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS P hP hF hG f).2
    ⟨U, T, b ≫ pullback.fst f a, a, m, ?_, hetale, ?_, ?_, ?_⟩
  · exact MorphismProperty.comp_mem _ _ _ hbetale (hfst _ hetale)
  · exact MorphismProperty.comp_mem _ _ _ hbsurj (hfst _ hsurj)
  · rw [hmap, Category.assoc, Category.assoc, hsq.w]
  · refine h U T b (𝟙 (yoneda.obj T)) m hbetale (MorphismProperty.id_mem _ _) ?_
    rw [hmap, Category.comp_id]

/-- If `a : h_T ⟶ G` is a surjective étale chart of the target of a morphism `f : F ⟶ G` of
algebraic spaces over `S` and the base change of `f` along `a` is unramified, then `f` is
unramified. -/
theorem isUnramified_of_etaleChart (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G)
    {T : BigFppfOver B S hS} {a : yoneda.obj T ⟶ G}
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (h : IsUnramified B S hS (pullback.snd f a)) :
    IsUnramified B S hS f :=
  holdsOnEveryEtaleChart_of_etaleChart B S hS _ unramified_isEtaleLocalOnSourceAndTarget hF hG f
    hsurj hetale h

/-! ### Unramifiedness as a property of morphisms of algebraic spaces -/

variable {X Y : AlgebraicSpaces B S hS}

/-- A property of morphisms of the category of algebraic spaces over `S` which respects
isomorphisms may be read on the presheaf fibre product rather than on the chosen fibre product of
the category: the two are identified by the comparison isomorphism of Stacks 02X2. -/
theorem prop_pullbackSnd_homMk_iff (Q : MorphismProperty (AlgebraicSpaces B S hS))
    [Q.RespectsIso] (k : X ⟶ Y) {T : BigFppfOver B S hS} (a : yoneda.obj T ⟶ Y.obj) :
    Q (Limits.pullback.snd k (ObjectProperty.homMk a :
        (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS) ⟶ Y)) ↔
      Q (ObjectProperty.homMk (Limits.pullback.snd k.hom a) :
        AlgebraicSpaces.fiberProduct B S hS k (ObjectProperty.homMk a :
            (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ :
              AlgebraicSpaces B S hS) ⟶ Y) ⟶
          ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩) := by
  have hp := AlgebraicSpaces.isPullback_fiberProduct B S hS k
    (ObjectProperty.homMk a : (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ :
      AlgebraicSpaces B S hS) ⟶ Y)
  rw [← Q.cancel_left_of_respectsIso hp.isoPullback.hom
    (Limits.pullback.snd k (ObjectProperty.homMk a :
      (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS) ⟶ Y)),
    hp.isoPullback_hom_snd]
  exact Iff.rfl

/-- Unramifiedness, as a property of morphisms of the category of algebraic spaces over `S`. -/
abbrev unramifiedMorphismProperty : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ k => IsUnramified B S hS k.hom

/-- Unramifiedness of morphisms of algebraic spaces respects isomorphisms. -/
instance unramifiedMorphismProperty_respectsIso :
    (unramifiedMorphismProperty B S hS).RespectsIso :=
  (isUnramified_isStableUnderBaseChange B S hS).respectsIso

/-- A composite of unramified morphisms of algebraic spaces is unramified. -/
instance unramifiedMorphismProperty_isStableUnderComposition :
    (unramifiedMorphismProperty B S hS).IsStableUnderComposition where
  comp_mem := fun {X' Y' Z'} k l hk hl =>
    isUnramified_comp B S hS X'.property Y'.property Z'.property k.hom l.hom hk hl

/-- Unramifiedness of morphisms of algebraic spaces over `S` may be tested on the base change to
a surjective étale scheme chart of the target. -/
theorem unramifiedMorphismProperty_of_pullbackSnd_atlas (k : X ⟶ Y)
    {T : BigFppfOver B S hS} {a : yoneda.obj T ⟶ Y.obj}
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (h : unramifiedMorphismProperty B S hS (Limits.pullback.snd k
      (ObjectProperty.homMk a : (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ :
        AlgebraicSpaces B S hS) ⟶ Y))) :
    unramifiedMorphismProperty B S hS k :=
  isUnramified_of_etaleChart B S hS X.property Y.property k.hom hsurj hetale
    ((prop_pullbackSnd_homMk_iff B S hS _ k a).1 h)

end AlgebraicGeometry.Space

end
