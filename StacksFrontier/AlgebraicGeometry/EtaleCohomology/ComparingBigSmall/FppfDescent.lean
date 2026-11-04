module

public import Mathlib.CategoryTheory.Monad.Comonadicity
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.ChangeOfTopologyDirectImage
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Basic
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.FppfToEtaleSquares
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.CoveringSieves
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.LocallyQuasiFiniteRefinement
public import StacksFrontier.CategoryTheory.Adjunction.CategoricalPullbackFullyFaithful
public import StacksFrontier.CategoryTheory.Sites.Localization.PushforwardAdjunction

/-!
# Fppf descent of étale sheaves through the big fppf site

Let `B` be a chosen big fppf site and `f : X ⟶ Y` a morphism of it. Write `a_X` for the
comparison of the big fppf topos of `X` with the small étale topos of `X`
(`AlgebraicGeometry.fppfToSmallEtaleMorphism`), `f_small` for the morphism of small étale topoi
and `f_{big,fppf}` for that of big fppf topoi. Stacks 0DEU says that if `f` is flat, locally of
finite presentation and surjective, the functor
`Sh(Y_étale) ⥤ {(G, H, α) | α : a_X⁻¹G ≅ f_{big,fppf}⁻¹H}`,
`F ↦ (f_small⁻¹F, a_Y⁻¹F, can)`, is an equivalence of categories.

## Main definitions

* `AlgebraicGeometry.fppfSmallEtaleInverseImageCommIso`: the canonical isomorphism
  `f_small⁻¹ ⋙ a_X⁻¹ ≅ a_Y⁻¹ ⋙ f_{big,fppf}⁻¹` of inverse images around the square of Stacks
  0DDM.

## Main results

* `AlgebraicGeometry.isEquivalence_fppfSmallEtaleTripleFunctor`: for `f` flat, locally of finite
  presentation and surjective, `F ↦ (f_small⁻¹F, a_Y⁻¹F, can)` is an equivalence onto the
  category of triples.
* `AlgebraicGeometry.isIso_fppfToSmallEtaleMorphism_unit`: `a_X⁻¹` is fully faithful
  (Stacks 0DDL), with instances `Full` and `Faithful`.
* `AlgebraicGeometry.isIso_of_forall_isIso_bigFppfRestriction`: restriction along the members
  of a flat, locally finitely presented, jointly surjective family detects isomorphisms of big
  fppf sheaves.
* `AlgebraicGeometry.fppfToSmallEtale_essImage_of_restriction_of_isFinite`,
  `AlgebraicGeometry.fppfToSmallEtale_essImage_of_forall_restriction_of_etale` and
  `AlgebraicGeometry.fppfToSmallEtale_essImage_of_restriction`: a big fppf sheaf on `Y` whose
  restriction to `X` lies in the essential image of `a_X⁻¹` lies in that of `a_Y⁻¹`: for `f`
  finite flat surjective, for étale coverings, and for `f` flat, locally of finite presentation
  and surjective.

## Implementation notes

By `Stacks.CategoryTheory.modificationGluingFunctor_isEquivalence_of_snd` the equivalence
reduces to: `H` lies in the essential image of `a_Y⁻¹` as soon as `f_{big,fppf}⁻¹H` lies in that
of `a_X⁻¹`. This property is étale local on `Y`, through the counit of `a_Y⁻¹ ⊣ a_{Y,*}`, so no
glueing of triples is needed. By Stacks 0DET it reduces to a finite locally free `f`, where it
follows from Beck's unit equalizer for restriction along `f` and Stacks 0DDN for finite morphisms.

## References

* [Stacks Project, Tag 0DEU](https://stacks.math.columbia.edu/tag/0DEU)
* [Stacks Project, Tag 0DDL](https://stacks.math.columbia.edu/tag/0DDL)
* [Stacks Project, Tag 0DDM](https://stacks.math.columbia.edu/tag/0DDM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-! ### The comparison with the small étale topos is fully faithful -/

/-- The unit of `π_S⁻¹ ⊣ π_{S,*}` is an isomorphism. -/
public theorem isIso_bigEtaleToSmallEtaleMorphism_unit (E : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : E.Contains S) : IsIso (bigEtaleToSmallEtaleMorphism E S hS).adj.unit := by
  let i := smallEtaleToBigEtaleMorphism E (E.obj S hS) (E.obj S hS) (𝟙 (E.obj S hS))
  let p := bigEtaleToSmallEtaleMorphism E S hS
  let adj₂ := i.adj.ofNatIsoLeft (inclusionInverseImageIsoProjectionPushforward E S hS)
  have hc : IsIso adj₂.counit :=
    adj₂.isIso_counit_of_iso (projectionCompInclusionPushforwardIso E S hS)
  exact (Adjunction.Triple.isIso_unit_iff_isIso_counit ⟨p.adj, adj₂⟩).2 hc

variable (B : BigFppfSite.{u})

/-- The unit of `a_X⁻¹ ⊣ a_{X,*}` is an isomorphism, so `a_X⁻¹` is fully faithful (Stacks 0DDL). -/
public theorem isIso_fppfToSmallEtaleMorphism_unit (X : B.Schemes) :
    IsIso (fppfToSmallEtaleMorphism B X).adj.unit := by
  have := isIso_bigEtaleToSmallEtaleMorphism_unit (associatedBigEtaleSite B) X.1 X.2
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun F ↦ ?_
  have := isIso_fppfToBigEtale_unit_app B X F
  show IsIso (((bigEtaleToSmallEtaleMorphism (associatedBigEtaleSite B) X.1 X.2).adj.comp
    (fppfToBigEtaleMorphism B X).adj).unit.app F)
  rw [Adjunction.comp_unit_app]
  infer_instance

/-- `a_X⁻¹` is fully faithful (Stacks 0DDL). -/
public def fppfToSmallEtaleInverseImageFullyFaithful (X : B.Schemes) :
    (fppfToSmallEtaleMorphism B X).inverseImage.FullyFaithful :=
  have := isIso_fppfToSmallEtaleMorphism_unit B X
  (fppfToSmallEtaleMorphism B X).adj.fullyFaithfulLOfIsIsoUnit

/-- `a_X⁻¹` is full. -/
public instance (X : B.Schemes) : (fppfToSmallEtaleMorphism B X).inverseImage.Full :=
  (fppfToSmallEtaleInverseImageFullyFaithful B X).full

/-- `a_X⁻¹` is faithful. -/
public instance (X : B.Schemes) : (fppfToSmallEtaleMorphism B X).inverseImage.Faithful :=
  (fppfToSmallEtaleInverseImageFullyFaithful B X).faithful

/-- `a_X⁻¹` preserves finite limits. -/
public instance (X : B.Schemes) :
    PreservesFiniteLimits (fppfToSmallEtaleMorphism B X).inverseImage :=
  (fppfToSmallEtaleMorphism B X).preservesFiniteLimits

/-! ### The canonical isomorphism of inverse images -/

/-- The canonical isomorphism `can : f_small⁻¹ ⋙ a_X⁻¹ ≅ a_Y⁻¹ ⋙ f_{big,fppf}⁻¹` of the square
of topoi of Stacks 0DDM: the conjugate of the identification
`AlgebraicGeometry.bigFppfSmallEtale_pushforwardCommIso` of the composite direct images. -/
public def fppfSmallEtaleInverseImageCommIso {X Y : B.Schemes} (f : X ⟶ Y) :
    (smallEtaleMorphism B f).inverseImage ⋙ (fppfToSmallEtaleMorphism B X).inverseImage ≅
      (fppfToSmallEtaleMorphism B Y).inverseImage ⋙ (bigFppfMorphism B X Y f).inverseImage :=
  ((conjugateIsoEquiv ((smallEtaleMorphism B f).comp (fppfToSmallEtaleMorphism B X)).adj
    ((fppfToSmallEtaleMorphism B Y).comp (bigFppfMorphism B X Y f)).adj).symm
    (bigFppfSmallEtale_pushforwardCommIso B f)).symm

/-! ### Restriction of big fppf sheaves -/

/-- Restriction along `f` carries a sheaf in the essential image of `a_Y⁻¹` to one in the
essential image of `a_X⁻¹`: `f_{big,fppf}⁻¹ a_Y⁻¹ F ≅ a_X⁻¹ f_small⁻¹ F`. -/
public theorem fppfToSmallEtale_essImage_restriction {X Y : B.Schemes} (f : X ⟶ Y)
    {H : Sheaf (B.topology.over Y) (Type (u + 1))}
    (hH : (fppfToSmallEtaleMorphism B Y).inverseImage.essImage H) :
    (fppfToSmallEtaleMorphism B X).inverseImage.essImage
      (((Over.map f).sheafPushforwardContinuous (Type (u + 1)) (B.topology.over X)
        (B.topology.over Y)).obj H) := by
  obtain ⟨F, ⟨e⟩⟩ := hH
  exact ⟨(smallEtaleMorphism B f).inverseImage.obj F,
    ⟨(fppfSmallEtaleInverseImageCommIso B f).app F ≪≫
      (bigFppfMorphism B X Y f).inverseImage.mapIso e ≪≫
      ((Over.map f).sheafPullbackCocontinuousIsoSheafPushforwardContinuous (Type (u + 1))
        (B.topology.over X) (B.topology.over Y)).app H⟩⟩

/-- Restriction along a composite is the composite of the restrictions. -/
public def bigFppfRestrictionCompIso {X Y Z : B.Schemes} (l : X ⟶ Y) (f : Y ⟶ Z) :
    (Over.map f).sheafPushforwardContinuous (Type (u + 1)) (B.topology.over Y)
        (B.topology.over Z) ⋙
      (Over.map l).sheafPushforwardContinuous (Type (u + 1)) (B.topology.over X)
        (B.topology.over Y) ≅
    (Over.map (l ≫ f)).sheafPushforwardContinuous (Type (u + 1)) (B.topology.over X)
      (B.topology.over Z) :=
  Functor.sheafPushforwardContinuousComp' (Over.mapComp l f).symm (Type (u + 1))
    (B.topology.over X) (B.topology.over Y) (B.topology.over Z)

/-- Restriction along a flat, locally finitely presented, jointly surjective family detects
isomorphisms of big fppf sheaves. -/
public theorem isIso_of_forall_isIso_bigFppfRestriction {Y : B.Schemes} {I : Type (u + 1)}
    (V : I → B.Schemes) (j : ∀ i, V i ⟶ Y) (hflat : ∀ i, Flat (B.inclusion.map (j i)))
    (hlfp : ∀ i, LocallyOfFinitePresentation (B.inclusion.map (j i)))
    (hsurj : ∀ y : B.inclusion.obj Y, ∃ i, y ∈ Set.range (B.inclusion.map (j i)))
    {H H' : Sheaf (B.topology.over Y) (Type (u + 1))} (φ : H ⟶ H')
    (h : ∀ i, IsIso (((Over.map (j i)).sheafPushforwardContinuous (Type (u + 1))
      (B.topology.over (V i)) (B.topology.over Y)).map φ)) :
    IsIso φ := by
  have hbij : ∀ (U : Over Y) (i : I), Function.Bijective
      (φ.hom.app (op (Over.mk (pullback.fst U.hom (j i) ≫ U.hom)))) := by
    intro U i
    have hi := h i
    have : IsIso (((Over.map (j i)).sheafPushforwardContinuous (Type (u + 1))
        (B.topology.over (V i)) (B.topology.over Y)).map φ).hom :=
      inferInstanceAs (IsIso ((sheafToPresheaf (B.topology.over (V i)) (Type (u + 1))).map
        (((Over.map (j i)).sheafPushforwardContinuous (Type (u + 1))
          (B.topology.over (V i)) (B.topology.over Y)).map φ)))
    have : IsIso ((((Over.map (j i)).sheafPushforwardContinuous (Type (u + 1))
        (B.topology.over (V i)) (B.topology.over Y)).map φ).hom.app
          (op (Over.mk (pullback.snd U.hom (j i))))) := inferInstance
    rw [← isIso_iff_bijective]
    have e : Over.mk (pullback.fst U.hom (j i) ≫ U.hom) =
        (Over.map (j i)).obj (Over.mk (pullback.snd U.hom (j i))) := by
      rw [pullback.condition]
      rfl
    rw [e]
    exact this
  have hcov : ∀ U : Over Y, Sieve.ofArrows
      (fun i ↦ (Over.mk (pullback.fst U.hom (j i) ≫ U.hom) : Over Y))
      (fun i ↦ (Over.homMk (pullback.fst U.hom (j i)) :
        Over.mk (pullback.fst U.hom (j i) ≫ U.hom) ⟶ U)) ∈ B.topology.over Y U := by
    intro U
    have hsq : ∀ i, IsPullback (B.inclusion.map (pullback.snd U.hom (j i)))
        (B.inclusion.map (pullback.fst U.hom (j i))) (B.inclusion.map (j i))
        (B.inclusion.map U.hom) := fun i ↦
      (IsPullback.of_hasPullback U.hom (j i)).flip.map B.inclusion
    refine mem_topology_of_family B Y.1 Y.2 (U := U) (fun i ↦ pullback U.hom (j i))
      (fun i ↦ pullback.fst U.hom (j i))
      (fun i ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback (hsq i) (hflat i))
      (fun i ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback (hsq i) (hlfp i)) ?_
    intro x
    obtain ⟨i, v, hv⟩ := hsurj (B.inclusion.map U.hom x)
    refine ⟨i, ?_⟩
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := B.inclusion.map U.hom) (g := B.inclusion.map (j i)) x v hv.symm
    let e := ((IsPullback.of_hasPullback U.hom (j i)).map B.inclusion).isoPullback
    refine ⟨e.inv z, ?_⟩
    rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst]
    exact hz
  have hsepH := fun U : Over Y ↦
    ((isSheaf_iff_isSheaf_of_type _ H.obj).1 H.property).isSeparated _ (hcov U)
  have hinj : ∀ U : Over Y, Function.Injective (φ.hom.app (op U)) := by
    intro U x y hxy
    refine (hsepH U).ext ?_
    rintro W k ⟨T, a, b, ⟨i⟩, rfl⟩
    rw [op_comp, Functor.map_comp, types_comp_apply, types_comp_apply]
    congr 1
    apply (hbij U i).1
    rw [NatTrans.naturality_apply φ.hom, NatTrans.naturality_apply φ.hom, hxy]
  have himg : ∀ (U : Over Y) (s : H'.obj.obj (op U)),
      Presheaf.imageSieve φ.hom s ∈ B.topology.over Y U := by
    intro U s
    refine (B.topology.over Y).superset_covering ?_ (hcov U)
    rintro W k ⟨T, a, b, ⟨i⟩, rfl⟩
    apply (Presheaf.imageSieve φ.hom s).downward_closed
    obtain ⟨t, ht⟩ := (hbij U i).2 (H'.obj.map (Over.homMk (pullback.fst U.hom (j i)) :
      Over.mk (pullback.fst U.hom (j i) ≫ U.hom) ⟶ U).op s)
    exact ⟨t, ht⟩
  have hsurj' : ∀ (U : Over Y), Function.Surjective (φ.hom.app (op U)) := by
    intro U s
    have hH := (isSheaf_iff_isSheaf_of_type _ H.obj).1 H.property _ (himg U s)
    let t : Presieve.FamilyOfElements H.obj (Presheaf.imageSieve φ.hom s).arrows :=
      fun W g hg ↦ Presheaf.localPreimage φ.hom s g hg
    have ht : t.Compatible := by
      intro Y₁ Y₂ W g₁ g₂ f₁ f₂ hf₁ hf₂ w
      apply hinj
      have eq₁ := NatTrans.naturality_apply φ.hom g₁.op (t f₁ hf₁)
      have eq₂ := NatTrans.naturality_apply φ.hom g₂.op (t f₂ hf₂)
      have eq₃ := congr_arg (H'.obj.map g₁.op) (Presheaf.app_localPreimage φ.hom s _ hf₁)
      have eq₄ := congr_arg (H'.obj.map g₂.op) (Presheaf.app_localPreimage φ.hom s _ hf₂)
      refine eq₁.trans (eq₃.trans (Eq.trans ?_ (eq₄.symm.trans eq₂.symm)))
      rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
      simp only [← op_comp, w]
    refine ⟨hH.amalgamate t ht, ?_⟩
    apply (((isSheaf_iff_isSheaf_of_type _ H'.obj).1 H'.property).isSeparated _
      (himg U s)).ext
    intro W g hg
    rw [← NatTrans.naturality_apply, hH.valid_glue ht]
    exact Presheaf.app_localPreimage φ.hom s g hg
  rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _), NatTrans.isIso_iff_isIso_app]
  intro U
  rw [isIso_iff_bijective]
  exact ⟨hinj U.unop, hsurj' U.unop⟩

/-! ### Descent of the essential image of `a⁻¹` -/

/-- A morphism between sheaves in the essential image of `a_X⁻¹` is an isomorphism once its image
under `a_{X,*}` is. -/
public theorem isIso_of_isIso_fppfToSmallEtale_pushforward_map {X : B.Schemes}
    {K K' : Sheaf (B.topology.over X) (Type (u + 1))} (φ : K ⟶ K')
    (hK : (fppfToSmallEtaleMorphism B X).inverseImage.essImage K)
    (hK' : (fppfToSmallEtaleMorphism B X).inverseImage.essImage K')
    (h : IsIso ((fppfToSmallEtaleMorphism B X).pushforward.map φ)) : IsIso φ := by
  let a := fppfToSmallEtaleMorphism B X
  have h₁ : IsIso (a.adj.counit.app K) := (a.adj.isIso_counit_app_iff_mem_essImage).2 hK
  have h₂ : IsIso (a.adj.counit.app K') := (a.adj.isIso_counit_app_iff_mem_essImage).2 hK'
  have hn : a.inverseImage.map (a.pushforward.map φ) ≫ a.adj.counit.app K' =
      a.adj.counit.app K ≫ φ := a.adj.counit.naturality φ
  have : IsIso (a.adj.counit.app K ≫ φ) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_left (a.adj.counit.app K) φ

/-- Let `f : X ⟶ Y` be finite, flat, locally of finite presentation and surjective, and let `H` be
a big fppf sheaf on `Y` whose restriction to `X` lies in the essential image of `a_X⁻¹`. Then `H`
lies in the essential image of `a_Y⁻¹`. -/
public theorem fppfToSmallEtale_essImage_of_restriction_of_isFinite {X Y : B.Schemes} (f : X ⟶ Y)
    [IsFinite (B.inclusion.map f)] [Flat (B.inclusion.map f)]
    [LocallyOfFinitePresentation (B.inclusion.map f)] [Surjective (B.inclusion.map f)]
    {H : Sheaf (B.topology.over Y) (Type (u + 1))}
    (hH : (fppfToSmallEtaleMorphism B X).inverseImage.essImage
      (((Over.map f).sheafPushforwardContinuous (Type (u + 1)) (B.topology.over X)
        (B.topology.over Y)).obj H)) :
    (fppfToSmallEtaleMorphism B Y).inverseImage.essImage H := by
  let L := (Over.map f).sheafPushforwardContinuous (Type (u + 1)) (B.topology.over X)
    (B.topology.over Y)
  let R := (Over.pullback f).sheafPushforwardContinuous (Type (u + 1)) (B.topology.over Y)
    (B.topology.over X)
  let adj : L ⊣ R := (Over.mapPullbackAdj f).sheafPushforwardAdjunction (Type (u + 1))
  have : L.ReflectsIsomorphisms := ⟨fun {K K'} φ hφ ↦
    isIso_of_forall_isIso_bigFppfRestriction B (I := PUnit) (fun _ ↦ X) (fun _ ↦ f)
      (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
      (fun y ↦ ⟨PUnit.unit, (B.inclusion.map f).surjective y⟩) φ (fun _ ↦ hφ)⟩
  have : PreservesLimitsOfShape WalkingParallelPair L := by
    have := (bigFppfMorphism B X Y f).preservesFiniteLimits
    exact preservesLimitsOfShape_of_natIso
      ((Over.map f).sheafPullbackCocontinuousIsoSheafPushforwardContinuous (Type (u + 1))
        (B.topology.over X) (B.topology.over Y))
  have : ReflectsLimitsOfShape WalkingParallelPair L :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  have hR : ∀ K, (fppfToSmallEtaleMorphism B X).inverseImage.essImage K →
      (fppfToSmallEtaleMorphism B Y).inverseImage.essImage (R.obj K) := by
    rintro K ⟨G, ⟨e⟩⟩
    have := isIso_bigFppfSmallEtaleBaseChange_of_isFinite B f
    exact ⟨((associatedBigEtaleSite B).smallPushforward f (Type (u + 1))).obj G,
      ⟨(asIso (bigFppfSmallEtaleBaseChange B f)).app G ≪≫ R.mapIso e⟩⟩
  have hlim := Comonad.ComonadicityInternal.unitEqualizerOfCoreflectsEqualizer adj H
  refine ObjectProperty.prop_of_isLimit _ hlim ?_
  rintro (_ | _)
  · exact hR _ hH
  · exact hR _ (fppfToSmallEtale_essImage_restriction B f (hR _ hH))

/-- Let `{j_i : V_i ⟶ Y}` be a jointly surjective family of étale morphisms and `H` a big fppf
sheaf on `Y` whose restrictions to all `V_i` lie in the essential images of `a_{V_i}⁻¹`. Then `H`
lies in the essential image of `a_Y⁻¹`. -/
public theorem fppfToSmallEtale_essImage_of_forall_restriction_of_etale {Y : B.Schemes}
    {I : Type (u + 1)} (V : I → B.Schemes) (j : ∀ i, V i ⟶ Y)
    (het : ∀ i, Etale (B.inclusion.map (j i)))
    (hsurj : ∀ y : B.inclusion.obj Y, ∃ i, y ∈ Set.range (B.inclusion.map (j i)))
    {H : Sheaf (B.topology.over Y) (Type (u + 1))}
    (hH : ∀ i, (fppfToSmallEtaleMorphism B (V i)).inverseImage.essImage
      (((Over.map (j i)).sheafPushforwardContinuous (Type (u + 1)) (B.topology.over (V i))
        (B.topology.over Y)).obj H)) :
    (fppfToSmallEtaleMorphism B Y).inverseImage.essImage H := by
  let a := fppfToSmallEtaleMorphism B Y
  rw [← a.adj.isIso_counit_app_iff_mem_essImage]
  have hu := isIso_fppfToSmallEtaleMorphism_unit B Y
  have hε : IsIso (a.pushforward.map (a.adj.counit.app H)) := by
    have e := a.adj.right_triangle_components H
    have : IsIso (a.adj.unit.app (a.pushforward.obj H) ≫
        a.pushforward.map (a.adj.counit.app H)) := by
      rw [e]
      exact ⟨⟨𝟙 _, Category.id_comp _, Category.id_comp _⟩⟩
    exact IsIso.of_isIso_comp_left (a.adj.unit.app _) _
  have hεp : IsIso (a.pushforward.map (a.adj.counit.app H)).hom :=
    inferInstanceAs (IsIso ((sheafToPresheaf _ (Type (u + 1))).map
      (a.pushforward.map (a.adj.counit.app H))))
  refine isIso_of_forall_isIso_bigFppfRestriction B V j (fun i ↦ by have := het i; infer_instance)
    (fun i ↦ by have := het i; infer_instance) hsurj _ fun i ↦ ?_
  let ρ := (Over.map (j i)).sheafPushforwardContinuous (Type (u + 1)) (B.topology.over (V i))
    (B.topology.over Y)
  refine isIso_of_isIso_fppfToSmallEtale_pushforward_map B (ρ.map (a.adj.counit.app H))
    (fppfToSmallEtale_essImage_restriction B (j i) ⟨_, ⟨Iso.refl _⟩⟩) (hH i) ?_
  let aV := fppfToSmallEtaleMorphism B (V i)
  have key : ∀ U : (SmallEtale (associatedBigEtaleSite B) (V i).1 (V i).2)ᵒᵖ,
      IsIso ((aV.pushforward.map (ρ.map (a.adj.counit.app H))).hom.app U) := by
    intro U
    have := het i
    have hU : Etale (B.inclusion.map (U.unop.obj.hom ≫ j i)) := by
      rw [Functor.map_comp]
      have := U.unop.property
      exact inferInstanceAs (Etale ((associatedBigEtaleSite B).inclusion.map U.unop.obj.hom ≫
        B.inclusion.map (j i)))
    let W : SmallEtale (associatedBigEtaleSite B) Y.1 Y.2 := ⟨(Over.map (j i)).obj U.unop.obj, hU⟩
    exact (inferInstance : IsIso ((a.pushforward.map (a.adj.counit.app H)).hom.app (op W)))
  have : IsIso ((sheafToPresheaf _ (Type (u + 1))).map
      (aV.pushforward.map (ρ.map (a.adj.counit.app H)))) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ key
  exact isIso_of_reflects_iso _ (sheafToPresheaf _ (Type (u + 1)))

/-- Let `f : X ⟶ Y` be flat, locally of finite presentation and surjective, and let `H` be a big
fppf sheaf on `Y` whose restriction to `X` lies in the essential image of `a_X⁻¹`. Then `H` lies
in the essential image of `a_Y⁻¹`. -/
public theorem fppfToSmallEtale_essImage_of_restriction {X Y : B.Schemes} (f : X ⟶ Y)
    [Flat (B.inclusion.map f)] [LocallyOfFinitePresentation (B.inclusion.map f)]
    [Surjective (B.inclusion.map f)] {H : Sheaf (B.topology.over Y) (Type (u + 1))}
    (hH : (fppfToSmallEtaleMorphism B X).inverseImage.essImage
      (((Over.map f).sheafPushforwardContinuous (Type (u + 1)) (B.topology.over X)
        (B.topology.over Y)).obj H)) :
    (fppfToSmallEtaleMorphism B Y).inverseImage.essImage H := by
  classical
  let 𝒮 : (B.inclusion.obj Y).Cover.{u} Scheme.fppfPrecoverage :=
    Scheme.Cover.mkOfCovers (P := @Flat ⊓ @LocallyOfFinitePresentation) PUnit.{u + 1}
      (fun _ ↦ B.inclusion.obj X) (fun _ ↦ B.inclusion.map f)
      (fun y ↦ ⟨PUnit.unit, (B.inclusion.map f).surjective y⟩)
      (fun _ ↦ ⟨inferInstance, inferInstance⟩)
  obtain ⟨𝒱, 𝒲, ⟨r⟩, e, g, hcomm, hgsurj, hgflf⟩ :=
    Stacks.Topologies.Fppf.etaleFiniteLocallyFreeDominates 𝒮
  let I : Type (u + 1) := ULift.{u + 1} (Σ a : 𝒲.I₀, (𝒱.X (e a)).affineOpens)
  let A : ∀ i : I, (𝒱.X (e i.down.1)).Opens := fun i ↦ i.down.2.1
  have hAaff : ∀ i : I, IsAffine (A i) := fun i ↦ i.down.2.2
  let jA : ∀ i : I, (A i : Scheme.{u}) ⟶ B.inclusion.obj Y := fun i ↦
    (A i).ι ≫ 𝒱.f (e i.down.1)
  have hjAet : ∀ i : I, Etale (jA i) := fun i ↦ by
    have : Etale (𝒱.f (e i.down.1)) := 𝒱.map_prop (e i.down.1)
    infer_instance
  let pA : ∀ i : I, pullback (g i.down.1) (A i).ι ⟶ (A i : Scheme.{u}) := fun i ↦
    pullback.snd (g i.down.1) (A i).ι
  have hpb : ∀ (P : MorphismProperty Scheme) [P.IsStableUnderBaseChange] (i : I),
      P (g i.down.1) → P (pA i) := fun P _ i ↦
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (g i.down.1) (A i).ι)
  have hpfin : ∀ i : I, IsFinite (pA i) := fun i ↦
    hpb @IsFinite i (Stacks.Morphisms.IsFiniteLocallyFree.isFinite (g i.down.1))
  have hAsize : ∀ i : I, (A i : Scheme.{u}).size < B.cutoff := fun i ↦ by
    have := hAaff i
    have := hjAet i
    exact (Scheme.size_le_of_locallyOfFiniteType (jA i)).trans_lt Y.2
  have hTsize : ∀ i : I, (pullback (g i.down.1) (A i).ι).size < B.cutoff := fun i ↦ by
    have := hAaff i
    have := hjAet i
    have := hpfin i
    have : IsAffine (pullback (g i.down.1) (A i).ι) := isAffine_of_isAffineHom (pA i)
    exact (Scheme.size_le_of_locallyOfFiniteType (pA i ≫ jA i)).trans_lt Y.2
  let V' : I → B.Schemes := fun i ↦ ⟨A i, hAsize i⟩
  let T' : I → B.Schemes := fun i ↦ ⟨pullback (g i.down.1) (A i).ι, hTsize i⟩
  let j' : ∀ i, V' i ⟶ Y := fun i ↦ B.inclusion.preimage (jA i)
  let p' : ∀ i, T' i ⟶ V' i := fun i ↦ B.inclusion.preimage (pA i)
  let l' : ∀ i, T' i ⟶ X := fun i ↦ B.inclusion.preimage
    (pullback.fst (g i.down.1) (A i).ι ≫ r.h₀ i.down.1)
  have hj' : ∀ i, B.inclusion.map (j' i) = jA i := fun i ↦ Functor.map_preimage _ _
  have hp' : ∀ i, B.inclusion.map (p' i) = pA i := fun i ↦ Functor.map_preimage _ _
  have heq : ∀ i, l' i ≫ f = p' i ≫ j' i := fun i ↦ by
    apply B.inclusion.map_injective
    rw [Functor.map_comp, Functor.map_comp, Functor.map_preimage, hp', hj']
    have hw := r.w₀ i.down.1
    have hc := hcomm i.down.1
    show pullback.fst (g i.down.1) (A i).ι ≫ r.h₀ i.down.1 ≫ 𝒮.f (r.s₀ i.down.1) =
      pullback.snd (g i.down.1) (A i).ι ≫ (A i).ι ≫ 𝒱.f (e i.down.1)
    rw [hw, ← hc, ← Category.assoc, pullback.condition, Category.assoc]
  have hV : ∀ i, (fppfToSmallEtaleMorphism B (V' i)).inverseImage.essImage
      (((Over.map (j' i)).sheafPushforwardContinuous (Type (u + 1)) (B.topology.over (V' i))
        (B.topology.over Y)).obj H) := fun i ↦ by
    have hT : (fppfToSmallEtaleMorphism B (T' i)).inverseImage.essImage
        (((Over.map (p' i ≫ j' i)).sheafPushforwardContinuous (Type (u + 1))
          (B.topology.over (T' i)) (B.topology.over Y)).obj H) := by
      rw [← heq i]
      exact ObjectProperty.prop_of_iso _ ((bigFppfRestrictionCompIso B (l' i) f).app H)
        (fppfToSmallEtale_essImage_restriction B (l' i) hH)
    have hT' := ObjectProperty.prop_of_iso _
      ((bigFppfRestrictionCompIso B (p' i) (j' i)).app H).symm hT
    have : IsFinite (B.inclusion.map (p' i)) := by rw [hp']; exact hpfin i
    have : Flat (B.inclusion.map (p' i)) := by
      rw [hp']; exact hpb @Flat i (Stacks.Morphisms.IsFiniteLocallyFree.flat (g i.down.1))
    have : LocallyOfFinitePresentation (B.inclusion.map (p' i)) := by
      rw [hp']
      exact hpb @LocallyOfFinitePresentation i
        (Stacks.Morphisms.IsFiniteLocallyFree.locallyOfFinitePresentation (g i.down.1))
    have : Surjective (B.inclusion.map (p' i)) := by rw [hp']; exact hpb @Surjective i (hgsurj _)
    exact fppfToSmallEtale_essImage_of_restriction_of_isFinite B (p' i) hT'
  refine fppfToSmallEtale_essImage_of_forall_restriction_of_etale B V' j'
    (fun i ↦ by rw [hj']; exact hjAet i) ?_ hV
  intro y
  have hcov := (Scheme.presieve₀_mem_precoverage_iff (P := @Etale)
    𝒱.toPreZeroHypercover).mp 𝒱.mem₀
  obtain ⟨b, v, hv⟩ := hcov.1 y
  let a := e.symm b
  obtain ⟨v', hv'⟩ : ∃ v' : 𝒱.X (e a), 𝒱.f (e a) v' = y := by
    rw [show e a = b from e.apply_symm_apply b]
    exact ⟨v, hv⟩
  obtain ⟨W, hW, hvW, -⟩ := exists_isAffineOpen_mem_and_subset (x := v')
    (U := (⊤ : (𝒱.X (e a)).Opens)) trivial
  refine ⟨ULift.up ⟨a, ⟨W, hW⟩⟩, ⟨v', hvW⟩, ?_⟩
  rw [hj']
  show 𝒱.f (e a) (W.ι ⟨v', hvW⟩) = y
  simpa using hv'

/-- Let `f : X ⟶ Y` be a morphism of the big fppf site which is flat, locally of finite
presentation and surjective. Then the functor from `Sh(Y_étale)` to the category of
triples `(G, H, α)` with `G ∈ Sh(X_étale)`, `H ∈ Sh((Sch/Y)_fppf)` and
`α : a_X⁻¹G ≅ f_{big,fppf}⁻¹H` an isomorphism, `F ↦ (f_small⁻¹F, a_Y⁻¹F, can)`, is an
equivalence of categories.

The category of triples is the two-fibre product `a_X⁻¹ ⊡ f_{big,fppf}⁻¹`
(`CategoryTheory.Limits.CategoricalPullback`), whose objects are exactly `(G, H, α)` with
`α : a_X⁻¹G ≅ f_{big,fppf}⁻¹H`, and the functor is the canonical functor into it built from the
canonical isomorphism `can = AlgebraicGeometry.fppfSmallEtaleInverseImageCommIso`. -/
public theorem isEquivalence_fppfSmallEtaleTripleFunctor {X Y : B.Schemes} (f : X ⟶ Y)
    [Flat (B.inclusion.map f)] [LocallyOfFinitePresentation (B.inclusion.map f)]
    [Surjective (B.inclusion.map f)] :
    (Stacks.CategoryTheory.modificationGluingFunctor
      (fppfSmallEtaleInverseImageCommIso B f)).IsEquivalence :=
  Stacks.CategoryTheory.modificationGluingFunctor_isEquivalence_of_snd _ fun T ↦
    fppfToSmallEtale_essImage_of_restriction B f
      ⟨T.fst, ⟨T.iso ≪≫ ((Over.map f).sheafPullbackCocontinuousIsoSheafPushforwardContinuous
        (Type (u + 1)) (B.topology.over X) (B.topology.over Y)).app T.snd⟩⟩

end AlgebraicGeometry
