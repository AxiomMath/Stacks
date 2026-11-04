module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom
public import StacksFrontier.CategoryTheory.Sites.Topos.LocalizationOfTopoi

/-!
# Étale charts from a 2-isomorphism of small étale ringed topoi

Let `S` be a scheme and let `a, b : X ⟶ Y` be two *representable* morphisms of algebraic spaces
over `S`.  Each induces a morphism of small étale ringed topoi, whose direct image is base change
of étale scheme charts along it (Stacks 03G8,
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_representable`).  A 2-isomorphism of the two
morphisms of ringed topoi is therefore an isomorphism of the two direct images of charts, and
such an isomorphism is *induced by an isomorphism of the chart base-change functors themselves*:
over each étale chart `V` of `Y` it is restriction along an isomorphism `V ×_{Y,b} X ≅ V ×_{Y,a} X`
of étale charts of `X`.

This is the step of Stacks 04M6 which produces, from the 2-isomorphism `t : a_{small} ≅ b_{small}`,
the morphism of charts that the source calls `β`: the source argues that `b^{-1}h_V` is
isomorphic to `h_{V ×_{Y,b} X}`, so that the dotted arrow `h_U ⟶ b^{-1}h_V` comes from a morphism
of schemes.  Here that is carried out for the direct images, where the identification is the
Stacks 03G8 comparison, and the conclusion is an isomorphism of the base-change functors.

Recovering it needs the small étale topology of an algebraic space to be *subcanonical*, so that
the sections of a sheaf over a chart are the maps out of the chart it represents; that is proved
here as well.

## Main results

* `AlgebraicGeometry.Space.smallEtaleTopology_subcanonical`: the small étale topology of an
  algebraic space is subcanonical — every representable presheaf on the site of étale scheme
  charts is a sheaf.
* `AlgebraicGeometry.Space.exists_smallBaseChange_iso_of_twoIso`: for two representable
  morphisms, a 2-isomorphism of the induced morphisms of small étale ringed topoi is, through the
  Stacks 03G8 identification of the direct images with chart base change, restriction along an
  isomorphism of the chart base-change functors.

## Implementation notes

Subcanonicity is reduced to subcanonicity of the topology induced on the whole category of
objects over the algebraic space, where it is the sheaf condition for the representable
presheaves of the big fppf site, and the étale charts are a full subcategory closed under fibre
products, so that the inclusion is continuous and reflects the sheaf condition.  Closure under
fibre products uses that a morphism between two étale charts is étale
(`AlgebraicGeometry.Space.etale_of_etale_charts`), which is also what makes the induced topology
land back in the small étale one.

The passage from an isomorphism of direct images to an isomorphism of the functors of sites is
corepresentability: the sections of the direct image of `H` along a functor `F` over an object
`V` are the maps `h_{F V} ⟶ H`, so an isomorphism of direct images is an isomorphism of the
corepresented functors, and Yoneda turns it back into an isomorphism `F V ≅ G V`.  This holds for
any pair of continuous functors into a subcanonical site and is used here only at the chart
base-change functors.

What the conclusion does *not* record is that the two chart projections `V ×_{Y,a} X ⟶ V` and
`V ×_{Y,b} X ⟶ V` agree through that isomorphism.  That is the remaining content of Stacks 04M6,
and in the source it is where the structure maps `a^♯` and `b^♯` enter: it needs the sectionwise
formula identifying `f^♯`, read through the Stacks 03G8 comparison for a representable `f`, with
pullback of regular functions along the cartesian chart projection.  The chartwise formula for
the structure map itself is formalized as
`AlgebraicGeometry.Space.chartProjection_structureMapApp`, but its transport along the
representable comparison is not, so the compatibility of `t` with the structure sheaves — the
`commutes` field of the 2-isomorphism — is not used below, only the underlying isomorphism of
direct images.

## References

* [Stacks Project, Tag 04M6](https://stacks.math.columbia.edu/tag/04M6)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

section Corepresentability

universe vC uC vD uD

variable {C : Type uC} [Category.{vC, uC} C] {D : Type uD} [Category.{vD, uD} D]

/-- On a subcanonical site, an isomorphism of the direct images along two continuous functors is,
over each object `V`, restriction along an isomorphism `G V ≅ F V`. -/
theorem exists_iso_of_pushforward_iso
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) [K.Subcanonical]
    (F G : C ⥤ D) [F.IsContinuous J K] [G.IsContinuous J K]
    (t : F.sheafPushforwardContinuous (Type vD) J K ≅
      G.sheafPushforwardContinuous (Type vD) J K) (V : C) :
    ∃ e : G.obj V ≅ F.obj V,
      ∀ (H : Sheaf K (Type vD))
        (x : (F.sheafPushforwardContinuous (Type vD) J K).obj H |>.obj.obj (op V)),
        ((t.hom.app H).hom.app (op V)) x = H.obj.map (op e.hom) x := by
  let P := F.sheafPushforwardContinuous (Type vD) J K
  let Q := G.sheafPushforwardContinuous (Type vD) J K
  let A := K.yoneda.obj (F.obj V)
  let B := K.yoneda.obj (G.obj V)
  let lhs (H : Sheaf K (Type vD)) : (A ⟶ H) ≃ (P.obj H).obj.obj (op V) :=
    K.yonedaEquiv (X := F.obj V) (F := H)
  let rhs (H : Sheaf K (Type vD)) : (B ⟶ H) ≃ (Q.obj H).obj.obj (op V) :=
    K.yonedaEquiv (X := G.obj V) (F := H)
  have lhs_natural (H H' : Sheaf K (Type vD)) (α : H ⟶ H') (g : A ⟶ H) :
      lhs H' (g ≫ α) = ((P.map α).hom.app (op V)) (lhs H g) := by
    show K.yonedaEquiv (g ≫ α) = _
    rw [K.yonedaEquiv_comp]
    rfl
  have rhs_natural (H H' : Sheaf K (Type vD)) (α : H ⟶ H') (g : B ⟶ H) :
      rhs H' (g ≫ α) = ((Q.map α).hom.app (op V)) (rhs H g) := by
    show K.yonedaEquiv (g ≫ α) = _
    rw [K.yonedaEquiv_comp]
    rfl
  let sectionMap (H : Sheaf K (Type vD)) :
      (P.obj H).obj.obj (op V) ≃ (Q.obj H).obj.obj (op V) :=
    (asIso ((t.app H).hom.hom.app (op V))).toEquiv
  have sectionMap_natural (H H' : Sheaf K (Type vD)) (α : H ⟶ H')
      (x : (P.obj H).obj.obj (op V)) :
      sectionMap H' (((P.map α).hom.app (op V)) x) =
        ((Q.map α).hom.app (op V)) (sectionMap H x) := by
    have ht := t.hom.naturality α
    have htV := congrArg (fun q => q.hom.app (op V)) ht
    have htV' := congrArg (fun q => q x) htV
    change ((t.hom.app H').hom.app (op V))
        (((P.map α).hom.app (op V)) x) =
      ((Q.map α).hom.app (op V))
        (((t.hom.app H).hom.app (op V)) x) at htV'
    simpa only [sectionMap, CategoryTheory.Iso.toEquiv_apply, CategoryTheory.Iso.app_hom,
      asIso_hom] using htV'
  let ecorep : coyoneda.obj (op A) ≅ coyoneda.obj (op B) := by
    refine NatIso.ofComponents (fun H => Equiv.toIso
      ((lhs H).trans ((sectionMap H).trans (rhs H).symm))) ?_
    intro H H' α
    ext g
    show (rhs H').symm (sectionMap H' (lhs H' (g ≫ α))) =
      (rhs H).symm (sectionMap H (lhs H g)) ≫ α
    apply (rhs H').injective
    rw [lhs_natural, sectionMap_natural, rhs_natural]
    simp
  let sheafIso := (Coyoneda.fullyFaithful (C := Sheaf K (Type vD))).preimageIso ecorep
  let e := K.yonedaFullyFaithful.preimageIso (sheafIso.unop.symm)
  refine ⟨e.symm, ?_⟩
  intro H x
  let g : A ⟶ H := (lhs H).symm x
  have hmap : coyoneda.map sheafIso.hom = ecorep.hom := by
    dsimp [sheafIso]
    exact Coyoneda.fullyFaithful.map_preimage ecorep.hom
  have he : K.yoneda.map e.inv = sheafIso.unop.hom := by
    dsimp [e]
    simp
  have hc := congrFun (congrArg (fun n => n.app H) hmap) g
  change (sheafIso.hom).unop ≫ g = ecorep.hom.app H g at hc
  have hcorep : ecorep.hom.app H g = K.yoneda.map e.inv ≫ g := by
    rw [he]
    exact (show sheafIso.unop.hom ≫ g = ecorep.hom.app H g by simpa using hc).symm
  have hfirst : ((t.hom.app H).hom.app (op V)) x = (sectionMap H) x := by
    simp [sectionMap, CategoryTheory.Iso.toEquiv_apply]
  have hsecond : (sectionMap H) x = (rhs H) (ecorep.hom.app H g) := by
    dsimp [ecorep]
    simp [g]
  have hthird : (rhs H) (ecorep.hom.app H g) = (rhs H) (K.yoneda.map e.inv ≫ g) :=
    congrArg _ hcorep
  have hfourth : (rhs H) (K.yoneda.map e.inv ≫ g) = H.obj.map (op e.inv) x := by
    show K.yonedaEquiv (K.yoneda.map e.inv ≫ g) = H.obj.map (op e.inv) x
    have hg : K.yonedaEquiv g = x := Equiv.apply_symm_apply (lhs H) x
    have hn := K.yonedaEquiv_naturality' g (op e.inv)
    rw [hg] at hn
    exact hn.symm
  exact hfirst.trans (hsecond.trans (hthird.trans hfourth))

/-- On a subcanonical site, an isomorphism of the direct images along two continuous functors is
restriction along an isomorphism of the two functors. -/
theorem exists_natIso_of_pushforward_iso
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) [K.Subcanonical]
    (F G : C ⥤ D) [F.IsContinuous J K] [G.IsContinuous J K]
    (t : F.sheafPushforwardContinuous (Type vD) J K ≅
      G.sheafPushforwardContinuous (Type vD) J K) :
    ∃ e : G ≅ F,
      ∀ (H : Sheaf K (Type vD)) (V : C)
        (x : (F.sheafPushforwardContinuous (Type vD) J K).obj H |>.obj.obj (op V)),
        ((t.hom.app H).hom.app (op V)) x = H.obj.map (op (e.hom.app V)) x := by
  choose e he using fun V => exists_iso_of_pushforward_iso J K F G t V
  refine ⟨NatIso.ofComponents e ?_, fun H V x => he V H x⟩
  intro V W j
  let H := K.yoneda.obj (F.obj W)
  have hh := congrArg (fun k => k (CategoryStruct.id (F.obj W)))
    ((t.hom.app H).hom.naturality j.op)
  change ((t.hom.app H).hom.app (op V)) (F.map j ≫ CategoryStruct.id (F.obj W)) =
    G.map j ≫ ((t.hom.app H).hom.app (op W)) (CategoryStruct.id (F.obj W)) at hh
  have h1 := he V H (F.map j ≫ CategoryStruct.id (F.obj W))
  have h2 := he W H (CategoryStruct.id (F.obj W))
  change _ = (e V).hom ≫ (F.map j ≫ CategoryStruct.id (F.obj W)) at h1
  change _ = (e W).hom ≫ CategoryStruct.id (F.obj W) at h2
  rw [h1, h2] at hh
  simp only [Category.comp_id] at hh
  exact hh.symm

end Corepresentability

section ChartComparison

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The small étale topology of an algebraic space is subcanonical.** Every presheaf on the
site of étale scheme charts of an algebraic space represented by a chart is a sheaf. -/
theorem smallEtaleTopology_subcanonical (X : AlgebraicSpaces B S hS) :
    (SmallEtale.topology B S hS X.obj).Subcanonical := by
  let : HasPullbacks B.Schemes := inferInstance
  let : PreservesLimitsOfShape WalkingCospan B.inclusion := inferInstance
  let : HasPullbacks (BigFppfOver B S hS) := inferInstance
  let J := BigFppfOver.topology B S hS
  let π := CostructuredArrow.proj yoneda X.obj
  let K := π.restrictedTopology J
  have hloc := Presheaf.IsSheaf.exists_sheafEquivalence_costructuredArrow_yoneda
    X.property.isSheaf
  let : K.Subcanonical := by
    apply GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj
    intro V
    rw [← isSheaf_iff_isSheaf_of_type]
    have hv := (hloc.2.1 (Over.mk V.hom)).mpr
      (isAlgebraicSpace_yoneda B S hS V.left).isSheaf
    exact (Presheaf.isSheaf_of_iso_iff
      ((OverPresheafAux.toOverYonedaCompRestrictedYoneda X.obj).app V)).mp hv
  let : (IsEtaleChart B S hS X.obj).IsClosedUnderLimitsOfShape WalkingCospan := by
    refine ⟨?_⟩
    rintro U ⟨d, hd⟩
    have hp := IsPullback.of_isLimit_cone (isLimitOfPreserves π d.isLimit)
    have he : Etale ((BigFppfOver.toScheme B S hS).map
        (d.diag.map WalkingCospan.Hom.inr).left) :=
      etale_of_etale_charts B S hS _ _ (hd .right) (hd .one) _ (CostructuredArrow.w _)
    have hep : Etale ((BigFppfOver.toScheme B S hS).map
        (d.π.app WalkingCospan.left).left) :=
      MorphismProperty.of_isPullback (hp.flip.map (BigFppfOver.toScheme B S hS)) he
    show (IsEtaleChart B S hS X.obj) U
    show (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
      (((Functor.const WalkingCospan).obj U).obj WalkingCospan.left).hom
    rw [← CostructuredArrow.w (d.π.app WalkingCospan.left)]
    exact etale_comp_of_scheme B S hS _ _ hep (hd .left)
  let I := SmallEtale.inclusion B S hS X.obj
  let Q := K.toPrecoverage.comap I
  let : PreservesLimitsOfShape WalkingCospan I := inferInstance
  have hKK : K.toPrecoverage.toGrothendieck = K := by
    apply le_antisymm (GrothendieckTopology.toGrothendieck_toPrecoverage_le K)
    intro V R hR
    rw [← Sieve.generate_sieve R]
    exact Precoverage.generate_mem_toGrothendieck
      ((GrothendieckTopology.arrows_mem_toPrecoverage_iff K R).mpr hR)
  let : I.IsContinuous Q.toGrothendieck K := by
    simpa only [hKK] using
      (Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy
        (F := I) (J := Q) (K := K.toPrecoverage) le_rfl)
  let : Q.toGrothendieck.Subcanonical :=
    GrothendieckTopology.subcanonical_of_full_of_faithful I Q.toGrothendieck K
  apply GrothendieckTopology.Subcanonical.of_le (K := Q.toGrothendieck)
  apply Precoverage.toGrothendieck_mono
  intro V R hR
  obtain ⟨E, rfl, hE⟩ := hR
  rw [Precoverage.mem_comap_iff, GrothendieckTopology.mem_toPrecoverage_iff]
  apply (hloc.1 (I.obj V) (Sieve.generate (E.presieve₀.map I))).mpr
  rw [← Sieve.generate_map_eq_functorPushforward]
  show Sieve.generate ((E.presieve₀.map I).map π) ∈ J V.obj.left
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_generate,
    ← Sieve.arrows_generate_map_eq_functorPushforward]
  simp only [Sieve.generate_sieve]
  have hc : B.IsCovering
      ⟨(SmallEtale.toSchemes B S hS X.obj).obj V,
        E.map (SmallEtale.toSchemes B S hS X.obj)⟩ := hE.1
  have hm := Precoverage.generate_mem_toGrothendieck
    (show (E.map (SmallEtale.toSchemes B S hS X.obj)).presieve₀ ∈ B.precoverage _ from
      ⟨_, rfl, hc⟩)
  simpa [PreZeroHypercover.presieve₀, PreZeroHypercover.map,
    Presieve.map_ofArrows, Functor.comp_map, I, π] using hm

/-- **The étale-chart comparison of Stacks 04M6.** Let `a, b : X ⟶ Y` be two representable
morphisms of algebraic spaces whose morphisms of small étale ringed topoi are 2-isomorphic.
Through the Stacks 03G8 identification of the two direct images with base change of étale scheme
charts, the 2-isomorphism is restriction along an isomorphism `V ×_{Y,b} X ≅ V ×_{Y,a} X` of the
chart base-change functors, natural in the étale chart `V` of `Y`. -/
@[stacks 04M6 "the étale-chart comparison of the proof: for two representable morphisms the
  2-isomorphism of the morphisms of small étale ringed topoi is, through the 03G8 identification
  of the direct images with étale-chart base change, restriction along an isomorphism of the
  chart base-change functors"]
theorem exists_smallBaseChange_iso_of_twoIso {X Y : AlgebraicSpaces B S hS} (a b : X ⟶ Y)
    (ha : yoneda.relativelyRepresentable a.hom) (hb : yoneda.relativelyRepresentable b.hom)
    (t : RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS a) (smallEtaleRingedToposHom B S hS b)) :
    letI := (smallBaseChange_isMorphismOfSites B S hS a ha).toIsContinuous
    letI := (smallBaseChange_isMorphismOfSites B S hS b hb).toIsContinuous
    ∃ e : smallBaseChange B S hS b hb ≅ smallBaseChange B S hS a ha,
      ∀ (H : Sheaf (SmallEtale.topology B S hS X.obj) (Type u))
        (V : SmallEtale B S hS Y.obj)
        (x : (((smallBaseChange B S hS a ha).sheafPushforwardContinuous (Type u)
          (SmallEtale.topology B S hS Y.obj)
          (SmallEtale.topology B S hS X.obj)).obj H).obj.obj (op V)),
        ((((smallEtaleRingedToposHom_representable B S hS a ha).symm ≪≫ t.e ≪≫
            smallEtaleRingedToposHom_representable B S hS b hb).hom.app H).hom.app (op V)) x =
          H.obj.map (op (e.hom.app V)) x := by
  let := (smallBaseChange_isMorphismOfSites B S hS a ha).toIsContinuous
  let := (smallBaseChange_isMorphismOfSites B S hS b hb).toIsContinuous
  let : (SmallEtale.topology B S hS X.obj).Subcanonical :=
    smallEtaleTopology_subcanonical B S hS X
  exact exists_natIso_of_pushforward_iso (SmallEtale.topology B S hS Y.obj)
    (SmallEtale.topology B S hS X.obj) (smallBaseChange B S hS a ha)
    (smallBaseChange B S hS b hb)
    ((smallEtaleRingedToposHom_representable B S hS a ha).symm ≪≫ t.e ≪≫
      smallEtaleRingedToposHom_representable B S hS b hb)

end ChartComparison

end AlgebraicGeometry.Space

end
