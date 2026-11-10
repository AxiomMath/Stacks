module

public import StacksFrontier.AlgebraicGeometry.Groupoids.InvariantOpenSubgroupoid
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.GroupoidInverse
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.StrongSplittingDerealizationComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.StrongSplittingDerealizationInv

/-!
# The structure morphisms of a realization of a restriction

The structure `AlgebraicGeometry.GroupoidScheme.Restriction` pins down the object scheme, the
arrow scheme, the source, the target and the morphism to the ambient groupoid of a realization of
a restriction, but not its identity, its inverse or its composition.  Those three are pinned down
all the same, because a generalized point of the arrow scheme of a restriction is determined by
its source, its target and its underlying ambient arrow.

## Main results

* `AlgebraicGeometry.GroupoidScheme.Restriction.identity_eq`,
  `AlgebraicGeometry.GroupoidScheme.Restriction.inverse_eq` and
  `AlgebraicGeometry.GroupoidScheme.Restriction.comp_eq`: the identity, the inverse and the
  composition of a realization of a restriction are the identity, the inverse and the composition
  of the chosen iterated fibre product.

## References

* [Stacks Project, Tag 02VB](https://stacks.math.columbia.edu/tag/02VB)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids Stacks.Groupoids.GroupoidScheme

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}} {G : Stacks.Groupoids.GroupoidScheme S} {X : Over S}
  {p : X ⟶ G.objects} (Gr : Restriction G p)

/-- The source morphism of a realization of a restriction, read as the source of the chosen
iterated fibre product. -/
theorem Restriction.restrictionSource_eq :
    AlgebraicGeometry.restrictionSource G p =
      eqToHom Gr.arrows_eq.symm ≫ Gr.groupoid.source ≫ eqToHom Gr.objects_eq := by
  rw [Gr.source_eq]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, eqToHom_trans,
    Category.comp_id]

/-- The target morphism of a realization of a restriction, read as the target of the chosen
iterated fibre product. -/
theorem Restriction.restrictionTarget_eq :
    AlgebraicGeometry.restrictionTarget G p =
      eqToHom Gr.arrows_eq.symm ≫ Gr.groupoid.target ≫ eqToHom Gr.objects_eq := by
  rw [Gr.target_eq]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, eqToHom_trans,
    Category.comp_id]

/-- The projection to the ambient arrow scheme of a realization of a restriction, read as the
projection of the chosen iterated fibre product. -/
theorem Restriction.restrictionArrowsToArrows_eq :
    AlgebraicGeometry.restrictionArrowsToArrows G p =
      eqToHom Gr.arrows_eq.symm ≫ Gr.hom.mapArrows := by
  rw [Gr.mapArrows_eq]
  simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

/-- The source of a realization of a restriction, transported to the source of the chosen
iterated fibre product. -/
theorem Restriction.source_comp_eqToHom :
    Gr.groupoid.source ≫ eqToHom Gr.objects_eq =
      eqToHom Gr.arrows_eq ≫ AlgebraicGeometry.restrictionSource G p := by
  rw [Gr.restrictionSource_eq]
  simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

/-- The target of a realization of a restriction, transported to the target of the chosen
iterated fibre product. -/
theorem Restriction.target_comp_eqToHom :
    Gr.groupoid.target ≫ eqToHom Gr.objects_eq =
      eqToHom Gr.arrows_eq ≫ AlgebraicGeometry.restrictionTarget G p := by
  rw [Gr.restrictionTarget_eq]
  simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

-- A generalized point of the arrow scheme of a realization of a restriction is determined by
-- its source, its target and its underlying arrow of the ambient groupoid.  That is
-- `AlgebraicGeometry.GroupoidScheme.Restriction.hom_ext` in
-- `StacksFrontier/AlgebraicGeometry/Groupoids/More/IteratedRestriction.lean`, which states and
-- proves it for an arbitrary realization and takes the realization as an explicit argument.
-- It is not restated here.

/-- **The identity of a realization of a restriction** is the identity arrow of the chosen
iterated fibre product. -/
theorem Restriction.identity_eq :
    Gr.groupoid.identity =
      eqToHom Gr.objects_eq ≫ restrictionIdentity G p ≫ eqToHom Gr.arrows_eq.symm := by
  have hsrc : Gr.groupoid.identity ≫ Gr.groupoid.source ≫ eqToHom Gr.objects_eq =
      eqToHom Gr.objects_eq := by
    rw [← Category.assoc, Gr.groupoid.source_identity, Category.id_comp]
  have htgt : Gr.groupoid.identity ≫ Gr.groupoid.target ≫ eqToHom Gr.objects_eq =
      eqToHom Gr.objects_eq := by
    rw [← Category.assoc, Gr.groupoid.target_identity, Category.id_comp]
  have key : eqToHom Gr.objects_eq.symm ≫ Gr.groupoid.identity ≫ eqToHom Gr.arrows_eq =
      restrictionIdentity G p := by
    refine eq_restrictionIdentity_of_spec G p _ ?_ ?_ ?_
    · rw [Gr.restrictionSource_eq]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [hsrc, eqToHom_trans, eqToHom_refl]
    · rw [Gr.restrictionTarget_eq]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [htgt, eqToHom_trans, eqToHom_refl]
    · rw [Gr.restrictionArrowsToArrows_eq]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [← Gr.hom.map_identity, Gr.mapObjects_eq]
      simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  rw [← key]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

/-- **The inverse of a realization of a restriction** is the inverse of the chosen iterated fibre
product. -/
theorem Restriction.inverse_eq :
    Gr.groupoid.inverse =
      eqToHom Gr.arrows_eq ≫ restrictionInverse G p ≫ eqToHom Gr.arrows_eq.symm := by
  have hinv := AlgebraicGeometry.groupoidHom_map_inverse Gr.hom
  have hsrc : Gr.groupoid.inverse ≫ Gr.groupoid.source ≫ eqToHom Gr.objects_eq =
      Gr.groupoid.target ≫ eqToHom Gr.objects_eq := by
    rw [← Category.assoc, Gr.groupoid.source_inverse]
  have htgt : Gr.groupoid.inverse ≫ Gr.groupoid.target ≫ eqToHom Gr.objects_eq =
      Gr.groupoid.source ≫ eqToHom Gr.objects_eq := by
    rw [← Category.assoc, Gr.groupoid.target_inverse]
  have harr : Gr.groupoid.inverse ≫ Gr.hom.mapArrows = Gr.hom.mapArrows ≫ G.inverse := hinv.symm
  have key : eqToHom Gr.arrows_eq.symm ≫ Gr.groupoid.inverse ≫ eqToHom Gr.arrows_eq =
      restrictionInverse G p := by
    refine eq_restrictionInverse_of_spec G p _ ?_ ?_ ?_
    · rw [Gr.restrictionSource_eq, Gr.restrictionTarget_eq]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [hsrc]
    · rw [Gr.restrictionTarget_eq, Gr.restrictionSource_eq]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [htgt]
    · rw [Gr.restrictionArrowsToArrows_eq]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [harr, ← Category.assoc, ← Gr.restrictionArrowsToArrows_eq]
  rw [← key]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

/-- The comparison of the schemes of composable pairs: that of a realization of a restriction with
that of the chosen iterated fibre product. -/
def Restriction.composablesComparison :
    pullback Gr.groupoid.source Gr.groupoid.target ⟶ restrictionComposablePairs G p :=
  pullback.map Gr.groupoid.source Gr.groupoid.target (AlgebraicGeometry.restrictionSource G p)
    (AlgebraicGeometry.restrictionTarget G p) (eqToHom Gr.arrows_eq) (eqToHom Gr.arrows_eq)
    (eqToHom Gr.objects_eq) Gr.source_comp_eqToHom Gr.target_comp_eqToHom

/-- The comparison of composable pairs commutes with the first projection. -/
theorem Restriction.composablesComparison_comp_fst :
    Gr.composablesComparison ≫ composablePairsFst G p =
      pullback.fst Gr.groupoid.source Gr.groupoid.target ≫ eqToHom Gr.arrows_eq :=
  pullback.lift_fst _ _ _

/-- The comparison of composable pairs commutes with the second projection. -/
theorem Restriction.composablesComparison_comp_snd :
    Gr.composablesComparison ≫ composablePairsSnd G p =
      pullback.snd Gr.groupoid.source Gr.groupoid.target ≫ eqToHom Gr.arrows_eq :=
  pullback.lift_snd _ _ _

/-- The composition of a realization of a restriction is the composite of the two projections of
its scheme of composable pairs. -/
theorem Restriction.comp_eq_compose :
    Gr.groupoid.compose (pullback.fst Gr.groupoid.source Gr.groupoid.target)
        (pullback.snd Gr.groupoid.source Gr.groupoid.target) pullback.condition =
      Gr.groupoid.comp := by
  change pullback.lift (pullback.fst Gr.groupoid.source Gr.groupoid.target)
    (pullback.snd Gr.groupoid.source Gr.groupoid.target) pullback.condition ≫
      Gr.groupoid.comp = _
  refine (congrArg (fun k => k ≫ Gr.groupoid.comp) (pullback.hom_ext ?_ ?_)).trans
    (Category.id_comp _)
  · exact (pullback.lift_fst _ _ _).trans (Category.id_comp _).symm
  · exact (pullback.lift_snd _ _ _).trans (Category.id_comp _).symm

/-- **The composition of a realization of a restriction** is the composition of the chosen
iterated fibre product. -/
theorem Restriction.comp_eq :
    Gr.groupoid.comp =
      Gr.composablesComparison ≫ restrictionComposition G p ≫ eqToHom Gr.arrows_eq.symm := by
  have w' : ((pullback.fst Gr.groupoid.source Gr.groupoid.target ≫ Gr.hom.mapArrows) ≫
      G.source) = ((pullback.snd Gr.groupoid.source Gr.groupoid.target ≫
        Gr.hom.mapArrows) ≫ G.target) := by
    simp only [Category.assoc, Gr.hom.map_source, Gr.hom.map_target]
    simp only [← Category.assoc, pullback.condition]
  have w₀ : (composablePairsFst G p ≫ AlgebraicGeometry.restrictionArrowsToArrows G p) ≫
      G.source = (composablePairsSnd G p ≫
        AlgebraicGeometry.restrictionArrowsToArrows G p) ≫ G.target := by
    rw [Category.assoc, Category.assoc,
      ← AlgebraicGeometry.GroupoidScheme.restriction_condition,
      AlgebraicGeometry.GroupoidScheme.restriction_condition',
      ← Category.assoc, ← Category.assoc, pullback.condition]
  have hfst : Gr.composablesComparison ≫ composablePairsFst G p ≫
      AlgebraicGeometry.restrictionArrowsToArrows G p =
      pullback.fst Gr.groupoid.source Gr.groupoid.target ≫ Gr.hom.mapArrows := by
    rw [← Category.assoc, Gr.composablesComparison_comp_fst, Category.assoc,
      Gr.restrictionArrowsToArrows_eq]
    simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  have hsnd : Gr.composablesComparison ≫ composablePairsSnd G p ≫
      AlgebraicGeometry.restrictionArrowsToArrows G p =
      pullback.snd Gr.groupoid.source Gr.groupoid.target ≫ Gr.hom.mapArrows := by
    rw [← Category.assoc, Gr.composablesComparison_comp_snd, Category.assoc,
      Gr.restrictionArrowsToArrows_eq]
    simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  have hcs : Gr.groupoid.comp ≫ Gr.groupoid.source ≫ eqToHom Gr.objects_eq =
      pullback.snd Gr.groupoid.source Gr.groupoid.target ≫ Gr.groupoid.source ≫
        eqToHom Gr.objects_eq := by
    rw [← Category.assoc, Gr.groupoid.source_comp, Category.assoc]
  have hct : Gr.groupoid.comp ≫ Gr.groupoid.target ≫ eqToHom Gr.objects_eq =
      pullback.fst Gr.groupoid.source Gr.groupoid.target ≫ Gr.groupoid.target ≫
        eqToHom Gr.objects_eq := by
    rw [← Category.assoc, Gr.groupoid.target_comp, Category.assoc]
  have hmap : eqToHom Gr.arrows_eq ≫ AlgebraicGeometry.restrictionArrowsToArrows G p =
      Gr.hom.mapArrows := by
    rw [Gr.restrictionArrowsToArrows_eq, ← Category.assoc, eqToHom_trans, eqToHom_refl,
      Category.id_comp]
  have key : Gr.groupoid.comp ≫ eqToHom Gr.arrows_eq =
      Gr.composablesComparison ≫ restrictionComposition G p := by
    refine AlgebraicGeometry.GroupoidScheme.restriction_hom_ext G p _ _ ?_ ?_ ?_
    · have hL : (Gr.groupoid.comp ≫ eqToHom Gr.arrows_eq) ≫
          AlgebraicGeometry.restrictionSource G p =
          pullback.snd Gr.groupoid.source Gr.groupoid.target ≫ eqToHom Gr.arrows_eq ≫
            AlgebraicGeometry.restrictionSource G p := by
        rw [Category.assoc, ← Gr.source_comp_eqToHom, hcs, Gr.source_comp_eqToHom]
      have hR : (Gr.composablesComparison ≫ restrictionComposition G p) ≫
          AlgebraicGeometry.restrictionSource G p =
          pullback.snd Gr.groupoid.source Gr.groupoid.target ≫ eqToHom Gr.arrows_eq ≫
            AlgebraicGeometry.restrictionSource G p := by
        rw [Category.assoc, restrictionComposition_comp_source, ← Category.assoc,
          Gr.composablesComparison_comp_snd, Category.assoc]
      exact hL.trans hR.symm
    · have hL : (Gr.groupoid.comp ≫ eqToHom Gr.arrows_eq) ≫
          AlgebraicGeometry.restrictionTarget G p =
          pullback.fst Gr.groupoid.source Gr.groupoid.target ≫ eqToHom Gr.arrows_eq ≫
            AlgebraicGeometry.restrictionTarget G p := by
        rw [Category.assoc, ← Gr.target_comp_eqToHom, hct, Gr.target_comp_eqToHom]
      have hR : (Gr.composablesComparison ≫ restrictionComposition G p) ≫
          AlgebraicGeometry.restrictionTarget G p =
          pullback.fst Gr.groupoid.source Gr.groupoid.target ≫ eqToHom Gr.arrows_eq ≫
            AlgebraicGeometry.restrictionTarget G p := by
        rw [Category.assoc, restrictionComposition_comp_target, ← Category.assoc,
          Gr.composablesComparison_comp_fst, Category.assoc]
      exact hL.trans hR.symm
    · have hL : (Gr.groupoid.comp ≫ eqToHom Gr.arrows_eq) ≫
          AlgebraicGeometry.restrictionArrowsToArrows G p =
          G.compose (pullback.fst Gr.groupoid.source Gr.groupoid.target ≫ Gr.hom.mapArrows)
            (pullback.snd Gr.groupoid.source Gr.groupoid.target ≫ Gr.hom.mapArrows) w' := by
        rw [Category.assoc, hmap]
        refine (congrArg (fun k => k ≫ Gr.hom.mapArrows) Gr.comp_eq_compose.symm).trans ?_
        exact Gr.hom.map_comp _ _ _ pullback.condition w'
      have hR : (Gr.composablesComparison ≫ restrictionComposition G p) ≫
          AlgebraicGeometry.restrictionArrowsToArrows G p =
          G.compose (pullback.fst Gr.groupoid.source Gr.groupoid.target ≫ Gr.hom.mapArrows)
            (pullback.snd Gr.groupoid.source Gr.groupoid.target ≫ Gr.hom.mapArrows) w' := by
        rw [Category.assoc, restrictionComposition_comp_arrowsToArrows,
          ← restrictionAmbientComp_eq_compose G p w₀,
          ← groupoidCompose_precomp G Gr.composablesComparison _ _ w₀
            (by rw [hfst, hsnd]; exact w')]
        exact groupoidCompose_arrow_eq _ _ _ _ _ w' hfst hsnd
      exact hL.trans hR.symm
  rw [← Category.assoc, ← key, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

end AlgebraicGeometry.GroupoidScheme

namespace AlgebraicGeometry.Space

/-- An isomorphism of algebraic spaces over `S` is finite: its base change along any morphism
from a chart is that chart itself, with the identity as projection. -/
theorem isFinite_of_isIso (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : Y ⟶ Z) [IsIso f] : IsFinite B S hS f := by
  intro U hU ξ
  refine ⟨U, 𝟙 U, ξ ≫ inv f, hU, ?_, ?_⟩
  · rw [CategoryTheory.Functor.map_id]
    exact inferInstanceAs (_root_.AlgebraicGeometry.IsFinite (𝟙 _))
  · rw [CategoryTheory.Functor.map_id]
    exact IsPullback.of_vert_isIso ⟨by rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id,
      Category.id_comp]⟩

end AlgebraicGeometry.Space

namespace Stacks.Groupoids.GroupoidScheme

open AlgebraicGeometry.Space

variable {S : Scheme.{u}}
  (G : Stacks.Groupoids.GroupoidScheme S) (C : BigFppfSite.{u}) (hS : C.Contains S)
  (hU : C.Contains G.objects.left) (hR : C.Contains G.arrows.left)
  (hP : C.Contains (pullback G.source G.target).left)
  {X : Over S} (hX : C.Contains X.left) (p : X ⟶ G.objects)
  (hA : C.Contains (pullback p G.target).left)
  (hB : C.Contains (pullback G.source p).left)
  (hRA : C.Contains (AlgebraicGeometry.restrictionArrows G p).left)
  (Rs : GroupoidInAlgebraicSpaces.Restriction (G.realization C hS hU hR hP)
    (realizationMap G C hS hU hR hP hX p))
  (P : GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid Rs.groupoid)

/-- The open subscheme of the arrow scheme cut out by a splitting is contained in the big fppf
site: it is the source of a monomorphism into a scheme the site contains. -/
theorem contains_splittingOpens :
    C.Contains (openOver (AlgebraicGeometry.restrictionArrows G p)
      (splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P)).left :=
  C.contains_of_mono (splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P).ι hRA

/-- The inclusion of the open cut out by a splitting, read as a morphism of the big fppf site. -/
def splittingOpensHom :
    schemeSiteObject C hS (contains_splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P) ⟶
      schemeSiteObject C hS hRA :=
  schemeSiteMap C hS (contains_splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P) hRA
    (openOverι (AlgebraicGeometry.restrictionArrows G p)
      (splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P))

/-- The inclusion of the open cut out by a splitting is an open immersion of schemes. -/
theorem isOpenImmersion_splittingOpensHom :
    _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme C S hS).map
      (splittingOpensHom G C hS hU hR hP hX p hA hB hRA Rs P)) := by
  rw [splittingOpensHom, toScheme_map_schemeSiteMap_eq]
  exact inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion
    (splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P).ι)

/-- The image of the inclusion of the open cut out by a splitting is that open, as a subspace of
the space represented by the arrow scheme. -/
theorem range_splittingOpensHom :
    Subfunctor.range (yoneda.map (splittingOpensHom G C hS hU hR hP hX p hA hB hRA Rs P)) =
      splittingSubfunctor G C hS hU hR hP hX p hA hB hRA Rs P := by
  refine Eq.trans (range_yoneda_map_eq_subspaceOfOpens C S hS _
    (isOpenImmersion_splittingOpensHom G C hS hU hR hP hX p hA hB hRA Rs P)
    (show ((BigFppfOver.toScheme C S hS).obj (schemeSiteObject C hS hRA)).Opens from
      splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P) ?_) ?_
  · rw [splittingOpensHom, toScheme_map_schemeSiteMap_eq]
    exact (splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P).range_ι
  · exact subspaceOfOpens_opensOfOpenSubspace C S hS (schemeSiteObject C hS hRA)
      (splittingSubfunctor G C hS hU hR hP hX p hA hB hRA Rs P)
      (isOpenSubspace_splittingSubfunctor G C hS hU hR hP hX p hA hB hRA Rs P)

/-- The morphism of spaces represented by the inclusion of the open cut out by a splitting is a
monomorphism. -/
theorem mono_yoneda_splittingOpensHom :
    Mono (yoneda.map (splittingOpensHom G C hS hU hR hP hX p hA hB hRA Rs P)) :=
  mono_of_presheaf_isOpenImmersion
    ((presheaf_yoneda_map_iff C S hS inferInstance _).2
      (isOpenImmersion_splittingOpensHom G C hS hU hR hP hX p hA hB hRA Rs P))

/-- The inclusion of the open cut out by a splitting, followed by a morphism of the restriction
that the identification of arrow spaces carries to a morphism of the realized restriction. -/
private theorem splittingSubfunctor_ι_comp_map
    (f : AlgebraicGeometry.restrictionArrows G p ⟶ X)
    (g : Rs.groupoid.arrows.obj ⟶ Rs.groupoid.objects.obj)
    (hfg : (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom ≫ g =
      yoneda.map (schemeSiteMap C hS hRA hX f) ≫
        eqToHom (restrictionObjectsObj_eq G C hS hU hR hP hX p Rs).symm) :
    (splittingSubfunctor G C hS hU hR hP hX p hA hB hRA Rs P).ι ≫
        yoneda.map (schemeSiteMap C hS hRA hX f) =
      P.arrows.fromPreimage (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom ≫
        (P.arrows.ι ≫ g) ≫ eqToHom (restrictionObjectsObj_eq G C hS hU hR hP hX p Rs) := by
  have hsq := Subfunctor.isPullback_preimage
    (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom P.arrows
  have hf : yoneda.map (schemeSiteMap C hS hRA hX f) =
      (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom ≫ g ≫
        eqToHom (restrictionObjectsObj_eq G C hS hU hR hP hX p Rs) := by
    rw [← Category.assoc, hfg, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  rw [hf]
  change (P.arrows.preimage (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom).ι ≫
    (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom ≫ _ = _
  rw [← Category.assoc, ← hsq.w]
  simp only [Category.assoc]

/-- The inclusion of the open cut out by a splitting, followed by the source of the restriction,
is the inclusion of the arrows of the splitting followed by the source of the realized
restriction. -/
theorem splittingSubfunctor_ι_comp_source :
    (splittingSubfunctor G C hS hU hR hP hX p hA hB hRA Rs P).ι ≫
        yoneda.map (schemeSiteMap C hS hRA hX (AlgebraicGeometry.restrictionSource G p)) =
      P.arrows.fromPreimage
          (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom ≫
        (P.arrows.ι ≫ Rs.groupoid.source.hom) ≫
          eqToHom (restrictionObjectsObj_eq G C hS hU hR hP hX p Rs) :=
  splittingSubfunctor_ι_comp_map G C hS hU hR hP hX p hA hB hRA Rs P _ _
    (restrictionArrowsSpaceIso_hom_comp_source G C hS hU hR hP hX p hA hB hRA Rs)

/-- The inclusion of the open cut out by a splitting, followed by the target of the
restriction. -/
theorem splittingSubfunctor_ι_comp_target :
    (splittingSubfunctor G C hS hU hR hP hX p hA hB hRA Rs P).ι ≫
        yoneda.map (schemeSiteMap C hS hRA hX (AlgebraicGeometry.restrictionTarget G p)) =
      P.arrows.fromPreimage
          (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom ≫
        (P.arrows.ι ≫ Rs.groupoid.target.hom) ≫
          eqToHom (restrictionObjectsObj_eq G C hS hU hR hP hX p Rs) :=
  splittingSubfunctor_ι_comp_map G C hS hU hR hP hX p hA hB hRA Rs P _ _
    (restrictionArrowsSpaceIso_hom_comp_target G C hS hU hR hP hX p hA hB hRA Rs)

/-- The comparison of the arrows of a splitting with their preimage under the identification of
arrow spaces is an isomorphism, being a base change of that identification. -/
theorem isIso_fromPreimage_restrictionArrowsSpaceIso :
    IsIso (P.arrows.fromPreimage
      (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom) := by
  have hsq := Subfunctor.isPullback_preimage
    (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom P.arrows
  have hiso : (MorphismProperty.isomorphisms
      ((BigFppfOver C S hS)ᵒᵖ ⥤ Type u))
      (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom :=
    (MorphismProperty.isomorphisms.iff _).2 inferInstance
  exact (MorphismProperty.isomorphisms.iff _).1
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip hiso)

/-- A morphism out of the arrow scheme of the restriction that the identification of arrow spaces
carries to a finite morphism of the realized restriction is finite on the open cut out by a
splitting. -/
private theorem isFinite_splittingOpens_comp
    (f : AlgebraicGeometry.restrictionArrows G p ⟶ X)
    (g : Rs.groupoid.arrows.obj ⟶ Rs.groupoid.objects.obj)
    (hfg : (splittingSubfunctor G C hS hU hR hP hX p hA hB hRA Rs P).ι ≫
        yoneda.map (schemeSiteMap C hS hRA hX f) =
      P.arrows.fromPreimage (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom ≫
        (P.arrows.ι ≫ g) ≫ eqToHom (restrictionObjectsObj_eq G C hS hU hR hP hX p Rs))
    (hg : Space.IsFinite C S hS (P.arrows.ι ≫ g)) :
    _root_.AlgebraicGeometry.IsFinite
      (openOverι (AlgebraicGeometry.restrictionArrows G p)
          (splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P) ≫ f).left := by
  have := mono_yoneda_splittingOpensHom G C hS hU hR hP hX p hA hB hRA Rs P
  have : IsIso (P.arrows.fromPreimage
      (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom) :=
    isIso_fromPreimage_restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs P
  refine (isFinite_schemeSpaceMap_iff C hS
    (contains_splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P) hX _).1 ?_
  have hfin : Space.IsFinite C S hS
      ((splittingSubfunctor G C hS hU hR hP hX p hA hB hRA Rs P).ι ≫
        yoneda.map (schemeSiteMap C hS hRA hX f)) := by
    rw [hfg]
    exact isFinite_comp C S hS (isFinite_of_isIso C S hS
        (P.arrows.fromPreimage
          (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom))
      (isFinite_comp C S hS hg (isFinite_of_isIso C S hS
        (eqToHom (restrictionObjectsObj_eq G C hS hU hR hP hX p Rs))))
  rw [← range_splittingOpensHom G C hS hU hR hP hX p hA hB hRA Rs P] at hfin
  have hsplit : schemeSiteMap C hS
      (contains_splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P) hX
      (openOverι (AlgebraicGeometry.restrictionArrows G p)
          (splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P) ≫ f) =
      splittingOpensHom G C hS hU hR hP hX p hA hB hRA Rs P ≫ schemeSiteMap C hS hRA hX f :=
    schemeSiteMap_comp C hS _ hRA hX _ _
  change Space.IsFinite C S hS (yoneda.map (schemeSiteMap C hS
    (contains_splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P) hX _))
  rw [hsplit, yoneda.map_comp,
    ← rangeIsoOfMono_hom_ι C S hS
      (yoneda.map (splittingOpensHom G C hS hU hR hP hX p hA hB hRA Rs P)), Category.assoc]
  exact isFinite_comp C S hS (isFinite_of_isIso C S hS
    (rangeIsoOfMono C S hS
      (yoneda.map (splittingOpensHom G C hS hU hR hP hX p hA hB hRA Rs P))).hom) hfin

/-- **The source morphism of a splitting, read on the arrow scheme of the restriction, is
finite.** -/
theorem isFinite_splittingOpens_comp_restrictionSource :
    _root_.AlgebraicGeometry.IsFinite
      (openOverι (AlgebraicGeometry.restrictionArrows G p)
          (splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P) ≫
        AlgebraicGeometry.restrictionSource G p).left :=
  isFinite_splittingOpens_comp G C hS hU hR hP hX p hA hB hRA Rs P _ _
    (splittingSubfunctor_ι_comp_source G C hS hU hR hP hX p hA hB hRA Rs P) P.source_finite

/-- **The target morphism of a splitting, read on the arrow scheme of the restriction, is
finite.** -/
theorem isFinite_splittingOpens_comp_restrictionTarget :
    _root_.AlgebraicGeometry.IsFinite
      (openOverι (AlgebraicGeometry.restrictionArrows G p)
          (splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P) ≫
        AlgebraicGeometry.restrictionTarget G p).left :=
  isFinite_splittingOpens_comp G C hS hU hR hP hX p hA hB hRA Rs P _ _
    (splittingSubfunctor_ι_comp_target G C hS hU hR hP hX p hA hB hRA Rs P) P.target_finite

/-! ### The de-realized open finite subgroupoid -/

variable (hCP : C.Contains (restrictionComposablePairs G p).left)
  (Gr : AlgebraicGeometry.GroupoidScheme.Restriction G p)

/-- A point of the open cut out by a splitting lies in that open. -/
theorem mem_splittingOpens_openOverι
    (x : (openOver (AlgebraicGeometry.restrictionArrows G p)
      (splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P)).left) :
    (openOverι (AlgebraicGeometry.restrictionArrows G p)
        (splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P)).left.base x ∈
      splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P := x.2

/-- The inclusion of the open cut out by a splitting into the arrow scheme of a realization of
the restriction. -/
def splittingIncl :
    openOver (AlgebraicGeometry.restrictionArrows G p)
        (splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P) ⟶ Gr.groupoid.arrows :=
  openOverι (AlgebraicGeometry.restrictionArrows G p)
      (splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P) ≫ eqToHom Gr.arrows_eq.symm

/-- The source morphism of the open cut out by a splitting. -/
def splittingSource :
    openOver (AlgebraicGeometry.restrictionArrows G p)
        (splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P) ⟶ Gr.groupoid.objects :=
  openOverι (AlgebraicGeometry.restrictionArrows G p)
      (splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P) ≫
    AlgebraicGeometry.restrictionSource G p ≫ eqToHom Gr.objects_eq.symm

/-- The target morphism of the open cut out by a splitting. -/
def splittingTarget :
    openOver (AlgebraicGeometry.restrictionArrows G p)
        (splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P) ⟶ Gr.groupoid.objects :=
  openOverι (AlgebraicGeometry.restrictionArrows G p)
      (splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P) ≫
    AlgebraicGeometry.restrictionTarget G p ≫ eqToHom Gr.objects_eq.symm

/-- The source morphism of the open cut out by a splitting lies over the source of the chosen
iterated fibre product. -/
theorem splittingSource_comp_eqToHom :
    splittingSource G C hS hU hR hP hX p hA hB hRA Rs P Gr ≫ eqToHom Gr.objects_eq =
      openOverι (AlgebraicGeometry.restrictionArrows G p)
          (splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P) ≫
        AlgebraicGeometry.restrictionSource G p := by
  rw [splittingSource]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- The target morphism of the open cut out by a splitting lies over the target of the chosen
iterated fibre product. -/
theorem splittingTarget_comp_eqToHom :
    splittingTarget G C hS hU hR hP hX p hA hB hRA Rs P Gr ≫ eqToHom Gr.objects_eq =
      openOverι (AlgebraicGeometry.restrictionArrows G p)
          (splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P) ≫
        AlgebraicGeometry.restrictionTarget G p := by
  rw [splittingTarget]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- The comparison of the composable pairs of the open cut out by a splitting with the composable
pairs of the chosen iterated fibre product. -/
def splittingComposables :
    pullback (splittingSource G C hS hU hR hP hX p hA hB hRA Rs P Gr)
        (splittingTarget G C hS hU hR hP hX p hA hB hRA Rs P Gr) ⟶
      restrictionComposablePairs G p :=
  pullback.map _ _ (AlgebraicGeometry.restrictionSource G p)
    (AlgebraicGeometry.restrictionTarget G p)
    (openOverι (AlgebraicGeometry.restrictionArrows G p)
      (splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P))
    (openOverι (AlgebraicGeometry.restrictionArrows G p)
      (splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P)) (eqToHom Gr.objects_eq)
    (splittingSource_comp_eqToHom G C hS hU hR hP hX p hA hB hRA Rs P Gr)
    (splittingTarget_comp_eqToHom G C hS hU hR hP hX p hA hB hRA Rs P Gr)

/-- The identity arrow of a realization of the restriction lies in the open cut out by a
splitting. -/
theorem mem_splittingOpens_identity (x : Gr.groupoid.objects.left) :
    (eqToHom Gr.objects_eq ≫ restrictionIdentity G p).left.base x ∈
      splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P := by
  rw [Over.comp_left, Scheme.Hom.comp_apply]
  exact mem_splittingOpens_restrictionIdentity G C hS hU hR hP hX p hA hB hRA Rs P _

/-- The inverse of an arrow of the open cut out by a splitting lies in that open. -/
theorem mem_splittingOpens_inverse
    (x : (openOver (AlgebraicGeometry.restrictionArrows G p)
      (splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P)).left) :
    (openOverι (AlgebraicGeometry.restrictionArrows G p)
          (splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P) ≫
        restrictionInverse G p).left.base x ∈
      splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P := by
  rw [Over.comp_left, Scheme.Hom.comp_apply]
  exact mem_splittingOpens_restrictionInverse G C hS hU hR hP hX p hA hB hRA Rs P _
    (mem_splittingOpens_openOverι G C hS hU hR hP hX p hA hB hRA Rs P x)

include hCP in
/-- The composite of a composable pair of arrows of the open cut out by a splitting lies in that
open. -/
theorem mem_splittingOpens_composition
    (x : (pullback (splittingSource G C hS hU hR hP hX p hA hB hRA Rs P Gr)
      (splittingTarget G C hS hU hR hP hX p hA hB hRA Rs P Gr)).left) :
    (splittingComposables G C hS hU hR hP hX p hA hB hRA Rs P Gr ≫
        restrictionComposition G p).left.base x ∈
      splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P := by
  have hfst := congrArg
    (fun k : pullback (splittingSource G C hS hU hR hP hX p hA hB hRA Rs P Gr)
      (splittingTarget G C hS hU hR hP hX p hA hB hRA Rs P Gr) ⟶
        AlgebraicGeometry.restrictionArrows G p => k.left.base x)
    (show splittingComposables G C hS hU hR hP hX p hA hB hRA Rs P Gr ≫
        composablePairsFst G p =
        pullback.fst (splittingSource G C hS hU hR hP hX p hA hB hRA Rs P Gr)
            (splittingTarget G C hS hU hR hP hX p hA hB hRA Rs P Gr) ≫
          openOverι (AlgebraicGeometry.restrictionArrows G p)
            (splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P) from
      pullback.lift_fst _ _ _)
  have hsnd := congrArg
    (fun k : pullback (splittingSource G C hS hU hR hP hX p hA hB hRA Rs P Gr)
      (splittingTarget G C hS hU hR hP hX p hA hB hRA Rs P Gr) ⟶
        AlgebraicGeometry.restrictionArrows G p => k.left.base x)
    (show splittingComposables G C hS hU hR hP hX p hA hB hRA Rs P Gr ≫
        composablePairsSnd G p =
        pullback.snd (splittingSource G C hS hU hR hP hX p hA hB hRA Rs P Gr)
            (splittingTarget G C hS hU hR hP hX p hA hB hRA Rs P Gr) ≫
          openOverι (AlgebraicGeometry.restrictionArrows G p)
            (splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P) from
      pullback.lift_snd _ _ _)
  simp only [Over.comp_left, Scheme.Hom.comp_apply] at hfst hsnd
  rw [Over.comp_left, Scheme.Hom.comp_apply]
  refine mem_splittingOpens_restrictionComposition G C hS hU hR hP hX p hA hB hRA hCP Rs P _
    ?_ ?_
  · rw [hfst]
    exact mem_splittingOpens_openOverι G C hS hU hR hP hX p hA hB hRA Rs P _
  · rw [hsnd]
    exact mem_splittingOpens_openOverι G C hS hU hR hP hX p hA hB hRA Rs P _

/-- The inclusion of the open cut out by a splitting is a monomorphism. -/
theorem mono_splittingIncl :
    Mono (splittingIncl G C hS hU hR hP hX p hA hB hRA Rs P Gr) := by
  change Mono (openOverι (AlgebraicGeometry.restrictionArrows G p)
    (splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P) ≫ eqToHom Gr.arrows_eq.symm)
  infer_instance

/-- The inclusion of the open cut out by a splitting is an open immersion. -/
theorem isOpenImmersion_splittingIncl :
    _root_.AlgebraicGeometry.IsOpenImmersion
      (splittingIncl G C hS hU hR hP hX p hA hB hRA Rs P Gr).left := by
  have hiso : IsIso (eqToHom Gr.arrows_eq.symm).left :=
    inferInstanceAs (IsIso ((Over.forget S).map (eqToHom Gr.arrows_eq.symm)))
  change _root_.AlgebraicGeometry.IsOpenImmersion
    ((openOverι (AlgebraicGeometry.restrictionArrows G p)
      (splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P) ≫ eqToHom Gr.arrows_eq.symm).left)
  rw [Over.comp_left]
  infer_instance

/-- A finite morphism to the objects of the restriction stays finite after identifying them with
the objects of a realization of the restriction. -/
private theorem isFinite_comp_eqToHom_objects_symm {Y : Over S} (u : Y ⟶ X)
    (hu : _root_.AlgebraicGeometry.IsFinite u.left) :
    _root_.AlgebraicGeometry.IsFinite (u ≫ eqToHom Gr.objects_eq.symm).left := by
  have hiso : IsIso (eqToHom Gr.objects_eq.symm).left :=
    inferInstanceAs (IsIso ((Over.forget S).map (eqToHom Gr.objects_eq.symm)))
  rw [Over.comp_left]
  infer_instance

/-- The source morphism of the open cut out by a splitting is finite. -/
theorem isFinite_splittingSource :
    _root_.AlgebraicGeometry.IsFinite
      (splittingSource G C hS hU hR hP hX p hA hB hRA Rs P Gr).left :=
  isFinite_comp_eqToHom_objects_symm G p Gr _
    (isFinite_splittingOpens_comp_restrictionSource G C hS hU hR hP hX p hA hB hRA Rs P)

/-- The target morphism of the open cut out by a splitting is finite. -/
theorem isFinite_splittingTarget :
    _root_.AlgebraicGeometry.IsFinite
      (splittingTarget G C hS hU hR hP hX p hA hB hRA Rs P Gr).left :=
  isFinite_comp_eqToHom_objects_symm G p Gr _
    (isFinite_splittingOpens_comp_restrictionTarget G C hS hU hR hP hX p hA hB hRA Rs P)

/-- The source morphism of the open cut out by a splitting is the restriction of the source of a
realization of the restriction. -/
theorem splittingSource_ι :
    splittingSource G C hS hU hR hP hX p hA hB hRA Rs P Gr ≫ 𝟙 Gr.groupoid.objects =
      splittingIncl G C hS hU hR hP hX p hA hB hRA Rs P Gr ≫ Gr.groupoid.source := by
  rw [splittingSource, splittingIncl, Category.comp_id, Gr.source_eq]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- The target morphism of the open cut out by a splitting is the restriction of the target of a
realization of the restriction. -/
theorem splittingTarget_ι :
    splittingTarget G C hS hU hR hP hX p hA hB hRA Rs P Gr ≫ 𝟙 Gr.groupoid.objects =
      splittingIncl G C hS hU hR hP hX p hA hB hRA Rs P Gr ≫ Gr.groupoid.target := by
  rw [splittingTarget, splittingIncl, Category.comp_id, Gr.target_eq]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- The comparison of composable pairs of the open cut out by a splitting factors through the
comparison for a realization of the restriction. -/
theorem splittingComposables_eq
    (h₁ : splittingSource G C hS hU hR hP hX p hA hB hRA Rs P Gr ≫ 𝟙 Gr.groupoid.objects =
      splittingIncl G C hS hU hR hP hX p hA hB hRA Rs P Gr ≫ Gr.groupoid.source)
    (h₂ : splittingTarget G C hS hU hR hP hX p hA hB hRA Rs P Gr ≫ 𝟙 Gr.groupoid.objects =
      splittingIncl G C hS hU hR hP hX p hA hB hRA Rs P Gr ≫ Gr.groupoid.target) :
    splittingComposables G C hS hU hR hP hX p hA hB hRA Rs P Gr =
      pullback.map _ _ Gr.groupoid.source Gr.groupoid.target
          (splittingIncl G C hS hU hR hP hX p hA hB hRA Rs P Gr)
          (splittingIncl G C hS hU hR hP hX p hA hB hRA Rs P Gr) (𝟙 Gr.groupoid.objects)
          h₁ h₂ ≫
        Gr.composablesComparison := by
  refine pullback.hom_ext ?_ ?_
  · refine (pullback.lift_fst _ _ _).trans ?_
    rw [Category.assoc, Gr.composablesComparison_comp_fst, ← Category.assoc, pullback.lift_fst,
      splittingIncl]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  · refine (pullback.lift_snd _ _ _).trans ?_
    rw [Category.assoc, Gr.composablesComparison_comp_snd, ← Category.assoc, pullback.lift_snd,
      splittingIncl]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- The composition morphism of the open cut out by a splitting is the restriction of the
composition of a realization of the restriction. -/
theorem splittingComp_ι
    (h₁ : splittingSource G C hS hU hR hP hX p hA hB hRA Rs P Gr ≫ 𝟙 Gr.groupoid.objects =
      splittingIncl G C hS hU hR hP hX p hA hB hRA Rs P Gr ≫ Gr.groupoid.source)
    (h₂ : splittingTarget G C hS hU hR hP hX p hA hB hRA Rs P Gr ≫ 𝟙 Gr.groupoid.objects =
      splittingIncl G C hS hU hR hP hX p hA hB hRA Rs P Gr ≫ Gr.groupoid.target)
    (h : ∀ x, (splittingComposables G C hS hU hR hP hX p hA hB hRA Rs P Gr ≫
        restrictionComposition G p).left.base x ∈
      splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P) :
    openOverLift (splittingComposables G C hS hU hR hP hX p hA hB hRA Rs P Gr ≫
          restrictionComposition G p) _ h ≫
        splittingIncl G C hS hU hR hP hX p hA hB hRA Rs P Gr =
      pullback.map _ _ Gr.groupoid.source Gr.groupoid.target
          (splittingIncl G C hS hU hR hP hX p hA hB hRA Rs P Gr)
          (splittingIncl G C hS hU hR hP hX p hA hB hRA Rs P Gr) (𝟙 Gr.groupoid.objects)
          h₁ h₂ ≫
        Gr.groupoid.comp := by
  have hL : openOverLift (splittingComposables G C hS hU hR hP hX p hA hB hRA Rs P Gr ≫
        restrictionComposition G p) _ h ≫
      splittingIncl G C hS hU hR hP hX p hA hB hRA Rs P Gr =
      (splittingComposables G C hS hU hR hP hX p hA hB hRA Rs P Gr ≫
        restrictionComposition G p) ≫ eqToHom Gr.arrows_eq.symm := by
    change openOverLift _ _ h ≫ (openOverι (AlgebraicGeometry.restrictionArrows G p)
      (splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P) ≫ eqToHom Gr.arrows_eq.symm) = _
    rw [← Category.assoc, openOverLift_comp_openOverι]
  rw [hL, Gr.comp_eq, ← Category.assoc,
    ← splittingComposables_eq G C hS hU hR hP hX p hA hB hRA Rs P Gr h₁ h₂]
  simp only [Category.assoc]

include hCP in
/-- **Conditions (a) and (b) of Stacks 04RK for a de-realized splitting.**  The open of the arrow
scheme of a restriction cut out by a splitting of the realized restriction is a subgroupoid of
every realization of the restriction. -/
def splittingMonoSubgroupoid :
    Stacks.Groupoids.GroupoidScheme.MonoSubgroupoid Gr.groupoid where
  objects := Gr.groupoid.objects
  arrows := openOver (AlgebraicGeometry.restrictionArrows G p)
    (splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P)
  ιObjects := 𝟙 Gr.groupoid.objects
  ιArrows := splittingIncl G C hS hU hR hP hX p hA hB hRA Rs P Gr
  mono_ιObjects := inferInstance
  mono_ιArrows := mono_splittingIncl G C hS hU hR hP hX p hA hB hRA Rs P Gr
  source := splittingSource G C hS hU hR hP hX p hA hB hRA Rs P Gr
  target := splittingTarget G C hS hU hR hP hX p hA hB hRA Rs P Gr
  comp := openOverLift (splittingComposables G C hS hU hR hP hX p hA hB hRA Rs P Gr ≫
      restrictionComposition G p) _
    (mem_splittingOpens_composition G C hS hU hR hP hX p hA hB hRA Rs P hCP Gr)
  identity := openOverLift (eqToHom Gr.objects_eq ≫ restrictionIdentity G p) _
    (mem_splittingOpens_identity G C hS hU hR hP hX p hA hB hRA Rs P Gr)
  inverse := openOverLift (openOverι (AlgebraicGeometry.restrictionArrows G p)
      (splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P) ≫ restrictionInverse G p) _
    (mem_splittingOpens_inverse G C hS hU hR hP hX p hA hB hRA Rs P)
  source_ι := splittingSource_ι G C hS hU hR hP hX p hA hB hRA Rs P Gr
  target_ι := splittingTarget_ι G C hS hU hR hP hX p hA hB hRA Rs P Gr
  identity_ι := by
    rw [splittingIncl, Category.id_comp, Gr.identity_eq, ← Category.assoc,
      openOverLift_comp_openOverι, Category.assoc]
  inverse_ι := by
    rw [splittingIncl, Gr.inverse_eq, ← Category.assoc, openOverLift_comp_openOverι]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  comp_ι := splittingComp_ι G C hS hU hR hP hX p hA hB hRA Rs P Gr _ _ _

include hCP in
/-- **The de-realized open finite subgroupoid.**  The open of the arrow scheme of a restriction
cut out by a splitting of the realized restriction is an open finite subgroupoid of every
realization of the restriction. -/
def splittingOpenFiniteSubgroupoid :
    Stacks.Groupoids.GroupoidScheme.OpenFiniteSubgroupoid Gr.groupoid where
  subgroupoid := (splittingMonoSubgroupoid G C hS hU hR hP hX p hA hB hRA Rs P hCP
    Gr).toGroupoidScheme
  objects_eq := rfl
  inclusion := (splittingMonoSubgroupoid G C hS hU hR hP hX p hA hB hRA Rs P hCP Gr).hom
  mapObjects_eq := rfl
  arrows_open := isOpenImmersion_splittingIncl G C hS hU hR hP hX p hA hB hRA Rs P Gr
  source_finite := isFinite_splittingSource G C hS hU hR hP hX p hA hB hRA Rs P Gr
  target_finite := isFinite_splittingTarget G C hS hU hR hP hX p hA hB hRA Rs P Gr

/-! ### Condition (c): the stabilizer of a point -/

/-- Transporting a point of the arrow scheme of a realization of a restriction to the chosen
iterated fibre product and back again returns the point. -/
theorem eqToHom_arrows_apply_symm (r : Gr.groupoid.arrows.left) :
    (eqToHom Gr.arrows_eq.symm).left.base ((eqToHom Gr.arrows_eq).left.base r) = r :=
  over_eqToHom_apply_symm Gr.arrows_eq.symm r

/-- A morphism of the arrow scheme of a realization of a restriction that is a transport of a
morphism of the realization is computed on points by that morphism. -/
private theorem restrictionHom_apply (f : AlgebraicGeometry.restrictionArrows G p ⟶ X)
    (g : Gr.groupoid.arrows ⟶ Gr.groupoid.objects)
    (h : f = eqToHom Gr.arrows_eq.symm ≫ g ≫ eqToHom Gr.objects_eq) (r : Gr.groupoid.arrows.left) :
    f.left.base ((eqToHom Gr.arrows_eq).left.base r) =
      (eqToHom Gr.objects_eq).left.base (g.left.base r) := by
  have h := congrArg (fun k : AlgebraicGeometry.restrictionArrows G p ⟶ X => k.left.base
    ((eqToHom Gr.arrows_eq).left.base r)) h
  simp only [Over.comp_left, Scheme.Hom.comp_apply] at h
  rw [h, eqToHom_arrows_apply_symm]

/-- The source of an arrow of a realization of a restriction, read on the chosen iterated fibre
product. -/
theorem restrictionSource_apply (r : Gr.groupoid.arrows.left) :
    (AlgebraicGeometry.restrictionSource G p).left.base
        ((eqToHom Gr.arrows_eq).left.base r) =
      (eqToHom Gr.objects_eq).left.base (Gr.groupoid.source.left.base r) :=
  restrictionHom_apply G p Gr _ _ Gr.restrictionSource_eq r

/-- The target of an arrow of a realization of a restriction, read on the chosen iterated fibre
product. -/
theorem restrictionTarget_apply (r : Gr.groupoid.arrows.left) :
    (AlgebraicGeometry.restrictionTarget G p).left.base
        ((eqToHom Gr.arrows_eq).left.base r) =
      (eqToHom Gr.objects_eq).left.base (Gr.groupoid.target.left.base r) :=
  restrictionHom_apply G p Gr _ _ Gr.restrictionTarget_eq r

/-- The point of the object space of the realized restriction carried by a point of the object
scheme of a realization of the restriction. -/
def derealizedObjectPoint (x : Gr.groupoid.objects.left) :
    Space.points C S hS Rs.groupoid.objects.obj :=
  Space.pointsMap C S hS (yoneda.obj (schemeSiteObject C hS hX))
    (eqToHom (restrictionObjectsObj_eq G C hS hU hR hP hX p Rs).symm)
    ((pointsEquivScheme C S hS (schemeSiteObject C hS hX)).symm
      ((eqToHom Gr.objects_eq).left.base x))

/-- A morphism of the arrow scheme of the restriction that is carried by the identification of
arrow spaces to a morphism of the realized restriction sends a point to the point carried by its
image. -/
private theorem pointsMap_restrictionArrowsSpaceIso
    (f : AlgebraicGeometry.restrictionArrows G p ⟶ X)
    (g : Rs.groupoid.arrows.obj ⟶ Rs.groupoid.objects.obj)
    (hfg : (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom ≫ g =
      yoneda.map (schemeSiteMap C hS hRA hX f) ≫
        eqToHom (restrictionObjectsObj_eq G C hS hU hR hP hX p Rs).symm)
    (r : Gr.groupoid.arrows.left) (x : Gr.groupoid.objects.left)
    (hf : f.left.base ((eqToHom Gr.arrows_eq).left.base r) = (eqToHom Gr.objects_eq).left.base x) :
    Space.pointsMap C S hS Rs.groupoid.arrows.obj g
        (Space.pointsMap C S hS (yoneda.obj (schemeSiteObject C hS hRA))
          (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom
          ((pointsEquivScheme C S hS (schemeSiteObject C hS hRA)).symm
            ((eqToHom Gr.arrows_eq).left.base r))) =
      derealizedObjectPoint G C hS hU hR hP hX p Rs Gr x := by
  have hkey : Space.pointsMap C S hS (yoneda.obj (schemeSiteObject C hS hRA))
      (yoneda.map (schemeSiteMap C hS hRA hX f))
      ((pointsEquivScheme C S hS (schemeSiteObject C hS hRA)).symm
        ((eqToHom Gr.arrows_eq).left.base r)) =
      (pointsEquivScheme C S hS (schemeSiteObject C hS hX)).symm
        ((eqToHom Gr.objects_eq).left.base x) := by
    have hz := pointsToScheme_pointsEquivScheme_symm C hS (schemeSiteObject C hS hRA)
      ((eqToHom Gr.arrows_eq).left.base r)
    refine (Equiv.eq_symm_apply _).2 ?_
    change Space.pointsToScheme C S hS (schemeSiteObject C hS hX) _ = _
    rw [pointsToScheme_pointsMap_yoneda, toScheme_map_schemeSiteMap_eq]
    exact (congrArg (fun t : (AlgebraicGeometry.restrictionArrows G p).left => f.left.base t)
      hz).trans hf
  refine Eq.trans ?_ (congrArg (Space.pointsMap C S hS
    (yoneda.obj (schemeSiteObject C hS hX))
    (eqToHom (restrictionObjectsObj_eq G C hS hU hR hP hX p Rs).symm)) hkey)
  rw [← Space.pointsMap_comp_apply, ← Space.pointsMap_comp_apply, hfg]

/-- The source of a point of the arrow scheme, read in the realized restriction. -/
theorem pointsMap_source_restrictionArrowsSpaceIso (r : Gr.groupoid.arrows.left)
    (x : Gr.groupoid.objects.left) (hrs : Gr.groupoid.source.left.base r = x) :
    Space.pointsMap C S hS Rs.groupoid.arrows.obj Rs.groupoid.source.hom
        (Space.pointsMap C S hS (yoneda.obj (schemeSiteObject C hS hRA))
          (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom
          ((pointsEquivScheme C S hS (schemeSiteObject C hS hRA)).symm
            ((eqToHom Gr.arrows_eq).left.base r))) =
      derealizedObjectPoint G C hS hU hR hP hX p Rs Gr x :=
  pointsMap_restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs Gr _ _
    (restrictionArrowsSpaceIso_hom_comp_source G C hS hU hR hP hX p hA hB hRA Rs) r x
    ((restrictionSource_apply G p Gr r).trans (congrArg _ hrs))

/-- The target of a point of the arrow scheme, read in the realized restriction. -/
theorem pointsMap_target_restrictionArrowsSpaceIso (r : Gr.groupoid.arrows.left)
    (x : Gr.groupoid.objects.left) (hrt : Gr.groupoid.target.left.base r = x) :
    Space.pointsMap C S hS Rs.groupoid.arrows.obj Rs.groupoid.target.hom
        (Space.pointsMap C S hS (yoneda.obj (schemeSiteObject C hS hRA))
          (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom
          ((pointsEquivScheme C S hS (schemeSiteObject C hS hRA)).symm
            ((eqToHom Gr.arrows_eq).left.base r))) =
      derealizedObjectPoint G C hS hU hR hP hX p Rs Gr x :=
  pointsMap_restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs Gr _ _
    (restrictionArrowsSpaceIso_hom_comp_target G C hS hU hR hP hX p hA hB hRA Rs) r x
    ((restrictionTarget_apply G p Gr r).trans (congrArg _ hrt))

include hA hB hRA hCP in
/-- **The de-realized strong splitting.**  If a splitting of the realization of a restriction
contains every arrow with both endpoints at the point carried by a point `x` of the object
scheme, then the open of the arrow scheme it cuts out is a strong splitting of every realization
of the restriction over `x`. -/
theorem isStronglySplitAt_of_contains_arrows (x : Gr.groupoid.objects.left)
    (hcontains : ∀ r : Space.points C S hS Rs.groupoid.arrows.obj,
      Space.pointsMap C S hS Rs.groupoid.arrows.obj Rs.groupoid.source.hom r =
          derealizedObjectPoint G C hS hU hR hP hX p Rs Gr x ∧
        Space.pointsMap C S hS Rs.groupoid.arrows.obj Rs.groupoid.target.hom r =
          derealizedObjectPoint G C hS hU hR hP hX p Rs Gr x →
      ∃ q : Space.points C S hS P.arrows.toFunctor,
        Space.pointsMap C S hS P.arrows.toFunctor P.arrows.ι q = r) :
    IsStronglySplitAt Gr.groupoid x := by
  refine ⟨{ splittingOpenFiniteSubgroupoid G C hS hU hR hP hX p hA hB hRA Rs P hCP Gr with
    contains_stabilizer := ?_ }⟩
  intro r hrs hrt
  have hmem : (eqToHom Gr.arrows_eq).left.base r ∈
      splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P := by
    refine (mem_splittingOpens_iff_of_eq G C hS hU hR hP hX p hA hB hRA Rs P
      (pointsToScheme_pointsEquivScheme_symm C hS (schemeSiteObject C hS hRA)
        ((eqToHom Gr.arrows_eq).left.base r))).2 ?_
    obtain ⟨q, hq⟩ := hcontains _
      ⟨pointsMap_source_restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs Gr r x hrs,
        pointsMap_target_restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs Gr r x hrt⟩
    exact ⟨q, hq⟩
  refine ⟨⟨(eqToHom Gr.arrows_eq).left.base r, hmem⟩, ?_⟩
  change (splittingIncl G C hS hU hR hP hX p hA hB hRA Rs P Gr).left.base
    ⟨(eqToHom Gr.arrows_eq).left.base r, hmem⟩ = r
  refine Eq.trans ?_ (eqToHom_arrows_apply_symm G p Gr r)
  change (openOverι (AlgebraicGeometry.restrictionArrows G p)
      (splittingOpens G C hS hU hR hP hX p hA hB hRA Rs P) ≫
    eqToHom Gr.arrows_eq.symm).left.base ⟨(eqToHom Gr.arrows_eq).left.base r, hmem⟩ = _
  rfl

end Stacks.Groupoids.GroupoidScheme

end

end
