module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineChartSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescent
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRepresentable

/-!
# The chapter's convention on the site survives relocalization

Section 70.2 of the source (tag 07SD) assumes that every ring it considers has its spectrum in
the big fppf site. For an inverse system `D` of presheaves on the big fppf site of `S` with
affine transition morphisms this is `AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`: for
every stage `D i` and every affine scheme-valued point `Z ⟶ D i`, the limit of the affine
schemes `Z ×_{D i} D j`, `j` over `i`, lies in the site.

The convention is a statement about schemes, and it does not depend on the base: relocalizing the
system along a morphism `S ⟶ S'` of the site does not change the schemes `Z ×_{D i} D j`. A
scheme-valued point of the relocalized stage over `S'` is the relocalization of a scheme-valued
point of the stage over `S` with the same source scheme, and relocalization preserves fibre
products and carries representables to representables with the same underlying scheme. So the
two diagrams of base changes have isomorphic underlying diagrams of schemes, and the limits of
these lie in the site together.

This is what lets a descent along a system over `S` be carried out over the terminal scheme, as
the proof of Stacks 07SQ does.

## Main results

* `AlgebraicGeometry.BigFppfOver.LimitInSite.of_iso`: whether the limit of a cofiltered diagram
  of objects of a big fppf site lies in the site depends only on the underlying diagram of
  schemes.
* `AlgebraicGeometry.Space.relocalizeStageBaseChangeIso`: relocalization carries the diagram of
  base changes along a scheme-valued point to the diagram of base changes along its
  relocalization.
* `AlgebraicGeometry.Space.SiteContainsBaseChangeLimits.relocalize`: the convention for a system
  over `S` gives it for the relocalized system over `S'`.
* `AlgebraicGeometry.Space.DescentSituation.siteContainsBaseChangeLimits_viewOverIntegers`: the
  convention for a descent situation over `S` gives it for its view over the terminal scheme.

## References

* [Stacks Project, Tag 07SD](https://stacks.math.columbia.edu/tag/07SD)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- **The convention for a diagram depends only on its underlying schemes.** If two cofiltered
diagrams of objects of big fppf sites, possibly over different bases, have isomorphic underlying
diagrams of schemes, then the limit of one lies in the site exactly when the limit of the other
does: a limit cone of one is carried to a limit cone of the other with the same vertex. -/
theorem BigFppfOver.LimitInSite.of_iso {B : BigFppfSite.{u}} {S S' : Scheme.{u}}
    {hS : B.Contains S} {hS' : B.Contains S'} {J : Type u} [Category.{u} J]
    {V : J ⥤ BigFppfOver B S hS} {V' : J ⥤ BigFppfOver B S' hS'}
    (e : underlyingDiagram V ≅ underlyingDiagram V') (hV' : BigFppfOver.LimitInSite V') :
    BigFppfOver.LimitInSite V := fun c hc =>
  hV' ((Cone.postcompose e.hom).obj c) ((IsLimit.postcomposeHomEquiv e c).symm hc)

namespace Space

variable {B : BigFppfSite.{u}} {S S' : Scheme.{u}} {hS : B.Contains S} {hS' : B.Contains S'}
  (k : B.obj hS ⟶ B.obj hS')

section BaseChange

variable {I : Type u} [Category.{u} I] (i₀ : I) (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (Z : BigAffineFppf B S hS)
  (σ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z) ⟶ D.obj i₀)
  (Z' : BigAffineFppf B S' hS')
  (φ : yoneda.obj ((BigAffineFppf.inclusion B S' hS').obj Z') ≅
    (OverShriek.relocalizePresheafFunctor k).obj
      (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z)))

/-- The relocalization of the base change of a stage over `i₀` along `σ` is a base change of the
relocalized stage along `φ ≫ Λ σ`: relocalization preserves fibre products. -/
theorem isPullback_relocalize_stageBaseChange (j : Over i₀) :
    IsPullback
      ((OverShriek.relocalizePresheafFunctor k).map (stageBaseChangeFst B S hS i₀ D Z σ j))
      ((OverShriek.relocalizePresheafFunctor k).map (stageBaseChangeSnd B S hS i₀ D Z σ j) ≫
        φ.inv)
      ((OverShriek.relocalizePresheafFunctor k).map (D.map j.hom))
      (φ.hom ≫ (OverShriek.relocalizePresheafFunctor k).map σ) := by
  refine ((isPullback_stageBaseChange B S hS i₀ D Z σ j).map
    (OverShriek.relocalizePresheafFunctor k)).of_iso (Iso.refl _) (Iso.refl _) φ.symm
    (Iso.refl _) (by simp) (by simp) (by simp) (by simp)

/-- The comparison of a relocalized base change with the base change of the relocalized stage,
at one stage over `i₀`. -/
def relocalizeStageBaseChangeIsoApp (j : Over i₀) :
    (OverShriek.relocalizePresheafFunctor k).obj ((stageBaseChangeDiagram B S hS i₀ D Z σ).obj j) ≅
      (stageBaseChangeDiagram B S' hS' i₀ (D ⋙ OverShriek.relocalizePresheafFunctor k) Z'
        (φ.hom ≫ (OverShriek.relocalizePresheafFunctor k).map σ)).obj j :=
  have h := isPullback_relocalize_stageBaseChange k i₀ D Z σ Z' φ j
  haveI := h.hasPullback
  h.isoPullback

/-- The comparison at a stage lies over the relocalized stage. -/
theorem relocalizeStageBaseChangeIsoApp_hom_fst (j : Over i₀) :
    (relocalizeStageBaseChangeIsoApp k i₀ D Z σ Z' φ j).hom ≫
        stageBaseChangeFst B S' hS' i₀ (D ⋙ OverShriek.relocalizePresheafFunctor k) Z'
          (φ.hom ≫ (OverShriek.relocalizePresheafFunctor k).map σ) j =
      (OverShriek.relocalizePresheafFunctor k).map (stageBaseChangeFst B S hS i₀ D Z σ j) := by
  have h := isPullback_relocalize_stageBaseChange k i₀ D Z σ Z' φ j
  haveI := h.hasPullback
  exact h.isoPullback_hom_fst

/-- The comparison at a stage lies over the scheme-valued point. -/
theorem relocalizeStageBaseChangeIsoApp_hom_snd (j : Over i₀) :
    (relocalizeStageBaseChangeIsoApp k i₀ D Z σ Z' φ j).hom ≫
        stageBaseChangeSnd B S' hS' i₀ (D ⋙ OverShriek.relocalizePresheafFunctor k) Z'
          (φ.hom ≫ (OverShriek.relocalizePresheafFunctor k).map σ) j =
      (OverShriek.relocalizePresheafFunctor k).map (stageBaseChangeSnd B S hS i₀ D Z σ j) ≫
        φ.inv := by
  have h := isPullback_relocalize_stageBaseChange k i₀ D Z σ Z' φ j
  haveI := h.hasPullback
  exact h.isoPullback_hom_snd

/-- **Relocalization of the diagram of base changes.** The relocalization along `k` of the
diagram of base changes of the stages over `i₀` along `σ` is the diagram of base changes of the
relocalized stages along `φ ≫ Λ σ`. -/
def relocalizeStageBaseChangeIso :
    stageBaseChangeDiagram B S hS i₀ D Z σ ⋙ OverShriek.relocalizePresheafFunctor k ≅
      stageBaseChangeDiagram B S' hS' i₀ (D ⋙ OverShriek.relocalizePresheafFunctor k) Z'
        (φ.hom ≫ (OverShriek.relocalizePresheafFunctor k).map σ) :=
  NatIso.ofComponents (relocalizeStageBaseChangeIsoApp k i₀ D Z σ Z' φ)
    (fun {j j'} m => by
      refine (isPullback_stageBaseChange B S' hS' i₀ _ Z' _ j').hom_ext ?_ ?_
      · rw [Category.assoc, Category.assoc, stageBaseChangeDiagram_map_comp_fst,
          relocalizeStageBaseChangeIsoApp_hom_fst, ← Category.assoc,
          relocalizeStageBaseChangeIsoApp_hom_fst]
        exact ((Functor.map_comp (OverShriek.relocalizePresheafFunctor k) _ _).symm.trans
          (congrArg (OverShriek.relocalizePresheafFunctor k).map
            (stageBaseChangeDiagram_map_comp_fst B S hS i₀ D Z σ m))).trans
          (Functor.map_comp _ _ _)
      · rw [Category.assoc, Category.assoc, stageBaseChangeDiagram_map_comp_snd,
          relocalizeStageBaseChangeIsoApp_hom_snd, relocalizeStageBaseChangeIsoApp_hom_snd,
          Functor.comp_map, ← Category.assoc, ← Functor.map_comp,
          stageBaseChangeDiagram_map_comp_snd])

end BaseChange

/-- **The chapter's convention survives relocalization.** If an inverse system `D` of presheaves
on the big fppf site of `S` with affine transition morphisms satisfies the convention of
Section 70.2 (tag 07SD), then so does its relocalization along a morphism `k : S ⟶ S'` of the
site, as a system of presheaves on the big fppf site of `S'`.

A scheme-valued point `Z ⟶ Λ (D i)` of a relocalized stage is `Λ σ` for a scheme-valued point
`σ` of the stage `D i` whose source has the same underlying scheme
(`CategoryTheory.OverShriek.exists_eq_relocalizeYonedaFactorIso_comp`); relocalization carries
the diagram of base changes along `σ` to that along the given point
(`AlgebraicGeometry.Space.relocalizeStageBaseChangeIso`) and representables to representables
with the same underlying scheme (`CategoryTheory.OverShriek.relocalizeYonedaIso`). So any lift of
the second diagram has the same underlying schemes as a chart system of `D`, whose limit lies in
the site by the convention for `D`. -/
theorem SiteContainsBaseChangeLimits.relocalize {I : Type u} [Category.{u} I] [IsCofiltered I]
    {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hconv : SiteContainsBaseChangeLimits B S hS D) :
    SiteContainsBaseChangeLimits B S' hS' (D ⋙ OverShriek.relocalizePresheafFunctor k) := by
  intro i Z' g W iso
  obtain ⟨ψ, h, σ, hg⟩ := OverShriek.exists_eq_relocalizeYonedaFactorIso_comp k g
  have haff : IsAffine ((BigFppfOver.toScheme B S hS).obj (Over.mk ψ)) := Z'.property
  set Z : BigAffineFppf B S hS := ⟨Over.mk ψ, haff⟩ with hZdef
  set C := affineChartSystem B S hS i D Z σ hAffine with hC
  have hL : BigFppfOver.LimitInSite C.siteDiagram := hconv i Z σ C.diagram C.iso
  set φ := OverShriek.relocalizeYonedaFactorIso k h with hφ
  -- the two diagrams of presheaves over `S'`
  have ey : (W ⋙ BigAffineFppf.inclusion B S' hS') ⋙ yoneda ≅
      (C.siteDiagram ⋙ Over.map k) ⋙ yoneda :=
    iso ≪≫ eqToIso (by rw [hg]) ≪≫
      (relocalizeStageBaseChangeIso k i D Z σ Z' φ).symm ≪≫
      Functor.isoWhiskerRight C.iso.symm (OverShriek.relocalizePresheafFunctor k) ≪≫
      Functor.isoWhiskerLeft C.siteDiagram (OverShriek.relocalizeYonedaIso k)
  have e : W ⋙ BigAffineFppf.inclusion B S' hS' ≅ C.siteDiagram ⋙ Over.map k :=
    (Functor.FullyFaithful.whiskeringRight (Functor.FullyFaithful.ofFullyFaithful yoneda)
      _).preimageIso ey
  exact BigFppfOver.LimitInSite.of_iso (V' := C.siteDiagram)
    (Functor.isoWhiskerRight e (BigFppfOver.toScheme B S' hS')) hL

/-- **The chapter's convention for a descent situation is unchanged by viewing it over the
terminal scheme.** The system of the view is the relocalized system, so this is
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits.relocalize`. It is the convention-form
counterpart of `AlgebraicGeometry.Space.DescentSituation.isSiteSmall_viewOverIntegers_system`. -/
theorem DescentSituation.siteContainsBaseChangeLimits_viewOverIntegers
    (hZ : B.Contains (⊤_ Scheme.{u})) {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : DescentSituation B S hS hZ I) (hconv : SiteContainsBaseChangeLimits B S hS D.system) :
    SiteContainsBaseChangeLimits B (⊤_ Scheme.{u}) hZ
      (D.viewOverIntegers B S hS hZ).system :=
  have : Nonempty I := ⟨D.base⟩
  SiteContainsBaseChangeLimits.relocalize (integersMap B S hS hZ)
    (fun f => D.transition_affine f) hconv

end Space

end AlgebraicGeometry
