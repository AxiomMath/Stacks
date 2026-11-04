module

public import Mathlib
public import StacksCore.FieldTheory.PurelyTranscendental
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEtaleDescent
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteEnlargement
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SchemeStage
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Jacobson
public import StacksFrontier.AlgebraicGeometry.Spaces.JacobsonFiniteTypePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.JacobsonPointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SmallApproximationOverBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.NoetherianApproximationInduction
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.MapToFiniteType
public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.StepInputs
public import StacksFrontier.AlgebraicGeometry.Spaces.OverFields.AlgClosureFGSubalgebraDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCover
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoverAffineAtlas
import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFree
import StacksFrontier.AlgebraicGeometry.Spaces.Flat
import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointsFromEtaleCover
import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Spaces.OverFields.PurelyTranscendentalDescent.AlgebraMapSections

/-!
# Reduction to the quasi-compact case for purely transcendental descent

Covering an algebraic space by quasi-compact open subspaces and gluing representability back
along a Zariski cover; affine morphisms and quasi-separatedness of algebraic spaces; closed
points in the schematic locus give a scheme; affine representations of limits of affine
morphisms.

This is part of `StacksFrontier.AlgebraicGeometry.Spaces.OverFields.PurelyTranscendentalDescent`.

## Main results

* `exists_zariski_cover_with_quasiCompact_members`: an algebraic space has a Zariski covering by
  quasi-compact open subspaces.
* `isRepresentable_of_zariskiCover`: an algebraic space with a Zariski covering by representable
  open subspaces is representable.
* `isQuasiCompact_of_isAffineHom`: an algebraic space affine over a quasi-compact one is
  quasi-compact.
* `isRepresentable_of_closedPoints_mem_schematicLocus`: an algebraic space with Jacobson space of
  points whose closed points lie in the schematic locus is representable.
* `isAffineHom_cone_projection`: the projections of a cofiltered limit of algebraic spaces along
  affine transition morphisms are affine.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

namespace PurelyTranscendentalDescent

/-- A morphism of presheaves on the big fppf site over `S` that is representable by étale
morphisms of schemes is étale in the sense of `AlgebraicGeometry.Space.IsEtale`. -/
theorem isEtale_of_presheaf_etale
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hf : (MorphismProperty.presheaf
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS))) f) :
    AlgebraicGeometry.Space.IsEtale B S hS f := by
  have : MorphismProperty.IsStableUnderComposition (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    (inferInstance : MorphismProperty.IsMultiplicative
      (@Etale.{u} : MorphismProperty Scheme.{u})).toIsStableUnderComposition
  let P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  have : P.IsStableUnderComposition := MorphismProperty.IsStableUnderComposition.inverseImage _
  have : P.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition P
  exact fun U g hg => MorphismProperty.comp_mem P.presheaf g f hg hf

private theorem isQuasiCompact_of_affine_etale_surjective_atlas
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (U : AlgebraicGeometry.BigFppfOver B S hS) (f : yoneda.obj U ⟶ F)
    (hU : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U))
    (hsurj : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf f)
    (hetale : (MorphismProperty.presheaf
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS))) f) :
    AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS F :=
  (AlgebraicGeometry.Space.isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover
    B S hS F hF).2 ⟨U, f, hU, hsurj,
      isEtale_of_presheaf_etale B S hS f hetale⟩

/-- Every algebraic space over `S` admits a Zariski covering by open subspaces each of which is
quasi-compact. -/
theorem exists_zariski_cover_with_quasiCompact_members
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F) :
    ∃ (I : Type u) (V : I → Subfunctor F),
      AlgebraicGeometry.Space.IsZariskiCover B S hS I V ∧
        ∀ i, AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS (V i).toFunctor := by
  obtain ⟨I, V, hcover, hatlas⟩ :=
    AlgebraicGeometry.Space.exists_zariski_cover_affine_etale_atlas B S hS F hF
  refine ⟨I, V, hcover, fun i => ?_⟩
  obtain ⟨U, f, _, hU, hsurj, hetale, _, _⟩ := hatlas i
  exact isQuasiCompact_of_affine_etale_surjective_atlas B S hS
    (V i).toFunctor (hcover.1 i).1 U f hU hsurj hetale

/-- If `f : G ⟶ F` is relatively representable and `F` is representable, then `G` is
representable. -/
theorem isRepresentable_of_relativelyRepresentable_of_isRepresentable
    {C : Type v} [Category.{w, v} C] {F G : Cᵒᵖ ⥤ Type w} (f : G ⟶ F)
    (hrel : yoneda.relativelyRepresentable f) (hF : F.IsRepresentable) :
    G.IsRepresentable := by
  have : IsIso (hrel.fst F.reprW.hom) := (hrel.isPullback F.reprW.hom).isIso_fst_of_isIso
  exact Functor.IsRepresentable.mk' (asIso (hrel.fst F.reprW.hom))

/-- For `p : W ⟶ (Over.map g).obj T`, restricting `yoneda.map p` along `g` yields a pullback
square over the morphism `Over.mk (p.left ≫ T.hom) ⟶ T` induced by `p.left`. -/
private theorem isPullback_relocalizeRestrict_map_yoneda_map
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS') (T : AlgebraicGeometry.BigFppfOver B S hS)
    {W : AlgebraicGeometry.BigFppfOver B S' hS'} (p : W ⟶ (Over.map g).obj T) :
    IsPullback
      (yonedaEquiv.symm
          (Over.isoMk (Iso.refl _) (Over.w p).symm :
            (Over.map g).obj (Over.mk (p.left ≫ T.hom)) ≅ W).hom :
        yoneda.obj (Over.mk (p.left ≫ T.hom) : AlgebraicGeometry.BigFppfOver B S hS) ⟶
          (OverShriek.relocalizeRestrict g).obj (yoneda.obj W))
      (yoneda.map (Over.homMk p.left rfl :
        (Over.mk (p.left ≫ T.hom) : AlgebraicGeometry.BigFppfOver B S hS) ⟶ T))
      ((OverShriek.relocalizeRestrict g).map (yoneda.map p))
      (yonedaEquiv.symm (𝟙 ((Over.map g).obj T)) :
        yoneda.obj T ⟶
          (OverShriek.relocalizeRestrict g).obj (yoneda.obj ((Over.map g).obj T))) := by
  let C := AlgebraicGeometry.BigFppfOver B S hS
  let H : C ⥤ AlgebraicGeometry.BigFppfOver B S' hS' := Over.map g
  let R := OverShriek.relocalizeRestrict g
  let W' : C := Over.mk (p.left ≫ T.hom)
  let s : W' ⟶ T := Over.homMk p.left rfl
  let e : H.obj W' ≅ W := Over.isoMk (Iso.refl _) (Over.w p).symm
  let θW : yoneda.obj W' ⟶ R.obj (yoneda.obj W) := yonedaEquiv.symm e.hom
  let θT : yoneda.obj T ⟶ R.obj (yoneda.obj (H.obj T)) := yonedaEquiv.symm (𝟙 (H.obj T))
  have hθ : θW ≫ R.map (yoneda.map p) = yoneda.map s ≫ θT := by
    apply yonedaEquiv.injective
    apply Over.OverMorphism.ext
    change e.hom.left ≫ p.left = (H.map s).left
    simp [e, s, H]
  change IsPullback θW (yoneda.map s) (R.map (yoneda.map p)) θT
  apply IsPullback.of_forall_isPullback_app (fun Z => ?_)
  rw [Types.isPullback_iff]
  refine ⟨by simpa using congrArg (fun α => α.app Z) hθ, fun x y hxy => ?_, fun a t h => ?_⟩
  · have hleft := congrArg Over.Hom.left hxy.1
    change x.left ≫ e.hom.left = y.left ≫ e.hom.left at hleft
    exact Over.OverMorphism.ext ((cancel_mono e.hom.left).mp hleft)
  · have hleft := congrArg Over.Hom.left h
    change a.left ≫ p.left = t.left at hleft
    let z : Z.unop ⟶ W' := Over.homMk a.left (by
      change a.left ≫ p.left ≫ T.hom = Z.unop.hom
      simpa [W'] using (congrArg (fun f => f ≫ T.hom) hleft).trans t.w)
    refine ⟨z, ?_, ?_⟩
    · apply Over.OverMorphism.ext
      change (H.map z).left ≫ e.hom.left = a.left
      simp [e, z, H]
    · apply Over.OverMorphism.ext
      change z.left ≫ s.left = t.left
      simpa [z, s] using hleft

/-- Let `g : S ⟶ S'` be a morphism of the big fppf site and `Q` a property of morphisms of schemes
respecting isomorphisms. If a morphism `f` of presheaves over `S'` is representable by morphisms
having `Q`, then so is its restriction `(OverShriek.relocalizeRestrict g).map f` over `S`. -/
theorem presheaf_property_restrict
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    {F G : (AlgebraicGeometry.BigFppfOver B S' hS')ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (Q : MorphismProperty Scheme.{u}) [MorphismProperty.RespectsIso Q]
    (hf : (MorphismProperty.inverseImage Q
      (AlgebraicGeometry.BigFppfOver.toScheme B S' hS')).presheaf f) :
    (MorphismProperty.inverseImage Q
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf
      ((OverShriek.relocalizeRestrict g).map f) := by
  let P' := MorphismProperty.inverseImage Q
    (AlgebraicGeometry.BigFppfOver.toScheme B S' hS')
  let P := MorphismProperty.inverseImage Q
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  change P'.relative yoneda f at hf
  apply MorphismProperty.relative.of_exists (P := P) (F := yoneda)
  intro T q
  let C := AlgebraicGeometry.BigFppfOver B S hS
  let C' := AlgebraicGeometry.BigFppfOver B S' hS'
  let H : C ⥤ C' := Over.map g
  let R := OverShriek.relocalizeRestrict g
  let x : G.obj (Opposite.op (H.obj T)) := q.app (Opposite.op T) (𝟙 T)
  let q₀ : yoneda.obj (H.obj T) ⟶ G := yonedaEquiv.symm x
  let W := hf.1.pullback q₀
  let p : W ⟶ H.obj T := hf.1.snd q₀
  let i : yoneda.obj W ⟶ F := hf.1.fst q₀
  have hsquare := hf.1.isPullback q₀
  let W' : C := Over.mk (p.left ≫ T.hom)
  let s : W' ⟶ T := Over.homMk p.left rfl
  let e : H.obj W' ≅ W := Over.isoMk (Iso.refl _) (Over.w p).symm
  let θW : yoneda.obj W' ⟶ R.obj (yoneda.obj W) := yonedaEquiv.symm e.hom
  let θT : yoneda.obj T ⟶ R.obj (yoneda.obj (H.obj T)) :=
    yonedaEquiv.symm (𝟙 (H.obj T))
  have hq : θT ≫ R.map q₀ = q := by
    apply yonedaEquiv.injective
    change ((R.map q₀).app (Opposite.op T))
      ((θT.app (Opposite.op T)) (𝟙 T)) = x
    simp only [Functor.whiskeringLeft_obj_obj, Functor.comp_obj, Functor.op_obj, yoneda_obj_obj,
      Functor.whiskeringLeft_obj_map, Functor.whiskerLeft_app, yonedaEquiv_symm_app,
      yonedaEquiv_symm_app_apply, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, R, q₀, x, θT]
    change G.map (𝟙 (H.obj T)).op x = x
    simp
  have hsq : IsPullback (θW ≫ R.map i) (yoneda.map s) (R.map f) q := by
    rw [← hq]
    change IsPullback (θW ≫ R.map (hf.1.fst q₀)) (yoneda.map s)
      (R.map f) (θT ≫ R.map q₀)
    exact (isPullback_relocalizeRestrict_map_yoneda_map B S S' hS hS' g T p).paste_horiz
      (hsquare.map R)
  refine ⟨W', θW ≫ R.map i, s, hsq, ?_⟩
  have hprop := hf.property q₀ i p hsquare
  change Q ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map s)
  change Q ((AlgebraicGeometry.BigFppfOver.toScheme B S' hS').map p) at hprop
  simpa [s] using hprop

private lemma subfunctor_eq_top_of_isLocallySurjective
    {C : Type v} [Category.{w, v} C] {J : GrothendieckTopology C}
    {F : Cᵒᵖ ⥤ Type w} (A : Subfunctor F)
    (hF : Presieve.IsSheaf J F) (hA : Presieve.IsSheaf J A.toFunctor)
    (hls : Presheaf.IsLocallySurjective J A.ι) : A = ⊤ := by
  have hcover (U : C) (x : F.obj (Opposite.op U)) : A.sieveOfSection x ∈ J U := by
    apply J.superset_covering ?_ (Presheaf.imageSieve_mem J A.ι x)
    rintro V f ⟨a, ha⟩
    change F.map f.op x ∈ A.obj (Opposite.op V)
    rw [← ha]
    exact a.property
  exact top_unique fun U x _ => (A.isSheaf_iff hF).1 hA U x (hcover U.unop x)

/-- If a representable subfunctor `U` of `F` is all of `F`, then `F` is representable. -/
private lemma isRepresentable_of_subfunctor_eq_top
    {C : Type v} [Category.{w, v} C] {F : Cᵒᵖ ⥤ Type w} (U : Subfunctor F)
    (hU : U.toFunctor.IsRepresentable) (h : U = ⊤) : F.IsRepresentable := by
  have : IsIso U.ι := (Subfunctor.eq_top_iff_isIso U).mp h
  exact isRepresentable_of_natIso U.toFunctor (asIso U.ι)

/-- An algebraic space admitting a Zariski covering by representable open subspaces is
representable. -/
theorem isRepresentable_of_zariskiCover
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (I : Type u) (U : I → Subfunctor F)
    (hcover : AlgebraicGeometry.Space.IsZariskiCover B S hS I U)
    (hrep : ∀ i, (U i).toFunctor.IsRepresentable) : F.IsRepresentable := by
  let J := AlgebraicGeometry.BigFppfOver.topology B S hS
  let Z := AlgebraicGeometry.Space.schematicLocus B S hS F
  obtain ⟨hZopen, hZrep⟩ : _ ∧ Z.toFunctor.IsRepresentable :=
    AlgebraicGeometry.Space.isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace
      B S hS hF
  have hsubset : ∀ i, U i ≤ Z := fun i =>
    AlgebraicGeometry.Space.le_schematicLocus B S hS F (U i) (hcover.1 i) (hrep i)
  have : Presheaf.IsLocallySurjective J (Sigma.desc fun i ↦ (U i).ι) := hcover.2
  let f := Sigma.desc fun i ↦ Subfunctor.homOfLe (hsubset i)
  have hfac : f ≫ Z.ι = Sigma.desc fun i ↦ (U i).ι := by
    ext i
    simp [f, Subfunctor.homOfLe_ι]
  have hZls : Presheaf.IsLocallySurjective J Z.ι :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hfac
  have hZtop : Z = ⊤ :=
    subfunctor_eq_top_of_isLocallySurjective Z
      ((isSheaf_iff_isSheaf_of_type J F).1 hF.isSheaf)
      ((isSheaf_iff_isSheaf_of_type J Z.toFunctor).1 hZopen.1.isSheaf) hZls
  exact isRepresentable_of_subfunctor_eq_top Z hZrep hZtop

/-- Affine morphisms are stable under base change: in a pullback square whose side `f` is affine,
the opposite side `q` is affine. -/
theorem isAffineHom_of_isPullback
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F F' G G' : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : F' ⟶ F} {q : F' ⟶ G'} {f : F ⟶ G} {g : G' ⟶ G}
    (h : IsPullback p q f g) (hf : AlgebraicGeometry.Space.IsAffineHom B S hS f) :
    AlgebraicGeometry.Space.IsAffineHom B S hS q := by
  intro Z z
  obtain ⟨W, a, b, hb⟩ := hf Z (z ≫ g)
  let a' := h.lift a (yoneda.map b ≫ z) (by simpa only [Category.assoc] using hb.w)
  exact ⟨W, a', b, IsPullback.of_right (by simpa only [a', IsPullback.lift_fst] using hb)
    (by simp only [a', IsPullback.lift_snd]) h⟩

/-- If `f : F ⟶ G` is an affine morphism of algebraic spaces and `G` is quasi-compact, then `F` is
quasi-compact. -/
theorem isQuasiCompact_of_isAffineHom
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G)
    (hf : AlgebraicGeometry.Space.IsAffineHom B S hS f)
    (hqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS G) :
    AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS F := by
  obtain ⟨U, a, ha, hs, he⟩ :=
    (AlgebraicGeometry.Space.isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover
      B S hS G hG).mp hqc
  obtain ⟨W, p, q, hp⟩ := hf ⟨U, ha⟩ a
  refine ⟨W.obj, p, ?_, ?_, ?_⟩
  · have := W.property
    infer_instance
  · let P := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
    have : P.presheaf.IsStableUnderBaseChange :=
      MorphismProperty.relative_isStableUnderBaseChange P
    exact MorphismProperty.of_isPullback hp.flip hs
  · let X : AlgebraicGeometry.AlgebraicSpaces B S hS := ⟨F, hF⟩
    let Y : AlgebraicGeometry.AlgebraicSpaces B S hS := ⟨G, hG⟩
    let A : AlgebraicGeometry.AlgebraicSpaces B S hS :=
      ⟨yoneda.obj U, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U⟩
    let T : AlgebraicGeometry.AlgebraicSpaces B S hS :=
      ⟨yoneda.obj W.obj, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS W.obj⟩
    let p' : T ⟶ X := ObjectProperty.homMk p
    let q' : T ⟶ A := ObjectProperty.homMk (yoneda.map q)
    let a' : A ⟶ Y := ObjectProperty.homMk a
    let f' : X ⟶ Y := ObjectProperty.homMk f
    have hp' : IsPullback q' p' a' f' :=
      IsPullback.of_map_of_faithful
        (ObjectProperty.ι (AlgebraicGeometry.IsAlgebraicSpace B S hS)) hp.flip
    exact AlgebraicGeometry.Space.isEtale_of_isPullback B S hS q' p' a' f' hp' he

/-- The inclusion of the schemes of the big fppf site `B` into all schemes preserves pullbacks. -/
theorem bigFppf_preservesPullbacks (B : AlgebraicGeometry.BigFppfSite.{u}) :
    PreservesLimitsOfShape WalkingCospan B.inclusion := by
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (fun X : Scheme.{u} => X.size < B.cutoff) :=
    ⟨fun e h => by rwa [← Scheme.size_congr e]⟩
  have : ObjectProperty.IsClosedUnderLimitsOfShape
      (fun X : Scheme.{u} => X.size < B.cutoff) WalkingCospan :=
    .mk' (by
      rintro _ ⟨D, hD⟩
      rw [Scheme.size_congr (HasLimit.isoOfNatIso (diagramIsoCospan D))]
      exact Scheme.size_pullback_lt _ _ (hD .left) (hD .right))
  infer_instance

private theorem presheaf_affine_yoneda
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicGeometry.BigFppfOver B S hS} (f : X ⟶ Y)
    (hf : IsAffineHom ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map f)) :
    (MorphismProperty.inverseImage (@IsAffineHom.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf (yoneda.map f) := by
  have : HasPullbacks B.Schemes := inferInstance
  have := bigFppf_preservesPullbacks B
  let P := MorphismProperty.inverseImage (@IsAffineHom.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  have : PreservesLimitsOfShape WalkingCospan
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS) := by
    change PreservesLimitsOfShape WalkingCospan (Over.forget _ ⋙ B.inclusion)
    infer_instance
  have : P.IsStableUnderBaseChange := ⟨fun h hp =>
    MorphismProperty.of_isPullback (P := @IsAffineHom.{u})
      (h.map (AlgebraicGeometry.BigFppfOver.toScheme B S hS)) hp⟩
  exact MorphismProperty.relative_map hf

/-- A morphism of presheaves representable by affine morphisms of schemes is affine in the sense of
`AlgebraicGeometry.Space.IsAffineHom`. -/
theorem isAffineHom_of_presheaf_affine
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hf : (MorphismProperty.inverseImage (@IsAffineHom.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf f) :
    AlgebraicGeometry.Space.IsAffineHom B S hS f := by
  intro Z z
  let W := hf.1.pullback z
  let q := hf.1.snd z
  have : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj Z.obj) := Z.property
  have : IsAffineHom ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q) :=
    hf.property_snd z
  have hW : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj W) := by
    have : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
        ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj Z)) := Z.property
    exact isAffine_of_isAffineHom ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q)
  exact ⟨⟨W, hW⟩, hf.1.fst z, q, hf.1.isPullback z⟩

/-- For `f : X ⟶ Y`, the square formed by `prod.snd : F ⨯ X ⟶ X`, `prod.map (𝟙 F) f`, `f` and
`prod.snd : F ⨯ Y ⟶ Y` is a pullback square. -/
theorem isPullback_prod_snd_map
    {C : Type*} [Category C] [HasBinaryProducts C]
    (F : C) {X Y : C} (f : X ⟶ Y) :
    IsPullback (prod.snd : F ⨯ X ⟶ X) (prod.map (𝟙 F) f) f prod.snd := by
  apply IsPullback.mk'
  · simp
  · intro W a b h₁ h₂
    apply prod.hom_ext
    · simpa using congrArg (fun t => t ≫ prod.fst) h₂
    · exact h₁
  · intro W a b h
    refine ⟨prod.lift (b ≫ prod.fst) a, by simp, ?_⟩
    apply prod.hom_ext
    · simp
    · simpa using h

/-- If the structure morphism of `X` is affine, then the projection `F ⨯ yoneda.obj X ⟶ F` is
representable by affine morphisms of schemes. -/
theorem presheaf_affine_prod_fst
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (X : AlgebraicGeometry.BigFppfOver B S hS)
    (hX : IsAffineHom (B.inclusion.map X.hom)) :
    (MorphismProperty.inverseImage (@IsAffineHom.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf
      (prod.fst : F ⨯ yoneda.obj X ⟶ F) := by
  let Z : AlgebraicGeometry.BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))
  let p : X ⟶ Z := Over.homMk X.hom (by simp [Z])
  have ht : IsTerminal (yoneda.obj Z) := IsTerminal.isTerminalObj yoneda _ Over.mkIdTerminal
  have hp := presheaf_affine_yoneda B S hS p hX
  have he : yoneda.map p = ht.from (yoneda.obj X) := ht.hom_ext _ _
  rw [he] at hp
  let P := MorphismProperty.inverseImage (@IsAffineHom.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  have : P.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange P
  exact MorphismProperty.of_isPullback
    (IsPullback.of_is_product (prodIsProd F (yoneda.obj X)) ht).flip hp

/-- The product of an algebraic space `F` over `S` with the functor represented by an object `X` of
the big fppf site over `S` is an algebraic space. -/
theorem isAlgebraicSpace_prod_yoneda
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (X : AlgebraicGeometry.BigFppfOver B S hS) :
    AlgebraicGeometry.IsAlgebraicSpace B S hS (F ⨯ yoneda.obj X) := by
  have hb := AlgebraicGeometry.isAlgebraicSpace_relocalizeRestrict B X.left.obj S X.left.property hS
    X.hom F hF
  have hv := AlgebraicGeometry.isAlgebraicSpace_viewOver B X.left.obj S X.left.property hS
    X.hom _ hb
  have e := relocalizeRestrictIsoProduct X.hom F ≪≫ prod.braiding _ _
  have hXeq : Over.mk X.hom = X := by cases X; rfl
  rw [hXeq] at e
  exact hv.of_iso e

/-- Let `f : F ⟶ G` be a morphism of algebraic spaces representable by affine morphisms of schemes.
If `G` is absolutely quasi-separated, then so is `F`. -/
theorem isQuasiSeparated_of_presheaf_affine
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G)
    (f : F ⟶ G)
    (hf : (MorphismProperty.inverseImage (@IsAffineHom.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf f)
    (hqs : AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ G) :
    AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ F := by
  refine AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hF
    hqs (f := f) ?_
  apply (AlgebraicGeometry.Space.isQuasiSeparated_iff_presheaf
    B S hS f hF hG hf.1).mpr
  refine ⟨hf.1, fun U V g p q hpb => ?_⟩
  have : IsAffineHom ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q) :=
    hf.property g p q hpb
  change QuasiSeparated ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q)
  infer_instance

/-- If `S` is quasi-separated, then an algebraic space quasi-separated over `S` is absolutely
quasi-separated. -/
theorem isQuasiSeparated_absolute_of_relative
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u})) [QuasiSeparatedSpace S]
    (F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (hqs : AlgebraicGeometry.Space.IsQuasiSeparatedOver B S hS F) :
    AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ F := by
  let T : AlgebraicGeometry.BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))
  have ht : IsTerminal (yoneda.obj T) := IsTerminal.isTerminalObj yoneda _ Over.mkIdTerminal
  have hTabs :=
    AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme
      B S hS (yoneda.obj T) hZ ⟨T, inferInstanceAs (QuasiSeparatedSpace S),
        ⟨Functor.RepresentableBy.yoneda T⟩⟩
  exact AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ
    hF hTabs
    (AlgebraicGeometry.Space.isQuasiSeparated_of_isQuasiSeparatedOver B S hS hqs (ht.from F))

/-- Let `F` be an algebraic space whose space of points is Jacobson. If every closed point of `F`
lies in the schematic locus of `F`, then `F` is representable. -/
theorem isRepresentable_of_closedPoints_mem_schematicLocus
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (hJac : @JacobsonSpace (AlgebraicGeometry.Space.points B S hS F)
      (AlgebraicGeometry.Space.pointTopology B S hS F))
    (hclosed : ∀ x : AlgebraicGeometry.Space.points B S hS F,
      @IsClosed _ (AlgebraicGeometry.Space.pointTopology B S hS F) ({x} : Set _) →
      x ∈ Set.range (AlgebraicGeometry.Space.pointsMap B S hS
        (AlgebraicGeometry.Space.schematicLocus B S hS F).toFunctor
        (AlgebraicGeometry.Space.schematicLocus B S hS F).ι)) : F.IsRepresentable := by
  let := AlgebraicGeometry.Space.pointTopology B S hS F
  have : JacobsonSpace (AlgebraicGeometry.Space.points B S hS F) := hJac
  let U := AlgebraicGeometry.Space.schematicLocus B S hS F
  obtain ⟨hU, hUrep⟩ :=
    AlgebraicGeometry.Space.isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace
      B S hS hF
  let V := AlgebraicGeometry.Space.openSubspacesOrderIso B S hS F hF ⟨U, hU⟩
  have hV : (V : Set _) = Set.range (AlgebraicGeometry.Space.pointsMap B S hS U.toFunctor U.ι) :=
    AlgebraicGeometry.Space.openSubspacesOrderIso_apply B S hS F hF ⟨U, hU⟩
  have hbad : (V : Set _)ᶜ ∩ closedPoints (AlgebraicGeometry.Space.points B S hS F) = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr fun x ⟨hx, hxc⟩ => hx (hV ▸ hclosed x hxc)
  have hVall : ∀ x : AlgebraicGeometry.Space.points B S hS F, x ∈ V := by
    have he := JacobsonSpace.closure_inter_closedPoints V.isOpen.isClosed_compl
    rw [hbad, closure_empty] at he
    intro x
    by_contra hx
    exact (he.symm ▸ hx : x ∈ (∅ : Set (AlgebraicGeometry.Space.points B S hS F)))
  obtain ⟨g, hg⟩ := (AlgebraicGeometry.Space.factorsThrough_openSubspace_iff_points
    B S hS hF hF U hU (𝟙 F)).mpr (fun x _ => hV ▸ hVall x)
  have htop : U = ⊤ := by
    apply top_unique
    intro T x _
    have hx : (g.app T x).val = x := congrArg (fun k => k.app T x) hg
    rw [← hx]
    exact (g.app T x).property
  exact isRepresentable_of_subfunctor_eq_top U hUrep htop

private theorem mk_globalSections_le (A : Scheme.{u}) :
    Cardinal.mk Γ(A, ⊤) ≤ A.size ^ A.size := by
  let f : Γ(A, ⊤) → ∀ V : A.affineOpens, Γ(A, V.1) :=
    fun x V => A.presheaf.map (homOfLE le_top).op x
  have hf : Function.Injective f := by
    intro x y h
    apply A.IsSheaf.section_ext
    intro p hp
    have hp' : p ∈ (⨆ V : A.affineOpens, V.1) := by
      rw [iSup_affineOpens_eq_top]
      trivial
    obtain ⟨V, hpV⟩ := TopologicalSpace.Opens.mem_iSup.mp hp'
    exact ⟨V.1, le_top, hpV, congrFun h V⟩
  calc
    Cardinal.mk Γ(A, ⊤) ≤ Cardinal.mk (∀ V : A.affineOpens, Γ(A, V.1)) :=
      Cardinal.mk_le_of_injective hf
    _ = Cardinal.prod (fun V : A.affineOpens => Cardinal.mk Γ(A, V.1)) := by
      rw [Cardinal.mk_pi]
    _ ≤ Cardinal.prod (fun _ : A.affineOpens => A.size) :=
      Cardinal.prod_le_prod _ _ A.mk_sections_le_size
    _ = A.size ^ Cardinal.mk A.affineOpens := by simp only [Cardinal.prod_const, Cardinal.lift_id]
    _ ≤ A.size ^ A.size := Cardinal.power_le_power_left
      (ne_of_gt (lt_of_lt_of_le Cardinal.aleph0_pos A.aleph0_le_size)) A.mk_affineOpens_le_size

private theorem size_spec_globalSections_lt
    (B : AlgebraicGeometry.BigFppfSite.{u}) (A : Scheme.{u}) (hA : B.Contains A) :
    B.Contains (Spec Γ(A, ⊤)) := by
  rw [AlgebraicGeometry.BigFppfSite.Contains, Scheme.size_Spec]
  apply max_lt B.aleph0_lt_cutoff
  apply (mk_globalSections_le A).trans_lt
  rw [Cardinal.power_self_eq A.aleph0_le_size]
  exact B.cutoff_isStrongPrelimit hA

private theorem exists_affine_factor_of_directed
    (B : AlgebraicGeometry.BigFppfSite.{u}) {A : Scheme.{u}} (hA : B.Contains A)
    {I : Type v} [Nonempty I] (Y : I → Scheme.{u}) [∀ i, IsAffine (Y i)]
    (f : ∀ i, A ⟶ Y i)
    (hf : Directed (· ≤ ·) (fun i => (f i).appTop.hom.range)) :
    ∃ (T : Scheme.{u}) (_ : IsAffine T) (_ : B.Contains T)
      (p : A ⟶ T) (g : ∀ i, T ⟶ Y i),
      Function.Injective p.appTop ∧ (∀ i, p ≫ g i = f i) ∧
      (∀ x : Γ(T, ⊤), ∃ i y, (g i).appTop y = x) ∧
      ∀ (Z : Scheme.{u}) (a b : Z ⟶ T), (∀ i, a ≫ g i = b ≫ g i) → a = b := by
  classical
  let R : Subring Γ(A, ⊤) := ⨆ i, (f i).appTop.hom.range
  let Rcat : CommRingCat := .of R
  let j : Rcat ⟶ Γ(A, ⊤) := CommRingCat.ofHom R.subtype
  let t (i : I) : Γ(Y i, ⊤) ⟶ Rcat := CommRingCat.ofHom
    ((f i).appTop.hom.codRestrict R fun x => le_iSup (fun i => (f i).appTop.hom.range) i
      ⟨x, rfl⟩)
  have ht (i : I) : t i ≫ j = (f i).appTop := by ext; rfl
  let p : A ⟶ Spec Rcat := (ΓSpec.adjunction.homEquiv A (Opposite.op Rcat)) j.op
  let g (i : I) : Spec Rcat ⟶ Y i := Spec.map (t i) ≫ (Y i).isoSpec.inv
  have hp : p = A.toSpecΓ ≫ Spec.map j := rfl
  have hpj : Function.Injective p.appTop := by
    rw [ΓSpec_adjunction_homEquiv_eq]
    exact Subtype.val_injective.comp ((Scheme.ΓSpecIso Rcat).commRingCatIsoToRingEquiv.injective)
  have hpg (i : I) : p ≫ g i = f i := by
    dsimp only [g]
    rw [hp, Category.assoc, ← Spec.map_comp_assoc, ht, ← Category.assoc,
      ← Scheme.toSpecΓ_naturality]
    change (f i ≫ (Y i).isoSpec.hom) ≫ (Y i).isoSpec.inv = f i
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine ⟨Spec Rcat, inferInstance,
    Scheme.size_Spec_lt_of_subring B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit R
      (size_spec_globalSections_lt B A hA), p, g, hpj, hpg, ?_, ?_⟩
  · intro x
    obtain ⟨i, y, hy⟩ := (Subring.mem_iSup_of_directed hf).mp
      ((Scheme.ΓSpecIso Rcat).hom x).property
    refine ⟨i, y, hpj ?_⟩
    change (p ≫ g i).appTop y = p.appTop x
    rwa [hpg, ΓSpec_adjunction_homEquiv_eq]
  intro Z a b hab
  apply ext_to_Spec
  apply CommRingCat.hom_ext
  ext x
  obtain ⟨i, y, hy⟩ := (Subring.mem_iSup_of_directed hf).mp x.property
  rw [← show t i y = x from Subtype.ext hy]
  have heq := congrArg (fun k : Z ⟶ Y i => k ≫ (Y i).isoSpec.hom) (hab i)
  have heq' : a ≫ Spec.map (t i) = b ≫ Spec.map (t i) := by
    simpa only [g, Category.assoc, Iso.inv_hom_id, Category.comp_id] using heq
  have heq'' := congrArg (fun k => (Scheme.ΓSpecIso Γ(Y i, ⊤)).inv ≫ k.appTop) heq'
  have hnat := Scheme.ΓSpecIso_inv_naturality (t i)
  change (Scheme.ΓSpecIso Γ(Y i, ⊤)).inv ≫ (Spec.map (t i)).appTop ≫ a.appTop =
    (Scheme.ΓSpecIso Γ(Y i, ⊤)).inv ≫ (Spec.map (t i)).appTop ≫ b.appTop at heq''
  rw [← Category.assoc, ← Category.assoc, ← hnat] at heq''
  exact congrArg (fun k => k y) heq''

private theorem isIso_of_mono_factor_atlas
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (A T : AlgebraicGeometry.BigFppfOver B S hS)
    (a : yoneda.obj A ⟶ X)
    (haS : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf a)
    (haE : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf a)
    (g : yoneda.obj T ⟶ X) [Mono g]
    (p : yoneda.obj A ⟶ yoneda.obj T) (hp : p ≫ g = a) : IsIso g := by
  let J := AlgebraicGeometry.BigFppfOver.topology B S hS
  let Ash : Sheaf J (Type u) :=
    ⟨yoneda.obj A, (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS A).isSheaf⟩
  let Tsh : Sheaf J (Type u) :=
    ⟨yoneda.obj T, (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T).isSheaf⟩
  let Xsh : Sheaf J (Type u) := ⟨X, hX.isSheaf⟩
  let ash : Ash ⟶ Xsh := ⟨a⟩
  let gsh : Tsh ⟶ Xsh := ⟨g⟩
  have ha : Sheaf.IsLocallySurjective ash := by
    apply Space.isLocallySurjective_of_representable_flat_locallyOfFinitePresentation_surjective
      B S hS ash
    refine ⟨haE.1, fun V W q fst snd hs => ?_⟩
    have : Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map snd) :=
      haE.2 q fst snd hs
    exact ⟨inferInstance, inferInstance, haS.2 q fst snd hs⟩
  have : Presheaf.IsLocallySurjective J a := ha
  have : Presheaf.IsLocallySurjective J g :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hp
  have : Mono gsh := Sheaf.Hom.mono_of_presheaf_mono J (Type u) gsh
  have : Presheaf.IsLocallyInjective J g :=
    Presheaf.isLocallyInjective_of_injective J g fun V =>
      (CategoryTheory.mono_iff_injective (g.app V)).mp inferInstance
  have : Sheaf.IsLocallySurjective gsh := inferInstanceAs (Presheaf.IsLocallySurjective J g)
  have : IsIso gsh := (Sheaf.isLocallyBijective_iff_isIso gsh).mp ⟨inferInstance, inferInstance⟩
  exact (inferInstance : IsIso ((sheafToPresheaf J (Type u)).map gsh))

private theorem affine_hom_ext_of_comp_eq
    {A T Y : Scheme.{u}} [IsAffine Y]
    (p : A ⟶ T) (hp : Function.Injective p.appTop)
    {f g : T ⟶ Y} (h : p ≫ f = p ≫ g) : f = g := by
  apply ext_of_isAffine
  ext x
  exact hp (congrArg (fun k : A ⟶ Y => k.appTop x) h)

/-- A compatible family of morphisms from a scheme into a cofiltered diagram of schemes has a
directed family of images on global sections. -/
private theorem directed_range_appTop_of_compatible
    {I : Type v} [Category I] [IsCofilteredOrEmpty I] {A : Scheme.{u}} (Y : I ⥤ Scheme.{u})
    (f : ∀ i, A ⟶ Y.obj i) (hf : ∀ {i j : I} (e : i ⟶ j), f i ≫ Y.map e = f j) :
    Directed (· ≤ ·) (fun i => (f i).appTop.hom.range) := by
  intro i j
  obtain ⟨k, ki, kj, _⟩ := IsCofilteredOrEmpty.cone_objs i j
  have key {l : I} (e : k ⟶ l) : (f l).appTop.hom.range ≤ (f k).appTop.hom.range := by
    rintro x ⟨y, rfl⟩
    refine ⟨(Y.map e).appTop y, ?_⟩
    change (f k ≫ Y.map e).appTop y = _
    rw [hf]
  exact ⟨k, key ki, key kj⟩

private theorem exists_affine_over_factor
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} [Category I] [IsCofiltered I]
    (E : I ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hE : ∀ i, IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (E.obj i)))
    (A : AlgebraicGeometry.BigFppfOver B S hS) (f : ∀ i, A ⟶ E.obj i)
    (hf : ∀ {i j : I} (e : i ⟶ j), f i ≫ E.map e = f j) :
    ∃ (T : AlgebraicGeometry.BigFppfOver B S hS) (p : A ⟶ T) (g : ∀ i, T ⟶ E.obj i),
      IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T) ∧
      (∀ {i j : I} (e : i ⟶ j), g i ≫ E.map e = g j) ∧ (∀ i, p ≫ g i = f i) ∧
      (∀ x : Γ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T, ⊤),
        ∃ i y, ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (g i)).appTop y = x) ∧
      ∀ (Z : AlgebraicGeometry.BigFppfOver B S hS) (a b : Z ⟶ T),
        (∀ i, a ≫ g i = b ≫ g i) → a = b := by
  classical
  have : Nonempty I := IsCofiltered.nonempty
  let F := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  have (i : I) : IsAffine (F.obj (E.obj i)) := hE i
  obtain ⟨T, hTaff, hT, p, g, hpinj, hpg, hgen, hgmono⟩ :=
    exists_affine_factor_of_directed B A.left.property (fun i => F.obj (E.obj i))
      (fun i => F.map (f i)) (directed_range_appTop_of_compatible (E ⋙ F) (fun i => F.map (f i))
        fun {i j} e => by
          change F.map (f i) ≫ F.map (E.map e) = F.map (f j)
          rw [← F.map_comp, hf])
  have hg {i j : I} (e : i ⟶ j) : g i ≫ F.map (E.map e) = g j := by
    apply affine_hom_ext_of_comp_eq p hpinj
    rw [← Category.assoc, hpg, hpg, ← F.map_comp, hf]
  let i₀ : I := Classical.arbitrary I
  let Ts : AlgebraicGeometry.BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk (g i₀ ≫ B.inclusion.map (E.obj i₀).hom) :
      (⟨T, hT⟩ : B.Schemes) ⟶ B.obj hS)
  have hbase (i : I) : g i ≫ B.inclusion.map (E.obj i).hom =
      g i₀ ≫ B.inclusion.map (E.obj i₀).hom := by
    obtain ⟨k, ki, ki₀, _⟩ := IsCofilteredOrEmpty.cone_objs i i₀
    rw [← hg ki, ← hg ki₀, Category.assoc, Category.assoc]
    congr 1
    change B.inclusion.map ((E.map ki).left ≫ (E.obj i).hom) =
      B.inclusion.map ((E.map ki₀).left ≫ (E.obj i₀).hom)
    rw [(E.map ki).w, (E.map ki₀).w]
  let gs (i : I) : Ts ⟶ E.obj i :=
    Over.homMk (ObjectProperty.homMk (g i)) (B.inclusion.map_injective (hbase i))
  have hgs {i j : I} (e : i ⟶ j) : gs i ≫ E.map e = gs j := F.map_injective (hg e)
  let ps : A ⟶ Ts := Over.homMk (ObjectProperty.homMk p) (by
    apply B.inclusion.map_injective
    change p ≫ g i₀ ≫ B.inclusion.map (E.obj i₀).hom = B.inclusion.map A.hom
    rw [← Category.assoc, hpg]
    change B.inclusion.map ((f i₀).left ≫ (E.obj i₀).hom) = _
    rw [(f i₀).w])
  refine ⟨Ts, ps, gs, hTaff, hgs, fun i => F.map_injective (hpg i), hgen, ?_⟩
  intro Z b₁ b₂ h
  apply F.map_injective
  apply hgmono (F.obj Z)
  intro i
  exact congrArg F.map (h i)

private theorem exists_affine_representation_of_isLimit
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} [Category I] [IsCofiltered I]
    (E : I ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hE : ∀ i, IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (E.obj i)))
    (c : Cone (E ⋙ yoneda)) (hc : IsLimit c)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS c.pt) :
    ∃ T : AlgebraicGeometry.BigFppfOver B S hS,
      IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T) ∧
      ∃ e : yoneda.obj T ≅ c.pt,
        ∀ x : Γ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T, ⊤),
          ∃ i y, ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
            (yoneda.preimage (e.hom ≫ c.π.app i))).appTop y = x := by
  let F := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  obtain ⟨A, a, haS, haE⟩ := hX.exists_atlas
  let f (i : I) : A ⟶ E.obj i := yoneda.preimage (a ≫ c.π.app i)
  have hfi (i : I) : yoneda.map (f i) = a ≫ c.π.app i := yoneda.map_preimage _
  obtain ⟨Ts, ps, gs, hTaff, hgs, hpg, hgen, hmono⟩ :=
    exists_affine_over_factor B S hS E hE A f fun e => by
      apply yoneda.map_injective
      rw [Functor.map_comp, hfi, hfi, Category.assoc, ← c.w e]
      rfl
  let d : Cone (E ⋙ yoneda) := ⟨yoneda.obj Ts, {
    app i := yoneda.map (gs i)
    naturality i j e := by
      dsimp
      rw [Category.id_comp, ← yoneda.map_comp, hgs] }⟩
  let q : yoneda.obj Ts ⟶ c.pt := hc.lift d
  have hq (i : I) : q ≫ c.π.app i = yoneda.map (gs i) := hc.fac d i
  have hpq : yoneda.map ps ≫ q = a := by
    refine hc.hom_ext fun i => ?_
    rw [Category.assoc, hq, ← yoneda.map_comp, ← hfi]
    exact congrArg yoneda.map (hpg i)
  have : Mono q := (NatTrans.mono_iff_mono_app q).mpr fun Z =>
    (CategoryTheory.mono_iff_injective _).mpr fun b₁ b₂ hb => hmono _ b₁ b₂ fun i => by
      have h := congrArg (fun x => (c.π.app i).app Z x) hb
      have hqi := congrArg (fun k => k.app Z) (hq i)
      change (yoneda.map (gs i)).app Z b₁ = (yoneda.map (gs i)).app Z b₂
      rw [← hqi]
      exact h
  have : IsIso q := isIso_of_mono_factor_atlas B S hS hX A Ts a haS haE q (yoneda.map ps) hpq
  refine ⟨Ts, hTaff, asIso q, fun x => ?_⟩
  obtain ⟨i, y, hy⟩ := hgen x
  refine ⟨i, y, ?_⟩
  change (F.map (yoneda.preimage (q ≫ c.π.app i))).appTop y = x
  rwa [hq, yoneda.preimage_map]

private theorem exists_affine_represented_diagram
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {J : Type v} [Category J]
    (H : J ⥤ (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hH : ∀ i, ∃ A : AlgebraicGeometry.BigFppfOver B S hS,
      IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj A) ∧
      Nonempty (yoneda.obj A ≅ H.obj i)) :
    ∃ E : J ⥤ AlgebraicGeometry.BigFppfOver B S hS,
      (∀ i, IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (E.obj i))) ∧
      Nonempty (E ⋙ yoneda ≅ H) := by
  classical
  choose A hA e using hH
  let e (i : J) : yoneda.obj (A i) ≅ H.obj i := (e i).some
  let E : J ⥤ AlgebraicGeometry.BigFppfOver B S hS := {
    obj := A
    map {i j} f := yoneda.preimage ((e i).hom ≫ H.map f ≫ (e j).inv)
    map_id i := yoneda.map_injective (by simp)
    map_comp f g := yoneda.map_injective (by simp) }
  refine ⟨E, hA, ⟨NatIso.ofComponents e ?_⟩⟩
  intro i j f
  dsimp [E]
  simp

/-- Let `E` be a cofiltered diagram of algebraic spaces with affine transition morphisms and `c` a
limit cone of `E` whose apex is an algebraic space. Then every projection `c.π.app j` is affine. -/
theorem isAffineHom_cone_projection
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {J : Type v} [Category J] [IsCofiltered J]
    (E : J ⥤ (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hE : ∀ j, AlgebraicGeometry.IsAlgebraicSpace B S hS (E.obj j))
    (hAffine : ∀ {j k : J} (a : j ⟶ k), AlgebraicGeometry.Space.IsAffineHom B S hS (E.map a))
    (c : Cone E) (hc : IsLimit c)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS c.pt) (j : J) :
    AlgebraicGeometry.Space.IsAffineHom B S hS (c.π.app j) := by
  classical
  intro A a
  let K := Over j
  have : IsConnected K := IsCofiltered.isConnected K
  let H := Over.post (X := j) E ⋙ Over.pullback a ⋙ Over.forget (yoneda.obj A.obj)
  let cH : Cone H := (Over.forget (yoneda.obj A.obj)).mapCone
    ((Over.pullback a).mapCone (c.overPost j))
  have hcH : IsLimit cH := isLimitOfPreserves (Over.forget (yoneda.obj A.obj))
    (isLimitOfPreserves (Over.pullback a) (hc.overPost j))
  have hH (k : K) : ∃ T : AlgebraicGeometry.BigFppfOver B S hS,
      IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T) ∧
      Nonempty (yoneda.obj T ≅ H.obj k) := by
    obtain ⟨T, p, q, hs⟩ := hAffine k.hom A a
    exact ⟨T.obj, T.property, ⟨hs.isoPullback⟩⟩
  obtain ⟨F, hF, ⟨eF⟩⟩ := exists_affine_represented_diagram B S hS H hH
  let cF : Cone (F ⋙ yoneda) := (Cone.postcompose eF.inv).obj cH
  have hcF : IsLimit cF := (IsLimit.postcomposeHomEquiv eF.symm cH).symm hcH
  have hP : AlgebraicGeometry.IsAlgebraicSpace B S hS cH.pt :=
    AlgebraicGeometry.isAlgebraicSpace_pullback B S hS (c.π.app j) a hX
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS A.obj) (hE j)
  obtain ⟨T, hT, e, _⟩ := exists_affine_representation_of_isLimit B S hS F hF cF hcF hP
  let e' : yoneda.obj T ≅ pullback (c.π.app j) a := e
  refine ⟨⟨T, hT⟩, e'.hom ≫ pullback.fst _ _,
    yoneda.preimage (e'.hom ≫ pullback.snd _ _), ?_⟩
  rw [yoneda.map_preimage]
  exact (IsPullback.of_hasPullback (c.π.app j) a).of_iso'
    e' (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp)

end PurelyTranscendentalDescent

end AlgebraicGeometry

end
