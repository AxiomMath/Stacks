module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Descent.ClosedImmersionEffectiveDescent
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.StableOpenQuasiFiniteDescent
public import StacksFrontier.AlgebraicGeometry.EventualLimitProperties.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.EventualLimitProperties.Immersion
public import StacksFrontier.AlgebraicGeometry.Limits.RelativeApproximation.ClosedImmersionDescent
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyConnectedFiniteSeparable
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.Smallness
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionQuasiAffineTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendOpens
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.OpenSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ClosedImmersionDescent.AffinePullbackSystem
import all StacksFrontier.AlgebraicGeometry.Spaces.Limits.ClosedImmersionDescent.AffinePullbackSystem

/-!
# Closed immersions and immersions into a directed limit of algebraic spaces

Let `X = lim Xᵢ` be a directed inverse limit of algebraic spaces over a base algebraic space,
with affine transition morphisms and quasi-compact stages.  A closed immersion `Y ⟶ X` whose
source is locally of finite type over the base is already a closed immersion into `Xᵢ` for all
sufficiently large `i`, and the same holds for immersions at quasi-separated stages.

## Main results

* `AlgebraicGeometry.Space.eventually_isClosedImmersion_comp_limitπ`: the eventual closed
  immersion at the stages of the inverse system.
* `AlgebraicGeometry.Space.eventually_isClosedImmersion_comp_limitπ'`: the same statement with
  its descent hypothesis discharged, which is **Stacks 0828, part (1)**.
* `AlgebraicGeometry.Space.eventually_isImmersion_comp_limitπ_of_small`: the eventual immersion
  for an index set which is small for the site, with no hypothesis on the stages.
* `AlgebraicGeometry.Space.eventually_isImmersion_comp_limitπ`: the eventual immersion at the
  quasi-separated stages of the inverse system, which is **Stacks 0828, part (2)**.

## Implementation notes

The proof follows the Stacks project.  Quasi-compactness of one stage `Xᵢ₀` provides an affine
object `U₀` of the site with a surjective étale morphism `U₀ ⟶ Xᵢ₀`, and the inverse system of
affine base changes along `U₀` reduces part (1) to the scheme-level statement
`AlgebraicGeometry.EventualLimit.eventually_isClosedImmersion_comp_π_app`.

Part (2) runs the same argument with immersions in place of closed immersions, after replacing
the stages by the preimages of a quasi-compact open subspace of one stage containing the image
of `Y`.  The base change of `Y` to the affine atlas is no longer affine, but it is quasi-compact
because that stage is quasi-separated; the scheme-level input is
`AlgebraicGeometry.EventualLimit.eventually_isImmersion_comp_π_app`, and the descent to the
stages uses effective descent of immersions along surjective étale morphisms.  No bound on the
index set is needed: the limit of the system is never required to be an algebraic space.

The private auxiliaries of the inverse system of affine base changes are used here through
`import all` of the file defining them.

## References

* [Stacks Project, Tag 0828](https://stacks.math.columbia.edu/tag/0828)
* [Stacks Project, Tag 081B](https://stacks.math.columbia.edu/tag/081B)
* [Stacks Project, Tag 03M4](https://stacks.math.columbia.edu/tag/03M4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Filter Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] affinePullbackTail_nonempty affinePullbackTail_isDirected

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for the limits of presheaves on the big fppf site times out at the default limit
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
private instance hasPullbacks_presheaf_eventualImmersion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

private instance (priority := high) hasPullback_presheaf_eventualImmersion
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for the limits of presheaves on the big fppf site times out at the default limit
private instance hasFiniteProducts_presheaf_eventualImmersion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasFiniteProducts ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- An immersion of algebraic spaces is recognised on one surjective étale chart of its target:
if the base change of `g` along a surjective étale chart `p` is the morphism of the site `k`, and
the underlying morphism of schemes of `k` is an immersion, then `g` is an immersion. This is the
fourth criterion of Stacks 03M4 at the immersions, with effective descent of immersions along
surjective étale morphisms discharged. -/
private lemma isImmersion_of_isPullback_chart
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY' : IsAlgebraicSpace B S hS Y') (hX' : IsAlgebraicSpace B S hS X') (g : Y' ⟶ X')
    {W' U' : BigFppfOver B S hS} (p : yoneda.obj U' ⟶ X')
    (hpS : (MorphismProperty.inverseImage (@Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (hpE : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (k : W' ⟶ U') (m : yoneda.obj W' ⟶ Y') (sq : IsPullback (yoneda.map k) m p g)
    (hk : _root_.AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map k)) :
    Space.IsImmersion B S hS g := by
  let T := BigFppfOver.toScheme B S hS
  let C := (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsImmersion.{u}) T).presheaf
  have hKC : C (yoneda.map k) := by
    let : PreservesLimitsOfShape WalkingCospan T := by apply comp_preservesLimitsOfShape
    let : (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsImmersion.{u}) T).IsStableUnderBaseChange := {
      of_isPullback := fun h hf =>
        (inferInstance : MorphismProperty.IsStableUnderBaseChange
          (@_root_.AlgebraicGeometry.IsImmersion.{u})).of_isPullback (h.map T) hf }
    apply MorphismProperty.relative_map
    exact hk
  apply ((presheaf_tfae B S hS _ inferInstance
    (isEffectiveDescentAlongSurjectiveEtale_isImmersion_of_isQuasiAffineHom
      (isEffectiveDescentAlongSurjectiveEtale_isQuasiAffineHom B S hS)) hY' hX' g).out 4 1).mp
  refine ⟨U', p, hpS, hpE, ?_⟩
  have heq : sq.flip.isoPullback.inv ≫ yoneda.map k = pullback.snd g p :=
    IsPullback.isoPullback_inv_snd _
  change C (pullback.snd g p)
  rw [← heq]
  exact MorphismProperty.RespectsIso.precomp C sq.flip.isoPullback.inv (yoneda.map k) hKC

/-- The preimage of a quasi-compact open subspace along an affine morphism of algebraic spaces
is quasi-compact. -/
private lemma isQuasiCompactSpace_preimage_of_isAffineHom
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : X ⟶ Y) (V : Subfunctor Y)
    (hV : IsOpenSubspace B S hS V) (hVp : IsOpenSubspace B S hS (V.preimage p))
    (hVqc : IsQuasiCompactSpace B S hS V.toFunctor) (hp : IsAffineHom B S hS p) :
    IsQuasiCompactSpace B S hS (V.preimage p).toFunctor := by
  have haff : IsAffineHom B S hS (V.fromPreimage p) :=
    isAffineHom_of_isPullback (Subfunctor.isPullback_fromPreimage V p).flip hp
  have hq : IsQuasiCompact B S hS (V.fromPreimage p) := by
    refine isQuasiCompact_of_isQuasiCompactSpace_pullback_affine B S hS hVp.1 hV.1 _
      fun T hT k => ?_
    obtain ⟨W, p, q, hpb⟩ := haff ⟨T, hT⟩ k
    exact isQuasiCompactSpace_of_iso B S hS
      (hpb.flip.isoIsPullback _ _ (IsPullback.of_hasPullback k _))
      (isQuasiCompactSpace_yoneda_of_isAffine B S hS _ W.property)
  exact isQuasiCompactSpace_of_iso B S hS
    (IsPullback.of_id_snd (f := V.fromPreimage p)).isoPullback.symm
    (hq V.toFunctor hV.1 hVqc (𝟙 V.toFunctor))

/-- The tail of a directed preorder above a point is directed. -/
private lemma isDirected_limitTail {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (i₀ : I) :
    IsDirected (LimitTail I i₀) (· ≤ ·) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨k, hxk, hyk⟩ := IsDirected.directed (r := (· ≤ ·)) x.1 y.1
  exact ⟨⟨k, x.2.trans hxk⟩, hxk, hyk⟩

/-- The chart-level data of `eventually_isImmersion_of_affine_atlas`: the base change of an
immersion into the limit along an affine étale atlas of a stage is represented by an object `V`
of the site immersed into the limit of the affine base changes of the stages, computed in the
category of schemes. -/
private lemma exists_chart_representation_of_isImmersion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj (op i)))
    (hAffine : ∀ ⦃i j : I⦄ (h : i ≤ j),
      Space.IsAffineHom B S hS (D.map (homOfLE h).op))
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (f : Y ⟶ limit D)
    (hImmersion : Space.IsImmersion B S hS f)
    (i₀ : I) (U₀ : BigFppfOver B S hS)
    (hU₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj U₀))
    (p₀ : yoneda.obj U₀ ⟶ D.obj (op i₀)) :
    ∃ (V : BigFppfOver B S hS)
      (eV : yoneda.obj V ≅ pullback (f ≫ limit.π D (op i₀)) p₀)
      (k : ∀ j : (AffinePullbackTail I i₀)ᵒᵖ,
        V ⟶ (affinePullbackSiteDiagram B S hS D hAffine i₀ U₀ hU₀ p₀).obj j)
      (sc : Cone (affinePullbackSiteDiagram B S hS D hAffine i₀ U₀ hU₀ p₀ ⋙
        BigFppfOver.toScheme B S hS))
      (_ : IsLimit sc) (vl : (BigFppfOver.toScheme B S hS).obj V ⟶ sc.pt),
      _root_.AlgebraicGeometry.IsImmersion vl ∧
      (∀ j, (BigFppfOver.toScheme B S hS).map (k j) = vl ≫ sc.π.app j) ∧
      (∀ j, yoneda.map (k j) ≫
          (affinePullbackStage B S hS D hAffine i₀ U₀ hU₀ p₀ j.unop).p =
        eV.hom ≫ pullback.fst _ _ ≫ f ≫ limit.π D (op j.unop.1)) ∧
      (∀ j, yoneda.map (k j) ≫
          yoneda.map (affinePullbackStage B S hS D hAffine i₀ U₀ hU₀ p₀ j.unop).q =
        eV.hom ≫ pullback.snd _ _) := by
  classical
  let F := Over.post (X := B.obj hS) B.inclusion
  let T := BigFppfOver.toScheme B S hS
  let R := restrictedPoints F
  let E := (MorphismProperty.inverseImage (@Etale.{u}) T).presheaf
  let C := (MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.IsImmersion.{u}) T).presheaf
  let J := AffinePullbackTail I i₀
  let : IsConnected Jᵒᵖ := IsCofiltered.isConnected _
  let A := affinePullbackSiteDiagram B S hS D hAffine i₀ U₀ hU₀ p₀
  let P := affinePullbackStage B S hS D hAffine i₀ U₀ hU₀ p₀
  let eA := affinePullbackChosenPresheafDiagramIsoCanonical
    B S hS D hAffine i₀ U₀ hU₀ p₀
  let cc := affinePullbackCanonicalLimitCone B S hS D i₀ U₀ p₀
  let pc : Cone (A ⋙ yoneda) :=
    { pt := pullback (limit.π D (op i₀)) p₀
      π := ((Cone.postcompose eA.inv).obj cc).π }
  have hpc : IsLimit pc := (IsLimit.postcomposeHomEquiv eA.symm cc).symm
    (affinePullbackCanonicalLimitCone_isLimit B S hS D i₀ U₀ p₀)
  have hAs (j) : IsAffine (T.obj (A.obj j)) :=
    affinePullbackSchemeDiagram_obj_isAffine B S hS D hAffine i₀ U₀ hU₀ p₀ j
  obtain ⟨lc, ⟨hlc⟩, hla, e, he⟩ := exists_over_limit_of_affine B S hS A
    (affinePullbackSchemeLimitCone B S hS D hAffine i₀ U₀ hU₀ p₀)
    (affinePullbackSchemeLimitCone_isLimit B S hS D hAffine i₀ U₀ hU₀ p₀)
    hAs pc hpc
  have : IsAffine lc.pt.left := hla
  let shA : Jᵒᵖ ⥤ Sheaf (BigFppfOver.topology B S hS) (Type u) := {
    obj j := ⟨yoneda.obj (A.obj j),
      (isAlgebraicSpace_yoneda B S hS (A.obj j)).isSheaf⟩
    map g := ⟨yoneda.map (A.map g)⟩
    map_id j := Sheaf.hom_ext
      (show yoneda.map (A.map (𝟙 j)) = 𝟙 _ by rw [A.map_id, yoneda.map_id])
    map_comp f g := Sheaf.hom_ext
      (show yoneda.map (A.map (f ≫ g)) = yoneda.map (A.map f) ≫ yoneda.map (A.map g) by
        rw [A.map_comp, yoneda.map_comp]) }
  have hps : Presheaf.IsSheaf _ pc.pt := Sheaf.isSheaf_of_isLimit shA pc hpc
  have hls : Presheaf.IsSheaf _ (R.obj lc.pt) :=
    (Presheaf.isSheaf_of_iso_iff e).mpr hps
  let G := pullback (f ≫ limit.π D (op i₀)) p₀
  let a : G ⟶ Y := pullback.fst _ _
  let b : G ⟶ yoneda.obj U₀ := pullback.snd _ _
  have hG := _root_.AlgebraicGeometry.isAlgebraicSpace_pullback B S hS
    (f ≫ limit.π D (op i₀)) p₀ hY
    (isAlgebraicSpace_yoneda B S hS U₀) (hD i₀)
  have hcond : (a ≫ f) ≫ limit.π D (op i₀) = b ≫ p₀ := by
    simpa only [Category.assoc, a, b] using
      pullback.condition (f := f ≫ limit.π D (op i₀)) (g := p₀)
  let d : G ⟶ pullback (limit.π D (op i₀)) p₀ := pullback.lift (a ≫ f) b hcond
  have hdfst : d ≫ pullback.fst (limit.π D (op i₀)) p₀ = a ≫ f := pullback.lift_fst _ _ _
  have hdsnd : d ≫ pullback.snd (limit.π D (op i₀)) p₀ = b := pullback.lift_snd _ _ _
  have hd : IsPullback d a (pullback.fst (limit.π D (op i₀)) p₀) f := by
    have ho : IsPullback (d ≫ pullback.snd (limit.π D (op i₀)) p₀) a
        p₀ (f ≫ limit.π D (op i₀)) := by
      rw [hdsnd]
      exact (IsPullback.of_hasPullback (f ≫ limit.π D (op i₀)) p₀).flip
    exact ho.of_right hdfst (IsPullback.of_hasPullback _ _).flip
  have hdC : C d :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hd.flip hImmersion
  have hde : C (d ≫ e.inv) := MorphismProperty.RespectsIso.postcomp C e.inv d hdC
  obtain ⟨V, eV, v, hv, hev⟩ := exists_representation_of_presheaf B S hS
    (@_root_.AlgebraicGeometry.IsImmersion.{u})
    (fun q m hq hm => by have := hq; have := hm; exact inferInstanceAs
      (_root_.AlgebraicGeometry.IsImmersion (q ≫ m)))
    lc.pt hG hls (d ≫ e.inv) hde
  have hvci : _root_.AlgebraicGeometry.IsImmersion v.left := hv
  let k (j : Jᵒᵖ) : V ⟶ A.obj j := F.preimage (v ≫ lc.π.app j)
  have hk (j : Jᵒᵖ) : yoneda.map (k j) = eV.hom ≫ d ≫ pc.π.app j := by
    have he' := he j
    have hv' := congrArg
      (· ≫ R.map (lc.π.app j) ≫ (restrictedPointsIso F (A.obj j)).hom) hev
    dsimp only [k]
    simp only [Category.assoc] at hv'
    rw [← he', Iso.inv_hom_id_assoc] at hv'
    rw [he'] at hv'
    calc
      yoneda.map (F.preimage (v ≫ lc.π.app j)) =
          (restrictedPointsIso F V).inv ≫ R.map (F.map (F.preimage
            (v ≫ lc.π.app j))) ≫ (restrictedPointsIso F (A.obj j)).hom := by
        rw [restrictedPointsIso_naturality]
        simp
      _ = (restrictedPointsIso F V).inv ≫ R.map v ≫
          R.map (lc.π.app j) ≫ (restrictedPointsIso F (A.obj j)).hom := by
        rw [F.map_preimage, R.map_comp]
        simp only [Category.assoc]
      _ = eV.hom ≫ d ≫ pc.π.app j := hv'.symm
  have hpcP (j : Jᵒᵖ) : pc.π.app j ≫ (P j.unop).p =
      pullback.fst (limit.π D (op i₀)) p₀ ≫ limit.π D (op j.unop.1) := by
    have h2 : (P j.unop).isPullback.isoPullback.inv ≫ (P j.unop).p =
        pullback.fst (D.map (homOfLE j.unop.2).op) p₀ := IsPullback.isoPullback_inv_fst _
    exact (congrArg (fun x => cc.π.app j ≫ x) h2).trans (pullback.lift_fst _ _ _)
  have hpcQ (j : Jᵒᵖ) : pc.π.app j ≫ yoneda.map (P j.unop).q =
      pullback.snd (limit.π D (op i₀)) p₀ := by
    have h2 : (P j.unop).isPullback.isoPullback.inv ≫ yoneda.map (P j.unop).q =
        pullback.snd (D.map (homOfLE j.unop.2).op) p₀ := IsPullback.isoPullback_inv_snd _
    exact (congrArg (fun x => cc.π.app j ≫ x) h2).trans (pullback.lift_snd _ _ _)
  have hkP (j : Jᵒᵖ) : yoneda.map (k j) ≫ (P j.unop).p =
      eV.hom ≫ a ≫ f ≫ limit.π D (op j.unop.1) :=
    calc yoneda.map (k j) ≫ (P j.unop).p
        = (eV.hom ≫ d ≫ pc.π.app j) ≫ (P j.unop).p :=
          congrArg (fun x => x ≫ (P j.unop).p) (hk j)
      _ = eV.hom ≫ (d ≫ pc.π.app j) ≫ (P j.unop).p := Category.assoc _ _ _
      _ = eV.hom ≫ d ≫ pc.π.app j ≫ (P j.unop).p :=
          congrArg (fun x => eV.hom ≫ x) (Category.assoc _ _ _)
      _ = eV.hom ≫ d ≫ pullback.fst (limit.π D (op i₀)) p₀ ≫ limit.π D (op j.unop.1) :=
          congrArg (fun x => eV.hom ≫ d ≫ x) (hpcP j)
      _ = eV.hom ≫ (d ≫ pullback.fst (limit.π D (op i₀)) p₀) ≫ limit.π D (op j.unop.1) :=
          congrArg (fun x => eV.hom ≫ x) (Category.assoc _ _ _).symm
      _ = eV.hom ≫ (a ≫ f) ≫ limit.π D (op j.unop.1) :=
          congrArg (fun x => eV.hom ≫ x ≫ limit.π D (op j.unop.1)) hdfst
      _ = eV.hom ≫ a ≫ f ≫ limit.π D (op j.unop.1) :=
          congrArg (fun x => eV.hom ≫ x) (Category.assoc _ _ _)
  have hkQ (j : Jᵒᵖ) : yoneda.map (k j) ≫ yoneda.map (P j.unop).q = eV.hom ≫ b :=
    calc yoneda.map (k j) ≫ yoneda.map (P j.unop).q
        = (eV.hom ≫ d ≫ pc.π.app j) ≫ yoneda.map (P j.unop).q :=
          congrArg (fun x => x ≫ yoneda.map (P j.unop).q) (hk j)
      _ = eV.hom ≫ (d ≫ pc.π.app j) ≫ yoneda.map (P j.unop).q := Category.assoc _ _ _
      _ = eV.hom ≫ d ≫ pc.π.app j ≫ yoneda.map (P j.unop).q :=
          congrArg (fun x => eV.hom ≫ x) (Category.assoc _ _ _)
      _ = eV.hom ≫ d ≫ pullback.snd (limit.π D (op i₀)) p₀ :=
          congrArg (fun x => eV.hom ≫ d ≫ x) (hpcQ j)
      _ = eV.hom ≫ b := congrArg (fun x => eV.hom ≫ x) hdsnd
  have hks (j : Jᵒᵖ) : T.map (k j) = v.left ≫ ((Over.forget S).mapCone lc).π.app j :=
    congrArg (fun z => z.left) (F.map_preimage (v ≫ lc.π.app j))
  exact ⟨V, eV, k, (Over.forget S).mapCone lc, isLimitOfPreserves (Over.forget S) hlc, v.left,
    hvci, hks, hkP, hkQ⟩

/-- The eventual immersion over an affine étale atlas of one stage: the counterpart of
`eventually_isClosedImmersion_of_affine_atlas` for an immersion whose base change to the atlas
is quasi-compact. The scheme-level input is Stacks 081B, part (2), in the form
`AlgebraicGeometry.EventualLimit.eventually_isImmersion_comp_π_app`, and the descent to the
stages uses effective descent of immersions along surjective étale morphisms. -/
private lemma eventually_isImmersion_of_affine_atlas
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj (op i)))
    (hAffine : ∀ ⦃i j : I⦄ (h : i ≤ j),
      Space.IsAffineHom B S hS (D.map (homOfLE h).op))
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (f : Y ⟶ limit D)
    (hImmersion : Space.IsImmersion B S hS f)
    (i₀ : I) (U₀ : BigFppfOver B S hS)
    (hU₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj U₀))
    (p₀ : yoneda.obj U₀ ⟶ D.obj (op i₀))
    (hpS : (MorphismProperty.inverseImage (@Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p₀)
    (hpE : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p₀)
    (hFinite : Space.IsLocallyOfFiniteType B S hS (f ≫ limit.π D (op i₀)))
    (hGqc : IsQuasiCompactSpace B S hS (pullback (f ≫ limit.π D (op i₀)) p₀)) :
    ∀ᶠ i in atTop, Space.IsImmersion B S hS (f ≫ limit.π D (op i)) := by
  classical
  let T := BigFppfOver.toScheme B S hS
  let E := (MorphismProperty.inverseImage (@Etale.{u}) T).presheaf
  let J := AffinePullbackTail I i₀
  let A := affinePullbackSiteDiagram B S hS D hAffine i₀ U₀ hU₀ p₀
  let P := affinePullbackStage B S hS D hAffine i₀ U₀ hU₀ p₀
  have hAs (j) : IsAffine (T.obj (A.obj j)) :=
    affinePullbackSchemeDiagram_obj_isAffine B S hS D hAffine i₀ U₀ hU₀ p₀ j
  obtain ⟨V, eV, k, sc, hsc, vl, hvcl, hks, hkP, hkQ⟩ :=
    exists_chart_representation_of_isImmersion B S hS D hD hAffine hY f hImmersion i₀ U₀ hU₀ p₀
  let a : pullback (f ≫ limit.π D (op i₀)) p₀ ⟶ Y := pullback.fst _ _
  let b : pullback (f ≫ limit.π D (op i₀)) p₀ ⟶ yoneda.obj U₀ := pullback.snd _ _
  have : CompactSpace (T.obj V) :=
    compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS
      (isQuasiCompactSpace_of_iso B S hS eV.symm hGqc)
  let j₀ : J := ⟨i₀, le_rfl⟩
  have haE : E a := (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
    (IsPullback.of_hasPullback (f ≫ limit.π D (op i₀)) p₀).flip hpE
  have hVE : E (eV.hom ≫ a) := MorphismProperty.RespectsIso.precomp E eV.hom a haE
  have hPE (j : Jᵒᵖ) : E (P j.unop).p :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (P j.unop).isPullback.flip hpE
  have hft : LocallyOfFiniteType (T.map (k (op j₀))) :=
    hFinite V (A.obj (op j₀)) (eV.hom ≫ a) (P j₀).p (k (op j₀))
      hVE (hPE (op j₀)) (by simpa only [Category.assoc] using hkP (op j₀))
  let τ : A ⋙ T ⟶ (Functor.const Jᵒᵖ).obj (T.obj (A.obj (op j₀))) := {
    app j := (A ⋙ T).map (homOfLE (show j₀ ≤ j.unop from j.unop.2)).op
    naturality := by
      intro j l g
      dsimp
      rw [Category.comp_id, ← Functor.map_comp, ← Functor.map_comp]
      congr 2 }
  have hτ : sc.π ≫ τ = (Functor.const Jᵒᵖ).map (sc.π.app (op j₀)) := by
    ext j
    exact sc.w (homOfLE (show j₀ ≤ j.unop from j.unop.2)).op
  let s₀ : sc.pt ⟶ T.obj (A.obj (op j₀)) := sc.π.app (op j₀)
  have hlft : LocallyOfFiniteType (vl ≫ s₀) := by
    have h : LocallyOfFiniteType (T.map (k (op j₀))) := hft
    rw [hks (op j₀)] at h
    exact h
  have := hlft
  let (j : Jᵒᵖ) : IsAffine ((A ⋙ T).obj j) := hAs j
  have (j : J) : CompactSpace ((A ⋙ T).obj (op j)) := by
    rw [compactSpace_iff_quasiCompact]
    infer_instance
  have {j l : J} (h : j ≤ l) :
      _root_.AlgebraicGeometry.IsAffineHom ((A ⋙ T).map (homOfLE h).op) :=
    isAffineHom_of_isAffine _
  have hEventually :=
    _root_.AlgebraicGeometry.EventualLimit.eventually_isImmersion_comp_π_app
      (A ⋙ T) τ sc hsc s₀ vl hτ
  obtain ⟨j, hj⟩ := eventually_atTop.1 hEventually
  refine eventually_atTop.2 ⟨j.1, fun i hi => ?_⟩
  let l : J := ⟨i, j.2.trans hi⟩
  have : _root_.AlgebraicGeometry.IsImmersion (T.map (k (op l))) := by
    rw [hks]
    exact hj l hi
  have hOuter : IsPullback (eV.hom ≫ b) (eV.hom ≫ a) p₀
      (f ≫ limit.π D (op i₀)) :=
    (IsPullback.of_iso_pullback ⟨by
      rw [Category.assoc, Category.assoc]
      exact congrArg (eV.hom ≫ ·) pullback.condition⟩ eV rfl rfl).flip
  have hw : (f ≫ limit.π D (op i)) ≫ D.map (homOfLE l.2).op = f ≫ limit.π D (op i₀) := by
    rw [Category.assoc, limit.w]
  have hOuter' : IsPullback (yoneda.map (k (op l)) ≫ yoneda.map (P l).q)
      (eV.hom ≫ a) p₀
      ((f ≫ limit.π D (op i)) ≫ D.map (homOfLE l.2).op) := by
    rw [hkQ, hw]
    exact hOuter
  have hSquare := hOuter'.of_right (hkP (op l)) (P l).isPullback.flip
  have hpS' := (MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.inverseImage (@Surjective.{u}) T)).of_isPullback
        (P l).isPullback.flip hpS
  exact isImmersion_of_isPullback_chart B S hS hY (hD i) (f ≫ limit.π D (op i)) (P l).p hpS'
    (hPE (op l)) (k (op l)) (eV.hom ≫ a) hSquare this

/-- **Stacks 0828, part (1)**, conditional on effective descent for closed immersions of schemes
along a surjective étale morphism of the site.

Let `X = lim Xᵢ` be a directed limit of algebraic spaces over an algebraic space `Bspace`, with
affine transition morphisms and quasi-compact stages, and let `f : Y ⟶ X` be a closed immersion
with `Y` locally of finite type over `Bspace`.  Then `Y ⟶ Xᵢ` is a closed immersion for all
sufficiently large `i`.

The hypothesis `hdesc` is Stacks 03I2 for the class of closed immersions of schemes.  It is
needed only to invoke `AlgebraicGeometry.Space.presheaf_tfae` at the closed immersions, which
recognises a
closed immersion of algebraic spaces from its base change along a single surjective étale chart
of the target; that is the step which transports the scheme-level statement
`AlgebraicGeometry.EventualLimit.eventually_isClosedImmersion_comp_π_app` back to the spaces.
The hypothesis is discharged in
`AlgebraicGeometry.Space.eventually_isClosedImmersion_comp_limitπ'`, which carries the tag. -/
theorem eventually_isClosedImmersion_comp_limitπ
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}))
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (Bspace : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hBspace : IsAlgebraicSpace B S hS Bspace)
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj (op i)))
    (t : D ⟶ (Functor.const Iᵒᵖ).obj Bspace)
    (c : Cone D) (hc : IsLimit c) (s : c.pt ⟶ Bspace)
    (hcomm : c.π ≫ t = (Functor.const Iᵒᵖ).map s)
    (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : Y ⟶ c.pt)
    (hCompact : ∀ i, IsQuasiCompactSpace B S hS (D.obj (op i)))
    (hAffine : ∀ ⦃i j : I⦄ (h : i ≤ j),
      Space.IsAffineHom B S hS (D.map (homOfLE h).op))
    (hFiniteType : Space.IsLocallyOfFiniteType B S hS (f ≫ s))
    (hClosed : Space.IsClosedImmersion B S hS f) :
    ∀ᶠ i in atTop,
      Space.IsClosedImmersion B S hS (f ≫ c.π.app (op i)) := by
  classical
  let i₀ : I := Classical.choice ‹Nonempty I›
  obtain ⟨U₀, p₀, hU₀aff, hp₀surj, hp₀etale⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover
      B S hS (D.obj (op i₀)) (hD i₀)).mp (hCompact i₀)
  have hStageFiniteType (i : I) : Space.IsLocallyOfFiniteType B S hS
      (f ≫ c.π.app (op i)) := by
    apply isLocallyOfFiniteType_of_comp B S hS hY (hD i) hBspace
      (f ≫ c.π.app (op i)) (t.app (op i))
    have hi := congrArg (fun α => α.app (op i)) hcomm
    change c.π.app (op i) ≫ t.app (op i) = s at hi
    simpa only [Category.assoc, hi] using hFiniteType
  have hpE := presheaf_etale_of_isEtale B S hS hp₀etale
  let C := (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
    (BigFppfOver.toScheme B S hS)).presheaf
  let e := hc.conePointUniqueUpToIso (limit.isLimit D)
  have he (i) : e.hom ≫ limit.π D i = c.π.app i :=
    hc.conePointUniqueUpToIso_hom_comp (limit.isLimit D) i
  have hClosed' : C (f ≫ e.hom) :=
    MorphismProperty.RespectsIso.postcomp C e.hom f hClosed
  have hFinite' : Space.IsLocallyOfFiniteType B S hS
      ((f ≫ e.hom) ≫ limit.π D (op i₀)) := by
    simpa only [Category.assoc, he] using hStageFiniteType i₀
  have h := eventually_isClosedImmersion_of_affine_atlas B S hS hdesc D hD hAffine
    hY (f ≫ e.hom) hClosed' i₀ U₀ hU₀aff p₀ hp₀surj hpE hFinite'
  simpa only [Category.assoc, he] using h

/-- **Stacks 0828, part (1).** Let `X = lim Xᵢ` be a directed limit of algebraic spaces over an
algebraic space `Bspace`, with affine transition morphisms and quasi-compact stages, and let
`f : Y ⟶ X` be a closed immersion with `Y` locally of finite type over `Bspace`.  Then `Y ⟶ Xᵢ`
is a closed immersion for all sufficiently large `i`. -/
@[stacks 0828 "part (1): closed immersions"]
theorem eventually_isClosedImmersion_comp_limitπ'
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (contains : B.Contains S)
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (Bspace : (BigFppfOver B S contains)ᵒᵖ ⥤ Type u)
    (algebraicBase : IsAlgebraicSpace B S contains Bspace)
    (D : Iᵒᵖ ⥤ (BigFppfOver B S contains)ᵒᵖ ⥤ Type u)
    (algebraicStage : ∀ i, IsAlgebraicSpace B S contains (D.obj (op i)))
    (t : D ⟶ (Functor.const Iᵒᵖ).obj Bspace)
    (c : Cone D) (isLimit : IsLimit c) (s : c.pt ⟶ Bspace)
    (commutes : c.π ≫ t = (Functor.const Iᵒᵖ).map s)
    (Y : (BigFppfOver B S contains)ᵒᵖ ⥤ Type u)
    (algebraic : IsAlgebraicSpace B S contains Y)
    (f : Y ⟶ c.pt)
    (quasiCompactStage : ∀ i, IsQuasiCompactSpace B S contains (D.obj (op i)))
    (affine : ∀ ⦃i j : I⦄ (h : i ≤ j), Space.IsAffineHom B S contains (D.map (homOfLE h).op))
    (finiteType : Space.IsLocallyOfFiniteType B S contains (f ≫ s))
    (closed : Space.IsClosedImmersion B S contains f) :
    ∀ᶠ i in atTop, Space.IsClosedImmersion B S contains (f ≫ c.π.app (op i)) :=
  eventually_isClosedImmersion_comp_limitπ B S contains
    (isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion B S contains) Bspace algebraicBase D
    algebraicStage t c isLimit s commutes Y algebraic f quasiCompactStage affine finiteType closed

/-! ### Immersions into a directed limit -/

section Immersions

open Cardinal

/-- The eventual immersion into the stages of a directed limit of algebraic spaces with affine
transition morphisms, for an immersion `f : Y ⟶ X` whose source is quasi-compact and locally of
finite type over `Bspace`, when the index set is small for the site and with no hypothesis on
the stages.

Under the bound `small` the limit is an algebraic space by Stacks 07SF, and part (1) is applied
to the inverse system of quasi-compact open subspaces of the stages supplied by
`AlgebraicGeometry.Space.exists_isOpenSubspace_isQuasiCompactSpace_preimage_eq` (Stacks 0827).
Stacks 0828, part (2), with no bound on the index set and quasi-separated stages, is
`AlgebraicGeometry.Space.eventually_isImmersion_comp_limitπ`. -/
theorem eventually_isImmersion_comp_limitπ_of_small
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (contains : B.Contains S)
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (small : #I < B.cutoff.ord.cof)
    (Bspace : (BigFppfOver B S contains)ᵒᵖ ⥤ Type u)
    (algebraicBase : IsAlgebraicSpace B S contains Bspace)
    (D : Iᵒᵖ ⥤ (BigFppfOver B S contains)ᵒᵖ ⥤ Type u)
    (algebraicStage : ∀ i, IsAlgebraicSpace B S contains (D.obj (op i)))
    (t : D ⟶ (Functor.const Iᵒᵖ).obj Bspace)
    (c : Cone D) (isLimit : IsLimit c) (s : c.pt ⟶ Bspace)
    (commutes : c.π ≫ t = (Functor.const Iᵒᵖ).map s)
    (Y : (BigFppfOver B S contains)ᵒᵖ ⥤ Type u)
    (algebraic : IsAlgebraicSpace B S contains Y)
    (quasiCompact : IsQuasiCompactSpace B S contains Y)
    (f : Y ⟶ c.pt)
    (affine : ∀ ⦃i j : I⦄ (h : i ≤ j), IsAffineHom B S contains (D.map (homOfLE h).op))
    (finiteType : IsLocallyOfFiniteType B S contains (f ≫ s))
    (immersion : IsImmersion B S contains f) :
    ∀ᶠ i in atTop, IsImmersion B S contains (f ≫ c.π.app (op i)) := by
  classical
  -- The size hypotheses of Stacks 07SF for the index category `Iᵒᵖ`.
  have hSizeOp : #(Iᵒᵖ) < B.cutoff.ord.cof := by
    rw [← Cardinal.mk_congr (Opposite.equivToOpposite (α := I))]; exact small
  have hHomSizeOp : ∀ a b : Iᵒᵖ, #(a ⟶ b) < B.cutoff.ord.cof := by
    intro a b
    have h1 : #(a ⟶ b) ≤ 1 := by rw [Cardinal.le_one_iff_subsingleton]; infer_instance
    exact h1.trans_lt (Cardinal.one_lt_aleph0.trans B.aleph0_lt_cutoff_cof)
  have hDop : ∀ a : Iᵒᵖ, IsAlgebraicSpace B S contains (D.obj a) := fun a => algebraicStage a.unop
  have hAffineOp : ∀ {a b : Iᵒᵖ} (g : a ⟶ b), IsAffineHom B S contains (D.map g) := by
    intro a b g
    have h : b.unop ≤ a.unop := leOfHom g.unop
    have hg : g = (homOfLE h).op := Subsingleton.elim _ _
    rw [hg]
    exact affine h
  have hlimAlg : IsAlgebraicSpace B S contains (limit D) :=
    isAlgebraicSpace_limit B S contains D hSizeOp hHomSizeOp hDop hAffineOp
  -- Transport `f` to the chosen limit.
  let e := isLimit.conePointUniqueUpToIso (limit.isLimit D)
  have he (a) : e.hom ≫ limit.π D a = c.π.app a :=
    isLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit D) a
  have _hbc : MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S contains))) :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hf' : IsImmersion B S contains (f ≫ e.hom) :=
    MorphismProperty.RespectsIso.postcomp _ e.hom f immersion
  -- Shrink to a closed immersion into a quasi-compact open subspace of the limit.
  obtain ⟨U, g, hUopen, hUqc, hgclosed, hgι⟩ :=
    exists_isQuasiCompactSpace_isClosedImmersion_of_isImmersion B S contains hlimAlg algebraic
      quasiCompact (f ≫ e.hom) hf'
  -- Descend that open subspace to a stage, by Stacks 0827.
  obtain ⟨a, V, hVopen, hVqc, hVpre⟩ :=
    exists_isOpenSubspace_isQuasiCompactSpace_preimage_eq B S contains D hSizeOp hHomSizeOp hDop
      hAffineOp U hUopen hUqc
  subst hVpre
  obtain ⟨i₀⟩ := a
  -- The tail of the index preorder above `i₀`, with its inclusion into `Iᵒᵖ`.
  have : Nonempty (LimitTail I i₀) := ⟨⟨i₀, le_rfl⟩⟩
  have := isDirected_limitTail i₀
  let G : (LimitTail I i₀)ᵒᵖ ⥤ Iᵒᵖ :=
    (limitTailOverEquiv i₀).functor ⋙ Over.forget (op i₀)
  have : G.Initial := by dsimp only [G]; infer_instance
  let ct : Cone (G ⋙ D) := (limit.cone D).whisker G
  have hct : IsLimit ct :=
    (Functor.Initial.isLimitWhiskerEquiv G (limit.cone D)).symm (limit.isLimit D)
  let τ : (G ⋙ D) ⟶ (Functor.const ((LimitTail I i₀)ᵒᵖ)).obj (D.obj (op i₀)) :=
    { app := fun j => D.map (homOfLE j.unop.2).op
      naturality := fun j k φ =>
        ((D.map_comp (G.map φ) ((homOfLE k.unop.2).op)).symm.trans
            (congrArg (fun x : G.obj j ⟶ op i₀ => D.map x) (Subsingleton.elim _ _))).trans
          (Category.comp_id _).symm }
  have hσ : ∀ j, ct.π.app j ≫ τ.app j = limit.π D (op i₀) := fun j =>
    limit.w D (homOfLE j.unop.2).op
  have hcE : IsLimit (Subfunctor.preimageCone τ V hσ) :=
    Subfunctor.isLimitPreimageCone τ V hσ hct
  have hctπ : ∀ j, ct.π.app j = limit.π D (G.obj j) := fun _ => rfl
  -- Each stage of the system of preimages is a quasi-compact open subspace.
  have hVp : ∀ j : (LimitTail I i₀)ᵒᵖ, IsOpenSubspace B S contains (V.preimage (τ.app j)) :=
    fun j => isOpenSubspace_preimage B S contains (τ.app j) V (algebraicStage i₀)
      (algebraicStage j.unop.1) hVopen
  have hτaff : ∀ j : (LimitTail I i₀)ᵒᵖ, IsAffineHom B S contains (τ.app j) := fun j =>
    affine j.unop.2
  have hEqc : ∀ j : LimitTail I i₀,
      IsQuasiCompactSpace B S contains ((Subfunctor.preimageDiagram τ V).obj (op j)) := by
    intro j
    exact isQuasiCompactSpace_preimage_of_isAffineHom B S contains (τ.app (op j)) V hVopen
      (hVp (op j)) hVqc (hτaff (op j))
  have hEaff : ∀ ⦃x y : LimitTail I i₀⦄ (h : x ≤ y),
      IsAffineHom B S contains ((Subfunctor.preimageDiagram τ V).map (homOfLE h).op) := by
    intro x y h
    exact isAffineHom_of_isPullback
      (Subfunctor.isPullback_preimageDiagram_map τ V (homOfLE h).op).flip
      (affine (show x.1 ≤ y.1 from h))
  -- The structure morphisms of the system of preimages over the base.
  let tE : Subfunctor.preimageDiagram τ V ⟶
      (Functor.const ((LimitTail I i₀)ᵒᵖ)).obj Bspace :=
    { app := fun j => (V.preimage (τ.app j)).ι ≫ t.app (G.obj j)
      naturality := fun j k φ => by
        have hw := (Subfunctor.isPullback_preimageDiagram_map τ V φ).w
        have hn := t.naturality (G.map φ)
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at hn
        have h1 : (Subfunctor.preimageDiagram τ V).map φ ≫
              ((V.preimage (τ.app k)).ι ≫ t.app (G.obj k))
            = ((Subfunctor.preimageDiagram τ V).map φ ≫ (V.preimage (τ.app k)).ι) ≫
              t.app (G.obj k) := (Category.assoc _ _ _).symm
        have h2 := congrArg (· ≫ t.app (G.obj k)) hw
        have h3 : ((V.preimage (τ.app j)).ι ≫ (G ⋙ D).map φ) ≫ t.app (G.obj k)
            = (V.preimage (τ.app j)).ι ≫ ((G ⋙ D).map φ ≫ t.app (G.obj k)) :=
          Category.assoc _ _ _
        have h4 := congrArg ((V.preimage (τ.app j)).ι ≫ ·) hn
        exact ((h1.trans h2).trans (h3.trans h4)).trans (Category.comp_id _).symm }
  have hπs : ∀ a : Iᵒᵖ, limit.π D a ≫ t.app a = e.inv ≫ s := by
    intro a
    have h := congrArg (fun α => α.app a) commutes
    change c.π.app a ≫ t.app a = s at h
    have h2 : e.hom ≫ limit.π D a ≫ t.app a = s := by
      rw [← Category.assoc, he a]; exact h
    rw [← h2]
    simp
  let sE : (Subfunctor.preimageCone τ V hσ).pt ⟶ Bspace :=
    (V.preimage (limit.π D (op i₀))).ι ≫ e.inv ≫ s
  have hcommE : (Subfunctor.preimageCone τ V hσ).π ≫ tE
      = (Functor.const ((LimitTail I i₀)ᵒᵖ)).map sE := by
    refine NatTrans.ext (funext fun j => ?_)
    have h1 : (Subfunctor.preimageCone τ V hσ).π.app j ≫ (V.preimage (τ.app j)).ι
        = (V.preimage (limit.π D (op i₀))).ι ≫ ct.π.app j := rfl
    have h0 : ((Subfunctor.preimageCone τ V hσ).π.app j ≫ (V.preimage (τ.app j)).ι) ≫
          t.app (G.obj j)
        = (Subfunctor.preimageCone τ V hσ).π.app j ≫
          ((V.preimage (τ.app j)).ι ≫ t.app (G.obj j)) := Category.assoc _ _ _
    have h2 := congrArg (· ≫ t.app (G.obj j)) h1
    have h3 : ((V.preimage (limit.π D (op i₀))).ι ≫ ct.π.app j) ≫ t.app (G.obj j)
        = (V.preimage (limit.π D (op i₀))).ι ≫ (ct.π.app j ≫ t.app (G.obj j)) :=
      Category.assoc _ _ _
    have h4 := congrArg ((V.preimage (limit.π D (op i₀))).ι ≫ ·) (hπs (G.obj j))
    exact h0.symm.trans ((h2.trans h3).trans h4)
  have hFT : IsLocallyOfFiniteType B S contains (g ≫ sE) := by
    have hgs : g ≫ sE = f ≫ s := by
      change g ≫ (V.preimage (limit.π D (op i₀))).ι ≫ e.inv ≫ s = f ≫ s
      rw [← Category.assoc, hgι]
      simp
    rw [hgs]
    exact finiteType
  -- Part (1) at the system of quasi-compact opens.
  have hres := eventually_isClosedImmersion_comp_limitπ' B S contains Bspace algebraicBase
    (Subfunctor.preimageDiagram τ V) (fun j => (hVp (op j)).1) tE
    (Subfunctor.preimageCone τ V hσ) hcE sE hcommE Y algebraic g hEqc hEaff hFT hgclosed
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 hres
  refine eventually_atTop.2 ⟨j₀.1, fun i hi => ?_⟩
  have hclo := hj₀ ⟨i, j₀.2.trans hi⟩ hi
  have himm : IsImmersion B S contains
      ((g ≫ (Subfunctor.preimageCone τ V hσ).π.app (op ⟨i, j₀.2.trans hi⟩)) ≫
        (V.preimage (τ.app (op ⟨i, j₀.2.trans hi⟩))).ι) :=
    isImmersion_comp B S contains _ _ (isImmersion_of_isClosedImmersion B S contains hclo)
      (isImmersion_of_isOpenImmersion B S contains (hVp (op ⟨i, j₀.2.trans hi⟩)).2)
  have k1 : (g ≫ (Subfunctor.preimageCone τ V hσ).π.app (op ⟨i, j₀.2.trans hi⟩)) ≫
        (V.preimage (τ.app (op ⟨i, j₀.2.trans hi⟩))).ι
      = g ≫ ((Subfunctor.preimageCone τ V hσ).π.app (op ⟨i, j₀.2.trans hi⟩) ≫
        (V.preimage (τ.app (op ⟨i, j₀.2.trans hi⟩))).ι) := Category.assoc _ _ _
  have k2 := congrArg (g ≫ ·)
    (show (Subfunctor.preimageCone τ V hσ).π.app (op ⟨i, j₀.2.trans hi⟩) ≫
          (V.preimage (τ.app (op ⟨i, j₀.2.trans hi⟩))).ι
        = (V.preimage (limit.π D (op i₀))).ι ≫ limit.π D (op i) from rfl)
  have k3 : g ≫ ((V.preimage (limit.π D (op i₀))).ι ≫ limit.π D (op i))
      = (g ≫ (V.preimage (limit.π D (op i₀))).ι) ≫ limit.π D (op i) :=
    (Category.assoc _ _ _).symm
  have k4 := congrArg (· ≫ limit.π D (op i)) hgι
  have k5 : (f ≫ e.hom) ≫ limit.π D (op i) = f ≫ (e.hom ≫ limit.π D (op i)) :=
    Category.assoc _ _ _
  have k6 := congrArg (f ≫ ·) (he (op i))
  rwa [((k1.trans k2).trans (k3.trans k4)).trans (k5.trans k6)] at himm

/-- **Stacks 0828, part (2).** Let `X = lim Xᵢ` be a directed limit of algebraic spaces over an
algebraic space `Bspace`, with affine transition morphisms and quasi-separated stages, and let
`f : Y ⟶ X` be an immersion whose source is quasi-compact and locally of finite type over
`Bspace`.  Then `Y ⟶ Xᵢ` is an immersion for all sufficiently large `i`.

The image of `Y` in one stage `Xᵢ₀` lies in a quasi-compact open subspace `V`, and the system of
preimages of `V` in the stages above `i₀` has quasi-compact stages and limit the preimage of `V`
in `X`, through which `f` factors by an immersion.  An affine étale atlas of `V` reduces the
statement to schemes, where it is Stacks 081B, part (2)
(`AlgebraicGeometry.EventualLimit.eventually_isImmersion_comp_π_app`), and the immersion is
carried back to the stages by effective descent of immersions along surjective étale
morphisms; quasi-separatedness of `Xᵢ₀` makes the base change of `Y` to the atlas quasi-compact.
-/
@[stacks 0828 "part (2): immersions"]
theorem eventually_isImmersion_comp_limitπ
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (contains : B.Contains S)
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (Bspace : (BigFppfOver B S contains)ᵒᵖ ⥤ Type u)
    (algebraicBase : IsAlgebraicSpace B S contains Bspace)
    (D : Iᵒᵖ ⥤ (BigFppfOver B S contains)ᵒᵖ ⥤ Type u)
    (algebraicStage : ∀ i, IsAlgebraicSpace B S contains (D.obj (op i)))
    (t : D ⟶ (Functor.const Iᵒᵖ).obj Bspace)
    (c : Cone D) (isLimit : IsLimit c) (s : c.pt ⟶ Bspace)
    (commutes : c.π ≫ t = (Functor.const Iᵒᵖ).map s)
    (Y : (BigFppfOver B S contains)ᵒᵖ ⥤ Type u)
    (algebraic : IsAlgebraicSpace B S contains Y)
    (quasiCompact : IsQuasiCompactSpace B S contains Y)
    (f : Y ⟶ c.pt)
    (affine : ∀ ⦃i j : I⦄ (h : i ≤ j), IsAffineHom B S contains (D.map (homOfLE h).op))
    (quasiSeparated : ∀ i,
      IsAbsolutelyQuasiSeparated B S contains B.contains_terminal (D.obj (op i)))
    (finiteType : IsLocallyOfFiniteType B S contains (f ≫ s))
    (immersion : IsImmersion B S contains f) :
    ∀ᶠ i in atTop, IsImmersion B S contains (f ≫ c.π.app (op i)) := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty I›
  -- A quasi-compact open subspace `V` of the stage `i₀` through which `Y` maps.
  obtain ⟨V, g₀, hVopen, hVqc, hg₀⟩ := exists_isOpenSubspace_isQuasiCompactSpace_lift B S contains
    (algebraicStage i₀) algebraic quasiCompact (f ≫ c.π.app (op i₀))
  -- The tail of the index preorder above `i₀`, with its inclusion into `Iᵒᵖ`.
  have : Nonempty (LimitTail I i₀) := ⟨⟨i₀, le_rfl⟩⟩
  have := isDirected_limitTail i₀
  let G : (LimitTail I i₀)ᵒᵖ ⥤ Iᵒᵖ :=
    (limitTailOverEquiv i₀).functor ⋙ Over.forget (op i₀)
  have : G.Initial := by dsimp only [G]; infer_instance
  let ct : Cone (G ⋙ D) := c.whisker G
  have hct : IsLimit ct := (Functor.Initial.isLimitWhiskerEquiv G c).symm isLimit
  let τ : (G ⋙ D) ⟶ (Functor.const ((LimitTail I i₀)ᵒᵖ)).obj (D.obj (op i₀)) :=
    { app := fun j => D.map (homOfLE j.unop.2).op
      naturality := fun j k φ =>
        ((D.map_comp (G.map φ) ((homOfLE k.unop.2).op)).symm.trans
            (congrArg (fun x : G.obj j ⟶ op i₀ => D.map x) (Subsingleton.elim _ _))).trans
          (Category.comp_id _).symm }
  have hσ : ∀ j, ct.π.app j ≫ τ.app j = c.π.app (op i₀) := fun j =>
    c.w (homOfLE j.unop.2).op
  -- The system of preimages of `V`, and its limit.
  let E := Subfunctor.preimageDiagram τ V
  let cE := Subfunctor.preimageCone τ V hσ
  have hcE : IsLimit cE := Subfunctor.isLimitPreimageCone τ V hσ hct
  have hVp : ∀ j : (LimitTail I i₀)ᵒᵖ, IsOpenSubspace B S contains (V.preimage (τ.app j)) :=
    fun j => isOpenSubspace_preimage B S contains (τ.app j) V (algebraicStage i₀)
      (algebraicStage j.unop.1) hVopen
  have hEqc : ∀ j : LimitTail I i₀, IsQuasiCompactSpace B S contains (E.obj (op j)) := by
    intro j
    exact isQuasiCompactSpace_preimage_of_isAffineHom B S contains (τ.app (op j)) V hVopen
      (hVp (op j)) hVqc (affine j.2)
  have hEaff : ∀ ⦃x y : LimitTail I i₀⦄ (h : x ≤ y),
      IsAffineHom B S contains (E.map (homOfLE h).op) := by
    intro x y h
    exact isAffineHom_of_isPullback
      (Subfunctor.isPullback_preimageDiagram_map τ V (homOfLE h).op).flip
      (affine (show x.1 ≤ y.1 from h))
  -- `f` factors through the preimage of `V` in the limit, by an immersion.
  have hrange : Subfunctor.range f ≤ V.preimage (c.π.app (op i₀)) := by
    rw [← Subfunctor.image_le_iff, ← Subfunctor.range_comp, ← hg₀]
    exact (Subfunctor.range_comp_le g₀ V.ι).trans (Subfunctor.range_ι V).le
  let ιP : cE.pt ⟶ c.pt := (V.preimage (c.π.app (op i₀))).ι
  have : Mono ιP := inferInstanceAs (Mono (V.preimage (c.π.app (op i₀))).ι)
  let ιE (j : LimitTail I i₀) : E.obj (op j) ⟶ D.obj (op j.1) := (V.preimage (τ.app (op j))).ι
  have h1 (j : LimitTail I i₀) : cE.π.app (op j) ≫ ιE j = ιP ≫ c.π.app (op j.1) := rfl
  let g : Y ⟶ cE.pt := Subfunctor.lift f hrange
  have hgι : g ≫ ιP = f := Subfunctor.lift_ι f hrange
  have _hbc : MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S contains))) :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hg : IsImmersion B S contains g :=
    MorphismProperty.of_isPullback
      (IsPullback.of_horiz_isIso_mono (fst := 𝟙 Y) (snd := g) (f := f)
        (g := ιP) ⟨by simpa using hgι.symm⟩) immersion
  -- Transport to the chosen limit of the system of preimages.
  let e := hcE.conePointUniqueUpToIso (limit.isLimit E)
  have he (a) : e.hom ≫ limit.π E a = cE.π.app a :=
    hcE.conePointUniqueUpToIso_hom_comp (limit.isLimit E) a
  have hg' : IsImmersion B S contains (g ≫ e.hom) :=
    MorphismProperty.RespectsIso.postcomp _ e.hom g hg
  -- An affine étale atlas of the first stage of the system.
  let j₀ : LimitTail I i₀ := ⟨i₀, le_rfl⟩
  obtain ⟨U₀, p₀, hU₀aff, hp₀surj, hp₀etale⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover
      B S contains (E.obj (op j₀)) (hVp (op j₀)).1).mp (hEqc j₀)
  have hpE := presheaf_etale_of_isEtale B S contains hp₀etale
  -- The composite to the first stage is locally of finite type.
  have h2 : c.π.app (op i₀) ≫ t.app (op i₀) = s := by
    simpa using congrArg (fun η => η.app (op i₀)) commutes
  have hcomp₀ : (g ≫ cE.π.app (op j₀)) ≫ (ιE j₀ ≫ t.app (op i₀)) = f ≫ s :=
    calc (g ≫ cE.π.app (op j₀)) ≫ (ιE j₀ ≫ t.app (op i₀))
        = g ≫ (cE.π.app (op j₀) ≫ ιE j₀) ≫ t.app (op i₀) := by simp only [Category.assoc]
      _ = g ≫ (ιP ≫ c.π.app (op i₀)) ≫ t.app (op i₀) := by rw [h1]
      _ = (g ≫ ιP) ≫ c.π.app (op i₀) ≫ t.app (op i₀) := by simp only [Category.assoc]
      _ = f ≫ s := by rw [hgι, h2]
  have hFinite : IsLocallyOfFiniteType B S contains ((g ≫ e.hom) ≫ limit.π E (op j₀)) := by
    rw [Category.assoc, he]
    exact isLocallyOfFiniteType_of_comp B S contains algebraic (hVp (op j₀)).1 algebraicBase
      (g ≫ cE.π.app (op j₀)) (ιE j₀ ≫ t.app (op i₀))
      (by have h := finiteType; rw [← hcomp₀] at h; exact h)
  -- The base change of `Y` to the atlas is quasi-compact, the stage being quasi-separated.
  have hEqs : IsAbsolutelyQuasiSeparated B S contains B.contains_terminal (E.obj (op j₀)) := by
    let ι₀ := ιE j₀
    have : Mono ι₀ := inferInstanceAs (Mono (V.preimage (τ.app (op j₀))).ι)
    have : IsIso (pullback.diagonal ι₀) := (pullback.isIso_diagonal_iff ι₀).2 inferInstance
    have hqs : IsQuasiSeparated B S contains ι₀ := by
      intro Z _ hZqc k
      exact isQuasiCompactSpace_of_iso B S contains
        (asIso (pullback.fst k (pullback.diagonal ι₀))).symm hZqc
    exact isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S contains B.contains_terminal
      (hVp (op j₀)).1 (quasiSeparated i₀) hqs
  have hGqc : IsQuasiCompactSpace B S contains
      (pullback ((g ≫ e.hom) ≫ limit.π E (op j₀)) p₀) :=
    isQuasiCompactSpace_pullback B S contains B.contains_terminal _ p₀ algebraic
      (hVp (op j₀)).1 quasiCompact (isQuasiCompactSpace_yoneda_of_isAffine B S contains _ hU₀aff)
      hEqs
  have hres := eventually_isImmersion_of_affine_atlas B S contains E (fun j => (hVp (op j)).1)
    hEaff algebraic (g ≫ e.hom) hg' j₀ U₀ hU₀aff p₀ hp₀surj hpE hFinite hGqc
  obtain ⟨j₁, hj₁⟩ := eventually_atTop.1 hres
  refine eventually_atTop.2 ⟨j₁.1, fun i hi => ?_⟩
  let j : LimitTail I i₀ := ⟨i, j₁.2.trans hi⟩
  have himm : IsImmersion B S contains (g ≫ cE.π.app (op j)) := by
    have h := hj₁ j hi
    rwa [Category.assoc, he] at h
  have hcomp : (g ≫ cE.π.app (op j)) ≫ ιE j = f ≫ c.π.app (op i) := by
    rw [Category.assoc, h1 j, ← Category.assoc, hgι]
  rw [← hcomp]
  exact isImmersion_comp B S contains _ _ himm
    (isImmersion_of_isOpenImmersion B S contains (hVp (op j)).2)

end Immersions

end AlgebraicGeometry.Space
