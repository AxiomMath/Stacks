module

public import StacksFrontier.AlgebraicGeometry.Descent.SurjectiveEtaleDescent
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeEtaleFamily
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeOnReductionsCharacterizationRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeOnReductionsChartMaps
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionSmoothBaseChangeRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTargetRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SchemeAtlas
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.LocallySurjectiveTransfer
import all StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSitePostcomposition

/-!
# Characterising finite type on reductions on affine charts

Let `S` be a scheme contained in a big fppf site `B`. **Stacks 0GC7** says that for a morphism
`f : X ⟶ Y` of locally countably indexed formal algebraic spaces over `S` the following four
conditions are equivalent:

1. every commutative square with affine formal algebraic spaces `U`, `V` and representable
   étale maps `U ⟶ X`, `V ⟶ Y` has its upper map `U ⟶ V` given by an arrow of `WAdm^{count}`
   with the property of Stacks 0GC2, that the induced map of the quotients by the ideals of
   topologically nilpotent elements be of finite type;
2. there is a covering `{Yⱼ ⟶ Y}` as in Definition 0AIM and for each `j` a covering
   `{Xⱼᵢ ⟶ Yⱼ ×_Y X}` as in Definition 0AIM with each `Xⱼᵢ ⟶ Yⱼ` given by such an arrow;
3. there is a covering `{Xᵢ ⟶ X}` as in Definition 0AIM and for each `i` a factorization
   `Xᵢ ⟶ Yᵢ ⟶ Y` through an affine formal algebraic space representable étale over `Y` with
   `Xᵢ ⟶ Yᵢ` given by such an arrow;
4. the morphism of reductions `f_red : X_red ⟶ Y_red` is locally of finite type.

This file proves it with no hypothesis beyond those of the source.

## Main results

All names below are in the namespace `AlgebraicGeometry.FormalSpace`.

* `isLocallyOfFiniteTypeULift_of_isEtaleULift`: an étale morphism of algebraic spaces over `S`
  is locally of finite type.
* `isLocallyOfFiniteTypeULift_of_etaleFamily`: **being locally of finite type is local on the
  source along a jointly surjective family of representable étale morphisms**, read for the
  morphism of algebraic spaces of Stacks 03XF on a morphism of fppf sheaves.
* `isLocallyOfFiniteTypeOnReductions_of_hasPropertyAfterSourceCover`: the implication (3) ⟹ (4)
  of Stacks 0GC7.
* `isLocallyOfFiniteTypeOnReductions_tfae_of_isLocallyCountablyIndexed`: **Stacks 0GC7**.

## Implementation notes

The equivalence of (1), (2) and (3) is Stacks 0ANG for the property of Stacks 0GC2 on
`WAdm^{count}`, run through the three legs the library carries for it, with the locality axioms
and the refinement of a source covering at `WAdm^{count}` already proved there. The implication
(4) ⟹ (1) is `hasPropertyOnEveryAffineEtaleDiagram_of_isLocallyOfFiniteTypeOnReductions`.

For (3) ⟹ (4), given reductions `X_red`, `Y_red` and a morphism `f_red` between them over `f`,
the reductions of the members of the covering are taken to be the fibre products
`Xᵢ ×_X X_red` and `Yᵢ ×_Y Y_red`, which are reductions by Stacks 0GB7 because étale morphisms
are smooth. Their projections to `X_red` form a jointly surjective family of representable étale
morphisms, the base change of the covering, and the composite `Xᵢ ×_X X_red ⟶ X_red ⟶ Y_red`
factors as the morphism of reductions of `Xᵢ ⟶ Yᵢ`, locally of finite type by the affine
computation of Stacks 0GB6, followed by the étale `Yᵢ ×_Y Y_red ⟶ Y_red`. Being locally of
finite type is local on the source along such a family, which is the étale locality of Stacks
040Y the proof of the source invokes: an étale chart `h_A ⟶ X_red` is covered by the scheme
atlases of the algebraic spaces `h_A ×_{X_red} (Xᵢ ×_X X_red)`, the family of these is cut down
and glued to a single surjective étale chart of `h_A` by
`AlgebraicGeometry.FormalSpace.exists_chart_of_etaleChartFamily`, and local finite type
descends along a surjective étale morphism of schemes.

Condition (4) is `AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteTypeOnReductions`, which asks
the morphism of algebraic spaces to be locally of finite type for every choice of reductions and
of a morphism between them over `f`. Reductions exist by Stacks 0AIN and any two are isomorphic,
so this is the condition on `f_red`.

## References

* [Stacks Project, Tag 03XF](https://stacks.math.columbia.edu/tag/03XF)
* [Stacks Project, Tag 040Y](https://stacks.math.columbia.edu/tag/040Y)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0GB6](https://stacks.math.columbia.edu/tag/0GB6)
* [Stacks Project, Tag 0GB7](https://stacks.math.columbia.edu/tag/0GB7)
* [Stacks Project, Tag 0GC2](https://stacks.math.columbia.edu/tag/0GC2)
* [Stacks Project, Tag 0GC7](https://stacks.math.columbia.edu/tag/0GC7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Local finite type for morphisms of algebraic spaces -/

/-- An étale morphism of algebraic spaces over `S` is locally of finite type: for a scheme atlas
`W ⟶ F` of the source, the composite `W ⟶ F ⟶ G` is an étale chart of the target, so the
identity of `W` is a surjective étale chart of the morphism on which it is locally of finite
type, and Stacks 03MJ applies. -/
theorem isLocallyOfFiniteTypeULift_of_isEtaleULift
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (hF : Space.IsAlgebraicSpaceULift.{u + 1} B S hS F)
    (hG : Space.IsAlgebraicSpaceULift.{u + 1} B S hS G) (f : F ⟶ G)
    (hf : Space.IsEtaleULift.{u + 1} B S hS f) :
    Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS f := by
  obtain ⟨W, w, hws, hwe⟩ := hF.exists_atlas
  refine Space.holdsOnEveryEtaleChartULift_of_surjectiveChart B S hS
    (@AlgebraicGeometry.LocallyOfFiniteType.{u})
    LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget hF hG W W w (w ≫ f) (𝟙 W) hwe
    (hf W w hwe) hws (by simp) ?_
  rw [CategoryTheory.Functor.map_id]
  infer_instance

/-- **Being locally of finite type is local on the source along a jointly surjective family of
representable étale morphisms.** Let `g : F ⟶ G` be a morphism of fppf sheaves on the big fppf
site of `S` and let `{pᵢ : Eᵢ ⟶ F}` be a family of representable étale morphisms which is
jointly surjective as a family of morphisms of sheaves. If every composite `pᵢ ≫ g` is locally
of finite type in the sense of Stacks 03XF, then so is `g`.

Let `h : A ⟶ B'` be a morphism of the site lying over `g` through étale charts `h_A ⟶ F` and
`h_{B'} ⟶ G`. Each base change `h_A ×_F Eᵢ` is an algebraic space étale over `A`; its scheme
atlas `Wᵢ` maps to `A` étale, and to `Eᵢ` by an étale chart lying over `pᵢ ≫ g`, so
`Wᵢ ⟶ A ⟶ B'` is locally of finite type. The image sieves of the family `{Wᵢ ⟶ A}` cover, so
`AlgebraicGeometry.FormalSpace.exists_chart_of_etaleChartFamily` replaces it by one surjective
étale `Z ⟶ A` with `Z ⟶ A ⟶ B'` locally of finite type, and local finite type descends along a
surjective étale morphism. -/
theorem isLocallyOfFiniteTypeULift_of_etaleFamily {F G : FppfSheaf B S hS} (g : F ⟶ G)
    {I : Type (u + 1)} {E : I → FppfSheaf B S hS} (p : ∀ i, E i ⟶ F)
    (hp : ∀ i, IsRepresentableEtale B S hS (p i))
    (hcov : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc p))
    (hlft : ∀ i, Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS (p i ≫ g).hom) :
    Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS g.hom := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  intro A B' α β h hα hβ hsq
  choose W w hws hwe using fun i ↦ ((hp i).1 A α).exists_atlas
  have hγe : ∀ i, (Space.etaleOnSite B S hS).relative uliftYoneda.{u + 1}
      (w i ≫ pullback.fst α (p i).hom) := fun i ↦ (hp i).2 A α (W i) (w i) (hwe i)
  have hsieve := imageSieve_iSup_mem_comp (BigFppfOver.topology B S hS)
    (fun i ↦ pullback.fst α (p i).hom) w
    (fun i ↦ isLocallySurjective_of_relative_surjective_etale B S hS (w i) (hws i) (hwe i))
    (imageSieve_iSup_mem_pullback_fst (BigFppfOver.topology B S hS)
      (fun i ↦ (p i).hom) α
      (fun V x ↦ family_imageSieve_mem (BigFppfOver.topology B S hS) E F p hcov V x))
  obtain ⟨Z, q, hqs, hqe, hqP⟩ := exists_chart_of_etaleChartFamily B S hS
    (E := (⟨(uliftYoneda.{u + 1}).obj A,
      (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS A).isSheaf⟩ : FppfSheaf B S hS))
    (𝟙 _) inferInstance (fun i ↦ w i ≫ pullback.fst α (p i).hom) hγe hsieve
  have hmem : ∀ i, LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map
      ((uliftYoneda.{u + 1}).preimage
        ((w i ≫ pullback.fst α (p i).hom) ≫ (uliftYoneda.{u + 1}).map h))) := by
    intro i
    refine hlft i (W i) B' (w i ≫ pullback.snd α (p i).hom) β _
      (Space.relative_comp B S hS (hwe i)
        (Space.relative_of_isPullback B S hS (IsPullback.of_hasPullback α (p i).hom).flip hα))
      hβ ?_
    rw [Functor.map_preimage, Category.assoc, Category.assoc, hsq, pullback.condition_assoc]
    rfl
  have hZ := hqP B' ((uliftYoneda.{u + 1}).map h) (@AlgebraicGeometry.LocallyOfFiniteType.{u})
    (HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @AlgebraicGeometry.LocallyOfFiniteType.{u})) hmem
  obtain ⟨z, rfl⟩ : ∃ z : Z ⟶ A, (uliftYoneda.{u + 1}).map z = q :=
    ⟨(uliftYoneda.{u + 1}).preimage q, by simp⟩
  rw [← Functor.map_comp, Functor.preimage_map, Functor.map_comp] at hZ
  exact locallyOfFiniteType_of_comp_surjective_etale _ _
    (hqs.property (𝟙 _) (𝟙 _) z IsPullback.of_id_fst)
    (hqe.property (𝟙 _) (𝟙 _) z IsPullback.of_id_fst) hZ

/-! ### Stacks 0GC7, condition (3) implies condition (4) -/

/-- **Stacks 0GC7, condition (3) implies condition (4).** Let `f : X ⟶ Y` be a morphism of
locally countably indexed formal algebraic spaces over `S` admitting a covering `{Xᵢ ⟶ X}` as in
Definition 0AIM whose members factor as `Xᵢ ⟶ Yᵢ ⟶ Y` through affine formal algebraic spaces
representable étale over `Y`, by arrows of `WAdm^{count}` with the property of Stacks 0GC2. Then
the morphism of reductions of `f` is locally of finite type.

The reductions of `Xᵢ` and `Yᵢ` are the fibre products `Xᵢ ×_X X_red` and `Yᵢ ×_Y Y_red`
(Stacks 0GB7), the morphism between them over `Xᵢ ⟶ Yᵢ` is locally of finite type by the affine
computation of Stacks 0GB6, the projection `Yᵢ ×_Y Y_red ⟶ Y_red` is étale, and the composite
is the restriction of `f_red` to the member `Xᵢ ×_X X_red` of a jointly surjective family of
representable étale morphisms into `X_red`, along which local finite type descends. -/
theorem isLocallyOfFiniteTypeOnReductions_of_hasPropertyAfterSourceCover
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyCountablyIndexed B S hS X) (hY : IsLocallyCountablyIndexed B S hS Y)
    (hf : HasPropertyAfterSourceCover B S hS TopologicalRing.IsCountablyWeaklyAdmissible
      TopologicalRing.FiniteTypeOnReductionsProperty f) :
    IsLocallyOfFiniteTypeOnReductions B S hS f := by
  obtain ⟨I, U, a, ⟨hUaff, haE, hcov⟩, hfac⟩ := hf
  choose V b t hVaff hbE hsq ht using hfac
  intro Xred Yred iX iY hXr hYr fred hfred
  have hred_pullback : ∀ {Z Zred : FppfSheaf B S hS} {iZ : Zred ⟶ Z} {W : FppfSheaf B S hS}
      (c : W ⟶ Z), IsReduction B S hS Z Zred iZ → IsRepresentableEtale B S hS c →
      IsReduction B S hS W (pullback c iZ) (pullback.fst c iZ) :=
    fun c hZr hcE ↦ IsReduction.pullback_of_smooth B S hS hcE.1
      (hasPropertyULift_smooth_of_etale B S hS hcE.1 hcE.2) hZr
      (IsPullback.of_hasPullback c _)
  have hEr := fun i ↦ hred_pullback (a i) hXr (haE i)
  have hFr := fun i ↦ hred_pullback (b i) hYr (hbE i)
  have htR : ∀ i, (pullback.fst (a i) iX ≫ t i) ≫ b i =
      (pullback.snd (a i) iX ≫ fred) ≫ iY := fun i ↦ by
    rw [Category.assoc, ← hsq i, pullback.condition_assoc, Category.assoc, hfred]
  have hlft : ∀ i, Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS
      (pullback.snd (a i) iX ≫ fred).hom := by
    intro i
    have hred := (chartPropertyIsFiniteTypeOnReductions B S hS (t i) (hUaff i) (hVaff i)
      (isCountablyIndexed_of_isRepresentableEtale_of_isLocallyCountablyIndexed B S hS X hX
        (U i) (a i) (hUaff i) (haE i))
      (isCountablyIndexed_of_isRepresentableEtale_of_isLocallyCountablyIndexed B S hS Y hY
        (V i) (b i) (hVaff i) (hbE i))).2 (ht i) _ _ _ _ (hEr i) (hFr i)
      (pullback.lift _ _ (htR i)) (pullback.lift_fst _ _ _)
    have hr := isLocallyOfFiniteTypeULift_of_isEtaleULift B S hS (hFr i).algebraic
      hYr.algebraic _ (IsReduction.isEtaleULift_map B S hS (hFr i) hYr (hbE i).1 (hbE i).2
        pullback.condition.symm)
    rw [← pullback.lift_snd (pullback.fst (a i) iX ≫ t i) (pullback.snd (a i) iX ≫ fred)
      (htR i)]
    exact Space.isLocallyOfFiniteTypeULift_comp B S hS (hEr i).algebraic (hFr i).algebraic
      hYr.algebraic _ _ hred hr
  exact isLocallyOfFiniteTypeULift_of_etaleFamily B S hS fred (fun i ↦ pullback.snd (a i) iX)
    (fun i ↦ isRepresentableEtale_pullback_snd B S hS (a i) iX (haE i))
    (Sheaf.isLocallySurjective_sigmaDesc_pullback_snd iX a hcov) hlft

/-! ### Stacks 0GC7 -/

variable {B S hS}

/-- **Stacks 0GC7.** For a morphism `f : X ⟶ Y` of locally countably indexed formal algebraic
spaces over `S` the following are equivalent:

1. every affine representable étale square over `f` has its upper map given by an arrow of
   `WAdm^{count}` with the property of Stacks 0GC2;
2. there is an affine étale covering of `Y` together with affine étale coverings of the fibre
   products of its members with `X` whose maps to the members of the first covering are given by
   such arrows;
3. there is an affine étale covering of `X` whose members factor through affine formal
   algebraic spaces representable étale over `Y` by such arrows;
4. the morphism of reductions `f_red : X_red ⟶ Y_red` is locally of finite type.

The first three are the three conditions of Stacks 0ANG for the property of Stacks 0GC2, which
is local on `WAdm^{count}`; (3) ⟹ (4) and (4) ⟹ (1) are the affine computation of Stacks 0GB6
together with the étale locality of being locally of finite type. -/
@[stacks 0GC7 "the four conditions, for a morphism of locally countably indexed formal \
algebraic spaces; condition (4) is read for every pair of reductions of the source and the \
target and every morphism between them over f, reductions existing and being unique up to \
unique isomorphism by Stacks 0AIN"]
theorem isLocallyOfFiniteTypeOnReductions_tfae_of_isLocallyCountablyIndexed
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyCountablyIndexed B S hS X) (hY : IsLocallyCountablyIndexed B S hS Y) :
    List.TFAE
      [HasPropertyOnEveryAffineEtaleDiagram B S hS
          TopologicalRing.IsCountablyWeaklyAdmissible
          TopologicalRing.FiniteTypeOnReductionsProperty f,
        HasPropertyAfterTargetCover B S hS
          TopologicalRing.IsCountablyWeaklyAdmissible
          TopologicalRing.FiniteTypeOnReductionsProperty f,
        HasPropertyAfterSourceCover B S hS
          TopologicalRing.IsCountablyWeaklyAdmissible
          TopologicalRing.FiniteTypeOnReductionsProperty f,
        IsLocallyOfFiniteTypeOnReductions B S hS f] := by
  tfae_have 1 → 2 := fun h ↦ hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram B S hS
    TopologicalRing.IsCountablyWeaklyAdmissible
    TopologicalRing.FiniteTypeOnReductionsProperty f hY.1
    (fun _V v' hV' _ ↦ isFormalAlgebraicSpace_pullback_chart_of_isFormalAlgebraicSpace B S hS
      v' f hY.1 hV' hX.1) h
  tfae_have 2 → 3 := fun h ↦ hasPropertyAfterSourceCover_of_afterTargetCover B S hS
    TopologicalRing.IsCountablyWeaklyAdmissible
    TopologicalRing.FiniteTypeOnReductionsProperty f h
  tfae_have 3 → 1 := fun h ↦ hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover' B S hS
    TopologicalRing.IsCountablyWeaklyAdmissible
    TopologicalRing.FiniteTypeOnReductionsProperty f hX hY
    (chartPropertyAscendsAlongAffineEtale_finiteTypeOnReductions B S hS)
    (chartPropertyDescendsAlongFiniteAffineEtaleCover_finiteTypeOnReductions B S hS)
    (hasEtaleRefinementOfSourceCover_isCountablyWeaklyAdmissible B S hS f) h
  tfae_have 3 → 4 :=
    isLocallyOfFiniteTypeOnReductions_of_hasPropertyAfterSourceCover B S hS f hX hY
  tfae_have 4 → 1 :=
    hasPropertyOnEveryAffineEtaleDiagram_of_isLocallyOfFiniteTypeOnReductions B S hS f hX hY
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
