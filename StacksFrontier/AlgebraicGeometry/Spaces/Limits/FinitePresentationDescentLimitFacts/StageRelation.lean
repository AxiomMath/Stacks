module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescentLimitFacts.MorphismDescent
import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative
import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.Separated
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
import all StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent
import all StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescentLimitFacts.AffineStageCharts
import all StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescentLimitFacts.MorphismDescent

/-!
# A finite-presentation model from a stage relation, under `LimitFacts`

The étale relation presenting an algebraic space of finite presentation over the limit, once
it is defined at a stage, becomes an étale equivalence relation at a later stage, where it
presents a finite-presentation model of the space.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! The two projections of an explicit fibre product out of a lift into it are not `simp`
lemmas in Mathlib, where `pullback.hom_ext` is the preferred interface; the explicit cones
built below are compared projection by projection throughout. -/

attribute [local simp] pullback.lift_fst pullback.lift_snd
  pullback.lift_fst_assoc pullback.lift_snd_assoc

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
variable {I : Type u} [Category.{u} I] [IsCofiltered I]
variable (D : I ⥤ (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
variable (hSize : Cardinal.mk I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, Cardinal.mk (i ⟶ j) < B.cutoff.ord.cof)
variable (hD : ∀ i, AlgebraicGeometry.IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    (hQc : ∀ i, AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS (D.obj i))
    (hQs : ∀ i, AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))

include hD hAffine hQc hQs

include hZ hD hAffine hQc hQs in
/-- The étale relation presenting an algebraic space of finite presentation over the
limit, once it is defined at a stage, becomes an étale equivalence relation at a later
stage, where it presents a finite-presentation model of the space. -/
private theorem exists_model_of_stage_relation_of_limitFacts
    (hFacts : LimitFacts B S hS D) (nn : I)
    (hLim : AlgebraicGeometry.IsAlgebraicSpace B S hS (limit D))
    (Y : Over (limit D)) (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y.left)
    {W KR : AlgebraicGeometry.BigFppfOver B S hS} (w : yoneda.obj W ⟶ Y.left)
    (hws : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf w)
    (hwe : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf w)
    (kt ks : KR ⟶ W) (hwk : IsPullback (yoneda.map kt) (yoneda.map ks) w w)
    {Wn Rn : AlgebraicGeometry.BigFppfOver B S hS}
    (hWnAff : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj Wn))
    (wn : yoneda.obj Wn ⟶ D.obj nn) (sn tn : Rn ⟶ Wn)
    (htn : yoneda.map tn ≫ wn = yoneda.map sn ≫ wn)
    (hsnEtale : Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map sn))
    (htnEtale : Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map tn))
    (hWnFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS wn)
    (hRnFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS (yoneda.map sn ≫ wn))
    (awn : W ⟶ Wn) (arn : KR ⟶ Rn)
    (hWnlim : IsPullback (yoneda.map awn) (w ≫ Y.hom) wn (limit.π D nn))
    (hRnlim : IsPullback (yoneda.map arn) (yoneda.map kt ≫ w ≫ Y.hom)
      (yoneda.map sn ≫ wn) (limit.π D nn))
    (hsnCompat : arn ≫ sn = kt ≫ awn) (htnCompat : arn ≫ tn = ks ≫ awn) :
    ∃ (i : I) (Yᵢ : Over (D.obj i)),
      AlgebraicGeometry.IsAlgebraicSpace B S hS Yᵢ.left ∧
        AlgebraicGeometry.Space.IsFinitePresentation B S hS Yᵢ.hom ∧
          Nonempty (Y ≅ (Over.pullback (limit.π D i)).obj Yᵢ) := by
  let Q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  set rn := yoneda.map sn ≫ wn with hrnDef
  set pW := w ≫ Y.hom with hpWDef
  set pR := yoneda.map kt ≫ pW with hpRDef
  have ht : yoneda.map kt ≫ pW = pR := rfl
  have hs : yoneda.map ks ≫ pW = pR := by
    simpa only [pR, pW, ← Category.assoc] using congrArg (fun z => z ≫ Y.hom) hwk.w.symm
  have hRnAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Rn
  have hWnAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wn
  let Rₙ := Over.mk rn
  let Wₙ := Over.mk wn
  let sₙ : Rₙ ⟶ Wₙ := Over.homMk (yoneda.map sn) rfl
  let tₙ : Rₙ ⟶ Wₙ := Over.homMk (yoneda.map tn) htn
  let sL : Over.mk pR ⟶ Over.mk pW := Over.homMk (yoneda.map kt) ht
  let tL : Over.mk pR ⟶ Over.mk pW := Over.homMk (yoneda.map ks) hs
  let F := Over.pullback (limit.π D nn)
  let εR : Over.mk pR ≅ F.obj Rₙ := Over.isoMk hRnlim.isoPullback hRnlim.isoPullback_hom_snd
  let εW : Over.mk pW ≅ F.obj Wₙ := Over.isoMk hWnlim.isoPullback hWnlim.isoPullback_hom_snd
  have hεs : εR.hom ≫ F.map sₙ = sL ≫ εW.hom := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simpa [F, εR, εW, sₙ, sL, Rₙ, Wₙ, Over.pullback_map_left,
        IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_fst_assoc,
        Category.assoc] using congrArg yoneda.map hsnCompat
    · simp [F, εR, εW, sₙ, sL, Rₙ, Wₙ, Over.pullback_map_left, Category.assoc, ht]
  have hεt : εR.hom ≫ F.map tₙ = tL ≫ εW.hom := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simpa [F, εR, εW, tₙ, tL, Rₙ, Wₙ, Over.pullback_map_left,
        IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_fst_assoc,
        Category.assoc] using congrArg yoneda.map htnCompat
    · simp [F, εR, εW, tₙ, tL, Rₙ, Wₙ, Over.pullback_map_left, Category.assoc, hs]
  let rL : Over.mk pW ⟶ Over.mk pR := Over.homMk
    (hwk.lift (𝟙 _) (𝟙 _) (by simp)) (by
      dsimp only [Over.mk_hom, Over.mk_left]
      rw [← ht, IsPullback.lift_fst_assoc, Category.id_comp])
  have hrLs : rL ≫ sL = 𝟙 _ := by ext; simp [rL, sL]
  have hrLt : rL ≫ tL = 𝟙 _ := by ext; simp [rL, tL]
  let rF := εW.inv ≫ rL ≫ εR.hom
  have hrF : ∀ (s : Rₙ ⟶ Wₙ) (sl : Over.mk pR ⟶ Over.mk pW),
      εR.hom ≫ F.map s = sl ≫ εW.hom → rL ≫ sl = 𝟙 _ → rF ≫ F.map s = F.map (𝟙 Wₙ) := by
    intro s sl h hr
    simp only [rF, Category.assoc, h, ← Category.assoc rL sl, hr, Category.id_comp,
      Iso.inv_hom_id]
    exact (F.map_id Wₙ).symm
  obtain ⟨ir, er', rr, hrrs, hrrt⟩ := exists_lift_pair_after_baseChange_of_limitFacts
    B S hS hZ D hD hAffine hQc hQs hFacts nn Wₙ Rₙ Wₙ
    hWnAlg hRnAlg hWnAlg hWnFp hRnFp hWnFp sₙ tₙ (𝟙 _) (𝟙 _) rF (hrF sₙ sL hεs hrLs)
    (hrF tₙ tL hεt hrLt)
  let invL : Over.mk pR ⟶ Over.mk pR := Over.homMk
    (hwk.lift (yoneda.map ks) (yoneda.map kt) hwk.w.symm) (by
      dsimp only [Over.mk_hom, Over.mk_left]
      rw [← ht, IsPullback.lift_fst_assoc, hs])
  have hiLs : invL ≫ sL = tL := by ext; simp [invL, sL, tL]
  have hiLt : invL ≫ tL = sL := by ext; simp [invL, sL, tL]
  let invF := εR.inv ≫ invL ≫ εR.hom
  have hiF : ∀ (s t : Rₙ ⟶ Wₙ) (sl tl : Over.mk pR ⟶ Over.mk pW),
      εR.hom ≫ F.map s = sl ≫ εW.hom → εR.hom ≫ F.map t = tl ≫ εW.hom → invL ≫ sl = tl →
        invF ≫ F.map s = F.map t := by
    intro s t sl tl hs' ht' hi
    simp only [invF, Category.assoc, hs', ← Category.assoc invL sl, hi]
    rw [← ht', Iso.inv_hom_id_assoc]
  obtain ⟨ii, ei, ri, hris, hrit⟩ := exists_lift_pair_after_baseChange_of_limitFacts
    B S hS hZ D hD hAffine hQc hQs hFacts nn Rₙ Rₙ Wₙ
    hRnAlg hRnAlg hWnAlg hRnFp hRnFp hWnFp sₙ tₙ tₙ sₙ invF (hiF sₙ tₙ sL tL hεs hεt hiLs)
    (hiF tₙ sₙ tL sL hεt hεs hiLt)
  let cn := overPullbackCone tₙ sₙ
  have hCAlg : AlgebraicGeometry.IsAlgebraicSpace B S hS cn.pt.left :=
    AlgebraicGeometry.isAlgebraicSpace_pullback B S hS tₙ.left sₙ.left hRnAlg hRnAlg hWnAlg
  have hsₙfp := isFinitePresentation_overHom B S hS hZ (hD nn) (hQc nn) (hQs nn)
    Rₙ Wₙ hRnAlg hWnAlg hRnFp hWnFp sₙ
  have hCfst := isFinitePresentation_of_isPullback B S hS hCAlg hRnAlg hRnAlg hWnAlg
    (IsPullback.of_hasPullback tₙ.left sₙ.left).flip hsₙfp
  have hCFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS cn.pt.hom :=
    AlgebraicGeometry.Space.isFinitePresentation_comp B S hS hCAlg hRnAlg (hD nn)
      (pullback.fst tₙ.left sₙ.left) rn hCfst hRnFp
  let ca : F.obj cn.pt ⟶ Over.mk pR := F.map cn.fst ≫ εR.inv
  let cb : F.obj cn.pt ⟶ Over.mk pR := F.map cn.snd ≫ εR.inv
  have hcab : ca ≫ tL = cb ≫ sL := by
    apply (cancel_mono εW.hom).mp
    simp only [ca, cb, Category.assoc]
    rw [← hεt, ← hεs, Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc,
      ← F.map_comp, ← F.map_comp, cn.condition]
  have hcabLeft : ca.left ≫ yoneda.map ks = cb.left ≫ yoneda.map kt :=
    congrArg (fun z => z.left) hcab
  have hcomp : (ca.left ≫ yoneda.map kt) ≫ w =
      (cb.left ≫ yoneda.map ks) ≫ w := by
    rw [Category.assoc, hwk.w, ← Category.assoc, hcabLeft,
      Category.assoc, hwk.w, Category.assoc]
  let compL : F.obj cn.pt ⟶ Over.mk pR := Over.homMk
    (hwk.lift (ca.left ≫ yoneda.map kt) (cb.left ≫ yoneda.map ks) hcomp)
    (by
      dsimp only [Over.mk_hom]
      calc hwk.lift (ca.left ≫ yoneda.map kt)
              (cb.left ≫ yoneda.map ks) hcomp ≫ pR
          = hwk.lift (ca.left ≫ yoneda.map kt)
              (cb.left ≫ yoneda.map ks) hcomp ≫ yoneda.map kt ≫ pW := by
            rw [ht]
        _ = (ca.left ≫ yoneda.map kt) ≫ pW := IsPullback.lift_fst_assoc _ _ _ _ _
        _ = ca.left ≫ pR := by rw [Category.assoc, ht]
        _ = (F.obj cn.pt).hom := ca.w)
  have hcompS : compL ≫ sL = ca ≫ sL := by ext; simp [compL, sL]
  have hcompT : compL ≫ tL = cb ≫ tL := by ext; simp [compL, tL]
  let compF := compL ≫ εR.hom
  have hcompF : ∀ (s : Rₙ ⟶ Wₙ) (sl : Over.mk pR ⟶ Over.mk pW) (c : cn.pt ⟶ Rₙ),
      εR.hom ≫ F.map s = sl ≫ εW.hom → compL ≫ sl = (F.map c ≫ εR.inv) ≫ sl →
        compF ≫ F.map s = F.map (c ≫ s) := by
    intro s sl c h hc
    simp only [compF]
    rw [Category.assoc, h, ← Category.assoc, hc]
    simp only [Category.assoc]
    rw [← h, Iso.inv_hom_id_assoc, F.map_comp]
  obtain ⟨ic, ec, rc, hrcs, hrct⟩ := exists_lift_pair_after_baseChange_of_limitFacts
    B S hS hZ D hD hAffine hQc hQs hFacts nn cn.pt Rₙ Wₙ
    hCAlg hRnAlg hWnAlg hCFp hRnFp hWnFp sₙ tₙ
    (cn.fst ≫ sₙ) (cn.snd ≫ tₙ) compF (hcompF sₙ sL cn.fst hεs hcompS)
    (hcompF tₙ tL cn.snd hεt hcompT)
  let KWn := atlasKernelPair B S hS wn (hD nn).diagonal_representable
  have hψcomm : yoneda.map sn ≫ wn = yoneda.map tn ≫ wn := htn.symm
  let ψ₀ : Rn ⟶ KWn.R := yoneda.preimage
    (KWn.kernelPair.lift (yoneda.map sn) (yoneda.map tn) hψcomm)
  have hψ₀ : yoneda.map ψ₀ =
      KWn.kernelPair.lift (yoneda.map sn) (yoneda.map tn) hψcomm := yoneda.map_preimage _
  have hψs : ψ₀ ≫ KWn.s = sn :=
    yoneda.map_injective (by rw [yoneda.map_comp, hψ₀]; exact KWn.kernelPair.lift_fst _ _ _)
  have hψt : ψ₀ ≫ KWn.t = tn :=
    yoneda.map_injective (by rw [yoneda.map_comp, hψ₀]; exact KWn.kernelPair.lift_snd _ _ _)
  let Zₙ : Over (D.obj nn) := Over.mk (yoneda.map KWn.s ≫ wn)
  let ψ : Rₙ ⟶ Zₙ := Over.homMk (yoneda.map ψ₀) (by
    show yoneda.map ψ₀ ≫ yoneda.map KWn.s ≫ wn = rn
    rw [← Category.assoc, ← yoneda.map_comp, hψs])
  have hZnAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS KWn.R
  have hKWnt : AlgebraicGeometry.Space.IsFinitePresentation B S hS (yoneda.map KWn.s) :=
    isFinitePresentation_of_isPullback B S hS hZnAlg hWnAlg hWnAlg (hD nn)
      KWn.kernelPair.flip hWnFp
  have hZnFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Zₙ.hom :=
    AlgebraicGeometry.Space.isFinitePresentation_comp B S hS hZnAlg hWnAlg (hD nn)
      (yoneda.map KWn.s) wn hKWnt hWnFp
  have hψfst : (F.map ψ).left ≫ pullback.fst Zₙ.hom (limit.π D nn) =
      pullback.fst rn (limit.π D nn) ≫ yoneda.map ψ₀ := by
    simp [F, Over.pullback_map_left, ψ, Rₙ]
  have hψsnd : (F.map ψ).left ≫ pullback.snd Zₙ.hom (limit.π D nn) =
      pullback.snd rn (limit.π D nn) := by
    simp [F, Over.pullback_map_left, ψ, Rₙ]
  have e₂ : (hRnlim.isoPullback.hom ≫ (F.map ψ).left) ≫
      pullback.snd Zₙ.hom (limit.π D nn) = pR := by
    rw [Category.assoc, hψsnd, hRnlim.isoPullback_hom_snd]
  have e₁ : (hRnlim.isoPullback.hom ≫ (F.map ψ).left) ≫
      pullback.fst Zₙ.hom (limit.π D nn) ≫ yoneda.map KWn.s =
      yoneda.map kt ≫ yoneda.map awn := by
    rw [Category.assoc, reassoc_of% hψfst, hRnlim.isoPullback_hom_fst_assoc,
      ← yoneda.map_comp ψ₀ KWn.s, hψs, ← yoneda.map_comp, hsnCompat,
      yoneda.map_comp]
  have e₁' : (hRnlim.isoPullback.hom ≫ (F.map ψ).left) ≫
      pullback.fst Zₙ.hom (limit.π D nn) ≫ yoneda.map KWn.t =
      yoneda.map ks ≫ yoneda.map awn := by
    rw [Category.assoc, reassoc_of% hψfst, hRnlim.isoPullback_hom_fst_assoc,
      ← yoneda.map_comp ψ₀ KWn.t, hψt, ← yoneda.map_comp, htnCompat,
      yoneda.map_comp]
  have hμ : Mono (hRnlim.isoPullback.hom ≫ (F.map ψ).left) := by
    refine ⟨fun {T} a b hab => ?_⟩
    have hab' : (a ≫ hRnlim.isoPullback.hom) ≫ (F.map ψ).left =
        (b ≫ hRnlim.isoPullback.hom) ≫ (F.map ψ).left := by
      simpa only [← Category.assoc] using hab
    refine hwk.hom_ext (hWnlim.hom_ext ?_ ?_) (hWnlim.hom_ext ?_ ?_)
    · rw [Category.assoc, Category.assoc, ← e₁]
      simp only [← Category.assoc]
      rw [hab']
    · rw [Category.assoc, Category.assoc, ht, ← e₂]
      simp only [← Category.assoc]
      rw [hab']
    · rw [Category.assoc, Category.assoc, ← e₁']
      simp only [← Category.assoc]
      rw [hab']
    · rw [Category.assoc, Category.assoc, hs, ← e₂]
      simp only [← Category.assoc]
      rw [hab']
  have hmonoψ : Mono ((Over.pullback (limit.π D nn)).map ψ) := by
    apply mono_of_mono_left
    have := hμ
    rw [show (F.map ψ).left = inv hRnlim.isoPullback.hom ≫
      (hRnlim.isoPullback.hom ≫ (F.map ψ).left) from by simp]
    infer_instance
  obtain ⟨jm, ejm, hjmMono⟩ := exists_mono_after_baseChange_of_limitFacts B S hS hZ D hD hAffine
    hQc hQs hFacts nn Rₙ Zₙ hRnAlg hZnAlg hRnFp hZnFp ψ
  -- a single stage carrying all of reflexivity, symmetry, transitivity and monicity
  let oo : Over nn := IsCofiltered.min
    (IsCofiltered.min (IsCofiltered.min (Over.mk er') (Over.mk ei)) (Over.mk ec))
    (Over.mk ejm)
  let aMono : oo ⟶ Over.mk ejm := IsCofiltered.minToRight _ _
  let aComp : oo ⟶ Over.mk ec :=
    IsCofiltered.minToLeft _ _ ≫ IsCofiltered.minToRight _ _
  let aRefl : oo ⟶ Over.mk er' :=
    IsCofiltered.minToLeft _ _ ≫ IsCofiltered.minToLeft _ _ ≫ IsCofiltered.minToLeft _ _
  let aSymm : oo ⟶ Over.mk ei :=
    IsCofiltered.minToLeft _ _ ≫ IsCofiltered.minToLeft _ _ ≫ IsCofiltered.minToRight _ _
  obtain ⟨rrO, hrrOs, hrrOt⟩ := exists_liftPair_of_comp (D.map er') (D.map aRefl.left)
    (D.map oo.hom) (by rw [← D.map_comp]; exact congrArg D.map (Over.w aRefl))
    sₙ tₙ (𝟙 Wₙ) (𝟙 Wₙ) rr hrrs hrrt
  obtain ⟨riO, hriOs, hriOt⟩ := exists_liftPair_of_comp (D.map ei) (D.map aSymm.left)
    (D.map oo.hom) (by rw [← D.map_comp]; exact congrArg D.map (Over.w aSymm))
    sₙ tₙ tₙ sₙ ri hris hrit
  obtain ⟨rcO, hrcOs, hrcOt⟩ := exists_liftPair_of_comp (D.map ec) (D.map aComp.left)
    (D.map oo.hom) (by rw [← D.map_comp]; exact congrArg D.map (Over.w aComp))
    sₙ tₙ (cn.fst ≫ sₙ) (cn.snd ≫ tₙ) rc hrcs hrct
  have hmonoO : Mono ((Over.pullback (D.map oo.hom)).map ψ) := by
    have := mono_overPullback_map (D.map aMono.left)
      ((Over.pullback (D.map ejm)).map ψ) hjmMono
    have hcomp' : D.map aMono.left ≫ D.map ejm = D.map oo.hom := by
      rw [← D.map_comp]; exact congrArg D.map (Over.w aMono)
    rw [show (Over.pullback (D.map oo.hom)).map ψ =
        (iteratedBaseChangeIso (D.map ejm) (D.map aMono.left) (D.map oo.hom)
            hcomp' Rₙ).inv ≫
          (Over.pullback (D.map aMono.left)).map ((Over.pullback (D.map ejm)).map ψ) ≫
          (iteratedBaseChangeIso (D.map ejm) (D.map aMono.left) (D.map oo.hom)
            hcomp' Zₙ).hom from by
      rw [iteratedBaseChangeIso_naturality, Iso.inv_hom_id_assoc]]
    infer_instance
  -- the descended relation as objects of the site
  have hoAff := ((AlgebraicGeometry.Space.isAffineHom_tfae_of_isAlgebraicSpace B S hS (D.map oo.hom)
    (hD oo.left) (hD nn)).out 2 1).mp (hAffine oo.hom)
  let WO := hoAff.1.pullback wn
  let RO := hoAff.1.pullback rn
  let wO := hoAff.1.fst wn
  let rO := hoAff.1.fst rn
  let bW : WO ⟶ Wn := hoAff.1.snd wn
  let bR : RO ⟶ Rn := hoAff.1.snd rn
  have hWO : IsPullback wO (yoneda.map bW) (D.map oo.hom) wn := hoAff.1.isPullback wn
  have hRO : IsPullback rO (yoneda.map bR) (D.map oo.hom) rn := hoAff.1.isPullback rn
  let εWO : Over.mk wO ≅ (Over.pullback (D.map oo.hom)).obj Wₙ :=
    Over.isoMk hWO.flip.isoPullback (by exact hWO.flip.isoPullback_hom_snd)
  let εRO : Over.mk rO ≅ (Over.pullback (D.map oo.hom)).obj Rₙ :=
    Over.isoMk hRO.flip.isoPullback (by exact hRO.flip.isoPullback_hom_snd)
  obtain ⟨sOO, hsOOdef⟩ : ∃ z : Over.mk rO ⟶ Over.mk wO,
      z = εRO.hom ≫ (Over.pullback (D.map oo.hom)).map sₙ ≫ εWO.inv := ⟨_, rfl⟩
  obtain ⟨tOO, htOOdef⟩ : ∃ z : Over.mk rO ⟶ Over.mk wO,
      z = εRO.hom ≫ (Over.pullback (D.map oo.hom)).map tₙ ≫ εWO.inv := ⟨_, rfl⟩
  let sO : RO ⟶ WO := yoneda.preimage sOO.left
  let tO : RO ⟶ WO := yoneda.preimage tOO.left
  have hsOl : yoneda.map sO = sOO.left := yoneda.map_preimage _
  have htOl : yoneda.map tO = tOO.left := yoneda.map_preimage _
  have hsOW : yoneda.map sO ≫ wO = rO := by rw [hsOl]; exact Over.w sOO
  have htOW : yoneda.map tO ≫ wO = rO := by rw [htOl]; exact Over.w tOO
  have hsOO : εRO.hom ≫ (Over.pullback (D.map oo.hom)).map sₙ = sOO ≫ εWO.hom := by
    rw [hsOOdef]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have htOO : εRO.hom ≫ (Over.pullback (D.map oo.hom)).map tₙ = tOO ≫ εWO.hom := by
    rw [htOOdef]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hεWfst : εWO.hom.left ≫ pullback.fst wn (D.map oo.hom) = yoneda.map bW :=
    hWO.flip.isoPullback_hom_fst
  have hεRfst : εRO.hom.left ≫ pullback.fst rn (D.map oo.hom) = yoneda.map bR :=
    hRO.flip.isoPullback_hom_fst
  have hsq : ∀ (s : Rₙ ⟶ Wₙ) (z : Over.mk rO ⟶ Over.mk wO),
      εRO.hom ≫ (Over.pullback (D.map oo.hom)).map s = z ≫ εWO.hom →
        z.left ≫ yoneda.map bW = yoneda.map bR ≫ s.left := by
    intro s z h
    have h2 := congrArg (fun z : Over.mk rO ⟶ (Over.pullback (D.map oo.hom)).obj Wₙ =>
      z.left ≫ pullback.fst wn (D.map oo.hom)) h
    simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, Rₙ, Wₙ,
      Over.mk_hom, pullback.lift_fst, hεWfst, reassoc_of% hεRfst] at h2
    exact h2.symm
  have hsoSq : sO ≫ bW = bR ≫ sn :=
    yoneda.map_injective (by rw [yoneda.map_comp, yoneda.map_comp, hsOl]; exact hsq sₙ sOO hsOO)
  have htoSq : tO ≫ bW = bR ≫ tn :=
    yoneda.map_injective (by rw [yoneda.map_comp, yoneda.map_comp, htOl]; exact hsq tₙ tOO htOO)
  have hsite : ∀ (n : Rn ⟶ Wn) (o : RO ⟶ WO), yoneda.map o ≫ wO = rO → o ≫ bW = bR ≫ n →
      yoneda.map n ≫ wn = rn → IsPullback bR o n bW := by
    intro n o ho hq hn
    apply IsPullback.of_map yoneda hq.symm
    apply IsPullback.of_bot (v₂₂ := wn) ?_
      (by rw [← yoneda.map_comp, ← yoneda.map_comp, hq]) hWO.flip
    rw [ho, hn]
    exact hRO.flip
  have hsoSite : IsPullback bR sO sn bW := hsite sn sO hsOW hsoSq rfl
  have htoSite : IsPullback bR tO tn bW := hsite tn tO htOW htoSq htn
  have hEtale : ∀ (n : Rn ⟶ Wn) (o : RO ⟶ WO), IsPullback bR o n bW → Etale (Q.map n) →
      Etale (Q.map o) := by
    intro n o h hn
    exact (etale_iff_pullback_of_isPullback (h.map Q)).mpr inferInstance
  have hsOEtale : Etale (Q.map sO) := hEtale sn sO hsoSite hsnEtale
  have htOEtale : Etale (Q.map tO) := hEtale tn tO htoSite htnEtale
  have hWOAff : IsAffine (Q.obj WO) := by
    let : IsAffine (Q.obj Wn) := hWnAff
    let : _root_.AlgebraicGeometry.IsAffineHom (Q.map bW) := hoAff.2.property wn wO bW hWO
    exact isAffine_of_isAffineHom (Q.map bW)
  have hWOAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS WO
  have hROAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS RO
  have hwOFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS wO :=
    isFinitePresentation_of_isPullback B S hS hWOAlg hWnAlg (hD oo.left) (hD nn)
      hWO.flip hWnFp
  have hrOFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS rO :=
    isFinitePresentation_of_isPullback B S hS hROAlg hRnAlg (hD oo.left) (hD nn)
      hRO.flip hRnFp
  have hROqc := AlgebraicGeometry.Space.isQuasiCompactSpace_of_isFinitePresentation B S hS rO
    (hD oo.left) (hQc oo.left) hrOFp
  -- reflexivity, symmetry and transitivity of the descended relation
  obtain ⟨rflO, hrflOdef⟩ : ∃ z : Over.mk wO ⟶ Over.mk rO, z = εWO.hom ≫ rrO ≫ εRO.inv :=
    ⟨_, rfl⟩
  have hrflS : rflO ≫ sOO = 𝟙 (Over.mk wO) := by
    rw [hrflOdef, hsOOdef]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hrrOs]
    rw [show (Over.pullback (D.map oo.hom)).map (𝟙 Wₙ) = 𝟙 _ from
      (Over.pullback (D.map oo.hom)).map_id Wₙ, Category.id_comp, Iso.hom_inv_id]
  have hrflT : rflO ≫ tOO = 𝟙 (Over.mk wO) := by
    rw [hrflOdef, htOOdef]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hrrOt]
    rw [show (Over.pullback (D.map oo.hom)).map (𝟙 Wₙ) = 𝟙 _ from
      (Over.pullback (D.map oo.hom)).map_id Wₙ, Category.id_comp, Iso.hom_inv_id]
  obtain ⟨symO, hsymOdef⟩ : ∃ z : Over.mk rO ⟶ Over.mk rO, z = εRO.hom ≫ riO ≫ εRO.inv :=
    ⟨_, rfl⟩
  have hsymS : symO ≫ sOO = tOO := by
    rw [hsymOdef, hsOOdef, htOOdef]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hriOs]
  have hsymT : symO ≫ tOO = sOO := by
    rw [hsymOdef, htOOdef, hsOOdef]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hriOt]
  let rflSite : WO ⟶ RO := yoneda.preimage rflO.left
  have hrflSite₁ : rflSite ≫ sO = 𝟙 WO :=
    yoneda.map_injective (by
      simpa [rflSite, hsOl, htOl] using congrArg (fun z => z.left) hrflS)
  have hrflSite₂ : rflSite ≫ tO = 𝟙 WO :=
    yoneda.map_injective (by
      simpa [rflSite, hsOl, htOl] using congrArg (fun z => z.left) hrflT)
  let symSite : RO ⟶ RO := yoneda.preimage symO.left
  have hsymSite₁ : symSite ≫ sO = tO :=
    yoneda.map_injective (by
      simpa [symSite, hsOl, htOl] using congrArg (fun z => z.left) hsymS)
  have hsymSite₂ : symSite ≫ tO = sO :=
    yoneda.map_injective (by
      simpa [symSite, hsOl, htOl] using congrArg (fun z => z.left) hsymT)
  have hpoCond : yoneda.map (pullback.fst tO sO) ≫ yoneda.map tO =
      yoneda.map (pullback.snd tO sO) ≫ yoneda.map sO := by
    rw [← yoneda.map_comp, ← yoneda.map_comp, pullback.condition]
  let Pₒ : Over (D.obj oo.left) := Over.mk (yoneda.map (pullback.fst tO sO) ≫ rO)
  let cfstₒ : Pₒ ⟶ Over.mk rO := Over.homMk (yoneda.map (pullback.fst tO sO)) rfl
  let csndₒ : Pₒ ⟶ Over.mk rO := Over.homMk (yoneda.map (pullback.snd tO sO)) (by
    show yoneda.map (pullback.snd tO sO) ≫ rO = yoneda.map (pullback.fst tO sO) ≫ rO
    calc yoneda.map (pullback.snd tO sO) ≫ rO
        = yoneda.map (pullback.snd tO sO) ≫ yoneda.map sO ≫ wO := by rw [hsOW]
      _ = yoneda.map (pullback.fst tO sO) ≫ yoneda.map tO ≫ wO := by
            rw [← Category.assoc, ← Category.assoc, ← hpoCond]
      _ = yoneda.map (pullback.fst tO sO) ≫ rO := by rw [htOW])
  have hcommₒ : cfstₒ ≫ tOO = csndₒ ≫ sOO := by
    apply Over.OverMorphism.ext
    simpa only [Over.comp_left, cfstₒ, csndₒ, Over.homMk_left, hsOl, htOl] using hpoCond
  have hPₒ : IsPullback cfstₒ csndₒ tOO sOO := by
    apply IsPullback.of_map (Over.forget (D.obj oo.left)) hcommₒ
    rw [show ((Over.forget (D.obj oo.left)).map tOO) = yoneda.map tO from htOl.symm,
      show ((Over.forget (D.obj oo.left)).map sOO) = yoneda.map sO from hsOl.symm]
    exact (IsPullback.of_hasPullback tO sO).map yoneda
  have hpbcn : IsPullback ((Over.pullback (D.map oo.hom)).map cn.fst)
      ((Over.pullback (D.map oo.hom)).map cn.snd)
      ((Over.pullback (D.map oo.hom)).map tₙ)
      ((Over.pullback (D.map oo.hom)).map sₙ) :=
    (overPullbackCone_isPullback tₙ sₙ).map (Over.pullback (D.map oo.hom))
  let ζ : Pₒ ⟶ (Over.pullback (D.map oo.hom)).obj cn.pt :=
    hpbcn.lift (cfstₒ ≫ εRO.hom) (csndₒ ≫ εRO.hom) (by
      simpa only [Category.assoc, ← htOO, ← hsOO] using
        congrArg (fun z : Pₒ ⟶ Over.mk wO => z ≫ εWO.hom) hcommₒ)
  have hζfst : ζ ≫ (Over.pullback (D.map oo.hom)).map cn.fst = cfstₒ ≫ εRO.hom :=
    hpbcn.lift_fst _ _ _
  have hζsnd : ζ ≫ (Over.pullback (D.map oo.hom)).map cn.snd = csndₒ ≫ εRO.hom :=
    hpbcn.lift_snd _ _ _
  obtain ⟨cmpO, hcmpOdef⟩ : ∃ z : Pₒ ⟶ Over.mk rO, z = ζ ≫ rcO ≫ εRO.inv := ⟨_, rfl⟩
  have hcmpS : cmpO ≫ sOO = cfstₒ ≫ sOO := by
    rw [hcmpOdef, hsOOdef]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hrcOs,
      Functor.map_comp, reassoc_of% hζfst]
  have hcmpT : cmpO ≫ tOO = csndₒ ≫ tOO := by
    rw [hcmpOdef, htOOdef]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hrcOt,
      Functor.map_comp, reassoc_of% hζsnd]
  let cmpSite : pullback tO sO ⟶ RO := yoneda.preimage cmpO.left
  have hcmpSite₁ : cmpSite ≫ sO = pullback.fst tO sO ≫ sO :=
    yoneda.map_injective (by
      simpa [cmpSite, hsOl, htOl, cfstₒ] using congrArg (fun z => z.left) hcmpS)
  have hcmpSite₂ : cmpSite ≫ tO = pullback.snd tO sO ≫ tO :=
    yoneda.map_injective (by
      simpa [cmpSite, hsOl, htOl, csndₒ] using congrArg (fun z => z.left) hcmpT)
  -- the atlas of the space compared with the descended relation
  let awO : W ⟶ WO := yoneda.preimage (hWO.flip.lift (yoneda.map awn)
    (pW ≫ limit.π D oo.left) (by rw [Category.assoc, limit.w]; exact hWnlim.w))
  let arO : KR ⟶ RO := yoneda.preimage (hRO.flip.lift (yoneda.map arn)
    (pR ≫ limit.π D oo.left) (by rw [Category.assoc, limit.w]; exact hRnlim.w))
  have hWOlim : IsPullback (yoneda.map awO) pW wO (limit.π D oo.left) := by
    have hh : IsPullback (yoneda.map awn) pW wn (limit.π D oo.left ≫ D.map oo.hom) := by
      rw [limit.w]
      exact hWnlim
    simpa only [awO, yoneda.map_preimage] using hh.of_right' hWO.flip
  have hROlim : IsPullback (yoneda.map arO) pR rO (limit.π D oo.left) := by
    have hh : IsPullback (yoneda.map arn) pR rn (limit.π D oo.left ≫ D.map oo.hom) := by
      rw [limit.w]
      exact hRnlim
    simpa only [arO, yoneda.map_preimage] using hh.of_right' hRO.flip
  have hawOb : awO ≫ bW = awn := by
    apply yoneda.map_injective
    simp [awO]
  have harOb : arO ≫ bR = arn := by
    apply yoneda.map_injective
    simp [arO]
  have hsqO : ∀ (n : Rn ⟶ Wn) (o : RO ⟶ WO) (k : KR ⟶ W), yoneda.map o ≫ wO = rO →
      o ≫ bW = bR ≫ n → yoneda.map k ≫ pW = pR → arn ≫ n = k ≫ awn → IsPullback arO k o awO := by
    intro n o k ho hq hk hc
    have hcompat : arO ≫ o = k ≫ awO := by
      apply yoneda.map_injective
      apply hWO.hom_ext
      · rw [yoneda.map_comp, yoneda.map_comp, Category.assoc, Category.assoc, ho,
          hWOlim.w, hROlim.w, ← Category.assoc, hk]
      · rw [yoneda.map_comp, yoneda.map_comp, Category.assoc, Category.assoc,
          ← yoneda.map_comp o bW, ← yoneda.map_comp awO bW, hq, hawOb, yoneda.map_comp,
          ← Category.assoc, ← yoneda.map_comp arO bR, harOb, ← yoneda.map_comp, hc,
          yoneda.map_comp]
    apply IsPullback.of_map yoneda hcompat
    apply IsPullback.of_bot _
      (by simpa only [Functor.map_comp] using congrArg yoneda.map hcompat) hWOlim
    simpa only [hk, ho] using hROlim
  have hsqsO : IsPullback arO kt sO awO := hsqO sn sO kt hsOW hsoSq ht hsnCompat
  have hsqtO : IsPullback arO ks tO awO := hsqO tn tO ks htOW htoSq hs htnCompat
  -- joint monicity of the descended relation
  have hρcomm : yoneda.map sO ≫ wO = yoneda.map tO ≫ wO := by rw [hsOW, htOW]
  let KWO := atlasKernelPair B S hS wO (hD oo.left).diagonal_representable
  let ρ : RO ⟶ KWO.R := yoneda.preimage
    (KWO.kernelPair.lift (yoneda.map sO) (yoneda.map tO) hρcomm)
  have hρl : yoneda.map ρ =
      KWO.kernelPair.lift (yoneda.map sO) (yoneda.map tO) hρcomm := yoneda.map_preimage _
  have hρs : ρ ≫ KWO.s = sO :=
    yoneda.map_injective (by rw [yoneda.map_comp, hρl]; exact KWO.kernelPair.lift_fst _ _ _)
  have hρt : ρ ≫ KWO.t = tO :=
    yoneda.map_injective (by rw [yoneda.map_comp, hρl]; exact KWO.kernelPair.lift_snd _ _ _)
  have _ : IsIso εRO.hom.left :=
    inferInstanceAs (IsIso ((Over.forget (D.obj oo.left)).map εRO.hom))
  have hνmono : Mono (εRO.hom.left ≫
      ((Over.pullback (D.map oo.hom)).map ψ).left) := by
    have := mono_left_of_mono _ hmonoO
    infer_instance
  have hνfst : εRO.hom.left ≫ ((Over.pullback (D.map oo.hom)).map ψ).left ≫
      pullback.fst Zₙ.hom (D.map oo.hom) = yoneda.map bR ≫ yoneda.map ψ₀ := by
    simp only [Over.pullback_map_left, Rₙ, Over.mk_hom,
      pullback.lift_fst, ψ, Over.homMk_left, reassoc_of% hεRfst]
  have hνsnd : εRO.hom.left ≫ ((Over.pullback (D.map oo.hom)).map ψ).left ≫
      pullback.snd Zₙ.hom (D.map oo.hom) = rO := by
    simp only [Over.pullback_map_left, pullback.lift_snd]
    exact εRO.hom.w
  have hρmono : Mono (yoneda.map ρ) := by
    refine ⟨fun {T} a b hab => ?_⟩
    have ha : a ≫ yoneda.map sO = b ≫ yoneda.map sO := by
      rw [← hρs, yoneda.map_comp]
      simp only [← Category.assoc]
      rw [hab]
    have hb : a ≫ yoneda.map tO = b ≫ yoneda.map tO := by
      rw [← hρt, yoneda.map_comp]
      simp only [← Category.assoc]
      rw [hab]
    apply (cancel_mono (εRO.hom.left ≫ ((Over.pullback (D.map oo.hom)).map ψ).left)).mp
    apply pullback.hom_ext
    · simp only [Category.assoc, hνfst]
      apply KWn.kernelPair.hom_ext
      · simp only [Category.assoc, ← yoneda.map_comp ψ₀ KWn.s, hψs,
          ← yoneda.map_comp bR sn, ← hsoSq, yoneda.map_comp]
        simp only [← Category.assoc]
        rw [ha]
      · simp only [Category.assoc, ← yoneda.map_comp ψ₀ KWn.t, hψt,
          ← yoneda.map_comp bR tn, ← htoSq, yoneda.map_comp]
        simp only [← Category.assoc]
        rw [hb]
    · simp only [Category.assoc, hνsnd]
      rw [← hsOW]
      simp only [← Category.assoc]
      rw [ha]
  have hjmO : JointlyMono₂ ((Over.post (X := B.obj hS) B.inclusion).map sO)
      ((Over.post (X := B.obj hS) B.inclusion).map tO) :=
    jointlyMono₂_of_mono_to_kernelPair B S hS wO KWO.s KWO.t KWO.kernelPair
      sO tO ρ hρs hρt hρmono
  obtain ⟨Yᵢ, hYᵢalg, hYᵢfp, hYᵢiso⟩ := exists_model_of_descended_presentation
    B S hS hZ D oo.left hLim (hD oo.left) (hQc oo.left) (hQs oo.left) Y hY w hws hwe
    kt ks hwk hWOAff sO tO hsOEtale htOEtale hjmO rflSite hrflSite₁ hrflSite₂
    symSite hsymSite₁ hsymSite₂ cmpSite hcmpSite₁ hcmpSite₂ wO hρcomm hwOFp hROqc
    awO arO (by rw [← hpWDef]; exact hWOlim) hsqsO hsqtO
  exact ⟨oo.left, Yᵢ, hYᵢalg, hYᵢfp, hYᵢiso⟩

end AlgebraicGeometry.Space

end
