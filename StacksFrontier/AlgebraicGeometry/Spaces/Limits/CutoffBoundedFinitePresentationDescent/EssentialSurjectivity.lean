module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.CutoffBoundedSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent
import all StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent
import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative
import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.Separated
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.CutoffBoundedFinitePresentationDescent.AffineCharts
import all StacksFrontier.AlgebraicGeometry.Spaces.Limits.CutoffBoundedFinitePresentationDescent.AffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.CutoffBoundedFinitePresentationDescent.FullyFaithful
import all StacksFrontier.AlgebraicGeometry.Spaces.Limits.CutoffBoundedFinitePresentationDescent.FullyFaithful

/-!
# Essential surjectivity of the base change to a limit bounded by the cutoff

This is the essential surjectivity of Stacks 07SK, for a cofiltered inverse system of
quasi-compact, absolutely quasi-separated algebraic spaces with affine transition morphisms
satisfying `AlgebraicGeometry.Space.IsCutoffBoundedSystem` in place of the bound of the index
category by the cofinality of the cutoff which the registered forms in
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent` ask for.

Its main step passes from an étale relation presenting an algebraic space of finite presentation
over the limit, once it is defined at a stage, to an étale equivalence relation at a later stage,
where it presents a finite-presentation model of the space. It uses the fullness and faithfulness
proved in the `FullyFaithful` part of this split.

## Main results

* `AlgebraicGeometry.Space.IsCutoffBoundedSystem.exists_model_of_finitePresentation`:
  essential surjectivity.

Nothing here is registered: Stacks 07SK is registered on the forms bounded by the cofinality.

## References

* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local simp] pullback.lift_fst pullback.lift_snd
  pullback.lift_fst_assoc pullback.lift_snd_assoc

namespace IsCutoffBoundedSystem

/-- A pullback square over a stage, compared with the cartesian square of a transition map, is
induced by a morphism of the representable sources, which is again a pullback over the earlier
stage. -/
private theorem exists_isPullback_comparison {C E : Type*} [Category* C] [Category* E]
    (F : C ⥤ E) [F.Full] [F.Faithful] {X Wj Wl : C} {Dl Dj L : E}
    {wl : F.obj Wl ⟶ Dl} {wj : F.obj Wj ⟶ Dj} {g : Dl ⟶ Dj} {q : L ⟶ Dl} {r : L ⟶ Dj}
    {b : Wl ⟶ Wj} {a : F.obj X ⟶ F.obj Wj} {p : F.obj X ⟶ L}
    (hb : IsPullback (F.map b) wl wj g) (hq : q ≫ g = r) (h : IsPullback a p wj r) :
    ∃ c : X ⟶ Wl, F.map c ≫ F.map b = a ∧ IsPullback (F.map c) p wl q := by
  subst hq
  refine ⟨F.preimage (hb.lift a (p ≫ q) (by rw [h.w, Category.assoc])), ?_, ?_⟩
  · simp
  · simpa only [F.map_preimage] using h.of_right' hb

/-- A commuting square of representable objects is a pullback as soon as it is one after
composing with the pullback square `hW` over the same base. -/
private theorem isPullback_of_isPullback_over {C E : Type*} [Category* C] [Category* E]
    (F : C ⥤ E) [F.Full] [F.Faithful] {P X Y Z : C} {Dw L : E} {u : P ⟶ X} {v : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} {wZ : F.obj Z ⟶ Dw} {wX : F.obj X ⟶ Dw} {pY : F.obj Y ⟶ L}
    {pP : F.obj P ⟶ L} {π : L ⟶ Dw} (hcomm : u ≫ f = v ≫ g)
    (hW : IsPullback (F.map g) pY wZ π) (hv : F.map v ≫ pY = pP) (hf : F.map f ≫ wZ = wX)
    (hP : IsPullback (F.map u) pP wX π) : IsPullback u v f g := by
  subst hv hf
  refine IsPullback.of_map F hcomm (IsPullback.of_bot hP ?_ hW)
  rw [← F.map_comp, ← F.map_comp, hcomm]

/-- A pair of morphisms with equal composites to an atlas factors through the kernel pair. -/
private theorem exists_comp_eq_atlasKernelPair (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U T : AlgebraicGeometry.BigFppfOver B S hS} {q : yoneda.obj U ⟶ F}
    (K : AtlasKernelPair B S hS q) (s t : T ⟶ U) (h : yoneda.map s ≫ q = yoneda.map t ≫ q) :
    ∃ ψ : T ⟶ K.R, ψ ≫ K.s = s ∧ ψ ≫ K.t = t :=
  ⟨yoneda.preimage (K.kernelPair.lift (yoneda.map s) (yoneda.map t) h),
    yoneda.map_injective (by simp), yoneda.map_injective (by simp)⟩

/-- Finite presentation of a morphism descends along a pullback square of representables. -/
private theorem isFinitePresentation_of_isPullback_yoneda
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    (hZ : AlgebraicGeometry.IsAlgebraicSpace B S hS Z)
    {W X : AlgebraicGeometry.BigFppfOver B S hS} {a : yoneda.obj W ⟶ yoneda.obj X}
    {b : yoneda.obj W ⟶ Y} {f : yoneda.obj X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback a b f g)
    (hf : AlgebraicGeometry.Space.IsFinitePresentation B S hS f) :
    AlgebraicGeometry.Space.IsFinitePresentation B S hS b :=
  isFinitePresentation_of_isPullback B S hS (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS W)
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS X) hY hZ h hf

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable (hZ : B.Contains (⊤_ Scheme.{u}))
variable {I : Type u} [Category.{u} I] [IsCofiltered I]
variable (D : I ⥤ (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
variable (hD : ∀ i, AlgebraicGeometry.IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    (hQc : ∀ i, AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS (D.obj i))
    (hQs : ∀ i, AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))

include hD hAffine hQc hQs

/-- The étale relation presenting an algebraic space of finite presentation over the
limit, once it is defined at a stage, becomes an étale equivalence relation at a later
stage, where it presents a finite-presentation model of the space. -/
private theorem exists_model_of_stage_relation
    (hConv : IsCutoffBoundedSystem B S hS D) (nn : I)
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
  let εR : Over.mk pR ≅ (Over.pullback (limit.π D nn)).obj Rₙ :=
    Over.isoMk hRnlim.isoPullback hRnlim.isoPullback_hom_snd
  let εW : Over.mk pW ≅ (Over.pullback (limit.π D nn)).obj Wₙ :=
    Over.isoMk hWnlim.isoPullback hWnlim.isoPullback_hom_snd
  have hεs : εR.hom ≫ (Over.pullback (limit.π D nn)).map sₙ = sL ≫ εW.hom := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simpa [εR, εW, sₙ, sL, Rₙ, Wₙ, Over.pullback_map_left,
        IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_fst_assoc,
        Category.assoc] using congrArg yoneda.map hsnCompat
    · simp [εR, εW, sₙ, sL, Rₙ, Wₙ, Over.pullback_map_left, Category.assoc, ht]
  have hεt : εR.hom ≫ (Over.pullback (limit.π D nn)).map tₙ = tL ≫ εW.hom := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simpa [εR, εW, tₙ, tL, Rₙ, Wₙ, Over.pullback_map_left,
        IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_fst_assoc,
        Category.assoc] using congrArg yoneda.map htnCompat
    · simp [εR, εW, tₙ, tL, Rₙ, Wₙ, Over.pullback_map_left, Category.assoc, hs]
  let rL : Over.mk pW ⟶ Over.mk pR := Over.homMk
    (hwk.lift (𝟙 _) (𝟙 _) (by simp)) (by
      dsimp only [Over.mk_hom, Over.mk_left]
      rw [← ht, IsPullback.lift_fst_assoc, Category.id_comp])
  have hrLs : rL ≫ sL = 𝟙 _ := by ext; simp [rL, sL]
  have hrLt : rL ≫ tL = 𝟙 _ := by ext; simp [rL, tL]
  let rF := εW.inv ≫ rL ≫ εR.hom
  have hrFs : rF ≫ (Over.pullback (limit.π D nn)).map sₙ =
      (Over.pullback (limit.π D nn)).map (𝟙 Wₙ) := by
    simp only [rF, Category.assoc, hεs, ← Category.assoc rL sL, hrLs,
      Category.id_comp, Iso.inv_hom_id]
    exact ((Over.pullback (limit.π D nn)).map_id Wₙ).symm
  have hrFt : rF ≫ (Over.pullback (limit.π D nn)).map tₙ =
      (Over.pullback (limit.π D nn)).map (𝟙 Wₙ) := by
    simp only [rF, Category.assoc, hεt, ← Category.assoc rL tL, hrLt,
      Category.id_comp, Iso.inv_hom_id]
    exact ((Over.pullback (limit.π D nn)).map_id Wₙ).symm
  obtain ⟨ir, er', rr, hrrs, hrrt⟩ := exists_lift_pair_after_baseChange
    B S hS hZ D hD hAffine hQc hQs hConv nn Wₙ Rₙ Wₙ
    hWnAlg hRnAlg hWnAlg hWnFp hRnFp hWnFp sₙ tₙ (𝟙 _) (𝟙 _) rF hrFs hrFt
  let invL : Over.mk pR ⟶ Over.mk pR := Over.homMk
    (hwk.lift (yoneda.map ks) (yoneda.map kt) hwk.w.symm) (by
      dsimp only [Over.mk_hom, Over.mk_left]
      rw [← ht, IsPullback.lift_fst_assoc, hs])
  have hiLs : invL ≫ sL = tL := by ext; simp [invL, sL, tL]
  have hiLt : invL ≫ tL = sL := by ext; simp [invL, sL, tL]
  let invF := εR.inv ≫ invL ≫ εR.hom
  have hiFs : invF ≫ (Over.pullback (limit.π D nn)).map sₙ =
      (Over.pullback (limit.π D nn)).map tₙ := by
    simp only [invF, Category.assoc, hεs, ← Category.assoc invL sL, hiLs]
    rw [← hεt, Iso.inv_hom_id_assoc]
  have hiFt : invF ≫ (Over.pullback (limit.π D nn)).map tₙ =
      (Over.pullback (limit.π D nn)).map sₙ := by
    simp only [invF, Category.assoc, hεt, ← Category.assoc invL tL, hiLt]
    rw [← hεs, Iso.inv_hom_id_assoc]
  obtain ⟨ii, ei, ri, hris, hrit⟩ := exists_lift_pair_after_baseChange
    B S hS hZ D hD hAffine hQc hQs hConv nn Rₙ Rₙ Wₙ
    hRnAlg hRnAlg hWnAlg hRnFp hRnFp hWnFp sₙ tₙ tₙ sₙ invF hiFs hiFt
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
  let F := Over.pullback (limit.π D nn)
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
  have hcompFs : compF ≫ F.map sₙ = F.map (cn.fst ≫ sₙ) := by
    simp only [compF]
    rw [Category.assoc, hεs, ← Category.assoc, hcompS]
    simp only [ca, Category.assoc]
    rw [← hεs, Iso.inv_hom_id_assoc, F.map_comp]
  have hcompFt : compF ≫ F.map tₙ = F.map (cn.snd ≫ tₙ) := by
    simp only [compF]
    rw [Category.assoc, hεt, ← Category.assoc, hcompT]
    simp only [cb, Category.assoc]
    rw [← hεt, Iso.inv_hom_id_assoc, F.map_comp]
  obtain ⟨ic, ec, rc, hrcs, hrct⟩ := exists_lift_pair_after_baseChange
    B S hS hZ D hD hAffine hQc hQs hConv nn cn.pt Rₙ Wₙ
    hCAlg hRnAlg hWnAlg hCFp hRnFp hWnFp sₙ tₙ
    (cn.fst ≫ sₙ) (cn.snd ≫ tₙ) compF hcompFs hcompFt
  let KWn := atlasKernelPair B S hS wn (hD nn).diagonal_representable
  obtain ⟨ψ₀, hψs, hψt⟩ := exists_comp_eq_atlasKernelPair B S hS KWn sn tn htn.symm
  let Zₙ : Over (D.obj nn) := Over.mk (yoneda.map KWn.s ≫ wn)
  let ψ : Rₙ ⟶ Zₙ := Over.homMk (yoneda.map ψ₀) (by
    show yoneda.map ψ₀ ≫ yoneda.map KWn.s ≫ wn = rn
    rw [← Category.assoc, ← yoneda.map_comp, hψs])
  have hZnAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS KWn.R
  have hKWnt : AlgebraicGeometry.Space.IsFinitePresentation B S hS (yoneda.map KWn.s) :=
    isFinitePresentation_of_isPullback_yoneda B S hS hWnAlg (hD nn) KWn.kernelPair.flip hWnFp
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
  obtain ⟨jm, ejm, hjmMono⟩ := exists_mono_after_baseChange B S hS hZ D hD hAffine
    hQc hQs hConv nn Rₙ Zₙ hRnAlg hZnAlg hRnFp hZnFp ψ
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
    Over.isoMk hWO.flip.isoPullback hWO.flip.isoPullback_hom_snd
  let εRO : Over.mk rO ≅ (Over.pullback (D.map oo.hom)).obj Rₙ :=
    Over.isoMk hRO.flip.isoPullback hRO.flip.isoPullback_hom_snd
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
  have hεWfst : εWO.hom.left ≫ pullback.fst wn (D.map oo.hom) = yoneda.map bW :=
    hWO.flip.isoPullback_hom_fst
  have hεRfst : εRO.hom.left ≫ pullback.fst rn (D.map oo.hom) = yoneda.map bR :=
    hRO.flip.isoPullback_hom_fst
  have hsOO : εRO.hom ≫ (Over.pullback (D.map oo.hom)).map sₙ = sOO ≫ εWO.hom := by
    rw [hsOOdef]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have htOO : εRO.hom ≫ (Over.pullback (D.map oo.hom)).map tₙ = tOO ≫ εWO.hom := by
    rw [htOOdef]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hsoSq : sO ≫ bW = bR ≫ sn := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, yoneda.map_comp, hsOl]
    have h2 := congrArg (fun z : Over.mk rO ⟶ (Over.pullback (D.map oo.hom)).obj Wₙ =>
      z.left ≫ pullback.fst wn (D.map oo.hom)) hsOO.symm
    simpa only [Over.comp_left, Category.assoc, Over.pullback_map_left, Rₙ, Wₙ,
      Over.mk_hom, pullback.lift_fst, hεWfst, reassoc_of% hεRfst, sₙ,
      Over.homMk_left] using h2
  have htoSq : tO ≫ bW = bR ≫ tn := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, yoneda.map_comp, htOl]
    have h2 := congrArg (fun z : Over.mk rO ⟶ (Over.pullback (D.map oo.hom)).obj Wₙ =>
      z.left ≫ pullback.fst wn (D.map oo.hom)) htOO.symm
    simpa only [Over.comp_left, Category.assoc, Over.pullback_map_left, Rₙ, Wₙ,
      Over.mk_hom, pullback.lift_fst, hεWfst, reassoc_of% hεRfst, tₙ,
      Over.homMk_left] using h2
  have hsoSite : IsPullback bR sO sn bW := by
    apply IsPullback.of_map yoneda hsoSq.symm
    apply IsPullback.of_bot (v₂₂ := wn) ?_
      (by rw [← yoneda.map_comp, ← yoneda.map_comp, hsoSq]) hWO.flip
    rw [hsOW]
    exact hRO.flip
  have htoSite : IsPullback bR tO tn bW := by
    apply IsPullback.of_map yoneda htoSq.symm
    apply IsPullback.of_bot (v₂₂ := wn) ?_
      (by rw [← yoneda.map_comp, ← yoneda.map_comp, htoSq]) hWO.flip
    rw [htOW, htn]
    exact hRO.flip
  have hsOEtale : Etale (Q.map sO) := by
    let : Etale (Q.map sn) := hsnEtale
    exact (etale_iff_pullback_of_isPullback (hsoSite.map Q)).mpr inferInstance
  have htOEtale : Etale (Q.map tO) := by
    let : Etale (Q.map tn) := htnEtale
    exact (etale_iff_pullback_of_isPullback (htoSite.map Q)).mpr inferInstance
  have hWOAff : IsAffine (Q.obj WO) := by
    let : IsAffine (Q.obj Wn) := hWnAff
    let : _root_.AlgebraicGeometry.IsAffineHom (Q.map bW) := hoAff.2.property wn wO bW hWO
    exact isAffine_of_isAffineHom (Q.map bW)
  have hwOFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS wO :=
    isFinitePresentation_of_isPullback_yoneda B S hS (hD oo.left) (hD nn) hWO.flip hWnFp
  have hrOFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS rO :=
    isFinitePresentation_of_isPullback_yoneda B S hS (hD oo.left) (hD nn) hRO.flip hRnFp
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
  have hrflSite₁ : rflSite ≫ sO = 𝟙 WO := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, yoneda.map_preimage, hsOl, yoneda.map_id]
    simpa only [Over.comp_left, Over.id_left, Over.mk_left] using
      congrArg (fun z => z.left) hrflS
  have hrflSite₂ : rflSite ≫ tO = 𝟙 WO := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, yoneda.map_preimage, htOl, yoneda.map_id]
    simpa only [Over.comp_left, Over.id_left, Over.mk_left] using
      congrArg (fun z => z.left) hrflT
  let symSite : RO ⟶ RO := yoneda.preimage symO.left
  have hsymSite₁ : symSite ≫ sO = tO := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, yoneda.map_preimage, hsOl, htOl]
    simpa only [Over.comp_left] using congrArg (fun z => z.left) hsymS
  have hsymSite₂ : symSite ≫ tO = sO := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, yoneda.map_preimage, htOl, hsOl]
    simpa only [Over.comp_left] using congrArg (fun z => z.left) hsymT
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
  have hcmpSite₁ : cmpSite ≫ sO = pullback.fst tO sO ≫ sO := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, yoneda.map_comp, yoneda.map_preimage, hsOl]
    simpa only [Over.comp_left, cfstₒ, Over.homMk_left] using
      congrArg (fun z => z.left) hcmpS
  have hcmpSite₂ : cmpSite ≫ tO = pullback.snd tO sO ≫ tO := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, yoneda.map_comp, yoneda.map_preimage, htOl]
    simpa only [Over.comp_left, csndₒ, Over.homMk_left] using
      congrArg (fun z => z.left) hcmpT
  -- the atlas of the space compared with the descended relation
  obtain ⟨awO, hawOb, hWOlim⟩ :=
    exists_isPullback_comparison yoneda hWO.flip (limit.w D oo.hom) hWnlim
  obtain ⟨arO, harOb, hROlim⟩ :=
    exists_isPullback_comparison yoneda hRO.flip (limit.w D oo.hom) hRnlim
  have hsOCompat : arO ≫ sO = kt ≫ awO := by
    apply yoneda.map_injective
    apply hWO.hom_ext
    · rw [yoneda.map_comp, yoneda.map_comp, Category.assoc, Category.assoc, hsOW,
        hWOlim.w, hROlim.w, ← Category.assoc, ht]
    · rw [yoneda.map_comp, yoneda.map_comp, Category.assoc, Category.assoc,
        ← yoneda.map_comp sO bW, hsoSq, hawOb, yoneda.map_comp,
        ← Category.assoc, harOb, ← yoneda.map_comp, hsnCompat, yoneda.map_comp]
  have htOCompat : arO ≫ tO = ks ≫ awO := by
    apply yoneda.map_injective
    apply hWO.hom_ext
    · rw [yoneda.map_comp, yoneda.map_comp, Category.assoc, Category.assoc, htOW,
        hWOlim.w, hROlim.w, ← Category.assoc, hs]
    · rw [yoneda.map_comp, yoneda.map_comp, Category.assoc, Category.assoc,
        ← yoneda.map_comp tO bW, htoSq, hawOb, yoneda.map_comp,
        ← Category.assoc, harOb, ← yoneda.map_comp, htnCompat, yoneda.map_comp]
  have hsqsO : IsPullback arO kt sO awO :=
    isPullback_of_isPullback_over yoneda hsOCompat hWOlim ht hsOW hROlim
  have hsqtO : IsPullback arO ks tO awO :=
    isPullback_of_isPullback_over yoneda htOCompat hWOlim hs htOW hROlim
  -- joint monicity of the descended relation
  have hρcomm : yoneda.map sO ≫ wO = yoneda.map tO ≫ wO := by rw [hsOW, htOW]
  let KWO := atlasKernelPair B S hS wO (hD oo.left).diagonal_representable
  obtain ⟨ρ, hρs, hρt⟩ := exists_comp_eq_atlasKernelPair B S hS KWO sO tO hρcomm
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

/-- **Stacks 07SK, essential surjectivity, for a system bounded by the cutoff.** Let `D` be a
cofiltered inverse system of quasi-compact, absolutely quasi-separated algebraic spaces over `S`
with affine transition morphisms, satisfying `AlgebraicGeometry.Space.IsCutoffBoundedSystem`.
Every algebraic space of finite presentation over the limit is the base change of an algebraic
space of finite presentation over some stage. This is
`AlgebraicGeometry.Space.exists_model_of_finitePresentation` with the bound of the index category
by the cofinality of the cutoff replaced by `AlgebraicGeometry.Space.IsCutoffBoundedSystem`, which
the systems of Stacks 07SU and Stacks 0A0X satisfy. -/
public theorem exists_model_of_finitePresentation
    (hConv : IsCutoffBoundedSystem B S hS D)
    (Y : Over (limit D))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y.left)
    (hFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Y.hom) :
    ∃ (i : I) (Yᵢ : Over (D.obj i)),
      AlgebraicGeometry.IsAlgebraicSpace B S hS Yᵢ.left ∧
        AlgebraicGeometry.Space.IsFinitePresentation B S hS Yᵢ.hom ∧
        Nonempty (Y ≅ (Over.pullback (limit.π D i)).obj Yᵢ) := by
  classical
  obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
  obtain ⟨U₀, p₀, hU₀, hs₀, he₀⟩ := exists_affine_etale_atlas B S hS
    (D.obj i) (hD i) (hQc i)
  let U₀' : AlgebraicGeometry.BigAffineFppf B S hS := ⟨U₀, hU₀⟩
  have hp₀ := represented_etale_of_isEtale B S hS p₀ he₀
  obtain ⟨U, p, q, hp⟩ :=
    isAffineHom_limitπ_of_isCutoffBoundedSystem B S hS D hConv hAffine i U₀' p₀
  let Q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let P := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u}) Q
  let E := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) Q
  let : P.presheaf.IsStableUnderBaseChange := P.relative_isStableUnderBaseChange (F := yoneda)
  let : E.presheaf.IsStableUnderBaseChange := E.relative_isStableUnderBaseChange (F := yoneda)
  let : P.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition P (surjectiveInverseImageIsStableUnderComposition _)
  let : E.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition E (etaleInverseImageIsStableUnderComposition _)
  have hs : P.presheaf p := P.presheaf.of_isPullback hp.flip hs₀
  have he : E.presheaf p := E.presheaf.of_isPullback hp.flip hp₀
  have hX := isAlgebraicSpace_limit_of_isCutoffBoundedSystem B S hS D hConv hD hAffine
  have hXqs := AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ
    hX (hQs i)
    (isQuasiSeparated_of_isAffineHom B S hS (limit.π D i) hX (hD i)
      (isAffineHom_limitπ_of_isCutoffBoundedSystem B S hS D hConv hAffine i))
  have hYqs := AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated
    B S hS hZ hY hXqs hFp.2.2
  obtain ⟨W, w, g, hws, hwe, hw, hg⟩ :=
    exists_affine_finitePresentation_chart B S hS hX hY Y.hom hFp U p hs he
  let K := atlasKernelPair B S hS w hY.diagonal_representable
  have hKt := atlasKernelPair_target_finitePresentation B S hS hZ hY hYqs W w hwe
  have hKg : AlgebraicGeometry.FinitePresentation (Q.map (K.s ≫ g)) := by
    let : LocallyOfFinitePresentation (Q.map K.s) := hKt.1
    let : QuasiCompact (Q.map K.s) := hKt.2.1
    let : QuasiSeparated (Q.map K.s) := hKt.2.2
    let : LocallyOfFinitePresentation (Q.map g) := hg.1
    let : QuasiCompact (Q.map g) := hg.2.1
    let : QuasiSeparated (Q.map g) := hg.2.2
    rw [Q.map_comp]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  let : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj W.obj) := W.property
  obtain ⟨j, Wj, wj, aw, hwj, hWjaff, hWmodel⟩ := exists_affine_site_model_over_affine_chart
    B S hS hZ D hD hAffine hQs hConv i U₀' p₀ hp₀ U p q hp W.obj g hg
  obtain ⟨k, Rk, rk, ar, hrk, hRmodel⟩ := exists_site_model_over_affine_chart
    B S hS hZ D hD hAffine hQs hConv i U₀' p₀ hp₀ U p q hp
      K.R (K.s ≫ g) hKg
  let l := IsCofiltered.min j.left k.left
  let ej : l ⟶ j.left := IsCofiltered.minToLeft _ _
  let ek : l ⟶ k.left := IsCofiltered.minToRight _ _
  let pW := yoneda.map g ≫ p
  let pR := yoneda.map (K.s ≫ g) ≫ p
  obtain ⟨WlA, wl, bl, hbl⟩ := hAffine ej ⟨Wj, hWjaff⟩ wj
  let Wl := WlA.obj
  have hwl : AlgebraicGeometry.Space.IsFinitePresentation B S hS wl :=
    isFinitePresentation_of_isPullback_yoneda B S hS (hD l) (hD j.left) hbl.flip hwj
  obtain ⟨awl, -, hWl⟩ :=
    exists_isPullback_comparison (p := pW) yoneda hbl.flip (limit.w D ej) hWmodel
  obtain ⟨Rl, rl, arl, hrl, hRl⟩ := advance_represented_model B S hS
    (hD l) (hD k.left) rk ar pR (limit.π D l) (D.map ek) (limit.π D k.left)
    (limit.w D ek) (hAffine ek) hrk hRmodel
  let KW := atlasKernelPair B S hS wl (hD l).diagonal_representable
  have hWlAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wl
  have hKWAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS KW.R
  have hKWt : AlgebraicGeometry.Space.IsFinitePresentation B S hS (yoneda.map KW.s) :=
    isFinitePresentation_of_isPullback_yoneda B S hS hWlAlg (hD l) KW.kernelPair.flip hwl
  let vKW := yoneda.map KW.s ≫ wl
  have hKWfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS vKW :=
    AlgebraicGeometry.Space.isFinitePresentation_comp B S hS hKWAlg hWlAlg (hD l)
      (yoneda.map KW.s) wl hKWt hwl
  have ht : yoneda.map K.s ≫ pW = pR := by
    simp only [pW, pR, Functor.map_comp, Category.assoc]
  have hs : yoneda.map K.t ≫ pW = pR := by
    rw [← ht]
    simpa only [pW, hw, Category.assoc] using
      congrArg (fun t => t ≫ Y.hom) K.kernelPair.w.symm
  let b : yoneda.obj K.R ⟶ yoneda.obj KW.R := KW.kernelPair.lift
    (yoneda.map K.s ≫ yoneda.map awl) (yoneda.map K.t ≫ yoneda.map awl) (by
      simp only [Category.assoc, hWl.w]
      rw [← Category.assoc, ht, ← Category.assoc, hs])
  have hb : b ≫ vKW = pR ≫ limit.π D l := by
    simp only [b, vKW, IsPullback.lift_fst_assoc]
    rw [Category.assoc, hWl.w, ← Category.assoc, ht]
  let source := Over.mk rl
  let target := Over.mk vKW
  let er : Over.mk pR ≅ (Over.pullback (limit.π D l)).obj source :=
    Over.isoMk hRl.isoPullback hRl.isoPullback_hom_snd
  let f : (Over.pullback (limit.π D l)).obj source ⟶
      (Over.pullback (limit.π D l)).obj target :=
    Over.homMk (pullback.lift (er.inv.left ≫ b)
      (pullback.snd rl (limit.π D l)) (by
        show (er.inv.left ≫ b) ≫ vKW = _
        rw [Category.assoc, hb, ← Category.assoc]
        exact congrArg (fun t => t ≫ limit.π D l) er.inv.w)) (by simp [source, target])
  obtain ⟨m, em, gm, αm, βm, hαm, hβm, hgm⟩ := exists_morphism_after_baseChange
    B S hS hZ D hD hAffine hQc hQs hConv l source target
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Rl) hKWAlg hrl hKWfp f
  have hαmEq := iteratedBaseChangeIso_unique (D.map em) (limit.π D m) (limit.π D l)
    (limit.w D em) source αm hαm
  have hβmEq := iteratedBaseChangeIso_unique (D.map em) (limit.π D m) (limit.π D l)
    (limit.w D em) target βm hβm
  rw [hαmEq, hβmEq] at hgm
  have hmAffine := ((AlgebraicGeometry.Space.isAffineHom_tfae_of_isAlgebraicSpace B S hS (D.map em)
    (hD m) (hD l)).out 2 1).mp (hAffine em)
  let Rm := hmAffine.1.pullback rl
  let Wm := hmAffine.1.pullback wl
  let rm := hmAffine.1.fst rl
  let wm := hmAffine.1.fst wl
  have hRm : IsPullback rm (yoneda.map (hmAffine.1.snd rl)) (D.map em) rl :=
    hmAffine.1.isPullback rl
  have hWm : IsPullback wm (yoneda.map (hmAffine.1.snd wl)) (D.map em) wl :=
    hmAffine.1.isPullback wl
  have hWmAffineHom : _root_.AlgebraicGeometry.IsAffineHom (Q.map (hmAffine.1.snd wl)) :=
    hmAffine.2.property wl wm (hmAffine.1.snd wl) hWm
  have hWmAffine : IsAffine (Q.obj Wm) := by
    let : IsAffine (Q.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj WlA)) :=
      WlA.property
    let : _root_.AlgebraicGeometry.IsAffineHom (Q.map (hmAffine.1.snd wl)) := hWmAffineHom
    exact isAffine_of_isAffineHom (Q.map (hmAffine.1.snd wl))
  have hRmFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS rm :=
    isFinitePresentation_of_isPullback_yoneda B S hS (hD m) (hD l) hRm.flip hrl
  have hWmFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS wm :=
    isFinitePresentation_of_isPullback_yoneda B S hS (hD m) (hD l) hWm.flip hwl
  let st : target ⟶ Over.mk wl := Over.homMk (yoneda.map KW.s) (by rfl)
  let tt : target ⟶ Over.mk wl := Over.homMk (yoneda.map KW.t) KW.kernelPair.w.symm
  let sm₀ := gm ≫ (Over.pullback (D.map em)).map st
  let tm₀ := gm ≫ (Over.pullback (D.map em)).map tt
  let sm : Rm ⟶ Wm := yoneda.preimage
    (hRm.flip.isoPullback.hom ≫ sm₀.left ≫ hWm.flip.isoPullback.inv)
  let tm : Rm ⟶ Wm := yoneda.preimage
    (hRm.flip.isoPullback.hom ≫ tm₀.left ≫ hWm.flip.isoPullback.inv)
  have hsm : yoneda.map sm ≫ wm = rm := by
    simp only [sm, yoneda.map_preimage, Category.assoc, IsPullback.isoPullback_inv_snd]
    rw [show sm₀.left ≫ pullback.snd wl (D.map em) =
      pullback.snd rl (D.map em) from sm₀.w, hRm.flip.isoPullback_hom_snd]
  have htm : yoneda.map tm ≫ wm = rm := by
    simp only [tm, yoneda.map_preimage, Category.assoc, IsPullback.isoPullback_inv_snd]
    rw [show tm₀.left ≫ pullback.snd wl (D.map em) =
      pullback.snd rl (D.map em) from tm₀.w, hRm.flip.isoPullback_hom_snd]
  obtain ⟨arm, harm, hRlim⟩ :=
    exists_isPullback_comparison (p := pR) yoneda hRm.flip (limit.w D em) hRl
  obtain ⟨awm, hawm, hWlim⟩ :=
    exists_isPullback_comparison (p := pW) yoneda hWm.flip (limit.w D em) hWl
  have harPB : yoneda.map arm ≫ hRm.flip.isoPullback.hom =
      er.hom.left ≫
        (iteratedBaseChangeIso (D.map em) (limit.π D m) (limit.π D l)
          (limit.w D em) source).inv.left ≫
          pullback.fst ((Over.pullback (D.map em)).obj source).hom (limit.π D m) := by
    apply pullback.hom_ext
    · simp [er, source, iteratedBaseChangeIso, Category.assoc, harm]
    · simp [er, source, iteratedBaseChangeIso, Category.assoc, hRlim.w]
  have hgm' : yoneda.map arm ≫ hRm.flip.isoPullback.hom ≫ gm.left ≫
      pullback.fst vKW (D.map em) = b := by
    have hh := congrArg (fun z => er.hom ≫
      (iteratedBaseChangeIso (D.map em) (limit.π D m) (limit.π D l)
        (limit.w D em) source).inv ≫ z) hgm
    simp only [Iso.inv_hom_id_assoc] at hh
    have hh' := congrArg (fun z => z.left ≫ pullback.fst vKW (limit.π D l)) hh
    have her : er.hom.left ≫ er.inv.left = 𝟙 _ :=
      congrArg (fun z => z.left) er.hom_inv_id
    simp only [Over.comp_left, Category.assoc] at hh'
    have hβfst := iteratedBaseChangeIso_hom_fst (D.map em) (limit.π D m)
      (limit.π D l) (limit.w D em) target
    change (iteratedBaseChangeIso (D.map em) (limit.π D m) (limit.π D l)
      (limit.w D em) target).hom.left ≫ pullback.fst vKW (limit.π D l) = _ at hβfst
    rw [hβfst] at hh'
    rw [reassoc_of% harPB]
    simpa only [source, target,
      Over.pullback_map_left, Over.pullback_obj_hom, Over.mk_hom, f,
      Over.homMk_left, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
      her, reassoc_of% her, Category.id_comp] using hh'.symm
  have hsmCompat : arm ≫ sm = K.s ≫ awm := by
    apply yoneda.map_injective
    apply hWm.hom_ext
    · simp only [Functor.map_comp, Category.assoc, hsm, hRlim.w,
        hWlim.w]
      rw [← Category.assoc, ht]
    · simp only [Functor.map_comp, Category.assoc, sm, yoneda.map_preimage,
        IsPullback.isoPullback_inv_fst]
      show yoneda.map arm ≫ hRm.flip.isoPullback.hom ≫
        (gm ≫ (Over.pullback (D.map em)).map st).left ≫
          pullback.fst wl (D.map em) =
        yoneda.map K.s ≫ yoneda.map awm ≫ yoneda.map (hmAffine.1.snd wl)
      simp only [Over.comp_left, Over.pullback_map_left, Category.assoc,
        pullback.lift_fst, hawm, source, target, st, Over.mk_hom, Over.homMk_left]
      show yoneda.map arm ≫ hRm.flip.isoPullback.hom ≫ gm.left ≫
        pullback.fst vKW (D.map em) ≫ yoneda.map KW.s = _
      rw [reassoc_of% hgm']
      simp [b]
  have htmCompat : arm ≫ tm = K.t ≫ awm := by
    apply yoneda.map_injective
    apply hWm.hom_ext
    · simp only [Functor.map_comp, Category.assoc, htm, hRlim.w,
        hWlim.w]
      rw [← Category.assoc, hs]
    · simp only [Functor.map_comp, Category.assoc, tm, yoneda.map_preimage,
        IsPullback.isoPullback_inv_fst]
      show yoneda.map arm ≫ hRm.flip.isoPullback.hom ≫
        (gm ≫ (Over.pullback (D.map em)).map tt).left ≫
          pullback.fst wl (D.map em) =
        yoneda.map K.t ≫ yoneda.map awm ≫ yoneda.map (hmAffine.1.snd wl)
      simp only [Over.comp_left, Over.pullback_map_left, Category.assoc,
        pullback.lift_fst, hawm, source, target, tt, Over.mk_hom, Over.homMk_left]
      show yoneda.map arm ≫ hRm.flip.isoPullback.hom ≫ gm.left ≫
        pullback.fst vKW (D.map em) ≫ yoneda.map KW.t = _
      rw [reassoc_of% hgm']
      simp [b]
  have hsmSquare : IsPullback arm K.s sm awm :=
    isPullback_of_isPullback_over yoneda hsmCompat hWlim ht hsm hRlim
  have htmSquare : IsPullback arm K.t tm awm :=
    isPullback_of_isPullback_over yoneda htmCompat hWlim hs htm hRlim
  have hRmAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Rm
  have hWmAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wm
  have hSmFp := finitePresentation_of_yoneda B S hS sm
    (isFinitePresentation_overHom B S hS hZ (hD m) (hQc m) (hQs m)
      (Over.mk rm) (Over.mk wm) hRmAlg hWmAlg hRmFp hWmFp
      (Over.homMk (yoneda.map sm) hsm))
  have hTmFp := finitePresentation_of_yoneda B S hS tm
    (isFinitePresentation_overHom B S hS hZ (hD m) (hQc m) (hQs m)
      (Over.mk rm) (Over.mk wm) hRmAlg hWmAlg hRmFp hWmFp
      (Over.homMk (yoneda.map tm) htm))
  let WmA : AlgebraicGeometry.BigAffineFppf B S hS := ⟨Wm, hWmAffine⟩
  let : Etale ((Over.pullback (Q.map awm)).obj (Over.mk (Q.map sm))).hom :=
    (etale_iff_pullback_of_isPullback (hsmSquare.map Q)).mp
      (hwe.property w (yoneda.map K.t) K.s K.kernelPair.flip)
  let : Etale ((Over.pullback (Q.map awm)).obj (Over.mk (Q.map tm))).hom :=
    (etale_iff_pullback_of_isPullback (htmSquare.map Q)).mp
      (hwe.property w (yoneda.map K.s) K.t K.kernelPair)
  obtain ⟨js, hjs⟩ := eventually_etale_over_affine_chart B S hS D hAffine
    hConv m WmA wm W pW awm hWlim.flip (Over.mk (Q.map sm)) hSmFp
  obtain ⟨jt, hjt⟩ := eventually_etale_over_affine_chart B S hS D hAffine
    hConv m WmA wm W pW awm hWlim.flip (Over.mk (Q.map tm)) hTmFp
  let n := IsCofiltered.min js jt
  let as' := IsCofiltered.minToLeft js jt
  let at' := IsCofiltered.minToRight js jt
  let En := affineStageChartOverDiagram B S hS D m WmA wm hAffine
  let Cn := affineStageChart B S hS D m WmA wm hAffine n
  have hsChart : Etale (pullback.snd (Q.map sm) (Q.map Cn.toChart)) := by
    let : Etale ((Over.pullback (Q.map (En.obj js).hom)).obj (Over.mk (Q.map sm))).hom := hjs
    exact etale_pullback_of_etale_pullback (Q.map (En.obj js).hom)
      (Q.map (En.map as').left) (Q.map (En.obj n).hom)
      (by rw [← Q.map_comp]; exact congrArg Q.map (En.map as').w) (Over.mk (Q.map sm))
  have htChart : Etale (pullback.snd (Q.map tm) (Q.map Cn.toChart)) := by
    let : Etale ((Over.pullback (Q.map (En.obj jt).hom)).obj (Over.mk (Q.map tm))).hom := hjt
    exact etale_pullback_of_etale_pullback (Q.map (En.obj jt).hom)
      (Q.map (En.map at').left) (Q.map (En.obj n).hom)
      (by rw [← Q.map_comp]; exact congrArg Q.map (En.map at').w) (Over.mk (Q.map tm))
  let Wn := Cn.U.obj
  let wn := Cn.toStage
  let Rn := pullback sm Cn.toChart
  let sn : Rn ⟶ Wn := pullback.snd sm Cn.toChart
  let br : Rn ⟶ Rm := pullback.fst sm Cn.toChart
  let rn := yoneda.map sn ≫ wn
  have hRn : IsPullback (yoneda.map br) rn rm (D.map n.hom) := by
    have hh := ((IsPullback.of_hasPullback sm Cn.toChart).map yoneda).paste_vert
      Cn.isPullback.flip
    simpa only [hsm] using hh
  let tn : Rn ⟶ Wn := yoneda.preimage (Cn.isPullback.lift rn
    (yoneda.map br ≫ yoneda.map tm) (by
      simp only [Category.assoc, htm]
      exact hRn.w.symm))
  have htn : yoneda.map tn ≫ wn = rn := by simp [tn, wn]
  have htnBr : br ≫ tm = tn ≫ Cn.toChart := by
    apply yoneda.map_injective
    simp [tn]
  have htnSquare : IsPullback br tn tm Cn.toChart := by
    apply IsPullback.of_map yoneda htnBr
    apply IsPullback.of_bot _ (by simpa only [Functor.map_comp] using congrArg yoneda.map htnBr)
      Cn.isPullback.flip
    simpa only [← show wn = Cn.toStage from rfl, htm, htn] using hRn
  have hsnEtale : Etale (Q.map sn) :=
    (etale_iff_pullback_of_isPullback ((IsPullback.of_hasPullback sm Cn.toChart).map Q)).mpr hsChart
  have htnEtale : Etale (Q.map tn) :=
    (etale_iff_pullback_of_isPullback (htnSquare.map Q)).mpr htChart
  have hRnFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS rn :=
    isFinitePresentation_of_isPullback_yoneda B S hS (hD n.left) (hD m) hRn hRmFp
  have hWnFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS wn :=
    isFinitePresentation_of_isPullback_yoneda B S hS (hD n.left) (hD m) Cn.isPullback.flip hWmFp
  obtain ⟨awn, hAwnBw, hWnlim⟩ :=
    exists_isPullback_comparison (p := pW) yoneda Cn.isPullback.flip (limit.w D n.hom) hWlim
  obtain ⟨arn, hArnBr, hRnlim⟩ :=
    exists_isPullback_comparison (p := pR) yoneda hRn (limit.w D n.hom) hRlim
  have hsnCompat : arn ≫ sn = K.s ≫ awn := by
    apply yoneda.map_injective
    apply Cn.isPullback.hom_ext
    · simp only [Functor.map_comp, Category.assoc]
      show yoneda.map arn ≫ rn = yoneda.map K.s ≫ yoneda.map awn ≫ wn
      rw [hRnlim.w, hWnlim.w, ← Category.assoc, ht]
    · simp only [Functor.map_comp, Category.assoc]
      have hsn : sn ≫ Cn.toChart = br ≫ sm := pullback.condition.symm
      rw [← yoneda.map_comp sn Cn.toChart, hsn, yoneda.map_comp,
        ← Category.assoc, hArnBr, hAwnBw]
      exact congrArg yoneda.map hsmCompat
  have htnCompat : arn ≫ tn = K.t ≫ awn := by
    apply yoneda.map_injective
    apply Cn.isPullback.hom_ext
    · simp only [Functor.map_comp, Category.assoc]
      show yoneda.map arn ≫ yoneda.map tn ≫ wn =
        yoneda.map K.t ≫ yoneda.map awn ≫ wn
      rw [htn, hRnlim.w, hWnlim.w, ← Category.assoc, hs]
    · simp only [Functor.map_comp, Category.assoc]
      rw [← yoneda.map_comp tn Cn.toChart, ← htnBr, yoneda.map_comp,
        ← Category.assoc, hArnBr, hAwnBw]
      exact congrArg yoneda.map htmCompat
  have hsnSquare : IsPullback arn K.s sn awn :=
    isPullback_of_isPullback_over yoneda hsnCompat hWnlim ht rfl hRnlim
  have htnLimitSquare : IsPullback arn K.t tn awn :=
    isPullback_of_isPullback_over yoneda htnCompat hWnlim hs htn hRnlim
  have hRnlim' : IsPullback (yoneda.map arn) (yoneda.map K.s ≫ w ≫ Y.hom)
      (yoneda.map sn ≫ wn) (limit.π D n.left) := by
    rw [show (yoneda.map K.s ≫ w ≫ Y.hom) = pR from by rw [← hw]; exact ht]
    exact hRnlim
  exact exists_model_of_stage_relation B S hS hZ D hD hAffine hQc hQs hConv
    n.left hX Y hY w hws hwe K.s K.t K.kernelPair
    (show IsAffine (Q.obj Wn) from Cn.U.property) wn sn tn htn hsnEtale htnEtale
    hWnFp hRnFp awn arn (by rw [← hw]; exact hWnlim) hRnlim' hsnCompat htnCompat

end IsCutoffBoundedSystem

end AlgebraicGeometry.Space

end
