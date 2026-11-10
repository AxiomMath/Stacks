module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescentLimitFacts.StageRelation
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
import all StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescentLimitFacts.StageRelation

/-!
# Stacks 07SK without a bound on the index category

Essential surjectivity in its private `LimitFacts` form, the two ways of supplying
`LimitFacts` (a bound on the index category, or
`AlgebraicGeometry.Space.AffineChartLimitsInSchemes`), and the three statements of Stacks 07SK
for systems whose affine chart systems have their limits computed in schemes.
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

/-- Pasting a pullback square on the right of an outer pullback square: the lift of the outer
top map through the right square is the top map of the left square. -/
private theorem isPullback_lift_of_comp_eq {E : Type*} [Category E] {A Wl Wj L Dl Dj : E}
    {b : Wl ⟶ Wj} {wl : Wl ⟶ Dl} {wj : Wj ⟶ Dj} {d : Dl ⟶ Dj} {a : A ⟶ Wj} {p : A ⟶ L}
    {π : L ⟶ Dl} {π' : L ⟶ Dj} (hsq : IsPullback b wl wj d) (hπ : π ≫ d = π')
    (hout : IsPullback a p wj π') :
    IsPullback (hsq.lift a (p ≫ π) (by rw [Category.assoc, hπ, hout.w])) p wl π := by
  subst hπ
  exact hout.of_right' hsq

/-- A commuting square of representable morphisms is a pullback as soon as it sits over a
pullback square with the same bottom-right corner as a pullback square of presheaves. -/
private theorem isPullback_of_isPullback_yoneda_comp {C : Type*} [Category.{u} C] {R W R' W' : C}
    {L M : Cᵒᵖ ⥤ Type u} {a : R ⟶ R'} {k : R ⟶ W} {s : R' ⟶ W'} {aw : W ⟶ W'}
    (compat : a ≫ s = k ≫ aw) {pW : yoneda.obj W ⟶ L} {pR : yoneda.obj R ⟶ L}
    {w : yoneda.obj W' ⟶ M} {r : yoneda.obj R' ⟶ M} {π : L ⟶ M}
    (hW : IsPullback (yoneda.map aw) pW w π) (hR : IsPullback (yoneda.map a) pR r π)
    (hs : yoneda.map s ≫ w = r) (hk : yoneda.map k ≫ pW = pR) : IsPullback a k s aw := by
  apply IsPullback.of_map yoneda compat
  apply IsPullback.of_bot _ (by simpa only [Functor.map_comp] using congrArg yoneda.map compat) hW
  simpa only [hs, hk] using hR

include hD hAffine hQc hQs

/-- Every algebraic space of finite presentation over the limit descends to a
finite stage. -/
private theorem exists_model_of_finitePresentation_aux
    (hFacts : LimitFacts B S hS D)
    (Y : Over (limit D))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y.left)
    (hFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Y.hom) :
    ∃ (i : I) (Yᵢ : Over (D.obj i)),
      AlgebraicGeometry.IsAlgebraicSpace B S hS Yᵢ.left ∧
        AlgebraicGeometry.Space.IsFinitePresentation B S hS Yᵢ.hom ∧
        Nonempty (Y ≅ (Over.pullback (limit.π D i)).obj Yᵢ)  := by
  classical
  obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
  obtain ⟨U₀, p₀, hU₀, hs₀, he₀⟩ := exists_affine_etale_atlas B S hS
    (D.obj i) (hD i) (hQc i)
  let U₀' : AlgebraicGeometry.BigAffineFppf B S hS := ⟨U₀, hU₀⟩
  have hp₀ := represented_etale_of_isEtale B S hS p₀ he₀
  obtain ⟨U, p, q, hp⟩ :=
    hFacts.piAff i U₀' p₀
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
  have hX := hFacts.limAlg
  have hXqs := AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ
    hX (hQs i)
    (AlgebraicGeometry.Space.isQuasiSeparated_of_isAffineHom B S hS (limit.π D i) hX (hD i)
      (hFacts.piAff i))
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
  obtain ⟨j, Wj, wj, aw, hwj, hWjaff, hWmodel⟩ :=
    exists_affine_site_model_over_affine_chart_of_limitFacts
      B S hS hZ D hD hAffine hQs hFacts i U₀' p₀ hp₀ U p q hp W.obj g hg
  obtain ⟨k, Rk, rk, ar, hrk, -, hRmodel⟩ := exists_site_model_over_affine_chart_of_limitFacts
    B S hS hZ D hD hAffine hQs hFacts i U₀' p₀ hp₀ U p q hp
      K.R (K.s ≫ g) hKg
  let l := IsCofiltered.min j.left k.left
  let ej : l ⟶ j.left := IsCofiltered.minToLeft _ _
  let ek : l ⟶ k.left := IsCofiltered.minToRight _ _
  let pW := yoneda.map g ≫ p
  let pR := yoneda.map (K.s ≫ g) ≫ p
  obtain ⟨WlA, wl, bl, hbl⟩ := hAffine ej ⟨Wj, hWjaff⟩ wj
  let Wl := WlA.obj
  have hwl : AlgebraicGeometry.Space.IsFinitePresentation B S hS wl :=
    isFinitePresentation_of_isPullback B S hS
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wl)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wj)
      (hD l) (hD j.left) hbl.flip hwj
  let awl : W.obj ⟶ Wl := yoneda.preimage (hbl.flip.lift (yoneda.map aw)
    (pW ≫ limit.π D l) (by rw [Category.assoc, limit.w]; exact hWmodel.w))
  have hWl : IsPullback (yoneda.map awl) pW wl (limit.π D l) := by
    simpa only [awl, yoneda.map_preimage] using
      isPullback_lift_of_comp_eq hbl.flip (limit.w D ej) hWmodel
  obtain ⟨Rl, rl, arl, hrl, hRl⟩ := advance_represented_model B S hS
    (hD l) (hD k.left) rk ar pR (limit.π D l) (D.map ek) (limit.π D k.left)
    (limit.w D ek) (hAffine ek) hrk hRmodel
  let KW := atlasKernelPair B S hS wl (hD l).diagonal_representable
  have hWlAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wl
  have hKWAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS KW.R
  have hKWt : AlgebraicGeometry.Space.IsFinitePresentation B S hS (yoneda.map KW.s) :=
    isFinitePresentation_of_isPullback B S hS hKWAlg hWlAlg hWlAlg (hD l)
      KW.kernelPair.flip hwl
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
    Over.isoMk hRl.isoPullback (by exact hRl.isoPullback_hom_snd)
  let f : (Over.pullback (limit.π D l)).obj source ⟶
      (Over.pullback (limit.π D l)).obj target :=
    Over.homMk (pullback.lift (er.inv.left ≫ b)
      (pullback.snd rl (limit.π D l)) (by
        change (er.inv.left ≫ b) ≫ vKW = _
        rw [Category.assoc, hb, ← Category.assoc]
        exact congrArg (fun t => t ≫ limit.π D l) er.inv.w)) (by simp [source, target])
  obtain ⟨m, em, gm, αm, βm, hαm, hβm, hgm⟩ := exists_morphism_after_baseChange_aux
    B S hS hZ D hD hAffine hQc hQs hFacts l source target
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
    isFinitePresentation_of_isPullback B S hS
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Rm)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Rl) (hD m) (hD l) hRm.flip hrl
  have hWmFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS wm :=
    isFinitePresentation_of_isPullback B S hS
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wm)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wl) (hD m) (hD l) hWm.flip hwl
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
  let arm : K.R ⟶ Rm := yoneda.preimage (hRm.flip.lift (yoneda.map arl)
    (pR ≫ limit.π D m) (by rw [Category.assoc, limit.w]; exact hRl.w))
  let awm : W.obj ⟶ Wm := yoneda.preimage (hWm.flip.lift (yoneda.map awl)
    (pW ≫ limit.π D m) (by rw [Category.assoc, limit.w]; exact hWl.w))
  have hRlim : IsPullback (yoneda.map arm) pR rm (limit.π D m) := by
    simpa only [arm, yoneda.map_preimage] using
      isPullback_lift_of_comp_eq hRm.flip (limit.w D em) hRl
  have hWlim : IsPullback (yoneda.map awm) pW wm (limit.π D m) := by
    simpa only [awm, yoneda.map_preimage] using
      isPullback_lift_of_comp_eq hWm.flip (limit.w D em) hWl
  have harm : yoneda.map arm ≫ yoneda.map (hmAffine.1.snd rl) = yoneda.map arl := by
    simp [arm]
  have hawm : yoneda.map awm ≫ yoneda.map (hmAffine.1.snd wl) = yoneda.map awl := by
    simp [awm]
  have harPB : yoneda.map arm ≫ hRm.flip.isoPullback.hom =
      er.hom.left ≫
        (iteratedBaseChangeIso (D.map em) (limit.π D m) (limit.π D l)
          (limit.w D em) source).inv.left ≫
          pullback.fst ((Over.pullback (D.map em)).obj source).hom (limit.π D m) := by
    apply pullback.hom_ext
    · simp [arm, er, source, iteratedBaseChangeIso, Category.assoc]
    · simp [arm, er, source, iteratedBaseChangeIso, Category.assoc]
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
      change yoneda.map arm ≫ hRm.flip.isoPullback.hom ≫
        (gm ≫ (Over.pullback (D.map em)).map st).left ≫
          pullback.fst wl (D.map em) =
        yoneda.map K.s ≫ yoneda.map awm ≫ yoneda.map (hmAffine.1.snd wl)
      simp only [Over.comp_left, Over.pullback_map_left, Category.assoc,
        pullback.lift_fst, hawm, source, target, st, Over.mk_hom, Over.homMk_left]
      change yoneda.map arm ≫ hRm.flip.isoPullback.hom ≫ gm.left ≫
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
      change yoneda.map arm ≫ hRm.flip.isoPullback.hom ≫
        (gm ≫ (Over.pullback (D.map em)).map tt).left ≫
          pullback.fst wl (D.map em) =
        yoneda.map K.t ≫ yoneda.map awm ≫ yoneda.map (hmAffine.1.snd wl)
      simp only [Over.comp_left, Over.pullback_map_left, Category.assoc,
        pullback.lift_fst, hawm, source, target, tt, Over.mk_hom, Over.homMk_left]
      change yoneda.map arm ≫ hRm.flip.isoPullback.hom ≫ gm.left ≫
        pullback.fst vKW (D.map em) ≫ yoneda.map KW.t = _
      rw [reassoc_of% hgm']
      simp [b]
  have hsmSquare : IsPullback arm K.s sm awm :=
    isPullback_of_isPullback_yoneda_comp hsmCompat hWlim hRlim hsm ht
  have htmSquare : IsPullback arm K.t tm awm :=
    isPullback_of_isPullback_yoneda_comp htmCompat hWlim hRlim htm hs
  have hRmAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Rm
  have hWmAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wm
  have hFpOfOver : ∀ (u : Rm ⟶ Wm), yoneda.map u ≫ wm = rm →
      AlgebraicGeometry.FinitePresentation (Q.map u) := fun u hu =>
    finitePresentation_of_yoneda B S hS u
      (isFinitePresentation_overHom B S hS hZ (hD m) (hQc m) (hQs m)
        (Over.mk rm) (Over.mk wm) hRmAlg hWmAlg hRmFp hWmFp (Over.homMk (yoneda.map u) hu))
  let WmA : AlgebraicGeometry.BigAffineFppf B S hS := ⟨Wm, hWmAffine⟩
  let : Etale ((Over.pullback (Q.map awm)).obj (Over.mk (Q.map sm))).hom :=
    (etale_iff_pullback_of_isPullback (hsmSquare.map Q)).mp
      (hwe.property w (yoneda.map K.t) K.s K.kernelPair.flip)
  let : Etale ((Over.pullback (Q.map awm)).obj (Over.mk (Q.map tm))).hom :=
    (etale_iff_pullback_of_isPullback (htmSquare.map Q)).mp
      (hwe.property w (yoneda.map K.s) K.t K.kernelPair)
  obtain ⟨js, hjs⟩ := eventually_etale_over_affine_chart_of_limitFacts B S hS D hAffine
    hFacts m WmA wm W pW awm hWlim.flip (Over.mk (Q.map sm)) (hFpOfOver sm hsm)
  obtain ⟨jt, hjt⟩ := eventually_etale_over_affine_chart_of_limitFacts B S hS D hAffine
    hFacts m WmA wm W pW awm hWlim.flip (Over.mk (Q.map tm)) (hFpOfOver tm htm)
  let n := IsCofiltered.min js jt
  let as' := IsCofiltered.minToLeft js jt
  let at' := IsCofiltered.minToRight js jt
  let En := affineStageChartOverDiagramOfLimitFacts B S hS D
    m WmA wm hAffine
  let Cn := affineStageChartOfLimitFacts B S hS D m WmA wm hAffine n
  have hChart : ∀ (u : Rm ⟶ Wm) (j) (a : n ⟶ j),
      Etale ((Over.pullback (Q.map (En.obj j).hom)).obj (Over.mk (Q.map u))).hom →
        Etale (pullback.snd (Q.map u) (Q.map Cn.toChart)) := fun u j a hj =>
    etale_pullback_of_etale_pullback (Q.map (En.obj j).hom)
      (Q.map (En.map a).left) (Q.map (En.obj n).hom)
      (by rw [← Q.map_comp]; exact congrArg Q.map (En.map a).w) (Over.mk (Q.map u))
  have hsChart := hChart sm js as' hjs
  have htChart := hChart tm jt at' hjt
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
  have hRnAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Rn
  have hWnAlg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Wn
  have hRnFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS rn :=
    isFinitePresentation_of_isPullback B S hS hRnAlg hRmAlg (hD n.left) (hD m) hRn hRmFp
  have hWnFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS wn :=
    isFinitePresentation_of_isPullback B S hS hWnAlg hWmAlg (hD n.left) (hD m)
      Cn.isPullback.flip hWmFp
  let awn : W.obj ⟶ Wn := yoneda.preimage (Cn.isPullback.flip.lift (yoneda.map awm)
    (pW ≫ limit.π D n.left) (by rw [Category.assoc, limit.w]; exact hWlim.w))
  let arn : K.R ⟶ Rn := yoneda.preimage (hRn.lift (yoneda.map arm)
    (pR ≫ limit.π D n.left) (by rw [Category.assoc, limit.w]; exact hRlim.w))
  have hWnlim : IsPullback (yoneda.map awn) pW wn (limit.π D n.left) := by
    simpa only [awn, yoneda.map_preimage] using
      isPullback_lift_of_comp_eq Cn.isPullback.flip (limit.w D n.hom) hWlim
  have hRnlim : IsPullback (yoneda.map arn) pR rn (limit.π D n.left) := by
    simpa only [arn, yoneda.map_preimage] using
      isPullback_lift_of_comp_eq hRn (limit.w D n.hom) hRlim
  have hArnBr : yoneda.map arn ≫ yoneda.map br = yoneda.map arm := by simp [arn]
  have hAwnBw : yoneda.map awn ≫ yoneda.map Cn.toChart = yoneda.map awm := by simp [awn]
  have hsnCompat : arn ≫ sn = K.s ≫ awn := by
    apply yoneda.map_injective
    apply Cn.isPullback.hom_ext
    · simp only [Functor.map_comp, Category.assoc]
      change yoneda.map arn ≫ rn = yoneda.map K.s ≫ yoneda.map awn ≫ wn
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
      change yoneda.map arn ≫ yoneda.map tn ≫ wn =
        yoneda.map K.t ≫ yoneda.map awn ≫ wn
      rw [htn, hRnlim.w, hWnlim.w, ← Category.assoc, hs]
    · simp only [Functor.map_comp, Category.assoc]
      rw [← yoneda.map_comp tn Cn.toChart, ← htnBr, yoneda.map_comp,
        ← Category.assoc, hArnBr, hAwnBw]
      exact congrArg yoneda.map htmCompat
  have hsnSquare : IsPullback arn K.s sn awn :=
    isPullback_of_isPullback_yoneda_comp hsnCompat hWnlim hRnlim rfl ht
  have htnLimitSquare : IsPullback arn K.t tn awn :=
    isPullback_of_isPullback_yoneda_comp htnCompat hWnlim hRnlim htn hs
  have hRnlim' : IsPullback (yoneda.map arn) (yoneda.map K.s ≫ w ≫ Y.hom)
      (yoneda.map sn ≫ wn) (limit.π D n.left) := by
    rw [show (yoneda.map K.s ≫ w ≫ Y.hom) = pR from by rw [← hw]; exact ht]
    exact hRnlim
  exact exists_model_of_stage_relation_of_limitFacts B S hS hZ D hD hAffine hQc hQs hFacts
    n.left hX Y hY w hws hwe K.s K.t K.kernelPair
    (show IsAffine (Q.obj Wn) from Cn.U.property) wn sn tn htn hsnEtale htnEtale
    hWnFp hRnFp awn arn (by rw [← hw]; exact hWnlim) hRnlim' hsnCompat htnCompat

section BoundedInterface

include hSize hHomSize

/-- A bound on the index category supplies the three facts the descent argument needs: this is
the only place the bound is used. -/
private noncomputable def limitFacts_of_indexBound : LimitFacts B S hS D where
  limAlg := AlgebraicGeometry.Space.isAlgebraicSpace_limit B S hS D hSize hHomSize hD hAffine
  piAff := fun i => AlgebraicGeometry.Space.isAffineHom_limitπ_of_chartsBounded B S hS D
    (AlgebraicGeometry.Space.chartsBounded_of_lt_cof_ord B S hS D hSize hHomSize) hAffine i
  chartLim := fun hAff i₀ U₀ q₀ U p q h => by
    let T := (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀
    let E := affineStageChartOverDiagramOfLimitFacts B S hS D i₀ U₀ q₀ hAff
    let c := affineStageChartConeOfLimitFacts B S hS D i₀ U₀ q₀ hAff U p q h
    let hc := affineStageChartConeIsLimitOfLimitFacts B S hS D i₀ U₀ q₀ hAff U p q h
    let : IsConnected (Over i₀) := IsCofiltered.isConnected _
    have hE : ∀ j,
        IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (E.obj j).left) :=
      fun j => (affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAff j).U.property
    exact isLimit_toScheme_of_affine B S hS (cardinalMk_over_lt B hSize hHomSize i₀)
      (E ⋙ Over.forget T) hE ((Over.forget T).mapCone c)
      (isLimitOfPreserves (Over.forget T) hc)

end BoundedInterface

section ChartLimitInterface

omit hD hAffine hQc hQs in
/-- **The affine chart systems of an inverse system of algebraic spaces have their limits
computed in schemes.** For every stage `i₀`, every affine object `U₀` of the site with a
morphism `q₀ : U₀ ⟶ D i₀`, every system of base changes `F j = U₀ ×_{D i₀} D j` over the stages
`j ⟶ i₀` (presented by the maps `toStage j : F j ⟶ D j` and the cartesian squares `hpb`), and
every cone `c` over that system whose apex is the base change `U₀ ×_{D i₀} lim D` (the square
`hp`, compatibly with the stage maps), the cone of underlying schemes is a limit.

This is the condition under which the descent of finite-presentation algebraic spaces and their
morphisms to a finite stage (Stacks 07SK) runs without a bound on the index category: a bound on
the index category implies it, and it holds as well for systems whose limits are presented at
the level of schemes, such as the systems of quotients built in the proof of Stacks 07SU. -/
def AffineChartLimitsInSchemes : Prop :=
  ∀ (i₀ : I) (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (F : Over i₀ ⥤ Over ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀))
    (toStage : ∀ j : Over i₀, yoneda.obj (F.obj j).left ⟶ D.obj j.left),
    (∀ {j k : Over i₀} (e : j ⟶ k),
      yoneda.map (F.map e).left ≫ toStage k = toStage j ≫ D.map e.left) →
    (∀ j : Over i₀, IsPullback (toStage j) (yoneda.map (F.obj j).hom) (D.map j.hom) q₀) →
    ∀ (c : Cone F) (p : yoneda.obj c.pt.left ⟶ limit D),
    IsPullback p (yoneda.map c.pt.hom) (limit.π D i₀) q₀ →
    (∀ j : Over i₀, yoneda.map (c.π.app j).left ≫ toStage j = p ≫ limit.π D j.left) →
    Nonempty (IsLimit ((Over.forget ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⋙
        AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone c))

variable {B S hS D} in
omit hD hAffine hQc hQs in
/-- Under `AlgebraicGeometry.Space.AffineChartLimitsInSchemes`, the private chart systems of
this file have their limits computed in schemes. -/
private noncomputable def chartLim_of_affineChartLimitsInSchemes
    (hC : AffineChartLimitsInSchemes B S hS D)
    (hAff : ∀ {i j : I} (f : i ⟶ j), AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    (i₀ : I) (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (U : AlgebraicGeometry.BigFppfOver B S hS) (p : yoneda.obj U ⟶ limit D)
    (q : U ⟶ (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀)
    (h : IsPullback p (yoneda.map q) (limit.π D i₀) q₀) :
    IsLimit ((Over.forget ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⋙
        AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone
      (affineStageChartConeOfLimitFacts B S hS D i₀ U₀ q₀ hAff U p q h)) :=
  Classical.choice <| hC i₀ U₀ q₀ (affineStageChartOverDiagramOfLimitFacts B S hS D i₀ U₀ q₀ hAff)
    (fun j => (affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAff j).toStage)
    (fun e => affineStageChartMap_toStage_of_limitFacts B S hS D i₀ U₀ q₀ hAff e)
    (fun j => (affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAff j).isPullback)
    (affineStageChartConeOfLimitFacts B S hS D i₀ U₀ q₀ hAff U p q h) p h
    (fun j => by
      change yoneda.map (affineStageChartLiftOfLimitFacts B S hS D i₀ U₀ q₀ hAff U p q h j) ≫ _ = _
      simp only [affineStageChartLiftOfLimitFacts, Functor.map_preimage, IsPullback.lift_fst]
      rfl)

variable (hL : AlgebraicGeometry.IsAlgebraicSpace B S hS (limit D))
  (hπ : ∀ i : I, AlgebraicGeometry.Space.IsAffineHom B S hS (limit.π D i))
  (hC : AffineChartLimitsInSchemes B S hS D)

omit hD hAffine hQc hQs in
/-- The three facts the descent argument needs, from an algebraic limit with affine
projections whose affine chart systems have their limits computed in schemes. -/
private noncomputable def limitFacts_of_affineChartLimitsInSchemes : LimitFacts B S hS D where
  limAlg := hL
  piAff := hπ
  chartLim := fun hAff i₀ U₀ q₀ U p q h =>
    chartLim_of_affineChartLimitsInSchemes hC hAff i₀ U₀ q₀ U p q h


/-- **Stacks 07SK, fullness, without a bound on the index category.** For an inverse system of
quasi-compact quasi-separated algebraic spaces with affine transition morphisms whose limit is
an algebraic space with affine projections and whose affine chart systems have their limits
computed in schemes, a morphism between base changes of finite-presentation algebraic spaces
is defined at a sufficiently late stage. -/
theorem exists_morphism_after_baseChange_of_affineChartLimitsInSchemes
    (hL : AlgebraicGeometry.IsAlgebraicSpace B S hS (limit D))
    (hπ : ∀ i : I, AlgebraicGeometry.Space.IsAffineHom B S hS (limit.π D i))
    (hC : AffineChartLimitsInSchemes B S hS D)
    (i : I) (Yᵢ Zᵢ : Over (D.obj i))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Yᵢ.left)
    (hZ' : AlgebraicGeometry.IsAlgebraicSpace B S hS Zᵢ.left)
    (hYfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Yᵢ.hom)
    (hZfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Zᵢ.hom)
    (f : (Over.pullback (limit.π D i)).obj Yᵢ ⟶
      (Over.pullback (limit.π D i)).obj Zᵢ) :
    ∃ (j : I) (e : j ⟶ i)
      (g : (Over.pullback (D.map e)).obj Yᵢ ⟶
        (Over.pullback (D.map e)).obj Zᵢ)
      (α : (Over.pullback (limit.π D j)).obj
          ((Over.pullback (D.map e)).obj Yᵢ) ≅
        (Over.pullback (limit.π D i)).obj Yᵢ)
      (β : (Over.pullback (limit.π D j)).obj
          ((Over.pullback (D.map e)).obj Zᵢ) ≅
        (Over.pullback (limit.π D i)).obj Zᵢ),
      (α.hom.left ≫ pullback.fst Yᵢ.hom (limit.π D i) =
        pullback.fst ((Over.pullback (D.map e)).obj Yᵢ).hom (limit.π D j) ≫
          pullback.fst Yᵢ.hom (D.map e)) ∧
      (β.hom.left ≫ pullback.fst Zᵢ.hom (limit.π D i) =
        pullback.fst ((Over.pullback (D.map e)).obj Zᵢ).hom (limit.π D j) ≫
          pullback.fst Zᵢ.hom (D.map e)) ∧
      α.hom ≫ f = (Over.pullback (limit.π D j)).map g ≫ β.hom :=
  exists_morphism_after_baseChange_aux B S hS hZ D hD hAffine hQc hQs
    (limitFacts_of_affineChartLimitsInSchemes B S hS D hL hπ hC)
    i Yᵢ Zᵢ hY hZ' hYfp hZfp f

omit hQs in
/-- **Stacks 07SK, faithfulness, without a bound on the index category**, under the hypotheses
of `AlgebraicGeometry.Space.exists_morphism_after_baseChange_of_affineChartLimitsInSchemes`. -/
theorem eventually_eq_of_baseChange_eq_of_affineChartLimitsInSchemes
    (hL : AlgebraicGeometry.IsAlgebraicSpace B S hS (limit D))
    (hπ : ∀ i : I, AlgebraicGeometry.Space.IsAffineHom B S hS (limit.π D i))
    (hC : AffineChartLimitsInSchemes B S hS D)
    (i : I) (Yᵢ Zᵢ : Over (D.obj i))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Yᵢ.left)
    (hZ' : AlgebraicGeometry.IsAlgebraicSpace B S hS Zᵢ.left)
    (hYfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Yᵢ.hom)
    (hZfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Zᵢ.hom)
    (f g : Yᵢ ⟶ Zᵢ)
    (hfg : (Over.pullback (limit.π D i)).map f =
      (Over.pullback (limit.π D i)).map g) :
    ∃ (j : I) (e : j ⟶ i),
      (Over.pullback (D.map e)).map f =
        (Over.pullback (D.map e)).map g :=
  eventually_eq_of_baseChange_eq_aux B S hS D hD hAffine hQc
    (limitFacts_of_affineChartLimitsInSchemes B S hS D hL hπ hC)
    i Yᵢ Zᵢ hY hZ' hYfp hZfp f g hfg

/-- **Stacks 07SK, essential surjectivity, without a bound on the index category**, under the
hypotheses of
`AlgebraicGeometry.Space.exists_morphism_after_baseChange_of_affineChartLimitsInSchemes`. -/
theorem exists_model_of_finitePresentation_of_affineChartLimitsInSchemes
    (hL : AlgebraicGeometry.IsAlgebraicSpace B S hS (limit D))
    (hπ : ∀ i : I, AlgebraicGeometry.Space.IsAffineHom B S hS (limit.π D i))
    (hC : AffineChartLimitsInSchemes B S hS D)
    (Y : Over (limit D))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y.left)
    (hFp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Y.hom) :
    ∃ (i : I) (Yᵢ : Over (D.obj i)),
      AlgebraicGeometry.IsAlgebraicSpace B S hS Yᵢ.left ∧
        AlgebraicGeometry.Space.IsFinitePresentation B S hS Yᵢ.hom ∧
        Nonempty (Y ≅ (Over.pullback (limit.π D i)).obj Yᵢ) :=
  exists_model_of_finitePresentation_aux B S hS hZ D hD hAffine hQc hQs
    (limitFacts_of_affineChartLimitsInSchemes B S hS D hL hπ hC)
    Y hY hFp

end ChartLimitInterface


end AlgebraicGeometry.Space

end
