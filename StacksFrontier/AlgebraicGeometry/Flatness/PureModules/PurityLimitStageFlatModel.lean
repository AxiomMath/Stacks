module

public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Limits.IndexHomUniverse
public import StacksFrontier.AlgebraicGeometry.Limits.RelativeApproximation.FlatDescent
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MorphismDescentGlue
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FlatLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.IsoTransport
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.EtaleBase
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PullbackFlatness
public import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic

/-!
# Descending a morphism, a module and its relative flatness to a finite stage

Let `S = lim S_k` be the limit of an inverse system of affine schemes indexed by a directed set,
let `f : X ⟶ S` be of finite presentation, let `ℱ` be a quasi-coherent `𝒪_X`-module of finite
presentation and let `s` be a point of `S` such that `ℱ` is flat over `S` at every point of the
fibre `X_s`.  This file produces a finite stage `k` carrying all of that data: a morphism
`X_k ⟶ S_k` of finite presentation, a finitely presented quasi-coherent module `ℱ_k` which is
flat over `S_k` at every point of `(X_k)_{s_k}`, with `X = X_k ×_{S_k} S` and `ℱ` the pullback
of `ℱ_k`.

This is the first half of the proof of [Stacks Project, Tag 05MA]; the passage of purity to a
finite stage is the other half and is
`AlgebraicGeometry.exists_stage_isPureAlong`.

## Main results

* `AlgebraicGeometry.exists_stage_isFlatOverAt_fiber_of_isLimit`: the statement above.

## Implementation notes

The flatness is *not* descended pointwise on the fibre.  Following the source, the open locus
`U` where `ℱ` is flat over `S` — open by Tag 0399 — is shrunk to a quasi-compact open `U'`
still containing the quasi-compact fibre `X_s`, and it is the flatness of `ℱ` over `S` on the
whole of `U'` that descends, by Tag 05LY.  At the stage the fibre `(X_k)_{s_k}` is contained in
the descended open `U'_k`, because `X_s` surjects onto it, and flatness at its points follows.

Tag 05LY is stated for a morphism of objects over a stage, and the flatness it descends is
flatness relative to the base change of the *target* of that morphism.  To read it as flatness
over the stage itself the morphism is taken to be the structure morphism `X ⟶ S_k`, that is the
map to the terminal object `Over.mk (𝟙 S_k)` of the slice, whose base change is the stage only
up to the canonical isomorphism `S_k ×_{S_k} S_j ≅ S_j`.  That isomorphism is étale, so
`AlgebraicGeometry.isFlatOver_comp_iff_of_etale` removes it.

The reindexing by a directed set that the source uses costs nothing here: `Iᵒᵖ` is cofiltered
and, `I` lying in the universe of the schemes, essentially small, so the cofiltered forms of
Tags 01ZM, 01ZR, 01Z4 and 05LY apply to it directly.

## References

* [Stacks Project, Tag 0399](https://stacks.math.columbia.edu/tag/0399)
* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 05LY](https://stacks.math.columbia.edu/tag/05LY)
* [Stacks Project, Tag 05MA](https://stacks.math.columbia.edu/tag/05MA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

/-! ### Flatness over the base on an open subscheme -/

/-- Flatness over the base of the restriction of a module to an open subscheme, at every point
of that subscheme, is flatness of the module itself at every point of the open. -/
public theorem isFlatOver_pullback_opens_iff {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    (U : X.Opens) :
    IsFlatOver (U.ι ≫ f).toLRSHom.toShHom ((Scheme.Modules.pullback U.ι).obj F) ↔
      ∀ x ∈ U, IsFlatOverAt f.toLRSHom.toShHom F x :=
  ⟨fun h x hx => (isFlatOverAt_iff_modulePullback_isFlatOverAt U.ι f F ⟨x, hx⟩
      (Flat.stalkMap U.ι ⟨x, hx⟩)).mpr (h ⟨x, hx⟩),
    fun h x => (isFlatOverAt_iff_modulePullback_isFlatOverAt U.ι f F x
      (Flat.stalkMap U.ι x)).mp (h x.val x.property)⟩

/-- A quasi-compact open of the source on which a finitely presented quasi-coherent module is
flat over the base, containing the whole fibre over a point.  The flat locus is open by Tag
0399 and the fibre is quasi-compact, so a quasi-compact open fits in between. -/
public theorem exists_isCompact_opens_isFlatOverAt_of_fiber {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [QuasiCompact f] (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFinitePresentation] (s : S)
    (hflat : ∀ x : f.fiber s, IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s x)) :
    ∃ U : X.Opens, IsCompact (U : Set X) ∧ Set.range (f.fiberι s) ⊆ (U : Set X) ∧
      ∀ x ∈ U, IsFlatOverAt f.toLRSHom.toShHom F x := by
  obtain ⟨W, hWcpt, hWopen, hWsub, hWle⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between
      (isCompact_range (f.fiberι s).continuous) (isOpen_setOf_flatOverAt f F)
      (by rintro _ ⟨x, rfl⟩; exact hflat x)
  exact ⟨⟨W, hWopen⟩, hWcpt, hWsub, fun _ hx => hWle hx⟩

/-! ### Base change of an open subscheme -/

/-- Flatness over the base change of the base, read on the base change of an open subscheme of
the source, agrees with flatness at the points of the preimage of that open. -/
public theorem isFlatOverAt_pullback_opens_baseChange_iff {S T : Scheme.{u}} (b : T ⟶ S)
    (X : Over S) (F : X.left.Modules) (V : X.left.Opens)
    (x : (pullback (V.ι ≫ X.hom) b : Scheme.{u})) :
    IsFlatOverAt (pullback.snd X.hom b).toLRSHom.toShHom
        ((Scheme.Modules.pullback (pullback.fst X.hom b)).obj F)
        (((Over.pullback b).map (Over.homMk V.ι : Over.mk (V.ι ≫ X.hom) ⟶ X)).left x) ↔
      IsFlatOverAt (pullback.snd (V.ι ≫ X.hom) b).toLRSHom.toShHom
        ((Scheme.Modules.pullback (pullback.fst (V.ι ≫ X.hom) b)).obj
          ((Scheme.Modules.pullback V.ι).obj F)) x := by
  let Z : Over S := Over.mk (V.ι ≫ X.hom)
  let v : Z ⟶ X := Over.homMk V.ι
  let a := ((Over.pullback b).map v).left
  have hpb := overPullback_isPullback b Z X v
  have : IsOpenImmersion a :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hpb
      (inferInstanceAs (IsOpenImmersion V.ι))
  let H := (Scheme.Modules.pullback (pullback.fst X.hom b)).obj F
  have ha : a ≫ pullback.snd X.hom b = pullback.snd Z.hom b := by
    simp only [a, Over.pullback_map_left, pullback.lift_snd]
  let e : (Scheme.Modules.pullback a).obj H ≅
      (Scheme.Modules.pullback (pullback.fst Z.hom b)).obj
        ((Scheme.Modules.pullback V.ι).obj F) :=
    (Scheme.Modules.pullbackComp a (pullback.fst X.hom b)).app F ≪≫
      (Scheme.Modules.pullbackCongr hpb.w.symm).app F ≪≫
      ((Scheme.Modules.pullbackComp (pullback.fst Z.hom b) V.ι).app F).symm
  have h := isFlatOverAt_iff_modulePullback_isFlatOverAt a (pullback.snd X.hom b) H x
    (Flat.stalkMap a x)
  rw [ha] at h
  exact h.trans (isFlatOverAt_iff_of_moduleIso _ e x)

/-- Flatness over the base change of the base on the base change of an open subscheme of the
source is flatness at every point of the preimage of that open. -/
public theorem isFlatOver_pullback_opens_baseChange_iff {S T : Scheme.{u}} (b : T ⟶ S)
    (X : Over S) (F : X.left.Modules) (V : X.left.Opens) :
    IsFlatOver (pullback.snd (V.ι ≫ X.hom) b).toLRSHom.toShHom
        ((Scheme.Modules.pullback (pullback.fst (V.ι ≫ X.hom) b)).obj
          ((Scheme.Modules.pullback V.ι).obj F)) ↔
      ∀ y ∈ pullback.fst X.hom b ⁻¹ᵁ V,
        IsFlatOverAt (pullback.snd X.hom b).toLRSHom.toShHom
          ((Scheme.Modules.pullback (pullback.fst X.hom b)).obj F) y := by
  let Z : Over S := Over.mk (V.ι ≫ X.hom)
  let v : Z ⟶ X := Over.homMk V.ι
  let a := ((Over.pullback b).map v).left
  have hpb := overPullback_isPullback b Z X v
  refine ⟨fun h y hy => ?_, fun h x => ?_⟩
  · obtain ⟨x, -, hx⟩ := Scheme.exists_preimage_of_isPullback hpb
      (⟨(pullback.fst X.hom b) y, hy⟩ : V) y rfl
    exact hx ▸ (isFlatOverAt_pullback_opens_baseChange_iff b X F V x).mpr (h x)
  · refine (isFlatOverAt_pullback_opens_baseChange_iff b X F V x).mp (h _ ?_)
    have heq : (pullback.fst X.hom b) (a x) = V.ι ((pullback.fst Z.hom b) x) :=
      congrArg (fun k : ((Over.pullback b).obj Z).left ⟶ X.left => k x) hpb.w.symm
    change (pullback.fst X.hom b) (a x) ∈ V
    rw [heq]
    exact ((pullback.fst Z.hom b) x).property

/-! ### Flatness over a stage rather than over the base change of a slice object -/

/-- The structure morphism of a scheme over `S`, read as a morphism to the terminal object
`Over.mk (𝟙 S)` of the slice category. -/
public abbrev overToBase {S : Scheme.{u}} (X : Over S) : X ⟶ Over.mk (𝟙 S) :=
  Over.homMk X.hom (by simp)

/-- Flatness relative to the base change of the structure morphism of a slice object is
flatness relative to the base change of the base.  The two differ by the canonical isomorphism
`S ×_S T ≅ T`, which is étale. -/
public theorem isFlatOver_overPullback_overToBase_iff {S T : Scheme.{u}} (b : T ⟶ S)
    (X : Over S) (F : X.left.Modules) [F.IsQuasicoherent] :
    IsFlatOver ((Over.pullback b).map (overToBase X)).left.toLRSHom.toShHom
        ((Scheme.Modules.pullback (pullback.fst X.hom b)).obj F) ↔
      IsFlatOver (pullback.snd X.hom b).toLRSHom.toShHom
        ((Scheme.Modules.pullback (pullback.fst X.hom b)).obj F) := by
  let a : (pullback X.hom b : Scheme.{u}) ⟶ pullback (𝟙 S) b :=
    ((Over.pullback b).map (overToBase X)).left
  let G := (Scheme.Modules.pullback (pullback.fst X.hom b)).obj F
  have : G.IsQuasicoherent := @SheafOfModules.modulePullback_isQuasicoherent _ _
    (pullback.fst X.hom b).toLRSHom.toShHom F ‹F.IsQuasicoherent›
  have hcomp : a ≫ pullback.snd (𝟙 S) b = pullback.snd X.hom b :=
    pullback.lift_snd _ _ _
  have h := isFlatOver_comp_iff_of_etale a (pullback.snd (𝟙 S) b) G
  rw [hcomp] at h
  exact h.symm

/-! ### Tag 05LY as a statement about flatness over the stages -/

/-- **Tag 05LY, read as flatness over the stages.**  A finitely presented quasi-coherent module
on a scheme of finite presentation over a stage, whose base change to the limit is flat over the
limit, is flat over a later stage after base change to it. -/
public theorem exists_stage_isFlatOver_pullback {J : Type v} [Category.{v} J] [IsCofiltered J]
    [EssentiallySmall.{u} J] (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : J} (e : i ⟶ j), IsAffineHom (D.map e)] [∀ i : J, CompactSpace (D.obj i)]
    [∀ i : J, QuasiSeparatedSpace (D.obj i)] (i : J) (X : Over (D.obj i))
    (hf : FinitePresentation X.hom) (F : X.left.Modules) (hFqc : F.IsQuasicoherent)
    (hFfp : F.IsFinitePresentation)
    (hflat : IsFlatOver (pullback.snd X.hom (c.π.app i)).toLRSHom.toShHom
      ((Scheme.Modules.pullback (pullback.fst X.hom (c.π.app i))).obj F)) :
    ∃ (j : J) (e : j ⟶ i),
      IsFlatOver (pullback.snd X.hom (D.map e)).toLRSHom.toShHom
        ((Scheme.Modules.pullback (pullback.fst X.hom (D.map e))).obj F) := by
  have : F.IsQuasicoherent := hFqc
  obtain ⟨j, e, hj⟩ := @eventually_isFlatOver_modulePullback _ _ _ _ D c hc _ _ _ i X
    (Over.mk (𝟙 (D.obj i))) hf
    (FinitePresentation.mk (f := 𝟙 (D.obj i)) inferInstance inferInstance inferInstance)
    (overToBase X) F hFqc hFfp
    ((isFlatOver_overPullback_overToBase_iff (c.π.app i) X F).mpr hflat)
  exact ⟨j, e, (isFlatOver_overPullback_overToBase_iff (D.map e) X F).mp hj⟩

/-- **Descending flatness over the base on a quasi-compact open to a finite stage.**  If a
finitely presented quasi-coherent module on a scheme of finite presentation over a stage is,
after base change to the limit, flat over the limit at every point above a quasi-compact open
`V` of that scheme, then the same holds above `V` after base change to some later stage. -/
public theorem exists_stage_isFlatOverAt_preimage_opens {J : Type v} [Category.{v} J]
    [IsCofiltered J] [EssentiallySmall.{u} J] (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : J} (e : i ⟶ j), IsAffineHom (D.map e)] [∀ i : J, CompactSpace (D.obj i)]
    [∀ i : J, QuasiSeparatedSpace (D.obj i)] (i : J) (X : Over (D.obj i))
    (hf : FinitePresentation X.hom) (F : X.left.Modules) (hFqc : F.IsQuasicoherent)
    (hFfp : F.IsFinitePresentation) (V : X.left.Opens) (hV : IsCompact (V : Set X.left))
    (hflat : ∀ y ∈ pullback.fst X.hom (c.π.app i) ⁻¹ᵁ V,
      IsFlatOverAt (pullback.snd X.hom (c.π.app i)).toLRSHom.toShHom
        ((Scheme.Modules.pullback (pullback.fst X.hom (c.π.app i))).obj F) y) :
    ∃ (j : J) (e : j ⟶ i), ∀ y ∈ pullback.fst X.hom (D.map e) ⁻¹ᵁ V,
      IsFlatOverAt (pullback.snd X.hom (D.map e)).toLRSHom.toShHom
        ((Scheme.Modules.pullback (pullback.fst X.hom (D.map e))).obj F) y := by
  have : LocallyOfFinitePresentation X.hom := hf.1
  have : QuasiSeparated X.hom := hf.2.2
  have : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  have : CompactSpace V := isCompact_iff_compactSpace.mp hV
  let Z : Over (D.obj i) := Over.mk (V.ι ≫ X.hom)
  have hZ : FinitePresentation Z.hom :=
    FinitePresentation.mk (f := V.ι ≫ X.hom) inferInstance inferInstance inferInstance
  let G := (Scheme.Modules.pullback V.ι).obj F
  have hGqc : G.IsQuasicoherent := @SheafOfModules.modulePullback_isQuasicoherent _ _
    V.ι.toLRSHom.toShHom F hFqc
  have hGfp : G.IsFinitePresentation :=
    @Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _ V.ι.toLRSHom.toShHom F hFfp
  obtain ⟨j, e, he⟩ := exists_stage_isFlatOver_pullback D c hc i Z hZ G hGqc hGfp
    ((isFlatOver_pullback_opens_baseChange_iff (c.π.app i) X F V).mpr hflat)
  exact ⟨j, e, (isFlatOver_pullback_opens_baseChange_iff (D.map e) X F V).mp he⟩

/-! ### Descending the morphism, the module and a quasi-compact open together -/

/-- The inverse of the comparison between iterated and direct base change carries the two first
projections of the iterated base change to the first projection of the direct one. -/
private theorem overPullbackCompIso_inv_left_fst_fst {S S' T : Scheme.{u}} (p : S ⟶ T)
    (q : S' ⟶ S) (r : S' ⟶ T) (h : q ≫ p = r) (X : Over T) :
    (overPullbackCompIso p q r h X).inv.left ≫
        pullback.fst ((Over.pullback p).obj X).hom q ≫ pullback.fst X.hom p =
      pullback.fst X.hom r := by
  rw [← overPullbackCompIso_fst p q r h X, ← Category.assoc, ← Over.comp_left, Iso.inv_hom_id,
    Over.id_left, Category.id_comp]

/-- **Tags 01ZM (1), 01ZR (1) and 01Z4 (1) together.**  A scheme of finite presentation over the
limit, a finitely presented quasi-coherent module on it and a quasi-compact open of it all come
from one finite stage. -/
public theorem exists_stage_model_with_opens {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ k : Iᵒᵖ, IsAffine (D.obj k)] (X : Over c.pt) (hf : FinitePresentation X.hom)
    (F : X.left.Modules) (hFfp : F.IsFinitePresentation)
    (U : X.left.Opens) (hU : IsCompact (U : Set X.left)) :
    ∃ (i : I) (Xᵢ : Over (D.obj (op i))) (Fᵢ : Xᵢ.left.Modules),
      FinitePresentation Xᵢ.hom ∧ Fᵢ.IsQuasicoherent ∧ Fᵢ.IsFinitePresentation ∧
      ∃ (α : X ≅ (Over.pullback (c.π.app (op i))).obj Xᵢ) (V : Xᵢ.left.Opens),
        IsCompact (V : Set Xᵢ.left) ∧
        (α.hom.left ≫ pullback.fst Xᵢ.hom (c.π.app (op i))) ⁻¹ᵁ V = U ∧
        Nonempty (F ≅ (Scheme.Modules.pullback
          (α.hom.left ≫ pullback.fst Xᵢ.hom (c.π.app (op i)))).obj Fᵢ) := by
  classical
  have : F.IsFinitePresentation := hFfp
  have : ∀ {a b : Iᵒᵖ} (e : a ⟶ b), IsAffineHom (D.map e) := fun e => isAffineHom_of_isAffine _
  obtain ⟨i₀, X₀, hfp₀, ⟨eX₀⟩⟩ :=
    LimitFPObjectDescent.exists_model_of_finitePresentation D c hc X hf
  have : LocallyOfFinitePresentation X₀.hom := hfp₀.1
  have : QuasiCompact X₀.hom := hfp₀.2.1
  have : QuasiSeparated X₀.hom := hfp₀.2.2
  have : CompactSpace X₀.left := QuasiCompact.compactSpace_of_compactSpace X₀.hom
  have : QuasiSeparatedSpace X₀.left := quasiSeparatedSpace_of_quasiSeparated X₀.hom
  -- The base change of the system along `X₀ ⟶ S_{i₀}`, indexed by the objects over `i₀`.
  let Xdiag : Over i₀ ⥤ Scheme.{u} :=
    Over.post D ⋙ Over.pullback X₀.hom ⋙ Over.forget X₀.left
  let cX : Cone Xdiag :=
    (Over.pullback X₀.hom ⋙ Over.forget X₀.left).mapCone ((Over.conePost D i₀).obj c)
  have hcX : IsLimit cX :=
    isLimitOfPreserves (Over.pullback X₀.hom ⋙ Over.forget X₀.left) (Over.isLimitConePost i₀ hc)
  let σ : cX.pt ≅ ((Over.pullback (c.π.app i₀)).obj X₀).left :=
    pullbackSymmetry (c.π.app i₀) X₀.hom
  let eη : cX.pt ≅ X.left := σ ≪≫ (Over.forget c.pt).mapIso eX₀.symm
  let Fbase := (Scheme.Modules.pullback eη.hom).obj F
  have hFbasefp : Fbase.IsFinitePresentation :=
    @Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _ eη.hom.toLRSHom.toShHom F hFfp
  have : Fbase.IsFinitePresentation := hFbasefp
  have hXdiagAff : ∀ {a b : Over i₀} (g : a ⟶ b), IsAffineHom (Xdiag.map g) := by
    intro a b g
    have hbase : IsAffineHom ((Over.post D).map g).left := by
      change IsAffineHom (D.map g.left)
      infer_instance
    exact MorphismProperty.overPullbackMap (P := @IsAffineHom) X₀.hom ((Over.post D).map g) hbase
  have hXdiagCpt (a : Over i₀) : CompactSpace (Xdiag.obj a) := by
    have : IsAffine ((Over.post D).obj a).left := ‹∀ k : Iᵒᵖ, IsAffine (D.obj k)› a.left
    have : CompactSpace ((Over.post D).obj a).left :=
      Scheme.compactSpace_of_isAffine ((Over.post D).obj a).left
    have : LocallyOfFinitePresentation (pullback.fst ((Over.post D).obj a).hom X₀.hom) :=
      MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
        (IsPullback.of_hasPullback ((Over.post D).obj a).hom X₀.hom).flip hfp₀.1
    have : QuasiCompact (pullback.fst ((Over.post D).obj a).hom X₀.hom) := by infer_instance
    exact QuasiCompact.compactSpace_of_compactSpace
      (pullback.fst ((Over.post D).obj a).hom X₀.hom)
  have hXdiagQS (a : Over i₀) : QuasiSeparatedSpace (Xdiag.obj a) := by
    have : IsAffine ((Over.post D).obj a).left := ‹∀ k : Iᵒᵖ, IsAffine (D.obj k)› a.left
    have : QuasiSeparatedSpace ((Over.post D).obj a).left :=
      quasiSeparatedSpace_of_isAffine ((Over.post D).obj a).left
    have : QuasiSeparated (pullback.fst ((Over.post D).obj a).hom X₀.hom) :=
      MorphismProperty.of_isPullback (P := @QuasiSeparated)
        (IsPullback.of_hasPullback ((Over.post D).obj a).hom X₀.hom).flip hfp₀.2.2
    exact quasiSeparatedSpace_of_quasiSeparated
      (pullback.fst ((Over.post D).obj a).hom X₀.hom)
  -- Tag 01ZR (1): the module comes from a stage of the base-changed system.
  obtain ⟨a₀, F₀, hF₀, ⟨eF₀⟩⟩ :=
    Stacks.AlgebraicGeometry.ModuleLimits.exists_isFinitePresentation_pullback_iso_of_qcqs
      Xdiag cX hcX Fbase
  -- Tag 01Z4 (1): the quasi-compact open comes from a stage of the base-changed system.
  obtain ⟨b, W, hW, hWpre⟩ :=
    AlgebraicGeometry.exists_preimage_eq Xdiag cX hcX (eη.hom ⁻¹ᵁ U)
      (QuasiCompact.isCompact_preimage (f := eη.hom) _ U.isOpen hU)
  obtain ⟨a, fa₀, fb, -⟩ := IsCofilteredOrEmpty.cone_objs a₀ b
  let Fₐ := (Scheme.Modules.pullback (Xdiag.map fa₀)).obj F₀
  have hFₐ : Fₐ.IsFinitePresentation :=
    @Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _
      (Xdiag.map fa₀).toLRSHom.toShHom F₀ hF₀
  let eFbase : Fbase ≅ (Scheme.Modules.pullback (cX.π.app a)).obj Fₐ :=
    eF₀ ≪≫ ((Scheme.Modules.pullbackCongr (cX.w fa₀)).app F₀).symm ≪≫
      ((Scheme.Modules.pullbackComp (cX.π.app a) (Xdiag.map fa₀)).app F₀).symm
  let Vₐ := Xdiag.map fb ⁻¹ᵁ W
  have hVₐ : IsCompact (Vₐ : Set (Xdiag.obj a)) :=
    QuasiCompact.isCompact_preimage (f := Xdiag.map fb) _ W.isOpen hW
  have hVₐpre : cX.π.app a ⁻¹ᵁ Vₐ = eη.hom ⁻¹ᵁ U := by
    rw [show (Vₐ : (Xdiag.obj a).Opens) = Xdiag.map fb ⁻¹ᵁ W from rfl,
      ← Scheme.Hom.comp_preimage, cX.w fb, hWpre]
  -- Transport from the base-changed system to the slice over the stage.
  let Xᵢ : Over (D.obj a.left) := (Over.pullback (D.map a.hom)).obj X₀
  let τ : Xdiag.obj a ≅ Xᵢ.left := pullbackSymmetry (D.map a.hom) X₀.hom
  have : LocallyOfFinitePresentation Xᵢ.hom :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
      (IsPullback.of_hasPullback X₀.hom (D.map a.hom)) hfp₀.1
  have : QuasiCompact Xᵢ.hom :=
    MorphismProperty.of_isPullback (P := @QuasiCompact)
      (IsPullback.of_hasPullback X₀.hom (D.map a.hom)) hfp₀.2.1
  have : QuasiSeparated Xᵢ.hom :=
    MorphismProperty.of_isPullback (P := @QuasiSeparated)
      (IsPullback.of_hasPullback X₀.hom (D.map a.hom)) hfp₀.2.2
  have hfᵢ : FinitePresentation Xᵢ.hom :=
    FinitePresentation.mk (f := Xᵢ.hom) inferInstance inferInstance inferInstance
  let Fᵢ : Xᵢ.left.Modules := (Scheme.Modules.pullback τ.inv).obj Fₐ
  have hFᵢfp : Fᵢ.IsFinitePresentation :=
    @Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _ τ.inv.toLRSHom.toShHom Fₐ hFₐ
  have : Fᵢ.IsFinitePresentation := hFᵢfp
  have hFₐqc : Fₐ.IsQuasicoherent := by
    obtain ⟨σ, -⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData Fₐ (self := hFₐ)
    exact σ.isQuasicoherent
  have hFᵢqc : Fᵢ.IsQuasicoherent :=
    @SheafOfModules.modulePullback_isQuasicoherent _ _ τ.inv.toLRSHom.toShHom Fₐ hFₐqc
  let α : X ≅ (Over.pullback (c.π.app a.left)).obj Xᵢ :=
    eX₀ ≪≫ (overPullbackCompIso (D.map a.hom) (c.π.app a.left) (c.π.app i₀) (c.w a.hom) X₀).symm
  have hqfst : cX.π.app a ≫ pullback.fst ((Over.post D).obj a).hom X₀.hom =
      pullback.fst (c.π.app i₀) X₀.hom ≫ c.π.app a.left := by
    simp only [Over.post, Over.pullback, Over.mk_left, Over.conePost, Functor.const_obj_obj,
      Functor.mapCone_pt, Functor.comp_obj, Over.mk_hom, Over.forget_obj, Functor.mapCone_π_app,
      Functor.comp_map, Over.forget_map, Over.homMk_left, Xdiag, cX]
    exact pullback.lift_fst _ _ _
  have hqsnd : cX.π.app a ≫ pullback.snd ((Over.post D).obj a).hom X₀.hom =
      pullback.snd (c.π.app i₀) X₀.hom := by
    simp only [Over.post, Over.pullback, Over.mk_left, Over.conePost, Functor.const_obj_obj,
      Functor.mapCone_pt, Functor.comp_obj, Over.mk_hom, Over.forget_obj, Functor.mapCone_π_app,
      Functor.comp_map, Over.forget_map, Over.homMk_left, Xdiag, cX]
    exact pullback.lift_snd _ _ _
  have hmap : eη.inv ≫ cX.π.app a =
      α.hom.left ≫ pullback.fst Xᵢ.hom (c.π.app a.left) ≫ τ.inv := by
    have : IsIso eX₀.hom.left := (Over.forget c.pt).map_isIso eX₀.hom
    have : Epi eX₀.hom.left := by infer_instance
    let ι := overPullbackCompIso (D.map a.hom) (c.π.app a.left) (c.π.app i₀) (c.w a.hom) X₀
    have hfst := overPullbackCompIso_inv_left_fst_fst (D.map a.hom) (c.π.app a.left)
      (c.π.app i₀) (c.w a.hom) X₀
    have hmid : ι.inv.left ≫ pullback.fst Xᵢ.hom (c.π.app a.left) ≫
        pullback.snd X₀.hom (D.map a.hom) =
          pullback.snd X₀.hom (c.π.app i₀) ≫ c.π.app a.left := by
      rw [show pullback.fst Xᵢ.hom (c.π.app a.left) ≫ pullback.snd X₀.hom (D.map a.hom) =
        pullback.snd Xᵢ.hom (c.π.app a.left) ≫ c.π.app a.left from pullback.condition,
        ← Category.assoc]
      exact congrArg (· ≫ c.π.app a.left) (Over.w ι.inv)
    simp only [eη, α, Iso.trans_inv, Functor.mapIso_symm, Iso.symm_inv, Iso.symm_hom,
      Iso.trans_hom, Over.comp_left, Category.assoc]
    refine (cancel_epi eX₀.hom.left).mpr (pullback.hom_ext ?_ ?_)
    · rw [Category.assoc, Category.assoc, Category.assoc, hqfst]
      exact (pullbackSymmetry_inv_comp_fst_assoc _ _ _).trans (hmid.symm.trans
        (congrArg (ι.inv.left ≫ pullback.fst Xᵢ.hom (c.π.app a.left) ≫ ·)
          (pullbackSymmetry_inv_comp_fst (D.map a.hom) X₀.hom).symm))
    · rw [Category.assoc, Category.assoc, Category.assoc, hqsnd]
      exact (pullbackSymmetry_inv_comp_snd _ _).trans (hfst.symm.trans
        (congrArg (ι.inv.left ≫ pullback.fst Xᵢ.hom (c.π.app a.left) ≫ ·)
          (pullbackSymmetry_inv_comp_snd (D.map a.hom) X₀.hom).symm))
  let eModule : F ≅ (Scheme.Modules.pullback
      (α.hom.left ≫ pullback.fst Xᵢ.hom (c.π.app a.left))).obj Fᵢ :=
    (((Scheme.Modules.pullbackComp eη.inv eη.hom).app F ≪≫
      (Scheme.Modules.pullbackCongr eη.inv_hom_id).app F ≪≫
      (Scheme.Modules.pullbackId X.left).app F).symm ≪≫
      (Scheme.Modules.pullback eη.inv).mapIso eFbase ≪≫
      (Scheme.Modules.pullbackComp eη.inv (cX.π.app a)).app Fₐ ≪≫
      (Scheme.Modules.pullbackCongr hmap).app Fₐ ≪≫
      ((Scheme.Modules.pullbackComp
        (α.hom.left ≫ pullback.fst Xᵢ.hom (c.π.app a.left)) τ.inv).app Fₐ).symm)
  refine ⟨a.left.unop, Xᵢ, Fᵢ, hfᵢ, hFᵢqc, hFᵢfp, α, τ.inv ⁻¹ᵁ Vₐ,
    QuasiCompact.isCompact_preimage (f := τ.inv) _ Vₐ.isOpen hVₐ, ?_, ⟨eModule⟩⟩
  rw [← Scheme.Hom.comp_preimage, Category.assoc, ← hmap, Scheme.Hom.comp_preimage, hVₐpre,
    ← Scheme.Hom.comp_preimage, eη.inv_hom_id]
  simp

/-! ### Transporting the model along the identification of the base change -/

/-- A quasi-compact open of the model whose preimage contains the fibre of the base change
contains the fibre of the model. -/
public theorem range_fiberι_subset_of_isPullback {X Y S T : Scheme.{u}} {a : X ⟶ Y} {f : X ⟶ S}
    {g : Y ⟶ T} {b : S ⟶ T} (h : IsPullback a f g b) (s : S) (U : Set Y)
    (hcover : Set.range (f.fiberι s) ⊆ a ⁻¹' U) :
    Set.range (g.fiberι (b s)) ⊆ U := by
  rintro _ ⟨y, rfl⟩
  obtain ⟨x, hax, hfx⟩ :=
    Scheme.exists_preimage_of_isPullback h _ s (g.apply_fiberι (b s) y)
  have hx : x ∈ Set.range (f.fiberι s) := by rwa [f.range_fiberι]
  exact hax ▸ hcover hx

/-- The identification of a scheme over the limit with the base change of its model is a
pullback square. -/
public theorem isPullback_of_model_iso {S T : Scheme.{u}} (b : S ⟶ T) (X : Over S) (Y : Over T)
    (α : X ≅ (Over.pullback b).obj Y) :
    IsPullback (α.hom.left ≫ pullback.fst Y.hom b) X.hom Y.hom b := by
  refine (IsPullback.of_hasPullback Y.hom b).of_iso' ((Over.forget S).mapIso α) (Iso.refl _)
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simpa using Over.w α.hom
  · simp
  · simp

/-- Flatness over the base at every point of a quasi-compact open, transported to the base
change of the model. -/
public theorem isFlatOverAt_model_pullback {S T : Scheme.{u}} (b : S ⟶ T) (X : Over S)
    (Y : Over T) (F : X.left.Modules) (G : Y.left.Modules)
    (α : X ≅ (Over.pullback b).obj Y)
    (eF : F ≅ (Scheme.Modules.pullback (α.hom.left ≫ pullback.fst Y.hom b)).obj G)
    (V : Y.left.Opens)
    (hflat : ∀ x ∈ (α.hom.left ≫ pullback.fst Y.hom b) ⁻¹ᵁ V,
      IsFlatOverAt X.hom.toLRSHom.toShHom F x) :
    ∀ y ∈ pullback.fst Y.hom b ⁻¹ᵁ V,
      IsFlatOverAt (pullback.snd Y.hom b).toLRSHom.toShHom
        ((Scheme.Modules.pullback (pullback.fst Y.hom b)).obj G) y := by
  let q := α.hom.left
  let H := (Scheme.Modules.pullback (pullback.fst Y.hom b)).obj G
  have : IsIso q := (Over.forget S).map_isIso α.hom
  let e : F ≅ (Scheme.Modules.pullback q).obj H :=
    eF ≪≫ ((Scheme.Modules.pullbackComp q (pullback.fst Y.hom b)).app G).symm
  intro y hy
  have hqx : q (α.inv.left y) = y := by
    rw [← Scheme.Hom.comp_apply]
    change ((Over.forget S).map (α.inv ≫ α.hom)) y = y
    simp
  have hx : α.inv.left y ∈ (q ≫ pullback.fst Y.hom b) ⁻¹ᵁ V := by
    change (pullback.fst Y.hom b) (q (α.inv.left y)) ∈ V
    rwa [hqx]
  have h := (isFlatOverAt_iff_of_moduleIso X.hom.toLRSHom.toShHom e (α.inv.left y)).mp
    (hflat (α.inv.left y) hx)
  rw [← show q ≫ pullback.snd Y.hom b = X.hom from Over.w α.hom] at h
  exact hqx ▸ (isFlatOverAt_iff_modulePullback_isFlatOverAt q (pullback.snd Y.hom b) H
    (α.inv.left y) (Flat.stalkMap q (α.inv.left y))).mpr h

/-! ### The combined descent -/

/-- **The limit descent half of Stacks Project, Tag 05MA.**  Let `S` be the limit of an inverse
system of affine schemes indexed by a directed set, let `f : X ⟶ S` be of finite presentation,
let `ℱ` be a finitely presented quasi-coherent `𝒪_X`-module and let `s` be a point of `S` at
whose fibre `ℱ` is flat over `S`.  Then some finite stage carries a morphism of finite
presentation, a finitely presented quasi-coherent module flat over that stage along the fibre,
and identifications of `f` and `ℱ` with their base change and pullback. -/
public theorem exists_stage_isFlatOverAt_fiber_of_isLimit {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ k : Iᵒᵖ, IsAffine (D.obj k)] {X : Scheme.{u}} (f : X ⟶ c.pt)
    (hf : FinitePresentation f) (F : X.Modules) (hFqc : F.IsQuasicoherent)
    (hFfp : F.IsFinitePresentation) (s : c.pt)
    (hflat : ∀ x : f.fiber s, IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s x)) :
    ∃ (k : I) (Xk : Scheme.{u}) (fk : Xk ⟶ D.obj (op k)) (Fk : Xk.Modules) (a : X ⟶ Xk),
      FinitePresentation fk ∧ Fk.IsQuasicoherent ∧ Fk.IsFinitePresentation ∧
      IsPullback a f fk (c.π.app (op k)) ∧
      Nonempty (F ≅ (Scheme.Modules.pullback a).obj Fk) ∧
      ∀ x : fk.fiber (c.π.app (op k) s),
        IsFlatOverAt fk.toLRSHom.toShHom Fk (fk.fiberι (c.π.app (op k) s) x) := by
  classical
  have : LocallyOfFinitePresentation f := hf.1
  have : QuasiCompact f := hf.2.1
  have : F.IsQuasicoherent := hFqc
  have : F.IsFinitePresentation := hFfp
  have : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (D.map e) := fun e => isAffineHom_of_isAffine _
  -- Tag 0399: shrink the flat locus to a quasi-compact open still containing the fibre.
  obtain ⟨U, hU, hcover, hUflat⟩ := exists_isCompact_opens_isFlatOverAt_of_fiber f F s hflat
  -- Tags 01ZM (1), 01ZR (1) and 01Z4 (1): descend the morphism, the module and the open.
  obtain ⟨i, Xᵢ, Fᵢ, hfᵢ, hqcᵢ, hfpᵢ, α, V, hVcpt, hVpre, ⟨eF⟩⟩ :=
    exists_stage_model_with_opens D c hc (Over.mk f) hf F hFfp U hU
  have hVcover : Set.range (Xᵢ.hom.fiberι (c.π.app (op i) s)) ⊆ (V : Set Xᵢ.left) := by
    refine range_fiberι_subset_of_isPullback
      (isPullback_of_model_iso (c.π.app (op i)) (Over.mk f) Xᵢ α) s _ fun x hx => ?_
    rw [← hVpre] at hcover
    exact hcover hx
  have hflatV : ∀ y ∈ pullback.fst Xᵢ.hom (c.π.app (op i)) ⁻¹ᵁ V,
      IsFlatOverAt (pullback.snd Xᵢ.hom (c.π.app (op i))).toLRSHom.toShHom
        ((Scheme.Modules.pullback (pullback.fst Xᵢ.hom (c.π.app (op i)))).obj Fᵢ) y :=
    isFlatOverAt_model_pullback (c.π.app (op i)) (Over.mk f) Xᵢ F Fᵢ α eF V
      fun x hx => hUflat x (by simpa only [hVpre] using hx)
  -- Tag 05LY: the flatness over the open descends to a later stage.
  obtain ⟨j, e, he⟩ := exists_stage_isFlatOverAt_preimage_opens D c hc (op i) Xᵢ hfᵢ Fᵢ hqcᵢ hfpᵢ
    V hVcpt hflatV
  let Y : Over (D.obj j) := (Over.pullback (D.map e)).obj Xᵢ
  let G := (Scheme.Modules.pullback (pullback.fst Xᵢ.hom (D.map e))).obj Fᵢ
  have hcone : c.π.app (op i) = c.π.app j ≫ D.map e := c.π.naturality e
  -- The fibre at the later stage lands in the descended open, so the flatness applies to it.
  have hflatY : ∀ x : Y.hom.fiber (c.π.app j s),
      IsFlatOverAt Y.hom.toLRSHom.toShHom G (Y.hom.fiberι (c.π.app j s) x) := by
    intro x
    refine he _ (hVcover ?_)
    rw [Xᵢ.hom.range_fiberι]
    change Xᵢ.hom ((pullback.fst Xᵢ.hom (D.map e)) (Y.hom.fiberι (c.π.app j s) x)) =
      c.π.app (op i) s
    have hpb := congrArg (fun k : Y.left ⟶ D.obj (op i) => k (Y.hom.fiberι (c.π.app j s) x))
      (pullback.condition (f := Xᵢ.hom) (g := D.map e))
    change Xᵢ.hom ((pullback.fst Xᵢ.hom (D.map e)) (Y.hom.fiberι (c.π.app j s) x)) =
      c.π.app (op i) s
    rw [show Xᵢ.hom ((pullback.fst Xᵢ.hom (D.map e)) (Y.hom.fiberι (c.π.app j s) x)) =
        D.map e (Y.hom (Y.hom.fiberι (c.π.app j s) x)) from hpb,
      Y.hom.apply_fiberι (c.π.app j s) x]
    exact congrArg (fun k : c.pt ⟶ D.obj (op i) => k s) hcone.symm
  have hGqc : G.IsQuasicoherent := @SheafOfModules.modulePullback_isQuasicoherent _ _
    (pullback.fst Xᵢ.hom (D.map e)).toLRSHom.toShHom Fᵢ hqcᵢ
  have hGfp : G.IsFinitePresentation :=
    @Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _
      (pullback.fst Xᵢ.hom (D.map e)).toLRSHom.toShHom Fᵢ hfpᵢ
  -- Reassemble the identification of `f` and `ℱ` at the later stage.
  let β : Over.mk f ≅ (Over.pullback (c.π.app j)).obj Y :=
    α ≪≫ (overPullbackCompIso (D.map e) (c.π.app j) (c.π.app (op i)) (c.w e) Xᵢ).symm
  have hmap : (β.hom.left ≫ pullback.fst Y.hom (c.π.app j)) ≫
      pullback.fst Xᵢ.hom (D.map e) =
        α.hom.left ≫ pullback.fst Xᵢ.hom (c.π.app (op i)) := by
    simp only [β, Iso.trans_hom, Over.comp_left, Iso.symm_hom, Category.assoc]
    rw [overPullbackCompIso_inv_left_fst_fst]
  exact ⟨j.unop, Y.left, Y.hom, G, β.hom.left ≫ pullback.fst Y.hom (c.π.app j),
    LimitFPObjectDescent.finitePresentation_overPullback (D.map e) Xᵢ hfᵢ, hGqc, hGfp,
    isPullback_of_model_iso (c.π.app j) (Over.mk f) Y β,
    ⟨eF ≪≫ (Scheme.Modules.pullbackCongr hmap.symm).app Fᵢ ≪≫
      ((Scheme.Modules.pullbackComp (β.hom.left ≫ pullback.fst Y.hom (c.π.app j))
        (pullback.fst Xᵢ.hom (D.map e))).app Fᵢ).symm⟩, hflatY⟩

end AlgebraicGeometry

end
