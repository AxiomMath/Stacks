/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Immersion
public import StacksFrontier.AlgebraicGeometry.Limits.FinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MorphismDescentGlue
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.DirectImage

/-!
# A projectively immersed scheme with a module of finite presentation descends to a stage

Let `S = lim S_i` be the limit of a cofiltered diagram of quasi-compact quasi-separated schemes
with affine transition morphisms, `f : X ⟶ S` a morphism of finite presentation, `j : X ⟶ ℙⁿ_S`
an immersion over `S` and `N` an `𝒪_X`-module of finite presentation. Then for some stage `i`
there are a morphism of finite presentation `f_i : X_i ⟶ S_i`, a cartesian square

```
X ──g──▶ X_i
│f       │f_i
▼        ▼
S ─────▶ S_i
```

an immersion `j_i : X_i ⟶ ℙⁿ_{S_i}` over `S_i` with `g ≫ j_i = j ≫ (ℙⁿ_S ⟶ ℙⁿ_{S_i})`, and an
`𝒪_{X_i}`-module of finite presentation `N_i` with `N ≅ g^* N_i`.

This is the descent step of the proof of Stacks 0DPD over an affine base (the paragraph "Assume
`B = Spec(Λ)`" of its proof): the scheme `X` is descended by Stacks 01ZM part (1), the morphism
`X ⟶ ℙⁿ_ℤ` by Stacks 01ZC (Mathlib's
`AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`), the immersion
property by Stacks 0GTB and the module by Stacks 01ZR part (1).

## Main results

* `AlgebraicGeometry.exists_projectiveImmersionStageModel_of_isLimit`: the statement above.

## References

* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
* [Stacks Project, Tag 0GTB](https://stacks.math.columbia.edu/tag/0GTB)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 0DPD](https://stacks.math.columbia.edu/tag/0DPD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- `ℙⁿ_{S'}` is the base change of `ℙⁿ_S` along `g : S' ⟶ S`. -/
private theorem isPullback_projectiveSpaceOver_map (n : ℕ) {S' S : Scheme.{u}} (g : S' ⟶ S) :
    IsPullback (projectiveSpaceOverMap n g) (projectiveSpaceOver n S' ↘ S')
      (projectiveSpaceOver n S ↘ S) g :=
  isPullback_projectiveSpaceOverMap n g

/-- `projectiveSpaceOverMap n g` lies over `g`. -/
private theorem projectiveSpaceOverMap_comp_fst (n : ℕ) {S' S : Scheme.{u}} (g : S' ⟶ S) :
    projectiveSpaceOverMap n g ≫ (projectiveSpaceOver n S ↘ S) =
      (projectiveSpaceOver n S' ↘ S') ≫ g :=
  projectiveSpaceOverMap_fst n g

/-- The base change of a morphism of finite presentation to a compact space is compact. -/
private theorem compactSpace_pullback_of_finitePresentation {S' S X : Scheme.{u}} (g : S' ⟶ S)
    (f : X ⟶ S) [CompactSpace S'] (hf : FinitePresentation f) : CompactSpace ↥(pullback g f) :=
  have : QuasiCompact (pullback.fst g f) :=
    (FinitePresentation.of_isPullback (IsPullback.of_hasPullback g f).flip hf).2.1
  QuasiCompact.compactSpace_of_compactSpace (pullback.fst g f)

/-- The base change of a morphism of finite presentation to a quasi-separated space is
quasi-separated. -/
private theorem quasiSeparatedSpace_pullback_of_finitePresentation {S' S X : Scheme.{u}}
    (g : S' ⟶ S) (f : X ⟶ S) [QuasiSeparatedSpace S'] (hf : FinitePresentation f) :
    QuasiSeparatedSpace ↥(pullback g f) :=
  have : QuasiSeparated (pullback.fst g f) :=
    (FinitePresentation.of_isPullback (IsPullback.of_hasPullback g f).flip hf).2.2
  quasiSeparatedSpace_of_quasiSeparated (pullback.fst g f)

/-- The base change of `ji : X_i ⟶ ℙⁿ_S` over `S` along `p : T ⟶ S` is an immersion if and only if
the corresponding model `jt : X_t ⟶ ℙⁿ_T` of its base change is. -/
private theorem isImmersion_overPullback_map_iff (n : ℕ) {S Xi : Scheme.{u}} (fi : Xi ⟶ S)
    (ji : Xi ⟶ projectiveSpaceOver n S) (hji : ji ≫ (projectiveSpaceOver n S ↘ S) = fi)
    {T Xt : Scheme.{u}} (p : T ⟶ S) (ft : Xt ⟶ T) (gt : Xt ⟶ Xi)
    (jt : Xt ⟶ projectiveSpaceOver n T) (hpb : IsPullback gt ft fi p)
    (hjt : jt ≫ (projectiveSpaceOver n T ↘ T) = ft)
    (hgj : gt ≫ ji = jt ≫ projectiveSpaceOverMap n p) :
    IsImmersion ((Over.pullback p).map
      (Over.homMk ji hji : Over.mk fi ⟶ Over.mk (projectiveSpaceOver n S ↘ S))).left ↔
      IsImmersion jt := by
  have hP := isPullback_projectiveSpaceOver_map n p
  let ψ : pullback fi p ⟶ pullback (projectiveSpaceOver n S ↘ S) p :=
    ((Over.pullback p).map
      (Over.homMk ji hji : Over.mk fi ⟶ Over.mk (projectiveSpaceOver n S ↘ S))).left
  have h₁ : ψ ≫ pullback.fst (projectiveSpaceOver n S ↘ S) p = pullback.fst fi p ≫ ji :=
    overPullback_map_left_fst _ _
  have h₂ : ψ ≫ pullback.snd (projectiveSpaceOver n S ↘ S) p = pullback.snd fi p :=
    overPullback_map_left_snd _ _
  have he : hpb.isoPullback.hom ≫ ψ = jt ≫ hP.isoPullback.hom := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, h₁, ← Category.assoc, IsPullback.isoPullback_hom_fst, Category.assoc,
        IsPullback.isoPullback_hom_fst]
      exact hgj
    · rw [Category.assoc, h₂, Category.assoc, IsPullback.isoPullback_hom_snd,
        IsPullback.isoPullback_hom_snd]
      exact hjt.symm
  change IsImmersion ψ ↔ _
  constructor
  · intro h
    have : jt = hpb.isoPullback.hom ≫ ψ ≫ hP.isoPullback.inv := by
      rw [← Category.assoc, he, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [this]
    infer_instance
  · intro h
    have : ψ = hpb.isoPullback.inv ≫ jt ≫ hP.isoPullback.hom := by
      rw [← he, Iso.inv_hom_id_assoc]
    rw [this]
    infer_instance

section Model

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
  {X : Scheme.{u}} (f : X ⟶ c.pt) (n : ℕ) (j : X ⟶ projectiveSpaceOver n c.pt)
  (hj : j ≫ (projectiveSpaceOver n c.pt ↘ c.pt) = f)

include hj in
/-- **Base change of a projective stage model.** A model `(X_i, f_i, g, j_i)` of `(X, f, j)`
at the stage `i` gives one at every later stage `m ⟶ i`: the base change of `X_i` to `S_m`,
with the base change of `j_i`. -/
theorem exists_projectiveStageModel_baseChange {i m : I} (a : m ⟶ i) {Xi : Scheme.{u}}
    (fi : Xi ⟶ D.obj i) (g : X ⟶ Xi) (ji : Xi ⟶ projectiveSpaceOver n (D.obj i))
    (hfi : FinitePresentation fi) (hpb : IsPullback g f fi (c.π.app i))
    (hji : ji ≫ (projectiveSpaceOver n (D.obj i) ↘ D.obj i) = fi)
    (hgj : g ≫ ji = j ≫ projectiveSpaceOverMap n (c.π.app i))
    (g' : X ⟶ pullback (D.map a) fi) (hg'₁ : g' ≫ pullback.fst (D.map a) fi = f ≫ c.π.app m)
    (hg'₂ : g' ≫ pullback.snd (D.map a) fi = g) :
    ∃ jm : pullback (D.map a) fi ⟶ projectiveSpaceOver n (D.obj m),
      FinitePresentation (pullback.fst (D.map a) fi) ∧
      IsPullback g' f (pullback.fst (D.map a) fi) (c.π.app m) ∧
      jm ≫ (projectiveSpaceOver n (D.obj m) ↘ D.obj m) = pullback.fst (D.map a) fi ∧
      g' ≫ jm = j ≫ projectiveSpaceOverMap n (c.π.app m) ∧
      jm ≫ projectiveSpaceOverMap n (D.map a) = pullback.snd (D.map a) fi ≫ ji ∧
      IsPullback (pullback.snd (D.map a) fi) jm ji (projectiveSpaceOverMap n (D.map a)) := by
  have hP := isPullback_projectiveSpaceOver_map n (D.map a)
  have hw : (pullback.snd (D.map a) fi ≫ ji) ≫ (projectiveSpaceOver n (D.obj i) ↘ D.obj i) =
      pullback.fst (D.map a) fi ≫ D.map a := by
    rw [Category.assoc, hji, ← pullback.condition]
  let jm := hP.lift _ _ hw
  have hjm₁ : jm ≫ projectiveSpaceOverMap n (D.map a) = pullback.snd (D.map a) fi ≫ ji :=
    hP.lift_fst _ _ hw
  have hjm₂ : jm ≫ (projectiveSpaceOver n (D.obj m) ↘ D.obj m) = pullback.fst (D.map a) fi :=
    hP.lift_snd _ _ hw
  have ht : IsPullback (pullback.snd (D.map a) fi) (pullback.fst (D.map a) fi) fi (D.map a) :=
    (IsPullback.of_hasPullback (D.map a) fi).flip
  have hs : IsPullback g f fi (c.π.app m ≫ D.map a) := by rwa [c.w a]
  refine ⟨jm, FinitePresentation.of_isPullback ht hfi, ?_, hjm₂, ?_, hjm₁, ?_⟩
  · rw [← hg'₂] at hs
    exact hs.of_right hg'₁ ht
  · refine hP.hom_ext ?_ ?_
    · rw [Category.assoc, hjm₁, ← Category.assoc, hg'₂, hgj, Category.assoc,
        projectiveSpaceOverMap_comp, c.w a]
    · rw [Category.assoc, hjm₂, hg'₁, Category.assoc, projectiveSpaceOverMap_comp_fst,
        ← Category.assoc, hj]
  · refine IsPullback.of_bot ?_ hjm₁.symm hP
    rw [hjm₂, hji]
    exact ht

variable [IsCofiltered I] [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

include hj in
/-- **A projective stage model exists** (Stacks 01ZM part (1) and Stacks 01ZC): `X` is the base
change of a scheme `X_i` of finite presentation over a stage `S_i`, and `X ⟶ ℙⁿ_S` is the base
change of a morphism `X_i ⟶ ℙⁿ_{S_i}` over `S_i`. -/
theorem exists_projectiveStageModel (hc : IsLimit c) (hf : FinitePresentation f) :
    ∃ (i : I) (Xi : Scheme.{u}) (fi : Xi ⟶ D.obj i) (g : X ⟶ Xi)
      (ji : Xi ⟶ projectiveSpaceOver n (D.obj i)),
      FinitePresentation fi ∧ IsPullback g f fi (c.π.app i) ∧
      ji ≫ (projectiveSpaceOver n (D.obj i) ↘ D.obj i) = fi ∧
      g ≫ ji = j ≫ projectiveSpaceOverMap n (c.π.app i) := by
  obtain ⟨i₀, X₀, f₀, g₀, hf₀, hpb₀⟩ :=
    LimitDescent.exists_isPullback_of_finitePresentation D c hc f hf
  have : QuasiCompact f₀ := hf₀.2.1
  have : QuasiSeparated f₀ := hf₀.2.2
  let E := Scheme.baseChangeDiagram D i₀ (Over.mk f₀)
  let cE := Scheme.baseChangeCone D i₀ (Over.mk f₀) c
  have hcE : IsLimit cE := Scheme.isLimitBaseChangeCone D i₀ (Over.mk f₀) c hc
  let πE : ∀ m : Over i₀, pullback (c.π.app i₀) f₀ ⟶ pullback (D.map m.hom) f₀ :=
    fun m => cE.π.app m
  have hπ₁ : ∀ m : Over i₀, πE m ≫ pullback.fst (D.map m.hom) f₀ =
      pullback.fst (c.π.app i₀) f₀ ≫ c.π.app m.left :=
    fun m => Scheme.baseChangeCone_π_fst D i₀ (Over.mk f₀) c m
  have hπ₂ : ∀ m : Over i₀, πE m ≫ pullback.snd (D.map m.hom) f₀ =
      pullback.snd (c.π.app i₀) f₀ :=
    fun m => Scheme.baseChangeCone_π_snd D i₀ (Over.mk f₀) c m
  have : ∀ {a b : Over i₀} (e : a ⟶ b), IsAffineHom (E.map e) := fun e =>
    Scheme.isAffineHom_baseChangeDiagram_map D i₀ _ e
  have : ∀ a : Over i₀, CompactSpace (E.obj a) := fun a =>
    compactSpace_pullback_of_finitePresentation (D.map a.hom) f₀ hf₀
  have : ∀ a : Over i₀, QuasiSeparatedSpace (E.obj a) := fun a =>
    quasiSeparatedSpace_pullback_of_finitePresentation (D.map a.hom) f₀ hf₀
  let φ : X ≅ pullback (c.π.app i₀) f₀ := hpb₀.flip.isoPullback
  have hφ₁ : φ.hom ≫ pullback.fst (c.π.app i₀) f₀ = f := hpb₀.flip.isoPullback_hom_fst
  have hφ₂ : φ.hom ≫ pullback.snd (c.π.app i₀) f₀ = g₀ := hpb₀.flip.isoPullback_hom_snd
  let a : pullback (c.π.app i₀) f₀ ⟶ projectiveSpaceOver n (D.obj i₀) :=
    φ.inv ≫ j ≫ projectiveSpaceOverMap n (c.π.app i₀)
  have ha : cE.π ≫ Scheme.baseChangeStructureMap D i₀ (Over.mk f₀) =
      (Functor.const _).map (a ≫ (projectiveSpaceOver n (D.obj i₀) ↘ D.obj i₀)) := by
    ext m
    show πE m ≫ (pullback.snd (D.map m.hom) f₀ ≫ f₀) =
      a ≫ (projectiveSpaceOver n (D.obj i₀) ↘ D.obj i₀)
    rw [← Category.assoc, hπ₂ m, ← pullback.condition]
    simp only [a, Category.assoc, projectiveSpaceOverMap_comp_fst]
    rw [← Category.assoc j, hj, ← hφ₁]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have : LocallyOfFinitePresentation (projectiveSpaceOver n (D.obj i₀) ↘ D.obj i₀) :=
    (ProjectiveQuot.finitePresentation_projectiveSpaceOver n (D.obj i₀)).1
  obtain ⟨m, b, hb₁, hb₂⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation E
    (Scheme.baseChangeStructureMap D i₀ (Over.mk f₀))
    (projectiveSpaceOver n (D.obj i₀) ↘ D.obj i₀) cE hcE a ha
  let b' : pullback (D.map m.hom) f₀ ⟶ projectiveSpaceOver n (D.obj i₀) := b
  have hb₂' : b' ≫ (projectiveSpaceOver n (D.obj i₀) ↘ D.obj i₀) =
      pullback.snd (D.map m.hom) f₀ ≫ f₀ := hb₂
  have hb₁' : πE m ≫ b' = a := hb₁
  have hP := isPullback_projectiveSpaceOver_map n (D.map m.hom)
  have hw : b' ≫ (projectiveSpaceOver n (D.obj i₀) ↘ D.obj i₀) =
      pullback.fst (D.map m.hom) f₀ ≫ D.map m.hom := by
    rw [hb₂', pullback.condition]
  have ht : IsPullback (pullback.snd (D.map m.hom) f₀) (pullback.fst (D.map m.hom) f₀) f₀
      (D.map m.hom) := (IsPullback.of_hasPullback (D.map m.hom) f₀).flip
  let g : X ⟶ pullback (D.map m.hom) f₀ := φ.hom ≫ πE m
  have hg₁ : g ≫ pullback.fst (D.map m.hom) f₀ = f ≫ c.π.app m.left := by
    rw [Category.assoc, hπ₁ m, ← Category.assoc, hφ₁]
  have hg₂ : g ≫ pullback.snd (D.map m.hom) f₀ = g₀ := by
    rw [Category.assoc, hπ₂ m, hφ₂]
  refine ⟨m.left, pullback (D.map m.hom) f₀, pullback.fst (D.map m.hom) f₀, g, hP.lift b' _ hw,
    FinitePresentation.of_isPullback ht hf₀, ?_, hP.lift_snd _ _ hw, ?_⟩
  · have hs : IsPullback (g ≫ pullback.snd (D.map m.hom) f₀) f f₀
        (c.π.app m.left ≫ D.map m.hom) := by rw [c.w m.hom, hg₂]; exact hpb₀
    exact hs.of_right hg₁ ht
  · refine hP.hom_ext ?_ ?_
    · rw [Category.assoc, hP.lift_fst, Category.assoc j, projectiveSpaceOverMap_comp, c.w m.hom]
      simp only [g, Category.assoc]
      rw [hb₁']
      simp only [a, Iso.hom_inv_id_assoc]
    · rw [Category.assoc, hP.lift_snd, hg₁, Category.assoc, projectiveSpaceOverMap_comp_fst,
        ← Category.assoc, hj]

include hj in
/-- **The immersion descends** (Stacks 0GTB): a projective stage model of an immersion
`j : X ⟶ ℙⁿ_S` is, at a later stage, a model by an immersion. -/
theorem exists_projectiveStageModel_isImmersion [EssentiallySmall.{u} I] (hc : IsLimit c)
    [IsImmersion j] {i : I} {Xi : Scheme.{u}}
    (fi : Xi ⟶ D.obj i) (g : X ⟶ Xi) (ji : Xi ⟶ projectiveSpaceOver n (D.obj i))
    (hfi : FinitePresentation fi) (hpb : IsPullback g f fi (c.π.app i))
    (hji : ji ≫ (projectiveSpaceOver n (D.obj i) ↘ D.obj i) = fi)
    (hgj : g ≫ ji = j ≫ projectiveSpaceOverMap n (c.π.app i)) :
    ∃ (k : I) (Xk : Scheme.{u}) (fk : Xk ⟶ D.obj k) (g' : X ⟶ Xk)
      (jk : Xk ⟶ projectiveSpaceOver n (D.obj k)),
      FinitePresentation fk ∧ IsPullback g' f fk (c.π.app k) ∧
      jk ≫ (projectiveSpaceOver n (D.obj k) ↘ D.obj k) = fk ∧
      g' ≫ jk = j ≫ projectiveSpaceOverMap n (c.π.app k) ∧ IsImmersion jk := by
  have : QuasiCompact fi := hfi.2.1
  have : QuasiSeparated fi := hfi.2.2
  have : LocallyOfFinitePresentation fi := hfi.1
  have : CompactSpace Xi := QuasiCompact.compactSpace_of_compactSpace fi
  have : QuasiSeparatedSpace Xi := quasiSeparatedSpace_of_quasiSeparated fi
  have hPfp := ProjectiveQuot.finitePresentation_projectiveSpaceOver n (D.obj i)
  have : QuasiCompact (projectiveSpaceOver n (D.obj i) ↘ D.obj i) := hPfp.2.1
  have : QuasiSeparated (projectiveSpaceOver n (D.obj i) ↘ D.obj i) := hPfp.2.2
  have : CompactSpace (projectiveSpaceOver n (D.obj i)) :=
    QuasiCompact.compactSpace_of_compactSpace (projectiveSpaceOver n (D.obj i) ↘ D.obj i)
  have : QuasiSeparatedSpace (projectiveSpaceOver n (D.obj i)) :=
    quasiSeparatedSpace_of_quasiSeparated (projectiveSpaceOver n (D.obj i) ↘ D.obj i)
  let X₀ : Over (D.obj i) := Over.mk fi
  let Y₀ : Over (D.obj i) := Over.mk (projectiveSpaceOver n (D.obj i) ↘ D.obj i)
  let f₀ : X₀ ⟶ Y₀ := Over.homMk ji hji
  have : CompactSpace X₀.left := inferInstanceAs (CompactSpace Xi)
  have : QuasiSeparatedSpace X₀.left := inferInstanceAs (QuasiSeparatedSpace Xi)
  have : CompactSpace Y₀.left :=
    inferInstanceAs (CompactSpace (projectiveSpaceOver n (D.obj i)))
  have : QuasiSeparatedSpace Y₀.left :=
    inferInstanceAs (QuasiSeparatedSpace (projectiveSpaceOver n (D.obj i)))
  have : LocallyOfFiniteType f₀.left := by
    have : LocallyOfFiniteType (ji ≫ (projectiveSpaceOver n (D.obj i) ↘ D.obj i)) := by
      rw [hji]; infer_instance
    exact locallyOfFiniteType_of_comp ji (projectiveSpaceOver n (D.obj i) ↘ D.obj i)
  -- over the limit, the base change of `f₀` is `j`
  have hlim : IsImmersion ((Over.pullback (c.π.app i)).map f₀).left :=
    (isImmersion_overPullback_map_iff n fi ji hji (c.π.app i) f g j hpb hj hgj).2 inferInstance
  obtain ⟨k, hk, hk'⟩ := exists_isImmersion_baseChange_of_isLimit D c hc i X₀ Y₀ f₀
  have hw : (f ≫ c.π.app k) ≫ D.map hk = g ≫ fi := by
    rw [Category.assoc, c.w hk, hpb.w]
  let g' : X ⟶ pullback (D.map hk) fi := pullback.lift _ _ hw
  obtain ⟨jk, hfk, hpbk, hjk, hgjk, hjk₁, -⟩ := exists_projectiveStageModel_baseChange D c f n j
    hj hk fi g ji hfi hpb hji hgj g' (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  refine ⟨k, _, _, g', jk, hfk, hpbk, hjk, hgjk, ?_⟩
  exact (isImmersion_overPullback_map_iff n fi ji hji (D.map hk) _ _ jk
    (IsPullback.of_hasPullback (D.map hk) fi).flip hjk hjk₁.symm).1 hk'

include hj in
/-- **The module descends** (Stacks 01ZR part (1)): a projective stage model by an immersion
carries, at a later stage, a module of finite presentation whose pullback to `X` is `N`. -/
theorem exists_projectiveStageModel_module (hc : IsLimit c) {k : I} {Xk : Scheme.{u}}
    (fk : Xk ⟶ D.obj k) (g : X ⟶ Xk) (jk : Xk ⟶ projectiveSpaceOver n (D.obj k))
    (hfk : FinitePresentation fk) (hpb : IsPullback g f fk (c.π.app k))
    (hjk : jk ≫ (projectiveSpaceOver n (D.obj k) ↘ D.obj k) = fk)
    (hgj : g ≫ jk = j ≫ projectiveSpaceOverMap n (c.π.app k)) (himm : IsImmersion jk)
    (N : X.Modules) [N.IsFinitePresentation] :
    ∃ (m : I) (Xm : Scheme.{u}) (fm : Xm ⟶ D.obj m) (g' : X ⟶ Xm)
      (jm : Xm ⟶ projectiveSpaceOver n (D.obj m)) (Nm : Xm.Modules),
      FinitePresentation fm ∧ IsPullback g' f fm (c.π.app m) ∧
      jm ≫ (projectiveSpaceOver n (D.obj m) ↘ D.obj m) = fm ∧
      g' ≫ jm = j ≫ projectiveSpaceOverMap n (c.π.app m) ∧ IsImmersion jm ∧
      Nm.IsFinitePresentation ∧ Nonempty (N ≅ (Scheme.Modules.pullback g').obj Nm) := by
  have : QuasiCompact fk := hfk.2.1
  have : QuasiSeparated fk := hfk.2.2
  let E := Scheme.baseChangeDiagram D k (Over.mk fk)
  let cE := Scheme.baseChangeCone D k (Over.mk fk) c
  have hcE : IsLimit cE := Scheme.isLimitBaseChangeCone D k (Over.mk fk) c hc
  let πE : ∀ m : Over k, pullback (c.π.app k) fk ⟶ pullback (D.map m.hom) fk :=
    fun m => cE.π.app m
  have hπ₁ : ∀ m : Over k, πE m ≫ pullback.fst (D.map m.hom) fk =
      pullback.fst (c.π.app k) fk ≫ c.π.app m.left :=
    fun m => Scheme.baseChangeCone_π_fst D k (Over.mk fk) c m
  have hπ₂ : ∀ m : Over k, πE m ≫ pullback.snd (D.map m.hom) fk =
      pullback.snd (c.π.app k) fk :=
    fun m => Scheme.baseChangeCone_π_snd D k (Over.mk fk) c m
  have : ∀ {a b : Over k} (e : a ⟶ b), IsAffineHom (E.map e) := fun e =>
    Scheme.isAffineHom_baseChangeDiagram_map D k _ e
  have : ∀ a : Over k, CompactSpace (E.obj a) := fun a =>
    compactSpace_pullback_of_finitePresentation (D.map a.hom) fk hfk
  have : ∀ a : Over k, QuasiSeparatedSpace (E.obj a) := fun a =>
    quasiSeparatedSpace_pullback_of_finitePresentation (D.map a.hom) fk hfk
  let φ : X ≅ pullback (c.π.app k) fk := hpb.flip.isoPullback
  have hφ₁ : φ.hom ≫ pullback.fst (c.π.app k) fk = f := hpb.flip.isoPullback_hom_fst
  have hφ₂ : φ.hom ≫ pullback.snd (c.π.app k) fk = g := hpb.flip.isoPullback_hom_snd
  have hX : IsLimit (cE.extend φ.hom) := @IsLimit.extendIso _ _ _ _ _ cE X φ.hom φ.isIso_hom hcE
  obtain ⟨m, Nm, hNm, ⟨eN⟩⟩ :=
    Stacks.AlgebraicGeometry.ModuleLimits.exists_isFinitePresentation_pullback_iso_of_qcqs E
      (cE.extend φ.hom) hX N
  let g' : X ⟶ pullback (D.map m.hom) fk := φ.hom ≫ πE m
  have hg'₁ : g' ≫ pullback.fst (D.map m.hom) fk = f ≫ c.π.app m.left := by
    rw [Category.assoc, hπ₁ m, ← Category.assoc, hφ₁]
  have hg'₂ : g' ≫ pullback.snd (D.map m.hom) fk = g := by
    rw [Category.assoc, hπ₂ m, hφ₂]
  obtain ⟨jm, hfm, hpbm, hjm, hgjm, -, hsq⟩ := exists_projectiveStageModel_baseChange D c f n j
    hj m.hom fk g jk hfk hpb hjk hgj g' hg'₁ hg'₂
  exact ⟨m.left, _, _, g', jm, Nm, hfm, hpbm, hjm, hgjm,
    MorphismProperty.of_isPullback hsq himm, hNm, ⟨eN⟩⟩

include hj in
/-- **Stage models of a projectively immersed scheme with a module of finite presentation.** Let
`S = lim S_i` with affine transition morphisms between quasi-compact quasi-separated schemes,
`f : X ⟶ S` of finite presentation, `j : X ⟶ ℙⁿ_S` an immersion over `S` and `N` an
`𝒪_X`-module of finite presentation. Then for some stage `i` there are `f_i : X_i ⟶ S_i` of finite
presentation with `X = X_i ×_{S_i} S` (through `g : X ⟶ X_i`), an immersion
`j_i : X_i ⟶ ℙⁿ_{S_i}` over `S_i` with `g ≫ j_i = j ≫ (ℙⁿ_S ⟶ ℙⁿ_{S_i})`, and an
`𝒪_{X_i}`-module of finite presentation `N_i` with `N ≅ g^* N_i`. -/
theorem exists_projectiveImmersionStageModel_of_isLimit [EssentiallySmall.{u} I] (hc : IsLimit c)
    (hf : FinitePresentation f) [IsImmersion j] (N : X.Modules) [N.IsFinitePresentation] :
    ∃ (i : I) (Xi : Scheme.{u}) (fi : Xi ⟶ D.obj i) (g : X ⟶ Xi)
      (ji : Xi ⟶ projectiveSpaceOver n (D.obj i)) (Ni : Xi.Modules),
      FinitePresentation fi ∧ IsPullback g f fi (c.π.app i) ∧
      ji ≫ (projectiveSpaceOver n (D.obj i) ↘ D.obj i) = fi ∧
      g ≫ ji = j ≫ projectiveSpaceOverMap n (c.π.app i) ∧ IsImmersion ji ∧
      Ni.IsFinitePresentation ∧ Nonempty (N ≅ (Scheme.Modules.pullback g).obj Ni) := by
  obtain ⟨i, Xi, fi, g, ji, hfi, hpb, hji, hgj⟩ := exists_projectiveStageModel D c f n j hj hc hf
  obtain ⟨k, Xk, fk, g', jk, hfk, hpbk, hjk, hgjk, himm⟩ :=
    exists_projectiveStageModel_isImmersion D c f n j hj hc fi g ji hfi hpb hji hgj
  exact exists_projectiveStageModel_module D c f n j hj hc fk g' jk hfk hpbk hjk hgjk himm N

end Model

end AlgebraicGeometry

end
