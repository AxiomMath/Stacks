module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.CancelTwoFibreProductAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationBaseChangeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatOpenPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactFieldValuedPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStackInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismComp
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CospanReindex
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# Fppf descent of quasi-compactness of a 1-morphism of algebraic stacks

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` and let `g : 𝒵 ⟶ 𝒴` be a
surjective, flat, locally finitely presented 1-morphism of algebraic stacks. Then `f` is
quasi-compact as soon as its base change `𝒵 ×_𝒴 𝒳 ⟶ 𝒵` is.

## Main results

* `AlgebraicGeometry.Stack.isQuasiCompactMorphism_of_isQuasiCompactMorphism_fst_of_stack`:
  quasi-compactness of a 1-morphism descends along a surjective, flat, locally finitely
  presented 1-morphism of algebraic stacks.
* `AlgebraicGeometry.Stack.isQuasiCompactMorphism_of_isQuasiCompactMorphism_fst`: the case in
  which the source of that 1-morphism is an algebraic space.

## References

* [Stacks Project, Tag 050U](https://stacks.math.columbia.edu/tag/050U)
* [Stacks Project, Tag 06R7](https://stacks.math.columbia.edu/tag/06R7)
* [Stacks Project, Tag 0DQK](https://stacks.math.columbia.edu/tag/0DQK)
* [Stacks Project, Tag 0DTL](https://stacks.math.columbia.edu/tag/0DTL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Refining an open surjection from a scheme of the site by an affine one -/

/-- **An open surjection from a scheme of the site onto a compact space is refined by an affine
scheme of the site.** -/
theorem exists_affine_refinement_of_isOpenMap_surjective
    (U : BigFppfOver B S hS) {Z : Type*} [TopologicalSpace Z] [CompactSpace Z]
    (m : (BigFppfOver.toScheme B S hS).obj U → Z)
    (hmOpen : IsOpenMap m) (hmSurj : Function.Surjective m) :
    ∃ (A : BigFppfOver B S hS) (k : A ⟶ U),
      IsAffine ((BigFppfOver.toScheme B S hS).obj A) ∧
        Function.Surjective (m ∘ ((BigFppfOver.toScheme B S hS).map k).base) := by
  classical
  let T := BigFppfOver.toScheme B S hS
  let X := T.obj U
  have hv (i : X.affineOpens) : B.Contains i.1.toScheme :=
    Scheme.size_lt_of_isOpenImmersion i.1.ι U.left.property
  have hcover : (Set.univ : Set Z) ⊆ ⋃ i : X.affineOpens, m '' (i.1 : Set X) := by
    intro z _
    obtain ⟨x, rfl⟩ := hmSurj z
    obtain ⟨-, ⟨V₀, hV₀, rfl⟩, hxV₀, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact Set.mem_iUnion.mpr ⟨⟨V₀, hV₀⟩, x, hxV₀, rfl⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun i : X.affineOpens => m '' (i.1 : Set X)) (fun i => hmOpen _ i.1.isOpen) hcover
  let _ : Finite { i : X.affineOpens // i ∈ s } := s.finite_toSet
  let Y (i : s) : Scheme.{u} := i.val.1.toScheme
  let d : (∐ Y) ⟶ X := Limits.Sigma.desc (fun i : s => i.val.1.ι)
  have hY : B.Contains (∐ Y) := Scheme.size_sigmaObj_lt B.aleph0_lt_cutoff
    B.aleph0_lt_cutoff_cof Cardinal.mk_le_aleph0 Y (fun i => hv i.val)
  let A : BigFppfOver B S hS :=
    Over.mk (⟨d ≫ B.inclusion.map U.hom⟩ : B.obj hY ⟶ B.obj hS)
  let k : A ⟶ U := Over.homMk ⟨d⟩ (by rfl)
  refine ⟨A, k, ?_, ?_⟩
  · change IsAffine (∐ Y)
    let instAff (i : s) : IsAffine (Y i) := i.val.2
    infer_instance
  · intro z
    obtain ⟨i, hi, x, hx, hmx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ z))
    have hdesc : Limits.Sigma.ι Y (⟨i, hi⟩ : s) ≫ d = i.1.ι := Limits.Sigma.ι_comp_desc _ _
    refine ⟨(Limits.Sigma.ι Y (⟨i, hi⟩ : s)).base ⟨x, hx⟩, ?_⟩
    have hbase : d.base ((Limits.Sigma.ι Y (⟨i, hi⟩ : s)).base ⟨x, hx⟩) = x :=
      congrArg (fun φ : Y (⟨i, hi⟩ : s) ⟶ X => φ.base ⟨x, hx⟩) hdesc
    change m ((T.map k).base _) = z
    rwa [show (T.map k).base = d.base from rfl, hbase]

/-! ### Fppf descent of quasi-compactness -/

/-- Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` and let
`g : 𝒵 ⟶ 𝒴` be a surjective, flat, locally finitely presented 1-morphism of algebraic stacks.
If the base change `𝒵 ×_𝒴 𝒳 ⟶ 𝒵` of `f` along `g` is quasi-compact, then `f` is
quasi-compact. -/
@[stacks 0DQK]
theorem isQuasiCompactMorphism_of_isQuasiCompactMorphism_fst_of_stack
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (hgsurj : IsSurjective B S hS g)
    (hgflat : AlgebraicStacks.IsFlat B S hS g)
    (hglfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS g)
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (hbase : IsQuasiCompactMorphism B S hS P.fst) :
    IsQuasiCompactMorphism B S hS f := by
  intro 𝒯 q h𝒯
  let R := twoFibreProductSquareAlgebraicStacks B S hS g q
  have hR := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g q
  have hRsurj : IsSurjective B S hS R.snd :=
    isSurjective_of_isTwoFibreProduct B S hS R hR hgsurj
  have hRflat : AlgebraicStacks.IsFlat B S hS R.snd :=
    AlgebraicStacks.isFlat_baseChange B S hS g q R.swap
      (Bicategory.isTwoFibreProduct_swap hR) hgflat
  have hRlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS R.snd :=
    AlgebraicStacks.isLocallyOfFinitePresentation_baseChange B S hS g q R.swap
      (Bicategory.isTwoFibreProduct_swap hR) hglfp
  obtain ⟨U, a₁, ha₁sm, ha₁su⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS R.pt
  have hcsurj : IsSurjective B S hS (a₁ ≫ R.snd) :=
    isSurjective_comp B S hS a₁ R.snd ha₁su hRsurj
  have hcflat : AlgebraicStacks.IsFlat B S hS (a₁ ≫ R.snd) :=
    AlgebraicStacks.isFlat_comp B S hS a₁ R.snd
      (AlgebraicStacks.isFlat_of_isSmooth B S hS a₁ ha₁sm) hRflat
  have hclfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS (a₁ ≫ R.snd) :=
    AlgebraicStacks.isLocallyOfFinitePresentation_comp B S hS a₁ R.snd
      (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS a₁ ha₁sm) hRlfp
  let _ := pointTopology B S hS (schemeStack.{u, w} B S hS U).val
  let _ := pointTopology B S hS 𝒯.val
  let _ : CompactSpace (AlgebraicStacks.points B S hS 𝒯) := h𝒯
  let φ := pointsHomeomorphScheme B S hS U
  let n : (BigFppfOver.toScheme B S hS).obj U → AlgebraicStacks.points B S hS 𝒯 :=
    AlgebraicStacks.pointsMap B S hS (a₁ ≫ R.snd) ∘ φ.symm
  have hnOpen : IsOpenMap n :=
    (AlgebraicStacks.isOpenMap_pointsMap B S hS (a₁ ≫ R.snd) hcflat hclfp).comp
      φ.symm.isOpenMap
  have hnSurj : Function.Surjective n := hcsurj.comp φ.symm.surjective
  obtain ⟨A, k, hAaff, hAsurj⟩ :=
    exists_affine_refinement_of_isOpenMap_surjective B S hS U n hnOpen hnSurj
  let _ := pointTopology B S hS (schemeFibredCategory B S hS A)
  let 𝒜 := schemeStack.{u, w} B S hS A
  have h𝒜 : IsQuasiCompactStack.{u, w} B S hS 𝒜.val 𝒜.property :=
    isQuasiCompactStack_schemeStack_of_isAffine.{u, w} B S hS A hAaff
  let kk : 𝒜 ⟶ schemeStack.{u, w} B S hS U :=
    Bicategory.InducedBicategory.mkHom (schemeFibredCategoryMap B S hS k)
  let cc : 𝒜 ⟶ R.pt := kk ≫ a₁
  have hccsurj : IsSurjective B S hS (cc ≫ R.snd) := by
    have hpt : ∀ y : AlgebraicStacks.points B S hS 𝒜,
        AlgebraicStacks.pointsMap B S hS (cc ≫ R.snd) y =
          n (((BigFppfOver.toScheme B S hS).map k).base (pointsHomeomorphScheme B S hS A y)) := by
      intro y
      have hnat := pointsHomeomorphScheme_naturality B S hS k y
      change _ = AlgebraicStacks.pointsMap B S hS (a₁ ≫ R.snd) (φ.symm _)
      rw [← hnat, Homeomorph.symm_apply_apply]
      simp only [cc, AlgebraicStacks.pointsMap_comp]
      rfl
    intro z
    obtain ⟨x, hx⟩ := hAsurj z
    obtain ⟨y, hy⟩ := (pointsHomeomorphScheme B S hS A).surjective x
    exact ⟨y, by rwa [hpt y, hy]⟩
  let aZ : 𝒜 ⟶ 𝒵 := cc ≫ R.fst
  let aa : 𝒜 ⟶ 𝒯 := cc ≫ R.snd
  let θ : aZ ≫ g ≅ aa ≫ q :=
    Bicategory.associator cc R.fst g ≪≫ Bicategory.whiskerLeftIso cc R.iso ≪≫
      (Bicategory.associator cc R.snd q).symm
  have hqc0 := hbase 𝒜 aZ h𝒜
  let Qsq := twoFibreProductSquareAlgebraicStacks B S hS aZ P.fst
  have hQsq := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS aZ P.fst
  have hre : Bicategory.IsTwoFibreProduct ((P.swap.paste Qsq.swap).reindexSnd θ) :=
    Bicategory.isTwoFibreProduct_reindexSnd θ
      (Bicategory.isTwoFibreProduct_paste (Bicategory.isTwoFibreProduct_swap hP)
        (Bicategory.isTwoFibreProduct_swap hQsq))
  have h0 := isQuasiCompactStack_of_isTwoFibreProduct B S hS hre
    (isTwoFibreProduct_cancelSndSquareAlgebraicStacks B S hS f q aa (aa ≫ q) (Iso.refl _)) hqc0
  let Q := twoFibreProductSquareAlgebraicStacks B S hS
    (twoFibreProductSquareAlgebraicStacks B S hS f q).snd aa
  have hQ := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS
    (twoFibreProductSquareAlgebraicStacks B S hS f q).snd aa
  have h1 := isQuasiCompactStack_of_isSurjective B S hS Q.fst h0
    (isSurjective_of_isTwoFibreProduct B S hS Q.swap (Bicategory.isTwoFibreProduct_swap hQ)
      hccsurj)
  exact isQuasiCompactStack_of_isTwoFibreProduct B S hS
    (Bicategory.isTwoFibreProduct_swap
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f q))
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS q f) h1

/-- Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` and let
`g : W ⟶ 𝒴` be surjective, flat and locally of finite presentation, where `W` is an algebraic
space. If the base change `W ×_𝒴 𝒳 ⟶ W` of `f` along `g` is quasi-compact, then `f` is
quasi-compact. -/
@[stacks 0DTL]
theorem isQuasiCompactMorphism_of_isQuasiCompactMorphism_fst
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS W)
    (g : algebraicSpaceStack.{u, w} B S hS W hW ⟶ 𝒴)
    (hgsurj : IsSurjective B S hS g)
    (hgflat : AlgebraicStacks.IsFlat B S hS g)
    (hglfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS g)
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (hbase : IsQuasiCompactMorphism B S hS P.fst) :
    IsQuasiCompactMorphism B S hS f :=
  isQuasiCompactMorphism_of_isQuasiCompactMorphism_fst_of_stack.{u, w} B S hS f g hgsurj hgflat
    hglfp P hP hbase

end AlgebraicGeometry.Stack

end
