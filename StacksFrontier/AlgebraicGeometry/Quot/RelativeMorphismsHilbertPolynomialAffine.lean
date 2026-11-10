/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.HilbertPolynomialEmbeddingChain
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.DirectImage
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertProjectiveSpaceRepresented
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFunctorOpenImmersionQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeMorphismsIsoLocusQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeMorphismsHilbertPolynomialProperties
public import StacksFrontier.AlgebraicGeometry.Quot.RelativelyAmpleAffineEmbedding
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFunctorClosedImmersionLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactRepresentableOfAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.CoverSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuasiAffineClosedInFinitePresentation

/-!
# `Mor^{P, ℳ}_T(Z, X)` over an affine base is a quasi-compact scheme

Let `T` be an affine scheme, `z : Z ⟶ h_T` flat, proper, of finite presentation and representable,
`x : X ⟶ h_T` separated, of finite presentation and representable, `ℳ` an invertible module on
`Z ×_T X` ample over `T` and `P` a numerical polynomial.  Then `Mor^{P, ℳ}_T(Z, X)` is represented
by a scheme which is quasi-compact and locally of finite type over `T`.

This is the core of the proof of Stacks 0DPR, carried out without the Noetherian approximation of
the source: `Z ×_T X` is a scheme `U` with a closed immersion `c : U ⟶ V` into a quasi-compact
open `V ⊆ ℙⁿ_T` with `ℳ^{⊗ d} ≅ (c ≫ o)^* 𝒪(1)` (Stacks 01VS, 0DNK); the graph (Stacks 0D1A) and
the images along `c` (Stacks 0DPF) and `o` (Stacks 0DPE) embed `Mor^{P, ℳ}_T(Z, X)` into
`Hilb^{P(d ·), 𝒪(1)}_{ℙⁿ_T/T}`, which is a scheme `H` proper over `T` (Stacks 0DPB, 0D00).  Each
step is representable by an immersion of schemes, and quasi-compact over the quasi-compact
quasi-separated `H`: the image along `o` because `V` is quasi-compact (Chevalley, Stacks 0ECX),
the graph because the locus where a family is a graph is quasi-compact (Stacks 05XD after
Noetherian approximation).

## Main results

* `AlgebraicGeometry.Space.exists_isPullback_relativeHomHilbertPolynomial_of_isAffine`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.ProjectiveQuotOverSpace
  AlgebraicGeometry.ProjectiveQuot

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}}

local notation "ℤS" => B.contains_integerBase

local notation "𝒯" => BigFppfOver.toScheme B integerBase ℤS

/-- A morphism of presheaves representable with property `P` has, over every scheme, a represented
base change with property `P`. -/
theorem exists_isPullback_of_presheaf {P : MorphismProperty Scheme.{u}}
    {F G : (BigFppfOver B integerBase ℤS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (hf : (P.inverseImage (𝒯)).presheaf f) {W : BigFppfOver B integerBase ℤS}
    (ξ : yoneda.obj W ⟶ G) :
    ∃ (V : BigFppfOver B integerBase ℤS) (s : yoneda.obj V ⟶ F) (q : V ⟶ W),
      IsPullback s (yoneda.map q) f ξ ∧ P ((𝒯).map q) :=
  ⟨_, hf.rep.fst ξ, hf.rep.snd ξ, hf.rep.isPullback ξ, hf.property_snd ξ⟩

/-- The projection `ℙⁿ × T ⟶ T` of algebraic spaces is separated. -/
private theorem isSeparated_productSnd_schemeSpace (n : ℕ) (T : BigFppfOver B integerBase ℤS) :
    IsSeparated B integerBase ℤS (ProjectiveQuotOverSpace.productSnd n (schemeSpace T)).hom := by
  let κ := QuotSituation.projectiveSiteProductIso n T
  let bP := ProjectiveQuotOverSpace.productSnd n (schemeSpace T)
  have : _root_.AlgebraicGeometry.IsProper ((𝒯).map (projectiveSiteStructure B n T)) :=
    isProper_projectiveSpaceOver n ((𝒯).obj T)
  have : IsIso κ.inv.hom := inferInstanceAs (IsIso ((ObjectProperty.ι _).mapIso κ).inv)
  have h : IsSeparated B integerBase ℤS (κ.hom.hom ≫ bP.hom) := by
    rw [show κ.hom.hom ≫ bP.hom = yoneda.map (projectiveSiteStructure B n T) from
      congrArg (fun k => k.hom) (QuotSituation.projectiveSiteProductIso_hom_productSnd n T)]
    exact (isSeparated_yoneda_map_iff B integerBase ℤS (projectiveSiteStructure B n T)).2
      inferInstance
  have e : κ.inv.hom ≫ κ.hom.hom ≫ bP.hom = bP.hom := by
    rw [← Category.assoc]
    exact (congrArg (fun k => k.hom ≫ bP.hom) κ.inv_hom_id).trans (Category.id_comp _)
  have h' := isSeparated_comp B integerBase ℤS κ.inv.hom _
    (isSeparated_of_isIso B integerBase ℤS κ.inv.hom) h
  rwa [e] at h'

/-- If `p` takes the values of `P` on the integers, then `p(d X)` takes the values of `P(d ·)`. -/
private theorem eval_comp_C_mul_X_of_eval {P : ℤ → ℤ} {p : Polynomial ℚ}
    (hP : ∀ m : ℤ, p.eval (m : ℚ) = (P m : ℚ)) (d : ℕ) (m : ℤ) :
    (p.comp (Polynomial.C (d : ℚ) * Polynomial.X)).eval (m : ℚ) = (P ((d : ℤ) * m) : ℚ) := by
  rw [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  exact_mod_cast hP ((d : ℤ) * m)

/-- A quasi-compact open of `ℙⁿ_T` is of finite presentation over an affine `T`. -/
private theorem isFinitePresentation_schemeSpaceMap_comp_projectiveSiteStructure {n : ℕ}
    {T V : BigFppfOver B integerBase ℤS} [IsAffine ((𝒯).obj T)] (o : V ⟶ projectiveSite B n T)
    [CompactSpace ((𝒯).obj V)] [_root_.AlgebraicGeometry.IsOpenImmersion ((𝒯).map o)] :
    IsFinitePresentation B integerBase ℤS
      (schemeSpaceMap (o ≫ projectiveSiteStructure B n T)).hom := by
  have : _root_.AlgebraicGeometry.IsProper ((𝒯).map (projectiveSiteStructure B n T)) :=
    isProper_projectiveSpaceOver n ((𝒯).obj T)
  refine isFinitePresentation_yoneda_map B integerBase ℤS _ ?_
  rw [Functor.map_comp]
  have : LocallyOfFinitePresentation ((𝒯).map (projectiveSiteStructure B n T)) :=
    (finitePresentation_projectiveSpaceOver n ((𝒯).obj T)).1
  have : QuasiCompact ((𝒯).map o ≫ (𝒯).map (projectiveSiteStructure B n T)) :=
    quasiCompact_of_compactSpace _
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- **`Mor^{P, ℳ}_T(Z, X)` over an affine `T` is a scheme quasi-compact and locally of finite type
over `T`.** -/
theorem exists_isPullback_relativeHomHilbertPolynomial_of_isAffine
    (T : BigFppfOver B integerBase ℤS) [IsAffine ((𝒯).obj T)]
    {Z X : (BigFppfOver B integerBase ℤS)ᵒᵖ ⥤ Type u} {z : Z ⟶ yoneda.obj T}
    {x : X ⟶ yoneda.obj T}
    (hZ : IsAlgebraicSpace B integerBase ℤS Z) (hX : IsAlgebraicSpace B integerBase ℤS X)
    (hQ : IsAlgebraicSpace B integerBase ℤS (yoneda.obj T))
    (hsep : IsSeparated B integerBase ℤS x) (hxfp : IsFinitePresentation B integerBase ℤS x)
    (hfp : IsFinitePresentation B integerBase ℤS z) (hflat : IsFlat B integerBase ℤS z)
    (hproper : IsProper B integerBase ℤS z)
    (hzrep : yoneda.relativelyRepresentable z) (hxrep : yoneda.relativelyRepresentable x)
    (M : Modules.{u, u} B integerBase ℤS (graphAmbient B integerBase ℤS z x hZ hX hQ).1
      (graphAmbient B integerBase ℤS z x hZ hX hQ).2)
    [hM : Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B integerBase ℤS (graphAmbient B integerBase ℤS z x hZ hX hQ).1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B integerBase ℤS
        (graphAmbient B integerBase ℤS z x hZ hX hQ).1
        (graphAmbient B integerBase ℤS z x hZ hX hQ).2).O)).property M]
    (hMa : IsRelativelyAmple B integerBase ℤS (graphAmbientMap B integerBase ℤS z x hZ hX hQ) M)
    {P : ℤ → ℤ} {p : Polynomial ℚ} (hP : ∀ m : ℤ, p.eval (m : ℚ) = (P m : ℚ)) :
    ∃ (Y : BigFppfOver B integerBase ℤS)
      (s : yoneda.obj Y ⟶
        (relativeHomHilbertPolynomial hZ hX hQ hsep hxfp hfp hflat hproper M P).toFunctor)
      (q : Y ⟶ T),
      IsPullback s (yoneda.map q)
        ((relativeHomHilbertPolynomial hZ hX hQ hsep hxfp hfp hflat hproper M P).ι ≫
          relativeHomProjection B integerBase ℤS Z X (yoneda.obj T) z x hZ hX hQ) (𝟙 _) ∧
      QuasiCompactFiniteType ((𝒯).map q) := by
  classical
  let G := graphAmbient B integerBase ℤS z x hZ hX hQ
  let f : G ⟶ schemeSpace T := graphAmbientMap B integerBase ℤS z x hZ hX hQ
  have hfG : IsFinitePresentation B integerBase ℤS f.hom :=
    isFinitePresentation_graphAmbientMap z x hZ hX hQ hfp hxfp
  obtain ⟨U, p₀, q₀, hsq, hinv, n, d, hd, V, c, o, hc, ho, hVc, hco, ⟨e⟩⟩ :=
    QuotSituation.exists_immersionData_of_isRelativelyAmple T f hfG M hMa
  have : IsIso p₀ := hsq.isIso_fst_of_isIso (inferInstanceAs (IsIso (yoneda.map (𝟙 T))))
  let ep := asIso p₀
  let p' : schemeSpace U ⟶ G := ObjectProperty.homMk p₀
  let pinv : G ⟶ schemeSpace U := ObjectProperty.homMk ep.inv
  have hpp : pinv ≫ p' = 𝟙 G := ObjectProperty.hom_ext _ ep.inv_hom_id
  let κ := QuotSituation.projectiveSiteProductIso n T
  have hκ : IsIso κ.hom.hom := inferInstanceAs (IsIso ((ObjectProperty.ι _).mapIso κ).hom)
  let π₁ : G ⟶ schemeSpace V := pinv ≫ schemeSpaceMap c
  let π₂ : schemeSpace V ⟶ ProjectiveQuotOverSpace.productSpace n (schemeSpace T) :=
    schemeSpaceMap o ≫ κ.hom
  let bV : schemeSpace V ⟶ schemeSpace T := schemeSpaceMap (o ≫ projectiveSiteStructure B n T)
  let bP := ProjectiveQuotOverSpace.productSnd n (schemeSpace T)
  have hpq : p₀ ≫ f.hom = yoneda.map q₀ := hsq.w.trans (Category.comp_id _)
  have hπ₁ : π₁ ≫ bV = f := ObjectProperty.hom_ext _ (by
    change ep.inv ≫ yoneda.map c ≫ yoneda.map (o ≫ projectiveSiteStructure B n T) = f.hom
    rw [← Functor.map_comp, hco, ← hpq]
    exact ep.inv_hom_id_assoc f.hom)
  have hπ₂ : π₂ ≫ bP = bV := by
    change (schemeSpaceMap o ≫ κ.hom) ≫ bP = bV
    rw [Category.assoc, QuotSituation.projectiveSiteProductIso_hom_productSnd]
    exact ObjectProperty.hom_ext _ (yoneda.map_comp _ _).symm
  have hclosed : IsClosedImmersion B integerBase ℤS π₁.hom :=
    isClosedImmersion_comp B integerBase ℤS ep.inv (yoneda.map c)
      (isClosedImmersion_of_isIso B integerBase ℤS ep.inv)
      ((presheaf_yoneda_map_iff B integerBase ℤS inferInstance c).2 hc)
  have hopen : IsOpenImmersion B integerBase ℤS π₂.hom :=
    isOpenImmersion_comp B integerBase ℤS (yoneda.map o) κ.hom.hom
      ((presheaf_yoneda_map_iff B integerBase ℤS inferInstance o).2 ho)
      (isOpenImmersion_of_isIso B integerBase ℤS κ.hom.hom)
  have : _root_.AlgebraicGeometry.IsProper ((𝒯).map (projectiveSiteStructure B n T)) :=
    isProper_projectiveSpaceOver n ((𝒯).obj T)
  have : QuasiSeparatedSpace ((𝒯).obj (projectiveSite B n T)) :=
    quasiSeparatedSpace_of_quasiSeparated ((𝒯).map (projectiveSiteStructure B n T))
  have hqc₂ : IsQuasiCompact B integerBase ℤS π₂.hom :=
    (@isQuasiCompact_comp_isIso_iff B integerBase ℤS _ _ _ (yoneda.map o) κ.hom.hom hκ).2
      (isQuasiCompact_yoneda_map_of_compactSpace B integerBase ℤS o hVc inferInstance)
  have hsepP : IsSeparated B integerBase ℤS bP.hom := isSeparated_productSnd_schemeSpace n T
  have : CompactSpace ((𝒯).obj V) := hVc
  have : _root_.AlgebraicGeometry.IsOpenImmersion ((𝒯).map o) := ho
  have : _root_.AlgebraicGeometry.IsClosedImmersion ((𝒯).map c) := hc
  have hfV : IsFinitePresentation B integerBase ℤS bV.hom :=
    isFinitePresentation_schemeSpaceMap_comp_projectiveSiteStructure o
  have hfP : IsFinitePresentation B integerBase ℤS bP.hom := isFinitePresentation_productSnd n _
  let MG := HilbertPresheafModel.canonical f
  let MV := HilbertPresheafModel.canonical bV
  let MP := HilbertPresheafModel.canonical bP
  -- the twisting modules
  let O := productTwistingModule n (schemeSpace T)
  have hOqc : O.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_of_isInvertible B integerBase ℤS _ O
      (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
        (isInvertible_productTwistingModule n (schemeSpace T)))
  let M₀ := (modulePullback B integerBase ℤS p').obj M
  have hM₀ : Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B integerBase ℤS (yoneda.obj U))
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B integerBase ℤS
        (yoneda.obj U) (isAlgebraicSpace_yoneda B integerBase ℤS U)).O)).property M₀ :=
    isInvertible_modulePullback B integerBase ℤS p' M
  have hM₀qc : M₀.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isInvertible p' M hM
  let eρ := QuotSituation.modulePullbackProjectiveSiteIso (c ≫ o) O hOqc
      (QuotSituation.isoReadingTwistingModuleIso n T) ≪≫
    (QuotSituation.associatedSpaceModule U).mapIso e.symm ≪≫
    (QuotSituation.invertibleTensorPowerAssociatedIso U M₀ (hM₀ := hM₀) hM₀qc (hN := hinv)
      (d : ℤ)).symm
  have hπ₁₂ : π₁ ≫ π₂ = pinv ≫ (schemeSpaceMap (c ≫ o) ≫ κ.hom) := by
    change (pinv ≫ schemeSpaceMap c) ≫ schemeSpaceMap o ≫ κ.hom = _
    rw [Category.assoc, ← Category.assoc (schemeSpaceMap c)]
    congr 2
  let eM : (modulePullback B integerBase ℤS π₁).obj ((modulePullback B integerBase ℤS π₂).obj O) ≅
      invertibleTensorPower B integerBase ℤS G.1 G.2 M (d : ℤ) :=
    (modulePullbackCompIso B integerBase ℤS π₁ π₂).app O ≪≫
      eqToIso (congrArg (fun k => (modulePullback B integerBase ℤS k).obj O) hπ₁₂) ≪≫
      modulePullbackCompIsoInvertibleTensorPower pinv p' hpp _ O M (d : ℤ) eρ
  -- the Hilbert scheme of `ℙⁿ_T`
  obtain ⟨H, ξH, qH, hmono, hrange, hbase, hHprop⟩ :=
    exists_mono_hilbertPolynomialSubfunctor_productSnd n T MP (eval_comp_C_mul_X_of_eval hP d)
  have : _root_.AlgebraicGeometry.IsProper ((𝒯).map qH) := hHprop
  have : CompactSpace ((𝒯).obj H) := QuasiCompact.compactSpace_of_compactSpace ((𝒯).map qH)
  have : QuasiSeparatedSpace ((𝒯).obj H) := quasiSeparatedSpace_of_quasiSeparated ((𝒯).map qH)
  -- the chain of embeddings
  let μG := morToHilbertModel z x hZ hX hQ MG hsep hfp hflat hproper
  let μ₁ := hilbertModelMapOfClosed hπ₁ hclosed MG MV
  let μ₂ := hilbertModelMap hπ₂ hopen hsepP MV MP
  let F := relativeHomHilbertPolynomial hZ hX hQ hsep hxfp hfp hflat hproper M P
  have hle : Subfunctor.range (F.ι ≫ μG ≫ μ₁ ≫ μ₂) ≤ Subfunctor.range ξH := by
    rintro ⟨T'⟩ _ ⟨w, rfl⟩
    refine (hrange T' _).2 ?_
    have hG : MG.familyEquiv T' (μG.app (Opposite.op T') w.1) =
        (graphTransformation hZ hX hQ hsep hfp hflat hproper).app (Opposite.op T')
          (ULift.up w.1) :=
      types_congr_hom (MG.iso.inv_hom_id_app (Opposite.op T'))
        ((graphTransformation hZ hX hQ hsep hfp hflat hproper).app (Opposite.op T')
          (ULift.up w.1))
    have hw : MG.familyEquiv T' (μG.app (Opposite.op T') w.1) ∈
        (hilbertPolynomialSubfunctor f hfG M P).obj (Opposite.op T') := by
      rw [hG]
      exact w.2
    exact familyEquiv_hilbertModelMapOfClosed_comp_mem hπ₁ hclosed hπ₂ hopen hsepP hfG hfV hfP
      MG MV MP O M (d : ℤ) eM P _ hw
  let φ : F.toFunctor ⟶ yoneda.obj H :=
    Subfunctor.lift (F.ι ≫ μG ≫ μ₁ ≫ μ₂) hle ≫ inv (Subfunctor.toRange ξH)
  have hφ : φ ≫ ξH = F.ι ≫ μG ≫ μ₁ ≫ μ₂ := by
    rw [← Subfunctor.toRange_ι ξH, Category.assoc, IsIso.inv_hom_id_assoc, Subfunctor.lift_ι]
  -- base changes along `ξH`
  obtain ⟨V₂, s₂, q₂, hpb₂, ho₂, hc₂⟩ :=
    exists_isPullback_compactSpace_hilbertModelMap hπ₂ hopen hsepP hqc₂ MV MP H ξH
  have : _root_.AlgebraicGeometry.IsOpenImmersion ((𝒯).map q₂) := ho₂
  have : QuasiSeparatedSpace ((𝒯).obj V₂) := quasiSeparatedSpace_of_quasiSeparated ((𝒯).map q₂)
  obtain ⟨C₁, s₃, q₃, hpb₃, hc₃⟩ := exists_isPullback_of_presheaf
    (isClosedImmersion_hilbertModelMapOfClosed hπ₁ hclosed hfV MG MV) s₂
  have : _root_.AlgebraicGeometry.IsClosedImmersion ((𝒯).map q₃) := hc₃
  have : CompactSpace ((𝒯).obj C₁) := QuasiCompact.compactSpace_of_compactSpace ((𝒯).map q₃)
  have : QuasiSeparatedSpace ((𝒯).obj C₁) := quasiSeparatedSpace_of_quasiSeparated ((𝒯).map q₃)
  obtain ⟨O₃, s₄, q₄, hpb₄, ho₄, hc₄⟩ :=
    exists_isPullback_compactSpace_morToHilbertModel hZ hX hQ hsep hfp hflat hproper hzrep hxrep
      MG C₁ s₃
  have : _root_.AlgebraicGeometry.IsOpenImmersion ((𝒯).map q₄) := ho₄
  obtain ⟨Y, s₅, q₅, hpb₅, hc₅⟩ := exists_isPullback_of_presheaf
    (isOpenImmersion_and_isClosedImmersion_relativeHomHilbertPolynomial_ι hZ hX hQ hsep hxfp hfp
      hflat hproper M P).2 s₄
  have : _root_.AlgebraicGeometry.IsClosedImmersion ((𝒯).map q₅) := hc₅
  have : CompactSpace ((𝒯).obj Y) := QuasiCompact.compactSpace_of_compactSpace ((𝒯).map q₅)
  have hall := hpb₅.paste_vert (hpb₄.paste_vert (hpb₃.paste_vert hpb₂))
  -- `s₅` is an isomorphism
  have hs₅φ : s₅ ≫ φ = yoneda.map q₅ ≫ yoneda.map q₄ ≫ yoneda.map q₃ ≫ yoneda.map q₂ := by
    rw [← cancel_mono ξH, Category.assoc, hφ]
    exact hall.w
  let l := hall.lift (𝟙 F.toFunctor) φ (by rw [Category.id_comp, hφ])
  have hl₁ : l ≫ s₅ = 𝟙 _ := hall.lift_fst _ _ _
  have hl₂ : l ≫ (yoneda.map q₅ ≫ yoneda.map q₄ ≫ yoneda.map q₃ ≫ yoneda.map q₂) = φ :=
    hall.lift_snd _ _ _
  have : IsIso s₅ := ⟨⟨l, hall.hom_ext (by rw [Category.assoc, hl₁, Category.comp_id,
      Category.id_comp]) (by rw [Category.assoc, hl₂, hs₅φ, Category.id_comp]), hl₁⟩⟩
  -- the base
  have h₂b : μ₂ ≫ MP.toBase = MV.toBase := hilbertModelMap_comp_toBase hπ₂ hopen hsepP MV MP
  have h₁b : μ₁ ≫ MV.toBase = MG.toBase := hilbertModelMapOfClosed_comp_toBase hπ₁ hclosed MG MV
  have h₀b : μG ≫ MG.toBase =
      relativeHomProjection B integerBase ℤS Z X (yoneda.obj T) z x hZ hX hQ :=
    morToHilbertModel_comp_toBase z x hZ hX hQ MG hsep hfp hflat hproper
  have hproj : F.ι ≫ relativeHomProjection B integerBase ℤS Z X (yoneda.obj T) z x hZ hX hQ =
      φ ≫ yoneda.map qH := by
    have e1 : (F.ι ≫ μG ≫ μ₁ ≫ μ₂) ≫ MP.toBase =
        F.ι ≫ relativeHomProjection B integerBase ℤS Z X (yoneda.obj T) z x hZ hX hQ := by
      rw [Category.assoc, Category.assoc, Category.assoc, h₂b, h₁b, h₀b]
      rfl
    have e2 : (F.ι ≫ μG ≫ μ₁ ≫ μ₂) ≫ MP.toBase = φ ≫ yoneda.map qH := by
      rw [← hφ, Category.assoc, hbase]
      rfl
    exact e1.symm.trans e2
  refine ⟨Y, s₅, q₅ ≫ q₄ ≫ q₃ ≫ q₂ ≫ qH, IsPullback.of_horiz_isIso ⟨?_⟩, ?_, ?_⟩
  · rw [hproj, ← Category.assoc, hs₅φ, Category.comp_id]
    simp only [Functor.map_comp, Category.assoc]
  · exact quasiCompact_of_compactSpace _
  · simp only [Functor.map_comp]
    have : LocallyOfFiniteType ((𝒯).map qH) := inferInstance
    have : LocallyOfFiniteType ((𝒯).map q₂) := inferInstance
    have : LocallyOfFiniteType ((𝒯).map q₃) := inferInstance
    have : LocallyOfFiniteType ((𝒯).map q₄) := inferInstance
    have : LocallyOfFiniteType ((𝒯).map q₅) := inferInstance
    exact inferInstance

end AlgebraicGeometry.Space

end
