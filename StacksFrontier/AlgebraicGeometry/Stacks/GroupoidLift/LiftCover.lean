module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.LiftUniqueness
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.StackFppfLift
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.StackChartPairIso

/-!
# Lifts of a deformation situation along a faithfully flat finitely presented cover

Let `𝒳` be an algebraic stack over `S` whose structure morphism is locally of finite
presentation, `i : T ⟶ T'` a first-order thickening of affines (a deformation situation
`A' → A`), `k : c' ⟶ T'` flat, surjective and locally of finite presentation with `c'` affine,
and `c = T ×_{T'} c'`. Let `x` be an object over `T` and `y = x|_c`.

* **Injectivity** (`AlgebraicGeometry.Stack.GroupoidLift.exists_hom_of_cover`): two lifts
  `x ⟶ z₁`, `x ⟶ z₂` of `x` over `T'` whose pullbacks to `c'` are the same lift `y ⟶ y'` of
  `y` are isomorphic as lifts of `x`.

The lift `y'` itself serves as the chart: by the 2-Yoneda lemma it is a morphism
`(Sch/c') ⟶ 𝒳`, and with the chart algebra `P = Γ(c')` (finitely presented over `A'`) its
arrows have a formally étale finitely presented chart after a surjective étale refinement `C₁`
of `P` (`AlgebraicGeometry.Stack.GroupoidLift.StackChart.exists_arrowChart_finitePresentation`).
Over the faithfully flat finitely presented cover `A' → C₁`, both lifts restrict to the chart
lift of the point `P → C₁`, and the uniqueness at a chart point
(`AlgebraicGeometry.Stack.GroupoidLift.StackChart.exists_iso_of_chartLift`) gives the
isomorphism, transported from `Spec A'` to `T'`. For effectivity the identification of the two
pullbacks gives the arrow over `Spec (C₁ ⊗ C₁)` whose reduction is the descent arrow of `x`
(`AlgebraicGeometry.Stack.GroupoidLift.map_descArr_eq_chartRbar_of_cover`), the lifting step
at a chart point (`AlgebraicGeometry.Stack.GroupoidLift.StackChart.exists_lift_of_chartLift`)
descends it, and injectivity over the base `c'` identifies the pullback of the result with `y'`.

The only use of the finiteness of `𝒳 ⟶ S` is the finiteness of the space of arrows of the chart
`y'`, whose two objects over `Spec (P ⊗ P)` are isomorphic (through the lift over `T'`, resp.
through the descent datum). The forms `exists_hom_of_cover_of_arrSpace` and
`exists_lift_of_cover_of_arrSpace` take exactly that
(`AlgebraicGeometry.Stack.GroupoidLift.ArrowSpacesLocallyOfFinitePresentation`), which also holds
when only the inertia of `𝒳` is locally of finite presentation
(`AlgebraicGeometry.Stack.GroupoidLift.arrowSpacesLocallyOfFinitePresentation_of_inertia`).
-/

@[expose] public section

open scoped TensorProduct
open CategoryTheory Opposite Limits
open AlgebraicGeometry.Space.ChartDescent

namespace AlgebraicGeometry.Stack

universe w u

namespace GroupoidLift

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T' : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
  {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

open StackChart

/-- The projection of `𝒳` to `BigFppfOver B S hS` is a fibered category. -/
local instance : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered

/-- The image of the canonical arrow `a ⟶ 1_{c'}` under `G`, followed by a morphism over `𝟙 c'`,
lies over the structure morphism of `a`. -/
private theorem isHomLift_map_comp_of_isHomLift_id {c' : BigFppfOver B S hS}
    (G : BasedCategory.ofFunctor (Over.forget c') ⥤ᵇ BasedCategory.ofFunctor 𝒳.val.p)
    {y : 𝒳.val.obj} (ε : G.obj (Over.mk (𝟙 c')) ⟶ y) [𝒳.val.p.IsHomLift (𝟙 c') ε]
    (a : Over c') : 𝒳.val.p.IsHomLift a.hom (G.map (Over.mkIdTerminal.from a) ≫ ε) :=
  IsHomLift.comp_lift_id_right' 𝒳.val.p a.hom (G.map (Over.mkIdTerminal.from a)) c' ε

/-- A map `Spec C → Spec Γ(c')` followed by `Spec Γ(c') → c' → T'` is the structure map of `C`. -/
private theorem specOverMap_comp_sectionsHom_comp {c' : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj c')] (k : c' ⟶ T')
    {C : SmallAlg (ringOf B S hS T') B.cutoff} (g : sectionsAlg c' k ⟶ C) :
    (specOverMap g ≫ sectionsHom c' k) ≫ k = specOverToBase C := by
  rw [Category.assoc, sectionsHom_comp, specOverMap_comp_toBase]

/-- For a flat surjective finitely presented `k : c' → T'`, `Γ(c')` is finitely presented over
`Γ(T')`. -/
private theorem finitePresentation_of_chart {c' : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj c')] (k : c' ⟶ T')
    [Flat ((BigFppfOver.toScheme B S hS).map k)] [Surjective ((BigFppfOver.toScheme B S hS).map k)]
    [LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map k)] :
    Algebra.FinitePresentation (ringOf B S hS T') (sectionsAlg c' k).obj :=
  finitePresentation_of_specOverToBase _ (by
    rw [← sectionsHom_comp c' k, Functor.map_comp]; infer_instance)

/-- If `f₁ : Γ(c') ⟶ C` is an étale surjective cover of the chart of a flat surjective finitely
presented `k : c' → T'`, then `C` is faithfully flat and finitely presented over `Γ(T')`. -/
private theorem faithfullyFlat_finitePresentation_of_chart {c' : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj c')] (k : c' ⟶ T')
    {C : SmallAlg (ringOf B S hS T') B.cutoff} (f₁ : sectionsAlg c' k ⟶ C)
    [Etale ((BigFppfOver.toScheme B S hS).map (specOverMap f₁))]
    [Surjective ((BigFppfOver.toScheme B S hS).map (specOverMap f₁))]
    [Flat ((BigFppfOver.toScheme B S hS).map k)] [Surjective ((BigFppfOver.toScheme B S hS).map k)]
    [LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map k)] :
    Module.FaithfullyFlat (ringOf B S hS T') C.obj ∧
      Algebra.FinitePresentation (ringOf B S hS T') C.obj := by
  have h : specOverToBase C = (specOverMap f₁ ≫ sectionsHom c' k) ≫ k :=
    (specOverMap_comp_sectionsHom_comp k f₁).symm
  refine ⟨faithfullyFlat_of_specOverToBase C ?_ ?_, finitePresentation_of_specOverToBase C ?_⟩ <;>
    rw [h, Functor.map_comp, Functor.map_comp] <;> infer_instance

/-- **Two lifts with the same pullback to an fppf cover are isomorphic.** Let `i : T ⟶ T'` be
a deformation situation of affines, `k : c' ⟶ T'` flat, surjective and locally of finite
presentation with `c'` affine, and `c = T ×_{T'} c'` (by `j`, `l`). If two lifts
`φ₁ : x ⟶ z₁`, `φ₂ : x ⟶ z₂` of `x` along `i` both pull back to the lift `β : y ⟶ y'` of
`y = x|_c` (through `ρ₁`, `ρ₂` over `k` with `β ≫ ρₙ = α ≫ φₙ`), then there is `θ : z₁ ⟶ z₂`
over the identity of `T'` with `φ₁ ≫ θ = φ₂`.

The finiteness used is that of the space of arrows of a chart whose two objects over
`Spec (P ⊗ P)` are isomorphic (`harr`). -/
theorem exists_hom_of_cover_of_arrSpace (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (harr : ArrowSpacesLocallyOfFinitePresentation B S hS 𝒳)
    {T c c' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj c')]
    (i : T ⟶ T') (hi : Deformation.Artin.IsDeformationSituation
      ((BigFppfOver.toScheme B S hS).map i).appTop.hom)
    (j : c ⟶ T) (l : c ⟶ c') (k : c' ⟶ T') (hpb : IsPullback j l i k)
    (hkf : Flat ((BigFppfOver.toScheme B S hS).map k))
    (hks : Surjective ((BigFppfOver.toScheme B S hS).map k))
    (hkp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map k))
    {x y y' z₁ z₂ : 𝒳.val.obj} (hx : 𝒳.val.p.obj x = T) (α : y ⟶ x)
    (hα : 𝒳.val.p.IsHomLift j α) (β : y ⟶ y') (hβ : 𝒳.val.p.IsHomLift l β)
    (φ₁ : x ⟶ z₁) (hφ₁ : 𝒳.val.p.IsHomLift i φ₁) (φ₂ : x ⟶ z₂) (hφ₂ : 𝒳.val.p.IsHomLift i φ₂)
    (ρ₁ : y' ⟶ z₁) (hρ₁ : 𝒳.val.p.IsHomLift k ρ₁) (ρ₂ : y' ⟶ z₂)
    (hρ₂ : 𝒳.val.p.IsHomLift k ρ₂) (hw₁ : β ≫ ρ₁ = α ≫ φ₁) (hw₂ : β ≫ ρ₂ = α ≫ φ₂) :
    ∃ θ : z₁ ⟶ z₂, 𝒳.val.p.IsHomLift (𝟙 T') θ ∧ φ₁ ≫ θ = φ₂ := by
  classical
  obtain ⟨_, ⟨_, hst⟩, _⟩ := id h𝒳
  set A' := ringOf B S hS T'
  have hA : Cardinal.mk A' < B.cutoff := card_sections_lt T'
  have hsurjI : Function.Surjective (algebraMap A' (sectionsAlg T i).obj) := hi.1
  have hI : kerIdeal i ^ 2 = ⊥ := hi.2
  have hp := 𝒳.isFiberedInGroupoids
  have hy' : 𝒳.val.p.obj y' = c' := @IsHomLift.codomain_eq _ _ _ _ 𝒳.val.p _ _ _ _ l β hβ
  have hz₁ : 𝒳.val.p.obj z₁ = T' := @IsHomLift.codomain_eq _ _ _ _ 𝒳.val.p _ _ _ _ i φ₁ hφ₁
  have hz₂ : 𝒳.val.p.obj z₂ = T' := @IsHomLift.codomain_eq _ _ _ _ 𝒳.val.p _ _ _ _ i φ₂ hφ₂
  -- the lift `y'` as a chart
  let E := Functor.twoYonedaEvaluation 𝒳.val.p c'
  let : E.IsEquivalence := Functor.twoYonedaEvaluation_isEquivalence 𝒳.val.p 𝒳.property c'
  let aB := E.objPreimage ⟨y', hy'⟩
  let e := E.objObjPreimageIso ⟨y', hy'⟩
  let a : schemeFibredCategory B S hS c' ⟶ 𝒳 := Bicategory.InducedBicategory.mkHom aB
  let ε₀ : aB.obj (Over.mk (𝟙 c')) ⟶ y' := e.hom.1
  have hε₀ : 𝒳.val.p.IsHomLift (𝟙 c') ε₀ := e.hom.2
  let P := sectionsAlg c' k
  let ι : specOver P ⟶ c' := sectionsHom c' k
  have : Algebra.FinitePresentation A' P.obj := finitePresentation_of_chart k
  -- the two objects of the chart over `Spec (P ⊗ P)` are isomorphic, through `z₁`
  have hθ : Nonempty (pairObj₁ a ι ≅ pairObj₀ a ι) := by
    have : 𝒳.val.p.IsStronglyCartesian k ρ₁ := hp.isStronglyCartesian_homLift k ρ₁
    let m₀ : specOver (pairAlg P) ⟶ c' := specOverMap (SmallAlg.homMk (vtx₀ P)) ≫ ι
    let m₁ : specOver (pairAlg P) ⟶ c' := specOverMap (SmallAlg.homMk (vtx₁ P)) ≫ ι
    let s₀ : ξ a ι (vtx₀ P) ⟶ y' := aB.map (Over.mkIdTerminal.from (pt ι (vtx₀ P))) ≫ ε₀
    have hs₀ : 𝒳.val.p.IsHomLift m₀ s₀ :=
      isHomLift_map_comp_of_isHomLift_id aB ε₀ (pt ι (vtx₀ P))
    have hk : m₀ ≫ k = m₁ ≫ k := (specOverMap_comp_sectionsHom_comp k _).trans
      (specOverMap_comp_sectionsHom_comp k _).symm
    let s₁ : ξ a ι (vtx₀ P) ⟶ y' := Functor.IsStronglyCartesian.map 𝒳.val.p k ρ₁ hk (s₀ ≫ ρ₁)
    have hs₁ : 𝒳.val.p.IsHomLift m₁ s₁ := Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ _
    exact nonempty_pairObj_iso a ι ε₀ hε₀ s₀ s₁ hs₀ hs₁
  -- the arrow chart, after a surjective étale refinement `C₁` of `P`
  obtain ⟨C₁, f₁, hf₁s, hf₁e, Q, _, _, b, hb, sV, tV, hsV, htV, ε, hε⟩ :=
    exists_arrowChart_finitePresentation_of_isLocallyOfFinitePresentation a ι h𝒳
      (harr.isLocallyOfFinitePresentation a ι hθ)
      (AlgHom.id A' P.obj)
  have hC : Cardinal.mk C₁.obj < B.cutoff := C₁.2
  obtain ⟨hFF, hFP⟩ := faithfullyFlat_finitePresentation_of_chart k f₁
  -- the chart point over `C₁` and its reduction
  let q := (thk (kerIdeal i) hI (descNerve T' hC 0)).q
  let u : P.obj →ₐ[A'] (descNerve T' hC 0).obj := f₁.hom.hom.comp (AlgHom.id A' P.obj)
  let εbar := q.hom.hom.comp ε
  have hε' : b.app _ εbar = Arr.idt (q.hom.hom.comp u) :=
    (b.natural q ε).symm.trans ((congrArg _ hε).trans (Arr.map_idt _ _))
  -- the object over `Spec (A' ⧸ I) ≅ T`
  let φT := redToBase i hsurjI hA
  let xb := Functor.IsPreFibered.pullbackObj hx φT
  have hxb : 𝒳.val.p.obj xb = specOver (red (kerIdeal i) (baseAlg (κ := B.cutoff) hA)) :=
    Functor.IsPreFibered.pullbackObj_proj hx φT
  let c₀ : xb ⟶ x := Functor.IsPreFibered.pullbackMap hx φT
  have : 𝒳.val.p.IsStronglyCartesian φT c₀ := hp.isStronglyCartesian_homLift φT c₀
  -- the chart object over `C₁` maps to `y'`
  let ν : specOver (descNerve T' hC 0) ⟶ c' := specOverMap (SmallAlg.homMk u) ≫ ι
  let t : ξ a ι u ⟶ y' := aB.map (Over.mkIdTerminal.from (pt ι u)) ≫ ε₀
  have ht : 𝒳.val.p.IsHomLift ν t := isHomLift_map_comp_of_isHomLift_id aB ε₀ (pt ι u)
  have hνk : ν ≫ k = specOverToBase (descNerve T' hC 0) :=
    specOverMap_comp_sectionsHom_comp k _
  have hkey : (specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot ≫ φT) ≫ i =
      (specOverMap q ≫ ν) ≫ k := by
    rw [Category.assoc, Category.assoc, redToBase_comp, hνk, specOverMap_comp_toBase,
      specOverMap_comp_toBase]
  let μ := hpb.lift _ _ hkey
  have hμj : μ ≫ j = specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot ≫ φT :=
    hpb.lift_fst _ _ _
  have hμl : μ ≫ l = specOverMap q ≫ ν := hpb.lift_snd _ _ _
  have : 𝒳.val.p.IsStronglyCartesian l β := hp.isStronglyCartesian_homLift l β
  let c₁ : ξ a ι (q.hom.hom.comp u) ⟶ y :=
    Functor.IsStronglyCartesian.map 𝒳.val.p l β hμl.symm (StackChart.trans a ι q u ≫ t)
  have hc₁β : c₁ ≫ β = StackChart.trans a ι q u ≫ t := Functor.IsStronglyCartesian.fac _ _ _ _ _
  let cm : ξ a ι (q.hom.hom.comp u) ⟶ xb :=
    Functor.IsStronglyCartesian.map 𝒳.val.p φT c₀ hμj (c₁ ≫ α)
  have hcm : cm ≫ c₀ = c₁ ≫ α := Functor.IsStronglyCartesian.fac _ _ _ _ _
  have hc : 𝒳.val.p.IsHomLift (specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot) cm :=
    Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ _
  -- the two lifts, transported to `Spec A'`
  have := isIso_specOverToBase_baseAlg (T' := T') hA
  let toB := specOverToBase (T' := T') (baseAlg (κ := B.cutoff) hA)
  have hq : φT ≫ i = specOverMap (thk (kerIdeal i) hI (baseAlg (κ := B.cutoff) hA)).q ≫ toB := by
    rw [redToBase_comp, specOverMap_comp_toBase]
  have hbm : ν ≫ k = specOverMap (baseMap B.aleph0_lt_cutoff hC hA) ≫ toB :=
    hνk.trans (specOverMap_comp_toBase _).symm
  have key : ∀ {z : 𝒳.val.obj} (hz : 𝒳.val.p.obj z = T') (φ : x ⟶ z)
      (_ : 𝒳.val.p.IsHomLift i φ) (ρ : y' ⟶ z) (_ : 𝒳.val.p.IsHomLift k ρ)
      (_ : β ≫ ρ = α ≫ φ),
      ∃ (d : Functor.IsPreFibered.pullbackObj hz toB ⟶ z) (φ' : xb ⟶ _) (ζ : ξ a ι u ⟶ _),
        d = Functor.IsPreFibered.pullbackMap hz toB ∧ φ' ≫ d = c₀ ≫ φ ∧
        𝒳.val.p.IsHomLift (specOverMap (thk (kerIdeal i) hI (baseAlg (κ := B.cutoff) hA)).q) φ' ∧
        𝒳.val.p.IsHomLift (specOverMap (baseMap B.aleph0_lt_cutoff hC hA)) ζ ∧
        cm ≫ φ' = StackChart.trans a ι q u ≫ ζ := by
    intro z hz φ hφ ρ hρ hw
    let d := Functor.IsPreFibered.pullbackMap hz toB
    have : 𝒳.val.p.IsStronglyCartesian toB d := hp.isStronglyCartesian_homLift toB d
    let φ' := Functor.IsStronglyCartesian.map 𝒳.val.p toB d hq (c₀ ≫ φ)
    have hφ'd : φ' ≫ d = c₀ ≫ φ := Functor.IsStronglyCartesian.fac _ _ _ _ _
    let ζ := Functor.IsStronglyCartesian.map 𝒳.val.p toB d hbm (t ≫ ρ)
    have hζd : ζ ≫ d = t ≫ ρ := Functor.IsStronglyCartesian.fac _ _ _ _ _
    have hφ'l : 𝒳.val.p.IsHomLift
        (specOverMap (thk (kerIdeal i) hI (baseAlg (κ := B.cutoff) hA)).q) φ' :=
      Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ _
    have hζl : 𝒳.val.p.IsHomLift (specOverMap (baseMap B.aleph0_lt_cutoff hC hA)) ζ :=
      Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ _
    refine ⟨d, φ', ζ, rfl, hφ'd, hφ'l, hζl, ?_⟩
    have h₂ : 𝒳.val.p.IsHomLift (specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot ≫
        specOverMap (thk (kerIdeal i) hI (baseAlg (κ := B.cutoff) hA)).q)
        (StackChart.trans a ι q u ≫ ζ) :=
      isHomLift_of_eq (spec_baseMap_q hA hC (kerIdeal i) hI) inferInstance
    refine Functor.IsStronglyCartesian.ext 𝒳.val.p toB d
      (specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot ≫
        specOverMap (thk (kerIdeal i) hI (baseAlg (κ := B.cutoff) hA)).q) ?_
    calc (cm ≫ φ') ≫ d = cm ≫ c₀ ≫ φ := by rw [Category.assoc, hφ'd]
      _ = c₁ ≫ α ≫ φ := by rw [← Category.assoc, hcm, Category.assoc]
      _ = c₁ ≫ β ≫ ρ := by rw [hw]
      _ = StackChart.trans a ι q u ≫ t ≫ ρ := by rw [← Category.assoc, hc₁β, Category.assoc]
      _ = (StackChart.trans a ι q u ≫ ζ) ≫ d := by rw [Category.assoc, hζd]
  obtain ⟨d₁, φ₁', ζ₁, hd₁, hφ₁'d, hφ₁'l, hζ₁l, hcφ₁⟩ := key hz₁ φ₁ hφ₁ ρ₁ hρ₁ hw₁
  obtain ⟨d₂, φ₂', ζ₂, hd₂, hφ₂'d, hφ₂'l, hζ₂l, hcφ₂⟩ := key hz₂ φ₂ hφ₂ ρ₂ hρ₂ hw₂
  obtain ⟨θ', hθ', hφθ⟩ := exists_iso_of_chartLift hA hC (kerIdeal i) hI hst b hb sV tV hsV htV
    hxb u cm hc εbar hε' ζ₁ ζ₂ φ₁' φ₂' hζ₁l hζ₂l hφ₁'l hφ₂'l hcφ₁ hcφ₂
  -- back to `T'`
  have : IsIso c₀ := Functor.IsStronglyCartesian.isIso_of_base_isIso 𝒳.val.p φT c₀
  have hd₁l : 𝒳.val.p.IsHomLift toB d₁ := by rw [hd₁]; infer_instance
  have hd₂l : 𝒳.val.p.IsHomLift toB d₂ := by rw [hd₂]; infer_instance
  have : 𝒳.val.p.IsStronglyCartesian toB d₁ := hp.isStronglyCartesian_homLift toB d₁
  have : IsIso d₁ := Functor.IsStronglyCartesian.isIso_of_base_isIso 𝒳.val.p toB d₁
  have := IsHomLift.inv 𝒳.val.p toB d₁
  refine ⟨inv d₁ ≫ θ' ≫ d₂, isHomLift_of_eq (by simp) (inferInstance :
    𝒳.val.p.IsHomLift (inv toB ≫ 𝟙 _ ≫ toB) (inv d₁ ≫ θ' ≫ d₂)), ?_⟩
  rw [← cancel_epi c₀, ← Category.assoc, ← hφ₁'d, Category.assoc, IsIso.hom_inv_id_assoc,
    ← Category.assoc, hφθ, hφ₂'d]

/-- **Two lifts with the same pullback to an fppf cover are isomorphic.** Let `i : T ⟶ T'` be
a deformation situation of affines, `k : c' ⟶ T'` flat, surjective and locally of finite
presentation with `c'` affine, and `c = T ×_{T'} c'` (by `j`, `l`). If two lifts
`φ₁ : x ⟶ z₁`, `φ₂ : x ⟶ z₂` of `x` along `i` both pull back to the lift `β : y ⟶ y'` of
`y = x|_c` (through `ρ₁`, `ρ₂` over `k` with `β ≫ ρₙ = α ≫ φₙ`), then there is `θ : z₁ ⟶ z₂`
over the identity of `T'` with `φ₁ ≫ θ = φ₂`. -/
theorem exists_hom_of_cover (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (f : 𝒳 ⟶ schemeFibredCategory B S hS (Over.mk (𝟙 (B.obj hS))))
    (hf : HasPropertyOnEverySmoothDiagram B S hS
      (fun _ _ g => Space.IsLocallyOfFinitePresentation B S hS g) f)
    {T c c' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj c')]
    (i : T ⟶ T') (hi : Deformation.Artin.IsDeformationSituation
      ((BigFppfOver.toScheme B S hS).map i).appTop.hom)
    (j : c ⟶ T) (l : c ⟶ c') (k : c' ⟶ T') (hpb : IsPullback j l i k)
    (hkf : Flat ((BigFppfOver.toScheme B S hS).map k))
    (hks : Surjective ((BigFppfOver.toScheme B S hS).map k))
    (hkp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map k))
    {x y y' z₁ z₂ : 𝒳.val.obj} (hx : 𝒳.val.p.obj x = T) (α : y ⟶ x)
    (hα : 𝒳.val.p.IsHomLift j α) (β : y ⟶ y') (hβ : 𝒳.val.p.IsHomLift l β)
    (φ₁ : x ⟶ z₁) (hφ₁ : 𝒳.val.p.IsHomLift i φ₁) (φ₂ : x ⟶ z₂) (hφ₂ : 𝒳.val.p.IsHomLift i φ₂)
    (ρ₁ : y' ⟶ z₁) (hρ₁ : 𝒳.val.p.IsHomLift k ρ₁) (ρ₂ : y' ⟶ z₂)
    (hρ₂ : 𝒳.val.p.IsHomLift k ρ₂) (hw₁ : β ≫ ρ₁ = α ≫ φ₁) (hw₂ : β ≫ ρ₂ = α ≫ φ₂) :
    ∃ θ : z₁ ⟶ z₂, 𝒳.val.p.IsHomLift (𝟙 T') θ ∧ φ₁ ≫ θ = φ₂ :=
  exists_hom_of_cover_of_arrSpace h𝒳
    (arrowSpacesLocallyOfFinitePresentation_of_structureMorphism h𝒳 f hf)
    i hi j l k hpb hkf hks hkp hx α hα β hβ φ₁ hφ₁ φ₂ hφ₂ ρ₁ hρ₁ ρ₂ hρ₂ hw₁ hw₂

section Aux

variable {U₀ : BigFppfOver B S hS} {a : schemeFibredCategory B S hS U₀ ⟶ 𝒳}
  {P : SmallAlg (ringOf B S hS T') B.cutoff} {ι : specOver P ⟶ U₀}
  {hA : Cardinal.mk (ringOf B S hS T') < B.cutoff} {C' : Type u} [CommRing C']
  [Algebra (ringOf B S hS T') C'] {hC : Cardinal.mk C' < B.cutoff} {I : Ideal (ringOf B S hS T')}
  {hI : I ^ 2 = ⊥}

/-- One vertex of the reduction of a descent datum over a cover: the factorisation through
`y₂` of the reduced chart object at the vertex `V` is the composite through the reduced vertex
`rV`. -/
theorem trans_fac_of_cover {c c' c₂ : BigFppfOver B S hS}
    (u : P.obj →ₐ[ringOf B S hS T'] (descNerve T' hC 0).obj)
    (V : descNerve T' hC 0 ⟶ descNerve T' hC 1)
    (rV : red I (descNerve T' hC 0) ⟶ red I (descNerve T' hC 1))
    (hsq : qC hC I hI ≫ rV = V ≫ qC₁ hC I hI)
    {y y' y₂ w : 𝒳.val.obj} (l : c ⟶ c') (β : y ⟶ y') [𝒳.val.p.IsStronglyCartesian l β]
    (t : ξ a ι u ⟶ y') (μ : specOver (red I (descNerve T' hC 0)) ⟶ c)
    (c₁ : ξ a ι ((qC hC I hI).hom.hom.comp u) ⟶ y) [𝒳.val.p.IsHomLift μ c₁]
    (hc₁β : c₁ ≫ β = StackChart.trans a ι (qC hC I hI) u ≫ t) (σ : w ⟶ y')
    (s : ξ a ι (V.hom.hom.comp u) ⟶ w) (hs : s ≫ σ = StackChart.trans a ι V u ≫ t)
    (δ : y₂ ⟶ w) (μ₂ : specOver (red I (descNerve T' hC 1)) ⟶ c₂)
    (e : ξ a ι ((qC₁ hC I hI).hom.hom.comp (V.hom.hom.comp u)) ⟶ y₂) [𝒳.val.p.IsHomLift μ₂ e]
    (he : e ≫ δ = StackChart.trans a ι (qC₁ hC I hI) (V.hom.hom.comp u) ≫ s) (h : c₂ ⟶ c)
    (γ : y₂ ⟶ y) [𝒳.val.p.IsHomLift h γ] (hδσ : δ ≫ σ = γ ≫ β)
    (hb : μ₂ ≫ h = specOverMap rV ≫ μ)
    (hX : ξ a ι (rV.hom.hom.comp ((qC hC I hI).hom.hom.comp u)) =
      ξ a ι ((qC₁ hC I hI).hom.hom.comp (V.hom.hom.comp u))) :
    e ≫ γ = eqToHom hX.symm ≫ StackChart.trans a ι rV ((qC hC I hI).hom.hom.comp u) ≫ c₁ := by
  have : 𝒳.val.p.IsHomLift (μ₂ ≫ h)
      (eqToHom hX.symm ≫ StackChart.trans a ι rV ((qC hC I hI).hom.hom.comp u) ≫ c₁) :=
    isHomLift_of_eq hb.symm inferInstance
  refine Functor.IsStronglyCartesian.ext 𝒳.val.p l β (μ₂ ≫ h) ?_
  calc (e ≫ γ) ≫ β = (e ≫ δ) ≫ σ := by rw [Category.assoc, ← hδσ, Category.assoc]
    _ = StackChart.trans a ι (qC₁ hC I hI) (V.hom.hom.comp u) ≫
        StackChart.trans a ι V u ≫ t := by rw [he, Category.assoc, hs]
    _ = eqToHom hX.symm ≫ (StackChart.trans a ι rV ((qC hC I hI).hom.hom.comp u) ≫
        StackChart.trans a ι (qC hC I hI) u) ≫ t := by
        rw [trans_square (a := a) (ι := ι) (qC hC I hI) rV V (qC₁ hC I hI) hsq u hX]
        simp
    _ = (eqToHom hX.symm ≫ StackChart.trans a ι rV ((qC hC I hI).hom.hom.comp u) ≫ c₁) ≫ β := by
        simp only [Category.assoc, hc₁β]

/-- **The reduction of a descent datum over a cover is the descent arrow of the reduced
object.** The arrow `hom` over the double overlap of the chart cover, defined by
`hom ≫ s₁ = s₀` from the identifications `s₀`, `s₁` with the given object `w` over `c''`,
reduces to the descent arrow of `x̄` relative to `cm`, as soon as the reduction of `w` is
identified with the restriction `y₂` of `x` compatibly (`δ`, `γ₁`, `γ₂`). -/
theorem map_descArr_eq_chartRbar_of_cover {T c c' c'' c₂ : BigFppfOver B S hS}
    (u : P.obj →ₐ[ringOf B S hS T'] (descNerve T' hC 0).obj)
    (hom : ξ a ι ((descV₀ T' hC).hom.hom.comp u) ⟶ ξ a ι ((descVₗ T' hC).hom.hom.comp u))
    [𝒳.val.p.IsHomLift (𝟙 (specOver (descNerve T' hC 1))) hom]
    (φT : specOver (red I (baseAlg (κ := B.cutoff) hA)) ⟶ T) {x xb y y' y₂ w : 𝒳.val.obj}
    (c₀ : xb ⟶ x) [𝒳.val.p.IsStronglyCartesian φT c₀] (α : y ⟶ x)
    (cm : ξ a ι ((qC hC I hI).hom.hom.comp u) ⟶ xb)
    [𝒳.val.p.IsHomLift (specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot) cm]
    (μ : specOver (red I (descNerve T' hC 0)) ⟶ c)
    (c₁ : ξ a ι ((qC hC I hI).hom.hom.comp u) ⟶ y) [𝒳.val.p.IsHomLift μ c₁]
    (hcm : cm ≫ c₀ = c₁ ≫ α) (l : c ⟶ c') (β : y ⟶ y') [𝒳.val.p.IsStronglyCartesian l β]
    (t : ξ a ι u ⟶ y') (hc₁β : c₁ ≫ β = StackChart.trans a ι (qC hC I hI) u ≫ t)
    (κ : specOver (descNerve T' hC 1) ⟶ c'') (σ τ : w ⟶ y')
    (s₀ : ξ a ι ((descV₀ T' hC).hom.hom.comp u) ⟶ w)
    (s₁ : ξ a ι ((descVₗ T' hC).hom.hom.comp u) ⟶ w) [𝒳.val.p.IsHomLift κ s₀]
    [𝒳.val.p.IsHomLift κ s₁]
    (hs₀ : s₀ ≫ σ = StackChart.trans a ι (descV₀ T' hC) u ≫ t)
    (hs₁ : s₁ ≫ τ = StackChart.trans a ι (descVₗ T' hC) u ≫ t) (hhom : hom ≫ s₁ = s₀)
    (l₂ : c₂ ⟶ c'') (δ : y₂ ⟶ w) [𝒳.val.p.IsStronglyCartesian l₂ δ] (h₁ h₂ : c₂ ⟶ c)
    (γ₁ γ₂ : y₂ ⟶ y) [𝒳.val.p.IsHomLift h₁ γ₁] [𝒳.val.p.IsHomLift h₂ γ₂]
    (hδσ : δ ≫ σ = γ₁ ≫ β) (hδτ : δ ≫ τ = γ₂ ≫ β) (hγ : γ₁ ≫ α = γ₂ ≫ α)
    (μ₂ : specOver (red I (descNerve T' hC 1)) ⟶ c₂)
    (hμ₂l : μ₂ ≫ l₂ = specOverMap (qC₁ hC I hI) ≫ κ)
    (hb₀ : μ₂ ≫ h₁ = specOverMap (rV₀ hC I) ≫ μ) (hb₁ : μ₂ ≫ h₂ = specOverMap (rVₗ hC I) ≫ μ) :
    Arr.map a ι (qC₁ hC I hI) (descArr u hom) = chartRbar (hA := hA) hC I _ cm := by
  let q₁ := qC₁ hC I hI
  let e₀ : ξ a ι (q₁.hom.hom.comp ((descV₀ T' hC).hom.hom.comp u)) ⟶ y₂ :=
    Functor.IsStronglyCartesian.map 𝒳.val.p l₂ δ hμ₂l.symm
      (StackChart.trans a ι q₁ ((descV₀ T' hC).hom.hom.comp u) ≫ s₀)
  have he₀ : e₀ ≫ δ = StackChart.trans a ι q₁ ((descV₀ T' hC).hom.hom.comp u) ≫ s₀ :=
    Functor.IsStronglyCartesian.fac _ _ _ _ _
  let e₁ : ξ a ι (q₁.hom.hom.comp ((descVₗ T' hC).hom.hom.comp u)) ⟶ y₂ :=
    Functor.IsStronglyCartesian.map 𝒳.val.p l₂ δ hμ₂l.symm
      (StackChart.trans a ι q₁ ((descVₗ T' hC).hom.hom.comp u) ≫ s₁)
  have he₁ : e₁ ≫ δ = StackChart.trans a ι q₁ ((descVₗ T' hC).hom.hom.comp u) ≫ s₁ :=
    Functor.IsStronglyCartesian.fac _ _ _ _ _
  have he₀l : 𝒳.val.p.IsHomLift μ₂ e₀ := Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ _
  have he₁l : 𝒳.val.p.IsHomLift μ₂ e₁ := Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ _
  let R := Arr.map a ι q₁ (descArr u hom)
  let Rh : ξ a ι (q₁.hom.hom.comp ((descV₀ T' hC).hom.hom.comp u)) ⟶
      ξ a ι (q₁.hom.hom.comp ((descVₗ T' hC).hom.hom.comp u)) := R.hom
  have hRl : 𝒳.val.p.IsHomLift (𝟙 (specOver (red I (descNerve T' hC 1)))) Rh := R.lift
  have hA₁ : Rh ≫ e₁ = e₀ := by
    refine Functor.IsStronglyCartesian.ext 𝒳.val.p l₂ δ μ₂ ?_
    calc (Rh ≫ e₁) ≫ δ = Rh ≫ (StackChart.trans a ι q₁ ((descVₗ T' hC).hom.hom.comp u) ≫ s₁) := by
          rw [Category.assoc, he₁]
      _ = (StackChart.trans a ι q₁ ((descV₀ T' hC).hom.hom.comp u) ≫ hom) ≫ s₁ := by
          rw [← Category.assoc]
          exact congrArg (· ≫ s₁) (Arr.map_hom_fac q₁ (descArr u hom))
      _ = e₀ ≫ δ := by rw [Category.assoc, hhom, he₀]
  have hX₀ : ξ a ι ((rV₀ hC I).hom.hom.comp ((qC hC I hI).hom.hom.comp u)) =
      ξ a ι (q₁.hom.hom.comp ((descV₀ T' hC).hom.hom.comp u)) :=
    congrArg (ξ a ι) (congrArg (fun m : descNerve T' hC 0 ⟶ red I (descNerve T' hC 1) ↦
      m.hom.hom.comp u) (qC_rV₀ hC I hI))
  have hX₁ : ξ a ι ((rVₗ hC I).hom.hom.comp ((qC hC I hI).hom.hom.comp u)) =
      ξ a ι (q₁.hom.hom.comp ((descVₗ T' hC).hom.hom.comp u)) :=
    congrArg (ξ a ι) (congrArg (fun m : descNerve T' hC 0 ⟶ red I (descNerve T' hC 1) ↦
      m.hom.hom.comp u) (qC_rVₗ hC I hI))
  have hB₀ := trans_fac_of_cover u (descV₀ T' hC) (rV₀ hC I) (qC_rV₀ hC I hI) l β t μ c₁ hc₁β
    σ s₀ hs₀ δ μ₂ e₀ he₀ h₁ γ₁ hδσ hb₀ hX₀
  have hB₁ := trans_fac_of_cover u (descVₗ T' hC) (rVₗ hC I) (qC_rVₗ hC I hI) l β t μ c₁ hc₁β
    τ s₁ hs₁ δ μ₂ e₁ he₁ h₂ γ₂ hδτ hb₁ hX₁
  have hs : R.src = (rV₀ hC I).hom.hom.comp ((qC hC I hI).hom.hom.comp u) :=
    (congrArg (fun m : descNerve T' hC 0 ⟶ red I (descNerve T' hC 1) ↦
      m.hom.hom.comp u) (qC_rV₀ hC I hI)).symm
  have ht' : R.tgt = (rVₗ hC I).hom.hom.comp ((qC hC I hI).hom.hom.comp u) :=
    (congrArg (fun m : descNerve T' hC 0 ⟶ red I (descNerve T' hC 1) ↦
      m.hom.hom.comp u) (qC_rVₗ hC I hI)).symm
  unfold chartRbar
  refine eq_canArr _ _ _ _ _ _ hs ht' ?_
  show eqToHom hX₀ ≫ Rh ≫ eqToHom hX₁.symm ≫
    StackChart.trans a ι (rVₗ hC I) ((qC hC I hI).hom.hom.comp u) ≫ cm =
      StackChart.trans a ι (rV₀ hC I) ((qC hC I hI).hom.hom.comp u) ≫ cm
  have : 𝒳.val.p.IsHomLift (specOverMap (rV₀ hC I) ≫
      specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot)
      (eqToHom hX₀ ≫ Rh ≫ eqToHom hX₁.symm ≫
        StackChart.trans a ι (rVₗ hC I) ((qC hC I hI).hom.hom.comp u) ≫ cm) :=
    isHomLift_of_eq (spec_rV_base hA hC I hI) inferInstance
  refine Functor.IsStronglyCartesian.ext 𝒳.val.p φT c₀ (specOverMap (rV₀ hC I) ≫
    specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot) ?_
  calc (eqToHom hX₀ ≫ Rh ≫ eqToHom hX₁.symm ≫
        StackChart.trans a ι (rVₗ hC I) ((qC hC I hI).hom.hom.comp u) ≫ cm) ≫ c₀
      = eqToHom hX₀ ≫ Rh ≫ (eqToHom hX₁.symm ≫
        StackChart.trans a ι (rVₗ hC I) ((qC hC I hI).hom.hom.comp u) ≫ c₁) ≫ α := by
        simp only [Category.assoc, hcm]
    _ = eqToHom hX₀ ≫ (Rh ≫ e₁) ≫ γ₂ ≫ α := by rw [← hB₁]; simp only [Category.assoc]
    _ = eqToHom hX₀ ≫ (e₀ ≫ γ₁) ≫ α := by rw [hA₁]; simp only [Category.assoc, hγ]
    _ = (StackChart.trans a ι (rV₀ hC I) ((qC hC I hI).hom.hom.comp u) ≫ cm) ≫ c₀ := by
        rw [hB₀]; simp [hcm]

end Aux

/-- **The lift produced over the chart cover restricts to the given lift.** The tail of
`AlgebraicGeometry.Stack.GroupoidLift.exists_lift_of_cover`: a lift `φe : x̄ ⟶ x'` over
`Spec A'` whose pullback to the chart cover is the chart lift `ξ u ⟶ y'` is transported to a
lift `x ⟶ z` over `T'`, and its pullback to `c'` is identified with `y'` by
`AlgebraicGeometry.Stack.GroupoidLift.exists_hom_of_cover` over the base `c'`. -/
theorem exists_lift_of_chartLift_of_cover (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (harr : ArrowSpacesLocallyOfFinitePresentation B S hS 𝒳)
    {T c c' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj c)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj c')]
    (i : T ⟶ T') (hI : kerIdeal i ^ 2 = ⊥)
    (j : c ⟶ T) (l : c ⟶ c') (k : c' ⟶ T') (hpb : IsPullback j l i k)
    (hl : Deformation.Artin.IsDeformationSituation
      ((BigFppfOver.toScheme B S hS).map l).appTop.hom)
    (hA : Cardinal.mk (ringOf B S hS T') < B.cutoff) {C' : Type u} [CommRing C']
    [Algebra (ringOf B S hS T') C'] {hC : Cardinal.mk C' < B.cutoff}
    (φT : specOver (red (kerIdeal i) (baseAlg (κ := B.cutoff) hA)) ⟶ T) [IsIso φT]
    (hφT : φT ≫ i = specOverToBase (red (kerIdeal i) (baseAlg (κ := B.cutoff) hA)))
    {U₀ : BigFppfOver B S hS} {a : schemeFibredCategory B S hS U₀ ⟶ 𝒳}
    {P : SmallAlg (ringOf B S hS T') B.cutoff} {ι : specOver P ⟶ U₀}
    (u : P.obj →ₐ[ringOf B S hS T'] (descNerve T' hC 0).obj)
    (ν : specOver (descNerve T' hC 0) ⟶ c')
    (hνf : Flat ((BigFppfOver.toScheme B S hS).map ν))
    (hνs : Surjective ((BigFppfOver.toScheme B S hS).map ν))
    (hνp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map ν))
    (hbm : ν ≫ k = specOverMap (baseMap B.aleph0_lt_cutoff hC hA) ≫
      specOverToBase (T' := T') (baseAlg (κ := B.cutoff) hA))
    (μ : specOver (red (kerIdeal i) (descNerve T' hC 0)) ⟶ c)
    (hμj : μ ≫ j = specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot ≫ φT)
    (hμl : μ ≫ l = specOverMap (qC hC (kerIdeal i) hI) ≫ ν)
    {x xb y y' x' : 𝒳.val.obj} (c₀ : xb ⟶ x) [𝒳.val.p.IsHomLift φT c₀] (α : y ⟶ x)
    [𝒳.val.p.IsHomLift j α] (β : y ⟶ y') [hβ : 𝒳.val.p.IsHomLift l β] (t : ξ a ι u ⟶ y')
    [ht : 𝒳.val.p.IsHomLift ν t] (c₁ : ξ a ι ((qC hC (kerIdeal i) hI).hom.hom.comp u) ⟶ y)
    [hc₁l : 𝒳.val.p.IsHomLift μ c₁]
    (hc₁β : c₁ ≫ β = StackChart.trans a ι (qC hC (kerIdeal i) hI) u ≫ t)
    (cm : ξ a ι ((qC hC (kerIdeal i) hI).hom.hom.comp u) ⟶ xb) (hcm : cm ≫ c₀ = c₁ ≫ α)
    (ζ : ξ a ι u ⟶ x') [𝒳.val.p.IsHomLift (specOverMap (baseMap B.aleph0_lt_cutoff hC hA)) ζ]
    (φe : xb ⟶ x')
    [𝒳.val.p.IsHomLift (specOverMap (thk (kerIdeal i) hI (baseAlg (κ := B.cutoff) hA)).q) φe]
    (hcφ : cm ≫ φe = StackChart.trans a ι (qC hC (kerIdeal i) hI) u ≫ ζ) :
    ∃ (z : 𝒳.val.obj) (_ : 𝒳.val.p.obj z = T') (φ : x ⟶ z) (ρ : y' ⟶ z),
      𝒳.val.p.IsHomLift i φ ∧ 𝒳.val.p.IsHomLift k ρ ∧ β ≫ ρ = α ≫ φ := by
  have hp := 𝒳.isFiberedInGroupoids
  have := isIso_specOverToBase_baseAlg (T' := T') hA
  let toB := specOverToBase (T' := T') (baseAlg (κ := B.cutoff) hA)
  have hq : φT ≫ i = specOverMap (thk (kerIdeal i) hI (baseAlg (κ := B.cutoff) hA)).q ≫ toB := by
    rw [hφT, specOverMap_comp_toBase]
  have hx' : 𝒳.val.p.obj x' = specOver (baseAlg (κ := B.cutoff) hA) :=
    IsHomLift.codomain_eq 𝒳.val.p (specOverMap (baseMap B.aleph0_lt_cutoff hC hA)) ζ
  have hy : 𝒳.val.p.obj y = c := IsHomLift.domain_eq 𝒳.val.p j α
  let z := Functor.IsPreFibered.pullbackObj hx' (inv toB)
  have hz : 𝒳.val.p.obj z = T' := Functor.IsPreFibered.pullbackObj_proj hx' (inv toB)
  let d : z ⟶ x' := Functor.IsPreFibered.pullbackMap hx' (inv toB)
  have : 𝒳.val.p.IsStronglyCartesian (inv toB) d := hp.isStronglyCartesian_homLift (inv toB) d
  have : 𝒳.val.p.IsStronglyCartesian φT c₀ := hp.isStronglyCartesian_homLift φT c₀
  have : IsIso c₀ := Functor.IsStronglyCartesian.isIso_of_base_isIso 𝒳.val.p φT c₀
  have : IsIso d := Functor.IsStronglyCartesian.isIso_of_base_isIso 𝒳.val.p (inv toB) d
  have := IsHomLift.inv 𝒳.val.p φT c₀
  have := IsHomLift.inv 𝒳.val.p (inv toB) d
  let φ : x ⟶ z := inv c₀ ≫ φe ≫ inv d
  have hφ : 𝒳.val.p.IsHomLift i φ := isHomLift_of_eq (by
    rw [IsIso.inv_inv, ← hq, IsIso.inv_hom_id_assoc])
    (inferInstance : 𝒳.val.p.IsHomLift (inv φT ≫
      specOverMap (thk (kerIdeal i) hI (baseAlg (κ := B.cutoff) hA)).q ≫ inv (inv toB)) φ)
  have hζz : 𝒳.val.p.IsHomLift (ν ≫ k) (ζ ≫ inv d) := isHomLift_of_eq (by
    rw [IsIso.inv_inv, hbm]) (inferInstance : 𝒳.val.p.IsHomLift
      (specOverMap (baseMap B.aleph0_lt_cutoff hC hA) ≫ inv (inv toB)) (ζ ≫ inv d))
  let zc := Functor.IsPreFibered.pullbackObj hz k
  let dz : zc ⟶ z := Functor.IsPreFibered.pullbackMap hz k
  have : 𝒳.val.p.IsStronglyCartesian k dz := hp.isStronglyCartesian_homLift k dz
  let β₂ : y ⟶ zc := Functor.IsStronglyCartesian.map 𝒳.val.p k dz hpb.w (α ≫ φ)
  have hβ₂ : β₂ ≫ dz = α ≫ φ := Functor.IsStronglyCartesian.fac _ _ _ _ _
  let ζc : ξ a ι u ⟶ zc := Functor.IsStronglyCartesian.map 𝒳.val.p k dz (g := ν) rfl (ζ ≫ inv d)
  have hζc : ζc ≫ dz = ζ ≫ inv d := Functor.IsStronglyCartesian.fac _ _ _ _ _
  have hred : IsPullback (specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot ≫ φT)
      (specOverMap (qC hC (kerIdeal i) hI)) i (ν ≫ k) := by
    have h0 := isPullback_specOverMap_of_isPushout (baseMap B.aleph0_lt_cutoff hC hA)
      (thk (kerIdeal i) hI (baseAlg (κ := B.cutoff) hA)).q (qC hC (kerIdeal i) hI)
      (baseThk B.aleph0_lt_cutoff hC hI hA).bot
      (isPushout_red B.aleph0_lt_cutoff C' hC (kerIdeal i) hI hA)
    refine (IsPullback.of_iso h0 (Iso.refl _) (Iso.refl _) (asIso φT) (asIso toB) ?_ ?_ ?_ ?_).flip
    · simp
    · simp
    · simp [hbm, toB]
    · simp [hq, toB]
  have hred' : IsPullback μ (specOverMap (qC hC (kerIdeal i) hI)) l ν :=
    IsPullback.of_right (hμj ▸ hred) hμl hpb
  have hβ₂l : 𝒳.val.p.IsHomLift l β₂ := Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ _
  have hζcl : 𝒳.val.p.IsHomLift ν ζc := Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ _
  have hw₂ : StackChart.trans a ι (qC hC (kerIdeal i) hI) u ≫ ζc = c₁ ≫ β₂ := by
    have : 𝒳.val.p.IsHomLift (μ ≫ l) (StackChart.trans a ι (qC hC (kerIdeal i) hI) u ≫ ζc) :=
      isHomLift_of_eq hμl.symm inferInstance
    refine Functor.IsStronglyCartesian.ext 𝒳.val.p k dz (μ ≫ l) ?_
    rw [Category.assoc, hζc, Category.assoc, hβ₂, ← Category.assoc c₁, ← hcm, Category.assoc,
      IsIso.hom_inv_id_assoc]
    simp only [← Category.assoc, hcφ]
  obtain ⟨θ, hθ, hβθ⟩ := exists_hom_of_cover_of_arrSpace (T' := c') h𝒳 harr l hl μ
    (specOverMap (qC hC (kerIdeal i) hI)) ν hred' hνf hνs hνp hy c₁ hc₁l
    (StackChart.trans a ι (qC hC (kerIdeal i) hI) u) inferInstance β hβ β₂ hβ₂l t ht ζc hζcl
    hc₁β.symm hw₂
  refine ⟨z, hz, φ, θ ≫ dz, hφ, isHomLift_of_eq (Category.id_comp k) inferInstance, ?_⟩
  rw [← Category.assoc, hβθ, hβ₂]

/-- **A lift over an fppf cover with descent data descends, compatibly.** In the situation of
`AlgebraicGeometry.Stack.GroupoidLift.exists_hom_of_cover`, let `c'' = c' ×_{T'} c'` (by `k₁`,
`k₂`) with reduction `c₂ = T ×_{T'} c''` (by `j₂`, `l₂`) and its two maps `h₁`, `h₂` to `c`. Let
`β : y ⟶ y'` be a lift of `y = x|_c` along `l` whose two pullbacks to `c''` are identified as
lifts of `y₂ = x|_{c₂}`: an object `w` over `c''` with `σ : w ⟶ y'` over `k₁`, `τ : w ⟶ y'` over
`k₂` and `δ : y₂ ⟶ w` over `l₂` with `δ ≫ σ = γ₁ ≫ β`, `δ ≫ τ = γ₂ ≫ β`, where
`γ₁ ≫ α = γ₂ ≫ α`. Then `x` has a lift `φ : x ⟶ z` along `i` whose pullback to `c'` is the lift
`β`: there is `ρ : y' ⟶ z` over `k` with `β ≫ ρ = α ≫ φ`.

The finiteness used is that of the space of arrows of a chart whose two objects over
`Spec (P ⊗ P)` are isomorphic (`harr`). -/
theorem exists_lift_of_cover_of_arrSpace (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (harr : ArrowSpacesLocallyOfFinitePresentation B S hS 𝒳)
    {T c c' c'' c₂ : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj c)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj c')]
    (i : T ⟶ T') (hi : Deformation.Artin.IsDeformationSituation
      ((BigFppfOver.toScheme B S hS).map i).appTop.hom)
    (j : c ⟶ T) (l : c ⟶ c') (k : c' ⟶ T') (hpb : IsPullback j l i k)
    (hl : Deformation.Artin.IsDeformationSituation
      ((BigFppfOver.toScheme B S hS).map l).appTop.hom)
    (hkf : Flat ((BigFppfOver.toScheme B S hS).map k))
    (hks : Surjective ((BigFppfOver.toScheme B S hS).map k))
    (hkp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map k))
    (k₁ k₂ : c'' ⟶ c') (hpb₂ : IsPullback k₁ k₂ k k) (j₂ : c₂ ⟶ T) (l₂ : c₂ ⟶ c'')
    (hpb₃ : IsPullback j₂ l₂ i (k₁ ≫ k)) (h₁ h₂ : c₂ ⟶ c) (hh₁ : h₁ ≫ l = l₂ ≫ k₁)
    (hh₂ : h₂ ≫ l = l₂ ≫ k₂) (hh₁j : h₁ ≫ j = j₂) (hh₂j : h₂ ≫ j = j₂)
    {x y y' y₂ w : 𝒳.val.obj} (hx : 𝒳.val.p.obj x = T) (α : y ⟶ x)
    (hα : 𝒳.val.p.IsHomLift j α) (β : y ⟶ y') (hβ : 𝒳.val.p.IsHomLift l β)
    (γ₁ γ₂ : y₂ ⟶ y) (hγ₁ : 𝒳.val.p.IsHomLift h₁ γ₁) (hγ₂ : 𝒳.val.p.IsHomLift h₂ γ₂)
    (hγ : γ₁ ≫ α = γ₂ ≫ α) (σ τ : w ⟶ y') (hσ : 𝒳.val.p.IsHomLift k₁ σ)
    (hτ : 𝒳.val.p.IsHomLift k₂ τ) (δ : y₂ ⟶ w) (hδ : 𝒳.val.p.IsHomLift l₂ δ)
    (hδσ : δ ≫ σ = γ₁ ≫ β) (hδτ : δ ≫ τ = γ₂ ≫ β) :
    ∃ (z : 𝒳.val.obj) (_ : 𝒳.val.p.obj z = T') (φ : x ⟶ z) (ρ : y' ⟶ z),
      𝒳.val.p.IsHomLift i φ ∧ 𝒳.val.p.IsHomLift k ρ ∧ β ≫ ρ = α ≫ φ := by
  classical
  obtain ⟨_, ⟨_, hst⟩, _⟩ := id h𝒳
  set A' := ringOf B S hS T'
  have hA : Cardinal.mk A' < B.cutoff := card_sections_lt T'
  have hsurjI : Function.Surjective (algebraMap A' (sectionsAlg T i).obj) := hi.1
  have hI : kerIdeal i ^ 2 = ⊥ := hi.2
  have hp := 𝒳.isFiberedInGroupoids
  have hy' : 𝒳.val.p.obj y' = c' := @IsHomLift.codomain_eq _ _ _ _ 𝒳.val.p _ _ _ _ l β hβ
  -- the lift `y'` as a chart
  let E := Functor.twoYonedaEvaluation 𝒳.val.p c'
  let : E.IsEquivalence := Functor.twoYonedaEvaluation_isEquivalence 𝒳.val.p 𝒳.property c'
  let aB := E.objPreimage ⟨y', hy'⟩
  let e := E.objObjPreimageIso ⟨y', hy'⟩
  let a : schemeFibredCategory B S hS c' ⟶ 𝒳 := Bicategory.InducedBicategory.mkHom aB
  let ε₀ : aB.obj (Over.mk (𝟙 c')) ⟶ y' := e.hom.1
  have hε₀ : 𝒳.val.p.IsHomLift (𝟙 c') ε₀ := e.hom.2
  let P := sectionsAlg c' k
  let ι : specOver P ⟶ c' := sectionsHom c' k
  have : Algebra.FinitePresentation A' P.obj := finitePresentation_of_chart k
  -- the two objects of the chart over `Spec (P ⊗ P)` are isomorphic, through `w`
  have hθ : Nonempty (pairObj₁ a ι ≅ pairObj₀ a ι) := by
    let m₀ : specOver (pairAlg P) ⟶ c' := specOverMap (SmallAlg.homMk (vtx₀ P)) ≫ ι
    let m₁ : specOver (pairAlg P) ⟶ c' := specOverMap (SmallAlg.homMk (vtx₁ P)) ≫ ι
    have hk : m₀ ≫ k = m₁ ≫ k := (specOverMap_comp_sectionsHom_comp k _).trans
      (specOverMap_comp_sectionsHom_comp k _).symm
    let n := hpb₂.lift m₀ m₁ hk
    have hw : 𝒳.val.p.obj w = c'' := IsHomLift.domain_eq 𝒳.val.p k₁ σ
    let d := Functor.IsPreFibered.pullbackMap hw n
    have hs₀ : 𝒳.val.p.IsHomLift m₀ (d ≫ σ) :=
      isHomLift_of_eq (hpb₂.lift_fst m₀ m₁ hk) (inferInstance : 𝒳.val.p.IsHomLift (n ≫ k₁) (d ≫ σ))
    have hs₁ : 𝒳.val.p.IsHomLift m₁ (d ≫ τ) :=
      isHomLift_of_eq (hpb₂.lift_snd m₀ m₁ hk) (inferInstance : 𝒳.val.p.IsHomLift (n ≫ k₂) (d ≫ τ))
    exact nonempty_pairObj_iso a ι ε₀ hε₀ (d ≫ σ) (d ≫ τ) hs₀ hs₁
  obtain ⟨C₁, f₁, hf₁s, hf₁e, Q, _, _, b, hb, sV, tV, hsV, htV, ε, hε⟩ :=
    exists_arrowChart_finitePresentation_of_isLocallyOfFinitePresentation a ι h𝒳
      (harr.isLocallyOfFinitePresentation a ι hθ)
      (AlgHom.id A' P.obj)
  have hC : Cardinal.mk C₁.obj < B.cutoff := C₁.2
  obtain ⟨hFF, hFP⟩ := faithfullyFlat_finitePresentation_of_chart k f₁
  let q := (thk (kerIdeal i) hI (descNerve T' hC 0)).q
  let u : P.obj →ₐ[A'] (descNerve T' hC 0).obj := f₁.hom.hom.comp (AlgHom.id A' P.obj)
  have hu : SmallAlg.homMk u = f₁ :=
    ObjectProperty.hom_ext _ (CommAlgCat.hom_ext (AlgHom.ext fun _ ↦ rfl))
  let εbar := q.hom.hom.comp ε
  have hε' : b.app _ εbar = Arr.idt (q.hom.hom.comp u) :=
    (b.natural q ε).symm.trans ((congrArg _ hε).trans (Arr.map_idt _ _))
  let φT := redToBase i hsurjI hA
  let xb := Functor.IsPreFibered.pullbackObj hx φT
  have hxb : 𝒳.val.p.obj xb = specOver (red (kerIdeal i) (baseAlg (κ := B.cutoff) hA)) :=
    Functor.IsPreFibered.pullbackObj_proj hx φT
  let c₀ : xb ⟶ x := Functor.IsPreFibered.pullbackMap hx φT
  have : 𝒳.val.p.IsStronglyCartesian φT c₀ := hp.isStronglyCartesian_homLift φT c₀
  let ν : specOver (descNerve T' hC 0) ⟶ c' := specOverMap (SmallAlg.homMk u) ≫ ι
  let t : ξ a ι u ⟶ y' := aB.map (Over.mkIdTerminal.from (pt ι u)) ≫ ε₀
  have ht : 𝒳.val.p.IsHomLift ν t := isHomLift_map_comp_of_isHomLift_id aB ε₀ (pt ι u)
  have hνk : ν ≫ k = specOverToBase (descNerve T' hC 0) :=
    specOverMap_comp_sectionsHom_comp k _
  have hkey : (specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot ≫ φT) ≫ i =
      (specOverMap q ≫ ν) ≫ k := by
    rw [Category.assoc, Category.assoc, redToBase_comp, hνk, specOverMap_comp_toBase,
      specOverMap_comp_toBase]
  let μ := hpb.lift _ _ hkey
  have hμj : μ ≫ j = specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot ≫ φT :=
    hpb.lift_fst _ _ _
  have hμl : μ ≫ l = specOverMap q ≫ ν := hpb.lift_snd _ _ _
  have : 𝒳.val.p.IsStronglyCartesian l β := hp.isStronglyCartesian_homLift l β
  let c₁ : ξ a ι (q.hom.hom.comp u) ⟶ y :=
    Functor.IsStronglyCartesian.map 𝒳.val.p l β hμl.symm (StackChart.trans a ι q u ≫ t)
  have hc₁β : c₁ ≫ β = StackChart.trans a ι q u ≫ t := Functor.IsStronglyCartesian.fac _ _ _ _ _
  have hc₁l : 𝒳.val.p.IsHomLift μ c₁ := Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ _
  let cm : ξ a ι (q.hom.hom.comp u) ⟶ xb :=
    Functor.IsStronglyCartesian.map 𝒳.val.p φT c₀ hμj (c₁ ≫ α)
  have hcm : cm ≫ c₀ = c₁ ≫ α := Functor.IsStronglyCartesian.fac _ _ _ _ _
  have hc : 𝒳.val.p.IsHomLift (specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot) cm :=
    Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ _
  have := isIso_specOverToBase_baseAlg (T' := T') hA
  let toB := specOverToBase (T' := T') (baseAlg (κ := B.cutoff) hA)
  have hq : φT ≫ i = specOverMap (thk (kerIdeal i) hI (baseAlg (κ := B.cutoff) hA)).q ≫ toB := by
    rw [redToBase_comp, specOverMap_comp_toBase]
  have hbm : ν ≫ k = specOverMap (baseMap B.aleph0_lt_cutoff hC hA) ≫ toB :=
    hνk.trans (specOverMap_comp_toBase _).symm
  -- the descent datum over the double overlap of `C₁`
  have hκk : (specOverMap (descV₀ T' hC) ≫ ν) ≫ k = (specOverMap (descVₗ T' hC) ≫ ν) ≫ k := by
    simp only [Category.assoc]
    rw [hbm, ← Category.assoc, ← Category.assoc (specOverMap (descVₗ T' hC)),
      spec_descV_base hA]
  let κ := hpb₂.lift _ _ hκk
  have hκ₁ : κ ≫ k₁ = specOverMap (descV₀ T' hC) ≫ ν := hpb₂.lift_fst _ _ _
  have hκ₂ : κ ≫ k₂ = specOverMap (descVₗ T' hC) ≫ ν := hpb₂.lift_snd _ _ _
  have : 𝒳.val.p.IsStronglyCartesian k₁ σ := hp.isStronglyCartesian_homLift k₁ σ
  have : 𝒳.val.p.IsStronglyCartesian k₂ τ := hp.isStronglyCartesian_homLift k₂ τ
  let s₀ : ξ a ι ((descV₀ T' hC).hom.hom.comp u) ⟶ w :=
    Functor.IsStronglyCartesian.map 𝒳.val.p k₁ σ hκ₁.symm
      (StackChart.trans a ι (descV₀ T' hC) u ≫ t)
  have hs₀ : s₀ ≫ σ = StackChart.trans a ι (descV₀ T' hC) u ≫ t :=
    Functor.IsStronglyCartesian.fac _ _ _ _ _
  let s₁ : ξ a ι ((descVₗ T' hC).hom.hom.comp u) ⟶ w :=
    Functor.IsStronglyCartesian.map 𝒳.val.p k₂ τ hκ₂.symm
      (StackChart.trans a ι (descVₗ T' hC) u ≫ t)
  have hs₁ : s₁ ≫ τ = StackChart.trans a ι (descVₗ T' hC) u ≫ t :=
    Functor.IsStronglyCartesian.fac _ _ _ _ _
  have hs₀l : 𝒳.val.p.IsHomLift κ s₀ := Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ _
  have hs₁l : 𝒳.val.p.IsHomLift κ s₁ := Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ _
  have : 𝒳.val.p.IsStronglyCartesian κ s₁ := hp.isStronglyCartesian_homLift κ s₁
  let hom : ξ a ι ((descV₀ T' hC).hom.hom.comp u) ⟶ ξ a ι ((descVₗ T' hC).hom.hom.comp u) :=
    Functor.IsStronglyCartesian.map 𝒳.val.p κ s₁ (Category.id_comp κ).symm s₀
  have hhom : hom ≫ s₁ = s₀ := Functor.IsStronglyCartesian.fac _ _ _ _ _
  have hl' : 𝒳.val.p.IsHomLift (𝟙 (specOver (descNerve T' hC 1))) hom :=
    Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ _
  -- the reduction of the descent datum is the descent arrow of `x̄`
  let q₁ := qC₁ hC (kerIdeal i) hI
  have hμ₂ : (specOverMap (rV₀ hC (kerIdeal i)) ≫
      specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot ≫ φT) ≫ i =
      (specOverMap q₁ ≫ κ) ≫ k₁ ≫ k := by
    have e1 : (specOverMap (rV₀ hC (kerIdeal i)) ≫
        specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot ≫ φT) ≫ i =
        specOverToBase (red (kerIdeal i) (descNerve T' hC 1)) := by
      simp only [φT, Category.assoc, redToBase_comp, specOverMap_comp_toBase]
    have e2 : (specOverMap q₁ ≫ κ) ≫ k₁ ≫ k =
        specOverToBase (red (kerIdeal i) (descNerve T' hC 1)) := by
      rw [← Category.assoc, Category.assoc (specOverMap q₁), hκ₁]
      simp only [Category.assoc]
      rw [hbm]
      exact (congrArg (fun m ↦ specOverMap q₁ ≫ specOverMap (descV₀ T' hC) ≫ m)
        (specOverMap_comp_toBase (baseMap B.aleph0_lt_cutoff hC hA))).trans
          ((congrArg (specOverMap q₁ ≫ ·) (specOverMap_comp_toBase _)).trans
            (specOverMap_comp_toBase _))
    exact e1.trans e2.symm
  let μ₂ := hpb₃.lift _ _ hμ₂
  have hμ₂j : μ₂ ≫ j₂ = specOverMap (rV₀ hC (kerIdeal i)) ≫
      specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot ≫ φT := hpb₃.lift_fst _ _ _
  have hμ₂l : μ₂ ≫ l₂ = specOverMap q₁ ≫ κ := hpb₃.lift_snd _ _ _
  have hbase : ∀ (hn : c₂ ⟶ c) (_ : hn ≫ j = j₂) (kn : c'' ⟶ c') (_ : hn ≫ l = l₂ ≫ kn)
      (Vn : descNerve T' hC 0 ⟶ descNerve T' hC 1) (_ : κ ≫ kn = specOverMap Vn ≫ ν)
      (rVn : red (kerIdeal i) (descNerve T' hC 0) ⟶ red (kerIdeal i) (descNerve T' hC 1))
      (_ : q ≫ rVn = Vn ≫ q₁),
      μ₂ ≫ hn = specOverMap rVn ≫ μ := by
    intro hn hnj kn hnl Vn hκn rVn hsq
    refine hpb.hom_ext ?_ ?_
    · rw [Category.assoc, hnj, hμ₂j, Category.assoc, hμj, ← Category.assoc,
        ← Category.assoc, ← specOverMap_comp, ← specOverMap_comp,
        spec_red_base_eq (hA := hA) (kerIdeal i) ((baseThk B.aleph0_lt_cutoff hC hI hA).bot ≫ _)
          ((baseThk B.aleph0_lt_cutoff hC hI hA).bot ≫ rVn)]
    · calc (μ₂ ≫ hn) ≫ l = μ₂ ≫ l₂ ≫ kn := by rw [Category.assoc, hnl]
        _ = specOverMap q₁ ≫ κ ≫ kn := by rw [← Category.assoc, hμ₂l, Category.assoc]
        _ = specOverMap q₁ ≫ specOverMap Vn ≫ ν := by rw [hκn]
        _ = (specOverMap rVn ≫ specOverMap q) ≫ ν := by
          rw [← Category.assoc, ← specOverMap_comp, ← specOverMap_comp, hsq]
        _ = (specOverMap rVn ≫ μ) ≫ l := by rw [Category.assoc, Category.assoc, hμl]
  have hb₀ := hbase h₁ hh₁j k₁ hh₁ (descV₀ T' hC) hκ₁ (rV₀ hC (kerIdeal i))
    (qC_rV₀ hC (kerIdeal i) hI)
  have hb₁ := hbase h₂ hh₂j k₂ hh₂ (descVₗ T' hC) hκ₂ (rVₗ hC (kerIdeal i))
    (qC_rVₗ hC (kerIdeal i) hI)
  have : 𝒳.val.p.IsStronglyCartesian l₂ δ := hp.isStronglyCartesian_homLift l₂ δ
  have hrq := map_descArr_eq_chartRbar_of_cover u hom φT c₀ α cm μ c₁ hcm l β t hc₁β κ σ τ s₀ s₁
    hs₀ hs₁ hhom l₂ δ h₁ h₂ γ₁ γ₂ hδσ hδτ hγ μ₂ hμ₂l hb₀ hb₁
  -- the lifting step
  obtain ⟨x', ζ, φe, hζl, hφel, hcφ⟩ := exists_lift_of_chartLift hA hC (kerIdeal i) hI hst b hb sV
    tV hsV htV hxb u cm hc εbar hε' hom hrq
  have hνf : Flat ((BigFppfOver.toScheme B S hS).map ν) := by
    show Flat ((BigFppfOver.toScheme B S hS).map (specOverMap (SmallAlg.homMk u) ≫ ι))
    rw [hu, Functor.map_comp]; infer_instance
  have hνs : Surjective ((BigFppfOver.toScheme B S hS).map ν) := by
    show Surjective ((BigFppfOver.toScheme B S hS).map (specOverMap (SmallAlg.homMk u) ≫ ι))
    rw [hu, Functor.map_comp]; infer_instance
  have hνp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map ν) := by
    show LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map (specOverMap (SmallAlg.homMk u) ≫ ι))
    rw [hu, Functor.map_comp]; infer_instance
  exact exists_lift_of_chartLift_of_cover h𝒳 harr i hI j l k hpb hl hA φT
    (redToBase_comp i hsurjI hA) u ν hνf hνs hνp hbm μ hμj hμl c₀ α β t c₁ hc₁β cm hcm ζ φe hcφ

/-- **A lift over an fppf cover with descent data descends, compatibly.** In the situation of
`AlgebraicGeometry.Stack.GroupoidLift.exists_hom_of_cover`, let `c'' = c' ×_{T'} c'` (by `k₁`,
`k₂`) with reduction `c₂ = T ×_{T'} c''` (by `j₂`, `l₂`) and its two maps `h₁`, `h₂` to `c`. Let
`β : y ⟶ y'` be a lift of `y = x|_c` along `l` whose two pullbacks to `c''` are identified as
lifts of `y₂ = x|_{c₂}`: an object `w` over `c''` with `σ : w ⟶ y'` over `k₁`, `τ : w ⟶ y'` over
`k₂` and `δ : y₂ ⟶ w` over `l₂` with `δ ≫ σ = γ₁ ≫ β`, `δ ≫ τ = γ₂ ≫ β`, where
`γ₁ ≫ α = γ₂ ≫ α`. Then `x` has a lift `φ : x ⟶ z` along `i` whose pullback to `c'` is the lift
`β`: there is `ρ : y' ⟶ z` over `k` with `β ≫ ρ = α ≫ φ`. -/
theorem exists_lift_of_cover (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (f : 𝒳 ⟶ schemeFibredCategory B S hS (Over.mk (𝟙 (B.obj hS))))
    (hf : HasPropertyOnEverySmoothDiagram B S hS
      (fun _ _ g => Space.IsLocallyOfFinitePresentation B S hS g) f)
    {T c c' c'' c₂ : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj c)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj c')]
    (i : T ⟶ T') (hi : Deformation.Artin.IsDeformationSituation
      ((BigFppfOver.toScheme B S hS).map i).appTop.hom)
    (j : c ⟶ T) (l : c ⟶ c') (k : c' ⟶ T') (hpb : IsPullback j l i k)
    (hl : Deformation.Artin.IsDeformationSituation
      ((BigFppfOver.toScheme B S hS).map l).appTop.hom)
    (hkf : Flat ((BigFppfOver.toScheme B S hS).map k))
    (hks : Surjective ((BigFppfOver.toScheme B S hS).map k))
    (hkp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map k))
    (k₁ k₂ : c'' ⟶ c') (hpb₂ : IsPullback k₁ k₂ k k) (j₂ : c₂ ⟶ T) (l₂ : c₂ ⟶ c'')
    (hpb₃ : IsPullback j₂ l₂ i (k₁ ≫ k)) (h₁ h₂ : c₂ ⟶ c) (hh₁ : h₁ ≫ l = l₂ ≫ k₁)
    (hh₂ : h₂ ≫ l = l₂ ≫ k₂) (hh₁j : h₁ ≫ j = j₂) (hh₂j : h₂ ≫ j = j₂)
    {x y y' y₂ w : 𝒳.val.obj} (hx : 𝒳.val.p.obj x = T) (α : y ⟶ x)
    (hα : 𝒳.val.p.IsHomLift j α) (β : y ⟶ y') (hβ : 𝒳.val.p.IsHomLift l β)
    (γ₁ γ₂ : y₂ ⟶ y) (hγ₁ : 𝒳.val.p.IsHomLift h₁ γ₁) (hγ₂ : 𝒳.val.p.IsHomLift h₂ γ₂)
    (hγ : γ₁ ≫ α = γ₂ ≫ α) (σ τ : w ⟶ y') (hσ : 𝒳.val.p.IsHomLift k₁ σ)
    (hτ : 𝒳.val.p.IsHomLift k₂ τ) (δ : y₂ ⟶ w) (hδ : 𝒳.val.p.IsHomLift l₂ δ)
    (hδσ : δ ≫ σ = γ₁ ≫ β) (hδτ : δ ≫ τ = γ₂ ≫ β) :
    ∃ (z : 𝒳.val.obj) (_ : 𝒳.val.p.obj z = T') (φ : x ⟶ z) (ρ : y' ⟶ z),
      𝒳.val.p.IsHomLift i φ ∧ 𝒳.val.p.IsHomLift k ρ ∧ β ≫ ρ = α ≫ φ :=
  exists_lift_of_cover_of_arrSpace h𝒳
    (arrowSpacesLocallyOfFinitePresentation_of_structureMorphism h𝒳 f hf)
    i hi j l k hpb hl hkf hks hkp k₁ k₂ hpb₂ j₂ l₂ hpb₃ h₁ h₂ hh₁ hh₂ hh₁j hh₂j hx α hα β hβ γ₁ γ₂
    hγ₁ hγ₂ hγ σ τ hσ hτ δ hδ hδσ hδτ

end GroupoidLift

end AlgebraicGeometry.Stack

end
