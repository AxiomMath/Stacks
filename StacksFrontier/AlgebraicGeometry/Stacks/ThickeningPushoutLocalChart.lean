module

public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningPushoutAtlasChart
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningPushoutGluedChart
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactQuasiSeparatedPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.Thickenings.SchemeChartLift
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.Thickenings.SpacesEtaleEquivalenceGeneral
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningPushoutLocalDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningPushoutLocalToGlobal

/-!
# The local preimage of Stacks 07WN

Let `𝒵` be an algebraic stack over `S`, with a smooth surjective presentation `f₀ : U₀ ⟶ 𝒵`, let
`X ⟶ X'` be a thickening and `X ⟶ Y` an affine morphism of schemes over `S` with pushout
`Y' = Y ⨿_X X'`, and let `(y, x', α)` be an object of `𝒵_Y ×_{𝒵_X} 𝒵_{X'}`. This file carries
out the first two paragraphs of the essential surjectivity half of the proof of Stacks 07WN:
it produces a smooth surjective `q : P ⟶ Y'` with `P ×_{Y'} Y` and `P ×_{Y'} X'` étale charts of
the algebraic spaces `V = Y ×_{y, 𝒵} U₀` and `Q = X' ×_{x', 𝒵} U₀`, glued along `V ×_Y X ≅
Q ×_{X'} X`, together with a morphism `P ⟶ U₀` restricting to the two chart morphisms.

## References

* [Stacks Project, Tag 07WN](https://stacks.math.columbia.edu/tag/07WN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack.ThickeningPushout

open AlgebraicGeometry.Space.C1573 (SchemeChartLiftProperty ThickeningRepresentableProperty
  isEtale_of_isPullback_presheaf isThickeningHom_of_isPullback_yoneda
  exists_desc_of_isPushout_toScheme schemeChartLiftProperty_of_thickeningRepresentable)

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The local chart data -/

variable {B S hS}

/-- **The local preimage data of Stacks 07WN, on charts.** A smooth surjective `q : P ⟶ Y'`
obtained by gluing a scheme `V₁` smooth over `Y` and a scheme `U'₁` smooth over `X'` along
their common base change `U₁` to `X`, a morphism `cP : P ⟶ U₀` to the atlas, and morphisms from
the images under the atlas of the two restrictions of `cP` to `y` and to `x'`, compatible over
`U₁` through `α`. -/
structure LocalChartData (𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    {U₀ : BigFppfOver B S hS} (f₀ : schemeFibredCategory B S hS U₀ ⟶ 𝒵)
    {X X' Y Y' : BigFppfOver B S hS} (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y') (b : Y ⟶ Y')
    (c : 𝒵.val.p.ChoiceOfPullbacks) (y : 𝒵.val.p.Fiber Y) (x' : 𝒵.val.p.Fiber X')
    (α : c.obj f y ≅ c.obj i x') where
  /-- The chart over `Y`. -/
  V₁ : BigFppfOver B S hS
  /-- The chart over `X'`. -/
  U'₁ : BigFppfOver B S hS
  /-- The common chart over `X`. -/
  U₁ : BigFppfOver B S hS
  /-- The glued chart over `Y'`. -/
  P : BigFppfOver B S hS
  /-- The structure morphism of `V₁` to `Y`. -/
  t : V₁ ⟶ Y
  /-- The structure morphism of `U'₁` to `X'`. -/
  t' : U'₁ ⟶ X'
  /-- The structure morphism of `U₁` to `X`. -/
  r : U₁ ⟶ X
  /-- The base change morphism `U₁ ⟶ V₁` along `f`. -/
  g : U₁ ⟶ V₁
  /-- The base change morphism `U₁ ⟶ U'₁` along `i`. -/
  k : U₁ ⟶ U'₁
  /-- The inclusion of `U'₁` into the glued chart `P`. -/
  u₁ : U'₁ ⟶ P
  /-- The inclusion of `V₁` into the glued chart `P`. -/
  u₂ : V₁ ⟶ P
  /-- The structure morphism of `P` to `Y'`. -/
  q : P ⟶ Y'
  /-- The morphism from `P` to the atlas `U₀`. -/
  cP : P ⟶ U₀
  hk : IsPullback k r t' i
  hg : IsPullback g r t f
  hu₁ : IsPullback u₁ t' q a
  hu₂ : IsPullback u₂ t q b
  /-- The morphism `q` is smooth. -/
  smooth_q : Smooth ((BigFppfOver.toScheme B S hS).map q)
  /-- The morphism `q` is surjective. -/
  surjective_q : Surjective ((BigFppfOver.toScheme B S hS).map q)
  hkg : k ≫ u₁ = g ≫ u₂
  /-- The morphism to `y`. -/
  ψY : f₀.hom.obj (Over.mk (u₂ ≫ cP)) ⟶ y.1
  isHomLift_ψY : 𝒵.val.p.IsHomLift t ψY
  /-- The morphism to `x'`. -/
  ψX' : f₀.hom.obj (Over.mk (u₁ ≫ cP)) ⟶ x'.1
  isHomLift_ψX' : 𝒵.val.p.IsHomLift t' ψX'
  /-- The factorisation over `X`. -/
  lam : f₀.hom.obj (Over.mk (g ≫ u₂ ≫ cP)) ⟶ (c.obj f y).1
  isHomLift_lam : 𝒵.val.p.IsHomLift r lam
  lam_fac : lam ≫ c.map f y =
    f₀.hom.map (Over.homMk g rfl : Over.mk (g ≫ u₂ ≫ cP) ⟶ Over.mk (u₂ ≫ cP)) ≫ ψY
  lam_iso : lam ≫ α.hom.1 ≫ c.map i x' =
    f₀.hom.map (Over.homMk k (by simp only [Over.mk_hom, ← Category.assoc, hkg]) :
      Over.mk (g ≫ u₂ ≫ cP) ⟶ Over.mk (u₁ ≫ cP)) ≫ ψX'

/-- Evaluating a commutative square `yoneda.map k ≫ m' = m ≫ j` at the identity. -/
private lemma map_app_id_eq_of_yoneda_map_comp_eq.{v, w} {C : Type w} [Category.{v} C] {A A' : C}
    {F G : Cᵒᵖ ⥤ Type v} {k : A ⟶ A'} {m' : yoneda.obj A' ⟶ F} {m : yoneda.obj A ⟶ G}
    {j : G ⟶ F} (h : yoneda.map k ≫ m' = m ≫ j) :
    F.map k.op (m'.app (op A') (𝟙 A')) = j.app (op A) (m.app (op A) (𝟙 A)) := by
  have h' := congrArg (fun φ : yoneda.obj A ⟶ F => φ.app (op A) (𝟙 A)) h
  change m'.app (op A) (𝟙 A ≫ k) = j.app (op A) (m.app (op A) (𝟙 A)) at h'
  refine Eq.trans ?_ h'
  refine (NatTrans.naturality_apply m' k.op (𝟙 A')).symm.trans ?_
  change m'.app (op A) (k ≫ 𝟙 A') = m'.app (op A) (𝟙 A ≫ k)
  rw [Category.comp_id, Category.id_comp]

/-- **Stacks 07WN, the construction of a local preimage on charts.** -/
theorem nonempty_localChartData (hlift : SchemeChartLiftProperty B S hS)
    (𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    {U₀ : BigFppfOver B S hS} (f₀ : schemeFibredCategory B S hS U₀ ⟶ 𝒵)
    (hf₀ : IsRepresentableByAlgebraicSpaces B S hS f₀.hom)
    (hsm : HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.smoothMorphismProperty B S hS) f₀
      hf₀)
    (hsu : HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.surjectiveMorphismProperty B S hS)
      f₀ hf₀)
    {X X' Y Y' : BigFppfOver B S hS} (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y') (b : Y ⟶ Y')
    (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i))
    [IsAffineHom ((BigFppfOver.toScheme B S hS).map f)]
    (hsq : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f) ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b))
    (c : 𝒵.val.p.ChoiceOfPullbacks) (y : 𝒵.val.p.Fiber Y) (x' : 𝒵.val.p.Fiber X')
    (α : c.obj f y ≅ c.obj i x') :
    Nonempty (LocalChartData 𝒵 f₀ i f a b c y x' α) := by
  set Φs := BigFppfOver.toScheme B S hS
  have hp := 𝒵.isFiberedInGroupoids
  have hf₀w : f₀.hom.toFunctor ⋙ 𝒵.val.p = Over.forget U₀ := f₀.hom.w
  -- the two charts `V = Y ×_𝒵 U₀` and `Q = X' ×_𝒵 U₀`
  obtain ⟨FV, hFV, ⟨eV⟩⟩ := exists_chartSpace 𝒵 f₀ hf₀ y
  obtain ⟨FQ, hFQ, ⟨eQ⟩⟩ := exists_chartSpace 𝒵 f₀ hf₀ x'
  obtain ⟨V₁, aV, τ, haE, haτ, hmapτ, htsm, htsu⟩ := exists_chartTriple hf₀ hsm hsu y hFV eV
  obtain ⟨hsmQ, -⟩ := chartFst_smooth_surjective hf₀ hsm hsu x' hFQ eQ
  set ρY := chartFst eV
  set ρX' := chartFst eQ
  set Z := Presheaf.fibreProduct ρY (yoneda.map f)
  have hZpb := Presheaf.isPullback_fibreProduct ρY (yoneda.map f)
  -- the comparison `V ×_Y X ≅ Q ×_{X'} X`
  set Ψ := chartComparison hp hf₀w c f i y x' α eV eQ ρY ρX' (chartFst_app_tripSection eV)
    (chartFst_app_tripSection eQ) with hΨ
  have hZalg : IsAlgebraicSpace B S hS Z :=
    isAlgebraicSpace_of_isPullback hFV (isAlgebraicSpace_yoneda B S hS X)
      (isAlgebraicSpace_yoneda B S hS Y).isSheaf
      (isAlgebraicSpace_yoneda B S hS Y).diagonal_representable hZpb
  set jZ : Z ⟶ FQ := Ψ.hom ≫ Presheaf.fibreProductFst ρX' (yoneda.map i) with hjZ
  have hjpb : IsPullback jZ (Presheaf.fibreProductSnd ρY (yoneda.map f)) ρX' (yoneda.map i) :=
    IsPullback.of_iso (Presheaf.isPullback_fibreProduct ρX' (yoneda.map i)) Ψ.symm (Iso.refl _)
      (Iso.refl _) (Iso.refl _) (by simp [hjZ]) (by
        rw [Iso.symm_hom, Iso.refl_hom, Category.comp_id, Iso.eq_inv_comp, hΨ]
        exact chartComparison_hom_snd hp hf₀w c f i y x' α eV eQ ρY ρX'
          (chartFst_app_tripSection eV) (chartFst_app_tripSection eQ)) (by simp) (by simp)
  have hjth : Space.IsThickeningHom B S hS
      (ObjectProperty.homMk jZ : (⟨Z, hZalg⟩ : AlgebraicSpaces B S hS) ⟶ ⟨FQ, hFQ⟩) :=
    isThickeningHom_of_isPullback_yoneda B S hS _ _ ρX' i hi hjpb
  -- the chart `U₁ = V₁ ×_Y X` and its étale morphism to `V ×_Y X`
  have hpbU := IsPullback.of_hasPullback τ.1 f
  set U₁ := pullback τ.1 f
  set g : U₁ ⟶ V₁ := pullback.fst τ.1 f with hg
  set r : U₁ ⟶ X := pullback.snd τ.1 f with hr
  have hgr : yoneda.map g ≫ aV ≫ ρY = yoneda.map r ≫ yoneda.map f := by
    rw [← hmapτ, ← yoneda.map_comp, ← yoneda.map_comp, pullback.condition]
  set m : yoneda.obj U₁ ⟶ Z := Presheaf.fibreProductLift ρY (yoneda.map f)
    (yoneda.map g ≫ aV) (yoneda.map r) (by rw [Category.assoc, hgr])
  have hm₂ : m ≫ Presheaf.fibreProductSnd ρY (yoneda.map f) = yoneda.map r := rfl
  have hmpb : IsPullback (yoneda.map g) m aV (Presheaf.fibreProductFst ρY (yoneda.map f)) := by
    refine (IsPullback.of_right (h₁₁ := m) (h₁₂ := Presheaf.fibreProductSnd ρY (yoneda.map f))
      (v₁₁ := yoneda.map g) (v₁₂ := Presheaf.fibreProductFst ρY (yoneda.map f))
      (v₁₃ := yoneda.map f) (h₂₁ := aV) (h₂₂ := ρY) ?_ rfl hZpb.flip).flip
    rw [hm₂, ← hmapτ]
    exact (hpbU.map yoneda).flip
  -- the lift of `U₁` across the thickening `V ×_Y X ⟶ Q`
  obtain ⟨U'₁, m', k, hm'E, hkpb⟩ := hlift _ hjth U₁ m
    (isEtale_of_isPullback_presheaf B S hS (isAlgebraicSpace_yoneda B S hS U₁)
      (isAlgebraicSpace_yoneda B S hS V₁) hFV hZalg hmpb haE)
  have hkpb' : IsPullback (yoneda.map k) m m' jZ := hkpb
  -- the triple named by the lifted chart
  obtain ⟨τ', hτ'⟩ := tripSection_surjective eQ U'₁ (m'.app (op U'₁) (𝟙 U'₁))
  have hmapτ' : yoneda.map τ'.1 = m' ≫ ρX' := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    change τ'.1 = ρX'.app (op U'₁) (m'.app (op U'₁) (𝟙 U'₁))
    rw [← hτ']
    exact (chartFst_app_tripSection eQ τ').symm
  have ht'sm : Smooth (Φs.map τ'.1) := by
    refine (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      Smooth.isEtaleLocalOnSourceAndTarget τ'.1).1 ?_
    rw [hmapτ']
    exact Space.isSmooth_comp B S hS (isAlgebraicSpace_yoneda B S hS U'₁) hFQ
      (isAlgebraicSpace_yoneda B S hS X') m' _ (Space.isSmooth_of_isEtale B S hS hFQ hm'E) hsmQ
  -- the two cartesian squares of schemes over `X`
  have hkY : IsPullback (yoneda.map k) (yoneda.map r) (yoneda.map τ'.1) (yoneda.map i) := by
    rw [hmapτ', ← hm₂]
    exact hkpb'.paste_vert hjpb
  have : ReflectsLimitsOfShape WalkingCospan (yoneda (C := BigFppfOver B S hS)) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  have hk : IsPullback k r τ'.1 i := IsPullback.of_map_of_faithful yoneda hkY
  have : ReflectsLimitsOfShape WalkingCospan Φs := reflectsLimitsOfShape_of_reflectsIsomorphisms
  obtain ⟨P, u₁, u₂, q, hpush, hq₁, hq₂, hpb₁, hpb₂, hsmq, -, hsuq⟩ :=
    exists_gluedChart B S hS hi hsq (hk.map Φs) (hpbU.map Φs)
  -- the two triples agree over `U₁`, through `α`
  have hwY := TwoYoneda.liftFunctor_w 𝒵.val.p hp Y y
  have hwX := TwoYoneda.liftFunctor_w 𝒵.val.p hp X' x'
  set τg := τ.restrict hp hf₀w hwY g
  have hgτ : τg.1 = r ≫ f := by
    simp [τg, hg, hr, pullback.condition]
  have hmU : m.app (op U₁) (𝟙 U₁) =
      ⟨(tripSection eV τg, r), by
        rw [chartFst_app_tripSection]
        exact hgτ⟩ := by
    apply Subtype.ext
    refine Prod.ext ?_ rfl
    exact (NatTrans.naturality_apply aV g.op (𝟙 V₁)).trans ((congrArg (FV.map g.op) haτ).trans
      (map_tripSection hp hf₀w hwY eV g τ))
  have hsec : tripSection eQ (τ'.restrict hp hf₀w hwX k) =
      tripSection eQ (transfer hp c f i y x' α τg r hgτ) := by
    refine (map_tripSection hp hf₀w hwX eQ k τ').symm.trans ?_
    refine (congrArg (FQ.map k.op) hτ').trans
      ((map_app_id_eq_of_yoneda_map_comp_eq hkpb'.w).trans ?_)
    refine Eq.trans ?_ (chartComparison_hom_app_fst hp hf₀w c f i y x' α eV eQ ρY ρX'
      (chartFst_app_tripSection eV) (chartFst_app_tripSection eQ) _ r hgτ)
    rw [hmU]
    rfl
  obtain ⟨hcomp₁, hcomp₂, hcomp₃⟩ := exists_hom_of_tripSection_eq eQ _ _ hsec
  obtain ⟨cP, hcP₁, hcP₂⟩ := exists_desc_of_isPushout_toScheme B S hS hpush τ'.2.1 τ.2.1
    hcomp₂.symm
  have hkg : k ≫ u₁ = g ≫ u₂ := by
    apply Φs.map_injective
    rw [Φs.map_comp, Φs.map_comp]
    exact hpush.w
  -- the morphisms to `y` and to `x'`, and their compatibility over `U₁`
  obtain ⟨ψY, ψX, lam, hψY, hψX, hlam, hlamf, hlami⟩ := exists_glueMorphisms hp hf₀w c f i y x' α
    τ τ' g k r hgτ hcomp₁ hcomp₂ hcomp₃ (u₂ ≫ cP) (u₁ ≫ cP) hcP₂ hcP₁
  exact ⟨{
    V₁ := V₁
    U'₁ := U'₁
    U₁ := U₁
    P := P
    t := τ.1
    t' := τ'.1
    r := r
    g := g
    k := k
    u₁ := u₁
    u₂ := u₂
    q := q
    cP := cP
    hk := hk
    hg := hpbU
    hu₁ := IsPullback.of_map_of_faithful Φs hpb₁
    hu₂ := IsPullback.of_map_of_faithful Φs hpb₂
    smooth_q := hsmq htsm ht'sm
    surjective_q := ⟨hsuq htsu.surj⟩
    hkg := hkg
    ψY := ψY
    isHomLift_ψY := hψY
    ψX' := ψX
    isHomLift_ψX' := hψX
    lam := lam
    isHomLift_lam := hlam
    lam_fac := hlamf
    lam_iso := by rw [hlami] }⟩

/-! ### From chart data to a local preimage -/

section Generic

variable {𝒮 : Type*} [Category 𝒮] [HasPullbacks 𝒮] {𝒳 : Type*} [Category 𝒳] (p : 𝒳 ⥤ 𝒮)
  [p.IsFibered] {U₀ : 𝒮} (F₀ : Over U₀ ⥤ 𝒳)

omit [HasPullbacks 𝒮] [p.IsFibered] in
/-- If `φ` lies over `f₁` and `ψ` lies over `f₂`, then `φ ≫ ψ` lies over any `h` equal to
`f₁ ≫ f₂`. -/
lemma isHomLift_comp_of_eq {R S : 𝒮} {a b c : 𝒳} {f₁ : R ⟶ S} {T : 𝒮} {f₂ : S ⟶ T}
    {h : R ⟶ T} (φ : a ⟶ b) (ψ : b ⟶ c) (h₁ : p.IsHomLift f₁ φ) (h₂ : p.IsHomLift f₂ ψ)
    (e : f₁ ≫ f₂ = h) : p.IsHomLift h (φ ≫ ψ) := by
  subst e
  exact IsHomLift.comp p f₁ f₂ φ ψ

/-- **Chart data give a local preimage**, in a general category fibred over a category with
fibre products. -/
noncomputable def localPreimageOfCharts (hf₀w : F₀ ⋙ p = Over.forget U₀)
    {X X' Y Y' : 𝒮} {i : X ⟶ X'} {f : X ⟶ Y} {a : X' ⟶ Y'} {b : Y ⟶ Y'} (w : f ≫ b = i ≫ a)
    (e : CategoricalPullback (p.chosenPullbacks.pullbackFunctor f)
      (p.chosenPullbacks.pullbackFunctor i))
    {V₁ U'₁ U₁ P : 𝒮} {t : V₁ ⟶ Y} {t' : U'₁ ⟶ X'} {r : U₁ ⟶ X} {g : U₁ ⟶ V₁} {k : U₁ ⟶ U'₁}
    {u₁ : U'₁ ⟶ P} {u₂ : V₁ ⟶ P} {q : P ⟶ Y'} (cP : P ⟶ U₀)
    (hk : IsPullback k r t' i) (hg : IsPullback g r t f) (hu₁ : IsPullback u₁ t' q a)
    (hu₂ : IsPullback u₂ t q b) (hkg : k ≫ u₁ = g ≫ u₂)
    (ψY : F₀.obj (Over.mk (u₂ ≫ cP)) ⟶ e.fst.1) (hψY : p.IsHomLift t ψY)
    (ψX' : F₀.obj (Over.mk (u₁ ≫ cP)) ⟶ e.snd.1) (hψX' : p.IsHomLift t' ψX')
    (lam : F₀.obj (Over.mk (g ≫ u₂ ≫ cP)) ⟶ (p.chosenPullbacks.obj f e.fst).1)
    (hlam : p.IsHomLift r lam)
    (lam_fac : lam ≫ p.chosenPullbacks.map f e.fst =
      F₀.map (Over.homMk g rfl : Over.mk (g ≫ u₂ ≫ cP) ⟶ Over.mk (u₂ ≫ cP)) ≫ ψY)
    (lam_iso : lam ≫ e.iso.hom.1 ≫ p.chosenPullbacks.map i e.snd =
      F₀.map (Over.homMk k (by simp only [Over.mk_hom, ← Category.assoc, hkg]) :
        Over.mk (g ≫ u₂ ≫ cP) ⟶ Over.mk (u₁ ≫ cP)) ≫ ψX') :
    Deformation.Artin.LocalPreimage (p := p) (f := f) (i := i) (b := b) (a := a) w e q := by
  let ι : pullback b q ⟶ V₁ := hu₂.flip.isoPullback.inv
  have hιt : ι ≫ t = pullback.fst b q := hu₂.flip.isoPullback_inv_fst
  have hιu : ι ≫ u₂ = pullback.snd b q := hu₂.flip.isoPullback_inv_snd
  let ι' : pullback a q ⟶ U'₁ := hu₁.flip.isoPullback.inv
  have hι't : ι' ≫ t' = pullback.fst a q := hu₁.flip.isoPullback_inv_fst
  have hι'u : ι' ≫ u₁ = pullback.snd a q := hu₁.flip.isoPullback_inv_snd
  let bL := Deformation.Artin.baseChangeLeft f b q
  let bT := Deformation.Artin.baseChangeTop f i b a w q
  have hbL : bL ≫ pullback.snd b q = pullback.snd (f ≫ b) q := pullback.lift_snd _ _ _
  have hbT : bT ≫ pullback.snd a q = pullback.snd (f ≫ b) q := pullback.lift_snd _ _ _
  have hbLf : bL ≫ pullback.fst b q = pullback.fst (f ≫ b) q ≫ f := pullback.lift_fst _ _ _
  have hbTf : bT ≫ pullback.fst a q = pullback.fst (f ≫ b) q ≫ i := pullback.lift_fst _ _ _
  let ιX : pullback (f ≫ b) q ⟶ U₁ := hg.lift (bL ≫ ι) (pullback.fst (f ≫ b) q)
    (by rw [Category.assoc, hιt, hbLf])
  have hιXg : ιX ≫ g = bL ≫ ι := hg.lift_fst _ _ _
  have hιXr : ιX ≫ r = pullback.fst (f ≫ b) q := hg.lift_snd _ _ _
  have hιXk : ιX ≫ k = bT ≫ ι' := by
    refine hu₁.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hι'u, hbT, hkg, reassoc_of% hιXg, hιu, hbL]
    · rw [Category.assoc, Category.assoc, hι't, hbTf, hk.w, reassoc_of% hιXr]
  exact {
    obj := ⟨F₀.obj (Over.mk cP), Functor.congr_obj hf₀w _⟩
    zY := F₀.obj (Over.mk (pullback.snd b q ≫ cP))
    zX' := F₀.obj (Over.mk (pullback.snd a q ≫ cP))
    zX := F₀.obj (Over.mk (pullback.snd (f ≫ b) q ≫ cP))
    sY := F₀.map (Over.homMk (pullback.snd b q) rfl :
      Over.mk (pullback.snd b q ≫ cP) ⟶ Over.mk cP)
    tY := F₀.map (Over.homMk ι (by simp [reassoc_of% hιu]) :
      Over.mk (pullback.snd b q ≫ cP) ⟶ Over.mk (u₂ ≫ cP)) ≫ ψY
    sX' := F₀.map (Over.homMk (pullback.snd a q) rfl :
      Over.mk (pullback.snd a q ≫ cP) ⟶ Over.mk cP)
    tX' := F₀.map (Over.homMk ι' (by simp [reassoc_of% hι'u]) :
      Over.mk (pullback.snd a q ≫ cP) ⟶ Over.mk (u₁ ≫ cP)) ≫ ψX'
    lY := F₀.map (Over.homMk bL (by simp [reassoc_of% hbL]) :
      Over.mk (pullback.snd (f ≫ b) q ≫ cP) ⟶ Over.mk (pullback.snd b q ≫ cP))
    lX' := F₀.map (Over.homMk bT (by simp [reassoc_of% hbT]) :
      Over.mk (pullback.snd (f ≫ b) q ≫ cP) ⟶ Over.mk (pullback.snd a q ≫ cP))
    lam := F₀.map (Over.homMk ιX (by simp [reassoc_of% hιXg, reassoc_of% hιu,
      reassoc_of% hbL]) :
      Over.mk (pullback.snd (f ≫ b) q ≫ cP) ⟶ Over.mk (g ≫ u₂ ≫ cP)) ≫ lam
    isHomLift_sY := isHomLift_f₀_homMk hf₀w _ _
    isHomLift_tY := isHomLift_comp_of_eq p _ _ (isHomLift_f₀_map hf₀w (Over.homMk ι (by
      simp [reassoc_of% hιu]) : Over.mk (pullback.snd b q ≫ cP) ⟶ Over.mk (u₂ ≫ cP))) hψY hιt
    isHomLift_sX' := isHomLift_f₀_homMk hf₀w _ _
    isHomLift_tX' := isHomLift_comp_of_eq p _ _ (isHomLift_f₀_map hf₀w (Over.homMk ι' (by
      simp [reassoc_of% hι'u]) : Over.mk (pullback.snd a q ≫ cP) ⟶ Over.mk (u₁ ≫ cP))) hψX' hι't
    isHomLift_lY := isHomLift_f₀_map hf₀w (Over.homMk bL (by simp [reassoc_of% hbL]) :
      Over.mk (pullback.snd (f ≫ b) q ≫ cP) ⟶ Over.mk (pullback.snd b q ≫ cP))
    isHomLift_lX' := isHomLift_f₀_map hf₀w (Over.homMk bT (by simp [reassoc_of% hbT]) :
      Over.mk (pullback.snd (f ≫ b) q ≫ cP) ⟶ Over.mk (pullback.snd a q ≫ cP))
    isHomLift_lam := isHomLift_comp_of_eq p _ _ (isHomLift_f₀_map hf₀w (Over.homMk ιX (by
      simp [reassoc_of% hιXg, reassoc_of% hιu, reassoc_of% hbL]) :
      Over.mk (pullback.snd (f ≫ b) q ≫ cP) ⟶ Over.mk (g ≫ u₂ ≫ cP))) hlam hιXr
    lY_sY := by
      rw [← F₀.map_comp, ← F₀.map_comp]
      congr 1
      exact Over.OverMorphism.ext (by simp [hbL, hbT])
    lam_map := by
      rw [Category.assoc, lam_fac, ← F₀.map_comp_assoc, ← F₀.map_comp_assoc]
      congr 2
      exact Over.OverMorphism.ext (by simp [hιXg])
    lam_iso := by
      rw [Category.assoc]
      change _ ≫ lam ≫ e.iso.hom.1 ≫ _ = _
      rw [lam_iso, ← F₀.map_comp_assoc, ← F₀.map_comp_assoc]
      congr 2
      exact Over.OverMorphism.ext (by simp [hιXk]) }

end Generic

/-- **The chart data is a local preimage.** The object over `P` is the image under the atlas of
`cP : P ⟶ U₀`; its restrictions to `Y ×_{Y'} P` and `X' ×_{Y'} P` are identified with those of
`y` and `x'` through the cartesian squares of the chart data. -/
noncomputable def LocalChartData.localPreimage
    {𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} [𝒵.val.p.IsFibered]
    {U₀ : BigFppfOver B S hS} {f₀ : schemeFibredCategory B S hS U₀ ⟶ 𝒵}
    {X X' Y Y' : BigFppfOver B S hS} {i : X ⟶ X'} {f : X ⟶ Y} {a : X' ⟶ Y'} {b : Y ⟶ Y'}
    (w : f ≫ b = i ≫ a)
    (e : CategoricalPullback (𝒵.val.p.chosenPullbacks.pullbackFunctor f)
      (𝒵.val.p.chosenPullbacks.pullbackFunctor i))
    (D : LocalChartData 𝒵 f₀ i f a b 𝒵.val.p.chosenPullbacks e.fst e.snd e.iso) :
    Deformation.Artin.LocalPreimage (p := 𝒵.val.p) (f := f) (i := i) (b := b) (a := a) w e D.q :=
  localPreimageOfCharts 𝒵.val.p f₀.hom.toFunctor f₀.hom.w w e D.cP D.hk D.hg D.hu₁
    D.hu₂ D.hkg
    D.ψY D.isHomLift_ψY D.ψX' D.isHomLift_ψX' D.lam D.isHomLift_lam D.lam_fac D.lam_iso

/-! ### The equivalence, given lifts of scheme charts -/

/-- **Stacks 07WN, reduced to the lifting of étale scheme charts along thickenings.** -/
theorem fiberSquareComparison_isEquivalence_of_schemeChartLift.{w'}
    (hlift : SchemeChartLiftProperty B S hS)
    (𝒵 : BasedCategory.{u, u + 1} (BigFppfOver B S hS))
    (h𝒵 : IsAlgebraicStack.{u, w'} B S hS 𝒵)
    {X X' Y Y' : BigFppfOver B S hS} (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y') (b : Y ⟶ Y')
    (w : i ≫ a = f ≫ b)
    (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i))
    [IsAffineHom ((BigFppfOver.toScheme B S hS).map f)]
    (hsq : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f) ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b)) :
    letI : 𝒵.p.IsFibered := (Classical.choose h𝒵).isFibered
    (Deformation.Artin.fiberSquareComparison 𝒵.p 𝒵.p.chosenPullbacks f i b a
      w.symm).IsEquivalence := by
  let : 𝒵.p.IsFibered := (Classical.choose h𝒵).isFibered
  refine fiberSquareComparison_isEquivalence_of_isAlgebraicStack_of_localPreimage 𝒵 h𝒵
    w hi hsq (fun e => ?_)
  obtain ⟨U₀, f₀, hf₀, hsm, hsu⟩ := exists_atlas_of_isAlgebraicStack 𝒵 h𝒵
  obtain ⟨D⟩ := nonempty_localChartData hlift _ f₀ hf₀ hsm hsu i f a b hi hsq
    𝒵.p.chosenPullbacks e.fst e.snd e.iso
  have := D.smooth_q
  exact ⟨D.P, D.q, D.surjective_q, inferInstance, inferInstance,
    ⟨D.localPreimage (𝒵 := CatFiberedInGroupoids.mk 𝒵 (Classical.choose h𝒵)) w.symm e⟩⟩

end AlgebraicGeometry.Stack.ThickeningPushout

end
