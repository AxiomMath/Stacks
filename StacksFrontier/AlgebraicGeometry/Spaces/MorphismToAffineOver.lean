module

public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismToAffineScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.GlobalFunctionsAtlas

/-!
# Morphisms from an algebraic space to an affine object, over an arbitrary base

`AlgebraicGeometry.Space.morphismToAffineEquiv` (Stacks 05Z1) identifies the morphisms of
algebraic spaces `X ⟶ T` into an affine object `T` of the big fppf site of `S` with the ring
homomorphisms `Γ(T, 𝒪_T) →+* Γ(X, 𝒪_X)`, under the hypothesis that `S` is terminal. This file
removes that hypothesis, and then proves the relative form of the statement.

Over an arbitrary base the correspondence is with the ring homomorphisms `φ` whose chart
morphisms all lie over `S`: on every étale chart `U` of `X` the morphism of schemes `U ⟶ T`
determined by `φ` through the `Γ`–`Spec` adjunction must commute with the structure morphisms
to `S`. Over a terminal base this condition is empty.

The relative form is the case used in practice. Let `w : W ⟶ V` be a morphism of objects of
the site with affine underlying schemes and `p : X ⟶ V` a morphism from an algebraic space.
The morphisms `X ⟶ W` over `V` are then the ring homomorphisms `Γ(W) →+* Γ(X)` which restrict
to the pullback `p^*` along `Γ(V) →+* Γ(W)`, that is, the `Γ(V)`-algebra homomorphisms. The
condition over `S` is automatic here: a chart morphism into `W` which lies over `V` lies over
`S` because `W` and `V` do.

## Main definitions

* `AlgebraicGeometry.Space.chartMapOfGlobalHom`: the morphism of schemes from an étale chart of
  `X` to `T` determined by a ring homomorphism `φ`, with no hypothesis on `S`.
* `AlgebraicGeometry.Space.ChartMapsOver`: the condition that all of these lie over `S`.
* `AlgebraicGeometry.Space.chartPullbackFunctions`: the pullback of a function along a morphism
  to a representable, as a compatible family on all scheme charts; it identifies the pullback
  homomorphism under `AlgebraicGeometry.Space.globalFunctionsChartEquiv`.
* `AlgebraicGeometry.Space.morphismToAffineEquivOfChartMapsOver`: **Stacks 05Z1 over an
  arbitrary base.** Morphisms `X ⟶ T` correspond to the ring homomorphisms satisfying
  `AlgebraicGeometry.Space.ChartMapsOver`.
* `AlgebraicGeometry.Space.morphismToAffineOverEquiv`: **the relative form.** Morphisms
  `X ⟶ W` over `V` correspond to ring homomorphisms `Γ(W) →+* Γ(X)` extending `p^*`.

## Main results

* `AlgebraicGeometry.Space.pullbackToGlobalFunctions_injective`: a morphism into an affine
  object of the site is determined by its pullback on global functions, over any base.
* `AlgebraicGeometry.Space.pullbackToGlobalFunctions_comp_schemeSpaceMap_eq_comp` and
  `AlgebraicGeometry.Space.pullbackToGlobalFunctions_comp_left`: pullback of functions is
  natural in the target and in the source.

## Implementation notes

The descent along a surjective étale atlas is the one of
`AlgebraicGeometry.Space.affineMapOfGlobalHom`, with
`AlgebraicGeometry.Space.overMapOfSchemeHom` replaced by
`AlgebraicGeometry.Space.chartOverMap`, which takes the condition over `S` as input instead of
deriving it from terminality. The equivalence is `Equiv.ofBijective` of the pullback map, so
its forward map is pullback of functions by definition.

## References

* [Stacks Project, Lemma 66.6.6 (Tag 05Z1)](https://stacks.math.columbia.edu/tag/05Z1)
* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Chart morphisms over an arbitrary base -/

/-- The morphism of schemes from an étale chart of `X` to an affine object `T` of the site
whose action on global functions is `φ` followed by restriction to the chart. This is
`AlgebraicGeometry.Space.affineChartMap` without the terminality hypothesis, which that
definition does not use. -/
def chartMapOfGlobalHom (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (φ : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) →+* globalFunctions B S hS X.1)
    (V : SmallEtale B S hS X.1) :
    (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj V) ⟶
      (BigFppfOver.toScheme B S hS).obj T :=
  letI U := (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj V)
  letI R := (BigFppfOver.toScheme B S hS).obj T
  ΓSpec.adjunction.homEquiv U (op (CommRingCat.of Γ(R, ⊤)))
      (CommRingCat.ofHom ((globalFunctionsChartRestriction B S hS X V).comp φ)).op ≫
    (Scheme.isoSpec R).inv

/-- Over a terminal base, the chart morphism is the one of
`AlgebraicGeometry.Space.affineChartMap`. -/
lemma affineChartMap_eq_chartMapOfGlobalHom (X : AlgebraicSpaces B S hS)
    (T : BigFppfOver B S hS) (hterminal : IsTerminal S)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (φ : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) →+* globalFunctions B S hS X.1)
    (V : SmallEtale B S hS X.1) :
    affineChartMap B S hS X T hterminal φ V = chartMapOfGlobalHom B S hS X T φ V := rfl

/-- The action of `AlgebraicGeometry.Space.chartMapOfGlobalHom` on global functions is the
prescribed homomorphism followed by restriction to the chart. -/
lemma chartMapOfGlobalHom_appTop (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (φ : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) →+* globalFunctions B S hS X.1)
    (V : SmallEtale B S hS X.1) :
    Scheme.Hom.appTop (chartMapOfGlobalHom B S hS X T φ V) =
      CommRingCat.ofHom ((globalFunctionsChartRestriction B S hS X V).comp φ) := by
  let U := (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj V)
  let R := (BigFppfOver.toScheme B S hS).obj T
  change Scheme.Hom.appTop
    (ΓSpec.adjunction.homEquiv U (op (CommRingCat.of Γ(R, ⊤)))
      (CommRingCat.ofHom ((globalFunctionsChartRestriction B S hS X V).comp φ)).op ≫
      (Scheme.isoSpec R).inv) = _
  rw [Scheme.Hom.comp_appTop, Stacks.RelativeSpec.isoSpec_inv_appTop,
    ΓSpec_adjunction_homEquiv_eq]
  change (Scheme.ΓSpecIso Γ(R, ⊤)).inv ≫ (Scheme.ΓSpecIso Γ(R, ⊤)).hom ≫ _ = _
  rw [Iso.inv_hom_id_assoc]

/-- The chart morphisms are compatible with morphisms of charts. -/
lemma chartMapOfGlobalHom_comp (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (φ : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) →+* globalFunctions B S hS X.1)
    {V W : SmallEtale B S hS X.1} (g : V ⟶ W) :
    (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map g) ≫
        chartMapOfGlobalHom B S hS X T φ W =
      chartMapOfGlobalHom B S hS X T φ V := by
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, chartMapOfGlobalHom_appTop, chartMapOfGlobalHom_appTop]
  apply CommRingCat.hom_ext
  have hn := globalFunctionsChartRestriction_naturality B S hS X g
  ext s
  exact congrFun hn (φ s)

/-- A ring homomorphism on global functions is determined by its chart morphisms. -/
lemma eq_of_chartMapOfGlobalHom_eq (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    {φ ψ : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) →+* globalFunctions B S hS X.1}
    (h : ∀ V, chartMapOfGlobalHom B S hS X T φ V = chartMapOfGlobalHom B S hS X T ψ V) :
    φ = ψ := by
  refine RingHom.ext fun s ↦ Subtype.ext (funext fun V ↦ ?_)
  have hV := congrArg Scheme.Hom.appTop (h V.unop)
  rw [chartMapOfGlobalHom_appTop, chartMapOfGlobalHom_appTop] at hV
  exact congrArg (fun k => k.hom s) hV

/-- For a morphism to an affine object of the site, the chart morphism prescribed by its
pullback homomorphism is its restriction to the chart. -/
lemma chartMapOfGlobalHom_pullback (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (f : X ⟶ schemeSpace T) (V : SmallEtale B S hS X.1) :
    chartMapOfGlobalHom B S hS X T (pullbackToGlobalFunctions B S hS X T f) V =
      (BigFppfOver.toScheme B S hS).map (yoneda.preimage (V.1.hom ≫ f.hom)) := by
  apply ext_of_isAffine
  rw [chartMapOfGlobalHom_appTop]
  apply CommRingCat.hom_ext
  ext s
  rfl

/-- **The condition over the base.** Every chart morphism prescribed by `φ` commutes with the
structure morphisms to `S`. Over a terminal base it always holds. -/
def ChartMapsOver (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (φ : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) →+* globalFunctions B S hS X.1) : Prop :=
  ∀ V : SmallEtale B S hS X.1, chartMapOfGlobalHom B S hS X T φ V ≫ B.inclusion.map T.hom =
    B.inclusion.map ((SmallEtale.toOver B S hS X.1).obj V).hom

/-- Over a terminal base the condition `AlgebraicGeometry.Space.ChartMapsOver` is automatic. -/
lemma chartMapsOver_of_isTerminal (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    (hterminal : IsTerminal S) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (φ : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) →+* globalFunctions B S hS X.1) :
    ChartMapsOver B S hS X T φ :=
  fun _ => hterminal.hom_ext _ _

/-- The scheme morphism underlying a morphism of the site over `S` commutes with the structure
morphisms to `S`. -/
private lemma toScheme_map_comp_inclusion_map_hom {A T : BigFppfOver B S hS} (g : A ⟶ T) :
    (BigFppfOver.toScheme B S hS).map g ≫ B.inclusion.map T.hom = B.inclusion.map A.hom :=
  (B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map (Over.w g))

/-- The pullback homomorphism of a morphism to an affine object satisfies the condition over
the base. -/
lemma chartMapsOver_pullback (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (f : X ⟶ schemeSpace T) :
    ChartMapsOver B S hS X T (pullbackToGlobalFunctions B S hS X T f) := by
  intro V
  rw [chartMapOfGlobalHom_pullback]
  exact toScheme_map_comp_inclusion_map_hom B S hS _

/-- The chart morphism prescribed by `φ`, as a morphism of the site over `S`. -/
def chartOverMap (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (φ : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) →+* globalFunctions B S hS X.1)
    (h : ChartMapsOver B S hS X T φ) (V : SmallEtale B S hS X.1) :
    (SmallEtale.toOver B S hS X.1).obj V ⟶ T :=
  Over.homMk (B.inclusion.preimage (chartMapOfGlobalHom B S hS X T φ V))
    (B.inclusion.map_injective (by rw [Functor.map_comp, Functor.map_preimage]; exact h V))

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.chartOverMap`. -/
lemma toScheme_map_chartOverMap (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (φ : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) →+* globalFunctions B S hS X.1)
    (h : ChartMapsOver B S hS X T φ) (V : SmallEtale B S hS X.1) :
    (BigFppfOver.toScheme B S hS).map (chartOverMap B S hS X T φ h V) =
      chartMapOfGlobalHom B S hS X T φ V :=
  B.inclusion.map_preimage _

/-! ### Descent along an atlas -/

/-- The chart morphism prescribed by `φ` on the atlas of a presentation, as a morphism of the
site over `S`. -/
def atlasOverMap (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (φ : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) →+* globalFunctions B S hS X.1)
    (h : ChartMapsOver B S hS X T φ) (D : AtlasKernelPairData B S hS X) : D.U ⟶ T :=
  chartOverMap B S hS X T φ h (atlasChart B S hS X D)

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.atlasOverMap`. -/
lemma toScheme_map_atlasOverMap (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (φ : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) →+* globalFunctions B S hS X.1)
    (h : ChartMapsOver B S hS X T φ) (D : AtlasKernelPairData B S hS X) :
    (BigFppfOver.toScheme B S hS).map (atlasOverMap B S hS X T φ h D) =
      chartMapOfGlobalHom B S hS X T φ (atlasChart B S hS X D) :=
  B.inclusion.map_preimage _

/-- The chart morphism on the atlas of a presentation descends to a morphism of algebraic
spaces. -/
theorem exists_map_of_chartMapsOver (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (φ : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) →+* globalFunctions B S hS X.1)
    (h : ChartMapsOver B S hS X T φ) (D : AtlasKernelPairData B S hS X) :
    ∃ m : X ⟶ schemeSpace T,
      D.f ≫ m.hom = yoneda.map (atlasOverMap B S hS X T φ h D) := by
  let A := atlasChart B S hS X D
  -- the cocone condition
  have hcoc : D.t ≫ atlasOverMap B S hS X T φ h D = D.s ≫ atlasOverMap B S hS X T φ h D := by
    let AC : SmallEtale B S hS X.1 :=
      chartFromEtaleHom B S hS X D.R (yoneda.map D.t ≫ D.f)
        (chart_preimage_etale B S hS X D.f D.etale D.t D.tEtale)
    let tC : AC ⟶ A := ObjectProperty.homMk (CostructuredArrow.homMk D.t rfl)
    let sC : AC ⟶ A := ObjectProperty.homMk (CostructuredArrow.homMk D.s (by
      change yoneda.map D.s ≫ D.f = yoneda.map D.t ≫ D.f
      exact D.pullback.w.symm))
    apply Functor.map_injective (BigFppfOver.toScheme B S hS)
    rw [Functor.map_comp, Functor.map_comp, toScheme_map_atlasOverMap]
    exact (chartMapOfGlobalHom_comp B S hS X T φ tC).trans
      (chartMapOfGlobalHom_comp B S hS X T φ sC).symm
  let J := BigFppfOver.topology B S hS
  let TF : Sheaf J (Type u) := ⟨yoneda.obj T, (isAlgebraicSpace_yoneda B S hS T).isSheaf⟩
  obtain ⟨hRsh, hUsh, ⟨hc⟩⟩ := isCoequalizer_of_surjectiveEtale B S hS D.f D.t D.s D.pullback
    X.property D.surjective D.etale
  let RF : Sheaf J (Type u) := ⟨yoneda.obj D.R, hRsh⟩
  let UF : Sheaf J (Type u) := ⟨yoneda.obj D.U, hUsh⟩
  let sf : RF ⟶ UF := ⟨yoneda.map D.t⟩
  let tf : RF ⟶ UF := ⟨yoneda.map D.s⟩
  let k : UF ⟶ TF := ⟨yoneda.map (atlasOverMap B S hS X T φ h D)⟩
  have hw : sf ≫ k = tf ≫ k := by
    apply Sheaf.hom_ext
    change yoneda.map D.t ≫ yoneda.map (atlasOverMap B S hS X T φ h D) =
      yoneda.map D.s ≫ yoneda.map (atlasOverMap B S hS X T φ h D)
    rw [← Functor.map_comp, ← Functor.map_comp, hcoc]
  let c : Cofork sf tf := Cofork.ofπ k hw
  refine ⟨ObjectProperty.homMk (hc.desc c).hom, ?_⟩
  exact congrArg (fun q => q.hom) (hc.fac c WalkingParallelPair.one)

/-- A morphism descended from the chart morphisms of `φ` along an atlas restricts to the chart
morphism of `φ` on *every* étale chart. -/
lemma toScheme_map_preimage_of_chartMapsOver (X : AlgebraicSpaces B S hS)
    (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (φ : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) →+* globalFunctions B S hS X.1)
    (h : ChartMapsOver B S hS X T φ) (D : AtlasKernelPairData B S hS X)
    (m : X ⟶ schemeSpace T)
    (hm : D.f ≫ m.hom = yoneda.map (atlasOverMap B S hS X T φ h D))
    (V : SmallEtale B S hS X.1) :
    (BigFppfOver.toScheme B S hS).map (yoneda.preimage (V.1.hom ≫ m.hom)) =
      chartMapOfGlobalHom B S hS X T φ V := by
  classical
  let hrep := D.etale.1
  let i := hrep.fst' V.1.hom
  let j := hrep.snd V.1.hom
  let hp := hrep.isPullback' V.1.hom
  have hjEtale := D.etale.property V.1.hom (yoneda.map i) j hp
  let Wchart : SmallEtale B S hS X.1 :=
    chartFromEtaleHom B S hS X (hrep.pullback V.1.hom) (yoneda.map j ≫ V.1.hom)
      (chart_preimage_etale B S hS X V.1.hom V.2 j hjEtale)
  let A : SmallEtale B S hS X.1 := atlasChart B S hS X D
  let iC : Wchart ⟶ A := ObjectProperty.homMk (CostructuredArrow.homMk i hp.w)
  let jC : Wchart ⟶ V := ObjectProperty.homMk (CostructuredArrow.homMk j rfl)
  let vMap := yoneda.preimage (V.1.hom ≫ m.hom)
  have hlocal : j ≫ vMap = i ≫ atlasOverMap B S hS X T φ h D := by
    apply yoneda.map_injective
    rw [Functor.map_comp, Functor.map_comp, yoneda.map_preimage]
    change yoneda.map j ≫ V.1.hom ≫ m.hom = yoneda.map i ≫ yoneda.map _
    have h1 : yoneda.map j ≫ V.1.hom ≫ m.hom = (yoneda.map i ≫ D.f) ≫ m.hom := by
      rw [← Category.assoc, ← hp.w, Category.assoc]
    exact h1.trans ((Category.assoc _ _ _).trans (congrArg (fun q => yoneda.map i ≫ q) hm))
  have hlocalScheme := congrArg (BigFppfOver.toScheme B S hS).map hlocal
  rw [Functor.map_comp, Functor.map_comp, toScheme_map_atlasOverMap] at hlocalScheme
  have hcomp : (BigFppfOver.toScheme B S hS).map j ≫
      (BigFppfOver.toScheme B S hS).map vMap =
      (BigFppfOver.toScheme B S hS).map j ≫ chartMapOfGlobalHom B S hS X T φ V :=
    hlocalScheme.trans ((chartMapOfGlobalHom_comp B S hS X T φ iC).trans
      (chartMapOfGlobalHom_comp B S hS X T φ jC).symm)
  have : Surjective ((BigFppfOver.toScheme B S hS).map j) :=
    D.surjective.property V.1.hom (yoneda.map i) j hp
  have : Etale ((BigFppfOver.toScheme B S hS).map j) := hjEtale
  have : Epi ((BigFppfOver.toScheme B S hS).map j) :=
    AlgebraicGeometry.Flat.epi_of_flat_of_surjective _
  exact (cancel_epi ((BigFppfOver.toScheme B S hS).map j)).1 hcomp

/-- **A morphism into an affine object of the site is determined by its pullback on global
functions**, over an arbitrary base. -/
theorem pullbackToGlobalFunctions_injective (X : AlgebraicSpaces B S hS)
    (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] :
    Function.Injective (pullbackToGlobalFunctions B S hS X T) := by
  intro f g hfg
  let D := chosenAtlasKernelPair B S hS X
  let A := atlasChart B S hS X D
  have hchart := (chartMapOfGlobalHom_pullback B S hS X T f A).symm.trans
    ((congrArg (fun φ => chartMapOfGlobalHom B S hS X T φ A) hfg).trans
      (chartMapOfGlobalHom_pullback B S hS X T g A))
  have hbase : D.f ≫ f.hom = D.f ≫ g.hom := by
    have hpre : yoneda.preimage (D.f ≫ f.hom) = yoneda.preimage (D.f ≫ g.hom) :=
      Functor.map_injective (BigFppfOver.toScheme B S hS) hchart
    have h := congrArg yoneda.map hpre
    rwa [yoneda.map_preimage, yoneda.map_preimage] at h
  let J := BigFppfOver.topology B S hS
  obtain ⟨hRsh, hUsh, hc⟩ := isCoequalizer_of_surjectiveEtale B S hS D.f D.t D.s D.pullback
    X.property D.surjective D.etale
  let UF : Sheaf J (Type u) := ⟨yoneda.obj D.U, hUsh⟩
  let FF : Sheaf J (Type u) := ⟨X.1, X.property.isSheaf⟩
  let TF : Sheaf J (Type u) := ⟨yoneda.obj T, (isAlgebraicSpace_yoneda B S hS T).isSheaf⟩
  let ff : UF ⟶ FF := ⟨D.f⟩
  have _ : Epi ff := Cofork.IsColimit.epi (Classical.choice hc)
  have hsheaf : ff ≫ (⟨f.hom⟩ : FF ⟶ TF) = ff ≫ (⟨g.hom⟩ : FF ⟶ TF) :=
    Sheaf.hom_ext hbase
  exact ObjectProperty.hom_ext _ (congrArg (fun q => q.hom) ((cancel_epi ff).1 hsheaf))

/-- Every ring homomorphism satisfying the condition over the base is the pullback homomorphism
of a morphism of algebraic spaces. -/
theorem exists_pullbackToGlobalFunctions_eq (X : AlgebraicSpaces B S hS)
    (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (φ : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) →+* globalFunctions B S hS X.1)
    (h : ChartMapsOver B S hS X T φ) :
    ∃ m : X ⟶ schemeSpace T, pullbackToGlobalFunctions B S hS X T m = φ := by
  let D := chosenAtlasKernelPair B S hS X
  obtain ⟨m, hm⟩ := exists_map_of_chartMapsOver B S hS X T φ h D
  refine ⟨m, eq_of_chartMapOfGlobalHom_eq B S hS X T fun V => ?_⟩
  rw [chartMapOfGlobalHom_pullback]
  exact toScheme_map_preimage_of_chartMapsOver B S hS X T φ h D m hm V

/-! ### Stacks 05Z1 over an arbitrary base -/

/-- **Stacks 05Z1 over an arbitrary base.** Pullback of regular functions is a bijection
between morphisms of algebraic spaces `X ⟶ T` into an affine object of the site and the ring
homomorphisms `Γ(T, 𝒪_T) →+* Γ(X, 𝒪_X)` whose chart morphisms lie over `S`.

The forward map is pullback of functions on every étale chart of `X`. When `S` is terminal
the condition over `S` is automatic, by `AlgebraicGeometry.Space.chartMapsOver_of_isTerminal`,
and this recovers `AlgebraicGeometry.Space.morphismToAffineEquiv`. -/
def morphismToAffineEquivOfChartMapsOver (X : AlgebraicSpaces B S hS)
    (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] :
    { e : (X ⟶ schemeSpace T) ≃
        { φ : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) →+* globalFunctions B S hS X.1 //
          ChartMapsOver B S hS X T φ } //
      ∀ (f : X ⟶ schemeSpace T) (U : SmallEtale B S hS X.1)
        (s : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)),
        ((e f).1 s).1 (op U) = Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map
          (yoneda.preimage (U.1.hom ≫ f.hom)))) s } :=
  ⟨Equiv.ofBijective
      (fun f => ⟨pullbackToGlobalFunctions B S hS X T f, chartMapsOver_pullback B S hS X T f⟩)
      ⟨fun _ _ hfg => pullbackToGlobalFunctions_injective B S hS X T (congrArg Subtype.val hfg),
        fun φ => (exists_pullbackToGlobalFunctions_eq B S hS X T φ.1 φ.2).imp
          fun _ hm => Subtype.ext hm⟩,
    fun f U s => pullbackToGlobalFunctions_apply_chart B S hS X T f U s⟩

/-! ### Naturality of the pullback of functions -/

/-- Pullback of functions is natural in the target: composing with a morphism of the site
`w : W ⟶ V` composes the pullback homomorphism with pullback along `w`. This is the equation of
ring homomorphisms; its pointwise form is
`AlgebraicGeometry.Space.pullbackToGlobalFunctions_comp_schemeSpaceMap`. -/
lemma pullbackToGlobalFunctions_comp_schemeSpaceMap_eq_comp (X : AlgebraicSpaces B S hS)
    {V W : BigFppfOver B S hS} (w : W ⟶ V) (f : X ⟶ schemeSpace W) :
    pullbackToGlobalFunctions B S hS X V (f ≫ schemeSpaceMap w) =
      (pullbackToGlobalFunctions B S hS X W f).comp
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map w).op).hom := by
  refine RingHom.ext fun s ↦ Subtype.ext (funext fun U ↦ ?_)
  have hpre : yoneda.preimage (U.unop.1.hom ≫ f.hom ≫ yoneda.map w) =
      yoneda.preimage (U.unop.1.hom ≫ f.hom) ≫ w := by
    apply yoneda.map_injective
    rw [Functor.map_comp, yoneda.map_preimage, yoneda.map_preimage]
    exact (Category.assoc _ _ _).symm
  change Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map
      (yoneda.preimage (U.unop.1.hom ≫ f.hom ≫ yoneda.map w)))) s =
    Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map
      (yoneda.preimage (U.unop.1.hom ≫ f.hom))))
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map w).op s)
  rw [hpre, Functor.map_comp]
  rfl


/-- Pullback of a global function on an object `T` of the site along a morphism `f` from a
presheaf, as a compatible family of regular functions on *all* scheme charts of the presheaf. -/
def chartPullbackFunctions (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (T : BigFppfOver B S hS)
    (f : F ⟶ yoneda.obj T) :
    Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) →+* chartFunctions B S hS F where
  toFun r := ⟨fun j => (Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map
      (yoneda.preimage (j.unop.hom ≫ f))))).hom r, fun {j j'} g => by
    have hpre : yoneda.preimage (j'.unop.hom ≫ f) =
        g.unop.left ≫ yoneda.preimage (j.unop.hom ≫ f) := by
      apply yoneda.map_injective
      rw [Functor.map_comp, yoneda.map_preimage, yoneda.map_preimage, ← Category.assoc]
      exact congrArg (· ≫ f) (CostructuredArrow.w g.unop).symm
    change (Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map g.unop.left))).hom
        ((Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map
          (yoneda.preimage (j.unop.hom ≫ f))))).hom r) =
      (Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map
        (yoneda.preimage (j'.unop.hom ≫ f))))).hom r
    rw [hpre, Functor.map_comp]
    exact gamma_map_comp _ _ r⟩
  map_one' := Subtype.ext (funext fun _ => map_one _)
  map_mul' a b := Subtype.ext (funext fun _ => map_mul _ a b)
  map_zero' := Subtype.ext (funext fun _ => map_zero _)
  map_add' a b := Subtype.ext (funext fun _ => map_add _ a b)

/-- On the étale charts, the all-chart pullback family is the pullback homomorphism. -/
lemma chartFunctionsToSmall_chartPullbackFunctions (X : AlgebraicSpaces B S hS)
    (T : BigFppfOver B S hS) (f : X ⟶ schemeSpace T)
    (s : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) :
    chartFunctionsToSmall B S hS X.1 (chartPullbackFunctions B S hS X.1 T f.hom s) =
      pullbackToGlobalFunctions B S hS X T f s := by
  refine Subtype.ext (funext fun V => ?_)
  rw [pullbackToGlobalFunctions_apply_chart]
  rfl

/-- The comparison of global functions with all-chart families sends the pullback homomorphism
to the all-chart pullback family. -/
lemma globalFunctionsChartEquiv_pullbackToGlobalFunctions (X : AlgebraicSpaces B S hS)
    (T : BigFppfOver B S hS) (f : X ⟶ schemeSpace T)
    (s : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) :
    (globalFunctionsChartEquiv B S hS X).val (pullbackToGlobalFunctions B S hS X T f s) =
      chartPullbackFunctions B S hS X.1 T f.hom s :=
  chartFunctionsToSmall_injective B S hS X.1 X.property
    (((globalFunctionsChartEquiv B S hS X).property _).trans
      (chartFunctionsToSmall_chartPullbackFunctions B S hS X T f s).symm)

/-- Precomposing the all-chart pullback family along a morphism of presheaves. -/
lemma chartFunctionsMap_chartPullbackFunctions {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : G ⟶ F) (T : BigFppfOver B S hS) (f : F ⟶ yoneda.obj T)
    (s : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) :
    chartFunctionsMap B S hS g (chartPullbackFunctions B S hS F T f s) =
      chartPullbackFunctions B S hS G T (g ≫ f) s := by
  refine Subtype.ext (funext fun j => ?_)
  have h : (j.unop.hom ≫ g) ≫ f = j.unop.hom ≫ g ≫ f := Category.assoc _ _ _
  change (Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map
      (yoneda.preimage ((j.unop.hom ≫ g) ≫ f))))).hom s = _
  rw [h]
  rfl

/-- Pullback of functions is natural in the source: precomposing with a morphism of algebraic
spaces `g : X' ⟶ X` composes the pullback homomorphism with pullback of global functions along
`g`. -/
lemma pullbackToGlobalFunctions_comp_left {X X' : AlgebraicSpaces B S hS} (g : X' ⟶ X)
    (T : BigFppfOver B S hS) (f : X ⟶ schemeSpace T) :
    pullbackToGlobalFunctions B S hS X' T (g ≫ f) =
      (globalFunctionsMap B S hS g).comp (pullbackToGlobalFunctions B S hS X T f) := by
  refine RingHom.ext fun s => (globalFunctionsChartEquiv B S hS X').val.injective ?_
  rw [RingHom.comp_apply, globalFunctionsMap_chart,
    globalFunctionsChartEquiv_pullbackToGlobalFunctions,
    globalFunctionsChartEquiv_pullbackToGlobalFunctions]
  exact (chartFunctionsMap_chartPullbackFunctions B S hS g.hom T f.hom s).symm

/-! ### The relative form -/

/-- A ring homomorphism `Γ(W) →+* Γ(X)` extending the pullback `p^*` along `Γ(V) →+* Γ(W)`
satisfies the condition over the base: its chart morphisms lie over `V`, hence over `S`. -/
lemma chartMapsOver_of_comp_eq (X : AlgebraicSpaces B S hS) {V W : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W)] (w : W ⟶ V) (p : X ⟶ schemeSpace V)
    (φ : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) →+* globalFunctions B S hS X.1)
    (hφ : φ.comp (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map w).op).hom =
      pullbackToGlobalFunctions B S hS X V p) :
    ChartMapsOver B S hS X W φ := by
  intro U
  have h1 : chartMapOfGlobalHom B S hS X W φ U ≫ (BigFppfOver.toScheme B S hS).map w =
      (BigFppfOver.toScheme B S hS).map (yoneda.preimage (U.1.hom ≫ p.hom)) := by
    apply ext_of_isAffine
    rw [Scheme.Hom.comp_appTop, chartMapOfGlobalHom_appTop]
    apply CommRingCat.hom_ext
    ext s
    exact congrArg (fun ψ => (ψ s).1 (op U)) hφ
  rw [← toScheme_map_comp_inclusion_map_hom B S hS w, ← Category.assoc, h1]
  exact toScheme_map_comp_inclusion_map_hom B S hS _

/-- **Morphisms from an algebraic space into an affine object over an affine object.** Let
`w : W ⟶ V` be a morphism of objects of the big fppf site of `S` with affine underlying
schemes, and `p : X ⟶ V` a morphism from an algebraic space. Pullback of functions is a
bijection between the morphisms `f : X ⟶ W` over `V` and the ring homomorphisms
`φ : Γ(W) →+* Γ(X)` with `φ ∘ w^* = p^*`, that is, the `Γ(V)`-algebra homomorphisms.

No hypothesis is put on `S`. The bijection is natural in `X` by
`AlgebraicGeometry.Space.pullbackToGlobalFunctions_comp_left`. -/
def morphismToAffineOverEquiv (X : AlgebraicSpaces B S hS) {V W : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W)] (w : W ⟶ V) (p : X ⟶ schemeSpace V) :
    { e : { f : X ⟶ schemeSpace W // f ≫ schemeSpaceMap w = p } ≃
        { φ : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) →+* globalFunctions B S hS X.1 //
          φ.comp (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map w).op).hom =
            pullbackToGlobalFunctions B S hS X V p } //
      ∀ f, (e f).1 = pullbackToGlobalFunctions B S hS X W f.1 } :=
  ⟨Equiv.ofBijective
      (fun f => ⟨pullbackToGlobalFunctions B S hS X W f.1, by
        rw [← pullbackToGlobalFunctions_comp_schemeSpaceMap_eq_comp, f.2]⟩)
      ⟨fun f g hfg => Subtype.ext
          (pullbackToGlobalFunctions_injective B S hS X W (congrArg Subtype.val hfg)),
        fun φ => by
          obtain ⟨m, hm⟩ := exists_pullbackToGlobalFunctions_eq B S hS X W φ.1
            (chartMapsOver_of_comp_eq B S hS X w p φ.1 φ.2)
          refine ⟨⟨m, pullbackToGlobalFunctions_injective B S hS X V ?_⟩, Subtype.ext hm⟩
          rw [pullbackToGlobalFunctions_comp_schemeSpaceMap_eq_comp, hm]
          exact φ.2⟩,
    fun _ => rfl⟩

end AlgebraicGeometry.Space

end
