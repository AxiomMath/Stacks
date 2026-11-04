module

public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.RepresentedFibreComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceRepresentedFinitePushforward
public import StacksFrontier.AlgebraicGeometry.Divisors.RelativeWeakAssassin.FinitePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpBaseChange

/-!
# Affine base change of a finite direct image on represented algebraic spaces

Let `b : W ⟶ V` and `q : U ⟶ V` be morphisms of the big fppf category over `S` with the scheme
underlying `b` finite, let `P = U ×_V W` be their fibre product in the site and let `G` be a
quasi-coherent `𝒪`-module on the algebraic space `W` represents. The weakly associated points of
the inverse image along `q` of the direct image along `b` of `G` are the images, under the
projection `P ⟶ U`, of the weakly associated points of the inverse image of `G` along `P ⟶ W`.

This is **the base-change assertion of Stacks 02KG read on weakly associated points, for
represented algebraic spaces**. No étale hypothesis is placed on `q`: all four corners are
schemes of the site, so the comparison the statement needs is the scheme-level affine base
change, `Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom`,
in the packaged form `AlgebraicGeometry.pullbackPushforwardFiberIso`.

## Main results

* `AlgebraicGeometry.Space.weaklyAssociatedPoints_eq_preimage_representedChartModule`: on a
  represented algebraic space the weakly associated points of a quasi-coherent module are the
  preimage, under the comparison bijection of Stacks 03BV, of the Zariski weak assassin of the
  chart restriction.
* `Space.weaklyAssociatedPoints_modulePullback_modulePushforward_representedSpaceMap`: the
  statement above.

## Implementation notes

Both sides are carried onto the representing schemes by
`AlgebraicGeometry.Space.isWeaklyAssociatedPoint_iff_restrictToChartScheme_idEtaleChart`,
Stacks 0CTW on a represented algebraic space, whose only hypothesis is quasi-coherence of the
module. The chart restriction commutes with base change along a morphism of the site by
`AlgebraicGeometry.Space.nonempty_restrictToChartScheme_baseChange_of_isQuasicoherent`, and the
chart restriction of a direct image along a morphism of represented spaces is the scheme-level
direct image of the chart restriction by
`AlgebraicGeometry.Space.restrictToChartSchemePushforwardIdEtaleChartIso'`. What is left is a
statement about schemes alone: affine base change, then Stacks 05EZ.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 05EZ](https://stacks.math.columbia.edu/tag/05EZ)
* [Stacks Project, Tag 0CTW](https://stacks.math.columbia.edu/tag/0CTW)
* [Stacks Project, Tag 03BV](https://stacks.math.columbia.edu/tag/03BV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance] AlgebraicGeometry.BigFppfSite.hasPullbacks_schemes

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The preimage under the comparison bijection of Stacks 03BV of the image of a set of scheme
points along a morphism of the site is the image of its preimage along the induced map on
points. -/
theorem preimage_pointsToScheme_image_toScheme_map {U W : BigFppfOver B S hS} (b : W ⟶ U)
    (T : Set ((BigFppfOver.toScheme B S hS).obj W)) :
    pointsToScheme B S hS U ⁻¹' ((BigFppfOver.toScheme B S hS).map b '' T) =
      pointsMap B S hS (yoneda.obj W) (yoneda.map b) '' (pointsToScheme B S hS W ⁻¹' T) := by
  ext u
  constructor
  · rintro ⟨s, hs, hsu⟩
    obtain ⟨w, rfl⟩ := surjective_pointsToScheme B S hS W s
    exact ⟨w, hs, injective_pointsToScheme B S hS U
      ((pointsToScheme_pointsMap_yoneda B S hS b w).trans hsu)⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨pointsToScheme B S hS W w, hw, (pointsToScheme_pointsMap_yoneda B S hS b w).symm⟩

/-- **Stacks 0CTW on a represented algebraic space, read on sets.** The weakly associated points
of a quasi-coherent module on a represented algebraic space are the preimage, under the
comparison bijection of Stacks 03BV, of the Zariski weak assassin of its chart restriction. -/
theorem weaklyAssociatedPoints_eq_preimage_representedChartModule (T : BigFppfOver B S hS)
    (G : Modules.{u, u} B S hS (yoneda.obj T)
      (_root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T))
    (hG : G.IsQuasicoherentOnSite) :
    weaklyAssociatedPoints B S hS
        ⟨yoneda.obj T, _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩ G =
      pointsToScheme B S hS T ⁻¹'
        Stacks.Divisors.weaklyAssociatedPoints (representedChartModule B S hS G) :=
  Set.ext fun t ↦
    isWeaklyAssociatedPoint_iff_restrictToChartScheme_idEtaleChart B S hS T G hG t

/-- **Affine base change of a finite direct image on represented algebraic spaces, on weakly
associated points.** Let `b : W ⟶ V` have finite underlying morphism of schemes, let
`q : U ⟶ V` be arbitrary, let `P` present the fibre product `U ×_V W` in the site and let `G` be
a quasi-coherent `𝒪`-module on the algebraic space `W` represents. Then

`WeakAss(q^*(b_*G)) = |P ⟶ U| (WeakAss((P ⟶ W)^*G))`.

The four corners are schemes of the site, so the comparison of the two sides is the scheme-level
affine base change of Stacks 02KG and no étale hypothesis on `q` is needed. -/
theorem weaklyAssociatedPoints_modulePullback_modulePushforward_representedSpaceMap
    {U V W P : BigFppfOver B S hS} (q : U ⟶ V) (b : W ⟶ V) (b' : P ⟶ U) (c' : P ⟶ W)
    (hsq : IsPullback c' b' b q)
    (hb : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map b))
    (G : Modules.{u, u} B S hS (yoneda.obj W)
      (_root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS W))
    (hG : G.IsQuasicoherentOnSite) :
    weaklyAssociatedPoints B S hS
        ⟨yoneda.obj U, _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U⟩
        ((modulePullback B S hS (representedSpaceMap B S hS q)).obj
          ((modulePushforward B S hS (representedSpaceMap B S hS b)).obj G)) =
      pointsMap B S hS (yoneda.obj P) (yoneda.map b') ''
        weaklyAssociatedPoints B S hS
          ⟨yoneda.obj P, _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS P⟩
          ((modulePullback B S hS (representedSpaceMap B S hS c')).obj G) := by
  have hbfin' : _root_.AlgebraicGeometry.IsFinite
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) b.left) := hb
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  have hsqS : IsPullback ((BigFppfOver.toScheme B S hS).map c')
      ((BigFppfOver.toScheme B S hS).map b') ((BigFppfOver.toScheme B S hS).map b)
      ((BigFppfOver.toScheme B S hS).map q) := hsq.map (BigFppfOver.toScheme B S hS)
  have hb'fin : _root_.AlgebraicGeometry.IsFinite
      ((BigFppfOver.toScheme B S hS).map b') :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsqS hb
  have hGsqc : (representedChartModule B S hS G).IsQuasicoherent :=
    (isQuasicoherent_restrictToChart_iff B S hS
      (_root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS W) G
      (idEtaleChart B S hS W)).1
      (isQuasicoherent_restrictToChart B S hS
        ⟨yoneda.obj W, _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS W⟩ G hG
        (idEtaleChart B S hS W))
  have hM : ((modulePushforward B S hS (representedSpaceMap B S hS b)).obj
      G).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePushforward_representedSpaceMap B S hS b G hG
  have hN : ((modulePullback B S hS (representedSpaceMap B S hS q)).obj
      ((modulePushforward B S hS (representedSpaceMap B S hS b)).obj
        G)).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      (representedSpaceMap B S hS q) _ hM
  have hGc' : ((modulePullback B S hS (representedSpaceMap B S hS c')).obj
      G).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      (representedSpaceMap B S hS c') G hG
  have hpbqc : (((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map c')).obj
      (representedChartModule B S hS G))).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback ((BigFppfOver.toScheme B S hS).map c')
      (representedChartModule B S hS G) inferInstance
  let d : _root_.AlgebraicGeometry.BaseChangeDiagram.{u} :=
    { X' := (BigFppfOver.toScheme B S hS).obj P
      X := (BigFppfOver.toScheme B S hS).obj W
      S' := (BigFppfOver.toScheme B S hS).obj U
      S := (BigFppfOver.toScheme B S hS).obj V
      g' := (BigFppfOver.toScheme B S hS).map c'
      f' := (BigFppfOver.toScheme B S hS).map b'
      f := (BigFppfOver.toScheme B S hS).map b
      g := (BigFppfOver.toScheme B S hS).map q
      isPullback := hsqS
      F := representedChartModule B S hS G }
  have : _root_.AlgebraicGeometry.IsAffineHom d.f :=
    inferInstanceAs (_root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map b))
  have echart : representedChartModule B S hS
        ((modulePullback B S hS (representedSpaceMap B S hS q)).obj
          ((modulePushforward B S hS (representedSpaceMap B S hS b)).obj G)) ≅
      (Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map b')).obj
        ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map c')).obj
          (representedChartModule B S hS G)) :=
    (nonempty_restrictToChartScheme_baseChange_of_isQuasicoherent q _ hM).some ≪≫
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map q)).mapIso
          (restrictToChartSchemePushforwardIdEtaleChartIso' B S hS b G) ≪≫
        _root_.AlgebraicGeometry.pullbackPushforwardFiberIso d
  have echart' : representedChartModule B S hS
        ((modulePullback B S hS (representedSpaceMap B S hS c')).obj G) ≅
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map c')).obj
        (representedChartModule B S hS G) :=
    (nonempty_restrictToChartScheme_baseChange_of_isQuasicoherent c' G hG).some
  rw [weaklyAssociatedPoints_eq_preimage_representedChartModule B S hS U _ hN,
    weaklyAssociatedPoints_eq_preimage_representedChartModule B S hS P _ hGc',
    ← preimage_pointsToScheme_image_toScheme_map B S hS b',
    _root_.AlgebraicGeometry.weaklyAssociatedPoints_congr echart,
    _root_.AlgebraicGeometry.weaklyAssociatedPoints_congr echart',
    _root_.AlgebraicGeometry.weaklyAssociatedPoints_pushforward_eq_image_of_isFinite]

/-- For a cartesian square of algebraic spaces with étale top edge `κ`, a point `ω` of `U'` maps
under `c` into the image along `iT` of the weakly associated points of `H` exactly when `ω` lies in
the image along `f` of the weakly associated points of `κ^*H`. -/
theorem mem_image_weaklyAssociatedPoints_iff_of_isPullback {P' TZ U' T : AlgebraicSpaces B S hS}
    {κ : P' ⟶ TZ} {f : P' ⟶ U'} {iT : TZ ⟶ T} {c : U' ⟶ T} (h : IsPullback κ f iT c)
    (hκ : IsEtale B S hS κ.hom) (H : Modules.{u, u} B S hS TZ.1 TZ.2) (ω : points B S hS U'.1) :
    pointsMap B S hS U'.1 c.hom ω ∈
        pointsMap B S hS TZ.1 iT.hom '' weaklyAssociatedPoints B S hS TZ H ↔
      ω ∈ pointsMap B S hS P'.1 f.hom ''
        weaklyAssociatedPoints B S hS P' ((modulePullback B S hS κ).obj H) := by
  constructor
  · rintro ⟨z, hz, hzω⟩
    obtain ⟨ζ, hζz, hζω⟩ := exists_point_of_isPullback B S hS h z ω hzω
    exact ⟨ζ, (isWeaklyAssociatedPoint_modulePullback_iff B S hS κ hκ H ζ).2 (hζz ▸ hz), hζω⟩
  · rintro ⟨ζ, hζ, rfl⟩
    exact ⟨pointsMap B S hS P'.1 κ.hom ζ,
      (isWeaklyAssociatedPoint_modulePullback_iff B S hS κ hκ H ζ).1 hζ,
      pointsMap_apply_comm B S hS
        (show κ.hom ≫ iT.hom = f.hom ≫ c.hom from congrArg (fun k ↦ k.hom) h.w) ζ⟩

/-! ### Affine base change of a finite direct image, for an arbitrary base change -/

/-- Given a cartesian square `jZ, iT` over `i, π`, a cartesian square `jS, b` over `i, g` and a
cartesian square `s, f` over `b, q`, any `φ` with `φ ≫ π = q ≫ g` lifts to a map `κ` into the top
left corner making the square `κ, f` over `iT, φ` cartesian. -/
theorem _root_.CategoryTheory.IsPullback.exists_lift_isPullback {C : Type*} [Category C]
    {TZ Z T X P W U V : C} {jZ : TZ ⟶ Z} {iT : TZ ⟶ T} {i : Z ⟶ X} {π : T ⟶ X}
    (sq : IsPullback jZ iT i π) {jS : W ⟶ Z} {b : W ⟶ V} {g : V ⟶ X}
    (sqZ : IsPullback jS b i g) {s : P ⟶ W} {f : P ⟶ U} {q : U ⟶ V}
    (sqP : IsPullback s f b q) {φ : U ⟶ T} (hφ : φ ≫ π = q ≫ g) :
    ∃ κ : P ⟶ TZ, κ ≫ jZ = s ≫ jS ∧ IsPullback κ f iT φ := by
  have h := sqP.paste_horiz sqZ
  refine ⟨sq.lift (s ≫ jS) (f ≫ φ) (by simpa [hφ] using h.w), sq.lift_fst _ _ _,
    IsPullback.of_right ?_ (sq.lift_snd _ _ _) sq⟩
  rwa [sq.lift_fst, hφ]

/-- **Stacks 03LX on an étale chart.** For a cartesian square `jS, b` over `i, gX` with `gX` an
étale chart and `φ ≫ π = q ≫ gX`, the weakly associated points of `φ^*(π^*(i_*G))` are those of
`q^*(b_*(jS^*G))`. -/
theorem weaklyAssociatedPoints_modulePullback_modulePullback_modulePushforward_eq
    {T X Z : AlgebraicSpaces B S hS} {U₀ V₀ W₀ : BigFppfOver B S hS} {π : T ⟶ X} {i : Z ⟶ X}
    {q : U₀ ⟶ V₀} {b : W₀ ⟶ V₀}
    {gX : (⟨yoneda.obj V₀, _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V₀⟩ :
      AlgebraicSpaces B S hS) ⟶ X}
    {jS : (⟨yoneda.obj W₀, _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS W₀⟩ :
      AlgebraicSpaces B S hS) ⟶ Z}
    {φ : (⟨yoneda.obj U₀, _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U₀⟩ :
      AlgebraicSpaces B S hS) ⟶ T}
    (sqZS : IsPullback jS (representedSpaceMap B S hS b) i gX) (hgX : IsEtale B S hS gX.hom)
    (hcomm : φ ≫ π = representedSpaceMap B S hS q ≫ gX) (G : Modules.{u, u} B S hS Z.1 Z.2) :
    weaklyAssociatedPoints B S hS
        ⟨yoneda.obj U₀, _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U₀⟩
        ((modulePullback B S hS φ).obj
          ((modulePullback B S hS π).obj ((modulePushforward B S hS i).obj G))) =
      weaklyAssociatedPoints B S hS
        ⟨yoneda.obj U₀, _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U₀⟩
        ((modulePullback B S hS (representedSpaceMap B S hS q)).obj
          ((modulePushforward B S hS (representedSpaceMap B S hS b)).obj
            ((modulePullback B S hS jS).obj G))) := by
  have hjS : IsEtale B S hS jS.hom :=
    isEtale_of_isPullback B S hS (representedSpaceMap B S hS b) jS gX i sqZS.flip hgX
  -- Stacks 03LX: the restriction of `i_*G` to the chart is the direct image along `W ⟶ V`
  have e03LX : (modulePullback B S hS gX).obj ((modulePushforward B S hS i).obj G) ≅
      (modulePushforward B S hS (representedSpaceMap B S hS b)).obj
        ((modulePullback B S hS jS).obj G) :=
    ((modulePullbackIsoEtaleModulePullback B S hS gX hgX).app
        ((modulePushforward B S hS i).obj G)) ≪≫
      ((modulePushforwardEtaleBaseChangeIso B S hS jS (representedSpaceMap B S hS b) i gX
        sqZS hgX).app G).symm ≪≫
      (modulePushforward B S hS (representedSpaceMap B S hS b)).mapIso
        ((modulePullbackIsoEtaleModulePullback B S hS jS hjS).app G).symm
  exact Set.ext (isWeaklyAssociatedPoint_congr B S hS
    (((modulePullbackCompIso B S hS φ π).app ((modulePushforward B S hS i).obj G)) ≪≫
      eqToIso (congrArg (fun k ↦ (modulePullback B S hS k).obj
        ((modulePushforward B S hS i).obj G)) hcomm) ≪≫
      ((modulePullbackCompIso B S hS (representedSpaceMap B S hS q) gX).app
        ((modulePushforward B S hS i).obj G)).symm ≪≫
      (modulePullback B S hS (representedSpaceMap B S hS q)).mapIso e03LX))

/-- **Stacks 02KG on weakly associated points, on an étale chart.** Let `jZ, iT` over `i, π` be a
cartesian square of algebraic spaces, let `jS, b` over `i, gX` be its base change to an étale chart
`gX` with `b` finite, and let `φ` be étale with `φ ≫ π = q ≫ gX`. Then a point of the source of
`φ` maps into the weakly associated points of `π^*(i_*G)` exactly when it maps into the image under
`iT` of the weakly associated points of `jZ^*G`. -/
theorem pointsMap_mem_weaklyAssociatedPoints_modulePullback_modulePushforward_iff
    {T TZ X Z : AlgebraicSpaces B S hS} {U₀ V₀ W₀ : BigFppfOver B S hS} {π : T ⟶ X} {i : Z ⟶ X}
    {iT : TZ ⟶ T} {jZ : TZ ⟶ Z} (sq : IsPullback jZ iT i π) {q : U₀ ⟶ V₀} {b : W₀ ⟶ V₀}
    (hb : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map b))
    {gX : (⟨yoneda.obj V₀, _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V₀⟩ :
      AlgebraicSpaces B S hS) ⟶ X}
    {jS : (⟨yoneda.obj W₀, _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS W₀⟩ :
      AlgebraicSpaces B S hS) ⟶ Z}
    {φ : (⟨yoneda.obj U₀, _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U₀⟩ :
      AlgebraicSpaces B S hS) ⟶ T}
    (sqZS : IsPullback jS (representedSpaceMap B S hS b) i gX) (hgX : IsEtale B S hS gX.hom)
    (hφ : IsEtale B S hS φ.hom) (hcomm : φ ≫ π = representedSpaceMap B S hS q ≫ gX)
    (G : Modules.{u, u} B S hS Z.1 Z.2) (hG : G.IsQuasicoherentOnSite)
    (ω : points B S hS (yoneda.obj U₀)) :
    pointsMap B S hS (yoneda.obj U₀) φ.hom ω ∈ weaklyAssociatedPoints B S hS T
        ((modulePullback B S hS π).obj ((modulePushforward B S hS i).obj G)) ↔
      pointsMap B S hS (yoneda.obj U₀) φ.hom ω ∈ pointsMap B S hS TZ.1 iT.hom ''
        weaklyAssociatedPoints B S hS TZ ((modulePullback B S hS jZ).obj G) := by
  have hsqP : IsPullback (pullback.snd q b) (pullback.fst q b) b q :=
    (IsPullback.of_hasPullback q b).flip
  have hsqPS : IsPullback (representedSpaceMap B S hS (pullback.snd q b))
      (representedSpaceMap B S hS (pullback.fst q b)) (representedSpaceMap B S hS b)
      (representedSpaceMap B S hS q) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι fun F ↦ IsAlgebraicSpace B S hS F)
      (hsqP.map yoneda)
  obtain ⟨κ, hκjZ, hκsq⟩ := sq.exists_lift_isPullback sqZS hsqPS hcomm
  have hκ : IsEtale B S hS κ.hom :=
    isEtale_of_isPullback B S hS (representedSpaceMap B S hS (pullback.fst q b)) κ φ iT
      hκsq.flip hφ
  have eP : (modulePullback B S hS (representedSpaceMap B S hS (pullback.snd q b))).obj
        ((modulePullback B S hS jS).obj G) ≅
      (modulePullback B S hS κ).obj ((modulePullback B S hS jZ).obj G) :=
    ((modulePullbackCompIso B S hS
        (representedSpaceMap B S hS (pullback.snd q b)) jS).app G) ≪≫
      eqToIso (congrArg (fun k ↦ (modulePullback B S hS k).obj G) hκjZ.symm) ≪≫
      ((modulePullbackCompIso B S hS κ jZ).app G).symm
  have hR := weaklyAssociatedPoints_modulePullback_modulePushforward_representedSpaceMap
    B S hS q b (pullback.fst q b) (pullback.snd q b) hsqP hb
    ((modulePullback B S hS jS).obj G)
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS jS G hG)
  refine ((isWeaklyAssociatedPoint_modulePullback_iff B S hS φ hφ _ ω).symm.trans
    ((Set.ext_iff.1 (weaklyAssociatedPoints_modulePullback_modulePullback_modulePushforward_eq
      B S hS sqZS hgX hcomm G) ω).trans ?_)).trans
    (mem_image_weaklyAssociatedPoints_iff_of_isPullback B S hS hκsq hκ _ ω).symm
  exact (Set.ext_iff.1 hR ω).trans
    (exists_congr fun p ↦ and_congr_left' (isWeaklyAssociatedPoint_congr B S hS eP p))

/-- **The base-change assertion of Stacks 02KG on weakly associated points, for a finite
morphism of algebraic spaces and an arbitrary base change.**  Let

```
T_Z --jZ--> Z
|iT          |i
T ---π--->   X
```

be a cartesian square of algebraic spaces over `S` with `i` finite, and let `G` be a
quasi-coherent `𝒪_Z`-module.  Then the weakly associated points of `π^*(i_*G)` are the images
under `iT` of the weakly associated points of `jZ^*G`.

No hypothesis is placed on `π`.  The reduction is the source's own étale localization: an affine
étale chart `V ⟶ X` through the image of the point under consideration, an étale chart `U` of
`T ×_X V` through a point above it — so that `U ⟶ V` is a morphism of the site — and the base
change of `i` to `V`, which finiteness of `i` presents by an affine object `W` of the site finite
over `V`.  Weak association is read on `U` by Stacks 0CUU, the restriction of `i_*G` to `V` is
the direct image along `W ⟶ V` by Stacks 03LX, and what is left is the represented statement
`Space.weaklyAssociatedPoints_modulePullback_modulePushforward_representedSpaceMap` on the square
of schemes of the site over `U ⟶ V`. -/
theorem weaklyAssociatedPoints_modulePullback_modulePushforward_of_isFinite
    {T TZ X Z : AlgebraicSpaces B S hS} (π : T ⟶ X) (i : Z ⟶ X) (iT : TZ ⟶ T) (jZ : TZ ⟶ Z)
    (sq : IsPullback jZ iT i π) (hi : IsFinite B S hS i.hom)
    (G : Modules.{u, u} B S hS Z.1 Z.2) (hG : G.IsQuasicoherentOnSite) :
    weaklyAssociatedPoints B S hS T
        ((modulePullback B S hS π).obj ((modulePushforward B S hS i).obj G)) =
      pointsMap B S hS TZ.1 iT.hom ''
        weaklyAssociatedPoints B S hS TZ ((modulePullback B S hS jZ).obj G) := by
  refine Set.ext fun θ ↦ ?_
  obtain ⟨V₀, cX, hV₀, hcX, v, hv⟩ :=
    exists_affine_etale_chart_at_point B S hS X.1 X.2 (pointsMap B S hS T.1 π.hom θ)
  let gX : (⟨yoneda.obj V₀, _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V₀⟩ :
    AlgebraicSpaces B S hS) ⟶ X := ObjectProperty.homMk cX
  have hgX : IsEtale B S hS gX.hom := (isEtale_iff_presheaf_of_yoneda B S hS cX).2 hcX
  let rV : AlgebraicSpaces.fiberProduct B S hS gX π ⟶
    (⟨yoneda.obj V₀, _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V₀⟩ :
      AlgebraicSpaces B S hS) := ObjectProperty.homMk (pullback.fst gX.hom π.hom)
  let pT : AlgebraicSpaces.fiberProduct B S hS gX π ⟶ T :=
    ObjectProperty.homMk (pullback.snd gX.hom π.hom)
  have sqT : IsPullback pT rV π gX :=
    (AlgebraicSpaces.isPullback_fiberProduct B S hS gX π).flip
  obtain ⟨θ', hθ'V, hθ'T⟩ := exists_point_of_isPullback B S hS sqT.flip v θ hv
  obtain ⟨U₀, cT, hU₀, hcT, ω, hω⟩ := exists_affine_etale_chart_at_point B S hS
    (AlgebraicSpaces.fiberProduct B S hS gX π).1 (AlgebraicSpaces.fiberProduct B S hS gX π).2 θ'
  let ψ : (⟨yoneda.obj U₀, _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U₀⟩ :
    AlgebraicSpaces B S hS) ⟶ AlgebraicSpaces.fiberProduct B S hS gX π :=
    ObjectProperty.homMk cT
  have hcU : IsEtale B S hS (ψ ≫ pT).hom :=
    isEtale_comp B S hS ((isEtale_iff_presheaf_of_yoneda B S hS cT).2 hcT)
      (isEtale_of_isPullback B S hS rV pT gX π sqT.flip hgX)
  have hωθ : pointsMap B S hS (yoneda.obj U₀) (ψ ≫ pT).hom ω = θ := by
    rw [show (ψ ≫ pT).hom = ψ.hom ≫ pT.hom from rfl, pointsMap_comp_apply]
    exact (congrArg (pointsMap B S hS _ pT.hom) hω).trans hθ'T
  obtain ⟨q, hq⟩ : ∃ q : U₀ ⟶ V₀, yoneda.map q = (ψ ≫ rV).hom :=
    ⟨yoneda.preimage (ψ ≫ rV).hom, yoneda.map_preimage _⟩
  have hρ : representedSpaceMap B S hS q = ψ ≫ rV := ObjectProperty.hom_ext _ hq
  have hcomm : (ψ ≫ pT) ≫ π = representedSpaceMap B S hS q ≫ gX := by
    rw [hρ, Category.assoc, Category.assoc, sqT.w]
  obtain ⟨W₀, b, jW, hW₀, hbfin, sqZ⟩ := hi V₀ hV₀ cX
  let jS : (⟨yoneda.obj W₀, _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS W₀⟩ :
    AlgebraicSpaces B S hS) ⟶ Z := ObjectProperty.homMk jW
  have sqZS : IsPullback jS (representedSpaceMap B S hS b) i gX :=
    IsPullback.of_map_of_faithful
      (ObjectProperty.ι fun F ↦ IsAlgebraicSpace B S hS F) sqZ
  rw [← hωθ]
  exact pointsMap_mem_weaklyAssociatedPoints_modulePullback_modulePushforward_iff B S hS sq hbfin
    sqZS hgX hcU hcomm G hG ω

end AlgebraicGeometry.Space

end
