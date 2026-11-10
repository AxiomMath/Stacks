module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatStein.Core
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatStein.FibreCount
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatStein.Splitting
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatStein.Pieces
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatStein.LocalCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPointOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.GeometricallyReduced
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceGammaFullyFaithful
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource

/-!
# Shrinking a split chart of the Stein factorization

The second step of the proof of Stacks 0E0D, and its conclusion.  Let `f = f' ≫ π : X ⟶ Y` be
proper, flat, of finite presentation, with geometrically reduced fibres, where `f'` has connected
geometric fibres and `𝒪_{Y'} = f'_*𝒪_X`.  Over an étale chart of `Y` on which the base change of
`π` splits into open and closed pieces, each piece maps isomorphically onto a basic open of the
chart, so that `π` is finite étale over it.

## Main results

* `AlgebraicGeometry.Space.ProperFlatStein.isIso_restrictSiteMap_piece`: over a basic open where
  the geometric fibres of a piece are connected, the piece maps isomorphically onto the basic
  open.
* `AlgebraicGeometry.Space.ProperFlatStein.exists_finite_etale_chart_of_split`: a split affine
  chart can be shrunk to an étale chart over which `π` is finite étale.
* `AlgebraicGeometry.Space.ProperFlatStein.isFinite_and_isEtale_of_stein_of_inputs`: `π` is
  finite and étale.

## References

* [Stacks Project, Tag 0E0D](https://stacks.math.columbia.edu/tag/0E0D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.ProperFlatStein

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The restriction `f⁻¹(W) ⟶ W` of a morphism `f : T ⟶ U` of the site over an open `W` of `U`,
as a morphism between the open subobjects of the site. -/
noncomputable def restrictSiteMap {T U : BigFppfOver B S hS} (f : T ⟶ U)
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    opensSiteObject B S hS T ((BigFppfOver.toScheme B S hS).map f ⁻¹ᵁ W) ⟶
      opensSiteObject B S hS U W :=
  Over.homMk (⟨(BigFppfOver.toScheme B S hS).map f ∣_ W⟩ : B.obj _ ⟶ B.obj _) (by
    apply ObjectProperty.hom_ext
    change ((BigFppfOver.toScheme B S hS).map f ∣_ W) ≫ (opensSiteObject B S hS U W).hom.hom =
      (opensSiteObject B S hS T ((BigFppfOver.toScheme B S hS).map f ⁻¹ᵁ W)).hom.hom
    rw [hom_opensSiteObject, hom_opensSiteObject, ← Category.assoc, morphismRestrict_ι,
      Category.assoc]
    exact congrArg (fun k => _ ≫ k) (congrArg (fun k => k.hom) (Over.w f)))

/-- The scheme morphism underlying `restrictSiteMap B S hS f W` is the restriction of the scheme
morphism of `f` over `W`. -/
@[simp]
theorem toScheme_map_restrictSiteMap {T U : BigFppfOver B S hS} (f : T ⟶ U)
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    (BigFppfOver.toScheme B S hS).map (restrictSiteMap B S hS f W) =
      (BigFppfOver.toScheme B S hS).map f ∣_ W :=
  rfl

/-- The square of the site exhibiting `f⁻¹(W)` as the base change of `f` along `W ⊆ U`. -/
theorem isPullback_restrictSiteMap {T U : BigFppfOver B S hS} (f : T ⟶ U)
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    IsPullback (opensSiteObjectInclusion B S hS T ((BigFppfOver.toScheme B S hS).map f ⁻¹ᵁ W))
      (restrictSiteMap B S hS f W) f (opensSiteObjectInclusion B S hS U W) := by
  have h := (isPullback_morphismRestrict ((BigFppfOver.toScheme B S hS).map f) W).flip
  rw [← map_opensSiteObjectInclusion, ← map_opensSiteObjectInclusion,
    ← toScheme_map_restrictSiteMap] at h
  exact IsPullback.of_map (BigFppfOver.toScheme B S hS)
    ((BigFppfOver.toScheme B S hS).map_injective (by
      rw [Functor.map_comp, Functor.map_comp]
      exact h.w)) h

/-- A property of morphisms of algebraic spaces which is stable under base change passes from
`f` to `snd` along any cartesian square of presheaves of algebraic spaces. -/
theorem prop_snd_of_isPullback_algebraicSpaces
    (P : MorphismProperty (AlgebraicSpaces B S hS)) (hPbc : P.IsStableUnderBaseChange)
    {W X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS W)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) {fst : W ⟶ X} {snd : W ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ Y}
    (sq : IsPullback fst snd f g)
    (hf : P (ObjectProperty.homMk (X := (⟨X, hX⟩ : AlgebraicSpaces B S hS))
      (Y := ⟨Y, hY⟩) f)) :
    P (ObjectProperty.homMk (X := (⟨W, hW⟩ : AlgebraicSpaces B S hS)) (Y := ⟨Z, hZ⟩) snd) := by
  have sq' : IsPullback
      (ObjectProperty.homMk (X := (⟨W, hW⟩ : AlgebraicSpaces B S hS)) (Y := ⟨X, hX⟩) fst)
      (ObjectProperty.homMk (X := (⟨W, hW⟩ : AlgebraicSpaces B S hS)) (Y := ⟨Z, hZ⟩) snd)
      (ObjectProperty.homMk (X := (⟨X, hX⟩ : AlgebraicSpaces B S hS)) (Y := ⟨Y, hY⟩) f)
      (ObjectProperty.homMk (X := (⟨Z, hZ⟩ : AlgebraicSpaces B S hS)) (Y := ⟨Y, hY⟩) g) :=
    IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ sq.w) sq
  exact hPbc.of_isPullback sq' hf

/-- Properness passes from `f` to `snd` along a cartesian square of algebraic spaces. -/
private theorem isProper_snd_of_isPullback_algebraicSpaces
    {W X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B S hS W) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z) {fst : W ⟶ X} {snd : W ⟶ Z}
    {f : X ⟶ Y} {g : Z ⟶ Y}
    (sq : IsPullback fst snd f g) (hf : IsProper B S hS f) : IsProper B S hS snd :=
  prop_snd_of_isPullback_algebraicSpaces B S hS (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
    IsProper B S hS f.hom) (isProper_isStableUnderBaseChange B S hS) hW hX hY hZ sq hf

/-- Flatness passes from `f` to `snd` along a cartesian square of algebraic spaces. -/
private theorem isFlat_snd_of_isPullback_algebraicSpaces {W X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B S hS W) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z) {fst : W ⟶ X} {snd : W ⟶ Z}
    {f : X ⟶ Y} {g : Z ⟶ Y}
    (sq : IsPullback fst snd f g) (hf : IsFlat B S hS f) : IsFlat B S hS snd :=
  prop_snd_of_isPullback_algebraicSpaces B S hS (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
    IsFlat B S hS f.hom) (isFlat_isStableUnderBaseChange B S hS) hW hX hY hZ sq hf

/-- Finite presentation passes from `f` to `snd` along a cartesian square of algebraic spaces. -/
private theorem isFinitePresentation_snd_of_isPullback_algebraicSpaces
    {W X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B S hS W) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z) {fst : W ⟶ X} {snd : W ⟶ Z}
    {f : X ⟶ Y} {g : Z ⟶ Y}
    (sq : IsPullback fst snd f g) (hf : IsFinitePresentation B S hS f) :
    IsFinitePresentation B S hS snd :=
  prop_snd_of_isPullback_algebraicSpaces B S hS (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
    IsFinitePresentation B S hS f.hom) (isFinitePresentation_isStableUnderBaseChange B S hS)
    hW hX hY hZ sq hf

/-- Geometrically reduced fibres pass from `f` to `snd` along a cartesian square of algebraic
spaces. -/
private theorem isGeometricallyReducedFibreAt_snd_of_isPullback_algebraicSpaces
    {W X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B S hS W) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z) {fst : W ⟶ X} {snd : W ⟶ Z}
    {f : X ⟶ Y} {g : Z ⟶ Y}
    (sq : IsPullback fst snd f g)
    (hred : ∀ y, IsGeometricallyReducedFibreAt B S hS f hX hY y) :
    ∀ z, IsGeometricallyReducedFibreAt B S hS snd hW hZ z := by
  have hP' := isAlgebraicSpace_pullback B S hS f g hX hZ hY
  have h0 : MorphismProperty.ContainsIdentities
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toContainsIdentities
  have h0' : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have h1 : MorphismProperty.ContainsIdentities
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.ContainsIdentities.inverseImage (BigFppfOver.toScheme B S hS)
  have h2 : MorphismProperty.RespectsIso
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.RespectsIso.inverseImage _ (BigFppfOver.toScheme B S hS)
  intro z
  rw [← sq.isoPullback_hom_snd]
  refine isGeometricallyReducedFibreAt_comp_of_etale B S hS (pullback.snd f g) hP' hZ
    sq.isoPullback.hom hW (MorphismProperty.presheaf_of_isIso _ _) (fun z' => ?_) z
  change z' ∈ geometricallyReducedFibreLocus B S hS _ hP' hZ
  rw [geometricallyReducedFibreLocus_pullback B S hS f g hX hY hZ]
  exact hred _

/-- **The pieces of the base change.**  Let `e₀ : T₀ ⟶ Y'` present the base change of `π`
along an étale chart `ξ₀ : U₀ ⟶ Y`, and let `ι : V ⟶ T₀` be an open and closed subscheme.
Then the morphism from `X ×_{Y'} V` to `U₀` is proper, flat, of finite presentation, and has
geometrically reduced fibres, as soon as `f' ≫ π` has these properties. -/
theorem piece_properties {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hY' : IsAlgebraicSpace B S hS Y') (f' : X ⟶ Y') (π : Y' ⟶ Y)
    (hf : IsProper B S hS (f' ≫ π)) (hfl : IsFlat B S hS (f' ≫ π))
    (hfp : IsFinitePresentation B S hS (f' ≫ π))
    (hred : ∀ y, IsGeometricallyReducedFibreAt B S hS (f' ≫ π) hX hY y)
    {U₀ T₀ V : BigFppfOver B S hS} (ξ₀ : yoneda.obj U₀ ⟶ Y) (p₀ : T₀ ⟶ U₀)
    (e₀ : yoneda.obj T₀ ⟶ Y') (hpb₀ : IsPullback e₀ (yoneda.map p₀) π ξ₀) (ι : V ⟶ T₀)
    (hιo : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map ι))
    (hιc : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map ι)) :
    ∃ hP : IsAlgebraicSpace B S hS (pullback f' (yoneda.map ι ≫ e₀)),
      IsProper B S hS (pullback.snd f' (yoneda.map ι ≫ e₀) ≫ yoneda.map (ι ≫ p₀)) ∧
      IsFlat B S hS (pullback.snd f' (yoneda.map ι ≫ e₀) ≫ yoneda.map (ι ≫ p₀)) ∧
      IsFinitePresentation B S hS
        (pullback.snd f' (yoneda.map ι ≫ e₀) ≫ yoneda.map (ι ≫ p₀)) ∧
      ∀ z, IsGeometricallyReducedFibreAt B S hS
        (pullback.snd f' (yoneda.map ι ≫ e₀) ≫ yoneda.map (ι ≫ p₀)) hP
        (isAlgebraicSpace_yoneda B S hS U₀) z := by
  have hT₀ := isAlgebraicSpace_yoneda B S hS T₀
  have hU₀ := isAlgebraicSpace_yoneda B S hS U₀
  have hX₀ : IsAlgebraicSpace B S hS (pullback f' e₀) :=
    isAlgebraicSpace_pullback B S hS f' e₀ hX hT₀ hY'
  have sq₀ : IsPullback (pullback.fst f' e₀) (pullback.snd f' e₀ ≫ yoneda.map p₀) (f' ≫ π) ξ₀ :=
    (IsPullback.of_hasPullback f' e₀).paste_vert hpb₀
  have sqi : IsPullback (pullback.lift (pullback.fst f' (yoneda.map ι ≫ e₀))
        (pullback.snd f' (yoneda.map ι ≫ e₀) ≫ yoneda.map ι)
        (by rw [pullback.condition, Category.assoc]))
      (pullback.snd f' (yoneda.map ι ≫ e₀)) (pullback.snd f' e₀) (yoneda.map ι) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f' e₀)
    rw [pullback.lift_fst]
    exact IsPullback.of_hasPullback f' (yoneda.map ι ≫ e₀)
  have hcomp : pullback.snd f' (yoneda.map ι ≫ e₀) ≫ yoneda.map (ι ≫ p₀) =
      pullback.lift (pullback.fst f' (yoneda.map ι ≫ e₀))
        (pullback.snd f' (yoneda.map ι ≫ e₀) ≫ yoneda.map ι)
        (by rw [pullback.condition, Category.assoc]) ≫
      (pullback.snd f' e₀ ≫ yoneda.map p₀) := by
    rw [← Category.assoc, pullback.lift_snd, Functor.map_comp, Category.assoc]
  have hP := isAlgebraicSpace_of_isPullback_yoneda_map B S hS hX₀ sqi
  refine ⟨hP, ?_, ?_, ?_, ?_⟩ <;> rw [hcomp]
  · exact isProper_comp_of_isPullback_isClosedImmersion B S hS hX₀ hU₀ _ sqi hιc
      (isProper_snd_of_isPullback_algebraicSpaces B S hS hX₀ hX hY hU₀ sq₀ hf)
  · exact isFlat_comp_of_isPullback_isOpenImmersion B S hS hX₀ hU₀ _ sqi hιo
      (isFlat_snd_of_isPullback_algebraicSpaces B S hS hX₀ hX hY hU₀ sq₀ hfl)
  · exact isFinitePresentation_comp_of_isPullback_isOpenImmersion_isClosedImmersion B S hS hX₀
      hU₀ _ sqi hιo hιc
      (isFinitePresentation_snd_of_isPullback_algebraicSpaces B S hS hX₀ hX hY hU₀ sq₀ hfp)
  · exact isGeometricallyReducedFibreAt_comp_of_isPullback_isOpenImmersion B S hS _ hX₀ hU₀ hP
      sqi hιo
      (isGeometricallyReducedFibreAt_snd_of_isPullback_algebraicSpaces B S hS hX₀ hX hY hU₀ sq₀
        hred)

/-- The Yoneda image of a morphism of the site whose scheme map is étale is étale after every
representable base change. -/
theorem presheaf_etale_yoneda_map {V T : BigFppfOver B S hS} (ι : V ⟶ T)
    (hι : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map ι)) :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map ι) :=
  presheaf_inverseImage_of_isPullback_yoneda_map B S hS _
    (IsPullback.of_id_snd (f := yoneda.map ι)) hι

/-- Precomposing an étale morphism of presheaves with the Yoneda image of the inclusion of an open
subobject of the site gives an étale morphism. -/
private theorem presheaf_etale_comp_opensSiteObjectInclusion (U : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens) {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {c : yoneda.obj U ⟶ Z}
    (hc : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
      (yoneda.map (opensSiteObjectInclusion B S hS U W) ≫ c) := by
  have := isMultiplicative_presheaf_etale B S hS
  exact MorphismProperty.comp_mem _ _ _ (presheaf_etale_yoneda_map B S hS _ (by
    rw [map_opensSiteObjectInclusion]
    exact HasRingHomProperty.of_isOpenImmersion RingHom.Etale.containsIdentities)) hc

/-- If the fibres of `g` over the points of an open `W` of `U₀` have one geometric connected
component, then the base change of `g` to `W` has connected geometric fibres. -/
private theorem connectedPullback_snd_opensSiteObjectInclusion {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hP : IsAlgebraicSpace B S hS P) {U₀ : BigFppfOver B S hS} (g : P ⟶ yoneda.obj U₀)
    (W : ((BigFppfOver.toScheme B S hS).obj U₀).Opens)
    (hcount : ∀ z : points B S hS (yoneda.obj U₀),
      pointsToScheme B S hS U₀ z ∈ W → numberGeometricConnectedComponents B S hS g z = 1)
    (t : GeometricPoint B S hS (yoneda.obj (opensSiteObject B S hS U₀ W))) :
    ConnectedPullback B S hS (pullback.snd g (yoneda.map (opensSiteObjectInclusion B S hS U₀ W)))
      (yonedaEquiv.symm t.val.value) := by
  have hU₀sp := isAlgebraicSpace_yoneda B S hS U₀
  have hUsp := isAlgebraicSpace_yoneda B S hS (opensSiteObject B S hS U₀ W)
  refine connectedPullback_of_numberGeometricConnectedComponents_eq_one B S hS
    (isAlgebraicSpace_pullback B S hS g _ hP hUsp hU₀sp) hUsp _ t ?_
  rw [numberGeometricConnectedComponents_baseChange B S hS hP hU₀sp hUsp g _, Function.comp_apply]
  refine hcount _ ?_
  rw [pointsToScheme_pointsMap_yoneda, map_opensSiteObjectInclusion]
  exact (pointsToScheme B S hS _ t.image).2

/-- A morphism `q : V ⟶ U` of affine objects of the site is an isomorphism of schemes as soon as
the global functions of an algebraic space `P` are computed both over `V` (along `m`) and over `U`
(along `m ≫ q`). -/
private theorem isIso_map_of_bijective_pullbackToGlobalFunctions
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hP : IsAlgebraicSpace B S hS P) {V U : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] (q : V ⟶ U) (m : P ⟶ yoneda.obj V)
    (b : P ⟶ yoneda.obj U) (hmb : m ≫ yoneda.map q = b)
    (hm : Function.Bijective (pullbackToGlobalFunctions B S hS ⟨P, hP⟩ V (ObjectProperty.homMk m)))
    (hb : Function.Bijective
      (pullbackToGlobalFunctions B S hS ⟨P, hP⟩ U (ObjectProperty.homMk b))) :
    IsIso ((BigFppfOver.toScheme B S hS).map q) := by
  have hfac : (ObjectProperty.homMk b : (⟨_, hP⟩ : AlgebraicSpaces B S hS) ⟶ schemeSpace U) =
      (ObjectProperty.homMk m : (⟨_, hP⟩ : AlgebraicSpaces B S hS) ⟶ schemeSpace V) ≫
        schemeSpaceMap q := by
    apply ObjectProperty.hom_ext
    change b = m ≫ yoneda.map q
    exact hmb.symm
  have hcomp : pullbackToGlobalFunctions B S hS ⟨_, hP⟩ U
      ((ObjectProperty.homMk m : (⟨_, hP⟩ : AlgebraicSpaces B S hS) ⟶ schemeSpace V) ≫
        schemeSpaceMap q) =
      (pullbackToGlobalFunctions B S hS ⟨_, hP⟩ V (ObjectProperty.homMk m)).comp
        ((BigFppfOver.toScheme B S hS).map q).appTop.hom :=
    RingHom.ext fun x => pullbackToGlobalFunctions_comp_schemeSpaceMap B S hS _ _ q x
  rw [hfac, hcomp] at hb
  refine isIso_of_bijective_appTop _ ⟨fun x y hxy => hb.1 ?_, fun x => ?_⟩
  · rw [RingHom.comp_apply, RingHom.comp_apply]
    exact congrArg _ hxy
  · obtain ⟨w, hw⟩ := hb.2 (pullbackToGlobalFunctions B S hS ⟨_, hP⟩ V (ObjectProperty.homMk m) x)
    exact ⟨w, hm.1 hw⟩

/-- **The pieces become the base after shrinking.**  In the situation of
`AlgebraicGeometry.Space.ProperFlatStein.piece_properties`, let `W = D(r)` be a basic open of
the affine `U₀` over which every geometric fibre of the piece `X ×_{Y'} V ⟶ U₀` is connected.
If the structure map of `f'` is an isomorphism on global functions over every affine étale chart
of `Y'` (the hypothesis `hglob`, which is `𝒪_{Y'} = f'_*𝒪_X`) and Stacks 0E0S holds in the form
`h0E0S`, then the part of `V` over `W` maps isomorphically onto `W`. -/
theorem isIso_restrictSiteMap_piece {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hY' : IsAlgebraicSpace B S hS Y') (f' : X ⟶ Y') (π : Y' ⟶ Y)
    (hf : IsProper B S hS (f' ≫ π)) (hfl : IsFlat B S hS (f' ≫ π))
    (hfp : IsFinitePresentation B S hS (f' ≫ π))
    (hred : ∀ y, IsGeometricallyReducedFibreAt B S hS (f' ≫ π) hX hY y)
    (hglob : ∀ (V : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
      ∀ (c : yoneda.obj V ⟶ Y'),
      (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf c →
      ∀ {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P)
        (a : P ⟶ X) (b : P ⟶ yoneda.obj V), IsPullback a b f' c →
        Function.Bijective (pullbackToGlobalFunctions B S hS ⟨P, hP⟩ V
          (ObjectProperty.homMk b)))
    (h0E0S : ∀ {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P)
      (U : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
      ∀ g : P ⟶ yoneda.obj U, IsProper B S hS g → IsFlat B S hS g →
        IsFinitePresentation B S hS g →
        (∀ z, IsGeometricallyReducedFibreAt B S hS g hP (isAlgebraicSpace_yoneda B S hS U) z) →
        (∀ t : GeometricPoint B S hS (yoneda.obj U),
          ConnectedPullback B S hS g (yonedaEquiv.symm t.val.value)) →
        Function.Bijective (pullbackToGlobalFunctions B S hS ⟨P, hP⟩ U
          (ObjectProperty.homMk g)))
    {U₀ T₀ V : BigFppfOver B S hS} (ξ₀ : yoneda.obj U₀ ⟶ Y) (p₀ : T₀ ⟶ U₀)
    (e₀ : yoneda.obj T₀ ⟶ Y') (hpb₀ : IsPullback e₀ (yoneda.map p₀) π ξ₀)
    (hξ₀ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf ξ₀)
    (hU₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj U₀))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) (ι : V ⟶ T₀)
    (hιo : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map ι))
    (hιc : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map ι))
    (r : Γ((BigFppfOver.toScheme B S hS).obj U₀, ⊤))
    (hcount : ∀ z : points B S hS (yoneda.obj U₀),
      pointsToScheme B S hS U₀ z ∈ ((BigFppfOver.toScheme B S hS).obj U₀).basicOpen r →
      numberGeometricConnectedComponents B S hS
        (pullback.snd f' (yoneda.map ι ≫ e₀) ≫ yoneda.map (ι ≫ p₀)) z = 1) :
    IsIso ((BigFppfOver.toScheme B S hS).map
      (restrictSiteMap B S hS (ι ≫ p₀) (((BigFppfOver.toScheme B S hS).obj U₀).basicOpen r))) := by
  obtain ⟨hP, hgp, hgfl, hgfp, hgred⟩ :=
    piece_properties B S hS hX hY hY' f' π hf hfl hfp hred ξ₀ p₀ e₀ hpb₀ ι hιo hιc
  set W : ((BigFppfOver.toScheme B S hS).obj U₀).Opens :=
    ((BigFppfOver.toScheme B S hS).obj U₀).basicOpen r with hWdef
  set c := yoneda.map ι ≫ e₀
  set g := pullback.snd f' c ≫ yoneda.map (ι ≫ p₀) with hg
  set U := opensSiteObject B S hS U₀ W
  set κ := opensSiteObjectInclusion B S hS U₀ W
  set V' := opensSiteObject B S hS V ((BigFppfOver.toScheme B S hS).map (ι ≫ p₀) ⁻¹ᵁ W)
  set lam := opensSiteObjectInclusion B S hS V ((BigFppfOver.toScheme B S hS).map (ι ≫ p₀) ⁻¹ᵁ W)
  set q' := restrictSiteMap B S hS (ι ≫ p₀) W
  have hU₀sp := isAlgebraicSpace_yoneda B S hS U₀
  have hUsp := isAlgebraicSpace_yoneda B S hS U
  have hX' : IsAlgebraicSpace B S hS (pullback g (yoneda.map κ)) :=
    isAlgebraicSpace_pullback B S hS g (yoneda.map κ) hP hUsp hU₀sp
  set a := pullback.fst g (yoneda.map κ)
  set b := pullback.snd g (yoneda.map κ)
  have sqV : IsPullback lam q' (ι ≫ p₀) κ := isPullback_restrictSiteMap B S hS (ι ≫ p₀) W
  have hcond : (a ≫ pullback.snd f' c) ≫ yoneda.map (ι ≫ p₀) = b ≫ yoneda.map κ := by
    rw [Category.assoc, ← hg, pullback.condition]
  set m := (sqV.map yoneda).lift (a ≫ pullback.snd f' c) b hcond
  have hm2 : m ≫ yoneda.map q' = b := (sqV.map yoneda).lift_snd _ _ _
  have houter : IsPullback a (m ≫ yoneda.map q') (pullback.snd f' c ≫ yoneda.map (ι ≫ p₀))
      (yoneda.map κ) := by
    rw [hm2, ← hg]
    exact IsPullback.of_hasPullback g (yoneda.map κ)
  have sqX : IsPullback (a ≫ pullback.fst f' c) m f' (yoneda.map lam ≫ c) :=
    (IsPullback.of_bot houter ((sqV.map yoneda).lift_fst _ _ _).symm (sqV.map yoneda)).paste_horiz
      (IsPullback.of_hasPullback f' c)
  have hUaff : IsAffine ((BigFppfOver.toScheme B S hS).obj U) :=
    (isAffineOpen_top ((BigFppfOver.toScheme B S hS).obj U₀)).basicOpen r
  have hV'aff' : IsAffine ((BigFppfOver.toScheme B S hS).obj V') := by
    change IsAffineOpen ((BigFppfOver.toScheme B S hS).map (ι ≫ p₀) ⁻¹ᵁ W)
    rw [hWdef, Scheme.preimage_basicOpen_top]
    exact (isAffineOpen_top ((BigFppfOver.toScheme B S hS).obj V)).basicOpen _
  have hEt : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map lam ≫ c) := by
    have := isMultiplicative_presheaf_etale B S hS
    exact presheaf_etale_comp_opensSiteObjectInclusion B S hS _ _
      (MorphismProperty.comp_mem _ _ _ (presheaf_etale_yoneda_map B S hS ι inferInstance)
        ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hpb₀.flip hξ₀))
  have hpb := IsPullback.of_hasPullback g (yoneda.map κ)
  exact isIso_map_of_bijective_pullbackToGlobalFunctions B S hS hX' q' m b hm2
    (hglob V' hV'aff' (yoneda.map lam ≫ c) hEt hX' (a ≫ pullback.fst f' c) m sqX)
    (h0E0S hX' U hUaff b
      (isProper_snd_of_isPullback_algebraicSpaces B S hS hX' hP hU₀sp hUsp hpb hgp)
      (isFlat_snd_of_isPullback_algebraicSpaces B S hS hX' hP hU₀sp hUsp hpb hgfl)
      (isFinitePresentation_snd_of_isPullback_algebraicSpaces B S hS hX' hP hU₀sp hUsp hpb hgfp)
      (isGeometricallyReducedFibreAt_snd_of_isPullback_algebraicSpaces B S hS hX' hP hU₀sp hUsp
        hpb hgred)
      (connectedPullback_snd_opensSiteObjectInclusion B S hS hP g W hcount))

/-- The inclusion of an open subobject of the site is an open immersion of schemes. -/
theorem isOpenImmersion_map_opensSiteObjectInclusion (U : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (opensSiteObjectInclusion B S hS U W)) := by
  have h : _root_.AlgebraicGeometry.IsOpenImmersion W.ι := inferInstance
  exact (map_opensSiteObjectInclusion B S hS U W) ▸ h

/-- The inclusion of an open subobject of the site sends a point to itself. -/
theorem map_opensSiteObjectInclusion_apply (U : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (x : (BigFppfOver.toScheme B S hS).obj (opensSiteObject B S hS U W)) :
    (BigFppfOver.toScheme B S hS).map (opensSiteObjectInclusion B S hS U W) x = x.1 := by
  rw [map_opensSiteObjectInclusion]
  rfl

/-- The part over `W` of a subobject `ι : V ⟶ T₀` lands in the part of `T₀` over `W`. -/
private theorem range_map_comp_subset_range_map_opensSiteObjectInclusion
    {T₀ U₀ : BigFppfOver B S hS} (p₀ : T₀ ⟶ U₀)
    (W : ((BigFppfOver.toScheme B S hS).obj U₀).Opens) {V : BigFppfOver B S hS} (ι : V ⟶ T₀) :
    Set.range ((BigFppfOver.toScheme B S hS).map (opensSiteObjectInclusion B S hS V
        ((BigFppfOver.toScheme B S hS).map (ι ≫ p₀) ⁻¹ᵁ W) ≫ ι)) ⊆
      Set.range ((BigFppfOver.toScheme B S hS).map (opensSiteObjectInclusion B S hS T₀
        ((BigFppfOver.toScheme B S hS).map p₀ ⁻¹ᵁ W))) := by
  set lami := opensSiteObjectInclusion B S hS V ((BigFppfOver.toScheme B S hS).map (ι ≫ p₀) ⁻¹ᵁ W)
  intro t ⟨x, hx⟩
  rw [map_opensSiteObjectInclusion]
  have hx' : (BigFppfOver.toScheme B S hS).map lami x ∈
      (BigFppfOver.toScheme B S hS).map (ι ≫ p₀) ⁻¹ᵁ W := by
    rw [map_opensSiteObjectInclusion]
    exact x.2
  have hmem : t ∈ (BigFppfOver.toScheme B S hS).map p₀ ⁻¹ᵁ W := by
    change (BigFppfOver.toScheme B S hS).map p₀ t ∈ W
    rw [← hx, ← Scheme.Hom.comp_apply]
    have hc : (BigFppfOver.toScheme B S hS).map (lami ≫ ι) ≫
        (BigFppfOver.toScheme B S hS).map p₀ =
        (BigFppfOver.toScheme B S hS).map lami ≫ (BigFppfOver.toScheme B S hS).map (ι ≫ p₀) := by
      simp only [← Functor.map_comp, Category.assoc]
    rw [hc, Scheme.Hom.comp_apply]
    exact hx'
  exact ⟨⟨t, hmem⟩, rfl⟩

/-- A factorization `μ` of the part over `W` of `ι : V ⟶ T₀` through the part of `T₀` over `W`
is compatible with the restrictions of `p₀` and of `ι ≫ p₀` over `W`. -/
private theorem comp_map_restrictSiteMap_of_comp_eq {T₀ U₀ : BigFppfOver B S hS} (p₀ : T₀ ⟶ U₀)
    (W : ((BigFppfOver.toScheme B S hS).obj U₀).Opens)
    {V : BigFppfOver B S hS} (ι : V ⟶ T₀)
    (μ : (BigFppfOver.toScheme B S hS).obj
        (opensSiteObject B S hS V ((BigFppfOver.toScheme B S hS).map (ι ≫ p₀) ⁻¹ᵁ W)) ⟶
      (BigFppfOver.toScheme B S hS).obj
        (opensSiteObject B S hS T₀ ((BigFppfOver.toScheme B S hS).map p₀ ⁻¹ᵁ W)))
    (hμ : μ ≫ (BigFppfOver.toScheme B S hS).map
        (opensSiteObjectInclusion B S hS T₀ ((BigFppfOver.toScheme B S hS).map p₀ ⁻¹ᵁ W)) =
      (BigFppfOver.toScheme B S hS).map (opensSiteObjectInclusion B S hS V
        ((BigFppfOver.toScheme B S hS).map (ι ≫ p₀) ⁻¹ᵁ W) ≫ ι)) :
    μ ≫ (BigFppfOver.toScheme B S hS).map (restrictSiteMap B S hS p₀ W) =
      (BigFppfOver.toScheme B S hS).map (restrictSiteMap B S hS (ι ≫ p₀) W) := by
  set κ := opensSiteObjectInclusion B S hS U₀ W
  set lam := opensSiteObjectInclusion B S hS T₀ ((BigFppfOver.toScheme B S hS).map p₀ ⁻¹ᵁ W)
  set lami := opensSiteObjectInclusion B S hS V ((BigFppfOver.toScheme B S hS).map (ι ≫ p₀) ⁻¹ᵁ W)
  set p := restrictSiteMap B S hS p₀ W
  have : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map κ) :=
    isOpenImmersion_map_opensSiteObjectInclusion B S hS _ _
  apply (cancel_mono ((BigFppfOver.toScheme B S hS).map κ)).1
  calc (μ ≫ (BigFppfOver.toScheme B S hS).map p) ≫ (BigFppfOver.toScheme B S hS).map κ
      = μ ≫ (BigFppfOver.toScheme B S hS).map (p ≫ κ) := by
        rw [Category.assoc, Functor.map_comp (BigFppfOver.toScheme B S hS) p κ]
    _ = μ ≫ (BigFppfOver.toScheme B S hS).map (lam ≫ p₀) := by
        rw [(isPullback_restrictSiteMap B S hS p₀ W).w]
    _ = (μ ≫ (BigFppfOver.toScheme B S hS).map lam) ≫ (BigFppfOver.toScheme B S hS).map p₀ := by
        rw [Functor.map_comp (BigFppfOver.toScheme B S hS) lam p₀, Category.assoc]
    _ = (BigFppfOver.toScheme B S hS).map (lami ≫ ι) ≫
          (BigFppfOver.toScheme B S hS).map p₀ := by rw [hμ]
    _ = (BigFppfOver.toScheme B S hS).map (lami ≫ (ι ≫ p₀)) := by
        rw [← Functor.map_comp (BigFppfOver.toScheme B S hS) (lami ≫ ι) p₀, Category.assoc]
    _ = (BigFppfOver.toScheme B S hS).map (restrictSiteMap B S hS (ι ≫ p₀) W ≫ κ) := by
        rw [(isPullback_restrictSiteMap B S hS (ι ≫ p₀) W).w]
    _ = _ := Functor.map_comp _ _ _

/-- If the `ι i` cover `T₀`, then factorizations `μ i` of their parts over `W` through the part
of `T₀` over `W` are jointly surjective. -/
private theorem exists_apply_eq_of_comp_eq_map {T₀ U₀ : BigFppfOver B S hS} (p₀ : T₀ ⟶ U₀)
    (W : ((BigFppfOver.toScheme B S hS).obj U₀).Opens)
    {n : ℕ} {V : Fin n → BigFppfOver B S hS} (ι : ∀ i, V i ⟶ T₀)
    (hcov : ∀ t : (BigFppfOver.toScheme B S hS).obj T₀,
      ∃ i, t ∈ Set.range ((BigFppfOver.toScheme B S hS).map (ι i)))
    (μ : ∀ i, (BigFppfOver.toScheme B S hS).obj
        (opensSiteObject B S hS (V i) ((BigFppfOver.toScheme B S hS).map (ι i ≫ p₀) ⁻¹ᵁ W)) ⟶
      (BigFppfOver.toScheme B S hS).obj
        (opensSiteObject B S hS T₀ ((BigFppfOver.toScheme B S hS).map p₀ ⁻¹ᵁ W)))
    (hμ : ∀ i, μ i ≫ (BigFppfOver.toScheme B S hS).map
        (opensSiteObjectInclusion B S hS T₀ ((BigFppfOver.toScheme B S hS).map p₀ ⁻¹ᵁ W)) =
      (BigFppfOver.toScheme B S hS).map (opensSiteObjectInclusion B S hS (V i)
        ((BigFppfOver.toScheme B S hS).map (ι i ≫ p₀) ⁻¹ᵁ W) ≫ ι i))
    (t : (BigFppfOver.toScheme B S hS).obj
      (opensSiteObject B S hS T₀ ((BigFppfOver.toScheme B S hS).map p₀ ⁻¹ᵁ W))) :
    ∃ i y, μ i y = t := by
  set lam := opensSiteObjectInclusion B S hS T₀ ((BigFppfOver.toScheme B S hS).map p₀ ⁻¹ᵁ W)
  have : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map lam) :=
    isOpenImmersion_map_opensSiteObjectInclusion B S hS _ _
  obtain ⟨i, v, hv⟩ := hcov ((BigFppfOver.toScheme B S hS).map lam t)
  have hvmem : v ∈ (BigFppfOver.toScheme B S hS).map (ι i ≫ p₀) ⁻¹ᵁ W := by
    change (BigFppfOver.toScheme B S hS).map (ι i ≫ p₀) v ∈ W
    rw [Functor.map_comp, Scheme.Hom.comp_apply, hv,
      map_opensSiteObjectInclusion_apply B S hS T₀]
    exact t.2
  refine ⟨i, ⟨v, hvmem⟩, ?_⟩
  apply ((BigFppfOver.toScheme B S hS).map lam).isOpenEmbedding.injective
  change (μ i ≫ (BigFppfOver.toScheme B S hS).map lam) ⟨v, hvmem⟩ = _
  rw [hμ, Functor.map_comp (BigFppfOver.toScheme B S hS) _ (ι i)]
  change (BigFppfOver.toScheme B S hS).map (ι i)
    ((BigFppfOver.toScheme B S hS).map (opensSiteObjectInclusion B S hS (V i) _) ⟨v, hvmem⟩) = _
  rw [map_opensSiteObjectInclusion_apply B S hS (V i) _ ⟨v, hvmem⟩, hv,
    map_opensSiteObjectInclusion_apply B S hS T₀]

/-- If open immersions `ι i` cover `T₀` and the part over `W` of each `ι i ≫ p₀` is an
isomorphism, then the part of `p₀` over `W` is étale. -/
private theorem etale_map_restrictSiteMap_of_isIso {T₀ U₀ : BigFppfOver B S hS} (p₀ : T₀ ⟶ U₀)
    (W : ((BigFppfOver.toScheme B S hS).obj U₀).Opens)
    {n : ℕ} {V : Fin n → BigFppfOver B S hS} (ι : ∀ i, V i ⟶ T₀)
    (hcov : ∀ t : (BigFppfOver.toScheme B S hS).obj T₀,
      ∃ i, t ∈ Set.range ((BigFppfOver.toScheme B S hS).map (ι i)))
    (hιo : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (ι i)))
    (hiso : ∀ i,
      IsIso ((BigFppfOver.toScheme B S hS).map (restrictSiteMap B S hS (ι i ≫ p₀) W))) :
    AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map (restrictSiteMap B S hS p₀ W)) := by
  set lam := opensSiteObjectInclusion B S hS T₀ ((BigFppfOver.toScheme B S hS).map p₀ ⁻¹ᵁ W)
  let lami := fun i => opensSiteObjectInclusion B S hS (V i)
    ((BigFppfOver.toScheme B S hS).map (ι i ≫ p₀) ⁻¹ᵁ W)
  have : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map lam) :=
    isOpenImmersion_map_opensSiteObjectInclusion B S hS _ _
  have hlamio : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (lami i ≫ ι i)) := by
    intro i
    have := hιo i
    have := isOpenImmersion_map_opensSiteObjectInclusion B S hS (V i)
      ((BigFppfOver.toScheme B S hS).map (ι i ≫ p₀) ⁻¹ᵁ W)
    rw [Functor.map_comp (BigFppfOver.toScheme B S hS) (lami i) (ι i)]
    infer_instance
  let μ := fun i => IsOpenImmersion.lift ((BigFppfOver.toScheme B S hS).map lam)
    ((BigFppfOver.toScheme B S hS).map (lami i ≫ ι i))
    (range_map_comp_subset_range_map_opensSiteObjectInclusion B S hS p₀ W (ι i))
  have hμfac : ∀ i, μ i ≫ (BigFppfOver.toScheme B S hS).map lam =
      (BigFppfOver.toScheme B S hS).map (lami i ≫ ι i) := fun i =>
    IsOpenImmersion.lift_fac _ _ _
  have hμio : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion (μ i) := by
    intro i
    have := hlamio i
    have : _root_.AlgebraicGeometry.IsOpenImmersion
        (μ i ≫ (BigFppfOver.toScheme B S hS).map lam) := hμfac i ▸ hlamio i
    exact IsOpenImmersion.of_comp (μ i) ((BigFppfOver.toScheme B S hS).map lam)
  let 𝒰 : ((BigFppfOver.toScheme B S hS).obj
      (opensSiteObject B S hS T₀ ((BigFppfOver.toScheme B S hS).map p₀ ⁻¹ᵁ W))).OpenCover :=
    Scheme.Cover.mkOfCovers (Fin n) _ μ
      (exists_apply_eq_of_comp_eq_map B S hS p₀ W ι hcov μ hμfac) hμio
  have _hel : IsZariskiLocalAtSource (@AlgebraicGeometry.Etale.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)
  refine IsZariskiLocalAtSource.of_openCover 𝒰 fun i => ?_
  change AlgebraicGeometry.Etale
    (μ i ≫ (BigFppfOver.toScheme B S hS).map (restrictSiteMap B S hS p₀ W))
  rw [comp_map_restrictSiteMap_of_comp_eq B S hS p₀ W (ι i) (μ i) (hμfac i)]
  have := hiso i
  infer_instance

/-- If finitely many morphisms `g i` to an affine `U₀` have open loci of points with one geometric
connected component, all containing `z₀`, then some basic open of `U₀` around `z₀` lies in all of
them. -/
private theorem exists_basicOpen_numberGeometricConnectedComponents_eq_one {U₀ : BigFppfOver B S hS}
    (hU₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj U₀)) {ι' : Type*} [Finite ι']
    {P : ι' → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : ∀ i, P i ⟶ yoneda.obj U₀)
    (hopen : ∀ i, IsOpen {z | numberGeometricConnectedComponents B S hS (g i) z = 1})
    (z₀ : points B S hS (yoneda.obj U₀))
    (hz₀ : ∀ i, numberGeometricConnectedComponents B S hS (g i) z₀ = 1) :
    ∃ r : Γ((BigFppfOver.toScheme B S hS).obj U₀, ⊤),
      pointsToScheme B S hS U₀ z₀ ∈ ((BigFppfOver.toScheme B S hS).obj U₀).basicOpen r ∧
      ∀ i, ∀ z : points B S hS (yoneda.obj U₀),
        pointsToScheme B S hS U₀ z ∈ ((BigFppfOver.toScheme B S hS).obj U₀).basicOpen r →
        numberGeometricConnectedComponents B S hS (g i) z = 1 := by
  set N : Set (points B S hS (yoneda.obj U₀)) :=
    ⋂ i, {z | numberGeometricConnectedComponents B S hS (g i) z = 1}
  have hO := (isOpen_pointTopology_yoneda_iff_isOpen_image B S hS U₀ N).1
    (isOpen_iInter_of_finite hopen)
  obtain ⟨r, hrle, hu₀r⟩ :=
    (isAffineOpen_top ((BigFppfOver.toScheme B S hS).obj U₀)).exists_basicOpen_le
    (V := ⟨_, hO⟩) ⟨pointsToScheme B S hS U₀ z₀, ⟨z₀, Set.mem_iInter.2 hz₀, rfl⟩⟩ trivial
  refine ⟨r, hu₀r, fun i z hz => ?_⟩
  obtain ⟨z', hz'N, hz'⟩ := hrle hz
  rw [injective_pointsToScheme B S hS U₀ hz'] at hz'N
  exact Set.mem_iInter.1 hz'N i

/-- **The local step of Stacks 0E0D.**  Given a split affine chart of the Stein factorization
through `y`, as produced by `AlgebraicGeometry.Space.ProperFlatStein.exists_split_affine_chart`,
there is an étale chart `ξ : U ⟶ Y` through `y` over which `π` is represented by a finite étale
morphism of schemes.  The chart is a basic open `U = D(r)` of the split chart, chosen inside the
locus where every piece has connected geometric fibres (the openness of the connected geometric
fibre locus, the part of Stacks 0E1E used here, as the hypothesis `h0E1E`), and over it every
piece is the base (`AlgebraicGeometry.Space.ProperFlatStein.isIso_restrictSiteMap_piece`). -/
theorem exists_finite_etale_chart_of_split {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hY' : IsAlgebraicSpace B S hS Y') (f' : X ⟶ Y') (π : Y' ⟶ Y)
    (hf : IsProper B S hS (f' ≫ π)) (hfl : IsFlat B S hS (f' ≫ π))
    (hfp : IsFinitePresentation B S hS (f' ≫ π))
    (hred : ∀ y, IsGeometricallyReducedFibreAt B S hS (f' ≫ π) hX hY y)
    (hconn : ∀ y' : GeometricPoint B S hS Y',
      ConnectedPullback B S hS f' (yonedaEquiv.symm y'.val.value))
    (hglob : ∀ (V : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
      ∀ (c : yoneda.obj V ⟶ Y'),
      (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf c →
      ∀ {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P)
        (a : P ⟶ X) (b : P ⟶ yoneda.obj V), IsPullback a b f' c →
        Function.Bijective (pullbackToGlobalFunctions B S hS ⟨P, hP⟩ V
          (ObjectProperty.homMk b)))
    (h0E0S : ∀ {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P)
      (U : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
      ∀ g : P ⟶ yoneda.obj U, IsProper B S hS g → IsFlat B S hS g →
        IsFinitePresentation B S hS g →
        (∀ z, IsGeometricallyReducedFibreAt B S hS g hP (isAlgebraicSpace_yoneda B S hS U) z) →
        (∀ t : GeometricPoint B S hS (yoneda.obj U),
          ConnectedPullback B S hS g (yonedaEquiv.symm t.val.value)) →
        Function.Bijective (pullbackToGlobalFunctions B S hS ⟨P, hP⟩ U
          (ObjectProperty.homMk g)))
    (h0E1E : ∀ {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P)
      {Z : BigFppfOver B S hS} (g : P ⟶ yoneda.obj Z), IsProper B S hS g → IsFlat B S hS g →
        IsFinitePresentation B S hS g →
        (∀ z, IsGeometricallyReducedFibreAt B S hS g hP (isAlgebraicSpace_yoneda B S hS Z) z) →
        IsOpen {z | numberGeometricConnectedComponents B S hS g z = 1})
    (y : points B S hS Y)
    {U₀ T₀ : BigFppfOver B S hS} (ξ₀ : yoneda.obj U₀ ⟶ Y) (p₀ : T₀ ⟶ U₀)
    (e₀ : yoneda.obj T₀ ⟶ Y') (z₀ : points B S hS (yoneda.obj U₀)) {n : ℕ}
    (V : Fin n → BigFppfOver B S hS) (ι : ∀ i, V i ⟶ T₀)
    (hU₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj U₀))
    (hξ₀ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf ξ₀)
    (hpb₀ : IsPullback e₀ (yoneda.map p₀) π ξ₀)
    (hp₀ : _root_.AlgebraicGeometry.IsIntegralHom ((BigFppfOver.toScheme B S hS).map p₀))
    (hz₀ : pointsMap B S hS (yoneda.obj U₀) ξ₀ z₀ = y)
    (hVaff : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (V i)))
    (hιo : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (ι i)))
    (hιc : ∀ i,
      _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map (ι i)))
    (hcov : ∀ t : (BigFppfOver.toScheme B S hS).obj T₀,
      ∃ i, t ∈ Set.range ((BigFppfOver.toScheme B S hS).map (ι i)))
    (huniq : ∀ i, ∃ v : (BigFppfOver.toScheme B S hS).obj (V i),
      (BigFppfOver.toScheme B S hS).map (ι i ≫ p₀) ⁻¹' {pointsToScheme B S hS U₀ z₀} = {v} ∧
      ((BigFppfOver.toScheme B S hS).map (ι i ≫ p₀) |>.residueFieldMap v).hom.IsPurelyInseparable) :
    ∃ (U : BigFppfOver B S hS) (ξ : yoneda.obj U ⟶ Y)
      (T : BigFppfOver B S hS) (p : T ⟶ U) (i : yoneda.obj T ⟶ Y'),
      (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf ξ ∧
      y ∈ Set.range (pointsMap B S hS (yoneda.obj U) ξ) ∧
      IsPullback i (yoneda.map p) π ξ ∧
      _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map p) ∧
      AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map p) := by
  choose hP hgp hgfl hgfp hgred using fun i => piece_properties B S hS hX hY hY' f' π hf hfl hfp
    hred ξ₀ p₀ e₀ hpb₀ (ι i) (hιo i) (hιc i)
  have hone : ∀ i, numberGeometricConnectedComponents B S hS
      (pullback.snd f' (yoneda.map (ι i) ≫ e₀) ≫ yoneda.map (ι i ≫ p₀)) z₀ = 1 := by
    intro i
    obtain ⟨v, hv, hinsep⟩ := huniq i
    exact numberGeometricConnectedComponents_eq_one B S hS f' hconn (yoneda.map (ι i) ≫ e₀)
      (ι i ≫ p₀) _ v hv hinsep z₀ rfl
  obtain ⟨r, hu₀r, hcount⟩ := exists_basicOpen_numberGeometricConnectedComponents_eq_one B S hS
    hU₀ (fun i => pullback.snd f' (yoneda.map (ι i) ≫ e₀) ≫ yoneda.map (ι i ≫ p₀))
    (fun i => h0E1E (hP i) _ (hgp i) (hgfl i) (hgfp i) (hgred i)) z₀ hone
  have hiso := fun i => isIso_restrictSiteMap_piece B S hS hX hY hY' f' π hf hfl hfp hred hglob
    h0E0S ξ₀ p₀ e₀ hpb₀ hξ₀ hU₀ (hVaff i) (ι i) (hιo i) (hιc i) r (hcount i)
  set W : ((BigFppfOver.toScheme B S hS).obj U₀).Opens :=
    ((BigFppfOver.toScheme B S hS).obj U₀).basicOpen r
  set κ := opensSiteObjectInclusion B S hS U₀ W
  set lam := opensSiteObjectInclusion B S hS T₀ ((BigFppfOver.toScheme B S hS).map p₀ ⁻¹ᵁ W)
  set p := restrictSiteMap B S hS p₀ W
  have hEtξ := presheaf_etale_comp_opensSiteObjectInclusion B S hS U₀ W hξ₀
  have hrange : y ∈ Set.range (pointsMap B S hS _ (yoneda.map κ ≫ ξ₀)) := by
    obtain ⟨z, hz⟩ := surjective_pointsToScheme B S hS (opensSiteObject B S hS U₀ W)
      ⟨pointsToScheme B S hS U₀ z₀, hu₀r⟩
    refine ⟨z, ?_⟩
    have hκz : pointsMap B S hS _ (yoneda.map κ) z = z₀ := by
      apply injective_pointsToScheme B S hS U₀
      rw [pointsToScheme_pointsMap_yoneda, map_opensSiteObjectInclusion, hz]
      rfl
    rw [pointsMap_comp_apply, hκz, hz₀]
  have hpb : IsPullback (yoneda.map lam ≫ e₀) (yoneda.map p) π (yoneda.map κ ≫ ξ₀) :=
    ((isPullback_restrictSiteMap B S hS p₀ W).map yoneda).paste_horiz hpb₀
  have het : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map p) :=
    etale_map_restrictSiteMap_of_isIso B S hS p₀ W ι hcov hιo hiso
  have hint : _root_.AlgebraicGeometry.IsIntegralHom ((BigFppfOver.toScheme B S hS).map p) := by
    have := hp₀
    exact (inferInstance : _root_.AlgebraicGeometry.IsIntegralHom
      ((BigFppfOver.toScheme B S hS).map p₀ ∣_ W))
  refine ⟨_, yoneda.map κ ≫ ξ₀, _, p, yoneda.map lam ≫ e₀, hEtξ, hrange, hpb, ?_, het⟩
  have := (Etale.iff_flat_and_formallyUnramified.1 het).2.2
  exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType
    (f := (BigFppfOver.toScheme B S hS).map p)).2 ⟨hint, inferInstance⟩

/-- **Stacks 0E0D, from its inputs.**  Let `f = f' ≫ π : X ⟶ Y` be proper, flat, of finite
presentation, with geometrically reduced fibres, factored through `π : Y' ⟶ Y` affine and
integral with `f'` having connected geometric fibres, and with `𝒪_{Y'} = f'_*𝒪_X` read on global
functions over the affine étale charts of `Y'` (`hglob`).  Granted Stacks 0E0S over affine
bases (`h0E0S`) and the openness of the connected geometric fibre locus (`h0E1E`), `π` is finite
and étale.

The proof is the source's: étale locally on `Y` the factorization splits by idempotents into
pieces with one point over a given point (Stacks 0E1C and 0BSR,
`AlgebraicGeometry.Space.ProperFlatStein.exists_split_affine_chart`); each piece has connected
geometric fibres near that point, so is the base there
(`AlgebraicGeometry.Space.ProperFlatStein.exists_finite_etale_chart_of_split`);
and finite étaleness is étale local on the base
(`AlgebraicGeometry.Space.ProperFlatStein.isFinite_and_isEtale_of_forall_point`). -/
theorem isFinite_and_isEtale_of_stein_of_inputs {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hY' : IsAlgebraicSpace B S hS Y') (f' : X ⟶ Y') (π : Y' ⟶ Y)
    (hπ : IsAffineHom B S hS π) (hπint : IsIntegralHom B S hS π)
    (hf : IsProper B S hS (f' ≫ π)) (hfl : IsFlat B S hS (f' ≫ π))
    (hfp : IsFinitePresentation B S hS (f' ≫ π))
    (hred : ∀ y, IsGeometricallyReducedFibreAt B S hS (f' ≫ π) hX hY y)
    (hconn : ∀ y' : GeometricPoint B S hS Y',
      ConnectedPullback B S hS f' (yonedaEquiv.symm y'.val.value))
    (hglob : ∀ (V : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
      ∀ (c : yoneda.obj V ⟶ Y'),
      (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf c →
      ∀ {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P)
        (a : P ⟶ X) (b : P ⟶ yoneda.obj V), IsPullback a b f' c →
        Function.Bijective (pullbackToGlobalFunctions B S hS ⟨P, hP⟩ V
          (ObjectProperty.homMk b)))
    (h0E0S : ∀ {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P)
      (U : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
      ∀ g : P ⟶ yoneda.obj U, IsProper B S hS g → IsFlat B S hS g →
        IsFinitePresentation B S hS g →
        (∀ z, IsGeometricallyReducedFibreAt B S hS g hP (isAlgebraicSpace_yoneda B S hS U) z) →
        (∀ t : GeometricPoint B S hS (yoneda.obj U),
          ConnectedPullback B S hS g (yonedaEquiv.symm t.val.value)) →
        Function.Bijective (pullbackToGlobalFunctions B S hS ⟨P, hP⟩ U
          (ObjectProperty.homMk g)))
    (h0E1E : ∀ {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P)
      {Z : BigFppfOver B S hS} (g : P ⟶ yoneda.obj Z), IsProper B S hS g → IsFlat B S hS g →
        IsFinitePresentation B S hS g →
        (∀ z, IsGeometricallyReducedFibreAt B S hS g hP (isAlgebraicSpace_yoneda B S hS Z) z) →
        IsOpen {z | numberGeometricConnectedComponents B S hS g z = 1}) :
    IsFinite B S hS π ∧ IsEtale B S hS π := by
  refine isFinite_and_isEtale_of_forall_point B S hS hY π hπ fun y => ?_
  obtain ⟨U₀, T₀, ξ₀, p₀, e₀, z₀, n, V, ι, hU₀, -, hξ₀, hpb₀, hp₀, hz₀, hVaff, hιo, hιc, hcov,
    huniq⟩ := exists_split_affine_chart B S hS hY f' π hπint hfp.2.1
      hf.2.1.1 (isSurjective_of_connectedPullback B S hS f' hconn) y
  exact exists_finite_etale_chart_of_split B S hS hX hY hY' f' π hf hfl hfp hred hconn hglob h0E0S
    h0E1E y ξ₀ p₀ e₀ z₀ V ι hU₀ hξ₀ hpb₀ hp₀ hz₀ hVaff hιo hιc hcov huniq

end AlgebraicGeometry.Space.ProperFlatStein

end
