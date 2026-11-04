module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PresentationPullbackDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PsiDescended

/-!
# The presentation of a base change `T ×_X P` over a scheme point of the base

Let `π : P ⟶ X` be presented as a relative homogeneous spectrum over the scheme points of `X`
(`AlgebraicGeometry.Space.RelativeProjPoints`, Stacks 084B), `X = U/R` a presentation of the base
and `f : T ⟶ X` a point of `X` by an object `T` of the site.  The base change of the atlas `U ⟶ X`
along `f` is an étale surjective atlas `T_U = T ×_X U ⟶ T` of the representable algebraic space
`T`, whose kernel pair is `T_U ×_T T_U`; this is a presentation `T = T_U/T_R` of `T` mapping to the
presentation of `X`.  The base change `T ×_X P ⟶ T` of `π` is again presented over the scheme
points of `T`, and the presentation `T ×_X P = (T_U ×_X P)/(T_R ×_X P)` it receives from `T_U/T_R`
maps to the presentation `P = (U ×_X P)/(R ×_X P)`.  These are the presentations along which the
base change clause of Stacks 084D is computed: an `𝒪_P`-module pulled back to `T ×_X P` is
identified with a module on the scheme of `T ×_X P` by comparing the two on the charts
`T_U ×_X P`.

## Main definitions

* `AlgebraicGeometry.Space.Presentation.alongPoint`: **the presentation `T = T_U/T_R` of a
  representable algebraic space over a point `f : T ⟶ X`**, the base change of a presentation of
  `X`.
* `AlgebraicGeometry.Space.Presentation.alongPointRelationMap`: the morphism `T_R ⟶ R` of the
  relations.
* `AlgebraicGeometry.Space.RelativeProjPoints.baseChangePoint`: the base change `T ×_X P ⟶ T`,
  presented over the scheme points of `T`.
* `AlgebraicGeometry.Space.presentationIsoOfChartIsos`: an isomorphism of quasi-coherent modules
  from identifications of their inverse images along the atlas of a presentation with a common
  `M^a`, compatible with the transitions (Stacks 03M3).

## Main results

* `AlgebraicGeometry.Space.Presentation.isPullback_alongPoint`: the chart `T_U` is `T ×_X U`.
* `AlgebraicGeometry.Space.RelativeProjPoints.LiesOver.of_baseChangePoint`: a morphism lying over
  a morphism of test objects for the base change lies over it for `π`.
* `AlgebraicGeometry.Space.transitionCommutes_representedQuasicoherent`: the canonical transition
  of the inverse image of a module `N^a` attached to a quasi-coherent module on a scheme is the
  module attached to the canonical scheme transition of the pullback of `N` (Stacks 03LU, 03DX).

## References

* [Stacks Project, Tag 0263](https://stacks.math.columbia.edu/tag/0263)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry.Space

namespace Presentation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hX : IsAlgebraicSpace B S hS X}
  (Px : Presentation B S hS X hX) {T : BigFppfOver B S hS} (f : yoneda.obj T ⟶ X)

/-! ### The presentation of a point of the base -/

/-- The chart `T_U = T ×_X U` of a point `f : T ⟶ X`, the base change of the atlas. -/
abbrev alongPointChart : BigFppfOver B S hS := Px.etale.rep.pullback f

/-- The projection `T ×_X U ⟶ T`. -/
abbrev alongPointToPoint : Px.alongPointChart f ⟶ T := Px.etale.rep.snd f

/-- The projection `T ×_X U ⟶ U`. -/
abbrev alongPointToAtlas : Px.alongPointChart f ⟶ Px.U :=
  Yoneda.fullyFaithful.preimage (Px.etale.rep.fst f)

/-- **The chart `T_U` is the fibre product `T ×_X U`.** -/
theorem isPullback_alongPoint :
    IsPullback (yoneda.map (Px.alongPointToAtlas f)) (yoneda.map (Px.alongPointToPoint f))
      Px.toSpace f := by
  rw [Yoneda.fullyFaithful.map_preimage]
  exact Px.etale.rep.isPullback f

/-- The two points `T_U ⟶ X` through `T` and through `U` agree. -/
theorem map_alongPointToAtlas_comp_toSpace :
    yoneda.map (Px.alongPointToAtlas f) ≫ Px.toSpace = yoneda.map (Px.alongPointToPoint f) ≫ f :=
  (Px.isPullback_alongPoint f).w

section KernelPair

attribute [local instance] BigFppfSite.hasPullbacks_schemes

/-- The kernel pair `T_R = T_U ×_T T_U` of the chart. -/
abbrev alongPointRelation : BigFppfOver B S hS :=
  pullback (Px.alongPointToPoint f) (Px.alongPointToPoint f)

/-- The first projection of the kernel pair of the chart. -/
abbrev alongPointTarget : Px.alongPointRelation f ⟶ Px.alongPointChart f := pullback.fst _ _

/-- The second projection of the kernel pair of the chart. -/
abbrev alongPointSource : Px.alongPointRelation f ⟶ Px.alongPointChart f := pullback.snd _ _

/-- The kernel pair of the chart, as a cartesian square of represented presheaves. -/
theorem isPullback_alongPointRelation :
    IsPullback (yoneda.map (Px.alongPointTarget f)) (yoneda.map (Px.alongPointSource f))
      (yoneda.map (Px.alongPointToPoint f)) (yoneda.map (Px.alongPointToPoint f)) :=
  (IsPullback.of_hasPullback _ _).map yoneda

/-- The two projections of the kernel pair have the same composite with `T_U ⟶ T`. -/
theorem alongPointTarget_comp_toPoint :
    Px.alongPointTarget f ≫ Px.alongPointToPoint f =
      Px.alongPointSource f ≫ Px.alongPointToPoint f :=
  pullback.condition

end KernelPair

/-- The chart `T_U ⟶ T` is étale after every representable base change. -/
theorem etale_alongPointToPoint :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map (Px.alongPointToPoint f)) :=
  presheaf_of_isPullback B S hS (Px.isPullback_alongPoint f) Px.etale

/-- The chart `T_U ⟶ T` is surjective after every representable base change. -/
theorem surjective_alongPointToPoint :
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map (Px.alongPointToPoint f)) :=
  presheaf_of_isPullback B S hS (Px.isPullback_alongPoint f) Px.surjective

/-- The kernel pair of a morphism of the site whose represented morphism is étale after every
representable base change is an étale equivalence relation. -/
theorem isEtaleEquivalenceRelation_of_isPullback {U R W : BigFppfOver B S hS} {t s : R ⟶ U}
    {g : U ⟶ W}
    (het : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map g))
    (hkernel : IsPullback (yoneda.map t) (yoneda.map s) (yoneda.map g) (yoneda.map g)) :
    Stacks.Groupoids.IsEtaleEquivalenceRelation
      (prod.lift ((Over.post B.inclusion).map t) ((Over.post B.inclusion).map s)) :=
  have hrel : MorphismProperty.relative yoneda
      (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))
      (yoneda.map g) := by
    simpa [MorphismProperty.presheaf] using het
  have hsrc : Stacks.Groupoids.PreRelation.source
      (prod.lift ((Over.post B.inclusion).map t) ((Over.post B.inclusion).map s)) =
      (Over.post B.inclusion).map s :=
    prod.lift_snd _ _
  have htgt : Stacks.Groupoids.PreRelation.target
      (prod.lift ((Over.post B.inclusion).map t) ((Over.post B.inclusion).map s)) =
      (Over.post B.inclusion).map t :=
    prod.lift_fst _ _
  { isEquivalenceRelation := by
      rw [htgt, hsrc]
      exact isEquivalenceRelation_of_isPullback B S hS _ _ _ hkernel
    etale_source := by
      rw [hsrc]
      exact hrel.2 _ _ _ hkernel
    etale_target := by
      rw [htgt]
      exact hrel.2 _ _ _ hkernel.flip }

/-- **The presentation `T = T_U/T_R` of the representable algebraic space of a point
`f : T ⟶ X`**: the base change along `f` of the presentation `X = U/R`, with presenting scheme
`T_U = T ×_X U` and relation its kernel pair `T_U ×_T T_U`. -/
abbrev alongPoint : Presentation B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) where
  U := Px.alongPointChart f
  R := Px.alongPointRelation f
  target := Px.alongPointTarget f
  source := Px.alongPointSource f
  isEtaleEquivalenceRelation := isEtaleEquivalenceRelation_of_isPullback
    (Px.etale_alongPointToPoint f) (Px.isPullback_alongPointRelation f)
  toSpace := yoneda.map (Px.alongPointToPoint f)
  surjective := Px.surjective_alongPointToPoint f
  etale := Px.etale_alongPointToPoint f
  isPullback := Px.isPullback_alongPointRelation f

/-- The presenting scheme of the presentation of `T` is the chart `T_U`. -/
@[simp] theorem alongPoint_U : (Px.alongPoint f).U = Px.alongPointChart f := rfl

/-- The atlas of the presentation of `T` is the represented projection `T_U ⟶ T`. -/
@[simp] theorem alongPoint_toSpace :
    (Px.alongPoint f).toSpace = yoneda.map (Px.alongPointToPoint f) := rfl

/-- The two points `T_U ⟶ X`, through `T` and through the atlas, as points of the presentation. -/
theorem map_alongPointToAtlas_comp_toSpace' :
    yoneda.map (Px.alongPointToAtlas f) ≫ Px.toSpace = (Px.alongPoint f).toSpace ≫ f :=
  Px.map_alongPointToAtlas_comp_toSpace f

/-- The condition defining the morphism `T_R ⟶ R` of the relations. -/
theorem alongPointRelationMap_condition :
    yoneda.map (Px.alongPointTarget f ≫ Px.alongPointToAtlas f) ≫ Px.toSpace =
      yoneda.map (Px.alongPointSource f ≫ Px.alongPointToAtlas f) ≫ Px.toSpace := by
  simp only [CategoryTheory.Functor.map_comp, Category.assoc,
    map_alongPointToAtlas_comp_toSpace]
  simp only [← Category.assoc, ← CategoryTheory.Functor.map_comp,
    Px.alongPointTarget_comp_toPoint f]

/-- **The morphism `T_R ⟶ R` of the relations** of the presentations of `T` and `X`. -/
def alongPointRelationMap : (Px.alongPoint f).R ⟶ Px.R :=
  Yoneda.fullyFaithful.preimage (Px.isPullback.lift _ _ (Px.alongPointRelationMap_condition f))

/-- The morphism `T_R ⟶ R` commutes with the target projections. -/
theorem alongPointRelationMap_comp_target :
    Px.alongPointRelationMap f ≫ Px.target = Px.alongPointTarget f ≫ Px.alongPointToAtlas f :=
  Yoneda.fullyFaithful.map_injective (by simp [alongPointRelationMap])

/-- The morphism `T_R ⟶ R` commutes with the source projections. -/
theorem alongPointRelationMap_comp_source :
    Px.alongPointRelationMap f ≫ Px.source = Px.alongPointSource f ≫ Px.alongPointToAtlas f :=
  Yoneda.fullyFaithful.map_injective (by simp [alongPointRelationMap])

end Presentation

/-! ### The base change `T ×_X P ⟶ T`, presented over the scheme points of `T` -/

namespace RelativeProjPoints

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : P ⟶ X}
  (d : RelativeProjPoints B S hS π) (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)

/-- The condition defining the morphism `Z ×_X P ⟶ T ×_X P` over a point `g : Z ⟶ T`. -/
theorem baseChangePoint_condition (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ yoneda.obj T) :
    d.fibreToSpace Z (g ≫ f) ≫ π =
      yoneda.map (d.fibreHom Z (g ≫ f) ≫ Yoneda.fullyFaithful.preimage g) ≫ f := by
  rw [(d.isPullback Z (g ≫ f)).w, CategoryTheory.Functor.map_comp,
    Yoneda.fullyFaithful.map_preimage, Category.assoc]

/-- The morphism `Z ×_X P ⟶ T ×_X P` of base changes over a point `g : Z ⟶ T`. -/
abbrev baseChangePointMap (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ yoneda.obj T) :
    d.fibre Z (g ≫ f) ⟶ d.fibre T f :=
  d.fibreLift (d.fibreHom Z (g ≫ f) ≫ Yoneda.fullyFaithful.preimage g) (d.fibreToSpace Z (g ≫ f))
    (d.baseChangePoint_condition T f Z g)

/-- The morphism `Z ×_X P ⟶ T ×_X P` commutes with the projections to `P`. -/
theorem map_baseChangePointMap_comp_fibreToSpace (Z : BigFppfOver B S hS)
    (g : yoneda.obj Z ⟶ yoneda.obj T) :
    yoneda.map (d.baseChangePointMap T f Z g) ≫ d.fibreToSpace T f = d.fibreToSpace Z (g ≫ f) :=
  d.map_fibreLift_comp_fibreToSpace _ _ _

/-- The morphism `Z ×_X P ⟶ T ×_X P` lies over `g : Z ⟶ T`. -/
theorem map_baseChangePointMap_comp_fibreHom (Z : BigFppfOver B S hS)
    (g : yoneda.obj Z ⟶ yoneda.obj T) :
    yoneda.map (d.baseChangePointMap T f Z g) ≫ yoneda.map (d.fibreHom T f) =
      yoneda.map (d.fibreHom Z (g ≫ f)) ≫ g := by
  rw [← CategoryTheory.Functor.map_comp, fibreLift_comp_fibreHom,
    CategoryTheory.Functor.map_comp, Yoneda.fullyFaithful.map_preimage]

/-- **The base change `T ×_X P ⟶ T` of `π` along a point `f : T ⟶ X`, presented over the scheme
points of `T`**: over `g : Z ⟶ T` it is the base change `Z ×_X P` of `π` along `g ≫ f`, with its
morphism to `T ×_X P`. -/
def baseChangePoint : RelativeProjPoints B S hS (yoneda.map (d.fibreHom T f)) where
  algebra Z g := d.algebra Z (g ≫ f)
  fibre Z g := d.fibre Z (g ≫ f)
  fibreIso Z g := d.fibreIso Z (g ≫ f)
  fibreHom Z g := d.fibreHom Z (g ≫ f)
  fibreHom_comp Z g := d.fibreHom_comp Z (g ≫ f)
  fibreToSpace Z g := yoneda.map (d.baseChangePointMap T f Z g)
  isPullback Z g := by
    refine IsPullback.of_right ?_ (d.map_baseChangePointMap_comp_fibreHom T f Z g)
      (d.isPullback T f)
    rw [d.map_baseChangePointMap_comp_fibreToSpace T f Z g]
    exact d.isPullback Z (g ≫ f)

/-- The fibre of the base change over `g : Z ⟶ T` is the fibre of `π` over `g ≫ f`. -/
@[simp] theorem baseChangePoint_fibre (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ yoneda.obj T) :
    (d.baseChangePoint T f).fibre Z g = d.fibre Z (g ≫ f) := rfl

/-- The projection of the base change over `g` is that of `π` over `g ≫ f`. -/
@[simp] theorem baseChangePoint_fibreHom (Z : BigFppfOver B S hS)
    (g : yoneda.obj Z ⟶ yoneda.obj T) :
    (d.baseChangePoint T f).fibreHom Z g = d.fibreHom Z (g ≫ f) := rfl

/-- The morphism of the base change over `g` to `T ×_X P` is the represented
`AlgebraicGeometry.Space.RelativeProjPoints.baseChangePointMap`. -/
theorem baseChangePoint_fibreToSpace (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ yoneda.obj T) :
    (d.baseChangePoint T f).fibreToSpace Z g = yoneda.map (d.baseChangePointMap T f Z g) := rfl

variable {d T f}

/-- **A morphism lying over a morphism of test objects for the base change `T ×_X P ⟶ T` lies
over it for `π`.** -/
theorem LiesOver.of_baseChangePoint {Z Z' : BigFppfOver B S hS} {g : yoneda.obj Z ⟶ yoneda.obj T}
    {g' : yoneda.obj Z' ⟶ yoneda.obj T} {y : d.fibre Z' (g' ≫ f) ⟶ d.fibre Z (g ≫ f)}
    {k : Z' ⟶ Z}
    (hy : (d.baseChangePoint T f).LiesOver (T := Z) (T' := Z') (f := g) (f' := g') y k) :
    d.LiesOver y k :=
  ⟨hy.1, (congrArg (yoneda.map y ≫ ·)
      (d.map_baseChangePointMap_comp_fibreToSpace T f Z g)).symm.trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ d.fibreToSpace T f) hy.2).trans
      (d.map_baseChangePointMap_comp_fibreToSpace T f Z' g')))⟩

end RelativeProjPoints

/-! ### The canonical transition of a module attached to a scheme -/

section Represented

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U R W : BigFppfOver B S hS} (t s : R ⟶ U) (q : U ⟶ W) (hts : t ≫ q = s ≫ q)
  (N : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj W).ringCatSheaf).FullSubcategory)

/-- **The canonical scheme transition `t^*(q^*N) ≅ s^*(q^*N)`** of the pullback of a
quasi-coherent module along `q`, for `t ≫ q = s ≫ q`: the contraction of the pullbacks, the
identification along `t ≫ q = s ≫ q` and the inverse contraction. -/
def canonicalSchemeTransition :
    quasicoherentPullbackObj B S hS t (quasicoherentPullbackObj B S hS q N) ⟶
      quasicoherentPullbackObj B S hS s (quasicoherentPullbackObj B S hS q N) :=
  (quasicoherentPullbackCompIso B S hS t q N).hom ≫ quasicoherentPullbackEqToHom B S hS hts N ≫
    (quasicoherentPullbackCompIso B S hS s q N).inv

/-- The module attached to a composite of morphisms of quasi-coherent modules. -/
theorem representedQuasicoherentSchemeEquivalence_map_comp_hom {V : BigFppfOver B S hS}
    {M₁ M₂ M₃ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj V).ringCatSheaf).FullSubcategory}
    (a : M₁ ⟶ M₂) (b : M₂ ⟶ M₃) :
    ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map (a ≫ b)).hom =
      ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map a).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map b).hom := by
  rw [CategoryTheory.Functor.map_comp]
  rfl

/-- The abstract shape of `AlgebraicGeometry.Space.transitionCommutes_representedQuasicoherent`,
at variables. -/
theorem transitionCommutes_representedQuasicoherent_core {D : Type*} [Category D]
    {P0 P1 Qt Qs Rt Rs Z Z' Yt Ys Wt Ws : D} (u : P0 ⟶ P1) (ms : P1 ⟶ Qs) (mt : P0 ⟶ Qt)
    (C3t : Qt ⟶ Rt) (Aτ : Rt ⟶ Rs) (C3s : Qs ≅ Rs) (As : Rs ≅ Z) (At : Rt ⟶ Z') (Aeq : Z' ⟶ Z)
    (cht : P0 ⟶ Yt) (trt : Yt ⟶ Wt) (C3tq : Wt ⟶ Z') (tre : Wt ⟶ Ws) (C3sq : Ws ⟶ Z)
    (chs : P1 ⟶ Ys) (trs : Ys ⟶ Ws) (trc : Yt ⟶ Ys)
    (hτa : Aτ ≫ As.hom = At ≫ Aeq) (L3 : tre ≫ C3sq = C3tq ≫ Aeq)
    (L2t : cht ≫ trt ≫ C3tq = mt ≫ C3t ≫ At) (L2s : chs ≫ trs ≫ C3sq = ms ≫ C3s.hom ≫ As.hom)
    (L1 : u ≫ chs = cht ≫ trc) (E : trc ≫ trs = trt ≫ tre) :
    u ≫ ms = mt ≫ C3t ≫ Aτ ≫ C3s.inv := by
  rw [← cancel_mono (C3s.hom ≫ As.hom)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← L2s, reassoc_of% L1, reassoc_of% E, L3, hτa, reassoc_of% L2t]

/-- **The canonical transition of the inverse image of `N^a` along a represented morphism is the
module attached to the canonical scheme transition of `q^*N`** (Stacks 03LU, 03DX): the
identification `c^*(N^a) ≅ (q^*N)^a` of
`AlgebraicGeometry.Space.modulePullbackRepresentedQuasicoherentIso` carries the transport of
`N^a` along `t ≫ c = s ≫ c` to the transition attached to
`AlgebraicGeometry.Space.canonicalSchemeTransition`. -/
theorem transitionCommutes_representedQuasicoherent
    (hc : @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ (representedSpaceMap B S hS t)
        (representedSpaceMap B S hS q) =
      @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ (representedSpaceMap B S hS s)
        (representedSpaceMap B S hS q)) :
    TransitionCommutes B S hS
      (U := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      (V := ⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩)
      (a := representedSpaceMap B S hS t) (b := representedSpaceMap B S hS s)
      (modulePullbackUnflatten (X := ⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩)
        (Y := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
        (a := representedSpaceMap B S hS t) (b := representedSpaceMap B S hS s)
        (representedSpaceMap B S hS q)
        (pullbackTransport (T := ⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩)
          (X := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩)
          ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj N).obj hc))
      (representedSchemeTransition B S hS t s (quasicoherentPullbackObj B S hS q N)
        (canonicalSchemeTransition B S hS t s q hts N))
      (modulePullbackRepresentedQuasicoherentIso B S hS q N).hom := by
  have L2t := compHom_comp_modulePullbackRepresentedQuasicoherentIso_hom B S hS t q N
  have L2s := compHom_comp_modulePullbackRepresentedQuasicoherentIso_hom B S hS s q N
  have L3 := pullbackTransport_comp_modulePullbackRepresentedQuasicoherentIso_hom B S hS hts
    (congrArg (representedSpaceMap B S hS) hts) N
  have L1 := modulePullbackUnflatten_comp_compHom B S hS (representedSpaceMap B S hS t)
    (representedSpaceMap B S hS s) (representedSpaceMap B S hS q)
    ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj N).obj
    (pullbackTransport _ hc)
  have hτ : canonicalSchemeTransition B S hS t s q hts N ≫
      (quasicoherentPullbackCompIso B S hS s q N).hom =
      (quasicoherentPullbackCompIso B S hS t q N).hom ≫
        quasicoherentPullbackEqToHom B S hS hts N := by
    simp only [canonicalSchemeTransition, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hτa := congrArg (fun k => ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map
    k).hom) hτ
  simp only [representedQuasicoherentSchemeEquivalence_map_comp_hom] at hτa
  have E := pullbackTransport_comp_eq_comp B S hS
    ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj N).obj hc
    (algebraicSpacesComp_representedSpaceMap B S hS s q)
    (algebraicSpacesComp_representedSpaceMap B S hS t q)
    (congrArg (representedSpaceMap B S hS) hts)
  exact transitionCommutes_representedQuasicoherent_core _ _ _ _ _
    (modulePullbackRepresentedQuasicoherentIso B S hS s (quasicoherentPullbackObj B S hS q N))
    ((ObjectProperty.ι _).mapIso
      ((representedQuasicoherentSchemeEquivalence B S hS R).functor.mapIso
        (quasicoherentPullbackCompIso B S hS s q N))) _ _ _ _ _ _ _ _ _ _ hτa L3 L2t L2s L1 E

end Represented

/-! ### Rewriting the transitions of a compatibility -/

section TransitionCommutesEq

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A compatibility may be rewritten along an equality of its first transition. -/
theorem transitionCommutes_of_eq_left {U V : AlgebraicSpaces B S hS} {a b : V ⟶ U}
    {F G : Modules.{u, u} B S hS U.1 U.2}
    {α α' : (modulePullback B S hS a).obj F ⟶ (modulePullback B S hS b).obj F}
    {β : (modulePullback B S hS a).obj G ⟶ (modulePullback B S hS b).obj G} {g : F ⟶ G}
    (e : α = α') (h : TransitionCommutes B S hS α β g) : TransitionCommutes B S hS α' β g :=
  e ▸ h

/-- A compatibility may be rewritten along an equality of its morphism of modules. -/
theorem transitionCommutes_of_eq_right {U V : AlgebraicSpaces B S hS} {a b : V ⟶ U}
    {F G : Modules.{u, u} B S hS U.1 U.2}
    {α : (modulePullback B S hS a).obj F ⟶ (modulePullback B S hS b).obj F}
    {β : (modulePullback B S hS a).obj G ⟶ (modulePullback B S hS b).obj G} {g g' : F ⟶ G}
    (e : g = g') (h : TransitionCommutes B S hS α β g) : TransitionCommutes B S hS α β g' :=
  e ▸ h

end TransitionCommutesEq

/-! ### Isomorphisms of quasi-coherent modules from identifications on the atlas -/

section ChartIsos

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X'' : AlgebraicSpaces B S hS}
  (P'' : Presentation B S hS X''.obj X''.property)
  {M'' : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj P''.U).ringCatSheaf).FullSubcategory}
  (τ'' : quasicoherentPullbackObj B S hS P''.target M'' ⟶
    quasicoherentPullbackObj B S hS P''.source M'')
  (Y₁ Y₂ : QuasicoherentSheaves.{u, u} B S hS X''.obj X''.property)
  (χ₁ : (modulePullback B S hS (presentationAtlas P'')).obj Y₁.obj ≅
    ((representedQuasicoherentSchemeEquivalence B S hS P''.U).functor.obj M'').obj)
  (hχ₁ : TransitionCommutes B S hS (U := (presentationGroupoid P'').objects)
    (V := (presentationGroupoid P'').arrows) (a := (presentationGroupoid P'').target)
    (b := (presentationGroupoid P'').source)
    (spaceBaseDescent B S hS (presentationGroupoid P'') (presentationAtlas P'')
      (presentationAtlas_comm P'') Y₁.obj)
    (presentationSchemeTransition P'' M'' τ'') χ₁.hom)
  (χ₂ : (modulePullback B S hS (presentationAtlas P'')).obj Y₂.obj ≅
    ((representedQuasicoherentSchemeEquivalence B S hS P''.U).functor.obj M'').obj)
  (hχ₂ : TransitionCommutes B S hS (U := (presentationGroupoid P'').objects)
    (V := (presentationGroupoid P'').arrows) (a := (presentationGroupoid P'').target)
    (b := (presentationGroupoid P'').source)
    (spaceBaseDescent B S hS (presentationGroupoid P'') (presentationAtlas P'')
      (presentationAtlas_comm P'') Y₂.obj)
    (presentationSchemeTransition P'' M'' τ'') χ₂.hom)

include hχ₁ hχ₂ in
/-- The morphism `χ₁ ≫ χ₂⁻¹` on the atlas carries the canonical transition of the inverse image of
`Y₁` to that of `Y₂`. -/
theorem transitionCommutes_chartIsos :
    TransitionCommutes B S hS (U := (presentationGroupoid P'').objects)
      (V := (presentationGroupoid P'').arrows) (a := (presentationGroupoid P'').target)
      (b := (presentationGroupoid P'').source)
      (spaceBaseDescent B S hS (presentationGroupoid P'') (presentationAtlas P'')
        (presentationAtlas_comm P'') Y₁.obj)
      (spaceBaseDescent B S hS (presentationGroupoid P'') (presentationAtlas P'')
        (presentationAtlas_comm P'') Y₂.obj) (χ₁.hom ≫ χ₂.inv) :=
  transitionSquare_comp (modulePullback B S hS (presentationGroupoid P'').target)
    (modulePullback B S hS (presentationGroupoid P'').source) _
    (presentationSchemeTransition P'' M'' τ'') _ χ₁.hom χ₂.inv hχ₁
    (transitionSquare_symm (modulePullback B S hS (presentationGroupoid P'').target)
      (modulePullback B S hS (presentationGroupoid P'').source) _
      (presentationSchemeTransition P'' M'' τ'') χ₂ hχ₂)

/-- The isomorphism of the groupoid modules of `Y₁` and `Y₂` attached to `χ₁ ≫ χ₂⁻¹`. -/
def presentationGroupoidIsoOfChartIsos :
    (presentationQuasicoherentEquivalence P'').functor.obj Y₁ ≅
      (presentationQuasicoherentEquivalence P'').functor.obj Y₂ :=
  QuasicoherentModule.isoMk (χ₁ ≪≫ χ₂.symm)
    ((presentationQuasicoherentEquivalence_compatible_iff P'' (χ₁ ≪≫ χ₂.symm).hom).2
      (transitionCommutes_chartIsos P'' τ'' Y₁ Y₂ χ₁ hχ₁ χ₂ hχ₂))

/-- **An isomorphism of quasi-coherent modules from identifications on the atlas** (Stacks 03M3):
two quasi-coherent `𝒪_X`-modules whose inverse images along the atlas of a presentation are
identified with a common `M''^a`, both carrying the canonical transition to the same `τ''^a`, are
isomorphic, by the isomorphism whose inverse image along the atlas is `χ₁ ≫ χ₂⁻¹`.  No cocycle
condition on `τ''` is needed. -/
def presentationIsoOfChartIsos : Y₁ ≅ Y₂ :=
  (presentationQuasicoherentEquivalence P'').functor.preimageIso
    (presentationGroupoidIsoOfChartIsos P'' τ'' Y₁ Y₂ χ₁ hχ₁ χ₂ hχ₂)

/-- The morphism underlying the isomorphism of groupoid modules is `χ₁ ≫ χ₂⁻¹`. -/
theorem presentationGroupoidIsoOfChartIsos_hom_hom :
    (presentationGroupoidIsoOfChartIsos P'' τ'' Y₁ Y₂ χ₁ hχ₁ χ₂ hχ₂).hom.hom = χ₁.hom ≫ χ₂.inv :=
  QuasicoherentModule.isoMk_hom_hom _ _

/-- **The inverse image along the atlas of the isomorphism from identifications on the atlas is
`χ₁ ≫ χ₂⁻¹`.** -/
theorem modulePullback_map_presentationIsoOfChartIsos_hom :
    (modulePullback B S hS (presentationAtlas P'')).map
        (presentationIsoOfChartIsos P'' τ'' Y₁ Y₂ χ₁ hχ₁ χ₂ hχ₂).hom.hom ≫ χ₂.hom = χ₁.hom := by
  have h := congrArg QuasicoherentModule.Hom.hom
    ((presentationQuasicoherentEquivalence P'').functor.map_preimage
      (presentationGroupoidIsoOfChartIsos P'' τ'' Y₁ Y₂ χ₁ hχ₁ χ₂ hχ₂).hom)
  rw [presentationQuasicoherentEquivalence_functor_map_hom,
    presentationGroupoidIsoOfChartIsos_hom_hom] at h
  have h4 : (modulePullback B S hS (presentationAtlas P'')).map
      (presentationIsoOfChartIsos P'' τ'' Y₁ Y₂ χ₁ hχ₁ χ₂ hχ₂).hom.hom = χ₁.hom ≫ χ₂.inv := h
  exact (congrArg (· ≫ χ₂.hom) h4).trans ((Category.assoc _ _ _).trans
    ((congrArg (χ₁.hom ≫ ·) χ₂.inv_hom_id).trans (Category.comp_id _)))

end ChartIsos

/-! ### The presentation of `T ×_X P` over the presentation of the base -/

namespace RelativeProjPoints

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : P ⟶ X.obj}
  (d : RelativeProjPoints B S hS π)

/-- **The morphism of base changes `V ×_X P ⟶ U ×_X P` over a morphism `k : V ⟶ U` of test
objects** compatible with the points of `X`. -/
def fibreMapOver {U V : BigFppfOver B S hS} {u : yoneda.obj U ⟶ X.obj} {v : yoneda.obj V ⟶ X.obj}
    (k : V ⟶ U) (hv : yoneda.map k ≫ u = v) : d.fibre V v ⟶ d.fibre U u :=
  d.fibreLift (d.fibreHom V v ≫ k) (d.fibreToSpace V v) (by
    rw [(d.isPullback V v).w, CategoryTheory.Functor.map_comp, Category.assoc, hv])

/-- The morphism of base changes over `k` lies over `k`. -/
theorem liesOver_fibreMapOver {U V : BigFppfOver B S hS} {u : yoneda.obj U ⟶ X.obj}
    {v : yoneda.obj V ⟶ X.obj} (k : V ⟶ U) (hv : yoneda.map k ≫ u = v) :
    d.LiesOver (d.fibreMapOver k hv) k :=
  ⟨d.fibreLift_comp_fibreHom _ _ _, d.map_fibreLift_comp_fibreToSpace _ _ _⟩

variable (Px : Presentation B S hS X.obj X.property) (hP : IsAlgebraicSpace B S hS P)
  (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X.obj)

/-- **The presentation `T ×_X P = (T_U ×_X P)/(T_R ×_X P)` of the base change of `π` along a point
`f : T ⟶ X`**, over the presentation `T = T_U/T_R` of `T`
(`AlgebraicGeometry.Space.Presentation.alongPoint`). -/
abbrev pointFibrePresentation :
    Presentation B S hS
      (schemeSpace (d.fibre T f) :
        AlgebraicSpaces B S hS).obj
      (schemeSpace (d.fibre T f) :
        AlgebraicSpaces B S hS).property :=
  (d.baseChangePoint T f).spacePresentation
    (X := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩) (Px.alongPoint f)
    (isAlgebraicSpace_yoneda B S hS (d.fibre T f))

/-- The atlas `T_U ×_X P ⟶ T ×_X P` of the presentation of the base change. -/
abbrev pointFibreAtlasMap :
    d.fibre (Px.alongPoint f).U ((Px.alongPoint f).toSpace ≫ f) ⟶ d.fibre T f :=
  d.baseChangePointMap T f (Px.alongPoint f).U (Px.alongPoint f).toSpace

/-- **The morphism `T_U ×_X P ⟶ U ×_X P` of the presenting schemes**, over `T_U ⟶ U`. -/
abbrev pointFibreChartMap :
    d.fibre (Px.alongPoint f).U ((Px.alongPoint f).toSpace ≫ f) ⟶ d.fibre Px.U Px.toSpace :=
  d.fibreMapOver (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f)

/-- The relation morphism `T_R ⟶ R` is compatible with the points of `X`. -/
theorem map_alongPointRelationMap_comp_relationPoint :
    yoneda.map (Px.alongPointRelationMap f) ≫ relationPoint Px =
      relationPoint (Px.alongPoint f) ≫ f := by
  rw [relationPoint, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
    Presentation.alongPointRelationMap_comp_target, CategoryTheory.Functor.map_comp,
    Category.assoc, Px.map_alongPointToAtlas_comp_toSpace', ← Category.assoc]

/-- **The morphism `T_R ×_X P ⟶ R ×_X P` of the relation schemes**, over `T_R ⟶ R`. -/
abbrev pointFibreRelationMap :
    d.fibre (Px.alongPoint f).R (relationPoint (Px.alongPoint f) ≫ f) ⟶
      d.fibre Px.R (relationPoint Px) :=
  d.fibreMapOver (Px.alongPointRelationMap f) (map_alongPointRelationMap_comp_relationPoint Px T f)

/-- The atlas of the presentation of the base change is the represented atlas morphism. -/
theorem pointFibrePresentation_toSpace :
    (d.pointFibrePresentation Px T f).toSpace = yoneda.map (d.pointFibreAtlasMap Px T f) :=
  rfl

/-- The atlas morphism lies over the chart `T_U ⟶ T`. -/
theorem liesOver_pointFibreAtlasMap :
    d.LiesOver (d.pointFibreAtlasMap Px T f) (Px.alongPointToPoint f) :=
  ⟨(d.fibreLift_comp_fibreHom _ _ _).trans (congrArg (d.fibreHom _ _ ≫ ·)
      (Yoneda.fullyFaithful.preimage_map (Px.alongPointToPoint f))),
    d.map_baseChangePointMap_comp_fibreToSpace T f _ _⟩

/-- The target projection `T_R ×_X P ⟶ T_U ×_X P` of the presentation of the base change, typed
through the base changes of `π`. -/
def pointFibreTargetMap :
    d.fibre (Px.alongPoint f).R (relationPoint (Px.alongPoint f) ≫ f) ⟶
      d.fibre (Px.alongPoint f).U ((Px.alongPoint f).toSpace ≫ f) :=
  (d.pointFibrePresentation Px T f).target

/-- The source projection `T_R ×_X P ⟶ T_U ×_X P` of the presentation of the base change, typed
through the base changes of `π`. -/
def pointFibreSourceMap :
    d.fibre (Px.alongPoint f).R (relationPoint (Px.alongPoint f) ≫ f) ⟶
      d.fibre (Px.alongPoint f).U ((Px.alongPoint f).toSpace ≫ f) :=
  (d.pointFibrePresentation Px T f).source

/-- The target projection of the presentation of the base change, unfolded. -/
theorem pointFibrePresentation_target :
    (d.pointFibrePresentation Px T f).target = d.pointFibreTargetMap Px T f := rfl

/-- The source projection of the presentation of the base change, unfolded. -/
theorem pointFibrePresentation_source :
    (d.pointFibrePresentation Px T f).source = d.pointFibreSourceMap Px T f := rfl

/-- The target projection of the presentation of the base change lies over the target projection
of `T_R ⇉ T_U`. -/
theorem liesOver_pointFibreTarget :
    d.LiesOver (d.pointFibreTargetMap Px T f) (Px.alongPointTarget f) :=
  LiesOver.of_baseChangePoint (RelativeProjPoints.liesOver_spaceTarget (d.baseChangePoint T f)
    (X := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩) (Px.alongPoint f)
    (isAlgebraicSpace_yoneda B S hS (d.fibre T f)))

/-- The source projection of the presentation of the base change lies over the source projection
of `T_R ⇉ T_U`. -/
theorem liesOver_pointFibreSource :
    d.LiesOver (d.pointFibreSourceMap Px T f) (Px.alongPointSource f) :=
  LiesOver.of_baseChangePoint (RelativeProjPoints.liesOver_spaceSource (d.baseChangePoint T f)
    (X := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩) (Px.alongPoint f)
    (isAlgebraicSpace_yoneda B S hS (d.fibre T f)))

/-- The base change morphism `T ×_X P ⟶ P`, as a morphism of algebraic spaces. -/
abbrev pointFibreSpaceMap :
    (schemeSpace (d.fibre T f) :
      AlgebraicSpaces B S hS) ⟶ ⟨P, hP⟩ :=
  ObjectProperty.homMk (d.fibreToSpace T f)

/-- **The atlases of the presentations of `T ×_X P` and of `P` are compatible.** -/
theorem presentationAtlas_comp_pointFibreSpaceMap :
    presentationAtlas (d.pointFibrePresentation Px T f) ≫ d.pointFibreSpaceMap hP T f =
      representedSpaceMap B S hS (d.pointFibreChartMap Px T f) ≫
        presentationAtlas (d.spacePresentation Px hP) :=
  ObjectProperty.hom_ext _ ((d.map_baseChangePointMap_comp_fibreToSpace T f _ _).trans
    (d.liesOver_fibreMapOver _ _).2.symm)

/-- The morphisms of the presenting schemes commute with the target projections. -/
theorem pointFibreTarget_comp_chartMap :
    d.pointFibreTargetMap Px T f ≫ d.pointFibreChartMap Px T f =
      d.pointFibreRelationMap Px T f ≫ (d.spacePresentation Px hP).target :=
  LiesOver.eq ((d.liesOver_fibreMapOver _ _).comp (d.liesOver_pointFibreTarget Px T f))
    ((d.liesOver_spaceTarget Px hP).comp (d.liesOver_fibreMapOver _ _))
    (Px.alongPointRelationMap_comp_target f).symm

/-- The morphisms of the presenting schemes commute with the source projections. -/
theorem pointFibreRelationMap_comp_source :
    d.pointFibreRelationMap Px T f ≫ (d.spacePresentation Px hP).source =
      d.pointFibreSourceMap Px T f ≫ d.pointFibreChartMap Px T f :=
  LiesOver.eq ((d.liesOver_spaceSource Px hP).comp (d.liesOver_fibreMapOver _ _))
    ((d.liesOver_fibreMapOver _ _).comp (d.liesOver_pointFibreSource Px T f))
    (Px.alongPointRelationMap_comp_source f)

/-- The two projections of the presentation of the base change have the same composite with its
atlas morphism. -/
theorem pointFibreTarget_comp_atlasMap :
    d.pointFibreTargetMap Px T f ≫ d.pointFibreAtlasMap Px T f =
      d.pointFibreSourceMap Px T f ≫ d.pointFibreAtlasMap Px T f :=
  LiesOver.eq ((d.liesOver_pointFibreAtlasMap Px T f).comp (d.liesOver_pointFibreTarget Px T f))
    ((d.liesOver_pointFibreAtlasMap Px T f).comp (d.liesOver_pointFibreSource Px T f))
    (Px.alongPointTarget_comp_toPoint f)

end RelativeProjPoints

end AlgebraicGeometry.Space

end
