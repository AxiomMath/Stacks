module

public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.FreeSectionsPurity
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionFromSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.EtaleSourceDecency
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeConditions
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFiniteReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.ExistenceFreeSectionsAlongFibreChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.FreeSectionsAffineNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.ImpurityFlatAscent
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityAscentHenselianReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.UniversalPurityRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleEtaleChartTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactAffineMorphism

/-!
# Stacks 0CW4: purity implies universal purity for a flat module

In the standing situation of Stacks 0CV6 — a decent, finite type morphism `f : X ⟶ Y` of
algebraic spaces over `S`, a finite type quasi-coherent `𝒪_X`-module `ℱ` and a point `y` of `Y` —
if `ℱ` is flat over `Y` at every point of `X` lying over `y` and pure above `y`, then `ℱ` is
universally pure above `y`.

## The proof

The source reduces, by Stacks 0CVG, to a strictly henselian local base and works there. The
argument here follows the same two steps over a Zariski local base, which suffices:

* Stacks 0CVW, in the form
  `AlgebraicGeometry.Space.exists_affineChart_hasFreeSectionsAlongFibre_chartFibre`, produces an
  affine étale chart `Y₁ ⟶ Y` through a point `w` over `y`, an affine étale chart `U` of `X`
  covering `X ×_Y Y₁`, and the conclusion of Stacks 05L1 for `U ⟶ Y₁` at `w`: an elementary
  étale neighbourhood of `w` and an affine scheme `Z'` over the spectrum of its local ring with
  free global sections. By `AlgebraicGeometry.HasFreeSectionsAlongFibreOver.exists_affine` the
  neighbourhood may be taken affine, hence an object `V` of the site, with a point `v`.
* The base change of the situation to `Spec 𝒪_{V, v}`,
  `AlgebraicGeometry.Space.PrePureSituation.specStalkPointedOver`, is flat over `Y` at its closed
  point, so Stacks 0CVG part (2) reduces universal purity of `ℱ` to that of the base change; and
  `AlgebraicGeometry.Space.isUniversallyPureAbove_of_isPureAbove_of_isEtale` reduces the latter
  to an étale morphism `Z' ⟶ X ×_Y Spec 𝒪_{V, v}` whose image contains the closed fibre and
  along which the module is universally pure — the two parts of Stacks 0CW3, the containment of
  the relative assassin being supplied by purity of `ℱ` above `y` through the limit presentation
  of `Spec 𝒪_{V, v}`.
* The étale morphism is `Z'` itself, an object of the site because it is of finite type over
  `Spec 𝒪_{V, v}`. Its image contains the closed fibre because `V` is elementary, so that over the
  closed point the fibre product `U ×_{Y₁} Spec 𝒪_{V, v}` has the points of the fibre of `U`
  over `w`. The pulled-back module is universally pure by More on Flatness, Stacks 05K6, in the
  form `AlgebraicGeometry.isUniversallyPureRelative_of_free_globalSections`, read on algebraic
  spaces by `AlgebraicGeometry.Space.isUniversallyPureAbove_of_isUniversallyPureAlong_represented`.

## Main results

* `AlgebraicGeometry.Space.isUniversallyPureAbove_of_flat_of_isPureAbove`: **Stacks 0CW4.**
* `AlgebraicGeometry.Space.isPureRelative_iff_isUniversallyPureRelative_of_flat`: **Stacks 0CW5**,
  with its substantive implication
  `AlgebraicGeometry.Space.isUniversallyPureRelative_of_flat_of_isPureRelative`.

## References

* [Stacks Project, Tag 0CW4](https://stacks.math.columbia.edu/tag/0CW4)
* [Stacks Project, Tag 0CW5](https://stacks.math.columbia.edu/tag/0CW5)
* [Stacks Project, Tag 0CVG](https://stacks.math.columbia.edu/tag/0CVG)
* [Stacks Project, Tag 0CVW](https://stacks.math.columbia.edu/tag/0CVW)
* [Stacks Project, Tag 05K6](https://stacks.math.columbia.edu/tag/05K6)
* [Stacks Project, Tag 0CW3](https://stacks.math.columbia.edu/tag/0CW3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v₁ u₁

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
private local instance (priority := high) hasPullbacks_presheaf_UniversalPurityOfFlatPure :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

private local instance (priority := high) hasPullback_presheaf_UniversalPurityOfFlatPure
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_UniversalPurityOfFlatPure B S hS).has_limit _

/-- **The base change of a lift into a fibre product.** Let `L : U ⟶ Y₁ ×_Y X` be induced by
`u : U ⟶ Y₁` and `e : U ⟶ X`, let `k : T ⟶ Y₁`, and let `R = U ×_{Y₁} T` (any pullback square
`(a, b)`). Then the square formed by `a : R ⟶ U`, the induced `R ⟶ T ×_Y X`, `L`, and the induced
`T ×_Y X ⟶ Y₁ ×_Y X` is a pullback: base changing `L` along `T ⟶ Y₁` gives the induced morphism
`R ⟶ T ×_Y X`. -/
theorem _root_.CategoryTheory.Limits.isPullback_pullbackLift_baseChange {C : Type u₁}
    [Category.{v₁} C] [HasPullbacks C] {U X Y Y₁ T R : C} (q : Y₁ ⟶ Y) (f : X ⟶ Y) (u : U ⟶ Y₁)
    (e : U ⟶ X) (hsq : u ≫ q = e ≫ f) (k : T ⟶ Y₁) (g' : T ⟶ Y) (hk : k ≫ q = g') (a : R ⟶ U)
    (b : R ⟶ T) (hab : IsPullback a b u k) :
    IsPullback a
      (pullback.lift b (a ≫ e) (by rw [← hk, ← Category.assoc, ← hab.w, Category.assoc, hsq,
        Category.assoc]) : R ⟶ pullback g' f)
      (pullback.lift u e hsq)
      (pullback.lift (pullback.fst g' f ≫ k) (pullback.snd g' f)
        (by rw [Category.assoc, hk, pullback.condition])) := by
  subst hk
  refine IsPullback.of_bot (v₂₁ := pullback.fst (k ≫ q) f) (v₂₂ := pullback.fst q f)
    (h₃₁ := k) ?_ ?_ ?_
  · simpa only [pullback.lift_fst] using hab
  · apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst,
        pullback.lift_fst_assoc, hab.w]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd,
        pullback.lift_snd]
  · refine IsPullback.of_right (h₁₂ := pullback.snd q f) (v₁₃ := f) (h₂₂ := q) ?_ ?_ ?_
    · simpa only [pullback.lift_snd] using (IsPullback.of_hasPullback (k ≫ q) f).flip
    · rw [pullback.lift_fst]
    · exact (IsPullback.of_hasPullback q f).flip

/-- Two points of a pullback square of schemes with the same images in both legs agree, provided
the second leg of the cospan is an isomorphism on residue fields at their common image. -/
private theorem _root_.CategoryTheory.IsPullback.eq_of_fst_eq_of_snd_eq_of_isIso_residueFieldMap
    {P X Y T : AlgebraicGeometry.Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ T}
    {g : Y ⟶ T} (h : IsPullback fst snd f g) {z z' : P} (hfst : fst z = fst z')
    (hsnd : snd z = snd z') (hiso : IsIso (g.residueFieldMap (snd z'))) : z = z' := by
  have key : ∀ p : P, pullback.fst f g (h.isoPullback.hom p) = fst p ∧
      pullback.snd f g (h.isoPullback.hom p) = snd p := fun p =>
    ⟨(AlgebraicGeometry.Scheme.Hom.comp_apply _ _ _).symm.trans (by rw [h.isoPullback_hom_fst]),
      (AlgebraicGeometry.Scheme.Hom.comp_apply _ _ _).symm.trans (by rw [h.isoPullback_hom_snd])⟩
  refine h.isoPullback.hom.isOpenEmbedding.injective
    (AlgebraicGeometry.Scheme.Pullback.eq_of_fst_eq_of_snd_eq_of_isIso_residueFieldMap f g _ _
      ?_ ?_ ?_)
  · rw [(key z).1, (key z').1, hfst]
  · rw [(key z).2, (key z').2, hsnd]
  · rwa [(key z').2]

/-- In a pullback square of schemes `P = X ×_T Y`, let `g : Y ⟶ T` be an isomorphism on residue
fields at `y`, and let `ℓ : Z ⟶ P` be such that the fibre of `f : X ⟶ T` over `g y` is the image
of the fibre of `ℓ ≫ snd` over `y`. Then every point of `P` over `y` lies in the image of `ℓ`. -/
private theorem _root_.CategoryTheory.IsPullback.mem_range_of_preimage_eq_image
    {P X Y T Z : AlgebraicGeometry.Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ T}
    {g : Y ⟶ T} (h : IsPullback fst snd f g) (ℓ : Z ⟶ P) {y : Y} {t : T} (hy : g y = t)
    (hcov : f ⁻¹' {t} = (ℓ ≫ fst) '' ((ℓ ≫ snd) ⁻¹' {y}))
    (hiso : IsIso (g.residueFieldMap y)) {p : P} (hp : snd p = y) : p ∈ Set.range ℓ := by
  have hfp : fst p ∈ f ⁻¹' {t} := by
    change f (fst p) = t
    rw [← AlgebraicGeometry.Scheme.Hom.comp_apply fst f p, h.w,
      AlgebraicGeometry.Scheme.Hom.comp_apply, hp, hy]
  rw [hcov] at hfp
  obtain ⟨z, hz, hzp⟩ := hfp
  refine ⟨z, h.eq_of_fst_eq_of_snd_eq_of_isIso_residueFieldMap
    ((AlgebraicGeometry.Scheme.Hom.comp_apply ℓ fst z).symm.trans hzp)
    ((AlgebraicGeometry.Scheme.Hom.comp_apply ℓ snd z).symm.trans (hz.trans hp.symm)) ?_⟩
  rwa [hp]

/-- Let `σ : W ⟶ T` be an elementary étale neighbourhood of `t` at `x₀`, and let `P` be a fibre
product of `g : U ⟶ T` with `Spec 𝒪_{W, x₀} ⟶ W ⟶ T`. If `ℓ : Z ⟶ P` is such that the fibre of
`g` over `t` is the image under `c = ℓ ≫ fst` of the fibre of `a = ℓ ≫ snd` over the closed
point, then every point of `P` over the closed point lies in the image of `ℓ`. -/
private theorem _root_.CategoryTheory.IsPullback.mem_range_of_isElementary
    {P U W T Z : AlgebraicGeometry.Scheme.{u}} {g : U ⟶ T} {σ : W ⟶ T} [Etale σ] {x₀ : W}
    {t : T} (hσ : σ x₀ = t) (hres : IsIso (σ.residueFieldMap x₀))
    {k : Spec (.of (W.presheaf.stalk x₀)) ⟶ T} (hk : k = W.fromSpecStalk x₀ ≫ σ)
    {fst : P ⟶ U} {snd : P ⟶ Spec (.of (W.presheaf.stalk x₀))} (h : IsPullback fst snd g k)
    (ℓ : Z ⟶ P) {c : Z ⟶ U} {a : Z ⟶ Spec (.of (W.presheaf.stalk x₀))} (hc : ℓ ≫ fst = c)
    (ha : ℓ ≫ snd = a) (hcov : g ⁻¹' {t} = c '' (a ⁻¹' {IsLocalRing.closedPoint _}))
    {p : P} (hp : snd p = IsLocalRing.closedPoint _) : p ∈ Set.range ℓ := by
  subst hk hc ha
  let N : _root_.AlgebraicGeometry.EtaleNeighborhood T t := ⟨W, x₀, σ, hσ⟩
  have : N.IsElementary := N.isElementary_iff.2 hres
  exact h.mem_range_of_preimage_eq_image ℓ
    ((Scheme.Hom.comp_apply _ _ _).trans (by rw [Scheme.fromSpecStalk_closedPoint, hσ])) hcov
    (neighborhood_base_residueFieldMap_isIso N) hp

/-- Let `P` be a fibre product of `g : U ⟶ T` with `k : V ⟶ T`. A morphism `ℓ : Z ⟶ P` is étale as
soon as the morphism `Z ⟶ U ×_T V` it induces on the chosen pullback is. -/
private theorem _root_.CategoryTheory.IsPullback.etale_of_etale_lift
    {P U V T Z : AlgebraicGeometry.Scheme.{u}} {fst : P ⟶ U} {snd : P ⟶ V} {g : U ⟶ T}
    {k : V ⟶ T} (h : IsPullback fst snd g k) (ℓ : Z ⟶ P) {c : Z ⟶ U} {a : Z ⟶ V}
    (hc : ℓ ≫ fst = c) (ha : ℓ ≫ snd = a) {k' : V ⟶ T} (hk : k = k')
    (hca : c ≫ g = a ≫ k') (het : Etale (pullback.lift c a hca)) : Etale ℓ := by
  subst hc ha hk
  have hfac : ℓ ≫ h.isoPullback.hom = pullback.lift (ℓ ≫ fst) (ℓ ≫ snd) hca := by
    apply pullback.hom_ext
    · rw [Category.assoc, IsPullback.isoPullback_hom_fst, pullback.lift_fst]
    · rw [Category.assoc, IsPullback.isoPullback_hom_snd, pullback.lift_snd]
  rwa [← MorphismProperty.cancel_right_of_respectsIso @Etale _ h.isoPullback.hom, hfac]

/-! ### Auxiliary properties of morphisms -/

/-- **A decent morphism stays decent after precomposition with an étale morphism.** Every base
change of `g ≫ f` along a morphism from a representable presheaf is étale over the corresponding
base change of `f`, which is decent, and an algebraic space étale over a decent one is decent by
Stacks 0B4D. -/
theorem isDecent_comp_of_isEtale {F' F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF' : IsAlgebraicSpace B S hS F') (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (g : F' ⟶ F) (hg : IsEtale B S hS g) (f : F ⟶ G)
    (hf : IsDecent B S hS f) : IsDecent B S hS (g ≫ f) := by
  intro T h
  have hP : IsAlgebraicSpace B S hS (pullback h f) :=
    isAlgebraicSpace_pullback B S hS h f (isAlgebraicSpace_yoneda B S hS T) hF hG
  -- the projection to the base change of `f` is a base change of `g`, hence étale
  let Psp : AlgebraicSpaces B S hS := ⟨pullback h f, hP⟩
  let Fsp : AlgebraicSpaces B S hS := ⟨F, hF⟩
  let F'sp : AlgebraicSpaces B S hS := ⟨F', hF'⟩
  let ksp : Psp ⟶ Fsp := ObjectProperty.homMk (pullback.snd h f)
  let gsp : F'sp ⟶ Fsp := ObjectProperty.homMk g
  let Wsp := AlgebraicSpaces.fiberProduct B S hS ksp gsp
  let p : Wsp ⟶ Psp := ObjectProperty.homMk (pullback.fst ksp.hom gsp.hom)
  let r : Wsp ⟶ F'sp := ObjectProperty.homMk (pullback.snd ksp.hom gsp.hom)
  have hpull : IsPullback p r ksp gsp := by
    simpa [p, r] using AlgebraicSpaces.isPullback_fiberProduct B S hS ksp gsp
  exact isDecentSpace_of_iso B S hS (pullbackLeftPullbackSndIso h f g)
    (isDecentSpace_of_isEtale B S hS _
      (isAlgebraicSpace_pullback B S hS (pullback.snd h f) g hP hF' hF) hP
      (isEtale_of_isPullback B S hS r p gsp ksp hpull.flip hg) (hf T h))

/-- A morphism of the site whose underlying morphism of schemes is affine and locally of finite
type is of finite type as a morphism of algebraic spaces. -/
theorem isFiniteType_yoneda_map {V U : BigFppfOver B S hS} (k : V ⟶ U)
    [LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map k)]
    (haff : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map k)) :
    IsFiniteType B S hS (yoneda.map k) :=
  ⟨(holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget k).2 inferInstance,
    isQuasiCompact_yoneda_map_of_isAffineHom B S hS k haff⟩

variable {B S hS}

/-- **The base change to `Spec 𝒪_{V, v}` along an étale chart is flat at the closed point.** If
`a : V ⟶ Y` factors as a morphism `ν : V ⟶ Y₁` of the site which is étale on schemes followed by
an étale chart `q : Y₁ ⟶ Y`, then the morphism `Spec 𝒪_{V, v} ⟶ V ⟶ Y` of the pointed base
change `AlgebraicGeometry.Space.PrePureSituation.specStalkPointedOver` is flat at the closed point:
on the chart `q` it is the morphism of schemes `Spec 𝒪_{V, v} ⟶ V ⟶ Y₁`, a localization followed
by an étale morphism. -/
theorem PrePureSituation.isFlatAt_specStalkPointedOver (P : PrePureSituation.{u, u} B S hS)
    {V Y₁ : BigFppfOver B S hS} (ν : V ⟶ Y₁) [Etale ((BigFppfOver.toScheme B S hS).map ν)]
    (q : yoneda.obj Y₁ ⟶ P.Y)
    (hq : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (v : points B S hS (yoneda.obj V))
    (hv : pointsMap B S hS (yoneda.obj V) (yoneda.map ν ≫ q) v = P.y) :
    IsFlatAt B S hS (P.specStalkPointedOver V (yoneda.map ν ≫ q) v hv).g
      (P.specStalkPointedOver V (yoneda.map ν ≫ q) v hv).y' := by
  set c := P.specStalkPointedOver V (yoneda.map ν ≫ q) v hv
  let SS := BigFppfOver.specStalk B S hS V (pointsToScheme B S hS V v)
  let hs : SS ⟶ Y₁ := BigFppfOver.specStalkTo B S hS V (pointsToScheme B S hS V v) ≫ ν
  have hcg : c.g = yoneda.map hs ≫ q := by
    change yoneda.map _ ≫ yoneda.map ν ≫ q = _
    rw [Functor.map_comp, Category.assoc]
  obtain ⟨p, hp⟩ := Quot.exists_rep c.y'
  have hflat : Flat ((BigFppfOver.toScheme B S hS).map hs) := by
    rw [Functor.map_comp, BigFppfOver.toScheme_map_specStalkTo]
    exact MorphismProperty.comp_mem @Flat _ _ (flat_fromSpecStalk _ _) inferInstance
  have h2 := (isFlatAt_chart_iff B S hS c.g SS Y₁ (yoneda.map (𝟙 SS)) q hs
    (presheaf_yoneda_map_id_etale B S hS SS) hq
    (by rw [hcg, yoneda.map_id]; exact Category.id_comp _)
    p (IsLocalRing.closedPoint p.carrier)).1
    ((isFlatAt_yoneda_iff B S hS SS Y₁ hs p).2 (Flat.stalkMap _ _))
  have hid : pointsMap B S hS (yoneda.obj SS) (yoneda.map (𝟙 SS))
      (p.class B S hS (yoneda.obj SS)) = c.y' := by
    rw [yoneda.map_id]
    exact (congrFun (pointsMap_id B S hS _) _).trans hp
  exact hid ▸ h2

/-- **The pullback of a chart module along a morphism into the chart.** Let `U` be an étale
scheme chart of `X` and `cs : Z ⟶ U` a morphism of the site whose represented morphism, followed
by the chart, factors as `g ≫ pr`. Then the pullback of the chart module of `F` along `cs` is the
represented chart module of `g^* pr^* F`. -/
private noncomputable def chartModulePullbackIso {X : AlgebraicSpaces B S hS}
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (U : SmallEtale B S hS X.1) {Z : BigFppfOver B S hS} (cs : Z ⟶ U.obj.left)
    {Y : AlgebraicSpaces B S hS}
    (g : (⟨yoneda.obj Z, isAlgebraicSpace_yoneda B S hS Z⟩ : AlgebraicSpaces B S hS) ⟶ Y)
    (pr : Y ⟶ X)
    (hmap : representedSpaceMap B S hS cs ≫
      (ObjectProperty.homMk U.obj.hom : schemeSpace U.obj.left ⟶ X) = g ≫ pr) :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map cs)).obj
        (chartModule B S hS X.2 F U) ≅
      representedChartModule B S hS
        ((modulePullback B S hS (X := ⟨yoneda.obj Z, isAlgebraicSpace_yoneda B S hS Z⟩)
          (Y := ⟨yoneda.obj Z, isAlgebraicSpace_yoneda B S hS Z⟩)
          (ObjectProperty.homMk (Iso.refl _).hom)).obj
          ((modulePullback B S hS g).obj ((modulePullback B S hS pr).obj F))) :=
  let X'sp : AlgebraicSpaces B S hS := ⟨yoneda.obj Z, isAlgebraicSpace_yoneda B S hS Z⟩
  let aU : schemeSpace U.obj.left ⟶ X := ObjectProperty.homMk U.obj.hom
  let N := (modulePullback B S hS aU).obj F
  let e₁ : chartModule B S hS X.2 F U ≅ representedZariskiRestriction B S hS U.obj.left
      (isAlgebraicSpace_yoneda B S hS U.obj.left) N :=
    restrictToChartIsoRepresentedZariskiRestrictionPullback B S hS (X := X) U.obj.hom
      ((isEtale_iff_presheaf_of_yoneda B S hS U.obj.hom).2 U.property) F hF
  let e₂ : representedZariskiRestriction B S hS U.obj.left
      (isAlgebraicSpace_yoneda B S hS U.obj.left) N ≅
      restrictToChartScheme B S hS (yoneda.obj U.obj.left)
        (isAlgebraicSpace_yoneda B S hS U.obj.left) N (idEtaleChart B S hS U.obj.left) :=
    restrictToChartIsoRestrictToChartScheme B S hS _ N (selfChart B S hS U.obj.left)
  let e₃ := (nonempty_restrictToChartScheme_baseChange_of_isQuasicoherent cs N
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS aU F hF)).some
  let eG : (modulePullback B S hS (representedSpaceMap B S hS cs)).obj N ≅
      (modulePullback B S hS (ObjectProperty.homMk (Iso.refl (yoneda.obj Z)).hom :
        X'sp ⟶ X'sp)).obj ((modulePullback B S hS g).obj ((modulePullback B S hS pr).obj F)) :=
    (modulePullbackCompIso B S hS (representedSpaceMap B S hS cs) aU).app F ≪≫
      eqToIso (congrArg (fun m : X'sp ⟶ X => (modulePullback B S hS m).obj F) hmap) ≪≫
      ((modulePullbackCompIso B S hS g pr).app F).symm ≪≫
      ((modulePullbackIdIso B S hS X'sp).app _).symm
  (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map cs)).mapIso (e₁ ≪≫ e₂) ≪≫
    e₃.symm ≪≫
    (restrictToChartIsoRestrictToChartScheme B S hS _ _ (idEtaleChart B S hS Z)).symm ≪≫
    restrictToChartIso B S hS _ eG (idEtaleChart B S hS Z) ≪≫
    restrictToChartIsoRestrictToChartScheme B S hS _ _ (idEtaleChart B S hS Z)

/-! ### Stacks 0CW4 -/

/-- **Stacks 0CW4.** In the situation of Stacks 0CV6 — a decent, finite type morphism
`f : X ⟶ Y` of algebraic spaces over `S`, a finite type quasi-coherent `𝒪_X`-module `ℱ` and a
point `y` of `Y` — if `ℱ` is flat over `Y` at every point of `X` lying over `y` and `ℱ` is pure
above `y`, then `ℱ` is universally pure above `y`.

See the module docstring for the proof: Stacks 0CVW and 05L1 over an affine elementary étale
neighbourhood `V` of the base, the descent of Stacks 0CVG part (2) along the flat morphism
`Spec 𝒪_{V, v} ⟶ Y`, both parts of Stacks 0CW3 over `Spec 𝒪_{V, v}`, and Stacks 05K6 for the
affine scheme with free global sections that Stacks 05L1 produces. -/
@[stacks 0CW4]
theorem isUniversallyPureAbove_of_flat_of_isPureAbove (P : PrePureSituation.{u, u} B S hS)
    (hflat : ∀ x : points B S hS P.X, pointsMap B S hS P.X P.f x = P.y →
      x ∈ flatLocus B S hS P.hX P.f P.F)
    (hpure : IsPureAbove P) :
    IsUniversallyPureAbove P := by
  classical
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  -- Stacks 0CVW at an affine étale chart `q : Y₁ ⟶ Y` of the base
  obtain ⟨Y₁, q, U, ĝ, hsq, w, hY₁aff, -, hqet, hw, hLsurj, hLet, hlft, -, -, hfree⟩ :=
    exists_affineChart_hasFreeSectionsAlongFibre_chartFibre B S hS
      (X := ⟨P.X, P.hX⟩) (Y := ⟨P.Y, P.hY⟩) (ObjectProperty.homMk P.f) P.finiteType P.F
      (fun U => isFiniteType_restrictToChart B S hS ⟨P.X, P.hX⟩ P.F P.moduleQuasicoherent
        P.moduleFiniteType U) P.y hflat
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj Y₁) := hY₁aff
  have : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map ĝ) := hlft
  have : (chartModule B S hS P.hX P.F U).IsQuasicoherent :=
    isQuasicoherent_restrictToChart B S hS ⟨P.X, P.hX⟩ P.F P.moduleQuasicoherent U
  have : (chartModule B S hS P.hX P.F U).IsFiniteType :=
    isFiniteType_restrictToChart B S hS ⟨P.X, P.hX⟩ P.F P.moduleQuasicoherent
      P.moduleFiniteType U
  -- Stacks 05L1 over an affine elementary étale neighbourhood `σ : W ⟶ Y₁`
  obtain ⟨W, σ, wpt, hWaff, hσet, hσw, hσres, Z', αZ, cZ, hcommZ, hetZ, hcovZ, hZaff,
    hfreeZ⟩ := hfree.exists_affine
  have := hWaff
  have := hσet
  have := hZaff
  -- the neighbourhood is an object `V` of the site, étale over `Y₁` by `ν`
  have hWc : B.Contains W := contains_of_locallyOfFiniteType_of_quasiCompact B S hS (Y₀ := Y₁) σ
  let V : BigFppfOver B S hS := BigFppfOver.mk B S hS hWc (σ ≫ B.inclusion.map Y₁.hom)
  let ν : V ⟶ Y₁ := siteHomMk B S hS (T₁ := V) (T₂ := Y₁) σ rfl
  have : Etale ((BigFppfOver.toScheme B S hS).map ν) := hσet
  obtain ⟨v, hv0⟩ : ∃ v : points B S hS (yoneda.obj V), pointsToScheme B S hS V v = wpt :=
    ⟨(pointsEquivScheme B S hS V).symm wpt, (pointsEquivScheme B S hS V).apply_symm_apply wpt⟩
  subst hv0
  let a : yoneda.obj V ⟶ P.Y := yoneda.map ν ≫ q
  have hνv : pointsMap B S hS (yoneda.obj V) (yoneda.map ν) v = w := by
    apply injective_pointsToScheme B S hS Y₁
    rwa [pointsToScheme_pointsMap_yoneda]
  have hv : pointsMap B S hS (yoneda.obj V) a v = P.y := by
    change pointsMap B S hS (yoneda.obj V) (yoneda.map ν ≫ q) v = P.y
    rwa [pointsMap_comp_apply, hνv]
  have hetale : IsEtale B S hS a :=
    (isEtale_iff_presheaf_of_yoneda B S hS _).2 (etale_comp_of_scheme B S hS ν q hσet hqet)
  -- the pointed base change to `Spec 𝒪_{V, v}`, flat at the closed point
  let c := P.specStalkPointedOver V a v hv
  have hascent : HasFlatImpurityAscentData c :=
    hasFlatImpurityAscentData_of_isFlatAt P c (P.isFlatAt_specStalkPointedOver ν q hqet v hv)
  let x₀ := pointsToScheme B S hS V v
  let SS := BigFppfOver.specStalk B S hS V x₀
  let hs : SS ⟶ Y₁ := BigFppfOver.specStalkTo B S hS V x₀ ≫ ν
  have hTs : (BigFppfOver.toScheme B S hS).map hs = W.fromSpecStalk x₀ ≫ σ := by
    rw [Functor.map_comp, BigFppfOver.toScheme_map_specStalkTo]
    rfl
  have hcg : yoneda.map hs ≫ q = c.g := by
    change yoneda.map hs ≫ q = yoneda.map _ ≫ yoneda.map ν ≫ q
    rw [Functor.map_comp, Category.assoc]
  -- `Z'` is an object `Zs` of the site over `Spec 𝒪_{V, v}`
  have : Etale (pullback.lift cZ αZ hcommZ) := hetZ
  have : LocallyOfFiniteType αZ := by
    rw [← pullback.lift_snd cZ αZ hcommZ]
    exact MorphismProperty.comp_mem @LocallyOfFiniteType _ _ inferInstance inferInstance
  let αZ' : Z' ⟶ (BigFppfOver.toScheme B S hS).obj SS := αZ
  have : LocallyOfFiniteType αZ' := ‹LocallyOfFiniteType αZ›
  have : QuasiCompact αZ' := (inferInstance : QuasiCompact αZ)
  have hZc : B.Contains Z' :=
    contains_of_locallyOfFiniteType_of_quasiCompact B S hS (Y₀ := SS) αZ'
  let Zs : BigFppfOver B S hS := BigFppfOver.mk B S hS hZc (αZ ≫ B.inclusion.map SS.hom)
  let κ : Zs ⟶ SS := siteHomMk B S hS (T₁ := Zs) (T₂ := SS) αZ rfl
  have hUover : (BigFppfOver.toScheme B S hS).map ĝ ≫ B.inclusion.map Y₁.hom =
      B.inclusion.map U.obj.left.hom :=
    (B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map (Over.w ĝ))
  have hSSover : B.inclusion.map SS.hom = W.fromSpecStalk x₀ ≫ σ ≫ B.inclusion.map Y₁.hom := by
    rw [← Over.w (BigFppfOver.specStalkTo B S hS V x₀), Functor.map_comp]
    change (BigFppfOver.toScheme B S hS).map (BigFppfOver.specStalkTo B S hS V x₀) ≫ _ = _
    rw [BigFppfOver.toScheme_map_specStalkTo]
    rfl
  let cs : Zs ⟶ U.obj.left := siteHomMk B S hS (T₁ := Zs) (T₂ := U.obj.left) cZ (by
    change cZ ≫ B.inclusion.map U.obj.left.hom = αZ ≫ B.inclusion.map SS.hom
    rw [← hUover, hSSover, ← Category.assoc, hcommZ, Category.assoc, Category.assoc])
  have hℓ : cs ≫ ĝ = κ ≫ hs := by
    apply hom_ext_toScheme B S hS
    rwa [Functor.map_comp, Functor.map_comp, hTs]
  let ℓ : Zs ⟶ pullback ĝ hs := pullback.lift cs κ hℓ
  -- the base change of the cover `U ⟶ X ×_Y Y₁` to `Spec 𝒪_{V, v}`
  let L := pullback.lift (yoneda.map ĝ) U.obj.hom hsq
  let m0 : yoneda.obj (pullback ĝ hs) ⟶ pullback c.g P.f :=
    pullback.lift (yoneda.map (pullback.snd ĝ hs)) (yoneda.map (pullback.fst ĝ hs) ≫ U.obj.hom)
      ((congrArg (yoneda.map (pullback.snd ĝ hs) ≫ ·) hcg.symm).trans
        (by rw [← Category.assoc, ← Functor.map_comp, ← pullback.condition,
          Functor.map_comp, Category.assoc, hsq, Category.assoc]; rfl))
  let n0 : pullback c.g P.f ⟶ pullback q P.f :=
    pullback.lift (pullback.fst c.g P.f ≫ yoneda.map hs) (pullback.snd c.g P.f)
      ((Category.assoc _ _ _).trans ((congrArg (pullback.fst c.g P.f ≫ ·) hcg).trans
        pullback.condition))
  have SQ : IsPullback (yoneda.map (pullback.fst ĝ hs)) m0 L n0 :=
    isPullback_pullbackLift_baseChange q P.f (yoneda.map ĝ) U.obj.hom hsq
      (yoneda.map hs) c.g hcg (yoneda.map (pullback.fst ĝ hs)) (yoneda.map (pullback.snd ĝ hs))
      ((IsPullback.of_hasPullback ĝ hs).map yoneda)
  have hm0et : IsEtale B S hS m0 :=
    isEtale_of_isPullback_yoneda B S hS SQ ((isEtale_iff_presheaf_of_yoneda B S hS L).2 hLet)
  -- `ℓ` is étale: on schemes it is the étale morphism that Stacks 05L1 provides
  have sqS : IsPullback ((BigFppfOver.toScheme B S hS).map (pullback.fst ĝ hs))
      ((BigFppfOver.toScheme B S hS).map (pullback.snd ĝ hs))
      ((BigFppfOver.toScheme B S hS).map ĝ) ((BigFppfOver.toScheme B S hS).map hs) :=
    (IsPullback.of_hasPullback ĝ hs).map (BigFppfOver.toScheme B S hS)
  have hℓet : Etale ((BigFppfOver.toScheme B S hS).map ℓ) :=
    sqS.etale_of_etale_lift _ (c := cZ) (a := αZ)
      ((Functor.map_comp _ _ _).symm.trans (congrArg _ (pullback.lift_fst _ _ _)))
      ((Functor.map_comp _ _ _).symm.trans (congrArg _ (pullback.lift_snd _ _ _))) hTs hcommZ
      hetZ
  let gmap : yoneda.obj Zs ⟶ pullback c.g P.f := yoneda.map ℓ ≫ m0
  have hget : IsEtale B S hS gmap :=
    (isEtale_iff_presheaf_of_yoneda B S hS _).2
      (etale_comp_of_scheme B S hS ℓ m0 hℓet ((isEtale_iff_presheaf_of_yoneda B S hS m0).1 hm0et))
  have hgfst : gmap ≫ pullback.fst c.g P.f = yoneda.map κ :=
    (Category.assoc _ _ _).trans ((congrArg (yoneda.map ℓ ≫ ·) (pullback.lift_fst _ _ _)).trans
      ((yoneda.map_comp _ _).symm.trans (congrArg yoneda.map (pullback.lift_snd _ _ _))))
  have hgsnd : gmap ≫ pullback.snd c.g P.f = yoneda.map cs ≫ U.obj.hom :=
    (Category.assoc _ _ _).trans ((congrArg (yoneda.map ℓ ≫ ·) (pullback.lift_snd _ _ _)).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ U.obj.hom)
        ((yoneda.map_comp _ _).symm.trans (congrArg yoneda.map (pullback.lift_fst _ _ _))))))
  have : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map κ) :=
    ‹LocallyOfFiniteType αZ›
  have hκaff : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map κ) :=
    (inferInstance : _root_.AlgebraicGeometry.IsAffineHom αZ)
  let X'sp : AlgebraicSpaces B S hS := ⟨yoneda.obj Zs, isAlgebraicSpace_yoneda B S hS Zs⟩
  let gsp : X'sp ⟶ (⟨c.baseChange.X, c.baseChange.hX⟩ : AlgebraicSpaces B S hS) :=
    ObjectProperty.homMk gmap
  let e : EtaleOverSource c.baseChange :=
    { X' := X'sp
      g := gsp
      isEtale := hget
      finiteType := by
        change IsFiniteType B S hS (gmap ≫ pullback.fst c.g P.f)
        rw [hgfst]
        exact isFiniteType_yoneda_map B S hS κ hκaff
      decent := isDecent_comp_of_isEtale B S hS (isAlgebraicSpace_yoneda B S hS Zs)
        c.baseChange.hX c.baseChange.hY gmap hget _ c.baseChange.decent }
  refine isUniversallyPureAbove_of_isPureAbove_of_isEtale P hpure V a v hv hetale hascent e
    ?_ ?_
  · -- the image of `Z'` contains the fibre over the closed point
    intro x hx
    -- `m0`, a base change of the surjective cover, is surjective on points
    have hsurjSt : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
      inverseImage_isStableUnderBaseChange B S hS inferInstance
    have hm0s : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf m0 :=
      (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback SQ hLsurj
    obtain ⟨p, hp⟩ := isSurjective_of_presheafSurjective B S hS m0 hm0s x
    have hm0fst : m0 ≫ pullback.fst c.g P.f = yoneda.map (pullback.snd ĝ hs) :=
      pullback.lift_fst _ _ _
    have h6 : pointsMap B S hS (yoneda.obj (pullback ĝ hs)) (yoneda.map (pullback.snd ĝ hs)) p
        = BigFppfOver.specStalkClosedPoint B S hS V x₀ :=
      (congrArg (fun φ => pointsMap B S hS (yoneda.obj (pullback ĝ hs)) φ p) hm0fst).symm.trans
        (by rwa [pointsMap_comp_apply, hp])
    have hp₀ : (BigFppfOver.toScheme B S hS).map (pullback.snd ĝ hs)
        (pointsToScheme B S hS (pullback ĝ hs) p) =
          IsLocalRing.closedPoint (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk x₀) :=
      (pointsToScheme_pointsMap_yoneda B S hS _ p).symm.trans
        (by rw [h6]; exact BigFppfOver.pointsToScheme_specStalkClosedPoint B S hS V x₀)
    obtain ⟨z, hz⟩ := sqS.mem_range_of_isElementary hσw hσres hTs
      ((BigFppfOver.toScheme B S hS).map ℓ) (c := cZ) (a := αZ)
      ((Functor.map_comp _ _ _).symm.trans (congrArg _ (pullback.lift_fst _ _ _)))
      ((Functor.map_comp _ _ _).symm.trans (congrArg _ (pullback.lift_snd _ _ _))) hcovZ hp₀
    refine ⟨(pointsEquivScheme B S hS Zs).symm z, ?_⟩
    change pointsMap B S hS (yoneda.obj Zs) (yoneda.map ℓ ≫ m0) _ = x
    rw [pointsMap_comp_apply, ← hp]
    congr 1
    apply injective_pointsToScheme B S hS (pullback ĝ hs)
    rw [pointsToScheme_pointsMap_yoneda]
    exact (congrArg _ ((pointsEquivScheme B S hS Zs).apply_symm_apply z)).trans hz
  · -- the pullback of the module to `Z'` is universally pure, by Stacks 05K6
    let F₀ := chartModule B S hS P.hX P.F U
    let M : ((BigFppfOver.toScheme B S hS).obj Zs).Modules :=
      (Scheme.Modules.pullback cZ).obj F₀
    have : M.IsQuasicoherent := pullback_isQuasicoherent' cZ F₀
    have : M.IsFiniteType := SheafOfModules.pullback_isFiniteType cZ.toLRSHom.toShHom F₀
    have hmap : representedSpaceMap B S hS cs ≫
        (ObjectProperty.homMk U.obj.hom :
          schemeSpace U.obj.left ⟶ (⟨P.X, P.hX⟩ : AlgebraicSpaces B S hS)) = gsp ≫ c.proj :=
      ObjectProperty.hom_ext _ (show yoneda.map cs ≫ U.obj.hom =
        gmap ≫ pullback.snd c.g P.f from hgsnd.symm)
    refine isUniversallyPureAbove_of_isUniversallyPureAlong_represented e.situation κ
      (Iso.refl _) (Iso.refl _) ?_ M
      (chartModulePullbackIso (X := ⟨P.X, P.hX⟩) P.F P.moduleQuasicoherent U cs gsp c.proj
        hmap) ?_
    · change 𝟙 _ ≫ gmap ≫ pullback.fst c.g P.f = yoneda.map κ ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id, hgfst]
    · let α₂ : (BigFppfOver.toScheme B S hS).obj Zs ⟶
          Spec (CommRingCat.of (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk x₀)) := αZ
      have : LocallyOfFiniteType α₂ := ‹LocallyOfFiniteType αZ›
      have : IsAffine ((BigFppfOver.toScheme B S hS).obj Zs) := hZaff
      exact isUniversallyPureRelative_of_free_globalSections α₂ M hfreeZ _

/-! ### Stacks 0CW5 -/

/-- **Stacks 0CW5**, the substantive implication. In the situation of Stacks 0CV6 — a decent,
finite type morphism `f : X ⟶ Y` of algebraic spaces over `S` and a finite type quasi-coherent
`𝒪_X`-module `ℱ` — if `ℱ` is flat over `Y` and pure relative to `Y`, then `ℱ` is universally pure
relative to `Y`.

Both notions of Stacks 0CVD quantify over the points of `Y`, so this is Stacks 0CW4,
`AlgebraicGeometry.Space.isUniversallyPureAbove_of_flat_of_isPureAbove`, at each point: flatness
over `Y` is flatness at every point of `X`, hence in particular along every fibre. -/
theorem isUniversallyPureRelative_of_flat_of_isPureRelative (P : PrePureSituation.{u, u} B S hS)
    (hflat : ∀ x : points B S hS P.X, x ∈ flatLocus B S hS P.hX P.f P.F)
    (hpure : IsPureRelative P) :
    IsUniversallyPureRelative P :=
  fun y => isUniversallyPureAbove_of_flat_of_isPureAbove _ (fun x _ => hflat x) (hpure y)

/-- **Stacks 0CW5.** In the situation of Stacks 0CV6 — a decent, finite type morphism
`f : X ⟶ Y` of algebraic spaces over `S` and a finite type quasi-coherent `𝒪_X`-module `ℱ` — if
`ℱ` is flat over `Y`, then `ℱ` is pure relative to `Y` if and only if it is universally pure
relative to `Y`.

The forward implication is Stacks 0CW4 at each point of `Y`,
`AlgebraicGeometry.Space.isUniversallyPureRelative_of_flat_of_isPureRelative`; the reverse one is
formal and holds with no flatness, by
`AlgebraicGeometry.Space.IsPureRelative.of_isUniversallyPureRelative`. -/
@[stacks 0CW5]
theorem isPureRelative_iff_isUniversallyPureRelative_of_flat (P : PrePureSituation.{u, u} B S hS)
    (hflat : ∀ x : points B S hS P.X, x ∈ flatLocus B S hS P.hX P.f P.F) :
    IsPureRelative P ↔ IsUniversallyPureRelative P :=
  ⟨isUniversallyPureRelative_of_flat_of_isPureRelative P hflat,
    IsPureRelative.of_isUniversallyPureRelative⟩

end AlgebraicGeometry.Space

end
