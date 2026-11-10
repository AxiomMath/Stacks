module

public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform
public import StacksFrontier.AlgebraicGeometry.StrictTransform.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionBaseChangeConstruction
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsIso
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.SpecFiniteCover
public import StacksFrontier.AlgebraicGeometry.RegularSequence.ExtVanishingAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedQuotientNoSupportedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.CokernelAffineSurjectivityFromCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformFittingRank
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections

/-!
# The strict transform of a module on an algebraic space, read on a scheme chart

Let `f : Y ⟶ 𝔅` and `b : 𝔅' ⟶ 𝔅` be morphisms of algebraic spaces, let `E ⊆ 𝔅'` be a subspace
and let `M` be a quasi-coherent `𝒪_Y`-module.  The strict transform of `M` along `(b, E)`
(Stacks 0862) is the quotient of the pullback of `M` to `Y ×_𝔅 𝔅'` by its sections supported on
the points of the inverse image of `E`.  This file compares it with the strict transform of
modules on schemes (Stacks 080D) on a scheme chart.

Let `V ⟶ Y`, `W ⟶ 𝔅` and `W' ⟶ 𝔅'` be scheme charts, the first étale, with `W' = W ×_𝔅 𝔅'`,
and let `p : V ⟶ W`, `b₀ : W' ⟶ W` be morphisms of schemes compatible with `f` and `b`.  Then
`V ×_W W'` is an étale chart of `Y ×_𝔅 𝔅'`.  If the points of the inverse image of `E` form a
closed set, and the sections of the pullback of `M` supported there form a module cartesian on
affine charts (both hold for the exceptional divisor of a blowup, by Stacks 0859), then the
restriction of the strict transform of `M` to `V ×_W W'` is the scheme strict transform, along
`p` and `b₀`, of the restriction of `M` to `V`, relative to any ideal sheaf on `W'` whose
support cuts out the points of `E` on `V ×_W W'`.

## Main definitions

* `AlgebraicGeometry.Space.strictTransformBaseChangeChart`: the étale chart `V ×_W W'` of
  `Y ×_𝔅 𝔅'`, built on the fibre product of the underlying schemes.

## Main results

* `AlgebraicGeometry.Space.nonempty_strictTransformSheaf_iso_restrictToChart`: the restriction
  of the strict transform to `V ×_W W'` is the scheme strict transform of the restriction.
* `AlgebraicGeometry.Space.epi_pushforward_chartRestrictionSheafHom_map`,
  `AlgebraicGeometry.Space.mono_restrictFunctor_pushforward_chartRestrictionSheafHom_map` and
  `AlgebraicGeometry.Space.mono_restrictAdjunction_unit_app_pushforward_chartRestrictionSheafHom`:
  the three properties of a morphism to the restriction of a module that the universal property
  of the scheme strict transform asks for, read on the sections over the charts cut out by the
  Zariski opens of the chart.
* `AlgebraicGeometry.Space.exists_comp_chartOpens_map_eq`: a morphism of étale charts into the
  chart cut out by an open factors through the chart cut out by a smaller open containing its
  image.

## Implementation notes

The comparison is the universal property of the scheme strict transform,
`AlgebraicGeometry.Scheme.Modules.exists_cokernelSupportedSectionsIso_of_compl_eq`: an
epimorphism out of the pullback, which is a monomorphism away from the inverse image of the
centre and whose target has no sections supported there, is the quotient onto the strict
transform.  The restriction of a module to a chart is read as a direct image along the inclusion
of the Zariski opens of the chart into the small étale site,
`AlgebraicGeometry.Space.restrictToChartIsoPushforward`, so its sections over an open are the
sections of the module over the chart that open cuts out.  The three properties are then read on
those sections: surjectivity over affine charts is
`AlgebraicGeometry.Space.surjective_val_app_cokernel_π_of_cartesian`, the kernel of the quotient
map is the supported submodule, `AlgebraicGeometry.Space.exact_app_cokernel_π`, and the absence
of supported sections in the quotient is
`AlgebraicGeometry.Space.hasNoSectionsSupportedIn_cokernel_supportedSectionsSubmodule`.  The
pullback of the restriction of `M` to `V` is the restriction of its pullback,
`AlgebraicGeometry.Space.chartRestrictionBaseChangeIso`.

The scheme of the chart `V ×_W W'` is, by construction, the fibre product of schemes on which the
scheme strict transform lives, so the two strict transforms are modules on the same scheme.

## References

* [Stacks Project, Tag 0862](https://stacks.math.columbia.edu/tag/0862)
* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
* [Stacks Project, Tag 0859](https://stacks.math.columbia.edu/tag/0859)
* [Stacks Project, Tag 0863](https://stacks.math.columbia.edu/tag/0863)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Pullbacks of the underlying presheaves of algebraic spaces (instance search times out
without this shortcut). -/
local instance (priority := high) hasPullback_hom_strictTransformChart
    {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Z) (g : Y ⟶ Z) : HasPullback f.hom g.hom :=
  HasLimitsOfShape.has_limit _

section Chart

variable {Y 𝔅 𝔅' : AlgebraicSpaces B S hS} (f : Y ⟶ 𝔅) (b : 𝔅' ⟶ 𝔅)
  (cV : SmallEtale B S hS Y.1) {W W' : BigFppfOver B S hS}
  (cW : yoneda.obj W ⟶ 𝔅.1) (cW' : yoneda.obj W' ⟶ 𝔅'.1)
  (p : cV.obj.left ⟶ W) (b₀ : W' ⟶ W)
  (hT : B.Contains (pullback ((BigFppfOver.toScheme B S hS).map p)
    ((BigFppfOver.toScheme B S hS).map b₀)))

/-- The fibre product `V ×_W W'` of two objects of the big fppf site over a third, built on the
fibre product of the underlying schemes. -/
abbrev chartPullbackObj : BigFppfOver B S hS :=
  Over.mk (Y := B.obj hT) (⟨Limits.pullback.fst ((BigFppfOver.toScheme B S hS).map p)
    ((BigFppfOver.toScheme B S hS).map b₀)⟩ ≫ cV.obj.left.hom)

/-- The first projection `V ×_W W' ⟶ V`. -/
abbrev chartPullbackFst : chartPullbackObj cV p b₀ hT ⟶ cV.obj.left :=
  Over.homMk ⟨Limits.pullback.fst _ _⟩ rfl

/-- The second projection `V ×_W W' ⟶ W'`. -/
abbrev chartPullbackSnd : chartPullbackObj cV p b₀ hT ⟶ W' :=
  Over.homMk ⟨Limits.pullback.snd _ _⟩ (by
    apply B.inclusion.map_injective
    have hp := Over.w p
    have hb := Over.w b₀
    change Limits.pullback.snd _ _ ≫ B.inclusion.map W'.hom =
      Limits.pullback.fst _ _ ≫ B.inclusion.map cV.obj.left.hom
    rw [← hb, ← hp, Functor.map_comp, Functor.map_comp, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ B.inclusion.map W.hom) Limits.pullback.condition.symm)

/-- The square formed by the two projections of `V ×_W W'` and the morphisms `p : V ⟶ W` and
`b₀ : W' ⟶ W` is a pullback square. -/
theorem isPullback_chartPullback :
    IsPullback (chartPullbackFst cV p b₀ hT) (chartPullbackSnd cV p b₀ hT) p b₀ :=
  FiniteFreeAlgebra.isPullback_of_isPullback_toScheme (IsPullback.of_hasPullback _ _)

variable {f b cV cW cW' p b₀} in
/-- The morphism `V ×_W W' ⟶ Y ×_𝔅 𝔅'` induced by the charts. -/
abbrev chartPullbackMap (hp : cV.obj.hom ≫ f.hom = yoneda.map p ≫ cW)
    (hb : yoneda.map b₀ ≫ cW = cW' ≫ b.hom) :
    yoneda.obj (chartPullbackObj cV p b₀ hT) ⟶ (strictTransformPullback B S hS f b).1 :=
  Limits.pullback.lift (yoneda.map (chartPullbackFst cV p b₀ hT) ≫ cV.obj.hom)
    (yoneda.map (chartPullbackSnd cV p b₀ hT) ≫ cW') (by
      rw [Category.assoc, hp, Category.assoc, ← hb, ← Category.assoc, ← Category.assoc,
        ← Functor.map_comp, ← Functor.map_comp, (isPullback_chartPullback cV p b₀ hT).w])

variable {f b cV cW cW' p b₀} in
/-- If `W' ⟶ 𝔅'` is the base change of the chart `W ⟶ 𝔅` along `b`, then the morphism
`V ×_W W' ⟶ Y ×_𝔅 𝔅'` and the projection to `V` form a pullback square over the chart
`V ⟶ Y`. -/
theorem isPullback_chartPullbackMap (hp : cV.obj.hom ≫ f.hom = yoneda.map p ≫ cW)
    (hb : yoneda.map b₀ ≫ cW = cW' ≫ b.hom) (hsq : IsPullback (yoneda.map b₀) cW' cW b.hom) :
    IsPullback (chartPullbackMap hT hp hb) (yoneda.map (chartPullbackFst cV p b₀ hT))
      (Limits.pullback.fst f.hom b.hom) cV.obj.hom := by
  have A : IsPullback (yoneda.map (chartPullbackSnd cV p b₀ hT))
      (yoneda.map (chartPullbackFst cV p b₀ hT)) (yoneda.map b₀) (yoneda.map p) :=
    ((isPullback_chartPullback cV p b₀ hT).map yoneda).flip
  refine IsPullback.of_right ?_ (Limits.pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback f.hom b.hom).flip
  have e1 : chartPullbackMap hT hp hb ≫ Limits.pullback.snd f.hom b.hom =
      yoneda.map (chartPullbackSnd cV p b₀ hT) ≫ cW' := Limits.pullback.lift_snd _ _ _
  rw [e1, hp]
  exact A.paste_horiz hsq.flip

variable {f b cV cW cW' p b₀} in
/-- The étale chart `V ×_W W' ⟶ Y ×_𝔅 𝔅'`: it is the base change of the chart `V ⟶ Y`. -/
abbrev strictTransformBaseChangeChart (hp : cV.obj.hom ≫ f.hom = yoneda.map p ≫ cW)
    (hb : yoneda.map b₀ ≫ cW = cW' ≫ b.hom) (hsq : IsPullback (yoneda.map b₀) cW' cW b.hom) :
    SmallEtale B S hS (strictTransformPullback B S hS f b).1 :=
  ⟨CostructuredArrow.mk (chartPullbackMap hT hp hb),
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (isPullback_chartPullbackMap hT hp hb hsq).flip cV.property⟩

end Chart

/-! ### Criteria on the sections of a chart restriction -/

section Criteria

/-- A morphism of modules on a scheme which is surjective on the sections over every affine open
is an epimorphism: the affine opens form a basis, so the morphism is locally surjective. -/
theorem epi_of_surjective_app_isAffineOpen {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ U : X.Opens, IsAffineOpen U → Function.Surjective (φ.app U)) : Epi φ := by
  apply (SheafOfModules.toSheaf.{u} X.ringCatSheaf).epi_of_epi_map
  apply (TopCat.Sheaf.isLocallySurjective_iff_epi (X := X.carrier)
    ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map φ)).mp
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro U s x hx
  obtain ⟨V, hV, hxV, hVU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
  exact ⟨V, hVU, h V hV _, hxV⟩

variable {X : AlgebraicSpaces B S hS} (U : SmallEtale B S hS X.1)
  [(chartOpens B S hS U).IsContinuous (Opens.grothendieckTopology (chartScheme U))
    (SmallEtale.topology B S hS X.1)]

/-- The direct image of a morphism of `𝒪_X`-modules to the Zariski site of an étale chart is an
epimorphism as soon as the morphism is surjective on the sections over the charts cut out by
the affine opens of the chart. -/
theorem epi_pushforward_chartRestrictionSheafHom_map {N N' : Modules.{u, u} B S hS X.1 X.2}
    (φ : N ⟶ N')
    (h : ∀ O : (chartScheme U).Opens, IsAffineOpen O →
      Function.Surjective (φ.val.app (op ((chartOpens B S hS U).obj O)))) :
    Epi ((SheafOfModules.pushforward.{u} (chartRestrictionSheafHom B S hS X.2 U)).map φ) :=
  epi_of_surjective_app_isAffineOpen _ fun O hO => h O hO

/-- The restriction to an open `O` of the chart of the direct image of a morphism is a
monomorphism as soon as the morphism is injective on the sections over the charts cut out by
the opens inside `O`. -/
theorem mono_restrictFunctor_pushforward_chartRestrictionSheafHom_map
    {N N' : Modules.{u, u} B S hS X.1 X.2} (φ : N ⟶ N') (O : (chartScheme U).Opens)
    (h : ∀ O' : (chartScheme U).Opens, O' ≤ O →
      Function.Injective (φ.val.app (op ((chartOpens B S hS U).obj O')))) :
    Mono ((Scheme.Modules.restrictFunctor O.ι).map
      ((SheafOfModules.pushforward.{u} (chartRestrictionSheafHom B S hS X.2 U)).map φ)) :=
  Stacks.RegularSequence.mono_of_injective_app _ fun O' =>
    h _ (O.ι.image_le_opensRange O' |>.trans_eq (Scheme.Opens.opensRange_ι O))

/-- The unit of the restriction to an open `O` of the chart is a monomorphism on the direct image
of a module as soon as a section over a chart cut out by an open which vanishes on the part of
that open inside `O` vanishes. -/
theorem mono_restrictAdjunction_unit_app_pushforward_chartRestrictionSheafHom
    (N : Modules.{u, u} B S hS X.1 X.2) (O : (chartScheme U).Opens)
    (h : ∀ (O' : (chartScheme U).Opens) (s : N.val.obj (op ((chartOpens B S hS U).obj O'))),
      N.val.map ((chartOpens B S hS U).map (homOfLE (O.ι.image_preimage_le O'))).op s = 0 →
        s = 0) :
    Mono ((Scheme.Modules.restrictAdjunction O.ι).unit.app
      ((SheafOfModules.pushforward.{u} (chartRestrictionSheafHom B S hS X.2 U)).obj N)) :=
  Stacks.RegularSequence.mono_of_injective_app _ fun O' =>
    (injective_iff_map_eq_zero _).mpr (h O')

end Criteria

/-! ### Points of the charts cut out by Zariski opens -/

section Points

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A point of an étale chart which maps to another chart lies, in the algebraic space, over the
image of its scheme point in the scheme of the other chart. -/
theorem pointsMap_hom_eq_pointOfEtaleChart_chartSchemeMap {C T : SmallEtale B S hS F}
    (g : C ⟶ T) (y : points B S hS (yoneda.obj C.obj.left)) :
    pointsMap B S hS (yoneda.obj C.obj.left) C.obj.hom y =
      pointOfEtaleChart B S hS T (chartSchemeMap g (pointsEquivScheme B S hS C.obj.left y)) := by
  rw [← pointsMap_chart_hom B S hS F g y]
  unfold pointOfEtaleChart
  congr 1
  apply (pointsEquivScheme B S hS T.obj.left).injective
  rw [Equiv.apply_symm_apply]
  exact pointsToScheme_pointsMap_yoneda B S hS _ y

/-- The point of an étale chart represented by a scheme point is the point represented by its
image in a chart it maps to. -/
theorem pointOfEtaleChart_eq_pointOfEtaleChart_chartSchemeMap {C T : SmallEtale B S hS F}
    (g : C ⟶ T) (c : chartScheme C) :
    pointOfEtaleChart B S hS C c = pointOfEtaleChart B S hS T (chartSchemeMap g c) := by
  have h := pointsMap_hom_eq_pointOfEtaleChart_chartSchemeMap g
    ((pointsEquivScheme B S hS C.obj.left).symm c)
  rwa [Equiv.apply_symm_apply] at h

/-- A morphism of étale charts into the chart cut out by a Zariski open `O'` of a chart `T`,
whose underlying morphism of schemes lands in a smaller open `O''`, factors through the chart cut
out by `O''`. -/
theorem exists_comp_chartOpens_map_eq {T : SmallEtale B S hS F}
    {O'' O' : (chartScheme T).Opens} (hle : O'' ≤ O') {U'' : SmallEtale B S hS F}
    (i : U'' ⟶ (chartOpens B S hS T).obj O') (hi : ∀ v, O'.ι (chartSchemeMap i v) ∈ O'') :
    ∃ i' : U'' ⟶ (chartOpens B S hS T).obj O'',
      i' ≫ (chartOpens B S hS T).map (homOfLE hle) = i := by
  let iS : chartScheme U'' ⟶ (O' : Scheme.{u}) := chartSchemeMap i
  let h₀ : chartScheme U'' ⟶ O''.toScheme :=
    IsOpenImmersion.lift O''.ι (iS ≫ O'.ι) (by
      rintro _ ⟨v, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hi v)
  have hh₀ : h₀ ≫ O''.ι = iS ≫ O'.ι := IsOpenImmersion.lift_fac _ _ _
  have hw : iS ≫ O'.ι ≫ B.inclusion.map T.obj.left.hom = B.inclusion.map U''.obj.left.hom :=
    congrArg B.inclusion.map (Over.w i.hom.left)
  let hsite : U''.obj.left ⟶ chartOpenOver B S hS T O'' :=
    Over.homMk (ObjectProperty.homMk h₀) (by
      apply B.inclusion.map_injective
      change h₀ ≫ O''.ι ≫ B.inclusion.map T.obj.left.hom = B.inclusion.map U''.obj.left.hom
      rw [← hw, ← Category.assoc, hh₀, Category.assoc])
  have hι : hsite ≫ chartOpenOverι B S hS T O'' = i.hom.left ≫ chartOpenOverι B S hS T O' := by
    apply (BigFppfOver.toScheme B S hS).map_injective
    exact hh₀
  refine ⟨ObjectProperty.homMk (CostructuredArrow.homMk hsite ?_), ?_⟩
  · have hc : yoneda.map i.hom.left ≫ yoneda.map (chartOpenOverι B S hS T O') ≫ T.obj.hom =
        U''.obj.hom := CostructuredArrow.w i.hom
    change yoneda.map hsite ≫ yoneda.map (chartOpenOverι B S hS T O'') ≫ T.obj.hom = U''.obj.hom
    rw [← hc]
    have h1 := congrArg (fun k => yoneda.map k ≫ T.obj.hom) hι
    simp only [Functor.map_comp, Category.assoc] at h1
    exact h1.trans ((congrArg (· ≫ T.obj.hom) (yoneda.map_comp _ _)).trans
      (Category.assoc _ _ _))
  · apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    apply (BigFppfOver.toScheme B S hS).map_injective
    change h₀ ≫ (chartScheme T).homOfLE hle = iS
    rw [← cancel_mono O'.ι, Category.assoc, Scheme.homOfLE_ι, hh₀]

end Points

/-! ### The quotient by the supported sections on the charts of an open -/

section SupportedQuotient

attribute [local instance] pointTopology

variable {X : AlgebraicSpaces B S hS} (T : SmallEtale B S hS X.1)
  (TE : Set (points B S hS X.1)) (G : Modules.{u, u} B S hS X.1 X.2)
  (Oc : (chartScheme T).Opens)

/-- Over the charts cut out by the opens of a chart lying over the complement of `TE`, the
quotient of `G` by its sections supported on `TE` is injective on sections: a section killed by
the quotient map is supported on `TE`, and the chart has no point over `TE`. -/
theorem injective_cokernel_π_app_of_le
    (hOc : ∀ t, t ∈ Oc ↔ pointOfEtaleChart B S hS T t ∉ TE)
    (O' : (chartScheme T).Opens) (hO' : O' ≤ Oc) :
    Function.Injective ((cokernel.π (supportedSectionsSubmodule B S hS X.1 X.2 TE G).ι).val.app
      (op ((chartOpens B S hS T).obj O'))) := by
  refine (injective_iff_map_eq_zero _).mpr fun t ht => ?_
  obtain ⟨k, rfl⟩ := (exact_app_cokernel_π B S hS _ ((chartOpens B S hS T).obj O') t).mp ht
  have hk := (mem_supportedSectionsSubmodule_iff B S hS X.1 X.2 TE G _ k.1).mp k.2
  refine eq_zero_of_supportOfSection_eq_empty (F := moduleAddSheaf B S hS X.1 X.2 G) _ k.1
    (Set.eq_empty_iff_forall_notMem.mpr fun y hy => ?_)
  have h1 : pointsMap B S hS _ ((chartOpens B S hS T).obj O').obj.hom y ∈ TE := hk hy
  rw [pointsMap_hom_eq_pointOfEtaleChart_chartSchemeMap (chartOpensHom B S hS X T O') y] at h1
  exact (hOc _).mp (hO' (Subtype.prop _)) h1

/-- A section over the chart cut out by an open `O'` of the quotient of `G` by its sections
supported on a closed `TE` vanishes as soon as it vanishes on the part of `O'` over the
complement of `TE`: it is then supported on `TE`, and the quotient has no such section. -/
theorem eq_zero_of_cokernel_π_restrict_eq_zero
    (hOc : ∀ t, t ∈ Oc ↔ pointOfEtaleChart B S hS T t ∉ TE) (hTE : IsClosed TE)
    (O' : (chartScheme T).Opens)
    (s : (cokernel (supportedSectionsSubmodule B S hS X.1 X.2 TE G).ι).val.obj
      (op ((chartOpens B S hS T).obj O')))
    (hs : (cokernel (supportedSectionsSubmodule B S hS X.1 X.2 TE G).ι).val.map
      ((chartOpens B S hS T).map (homOfLE (Oc.ι.image_preimage_le O'))).op s = 0) :
    s = 0 := by
  refine hasNoSectionsSupportedIn_cokernel_supportedSectionsSubmodule B S hS X TE hTE G _ s ?_
  refine sectionSupportedIn_of_restrict_eq_zero_of_imageInOpen B S hS X TE hTE _ _ s
    fun U'' i hi => ?_
  obtain ⟨i', hi'⟩ := exists_comp_chartOpens_map_eq (Oc.ι.image_preimage_le O') i (fun v => by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    refine ⟨(hOc _).mpr ?_, Subtype.prop _⟩
    have h1 := hi ((pointsEquivScheme B S hS U''.obj.left).symm v)
    simp only [Set.mem_preimage, Set.mem_compl_iff] at h1
    change pointsMap B S hS _ ((chartOpens B S hS T).obj O').obj.hom
      (pointsMap B S hS _ (yoneda.map i.hom.left) _) ∉ TE at h1
    rw [pointsMap_chart_hom B S hS X.1 i,
      pointsMap_hom_eq_pointOfEtaleChart_chartSchemeMap (i ≫ chartOpensHom B S hS X T O'),
      Equiv.apply_symm_apply] at h1
    exact h1)
  have hcomp := (cokernel (supportedSectionsSubmodule B S hS X.1 X.2 TE G).ι).val.map_comp_apply
    ((chartOpens B S hS T).map (homOfLE (Oc.ι.image_preimage_le O'))).op i'.op s
  rw [← hi']
  exact hcomp.trans ((congrArg _ hs).trans (map_zero _))

end SupportedQuotient

/-- A composite `β.hom ≫ ρ.hom ≫ π` of two isomorphisms and an epimorphism is an epimorphism. -/
theorem _root_.CategoryTheory.epi_iso_hom_comp_iso_hom_comp {C : Type*} [Category C]
    {X₁ X₂ X₃ X₄ : C} (β : X₁ ≅ X₂) (ρ : X₂ ≅ X₃) {π : X₃ ⟶ X₄} (hπ : Epi π) :
    Epi (β.hom ≫ ρ.hom ≫ π) :=
  inferInstance

/-- A functor sends `β.hom ≫ ρ.hom ≫ π`, for isomorphisms `β`, `ρ`, to a monomorphism as soon as
it sends `π` to one. -/
theorem _root_.CategoryTheory.mono_map_iso_hom_comp_iso_hom_comp {C D : Type*} [Category C]
    [Category D] (F : C ⥤ D) {X₁ X₂ X₃ X₄ : C} (β : X₁ ≅ X₂) (ρ : X₂ ≅ X₃) {π : X₃ ⟶ X₄}
    (hπ : Mono (F.map π)) : Mono (F.map (β.hom ≫ ρ.hom ≫ π)) := by
  rw [F.map_comp, F.map_comp]
  infer_instance

section Comparison

attribute [local instance] pointTopology

variable {Y 𝔅 𝔅' : AlgebraicSpaces B S hS} {f : Y ⟶ 𝔅} {b : 𝔅' ⟶ 𝔅}
  {cV : SmallEtale B S hS Y.1} {W W' : BigFppfOver B S hS}
  {cW : yoneda.obj W ⟶ 𝔅.1} {cW' : yoneda.obj W' ⟶ 𝔅'.1}
  {p : cV.obj.left ⟶ W} {b₀ : W' ⟶ W}
  (hT : B.Contains (pullback ((BigFppfOver.toScheme B S hS).map p)
    ((BigFppfOver.toScheme B S hS).map b₀)))
  (hp : cV.obj.hom ≫ f.hom = yoneda.map p ≫ cW)
  (hb : yoneda.map b₀ ≫ cW = cW' ≫ b.hom) (hsq : IsPullback (yoneda.map b₀) cW' cW b.hom)
  (E : Subfunctor 𝔅'.1) (M : Modules.{u, u} B S hS Y.1 Y.2)
  (E₀ : ((BigFppfOver.toScheme B S hS).obj W').IdealSheafData)

/-- **The chart restriction of the strict transform of a module is the strict transform of the
chart restriction.**  Let `f : Y ⟶ 𝔅` and `b : 𝔅' ⟶ 𝔅` be morphisms of algebraic spaces, let
`E ⊆ 𝔅'` be a subspace, let `V ⟶ Y`, `W ⟶ 𝔅`, `W' ⟶ 𝔅'` be charts with `W' = W ×_𝔅 𝔅'`,
compatible with `f` and `b` through morphisms `p : V ⟶ W` and `b₀ : W' ⟶ W`, and let `M` be a
quasi-coherent `𝒪_Y`-module.  Then `V ×_W W'` is an étale chart of `Y ×_𝔅 𝔅'`, and the restriction
to it of the strict transform of `M` is the strict transform, along the morphisms of schemes
`p` and `b₀`, of the restriction of `M` to `V`, relative to any ideal sheaf `E₀` on `W'` whose
support cuts out the points of `E` on `V ×_W W'`.

Two hypotheses carry the geometry: the points of the inverse image of `E` form a closed set,
and the sections of the pullback of `M` supported there form a module cartesian on affine
charts; both hold for the exceptional divisor of a blowup (Stacks 0859). -/
theorem nonempty_strictTransformSheaf_iso_restrictToChart (hM : M.IsQuasicoherentOnSite)
    (hE₀ : ∀ t : chartScheme (strictTransformBaseChangeChart hT hp hb hsq),
      t ∈ Stacks.StrictTransform.exceptionalPreimage ((BigFppfOver.toScheme B S hS).map p)
        ((BigFppfOver.toScheme B S hS).map b₀) E₀ ↔
      pointOfEtaleChart B S hS (strictTransformBaseChangeChart hT hp hb hsq) t ∈
        exceptionalPreimageSet B S hS f b E)
    (hclosed : IsClosed (exceptionalPreimageSet B S hS f b E))
    (hK : IsCartesianOnAffineCharts (supportedSectionsSubmodule B S hS
      (strictTransformPullback B S hS f b).1 (strictTransformPullback B S hS f b).2
      (exceptionalPreimageSet B S hS f b E)
      ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj
        M)).toSheafOfModules) :
    Nonempty (Stacks.StrictTransform.sheaf ((BigFppfOver.toScheme B S hS).map p)
        ((BigFppfOver.toScheme B S hS).map b₀) E₀ (restrictToChart B S hS Y.2 M cV) ≅
      restrictToChart B S hS (strictTransformPullback B S hS f b).2
        (strictTransformSheaf B S hS f b E M) (strictTransformBaseChangeChart hT hp hb hsq)) := by
  let := isContinuous_chartOpens B S hS _ (strictTransformPullback B S hS f b).2
    (strictTransformBaseChangeChart hT hp hb hsq)
  have hGcart := (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS _
    (strictTransformPullback B S hS f b).2 _).mp
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      (strictTransformPullbackToSource B S hS f b) M hM)
  let Oc : (chartScheme (strictTransformBaseChangeChart hT hp hb hsq)).Opens :=
    Stacks.StrictTransform.exceptionalComplement ((BigFppfOver.toScheme B S hS).map p)
      ((BigFppfOver.toScheme B S hS).map b₀) E₀
  have hOc : ∀ t, t ∈ Oc ↔
      pointOfEtaleChart B S hS (strictTransformBaseChangeChart hT hp hb hsq) t ∉
        exceptionalPreimageSet B S hS f b E := fun t => by
    rw [← hE₀ t, Stacks.StrictTransform.exceptionalPreimage_eq_compl, Set.mem_compl_iff,
      not_not]
    rfl
  let πs := (SheafOfModules.pushforward.{u} (chartRestrictionSheafHom B S hS
    (strictTransformPullback B S hS f b).2 (strictTransformBaseChangeChart hT hp hb hsq))).map
    (cokernel.π (supportedSectionsSubmodule B S hS
      (strictTransformPullback B S hS f b).1 (strictTransformPullback B S hS f b).2
      (exceptionalPreimageSet B S hS f b E)
      ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj M)).ι)
  have hepi : Epi πs :=
    epi_pushforward_chartRestrictionSheafHom_map _ _ fun O hO =>
      surjective_val_app_cokernel_π_of_cartesian _ hK hGcart _ hO
  have hmono : Mono ((Scheme.Modules.restrictFunctor Oc.ι).map πs) :=
    mono_restrictFunctor_pushforward_chartRestrictionSheafHom_map _ _ Oc
      (injective_cokernel_π_app_of_le _ _ _ Oc hOc)
  have hunit := mono_restrictAdjunction_unit_app_pushforward_chartRestrictionSheafHom
    (strictTransformBaseChangeChart hT hp hb hsq) (strictTransformSheaf B S hS f b E M) Oc
    (eq_zero_of_cokernel_π_restrict_eq_zero _ _ _ Oc hOc hclosed)
  let β := chartRestrictionBaseChangeIso B S hS (strictTransformPullbackToSource B S hS f b) M hM
    cV (strictTransformBaseChangeChart hT hp hb hsq) (chartPullbackFst cV p b₀ hT)
    (Limits.pullback.lift_fst _ _ _).symm
  let ρ := restrictToChartIsoPushforward B S hS _ (strictTransformBaseChangeChart hT hp hb hsq)
    ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj M)
  let q := @CategoryStruct.comp (Scheme.Modules (chartScheme
      (strictTransformBaseChangeChart hT hp hb hsq))) _ _ _ _ β.hom
    (@CategoryStruct.comp (Scheme.Modules (chartScheme
      (strictTransformBaseChangeChart hT hp hb hsq))) _ _ _ _ ρ.hom πs)
  have hq : Epi q := CategoryTheory.epi_iso_hom_comp_iso_hom_comp β ρ
    (⟨fun g k e => hepi.left_cancellation g k e⟩ : Epi (C := Scheme.Modules (chartScheme
      (strictTransformBaseChangeChart hT hp hb hsq))) πs)
  have hqm : Mono ((Scheme.Modules.restrictFunctor Oc.ι).map q) :=
    CategoryTheory.mono_map_iso_hom_comp_iso_hom_comp _ β ρ hmono
  obtain ⟨e, -⟩ := @Scheme.Modules.exists_cokernelSupportedSectionsIso_of_compl_eq _ Oc _
    (Stacks.StrictTransform.exceptionalPreimage_eq_compl ((BigFppfOver.toScheme B S hS).map p)
      ((BigFppfOver.toScheme B S hS).map b₀) E₀) _ _ q hq hunit hqm
  have hfst : (BigFppfOver.toScheme B S hS).map (chartPullbackFst cV p b₀ hT) =
      Limits.pullback.fst ((BigFppfOver.toScheme B S hS).map p) ((BigFppfOver.toScheme B S hS).map
          b₀) :=
    rfl
  rw [hfst] at e
  exact ⟨e ≪≫ (restrictToChartIsoPushforward B S hS _ _ _).symm⟩

end Comparison

end AlgebraicGeometry.Space

end
