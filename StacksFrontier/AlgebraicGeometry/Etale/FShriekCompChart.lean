module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekBaseChangeSupport
public import StacksFrontier.AlgebraicGeometry.Etale.OpenCovariance

/-!
# Charts for the composition of direct images with compact support

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of a big étale site, and let

```
X' --f'--> Y'
|jX        |jY
X  --f-->  Y
```

be a cartesian square whose vertical arrows are open immersions. For an object `W` of the
small étale site of `Z`, the base change `W ×_Z X'` of `X'` along `jX ≫ f ≫ g` and the base change
of `X` along the object `W ×_Z Y'` of the small étale site of `Y` are the same scheme. This file
records that identification as an isomorphism of the small étale site of `X`, natural in `W`, and
deduces from it the open immersion of the second scheme into the base change `W ×_Z X` of `X`
along `f ≫ g`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.compChartMap` — the morphism `W ×_Z X' ⟶ W ×_Z Y'`.
* `AlgebraicGeometry.SmallEtale.compChartBase` — the object `W ×_Z Y'` of the small étale site
  of `Y`.
* `AlgebraicGeometry.SmallEtale.compChartIso` — the identification of `W ×_Z X'`, read in the
  small étale site of `X`, with the base change of `X` along `compChartBase`.
* `AlgebraicGeometry.SmallEtale.compChartInclusion` — the resulting morphism from the base
  change of `X` along `compChartBase` to the base change of `X` along `W`.

## Main results

* `AlgebraicGeometry.SmallEtale.isPullback_compChartMap` — the chart square is cartesian.
* `AlgebraicGeometry.SmallEtale.compChartIso_naturality` and
  `AlgebraicGeometry.SmallEtale.compChartInclusion_naturality` — both are natural in `W`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

section Chart

variable (B : BigEtaleSite.{u}) {X Y Z X' Y' : B.Scheme}
  (f : X ⟶ Y) (g : Y ⟶ Z) (jX : X' ⟶ X) (jY : Y' ⟶ Y) (f' : X' ⟶ Y')
  [IsOpenImmersion (B.inclusion.map jX)] [IsOpenImmersion (B.inclusion.map jY)]

/-- The object `W ×_Z Y'` of the small étale site of `Y`, through the open immersion `jY`. -/
public abbrev compChartBase (W : SmallEtale B Z.obj Z.property) :
    SmallEtale B Y.obj Y.property :=
  (openPostcompose B jY).obj (baseChange B (jY ≫ g) W)

variable {f jX jY f'}

/-- The morphism `W ×_Z X' ⟶ W ×_Z Y'` induced by `f'`. -/
public def compChartMap (sq : f' ≫ jY = jX ≫ f) (W : SmallEtale B Z.obj Z.property) :
    (baseChange B (jX ≫ f ≫ g) W).obj.left ⟶ (baseChange B (jY ≫ g) W).obj.left :=
  (isPullback_fiberProjection B (jY ≫ g) W).lift (fiberProjection B (jX ≫ f ≫ g) W)
    ((baseChange B (jX ≫ f ≫ g) W).obj.hom ≫ f') (by
      rw [(isPullback_fiberProjection B (jX ≫ f ≫ g) W).w, Category.assoc,
        reassoc_of% sq])

omit [IsOpenImmersion (B.inclusion.map jX)] [IsOpenImmersion (B.inclusion.map jY)] in
/-- The chart map `W ×_Z X' ⟶ W ×_Z Y'` commutes with the projections to `W`. -/
@[reassoc (attr := simp)]
public theorem compChartMap_fst (sq : f' ≫ jY = jX ≫ f) (W : SmallEtale B Z.obj Z.property) :
    compChartMap B g sq W ≫ fiberProjection B (jY ≫ g) W =
      fiberProjection B (jX ≫ f ≫ g) W :=
  IsPullback.lift_fst _ _ _ _

omit [IsOpenImmersion (B.inclusion.map jX)] [IsOpenImmersion (B.inclusion.map jY)] in
/-- The chart map `W ×_Z X' ⟶ W ×_Z Y'` lies over `f' : X' ⟶ Y'`. -/
@[reassoc (attr := simp)]
public theorem compChartMap_snd (sq : f' ≫ jY = jX ≫ f) (W : SmallEtale B Z.obj Z.property) :
    compChartMap B g sq W ≫ (baseChange B (jY ≫ g) W).obj.hom =
      (baseChange B (jX ≫ f ≫ g) W).obj.hom ≫ f' :=
  IsPullback.lift_snd _ _ _ _

omit [IsOpenImmersion (B.inclusion.map jX)] [IsOpenImmersion (B.inclusion.map jY)] in
/-- The chart square `W ×_Z X' ⟶ W ×_Z Y'` over `X' ⟶ Y'` is cartesian. -/
public theorem isPullback_compChartMap (sq : f' ≫ jY = jX ≫ f)
    (W : SmallEtale B Z.obj Z.property) :
    IsPullback (compChartMap B g sq W) (baseChange B (jX ≫ f ≫ g) W).obj.hom
      (baseChange B (jY ≫ g) W).obj.hom f' := by
  refine IsPullback.of_right (h₁₂ := fiberProjection B (jY ≫ g) W) ?_
    (compChartMap_snd B g sq W) (isPullback_fiberProjection B (jY ≫ g) W)
  rw [compChartMap_fst, show f' ≫ jY ≫ g = jX ≫ f ≫ g by rw [reassoc_of% sq]]
  exact isPullback_fiberProjection B (jX ≫ f ≫ g) W

omit [IsOpenImmersion (B.inclusion.map jX)] [IsOpenImmersion (B.inclusion.map jY)] in
/-- The composite chart square, over `f : X ⟶ Y`, is cartesian. -/
public theorem isPullback_compChartMap_comp (sq : f' ≫ jY = jX ≫ f)
    (hsq : IsPullback f' jX jY f) (W : SmallEtale B Z.obj Z.property) :
    IsPullback (compChartMap B g sq W) ((baseChange B (jX ≫ f ≫ g) W).obj.hom ≫ jX)
      ((baseChange B (jY ≫ g) W).obj.hom ≫ jY) f :=
  (isPullback_compChartMap B g sq W).paste_vert hsq

/-- **The chart isomorphism**, as a morphism of the small étale site of `X`: the base change
`W ×_Z X'`, read in the small étale site of `X` through `jX`, maps to the base change of `X`
along `W ×_Z Y'`. -/
public def compChartHom (sq : f' ≫ jY = jX ≫ f) (W : SmallEtale B Z.obj Z.property) :
    (openPostcompose B jX).obj (baseChange B (jX ≫ f ≫ g) W) ⟶
      baseChange B f (compChartBase B g jY W) :=
  baseChangeObjLift B f _ _ (compChartMap B g sq W) (by
    change compChartMap B g sq W ≫ (baseChange B (jY ≫ g) W).obj.hom ≫ jY =
      (baseChange B (jX ≫ f ≫ g) W).obj.hom ≫ jX ≫ f
    rw [compChartMap_snd_assoc, sq])

/-- The underlying morphism of `compChartHom`, followed by the projection to `W ×_Z Y'`, is the
chart map `compChartMap`. -/
@[reassoc (attr := simp)]
public theorem compChartHom_proj (sq : f' ≫ jY = jX ≫ f) (W : SmallEtale B Z.obj Z.property) :
    (compChartHom B g sq W).hom.left ≫ baseChangeObjProjection B f (compChartBase B g jY W) =
      compChartMap B g sq W :=
  baseChangeObjLift_proj _ _ _ _ _ _

/-- When the square `f' ≫ jY = jX ≫ f` is cartesian, `compChartHom` is an isomorphism. -/
public theorem isIso_compChartHom (sq : f' ≫ jY = jX ≫ f) (hsq : IsPullback f' jX jY f)
    (W : SmallEtale B Z.obj Z.property) : IsIso (compChartHom B g sq W) := by
  have h1 := isPullback_compChartMap_comp B g sq hsq W
  have h2 := isPullback_baseChangeObjProjection B f (compChartBase B g jY W)
  have hl : IsIso (compChartHom B g sq W).hom.left := by
    have he : (compChartHom B g sq W).hom.left = (h1.isoIsPullback _ _ h2).hom := by
      refine h2.hom_ext ?_ ?_
      · rw [compChartHom_proj]
        exact (IsPullback.isoIsPullback_hom_fst _ _ h1 h2).symm
      · exact (Over.w (compChartHom B g sq W).hom).trans
          (IsPullback.isoIsPullback_hom_snd _ _ h1 h2).symm
    rw [he]
    exact Iso.isIso_hom _
  have : IsIso ((SmallEtale.inclusion B X.obj X.property ⋙ Over.forget _).map
      (compChartHom B g sq W)) := hl
  exact isIso_of_reflects_iso _ (SmallEtale.inclusion B X.obj X.property ⋙ Over.forget _)

/-- The chart isomorphism. -/
public def compChartIso (sq : f' ≫ jY = jX ≫ f) (hsq : IsPullback f' jX jY f)
    (W : SmallEtale B Z.obj Z.property) :
    (openPostcompose B jX).obj (baseChange B (jX ≫ f ≫ g) W) ≅
      baseChange B f (compChartBase B g jY W) :=
  haveI := isIso_compChartHom B g sq hsq W
  asIso (compChartHom B g sq W)

omit [IsOpenImmersion (B.inclusion.map jX)] [IsOpenImmersion (B.inclusion.map jY)] in
/-- The chart morphism is natural in the test object. -/
@[reassoc]
public theorem compChartMap_naturality (sq : f' ≫ jY = jX ≫ f)
    {W W' : SmallEtale B Z.obj Z.property} (φ : W' ⟶ W) :
    ((smallEtaleBaseChange B (jX ≫ f ≫ g)).map φ).hom.left ≫ compChartMap B g sq W =
      compChartMap B g sq W' ≫ ((smallEtaleBaseChange B (jY ≫ g)).map φ).hom.left := by
  refine (isPullback_fiberProjection B (jY ≫ g) W).hom_ext ?_ ?_
  · calc (((smallEtaleBaseChange B (jX ≫ f ≫ g)).map φ).hom.left ≫ compChartMap B g sq W) ≫
          fiberProjection B (jY ≫ g) W
        = ((smallEtaleBaseChange B (jX ≫ f ≫ g)).map φ).hom.left ≫
            fiberProjection B (jX ≫ f ≫ g) W := by rw [Category.assoc, compChartMap_fst]
      _ = fiberProjection B (jX ≫ f ≫ g) W' ≫ φ.hom.left :=
          baseChangeObjProjection_naturality B (jX ≫ f ≫ g) φ
      _ = compChartMap B g sq W' ≫ fiberProjection B (jY ≫ g) W' ≫ φ.hom.left := by
          rw [compChartMap_fst_assoc]
      _ = (compChartMap B g sq W' ≫ ((smallEtaleBaseChange B (jY ≫ g)).map φ).hom.left) ≫
          fiberProjection B (jY ≫ g) W := by
          rw [Category.assoc]
          exact congrArg (fun m => compChartMap B g sq W' ≫ m)
            (baseChangeObjProjection_naturality B (jY ≫ g) φ).symm
  · simp only [Category.assoc, compChartMap_snd, Over.w_assoc, Over.w]

/-- The chart morphism of the small étale site of `X` is natural in the test object. -/
@[reassoc]
public theorem compChartHom_naturality (sq : f' ≫ jY = jX ≫ f)
    {W W' : SmallEtale B Z.obj Z.property} (φ : W' ⟶ W) :
    (openPostcompose B jX).map ((smallEtaleBaseChange B (jX ≫ f ≫ g)).map φ) ≫
        compChartHom B g sq W =
      compChartHom B g sq W' ≫ (smallEtaleBaseChange B f).map
        ((openPostcompose B jY).map ((smallEtaleBaseChange B (jY ≫ g)).map φ)) := by
  refine baseChangeObj_hom_ext B f ?_
  simp only [ObjectProperty.FullSubcategory.comp_hom, Over.comp_left, Category.assoc,
    compChartHom_proj, baseChangeObjProjection_naturality, compChartHom_proj_assoc]
  exact compChartMap_naturality B g sq φ

/-- **The chart inclusion**: the base change of `X` along `W ×_Z Y'`, which is `W ×_Z X'`, maps
by an open immersion into the base change of `X` along `W` for `f ≫ g`. -/
public def compChartInclusion (sq : f' ≫ jY = jX ≫ f) (hsq : IsPullback f' jX jY f)
    (W : SmallEtale B Z.obj Z.property) :
    baseChange B f (compChartBase B g jY W) ⟶ baseChange B (f ≫ g) W :=
  (compChartIso B g sq hsq W).inv ≫ (openBaseChangeMap B jX (f ≫ g)).app W

/-- The chart inclusion is natural in the test object. -/
@[reassoc]
public theorem compChartInclusion_naturality (sq : f' ≫ jY = jX ≫ f)
    (hsq : IsPullback f' jX jY f) {W W' : SmallEtale B Z.obj Z.property} (φ : W' ⟶ W) :
    (smallEtaleBaseChange B f).map
        ((openPostcompose B jY).map ((smallEtaleBaseChange B (jY ≫ g)).map φ)) ≫
        compChartInclusion B g sq hsq W =
      compChartInclusion B g sq hsq W' ≫ (smallEtaleBaseChange B (f ≫ g)).map φ := by
  have hn := (openBaseChangeMap B jX (f ≫ g)).naturality φ
  dsimp only [Functor.comp_map] at hn
  have h' : (smallEtaleBaseChange B f).map
        ((openPostcompose B jY).map ((smallEtaleBaseChange B (jY ≫ g)).map φ)) ≫
        (compChartIso B g sq hsq W).inv =
      (compChartIso B g sq hsq W').inv ≫
        (openPostcompose B jX).map ((smallEtaleBaseChange B (jX ≫ f ≫ g)).map φ) := by
    rw [Iso.comp_inv_eq, Category.assoc]
    show _ = _ ≫ _ ≫ compChartHom B g sq W
    rw [compChartHom_naturality B g sq φ]
    exact ((compChartIso B g sq hsq W').inv_hom_id_assoc _).symm
  rw [compChartInclusion, compChartInclusion, ← Category.assoc, h', Category.assoc, hn,
    Category.assoc]

/-- On schemes, the chart inclusion is the inverse of the chart isomorphism followed by the open
immersion `W ×_Z X' ⟶ W ×_Z X`. -/
public theorem compChartInclusion_toScheme (sq : f' ≫ jY = jX ≫ f)
    (hsq : IsPullback f' jX jY f) (W : SmallEtale B Z.obj Z.property) :
    (SmallEtale.toScheme B X.obj X.property).map (compChartInclusion B g sq hsq W) =
      (SmallEtale.toScheme B X.obj X.property).map (compChartIso B g sq hsq W).inv ≫
        openBaseChangeHom B jX (f ≫ g) W := by
  rw [compChartInclusion, Functor.map_comp, openBaseChangeMap_toScheme]

/-- The chart inclusion is an open immersion. -/
public theorem isOpenImmersion_compChartInclusion (sq : f' ≫ jY = jX ≫ f)
    (hsq : IsPullback f' jX jY f) (W : SmallEtale B Z.obj Z.property) :
    IsOpenImmersion ((SmallEtale.toScheme B X.obj X.property).map
      (compChartInclusion B g sq hsq W)) := by
  rw [compChartInclusion_toScheme]
  exact MorphismProperty.comp_mem @IsOpenImmersion _ _ (IsOpenImmersion.of_isIso _)
    (openBaseChangeHom_isOpenImmersion B jX (f ≫ g) W)

/-- The inverse image under the chart inclusion of the image of a subset of `W ×_Z X'` in
`W ×_Z X` is the image of that subset under the chart isomorphism. -/
public theorem compChartInclusion_preimage_image (sq : f' ≫ jY = jX ≫ f)
    (hsq : IsPullback f' jX jY f) (W : SmallEtale B Z.obj Z.property)
    (T : Set ((SmallEtale.toScheme B X'.obj X'.property).obj (baseChange B (jX ≫ f ≫ g) W))) :
    ((SmallEtale.toScheme B X.obj X.property).map (compChartInclusion B g sq hsq W)).base ⁻¹'
        ((openBaseChangeHom B jX (f ≫ g) W).base '' T) =
      ((SmallEtale.toScheme B X.obj X.property).map (compChartIso B g sq hsq W).hom).base ''
        T := by
  rw [compChartInclusion_toScheme]
  set e := (SmallEtale.toScheme B X.obj X.property).mapIso (compChartIso B g sq hsq W)
  have hinj : Function.Injective (openBaseChangeHom B jX (f ≫ g) W) :=
    (openBaseChangeHom B jX (f ≫ g) W).isOpenEmbedding.injective
  have hinv (y) : e.hom (e.inv y) = y := by rw [← Scheme.Hom.comp_apply, e.inv_hom_id]; rfl
  have hinv' (x) : e.inv (e.hom x) = x := by rw [← Scheme.Hom.comp_apply, e.hom_inv_id]; rfl
  refine Eq.trans ?_ (congrFun (Set.image_eq_preimage_of_inverse hinv' hinv) T).symm
  exact congrArg (e.inv ⁻¹' ·) (Set.preimage_image_eq T hinj)

end Chart

end AlgebraicGeometry.SmallEtale

end
