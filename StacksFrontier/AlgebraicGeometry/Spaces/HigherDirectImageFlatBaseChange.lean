module

public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageBaseChangeAffineDerived
public import StacksFrontier.AlgebraicGeometry.Spaces.ToposModuleDerivedBaseChangeAffineChartwise
public import StacksFrontier.AlgebraicGeometry.Spaces.ToposModuleDerivedBaseChangeEtaleSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartFactorizationEnoughObjects
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource

/-!
# Flat base change for higher direct images of quasi-coherent modules (Stacks 073K, part (1))

Let

```
  X' ———→ X
   | f'    | f
   v       v
  Y' ———→ Y
      g
```

be a cartesian square of algebraic spaces over a scheme `S`, with `g` flat and `f`
quasi-compact and quasi-separated, and let `𝓕` be a quasi-coherent `𝒪_X`-module.  For every
`i ≥ 0` the base change map of **Stacks 0736**

`g^*R^if_*𝓕 ⟶ R^if'_*(g')^*𝓕`

is an isomorphism.

## Main results

* `AlgebraicGeometry.Space.isIso_toposModuleDerivedBaseChangeMap_app_single_of_isFlat`: the base
  change map `g^*Rf_* ⟶ Rf'_*(g')^*` of **Stacks 0736** on bounded below derived categories is
  invertible at `𝓕` placed in degree zero.
* `AlgebraicGeometry.Space.isIso_higherDirectImageBaseChangeMap_of_isFlat`: **Stacks 073K,
  part (1)**.

## Proof

The question is étale local on `Y'`: by
`Space.isIso_toposModuleDerivedBaseChangeMap_app_of_forall_chart_of_hasEnoughObjects` it suffices
to treat, for every affine étale chart `V ⟶ Y'` whose composite to `Y` factors as `V ⟶ W ⟶ Y`
through an affine étale chart `W` of `Y` — these are enough objects of the small étale site of `Y'`
(`AlgebraicGeometry.Space.hasEnoughObjects_isAffineChartFactorsThroughAffineChart`) — the base
change map of the rectangle obtained by pasting the cartesian square of `V ⟶ Y'` onto the given
square, and the base change map of the cartesian square of `V ⟶ Y'` itself.  The latter is an étale
square (`AlgebraicGeometry.Space.isIso_toposModuleDerivedBaseChangeMap_app_of_isEtale`).  The
rectangle is also the pasting of the étale square of `W ⟶ Y` and of a cartesian square over the
morphism `V ⟶ W` of affine schemes, which is flat since `V ⟶ Y` is flat and `W ⟶ Y` is étale
(`AlgebraicGeometry.Space.isFlat_yoneda_map_of_comp_eq`); over affine bases the base change map is
invertible by `Space.BaseChangeDiagram.isIso_toposModuleDerivedBaseChangeMap_app_single_of_affine`,
and the pasting law of **Stacks 0E47**
(`AlgebraicGeometry.Space.isIso_toposModuleDerivedBaseChangeMap_app_paste`) concludes.  Finally
`AlgebraicGeometry.Space.isIso_higherDirectImageBaseChangeMap_app` passes from `D⁺` to each degree.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 0736](https://stacks.math.columbia.edu/tag/0736)
* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] enoughInjectives_modules chartwiseLocalityHasDerivedCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Flatness

variable (B S hS)

/-- **A morphism of étale charts over a flat morphism is flat.**  If `g : Y' ⟶ Y` is flat, `V` is
an étale chart of `Y'`, `W` one of `Y` and `m : V ⟶ W` lies over `g`, then `m` is flat: a commuting
square of étale charts for `m` is, after composing its chart of `W` with the étale `W ⟶ Y`, a
commuting square of étale charts for the flat composite `V ⟶ Y' ⟶ Y`. -/
theorem isFlat_yoneda_map_of_comp_eq {Y' Y : AlgebraicSpaces B S hS} (g : Y' ⟶ Y)
    (hg : IsFlat B S hS g.hom) {V : SmallEtale B S hS Y'.obj} {W : SmallEtale B S hS Y.obj}
    (m : V.obj.left ⟶ W.obj.left) (hm : yoneda.map m ≫ W.obj.hom = V.obj.hom ≫ g.hom) :
    IsFlat B S hS (yoneda.map m) := by
  have hV : IsFlat B S hS (V.obj.hom ≫ g.hom) :=
    isFlat_comp_of_etale_chart B S hS Y'.property Y.property V.obj.hom V.property g.hom hg
  have := (isMultiplicative_presheaf_etale B S hS).toIsStableUnderComposition
  intro U U' a b h ha hb hcomm
  refine hV U U' a (b ≫ W.obj.hom) h ha (MorphismProperty.comp_mem _ _ _ hb W.property) ?_
  rw [← Category.assoc, hcomm, Category.assoc, hm]

end Flatness

section Reduction

variable {X X' Y Y' : AlgebraicSpaces B S hS}

/-- Invertibility of the base change map of **Stacks 0736** at an object depends on the two
horizontal morphisms of the square only through the morphisms themselves. -/
theorem isIso_toposModuleDerivedBaseChangeMap_app_congr (f : X ⟶ Y) (f' : X' ⟶ Y')
    {g₁ g₂ : Y' ⟶ Y} {g'₁ g'₂ : X' ⟶ X} (hg : g₁ = g₂) (hg' : g'₁ = g'₂)
    [PreservesFiniteLimits (modulePullback B S hS g₁)]
    [PreservesFiniteColimits (modulePullback B S hS g₁)]
    [PreservesFiniteLimits (modulePullback B S hS g₂)]
    [PreservesFiniteColimits (modulePullback B S hS g₂)]
    (comm₁ : g'₁ ≫ f = f' ≫ g₁) (comm₂ : g'₂ ≫ f = f' ≫ g₂)
    (M : DerivedCategory.Plus (Modules.{u, u} B S hS X.1 X.2)) :
    IsIso ((toposModuleDerivedBaseChangeMap f g₁ f' g'₁ comm₁).app M) ↔
      IsIso ((toposModuleDerivedBaseChangeMap f g₂ f' g'₂ comm₂).app M) := by
  subst hg hg'
  rfl

/-- The inverse image along an étale morphism of algebraic spaces is left exact: an étale
morphism is flat (**Stacks 0467**), and **Stacks 04JC** applies. -/
theorem preservesFiniteLimits_modulePullback_of_isEtale_hom {Z W : AlgebraicSpaces B S hS}
    (k : Z ⟶ W) (hk : IsEtale B S hS k.hom) : PreservesFiniteLimits (modulePullback B S hS k) :=
  preservesFiniteLimits_modulePullback_of_isFlat_hom B S hS k (isFlat_of_isEtale B S hS hk)

/-- **The base change map of Stacks 0736 for a flat base change, in `D⁺`.**  For a cartesian
square of algebraic spaces with `g` flat and `f` quasi-compact and quasi-separated, the base
change map `g^*Rf_* ⟶ Rf'_*(g')^*` is invertible at every quasi-coherent `𝓕` placed in degree
zero. -/
theorem isIso_toposModuleDerivedBaseChangeMap_app_single_of_isFlat {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g) (hg : IsFlat B S hS g.hom)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    [PreservesFiniteLimits (modulePullback B S hS g)]
    [PreservesFiniteColimits (modulePullback B S hS g)] :
    IsIso ((toposModuleDerivedBaseChangeMap f g f' g' sq.w).app
      ((DerivedCategory.Plus.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj F)) := by
  refine isIso_toposModuleDerivedBaseChangeMap_app_of_forall_chart_of_hasEnoughObjects f g f' g'
    sq.w (hasEnoughObjects_isAffineChartFactorsThroughAffineChart B S hS g) _ ?_
  rintro V ⟨hVaff, W, m, hWaff, hm⟩
  set v := chartToSpace B S hS Y' V
  set w := chartToSpace B S hS Y W
  let mA : chartSpace B S hS Y' V ⟶ chartSpace B S hS Y W := ObjectProperty.homMk (yoneda.map m)
  have hmA : mA ≫ w = v ≫ g := ObjectProperty.hom_ext _ hm
  have hmflat : IsFlat B S hS mA.hom := isFlat_yoneda_map_of_comp_eq B S hS g hg m hm
  have hvet : IsEtale B S hS v.hom := isEtale_chartToSpace B S hS Y' V
  have hwet : IsEtale B S hS w.hom := isEtale_chartToSpace B S hS Y W
  have sqV : IsPullback (pullback.fst f' v) (pullback.snd f' v) f' v :=
    IsPullback.of_hasPullback f' v
  have sqW : IsPullback (pullback.fst f w) (pullback.snd f w) f w := IsPullback.of_hasPullback f w
  set g'' := pullback.fst f' v
  set f'' := pullback.snd f' v
  set gW := pullback.fst f w
  set fW := pullback.snd f w
  let gA : pullback f' v ⟶ pullback f w := pullback.lift (g'' ≫ g') (f'' ≫ mA) (by
    simp only [Category.assoc, sq.w, hmA]
    rw [← Category.assoc, sqV.w, Category.assoc])
  have hgA : gA ≫ gW = g'' ≫ g' := pullback.lift_fst _ _ _
  have hfA : gA ≫ fW = f'' ≫ mA := pullback.lift_snd _ _ _
  have sqA : IsPullback gA f'' fW mA := by
    refine IsPullback.of_right ?_ hfA sqW
    rw [hgA, hmA]
    exact sqV.paste_horiz sq
  have := preservesFiniteLimits_modulePullback_of_isEtale_hom v hvet
  have := preservesFiniteLimits_modulePullback_of_isEtale_hom w hwet
  have := preservesFiniteLimits_modulePullback_of_isEtale_hom g''
    (isEtale_of_isPullback B S hS _ _ _ _ sqV.flip hvet)
  have := preservesFiniteLimits_modulePullback_of_isEtale_hom gW
    (isEtale_of_isPullback B S hS _ _ _ _ sqW.flip hwet)
  have := preservesFiniteLimits_modulePullback_of_isFlat_hom B S hS mA hmflat
  have := preservesFiniteLimits_modulePullback_of_isFlat_hom B S hS gA
    ((isFlat_isStableUnderBaseChange B S hS).of_isPullback sqA.flip hmflat)
  have : PreservesFiniteLimits (modulePullback B S hS (v ≫ g)) :=
    preservesFiniteLimits_modulePullback_of_isFlat_hom B S hS (v ≫ g)
      (isFlat_comp B S hS (chartSpace B S hS Y' V).property Y'.property Y.property v.hom g.hom
        (isFlat_of_isEtale B S hS hvet) hg)
  have : PreservesFiniteLimits (modulePullback B S hS (mA ≫ w)) := by rw [hmA]; infer_instance
  have : ∀ {Z T : AlgebraicSpaces B S hS} (k : Z ⟶ T),
      PreservesFiniteColimits (modulePullback B S hS k) :=
    fun k => preservesFiniteColimits_modulePullback_smallEtale B S hS k
  refine ⟨pullback f' v, f'', g'', sqV.w, inferInstance, inferInstance, inferInstance,
    inferInstance, ?_, isIso_toposModuleDerivedBaseChangeMap_app_of_isEtale sqV hvet _⟩
  have hqcW : IsQuasiCompact B S hS fW.hom :=
    isQuasiCompact_of_isPullback B S hS (AlgebraicSpaces.isPullback_hom _ _ _ sqW) hfqc
  have hqsW : IsQuasiSeparated B S hS fW.hom :=
    isQuasiSeparated_of_isPullback B S hS (AlgebraicSpaces.isPullback_hom _ _ _ sqW) hfqs
  let DA : BaseChangeDiagram B S hS :=
    { X' := pullback f' v
      X := pullback f w
      Y' := chartSpace B S hS Y' V
      Y := chartSpace B S hS Y W
      g' := gA
      f' := f''
      f := fW
      g := mA
      isPullback := sqA
      F := (modulePullback B S hS gW).obj F
      isQuasicoherent :=
        isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS gW F hF }
  let V₀ : SmallEtale B S hS DA.Y.1 := idEtaleChart B S hS ((SmallEtale.toOver B S hS Y.obj).obj W)
  let V₀' : SmallEtale B S hS DA.Y'.1 :=
    idEtaleChart B S hS ((SmallEtale.toOver B S hS Y'.obj).obj V)
  have : IsIso V₀.obj.hom := inferInstanceAs (IsIso (𝟙 _))
  have : IsIso V₀'.obj.hom := inferInstanceAs (IsIso (𝟙 _))
  have : IsAffine (chartScheme V₀) := hWaff
  have : IsAffine (chartScheme V₀') := hVaff
  have hright : IsIso ((toposModuleDerivedBaseChangeMap fW mA f'' gA sqA.w).app
      ((modulePullback B S hS gW).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) :=
    (NatTrans.isIso_app_iff_of_iso _
      ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
        (modulePullback B S hS gW) 0).app F).symm).2
      (DA.isIso_toposModuleDerivedBaseChangeMap_app_single_of_affine hmflat hqcW hqsW V₀ V₀')
  exact (isIso_toposModuleDerivedBaseChangeMap_app_congr f f'' hmA hgA _ _ _).1
    (isIso_toposModuleDerivedBaseChangeMap_app_paste f fW f'' w gW mA gA sqW.w sqA.w
      _ (isIso_toposModuleDerivedBaseChangeMap_app_of_isEtale sqW hwet _) hright)

end Reduction

section Registration

variable {X X' Y Y' : AlgebraicSpaces B S hS}

/-- **Stacks 073K, part (1): flat base change for higher direct images.**  Let

```
  X' ———→ X
   | f'    | f
   v       v
  Y' ———→ Y
      g
```

be a cartesian square of algebraic spaces over `S` with `g` flat and `f` quasi-compact and
quasi-separated, and let `𝓕` be a quasi-coherent `𝒪_X`-module with pullback `𝓕' = (g')^*𝓕`.  For
every `i ≥ 0` the base change map of **Stacks 0736**

`g^*R^if_*𝓕 ⟶ R^if'_*𝓕'`

(`AlgebraicGeometry.Space.higherDirectImageBaseChangeMap`) is an isomorphism.

The exactness of the two inverse images `g^*` and `(g')^*` that the base change map is constructed
against is **Stacks 04JC** for the flat `g` and, `g'` being flat by **Stacks 03MO**, for `g'`. -/
@[stacks 073K "part (1): for a cartesian square of algebraic spaces with g flat and f
  quasi-compact and quasi-separated, the base change map g^*R^if_*F ⟶ R^if'_*F' of Tag 0736 is an
  isomorphism for every quasi-coherent F and every i ≥ 0"]
theorem isIso_higherDirectImageBaseChangeMap_of_isFlat {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g) (hg : IsFlat B S hS g.hom)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) (i : ℕ) :
    have := preservesFiniteLimits_modulePullback_of_isFlat_hom B S hS g hg
    have := preservesFiniteColimits_modulePullback_smallEtale B S hS g
    have := preservesFiniteLimits_modulePullback_of_isFlat_hom B S hS g'
      ((isFlat_isStableUnderBaseChange B S hS).of_isPullback sq.flip hg)
    have := preservesFiniteColimits_modulePullback_smallEtale B S hS g'
    IsIso ((higherDirectImageBaseChangeMap f g f' g' sq.w i).app F) := by
  intro _ _ _ _
  exact isIso_higherDirectImageBaseChangeMap_app f g f' g' sq.w F
    (isIso_toposModuleDerivedBaseChangeMap_app_single_of_isFlat sq hg hfqc hfqs F hF) i

end Registration

end AlgebraicGeometry.Space

end
