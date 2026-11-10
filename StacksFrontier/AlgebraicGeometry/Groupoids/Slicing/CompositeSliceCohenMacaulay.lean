module

public import StacksFrontier.AlgebraicGeometry.Groupoids.More.DoubleRestrictionDescent
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.OverPullback
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FppfLocalTarget
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.OpenImmersion
public import StacksCore.Tactic.StacksAttribute

/-!
# Cohen–Macaulayness of the source map over a composite slice

Let `(U, R, s, t, c)` be a groupoid scheme over `S`, let `g : U' ⟶ U` and `g' : U'' ⟶ U'` be
morphisms and set `g'' = g ∘ g'`. Write

  `h   = s  ∘ pr₁ : U'  ×_{g , U , t } R  ⟶ U`,
  `h'  = s' ∘ pr₁ : U'' ×_{g', U', t'} R' ⟶ U'`,
  `h'' = s  ∘ pr₁ : U'' ×_{g'', U , t } R  ⟶ U`.

If `h` is flat and locally of finite presentation and `h'` is Cohen–Macaulay with locally
Noetherian fibres, then so is `h''`.

## Main results

* `AlgebraicGeometry.cohenMacaulayWithLocallyNoetherianFibers_compositeSourceMap` is the
  implication.

## Implementation notes

This is the composite step of the induction of Tag 04MZ, and it does not follow from stability
of Cohen–Macaulayness under composition: `h''` is not a composite of `h` and `h'`. The two
cartesian squares of Tag 04MW make `h'` base-change to the left leg of the square relating `h`
and `h''`, and `h''` is then recovered from that leg by descent along `h`.

Descent needs `h` to be a covering, which it is not: it covers only its own image. Since `h` is
flat and locally of finite presentation it is an open map, so that image is an open subscheme `V`
of `U`; and `h`, viewed as a morphism onto `V`, is flat, locally of finite presentation and
surjective, hence a one-element fppf covering of `V`. The morphism `h''` factors through `V`
because `g'' = g ∘ g'` puts its image inside the image of `h`, and the property descends to that
factorization by Tag 045V, Cohen–Macaulayness with locally Noetherian fibres being local on the
target for the fppf topology. Composing back with the open immersion `V ⟶ U` uses Tag 01UJ and
Tag 0C0W: an open immersion is syntomic, hence Cohen–Macaulay, and Cohen–Macaulay morphisms
compose.

The base change of `h'` to the left leg is the one place needing a finite type hypothesis: Tag
045T asks the morphism base-changed *along* to be locally of finite type, and here that morphism
is `pr₁ : U' ×_{g, U, t} R ⟶ U'`, a base change of `t`. Hence the hypothesis that `t` is locally
of finite type.

The general statement being specialized is Tag 04MX, which the library already carries in both
directions as `AlgebraicGeometry.restrictionSource_mem_of_composite` and
`AlgebraicGeometry.descent_to_open_image`. Those take the open image and its covering as given
and ask for an unconditional base-change stability of the property, which Cohen–Macaulayness
with locally Noetherian fibres does not have — being locally Noetherian is not preserved by base
change along an arbitrary morphism. The descent is therefore redone here with the finite type
hypothesis in hand.

## References

* [Stacks Project, Tag 04MZ](https://stacks.math.columbia.edu/tag/04MZ)
* [Stacks Project, Tag 04MX](https://stacks.math.columbia.edu/tag/04MX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- The image of a flat morphism locally of finite presentation, as an open subscheme of the
target: such a morphism is universally open, hence an open map. -/
private def flatImageOpens {A Y : Scheme.{u}} (h : A ⟶ Y) [Flat h]
    [LocallyOfFinitePresentation h] : Y.Opens :=
  ⟨Set.range h.base, by
    have _ : UniversallyOpen h := universallyOpen_of_flat_of_locallyOfFinitePresentation h
    exact h.isOpenMap.isOpen_range⟩

/-- The open image is exactly the image. -/
private theorem range_ι_flatImageOpens {A Y : Scheme.{u}} (h : A ⟶ Y) [Flat h]
    [LocallyOfFinitePresentation h] :
    Set.range (flatImageOpens h).ι.base = Set.range h.base :=
  (flatImageOpens h).range_ι

/-- A morphism factoring through an open immersion is the base change of itself along that
immersion, so every base-change-stable property of it passes to the factorization. -/
private theorem lift_mem_of_mem {A Y : Scheme.{u}} {V : Y.Opens} (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] (h : A ⟶ Y) (hsub : Set.range h.base ⊆ Set.range V.ι.base)
    (hh : P h) : P (IsOpenImmersion.lift V.ι h hsub) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsOpenImmersion.isPullback_lift_id h V.ι hsub).flip hh

/-- Descent along a flat morphism locally of finite presentation, onto its open image. Given a
cartesian square whose bottom row is `f` and `h`, a property local on the target for the fppf
topology passes from the leg over `h` to the factorization of `f` through the open image of `h`,
provided the image of `f` lies in the image of `h`. -/
private theorem descend_to_flatImage (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtTarget Scheme.fppfPrecoverage]
    {A B C Y : Scheme.{u}} (h : A ⟶ Y) [Flat h] [LocallyOfFinitePresentation h]
    (f : B ⟶ Y) (hsub : Set.range f.base ⊆ Set.range (flatImageOpens h).ι.base)
    {a : C ⟶ B} {b : C ⟶ A} (sq : IsPullback a b f h) (hb : P b) :
    P (IsOpenImmersion.lift (flatImageOpens h).ι f hsub) := by
  have hsubh : Set.range h.base ⊆ Set.range (flatImageOpens h).ι.base :=
    le_of_eq (range_ι_flatImageOpens h).symm
  -- `h` viewed as a morphism onto its open image is a one-element fppf covering of it.
  have hqfac : IsOpenImmersion.lift (flatImageOpens h).ι h hsubh ≫ (flatImageOpens h).ι = h :=
    IsOpenImmersion.lift_fac _ _ _
  have _ : Flat (IsOpenImmersion.lift (flatImageOpens h).ι h hsubh) :=
    lift_mem_of_mem @Flat h hsubh ‹_›
  have _ : LocallyOfFinitePresentation (IsOpenImmersion.lift (flatImageOpens h).ι h hsubh) :=
    lift_mem_of_mem @LocallyOfFinitePresentation h hsubh ‹_›
  have _ : Surjective (IsOpenImmersion.lift (flatImageOpens h).ι h hsubh) := by
    refine ⟨fun v => ?_⟩
    obtain ⟨x, hx⟩ : (flatImageOpens h).ι.base v ∈ Set.range h.base := by
      rw [← range_ι_flatImageOpens h]; exact ⟨v, rfl⟩
    refine ⟨x, (flatImageOpens h).ι.isEmbedding.injective ?_⟩
    change ((IsOpenImmersion.lift (flatImageOpens h).ι h hsubh) ≫
      (flatImageOpens h).ι).base x = _
    rw [hqfac]; exact hx
  have hcover : Presieve.singleton (IsOpenImmersion.lift (flatImageOpens h).ι h hsubh) ∈
      Scheme.fppfPrecoverage (flatImageOpens h).toScheme :=
    Scheme.Hom.singleton_mem_fppfPrecoverage _
  -- The given square, factored through the open image.
  have hright : IsPullback a b (IsOpenImmersion.lift (flatImageOpens h).ι f hsub)
      (IsOpenImmersion.lift (flatImageOpens h).ι h hsubh) := by
    have _ : Mono (flatImageOpens h).ι := IsOpenImmersion.mono (flatImageOpens h).ι
    exact IsPullback.of_isLimit (PullbackCone.isLimitOfFactors f h (flatImageOpens h).ι
      (IsOpenImmersion.lift (flatImageOpens h).ι f hsub)
      (IsOpenImmersion.lift (flatImageOpens h).ι h hsubh)
      (IsOpenImmersion.lift_fac _ _ _) hqfac _ sq.isLimit)
  apply MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd (P := P) hcover
  intro T k _ hk
  cases hk
  let hcanon := IsPullback.of_hasPullback (IsOpenImmersion.lift (flatImageOpens h).ι f hsub)
    (IsOpenImmersion.lift (flatImageOpens h).ι h hsubh)
  let e := hright.isoIsPullback _ _ hcanon
  apply (P.cancel_left_of_respectsIso e.hom _).mp
  exact (hright.isoIsPullback_hom_snd _ _ hcanon).symm ▸ hb

/-- Base change of a Cohen–Macaulay morphism with locally Noetherian fibres along a morphism
locally of finite type, for an arbitrary cartesian square. This is Tag 045T, transported from
the canonical fibre product. -/
@[ega "IV 6.8.2" "(ii)"]
private theorem cohenMacaulay_of_isPullback {X Y Y' Z : Scheme.{u}}
    {a : Z ⟶ X} {b : Z ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback a b f g) (hg : LocallyOfFiniteType g)
    (hf : cohenMacaulayWithLocallyNoetherianFibers f) :
    cohenMacaulayWithLocallyNoetherianFibers b := by
  have _ := hg
  obtain ⟨hNoeth, hCM⟩ := hf
  have hbase : cohenMacaulayWithLocallyNoetherianFibers (pullback.snd f g) :=
    ⟨fun y => isLocallyNoetherian_fiber_pullback f g hNoeth y,
      fun x => isCohenMacaulayAt_pullback f g hNoeth x (hCM _)⟩
  rw [← sq.isoPullback_hom_snd]
  exact (cohenMacaulayWithLocallyNoetherianFibers.cancel_left_of_respectsIso
    sq.isoPullback.hom _).mpr hbase

/-- A morphism Cohen–Macaulay with locally Noetherian fibres and locally of finite presentation
stays so after composing with an open immersion: an open immersion is syntomic, hence
Cohen–Macaulay, and Cohen–Macaulay morphisms compose. -/
private theorem cohenMacaulay_comp_isOpenImmersion {X V Y : Scheme.{u}}
    (q : X ⟶ V) (j : V ⟶ Y) [IsOpenImmersion j] [LocallyOfFinitePresentation q]
    (hq : cohenMacaulayWithLocallyNoetherianFibers q) :
    cohenMacaulayWithLocallyNoetherianFibers (q ≫ j) := by
  obtain ⟨hqNoeth, hqCM⟩ := hq
  have hjNoeth : ∀ y : Y, IsLocallyNoetherian (j.fiber y) := fun y =>
    isLocallyNoetherian_fiber_of_locallyOfFinitePresentation j y
  have hcNoeth : ∀ y : Y, IsLocallyNoetherian ((q ≫ j).fiber y) := fun y =>
    isLocallyNoetherian_fiber_of_locallyOfFinitePresentation (q ≫ j) y
  exact ⟨hcNoeth, isCohenMacaulay_comp q j hqNoeth hjNoeth hcNoeth hqCM
    (isCohenMacaulay_of_syntomic (syntomic_of_isOpenImmersion j) hjNoeth)⟩

/-- The comparison from the composite fibre product to the first one, over `U'`. -/
private def compositeToFirst {S : Scheme.{u}} (G : GroupoidScheme S) {U' U'' : Over S}
    (g : U' ⟶ G.objects) (g' : U'' ⟶ U') :
    compositeArrowSource G g g' ⟶ firstArrowSource G g :=
  pullback.lift (pullback.fst (g' ≫ g) G.target ≫ g')
    (pullback.snd (g' ≫ g) G.target)
    (by
      change (pullback.fst (g' ≫ g) G.target ≫ g') ≫ g = _
      rw [Category.assoc]
      exact pullback.condition)

/-- The comparison is compatible with the two source maps. -/
private theorem compositeToFirst_comp {S : Scheme.{u}} (G : GroupoidScheme S) {U' U'' : Over S}
    (g : U' ⟶ G.objects) (g' : U'' ⟶ U') :
    compositeToFirst G g g' ≫ firstSourceMap G g = compositeSourceMap G g g' := by
  dsimp [compositeToFirst, firstSourceMap, compositeSourceMap, firstArrowSource,
    compositeArrowSource]
  exact congrArg (fun f : compositeArrowSource G g g' ⟶ G.arrows => f ≫ G.source)
    (pullback.lift_snd _ _ _)

/-- **Stacks Project, Tag 04MZ**, the composite step. Let `(U, R, s, t, c)` be a groupoid scheme
over `S` with `t` locally of finite type, let `g : U' ⟶ U` and `g' : U'' ⟶ U'` be morphisms of
schemes over `S` and set `g'' = g ∘ g'`. Suppose `h : U' ×_{g, U, t} R ⟶ U` is flat and locally
of finite presentation, that `h'' : U'' ×_{g'', U, t} R ⟶ U` is locally of finite presentation,
and that `h' : U'' ×_{g', U', t'} R' ⟶ U'` is Cohen–Macaulay with locally Noetherian fibres.
Then `h''` is Cohen–Macaulay with locally Noetherian fibres.

This is Tag 04MX applied to Cohen–Macaulayness with locally Noetherian fibres and the fppf
topology, that property being fppf local on the target by Tag 045V; the two hypotheses of Tag
04MX on the image of `h` hold because a flat morphism locally of finite presentation is open and
covers its own open image.

The step is needed in the induction of Tag 04MZ because `h''` is not a composite of `h` and
`h'`, so Cohen–Macaulayness of `h''` does not follow from stability under composition. -/
public theorem cohenMacaulayWithLocallyNoetherianFibers_compositeSourceMap
    {S : Scheme.{u}} (G : GroupoidScheme S) {U' U'' : Over S}
    (g : U' ⟶ G.objects) (g' : U'' ⟶ U')
    [LocallyOfFiniteType G.target.left]
    [Flat (firstSourceMap G g).left]
    [LocallyOfFinitePresentation (firstSourceMap G g).left]
    [LocallyOfFinitePresentation (compositeSourceMap G g g').left]
    (hCM' : cohenMacaulayWithLocallyNoetherianFibers (secondSourceMap G g g').left) :
    cohenMacaulayWithLocallyNoetherianFibers (compositeSourceMap G g g').left := by
  have hfstLFT : LocallyOfFiniteType (pullback.fst g G.target).left :=
    overFibreProduct_fst g G.target ‹LocallyOfFiniteType G.target.left›
  -- The left leg of the right-hand square is the base change of `h'` along `pr₁`.
  have hcommon := cohenMacaulay_of_isPullback
    ((doubleRestrictionDiagram G g g').left_isPullback.map (Over.forget S)) hfstLFT hCM'
  -- The composite source map lands in the image of `h`, since `g'' = g ∘ g'`.
  have hsub : Set.range (compositeSourceMap G g g').left.base ⊆
      Set.range (flatImageOpens (firstSourceMap G g).left).ι.base := by
    rw [range_ι_flatImageOpens]
    rintro - ⟨x, rfl⟩
    refine ⟨(compositeToFirst G g g').left.base x, ?_⟩
    have hj := congrArg (fun k : compositeArrowSource G g g' ⟶ G.objects => k.left.base x)
      (compositeToFirst_comp G g g')
    simpa only [Over.comp_left, Scheme.Hom.comp_apply] using hj
  -- Descend along the covering, then compose back with the open immersion of the image.
  have hrightpb := (doubleRestrictionDiagram G g g').right_isPullback.map (Over.forget S)
  have hr := descend_to_flatImage cohenMacaulayWithLocallyNoetherianFibers
    (firstSourceMap G g).left (compositeSourceMap G g g').left hsub
    hrightpb hcommon
  have hrfac : IsOpenImmersion.lift (flatImageOpens (firstSourceMap G g).left).ι
      (compositeSourceMap G g g').left hsub ≫
        (flatImageOpens (firstSourceMap G g).left).ι = (compositeSourceMap G g g').left :=
    IsOpenImmersion.lift_fac _ _ _
  have _ : LocallyOfFinitePresentation
      (IsOpenImmersion.lift (flatImageOpens (firstSourceMap G g).left).ι
        (compositeSourceMap G g g').left hsub) :=
    lift_mem_of_mem @LocallyOfFinitePresentation _ hsub ‹_›
  rw [← hrfac]
  exact cohenMacaulay_comp_isOpenImmersion _ _ hr

end AlgebraicGeometry

end
