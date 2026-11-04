module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRespectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# Transporting a property of morphisms of schemes across the two readings of a base change

Let `B` be a big fppf site, let `X` and `T` be objects of it, and let `j : T ⟶ X` be a morphism
of the site over which base change is taken. A morphism `ψ : TL ⟶ TV` of the big fppf category
over `X` can be base changed in three places, and the proof of Stacks 0F9R in the language of
algebraic spaces has to pass between all three:

* on **algebraic spaces over `X`**, as the image of a morphism `p : L ⟶ V` of presheaves under
  the restriction functor `CategoryTheory.OverShriek.relocalizeRestrict j`;
* on the **site over `X`**, as `(CategoryTheory.Over.pullback j).map ψ`, read as a morphism of
  schemes by `AlgebraicGeometry.BigFppfOver.toScheme`;
* on **schemes over the underlying scheme of `X`**, as `(CategoryTheory.Over.pullback ρ).map h`
  for the morphism of schemes `ρ` underlying `j` and a morphism `h` of `Over X` whose
  underlying morphism of schemes is the one `ψ` induces.

The three are base changes of one and the same morphism of schemes, so a property of morphisms
of schemes holds for one exactly when it holds for the others. This module proves that, once,
with the property as a parameter.

Stacks 0F9R is stated in
`StacksFrontier/AlgebraicGeometry/Spaces/BeauvilleLaszloGlueingProperties.lean` in the third of
these readings, one declaration per property, while the algebraic spaces that consume it carry
their hypotheses in the first. The two declarations below are the bridge, and they are stated
for an arbitrary `P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme`: the properties
the Beauville--Laszlo argument needs — being a closed immersion, étaleness, flatness, flatness
together with being locally of finite presentation — are defined on algebraic spaces by three
*different* mechanisms, so there is no single generic transport at the level of algebraic
spaces, but there is one at the level of schemes, which is where both ends of the bridge live.

## Main definitions

* `AlgebraicGeometry.relocalizeRestrictArrowIso`: the comparison of the first two readings, as
  an isomorphism of arrows. This is the whole of the shared content, and the two transports
  below differ only in how they read a property off it.
* `AlgebraicGeometry.yonedaMapArrowIso`: the representation of `p` by `ψ`, as an isomorphism of
  arrows; the shared content of the two statements going back the other way.

## Main results

* `AlgebraicGeometry.prop_toScheme_pullback_map_of_presheaf_relocalizeRestrict` and
  `AlgebraicGeometry.prop_toScheme_pullback_map_of_holdsOnEveryEtaleChart`: the first reading
  implies the second, for a property given as a relatively representable condition and for one
  given by the chart condition of Stacks 03MJ respectively.
* `AlgebraicGeometry.prop_overPullback_map_of_prop_toScheme_pullback_map`: the second reading
  implies the third. If the morphism of schemes underlying `(Over.pullback j).map ψ` has `P`,
  then so does the underlying morphism of `(Over.pullback ρ).map h`.
* `AlgebraicGeometry.prop_of_presheaf_baseChange_triple`: the three legs of a glueing triple
  carried from the first reading to the third at once, which is the form Stacks 0F9R consumes.
* `AlgebraicGeometry.prop_overPullback_map_of_holdsOnEveryEtaleChart`: the same for one leg and
  a chart condition. The row of Stacks 0F9R for flatness together with local finite presentation
  states each component as a conjunction of two properties, so its consumer needs the legs one
  property at a time rather than as a triple.
* `AlgebraicGeometry.presheaf_of_prop_toScheme_map` and
  `AlgebraicGeometry.holdsOnEveryEtaleChart_of_prop_toScheme_map`: the way back for the two
  mechanisms, turning the conclusion of Stacks 0F9R into a statement about the morphism of
  presheaves the argument started from.

## Implementation notes

There are two transports rather than one because the mechanisms differ in what they say about
*representability*, not in how they behave under the comparison isomorphism. A relatively
representable property is a genuine `CategoryTheory.MorphismProperty` on presheaves and
respects isomorphisms for free by
`CategoryTheory.MorphismProperty.relative_respectsIso`; the chart condition of Stacks 03MJ
respects them by `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_respectsIso_presheaf`, also for
every `P`, but it does not entail representability, so it cannot be read through
`AlgebraicGeometry.Space.presheaf_yoneda_map_iff` and is instead read at the identity chart of a
representable. In both cases the transport itself is one application of
`CategoryTheory.MorphismProperty.arrow_mk_iso_iff` to the same isomorphism of arrows.

So the properties the Beauville--Laszlo argument needs are covered as follows: being a closed
immersion is a relatively representable condition and uses the first transport with its
hypothesis being the definition unfolded; flatness and being locally of finite presentation are
chart conditions and use the second; étaleness is neither on the nose, and is converted to a
relatively representable condition by
`AlgebraicGeometry.Space.isEtale_iff_presheaf_of_yoneda`.

The transport from the second reading to the third identifies two fibre products of one cospan
and cancels the comparison isomorphism, which is
`CategoryTheory.prop_snd_iff_of_isPullback`; that isomorphism is kept as a local constant
carrying its defining equation rather than inlined, which is what keeps the proof's unifier
problems small.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 0F9R](https://stacks.math.columbia.edu/tag/0F9R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **The comparison of the two base changes, as an isomorphism of arrows.** This is the one
piece of the transport that is shared by every mechanism defining a property of morphisms of
algebraic spaces, so it is recorded on its own rather than rebuilt inside each.

Restriction of presheaves along `j` carries the presheaf represented by `TL` to the one
represented by the fibre product `TL ×_X T`
(`CategoryTheory.OverShriek.restrictYonedaIso`), naturally in `TL`
(`CategoryTheory.OverShriek.restrictYonedaIso_naturality`). So if `p` corresponds to the
morphism `ψ` of the site under the given representations of its source and target, then the
restriction of `p` along `j` and the Yoneda image of the base change of `ψ` along `j` are the
same arrow up to isomorphism. -/
noncomputable def relocalizeRestrictArrowIso (B : BigFppfSite.{u})
    (X T : Scheme.{u}) (hX : B.Contains X) (hT : B.Contains T) (j : B.obj hT ⟶ B.obj hX)
    {TL TV : BigFppfOver B X hX} (ψ : TL ⟶ TV)
    {L V : (BigFppfOver B X hX)ᵒᵖ ⥤ Type u} (p : L ⟶ V)
    (eL : L ≅ yoneda.obj TL) (eV : V ≅ yoneda.obj TV)
    (hψ : yoneda.map ψ = eL.inv ≫ p ≫ eV.hom) :
    Arrow.mk ((OverShriek.relocalizeRestrict j).map p) ≅
      Arrow.mk (yoneda.map ((Over.pullback j).map ψ)) := by
  have key : (OverShriek.restrictYonedaIso j TL).inv ≫
        yoneda.map ((Over.pullback j).map ψ) =
      (OverShriek.relocalizeRestrict j).map (yoneda.map ψ) ≫
        (OverShriek.restrictYonedaIso j TV).inv := by
    rw [Iso.eq_comp_inv, Category.assoc, OverShriek.restrictYonedaIso_naturality,
      Iso.inv_hom_id_assoc]
  refine Arrow.isoMk
    ((OverShriek.relocalizeRestrict j).mapIso eL ≪≫ (OverShriek.restrictYonedaIso j TL).symm)
    ((OverShriek.relocalizeRestrict j).mapIso eV ≪≫ (OverShriek.restrictYonedaIso j TV).symm)
    ?_
  change ((OverShriek.relocalizeRestrict j).map eL.hom ≫
      (OverShriek.restrictYonedaIso j TL).inv) ≫ yoneda.map ((Over.pullback j).map ψ) =
    (OverShriek.relocalizeRestrict j).map p ≫
      (OverShriek.relocalizeRestrict j).map eV.hom ≫
        (OverShriek.restrictYonedaIso j TV).inv
  rw [Category.assoc, key, hψ, ← Category.assoc, ← Functor.map_comp]
  simp

/-- **From a property of the restricted morphism of presheaves to one of the base change on the
site.** Let `p : L ⟶ V` be a morphism of presheaves on the big fppf category over `X` whose
source and target are representable, by `TL` and `TV`, in such a way that `p` corresponds to the
morphism `ψ : TL ⟶ TV` of the site. If the restriction of `p` along `j` has the relatively
representable property attached to a base-change stable `P`, then the morphism of schemes
underlying the base change of `ψ` along `j` has `P`.

This is the comparison isomorphism
`AlgebraicGeometry.relocalizeRestrictArrowIso` together with the fact that a relatively
representable property of a morphism of representables is that property of the morphism of
schemes underneath. It is the reading the relatively representable properties of Stacks 02YU —
being a closed immersion, an open immersion, an immersion — are defined by, so for those the
hypothesis is the definition unfolded. -/
theorem prop_toScheme_pullback_map_of_presheaf_relocalizeRestrict
    (P : MorphismProperty Scheme.{u}) (hP : P.IsStableUnderBaseChange) (B : BigFppfSite.{u})
    (X T : Scheme.{u}) (hX : B.Contains X) (hT : B.Contains T) (j : B.obj hT ⟶ B.obj hX)
    {TL TV : BigFppfOver B X hX} (ψ : TL ⟶ TV)
    {L V : (BigFppfOver B X hX)ᵒᵖ ⥤ Type u} (p : L ⟶ V)
    (eL : L ≅ yoneda.obj TL) (eV : V ≅ yoneda.obj TV)
    (hψ : yoneda.map ψ = eL.inv ≫ p ≫ eV.hom)
    (hp : (P.inverseImage (BigFppfOver.toScheme B T hT)).presheaf
      ((OverShriek.relocalizeRestrict j).map p)) :
    P ((BigFppfOver.toScheme B T hT).map ((Over.pullback j).map ψ)) :=
  (Space.presheaf_yoneda_map_iff B T hT hP _).1
    ((MorphismProperty.arrow_mk_iso_iff _
      (relocalizeRestrictArrowIso B X T hX hT j ψ p eL eV hψ)).1 hp)

/-- The chart condition for `P` transfers along an isomorphism of arrows of presheaves. -/
private theorem holdsOnEveryEtaleChart_of_arrow_iso (P : MorphismProperty Scheme.{u})
    (B : BigFppfSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
    {L V L' V' : (BigFppfOver B X hX)ᵒᵖ ⥤ Type u} {p : L ⟶ V} {p' : L' ⟶ V'}
    (e : Arrow.mk p ≅ Arrow.mk p') (hp : Space.HoldsOnEveryEtaleChart B X hX P p) :
    Space.HoldsOnEveryEtaleChart B X hX P p' := by
  let Q : MorphismProperty ((BigFppfOver B X hX)ᵒᵖ ⥤ Type u) :=
    fun ⦃_ _⦄ k ↦ Space.HoldsOnEveryEtaleChart B X hX P k
  have : Q.RespectsIso := Space.holdsOnEveryEtaleChart_respectsIso_presheaf B X hX P
  exact (MorphismProperty.arrow_mk_iso_iff Q e).1 hp

/-- **The same transport for a property given by the chart condition of Stacks 03MJ.** The
properties of algebraic spaces that Stacks 03MJ defines — flatness, being locally of finite
presentation, being locally of finite type, smoothness — are not relatively representable
conditions, so the hypothesis cannot be read as in
`AlgebraicGeometry.prop_toScheme_pullback_map_of_presheaf_relocalizeRestrict`. The comparison of
the two base changes is the same isomorphism of arrows, however, and the chart condition
respects isomorphisms for every `P`
(`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_respectsIso_presheaf`), so the transport goes
through unchanged; the chart condition is then read at the identity chart of a representable. -/
theorem prop_toScheme_pullback_map_of_holdsOnEveryEtaleChart
    (P : MorphismProperty Scheme.{u}) (B : BigFppfSite.{u})
    (X T : Scheme.{u}) (hX : B.Contains X) (hT : B.Contains T) (j : B.obj hT ⟶ B.obj hX)
    {TL TV : BigFppfOver B X hX} (ψ : TL ⟶ TV)
    {L V : (BigFppfOver B X hX)ᵒᵖ ⥤ Type u} (p : L ⟶ V)
    (eL : L ≅ yoneda.obj TL) (eV : V ≅ yoneda.obj TV)
    (hψ : yoneda.map ψ = eL.inv ≫ p ≫ eV.hom)
    (hp : Space.HoldsOnEveryEtaleChart B T hT P ((OverShriek.relocalizeRestrict j).map p)) :
    P ((BigFppfOver.toScheme B T hT).map ((Over.pullback j).map ψ)) := by
  exact Space.prop_toScheme_map_of_holdsOnEveryEtaleChart B T hT
    (holdsOnEveryEtaleChart_of_arrow_iso P B T hT
      (relocalizeRestrictArrowIso B X T hX hT j ψ p eL eV hψ) hp) (𝟙 _)
    (Space.presheaf_etale_id B T hT _) (by simp)

/-- **The two readings of one base change on schemes agree.** The base change of `ψ` along a
morphism `j` of the site and the base change along the morphism `ρ` of schemes underneath `j` of
the morphism of schemes underneath `ψ` are isomorphic arrows, hence have the same `P` for any
`P` respecting isomorphisms.

Both are base changes of the same morphism of schemes
(`CategoryTheory.OverShriek.isPullback_pullback_map`), the first computed in the size-cut full
subcategory, which the inclusion into schemes preserves, and the second in schemes; the
comparison of the two fibre products of the target identifies the two cospans. -/
theorem prop_overPullback_map_of_prop_toScheme_pullback_map
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso] (B : BigFppfSite.{u})
    (X T : Scheme.{u}) (hX : B.Contains X) (hT : B.Contains T) (j : B.obj hT ⟶ B.obj hX)
    (ρ : T ⟶ X) (hρ : B.inclusion.map j = ρ)
    {TL TV : BigFppfOver B X hX} (ψ : TL ⟶ TV)
    (h : Over.mk (B.inclusion.map TL.hom) ⟶ Over.mk (B.inclusion.map TV.hom))
    (hh : h.left = (BigFppfOver.toScheme B X hX).map ψ)
    (he : P ((BigFppfOver.toScheme B T hT).map ((Over.pullback j).map ψ))) :
    P ((Over.pullback ρ).map h).left := by
  let : PreservesLimitsOfShape WalkingCospan B.inclusion := inferInstance
  have hTVsq : IsPullback (B.inclusion.map (pullback.fst TV.hom j))
      (B.inclusion.map (pullback.snd TV.hom j)) (B.inclusion.map TV.hom) ρ := by
    rw [← hρ]
    exact (IsPullback.of_hasPullback TV.hom j).map B.inclusion
  let i₂ := hTVsq.isoIsPullback _ _
    (IsPullback.of_hasPullback (B.inclusion.map TV.hom) ρ)
  have hi₂ : i₂.hom ≫ pullback.fst (B.inclusion.map TV.hom) ρ =
      B.inclusion.map (pullback.fst TV.hom j) :=
    hTVsq.isoIsPullback_hom_fst _ _ _
  have sqA : IsPullback ((BigFppfOver.toScheme B T hT).map ((Over.pullback j).map ψ))
      (B.inclusion.map (pullback.fst TL.hom j)) (B.inclusion.map (pullback.fst TV.hom j))
      ((BigFppfOver.toScheme B X hX).map ψ) :=
    (OverShriek.isPullback_pullback_map j ψ).map B.inclusion
  have sqB : IsPullback ((Over.pullback ρ).map h).left
      (pullback.fst (B.inclusion.map TL.hom) ρ)
      (pullback.fst (B.inclusion.map TV.hom) ρ) h.left :=
    OverShriek.isPullback_pullback_map ρ h
  have sqA' : IsPullback
      ((BigFppfOver.toScheme B T hT).map ((Over.pullback j).map ψ) ≫ i₂.hom)
      (B.inclusion.map (pullback.fst TL.hom j))
      (pullback.fst (B.inclusion.map TV.hom) ρ) h.left :=
    sqA.of_iso (Iso.refl _) i₂ (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (by simpa using hi₂.symm) (by simp [hh])
  rw [← prop_snd_iff_of_isPullback P sqA'.flip sqB.flip, P.cancel_right_of_respectsIso]
  exact he

/-- **The three components of a glueing triple, from the first reading to the third.** Let
`p : L ⟶ V` be a morphism of presheaves on the big fppf category over `X` whose source and
target are represented by `TL` and `TV` compatibly with `ψ : TL ⟶ TV`, and let `h` be a morphism
of schemes over `X` underlying `ψ`. Suppose the restriction of `p` along each of three
morphisms `j₁`, `j₂`, `j₃` of the site has the relatively representable property attached to a
base-change stable `P`. Then the base change of `h` along each of the three underlying
morphisms of schemes has `P`, so any statement deducing `P h.left` from those three — in the
application, Stacks 0F9R for `P` — applies.

The three morphisms of schemes are taken as parameters together with their defining equations
rather than spelled out, because the consumer has them in a form the site does not produce on
the nose: the composite leg of the Beauville--Laszlo square is `U' ⟶ U ⟶ X` on the site and the
single morphism `Spec R → Spec R'_{gf}` on schemes, and identifying the two is a computation in
`CommRingCat` that has no business inside this transport. Keeping them as local constants
carrying their equations is also what keeps the unifier's problems here small. -/
theorem prop_of_presheaf_baseChange_triple
    (P : MorphismProperty Scheme.{u}) (hP : P.IsStableUnderBaseChange) (B : BigFppfSite.{u})
    (X T₁ T₂ T₃ : Scheme.{u}) (hX : B.Contains X)
    (hT₁ : B.Contains T₁) (hT₂ : B.Contains T₂) (hT₃ : B.Contains T₃)
    (j₁ : B.obj hT₁ ⟶ B.obj hX) (j₂ : B.obj hT₂ ⟶ B.obj hX) (j₃ : B.obj hT₃ ⟶ B.obj hX)
    (ρ₁ : T₁ ⟶ X) (ρ₂ : T₂ ⟶ X) (ρ₃ : T₃ ⟶ X)
    (hρ₁ : B.inclusion.map j₁ = ρ₁) (hρ₂ : B.inclusion.map j₂ = ρ₂)
    (hρ₃ : B.inclusion.map j₃ = ρ₃)
    {TL TV : BigFppfOver B X hX} (ψ : TL ⟶ TV)
    (h : Over.mk (B.inclusion.map TL.hom) ⟶ Over.mk (B.inclusion.map TV.hom))
    (hh : h.left = (BigFppfOver.toScheme B X hX).map ψ)
    {L V : (BigFppfOver B X hX)ᵒᵖ ⥤ Type u} (p : L ⟶ V)
    (eL : L ≅ yoneda.obj TL) (eV : V ≅ yoneda.obj TV)
    (hψ : yoneda.map ψ = eL.inv ≫ p ≫ eV.hom)
    (hp₁ : (P.inverseImage (BigFppfOver.toScheme B T₁ hT₁)).presheaf
      ((OverShriek.relocalizeRestrict j₁).map p))
    (hp₂ : (P.inverseImage (BigFppfOver.toScheme B T₂ hT₂)).presheaf
      ((OverShriek.relocalizeRestrict j₂).map p))
    (hp₃ : (P.inverseImage (BigFppfOver.toScheme B T₃ hT₃)).presheaf
      ((OverShriek.relocalizeRestrict j₃).map p))
    (hcomponents : P ((Over.pullback ρ₁).map h).left → P ((Over.pullback ρ₂).map h).left →
      P ((Over.pullback ρ₃).map h).left → P h.left) :
    P h.left :=
  have := hP.respectsIso
  hcomponents
    (prop_overPullback_map_of_prop_toScheme_pullback_map P B X T₁ hX hT₁ j₁ ρ₁ hρ₁ ψ h hh
      (prop_toScheme_pullback_map_of_presheaf_relocalizeRestrict P hP B X T₁ hX hT₁ j₁ ψ p
        eL eV hψ hp₁))
    (prop_overPullback_map_of_prop_toScheme_pullback_map P B X T₂ hX hT₂ j₂ ρ₂ hρ₂ ψ h hh
      (prop_toScheme_pullback_map_of_presheaf_relocalizeRestrict P hP B X T₂ hX hT₂ j₂ ψ p
        eL eV hψ hp₂))
    (prop_overPullback_map_of_prop_toScheme_pullback_map P B X T₃ hX hT₃ j₃ ρ₃ hρ₃ ψ h hh
      (prop_toScheme_pullback_map_of_presheaf_relocalizeRestrict P hP B X T₃ hX hT₃ j₃ ψ p
        eL eV hψ hp₃))

/-- **The representation of `p` by `ψ`, as an isomorphism of arrows.** The shared content of the
two statements carrying the conclusion of Stacks 0F9R back to the morphism of presheaves the
argument started from. -/
noncomputable def yonedaMapArrowIso (B : BigFppfSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
    {TL TV : BigFppfOver B X hX} (ψ : TL ⟶ TV)
    {L V : (BigFppfOver B X hX)ᵒᵖ ⥤ Type u} (p : L ⟶ V)
    (eL : L ≅ yoneda.obj TL) (eV : V ≅ yoneda.obj TV)
    (hψ : yoneda.map ψ = eL.inv ≫ p ≫ eV.hom) :
    Arrow.mk (yoneda.map ψ) ≅ Arrow.mk p := by
  refine Arrow.isoMk eL.symm eV.symm ?_
  change eL.inv ≫ p = yoneda.map ψ ≫ eV.inv
  rw [hψ]
  simp

/-- **Back from the morphism of schemes to the morphism of presheaves.** If the morphism of
schemes underlying `ψ` has a base-change stable `P`, then the morphism of presheaves `p` that
`ψ` represents has the relatively representable property attached to `P`.

This is the converse direction of the dictionary, and it is what turns the conclusion of
Stacks 0F9R back into a statement about the algebraic spaces the argument started from. -/
theorem presheaf_of_prop_toScheme_map
    (P : MorphismProperty Scheme.{u}) (hP : P.IsStableUnderBaseChange) (B : BigFppfSite.{u})
    (X : Scheme.{u}) (hX : B.Contains X)
    {TL TV : BigFppfOver B X hX} (ψ : TL ⟶ TV)
    {L V : (BigFppfOver B X hX)ᵒᵖ ⥤ Type u} (p : L ⟶ V)
    (eL : L ≅ yoneda.obj TL) (eV : V ≅ yoneda.obj TV)
    (hψ : yoneda.map ψ = eL.inv ≫ p ≫ eV.hom)
    (hmain : P ((BigFppfOver.toScheme B X hX).map ψ)) :
    (P.inverseImage (BigFppfOver.toScheme B X hX)).presheaf p :=
  (MorphismProperty.arrow_mk_iso_iff _ (yonedaMapArrowIso B X hX ψ p eL eV hψ)).1
    ((Space.presheaf_yoneda_map_iff B X hX hP ψ).2 hmain)

/-- **The way back for a property given by the chart condition of Stacks 03MJ.** If the morphism
of schemes underlying `ψ` has a property that is étale local on source and target, then the
morphism of presheaves `p` that `ψ` represents satisfies the chart condition for it.

The morphism of the site satisfies the chart condition by
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_yoneda_map`, and the chart condition respects
isomorphisms, so it transfers to `p` along
`AlgebraicGeometry.yonedaMapArrowIso`. -/
theorem holdsOnEveryEtaleChart_of_prop_toScheme_map
    (P : MorphismProperty Scheme.{u}) (hP : IsEtaleLocalOnSourceAndTarget P)
    (B : BigFppfSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
    {TL TV : BigFppfOver B X hX} (ψ : TL ⟶ TV)
    {L V : (BigFppfOver B X hX)ᵒᵖ ⥤ Type u} (p : L ⟶ V)
    (eL : L ≅ yoneda.obj TL) (eV : V ≅ yoneda.obj TV)
    (hψ : yoneda.map ψ = eL.inv ≫ p ≫ eV.hom)
    (hmain : P ((BigFppfOver.toScheme B X hX).map ψ)) :
    Space.HoldsOnEveryEtaleChart B X hX P p := by
  exact holdsOnEveryEtaleChart_of_arrow_iso P B X hX (yonedaMapArrowIso B X hX ψ p eL eV hψ)
    (Space.holdsOnEveryEtaleChart_yoneda_map B X hX hP ψ hmain)

/-- **One leg of a glueing triple, from the first reading to the third, for a chart
condition.** The composite of
`AlgebraicGeometry.prop_toScheme_pullback_map_of_holdsOnEveryEtaleChart` and
`AlgebraicGeometry.prop_overPullback_map_of_prop_toScheme_pullback_map`.

This is the per-leg form rather than the triple form of
`AlgebraicGeometry.prop_of_presheaf_baseChange_triple`, because the row of Stacks 0F9R for
flatness together with local finite presentation states each of its three components as a
*conjunction* of two properties, so the consumer needs the legs one property at a time and
assembles them itself. -/
theorem prop_overPullback_map_of_holdsOnEveryEtaleChart
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso] (B : BigFppfSite.{u})
    (X T : Scheme.{u}) (hX : B.Contains X) (hT : B.Contains T) (j : B.obj hT ⟶ B.obj hX)
    (ρ : T ⟶ X) (hρ : B.inclusion.map j = ρ)
    {TL TV : BigFppfOver B X hX} (ψ : TL ⟶ TV)
    (h : Over.mk (B.inclusion.map TL.hom) ⟶ Over.mk (B.inclusion.map TV.hom))
    (hh : h.left = (BigFppfOver.toScheme B X hX).map ψ)
    {L V : (BigFppfOver B X hX)ᵒᵖ ⥤ Type u} (p : L ⟶ V)
    (eL : L ≅ yoneda.obj TL) (eV : V ≅ yoneda.obj TV)
    (hψ : yoneda.map ψ = eL.inv ≫ p ≫ eV.hom)
    (hp : Space.HoldsOnEveryEtaleChart B T hT P ((OverShriek.relocalizeRestrict j).map p)) :
    P ((Over.pullback ρ).map h).left :=
  prop_overPullback_map_of_prop_toScheme_pullback_map P B X T hX hT j ρ hρ ψ h hh
    (prop_toScheme_pullback_map_of_holdsOnEveryEtaleChart P B X T hX hT j ψ p eL eV hψ hp)

end AlgebraicGeometry

end
