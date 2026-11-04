module

public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleDescent

/-!
# Separating the object from the property in effective descent along an étale chart

`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale B S hS P` asserts that morphisms
with property `P` descend effectively along a surjective étale morphism of the big fppf site of
`S`. If a morphism `f` of presheaves is already known to be representable, and a surjective étale
chart `g` of its target makes the base change of `f` have a property `Q` which descends along
surjective flat morphisms of finite presentation, then `f` itself is representable with `Q`.
Consequently effective descent at a single property `P` supplies representability with every such
`Q`, and effective descent at `P` implies it at every such `Q ≤ P`.

## Main results

* `AlgebraicGeometry.Space.presheaf_of_surjectiveEtaleChart_of_descendsAlong`: a representable
  morphism of presheaves whose base change along a surjective étale chart of its target has a
  property which descends along surjective flat morphisms of finite presentation has that
  property.
* `AlgebraicGeometry.Space.presheaf_of_surjectiveEtaleChart_of_descent`: the same for a morphism of
  sheaves whose base change along the chart also has a property `P` at which
  `AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale` holds.
* `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_le`: effective descent
  along surjective étale morphisms at a property `P` implies it at every property `Q ≤ P`
  which descends along surjective flat morphisms of finite presentation.
* `AlgebraicGeometry.Space.presheaf_surjective_and_etale_of_surjectiveEtaleChart`: from
  effective descent at `IsSeparated ⊓ LocallyQuasiFinite`, a morphism of sheaves whose base
  change along a surjective étale chart of its target is a separated locally quasi-finite,
  surjective and étale morphism of schemes is representable, surjective and étale.
* `AlgebraicGeometry.Space.etale_descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation`
  and its `Surjective` companion: étale and surjective morphisms satisfy fppf descent.
* `AlgebraicGeometry.Space.isImmersion_le_isSeparated_inf_locallyQuasiFinite` and
  `Space.monomorphisms_inf_locallyOfFiniteType_le_isSeparated_inf_locallyQuasiFinite`: immersions,
  and monomorphisms locally of finite type, are separated and locally quasi-finite.

## References

* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 02Z0](https://stacks.math.columbia.edu/tag/02Z0)
* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
* [Stacks Project, Tag 0265](https://stacks.math.columbia.edu/tag/0265)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace Space

/-! ### fppf descent of the two properties of a chart -/

/-- A property of morphisms of schemes which is Zariski local on the target and descends along
the surjective flat quasi-compact morphisms descends along the surjective flat morphisms of
finite presentation. -/
theorem descendsAlong_fppf (Q : MorphismProperty Scheme.{u})
    [Q.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)] [IsZariskiLocalAtTarget Q] :
    Q.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
  inferInstance

/-- Étale morphisms satisfy fppf descent: if the base change of `g` along a surjective flat
morphism of finite presentation is étale, then so is `g`. -/
theorem etale_descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation :
    MorphismProperty.DescendsAlong (@Etale.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
  have : IsZariskiLocalAtTarget (@Etale.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := RingHom.Etale)
  descendsAlong_fppf _

/-- Surjective morphisms satisfy fppf descent: if the base change of `g` along a surjective
flat morphism of finite presentation is surjective, then so is `g`. -/
theorem surjective_descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation :
    MorphismProperty.DescendsAlong (@Surjective.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
  descendsAlong_fppf _

/-- A surjective étale morphism of schemes is surjective, flat and locally of finite
presentation. -/
theorem surjective_inf_flat_inf_locallyOfFinitePresentation_of_etale {X Y : Scheme.{u}}
    (f : X ⟶ Y) (hs : Surjective f) (he : Etale f) :
    (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) f :=
  have : Etale f := he
  ⟨⟨hs, inferInstance⟩, inferInstance⟩

/-! ### Separated locally quasi-finite morphisms -/

/-- An immersion of schemes is separated and locally quasi-finite. -/
@[ega "IV 1.2.2" "(i), immersions"]
theorem isImmersion_le_isSeparated_inf_locallyQuasiFinite :
    (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u}) ≤
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite :
        MorphismProperty Scheme.{u}) := fun _ _ f hf ↦
  have : _root_.AlgebraicGeometry.IsImmersion f := hf
  ⟨inferInstance, inferInstance⟩

/-- A monomorphism of schemes which is locally of finite type is separated and locally
quasi-finite. -/
@[ega "I 5.5.1" "more general"]
theorem monomorphisms_inf_locallyOfFiniteType_le_isSeparated_inf_locallyQuasiFinite :
    (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType) ≤
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite :
        MorphismProperty Scheme.{u}) := fun _ _ f hf ↦
  have : Mono f := hf.1
  have : LocallyOfFiniteType f := hf.2
  ⟨inferInstance, inferInstance⟩

/-! ### Descending a property along a surjective étale chart -/

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Let `f : X ⟶ Y` be a *representable* morphism of presheaves on the big fppf site of `S`, let
`g : yoneda.obj U ⟶ Y` be a surjective étale chart of its target, and let `r` be a base change of
`f` along `g`. If `r` is representable with a property `Q` of morphisms of schemes which descends
along the surjective flat morphisms of finite presentation, then `f` itself is representable with
`Q`. -/
theorem presheaf_of_surjectiveEtaleChart_of_descendsAlong
    {Q : MorphismProperty Scheme.{u}} [Q.RespectsIso]
    [Q.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f)
    {U : BigFppfOver B S hS} {g : yoneda.obj U ⟶ Y}
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) g)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) g)
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {m : A ⟶ X} {r : A ⟶ yoneda.obj U}
    (sq : IsPullback m r f g)
    (hr : (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf r) :
    (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf f := by
  have : MorphismProperty.RespectsIso (Q.inverseImage (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.RespectsIso.inverseImage _ _
  refine MorphismProperty.relative_of_snd hf fun a k ↦ ?_
  have hwsq : IsPullback (hs.rep.fst k) (yoneda.map (hs.rep.snd k)) g k := hs.rep.isPullback k
  have hwsurj : Surjective ((BigFppfOver.toScheme B S hS).map (hs.rep.snd k)) :=
    hs.property_snd k
  have hwet : Etale ((BigFppfOver.toScheme B S hS).map (hs.rep.snd k)) :=
    he.property k (hs.rep.fst k) (hs.rep.snd k) hwsq
  have pbC : IsPullback (pullback.fst (hf.snd k) (hs.rep.snd k))
      (pullback.snd (hf.snd k) (hs.rep.snd k)) (hf.snd k) (hs.rep.snd k) :=
    IsPullback.of_hasPullback _ _
  have hbig : IsPullback (yoneda.map (pullback.fst (hf.snd k) (hs.rep.snd k)) ≫ hf.fst k)
      (yoneda.map (pullback.snd (hf.snd k) (hs.rep.snd k))) f
      (hs.rep.fst k ≫ g) := by
    rw [hwsq.w]
    exact (pbC.map yoneda).paste_horiz (hf.isPullback k)
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (Q := (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}))
    (pbC.map (BigFppfOver.toScheme B S hS)).flip
    (surjective_inf_flat_inf_locallyOfFinitePresentation_of_etale _ hwsurj hwet)
    (hr.property (hs.rep.fst k) _ _ (hbig.of_right' sq))

/-- Assume effective descent along surjective étale morphisms of the big fppf site of `S` at a
property `P`, and let `Q` be a property which descends along the surjective flat morphisms of
finite presentation. Let `f : X ⟶ Y` be a morphism of presheaves with `X` and `Y` sheaves and let
`g` be a surjective étale chart of `Y` along which the base change of `f` is representable with
both `P` and `Q`. Then `f` is representable with `Q`. -/
theorem presheaf_of_surjectiveEtaleChart_of_descent
    {P Q : MorphismProperty Scheme.{u}} [P.RespectsIso] [Q.RespectsIso]
    [Q.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS P)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hYs : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y) {f : X ⟶ Y}
    {U : BigFppfOver B S hS} {g : yoneda.obj U ⟶ Y}
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) g)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) g)
    (hVP : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f g))
    (hVQ : (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f g)) :
    (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf f :=
  presheaf_of_surjectiveEtaleChart_of_descendsAlong
    (presheaf_of_surjectiveEtaleChart hdesc hX hYs hs he hVP).rep hs he
    (IsPullback.of_hasPullback f g) hVQ

/-- Effective descent along surjective étale morphisms of the big fppf site of `S` at a
property `P` implies it at every property `Q ≤ P` which descends along the surjective flat
morphisms of finite presentation. -/
theorem isEffectiveDescentAlongSurjectiveEtale_of_le
    {P Q : MorphismProperty Scheme.{u}} [Q.RespectsIso]
    [Q.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS P) (hQP : Q ≤ P) :
    IsEffectiveDescentAlongSurjectiveEtale B S hS Q := by
  intro X Y f hX hY a c h q hqs hqe A m r sq hr
  have hrP : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf r :=
    MorphismProperty.relative_monotone
      (MorphismProperty.monotone_inverseImage (BigFppfOver.toScheme B S hS) hQP) _ hr
  have hP := hdesc f hX hY h q hqs hqe m r sq hrP
  have hqs' : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (yoneda.map q) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ q).2 hqs
  have hqe' : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (yoneda.map q) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ q).2 hqe
  exact presheaf_of_surjectiveEtaleChart_of_descendsAlong hP.rep hqs' hqe'
    (sq.of_right' (IsPullback.of_hasPullback f h)) hr

/-! ### The atlas clause -/

/-- Assume effective descent along surjective étale morphisms of the big fppf site of `S` for the
separated locally quasi-finite morphisms. Let `f : X ⟶ Y` be a morphism of presheaves with `X` and
`Y` sheaves, and let `g` be a surjective étale chart of `Y` along which the base change of `f` is a
separated, locally quasi-finite, surjective and étale morphism of schemes. Then `f` is
representable, surjective and étale. -/
theorem presheaf_surjective_and_etale_of_surjectiveEtaleChart
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS
      ((@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite :
        MorphismProperty Scheme.{u})))
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hYs : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y) {f : X ⟶ Y}
    {U : BigFppfOver B S hS} {g : yoneda.obj U ⟶ Y}
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) g)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) g)
    (hV : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite :
        MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f g))
    (hVs : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f g))
    (hVe : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f g)) :
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f :=
  have _hsurj := surjective_descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation.{u}
  have _hetale := etale_descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation.{u}
  have _hbc : MorphismProperty.IsStableUnderBaseChange
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite :
        MorphismProperty Scheme.{u}) := .inf
  have _hri : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite :
        MorphismProperty Scheme.{u}) := inferInstance
  have _hrie : MorphismProperty.RespectsIso (@Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  ⟨presheaf_of_surjectiveEtaleChart_of_descent hdesc hX hYs hs he hV hVs,
    presheaf_of_surjectiveEtaleChart_of_descent hdesc hX hYs hs he hV hVe⟩

end Space

end AlgebraicGeometry

end
