module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace

/-!
# The atlas of an algebraic space is an fppf covering of it

Let `S` be a scheme contained in a big fppf site `B`. By definition (Stacks 025Y) an algebraic
space `F` over `S` admits a *scheme atlas*: an object `T` of the big fppf site of `S` and a
morphism `a : yoneda.obj T ⟶ F` which is surjective and étale after every representable base
change. This file shows that the one-member family `a` is an fppf covering of `F` in the sense
of Stacks 03Y8, hence a covering family of the fppf precoverage of Stacks 03YH on the category
of algebraic spaces over `S`.

This is the bridge between a property of morphisms of algebraic spaces and its test on
*scheme*-valued points: a property which is local on the base for the fppf topology, that is
`CategoryTheory.MorphismProperty.IsLocalAtTarget` for
`AlgebraicGeometry.Space.Topology.fppf.precoverage`, can be checked on the base change of the
morphism to a scheme atlas of its target. That is the step every argument of the shape
"`P` holds over every scheme, hence `P` holds over every algebraic space" turns on.

## Main results

* `AlgebraicGeometry.Space.etale_of_etaleChart_square`: in a commuting square of étale charts
  of an étale morphism out of a representable presheaf, the underlying morphism of schemes is
  étale.
* `AlgebraicGeometry.Space.isFlat_atlas` and
  `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_atlas`: a scheme atlas is flat and
  locally of finite presentation, in the sense of Stacks 03ML and 03XP.
* `AlgebraicGeometry.Space.isFppfCovering_atlas`: a surjective étale scheme atlas is an fppf
  covering in the sense of Stacks 03Y8.
* `AlgebraicGeometry.Space.ofArrows_atlas_mem_fppf_precoverage` and
  `AlgebraicGeometry.Space.exists_mem_fppf_precoverage_yoneda`: that covering read as a member
  of the fppf precoverage of Stacks 03YH, and the resulting statement that every algebraic
  space over `S` is covered, in the precoverage, by a single representable one.
* `AlgebraicGeometry.Space.prop_iff_pullbackSnd_atlas`: a property local on the base for the
  fppf topology may be tested on the base change to a scheme atlas of the target.
* `AlgebraicGeometry.Space.exists_etale_scheme_chart_through_point`: an étale morphism out of
  an algebraic space over `S` has an étale scheme chart through every point of its source, and
  the composite of the chart with the morphism is again étale.

## Implementation notes

The three conditions of Stacks 03Y8 are proved separately because they come from different
places. Flatness and local finite presentation are `HoldsOnEveryEtaleChart` of the
corresponding property of morphisms of schemes, so they are statements about the morphism of
schemes underlying a commuting square of étale charts; both follow from étaleness of that
morphism, which is `AlgebraicGeometry.Space.etale_of_etaleChart_square`: the composite of the
chart of the source with the atlas is étale by Stacks 03FT, hence so is the other side of the
square, and a morphism between two presheaves étale over a common algebraic space is étale by
Stacks 03FV. Joint surjectivity on the point sets of Stacks 03BU is, for a single morphism out
of a representable presheaf, exactly Stacks 03H5.

The index universe of a covering family of
`AlgebraicGeometry.Space.Topology.precoverage` is independent of the universe of the site, so
the one-member family is indexed by `PUnit` in a free universe; a consumer instantiates it at
whatever universe the `CategoryTheory.MorphismProperty.IsLocalAtTarget` hypothesis it has in
hand was stated at.

## References

* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
* [Stacks Project, Tag 03Y8](https://stacks.math.columbia.edu/tag/03Y8)
* [Stacks Project, Tag 03YH](https://stacks.math.columbia.edu/tag/03YH)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- In a commuting square of étale charts over a morphism `h` of the site, with an étale
morphism `a` out of a representable presheaf on the right, the morphism of schemes underlying
`h` is étale.

The composite of the chart of the source with `a` is étale by Stacks 03FT, so both `h ≫ b` and
`b` are étale; Stacks 03FV then makes `h` étale. -/
theorem etale_of_etaleChart_square
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {T : BigFppfOver B S hS} {a : yoneda.obj T ⟶ F} (ha : IsEtale B S hS a)
    {U V : BigFppfOver B S hS} {a' : yoneda.obj U ⟶ yoneda.obj T} {b : yoneda.obj V ⟶ F}
    {h : U ⟶ V}
    (ha' : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a')
    (hb : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hsq : yoneda.map h ≫ b = a' ≫ a) :
    AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map h) := by
  have ha'' : IsEtale B S hS a' := (isEtale_iff_presheaf_of_yoneda B S hS a').2 ha'
  have hb' : IsEtale B S hS b := (isEtale_iff_presheaf_of_yoneda B S hS b).2 hb
  have hcomp : IsEtale B S hS (yoneda.map h ≫ b) := by
    rw [hsq]
    exact isEtale_comp B S hS ha'' ha
  have hmap : IsEtale B S hS (yoneda.map h) :=
    isEtale_of_isEtale_over B S hS (isAlgebraicSpace_yoneda B S hS U)
      (isAlgebraicSpace_yoneda B S hS V) hF (yoneda.map h) (yoneda.map h ≫ b) b hcomp hb' rfl
  exact (presheaf_yoneda_map_etale_iff B S hS h).1
    ((isEtale_iff_presheaf_of_yoneda B S hS (yoneda.map h)).1 hmap)

/-- A property of morphisms of schemes implied by étaleness holds on every étale chart of an
étale morphism out of a representable presheaf. -/
theorem holdsOnEveryEtaleChart_of_isEtale
    (Q : MorphismProperty Scheme.{u})
    (hQ : ∀ {X Y : Scheme.{u}} (g : X ⟶ Y), AlgebraicGeometry.Etale g → Q g)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {T : BigFppfOver B S hS} {a : yoneda.obj T ⟶ F} (ha : IsEtale B S hS a) :
    HoldsOnEveryEtaleChart B S hS Q a := fun _ _ _ _ _ ha' hb hsq =>
  hQ _ (etale_of_etaleChart_square B S hS hF ha ha' hb hsq)

/-- A scheme atlas of an algebraic space is flat in the sense of Stacks 03ML: étale morphisms
of schemes are flat. -/
theorem isFlat_atlas
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {T : BigFppfOver B S hS} {a : yoneda.obj T ⟶ F} (ha : IsEtale B S hS a) :
    IsFlat B S hS a :=
  holdsOnEveryEtaleChart_of_isEtale B S hS
    (@AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u})
    (fun _ hg => have := hg; inferInstance) hF ha

/-- A scheme atlas of an algebraic space is locally of finite presentation in the sense of
Stacks 03XP: étale morphisms of schemes are. -/
theorem isLocallyOfFinitePresentation_atlas
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {T : BigFppfOver B S hS} {a : yoneda.obj T ⟶ F} (ha : IsEtale B S hS a) :
    IsLocallyOfFinitePresentation B S hS a :=
  holdsOnEveryEtaleChart_of_isEtale B S hS
    (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
    (fun _ hg => have := hg; inferInstance) hF ha

/-- A scheme atlas of an algebraic space over `S` which is surjective and étale after every
representable base change is an fppf covering of it in the sense of Stacks 03Y8, as a family
indexed by a one-element type. -/
theorem isFppfCovering_atlas
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {T : BigFppfOver B S hS} {a : yoneda.obj T ⟶ F}
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    IsFppfCovering B S hS (fun _ : PUnit.{v + 1} => yoneda.obj T) (fun _ => a) := by
  have ha : IsEtale B S hS a := (isEtale_iff_presheaf_of_yoneda B S hS a).2 hetale
  refine ⟨hF, fun _ => isAlgebraicSpace_yoneda B S hS T, fun _ => isFlat_atlas B S hS hF ha,
    fun _ => isLocallyOfFinitePresentation_atlas B S hS hF ha, ?_⟩
  have hpoints : Function.Surjective (pointsMap B S hS (yoneda.obj T) a) :=
    (surjective_iff_surjective_pointsMap B S hS F hF T a).1 hsurj
  simp only [Set.iUnion_const]
  exact hpoints.range_eq

/-- The one-member presieve of a surjective étale scheme atlas of an algebraic space is a
covering family of the fppf precoverage of Stacks 03YH on the algebraic spaces over `S`. -/
theorem ofArrows_atlas_mem_fppf_precoverage
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {T : BigFppfOver B S hS} {a : yoneda.obj T ⟶ F}
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    Presieve.ofArrows
        (fun _ : PUnit.{v + 1} =>
          (schemeSpace T : AlgebraicSpaces B S hS))
        (fun _ => (ObjectProperty.homMk a : schemeSpace T ⟶ ⟨F, hF⟩)) ∈
      (Topology.fppf.precoverage.{u, v} B S hS).coverings ⟨F, hF⟩ :=
  ⟨PUnit.{v + 1}, fun _ => ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩,
    fun _ => ObjectProperty.homMk a, rfl,
    hF, fun _ => isAlgebraicSpace_yoneda B S hS T,
    isFppfCovering_atlas.{u, v} B S hS hF hsurj hetale⟩

/-- Every algebraic space over `S` is covered, in the fppf precoverage of Stacks 03YH, by a
single representable algebraic space: its atlas, which exists by Stacks 025Y. -/
theorem exists_mem_fppf_precoverage_yoneda (X : AlgebraicSpaces B S hS) :
    ∃ (T : BigFppfOver B S hS) (a : (schemeSpace T : AlgebraicSpaces B S hS) ⟶ X),
      Presieve.ofArrows (fun _ : PUnit.{v + 1} =>
          (schemeSpace T : AlgebraicSpaces B S hS))
        (fun _ => a) ∈ (Topology.fppf.precoverage.{u, v} B S hS).coverings X := by
  obtain ⟨T, a, hsurj, hetale⟩ := X.property.exists_atlas
  exact ⟨T, ObjectProperty.homMk a,
    ofArrows_atlas_mem_fppf_precoverage.{u, v} B S hS X.property hsurj hetale⟩

/-- A property of morphisms of algebraic spaces over `S` which is local on the base for the
fppf topology may be tested on the base change of the morphism to a scheme atlas of its
target. This is the form in which a statement proved over every scheme is transported to a
statement over every algebraic space. -/
theorem prop_iff_pullbackSnd_atlas
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsLocalAtTarget (Topology.fppf.precoverage.{u, v} B S hS)]
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {T : BigFppfOver B S hS} {a : yoneda.obj T ⟶ Y.obj}
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    P f ↔ P (Limits.pullback.snd f (ObjectProperty.homMk a :
      (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS) ⟶ Y)) := by
  have key := MorphismProperty.IsLocalAtTarget.iff_of_forall_pullbackSnd
    (P := P) (K := Topology.fppf.precoverage.{u, v} B S hS)
    (ofArrows_atlas_mem_fppf_precoverage.{u, v} B S hS Y.property hsurj hetale) (f := f)
  refine key.trans
    ⟨fun h => h (ObjectProperty.homMk a :
        (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS) ⟶ Y)
      (Presieve.ofArrows.mk PUnit.unit), ?_⟩
  intro h U g hpb hg
  cases hg
  exact h

/-! ### An étale scheme chart through a point -/

/-- **An étale scheme chart through a point.** An étale morphism `f : X ⟶ Y` whose source is an
algebraic space over `S` admits, through every point `x` of `X`, an étale scheme chart
`a : yoneda.obj U ⟶ X` together with a point `u` of that chart lying over `x`; the composite
`a ≫ f` is again étale, and it carries `u` to the image of `x` under `f`.

A surjective étale atlas of `X` is such a chart: it is surjective on the point sets of
Tag 03BU by Tag 03H5, so some point of it lies over `x`, and the composite of an étale chart
with an étale morphism is étale by Tag 03FT. -/
theorem exists_etale_scheme_chart_through_point
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (f : X ⟶ Y) (hf : IsEtale B S hS f) (x : points B S hS X) :
    ∃ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (u : points B S hS (yoneda.obj U)),
      IsEtale B S hS a ∧
      pointsMap B S hS (yoneda.obj U) a u = x ∧
      IsEtale B S hS (a ≫ f) ∧
      pointsMap B S hS (yoneda.obj U) (a ≫ f) u = pointsMap B S hS X f x := by
  obtain ⟨U, a, ha_surjective, ha_etale⟩ := hX.exists_atlas
  obtain ⟨u, hu⟩ :=
    (surjective_iff_surjective_pointsMap B S hS X hX U a).mp ha_surjective x
  refine ⟨U, a, u, (isEtale_iff_presheaf_of_yoneda B S hS a).2 ha_etale, hu,
    (isEtale_iff_presheaf_of_yoneda B S hS (a ≫ f)).2 (hf U a ha_etale), ?_⟩
  simp [pointsMap_comp, hu]

end AlgebraicGeometry.Space

end
