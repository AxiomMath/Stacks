module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReducedSingleton
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidualSpaceExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Monomorphisms
public import StacksFrontier.AlgebraicGeometry.Stacks.Gerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeResidualGerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopologyRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented

/-!
# The residual gerbe of a gerbe exists (Stacks 06RA)

**Stacks 06RA** says that an algebraic stack over `S` which is a gerbe (**Stacks 06QC**) has a
residual gerbe at every point of its space of points. Existence of the residual gerbe at a point
is, by **Stacks 06MU**, condition (1) of **Stacks 06MT**, which this library spells
`AlgebraicGeometry.Stack.HasSingletonPointMonomorphism`.

The source's argument has two steps. Let `f : 𝒳 ⟶ 𝒴` exhibit `𝒳` as a gerbe over a stack `𝒴`
representable by an algebraic space `F`, and let `x` be a point of `|𝒳|`. The residual gerbe of
`𝒴` at the image of `x` is the *residual space* of `F` at the corresponding point of `|F|`,
viewed as an algebraic stack; and the transport of condition (1) back along `f` is the existence
clause of **Stacks 0H24**,
`AlgebraicGeometry.Stack.hasSingletonPointMonomorphism_of_isGerbeOver`.

Residual spaces of algebraic spaces are **Stacks 06QZ**, supplied by
`AlgebraicGeometry.Space.exists_isResidualSpaceAt`; their defining property is
`AlgebraicGeometry.Space.IsResidualSpaceAt` (**Stacks 06R0**).

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isMonomorphism_of_mono_representingMap`: a
  1-morphism between algebraic stacks representable by algebraic spaces is a monomorphism
  (**Stacks 04ZW**) as soon as the induced morphism of representing presheaves is one.
* `AlgebraicGeometry.Stack.hasSingletonPointMonomorphism_of_isRepresentableByAlgebraicSpace`:
  condition (1) of **Stacks 06MT** holds at every point of an algebraic stack representable by
  an algebraic space.
* `AlgebraicGeometry.Stack.hasSingletonPointMonomorphism_of_isGerbe`: **Stacks 06RA**.

## Implementation notes

The residual space `g : Z ⟶ F` is turned into a 1-morphism of algebraic stacks by
`AlgebraicGeometry.Stack.exists_oneMorphism_representingMap_eq'`, the surjectivity half of
**Stacks 04SW**: it produces a 1-morphism whose induced morphism of representing presheaves is
`g` on the nose. Both things that have to be known about that 1-morphism — that it is a
monomorphism and what it does on points — are statements about the induced morphism, so nothing
else about it is needed and no explicit functor has to be written down.

The monomorphism step does **not** go through full faithfulness. The reverse implication of
**Stacks 04ZZ**, that a fully faithful 1-morphism is a monomorphism, is not in this library, so
the argument is the direct one: a monomorphism of algebraic stacks is a condition of
Section 04XB, and for represented source and target that condition is tested on the base change
of the induced morphism of representing presheaves along a scheme-valued point of the target,
which is a base change of a monomorphism of algebraic spaces.

That test is `AlgebraicGeometry.Stack.hasRelativeProperty_iff_prop_representingMap`, which
cannot be invoked here: `AlgebraicGeometry.Stack.HasRelativeProperty` takes locality of the
property at the target for the fppf precoverage as an instance argument, and for the
monomorphisms of algebraic spaces over `S` that is **Stacks 042D**, which this library does not
have — the same obstruction that makes
`AlgebraicGeometry.Stack.AlgebraicStacks.IsMonomorphism` the body of that predicate written out
rather than the predicate itself. Its backward implication is therefore transcribed, and uses
no locality: `AlgebraicGeometry.Stack.prop_algebraicSpaceMap_iff` asks only that the property
respect isomorphisms, and the identification of the two arrows is
`AlgebraicGeometry.Stack.arrowIsoRelocalizeFibrePullbackOfPullback`, taken in the form that
accepts the induced morphism as an argument with its defining equation.

Only existence is proved. The uniqueness of the residual gerbe asserted by Stacks 06MT, and its
identification with a 2-fibre product in Stacks 0H24, are not proved here; neither is the
uniqueness clause of Stacks 06QZ, which `AlgebraicGeometry.Space.exists_isResidualSpaceAt` also
omits.

## References

* [Stacks Project, Tag 042D](https://stacks.math.columbia.edu/tag/042D)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04ZW](https://stacks.math.columbia.edu/tag/04ZW)
* [Stacks Project, Tag 04ZZ](https://stacks.math.columbia.edu/tag/04ZZ)
* [Stacks Project, Tag 06MT](https://stacks.math.columbia.edu/tag/06MT)
* [Stacks Project, Tag 06MU](https://stacks.math.columbia.edu/tag/06MU)
* [Stacks Project, Tag 06QC](https://stacks.math.columbia.edu/tag/06QC)
* [Stacks Project, Tag 06QZ](https://stacks.math.columbia.edu/tag/06QZ)
* [Stacks Project, Tag 06R0](https://stacks.math.columbia.edu/tag/06R0)
* [Stacks Project, Tag 06RA](https://stacks.math.columbia.edu/tag/06RA)
* [Stacks Project, Tag 0H24](https://stacks.math.columbia.edu/tag/0H24)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A 1-morphism of represented algebraic stacks inducing a monomorphism of representing
presheaves is a monomorphism of algebraic stacks (Stacks 04ZW).**

Representability by algebraic spaces of the 1-morphism is **Stacks 02ZZ** for represented source
and target. The relative clause is the backward implication of the bridge of Section 04XB at the
monomorphisms, transcribed rather than invoked because the locality instance that
`AlgebraicGeometry.Stack.HasRelativeProperty` demands is Stacks 042D; see the implementation
notes of this module. Concretely: an algebraic space representing a base change of the
1-morphism along a scheme-valued point of the target has structural morphism isomorphic, as an
arrow over the representable algebraic space of that scheme, to the base change of the induced
morphism of representing presheaves, and a base change of a monomorphism is a monomorphism. -/
theorem AlgebraicStacks.isMonomorphism_of_mono_representingMap
    {𝒵 𝒴 : AlgebraicStacks.{u, w} B S hS} (a : 𝒵 ⟶ 𝒴)
    (Z F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hZ : IsAlgebraicSpace B S hS Z) (hF : IsAlgebraicSpace B S hS F)
    (eZ : StacksRepresentableCFG.EquivalenceOver 𝒵.val.val.p
      (presheafOfCategories (Z ⋙ typeToCat)).p)
    (eF : StacksRepresentableCFG.EquivalenceOver 𝒴.val.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (hmono : Mono (representingMap B S hS 𝒵.val 𝒴.val Z F eZ eF a.hom)) :
    AlgebraicStacks.IsMonomorphism B S hS a := by
  refine ⟨isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS a.hom
    ⟨Z, hZ, ⟨eZ⟩⟩ ⟨F, hF, ⟨eF⟩⟩, ?_⟩
  rintro U y hy T hT ⟨eT⟩
  refine (prop_algebraicSpaceMap_iff B S hS
    (MorphismProperty.monomorphisms (AlgebraicSpaces B S hS)) U T hT).mpr ?_
  refine ((MorphismProperty.monomorphisms (AlgebraicSpaces B S hS)).arrow_mk_iso_iff
    (arrowIsoRelocalizeFibrePullbackOfPullback B S hS U a.hom y hy Z F eZ eF _ rfl _ rfl
      (isAlgebraicSpace_pullback B S hS _ _ (isAlgebraicSpace_yoneda B S hS U) hZ hF)
      T eT hT)).mp ?_
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct B S hS
      (ObjectProperty.homMk
          (representingMap B S hS (schemeSlice B S hS U) 𝒴.val (yoneda.obj U) F
            (schemeSliceEquivalenceOver B S hS U) eF (schemeSliceMap B S hS U y hy)) :
        (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶ ⟨F, hF⟩)
      (ObjectProperty.homMk (representingMap B S hS 𝒵.val 𝒴.val Z F eZ eF a.hom) :
        (⟨Z, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨F, hF⟩)).flip
    ((Space.mono_hom_iff_mono B S hS _).1 hmono)

/-- **Condition (1) of Stacks 06MT holds at every point of an algebraic stack representable by an
algebraic space.**

The points of such a stack are the points of a representing algebraic space `F`
(`AlgebraicGeometry.Stack.bijective_spacePointMap_representing`), so the given point comes from a
point of `|F|`; a residual space `g : Z ⟶ F` at that point is a monomorphism from a one-point
algebraic space lying over it. The stack of `Z` (**Stacks 03YS**) and the 1-morphism inducing `g`
(**Stacks 04SW**) are then the witness: the 1-morphism is a monomorphism by
`AlgebraicGeometry.Stack.AlgebraicStacks.isMonomorphism_of_mono_representingMap`, and it has the
required behaviour on points because the representing charts of the two stacks identify the map
on points of a 1-morphism with the map on points of the induced morphism of presheaves. -/
theorem hasSingletonPointMonomorphism_of_isRepresentableByAlgebraicSpace
    (𝒴 : AlgebraicStacks.{u, w} B S hS)
    (h𝒴 : IsRepresentableByAlgebraicSpace B S hS 𝒴.val)
    (y : points B S hS 𝒴.val.val (Classical.choose 𝒴.property)) :
    HasSingletonPointMonomorphism B S hS 𝒴 y := by
  obtain ⟨F, hF, ⟨eF⟩⟩ := h𝒴
  obtain ⟨pF, hpF⟩ := (bijective_spacePointMap_representing B S hS F 𝒴.val eF).2 y
  obtain ⟨Z, g, hZ, hgmono, -, -, ⟨z₀⟩, hzsub, hzover⟩ :=
    Space.exists_isResidualSpaceAt B S hS hF pF
  set 𝒵 : AlgebraicStacks.{u, w} B S hS := algebraicSpaceStack.{u, w} B S hS Z hZ
  let eZ : StacksRepresentableCFG.EquivalenceOver 𝒵.val.val.p
    (presheafOfCategories (Z ⋙ typeToCat)).p := StacksRepresentableCFG.EquivalenceOver.refl _
  obtain ⟨a', ha'⟩ := exists_oneMorphism_representingMap_eq' B S hS 𝒵.val 𝒴.val Z F eZ eF g
  let a : 𝒵 ⟶ 𝒴 := Bicategory.InducedBicategory.mkHom a'
  have hamono : AlgebraicStacks.IsMonomorphism B S hS a :=
    AlgebraicStacks.isMonomorphism_of_mono_representingMap B S hS a Z F hZ hF eZ eF
      (by rwa [ha'])
  refine ⟨𝒵, a, hamono, spacePointMap B S hS Z 𝒵.val
    (representingEquivalence B S hS Z 𝒵.val eZ).functor z₀, ?_, ?_⟩
  · intro z'
    obtain ⟨v, rfl⟩ := (bijective_spacePointMap_representing B S hS Z 𝒵.val eZ).2 z'
    exact congrArg _ (hzsub.elim v z₀)
  · have hnat := spacePointMap_representing_naturality B S hS Z F 𝒵.val 𝒴.val eZ eF a' z₀
    rw [ha', hzover z₀, hpF] at hnat
    exact hnat.symm

/-- **Stacks 06RA.** An algebraic stack over `S` which is a gerbe (**Stacks 06QC**) satisfies
condition (1) of **Stacks 06MT** at every point of its space of points; that is, its residual
gerbe exists at every point.

A gerbe comes with a 1-morphism `f : 𝒳 ⟶ 𝒴` to an algebraic stack representable by an algebraic
space which makes `𝒳` a gerbe over `𝒴`. Condition (1) holds for `𝒴` at the image of the point by
`AlgebraicGeometry.Stack.hasSingletonPointMonomorphism_of_isRepresentableByAlgebraicSpace`, and
transports back along `f` by the existence clause of **Stacks 0H24**. -/
@[stacks 06RA]
theorem hasSingletonPointMonomorphism_of_isGerbe
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : AlgebraicStacks.IsGerbe B S hS 𝒳)
    (x : points B S hS 𝒳.val.val (Classical.choose 𝒳.property)) :
    HasSingletonPointMonomorphism B S hS 𝒳 x := by
  obtain ⟨𝒴, h𝒴, f, hf⟩ := h𝒳
  exact hasSingletonPointMonomorphism_of_isGerbeOver B S hS f hf x
    (hasSingletonPointMonomorphism_of_isRepresentableByAlgebraicSpace B S hS 𝒴 h𝒴 _)

end AlgebraicGeometry.Stack

end
