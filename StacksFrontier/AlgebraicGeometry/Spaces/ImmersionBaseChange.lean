module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms

/-!
# Base change and composition of immersions of algebraic spaces (Stacks 02YW, 02YV)

Let `S` be a scheme contained in a big fppf site `B`. An open immersion, a closed immersion
and an immersion of algebraic spaces over `S` are each stable under base change: if
`fst, snd, f, g` is a cartesian square of algebraic spaces over `S` and `f` is an immersion
of one of the three kinds, so is `snd`. Each of the three is also stable under composition.

## Main definitions

* `AlgebraicGeometry.Space.openImmersionProperty`,
  `AlgebraicGeometry.Space.closedImmersionProperty` and
  `AlgebraicGeometry.Space.immersionProperty`: the three immersion conditions of Stacks 02YU
  read as properties of morphisms in the category of algebraic spaces over `S`.

## Main results

* `AlgebraicGeometry.Space.isOpenImmersion_of_isPullback`,
  `AlgebraicGeometry.Space.isClosedImmersion_of_isPullback` and
  `AlgebraicGeometry.Space.isImmersion_of_isPullback`: **Stacks 02YW** for open immersions,
  closed immersions and immersions.
* `AlgebraicGeometry.Space.isOpenImmersion_comp`,
  `AlgebraicGeometry.Space.isClosedImmersion_comp` and
  `AlgebraicGeometry.Space.isImmersion_comp`: **Stacks 02YV**, the three parts.

## Implementation notes

Each of the three immersion conditions is, by Stacks 02YU, the *relative* property
(`CategoryTheory.MorphismProperty.presheaf`) attached to the inverse image along
`AlgebraicGeometry.BigFppfOver.toScheme` of the corresponding property of morphisms of
schemes. Mathlib's `CategoryTheory.MorphismProperty.relative_isStableUnderBaseChange` says
that a relative property is stable under base change with no hypothesis whatsoever on the
property it is built from, so the entire content of Stacks 02YW here is the passage from a
cartesian square in the full subcategory of algebraic spaces to the underlying cartesian
square of presheaves. That passage is
`AlgebraicGeometry.AlgebraicSpaces.isPullback_hom`: the category of algebraic spaces has
fibre products computed in presheaves (Stacks 02X2,
`AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct`), and any two cartesian squares
on the same cospan have isomorphic apices.

The three results are stated for an arbitrary cartesian square rather than for the chosen
fibre product, so that they apply to any model of a base change; this is also the shape in
which the three `CategoryTheory.MorphismProperty.IsStableUnderBaseChange` instances below are
phrased, and those instances are one of the two hypotheses of Stacks 03YK
(`AlgebraicGeometry.Stack.HasRelativeProperty`).

Stacks 02YV is likewise `CategoryTheory.MorphismProperty.relative_isStableUnderComposition`
pulled back along `AlgebraicGeometry.BigFppfOver.toScheme`, over Mathlib's multiplicativity of
the three immersion properties of schemes. The two intermediate instances are supplied by hand
rather than looked up: for closed immersions and immersions Mathlib registers only
`CategoryTheory.MorphismProperty.IsMultiplicative`, whose projection to
`CategoryTheory.MorphismProperty.IsStableUnderComposition` is not an instance, and
`CategoryTheory.MorphismProperty.IsStableUnderComposition.inverseImage` is then applied
explicitly because instance search does not solve its universe metavariables here. The three
resulting `CategoryTheory.MorphismProperty.IsStableUnderComposition` instances are the third
hypothesis of `AlgebraicGeometry.Stack.hasRelativeProperty_comp` (Stacks 045B), which is what
Stacks 0502 needs.

## References

* [Stacks Project, Tag 02YW](https://stacks.math.columbia.edu/tag/02YW)
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 02YV](https://stacks.math.columbia.edu/tag/02YV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A property of schemes pulled back along `toScheme` and made relative is stable under base
change of algebraic spaces. -/
private theorem presheaf_inverseImage_snd (P : MorphismProperty Scheme.{u})
    {F G H Q : AlgebraicSpaces B S hS} {f : F ⟶ H} {g : G ⟶ H} {fst : Q ⟶ F} {snd : Q ⟶ G}
    (sq : IsPullback fst snd f g)
    (hf : (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf f.hom) :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf snd.hom :=
  (MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS))).of_isPullback
    (AlgebraicSpaces.isPullback_hom B S hS sq) hf

/-- A multiplicative property of schemes pulled back along `toScheme` and made relative is stable
under composition of presheaves on the big fppf site. -/
private theorem presheaf_inverseImage_comp (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative]
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G} {g : G ⟶ H}
    (hf : (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf f)
    (hg : (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf g) :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf (f ≫ g) :=
  have _hP : P.IsStableUnderComposition :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have _h :
      (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage (P := P) (BigFppfOver.toScheme B S hS)
  MorphismProperty.comp_mem _ f g hf hg

/-- **Stacks 02YW** for closed immersions: a base change of a closed immersion of algebraic
spaces over `S` is a closed immersion. -/
@[stacks 02YW "closed immersions", ega "I 4.3.2" "closed immersion"]
theorem isClosedImmersion_of_isPullback {F G H P : AlgebraicSpaces B S hS}
    {f : F ⟶ H} {g : G ⟶ H} {fst : P ⟶ F} {snd : P ⟶ G} (sq : IsPullback fst snd f g)
    (hf : IsClosedImmersion B S hS f.hom) :
    IsClosedImmersion B S hS snd.hom :=
  presheaf_inverseImage_snd B S hS _ sq hf

/-- **Stacks 02YW** for open immersions: a base change of an open immersion of algebraic
spaces over `S` is an open immersion. -/
@[stacks 02YW "open immersions", ega "I 4.3.2" "open immersion"]
theorem isOpenImmersion_of_isPullback {F G H P : AlgebraicSpaces B S hS}
    {f : F ⟶ H} {g : G ⟶ H} {fst : P ⟶ F} {snd : P ⟶ G} (sq : IsPullback fst snd f g)
    (hf : IsOpenImmersion B S hS f.hom) :
    IsOpenImmersion B S hS snd.hom :=
  presheaf_inverseImage_snd B S hS _ sq hf

/-- **Stacks 02YW** for immersions: a base change of an immersion of algebraic spaces over
`S` is an immersion. -/
@[stacks 02YW "immersions", ega "I 4.3.2" "immersion"]
theorem isImmersion_of_isPullback {F G H P : AlgebraicSpaces B S hS}
    {f : F ⟶ H} {g : G ⟶ H} {fst : P ⟶ F} {snd : P ⟶ G} (sq : IsPullback fst snd f g)
    (hf : IsImmersion B S hS f.hom) :
    IsImmersion B S hS snd.hom :=
  presheaf_inverseImage_snd B S hS _ sq hf

/-- Being an open immersion (**Stacks 02YU**, part (1)), as a property of morphisms in the
category of algebraic spaces over `S`. -/
abbrev openImmersionProperty : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ f => IsOpenImmersion B S hS f.hom

/-- Being a closed immersion (**Stacks 02YU**, part (3)), as a property of morphisms in the
category of algebraic spaces over `S`. -/
abbrev closedImmersionProperty : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ f => IsClosedImmersion B S hS f.hom

/-- Being an immersion (**Stacks 02YU**, part (5)), as a property of morphisms in the
category of algebraic spaces over `S`. -/
abbrev immersionProperty : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ f => IsImmersion B S hS f.hom

/-- The class of open immersions of algebraic spaces over `S` is stable under base change. -/
instance : (openImmersionProperty B S hS).IsStableUnderBaseChange where
  of_isPullback sq hf := isOpenImmersion_of_isPullback B S hS sq hf

/-- The class of closed immersions of algebraic spaces over `S` is stable under base change. -/
instance : (closedImmersionProperty B S hS).IsStableUnderBaseChange where
  of_isPullback sq hf := isClosedImmersion_of_isPullback B S hS sq hf

/-- The class of immersions of algebraic spaces over `S` is stable under base change. -/
instance : (immersionProperty B S hS).IsStableUnderBaseChange where
  of_isPullback sq hf := isImmersion_of_isPullback B S hS sq hf

/-- **Stacks 02YV**, part (1): a composite of open immersions of algebraic spaces over `S` is
an open immersion. -/
@[stacks 02YV "part (1): open immersions", ega "I 4.2.5" "open immersions"]
theorem isOpenImmersion_comp {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (g : G ⟶ H)
    (hf : IsOpenImmersion B S hS f) (hg : IsOpenImmersion B S hS g) :
    IsOpenImmersion B S hS (f ≫ g) :=
  presheaf_inverseImage_comp B S hS _ hf hg

/-- **Stacks 02YV**, part (2): a composite of closed immersions of algebraic spaces over `S` is
a closed immersion. -/
@[stacks 02YV "part (2): closed immersions",
  ega "I 4.2.5" "closed immersions",
  ega "I 4.1.6" "closed subprescheme"]
theorem isClosedImmersion_comp {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (g : G ⟶ H)
    (hf : IsClosedImmersion B S hS f) (hg : IsClosedImmersion B S hS g) :
    IsClosedImmersion B S hS (f ≫ g) :=
  presheaf_inverseImage_comp B S hS _ hf hg

/-- **Stacks 02YV**, part (3): a composite of immersions of algebraic spaces over `S` is an
immersion. -/
@[stacks 02YV "part (3): immersions", ega "I 4.2.5" "immersions", ega "I 4.1.6" "subprescheme case"]
theorem isImmersion_comp {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (g : G ⟶ H)
    (hf : IsImmersion B S hS f) (hg : IsImmersion B S hS g) :
    IsImmersion B S hS (f ≫ g) :=
  presheaf_inverseImage_comp B S hS _ hf hg

/-- The class of open immersions of algebraic spaces over `S` is stable under composition. -/
instance : (openImmersionProperty B S hS).IsStableUnderComposition where
  comp_mem f g hf hg := isOpenImmersion_comp B S hS f.hom g.hom hf hg

/-- The class of closed immersions of algebraic spaces over `S` is stable under composition. -/
instance : (closedImmersionProperty B S hS).IsStableUnderComposition where
  comp_mem f g hf hg := isClosedImmersion_comp B S hS f.hom g.hom hf hg

/-- The class of immersions of algebraic spaces over `S` is stable under composition. -/
instance : (immersionProperty B S hS).IsStableUnderComposition where
  comp_mem f g hf hg := isImmersion_comp B S hS f.hom g.hom hf hg

end Space

end AlgebraicGeometry

end
