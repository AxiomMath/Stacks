module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties

/-!
# Composition of proper morphisms of algebraic spaces (Stacks 04XY)

Let `S` be a scheme contained in a big fppf site `B`. Properness of a morphism of algebraic
spaces over `S` is the conjunction of separatedness, being of finite type and universal
closedness (**Stacks 03ZM**), and this file proves that properness is stable under composition
by proving two of the conjuncts and pairing them with the third, which is already available.

The separated and locally separated cases of **Stacks 03KQ** come first. Those two separation
axioms of Stacks 03HL ask the relative diagonal to be a closed immersion, respectively an
immersion, of the presheaves on the big fppf site of `S` on which it lives, so each is the
`CategoryTheory.MorphismProperty.diagonal` of a property of morphisms of presheaves which is
stable under base change and under composition — and Mathlib makes such a diagonal stable under
composition outright. No algebraicity hypothesis enters, so both hold for morphisms of
presheaves; the source states them for algebraic spaces. With the quasi-separated case already
proved in `StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedComposition`, all three separation
axioms of Stacks 03HL that this library states are stable under composition.

The finite-type case of **Stacks 03XG** is then the locally-of-finite-type case, already proved, paired
with **Stacks 03HG** for quasi-compactness, and **Stacks 04XY** is the triple of the separated
case of Stacks 03KQ, the finite-type case of Stacks 03XG and the universally closed case of
**Stacks 03IU**.

Finally the four remaining `CategoryTheory.MorphismProperty.IsStableUnderComposition` instances
on the six properties of
`StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties` are registered. With them
`AlgebraicGeometry.Space.properProperty` carries two of the three instance arguments that
**Stacks 045B** asks of a property of morphisms of algebraic spaces, the missing one being
locality at the target for the fppf precoverage (**Stacks 0422**).

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.properProperty_isStableUnderComposition`: Stacks 04XY registered at
  `AlgebraicGeometry.Space.properProperty`, together with the three instances it is the meet of.

## Implementation notes

The source's proof of Stacks 03KQ factors the relative diagonal of `f ≫ g` as
`X ⟶ X ×_Y X ⟶ X ×_Z X` and quotes Stacks 03KN for the second factor. Mathlib's
`CategoryTheory.MorphismProperty.diagonal_isStableUnderComposition` is that argument for an
abstract property, and here — unlike in the quasi-separated case, where Stacks 03HG binds an
algebraicity hypothesis and the instance is therefore unavailable — it applies: being a closed
immersion and being an immersion are stable under composition and under base change as properties
of morphisms of presheaves, with no hypothesis on the objects. So neither case needs the closed
immersion, respectively immersion, case of Stacks 03KN at all.

The three algebraicity hypotheses the source carries are dropped from the two cases of Stacks
03KQ, which is the arity adaptation already recorded for Stacks 04WP: the library's predicates do
not take them and dropping an unused hypothesis strengthens a theorem. The finite-type case of
Stacks 03XG and Stacks 04XY keep two of the three, `hG` and `hH`, because the quantifiers of
`AlgebraicGeometry.Space.IsQuasiCompact` and
`AlgebraicGeometry.Space.UniversallyClosed` demand algebraicity of the fibre products they test.

The four instances are stated at the packaged properties rather than at the longhand predicates
because `CategoryTheory.MorphismProperty.IsStableUnderComposition.inf` has no longhand analogue:
`AlgebraicGeometry.Space.finiteTypeProperty` and `.properProperty` are definitionally meets, by
`AlgebraicGeometry.Space.finiteTypeProperty_eq_inf` and `.properProperty_eq_inf`, and the two
derived instances are those equalities followed by that lemma.

## References

* [Stacks Project, Tag 03KQ](https://stacks.math.columbia.edu/tag/03KQ)
* [Stacks Project, Tag 03XG](https://stacks.math.columbia.edu/tag/03XG)
* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
* [Stacks Project, Tag 04XY](https://stacks.math.columbia.edu/tag/04XY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Stability of the immersion properties, feeding Stacks 03XG and Stacks 04XY -/

/-- Being a closed immersion of schemes is stable under composition. -/
theorem closedImmersion_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) :=
  ⟨fun _f _g hf hg => have := hf; have := hg; inferInstance⟩

/-- Being an immersion of schemes is stable under composition. -/
theorem immersion_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition
      (@AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u}) :=
  ⟨fun _f _g hf hg => have := hf; have := hg; inferInstance⟩

/-- Being a closed immersion of algebraic spaces over `S` is stable under composition, as being
a closed immersion of schemes is. This is the companion of
`AlgebraicGeometry.Space.isClosedImmersion_isStableUnderBaseChange`. -/
theorem isClosedImmersion_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) :=
  have _ := inverseImage_isStableUnderComposition B S hS
    closedImmersion_isStableUnderComposition.{u}
  MorphismProperty.relative_isStableUnderComposition _

/-- Being an immersion of algebraic spaces over `S` is stable under composition, as being an
immersion of schemes is. -/
theorem isImmersion_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) :=
  have _ := inverseImage_isStableUnderComposition B S hS
    immersion_isStableUnderComposition.{u}
  MorphismProperty.relative_isStableUnderComposition _

/-- Being an immersion of algebraic spaces over `S` is stable under base change, as being an
immersion of schemes is. -/
theorem isImmersion_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) :=
  MorphismProperty.relative_isStableUnderBaseChange _

/-! ### Stacks 03XG and Stacks 04XY -/



/-! ### The four missing composition instances -/

/-- Separatedness of a morphism of algebraic spaces over `S` is stable under composition. This is
`AlgebraicGeometry.Space.isSeparated_comp` registered at
`AlgebraicGeometry.Space.separatedProperty`. -/
instance separatedProperty_isStableUnderComposition :
    (separatedProperty B S hS).IsStableUnderComposition where
  comp_mem f g hf hg := isSeparated_comp B S hS f.hom g.hom hf hg

/-- Being locally of finite type is stable under composition as a property of morphisms of
algebraic spaces over `S`. This is
`AlgebraicGeometry.Space.isLocallyOfFiniteType_comp` (**Stacks 03XG**, the
locally-of-finite-type case) with the algebraicity of the three objects supplied by the objects
themselves. -/
instance locallyOfFiniteTypeProperty_isStableUnderComposition :
    (locallyOfFiniteTypeProperty B S hS).IsStableUnderComposition where
  comp_mem {X Y Z} f g hf hg :=
    isLocallyOfFiniteType_comp B S hS X.property Y.property Z.property f.hom g.hom hf hg

/-- Being of finite type is stable under composition as a property of morphisms of algebraic
spaces over `S`. Being of finite type is definitionally the meet of being locally of finite type
and being quasi-compact, by `AlgebraicGeometry.Space.finiteTypeProperty_eq_inf`, and both are
stable under composition. -/
instance finiteTypeProperty_isStableUnderComposition :
    (finiteTypeProperty B S hS).IsStableUnderComposition := by
  rw [finiteTypeProperty_eq_inf]
  exact MorphismProperty.IsStableUnderComposition.inf

/-- **Stacks 04XY** registered at `AlgebraicGeometry.Space.properProperty`: properness is stable
under composition as a property of morphisms of algebraic spaces over `S`.

Properness is definitionally the meet of separatedness, finite type and universal closedness, by
`AlgebraicGeometry.Space.properProperty_eq_inf`, and all three are stable under composition —
separatedness by `AlgebraicGeometry.Space.isSeparated_comp`, finite type by the instance
above and universal closedness by
`AlgebraicGeometry.Space.universallyClosedProperty_isStableUnderComposition`. -/
instance properProperty_isStableUnderComposition :
    (properProperty B S hS).IsStableUnderComposition := by
  rw [properProperty_eq_inf]
  exact MorphismProperty.IsStableUnderComposition.inf

end AlgebraicGeometry.Space

end
