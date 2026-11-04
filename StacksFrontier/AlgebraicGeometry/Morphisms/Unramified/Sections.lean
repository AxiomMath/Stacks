module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties

/-!
# Sections of unramified and of separated morphisms

Let `g : X ⟶ S` be a morphism of schemes and let `s : S ⟶ X` be a section of it, that is a
morphism with `s ≫ g = 𝟙 S`. This file proves the three parts of Stacks Project, Tag 024T: such
a section is an open immersion as soon as `g` is unramified, a closed immersion as soon as `g` is
separated, and consequently has open and closed image as soon as `g` is both.

The source argument realises the section as a base change of the diagonal of `g`. The route taken
here is the equivalent cancellation property: a section composes with `g` to the identity, which
is both an open and a closed immersion, and both classes can be cancelled past an unramified,
respectively separated, second factor. For closed immersions that cancellation is Mathlib's
`AlgebraicGeometry.IsClosedImmersion.of_comp`; for open immersions it is supplied here as
`AlgebraicGeometry.isOpenImmersion_hasOfPostcompProperty`, whose proof is the source's own
observation that the diagonal of an unramified morphism is an open immersion.

## Main results

* `AlgebraicGeometry.isOpenImmersion_hasOfPostcompProperty` — an open immersion can be cancelled
  past an unramified morphism: if `f ≫ g` is an open immersion and `g` is locally of finite type
  and formally unramified, then `f` is an open immersion.
* `AlgebraicGeometry.isOpenImmersion_of_isSection` — Stacks Project, Tag 024T part (1): a
  section of an unramified morphism is an open immersion.
* `AlgebraicGeometry.isClosedImmersion_of_isSection_of_isSeparated` — Stacks Project, Tag 024T part
  (2): a
  section of a separated morphism is a closed immersion.
* `AlgebraicGeometry.isClopen_range_of_isSection` — Stacks Project, Tag 024T part (3): a section
  of an unramified separated morphism has open and closed image.

## Implementation notes

Stacks' "unramified" is locally of finite type together with formal unramifiedness, which is this
library's `AlgebraicGeometry.Unramified`; the translation is
`AlgebraicGeometry.unramified_iff_locallyOfFiniteType_and_formallyUnramified`. The cancellation
instance is stated in Mathlib's vocabulary, as the morphism property
`@LocallyOfFiniteType ⊓ @FormallyUnramified`, so that it matches the existing instance
`AlgebraicGeometry.Etale.instHasOfPostcompPropertyEtaleInfLocallyOfFiniteTypeFormallyUnramified`
of Mathlib and can be used without unfolding `Unramified`.

## References

* [Stacks Project, Tag 024T](https://stacks.math.columbia.edu/tag/024T)
* [Stacks Project, Tag 02GE](https://stacks.math.columbia.edu/tag/02GE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **An open immersion can be cancelled past an unramified morphism.** If `f ≫ g` is an open
immersion and `g` is unramified — locally of finite type and formally unramified — then `f` is an
open immersion.

This is the cancellation form of the observation underlying Stacks Project, Tag 024T: the
diagonal of an unramified morphism is an open immersion, by Stacks Project, Tag 02GE in the form
of Mathlib's `AlgebraicGeometry.isOpenImmersion_diagonal`, and for a property stable under base
change and multiplicative that is exactly the of-postcomposition property. -/
instance isOpenImmersion_hasOfPostcompProperty :
    MorphismProperty.HasOfPostcompProperty
      (@IsOpenImmersion : MorphismProperty Scheme.{u})
      (@LocallyOfFiniteType ⊓ @FormallyUnramified) := by
  have : MorphismProperty.IsStableUnderBaseChange
      ((@LocallyOfFiniteType ⊓ @FormallyUnramified) : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.inf
  rw [MorphismProperty.hasOfPostcompProperty_iff_le_diagonal]
  intro X Y f ⟨hft, hfu⟩
  exact inferInstanceAs <| IsOpenImmersion (pullback.diagonal f)

variable {X S : Scheme.{u}} (g : X ⟶ S) (s : S ⟶ X)

/-- **Stacks Project, Tag 024T, part (1).** A section of an unramified morphism is an open
immersion. -/
@[stacks 024T "part (1): a section of an unramified morphism is an open immersion"]
theorem isOpenImmersion_of_isSection (hs : s ≫ g = 𝟙 S) [Unramified g] :
    IsOpenImmersion s := by
  obtain ⟨hft, hfu⟩ :=
    (unramified_iff_locallyOfFiniteType_and_formallyUnramified g).mp inferInstance
  have hid : IsOpenImmersion (s ≫ g) := by rw [hs]; infer_instance
  exact MorphismProperty.of_postcomp (W := @IsOpenImmersion)
    (W' := (@LocallyOfFiniteType ⊓ @FormallyUnramified)) s g ⟨hft, hfu⟩ hid

/-- **Stacks Project, Tag 024T, part (2).** A section of a separated morphism is a closed
immersion. -/
@[stacks 024T "part (2): a section of a separated morphism is a closed immersion",
  ega "I 5.4.6",
  sga "3 VIB 5.6.3" "(i) ⇒ (ii)"]
theorem isClosedImmersion_of_isSection_of_isSeparated (hs : s ≫ g = 𝟙 S) [IsSeparated g] :
    IsClosedImmersion s := by
  have hid : IsClosedImmersion (s ≫ g) := by rw [hs]; infer_instance
  exact IsClosedImmersion.of_comp s g

/-- **Stacks Project, Tag 024T, part (3).** A section of an unramified separated morphism is open
and closed: its image is an open and closed subset of the source. -/
@[stacks 024T "part (3): a section of an unramified separated morphism is open and closed"]
theorem isClopen_range_of_isSection (hs : s ≫ g = 𝟙 S) [Unramified g] [IsSeparated g] :
    IsClopen (Set.range s.base) := by
  have hopen : IsOpenImmersion s := isOpenImmersion_of_isSection g s hs
  have hclosed : IsClosedImmersion s := isClosedImmersion_of_isSection_of_isSeparated g s hs
  exact ⟨hclosed.isClosedEmbedding.isClosed_range, hopen.base_open.isOpen_range⟩

end AlgebraicGeometry

end
