module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated

/-!
# Separated morphisms of algebraic spaces are locally separated and quasi-separated

A separated morphism of algebraic spaces over a scheme is both locally separated and
quasi-separated, and so is a separated algebraic space. We also show that a closed immersion of
algebraic spaces is an immersion.

## Main results

* `AlgebraicGeometry.Space.isClosedImmersion_le_isImmersion`: closed immersions of schemes are
  immersions, as an inequality of morphism properties.
* `AlgebraicGeometry.Space.isImmersion_of_isClosedImmersion`: a closed immersion of algebraic
  spaces is an immersion.
* `AlgebraicGeometry.Space.isLocallySeparated_of_isSeparated`: a separated morphism of
  algebraic spaces is locally separated.
* `AlgebraicGeometry.Space.isQuasiSeparated_of_isSeparated`: a separated morphism of
  algebraic spaces is quasi-separated.
* `AlgebraicGeometry.Space.isAbsolutelyLocallySeparated_of_isAbsolutelySeparated` and
  `AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isAbsolutelySeparated`: a separated
  algebraic space is locally separated and quasi-separated.

## References

* [Stacks Project, Tag 03DY](https://stacks.math.columbia.edu/tag/03DY)
* [Stacks Project, Tag 03KK](https://stacks.math.columbia.edu/tag/03KK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### A closed immersion of algebraic spaces is an immersion -/

/-- A closed immersion of schemes is an immersion, as an inequality of morphism
properties. -/
theorem isClosedImmersion_le_isImmersion :
    (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) ≤
      (@AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u}) :=
  fun _ _ f (_ : AlgebraicGeometry.IsClosedImmersion f) ↦ inferInstance

/-- A closed immersion of algebraic spaces over `S` is an immersion. -/
theorem isImmersion_of_isClosedImmersion
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G} (hf : IsClosedImmersion B S hS f) :
    IsImmersion B S hS f :=
  MorphismProperty.relative_monotone
    (MorphismProperty.monotone_inverseImage _ isClosedImmersion_le_isImmersion) _ hf

/-! ### Separated morphisms are locally separated and quasi-separated -/

/-- A separated morphism of algebraic spaces over `S` is locally separated. -/
@[stacks 03KK "locally separated"]
theorem isLocallySeparated_of_isSeparated
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G} (hf : IsSeparated B S hS f) :
    IsLocallySeparated B S hS f :=
  isImmersion_of_isClosedImmersion B S hS hf

/-- A separated morphism of algebraic spaces over `S` is quasi-separated. -/
@[stacks 03KK "quasi-separated"]
theorem isQuasiSeparated_of_isSeparated
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G} (hf : IsSeparated B S hS f) :
    IsQuasiSeparated B S hS f :=
  isQuasiCompact_of_isClosedImmersion' B S hS hf

/-! ### Separated algebraic spaces are locally separated and quasi-separated -/

/-- A closed immersion of schemes is quasi-compact, as an inequality of morphism
properties. -/
@[ega "I 6.6.4"]
private theorem isClosedImmersion_le_quasiCompact :
    (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) ≤
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u}) :=
  fun _ _ f (_ : AlgebraicGeometry.IsClosedImmersion f) ↦ inferInstance

/-- A separated algebraic space is locally separated. -/
@[stacks 03DY "part (1): locally separated"]
theorem isAbsolutelyLocallySeparated_of_isAbsolutelySeparated
    (hZ : B.Contains (⊤_ Scheme.{u})) (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAbsolutelySeparated B S hS hZ F) :
    IsAbsolutelyLocallySeparated B S hS hZ F :=
  isImmersion_of_isClosedImmersion B (⊤_ Scheme.{u}) hZ hF

/-- A separated algebraic space is quasi-separated. -/
@[stacks 03DY "part (1): quasi-separated"]
theorem isAbsolutelyQuasiSeparated_of_isAbsolutelySeparated
    (hZ : B.Contains (⊤_ Scheme.{u})) (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAbsolutelySeparated B S hS hZ F) :
    IsAbsolutelyQuasiSeparated B S hS hZ F :=
  MorphismProperty.relative_monotone
    (MorphismProperty.monotone_inverseImage _ isClosedImmersion_le_quasiCompact) _ hF

end AlgebraicGeometry.Space

end
