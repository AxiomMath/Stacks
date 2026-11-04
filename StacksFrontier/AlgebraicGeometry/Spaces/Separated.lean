module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCover
public import StacksFrontier.CategoryTheory.Sites.Localization.Relocalize

/-!
# Separation properties of algebraic spaces

An algebraic space over a scheme `S` is separated, locally separated or quasi-separated
*over `S`* when its diagonal is respectively a closed immersion, an immersion or a
quasi-compact morphism; it is Zariski locally quasi-separated over `S` when it has a
Zariski covering by open subspaces which are quasi-separated over `S`.

The absolute versions of these four properties are the properties over `Spec ℤ`, the
terminal scheme. They are obtained by viewing an algebraic space over `S` as an algebraic
space over the terminal scheme along the lower-shriek extension of Stacks 03I5.

## Main definitions

* `AlgebraicGeometry.Space.IsSeparatedOver`,
  `AlgebraicGeometry.Space.IsLocallySeparatedOver`,
  `AlgebraicGeometry.Space.IsQuasiSeparatedOver` and
  `AlgebraicGeometry.Space.IsZariskiLocallyQuasiSeparatedOver` are the four separation
  properties of an algebraic space relative to its base scheme `S`.
* `AlgebraicGeometry.Space.viewOverIntegers` views a presheaf on the big fppf site of `S`
  as a presheaf on the big fppf site of the terminal scheme.
* `AlgebraicGeometry.Space.IsAbsolutelySeparated`,
  `AlgebraicGeometry.Space.IsAbsolutelyLocallySeparated`,
  `AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated` and
  `AlgebraicGeometry.Space.IsAbsolutelyZariskiLocallyQuasiSeparated` are the four absolute
  separation properties.

## References

* [Stacks Project, Tag 02X5](https://stacks.math.columbia.edu/tag/02X5)
* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Separation properties relative to the base scheme -/

/-- An algebraic space over `S` is *separated over `S`* when its diagonal is a closed immersion
of algebraic spaces. -/
@[stacks 02X5 "separated"]
abbrev IsSeparatedOver (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  IsClosedImmersion B S hS (diag F)

/-- An algebraic space over `S` is *locally separated over `S`* when its diagonal is an
immersion of algebraic spaces. -/
@[stacks 02X5 "locally_separated"]
abbrev IsLocallySeparatedOver (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  IsImmersion B S hS (diag F)

/-- An algebraic space over `S` is *quasi-separated over `S`* when its diagonal is
quasi-compact after every representable base change. -/
@[stacks 02X5 "quasi_separated"]
abbrev IsQuasiSeparatedOver (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS))) (diag F)

/-- An algebraic space over `S` is *Zariski locally quasi-separated over `S`* when it admits a
Zariski covering by open subspaces which are quasi-separated over `S`. -/
@[stacks 02X5 "zariski_locally_quasi_separated"]
abbrev IsZariskiLocallyQuasiSeparatedOver (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∃ (I : Type u) (U : I → Subfunctor F),
    IsZariskiCover B S hS I U ∧ ∀ i, IsQuasiSeparatedOver B S hS (U i).toFunctor

/-! ### Absolute separation properties -/

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- A presheaf on the big fppf site of `S`, viewed on the big fppf site of the terminal scheme
`Spec ℤ` along the lower-shriek extension of Stacks 03I5. -/
noncomputable abbrev viewOverIntegers (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u :=
  (OverShriek.relocalizePresheafFunctor
    (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ)).obj F

/-- An algebraic space is *separated* when it is separated over the terminal scheme, that is,
when its absolute diagonal is a closed immersion. -/
@[stacks 03BS "part (1): separated"]
abbrev IsAbsolutelySeparated (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  IsSeparatedOver B (⊤_ Scheme.{u}) hZ (viewOverIntegers B S hS hZ F)

/-- An algebraic space is *locally separated* when it is locally separated over the terminal
scheme, that is, when its absolute diagonal is an immersion. -/
@[stacks 03BS "part (2): locally separated"]
abbrev IsAbsolutelyLocallySeparated (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  IsLocallySeparatedOver B (⊤_ Scheme.{u}) hZ (viewOverIntegers B S hS hZ F)

/-- An algebraic space is *quasi-separated* when it is quasi-separated over the terminal
scheme, that is, when its absolute diagonal is quasi-compact. -/
@[stacks 03BS "part (3): quasi-separated"]
abbrev IsAbsolutelyQuasiSeparated (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  IsQuasiSeparatedOver B (⊤_ Scheme.{u}) hZ (viewOverIntegers B S hS hZ F)

/-- An algebraic space is *Zariski locally quasi-separated* when its absolute form admits a
Zariski covering by quasi-separated open subspaces. -/
@[stacks 03BS "part (4): Zariski locally quasi-separated"]
abbrev IsAbsolutelyZariskiLocallyQuasiSeparated
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  IsZariskiLocallyQuasiSeparatedOver B (⊤_ Scheme.{u}) hZ (viewOverIntegers B S hS hZ F)

end AlgebraicGeometry.Space

/-! ### Base change of algebraic spaces

The two operations attached to a morphism `S ⟶ S'` of the big fppf site — restriction of a
presheaf over `S'` to `S`, and the lower-shriek extension of a presheaf over `S` to `S'` —
are the relocalization functors `CategoryTheory.OverShriek.relocalizeRestrict` and
`CategoryTheory.OverShriek.relocalizePresheafFunctor`. -/

add_to_stacks 03I5 "part (1), base-change construction"
  CategoryTheory.OverShriek.relocalizeRestrict
add_to_stacks 03I5 "part (2), lower-shriek construction"
  CategoryTheory.OverShriek.relocalizePresheafFunctor

end
