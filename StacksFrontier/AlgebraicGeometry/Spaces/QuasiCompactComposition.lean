module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# Composition of quasi-compact morphisms of algebraic spaces

A morphism of algebraic spaces over a scheme `S` is quasi-compact when every base change of it
along a morphism from a quasi-compact algebraic space has quasi-compact source. This property
is stable under composition, and a representable morphism which is quasi-compact after every
representable base change is quasi-compact in this sense.

## Main results

* `AlgebraicGeometry.Space.isQuasiCompact_of_presheaf_quasiCompact`: a representable morphism
  which is quasi-compact after every representable base change is quasi-compact.
* `AlgebraicGeometry.Space.IsQuasiCompact.comp`: the composition of two quasi-compact morphisms
  of algebraic spaces is quasi-compact.

## Implementation notes

Quasi-compactness after every representable base change is read as `MorphismProperty.presheaf`
at the inverse image of `AlgebraicGeometry.QuasiCompact` along
`AlgebraicGeometry.BigFppfOver.toScheme`.

Algebraicity of the source of the composite is not used, so it is not assumed.

## References

* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 03E3](https://stacks.math.columbia.edu/tag/03E3)
* [Stacks Project, Tag 03HD](https://stacks.math.columbia.edu/tag/03HD)
* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 03HG](https://stacks.math.columbia.edu/tag/03HG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Representable quasi-compact morphisms -/

/-- A morphism of presheaves on the big fppf site of `S` which is representable and
quasi-compact after every representable base change is quasi-compact: every base change of it
along a morphism from a quasi-compact algebraic space has quasi-compact source. -/
@[stacks 03HD "part (1) implies part (2)"]
theorem isQuasiCompact_of_presheaf_quasiCompact
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (hf : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    IsQuasiCompact B S hS f := by
  intro Z _ hZqc g
  obtain ⟨W, a, hWc, hasurj, haet⟩ := hZqc
  have haet' := presheaf_etale_of_isEtale B S hS haet
  have sqA : IsPullback (pullback.fst (a ≫ g) f) _ a (pullback.fst g f) :=
    IsPullback.of_bot' (IsPullback.of_hasPullback (a ≫ g) f) (IsPullback.of_hasPullback g f)
  refine IsQuasiCompactSpace.of_surjective_etale B S hS
    ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback sqA hasurj)
    ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback sqA haet') ?_
  exact (isQuasiCompactSpace_yoneda_obj B S hS
      (@QuasiCompact.compactSpace_of_compactSpace _ _ _ (hf.property_snd (a ≫ g)) hWc)).of_iso
    B S hS ((IsPullback.of_hasPullback (a ≫ g) f).flip.isoIsPullback _ _
      (hf.rep.isPullback (a ≫ g))).symm

/-! ### Composition -/

/-- The composition of a pair of quasi-compact morphisms of algebraic spaces over `S` is
quasi-compact. -/
@[stacks 03HG]
theorem IsQuasiCompact.comp
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z)
    (hf : IsQuasiCompact B S hS f) (hg : IsQuasiCompact B S hS g) :
    IsQuasiCompact B S hS (f ≫ g) := by
  intro W hW hWqc h
  exact (hf (pullback h g) (isAlgebraicSpace_pullback B S hS h g hW hY hZ)
      (hg W hW hWqc h) (pullback.snd h g)).of_iso B S hS
    (((IsPullback.of_hasPullback (pullback.snd h g) f).flip.paste_vert
      (IsPullback.of_hasPullback h g).flip).flip.isoPullback)

end AlgebraicGeometry.Space

end
