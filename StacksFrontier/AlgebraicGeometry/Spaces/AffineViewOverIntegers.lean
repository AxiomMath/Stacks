module

public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeReflectsRepresentable

/-!
# Affineness is absolute

An algebraic space `F` over `S` is affine when it is represented by an object of the big fppf site
of `S` with affine underlying scheme (`AlgebraicGeometry.Space.IsAffineSpace`).  This file proves
that the notion does not depend on the base: `F` is affine over `S` exactly when its view over the
terminal scheme `Spec ℤ`, `AlgebraicGeometry.Space.viewOverIntegers`, is affine over `Spec ℤ`.

## Main results

* `AlgebraicGeometry.Space.isAffineSpace_viewOverIntegers_iff`: affineness over `S` is
  affineness over the terminal scheme.

## Implementation notes

`viewOverIntegers` is the presheaf level lower shriek `Λ` of the relocalization along the
structure morphism `S ⟶ ⊤_ Scheme` of the site (Stacks 03I5 (2)).  If `F ≅ h_T`, then
`Λ F ≅ Λ h_T ≅ h_{j T}` (`CategoryTheory.OverShriek.relocalizeYonedaIso`), and `j T` has the
underlying scheme of `T`.  Conversely, if `Λ F ≅ h_T`, then `F ≅ h_{T'}` for an object `T'` with
the underlying scheme of `T` (`CategoryTheory.OverShriek.exists_left_eq_nonempty_iso_yoneda`).
In both directions the representing scheme is unchanged, so it is affine on one side exactly
when it is on the other.

## References

* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- **Affineness of an algebraic space is absolute.**  A presheaf `F` on the big fppf site of `S`
is an affine algebraic space over `S` exactly when its view over the terminal scheme is an affine
algebraic space over the terminal scheme.  The representing object changes only by its structure
morphism, never by its underlying scheme. -/
theorem isAffineSpace_viewOverIntegers_iff (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} :
    IsAffineSpace B (⊤_ Scheme.{u}) hZ (viewOverIntegers B S hS hZ F) ↔
      IsAffineSpace B S hS F := by
  constructor
  · rintro ⟨T, hT, ⟨e⟩⟩
    obtain ⟨T', hT', ⟨e'⟩⟩ := OverShriek.exists_left_eq_nonempty_iso_yoneda _ e
    have hX : (BigFppfOver.toScheme B S hS).obj T' =
        (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj T :=
      congrArg B.inclusion.obj hT'
    exact ⟨T', hX ▸ hT, ⟨e'⟩⟩
  · rintro ⟨T, hT, ⟨e⟩⟩
    exact ⟨(Over.map _).obj T, hT,
      ⟨(OverShriek.relocalizePresheafFunctor _).mapIso e ≪≫
        (OverShriek.relocalizeYonedaIso _).app T⟩⟩

end AlgebraicGeometry.Space
