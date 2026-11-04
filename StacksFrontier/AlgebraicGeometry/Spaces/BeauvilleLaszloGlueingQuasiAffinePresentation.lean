module

public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingQuasiAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiAffineAffineSpaceBundleInSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability

/-!
# The affine presentation of a quasi-affine component (Stacks 0F9U, step 1)

The proof of Stacks 0F9U begins by choosing, for two of the three components of a glueing
triple with quasi-affine components, the affine-space bundle of Stacks 0F82: an integer `n`, an
affine scheme `T₁` and a morphism `T₁ → V` whose base change along any morphism from an affine
scheme is affine `n`-space.

A component of a glueing triple is an algebraic space over one of the four schemes of the square,
and `AlgebraicGeometry.Space.IsQuasiAffineSpace` says of it that it is represented by an object of
the big fppf site whose underlying scheme is quasi-affine. The bundle is produced as an object of
the site over the same base, together with a morphism of the site onto the representing object; in
this form it enters the assembly of the `A^n` triple and the appeal to Stacks 0F9Q in the proof of
Stacks 0F9U.

## Main results

* `AlgebraicGeometry.Space.exists_affineSpaceBundle_of_isQuasiAffineSpace`: **Stacks 0F9U,
  step 1.** A quasi-affine algebraic space over a base `S` of a big fppf site is represented by
  an object `T` of the site over `S`, and carries an affine-space bundle over `T` by an object
  `T₁` of the site over `S` with affine underlying scheme.

## Implementation notes

Containment of the representing object's underlying scheme in the site is not an extra
hypothesis: an object of `AlgebraicGeometry.BigFppfOver` has its underlying scheme in the
chosen category of schemes below the cutoff by construction, so the bound is the
`CategoryTheory.ObjectProperty.FullSubcategory` property of its left component.

## References

* [Stacks Project, Tag 0F82](https://stacks.math.columbia.edu/tag/0F82)
* [Stacks Project, Tag 0F9Q](https://stacks.math.columbia.edu/tag/0F9Q)
* [Stacks Project, Tag 0F9U](https://stacks.math.columbia.edu/tag/0F9U)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 0F9U, step 1.** Let `F` be a quasi-affine algebraic space over a scheme `S` of a
big fppf site `B`. Then `F` is represented by an object `T` of the big fppf category over `S`,
and there are an integer `n` and an object `T₁` of that category with affine underlying scheme,
together with a morphism `p : T₁ ⟶ T`, such that the base change of `p` along any morphism from
an affine scheme is affine `n`-space over that scheme.

This is Stacks 0F82 applied to the quasi-affine scheme representing `F`, with its total space
placed inside the site by
`AlgebraicGeometry.exists_contains_affine_pullback_iso_affineSpace` and both the bundle and its
structure morphism transported into the slice over `S`. -/
theorem exists_affineSpaceBundle_of_isQuasiAffineSpace
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsQuasiAffineSpace B S hS F) :
    ∃ (n : ℕ) (T T₁ : BigFppfOver B S hS) (p : T₁ ⟶ T),
      Nonempty (F ≅ yoneda.obj T) ∧
        IsAffine ((BigFppfOver.toScheme B S hS).obj T₁) ∧
          LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map p) ∧
            ∀ (X' : Scheme.{u}) (_ : IsAffine X')
              (g : X' ⟶ (BigFppfOver.toScheme B S hS).obj T),
              Nonempty (Over.mk (pullback.fst g ((BigFppfOver.toScheme B S hS).map p)) ≅
                Over.mk (AffineSpace.over (ULift.{u} (Fin n)) X').hom) := by
  obtain ⟨T, hTqa, hrep⟩ := hF
  have : Scheme.IsQuasiAffine ((BigFppfOver.toScheme B S hS).obj T) := hTqa
  have hTc : B.Contains ((BigFppfOver.toScheme B S hS).obj T) := T.left.2
  obtain ⟨n, T₁, hT₁aff, hT₁c, f, hft, hAn⟩ :=
    exists_contains_affine_pullback_iso_affineSpace B
      ((BigFppfOver.toScheme B S hS).obj T) hTc
  refine ⟨n, T, BigFppfOver.mk B S hS hT₁c (f ≫ B.inclusion.map T.hom),
    Over.homMk (ObjectProperty.homMk (X := B.obj hT₁c) f)
      (by apply ObjectProperty.hom_ext; rfl),
    hrep, hT₁aff, hft, hAn⟩

end AlgebraicGeometry.Space

end
