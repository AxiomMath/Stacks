module

public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineViewOverIntegers
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescent
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeReflectsIso

/-!
# Affineness of an algebraic space is unchanged by a change of base

Let `g : S ⟶ S'` be a morphism of a big fppf site. The lower-shriek extension
`CategoryTheory.OverShriek.relocalizePresheafFunctor g` of Stacks 03I5, part (2), carries an
algebraic space over `S` to an algebraic space over `S'`, and it *neither creates nor destroys
affineness*: the relocalized presheaf is affine exactly when the original is.

The forward direction is immediate, the lower-shriek extension carrying representables to
representables with the same underlying scheme. The converse is the substance: an identification
of the relocalized presheaf with a representable presheaf over `S'` is, by
`CategoryTheory.OverShriek.exists_eq_relocalizeYonedaFactorIso_comp`, the relocalization of a
morphism out of a representable presheaf *over `S`* with the same underlying scheme; and
relocalization reflects isomorphisms, so that morphism is already an isomorphism.

Applied to the structure morphism `S ⟶ Spec ℤ`, this is what lets a statement about affineness of
algebraic spaces over an arbitrary base be read over the terminal scheme, exactly as Stacks 084T
is read there for separatedness.

## Main results

* `AlgebraicGeometry.Space.isAffineSpace_relocalize`: affineness is carried along a change of
  base.
* `AlgebraicGeometry.Space.isAffineSpace_of_isAffineSpace_relocalize`: affineness is reflected by
  a change of base.

That an algebraic space over `S` is affine precisely when its view over the terminal scheme is,
is `AlgebraicGeometry.Space.isAffineSpace_viewOverIntegers_iff` of
`StacksFrontier.AlgebraicGeometry.Spaces.AffineViewOverIntegers`.

## Implementation notes

The representing object produced by the converse is `CategoryTheory.Over.mk ψ` for the
factorization `ψ` of the structure morphism of the representing object over `S'`. Its underlying
scheme is the same, so no transport of affineness of a scheme is needed.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 03I4](https://stacks.math.columbia.edu/tag/03I4)
* [Stacks Project, Tag 084T](https://stacks.math.columbia.edu/tag/084T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')

/-- **Affineness is carried along a change of base.** The lower-shriek extension carries the
presheaf represented by an object of the big fppf category over `S` to the presheaf represented by
the same scheme read over `S'`. -/
theorem isAffineSpace_relocalize (g : B.obj hS ⟶ B.obj hS')
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAffineSpace B S hS F) :
    IsAffineSpace B S' hS' ((OverShriek.relocalizePresheafFunctor g).obj F) := by
  obtain ⟨T, hT, ⟨e⟩⟩ := hF
  exact ⟨(Over.map g).obj T, hT,
    ⟨(OverShriek.relocalizePresheafFunctor g).mapIso e ≪≫
      (OverShriek.relocalizeYonedaIso g).app T⟩⟩

/-- **Affineness is reflected by a change of base.** If the lower-shriek extension of a presheaf
on the big fppf site of `S` is an affine algebraic space over `S'`, then the presheaf is an affine
algebraic space over `S`.

The identification with a representable presheaf is the relocalization of a morphism out of a
representable presheaf over `S`, with the same underlying scheme, and relocalization reflects
isomorphisms. -/
theorem isAffineSpace_of_isAffineSpace_relocalize (g : B.obj hS ⟶ B.obj hS')
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAffineSpace B S' hS' ((OverShriek.relocalizePresheafFunctor g).obj F)) :
    IsAffineSpace B S hS F := by
  obtain ⟨W, hW, ⟨e⟩⟩ := hF
  obtain ⟨ψ, hψ, σ, hσ⟩ := OverShriek.exists_eq_relocalizeYonedaFactorIso_comp g e.inv
  have hmap : (OverShriek.relocalizePresheafFunctor g).map σ =
      (OverShriek.relocalizeYonedaFactorIso g hψ).inv ≫ e.inv := by
    rw [hσ, Iso.inv_hom_id_assoc]
  have : IsIso ((OverShriek.relocalizePresheafFunctor g).map σ) := by
    rw [hmap]
    infer_instance
  have : IsIso σ := OverShriek.isIso_of_isIso_map_relocalizePresheafFunctor g σ
  exact ⟨Over.mk ψ, hW, ⟨(asIso σ).symm⟩⟩

end AlgebraicGeometry.Space

end
