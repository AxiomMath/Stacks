module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence

/-!
# A finite open subspace over a separated morphism is closed

Let `f : X ⟶ Y` be a separated morphism of algebraic spaces over a scheme `S`, let `T` be an
algebraic space over `S` and let `(a, Z)` be a pair as in Stacks 04PC: a morphism `a : T ⟶ Y`
together with an open subspace `Z` of `T ×_Y X` finite over `T`. Then `Z` is also a closed
subspace of `T ×_Y X`.

## Main results

* `AlgebraicGeometry.Space.FiniteOpenSubspace.isClosedSubspace` — Stacks 04PH.

## Implementation notes

The pair `(a, Z)` is `AlgebraicGeometry.Space.FiniteOpenSubspace`, and the conclusion concerns
its `subspace` field.

The projection `T ×_Y X ⟶ T` is separated, being a base change of `f`; the composite of the
inclusion of `Z` with that projection is universally closed, being finite; so the point set of
`Z` has closed image in that of `T ×_Y X` by Stacks 04NX, part (1). An immersion whose point
set has closed image is a closed immersion, which is Stacks 04CD.

Separatedness of the projection is obtained from Stacks 03KL for the *second* projection and
then transported across the symmetry of the fibre product, since the pair presents its open
subspace inside `pullback a.hom f.hom` with the projection to `T` as the first one.

## References

* [Stacks Project, Tag 04PH](https://stacks.math.columbia.edu/tag/04PH)
* [Stacks Project, Tag 04PC](https://stacks.math.columbia.edu/tag/04PC)
* [Stacks Project, Tag 04NX](https://stacks.math.columbia.edu/tag/04NX)
* [Stacks Project, Tag 04CD](https://stacks.math.columbia.edu/tag/04CD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 04PH.** An open subspace of `T ×_Y X` which is finite over `T` is a closed
subspace of `T ×_Y X`, provided `f : X ⟶ Y` is separated. -/
@[stacks 04PH]
theorem FiniteOpenSubspace.isClosedSubspace (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (T : AlgebraicSpaces B S hS) (Z : FiniteOpenSubspace B S hS f T)
    (hf : IsSeparated B S hS f.hom) :
    IsClosedSubspace B S hS Z.subspace := by
  let W := pullback Z.toBase.hom f.hom
  let i : Z.subspace.toFunctor ⟶ W := Z.subspace.ι
  let p : W ⟶ T.obj := pullback.fst Z.toBase.hom f.hom
  have hW : IsAlgebraicSpace B S hS W :=
    isAlgebraicSpace_pullback B S hS Z.toBase.hom f.hom T.property X.property Y.property
  have hZ : IsAlgebraicSpace B S hS Z.subspace.toFunctor := Z.isOpen.1
  have hcomp : UniversallyClosed B S hS (i ≫ p) :=
    ((isFinite_iff_isAffineHom_and_isProper B S hS hZ T.property
      (i ≫ p)).mp Z.finite_projection).2.2.2
  have hp : IsSeparated B S hS p := by
    let P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
      MorphismProperty.diagonal
        (MorphismProperty.presheaf
          (MorphismProperty.inverseImage
            (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B S hS)))
    have hP : P.RespectsIso := by
      dsimp [P]
      infer_instance
    show P (pullback.fst Z.toBase.hom f.hom)
    rw [← pullbackSymmetry_inv_comp_snd f.hom Z.toBase.hom]
    exact (MorphismProperty.cancel_left_of_respectsIso (P := P)
      (pullbackSymmetry f.hom Z.toBase.hom).inv
      (pullback.snd f.hom Z.toBase.hom)).mpr
      (isSeparated_pullback B S hS f.hom Z.toBase.hom hf)
  exact ⟨hZ, (isClosedImmersion_iff_isClosed_range_pointsMap B S hS hW i
    (isImmersion_of_isOpenImmersion B S hS Z.isOpen.2)).2
    (isClosed_range_of_comp_of_isSeparated B S hS hZ hW T.property i p hcomp hp)⟩

end AlgebraicGeometry.Space

end
