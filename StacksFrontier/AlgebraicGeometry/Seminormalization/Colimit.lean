module

public import StacksFrontier.AlgebraicGeometry.Seminormalization.IndexFiltered
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.FilteredColimit

/-!
# The seminormalization of a ring is a seminormalization candidate

For a commutative ring `A`, `Algebra.seminormalization A` is the colimit of the finitely
presented `A`-algebras whose spectrum morphisms to `Spec A` are universal homeomorphisms
inducing isomorphisms on all residue fields.  Now that the indexing category is known to be
filtered, the two filtered-colimit theorems of
`StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.FilteredColimit` apply
to that colimit and show that it has the same two properties.

## Main definitions

* `AlgebraicGeometry.seminormalizationObject`: the seminormalization of `A`, as an object of
  `AlgebraicGeometry.SeminormalizationCategory (Spec A)`.

## Main results

* `AlgebraicGeometry.seminormalization_universalHomeomorphism`: the canonical morphism
  `Spec (Algebra.seminormalization A) ⟶ Spec A` is a universal homeomorphism.
* `AlgebraicGeometry.seminormalization_inducesResidueFieldIsomorphisms`: it induces an
  isomorphism on the residue field at every point.
* `AlgebraicGeometry.isSeminormalizationCandidate_seminormalization`: the two statements
  together, in the form of the candidate property of
  `StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.Initial`.

## Implementation notes

The colimit in question is `CategoryTheory.Limits.colimit (Algebra.seminormalizationDiagram A)`,
whose cocone is `CategoryTheory.Limits.colimit.cocone`; for the residue-field statement the same
data is repackaged as a `CategoryTheory.Limits.ColimitPresentation`, which is the shape the
residue-field theorem takes.  Both stage hypotheses are the two components of the defining
property of `Algebra.SeminormalizationIndex`, read off by projection.

The candidate property is the one already in the tree for an arbitrary scheme; it is consumed
here, not restated.  Its base is the affine scheme `Spec A`, and the structure morphism is the
one coming from `algebraMap A (Algebra.seminormalization A)`.

Everything lives in a single universe `u`, as `AlgebraicGeometry.UniversalHomeomorphism` is
available only for `Scheme.{u}`.

No hypothesis beyond those of Tag 0EUS is used: `A` is an arbitrary commutative ring, with no
Noetherian or reducedness assumption.

## What is not done

Nothing here says that `AlgebraicGeometry.seminormalizationObject A` is *initial* in
`AlgebraicGeometry.SeminormalizationCategory (Spec A)`, nor that
`Algebra.seminormalization A` is terminal among `A`-algebras with the two candidate
properties, and nothing here constructs a map into or out of it.  Those statements need, in
addition, the presentation of an arbitrary such algebra as a filtered colimit of finitely
presented ones (Tag 0EUJ), for which no declaration exists in the Lean libraries of this
repository.  Consequently the `CategoryTheory.Limits.HasInitial` instance on
`AlgebraicGeometry.SeminormalizationCategory X` assumed by
`StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.Functorial` and
`StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.SeminormalizationFunctorial` is
still unproved after this file, for every scheme `X`, affine or not.

## References

* [Stacks Project, Tag 0CN8](https://stacks.math.columbia.edu/tag/0CN8)
* [Stacks Project, Tag 0EUR](https://stacks.math.columbia.edu/tag/0EUR)
* [Stacks Project, Tag 0EUS](https://stacks.math.columbia.edu/tag/0EUS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (A : Type u) [CommRing A]

/-- The seminormalization of `A`, presented as the colimit of the seminormalization diagram. -/
private def seminormalizationPresentation :
    ColimitPresentation (Algebra.SeminormalizationIndex A) (Algebra.seminormalization A) :=
  ⟨Algebra.seminormalizationDiagram A, (colimit.cocone (Algebra.seminormalizationDiagram A)).ι,
    colimit.isColimit _⟩

/-- **Stacks 0EUR.** The canonical morphism from the spectrum of the seminormalization of `A`
to `Spec A` is a universal homeomorphism. -/
theorem seminormalization_universalHomeomorphism :
    UniversalHomeomorphism
      (Spec.map (CommRingCat.ofHom (algebraMap A (Algebra.seminormalization A)))) :=
  universalHomeomorphism_specMap_of_isColimit A (Algebra.seminormalizationDiagram A)
    (colimit.cocone _) (colimit.isColimit _) (fun i => i.property.1)

/-- **Stacks 0EUR.** The canonical morphism from the spectrum of the seminormalization of `A`
to `Spec A` induces an isomorphism on the residue field at every point. -/
theorem seminormalization_inducesResidueFieldIsomorphisms :
    Scheme.Hom.InducesResidueFieldIsomorphisms
      (Spec.map (CommRingCat.ofHom (algebraMap A (Algebra.seminormalization A)))) :=
  isIso_residueFieldMap_specMap_of_colimitPresentation (seminormalizationPresentation A)
    (fun i x => i.property.2 x)

/-- **Stacks 0EUS.** The seminormalization of `A` is a seminormalization candidate over
`Spec A`. -/
theorem isSeminormalizationCandidate_seminormalization :
    IsSeminormalizationCandidate (Spec (CommRingCat.of A))
      (Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap A (Algebra.seminormalization A))))) :=
  (isSeminormalizationCandidate_iff _).mpr
    ⟨seminormalization_universalHomeomorphism A,
      seminormalization_inducesResidueFieldIsomorphisms A⟩

/-- The seminormalization of `A`, as an object of the seminormalization category of
`Spec A`. -/
def seminormalizationObject : SeminormalizationCategory (Spec (CommRingCat.of A)) :=
  ⟨Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A (Algebra.seminormalization A)))),
    isSeminormalizationCandidate_seminormalization A⟩

end AlgebraicGeometry

end
