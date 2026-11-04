module

public import StacksFrontier.AlgebraicGeometry.Seminormalization.UniversalProperty
public import Mathlib.CategoryTheory.ObjectProperty.Ind

/-!
# The universal property of the seminormalization of a ring, reduced to Tag 0EUJ

For a commutative ring `A`, the seminormalization `Algebra.seminormalization A` receives exactly
one `A`-algebra map from every *finitely presented* algebra whose structure morphism on spectra
is a universal homeomorphism inducing isomorphisms on all residue fields; that is
`StacksFrontier.AlgebraicGeometry.Seminormalization.UniversalProperty`.  Tag 0EUR asserts the
same for an arbitrary such algebra, finitely presented or not.

This file proves that implication *conditionally on Tag 0EUJ*, the statement that every such
algebra is a filtered colimit of finitely presented ones.  Nothing here assumes Tag 0EUJ as an
axiom: it appears as an explicit hypothesis on every declaration, spelled
`CategoryTheory.ObjectProperty.ind (AlgebraicGeometry.IsFinitelyPresentedCandidateUnder A)`.

The point of the file is to measure the gap.  After it, the only missing ingredient for the
ring-level universal property of Tag 0EUR is Tag 0EUJ, and that is checked by the compiler
rather than asserted in a comment.

## Main definitions

* `AlgebraicGeometry.uniqueHomToSeminormalization_of_ind`: conditionally on Tag 0EUJ for `B`,
  the `A`-algebra maps `B ⟶ Algebra.seminormalization A` form a singleton.

## Main results

* `AlgebraicGeometry.subsingleton_hom_seminormalization_of_ind`: conditionally on Tag 0EUJ for
  `B`, there is at most one `A`-algebra map `B ⟶ Algebra.seminormalization A`.
* `AlgebraicGeometry.nonempty_hom_seminormalization_of_ind`: conditionally on Tag 0EUJ for `B`,
  there is at least one.

## Implementation notes

Both halves come straight from the filtered-colimit presentation and the finitely presented case,
and neither needs the stages to be compatible by hand:

* *Uniqueness.*  Two maps out of the colimit agree because they agree after composition with
  every colimit inclusion, and each such composite starts at a finitely presented candidate,
  where `AlgebraicGeometry.subsingleton_underHom_seminormalization` applies.
* *Existence.*  The canonical maps
  `AlgebraicGeometry.canonicalUnderHomToSeminormalization` out of the stages assemble into a
  cocone with no work: the naturality squares are equalities between two maps out of a finitely
  presented candidate, so they hold by the same subsingleton statement.  The colimit then
  descends them.

Consequently the hypothesis is used only through `CategoryTheory.Limits.ColimitPresentation` and
its `isColimit` field; the filteredness of the index of that presentation is not used here
directly, only inside the finitely presented case.

The conclusions are stated in `CommAlgCat A`, where `Algebra.seminormalization` lives, while the
hypothesis is stated in `CategoryTheory.Under (CommRingCat.of A)`, which is where Tag 0EUJ
states it.  Passing between them is the full faithfulness of
`CommAlgCat.commAlgCatEquivUnder`, the objects on the two sides being equal by `rfl`.

Everything lives in a single universe `u`, as `AlgebraicGeometry.UniversalHomeomorphism` is
available only for `Scheme.{u}`.

## What is not done

Tag 0EUJ itself is not proved here; it enters only as a hypothesis.  Its own statement is
`AlgebraicGeometry.ind_finitePresentation_residueFieldMap_isIso_universalHomeomorphism`, which
derives it from the finite-stage result
`AlgebraicGeometry.exists_universalHomeomorphism_and_isIso_residueFieldMap_of_isColimit`.
Therefore nothing here is an unconditional statement of Tag 0EUR.

Nothing here is about schemes.  Even granting Tag 0EUJ, this file gives terminality of
`Algebra.seminormalization A` among candidate `A`-algebras, not initiality in
`AlgebraicGeometry.SeminormalizationCategory (Spec A)`: the latter needs in addition that every
candidate over an affine base is affine — which is
`AlgebraicGeometry.IsSeminormalizationCandidate.isAffine` — together with the identification of
morphisms of schemes over `Spec A` with maps of `A`-algebras in the opposite direction.  The
instance `CategoryTheory.Limits.HasInitial (AlgebraicGeometry.SeminormalizationCategory X)` for
general `X` needs, beyond that, the gluing over an affine cover.

## References

* [Stacks Project, Tag 0EUJ](https://stacks.math.columbia.edu/tag/0EUJ)
* [Stacks Project, Tag 0EUR](https://stacks.math.columbia.edu/tag/0EUR)
* [Stacks Project, Tag 0EUS](https://stacks.math.columbia.edu/tag/0EUS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- **Stacks 0EUR**, conditionally on Tag 0EUJ.  If `B` is a filtered colimit of finitely
presented `A`-algebras whose spectra are universal homeomorphisms over `Spec A` inducing
isomorphisms on all residue fields, then there is at most one `A`-algebra map from `B` to the
seminormalization of `A`. -/
theorem subsingleton_hom_seminormalization_of_ind
    (hind : ObjectProperty.ind.{u} (IsFinitelyPresentedCandidateUnder A)
      (Under.mk (CommRingCat.ofHom (algebraMap A B)))) :
    Subsingleton (CommAlgCat.of A B ⟶ Algebra.seminormalization A) := by
  obtain ⟨J, _, _, pres, hstage⟩ := hind
  have hU : Subsingleton (Under.mk (CommRingCat.ofHom (algebraMap A B)) ⟶
      seminormalizationUnder A) :=
    ⟨fun f g => pres.isColimit.hom_ext fun i =>
      (subsingleton_underHom_seminormalization (pres.diag.obj i) (hstage i)).allEq _ _⟩
  exact ⟨fun f g => (commAlgCatEquivUnder (CommRingCat.of A)).functor.map_injective
    (hU.allEq _ _)⟩

/-- **Stacks 0EUR**, conditionally on Tag 0EUJ.  Under the same hypothesis there is at least one
`A`-algebra map from `B` to the seminormalization of `A`, obtained by descending the canonical
maps out of the finitely presented stages. -/
theorem nonempty_hom_seminormalization_of_ind
    (hind : ObjectProperty.ind.{u} (IsFinitelyPresentedCandidateUnder A)
      (Under.mk (CommRingCat.ofHom (algebraMap A B)))) :
    Nonempty (CommAlgCat.of A B ⟶ Algebra.seminormalization A) := by
  obtain ⟨J, _, _, pres, hstage⟩ := hind
  let t : Cocone pres.diag :=
    { pt := seminormalizationUnder A
      ι :=
        { app := fun i => canonicalUnderHomToSeminormalization (pres.diag.obj i) (hstage i)
          naturality := fun i _ _ =>
            (subsingleton_underHom_seminormalization (pres.diag.obj i) (hstage i)).allEq _ _ } }
  obtain ⟨p, -⟩ := (commAlgCatEquivUnder (CommRingCat.of A)).functor.map_surjective
    (X := CommAlgCat.of A B) (Y := Algebra.seminormalization A) (pres.isColimit.desc t)
  exact ⟨p⟩

/-- **Stacks 0EUR**, conditionally on Tag 0EUJ.  Under the same hypothesis the seminormalization
of `A` admits exactly one `A`-algebra map from `B`.  This is the ring-level universal property of
Tag 0EUR, with Tag 0EUJ as its only remaining hypothesis. -/
@[instance_reducible]
def uniqueHomToSeminormalization_of_ind
    (hind : ObjectProperty.ind.{u} (IsFinitelyPresentedCandidateUnder A)
      (Under.mk (CommRingCat.ofHom (algebraMap A B)))) :
    Unique (CommAlgCat.of A B ⟶ Algebra.seminormalization A) :=
  let := subsingleton_hom_seminormalization_of_ind A B hind
  uniqueOfSubsingleton (nonempty_hom_seminormalization_of_ind A B hind).some

end AlgebraicGeometry

end
