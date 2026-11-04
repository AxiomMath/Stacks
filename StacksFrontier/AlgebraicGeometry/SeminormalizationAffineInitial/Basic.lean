module

public import StacksFrontier.AlgebraicGeometry.Seminormalization.AffineInitial
public import StacksFrontier.AlgebraicGeometry.IndPresentation.IndResidue

/-!
# The seminormalization of a ring is terminal, and initial over an affine base

For a commutative ring `A`, `Algebra.seminormalization A` is the colimit of the finitely
presented `A`-algebras whose spectrum morphism to `Spec A` is a universal homeomorphism inducing
isomorphisms on all residue fields.  `StacksDraft.AlgebraicGeometry.F3.Seminormalization` proves
its universal property for an arbitrary such algebra *conditionally* on Tag 0EUJ, the
presentation of an arbitrary candidate as a filtered colimit of finitely presented ones.  Tag
0EUJ is now a theorem of this repository, so this file discharges that hypothesis and states the
resulting universal property unconditionally.

## Main definitions

* `AlgebraicGeometry.IsSeminormalizationCandidateAlgebra` and
  `AlgebraicGeometry.SeminormalizationAlgebraCategory`: the `A`-algebras whose spectrum morphism
  is a universal homeomorphism inducing isomorphisms on all residue fields, as a full subcategory
  of `CommAlgCat A`.
* `AlgebraicGeometry.uniqueHomToSeminormalization_of_candidate`: every such algebra admits
  exactly one `A`-algebra map to `Algebra.seminormalization A`.
* `AlgebraicGeometry.seminormalizationAlgebraObject_isTerminal`: the seminormalization of `A` is
  terminal in that category.
* `AlgebraicGeometry.isInitial_seminormalizationObject`: the seminormalization of `A` is initial
  in `AlgebraicGeometry.SeminormalizationCategory (Spec A)`.

## Main results

* `AlgebraicGeometry.ind_isFinitelyPresentedCandidateUnder`: Tag 0EUJ in the shape the
  seminormalization's universal property consumes it.
* `AlgebraicGeometry.hasInitial_seminormalizationCategory_spec`: the seminormalization category
  of `Spec A` has an initial object.
* `AlgebraicGeometry.hasInitial_seminormalizationCategory_of_isAffine`: the same for an arbitrary
  affine scheme.

## Implementation notes

The whole content is the identification of two spellings of Tag 0EUJ.
`AlgebraicGeometry.ind_finitePresentation_residueFieldMap_isIso_universalHomeomorphism` states
the filtered-colimit presentation for the object property
`fun C ↦ C.hom.hom.FinitePresentation ∧ UniversalHomeomorphism (Scheme.Spec.map C.hom.op) ∧
∀ x, IsIso ((Scheme.Spec.map C.hom.op).residueFieldMap x)`, while
`AlgebraicGeometry.uniqueHomToSeminormalization_of_ind` consumes it for
`AlgebraicGeometry.IsFinitelyPresentedCandidateUnder`.  The two are definitionally equal --
`AlgebraicGeometry.Spec.map` unfolds to `Scheme.Spec.map _.op` and
`AlgebraicGeometry.Scheme.Hom.InducesResidueFieldIsomorphisms` is an `abbrev` for the
pointwise statement -- so no transport along a propositional equality of object properties is
needed and nothing has to be rebuilt from the `CategoryTheory.ObjectProperty.ind` existential.

The affine-scheme statement is obtained from the `Spec A` statement by transporting along
`AlgebraicGeometry.Scheme.isoSpec`.  `CategoryTheory.Over.mapIso` turns that isomorphism into an
equivalence of the slice categories, `CategoryTheory.ObjectProperty.congrFullSubcategory`
restricts it to the two seminormalization categories, and the inverse image of the candidate
property is computed by composing with an isomorphism, which is
`AlgebraicGeometry.IsSeminormalizationCandidate.comp`.

Everything lives in a single universe `u`, as `AlgebraicGeometry.UniversalHomeomorphism` is
available only for `Scheme.{u}`.

No hypothesis beyond those of Tags 0EUR and 0EUS is used: `A` is an arbitrary commutative ring
and `X` an arbitrary affine scheme, with no Noetherian, reducedness or finiteness assumption.

## What is not done

The initial object of `AlgebraicGeometry.SeminormalizationCategory X` for a scheme `X` which is
*not* affine is not constructed here; that is the gluing step of Tag 0EUS, and it needs the
ring-level functoriality of the seminormalization and its compatibility with the base change
along an open immersion, neither of which is a declaration of this repository.

## References

* [Stacks Project, Tag 0EUJ](https://stacks.math.columbia.edu/tag/0EUJ)
* [Stacks Project, Tag 0EUR](https://stacks.math.columbia.edu/tag/0EUR)
* [Stacks Project, Tag 0EUS](https://stacks.math.columbia.edu/tag/0EUS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (A : Type u) [CommRing A]

/-- **Stacks 0EUJ**, in the shape in which the universal property of the seminormalization
consumes it: an `A`-algebra whose spectrum morphism is a universal homeomorphism inducing
isomorphisms on all residue fields is a filtered colimit of finitely presented `A`-algebras with
the same two properties. -/
theorem ind_isFinitelyPresentedCandidateUnder (B : Type u) [CommRing B] [Algebra A B]
    (huh : UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (hres : Scheme.Hom.InducesResidueFieldIsomorphisms
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :
    ObjectProperty.ind.{u} (IsFinitelyPresentedCandidateUnder A)
      (Under.mk (CommRingCat.ofHom (algebraMap A B))) :=
  ind_finitePresentation_residueFieldMap_isIso_universalHomeomorphism (algebraMap A B) hres huh

/-- **Stacks 0EUR.** An `A`-algebra whose spectrum morphism is a universal homeomorphism inducing
isomorphisms on all residue fields admits exactly one `A`-algebra map to the seminormalization of
`A`. -/
@[instance_reducible]
def uniqueHomToSeminormalization_of_candidate (B : Type u) [CommRing B] [Algebra A B]
    (huh : UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (hres : Scheme.Hom.InducesResidueFieldIsomorphisms
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :
    Unique (CommAlgCat.of A B ⟶ Algebra.seminormalization A) :=
  uniqueHomToSeminormalization_of_ind A B (ind_isFinitelyPresentedCandidateUnder A B huh hres)

/-- The property of an `A`-algebra whose spectrum morphism is a universal homeomorphism inducing
isomorphisms on all residue fields. -/
def IsSeminormalizationCandidateAlgebra : ObjectProperty (CommAlgCat.{u} A) :=
  fun B => UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A B))) ∧
    Scheme.Hom.InducesResidueFieldIsomorphisms
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))

/-- The category of `A`-algebras whose spectrum morphism is a universal homeomorphism inducing
isomorphisms on all residue fields. -/
abbrev SeminormalizationAlgebraCategory :=
  (IsSeminormalizationCandidateAlgebra A).FullSubcategory

/-- The seminormalization of `A` is an object of
`AlgebraicGeometry.SeminormalizationAlgebraCategory A`. -/
def seminormalizationAlgebraObject : SeminormalizationAlgebraCategory A :=
  ⟨Algebra.seminormalization A,
    seminormalization_universalHomeomorphism A,
    seminormalization_inducesResidueFieldIsomorphisms A⟩

/-- **Stacks 0EUR.** The seminormalization of `A` is terminal among the `A`-algebras whose
spectrum morphism is a universal homeomorphism inducing isomorphisms on all residue fields. -/
@[stacks 0EUR "sn_final"]
def seminormalizationAlgebraObject_isTerminal :
    IsTerminal (seminormalizationAlgebraObject A) :=
  IsTerminal.ofUniqueHom
    (fun Y =>
      let := uniqueHomToSeminormalization_of_candidate A Y.obj Y.property.1 Y.property.2
      ObjectProperty.homMk (default : CommAlgCat.of A Y.obj ⟶ Algebra.seminormalization A))
    (fun Y f => by
      let := uniqueHomToSeminormalization_of_candidate A Y.obj Y.property.1 Y.property.2
      exact ObjectProperty.hom_ext (IsSeminormalizationCandidateAlgebra A)
        (Subsingleton.elim (α := CommAlgCat.of A Y.obj ⟶ Algebra.seminormalization A) _ _))

/-- **Stacks 0EUS** over an affine base: the seminormalization of `A` is an initial object of the
category of universal homeomorphisms onto `Spec A` which induce isomorphisms on all residue
fields. -/
def isInitial_seminormalizationObject : IsInitial (seminormalizationObject A) :=
  isInitial_seminormalizationObject_of_ind A
    fun B _ _ huh hres => ind_isFinitelyPresentedCandidateUnder A B huh hres

/-- **Stacks 0EUS** over an affine base: the seminormalization category of `Spec A` has an
initial object. -/
instance hasInitial_seminormalizationCategory_spec :
    HasInitial (SeminormalizationCategory (Spec (CommRingCat.of A))) :=
  (isInitial_seminormalizationObject A).hasInitial

section Transport

variable {X X' Z : Scheme.{u}}

/-- Postcomposing with an isomorphism does not change whether a morphism induces an isomorphism
on the residue field at a point. -/
theorem isIso_residueFieldMap_comp_isIso_iff (f : Z ⟶ X) (g : X ⟶ X') [IsIso g] (z : Z) :
    IsIso ((f ≫ g).residueFieldMap z) ↔ IsIso (f.residueFieldMap z) :=
  (Scheme.residueFieldMap_comp f g z).symm ▸
    isIso_comp_left_iff (g.residueFieldMap (f.base z)) (f.residueFieldMap z)

/-- Postcomposing with an isomorphism does not change whether a morphism is a universal
homeomorphism. -/
theorem universalHomeomorphism_comp_isIso_iff (f : Z ⟶ X) (g : X ⟶ X') [IsIso g] :
    UniversalHomeomorphism (f ≫ g) ↔ UniversalHomeomorphism f :=
  ⟨fun h => universalHomeomorphism_hasTwoOutOfThreeProperty.of_postcomp f g
      (universalHomeomorphism_of_isIso g) h,
    fun h => universalHomeomorphism_hasTwoOutOfThreeProperty.comp_mem f g h
      (universalHomeomorphism_of_isIso g)⟩

/-- An object of `CategoryTheory.Over X` is a seminormalization candidate exactly when its image
under an isomorphism `X ⟶ X'` of bases is one. -/
theorem isSeminormalizationCandidate_map_isIso_iff (g : X ⟶ X') [IsIso g] (Y : Over X) :
    IsSeminormalizationCandidate X' ((Over.map g).obj Y) ↔
      IsSeminormalizationCandidate X Y := by
  rw [isSeminormalizationCandidate_iff, isSeminormalizationCandidate_iff]
  exact and_congr (universalHomeomorphism_comp_isIso_iff Y.hom g)
    (forall_congr' fun y => isIso_residueFieldMap_comp_isIso_iff Y.hom g y)

/-- For an affine scheme `X`, the seminormalization category of `X` is equivalent to that of
`Spec Γ(X, ⊤)`. -/
def seminormalizationCategoryEquivSpec (X : Scheme.{u}) [IsAffine X] :
    SeminormalizationCategory X ≌ SeminormalizationCategory (Spec Γ(X, ⊤)) :=
  Equivalence.congrFullSubcategory (Over.mapIso X.isoSpec)
    (by ext Y; exact isSeminormalizationCandidate_map_isIso_iff X.isoSpec.hom Y)

/-- **Stacks 0EUS** for an affine scheme: the category of universal homeomorphisms onto `X` which
induce isomorphisms on all residue fields has an initial object. -/
instance hasInitial_seminormalizationCategory_of_isAffine (X : Scheme.{u}) [IsAffine X] :
    HasInitial (SeminormalizationCategory X) :=
  ((isInitial_seminormalizationObject (Γ(X, ⊤) : Type u)).isInitialObj
    (seminormalizationCategoryEquivSpec X).inverse _).hasInitial

end Transport

end AlgebraicGeometry

/-! ### Tag 0EUR, label `sn_final`

The label has three assertions.  Two of them -- that the canonical morphism out of the spectrum
of the seminormalization is a universal homeomorphism, and that it induces isomorphisms on all
residue fields -- are proved in
`StacksDraft.AlgebraicGeometry.F3.Seminormalization.Colimit`, which predates the proof of Tag
0EUJ and therefore could not yet state the third.  They are registered here with
`add_to_stacks` so that the tag sits on the whole covering set rather than on part of it.
-/

add_to_stacks 0EUR "sn_final" AlgebraicGeometry.seminormalization_universalHomeomorphism

add_to_stacks 0EUR "sn_final" AlgebraicGeometry.seminormalization_inducesResidueFieldIsomorphisms

end
