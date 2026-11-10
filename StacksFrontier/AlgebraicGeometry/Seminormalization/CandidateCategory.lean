module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.ResidueField
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Integral
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.TwoOutOfThree
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.Initial

/-!
# Structure of the seminormalization category of a scheme

For a scheme `X`, `AlgebraicGeometry.SeminormalizationCategory X` is the full subcategory of
`Over X` on the objects whose structure morphism is a universal homeomorphism and induces an
isomorphism on every residue field
([Stacks, Tag 0EUS](https://stacks.math.columbia.edu/tag/0EUS)).  Its initial object is the
seminormalization of `X`.

This file proves the structural facts about that category which the construction of the initial
object needs, none of which are about the initial object itself:

* a candidate is integral and affine over `X`, hence has affine source when `X` is affine;
* the candidate property is closed under composition;
* every morphism of the category is itself a universal homeomorphism inducing isomorphisms on
  residue fields;
* restricting a candidate along an open immersion into `X` again gives a candidate.

The route is short.  Affineness is read off the characterization of universal homeomorphisms as
the integral, universally injective, surjective morphisms
([Stacks, Tag 04DF](https://stacks.math.columbia.edu/tag/04DF)), proved in
`StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Integral`, together with
`AlgebraicGeometry.IsIntegralHom.iff_universallyClosed_and_isAffineHom`.  That a morphism of the
category is a universal homeomorphism is the two-out-of-three property
([Stacks, Tag 0H2M](https://stacks.math.columbia.edu/tag/0H2M)), proved in
`StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.TwoOutOfThree`; its residue
field half is `AlgebraicGeometry.Scheme.residueFieldMap_comp` and cancellation of an
isomorphism.  The restriction statement combines stability of
`CategoryTheory.MorphismProperty.universally` under base change with the fact that a base change
of an open immersion is an open immersion and that an open immersion induces isomorphisms on
residue fields.

## Main definitions

* `AlgebraicGeometry.SeminormalizationCategory.restrict`: the base change of a seminormalization
  candidate over `X` along an open immersion into `X`.

## Main results

* `AlgebraicGeometry.IsSeminormalizationCandidate.isIntegralHom`,
  `AlgebraicGeometry.IsSeminormalizationCandidate.isAffineHom` and
  `AlgebraicGeometry.IsSeminormalizationCandidate.isAffine`: a candidate is integral and affine
  over `X`, and has affine source when `X` is affine.
* `AlgebraicGeometry.IsSeminormalizationCandidate.comp`: a candidate over the source of a
  candidate is a candidate.
* `AlgebraicGeometry.SeminormalizationCategory.universalHomeomorphism_hom_left` and
  `AlgebraicGeometry.SeminormalizationCategory.isIso_residueFieldMap_hom_left`: every morphism of
  the category is a universal homeomorphism inducing isomorphisms on residue fields.
* `AlgebraicGeometry.isSeminormalizationCandidate_pullback`: the base change of a candidate along
  an open immersion is a candidate.

## Implementation notes

`AlgebraicGeometry.IsSeminormalizationCandidate` is a `CategoryTheory.ObjectProperty (Over X)`
defined by a `def`, and `AlgebraicGeometry.SeminormalizationCategory X` is its induced full
subcategory.  Its two components are therefore reached through the named
`AlgebraicGeometry.isSeminormalizationCandidate_iff` rather than by projecting the underlying
conjunction, so that no proof here depends on the `def` unfolding.

Everything is in a single universe `u`, as `CategoryTheory.MorphismProperty.topologically` and
hence `AlgebraicGeometry.UniversalHomeomorphism` are available only for `Scheme.{u}`.

No hypothesis beyond those of Tag 0EUS is used: `X` is an arbitrary scheme, with no
Noetherian, reducedness or finiteness assumption, and affineness of `X` is assumed only in the
one statement that concludes affineness of the source.

## What is not done

The initial object of `AlgebraicGeometry.SeminormalizationCategory X` — the seminormalization of
`X` — is *not* constructed here, and nothing here asserts that it exists.  Nothing in this file
mentions the seminormalization of a ring.  In particular the instance
`Limits.HasInitial (AlgebraicGeometry.SeminormalizationCategory X)` assumed by
`StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.Functorial` and
`StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.SeminormalizationFunctorial` is still
unproved after this file, and so is the characterization of when the morphism out of it is an
isomorphism.

Restriction is proved only along open immersions, which is what an affine-local argument needs;
the general base change of a candidate is not stated here.

## References

* [Stacks Project, Tag 04DF](https://stacks.math.columbia.edu/tag/04DF)
* [Stacks Project, Tag 0H2M](https://stacks.math.columbia.edu/tag/0H2M)
* [Stacks Project, Tag 0EUS](https://stacks.math.columbia.edu/tag/0EUS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The two-out-of-three property of universal homeomorphisms, named so that its components are
reached by projection.  Instance search finds
`CategoryTheory.MorphismProperty.HasTwoOutOfThreeProperty` for universal homeomorphisms but not
its parents `CategoryTheory.MorphismProperty.IsStableUnderComposition` and
`CategoryTheory.MorphismProperty.HasOfPostcompProperty`, so both are taken from here. -/
theorem hasTwoOutOfThreeProperty_universalHomeomorphism :
    MorphismProperty.HasTwoOutOfThreeProperty
      (@UniversalHomeomorphism.{u} : MorphismProperty Scheme.{u}) :=
  universalHomeomorphism_hasTwoOutOfThreeProperty

/-- Being a seminormalization candidate over `X` means exactly being a universal homeomorphism
onto `X` which induces an isomorphism on every residue field. -/
theorem isSeminormalizationCandidate_iff (Y : Over X) :
    IsSeminormalizationCandidate X Y ↔
      UniversalHomeomorphism Y.hom ∧ ∀ y : Y.left, IsIso (Y.hom.residueFieldMap y) :=
  Iff.rfl

namespace IsSeminormalizationCandidate

variable {Y : Over X}

/-- The structure morphism of a seminormalization candidate is a universal homeomorphism. -/
theorem universalHomeomorphism (hY : IsSeminormalizationCandidate X Y) :
    UniversalHomeomorphism Y.hom :=
  ((isSeminormalizationCandidate_iff Y).mp hY).1

/-- The structure morphism of a seminormalization candidate induces an isomorphism on the
residue field at every point. -/
theorem isIso_residueFieldMap (hY : IsSeminormalizationCandidate X Y) (y : Y.left) :
    IsIso (Y.hom.residueFieldMap y) :=
  ((isSeminormalizationCandidate_iff Y).mp hY).2 y

/-- The structure morphism of a seminormalization candidate is integral. -/
theorem isIntegralHom (hY : IsSeminormalizationCandidate X Y) : IsIntegralHom Y.hom :=
  ((universalHomeomorphism_iff_integral_universallyInjective_surjective Y.hom).mp
    hY.universalHomeomorphism).1

/-- The structure morphism of a seminormalization candidate is affine. -/
theorem isAffineHom (hY : IsSeminormalizationCandidate X Y) : IsAffineHom Y.hom :=
  (IsIntegralHom.iff_universallyClosed_and_isAffineHom.mp hY.isIntegralHom).2

/-- Over an affine scheme, the source of a seminormalization candidate is affine. -/
theorem isAffine [IsAffine X] (hY : IsSeminormalizationCandidate X Y) : IsAffine Y.left := by
  have := hY.isAffineHom
  exact isAffine_of_isAffineHom Y.hom

/-- A universal homeomorphism inducing isomorphisms on residue fields onto the source of a
seminormalization candidate over `X` is again a seminormalization candidate over `X`. -/
theorem comp {Z : Scheme.{u}} (hY : IsSeminormalizationCandidate X Y) (g : Z ⟶ Y.left)
    (hg : UniversalHomeomorphism g) (hgres : ∀ z : Z, IsIso (g.residueFieldMap z)) :
    IsSeminormalizationCandidate X (Over.mk (g ≫ Y.hom)) := by
  refine (isSeminormalizationCandidate_iff (Over.mk (g ≫ Y.hom))).mpr ⟨?_, fun z => ?_⟩
  · exact hasTwoOutOfThreeProperty_universalHomeomorphism.comp_mem g Y.hom hg
      hY.universalHomeomorphism
  · change IsIso ((g ≫ Y.hom).residueFieldMap z)
    rw [Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso' (hY.isIso_residueFieldMap (g.base z)) (hgres z)

end IsSeminormalizationCandidate

/-- If `g ≫ h` and `h` induce isomorphisms on residue fields at `g a` and `a`, so does `g`. -/
private theorem isIso_residueFieldMap_of_comp {A B C : Scheme.{u}} (g : A ⟶ B) (h : B ⟶ C) (a : A)
    (hh : IsIso (h.residueFieldMap (g.base a))) (hgh : IsIso ((g ≫ h).residueFieldMap a)) :
    IsIso (g.residueFieldMap a) := by
  rw [Scheme.residueFieldMap_comp] at hgh
  exact (isIso_comp_left_iff (h.residueFieldMap (g.base a)) (g.residueFieldMap a)).mp hgh

/-- The base change of a seminormalization candidate over `X` along an open immersion into `X`
is a seminormalization candidate over the open subscheme. -/
theorem isSeminormalizationCandidate_pullback {U : Scheme.{u}} (f : U ⟶ X)
    [IsOpenImmersion f] (Y : SeminormalizationCategory X) :
    IsSeminormalizationCandidate U (Over.mk (pullback.fst f Y.obj.hom)) := by
  refine (isSeminormalizationCandidate_iff (Over.mk (pullback.fst f Y.obj.hom))).mpr
    ⟨⟨?_⟩, fun z => ?_⟩
  · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f Y.obj.hom).flip
      (IsSeminormalizationCandidate.universalHomeomorphism
        Y.property).universally_isHomeomorph
  · change IsIso ((pullback.fst f Y.obj.hom).residueFieldMap z)
    refine isIso_residueFieldMap_of_comp _ f z inferInstance ?_
    rw [pullback.condition, Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso'
      (IsSeminormalizationCandidate.isIso_residueFieldMap Y.property
        ((pullback.snd f Y.obj.hom).base z)) inferInstance

namespace SeminormalizationCategory

/-- The base change of a seminormalization candidate over `X` along an open immersion `f : U ⟶ X`,
as an object of the seminormalization category of `U`. -/
noncomputable def restrict {U : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f]
    (Y : SeminormalizationCategory X) : SeminormalizationCategory U :=
  ⟨Over.mk (pullback.fst f Y.obj.hom), isSeminormalizationCandidate_pullback f Y⟩

variable {Y Z : SeminormalizationCategory X}

/-- Every morphism of the seminormalization category of `X` is a universal homeomorphism. -/
theorem universalHomeomorphism_hom_left (m : Y ⟶ Z) : UniversalHomeomorphism m.hom.left := by
  have hY : UniversalHomeomorphism (m.hom.left ≫ Z.obj.hom) := by
    rw [Over.w m.hom]
    exact IsSeminormalizationCandidate.universalHomeomorphism Y.property
  exact hasTwoOutOfThreeProperty_universalHomeomorphism.of_postcomp m.hom.left Z.obj.hom
    (IsSeminormalizationCandidate.universalHomeomorphism Z.property) hY

/-- Every morphism of the seminormalization category of `X` induces an isomorphism on the residue
field at every point. -/
theorem isIso_residueFieldMap_hom_left (m : Y ⟶ Z) (y : Y.obj.left) :
    IsIso (m.hom.left.residueFieldMap y) := by
  refine isIso_residueFieldMap_of_comp _ Z.obj.hom y
    (IsSeminormalizationCandidate.isIso_residueFieldMap Z.property _) ?_
  rw [Over.w m.hom]
  exact IsSeminormalizationCandidate.isIso_residueFieldMap Y.property y

end SeminormalizationCategory

end AlgebraicGeometry

end
