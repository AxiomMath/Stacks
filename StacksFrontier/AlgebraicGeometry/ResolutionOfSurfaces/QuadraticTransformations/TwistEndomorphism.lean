module

public import StacksFrontier.AlgebraicGeometry.InvertibleModuleEndomorphism
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.GlobalFunctions
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.ConormalDegreeOne

/-!
# A nonzero endomorphism of a twist on the projective line is an isomorphism

The step of [Stacks, Tag 0C5R] (Resolution of Surfaces, Lemma 54.17.1) treated in
`ConormalComparison.lean`, `DifferentialsVanishing.lean` and `ConormalDegreeOne.lean` of this
directory was carried out there under one hypothesis,
`Stacks.ResolutionOfSurfaces.NonzeroTwistEndoIsIso`: *for every `d`, a nonzero endomorphism of
the twist `𝒪(d)` on `𝐏¹_k` is an isomorphism*. This file **proves** that hypothesis, so the
results of those files become available with it discharged.

Two inputs do it. The twists on the projective line are invertible,
`AlgebraicGeometry.isInvertible_twistingSheaf_projectiveLineProj` (Equation 01MO, the polynomial
ring being generated in degree one), and the global functions on the projective line are the
ground field, `Stacks.ProjectiveSpace.Cohomology.coeffRingEquivGlobalSections` at `n = 1`
([Stacks, Tag 01XT] in degree zero). Joining them is
`Stacks.InvertibleEndomorphism.isIso_of_ne_zero_of_isInvertible_of_isField`: on a scheme whose
ring of global functions is a field, a nonzero endomorphism of an invertible module is an
isomorphism.

## Main results

All in the namespace `Stacks.ResolutionOfSurfaces`:

* `isField_sections_projectiveLineProj` — `Γ(𝐏¹_k, 𝒪)` is a field, being the ground field.
* `nonzeroTwistEndoIsIso` — **the carried hypothesis `NonzeroTwistEndoIsIso` is true.**
* `isIso_immersionConormalSheafMap_of_exceptionalCurvePair`,
  `isIso_conormalTransitivityMap_of_ne_zero_of_iso_projectiveLineTwist` and
  `isZero_pullback_relativeDifferentials_of_exceptionalCurveOfFirstKind` — the three consumers
  of that hypothesis, restated without it. The declarations in the other files of this directory
  are left untouched.

## What is and is not proved

Proved outright: the hypothesis `NonzeroTwistEndoIsIso`, and the three restatements.

Still carried by the last restatement, exactly as before:
`Stacks.ResolutionOfSurfaces.ConormalSequenceSecondArrow`, the second arrow of
[Stacks, Tag 067L] together with the two clauses of that tag which this library does not prove
(that the composite of the two arrows of the conormal sequence vanishes, and that the second
arrow is an epimorphism). It is quantified over every triangle of immersions of schemes and
mentions none of the objects of the conclusion; see the module documentation of
`DifferentialsVanishing.lean` for why it is carried existentially.

**No `@[stacks 0B40]` attribute is placed here**: part (5) of that tag is about two different
invertible modules on a proper integral curve and is formalized in
`StacksFrontier/AlgebraicGeometry/Variety/Curve/SectionDegree.lean`, while what is proved here is
the projective-line case needed by [Stacks, Tag 0C5R].

**No `@[stacks 0C5R]` attribute is placed here**: this is a step of the proof of that tag, not a
clause of its statement.

## References

* [Stacks Project, Tag 0C5R](https://stacks.math.columbia.edu/tag/0C5R)
* [Stacks Project, Tag 0B40](https://stacks.math.columbia.edu/tag/0B40)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 067L](https://stacks.math.columbia.edu/tag/067L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open RingedSpaceModuleAdjunction (toShHomIso)

universe u

namespace Stacks.ResolutionOfSurfaces

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### The global functions on the projective line form a field -/

/-- **`Γ(𝐏¹_k, 𝒪)` is a field.** The global functions on projective space over a ring are the
ring itself, through the structure morphism, by
`Stacks.ProjectiveSpace.Cohomology.coeffRingEquivGlobalSections`; at `n = 1` and over a field
that ring is the field. -/
public theorem isField_sections_projectiveLineProj (k : Type u) [Field k] :
    IsField Γ(projectiveLineProj k, ⊤) :=
  (Stacks.ProjectiveSpace.Cohomology.coeffRingEquivGlobalSections k
    1).symm.toMulEquiv.isField (Field.toIsField k)

/-! ### The carried hypothesis, discharged -/

/-- **A nonzero endomorphism of the twist `𝒪(d)` on `𝐏¹_k` is an isomorphism.** This is the
hypothesis `Stacks.ResolutionOfSurfaces.NonzeroTwistEndoIsIso` of `ConormalComparison.lean`,
proved: the twist is an invertible module and the global functions on the projective line are
the field `k`, so an endomorphism of the twist is multiplication by an element of `k` and a
nonzero element of a field is a unit. -/
public theorem nonzeroTwistEndoIsIso (k : Type u) [Field k] : NonzeroTwistEndoIsIso k :=
  fun d ψ hψ =>
    Stacks.InvertibleEndomorphism.isIso_of_ne_zero_of_isInvertible_of_isField
      (projectiveLineProj k) (isField_sections_projectiveLineProj k) (projectiveLineTwist k d)
      (isInvertible_twistingSheaf_projectiveLineProj k d) ψ hψ

/-! ### The consumers, restated without the hypothesis -/

/-- **The step of [Stacks, Tag 0C5R] at the conormal comparison map, unconditionally.** This is
`Stacks.ResolutionOfSurfaces.isIso_immersionConormalSheafMap_of_isExceptionalCurveOfFirstKind`
with its hypothesis `NonzeroTwistEndoIsIso` discharged: for two exceptional curves of the first
kind `E ⊆ X'` and `E' ⊆ Y'` with compatible presentations as `𝐏¹_k`, a morphism `g : E ⟶ E'` and
a morphism `f' : X' ⟶ Y'` making the square commute, the conormal comparison map
`g^* 𝒞_{E'/Y'} ⟶ 𝒞_{E/X'}` of [Stacks, Tag 01R4] is an isomorphism as soon as it is nonzero. -/
public theorem isIso_immersionConormalSheafMap_of_exceptionalCurvePair (k : Type u) [Field k]
    {X' Y' : Scheme.{u}} (f' : X' ⟶ Y') {D : X'.IdealSheafData} {D' : Y'.IdealSheafData}
    {e : projectiveLineProj k ≅ D.subscheme} {e' : projectiveLineProj k ≅ D'.subscheme}
    (hE : D.IsExceptionalCurveOfFirstKind k e) (hE' : D'.IsExceptionalCurveOfFirstKind k e')
    (g : D.subscheme ⟶ D'.subscheme) (he : e.hom ≫ g = e'.hom)
    (comm : D.subschemeι ≫ f' = g ≫ D'.subschemeι)
    (hne : Stacks.Immersion.immersionConormalSheafMap D.subschemeι D'.subschemeι g f'
      (Stacks.Immersion.toShHom_square comm) ≠ 0) :
    IsIso (Stacks.Immersion.immersionConormalSheafMap D.subschemeι D'.subschemeι g f'
      (Stacks.Immersion.toShHom_square comm)) :=
  isIso_immersionConormalSheafMap_of_isExceptionalCurveOfFirstKind k (nonzeroTwistEndoIsIso k)
    f' hE hE' g he comm hne

/-- **The first arrow of [Stacks, Tag 067L] is an isomorphism when it is nonzero and the two
conormal modules have the same degree on `𝐏¹_k`, unconditionally.** This is
`Stacks.ResolutionOfSurfaces.isIso_conormalTransitivityMap_of_ne_zero` with its hypothesis
`NonzeroTwistEndoIsIso` discharged. -/
public theorem isIso_conormalTransitivityMap_of_ne_zero_of_iso_projectiveLineTwist (k : Type u)
    [Field k] (d : ℤ) {E X' Y' : Scheme.{u}}
    (i : E ⟶ X') (j : E ⟶ Y') (f' : X' ⟶ Y') [IsImmersion i] [IsImmersion j]
    (h : i ≫ f' = j) (ε : projectiveLineProj k ≅ E)
    (α : (modulePullback (toShHomIso ε).hom).obj (Stacks.Conormal.conormalSheaf j) ≅
      projectiveLineTwist k d)
    (β : (modulePullback (toShHomIso ε).hom).obj (Stacks.Conormal.conormalSheaf i) ≅
      projectiveLineTwist k d)
    (hne : Stacks.ConormalSequenceTwoImmersions.conormalTransitivityMap i j f' h ≠ 0) :
    IsIso (Stacks.ConormalSequenceTwoImmersions.conormalTransitivityMap i j f' h) :=
  isIso_conormalTransitivityMap_of_ne_zero k (nonzeroTwistEndoIsIso k) d i j f' h ε α β hne

/-- **`i^* Ω_{X'/Y'} = 0` along the exceptional curve, with `NonzeroTwistEndoIsIso`
discharged.** This is
`Stacks.ResolutionOfSurfaces.isZero_pullback_relativeDifferentials_of_isExceptionalCurve` with
that hypothesis removed; the clauses of [Stacks, Tag 067L] gathered in
`Stacks.ResolutionOfSurfaces.ConormalSequenceSecondArrow` are still carried, since the library
does not prove them. -/
public theorem isZero_pullback_relativeDifferentials_of_exceptionalCurveOfFirstKind (k : Type u)
    [Field k] (hsec : ConormalSequenceSecondArrow.{u})
    {X' Y' : Scheme.{u}} (f' : X' ⟶ Y') {D : X'.IdealSheafData}
    {e : projectiveLineProj k ≅ D.subscheme} (hE : D.IsExceptionalCurveOfFirstKind k e)
    (j : D.subscheme ⟶ Y') [IsImmersion j] (h : D.subschemeι ≫ f' = j)
    (α : (modulePullback (toShHomIso e).hom).obj (Stacks.Conormal.conormalSheaf j) ≅
      projectiveLineTwist k 1)
    (hne : Stacks.ConormalSequenceTwoImmersions.conormalTransitivityMap D.subschemeι j f' h ≠ 0) :
    IsZero ((Scheme.Modules.pullback D.subschemeι).obj
      (Scheme.Hom.relativeDifferentials f')) :=
  isZero_pullback_relativeDifferentials_of_isExceptionalCurve k (nonzeroTwistEndoIsIso k) hsec
    f' hE j h α hne

end Stacks.ResolutionOfSurfaces

end
