module

public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealZeroLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated

/-!
# The situation for descending the resolution property

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S`.  The
section of the source on the resolution property works throughout with a fixed collection
of choices attached to `X`: an affine scheme `V` with a surjective étale morphism
`φ : V → X`, a factorization of `φ` as an open immersion `j : V → Y` into an algebraic
space followed by a finite morphism `π : Y → X`, and a finite type quasi-coherent sheaf of
ideals `ℐ ⊆ 𝒪_Y` whose zero locus is the complement `|Y| ∖ |j(V)|`.

This file records that collection of choices, together with the one existence assertion the
source makes which the library can discharge: a quasi-compact algebraic space does admit an
affine surjective étale chart.

## Main definitions

* `AlgebraicGeometry.Space.ResolutionPropertyDescentSituation` is the data chosen in the
  situation of the source, with all the conditions imposed on it.

## Main results

* `AlgebraicGeometry.Space.exists_affine_isSurjective_isEtale_of_isQuasiCompactSpace` is the
  parenthetical existence claim of the source for the chart `V → X`: it is Stacks 03H6 in
  the point-set spelling of surjectivity.

## Implementation notes

Quasi-compactness and quasi-separatedness of `X` are *parameters* of the structure, not
fields, because they are the hypotheses the source places on `X` before any choice is made;
a term of the structure therefore cannot be formed without them.  Everything the source
*chooses* — `V`, `φ`, `Y`, `j`, `π` and `ℐ` — is a field, and every condition the source
imposes on those choices is a field as well, so nothing of the situation's own content is
left to a hypothesis of a client.

Quasi-separatedness is the absolute form of Stacks 03BS, part (3), which is stated over the
terminal scheme and hence takes the containment of that scheme in the site as a parameter.

Surjectivity of `φ` is `AlgebraicGeometry.Space.IsSurjective`, the point-set notion of
Stacks 03ME, which is what the source means by a surjective morphism of algebraic spaces.
Stacks 03H6 produces a chart surjective in the sense that every represented base change of
it is a surjective morphism of schemes; the two agree for a morphism into an algebraic space
by Stacks 03H5, and the existence result below performs that translation.

The sheaf of ideals is a sheaf submodule of the unit module of `𝒪_Y` on the small étale site
of `Y`, the form taken by `AlgebraicGeometry.Space.definingIdealSheaf`, and being a finite
type quasi-coherent sheaf of ideals is
`AlgebraicGeometry.Space.IsFiniteTypeQuasicoherentIdeal`, which is Stacks 03DL(6) together
with Stacks 03DL(5) for the associated module.  Its zero locus is the point set
`AlgebraicGeometry.Space.idealZeroLocus`, namely `|V(ℐ)|` taken as a primitive; the closed
subspace `V(ℐ)` itself is not available, and the condition of the source refers only to the
point set.

The other two existence claims the source makes in parentheses are *not* discharged here,
because neither of their inputs is in the library: the factorization `V → Y → X` is
Zariski's Main Theorem for algebraic spaces, Stacks 082K, and the sheaf of ideals is part
(3) of Stacks 0855.  Part (3) **is** available: with parts (1) and (2), the implication
(2) ⟹ (3) is proved unconditionally as
`AlgebraicGeometry.Space.hasFiniteTypeQuasicoherentIdealZeroLocus_of_isQuasiCompactSpace`
in `StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeIdealOfQuasiCompactOpen`, for `X`
quasi-compact and absolutely quasi-separated and `U` a quasi-compact open subspace — which
are exactly the hypotheses of this situation.  So the only missing input for inhabiting the
structure is Stacks 082K, and no inhabitation statement is claimed here for that reason
alone.

### No `@[stacks 03H6]` and no `@[stacks 03H5]` here

The existence result below carries only `@[stacks 0GUY]`, as the parenthetical claim of that
tag.  It is Stacks 03H6 read through Stacks 03H5, and both of those tags already sit on
their general forms,
`AlgebraicGeometry.Space.isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover` and
`AlgebraicGeometry.Space.presheafSurjective_iff_isSurjective_yoneda`; a second copy of
either tag here would claim they are proved twice.

## References

* [Stacks Project, Tag 0GUY](https://stacks.math.columbia.edu/tag/0GUY)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03H5](https://stacks.math.columbia.edu/tag/03H5)
* [Stacks Project, Tag 0855](https://stacks.math.columbia.edu/tag/0855)
* [Stacks Project, Tag 082K](https://stacks.math.columbia.edu/tag/082K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

attribute [local instance] pointTopology

/-- **Stacks 0GUY, the existence of the chart `V → X`.** A quasi-compact algebraic space over
`S` admits a surjective étale morphism from an affine scheme of the site, surjectivity being
the point-set notion of Stacks 03ME.

This is the parenthetical claim of the source that such a chart exists: Stacks 03H6 gives a
chart whose every represented base change is a surjective morphism of schemes, and Stacks
03H5 identifies that with surjectivity on points. -/
@[stacks 0GUY "the existence of the affine surjective étale chart of the situation"]
theorem exists_affine_isSurjective_isEtale_of_isQuasiCompactSpace
    (X : AlgebraicSpaces B S hS) (hX : IsQuasiCompactSpace B S hS X.1) :
    ∃ (V : BigFppfOver B S hS) (φ : yoneda.obj V ⟶ X.1),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
        IsSurjective B S hS φ ∧ IsEtale B S hS φ := by
  obtain ⟨V, φ, haffine, hsurjective, hetale⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X.1 X.2).1 hX
  exact ⟨V, φ, haffine,
    (presheafSurjective_iff_isSurjective_yoneda B S hS X.1 X.2 V φ).1 hsurjective, hetale⟩

/-- **Stacks 0GUY.** The choices fixed in the situation of the source for a quasi-compact and
quasi-separated algebraic space `X` over `S`: an affine scheme `V` of the site with a
surjective étale morphism `φ : V → X`, a factorization of `φ` into an open immersion
`j : V → Y` into an algebraic space `Y` followed by a finite morphism `π : Y → X`, and a
finite type quasi-coherent sheaf of ideals `ℐ ⊆ 𝒪_Y` with `|V(ℐ)| = |Y| ∖ |j(V)|`.

A chart `V` as in the first clause exists by
`AlgebraicGeometry.Space.exists_affine_isSurjective_isEtale_of_isQuasiCompactSpace`. -/
@[stacks 0GUY "the data chosen in the situation, and the conditions imposed on it"]
structure ResolutionPropertyDescentSituation (X : AlgebraicSpaces B S hS)
    (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) where
  /-- The scheme of the site covering `X`. -/
  V : BigFppfOver B S hS
  /-- It is an affine scheme. -/
  isAffine_V : IsAffine ((BigFppfOver.toScheme B S hS).obj V)
  /-- The chosen morphism `φ : V → X`. -/
  φ : yoneda.obj V ⟶ X.1
  /-- It is surjective, in the point-set sense of Stacks 03ME. -/
  isSurjective_φ : IsSurjective B S hS φ
  /-- It is étale. -/
  isEtale_φ : IsEtale B S hS φ
  /-- The algebraic space through which `φ` is factored. -/
  Y : AlgebraicSpaces B S hS
  /-- The chosen morphism `j : V → Y`. -/
  j : yoneda.obj V ⟶ Y.1
  /-- The chosen morphism `π : Y → X`. -/
  π : Y.1 ⟶ X.1
  /-- `j` is an open immersion. -/
  isOpenImmersion_j : IsOpenImmersion B S hS j
  /-- `π` is a finite morphism of algebraic spaces. -/
  isFinite_π : IsFinite B S hS π
  /-- The triangle commutes: `π ∘ j = φ`. -/
  comp_eq : j ≫ π = φ
  /-- The chosen sheaf of ideals `ℐ ⊆ 𝒪_Y`. -/
  I : (SheafOfModules.unit (structureRingSheaf B S hS Y)).Submodule
  /-- `ℐ` is quasi-coherent and of finite type. -/
  isFiniteTypeQuasicoherent_I : IsFiniteTypeQuasicoherentIdeal B S hS Y I
  /-- Its zero locus is the complement of the image of `j`: `|V(ℐ)| = |Y| ∖ |j(V)|`. -/
  idealZeroLocus_I :
    idealZeroLocus B S hS Y I = (Set.range (pointsMap B S hS (yoneda.obj V) j))ᶜ

end AlgebraicGeometry.Space

end
