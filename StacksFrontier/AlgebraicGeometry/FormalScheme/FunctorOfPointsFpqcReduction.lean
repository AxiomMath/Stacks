module

public import Mathlib.AlgebraicGeometry.Sites.SheafQuasiCompact
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsZariskiSheaf

/-!
# Reduction of the fpqc sheaf condition for the functor of points to one affine descent

Let `𝔛` be a formal scheme. Its functor of points is a sheaf for the big Zariski topology
(`AlgebraicGeometry.isSheaf_zariskiTopology_formalSchemePoints`) and is separated for the fpqc
topology (`AlgebraicGeometry.isSeparated_fpqcTopology_formalSchemePoints`). Together with
`AlgebraicGeometry.isSheaf_type_propQCTopology_iff`, this reduces the fpqc sheaf condition to a
single statement about one faithfully flat morphism of affine schemes.

The reduction is stated in two forms: `isSheaf_fpqcTopology_formalSchemePoints_of_affine` asks for
the full sheaf condition for the presieve `{Spec S ⟶ Spec R}`, and
`isSheaf_fpqcTopology_formalSchemePoints_of_exists_affine` asks only for *existence* of an
amalgamation, uniqueness being supplied by the separatedness already proved.

## Main results

* `AlgebraicGeometry.isSheafFor_singleton_of_exists_amalgamation`: for a faithfully flat morphism
  of affine schemes, the sheaf condition for the one-element presieve follows from existence of
  amalgamations alone.
* `AlgebraicGeometry.isSheaf_fpqcTopology_formalSchemePoints_of_affine` and
  `AlgebraicGeometry.isSheaf_fpqcTopology_formalSchemePoints_of_exists_affine`: the functor of
  points is an fpqc sheaf as soon as a point over `Spec S` with matching pullbacks descends along
  one faithfully flat `Spec S ⟶ Spec R`.

## References

* [Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
* [Stacks Project, Tag 022H](https://stacks.math.columbia.edu/tag/022H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- For a faithfully flat morphism of affine schemes, the fpqc sheaf condition for the functor of
points of a formal scheme on the one-element presieve it generates reduces to the existence of
amalgamations. -/
theorem isSheafFor_singleton_of_exists_amalgamation (X : FormalScheme.{u})
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (hflat : Flat (Spec.map φ))
    (hsurj : Surjective (Spec.map φ))
    (hex : ∀ x : Presieve.FamilyOfElements (formalSchemePoints X)
        (Presieve.singleton (Spec.map φ)), x.Compatible → ∃ t, x.IsAmalgamation t) :
    Presieve.IsSheafFor (formalSchemePoints X) (Presieve.singleton (Spec.map φ)) := by
  have := hsurj
  refine Presieve.IsSeparatedFor.isSheafFor ?_ hex
  rw [Presieve.isSeparatedFor_iff_generate]
  intro x t₁ t₂ h₁ h₂
  exact isSeparated_fpqcTopology_formalSchemePoints X _
    (Scheme.Hom.generate_singleton_mem_propQCTopology (P := @Flat) (Spec.map φ) hflat)
    x t₁ t₂ h₁ h₂

/-- **The fpqc sheaf condition for the functor of points, reduced to one affine descent.** If a
point of the formal scheme `𝔛` over `Spec S` whose two pullbacks agree descends along every
faithfully flat `Spec S ⟶ Spec R`, then the functor of points of `𝔛` is a sheaf for the fpqc
topology. -/
theorem isSheaf_fpqcTopology_formalSchemePoints_of_affine (X : FormalScheme.{u})
    (haff : ∀ {R S : CommRingCat.{u}} (φ : R ⟶ S), Flat (Spec.map φ) →
      Surjective (Spec.map φ) →
      Presieve.IsSheafFor (formalSchemePoints X) (Presieve.singleton (Spec.map φ))) :
    Presieve.IsSheaf Scheme.fpqcTopology.{u} (formalSchemePoints X) :=
  have : IsZariskiLocalAtSource (@Flat : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  (isSheaf_type_propQCTopology_iff (P := (@Flat : MorphismProperty Scheme.{u}))
    (formalSchemePoints X)).mpr
      ⟨isSheaf_zariskiTopology_formalSchemePoints X, fun φ hf hs => haff φ hf hs⟩

/-- **The fpqc sheaf condition for the functor of points, reduced to one affine descent,
existence only.** The functor of points of a formal scheme is an fpqc sheaf as soon as, for every
faithfully flat morphism `Spec S ⟶ Spec R` of affine schemes, a compatible family of points over
`Spec S` admits *some* amalgamation over `Spec R`. -/
theorem isSheaf_fpqcTopology_formalSchemePoints_of_exists_affine (X : FormalScheme.{u})
    (hex : ∀ {R S : CommRingCat.{u}} (φ : R ⟶ S), Flat (Spec.map φ) →
      Surjective (Spec.map φ) →
      ∀ x : Presieve.FamilyOfElements (formalSchemePoints X)
        (Presieve.singleton (Spec.map φ)), x.Compatible → ∃ t, x.IsAmalgamation t) :
    Presieve.IsSheaf Scheme.fpqcTopology.{u} (formalSchemePoints X) :=
  isSheaf_fpqcTopology_formalSchemePoints_of_affine X fun φ hf hs =>
    isSheafFor_singleton_of_exists_amalgamation X φ hf hs (hex φ hf hs)

end AlgebraicGeometry

end
