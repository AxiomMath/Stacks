module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionChartBaseChangeDense
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureMap
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsMap

/-!
# The inverse-image form of the structure map of a closed immersion is locally surjective

Let `f : X ⟶ Y` be a closed immersion of algebraic spaces over a scheme `S`.  The surjectivity
clause of [Stacks Project, Tag 03MB] says that the structure map `f^♯ : 𝒪_Y ⟶ f_*𝒪_X` is locally
surjective on the small étale site of `Y`; that is
`AlgebraicGeometry.Space.isLocallySurjective_structureSharp`.  This file proves the same for the
*inverse-image* form `f^♯ : f^{-1}𝒪_Y ⟶ 𝒪_X` on the small étale site of `X`.

The two forms are adjunct: the transpose of the inverse-image form along `f^{-1} ⊣ f_*` is the
direct-image form, and the transpose is the unit of the adjunction followed by the direct image
of the inverse-image form.  The direct-image form is an epimorphism, so the direct image of the
inverse-image form is one too, being the second factor of an epimorphism; and for a closed
immersion the direct image is fully faithful by [Stacks Project, Tag 04E5], part (1), so it is
faithful and therefore reflects epimorphisms.  On a site with sheafification an epimorphism of
sheaves of sets is locally surjective, which closes the circle.

This is the hypothesis `hsharp` carried by the statements of
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsImmersion.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceDifferentialsEpi.lean`, discharged for a
closed immersion.  Those statements quantify the hypothesis over all *immersions*, which this
file does not reach: the reduction of an immersion to a closed immersion is Stacks 04CE and
06EC, which this development does not carry — the same gap the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModule.lean` record.

## Main results

* `AlgebraicGeometry.Space.isLocallySurjective_structureSharpSet`: the direct-image form of the
  structure map is locally surjective on underlying sheaves of sets.
* `AlgebraicGeometry.Space.epi_structureSharpInverseImageSet`: the inverse-image form is an
  epimorphism of sheaves of sets.
* `AlgebraicGeometry.Space.isLocallySurjective_structureSharpInverseImageSet` and
  `AlgebraicGeometry.Space.isLocallySurjective_structureSharpInverseImage`: **the surjectivity
  clause of [Stacks Project, Tag 03MB] in inverse-image form**, on sheaves of sets and on
  sheaves of commutative rings.

## Implementation notes

**Why local surjectivity is transported by hand between coefficient categories.**  A morphism
of sheaves valued in a concrete category is locally surjective when the image sieve of each
section is covering, and the image sieve only sees the underlying function.  The structure maps
of sheaves of commutative rings, of rings and of sets at the same morphism of algebraic spaces
have the same components, so each local surjectivity statement is the other one with the
coefficient category changed, and the transport is `CategoryTheory.Presheaf.imageSieve_mem`
applied to the same section.  This is the pattern of
`Stacks.Sites.isLocallySurjective_addGroupSheafMap` in
`StacksFrontier/AlgebraicGeometry/Spaces/LiftDifferenceDescent.lean`.

**Why the argument runs through epimorphisms and not through covers.**  A direct proof would
choose, for a chart `V` of `X` and a section of `𝒪_X` over it, a cover of `V` by charts base
changed from `Y` on which the section lifts — that is, it would redo the cover-density argument
of [Stacks Project, Tag 04E5].  Taking epimorphisms instead uses that argument once, in the
shape in which this development already has it:
`AlgebraicGeometry.Space.fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion`.  Reflecting the
epimorphism along the faithful direct image is what replaces the choice of cover; the unit of
the adjunction is used only to exhibit the direct-image form as a composite, by
`CategoryTheory.Adjunction.homEquiv_unit`.

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
* [Stacks Project, Tag 05Z9](https://stacks.math.columbia.edu/tag/05Z9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **The direct-image form of the structure map of a closed immersion is locally surjective on
underlying sheaves of sets.**  Local surjectivity only sees the underlying function, so this is
the surjectivity clause of [Stacks Project, Tag 03MB],
`AlgebraicGeometry.Space.isLocallySurjective_structureSharp`, with the ring operations
forgotten. -/
theorem isLocallySurjective_structureSharpSet (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) :
    Sheaf.IsLocallySurjective (structureSharpSet B S hS f) :=
  have := isLocallySurjective_structureSharp B S hS f hf
  { imageSieve_mem := fun {_V} y =>
      Presheaf.imageSieve_mem (SmallEtale.topology B S hS Y.1)
        (structureSharp B S hS f).hom y }

/-- The direct-image form of the structure map of a closed immersion is an epimorphism of
sheaves of sets. -/
theorem epi_structureSharpSet (f : X ⟶ Y) (hf : IsClosedImmersion B S hS f.hom) :
    Epi (structureSharpSet B S hS f) :=
  have := isLocallySurjective_structureSharpSet B S hS f hf
  inferInstance

/-- **The inverse-image form of the structure map of a closed immersion is an epimorphism.**
Its transpose along `f^{-1} ⊣ f_*` is the direct-image form, which is an epimorphism; so the
direct image of the inverse-image form is an epimorphism, being the second factor of one.  For
a closed immersion the direct image is faithful by [Stacks Project, Tag 04E5], part (1), hence
reflects epimorphisms. -/
theorem epi_structureSharpInverseImageSet (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) :
    Epi (structureSharpInverseImageSet B S hS f) := by
  have hepi : Epi ((smallEtaleRingedToposHom B S hS f).toToposHom.adj.homEquiv
      (structureSetSheaf B S hS Y) (structureSetSheaf B S hS X)
      (structureSharpInverseImageSet B S hS f)) := by
    rw [homEquiv_structureSharpInverseImageSet]
    exact epi_structureSharpSet B S hS f hf
  rw [Adjunction.homEquiv_unit] at hepi
  have hmap : Epi ((smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map
      (structureSharpInverseImageSet B S hS f)) :=
    epi_of_epi ((smallEtaleRingedToposHom B S hS f).toToposHom.adj.unit.app
      (structureSetSheaf B S hS Y)) _
  have : (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.Faithful :=
    (fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion B S hS f hf).faithful
  exact (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.epi_of_epi_map hmap

/-- **The surjectivity clause of [Stacks Project, Tag 03MB] in inverse-image form**, on sheaves
of sets: for a closed immersion `f : X ⟶ Y` of algebraic spaces the structure map
`f^♯ : f^{-1}𝒪_Y ⟶ 𝒪_X` is locally surjective on the small étale site of `X`. -/
theorem isLocallySurjective_structureSharpInverseImageSet (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) :
    Sheaf.IsLocallySurjective (structureSharpInverseImageSet B S hS f) :=
  have := epi_structureSharpInverseImageSet B S hS f hf
  (Sheaf.isLocallySurjective_iff_epi (structureSharpInverseImageSet B S hS f)).2 inferInstance

/-- **The surjectivity clause of [Stacks Project, Tag 03MB] in inverse-image form.**  For a
closed immersion `f : X ⟶ Y` of algebraic spaces over `S` the structure map
`f^♯ : f^{-1}𝒪_Y ⟶ 𝒪_X` of [Stacks Project, Tag 03G8] is locally surjective on the small étale
site of `X`.

This is the hypothesis `hsharp` of
`AlgebraicGeometry.Space.isZero_sheafOfDifferentials_of_isImmersion` and of the statements of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceDifferentialsEpi.lean`, discharged in the
closed case. -/
theorem isLocallySurjective_structureSharpInverseImage (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) :
    Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X.1)
      (structureSharpInverseImage B S hS f).hom :=
  have := isLocallySurjective_structureSharpInverseImageSet B S hS f hf
  { imageSieve_mem := fun {_V} y =>
      Presheaf.imageSieve_mem (SmallEtale.topology B S hS X.1)
        (structureSharpInverseImageSet B S hS f).hom y }

end AlgebraicGeometry.Space

end
