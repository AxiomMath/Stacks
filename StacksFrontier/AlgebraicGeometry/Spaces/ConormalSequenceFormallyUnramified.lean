module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceDifferentials
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceDifferentialsEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningDifferentials
import StacksCore.Tactic.StacksAttribute

/-!
# The conormal sequence of a formally unramified morphism of algebraic spaces

Let `B` be a big fppf site over a scheme `S`, let `Y` be an algebraic space (the base `B` of the
source; the letter `B` is taken here by the site, as in
`StacksFrontier/AlgebraicGeometry/Spaces/UniversalThickeningDifferentials.lean`), and let
`h : Z ⟶ X` be a formally unramified morphism of algebraic spaces over `Y`.  Stacks 060F
attaches to it a canonical exact sequence
```
  𝒞_{Z/X} ⟶ h^*Ω_{X/Y} ⟶ Ω_{Z/Y} ⟶ 0
```
of sheaves of `𝒪_Z`-modules on the small étale site of `Z`, whose first arrow is induced by
`d_{Z'/Y}`, where `Z ⊂ Z'` is the universal first order neighbourhood of `Z` over `X`.

The proof of the source is one line: the sequence of Stacks 05ZA for the closed subspace
`Z ⊂ Z'` over `Y`,
```
  𝒞_{Z/Z'} ⟶ ι^*Ω_{Z'/Y} ⟶ Ω_{Z/Y} ⟶ 0,
```
is carried onto the displayed one by the isomorphism `h^*Ω_{X/Y} ≅ ι^*Ω_{Z'/Y}` of Stacks 060E.
Its two terms on the left are the same objects: `𝒞_{Z/X}` *is* `𝒞_{Z/Z'}` by the definition of
Stacks 0607, part (2).  So the content of this tag is exactly that transport, and that is what is
proved below.

## How the situation is presented

As in `UniversalThickeningDifferentials.lean`, the datum is a universal first order thickening
`hZ : AlgebraicGeometry.Space.IsUniversalFirstOrderThickening B S hS Z h'` of a subfunctor `Z` of
an algebraic space `Z'` over a structure morphism `h' : Z' ⟶ X`, rather than a formally unramified
`h : Z ⟶ X` together with a thickening produced for it.  The morphism `h` of the source is then
not a separate datum: it is `ι ≫ h'`, where `ι` is
`AlgebraicGeometry.Space.universalThickeningInclusion`.  Formal unramifiedness of `h'` follows
from `hZ` by Stacks 0609,
`AlgebraicGeometry.Space.formallyUnramified_of_isUniversalFirstOrderThickening`, so nothing is
assumed that the source does not have; and `AlgebraicGeometry.Space.UniversalFirstOrderThickening`
of Stacks 0607 — which packages a formally unramified `h` with such a thickening and an
identification `Z ≅ Z ⊂ Z'` — instantiates the statements below through its `isUniversal` field,
its `closedSub` being exactly `AlgebraicGeometry.Space.thickeningClosedSubspace` of that field.

The middle term is read, as Stacks 060E reads it, as the double inverse image
`ι^*(h')^*Ω_{X/Y}`; that is `h^*Ω_{X/Y}` through `ι ≫ h' = h` and the comparison
`AlgebraicGeometry.Space.modulePullbackCompIso` of Stacks 03LU.  Stating the sequence with the
double inverse image is the reading under which Stacks 060E itself is proved, so the two compose
with no comparison isomorphism in between.

## Main definitions

* `AlgebraicGeometry.Space.thickeningClosedSubspace`: the smaller space of a universal first
  order thickening, as a closed subspace of the ambient space, which is the form the conormal
  module of Stacks 04CN and the first arrow of Stacks 05ZA consume.
* `AlgebraicGeometry.Space.thickeningConormalFirstMap`: the first arrow `𝒞_{Z/Z'} ⟶ h^*Ω_{X/Y}`
  of the sequence of Stacks 060F: the first arrow of Stacks 05ZA for the closed subspace `Z ⊂ Z'`
  over `Y`, followed by the inverse of the isomorphism of Stacks 060E.
* `AlgebraicGeometry.Space.thickeningConormalSecondMap`: the second arrow
  `h^*Ω_{X/Y} ⟶ Ω_{Z/Y}`: the isomorphism of Stacks 060E followed by the second arrow of
  Stacks 05ZA, which is the comparison map `AlgebraicGeometry.Space.pullbackDifferentialsMap` of
  Stacks 04CX.

## Main results

* `AlgebraicGeometry.Space.thickeningConormalFirstMap_comp_thickeningSheafOfDifferentialsMap`:
  composed with the isomorphism of Stacks 060E, the first arrow is the first arrow of Stacks 05ZA
  for `Z ⊂ Z'` over `Y`, which is induced by `d_{Z'/Y}` by
  `AlgebraicGeometry.Space.conormalSequenceIdealDifferential_val_app_apply`.
* `AlgebraicGeometry.Space.epi_thickeningConormalSecondMap`: the second arrow is an epimorphism
  whenever `ι♯ : ι⁻¹𝒪_{Z'} ⟶ 𝒪_Z` is locally surjective.
* `AlgebraicGeometry.Space.thickeningConormalSequence_exact`: the composite of the two arrows is
  zero and the short complex is exact at the middle term whenever the same holds for the sequence
  of Stacks 05ZA at `Z ⊂ Z'`; this is the transport across the isomorphism of Stacks 060E.

These lemmas take the isomorphism of Stacks 060E, and the clauses of Stacks 05ZA they transport,
as arguments, so that they can be applied to any realization of them.  All of these inputs are
proved in this library: the isomorphism of Stacks 060E is
`AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.isIso_thickeningSheafOfDifferentialsMap`,
the composite of Stacks 05ZA is zero by
`AlgebraicGeometry.Space.conormalSequenceFirstMap_comp_pullbackDifferentialsMap`, its exactness
in the middle is `AlgebraicGeometry.Space.exact_conormalSequence`, and the local surjectivity of
`ι♯` is `AlgebraicGeometry.Space.isLocallySurjective_structureSharpInverseImage`.  They are
assembled into the full statement of Stacks 060F, with no hypothesis beyond the universal first
order thickening, in
`AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.exists_conormalSequence_exact` of
`StacksFrontier/AlgebraicGeometry/Spaces/FormallyUnramifiedConormalSequence.lean`.

## References

* [Stacks Project, Tag 060F](https://stacks.math.columbia.edu/tag/060F)
* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA), the conormal sequence of
  an immersion, which this one is transported from.
* [Stacks Project, Tag 060E](https://stacks.math.columbia.edu/tag/060E), the isomorphism
  `h^*Ω_{X/Y} ≅ Ω_{Z'/Y} ⊗ 𝒪_Z` along which it is transported.
* [Stacks Project, Tag 0607](https://stacks.math.columbia.edu/tag/0607), the universal first
  order neighbourhood and the conormal sheaf `𝒞_{Z/X}` of a formally unramified morphism.
* [Stacks Project, Tag 0602](https://stacks.math.columbia.edu/tag/0602), the universal property.
* [Stacks Project, Tag 0609](https://stacks.math.columbia.edu/tag/0609), formal unramifiedness of
  the structure morphism of a universal first order thickening.
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN), the conormal module.
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX), the comparison map, which
  the second arrow is an instance of.
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB), whose surjectivity clause
  is, in inverse-image form, the argument `hsharp`.
-/

@[expose] public section

open CategoryTheory
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z' : AlgebraicSpaces B S hS} {Z : Subfunctor Z'.obj} {h' : Z' ⟶ X}

/-! ### The smaller space of the thickening as a closed subspace -/

/-- The smaller space of a universal first order thickening `Z ⊂ Z'`, read as a closed subspace
of `Z'`: a first-order thickening is in particular a thickening, by Stacks 05ZK, and a thickening
is in particular a closed subspace.

This is the shape in which the conormal module `𝒞_{Z/Z'}` of Stacks 04CN and the first arrow of
Stacks 05ZA take the subspace, whereas
`AlgebraicGeometry.Space.universalThickeningSubSpace` presents the same subfunctor as an
algebraic space; the inclusion `AlgebraicGeometry.Space.subspaceInclusion` of the former and
`AlgebraicGeometry.Space.universalThickeningInclusion` of the latter are the same morphism
`ObjectProperty.homMk Z.ι`.  It agrees with the `closedSub` field of
`AlgebraicGeometry.Space.UniversalFirstOrderThickening` of Stacks 0607. -/
abbrev thickeningClosedSubspace (hZ : IsUniversalFirstOrderThickening B S hS Z h') :
    ClosedSubspaces B S hS Z'.obj :=
  ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩

/-! ### The two arrows of the sequence of Stacks 060F -/

/-- The canonical first arrow `𝒞_{Z/X} ⟶ h^*Ω_{X/Y}` of the sequence of Stacks 060F.

The source `𝒞_{Z/X}` is the conormal module `𝒞_{Z/Z'}` of the closed subspace `Z ⊂ Z'`, which is
what Stacks 0607, part (2) defines `𝒞_{Z/X}` to be; the target `h^*Ω_{X/Y}` is read as the double
inverse image `ι^*(h')^*Ω_{X/Y}`, as in Stacks 060E.  The arrow is the first arrow
`AlgebraicGeometry.Space.conormalSequenceFirstMap` of Stacks 05ZA for `Z ⊂ Z'` over `Y`, followed
by the inverse of the isomorphism `AlgebraicGeometry.Space.thickeningSheafOfDifferentialsMap` of
Stacks 060E.

The argument `he` is that isomorphism, which
`AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.isIso_thickeningSheafOfDifferentialsMap`
supplies. -/
noncomputable def thickeningConormalFirstMap
    (hZ : IsUniversalFirstOrderThickening B S hS Z h') (p : X ⟶ Y)
    (he : IsIso (thickeningSheafOfDifferentialsMap B S hS hZ p)) :
    conormalModule B S hS Z' (thickeningClosedSubspace B S hS hZ) ⟶
      (modulePullback B S hS (universalThickeningInclusion B S hS hZ)).obj
        ((modulePullback B S hS h').obj (sheafOfDifferentials B S hS p)) :=
  have : IsIso (thickeningSheafOfDifferentialsMap B S hS hZ p) := he
  conormalSequenceFirstMap B S hS (thickeningClosedSubspace B S hS hZ) (h' ≫ p) ≫
    inv (thickeningSheafOfDifferentialsMap B S hS hZ p)

/-- The second arrow of the sequence of Stacks 060F, `h^*Ω_{X/Y} ⟶ Ω_{Z/Y}`: the isomorphism
`AlgebraicGeometry.Space.thickeningSheafOfDifferentialsMap` of Stacks 060E followed by the second
arrow `AlgebraicGeometry.Space.pullbackDifferentialsMap` of Stacks 05ZA for `Z ⊂ Z'` over `Y`.

Stacks 060F constructs no arrow here, and neither does this definition: the second arrow of
Stacks 05ZA is already the comparison map of Stacks 04CX, registered under that tag in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceSecondMap.lean`, and all that is done here
is to read its source as `h^*Ω_{X/Y}` across the identification of Stacks 060E. -/
noncomputable def thickeningConormalSecondMap
    (hZ : IsUniversalFirstOrderThickening B S hS Z h') (p : X ⟶ Y) :
    (modulePullback B S hS (universalThickeningInclusion B S hS hZ)).obj
        ((modulePullback B S hS h').obj (sheafOfDifferentials B S hS p)) ⟶
      sheafOfDifferentials B S hS (universalThickeningInclusion B S hS hZ ≫ (h' ≫ p)) :=
  thickeningSheafOfDifferentialsMap B S hS hZ p ≫
    pullbackDifferentialsMap B S hS (universalThickeningInclusion B S hS hZ) (h' ≫ p)

/-! ### The first arrow is induced by `d_{Z'/Y}` -/

/-- The first arrow of the sequence of Stacks 060F is induced by `d_{Z'/Y}`.  Composed with the
isomorphism of Stacks 060E, the first arrow is the first arrow of Stacks 05ZA for the closed
subspace `Z ⊂ Z'` over `Y`; and that arrow is induced by `d_{Z'/Y}` in the sense of
`AlgebraicGeometry.Space.conormalSequenceIdealDifferential_val_app_apply`, namely its transpose
across `ι^* ⊣ ι_*` carries a section of the defining ideal sheaf of `Z` to the universal
differential `d_{Z'/Y}` of that section followed by the unit of the adjunction.

Since the map of Stacks 060E is an isomorphism, this equation determines the first arrow, so it
is the whole of that arrow's dependence on `d_{Z'/Y}`.  It holds by construction — it is the
defining equation of `AlgebraicGeometry.Space.thickeningConormalFirstMap`, recorded so that
consumers may rewrite with it rather than unfold the definition, as
`AlgebraicGeometry.Space.conormalModule_eq` and
`AlgebraicGeometry.Space.conormalSheaf_eq` are for their definitions; what carries the
mathematical content of the clause is the Stacks 05ZA statement it defers to. -/
theorem thickeningConormalFirstMap_comp_thickeningSheafOfDifferentialsMap
    (hZ : IsUniversalFirstOrderThickening B S hS Z h') (p : X ⟶ Y)
    (he : IsIso (thickeningSheafOfDifferentialsMap B S hS hZ p)) :
    thickeningConormalFirstMap B S hS hZ p he ≫
        thickeningSheafOfDifferentialsMap B S hS hZ p =
      conormalSequenceFirstMap B S hS (thickeningClosedSubspace B S hS hZ) (h' ≫ p) := by
  have : IsIso (thickeningSheafOfDifferentialsMap B S hS hZ p) := he
  simp [thickeningConormalFirstMap]

/-! ### Exactness at the right term -/

/-- Exactness at the right term of the sequence of Stacks 060F: the second arrow
`h^*Ω_{X/Y} ⟶ Ω_{Z/Y}` is an epimorphism, so the sequence ends in zero.

It is the isomorphism of Stacks 060E followed by the second arrow of Stacks 05ZA, and the latter
is an epimorphism by `AlgebraicGeometry.Space.epi_pullbackDifferentialsMap_of_isLocallySurjective`
under local surjectivity of `ι♯`, which is the argument `hsharp` passed straight through; it is
supplied by `AlgebraicGeometry.Space.isLocallySurjective_structureSharpInverseImage`. -/
theorem epi_thickeningConormalSecondMap
    (hZ : IsUniversalFirstOrderThickening B S hS Z h') (p : X ⟶ Y)
    (he : IsIso (thickeningSheafOfDifferentialsMap B S hS hZ p))
    (hsharp : Presheaf.IsLocallySurjective
      (SmallEtale.topology B S hS (universalThickeningSubSpace B S hS hZ).obj)
      (structureSharpInverseImage B S hS (universalThickeningInclusion B S hS hZ)).hom) :
    Epi (thickeningConormalSecondMap B S hS hZ p) := by
  have : IsIso (thickeningSheafOfDifferentialsMap B S hS hZ p) := he
  exact epi_comp' (IsIso.epi_of_iso _)
    (epi_pullbackDifferentialsMap_of_isLocallySurjective B S hS
      (universalThickeningInclusion B S hS hZ) (h' ≫ p) hsharp)

/-! ### The composite is zero, and exactness at the middle term -/

/-- The composite of the two arrows of the sequence of Stacks 060F is zero, and the resulting
short complex `𝒞_{Z/X} ⟶ h^*Ω_{X/Y} ⟶ Ω_{Z/Y}` is exact at the middle term, provided the same
two clauses hold for the sequence of Stacks 05ZA at the closed subspace `Z ⊂ Z'` over `Y`.

This is the transport the source's proof performs.  The short complex of the conclusion is
isomorphic to the short complex of Stacks 05ZA, by the identity on the two outer terms and the
isomorphism of Stacks 060E on the middle one, so `CategoryTheory.ShortComplex.exact_iff_of_iso`
transfers exactness.  Both clauses of Stacks 05ZA are proved in this library
(`AlgebraicGeometry.Space.conormalSequenceFirstMap_comp_pullbackDifferentialsMap` and
`AlgebraicGeometry.Space.exact_conormalSequence`), and are applied to this lemma in
`AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.exists_conormalSequence_exact`. -/
theorem thickeningConormalSequence_exact
    (hZ : IsUniversalFirstOrderThickening B S hS Z h') (p : X ⟶ Y)
    (he : IsIso (thickeningSheafOfDifferentialsMap B S hS hZ p))
    (hzero : conormalSequenceFirstMap B S hS (thickeningClosedSubspace B S hS hZ) (h' ≫ p) ≫
      pullbackDifferentialsMap B S hS (universalThickeningInclusion B S hS hZ) (h' ≫ p) = 0)
    (h05ZA : (ShortComplex.mk _ _ hzero).Exact) :
    ∃ hc : thickeningConormalFirstMap B S hS hZ p he ≫
        thickeningConormalSecondMap B S hS hZ p = 0,
      (ShortComplex.mk _ _ hc).Exact := by
  have : IsIso (thickeningSheafOfDifferentialsMap B S hS hZ p) := he
  have hc : thickeningConormalFirstMap B S hS hZ p he ≫
      thickeningConormalSecondMap B S hS hZ p = 0 := by
    have key :=
      thickeningConormalFirstMap_comp_thickeningSheafOfDifferentialsMap B S hS hZ p he
    simp only [thickeningConormalSecondMap, ← Category.assoc]
    rw [key]
    exact hzero
  refine ⟨hc, ?_⟩
  have hiso : ShortComplex.mk _ _ hc ≅ ShortComplex.mk _ _ hzero :=
    ShortComplex.isoMk (Iso.refl _)
      (asIso (thickeningSheafOfDifferentialsMap B S hS hZ p)) (Iso.refl _)
      (by
        simpa using
          (thickeningConormalFirstMap_comp_thickeningSheafOfDifferentialsMap
            B S hS hZ p he).symm)
      (by simp [thickeningConormalSecondMap])
  exact (ShortComplex.exact_iff_of_iso hiso).mpr h05ZA

end AlgebraicGeometry.Space

end
