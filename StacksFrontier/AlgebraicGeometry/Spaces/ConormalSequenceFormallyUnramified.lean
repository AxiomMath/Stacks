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
`ι^*(h')^*Ω_{X/Y}`; that is `h^*Ω_{X/Y}` through `ι ≫ h' = h`.  The comparison
`(ι ≫ h')^* ≅ ι^*(h')^*` of Stacks 03LU is deliberately not used, because no such comparison
isomorphism exists in this development for the inverse image of modules on the small étale sites
of algebraic spaces — only for the ringed-space and lower-shriek settings.  Reading the middle
term this way is what lets the sequence be stated and transported with no such comparison, and it
is the reading under which Stacks 060E itself is proved, so the two compose.

## Main definitions

* `AlgebraicGeometry.Space.thickeningClosedSubspace`: the smaller space of a universal first
  order thickening, as a closed subspace of the ambient space, which is the form the conormal
  module of Stacks 04CN and the first arrow of Stacks 05ZA consume.
* `AlgebraicGeometry.Space.thickeningConormalFirstMap`: **Stacks 060F**, the canonical
  first arrow `𝒞_{Z/Z'} ⟶ h^*Ω_{X/Y}`: the first arrow of Stacks 05ZA for the closed subspace
  `Z ⊂ Z'` over `Y`, followed by the inverse of the isomorphism of Stacks 060E.
* `AlgebraicGeometry.Space.thickeningConormalSecondMap`: the second arrow
  `h^*Ω_{X/Y} ⟶ Ω_{Z/Y}`: the isomorphism of Stacks 060E followed by the second arrow of
  Stacks 05ZA, which is the comparison map `AlgebraicGeometry.Space.pullbackDifferentialsMap` of
  Stacks 04CX.  Stacks 060F constructs no new arrow here and neither does this file.

## Main results

* `AlgebraicGeometry.Space.thickeningConormalFirstMap_comp_thickeningSheafOfDifferentialsMap`:
  **Stacks 060F**, the sense in which the first arrow is induced by `d_{Z'/Y}`.  Composed with the
  isomorphism of Stacks 060E it is the first arrow of Stacks 05ZA for `Z ⊂ Z'` over `Y`, and that
  arrow is induced by `d_{Z'/Y}` by
  `AlgebraicGeometry.Space.conormalSequenceIdealDifferential_val_app_apply`.  Since the map of
  Stacks 060E is an isomorphism, this determines the first arrow.
* `AlgebraicGeometry.Space.epi_thickeningConormalSecondMap`: **Stacks 060F**, exactness at
  the right term.  This is proved, from the exactness at the right term of Stacks 05ZA.
* `AlgebraicGeometry.Space.thickeningConormalSequence_exact`: **Stacks 060F**, the composite of
  the two arrows is zero and the resulting short complex is exact at the middle term — *granted
  the same two clauses for the sequence of Stacks 05ZA at `Z ⊂ Z'`*.  The transport is the whole
  of the tag's proof and it is what is established here.

## What is carried, and why

Three hypotheses are carried.  Each is an input that this library does not have, and each is
disclosed in the attribute of the declaration that uses it.

* `he : IsIso (thickeningSheafOfDifferentialsMap B S hS hZ p)` — the isomorphism of
  Stacks 060E.  This is **proved**, not open:
  `AlgebraicGeometry.Space.isIso_thickeningSheafOfDifferentialsMap` discharges it, in turn
  granting the étale localization of Stacks 04CU and 060D as its own `hetale` hypothesis.  It is
  taken as an argument here rather than applied, so that the construction of the first arrow does
  not drag the étale-localization predicate into its own statement; the `hetale` carry of
  Stacks 060E propagates to any consumer that discharges `he` that way, which is correct and
  expected.
* `hzero` and `h05ZA` — the composite of the two arrows of the sequence of Stacks 05ZA for
  `Z ⊂ Z'` over `Y` being zero, and exactness of that sequence at its middle term.  Neither is
  proved: the *What is not proved* section of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceDifferentials.lean` records both as the
  two clauses of Stacks 05ZA that file leaves open, the first for elaboration cost and the second
  for want of the étale localization of Stacks 04CU in the shape the reduction to the case of
  schemes consumes.  They are carried in exactly the shape that file's first arrow and
  `AlgebraicGeometry.Space.pullbackDifferentialsMap` state them, so proving them for
  Stacks 05ZA discharges them here with no reformulation.
* `hsharp` — local surjectivity of `ι♯ : ι⁻¹𝒪_{Z'} ⟶ 𝒪_Z`, which is the inverse-image form of the
  surjectivity clause of Stacks 03MB.  This is the same hypothesis as in the exactness at the
  right term of Stacks 05ZA,
  `AlgebraicGeometry.Space.epi_pullbackDifferentialsMap_of_isLocallySurjective`, and is passed
  straight through to it; `AlgebraicGeometry.Space.isLocallySurjective_structureSharp` supplies
  only the direct-image form.

Nothing else is assumed.  In particular the right-hand half of the conclusion — exactness at
`Ω_{Z/Y}` — rests on no hypothesis beyond `he` and `hsharp`, and the left-hand half adds exactly
the corresponding half of Stacks 05ZA.

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
  is the hypothesis `hsharp`.
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

/-- **Stacks 060F, the canonical first arrow** `𝒞_{Z/X} ⟶ h^*Ω_{X/Y}`.

The source `𝒞_{Z/X}` is the conormal module `𝒞_{Z/Z'}` of the closed subspace `Z ⊂ Z'`, which is
what Stacks 0607, part (2) defines `𝒞_{Z/X}` to be; the target `h^*Ω_{X/Y}` is read as the double
inverse image `ι^*(h')^*Ω_{X/Y}`, as in Stacks 060E.  The arrow is the first arrow
`AlgebraicGeometry.Space.conormalSequenceFirstMap` of Stacks 05ZA for `Z ⊂ Z'` over `Y`, followed
by the inverse of the isomorphism `AlgebraicGeometry.Space.thickeningSheafOfDifferentialsMap` of
Stacks 060E.

The hypothesis `he` is that isomorphism, which
`AlgebraicGeometry.Space.isIso_thickeningSheafOfDifferentialsMap` supplies. -/
@[stacks 060F "the canonical first arrow `𝒞_{Z/X} ⟶ h^*Ω_{X/Y}`, with `𝒞_{Z/X}` the conormal \
module of `Z ⊂ Z'` of 0607(2) and the middle term read as `ι^*(h')^*Ω_{X/Y}`; granted as `he` \
that the map of 060E is an isomorphism, which `isIso_thickeningSheafOfDifferentialsMap` supplies"]
noncomputable def thickeningConormalFirstMap
    (hZ : IsUniversalFirstOrderThickening B S hS Z h') (p : X ⟶ Y)
    (he : IsIso (thickeningSheafOfDifferentialsMap B S hS hZ p)) :
    conormalModule B S hS Z' (thickeningClosedSubspace B S hS hZ) ⟶
      (modulePullback B S hS (universalThickeningInclusion B S hS hZ)).obj
        ((modulePullback B S hS h').obj (sheafOfDifferentials B S hS p)) :=
  have : IsIso (thickeningSheafOfDifferentialsMap B S hS hZ p) := he
  conormalSequenceFirstMap B S hS (thickeningClosedSubspace B S hS hZ) (h' ≫ p) ≫
    inv (thickeningSheafOfDifferentialsMap B S hS hZ p)

/-- **The second arrow of the sequence of Stacks 060F**, `h^*Ω_{X/Y} ⟶ Ω_{Z/Y}`: the isomorphism
`AlgebraicGeometry.Space.thickeningSheafOfDifferentialsMap` of Stacks 060E followed by the second
arrow `AlgebraicGeometry.Space.pullbackDifferentialsMap` of Stacks 05ZA for `Z ⊂ Z'` over `Y`.

Stacks 060F constructs no arrow here, and neither does this definition: the second arrow of
Stacks 05ZA is already the comparison map of Stacks 04CX, registered under that tag in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceSecondMap.lean`, and all that is done here
is to read its source as `h^*Ω_{X/Y}` across the identification of Stacks 060E.  No `@[stacks]`
attribute is claimed for it. -/
noncomputable def thickeningConormalSecondMap
    (hZ : IsUniversalFirstOrderThickening B S hS Z h') (p : X ⟶ Y) :
    (modulePullback B S hS (universalThickeningInclusion B S hS hZ)).obj
        ((modulePullback B S hS h').obj (sheafOfDifferentials B S hS p)) ⟶
      sheafOfDifferentials B S hS (universalThickeningInclusion B S hS hZ ≫ (h' ≫ p)) :=
  thickeningSheafOfDifferentialsMap B S hS hZ p ≫
    pullbackDifferentialsMap B S hS (universalThickeningInclusion B S hS hZ) (h' ≫ p)

/-! ### The first arrow is induced by `d_{Z'/Y}` -/

/-- **Stacks 060F, "the first arrow is induced by `d_{Z'/Y}`".**  Composed with the isomorphism
of Stacks 060E, the first arrow is the first arrow of Stacks 05ZA for the closed subspace
`Z ⊂ Z'` over `Y`; and that arrow is induced by `d_{Z'/Y}` in the sense of
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
@[stacks 060F "the first arrow is induced by `d_{Z'/B}`: composed with the isomorphism of 060E \
it is the first arrow of 05ZA for `Z ⊂ Z'` over the base, which \
`conormalSequenceIdealDifferential_val_app_apply` identifies with `d_{Z'/B}` on the defining \
ideal sheaf; granted as `he` that the map of 060E is an isomorphism"]
theorem thickeningConormalFirstMap_comp_thickeningSheafOfDifferentialsMap
    (hZ : IsUniversalFirstOrderThickening B S hS Z h') (p : X ⟶ Y)
    (he : IsIso (thickeningSheafOfDifferentialsMap B S hS hZ p)) :
    thickeningConormalFirstMap B S hS hZ p he ≫
        thickeningSheafOfDifferentialsMap B S hS hZ p =
      conormalSequenceFirstMap B S hS (thickeningClosedSubspace B S hS hZ) (h' ≫ p) := by
  have : IsIso (thickeningSheafOfDifferentialsMap B S hS hZ p) := he
  simp [thickeningConormalFirstMap]

/-! ### Exactness at the right term -/

/-- **Stacks 060F, exactness at the right term.**  The second arrow `h^*Ω_{X/Y} ⟶ Ω_{Z/Y}` is an
epimorphism, so the sequence ends in zero.

It is the isomorphism of Stacks 060E followed by the second arrow of Stacks 05ZA, and the latter
is an epimorphism by `AlgebraicGeometry.Space.epi_pullbackDifferentialsMap_of_isLocallySurjective`
under local surjectivity of `ι♯`, which is the hypothesis `hsharp` passed straight through. -/
@[stacks 060F "exactness at the right term: the second arrow `h^*Ω_{X/Y} ⟶ Ω_{Z/Y}` is an \
epimorphism.  Granted as `he` that the map of 060E is an isomorphism, and as `hsharp` local \
surjectivity of `ι♯` (the inverse-image form of the surjectivity clause of 03MB), which is the \
same hypothesis as in the exactness at the right term of 05ZA"]
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

/-- **Stacks 060F, the two remaining clauses**: the composite of the two arrows is zero, and the
resulting short complex `𝒞_{Z/X} ⟶ h^*Ω_{X/Y} ⟶ Ω_{Z/Y}` is exact at the middle term.

This is the transport the source's proof performs, and it is all that is proved here: both
clauses are *granted* for the sequence of Stacks 05ZA at the closed subspace `Z ⊂ Z'` over `Y`,
as `hzero` and `h05ZA`, and the isomorphism of Stacks 060E carries them across.  The short
complex of the conclusion is isomorphic to the short complex of Stacks 05ZA, by the identity on
the two outer terms and that isomorphism on the middle one, so
`CategoryTheory.ShortComplex.exact_iff_of_iso` transfers exactness.

The two granted clauses are precisely the two clauses that
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceDifferentials.lean` leaves open for
Stacks 05ZA, stated at its first arrow and at its second arrow
`AlgebraicGeometry.Space.pullbackDifferentialsMap`, so proving them there discharges them here
verbatim.  Exactness at the right term is not among them: it is proved, by
`AlgebraicGeometry.Space.epi_thickeningConormalSecondMap`. -/
@[stacks 060F "the composite of the two arrows is zero and the short complex is exact at the \
middle term `h^*Ω_{X/Y}` — the transport across the isomorphism of 060E, which is the whole of \
the tag's proof.  Granted as `he` that the map of 060E is an isomorphism, and as `hzero` and \
`h05ZA` the same two clauses for the sequence of 05ZA at `Z ⊂ Z'` over the base, which are the \
two clauses 05ZA leaves open in this tree.  Exactness at the right term is separate and is \
proved: see `epi_thickeningConormalSecondMap`"]
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
