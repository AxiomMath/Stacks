module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceFormallyUnramified
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceThickeningDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningDifferentialsIso

/-!
# The conormal sequence of a formally unramified morphism of algebraic spaces is exact

Let `S` be a scheme, let `Y` be an algebraic space over `S` (the base, written `B` in the source;
the letter `B` is taken here by the big fppf site) and let `h : Z ⟶ X` be a formally unramified
morphism of algebraic spaces over `Y`, with universal first order neighbourhood `Z ⊂ Z'` over
`X`, structure morphism `h' : Z' ⟶ X` and inclusion `ι : Z ⟶ Z'`, so that `h = ι ≫ h'`.  The
sequence
```
  𝒞_{Z/X} ⟶ h^*Ω_{X/Y} ⟶ Ω_{Z/Y} ⟶ 0
```
of sheaves of `𝒪_Z`-modules on the small étale site of `Z` is exact, and its first arrow is
induced by `d_{Z'/Y}`.

The proof is the source's: the conormal sequence of the closed subspace `Z ⊂ Z'` over `Y`,
```
  𝒞_{Z/Z'} ⟶ ι^*Ω_{Z'/Y} ⟶ Ω_{Z/Y} ⟶ 0,
```
is exact (the composite is zero by
`AlgebraicGeometry.Space.conormalSequenceFirstMap_comp_pullbackDifferentialsMap`, exactness in
the middle is `AlgebraicGeometry.Space.exact_conormalSequence` and exactness on the right is
`AlgebraicGeometry.Space.epi_pullbackDifferentialsMap_subspaceInclusion`), and the isomorphism
`h^*Ω_{X/Y} ≅ ι^*Ω_{Z'/Y}` of
`AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.isIso_thickeningSheafOfDifferentialsMap`
carries it onto the displayed one.  The outer terms agree: `𝒞_{Z/X}` is by definition the
conormal sheaf `𝒞_{Z/Z'}`.

## Main definitions

* `AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.conormalSequence`: the short complex
  `𝒞_{Z/X} ⟶ h^*Ω_{X/Y} ⟶ Ω_{Z/Y}`, whose arrows are
  `AlgebraicGeometry.Space.thickeningConormalFirstMap` and
  `AlgebraicGeometry.Space.thickeningConormalSecondMap`.

## Main results

* `AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.exists_conormalSequence_exact`: the
  composite of the two arrows is zero, the sequence is exact at `h^*Ω_{X/Y}`, the second arrow
  is an epimorphism, and the first arrow followed by the isomorphism of
  `AlgebraicGeometry.Space.thickeningSheafOfDifferentialsMap` is the arrow
  `AlgebraicGeometry.Space.conormalSequenceFirstMap` induced by `d_{Z'/Y}`.
* `AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.conormalSequence_exact` and
  `AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.epi_conormalSequence_g`: the same
  exactness statements, read off the short complex.

## Implementation notes

The situation is presented as in
`AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.isIso_thickeningSheafOfDifferentialsMap`:
by a universal first order thickening `hZ` of a subfunctor `Z` of `Z'` over `h' : Z' ⟶ X`, and a
morphism `p : X ⟶ Y` to the base; the morphism `h` of the source is `ι ≫ h'`.  This is the
datum the source starts from: for a formally unramified `h`,
`AlgebraicGeometry.Space.nonempty_universalFirstOrderThickening` (Stacks 0606) provides an
`AlgebraicGeometry.Space.UniversalFirstOrderThickening` of `h`, whose field `isUniversal` is such
an `hZ` and whose field `sourceIso` identifies `Z` with the subfunctor compatibly with `h`.  The
middle term `h^*Ω_{X/Y}` is written as the iterated inverse image `ι^*(h')^*Ω_{X/Y}`.

## References

* [Stacks Project, Tag 060F](https://stacks.math.columbia.edu/tag/060F)
* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA)
* [Stacks Project, Tag 060E](https://stacks.math.columbia.edu/tag/060E)
* [Stacks Project, Tag 0607](https://stacks.math.columbia.edu/tag/0607)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z' : AlgebraicSpaces B S hS} {Z : Subfunctor Z'.obj} {h' : Z' ⟶ X}

/-- The sequence `𝒞_{Z/Z'} ⟶ ι^*Ω_{Z'/Y} ⟶ Ω_{Z/Y}` of the closed subspace `Z ⊂ Z'` over `Y`
composes to zero, with the inclusion written
`AlgebraicGeometry.Space.universalThickeningInclusion`. This is
`AlgebraicGeometry.Space.conormalSequenceFirstMap_comp_pullbackDifferentialsMap` at
`AlgebraicGeometry.Space.thickeningClosedSubspace`. -/
theorem conormalSequenceFirstMap_comp_pullbackDifferentialsMap_thickening
    (hZ : IsUniversalFirstOrderThickening B S hS Z h') (p : X ⟶ Y) :
    conormalSequenceFirstMap B S hS (thickeningClosedSubspace B S hS hZ) (h' ≫ p) ≫
      pullbackDifferentialsMap B S hS (universalThickeningInclusion B S hS hZ) (h' ≫ p) = 0 := by
  convert conormalSequenceFirstMap_comp_pullbackDifferentialsMap B S hS
    (thickeningClosedSubspace B S hS hZ) (h' ≫ p) using 1

namespace IsUniversalFirstOrderThickening

/-- The sequence `𝒞_{Z/X} ⟶ h^*Ω_{X/Y} ⟶ Ω_{Z/Y}` has composite zero and is exact in the middle. -/
private theorem exists_thickeningConormalSequence_exact
    (hZ : IsUniversalFirstOrderThickening B S hS Z h') (p : X ⟶ Y) :
    ∃ hc : thickeningConormalFirstMap B S hS hZ p
        (hZ.isIso_thickeningSheafOfDifferentialsMap B S hS p) ≫
          thickeningConormalSecondMap B S hS hZ p = 0,
      (ShortComplex.mk _ _ hc).Exact :=
  thickeningConormalSequence_exact B S hS hZ p _
    (conormalSequenceFirstMap_comp_pullbackDifferentialsMap_thickening B S hS hZ p)
    (exact_conormalSequence B S hS (h' ≫ p) (thickeningClosedSubspace B S hS hZ))

/-- The composite of the two arrows of the sequence `𝒞_{Z/X} ⟶ h^*Ω_{X/Y} ⟶ Ω_{Z/Y}` is zero. -/
theorem thickeningConormalFirstMap_comp_thickeningConormalSecondMap
    (hZ : IsUniversalFirstOrderThickening B S hS Z h') (p : X ⟶ Y) :
    thickeningConormalFirstMap B S hS hZ p (hZ.isIso_thickeningSheafOfDifferentialsMap B S hS p) ≫
      thickeningConormalSecondMap B S hS hZ p = 0 :=
  (exists_thickeningConormalSequence_exact B S hS hZ p).1

/-- The sequence `𝒞_{Z/X} ⟶ h^*Ω_{X/Y} ⟶ Ω_{Z/Y}` of a formally unramified morphism, as a short
complex of sheaves of modules on the small étale site of `Z`. -/
noncomputable def conormalSequence (hZ : IsUniversalFirstOrderThickening B S hS Z h')
    (p : X ⟶ Y) :
    ShortComplex (Modules.{u, u} B S hS (universalThickeningSubSpace B S hS hZ).obj
      (universalThickeningSubSpace B S hS hZ).property) :=
  ShortComplex.mk _ _ (hZ.thickeningConormalFirstMap_comp_thickeningConormalSecondMap B S hS p)

/-- The first arrow of `conormalSequence` is `thickeningConormalFirstMap`. -/
@[simp]
theorem conormalSequence_f (hZ : IsUniversalFirstOrderThickening B S hS Z h') (p : X ⟶ Y) :
    (hZ.conormalSequence B S hS p).f =
      thickeningConormalFirstMap B S hS hZ p
        (hZ.isIso_thickeningSheafOfDifferentialsMap B S hS p) :=
  rfl

/-- The second arrow of `conormalSequence` is `thickeningConormalSecondMap`. -/
@[simp]
theorem conormalSequence_g (hZ : IsUniversalFirstOrderThickening B S hS Z h') (p : X ⟶ Y) :
    (hZ.conormalSequence B S hS p).g = thickeningConormalSecondMap B S hS hZ p :=
  rfl

/-- Let `h = ι ≫ h' : Z ⟶ X` be formally unramified over `Y`, with universal first order
neighbourhood `Z ⊂ Z'` over `X` given by `hZ`.  The canonical sequence
```
  𝒞_{Z/X} ⟶ h^*Ω_{X/Y} ⟶ Ω_{Z/Y} ⟶ 0
```
is exact: the composite of its two arrows is zero, it is exact at `h^*Ω_{X/Y}`, and its second
arrow is an epimorphism.  Its first arrow is induced by `d_{Z'/Y}`: followed by the isomorphism
`h^*Ω_{X/Y} ≅ ι^*Ω_{Z'/Y}` of Stacks 060E it is the arrow
`AlgebraicGeometry.Space.conormalSequenceFirstMap` of the closed subspace `Z ⊂ Z'`, whose
transpose sends a local section of the ideal of `Z` to its differential
(`AlgebraicGeometry.Space.conormalSequenceIdealDifferential_val_app_apply`).

The sequence of Stacks 05ZA for `Z ⊂ Z'` is exact, and the isomorphism of Stacks 060E carries
it onto this one. -/
@[stacks 060F]
theorem exists_conormalSequence_exact (hZ : IsUniversalFirstOrderThickening B S hS Z h')
    (p : X ⟶ Y) :
    ∃ hc : thickeningConormalFirstMap B S hS hZ p
        (hZ.isIso_thickeningSheafOfDifferentialsMap B S hS p) ≫
          thickeningConormalSecondMap B S hS hZ p = 0,
      (ShortComplex.mk _ _ hc).Exact ∧ Epi (thickeningConormalSecondMap B S hS hZ p) ∧
        thickeningConormalFirstMap B S hS hZ p
            (hZ.isIso_thickeningSheafOfDifferentialsMap B S hS p) ≫
          thickeningSheafOfDifferentialsMap B S hS hZ p =
        conormalSequenceFirstMap B S hS (thickeningClosedSubspace B S hS hZ) (h' ≫ p) :=
  ⟨hZ.thickeningConormalFirstMap_comp_thickeningConormalSecondMap B S hS p,
    (exists_thickeningConormalSequence_exact B S hS hZ p).2,
    epi_thickeningConormalSecondMap B S hS hZ p
      (hZ.isIso_thickeningSheafOfDifferentialsMap B S hS p)
      (isLocallySurjective_structureSharpInverseImage B S hS
        (universalThickeningInclusion B S hS hZ)
        (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1.2),
    thickeningConormalFirstMap_comp_thickeningSheafOfDifferentialsMap B S hS hZ p _⟩

/-- The sequence `𝒞_{Z/X} ⟶ h^*Ω_{X/Y} ⟶ Ω_{Z/Y}` is exact at `h^*Ω_{X/Y}`. -/
theorem conormalSequence_exact (hZ : IsUniversalFirstOrderThickening B S hS Z h')
    (p : X ⟶ Y) : (hZ.conormalSequence B S hS p).Exact :=
  (hZ.exists_conormalSequence_exact B S hS p).2.1

/-- The second arrow `h^*Ω_{X/Y} ⟶ Ω_{Z/Y}` of the sequence is an epimorphism. -/
instance epi_conormalSequence_g (hZ : IsUniversalFirstOrderThickening B S hS Z h')
    (p : X ⟶ Y) : Epi (hZ.conormalSequence B S hS p).g :=
  (hZ.exists_conormalSequence_exact B S hS p).2.2.1

end IsUniversalFirstOrderThickening

end AlgebraicGeometry.Space

end
