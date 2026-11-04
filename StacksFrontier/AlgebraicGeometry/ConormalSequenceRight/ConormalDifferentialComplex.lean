module

public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.SchemeMiddleExact
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentHomologyZero
public import StacksFrontier.Homology.DoubleExtend
public import StacksFrontier.Homology.DoubleHomology

/-!
# The two-term complex of the conormal sequence of an immersion

Let `i : Z ⟶ X` be an immersion of schemes over `p : X ⟶ S`. The first arrow of the conormal
sequence of [Stacks, Tag 01UZ], `Stacks.ConormalSequenceRight.conormalDifferential`, is a
morphism `𝒞_{Z/X} ⟶ i^*Ω_{X/S}` of `𝒪_Z`-modules; this file packages it as the two-term complex

```
(𝒞_{Z/X} ⟶ i^*Ω_{X/S})
```

with the conormal sheaf in degree `-1`, and computes its cohomology sheaves.

The object is the right-hand side of [Stacks, Tag 0FV4]: for a morphism of schemes `f : Z ⟶ S`
factored as `f = p ∘ i` with `i` an immersion and `p` formally smooth, that tag asserts a
canonical isomorphism `NL_{Z/S} ≅ (𝒞_{Z/X} ⟶ i^*Ω_{X/S})` in `D(𝒪_Z)`. **That tag is not proved
here and no attribute for it is attached.** What is proved is that the two complexes have
isomorphic degree-zero cohomology sheaves, both being `Ω_{Z/S}`.

## Main definitions

* `Stacks.ConormalSequenceRight.conormalDifferentialComplex`: the two-term complex
  `(𝒞_{Z/X} ⟶ i^*Ω_{X/S})`, with `𝒞_{Z/X}` in degree `-1`.

## Main results

* `Stacks.ConormalSequenceRight.conormalDifferentialComplexXIsoNegOne`,
  `...XIsoZero`, `...conormalDifferentialComplex_isZero_X` and
  `...conormalDifferentialComplex_d_negOne_zero` identify the two terms, record that all other
  terms vanish, and identify the one nonzero differential.
* `Stacks.ConormalSequenceRight.conormalDifferentialComplexHomologyZeroIso`: its degree-zero
  cohomology sheaf is `Ω_{Z/S}`.
* `Stacks.ConormalSequenceRight.conormalDifferentialComplexHomologyNegOneIso`: its degree `-1`
  cohomology sheaf is the kernel of the first arrow.
* `Stacks.ConormalSequenceRight.naiveCotangentComplexHomologyZeroIso`: the degree-zero
  cohomology sheaves of `NL_{Z/S}` and of `(𝒞_{Z/X} ⟶ i^*Ω_{X/S})` agree.

## Route

The complex is `HomologicalComplex.double` of the first arrow, so
`HomologicalComplex.doubleHomologyIsoCokernel` and `HomologicalComplex.doubleHomologyIsoKernel`
give its two cohomology sheaves as the cokernel and the kernel of that arrow. The cokernel is
`Ω_{Z/S}` because the conormal sequence is exact at its middle term
(`Stacks.ConormalSequenceRight.conormalShortComplex_exact`) and its second arrow is an
epimorphism (`Stacks.ConormalSequenceRight.epi_conormalShortComplex_g`); that is
`Stacks.ConormalSequenceRight.conormalShortComplexCokernelIso`. On the other side
`H⁰(NL_{Z/S}) = Ω_{Z/S}` is
`AlgebraicGeometry.Scheme.naiveCotangentComplexHomologyZeroIso`, the degree-zero clause of
[Stacks, Tag 0D0J].

## Scope

**No attribute for [Stacks, Tag 0FV4] is attached here.** The tag is proved, in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentImmersionFormallySmooth`, where the
complex of this file is the right-hand side; three things the tag asserts are missing *here*.

* No morphism of complexes between `NL_{Z/S}` and `(𝒞_{Z/X} ⟶ i^*Ω_{X/S})` is constructed. The
  isomorphism below is between their degree-zero cohomology sheaves only, assembled from two
  independent identifications of each with `Ω_{Z/S}`.
* Nothing identifies `H⁻¹(NL_{Z/S})` with `H⁻¹(𝒞_{Z/X} ⟶ i^*Ω_{X/S})`. That is where formal
  smoothness of `p` — the tag's hypothesis — enters. Both clauses of the forward implication of
  [Stacks, Tag 0D0L] that the source's proof uses at that point are now available: the
  vanishing `H⁻¹(NL_{X/S}) = 0` is
  `Stacks.Smooth.isZero_homology_negOne_naiveCotangentComplex_of_formallySmooth` and local
  projectivity of `Ω_{X/S}` is
  `Stacks.Smooth.isLocallyProjective_relativeDifferentials_of_formallySmooth`.
* No object of the derived category `D(𝒪_Z)` appears.

Consequently formal smoothness of `p` is **not** used below and is not needed: the degree-zero
cohomology sheaf of either side is `Ω_{Z/S}` for every immersion `i` and every `p`.

What the tag's own proof needs beyond the two clauses above is the composition triangle
`i^*NL_{X/S} ⟶ NL_{Z/S} ⟶ NL_{Z/X} ⟶ i^*NL_{X/S}[1]` of [Stacks, Tag 0FV3] at the scheme level,
which this section used to record as unavailable; it **is** available now, as
`Stacks.NaiveCotangentConeInvertible.cotangentTriangle_distinguished`, the invertibility in
`D(𝒪_Z)` of the comparison of [Stacks, Tag 0E1Z] that replaces the mapping cocone of
`NL_{Z/S} ⟶ NL_{Z/X}` by `i^*NL_{X/S}` being
`Stacks.NaiveCotangentConeInvertible.isIso_Q_map_coneMap`. The other input,
`NL_{Z/X} ≅ 𝒞_{Z/X}[1]` of [Stacks, Tag 0FV2], is
`Stacks.Conormal.Sites.quasiIso_conormalShiftComparison`. Rotating that triangle and reading
both of those identifications into it gives
`Stacks.NaiveCotangentConeInvertible.conormalDifferentialsTriangle_distinguished`, which
exhibits `NL_{Z/S}` as the cone of *a* map `𝒞_{Z/X} ⟶ i^*Ω_{X/S}` in `D(𝒪_Z)`.

What is still needed for the tag is that the map in question is the conormal differential
`Stacks.ConormalSequenceRight.conormalDifferential` of this file's complex, up to sign. That map
is the connecting morphism of the six term sequence of [Stacks, Tag 0E44] read through the degree
`-1` identification of [Stacks, Tag 0FV2]. The tag follows once the two are identified up to
sign, and a distinguished triangle pins its first morphism only up to automorphisms of that
morphism's source and target, so the connecting morphism has to be computed. It has been:
`Stacks.SheafOfModules.stalk_connecting_cotangent_mk` computes it at every stalk and the answer
is **minus** the conormal differential of this file. What is still missing is two coordinate
changes, the stalks of the comparison isomorphisms
`Stacks.Conormal.Sites.homologyNegOneIsoConormalSheaf` and
`Stacks.NaiveCotangentSixTermSequence.pullbackHomologyZeroIso`, listed in the `Scope` section of
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentConeMapInvertible`.

## References

* [Stacks Project, Tag 0FV4](https://stacks.math.columbia.edu/tag/0FV4)
* [Stacks Project, Tag 01UZ](https://stacks.math.columbia.edu/tag/01UZ), the conormal sequence,
  whose first arrow is the differential of this complex.
* [Stacks Project, Tag 0D0J](https://stacks.math.columbia.edu/tag/0D0J), the cohomology sheaves
  of `NL_{Z/S}`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace Stacks.ConormalSequenceRight

variable {Z X S : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (p : X ⟶ S)

/-- **The right-hand side of [Stacks, Tag 0FV4].** For an immersion `i : Z ⟶ X` of schemes over
`p : X ⟶ S`, the two-term complex `(𝒞_{Z/X} ⟶ i^*Ω_{X/S})` of `𝒪_Z`-modules whose differential
is the first arrow of the conormal sequence of [Stacks, Tag 01UZ], with the conormal sheaf
`𝒞_{Z/X}` placed in degree `-1` and `i^*Ω_{X/S}` in degree `0`. -/
noncomputable def conormalDifferentialComplex : CochainComplex Z.Modules ℤ :=
  HomologicalComplex.double (conormalDifferential i p) ComplexShape.upIntRelNegOneZero

/-- The degree `-1` term is the conormal sheaf `𝒞_{Z/X}`. -/
noncomputable def conormalDifferentialComplexXIsoNegOne :
    (conormalDifferentialComplex i p).X (-1) ≅ (conormalSheaf i : Z.Modules) :=
  HomologicalComplex.doubleXIso₀ _ ComplexShape.upIntRelNegOneZero

/-- The degree `0` term is the pullback `i^*Ω_{X/S}`. -/
noncomputable def conormalDifferentialComplexXIsoZero :
    (conormalDifferentialComplex i p).X 0 ≅
      (Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p) :=
  HomologicalComplex.doubleXIso₁ _ ComplexShape.upIntRelNegOneZero (by decide)

/-- The complex has no terms outside degrees `-1` and `0`. -/
theorem conormalDifferentialComplex_isZero_X (n : ℤ) (hneg : n ≠ -1) (hzero : n ≠ 0) :
    IsZero ((conormalDifferentialComplex i p).X n) :=
  HomologicalComplex.isZero_double_X (conormalDifferential i p)
    ComplexShape.upIntRelNegOneZero n hneg hzero

/-- The only nonzero differential is the first arrow of the conormal sequence. -/
theorem conormalDifferentialComplex_d_negOne_zero :
    (conormalDifferentialComplex i p).d (-1) 0 =
      (conormalDifferentialComplexXIsoNegOne i p).hom ≫ conormalDifferential i p ≫
        (conormalDifferentialComplexXIsoZero i p).inv :=
  HomologicalComplex.double_d _ ComplexShape.upIntRelNegOneZero (by decide)

/-- The degree `-1` cohomology sheaf of `(𝒞_{Z/X} ⟶ i^*Ω_{X/S})` is the kernel of the first
arrow of the conormal sequence.

Under the smoothness hypothesis of [Stacks, Tag 06AA] that first arrow is a monomorphism, so
this kernel vanishes; in general it does not. -/
noncomputable def conormalDifferentialComplexHomologyNegOneIso :
    (conormalDifferentialComplex i p).homology (-1) ≅ kernel (conormalDifferential i p) :=
  HomologicalComplex.doubleHomologyIsoKernel (conormalDifferential i p)
    ComplexShape.upIntRelNegOneZero (by decide)

/-- **The degree `0` cohomology sheaf of `(𝒞_{Z/X} ⟶ i^*Ω_{X/S})` is `Ω_{Z/S}`.** The conormal
sequence of [Stacks, Tag 01UZ] is exact at its middle term and ends in `Ω_{Z/S}`, so the
cokernel of its first arrow is `Ω_{Z/S}`.

No hypothesis beyond `IsImmersion i` is used; in particular `p` is arbitrary. -/
noncomputable def conormalDifferentialComplexHomologyZeroIso :
    (conormalDifferentialComplex i p).homology 0 ≅ Scheme.Hom.relativeDifferentials (i ≫ p) :=
  HomologicalComplex.doubleHomologyIsoCokernel (conormalDifferential i p)
      ComplexShape.upIntRelNegOneZero (by decide) ≪≫
    conormalShortComplexCokernelIso i p

/-- **`H⁰(NL_{Z/S}) = H⁰(𝒞_{Z/X} ⟶ i^*Ω_{X/S})`.** For a morphism of schemes that factors as
`i ≫ p` with `i : Z ⟶ X` an immersion, the degree `0` cohomology sheaf of `NL_{Z/S}` and the
degree `0` cohomology sheaf of the two-term complex `(𝒞_{Z/X} ⟶ i^*Ω_{X/S})` are isomorphic:
both are the sheaf of relative differentials `Ω_{Z/S}`.

Neither formal smoothness of `p` nor anything beyond `i` being an immersion is used:
`H⁰(NL_{Z/S}) = Ω_{Z/S}` holds for every morphism and
`H⁰(𝒞_{Z/X} ⟶ i^*Ω_{X/S}) = Ω_{Z/S}` holds for every immersion.

This is *weaker* than [Stacks, Tag 0FV4], which asserts an isomorphism of the two complexes in
`D(𝒪_Z)` when `p` is formally smooth: no morphism of complexes is constructed here, the degree
`-1` cohomology sheaves are not compared, and no object of `D(𝒪_Z)` appears. No attribute is
attached for that reason. -/
noncomputable def naiveCotangentComplexHomologyZeroIso :
    (Scheme.naiveCotangentComplex (i ≫ p)).homology 0 ≅
      (conormalDifferentialComplex i p).homology 0 :=
  Scheme.naiveCotangentComplexHomologyZeroIso (i ≫ p) ≪≫
    (conormalDifferentialComplexHomologyZeroIso i p).symm

end Stacks.ConormalSequenceRight

end
