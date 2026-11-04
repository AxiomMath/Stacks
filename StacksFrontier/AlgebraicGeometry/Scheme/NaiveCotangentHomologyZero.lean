module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Differentials
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentComplex
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentHomologyZeroDifferentials
public import StacksFrontier.CategoryTheory.Sites.Modules.CorepresentingConormalSequence
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangent
public import StacksFrontier.Homology.DoubleHomology
import StacksCore.Tactic.StacksAttribute

/-!
# The degree-zero cohomology sheaf of the naive cotangent complex

For a morphism of sheaves of commutative rings `a : A ⟶ B` on a site, the naive cotangent
complex `NL_{B/A}` of [Stacks, Tag 08TW] is the two-term complex

`I/I² ⟶ B ⊗_{A[B]} Ω_{A[B]/A]}`

in degrees `-1` and `0`, attached to the canonical polynomial presentation `A[B] ⟶ B`. Its
degree-zero cohomology sheaf is the sheaf of relative differentials `Ω_{B/A}`: the conormal
sequence of the presentation is exact at its middle term and its right-hand map is an
epimorphism onto `Ω_{B/A}`, so the cokernel of the one nonzero differential of `NL_{B/A}` is
`Ω_{B/A}`.

For a morphism of schemes `f : X ⟶ S` this reads `H⁰(NL_{X/S}) = Ω_{X/S}`. Applied to a
monomorphism — in particular to an immersion — it says that `H⁰(NL_{Z/X})` vanishes, since
`Ω_{Z/X} = 0` for a monomorphism by [Stacks, Tag 01UY]. Together with the vanishing of all terms
outside degrees `-1` and `0` this makes `NL_{Z/X}` acyclic in every degree other than `-1`.

That is what this file proves. The degree-zero identification itself is *not* proved here: it is
`AlgebraicGeometry.Scheme.naiveCotangentComplexHomologyZeroIso` of
`StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentHomologyZeroDifferentials`, which carries the
degree-zero clause of [Stacks, Tag 0D0J], and is imported and used as a black box.

## Main results

* `Stacks.SheafOfModules.naiveCotangentComplexHomologyNegOneIsoKernel`: on an arbitrary site,
  the degree `-1` cohomology sheaf of `NL_{B/A}` is the kernel of the conormal map of the
  canonical polynomial presentation of `B` over `A`.
* `AlgebraicGeometry.Scheme.isZero_naiveCotangentComplex_homology_zero_of_mono`: for a
  monomorphism of schemes `H⁰(NL_{Z/X}) = 0`.
* `AlgebraicGeometry.Scheme.naiveCotangentComplex_exactAt_of_mono` and
  `AlgebraicGeometry.Scheme.isZero_naiveCotangentComplex_homology_of_mono`: for a monomorphism
  of schemes — in particular for an immersion — `NL_{Z/X}` is acyclic in every degree other
  than `-1`, so it is concentrated in degree `-1`.

## Route

The vanishing in degree `0` is the imported identification `H⁰(NL_{Z/X}) = Ω_{Z/X}` read at a
monomorphism, where the right-hand side is zero by
`AlgebraicGeometry.Scheme.Hom.isZero_relativeDifferentials_of_mono` ([Stacks, Tag 01UY]).

Outside degrees `-1` and `0` the complex has zero terms, by
`AlgebraicGeometry.Scheme.naiveCotangentComplex_isZero_X`, hence is exact there; combined with
the vanishing in degree `0` for a monomorphism this is acyclicity away from degree `-1`.

## Scope

**No Stacks tag is claimed by this file**, and every tag mentioned above asserts strictly more
than what is proved here.

* [Stacks, Tag 0D0J] is not claimed here. Its degree-zero clause is carried by
  `AlgebraicGeometry.Scheme.naiveCotangentComplexHomologyZeroIso` in the imported module
  `StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentHomologyZeroDifferentials`, and its
  quasi-coherence clause elsewhere; neither is reproved below.
* [Stacks, Tag 0FV2] asserts that `NL_{Z/X} ≅ 𝒞_{Z/X}[1]` in `D(𝒪_Z)` for an immersion `i`.
  Acyclicity away from degree `-1`, which is what is proved here, is necessary but not
  sufficient: the tag also identifies the one surviving cohomology sheaf with the conormal sheaf
  `𝒞_{Z/X}`. Nothing here does that.
  `Stacks.SheafOfModules.naiveCotangentComplexHomologyNegOneIsoKernel` below identifies `H⁻¹`
  with the kernel of the conormal map of the *canonical polynomial* presentation
  `i^{-1}𝒪_X[𝒪_Z] ⟶ 𝒪_Z`, which is a different object from `𝒞_{Z/X}`; comparing the two is the
  content this file does not supply.

## References

* [Stacks Project, Tag 0D0J](https://stacks.math.columbia.edu/tag/0D0J), the cohomology sheaves
  of `NL_{X/Y}`; its degree-zero identification is imported and used, not proved here.
* [Stacks Project, Tag 0FV2](https://stacks.math.columbia.edu/tag/0FV2), `NL_{Z/X}` for an
  immersion; only acyclicity away from degree `-1` is proved here.
* [Stacks Project, Tag 08TW](https://stacks.math.columbia.edu/tag/08TW), the naive cotangent
  complex of a morphism of sheaves of rings.
* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY), the canonical
  identification of the complexes of two presentations.
* [Stacks Project, Tag 01UY](https://stacks.math.columbia.edu/tag/01UY), `Ω_{Z/X} = 0` for a
  monomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w z

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasSheafify J AddCommGrpCat.{max w u v z}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w u v z}]
  (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B)

/-- The degree `-1` cohomology sheaf of `NL_{B/A}` is the kernel of the conormal map of the
canonical polynomial presentation of `B` over `A`.

This is a restatement of the construction of `NL_{B/A}` as a two-term complex and carries no
mathematical content on its own; it is recorded because it is the companion of
`Stacks.SheafOfModules.naiveCotangentComplexHomologyZeroIso` — which identifies `H⁰(NL_{B/A})`
with `Ω_{B/A}` — and because identifying this kernel is what an identification of
`H⁻¹(NL_{B/A})` amounts to. -/
noncomputable def naiveCotangentComplexHomologyNegOneIsoKernel :
    (naiveCotangentComplex.{v, u, w, z} J A B a).homology (-1) ≅
      kernel (canonicalConormalSequence.{v, u, w, z} J A B a).f := by
  have : HasZeroObject
      (_root_.SheafOfModules.{max w u v z}
        (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  exact HomologicalComplex.doubleHomologyIsoKernel _
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Scheme

/-- **`H⁰(NL_{Z/X}) = 0` for a monomorphism.** For a monomorphism of schemes `i : Z ⟶ X` the
degree `0` cohomology sheaf of `NL_{Z/X}` vanishes, because it is `Ω_{Z/X}` — by
`AlgebraicGeometry.Scheme.naiveCotangentComplexHomologyZeroIso`, the degree-zero clause of
[Stacks, Tag 0D0J] — and that vanishes by [Stacks, Tag 01UY]. -/
theorem isZero_naiveCotangentComplex_homology_zero_of_mono {Z X : Scheme.{u}} (i : Z ⟶ X)
    [Mono i] : IsZero ((naiveCotangentComplex i).homology 0) :=
  (Scheme.Hom.isZero_relativeDifferentials_of_mono i).of_iso
    (naiveCotangentComplexHomologyZeroIso i)

/-- **`NL_{Z/X}` is acyclic away from degree `-1` for a monomorphism.** For a monomorphism of
schemes `i : Z ⟶ X` the complex `NL_{Z/X}` is exact in every degree other than `-1`: outside
degrees `-1` and `0` its terms vanish, and in degree `0` its cohomology sheaf vanishes because
it is `Ω_{Z/X}`. -/
theorem naiveCotangentComplex_exactAt_of_mono {Z X : Scheme.{u}} (i : Z ⟶ X) [Mono i] (n : ℤ)
    (hn : n ≠ -1) : (naiveCotangentComplex i).ExactAt n := by
  rcases eq_or_ne n 0 with rfl | hzero
  · exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
      (isZero_naiveCotangentComplex_homology_zero_of_mono i)
  · exact ShortComplex.exact_of_isZero_X₂ _ (naiveCotangentComplex_isZero_X i n hn hzero)

/-- **`NL_{Z/X}` is concentrated in degree `-1` for a monomorphism.** For a monomorphism of
schemes `i : Z ⟶ X` — in particular for an immersion — the naive cotangent complex `NL_{Z/X}`
has vanishing cohomology sheaf in every degree other than `-1`.

Only `Mono i` is used, through
`AlgebraicGeometry.Scheme.naiveCotangentComplex_exactAt_of_mono`.

This is *weaker* than [Stacks, Tag 0FV2], which asserts `NL_{Z/X} ≅ 𝒞_{Z/X}[1]` in `D(𝒪_Z)` for
an immersion: being concentrated in degree `-1` does not identify the surviving cohomology sheaf
with the conormal sheaf `𝒞_{Z/X}`, and no such identification is proved here. No attribute is
attached for that reason. -/
theorem isZero_naiveCotangentComplex_homology_of_mono {Z X : Scheme.{u}} (i : Z ⟶ X) [Mono i]
    (n : ℤ) (hn : n ≠ -1) : IsZero ((naiveCotangentComplex i).homology n) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).1
    (naiveCotangentComplex_exactAt_of_mono i n hn)

end AlgebraicGeometry.Scheme

end
