module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import StacksFrontier.Algebra.Homology.DerivedCategory.TwoTermExtZero
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentHomologyZero

/-!
# `Ext⁰` out of the naive cotangent complex of a homomorphism of sheaves of rings

Let `a : A ⟶ B` be a homomorphism of sheaves of commutative rings on a site and let `𝒢` be a
sheaf of `B`-modules.  The naive cotangent complex `NL_{B/A}` is the two-term complex
`I/I² ⟶ B ⊗_{A[B]} Ω_{A[B]/A}` in cohomological degrees `-1` and `0` attached to the conormal
sequence of the canonical polynomial presentation `A[B] ⟶ B`, so it lives in degrees `≤ 0` and

`Ext⁰_B(NL_{B/A}, 𝒢) = Hom_B(H⁰(NL_{B/A}), 𝒢) = Hom_B(Ω_{B/A}, 𝒢)`,

the second equality being the degree `0` half of **Stacks 08TY**
(`Stacks.SheafOfModules.naiveCotangentComplexHomologyZeroIso`).  The groups
`Ext^i_B(NL_{B/A}, 𝒢)` vanish for `i < 0`.

## Main definitions

* `Stacks.SheafOfModules.naiveCotangentObj`: `NL_{B/A}` as an object of the derived category of
  sheaves of `B`-modules.
* `Stacks.SheafOfModules.naiveCotangentExt`: `Ext^i_B(NL_{B/A}, 𝒢)`.
* `Stacks.SheafOfModules.canonicalConormalCokernelIsoDifferentials`: the cokernel of the
  conormal map of the canonical presentation is `Ω_{B/A}`.
* `Stacks.SheafOfModules.naiveCotangentExtZeroAddEquivCokernel`: the identification of
  `Ext⁰_B(NL_{B/A}, 𝒢)` with `Hom_B(coker(I/I² ⟶ B ⊗ Ω), 𝒢)` by taking `H⁰`, and
  `Stacks.SheafOfModules.naiveCotangentExtZeroAddEquiv`: the same identification with the group
  written as `Hom_B(Ω_{B/A}, 𝒢)`.

## Main results

* `Stacks.SheafOfModules.naiveCotangentComplex_eq_twoTermComplex`: `NL_{B/A}` is the two-term
  complex of the conormal map of the canonical presentation.
* `Stacks.SheafOfModules.naiveCotangentExt_eq_zero_of_neg`: `Ext^i_B(NL_{B/A}, 𝒢) = 0` for
  `i < 0`.

## Implementation notes

Everything is the general statement about a complex concentrated in degrees `-1` and `0` of
`StacksFrontier/Algebra/Homology/DerivedCategory/TwoTermExtZero.lean`, read at the conormal map of
the canonical presentation: `Stacks.SheafOfModules.naiveCotangentComplex` is by construction
`HomologicalComplex.double` of that map, so the two complexes are equal — the proof is `rfl`,
the two proofs of `(ComplexShape.up ℤ).Rel (-1) 0` involved being proofs of one proposition.

This is the canonical-presentation counterpart of
`StacksFrontier/CategoryTheory/Sites/Modules/InternalHomAndFlatness/NaiveCotangentExtZero.lean`,
which proves the same statements for the complex `NL(α)` of an arbitrary polynomial
presentation `α`.  Neither file is an instance of the other at this spelling: `NL(α)` carries a
local surjectivity hypothesis on `α` and is stated over `presentationConormalSequence`, while
`NL_{B/A}` is stated over `canonicalConormalSequence`, and the two agree only after the
rewriting `Stacks.SheafOfModules.presentationNaiveCotangentComplex_id`.  Downstream consumers
on a ringed space or a scheme speak about `NL_{B/A}`, which is why it is given its own
statements here.

The model of the derived category is left as a hypothesis rather than fixed by
`HasDerivedCategory.standard`: nothing below depends on the model, and a consumer working in
`D(𝒪_X)` with its own instance can use these statements directly.

Nothing here carries a `stacks` attribute: that a complex concentrated in two adjacent degrees
has its `Ext⁰` computed by `H⁰` is a general fact that no tag of the source states, and the
identification `H⁰(NL_{B/A}) = Ω_{B/A}` that it is combined with is tagged where it is proved.

## References

* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY), the cohomology sheaves
  of the naive cotangent complex
* [Stacks Project, Tag 08TW](https://stacks.math.columbia.edu/tag/08TW), the naive cotangent
  complex of a homomorphism of sheaves of rings
* [Stacks Project, Tag 06XS](https://stacks.math.columbia.edu/tag/06XS), `Ext` between
  complexes with disjoint homology ranges
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w z t

namespace Stacks.SheafOfModules

open AlgebraicGeometry.SheafOfModules ( moduleOfDifferentialsOfSite)

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B)
  [HasSheafify J AddCommGrpCat.{max w u v z}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w u v z}]

/-! ### `NL_{B/A}` as a two-term complex -/

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The naive cotangent complex of a homomorphism of sheaves of rings is the two-term complex
of the conormal map of its canonical polynomial presentation, with `I/I²` in degree `-1` and
`B ⊗_{A[B]} Ω_{A[B]/A}` in degree `0`. -/
theorem naiveCotangentComplex_eq_twoTermComplex :
    naiveCotangentComplex.{v, u, w, z} J A B a =
      StacksDraft.TwoTermExt.twoTermComplex
        (canonicalConormalSequence.{v, u, w, z} J A B a).f :=
  rfl

/-- The cokernel of the conormal map of the canonical polynomial presentation is the sheaf of
relative differentials `Ω_{B/A}`: it is `H⁰(NL_{B/A})`, which is `Ω_{B/A}` by the degree `0`
half of **Stacks 08TY**. -/
noncomputable def canonicalConormalCokernelIsoDifferentials :
    cokernel (canonicalConormalSequence.{v, u, w, z} J A B a).f ≅
      moduleOfDifferentialsOfSite.{v, u, w, z} A B a :=
  (naiveCotangentComplexHomologyZeroIsoCokernel.{v, u, w, z} J A B a).symm ≪≫
    naiveCotangentComplexHomologyZeroIso.{v, u, w, z} J A B a

/-! ### `Ext` out of `NL_{B/A}` -/

variable [HasDerivedCategory.{t}
  (_root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B))]

/-- `NL_{B/A}` as an object of the derived category of sheaves of `B`-modules. -/
noncomputable abbrev naiveCotangentObj :
    DerivedCategory
      (_root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
  DerivedCategory.Q.obj (naiveCotangentComplex.{v, u, w, z} J A B a)

variable (G : _root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B))

/-- The extension group `Ext^i_B(NL_{B/A}, 𝒢)` of the naive cotangent complex of a
homomorphism of sheaves of rings by a sheaf of `B`-modules. -/
noncomputable abbrev naiveCotangentExt (i : ℤ) : Type _ :=
  DerivedCategory.Ext (naiveCotangentObj.{v, u, w, z, t} J A B a)
    ((DerivedCategory.singleFunctor _ 0).obj G) i

/-- Taking `H⁰` identifies `Ext⁰_B(NL_{B/A}, 𝒢)` with the group of homomorphisms out of the
cokernel of the conormal map of the canonical presentation, which is `H⁰(NL_{B/A})`. -/
noncomputable def naiveCotangentExtZeroAddEquivCokernel :
    naiveCotangentExt.{v, u, w, z, t} J A B a G 0 ≃+
      (cokernel (canonicalConormalSequence.{v, u, w, z} J A B a).f ⟶ G) :=
  StacksDraft.TwoTermExt.twoTermExtZeroAddEquiv
    (canonicalConormalSequence.{v, u, w, z} J A B a).f G

/-- **`Ext⁰` out of the naive cotangent complex is a homomorphism out of `Ω`.**  For a
homomorphism `a : A ⟶ B` of sheaves of commutative rings and a sheaf of `B`-modules `𝒢`,

`Ext⁰_B(NL_{B/A}, 𝒢) = Hom_B(Ω_{B/A}, 𝒢)`:

`NL_{B/A}` lives in cohomological degrees `≤ 0`, so an `Ext⁰`-class out of it is exactly a
homomorphism out of `H⁰(NL_{B/A})`, and that cohomology sheaf is `Ω_{B/A}` by the degree `0`
half of **Stacks 08TY**. -/
noncomputable def naiveCotangentExtZeroAddEquiv :
    naiveCotangentExt.{v, u, w, z, t} J A B a G 0 ≃+
      (moduleOfDifferentialsOfSite.{v, u, w, z} A B a ⟶ G) :=
  (naiveCotangentExtZeroAddEquivCokernel.{v, u, w, z, t} J A B a G).trans
    (StacksDraft.TwoTermExt.precompAddEquiv
      (canonicalConormalCokernelIsoDifferentials.{v, u, w, z} J A B a) G).symm

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- `Ext^i_B(NL_{B/A}, 𝒢)` vanishes in negative degrees: `NL_{B/A}` lives in cohomological
degrees `≤ 0` and `𝒢[0]` in degrees `≥ 0`. -/
theorem naiveCotangentExt_eq_zero_of_neg {i : ℤ} (hi : i < 0)
    (ξ : naiveCotangentExt.{v, u, w, z, t} J A B a G i) : ξ = 0 :=
  StacksDraft.TwoTermExt.twoTermExt_eq_zero_of_neg
    (canonicalConormalSequence.{v, u, w, z} J A B a).f G hi ξ

end Stacks.SheafOfModules

end
