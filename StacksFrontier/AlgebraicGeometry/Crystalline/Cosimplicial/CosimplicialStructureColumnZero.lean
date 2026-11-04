module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedRingPAdicComplete
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CosimplicialDeRhamColumnZero
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CosimplicialStructurePair

/-!
# The column `a = 0` of the structure sheaf's double complex `K`, unconditionally

`Crystalline.CosimplicialCompletedModule.columnZeroIso` identifies the column `a = 0` of the
double complex `K^{a,b} = M(b) ⊗̂_{D(b)} Ω^a_{D(b)}` of
[Stacks, Proposition 60.21.3, Tag 07LG] with the cosimplicial module `M(•)`, for an *arbitrary*
`Crystalline.CosimplicialCompletedPair`.  It has one standing hypothesis,
`[∀ b, IsAdicComplete (pAdicIdeal (A := E.completedRing p b) p) (W.carrier b)]` — item (07JB) of
[Stacks, Lemma 60.17.3, Tag 07JG] in each cosimplicial degree.

For the pair of the coefficient sheaf `𝒪_{X/S}`, `Crystalline.CosimplicialDPAlgebra.structurePair`,
the module is the ring, `M(b) = D̂(b)`, so that hypothesis is the completeness of the completion
and is no longer a hypothesis: it is
`Crystalline.instIsAdicCompleteCompletedDividedPowerRing`.  This module supplies it in the three
spellings instance resolution needs — `Crystalline.CosimplicialDPAlgebra.structureModule`,
`Crystalline.CosimplicialDPAlgebra.structurePair` and `Crystalline.envelopeStructurePair` are
`def`s and not `abbrev`s, so the projection `W.carrier b` does not reduce to
`Crystalline.CosimplicialDPAlgebra.completedRing` at instance transparency — and then
instantiates the column-zero edge, so that for the structure sheaf it is a theorem about the
actual cosimplicial envelope `D(*)` of [Stacks, Equation 60.17.3, Tag 07JF] and not a statement
with a carried hypothesis.

## What this does and does not do to [Stacks, Tag 07LG]

**No `@[stacks 07LG]` attribute is placed.**  [Stacks, Tag 07LG] is
`...SmallSite.crystalPairDeRhamComplex_computesCohomology` of
`SmallSite/CrystalDeRhamComputesCohomology.lean`.  The hypothesis list of
`...SmallSite.computes07LG_of_doubleComplex` is `K`, `hcolumns`, `hrows`, `hrow0`, `hcolumn0`,
`hker`, and what this module touches is the *first half* of `hcolumn0` only, at the single
coefficient sheaf `𝒪_{X/S}`.

`hcolumn0` asks, for every quasi-coherent `ℱ`, for an identification of the cohomology of the
Moore complex of `K^{0,•}` with the cohomology of `...SmallSite.sectionsComplex`.  Two things
separate what is proved here from that:

* the identification proved here lands on the Moore complex of `M(•)`, and the comparison of
  *that* with `...SmallSite.sectionsComplex` is the whole content of the crystal property
  `...SmallSite.IsCrystalLevelQuotient` — it carries no forms and no completed tensor product and
  is untouched;
* `hcolumn0` is quantified over all quasi-coherent `ℱ`, while
  `Crystalline.CosimplicialDPAlgebra.structurePair` is the pair of `ℱ = 𝒪_{X/S}` alone.  For a
  general crystal the cosimplicial pair is `...SmallSite.crystalCosimplicialPair`, built by base
  change along the coprojections rather than from a per-degree
  `Crystalline.FirstOrderComparison`.

## Main definitions

* `Crystalline.CosimplicialDPAlgebra.structureColumnZeroEquiv` — **`D̂(b) ⊗̂_{D(b)} Ω^0_{D(b)} ≅
  D̂(b)`** in each cosimplicial degree, with no completeness hypothesis.
* `Crystalline.CosimplicialDPAlgebra.structureColumnZeroIso` — **the column `a = 0` of the
  structure sheaf's `K` is the cosimplicial ring `D̂(•)`**.
* `Crystalline.CosimplicialDPAlgebra.structureMooreHomologyColumnZeroIso` — the induced
  identification of the cohomology of the two Moore complexes, which is the shape the first half
  of `hcolumn0` is stated in.
* `Crystalline.envelopeStructureColumnZeroIso` and
  `Crystalline.envelopeStructureMooreHomologyColumnZeroIso` — the same two at the actual
  cosimplicial envelope `D(*)`.

## Main results

* `Crystalline.CosimplicialDPAlgebra.instStructureModuleCarrierIsAdicComplete`,
  `...instStructurePairCarrierIsAdicComplete` and
  `Crystalline.instEnvelopeStructurePairCarrierIsAdicComplete` — **item (07JB) for the structure
  sheaf's cosimplicial module**, as instances in the three spellings the consumers present.
* `Crystalline.CosimplicialDPAlgebra.structureColumnZeroEquiv_of_tmul` — the equation pinning the
  degree-zero identification down: `x ⊗ ω ↦ ω · x`.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Equation 60.17.3, Tag 07JF](https://stacks.math.columbia.edu/tag/07JF)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicTopology
open DividedPowers
open scoped TensorProduct

universe u v w uC

namespace Crystalline

namespace CosimplicialDPAlgebra

variable {A : Type u} [CommRing A] (E : CosimplicialDPAlgebra.{u, v} A) (p : ℕ)

/-! ### Item (07JB) for the cosimplicial module `b ↦ D̂(b)` -/

/-- **Item (07JB) of [Stacks, Lemma 60.17.3, Tag 07JG] for the cosimplicial module of the
structure sheaf**: each `M(b) = D̂(b)` is `p`-adically complete, being the `p`-adic completion of
`D(b)`.

It is stated at the projection `(E.structureModule p).carrier b` and not at
`Crystalline.CosimplicialDPAlgebra.completedRing` because
`Crystalline.CosimplicialDPAlgebra.structureModule` is a `def`: instance resolution does not
unfold it, so `Crystalline.instIsAdicCompleteCompletedDividedPowerRing` alone does not fire at
this goal. -/
instance instStructureModuleCarrierIsAdicComplete (b : ℕ) :
    IsAdicComplete (pAdicIdeal (A := E.completedRing p b) p)
      ((E.structureModule p).carrier b) :=
  instIsAdicCompleteCompletedDividedPowerRing p

/-- **Item (07JB) for the cosimplicial module of the structure sheaf**, at the spelling the
pair's consumers present.  `Crystalline.CosimplicialDPAlgebra.structurePair` is a `def` too, so
this is a second spelling of
`Crystalline.CosimplicialDPAlgebra.instStructureModuleCarrierIsAdicComplete` and not a
consequence of it at instance transparency. -/
instance instStructurePairCarrierIsAdicComplete (b : ℕ) :
    IsAdicComplete (pAdicIdeal (A := E.completedRing p b) p)
      ((E.structurePair p).carrier b) :=
  instIsAdicCompleteCompletedDividedPowerRing p

/-! ### The column `a = 0` of the structure sheaf's double complex -/

/-- **`D̂(b) ⊗̂_{D(b)} Ω^0_{D(b)} ≅ D̂(b)`**, the degree-`(0, b)` term of the structure sheaf's
double complex `K`.  This is
`Crystalline.CosimplicialCompletedModule.columnZeroEquiv` with its completeness hypothesis
discharged. -/
def structureColumnZeroEquiv (b : ℕ) :
    (E.structureModule p).obj 0 b ≃+ E.completedRing p b :=
  (E.structureModule p).columnZeroEquiv b

/-- **The equation pinning the degree-zero identification of the structure sheaf's `K` down**: it
carries the image of the pure tensor `x ⊗ ω` to `ω · x`, the zero-form `ω` read as a scalar. -/
theorem structureColumnZeroEquiv_of_tmul (b : ℕ) (x : E.completedRing p b)
    (omega : E.forms p 0 b) :
    E.structureColumnZeroEquiv p b (toCompletedTensor p (E.completedRing p b) (E.forms p 0 b)
        (E.completedRing p b) (x ⊗ₜ[E.completedRing p b] omega)) =
      E.formsZeroEquiv p b omega • x :=
  (E.structureModule p).columnZeroEquiv_of_tmul b x omega

/-- **The column `a = 0` of the structure sheaf's double complex `K` is the cosimplicial ring
`D̂(•)`**, as an isomorphism of cosimplicial abelian groups and not merely a family of
isomorphisms.

This is `Crystalline.CosimplicialCompletedModule.columnZeroIso` at
`Crystalline.CosimplicialDPAlgebra.structureModule`, where its standing completeness hypothesis
is no longer carried. -/
def structureColumnZeroIso :
    (E.structureModule p).column 0 ≅ (E.structureModule p).carrierCosimplicial :=
  (E.structureModule p).columnZeroIso

/-- **The cohomology of the Moore complex of the column `a = 0` of the structure sheaf's `K` is
the cohomology of the Moore complex of `D̂(•)`.**

This is the shape the first half of the hypothesis `hcolumn0` of
`...SmallSite.computes07LG_of_doubleComplex` is stated in; what that hypothesis still asks for is
the comparison of the Moore complex of `D̂(•)` with `...SmallSite.sectionsComplex`, which carries
no forms and is where `...SmallSite.IsCrystalLevelQuotient` enters. -/
def structureMooreHomologyColumnZeroIso (j : ℕ) :
    ((alternatingCofaceMapComplex AddCommGrpCat.{v}).obj
        ((E.structureDoubleComplex p).X 0)).homology j ≅
      ((alternatingCofaceMapComplex AddCommGrpCat.{v}).obj
        (E.structureModule p).carrierCosimplicial).homology j :=
  (E.structurePair p).mooreHomologyDoubleComplexXZeroIso j

end CosimplicialDPAlgebra

/-! ### The same two at the actual cosimplicial envelope `D(*)` -/

section Envelope

variable (s : AffineCrystallineSituation.{u, uC}) {ι : Type w}
  (f : MvPolynomial ι s.A →ₐ[s.A] s.C)

/-- **Item (07JB) for the cosimplicial module of the structure sheaf at the actual cosimplicial
envelope.**  `Crystalline.envelopeStructurePair` is a `def`, so this is a third spelling of
`Crystalline.CosimplicialDPAlgebra.instStructureModuleCarrierIsAdicComplete`; without it the
instantiation below does not synthesize. -/
instance instEnvelopeStructurePairCarrierIsAdicComplete (b : ℕ) :
    IsAdicComplete (pAdicIdeal (A := (envelopeDPAlgebra s f).completedRing s.p b) s.p)
      ((envelopeStructurePair s f).carrier b) :=
  instIsAdicCompleteCompletedDividedPowerRing s.p

/-- **The column `a = 0` of the double complex `K` of the actual cosimplicial envelope `D(*)` and
the structure sheaf is the cosimplicial ring `D̂(•)`.** -/
def envelopeStructureColumnZeroIso :
    ((envelopeDPAlgebra s f).structureModule s.p).column 0 ≅
      ((envelopeDPAlgebra s f).structureModule s.p).carrierCosimplicial :=
  (envelopeDPAlgebra s f).structureColumnZeroIso s.p

/-- **The cohomology of the Moore complex of the column `a = 0` of the actual envelope's `K` is
the cohomology of the Moore complex of `D̂(•)`** — the first half of `hcolumn0` for the structure
sheaf, at the rings `D(b)` of [Stacks, Equation 60.17.3, Tag 07JF]. -/
def envelopeStructureMooreHomologyColumnZeroIso (j : ℕ) :
    ((alternatingCofaceMapComplex AddCommGrpCat.{max u w}).obj
        ((envelopeStructureDoubleComplex s f).X 0)).homology j ≅
      ((alternatingCofaceMapComplex AddCommGrpCat.{max u w}).obj
        ((envelopeDPAlgebra s f).structureModule s.p).carrierCosimplicial).homology j :=
  (envelopeStructurePair s f).mooreHomologyDoubleComplexXZeroIso j

end Envelope

end Crystalline

end
