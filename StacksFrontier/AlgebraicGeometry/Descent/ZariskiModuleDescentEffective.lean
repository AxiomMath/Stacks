module

public import StacksFrontier.AlgebraicGeometry.Descent.ZariskiModuleGlueDescent

/-!
# Effectivity of quasi-coherent descent along an open covering

Stacks 023E makes two assertions about an open covering `S = ⋃ U i`: that every descent datum on
quasi-coherent sheaves for the family `U i → S` is **effective**, and *moreover* that the functor
from the quasi-coherent `𝒪_S`-modules to the descent data is **fully faithful**.  The second is
`AlgebraicGeometry.nonempty_fullyFaithful_canonicalDescentFunctor_zariski`; the first is proved
here, unconditionally.

`StacksFrontier/AlgebraicGeometry/Descent/ZariskiQuasicoherentDescent.lean` reduced the effectivity
assertion to the single statement `AlgebraicGeometry.ZariskiEssSurjToDescentDataOpens` — the
object-level Zariski stack property of `AlgebraicGeometry.modulePullbackPseudofunctor`, about
*arbitrary* sheaves of modules.  That statement is
`AlgebraicGeometry.essSurj_toDescentData_opens`, which comes from the gluing of sheaves of
modules of Stacks 00AM: a descent datum along a family of open subschemes is read as a
`Stacks.SheafOfModules.ModulesGlueData` by
`AlgebraicGeometry.modulesGlueDataOfDescentData`, and the chart comparisons of the glued module
assemble into an isomorphism of descent data by `AlgebraicGeometry.gluedDescentDataIso`.

## Main results

* `AlgebraicGeometry.zariskiEssSurjToDescentDataOpens`: the object-level Zariski stack property
  of the pullback pseudofunctor of sheaves of modules.
* `AlgebraicGeometry.isEffective_zariski`: **Stacks 023E, the effectivity assertion** — every
  quasi-coherent descent datum for a Zariski covering family is effective, with no hypothesis.

## References

* [Stacks Project, Tag 023E](https://stacks.math.columbia.edu/tag/023E)
* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe v u

namespace AlgebraicGeometry

/-- **The object-level Zariski stack property of the pullback pseudofunctor of sheaves of
modules.**  For every covering of a scheme by open subschemes, indexed in the scheme's own
universe, `CategoryTheory.Pseudofunctor.toDescentData` is essentially surjective.

This is `AlgebraicGeometry.essSurj_toDescentData_opens`, which needs no hypothesis that the
family covers. -/
public theorem zariskiEssSurjToDescentDataOpens : ZariskiEssSurjToDescentDataOpens.{u} :=
  fun _ _ ↦ essSurj_toDescentData_opens

/-- **Stacks 023E, the effectivity assertion, with no hypothesis.**  Every quasi-coherent descent
datum for a Zariski covering family of a scheme is effective.

Stacks 023E makes two assertions in one statement — this one and, *moreover*, that the functor
from the quasi-coherent `𝒪_S`-modules to the descent data is fully faithful — so this declaration
is half of its covering set, and the clause string on the attribute says so.  The other half is
`AlgebraicGeometry.nonempty_fullyFaithful_canonicalDescentFunctor_zariski`.

The proof is `AlgebraicGeometry.isEffective_of_zariskiEssSurjToDescentDataOpens`, whose single
hypothesis is discharged by `AlgebraicGeometry.zariskiEssSurjToDescentDataOpens`. -/
-- 023E's attribute lives on the pair (`QuasiCoherent/ZariskiEssSurj.lean`,
-- `QuasiCoherent/ZariskiGluing.lean`): those declarations and the ones here are pure
-- duplicates with neither subsuming, and that file is kept because it
-- registers the two prestack instances. One tag has one covering set.
public theorem isEffective_zariski {S : Scheme.{u}} {I : Type v} {X : I → Scheme.{u}}
    {f : ∀ i, X i ⟶ S} (hf : Presieve.ofArrows X f ∈ Scheme.zariskiPrecoverage.{u} S)
    (D : QuasicoherentDescentData f) : D.IsEffective :=
  isEffective_of_zariskiEssSurjToDescentDataOpens zariskiEssSurjToDescentDataOpens hf D

end AlgebraicGeometry

end
