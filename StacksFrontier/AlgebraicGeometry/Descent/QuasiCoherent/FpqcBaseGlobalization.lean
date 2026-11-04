module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.SigmaSummands

/-!
# What the effectivity half of Stacks 023T rests on: one morphism over one base

`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherent/FpqcEffective.lean` reduces the effectivity
half of Stacks 023T, for an arbitrary fpqc covering family of an arbitrary scheme and at an
arbitrary index universe, to two statements:
`AlgebraicGeometry.QuasicoherentDescentData.SigmaEssSurjOverAnyBase`, that restriction along the
coproduct refinement of a `Type u`-indexed family is essentially surjective, and
`AlgebraicGeometry.QuasicoherentDescentData.EffectiveSigmaFamilyOverAnyBase`, that every
quasi-coherent descent datum for the single morphism `∐ X i ⟶ S` is effective.

The first of those is a theorem:
`AlgebraicGeometry.QuasicoherentDescentData.essSurj_pullFunctor_toSigmaFamily` of
`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherent/SigmaSummands.lean` proves it for every
family over every base.  That file is downstream of `FpqcEffective`, which is why the
discharge is recorded here and not there.

What is left is one classical statement: **descent along a single faithfully flat morphism over
a base which is not assumed affine.**  Over a spectrum it is proved —
`AlgebraicGeometry.QuasicoherentDescentData.isEffective_fpqcPrecoverage_spec` — and
`AlgebraicGeometry.QuasicoherentDescentData.effectiveSigmaFamilyOverAnyBase_of_forall` shows
that assuming it over an arbitrary base asks for nothing beyond Stacks 023T itself.

## Main results

* `AlgebraicGeometry.QuasicoherentDescentData.sigmaEssSurjOverAnyBase`: the coproduct half,
  discharged.
* `AlgebraicGeometry.QuasicoherentDescentData.isEffective_fpqcPrecoverage_of_sigmaFamily`:
  **the effectivity half of Stacks 023T over `EffectiveSigmaFamilyOverAnyBase` alone**, for an
  arbitrary fpqc covering family of an arbitrary scheme at an arbitrary index universe.
* `AlgebraicGeometry.QuasicoherentDescentData.effectiveOverSpecBaseGlobalizes_of_sigmaFamily`:
  the globalization hypothesis `EffectiveOverSpecBaseGlobalizes`, over that one statement.
* `AlgebraicGeometry.QuasicoherentDescentData.effectiveSigmaFamilyOverAnyBase_iff`: that one
  statement is *equivalent* to the effectivity half of Stacks 023T, so it is a reformulation of
  what is missing and not a reduction of it to something stronger.

## Implementation notes

No `stacks` attribute is placed: every general statement here carries a hypothesis, and a
hypothesis is part of a citation.

## References

* [Stacks Project, Tag 023S](https://stacks.math.columbia.edu/tag/023S)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

@[expose] public section

open CategoryTheory

universe v u

namespace AlgebraicGeometry

namespace QuasicoherentDescentData

/-- **The coproduct refinement is essentially surjective over an arbitrary base.**  This is
`AlgebraicGeometry.QuasicoherentDescentData.SigmaEssSurjOverAnyBase` discharged by
`AlgebraicGeometry.QuasicoherentDescentData.essSurj_pullFunctor_toSigmaFamily`, which asks
nothing of the family beyond the smallness of its index and nothing at all of the base. -/
public theorem sigmaEssSurjOverAnyBase : SigmaEssSurjOverAnyBase.{u} :=
  fun 𝒲 ↦ essSurj_pullFunctor_toSigmaFamily 𝒲

/-- **The effectivity half of [Stacks, Tag 023T] over one hypothesis.**  For every fpqc covering
family of every scheme, at every index universe, every quasi-coherent descent datum is
effective, over `EffectiveSigmaFamilyOverAnyBase` and nothing else.

Every other input is proved: Stacks 022E made global
(`AlgebraicGeometry.QuasicoherentDescentData.exists_small_fpqc_refinement`) replaces the given
family by a `Type u`-indexed fpqc refinement, the refinement transport carries effectivity back
along it, and `sigmaEssSurjOverAnyBase` collapses the refinement to its one-element coproduct
family. -/
public theorem isEffective_fpqcPrecoverage_of_sigmaFamily
    (hsig : EffectiveSigmaFamilyOverAnyBase.{u}) {S : Scheme.{u}}
    (𝒰 : PreZeroHypercover.{v} S) (h𝒰 : 𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage.{u} S)
    (D : QuasicoherentDescentData 𝒰.f) : D.IsEffective :=
  isEffective_of_mem_fpqcPrecoverage_of_sigma sigmaEssSurjOverAnyBase hsig 𝒰 h𝒰 D

/-- **The globalization of the source's first passage, over the one-element case alone.**  The
antecedent of `EffectiveOverSpecBaseGlobalizes` is not used: the affine base is given up at the
one morphism `∐ X i ⟶ S` instead. -/
public theorem effectiveOverSpecBaseGlobalizes_of_sigmaFamily
    (hsig : EffectiveSigmaFamilyOverAnyBase.{u}) : EffectiveOverSpecBaseGlobalizes.{v, u} :=
  effectiveOverSpecBaseGlobalizes_of_sigma sigmaEssSurjOverAnyBase hsig

/-- **The one remaining statement is exactly the effectivity half of [Stacks, Tag 023T].**
Descent along the single morphism `∐ X i ⟶ S` over an arbitrary base is equivalent to
effectivity for every fpqc covering family of every scheme, so it is a reformulation of what is
missing and neither a weakening nor a strengthening of it.

The forward implication is `isEffective_fpqcPrecoverage_of_sigmaFamily` read at the index
universe `u`; the backward one is
`AlgebraicGeometry.QuasicoherentDescentData.effectiveSigmaFamilyOverAnyBase_of_forall`. -/
public theorem effectiveSigmaFamilyOverAnyBase_iff :
    EffectiveSigmaFamilyOverAnyBase.{u} ↔
      ∀ {S : Scheme.{u}} (𝒰 : PreZeroHypercover.{u} S),
        𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage.{u} S →
          ∀ D : QuasicoherentDescentData 𝒰.f, D.IsEffective :=
  ⟨fun hsig _ 𝒰 h𝒰 D ↦ isEffective_fpqcPrecoverage_of_sigmaFamily hsig 𝒰 h𝒰 D,
    effectiveSigmaFamilyOverAnyBase_of_forall⟩

end QuasicoherentDescentData

end AlgebraicGeometry

end
