module

public import StacksFrontier.AlgebraicGeometry.BaseAdicFiltration.AdicStageEndpoints
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsComplete
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.HypersurfaceCohomology

/-!
# The structure sheaf of an adic stage

`Stacks.BaseAdicFiltration.adicStage` cuts the stage `n` out of a family `p : U ⟶ Spec A` by the
ideal sheaf `Iⁿ⁺¹𝒪_U`, as a closed subscheme glued from spectra of quotient rings. The adic
filtration machinery of this directory instead works with
`Stacks.BaseAdicFiltration.adicQuotient`, the quotient `𝒪_U/Iⁿ⁺¹𝒪_U` formed as a cokernel of
sheaves of modules on `U`. The two describe the same object and nothing had identified them.

This file supplies the identification: the direct image of the structure sheaf of the stage is
the adic quotient. It is [Stacks, Tag 0EL1] — `Stacks.Algebraization.idealQuotientPushforwardIso`,
`F/IⁿF ≅ v_*v^*F` for a closed immersion `v` with ideal sheaf `Iⁿ` — read at `F = 𝒪_U` and
`v = adicStageι`, whose ideal sheaf is `Iⁿ⁺¹𝒪_U` by
`Stacks.BaseAdicFiltration.ker_adicStageι`, composed with the identification of the inverse image
of a structure sheaf with a structure sheaf.

The essential-surjectivity direction of [Stacks, Tag 0E3X] runs its induction up the tower of
adic stages while carrying sheaf-level data about `𝒪_U` and its filtration, so it needs exactly
this identification to pass between the two descriptions.

## Main results

* `Stacks.BaseAdicFiltration.adicQuotientIsoPushforwardStageUnit` — **the direct image of the
  structure sheaf of the stage `n` is `𝒪_U/Iⁿ⁺¹𝒪_U`.**

## Implementation notes

Both ingredients are in the library and neither is reproved here. [Stacks, Tag 0EL1] is applied with its
hypothesis discharged by `ker_adicStageι`, which holds by `Mathlib`'s `ker_subschemeι` and needs
no chart computation; the inverse image of the structure sheaf is
`AlgebraicGeometry.pullbackObjUnitIsoUnit`, itself a wrapper of
`Stacks.PullbackAlgebra.pullbackUnitIso` at the `AlgebraicGeometry.Scheme.Modules` spelling —
the spelling matters, because `Scheme.Modules.pullback` is a `def` over
`SheafOfModules.pullback` and instance search does not unfold it.

Stage `n` is cut out by the exponent `n + 1`, so the quotient identified here is the one at
exponent `n + 1`; the indexing is the one fixed in
`StacksFrontier/AlgebraicGeometry/BaseAdicFiltration/AdicStages.lean`, where stage `0` is the
special fibre.

## References

* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 0E3X](https://stacks.math.columbia.edu/tag/0E3X)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.BaseAdicFiltration

variable {A : Type u} [CommRing A] {U : Scheme.{u}} (p : U ⟶ Spec (CommRingCat.of A))
  (I : Ideal A) (n : ℕ)

/-- **The adic quotient of the structure sheaf is the direct image of the structure sheaf of the
adic stage.** For a family `p : U ⟶ Spec A` and an ideal `I` of `A`, the quotient
`𝒪_U/Iⁿ⁺¹𝒪_U`, formed as a cokernel of sheaves of modules on `U`, is the direct image along
`Stacks.BaseAdicFiltration.adicStageι` of the structure sheaf of the closed subscheme cut out by
`Iⁿ⁺¹𝒪_U`.

This is [Stacks, Tag 0EL1] at the structure sheaf, the stage's ideal sheaf being the right power
by `Stacks.BaseAdicFiltration.ker_adicStageι`. -/
def adicQuotientIsoPushforwardStageUnit :
    adicQuotient p I (n + 1) (SheafOfModules.unit U.ringCatSheaf) ≅
      (Scheme.Modules.pushforward (adicStageι p I n)).obj
        (SheafOfModules.unit (adicStage p I n).ringCatSheaf) :=
  Stacks.Algebraization.idealQuotientPushforwardIso (baseIdeal p I) (n + 1)
      (SheafOfModules.unit U.ringCatSheaf) (adicStageι p I n) (ker_adicStageι p I n) ≪≫
    (Scheme.Modules.pushforward (adicStageι p I n)).mapIso
      (AlgebraicGeometry.pullbackObjUnitIsoUnit (adicStageι p I n))

end Stacks.BaseAdicFiltration

end
