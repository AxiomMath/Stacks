module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.FormalFunctionsAdicLimitUnconditional

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.CohomologyAdicUniformBoundsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.FormalFunctions
public import StacksFrontier.RingTheory.AdicCompletion.Basic
public import StacksFrontier.RingTheory.AdicCompletion.IntertwinedFiltrationEventualRange
public import StacksFrontier.RingTheory.AdicCompletion.HomBijection.EventualRangeTopology
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyAdicUniformBoundsSpace

/-!
# The theorem on formal functions for algebraic spaces

In Situation 08AV — a Noetherian ring `A` with an ideal `I`, a proper morphism
`f : X ⟶ Spec A` of algebraic spaces and a coherent `𝒪_X`-module `F` — fix `p ≥ 0` and write
`M = Hᵖ(X, F)` and `Mₙ = Hᵖ(X, F / Iⁿ F)`.  [Stacks, Tag 08AZ] says that the maps
`M / Iⁿ M ⟶ Mₙ` define an isomorphism `M^∧ ⟶ lim Mₙ` from the `I`-adic completion of `M`, and
that it is a homeomorphism for the limit topologies.  [Stacks, Tag 08B0] says that when `A` is
moreover `I`-adically complete, `M` itself is `lim Mₙ`.

The proof is the source's, with nothing assumed beyond Situation 08AV.  By [Stacks, Tag 08AY]
(`AlgebraicGeometry.Space.C1573.exists_ker_cohomologyIdealQuotientProj_le` and
`AlgebraicGeometry.Space.C1573.exists_range_cohomologyIdealQuotientTr_eq`, both proved) the
kernels of `M ⟶ Mₙ` are intertwined with the `I`-adic filtration of `M`, and the images of the
transition maps into `Mₙ` are eventually the image of `M`; the comparison is then
`Stacks.IntertwinedFiltration.adicCompletionEquivTowerLimitOfEventualRange`.  For 08B0, `M` is
a finite module over the complete Noetherian ring `A` ([Stacks, Tag 08AS]), hence `I`-adically
complete.

## Main definitions

The `C1573` declarations are in the module of the same name under
`GrothendieckExistence.HomBijection`; this file restates their Situation 08AV results in the
namespace `AlgebraicGeometry.Space`.

* `AlgebraicGeometry.Space.C1573.cohomologyIdealQuotientLimit`: the limit `lim_n Hᵖ(X, F / Iⁿ F)`.
* `AlgebraicGeometry.Space.formalFunctionsEquiv`: the comparison `Hᵖ(X, F)^∧ ≃ lim_n Mₙ`.
* `AlgebraicGeometry.Space.C1573.cohomologyToIdealQuotientLimit`: the map `Hᵖ(X, F) ⟶ lim_n Mₙ`.

## Main results

* `AlgebraicGeometry.Space.formalFunctionsEquiv`,
  `AlgebraicGeometry.Space.formalFunctionsEquiv_apply` and
  `AlgebraicGeometry.Space.isHomeomorph_formalFunctionsEquiv`: **[Stacks, Tag 08AZ]**, the
  isomorphism, that it is defined by the system of maps `M / Iⁿ M ⟶ Mₙ`, and that it is a
  homeomorphism for the limit topologies.
* `AlgebraicGeometry.Space.C1573.formalFunctionsEquivOfIsAffine` and
  `AlgebraicGeometry.Space.C1573.formalFunctionsEquivOfIsAffine_apply`: the isomorphism of
  [Stacks, Tag 08AZ] for a proper morphism to an affine object of the site over an arbitrary
  base scheme, whose functions are identified with the Noetherian ring `A`.
* `AlgebraicGeometry.Space.bijective_cohomologyToIdealQuotientLimit`: **[Stacks, Tag 08B0]**.

## Implementation notes

The limit topologies are the topologies induced from the products of the discrete topologies of
the terms of the two towers (`Stacks.IntertwinedFiltration.C1573.adicCompletionLimitTopology`
and `Stacks.IntertwinedFiltration.C1573.towerLimitTopology`).

## References

* [Stacks Project, Tag 08AZ](https://stacks.math.columbia.edu/tag/08AZ)
* [Stacks Project, Tag 08B0](https://stacks.math.columbia.edu/tag/08B0)
* [Stacks Project, Tag 08AY](https://stacks.math.columbia.edu/tag/08AY)
* [Stacks Project, Tag 08AV](https://stacks.math.columbia.edu/tag/08AV)
* [Stacks Project, Tag 02OC](https://stacks.math.columbia.edu/tag/02OC)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.IntertwinedFiltration Stacks.Cohomology.SiteModules
open scoped IsMulCommutative

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] hasInjectiveResolutions_modules

section Situation

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}
  {X : AlgebraicSpaces B (Spec (.of A)) hA} [IsNoetherianRing A]
  (f : X ⟶ schemeSpace (baseObject A B hA)) (hf : IsProper B (Spec (.of A)) hA f.hom)
  (F : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) [IsCoherent B (Spec (.of A)) hA X.1 X.2 F]
  (I : Ideal A) (p : ℕ)

/-- **Stacks 08AZ, the isomorphism.**  In Situation 08AV, for every `p` the maps
`Hᵖ(X, F) / Iⁿ Hᵖ(X, F) ⟶ Hᵖ(X, F / Iⁿ F)` define an isomorphism
`Hᵖ(X, F)^∧ ⟶ lim_n Hᵖ(X, F / Iⁿ F)` from the `I`-adic completion; that it is defined by those
maps is `formalFunctionsEquiv_apply`. -/
@[stacks 08AZ "the isomorphism of limits"]
def formalFunctionsEquiv :
    AdicCompletion I (cohomologyRes (baseRingHom A B hA X.1 X.2) p F) ≃ₗ[A]
      C1573.cohomologyIdealQuotientLimit (baseRingHom A B hA X.1 X.2) F I p :=
  by apply C1573.formalFunctionsEquiv <;> assumption

/-- **Stacks 08AZ, the isomorphism is the one defined by the system of maps**: the `n`-th
component of the image of `w ∈ Hᵖ(X, F)^∧` is the image of the `n`-th component of `w` under
`Hᵖ(X, F) / Iⁿ Hᵖ(X, F) ⟶ Hᵖ(X, F / Iⁿ F)`. -/
@[stacks 08AZ "the isomorphism is the one defined by the system of maps"]
theorem formalFunctionsEquiv_apply
    (w : AdicCompletion I (cohomologyRes (baseRingHom A B hA X.1 X.2) p F)) (n : ℕ) :
    ((formalFunctionsEquiv f hf F I p w : C1573.cohomologyIdealQuotientLimit _ F I p) :
      ∀ k, C1573.cohomologyIdealQuotient (baseRingHom A B hA X.1 X.2) F I p k) n =
      C1573.adicQuotientMap _
        (C1573.cohomologyIdealQuotientProj (baseRingHom A B hA X.1 X.2) F I p) I
        (C1573.pow_smul_top_le_ker_cohomologyIdealQuotientProj _ F I p) n (w.val n) :=
  by apply C1573.formalFunctionsEquiv_apply

/-- **Stacks 08AZ, the homeomorphism**: the comparison is a homeomorphism for the limit
topologies. -/
@[stacks 08AZ "the isomorphism is a homeomorphism for the limit topologies"]
theorem isHomeomorph_formalFunctionsEquiv :
    @IsHomeomorph _ _
      (C1573.adicCompletionLimitTopology I (cohomologyRes (baseRingHom A B hA X.1 X.2) p F))
      (C1573.towerLimitTopology _ _) (formalFunctionsEquiv f hf F I p) :=
  by apply C1573.isHomeomorph_formalFunctionsEquiv

include hf in
/-- **Stacks 08B0.**  Let `A` be a Noetherian ring complete with respect to an ideal `I`,
`f : X ⟶ Spec A` a proper morphism of algebraic spaces and `F` a coherent `𝒪_X`-module.  Then
`Hᵖ(X, F) ⟶ lim_n Hᵖ(X, F / Iⁿ F)` is an isomorphism for every `p`. -/
@[stacks 08B0]
theorem bijective_cohomologyToIdealQuotientLimit [IsAdicComplete I A] :
    Function.Bijective
      (C1573.cohomologyToIdealQuotientLimit (baseRingHom A B hA X.1 X.2) F I p) :=
  by apply C1573.bijective_cohomologyToIdealQuotientLimit <;> assumption

end Situation

end AlgebraicGeometry.Space

end
