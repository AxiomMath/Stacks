module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.CohomologyAdicUniformBoundsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.FormalFunctions
public import StacksFrontier.RingTheory.AdicCompletion.Basic
public import StacksFrontier.RingTheory.AdicCompletion.IntertwinedFiltrationEventualRange
public import StacksFrontier.RingTheory.AdicCompletion.HomBijection.EventualRangeTopology

/-!
# The theorem on formal functions for algebraic spaces

In Situation 08AV — a Noetherian ring `A` with an ideal `I`, a proper morphism
`f : X ⟶ Spec A` of algebraic spaces and a coherent `𝒪_X`-module `F` — fix `p ≥ 0` and write
`M = Hᵖ(X, F)` and `Mₙ = Hᵖ(X, F / Iⁿ F)`.  [Stacks, Tag 08AZ] says that the maps
`M / Iⁿ M ⟶ Mₙ` define an isomorphism `M^∧ ⟶ lim Mₙ` from the `I`-adic completion of `M`, and
that it is a homeomorphism for the limit topologies.  [Stacks, Tag 08B0] says that when `A` is
moreover `I`-adically complete, `M` itself is `lim Mₙ`.

## Main definitions

* `AlgebraicGeometry.Space.C1573.cohomologyIdealQuotientLimit`: the limit `lim_n Hᵖ(X, F / Iⁿ F)`.
* `AlgebraicGeometry.Space.C1573.formalFunctionsEquiv`: the comparison `Hᵖ(X, F)^∧ ≃ lim_n Mₙ`.
* `AlgebraicGeometry.Space.C1573.cohomologyToIdealQuotientLimit`: the map `Hᵖ(X, F) ⟶ lim_n Mₙ`.
* `AlgebraicGeometry.Space.C1573.cohomologyEquivIdealQuotientLimit`: for `A` complete, the
  isomorphism `Hᵖ(X, F) ≃ lim_n Mₙ`.

## Main results

* `AlgebraicGeometry.Space.C1573.formalFunctionsEquiv`,
  `AlgebraicGeometry.Space.C1573.formalFunctionsEquiv_apply` and
  `AlgebraicGeometry.Space.C1573.isHomeomorph_formalFunctionsEquiv`: **[Stacks, Tag 08AZ]**, the
  isomorphism, that it is defined by the system of maps `M / Iⁿ M ⟶ Mₙ`, and that it is a
  homeomorphism for the limit topologies.
* `AlgebraicGeometry.Space.C1573.formalFunctionsEquivOfIsAffine` and
  `AlgebraicGeometry.Space.C1573.formalFunctionsEquivOfIsAffine_apply`: the isomorphism of
  [Stacks, Tag 08AZ] for a proper morphism to an affine object of the site over an arbitrary
  base scheme, whose functions are identified with the Noetherian ring `A`.
* `AlgebraicGeometry.Space.C1573.bijective_cohomologyToIdealQuotientLimit`: **[Stacks, Tag 08B0]**.

## Implementation notes

The limit topologies are the topologies induced from the products of the discrete topologies
of the terms of the two towers
(`Stacks.IntertwinedFiltration.C1573.adicCompletionLimitTopology` and
`Stacks.IntertwinedFiltration.C1573.towerLimitTopology`).

## References

* [Stacks Project, Tag 08AZ](https://stacks.math.columbia.edu/tag/08AZ)
* [Stacks Project, Tag 08B0](https://stacks.math.columbia.edu/tag/08B0)
* [Stacks Project, Tag 08AY](https://stacks.math.columbia.edu/tag/08AY)
* [Stacks Project, Tag 08AV](https://stacks.math.columbia.edu/tag/08AV)
* [Stacks Project, Tag 02OC](https://stacks.math.columbia.edu/tag/02OC)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.IntertwinedFiltration Stacks.IntertwinedFiltration.C1573
open Stacks.Cohomology.SiteModules
open scoped IsMulCommutative

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space.C1573

attribute [local instance] hasInjectiveResolutions_modules

section Tower

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} {A : Type u} [CommRing A]
  (φ : A →+* ↥(GlobalSectionRing
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))))
  (F : Modules.{u, u} B S hS X.1 X.2) (I : Ideal A) (p : ℕ)

/-- The limit `lim_n Hᵖ(X, F / Iⁿ F)`. -/
abbrev cohomologyIdealQuotientLimit :=
  towerLimit (fun n => cohomologyIdealQuotient φ F I p n)
    (fun _ _ h => cohomologyIdealQuotientTr φ F I p h)

/-- `Iⁿ Hᵖ(X, F)` lies in the kernel of `Hᵖ(X, F) ⟶ Hᵖ(X, F / Iⁿ F)`, which is killed by `Iⁿ`. -/
theorem pow_smul_top_le_ker_cohomologyIdealQuotientProj (n : ℕ) :
    I ^ n • (⊤ : Submodule A (cohomologyRes φ p F)) ≤
      LinearMap.ker (cohomologyIdealQuotientProj φ F I p n) := by
  refine Submodule.smul_le.2 fun a ha x _ => ?_
  rw [LinearMap.mem_ker, map_smul]
  exact (Submodule.eq_bot_iff _).1 (pow_smul_top_cohomologyIdealQuotient φ F I p n) _
    (Submodule.smul_mem_smul ha Submodule.mem_top)

/-- The map `Hᵖ(X, F) ⟶ lim_n Hᵖ(X, F / Iⁿ F)`. -/
def cohomologyToIdealQuotientLimit :
    cohomologyRes φ p F →ₗ[A] cohomologyIdealQuotientLimit φ F I p :=
  towerLimitLift _ _ (cohomologyIdealQuotientProj φ F I p)
    (fun _ _ h => cohomologyIdealQuotientTr_comp_proj φ F I p h)

end Tower

section OverAffine

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {V : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] {A : Type u} [CommRing A] [IsNoetherianRing A]
  (α : A ≃+* Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) {X : AlgebraicSpaces B S hS}
  (f : X ⟶ schemeSpace V) (hf : IsProper B S hS f.hom)
  (φ : A →+* ↥(GlobalSectionRing
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))))
  (hφ : ∀ a, φ a = pullbackToGlobalFunctions B S hS X V f (α a))
  (F : Modules.{u, u} B S hS X.1 X.2) [IsCoherent B S hS X.1 X.2 F] (I : Ideal A) (p : ℕ)

/-- The shift `c₁` of clause (1) of Stacks 08AY, over an affine object of the site. -/
def formalFunctionsShiftOfIsAffine : ℕ :=
  (exists_ker_cohomologyIdealQuotientProj_le_of_isAffine α f hf φ hφ F I p).choose

/-- **Stacks 08AZ over an affine object of the site.**  Let `p : X ⟶ V` be a proper morphism of
algebraic spaces over `S` to an affine object `V` of the site whose functions are identified with
the Noetherian ring `A` by `α`, let `φ` be the resulting map from `A` to the functions on `X`,
`I ⊆ A` an ideal and `F` a coherent `𝒪_X`-module.  Then the maps
`Hᵖ(X, F) / Iⁿ Hᵖ(X, F) ⟶ Hᵖ(X, F / Iⁿ F)` define an isomorphism
`Hᵖ(X, F)^∧ ⟶ lim_n Hᵖ(X, F / Iⁿ F)`. -/
def formalFunctionsEquivOfIsAffine :
    AdicCompletion I (cohomologyRes φ p F) ≃ₗ[A] cohomologyIdealQuotientLimit φ F I p :=
  adicCompletionEquivTowerLimitOfEventualRange _ _ (cohomologyIdealQuotientProj φ F I p) I
    (formalFunctionsShiftOfIsAffine α f hf φ hφ F I p)
    (fun _ _ h => cohomologyIdealQuotientTr_comp_proj _ F I p h)
    (pow_smul_top_le_ker_cohomologyIdealQuotientProj _ F I p)
    (exists_ker_cohomologyIdealQuotientProj_le_of_isAffine α f hf φ hφ F I p).choose_spec
    (fun n => exists_range_cohomologyIdealQuotientTr_eq_of_isAffine α f hf φ hφ F I p n)

/-- The `n`-th component of the image of `w ∈ Hᵖ(X, F)^∧` under
`AlgebraicGeometry.Space.C1573.formalFunctionsEquivOfIsAffine` is the image of the `n`-th component
of `w` under `Hᵖ(X, F) / Iⁿ Hᵖ(X, F) ⟶ Hᵖ(X, F / Iⁿ F)`. -/
theorem formalFunctionsEquivOfIsAffine_apply (w : AdicCompletion I (cohomologyRes φ p F))
    (n : ℕ) :
    ((formalFunctionsEquivOfIsAffine α f hf φ hφ F I p w : cohomologyIdealQuotientLimit φ F I p) :
      ∀ k, cohomologyIdealQuotient φ F I p k) n =
      adicQuotientMap _ (cohomologyIdealQuotientProj φ F I p) I
        (pow_smul_top_le_ker_cohomologyIdealQuotientProj _ F I p) n (w.val n) :=
  adicCompletionEquivTowerLimitOfEventualRange_apply _ _ _ I _ _ _ _ _ w n

end OverAffine

section Situation

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}
  {X : AlgebraicSpaces B (Spec (.of A)) hA} [IsNoetherianRing A]
  (f : X ⟶ schemeSpace (baseObject A B hA)) (hf : IsProper B (Spec (.of A)) hA f.hom)
  (F : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) [IsCoherent B (Spec (.of A)) hA X.1 X.2 F]
  (I : Ideal A) (p : ℕ)

/-- The shift `c₁` of clause (1) of Stacks 08AY. -/
def formalFunctionsShift : ℕ :=
  (exists_ker_cohomologyIdealQuotientProj_le f hf F I p).choose

/-- **Stacks 08AZ, the isomorphism.**  In Situation 08AV, for every `p` the maps
`Hᵖ(X, F) / Iⁿ Hᵖ(X, F) ⟶ Hᵖ(X, F / Iⁿ F)` define an isomorphism
`Hᵖ(X, F)^∧ ⟶ lim_n Hᵖ(X, F / Iⁿ F)` from the `I`-adic completion. -/
def formalFunctionsEquiv :
    AdicCompletion I (cohomologyRes (baseRingHom A B hA X.1 X.2) p F) ≃ₗ[A]
      cohomologyIdealQuotientLimit (baseRingHom A B hA X.1 X.2) F I p :=
  adicCompletionEquivTowerLimitOfEventualRange _ _
    (cohomologyIdealQuotientProj (baseRingHom A B hA X.1 X.2) F I p) I
    (formalFunctionsShift f hf F I p)
    (fun _ _ h => cohomologyIdealQuotientTr_comp_proj _ F I p h)
    (pow_smul_top_le_ker_cohomologyIdealQuotientProj _ F I p)
    (exists_ker_cohomologyIdealQuotientProj_le f hf F I p).choose_spec
    (fun n => exists_range_cohomologyIdealQuotientTr_eq f hf F I p n)

/-- **Stacks 08AZ, the isomorphism is the one defined by the system of maps**: the `n`-th
component of the image of `w ∈ Hᵖ(X, F)^∧` is the image of the `n`-th component of `w` under
`Hᵖ(X, F) / Iⁿ Hᵖ(X, F) ⟶ Hᵖ(X, F / Iⁿ F)`. -/
theorem formalFunctionsEquiv_apply
    (w : AdicCompletion I (cohomologyRes (baseRingHom A B hA X.1 X.2) p F)) (n : ℕ) :
    ((formalFunctionsEquiv f hf F I p w : cohomologyIdealQuotientLimit _ F I p) :
      ∀ k, cohomologyIdealQuotient (baseRingHom A B hA X.1 X.2) F I p k) n =
      adicQuotientMap _ (cohomologyIdealQuotientProj (baseRingHom A B hA X.1 X.2) F I p) I
        (pow_smul_top_le_ker_cohomologyIdealQuotientProj _ F I p) n (w.val n) :=
  adicCompletionEquivTowerLimitOfEventualRange_apply _ _ _ I _ _ _ _ _ w n

/-- **Stacks 08AZ, the homeomorphism**: the comparison is a homeomorphism for the limit
topologies. -/
theorem isHomeomorph_formalFunctionsEquiv :
    @IsHomeomorph _ _
      (adicCompletionLimitTopology I (cohomologyRes (baseRingHom A B hA X.1 X.2) p F))
      (towerLimitTopology _ _) (formalFunctionsEquiv f hf F I p) :=
  isHomeomorph_adicCompletionEquivTowerLimitOfEventualRange _ _ _ I _ _ _ _ _

include hf in
/-- **Stacks 08B0.**  Let `A` be a Noetherian ring complete with respect to an ideal `I`,
`f : X ⟶ Spec A` a proper morphism of algebraic spaces and `F` a coherent `𝒪_X`-module.  Then
`Hᵖ(X, F) ⟶ lim_n Hᵖ(X, F / Iⁿ F)` is an isomorphism for every `p`. -/
theorem bijective_cohomologyToIdealQuotientLimit [IsAdicComplete I A] :
    Function.Bijective
      (cohomologyToIdealQuotientLimit (baseRingHom A B hA X.1 X.2) F I p) := by
  have := moduleFinite_cohomology_of_isProper X.1 X.2 f.hom hf F p
  have := isAdicComplete_of_iInf_smul_eq_bot I
    (Ideal.iInf_pow_smul_eq_bot_of_le_jacobson I (IsAdicComplete.le_jacobson_bot I) :
      ⨅ n : ℕ, (I ^ n • (⊤ : Submodule A (cohomologyRes (baseRingHom A B hA X.1 X.2) p F))) = ⊥)
  exact bijective_towerLimitLift_of_isAdicComplete _ _ _ I
    (pow_smul_top_le_ker_cohomologyIdealQuotientProj _ F I p) (formalFunctionsShift f hf F I p)
    _ (exists_ker_cohomologyIdealQuotientProj_le f hf F I p).choose_spec
    (fun n => exists_range_cohomologyIdealQuotientTr_eq f hf F I p n)

include hf in
/-- Stacks 08B0 as an isomorphism `Hᵖ(X, F) ≃ lim_n Hᵖ(X, F / Iⁿ F)`. -/
def cohomologyEquivIdealQuotientLimit [IsAdicComplete I A] :
    cohomologyRes (baseRingHom A B hA X.1 X.2) p F ≃ₗ[A]
      cohomologyIdealQuotientLimit (baseRingHom A B hA X.1 X.2) F I p :=
  LinearEquiv.ofBijective _ (bijective_cohomologyToIdealQuotientLimit f hf F I p)

end Situation

end AlgebraicGeometry.Space.C1573

end
