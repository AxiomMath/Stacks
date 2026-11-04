module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartZariskiCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleVanishingAboveTheDimension

/-!
# Vanishing above the dimension on an algebraic space which is a Noetherian scheme

Let `X` be an algebraic space and `𝓜` a quasi-coherent `𝒪_X`-module. If `X` is a scheme whose
underlying space is Noetherian of dimension at most `d`, then `H^q(X, 𝓜) = 0` for `q > d`. This is
clause (1) of Stacks 0A4R for an algebraic space which is a scheme, read in the cohomology of the
small étale site of the algebraic space. The proof of Stacks 0E1J uses it for the fibre `X_s` of a
family of curves, a one-dimensional Noetherian scheme, in the form `H^i(X_s, 𝒪_{X_s}) = 0` for
`i ≥ 2`.

"`X` is a scheme" is read as: `X` has a terminal étale chart, that is, an étale chart `A ⟶ X`
which is an isomorphism. The scheme is then the chart's scheme.

## Main results

* `AlgebraicGeometry.Space.isZero_rightDerived_evaluation_of_noetherianSpace_of_dim_le`: for an
  étale chart `A` of `X` whose scheme is a Noetherian space of dimension at most `d`, the
  cohomology over `A` of a quasi-coherent module vanishes above degree `d`.
* `AlgebraicGeometry.Space.isZero_rightDerived_globalSectionsFunctor_of_isTerminal_of_dim_le`:
  the same for the global cohomology of `X`, when `A` is terminal.

## The argument

Over a chart `A` with scheme `T`, the cohomology of a quasi-coherent module is the Zariski
cohomology of its restriction to `T`
(`AlgebraicGeometry.Space.isZero_rightDerived_evaluation_of_isZero_hgroup`, the Leray collapse of
Stacks 03DW along `T_Zar ⟶ X_étale`), and the latter vanishes above the dimension by Grothendieck's
theorem, Stacks 02UZ, for sheaves of modules on a Noetherian space
(`Stacks.CohomologyVanishing.isZero_hgroup_top_of_noetherianSpace_of_dim_le`). When `A` is
terminal, global sections are sections over `A`
(`Stacks.Cohomology.SiteModules.globalSectionsFunctorForgetIsoEvaluation`, on underlying abelian
groups), and the forgetful functors are exact.

## References

* [Stacks Project, Tag 0A4R](https://stacks.math.columbia.edu/tag/0A4R)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 0E1J](https://stacks.math.columbia.edu/tag/0E1J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

noncomputable section

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] hasInjectiveResolutions_modules enoughInjectives_modules

/-- **Vanishing above the dimension over a Noetherian chart.** Let `A` be an étale chart of an
algebraic space `X` whose scheme has Noetherian underlying space of dimension at most `d`, and let
`𝓜` be a quasi-coherent `𝒪_X`-module. Then `H^q(A, 𝓜) = 0` for every `q > d`. -/
theorem isZero_rightDerived_evaluation_of_noetherianSpace_of_dim_le
    (X : AlgebraicSpaces B S hS) (A : SmallEtale B S hS X.1) [NoetherianSpace (chartScheme A)]
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite) {d q : ℕ}
    (hdim : topologicalKrullDim (chartScheme A) ≤ (d : WithBot ℕ∞)) (hq : d < q) :
    IsZero (((SheafOfModules.evaluation
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
        (Opposite.op A)).rightDerived q).obj M) :=
  isZero_rightDerived_evaluation_of_isZero_hgroup B S hS X A M hM q (by omega)
    (Stacks.CohomologyVanishing.isZero_hgroup_top_of_noetherianSpace_of_dim_le _ hdim hq _)

/-- **Vanishing above the dimension on an algebraic space which is a Noetherian scheme.** Let `X`
be an algebraic space with a terminal étale chart `A` (so `X` is the scheme of `A`), whose scheme
has Noetherian underlying space of dimension at most `d`, and let `𝓜` be a quasi-coherent
`𝒪_X`-module. Then `H^q(X, 𝓜) = 0` for every `q > d`. -/
theorem isZero_rightDerived_globalSectionsFunctor_of_isTerminal_of_dim_le
    (X : AlgebraicSpaces B S hS) {A : SmallEtale B S hS X.1} (hA : IsTerminal A)
    [NoetherianSpace (chartScheme A)]
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite) {d q : ℕ}
    (hdim : topologicalKrullDim (chartScheme A) ≤ (d : WithBot ℕ∞)) (hq : d < q) :
    IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived
        q).obj M) := by
  let O := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O
  let W : (SmallEtale B S hS X.1)ᵒᵖ := Opposite.op A
  let e := globalSectionsFunctorForgetIsoEvaluation.{u + 1, u, u, u} O W hA.op
  have : (SheafOfModules.evaluation O W).Additive := ⟨fun {_ _ _ _} => rfl⟩
  have h0 : IsZero (((SheafOfModules.evaluation O W).rightDerived q).obj M) :=
    isZero_rightDerived_evaluation_of_noetherianSpace_of_dim_le B S hS X A M hM hdim hq
  have h1 : IsZero ((forget₂ (ModuleCat.{u + 1} ↥(GlobalSectionRing O)) AddCommGrpCat.{u + 1}).obj
      (((globalSectionsFunctor.{u + 1, u, u, u} O).rightDerived q).obj M)) :=
    IsZero.of_iso (Functor.map_isZero (forget₂ (ModuleCat.{u} (O.obj.obj W)) AddCommGrpCat.{u} ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u}) h0)
      (((Functor.rightDerivedCompIso (globalSectionsFunctor.{u + 1, u, u, u} O)
          (forget₂ (ModuleCat.{u + 1} ↥(GlobalSectionRing O)) AddCommGrpCat.{u + 1}) q).app M).symm
              ≪≫
        (ModuleSheafCohomology.rightDerivedIso e q).app M ≪≫
          (Functor.rightDerivedCompIso (SheafOfModules.evaluation O W)
            (forget₂ (ModuleCat.{u} (O.obj.obj W)) AddCommGrpCat.{u} ⋙
              AddCommGrpCat.uliftFunctor.{u + 1, u}) q).app M)
  rw [ModuleCat.isZero_iff_subsingleton]
  exact AddCommGrpCat.isZero_iff_subsingleton.1 h1

end AlgebraicGeometry.Space

end
