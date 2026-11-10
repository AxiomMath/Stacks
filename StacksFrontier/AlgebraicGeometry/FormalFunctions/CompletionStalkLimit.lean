module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.CompletionStalkLimitAux
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.FormalFunctionsFrom02O8
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.InfinitesimalCohomologyTower
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.StalkFormalFunctionsFrom02O8
public import StacksFrontier.AlgebraicGeometry.Spaces.FormalFunctionsGeometricStalk

/-!
# The theorem on formal functions

Let `f : X ⟶ Y` be a proper morphism of schemes with `Y` locally Noetherian, let `ℱ` be a
coherent `𝒪_X`-module and let `y` be a point of `Y`. Write `A = 𝒪_{Y, y}` for the local ring,
`𝔪 = 𝔪_y` for its maximal ideal and

`X_n = Spec (A/𝔪 ⁿ) ×_Y X`,  `ℱ_n = i_n ^* ℱ`

for the infinitesimal neighbourhoods of the fibre `X_1 = X_y` and the restrictions of `ℱ` to
them. **[Stacks, Tag 02OD]** says that in every degree `p`

`(R ᵖ f_* ℱ) _y ^∧ ≅ lim_n H ᵖ (X_n, ℱ_n)`

as modules over the completed local ring `A ^∧_𝔪`, and that is what this file proves.

The proof is the source's. Put `X' = X ×_Y Spec A` with projections `g' : X' ⟶ X` and
`f' : X' ⟶ Spec A`, and `ℱ' = (g')^* ℱ`.

* Flat base change in every degree along `Spec A ⟶ Y` identifies the left-hand side before
  completion: `(R ᵖ f_* ℱ)_y ≅ H ᵖ (X', ℱ')`, which is
  `Stacks.FormalFunctions.nonempty_higherDirectImageStalkLinearEquiv`.
* The affine theorem on formal functions over `Spec A`, [Stacks, Tag 02OC] standing on
  [Stacks, Tag 02O8] alone, identifies the completion of `H ᵖ (X', ℱ')` with the limit of the
  tower `n ↦ H ᵖ (X', ℱ' / 𝓘 ⁿ ℱ')`, where `𝓘 = 𝔪 · 𝒪_{X'}`.
* `X_n` is the closed subscheme of `X'` cut out by `𝓘 ⁿ`, so by [Stacks, Tag 0EL1] and the
  invariance of cohomology along a closed immersion that tower is the tower
  `n ↦ H ᵖ (X_n, ℱ_n)`, compatibly with the transition maps. That is
  `Stacks.FormalFunctions.infinitesimalCohomologyEquiv`.
* Finally the comparison is linear over `A ^∧_𝔪` and not merely over `A`, because every term
  of the tower is annihilated by `𝔪 ⁿ`:
  `Stacks.FormalFunctions.map_adicCompletion_smul_towerLimit`. The two towers are matched by
  `Stacks.AdicTowerComparison.towerLimitCongr`, and the limit is read over the completion by
  `Stacks.FormalFunctions.towerLimitRestrictScalars`.

## Main results

* `Stacks.FormalFunctions.nonempty_adicCompletionHigherDirectImageStalkEquiv`:
  **[Stacks, Tag 02OD]**.

## Implementation notes

The isomorphism is asserted to exist rather than constructed as a named canonical map. That is
forced by the flat base change this rests on: the comparison
`g ^* (R ᵖ f_* ℱ) ≅ R ᵖ f'_* ((g')^* ℱ)` of [Stacks, Tag 0GN5] is available as an isomorphism
of sheaves, and the identification of `H ᵖ (X', ℱ')` with the stalk is then only an isomorphism
of `A`-modules, with no normalisation attached. The source likewise states the conclusion as an
isomorphism of `𝒪 ^∧_{Y, y}`-modules and nothing more.

The limit is `Stacks.IntertwinedFiltration.towerLimit`, the submodule of compatible families in
the product, taken over the completed local ring; its transition maps are
`Stacks.FormalFunctions.infinitesimalCohomologyMap`, which are the restriction maps
`H ᵖ (X_n, ℱ_n) ⟶ H ᵖ (X_m, ℱ_m)` built on `X'` — see the implementation notes of
`StacksFrontier/AlgebraicGeometry/FormalFunctions/InfinitesimalCohomologyTower.lean`.

## References

* [Stacks Project, Tag 02OD](https://stacks.math.columbia.edu/tag/02OD)
* [Stacks Project, Tag 02OC](https://stacks.math.columbia.edu/tag/02OC)
* [Stacks Project, Tag 02O8](https://stacks.math.columbia.edu/tag/02O8)
* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 0GN5](https://stacks.math.columbia.edu/tag/0GN5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.FormalFunctions

open Stacks.Algebraization Stacks.Cohomology.FormalFunctions Stacks.IntertwinedFiltration

variable {X Y : Scheme.{u}}

/-- **[Stacks, Tag 01BW] for modules on a scheme, as an instance**: a coherent module is
quasi-coherent. The statement of the tag below assumes only coherence, so the quasi-coherence
its ingredients ask for has to be available to instance search. -/
public instance isQuasicoherent_of_isCoherent_modules {Z : Scheme.{u}} (M : Z.Modules)
    [M.IsCoherent] : M.IsQuasicoherent :=
  isQuasicoherent_of_isCoherent M

/-- A scalar of `𝒪 ^∧_{Y, y}` acts on `H ᵖ (X_n, ℱ_n)` as any scalar of `𝒪_{Y, y}` with the same
image in the `n`-th truncation, in the `AdicCompletion.eval` spelling the completion machinery
uses. -/
public theorem infinitesimalCohomology_smul_eq_of_eval (f : X ⟶ Y) (F : X.Modules) (y : Y)
    (p n : ℕ) (r : AdicCompletion (stalkMaximalIdeal y) (Y.presheaf.stalk y))
    (a : Y.presheaf.stalk y)
    (ha : AdicCompletion.eval (stalkMaximalIdeal y) (Y.presheaf.stalk y) n r =
      AdicCompletion.eval (stalkMaximalIdeal y) (Y.presheaf.stalk y) n
        (AdicCompletion.of (stalkMaximalIdeal y) (Y.presheaf.stalk y) a))
    (z : infinitesimalCohomology f F y p n) : r • z = a • z := by
  refine infinitesimalCohomology_smul_eq f F y p n r a ?_ z
  have h1 := AdicCompletion.factor_eval_eq_evalₐ (I := stalkMaximalIdeal y) (n := n) r (by simp)
  have h2 := AdicCompletion.factor_eval_eq_evalₐ (I := stalkMaximalIdeal y) (n := n)
    (AdicCompletion.of (stalkMaximalIdeal y) (Y.presheaf.stalk y) a) (by simp)
  rw [← h1, ha, h2, AdicCompletion.evalₐ_of]

/-- **Stacks Project, Tag 02OD.** Let `f : X ⟶ Y` be a proper morphism of schemes with `Y`
locally Noetherian, let `ℱ` be a coherent `𝒪_X`-module and let `y` be a point of `Y`. Let
`X_n = Spec (𝒪_{Y, y}/𝔪_y ⁿ) ×_Y X` be the infinitesimal neighbourhoods of the fibre `X_y` and
`ℱ_n = i_n ^* ℱ`. Then in every degree `p`

`(R ᵖ f_* ℱ) _y ^∧ ≅ lim_n H ᵖ (X_n, ℱ_n)`

as `𝒪 ^∧_{Y, y}`-modules. -/
@[stacks 02OD, ega "III 4.2.4" "Degree p = 0 case"]
public theorem nonempty_adicCompletionHigherDirectImageStalkEquiv (f : X ⟶ Y)
    [IsLocallyNoetherian Y] [IsProper f] (F : X.Modules) [F.IsCoherent] (y : Y) (p : ℕ) :
    Nonempty
      (AdicCompletion (stalkMaximalIdeal y) (higherDirectImageStalk f F y p) ≃ₗ[
          AdicCompletion (stalkMaximalIdeal y) (Y.presheaf.stalk y)]
        towerLimit (infinitesimalCohomology f F y p) (infinitesimalCohomologyMap f F y p)) := by
  have hA : IsNoetherianRing ↥(Y.presheaf.stalk y) := inferInstance
  have : IsLocallyNoetherian (stalkBaseChange f y) := inferInstance
  have : (stalkBaseChangeModule f F y).IsCoherent := isCoherent_pullback _ F
  have hcoh : Stacks.SheafOfModules.IsCoherent (stalkBaseChangeModule f F y) :=
    Stacks.AlgebraicGeometry.ProperMapping.stacksIsCoherent inferInstance
  -- Flat base change: the stalk of the higher direct image is the cohomology of `X'`.
  obtain ⟨e₁⟩ := nonempty_higherDirectImageStalkLinearEquiv f F y p
  -- The affine theorem on formal functions over `Spec 𝒪_{Y,y}`.
  obtain ⟨e₂, -⟩ :=
    @exists_formalFunctionsEquiv_of_02O8 ↥(Y.presheaf.stalk y) _ hA _
      (stalkBaseChangeStructure f y) inferInstance (stalkMaximalIdeal y)
      (stalkBaseChangeModule f F y) hcoh p isReesFinite_cohomologyIdealPowerSystem
  -- The two towers agree.
  have e₃ := Stacks.AdicTowerComparison.towerLimitCongr
    (fun n => cohomologyOverBase ↥(Y.presheaf.stalk y) (stalkBaseChangeStructure f y) p
      (idealPowerQuotient (infinitesimalBaseIdealSheaf f y) n (stalkBaseChangeModule f F y)))
    (infinitesimalCohomology f F y p)
    (fun _ _ h => (cohomologyOverBaseMap ↥(Y.presheaf.stalk y)
      (stalkBaseChangeStructure f y) p
      (idealPowerQuotientDrop (infinitesimalBaseIdealSheaf f y) h
        (stalkBaseChangeModule f F y))).hom)
    (fun m n h => (infinitesimalCohomologyMap f F y p m n h).restrictScalars
      ↥(Y.presheaf.stalk y))
    (infinitesimalCohomologyEquiv f F y p)
    (fun m n h x => (infinitesimalCohomologyEquiv_naturality f F y p m n h x).symm)
  have e₄ := towerLimitRestrictScalars ↥(Y.presheaf.stalk y)
    (AdicCompletion (stalkMaximalIdeal y) (Y.presheaf.stalk y))
    (infinitesimalCohomology f F y p) (infinitesimalCohomologyMap f F y p)
  -- The composite, over the local ring.
  have E := ((AdicCompletion.congr (I := stalkMaximalIdeal y) e₁).restrictScalars
      ↥(Y.presheaf.stalk y) ≪≫ₗ e₂) ≪≫ₗ e₃ ≪≫ₗ e₄
  -- Upgrade to the completed local ring.
  refine ⟨{ E with
    map_smul' := fun r x => ?_ }⟩
  refine map_adicCompletion_smul_towerLimit (Ideal.fg_of_isNoetherianRing _)
    (infinitesimalCohomology f F y p) (infinitesimalCohomologyMap f F y p)
    (fun n => pow_smul_top_infinitesimalCohomology_eq_bot f F y p n)
    (fun n r' a' ha' z => infinitesimalCohomology_smul_eq_of_eval f F y p n r' a' ha' z)
    E.toLinearMap r x

end Stacks.FormalFunctions

end
