module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FirstCohomologyKilling.DominatedCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafTrivialization
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.AlgebraicBaseChangeDomination

/-!
# The effacement of `H¹(X_K, ℱ_ρ)` by finite étale covers of `X`

Let `X` be a quasi-compact quasi-separated connected scheme over a field `k`, `K/k` an algebraic
extension with `X_K` connected, `Λ` a finite ring and `M` a finite `Λ`-module with a continuous
action of `π₁(X, x)`. Every class of `H¹(X_K, ℱ_M)` dies under the restriction to `X_K` of the
unit `ℱ_M ⟶ π_* π^* ℱ_M` of some surjective finite étale `π : Y ⟶ X`. This is the hypothesis of
`AlgebraicGeometry.elementwiseEffaceable_geometricRepresentationCohomology_of_forall_exists_unit`
in degree one.

`ℱ_M` becomes constant on a surjective finite étale cover of `X`
(`AlgebraicGeometry.exists_finiteEtale_inverseImage_representationSheaf_iso_constant`); a class of
`H¹` with coefficients so trivialized dies on the base change to `X_K` of a surjective finite étale
cover of `X`, because `X_K ⟶ X` dominates finite étale covers (the injectivity half of Tag 0BTX,
`AlgebraicGeometry.dominatesFiniteEtale_pullbackFst_of_isAlgebraic`, and
`Stacks.EtaleCohomology.exists_finite_etale_surjective_restriction_eq_zero_of_trivialization`); and
a class restricting to zero there dies under the unit
(`Stacks.EtaleCohomology.rightDerived_map_inverseImage_unit_eq_zero`).

## Main results

* `AlgebraicGeometry.exists_finiteEtale_inverseImage_underlyingAbelian_iso_constant` — the
  trivialization of the underlying abelian sheaf of `ℱ_M`.
* `AlgebraicGeometry.exists_unit_map_eq_zero_of_eq_one` — the effacement hypothesis in degree
  one.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.EtaleCohomology Stacks.GroupCohomology

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (Λ : Type) [Ring Λ] [Finite Λ]

/-- **The underlying abelian sheaf of `ℱ_M` becomes constant on a surjective finite étale
cover**, with finite value killed by `#Λ`. -/
theorem exists_finiteEtale_inverseImage_underlyingAbelian_iso_constant
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :
    ∃ (Y : Scheme.{u}) (π : Y ⟶ X.1) (_ : IsFinite π) (_ : Etale π) (_ : Surjective π)
      (A : AddCommGrpCat.{u + 1}) (_ : Finite A) (_ : ∀ a : A, Nat.card Λ • a = 0),
      Nonempty ((etaleAbelianInverseImage.{u, 0} π).obj
          ((etaleModuleUnderlyingAbelian X.1 Λ).obj ((representationSheaf.{u, 0} B X x Λ).obj M)) ≅
        (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A) := by
  obtain ⟨Y, π, hf, he, hs, E, hE, ⟨e⟩⟩ :=
    exists_finiteEtale_inverseImage_representationSheaf_iso_constant B X x Λ M
  refine ⟨Y, π, hf, he, hs, (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj E,
    inferInstanceAs (Finite E), fun a => ?_, ⟨?_⟩⟩
  · have key : ∀ b : E, Nat.card Λ • b = 0 := fun b => by
      rw [← one_smul Λ b, ← smul_assoc, card_nsmul_eq_zero', zero_smul]
    exact key a
  exact (etaleModuleUnderlyingAbelianInverseImageIsoOfRing Λ π).app _ ≪≫
    (etaleModuleUnderlyingAbelian Y Λ).mapIso e ≪≫
    (Stacks.ModuleCatLift.constantSheafForget₂Iso.{u + 1, 0, u + 1, u} Λ
      Y.smallEtaleTopology).app E

/-- Sheafification of presheaves of `Λ`-modules on Mathlib's small étale site, pinned at
`u + 1`. -/
local instance (priority := 3000) etaleModules_hasSheafify_objectUniverse_degreeOne (Λ : Type)
    [Ring Λ] (Y : Scheme.{u}) : HasSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  etaleModules_hasSheafify.{u, 0} Λ Y

/-- Enough injectives for sheaves of `Λ`-modules on Mathlib's small étale site, pinned at
`u + 1`. -/
local instance (priority := 3000) etaleModules_enoughInjectives_objectUniverse_degreeOne
    (Λ : Type) [Ring Λ] (Y : Scheme.{u}) : EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

variable {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k)) (K : Type u) [Field K] [Algebra k K]

/-- **The effacement hypothesis in degree one.** For `X` quasi-compact and quasi-separated over
`k`, `K/k` algebraic and `X_K` connected, every class of `H¹(X_K, ℱ_M)` dies under the restriction
to `X_K` of the unit `ℱ_M ⟶ π_* π^* ℱ_M` of some surjective finite étale `π : Y ⟶ X`. -/
theorem exists_unit_map_eq_zero_of_eq_one [CompactSpace X.1] [QuasiSeparatedSpace X.1]
    [Algebra.IsAlgebraic k K] [ConnectedSpace (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)]
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
    (ξ : ((etaleModuleGlobalSections.{u, 0} Λ
        (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)).rightDerived (0 + 1)).obj
          ((geometricRepresentationSheaf B X x Λ f K).obj M)) :
    ∃ (Y : Scheme.{u}) (π : Y ⟶ X.1) (_ : IsFinite π) (_ : Etale π) (_ : Surjective π),
      ((etaleModuleGlobalSections.{u, 0} Λ
        (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)).rightDerived (0 + 1)).map
        ((etaleModuleInverseImage.{u, 0} Λ
          (pullback.fst (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K))).map
          ((etaleModuleInverseImageAdj.{u, 0} Λ π).unit.app
            ((representationSheaf.{u, 0} B X x Λ).obj M))) ξ = 0 := by
  have : ConnectedSpace (Over.mk f).left := inferInstanceAs (ConnectedSpace X.1)
  let i' := pullback.fst (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K)
  have hdom : DominatesFiniteEtale i' := dominatesFiniteEtale_pullbackFst_of_isAlgebraic k K f
  obtain ⟨T, p, hpf, hpe, hps, A, hA, -, ⟨e⟩⟩ :=
    exists_finiteEtale_inverseImage_underlyingAbelian_iso_constant B X x Λ M
  obtain ⟨W, π, hπf, hπe, hπs, hres⟩ :=
    exists_finite_etale_surjective_restriction_eq_zero_of_trivialization i' hdom _ p A e
      (inverseImageSheafHClass Λ i' ((representationSheaf.{u, 0} B X x Λ).obj M) 1 ξ)
  exact ⟨W, π, hπf, hπe, hπs,
    rightDerived_map_inverseImage_unit_eq_zero Λ i' π
      ((representationSheaf.{u, 0} B X x Λ).obj M) ξ hres⟩

end AlgebraicGeometry

end
