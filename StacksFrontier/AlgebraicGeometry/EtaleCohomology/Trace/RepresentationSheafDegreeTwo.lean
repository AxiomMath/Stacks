module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafDegreeOne
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveSecondCohomologyKilling

/-!
# The effacement of `H²(X_K, ℱ_ρ)` by finite étale covers of `X`

Let `X` be a quasi-compact quasi-separated connected scheme over a field `k`, `K/k` algebraic
with `K` algebraically closed, such that `X_K` is a smooth proper connected curve over `K` whose
fundamental group surjects continuously onto `ℤ/#Λ^(e+1)` for every `e` (true when the genus is at
least one, `AlgebraicGeometry.exists_surjective_geometricFundamentalGroup_zmod`). Let `Λ` be a
finite ring with `#Λ` invertible in `K` and `M` a finite `Λ`-module with a continuous action of
`π₁(X, x)`. Every class of `H²(X_K, ℱ_M)` dies under the restriction to `X_K` of the unit
`ℱ_M ⟶ π_* π^* ℱ_M` of some surjective finite étale `π : Y ⟶ X`. This is the hypothesis of
`AlgebraicGeometry.elementwiseEffaceable_geometricRepresentationCohomology_of_forall_exists_unit`
in degree two, for projective curves (Tag 03VM).

`ℱ_M` becomes constant, with value killed by `#Λ`, on a surjective finite étale cover of `X`
(`AlgebraicGeometry.exists_finiteEtale_inverseImage_underlyingAbelian_iso_constant`); the trace
argument
(`Stacks.EtaleCohomology.exists_finite_etale_surjective_restriction_eq_zero_of_trivialization_two`)
kills a class of `H²` with such coefficients on the base change to `X_K` of a surjective finite
étale cover of `X`, and a class restricting to zero there dies under the unit
(`Stacks.EtaleCohomology.rightDerived_map_inverseImage_unit_eq_zero`).

## Main results

* `AlgebraicGeometry.exists_unit_map_eq_zero_of_eq_two` — the effacement hypothesis in degree two.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.EtaleCohomology Stacks.GroupCohomology

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (Λ : Type) [Ring Λ] [Finite Λ]

/-- Sheafification of presheaves of `Λ`-modules on Mathlib's small étale site, pinned at
`u + 1`. -/
local instance (priority := 3000) etaleModules_hasSheafify_objectUniverse_degreeTwo (Λ : Type)
    [Ring Λ] (Y : Scheme.{u}) : HasSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  etaleModules_hasSheafify.{u, 0} Λ Y

/-- Enough injectives for sheaves of `Λ`-modules on Mathlib's small étale site, pinned at
`u + 1`. -/
local instance (priority := 3000) etaleModules_enoughInjectives_objectUniverse_degreeTwo
    (Λ : Type) [Ring Λ] (Y : Scheme.{u}) : EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

variable {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k)) (K : Type u) [Field K] [Algebra k K]

/-- **The effacement hypothesis in degree two.** For `X` quasi-compact and quasi-separated over
`k`, `K/k` algebraic with `K` algebraically closed, `X_K` a smooth proper connected curve over
`K` whose fundamental group at `z` surjects continuously onto `ℤ/#Λ^(e+1)` for every `e`, and
`#Λ` invertible in `K`, every class of `H²(X_K, ℱ_M)` dies under the restriction to
`X_K` of the unit `ℱ_M ⟶ π_* π^* ℱ_M` of some surjective finite étale `π : Y ⟶ X`. -/
theorem exists_unit_map_eq_zero_of_eq_two [CompactSpace X.1] [QuasiSeparatedSpace X.1]
    [Algebra.IsAlgebraic k K] [IsAlgClosed K]
    [ConnectedSpace (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)]
    [IsCurve K (pullback.snd (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K))]
    [Smooth (pullback.snd (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K))]
    [IsProper (pullback.snd (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K))]
    (z : GeometricPoint (Stacks.Frobenius.fieldBaseChange (Over.mk f) K))
    (hχ : ∀ e : ℕ,
      ∃ χ : EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) z →*
          Multiplicative (ZMod (Nat.card Λ ^ (e + 1))),
        IsOpen (χ.ker : Set (EtaleFundamentalGroup _ z)) ∧ Function.Surjective χ)
    (hΛ : IsUnit ((Nat.card Λ : ℕ) : K))
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
    (ξ : ((etaleModuleGlobalSections.{u, 0} Λ
        (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)).rightDerived (1 + 1)).obj
          ((geometricRepresentationSheaf B X x Λ f K).obj M)) :
    ∃ (Y : Scheme.{u}) (π : Y ⟶ X.1) (_ : IsFinite π) (_ : Etale π) (_ : Surjective π),
      ((etaleModuleGlobalSections.{u, 0} Λ
        (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)).rightDerived (1 + 1)).map
        ((etaleModuleInverseImage.{u, 0} Λ
          (pullback.fst (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K))).map
          ((etaleModuleInverseImageAdj.{u, 0} Λ π).unit.app
            ((representationSheaf.{u, 0} B X x Λ).obj M))) ξ = 0 := by
  have : ConnectedSpace (Over.mk f).left := inferInstanceAs (ConnectedSpace X.1)
  let i' := pullback.fst (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K)
  have hdom : DominatesFiniteEtale i' := dominatesFiniteEtale_pullbackFst_of_isAlgebraic k K f
  obtain ⟨T, p, hpf, hpe, hps, A, hA, hAn, ⟨e⟩⟩ :=
    exists_finiteEtale_inverseImage_underlyingAbelian_iso_constant B X x Λ M
  obtain ⟨W, π, hπf, hπe, hπs, hres⟩ :=
    exists_finite_etale_surjective_restriction_eq_zero_of_trivialization_two
      (pullback.snd (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K)) z i' hdom hΛ hχ _ p A
      hAn e (inverseImageSheafHClass Λ i' ((representationSheaf.{u, 0} B X x Λ).obj M) 2 ξ)
  exact ⟨W, π, hπf, hπe, hπs,
    rightDerived_map_inverseImage_unit_eq_zero Λ i' π ((representationSheaf.{u, 0} B X x Λ).obj M) ξ
      hres⟩

end AlgebraicGeometry

end
