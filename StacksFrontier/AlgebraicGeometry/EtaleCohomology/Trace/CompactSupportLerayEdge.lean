module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportDimensionZeroHomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LerayFrobeniusComparisonDischarge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.CompactSupportSheafFiniteness

/-!
# The bottom edge of the Leray sequence for compact supports

Let `k` be a finite field, `X` a scheme over `k` with a compactification and `k̄` an extension of
`k`. For a bounded below complex `K` of sheaves on `X_étale` with `Hᵐ(K) = 0` for `m < n`, the
first possibly nonzero cohomology sheaf contributes to `Hⁿ_c` only through
`H⁰_c(X_k̄, Hⁿ(K)) ≅ Hⁿ_c(X_k̄, τ_{≤ n} τ_{≥ n} K) ≅ Hⁿ_c(X_k̄, τ_{≥ n} K) ≅ Hⁿ_c(X_k̄, K)`
(`Stacks.EtaleCohomology.compactSupportBottomHomologyIso`): the cokernel `τ_{≥ n+1} K` of the
graded piece has no `Hⁱ_c` for `i ≤ n`.

Applied to the complex computing `Rg_! K` for `g : U ⟶ W` separated of finite type and an ℓ-power
torsion sheaf `K` on `U` with `R⁰g_! K = 0`, through the Leray comparison
`RΓ_c(U_k̄, K) ≅ RΓ_c(W_k̄, Rg_! K)` (Tags 0F7J, 0F7L,
`Stacks.EtaleCohomology.LAdicSheaf.lerayFrobeniusComparison`), this is the edge isomorphism
`H⁰_c(W_k̄, R¹g_! K) ≅ H¹_c(U_k̄, K)` of the Leray spectral sequence
`E₂^{p,q} = H^p_c(W_k̄, R^q g_! K)`
(`LAdicSheaf.nonempty_compactSupportSheafCohomology_lowerShriekHomology_one_iso`).
In Laumon's degeneration argument ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) it shows
that `G = R¹pr₂! K` has no compactly supported sections over `k̄` once `H¹_c(𝔸²_k̄, K) = 0`, which
excludes punctual sections of `G`.

## Main results

* `Stacks.EtaleCohomology.compactSupportBottomHomologyIso`.
* `LAdicSheaf.nonempty_compactSupportSheafCohomology_lowerShriekHomology_one_iso`.
* `Stacks.EtaleCohomology.LAdicSheaf.isZero_compactSupportSheafCohomology_lowerShriekHomology_one`.

## Implementation notes

`compactSupportFrobeniusFunctor` and `derivedLowerShriek` live in the standard model
`HasDerivedCategory.standard`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section Bottom

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- **`H⁰_c(X_k̄, Hⁿ(K)) ≅ Hⁿ_c(X_k̄, K)` when `Hᵐ(K) = 0` for `m < n`**: `K → τ_{≥ n} K` is a
quasi-isomorphism and `Hⁿ_c(X_k̄, τ_{≤ n} τ_{≥ n} K) ≅ Hⁿ_c(X_k̄, τ_{≥ n} K)`
(`Stacks.EtaleCohomology.isIso_compactSupportGradedToTrunc_app_self`), the graded piece being
`Hⁿ(K)` placed in degree `n`. -/
def compactSupportBottomHomologyIso (n : ℤ) (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
    [K.obj.IsGE n] :
    (compactSupportSheafCohomology Λ f j kbar 0).obj
        ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).obj K.obj) ≅
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) n).obj
        ((compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).obj K) :=
  haveI : QuasiIso ((CochainComplex.Plus.πTruncGE (C := EtaleModules.{u, 0} Λ X) n).app K).hom :=
    inferInstanceAs (QuasiIso (K.obj.πTruncGE n))
  haveI := isIso_compactSupportFrobeniusFunctor_map_of_quasiIso Λ f j kbar
    ((CochainComplex.Plus.πTruncGE (C := EtaleModules.{u, 0} Λ X) n).app K)
  haveI := isIso_compactSupportGradedToTrunc_app_self Λ f j kbar n K
  ((compactSupportGradedHomologyIso Λ f j kbar n n 0 (by omega)).app K).symm ≪≫
    asIso ((compactSupportGradedToTrunc Λ f j kbar n n).app K) ≪≫
    (asIso ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) n).map
      ((compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).map
        ((CochainComplex.Plus.πTruncGE (C := EtaleModules.{u, 0} Λ X) n).app K)))).symm

end Bottom

section Leray

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime] {U W : B.Scheme} [IsNoetherian U.1]
  [IsNoetherian W.1] (g : U ⟶ W) [LocallyOfFiniteType (B.inclusion.map g)]
  [QuasiCompact (B.inclusion.map g)] [IsSeparated (B.inclusion.map g)]
  (jg : CompactificationOf (Over.mk (B.inclusion.map g))) {k : Type u} [Field k] [Finite k]
  (fW : W.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fW] [QuasiCompact fW] [IsSeparated fW]
  (jW : CompactificationOf (Over.mk fW)) (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- **The Leray edge `H⁰_c(W_k̄, R¹g_! K) ≅ H¹_c(U_k̄, K)` when `R⁰g_! K = 0`**, for an ℓ-power
torsion sheaf `K` on `U` and a compactification `j_U` of `U` over `k`: the complex `C K` computing
`Rg_! K` (`Stacks.EtaleCohomology.LAdicSheaf.lerayFrobeniusComparison`) has no cohomology in
degrees `≤ 0`, so `H⁰_c(W_k̄, H¹(C K)) ≅ H¹_c(W_k̄, C K) ≅ H¹_c(U_k̄, K)` (Tags 0F7J, 0F7L), and
the choice of `j_U` does not matter (Tag 0ATU). -/
theorem LAdicSheaf.nonempty_compactSupportSheafCohomology_lowerShriekHomology_one_iso
    (K : (IsLPowerTorsion ℓ U.1).FullSubcategory)
    (h0 : IsZero ((lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg 0).obj K.obj))
    (jU : CompactificationOf (Over.mk (B.inclusion.map g ≫ fW))) :
    Nonempty ((compactSupportSheafCohomology ℤ_[ℓ] fW jW kbar 0).obj
        ((lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg 1).obj K.obj) ≅
      (compactSupportSheafCohomology ℤ_[ℓ] (B.inclusion.map g ≫ fW) jU kbar 1).obj K.obj) := by
  have : Fintype k := Fintype.ofFinite k
  obtain ⟨p, hp⟩ := CharP.exists k
  have : CharP k p := hp
  obtain ⟨q, hpr, hq⟩ := FiniteField.card k p
  have : Fact p.Prime := ⟨hpr⟩
  obtain ⟨jU', C, ψ, φ, -⟩ := LAdicSheaf.lerayFrobeniusComparison B ℓ g jg fW jW kbar p q hq
  -- `C K` has no cohomology in degrees `≤ 0`
  have : (C.obj K).obj.IsGE 0 := isGE_lerayComplex B ℓ g jg C ψ K
  have : (C.obj K).obj.IsGE 1 := by
    rw [CochainComplex.isGE_iff]
    intro i hi
    rcases lt_or_eq_of_le (show i ≤ 0 by omega) with h | rfl
    · exact (C.obj K).obj.exactAt_of_isGE 0 i h
    · rw [HomologicalComplex.exactAt_iff_isZero_homology]
      exact h0.of_iso ((lerayComplexHomologyIso B ℓ g jg C ψ 0).app K)
  obtain ⟨N, hN⟩ := K.property
  have hNpos : 0 < ℓ ^ N := pow_pos (Fact.out : ℓ.Prime).pos N
  have : LocallyOfFiniteType (B.inclusion.map g ≫ fW) := inferInstance
  have : QuasiCompact (B.inclusion.map g ≫ fW) := inferInstance
  have : IsSeparated (B.inclusion.map g ≫ fW) := inferInstance
  exact ⟨(compactSupportSheafCohomology ℤ_[ℓ] fW jW kbar 0).mapIso
      ((lerayComplexHomologyIso B ℓ g jg C ψ 1).app K).symm ≪≫
    compactSupportBottomHomologyIso ℤ_[ℓ] fW jW kbar 1 (C.obj K) ≪≫
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) 1).mapIso (φ.app K).symm ≪≫
    compactSupportSheafCohomologyCompactificationIso ℤ_[ℓ] (B.inclusion.map g ≫ fW) kbar jU' jU
      K.obj (ℓ ^ N) hNpos hN 1⟩

/-- **`H⁰_c(W_k̄, R¹g_! K) = 0` once `R⁰g_! K = 0` and `H¹_c(U_k̄, K) = 0`**, for an ℓ-power
torsion sheaf `K` on `U`: the Leray edge
(`LAdicSheaf.nonempty_compactSupportSheafCohomology_lowerShriekHomology_one_iso`). -/
theorem LAdicSheaf.isZero_compactSupportSheafCohomology_lowerShriekHomology_one
    (K : (IsLPowerTorsion ℓ U.1).FullSubcategory)
    (h0 : IsZero ((lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg 0).obj K.obj))
    (jU : CompactificationOf (Over.mk (B.inclusion.map g ≫ fW)))
    (h1 : IsZero ((compactSupportSheafCohomology ℤ_[ℓ] (B.inclusion.map g ≫ fW) jU kbar 1).obj
      K.obj)) :
    IsZero ((compactSupportSheafCohomology ℤ_[ℓ] fW jW kbar 0).obj
      ((lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg 1).obj K.obj)) := by
  obtain ⟨e⟩ := LAdicSheaf.nonempty_compactSupportSheafCohomology_lowerShriekHomology_one_iso B ℓ g
    jg fW jW kbar K h0 jU
  exact h1.of_iso e

end Leray

end Stacks.EtaleCohomology

end
