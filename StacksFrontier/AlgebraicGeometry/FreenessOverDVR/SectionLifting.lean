module

public import StacksFrontier.AlgebraicGeometry.FormalFunctions.IdealPowerShortExact
public import StacksFrontier.AlgebraicGeometry.FreenessOverDVR.CohomologyReduction

/-!
# Lifting sections from `F / πⁿ F` to `F`

Let `f : X ⟶ Spec A`, `π ∈ A` and `F` a quasi-coherent module on `X` whose stalks have
`π`-torsion of exponent at most `k`. Suppose the `π`-power torsion of `H¹(X, πᵏ F)` is killed by
`πᵉ`. Then for every `n ≥ k`, every global section of `F / πⁿ⁺ᵉ F`, reduced modulo `πⁿ`, lifts
to a global section of `F`.

The obstruction to lifting a section `s` of `F / πⁿ⁺ᵉ F` is its image `c` under the connecting
map to `H¹(X, πⁿ⁺ᵉ F)`, which is killed by `πⁿ⁺ᵉ` because its image in `H¹(X, F)` vanishes. The
obstruction for the reduction of `s` modulo `πⁿ` is the image of `c` in `H¹(X, πⁿ F)`, and
multiplication by `πᵉ` identifies `πⁿ F` with `πⁿ⁺ᵉ F` and carries that image to `πᵉ c = 0`.
This is the step of [Stacks, Tag 0EXF] turning a bound on the torsion of `H¹` into a lifting
statement independent of the module.

## Main results

The elided prefix is `Stacks.AlgebraicGeometry.FreenessOverDVR`.

* `pow_smul_cohomology_adicFiltration_eq_zero`: the torsion bound for `H¹(X, πᵏ F)` holds for
  every `H¹(X, πʲ F)` with `j ≥ k`.
* `exists_cohomology_lift`: **the lifting statement**, on zeroth cohomology.

## References

* [Stacks Project, Tag 0EXF](https://stacks.math.columbia.edu/tag/0EXF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.BaseAdicFiltration Stacks.Algebraization

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.AlgebraicGeometry.FreenessOverDVR

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (π : A)

/-- If `φ ≫ ψ` is multiplication by `πᵐ`, then `H¹(ψ) ∘ H¹(φ)` is multiplication by `πᵐ`. -/
private theorem cohomologyMap_comp_map_of_comp_eq_globalSmul {M N : X.Modules} {φ : M ⟶ N}
    {ψ : N ⟶ M} {m : ℕ} (h : φ ≫ ψ = globalSmul (baseScalarMap f π ^ m) M)
    (c : cohomologyOver A f 1 M) :
    cohomologyMap A f 1 ψ (cohomologyMap A f 1 φ c) = π ^ m • c := by
  rw [← LinearMap.comp_apply, ← cohomologyMap_comp, h, cohomologyMap_globalSmul]
  rfl

/-- **The torsion bound passes along the filtration.** If the `π`-power torsion of
`H¹(X, πᵏ F)` is killed by `πᵉ`, so is that of `H¹(X, πʲ F)` for every `j ≥ k`, multiplication
by `πʲ⁻ᵏ` identifying `πᵏ F` with `πʲ F`. -/
theorem pow_smul_cohomology_adicFiltration_eq_zero (F : X.Modules) [F.IsQuasicoherent]
    {k e : ℕ} (hk : StalkTorsionBounded F (baseScalarMap f π) k)
    (he : ∀ (c : cohomologyOver A f 1 (adicFiltration f (Ideal.span {π}) k F).toSheafOfModules)
      (i : ℕ), π ^ i • c = 0 → π ^ e • c = 0)
    (j : ℕ) (hj : k ≤ j)
    (c : cohomologyOver A f 1 (adicFiltration f (Ideal.span {π}) j F).toSheafOfModules) (i : ℕ)
    (hc : π ^ i • c = 0) : π ^ e • c = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
  let L := cohomologyLinearEquiv (A := A) (f := f) 1
    (@asIso X.Modules _ _ _ (adicMul f π F k d) (isIso_adicMul f π F hk le_rfl d))
  have h1 : π ^ i • L.symm c = 0 := by rw [← map_smul, hc, map_zero]
  have h2 := he _ i h1
  rw [← L.apply_symm_apply c, ← map_smul, h2, map_zero]

/-- **Lifting sections modulo `πⁿ`.** Let the stalks of the quasi-coherent module `F` have
`π`-torsion of exponent at most `k`, and let `πᵉ` kill the `π`-power torsion of `H¹(X, πᵏ F)`.
Then for `n ≥ k` the reduction modulo `πⁿ` of every class in `H⁰(X, F / πⁿ⁺ᵉ F)` comes from
`H⁰(X, F)`. -/
theorem exists_cohomology_lift (F : X.Modules) [F.IsQuasicoherent] {k e : ℕ}
    (hk : StalkTorsionBounded F (baseScalarMap f π) k)
    (he : ∀ (c : cohomologyOver A f 1 (adicFiltration f (Ideal.span {π}) k F).toSheafOfModules)
      (i : ℕ), π ^ i • c = 0 → π ^ e • c = 0)
    {n : ℕ} (hn : k ≤ n) (s : cohomologyOver A f 0 (adicQuotient f (Ideal.span {π}) (n + e) F)) :
    ∃ t : cohomologyOver A f 0 F,
      cohomologyMap A f 0 (adicProj f (Ideal.span {π}) n F) t =
        cohomologyMap A f 0 (idealPowerQuotientDrop (baseIdeal f (Ideal.span {π}))
          (Nat.le_add_right n e) F) s := by
  have hS := idealPowerQuotientShortComplex_shortExact (baseIdeal f (Ideal.span {π})) (n + e) F
  have hT := idealPowerQuotientShortComplex_shortExact (baseIdeal f (Ideal.span {π})) n F
  set c := cohomologyδ (A := A) (f := f) hS 0 s with hc
  -- The image of the obstruction in `H¹(X, F)` vanishes.
  have hc₁ : cohomologyMap A f 1 (adicFiltration f (Ideal.span {π}) (n + e) F).ι c = 0 :=
    (exact_cohomologyδ_map A f hS 0 _).2 ⟨s, rfl⟩
  -- Hence the obstruction is killed by `πⁿ⁺ᵉ`.
  have hc₂ : π ^ (n + e) • c = 0 := by
    exact (cohomologyMap_comp_map_of_comp_eq_globalSmul f π (ι_comp_adicLift f π F (n + e))
      c).symm.trans ((congrArg _ hc₁).trans (map_zero _))
  -- Hence it is killed by `πᵉ`.
  have hc₃ : π ^ e • c = 0 :=
    pow_smul_cohomology_adicFiltration_eq_zero f π F hk he (n + e) (by omega) c _ hc₂
  -- Its image in `H¹(X, πⁿ F)` therefore vanishes.
  have hc₄ : cohomologyMap A f 1 (adicIncl f π F (Nat.le_add_right n e)) c = 0 := by
    have h' : cohomologyMap A f 1 (adicMul f π F n e)
        (cohomologyMap A f 1 (adicIncl f π F (Nat.le_add_right n e)) c) = 0 := by
      exact (cohomologyMap_comp_map_of_comp_eq_globalSmul f π (adicIncl_comp_adicMul f π F n e)
        c).trans hc₃
    exact (cohomologyLinearEquiv (A := A) (f := f) 1
      (@asIso X.Modules _ _ _ (adicMul f π F n e) (isIso_adicMul f π F hk hn e))).injective
      (h'.trans (map_zero _).symm)
  have hδ : cohomologyδ (A := A) (f := f) hT 0 (cohomologyMap A f 0
      (idealPowerQuotientDrop (baseIdeal f (Ideal.span {π})) (Nat.le_add_right n e) F) s) = 0 :=
    (cohomologyδ_naturality A f hS hT (idealPowerQuotientShortComplexMap
      (baseIdeal f (Ideal.span {π})) F (Nat.le_add_right n e)) 0 s).trans hc₄
  obtain ⟨t, ht⟩ := (exact_cohomologyMap_δ A f hT 0 _).1 hδ
  exact ⟨t, ht⟩

end Stacks.AlgebraicGeometry.FreenessOverDVR
