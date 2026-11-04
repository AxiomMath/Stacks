module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernComponentModuleIso
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.KeyFormulaOnDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemeRegularSection
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafPullback
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeIdealSheaf

/-!
# The rational equivalence of the key formula for an arbitrary section of an invertible module

Let `Y` be integral and locally Noetherian, let `M` be an invertible `𝒪_Y`-module with a nonzero
global section `t`, let `N` be invertible and let `ℱ` be a situation of Stacks 0AYB for `M` and
`N` whose meromorphic section of `M` is the generic value of `t`. The left hand side of the key
formula Stacks 0AYC is then rationally equivalent to zero with witnesses inside the zero scheme
`Z(t)` ([Stacks, Tag 02OQ]).

On an integral scheme a nonzero global section is a nonzerodivisor, so `Z(t)` is an effective
Cartier divisor and `AlgebraicGeometry.invertibleSheafIsoZeroScheme` identifies `(M, t)` with
`(𝒪_Y(Z(t)), 1_{Z(t)})`. Coordinates of a meromorphic section transport along that isomorphism by
`Stacks.Divisors.IsCoordinateAt.mapStalkLinearMap`, so the statements of
`StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.KeyFormulaOnDivisor` for the invertible sheaf of a
divisor and its canonical section carry over to `(M, t)`.

## Main results

* `Stacks.Chow.isCoordinateAt_one_of_notMem_support_zeroScheme` — off `Z(t)` the generic value of
  `t` is the generic value of a generator of the stalk of `M`.
* `Stacks.Chow.KeyFormulaSituation.isRationallyEquivalentToZeroWithin_leftCoeff_zeroScheme` — the
  rational equivalence of the key formula is witnessed inside `Z(t)`.

## References

* [Stacks Project, Tag 0AYB](https://stacks.math.columbia.edu/tag/0AYB)
* [Stacks Project, Tag 0AYC](https://stacks.math.columbia.edu/tag/0AYC)
* [Stacks Project, Tag 01WY](https://stacks.math.columbia.edu/tag/01WY)
* [Stacks Project, Tag 01X0](https://stacks.math.columbia.edu/tag/01X0)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 02TM](https://stacks.math.columbia.edu/tag/02TM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.Divisors

/-- **A nonzero global section of an invertible module is a coordinate `1` of its own generic
value at every point off its zero scheme.** On an integral scheme the section is a
nonzerodivisor, so `Z(t)` is an effective Cartier divisor and `M` is the invertible sheaf of
`Z(t)` with `t` the canonical section; the statement is then
`Stacks.Chow.isCoordinateAt_one_divisorSheafGlobalSection` transported along that
isomorphism. -/
theorem isCoordinateAt_one_of_notMem_support_zeroScheme {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] (M : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]
    (t : Γ(M, ⊤)) (ht : t ≠ 0) {ξ : Y}
    (hξ : ξ ∉ ((Stacks.Divisors.zeroScheme Y M t).support : Set Y)) :
    IsCoordinateAt M ξ (M.presheaf.germ ⊤ (genericPoint Y) trivial t) 1 := by
  have hst : (Stacks.Divisors.sectionsOfTop M t).eval (op ⊤) = t :=
    Stacks.Divisors.sectionsOfTop_eval_top M t
  have hne : (Stacks.Divisors.sectionsOfTop M t).eval (op ⊤) ≠ 0 := by rw [hst]; exact ht
  have hreg : ∀ U : Y.Opens, Function.Injective fun r : Γ(Y, U) =>
      r • M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t := by
    have h := injective_smul_res_of_isRegularSection M (Stacks.Divisors.sectionsOfTop M t)
      (isRegularSection_of_eval_top_ne_zero M (Stacks.Divisors.sectionsOfTop M t) hne)
    rwa [hst] at h
  have hE : IsEffectiveCartierDivisor (Stacks.Divisors.zeroScheme Y M t) := by
    have h := isEffectiveCartierDivisor_zeroScheme_of_eval_top_ne_zero Y M
      (Stacks.Divisors.sectionsOfTop M t) hne
    rwa [hst] at h
  obtain ⟨φ, hsec⟩ : ∃ φ : M ≅ divisorSheaf (Stacks.Divisors.zeroScheme Y M t),
      φ.hom.val.app (op ⊤) t =
        divisorSheafGlobalSection (Stacks.Divisors.zeroScheme Y M t) :=
    ⟨invertibleSheafIsoZeroScheme M t hreg, invertibleSheafIsoZeroScheme_section M t hreg⟩
  have happ : φ.inv.val.app (op ⊤)
      (divisorSheafGlobalSection (Stacks.Divisors.zeroScheme Y M t)) = t := by
    rw [← hsec]
    exact congrArg (fun ψ : M ⟶ M => Scheme.Modules.Hom.app ψ ⊤ t) φ.hom_inv_id
  have hgerm : stalkLinearMap (divisorSheaf (Stacks.Divisors.zeroScheme Y M t)) M φ.inv
        (genericPoint Y)
        ((divisorSheaf (Stacks.Divisors.zeroScheme Y M t)).presheaf.germ ⊤ (genericPoint Y)
          trivial (divisorSheafGlobalSection (Stacks.Divisors.zeroScheme Y M t))) =
      M.presheaf.germ ⊤ (genericPoint Y) trivial t :=
    (stalkLinearMap_germ _ M φ.inv ⊤ (genericPoint Y) trivial _).trans
      (congrArg (fun z : Γ(M, ⊤) => M.presheaf.germ ⊤ (genericPoint Y) trivial z) happ)
  obtain ⟨m, hm, hsa⟩ := (isCoordinateAt_one_divisorSheafGlobalSection
    (Stacks.Divisors.zeroScheme Y M t) hξ).mapStalkLinearMap
      (divisorSheaf (Stacks.Divisors.zeroScheme Y M t)) M φ.inv
  exact ⟨m, hm, hgerm.symm.trans hsa⟩

/-- **The rational equivalence of the key formula for an invertible module with a nonzero global
section `t` is witnessed inside the zero scheme of `t`.** The generic value of `t` is the generic
value of a generator of the stalk of `M` at every point off `Z(t)`, so for the situation whose
generators of `M` are normalized the ratio `f_i` is `1` at every member `Z_i` whose generic point
is not on `Z(t)`, and the corresponding tame symbols drop out of the key formula. The surviving
members are contained in `Z(t)`, their supports being the closures of their generic points.

This generalizes
`Stacks.Chow.KeyFormulaSituation.isRationallyEquivalentToZeroWithin_leftCoeff_divisorSheaf` off
the invertible sheaf of a divisor and its canonical section. -/
theorem KeyFormulaSituation.isRationallyEquivalentToZeroWithin_leftCoeff_zeroScheme
    (C : ChowSituation.{u}) {Y : Scheme.{u}} (q : Y ⟶ C.S) [LocallyOfFiniteType q]
    [IsIntegral Y] [IsLocallyNoetherian Y] (M : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]
    (t : Γ(M, ⊤)) (ht : t ≠ 0) {N : Y.Modules}
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property N]
    {k : ℤ} (ℱ : KeyFormulaSituation M N)
    (hsection : ℱ.sectionL = M.presheaf.germ ⊤ (genericPoint Y) trivial t)
    (hdim : ∀ i : ℱ.Index,
      schemeDeltaDimension C (((ℱ.normalizeL.toKeyFormulaData C q).component i).subschemeι ≫ q) =
        ((k + 1 : ℤ) : EInt))
    (α : CycleGroup C q k)
    (hα : ∀ y : Y, α.1 y = (ℱ.normalizeL.toKeyFormulaData C q).leftCoeff C q y) :
    IsRationallyEquivalentToZeroWithin C q k α
      ((Stacks.Divisors.zeroScheme Y M t).support : Set Y) := by
  refine (ℱ.normalizeL.isRationallyEquivalentToZeroWithin_leftCoeff C q
    (fun i ↦ ℱ.componentPoint i ∈ ((Stacks.Divisors.zeroScheme Y M t).support : Set Y))
    (fun i hi ↦ ?_) hdim α hα).mono ?_
  · refine ℱ.normalizeL_ratioL_eq_one i ?_
    rw [hsection]
    exact isCoordinateAt_one_of_notMem_support_zeroScheme M t ht hi
  · refine Set.iUnion_subset fun j ↦ ?_
    rw [coe_support_integralComponentAt]
    exact ((Stacks.Divisors.zeroScheme Y M t).support.isClosed.closure_subset_iff).mpr
      (Set.singleton_subset_iff.mpr j.2)

end Stacks.Chow

end
