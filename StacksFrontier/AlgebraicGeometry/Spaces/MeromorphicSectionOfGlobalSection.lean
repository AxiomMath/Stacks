module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicFunctionsLocalFraction
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionSheafGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionTrivialChart
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroQuasiCompact

/-!
# The meromorphic section of a global section

Let `X` be an algebraic space over a scheme `S` and let `ℒ` be an `𝒪_X`-module. A global section
`s ∈ Γ(X, ℒ)` is a meromorphic section of `ℒ`: over every étale chart `V` it is the pure tensor
`1 ⊗ s|_V` of `𝒦_X(V) ⊗_{𝒪_X(V)} ℒ(V)`, read in the sheaf `𝒦_X(ℒ)` of Stacks 0EN5. This is the
map `Γ(X, ℒ) → Γ(X, 𝒦_X(ℒ))` induced by the canonical map `ℒ → 𝒦_X(ℒ)`. For an invertible `ℒ`,
a nonzero global section gives a nonzero meromorphic section.

## Main definitions

* `AlgebraicGeometry.Space.globalSectionMeromorphic`: the meromorphic section of a global
  section.

## Main results

* `AlgebraicGeometry.Space.globalSectionMeromorphic_eval`: its value over a chart is `1 ⊗ s|_V`.
* `AlgebraicGeometry.Space.globalSectionMeromorphic_ne_zero`: for an invertible module, the
  meromorphic section of a nonzero global section is nonzero.

## References

* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] chartMeromorphicAlgebra

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (L : Modules.{u, u} B S hS X hX)

/-- The meromorphic section of a global section: over an étale chart `V` it is the image of
`1 ⊗ s|_V` under the sheafification map `𝒦_X(V) ⊗_{𝒪_X(V)} ℒ(V) → 𝒦_X(ℒ)(V)` of Stacks 0EN5. -/
def globalSectionMeromorphic (s : L.sections) : MeromorphicSection.{u, u} B S hS X hX L :=
  PresheafOfModules.sectionsMk
    (fun V => toMeromorphicSectionSheaf B S hS X hX L V.unop
      ((1 : (meromorphicChartSheaf B S hS X hX).obj.obj V) ⊗ₜ[chartRing B S hS X hX V.unop]
        s.eval V))
    (fun V W f => by
      refine (toMeromorphicSectionSheaf_map B S hS X hX L V.unop W.unop f.unop _).trans ?_
      congr 1
      refine (meromorphicSectionModule_map_tmul B S hS X hX L V.unop W.unop f.unop _ _).trans ?_
      congr 1
      · exact map_one _
      · exact PresheafOfModules.sections_property s f)

/-- The value of the meromorphic section of a global section over a chart. -/
theorem globalSectionMeromorphic_eval (s : L.sections) (V : SmallEtale B S hS X) :
    (globalSectionMeromorphic B S hS hX L s).eval (op V) =
      toMeromorphicSectionSheaf B S hS X hX L V
        ((1 : (meromorphicChartSheaf B S hS X hX).obj.obj (op V)) ⊗ₜ[chartRing B S hS X hX V]
          s.eval (op V)) :=
  rfl

/-- For an invertible module the meromorphic section of a nonzero global section is nonzero. -/
theorem globalSectionMeromorphic_ne_zero
    (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L) {s : L.sections} (hs : s ≠ 0) :
    globalSectionMeromorphic B S hS hX L s ≠ 0 := by
  intro h0
  refine hs (PresheafOfModules.sections_ext _ _ fun U => ?_)
  obtain ⟨I, V, a, hcov, hgen⟩ := exists_generator_cover_smul_of_isInvertible B S hS
    (⟨X, hX⟩ : AlgebraicSpaces B S hS) L
    (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL) U.unop
  refine Stacks.SheafOfModules.eq_of_map_eq_of_sieve₀_mem L
    ⟨I, V, a⟩ hcov fun i => ?_
  obtain ⟨e, hcompat, hbij⟩ := hgen i
  obtain ⟨r, hr⟩ := (hbij (V i) (𝟙 (V i))).2 ((L.val.map (a i).op).hom (s.eval U))
  have hsV : s.eval (op (V i)) = r • e (V i) (𝟙 (V i)) :=
    (PresheafOfModules.sections_property s (a i).op).symm.trans hr.symm
  have hzero : toMeromorphicSectionSheaf B S hS X hX L (V i)
      (algebraMap (chartRing B S hS X hX (V i))
        ((meromorphicChartSheaf B S hS X hX).obj.obj (op (V i))) r ⊗ₜ[
        chartRing B S hS X hX (V i)] e (V i) (𝟙 (V i)) :
          (meromorphicSectionModule B S hS X hX L).obj (op (V i))) =
      toMeromorphicSectionSheaf B S hS X hX L (V i)
        ((0 : (meromorphicChartSheaf B S hS X hX).obj.obj (op (V i))) ⊗ₜ[
          chartRing B S hS X hX (V i)] e (V i) (𝟙 (V i)) :
            (meromorphicSectionModule B S hS X hX L).obj (op (V i))) := by
    have h := congrArg (fun t : MeromorphicSection.{u, u} B S hS X hX L => t.eval (op (V i))) h0
    refine Eq.trans ?_ (h.trans ((congrArg (toMeromorphicSectionSheaf B S hS X hX L (V i))
      (TensorProduct.zero_tmul (R := chartRing B S hS X hX (V i)) _
        (e (V i) (𝟙 (V i))))).trans (map_zero _)).symm)
    change _ = toMeromorphicSectionSheaf B S hS X hX L (V i)
      ((1 : (meromorphicChartSheaf B S hS X hX).obj.obj (op (V i))) ⊗ₜ[
        chartRing B S hS X hX (V i)] s.eval (op (V i)))
    rw [hsV, meromorphicSectionModule_tmul_smul, mul_one]
    rfl
  have hr0 : r = 0 := injective_toMeromorphicFunctionSheaf B S hS X hX (V i)
    ((injective_toMeromorphicSectionSheaf_tmul B S hS X hX L (V i) e hcompat hbij hzero).trans
      (map_zero _).symm)
  refine ((PresheafOfModules.sections_property s (a i).op).trans ?_).trans (map_zero _).symm
  exact hsV.trans (by rw [hr0, zero_smul]; rfl)

end AlgebraicGeometry.Space

end
