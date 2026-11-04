module

public import StacksFrontier.AlgebraicGeometry.DeRham.PoincareDuality.TopDifferentialFrobenius
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.GlobalSectionsPointedConnected
public import StacksFrontier.AlgebraicGeometry.CohomologyGlobalSectionScalar.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.SmoothDualizingModule
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen

/-!
# The top cohomology of differential forms of a pointed proper smooth variety is a line

Let `Z` be irreducible, proper and smooth over a field `k`, of dimension `n`, with a `k`-rational
point. Then `Hⁿ(Z, Ωⁿ_{Z/k})` is one-dimensional over `k`: it is dual to `H⁰(Z, 𝒪_Z)` by
[Stacks, Tag 0FW4], with the dualizing module of [Stacks, Tag 0FVV] (7), and `H⁰(Z, 𝒪_Z) = k`
because `Z` is connected, normal and has a rational point. Read on the cohomology groups `Hgroup`,
with `k` acting through multiplication by functions from the base, every class is a multiple of
any nonzero class.

This is the dimension count "`H^n(X_k, Ω^n_{X_k/k})` is one-dimensional" behind the claim that `ξ`
is a basis element in the proof of [Stacks, Tag 0G8J].

## Main results

* `AlgebraicGeometry.TopDegreeDifferential.finrank_topForms_eq_one_of_section`.
* `AlgebraicGeometry.TopDegreeDifferential.exists_eq_globalSmul_of_ne_zero`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Duality (dualizingModule globalRingHom)
open Stacks.Cohomology.GlobalKunneth (baseRing)

universe u

namespace AlgebraicGeometry.TopDegreeDifferential

variable {k : Type u} [Field k] {Z : Scheme.{u}} (h : Z ⟶ Spec (.of k)) [IsProper h] [Smooth h]
  [IrreducibleSpace Z] (σ : Spec (.of k) ⟶ Z) (hσ : σ ≫ h = 𝟙 _) (n : ℕ)
  (hd : topologicalKrullDim Z = n)

include hσ hd in
/-- **`Hⁿ(Z, Ωⁿ_{Z/k})` is one-dimensional** for `Z` irreducible, proper and smooth of dimension
`n` over `k` with a rational point. -/
theorem finrank_topForms_eq_one_of_section :
    Module.finrank k ((ModuleCat.restrictScalars (globalRingHom h)).obj
      (((SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)).rightDerived n).obj
        (Scheme.Hom.relativeDifferentialForms h n))) = 1 := by
  have hequi := TopologicalSpace.Equidimensional.of_preirreducibleSpace Z
  have : SmoothOfRelativeDimension n h :=
    smoothOfRelativeDimension_of_equidimensional k h hequi n hd
  obtain ⟨-, hrank⟩ := finiteDimensional_and_finrank_eq h
    (isCohenMacaulay_of_syntomic_over_field h (syntomic_of_smooth _)) hequi n hd
    (Stacks.Duality.nonempty_relativeDualizingComplex_iso_and_relativeDualizingModule_iso_of_smooth
      h n).2.some
  exact hrank.trans <| finrank_globalSections_eq_one_of_section k h σ hσ

include hσ hd in
/-- **Every class of `Hⁿ(Z, Ωⁿ_{Z/k})` is a multiple of a nonzero class**, the scalar `c ∈ k`
acting by multiplication by its image in `Γ(Z, 𝒪_Z)`. -/
theorem exists_eq_globalSmul_of_ne_zero
    (x₀ : Hgroup Z.ringCatSheaf ⊤ n (Scheme.Hom.relativeDifferentialForms h n)) (hx₀ : x₀ ≠ 0)
    (y : Hgroup Z.ringCatSheaf ⊤ n (Scheme.Hom.relativeDifferentialForms h n)) :
    ∃ c : k, y = ((Hfunctor Z.ringCatSheaf ⊤ n).map
      (globalSmul (globalRingHom h c) (Scheme.Hom.relativeDifferentialForms h n))).hom x₀ := by
  let F := Scheme.Hom.relativeDifferentialForms h n
  let E := (Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso
    Z.ringCatSheaf ⊤ n).app F
  let V := (ModuleCat.restrictScalars (globalRingHom h)).obj
    (((SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)).rightDerived n).obj F)
  let v₀ : V := E.inv x₀
  have hv₀ : v₀ ≠ 0 := fun h0 => hx₀ <| by
    simpa [v₀, Iso.inv_hom_id_apply] using (congrArg E.hom.hom h0).trans (map_zero _)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' v₀ hv₀).1
    (finrank_topForms_eq_one_of_section h σ hσ n hd) (E.inv y)
  refine ⟨c, ?_⟩
  have hnat := congrArg (fun φ => φ.hom (E.inv x₀))
    ((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso Z.ringCatSheaf ⊤
      n).hom.naturality (globalSmul (globalRingHom h c) F))
  change E.hom ((((AlgebraicGeometry.moduleGlobalSections Z).rightDerived n).map
      (globalSmul (globalRingHom h c) F)).hom (E.inv x₀)) =
    ((Hfunctor Z.ringCatSheaf ⊤ n).map (globalSmul (globalRingHom h c) F)).hom
      (E.hom (E.inv x₀)) at hnat
  rw [Iso.inv_hom_id_apply] at hnat
  have key : (((AlgebraicGeometry.moduleGlobalSections Z).rightDerived n).map
      (globalSmul (globalRingHom h c) F)).hom (E.inv x₀) = E.inv y := by
    rw [globalSmul_eq_smul_id, Functor.map_smul, CategoryTheory.Functor.map_id]
    exact hc
  rw [← hnat, key, Iso.inv_hom_id_apply]

end AlgebraicGeometry.TopDegreeDifferential

end
