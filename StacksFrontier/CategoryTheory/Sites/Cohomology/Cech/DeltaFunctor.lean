module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.ObjectProperty.FiniteLimits
public import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexOfAFamily
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexAsBoundedBelowFunctor
import StacksCore.Tactic.StacksAttribute

/-!
# Čech cohomology of presheaves as a cohomological delta functor

Let `E = {U_i → U}` be a family of morphisms of a category `C` with fixed target, all of
whose finite nonempty fibre products exist. Stacks 03AR asserts that the Čech cohomology
groups `H^n(E, -)` of Stacks 03AM, viewed as functors on abelian presheaves, form a
cohomological delta functor: a short exact sequence of abelian presheaves gives rise to a
long exact sequence of Čech cohomology groups, functorially in the short exact sequence.

## Main definitions

* `Stacks.CechSite.cechCohomologyDeltaFunctor`: the cohomological delta functor on abelian
  presheaves whose `n`-th functor is, on the nose, the `n`-th Čech cohomology of Stacks
  03AM.

## Implementation notes

The statement is packaged as a subtype: the data is a `DeltaFunctor` and the property pins
its `n`-th functor down to the composite of `Stacks.CechSite.cechComplexFunctor` with the
`n`-th homology functor, so that the delta functor really is Čech cohomology and not merely
isomorphic to it. Both sides are literally equal, which is what lets the connecting maps be
transported to the Čech cohomology groups without a comparison isomorphism.

The coefficient universe `a` is independent of the universes of the site, so the same delta
functor is available at every universe containing the index universe `w` of the family.

## References

* [Stacks Project, Tag 03AR](https://stacks.math.columbia.edu/tag/03AR)
* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
* [Stacks Project, Tag 03AQ](https://stacks.math.columbia.edu/tag/03AQ)
-/

@[expose] public section

namespace Stacks.CechSite

universe w v a u

open CategoryTheory CategoryTheory.Limits

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C : Type u} [Category.{v} C] {X : C} (E : PreZeroHypercover.{w} X)

/-- The Čech cohomology functors of a family of morphisms with fixed target
form a cohomological delta functor on abelian presheaves, whose `n`-th functor is the `n`-th
Čech cohomology functor of Stacks 03AM. -/
@[stacks 03AR]
public noncomputable def cechCohomologyDeltaFunctor
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun b ↦ Over.mk (E.f (i b)))] :
    { F : DeltaFunctor
        (CategoryTheory.Functor Cᵒᵖ AddCommGrpCat.{max w a}) AddCommGrpCat.{max w a} //
      ∀ n : ℕ, F.functor n = cechComplexFunctor E ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{max w a} (ComplexShape.up ℕ) n } := by
  let K := cechComplexFunctor (A := AddCommGrpCat.{max w a}) E
  have hK : exactFunctor _ _ K := by
    let h := (exactFunctor_iff _).mp (cechComplexPlusFunctor_exact E)
    let := h.1
    let := h.2
    let : (CochainComplex.plus AddCommGrpCat.{max w a}).IsClosedUnderFiniteLimits :=
      ⟨fun _ _ _ ↦ inferInstance⟩
    let : (CochainComplex.plus AddCommGrpCat.{max w a}).IsClosedUnderFiniteColimits :=
      ⟨fun _ _ _ ↦ inferInstance⟩
    have : PreservesFiniteLimits
        (K ⋙ ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{max w a}) := by
      change PreservesFiniteLimits
        (cechComplexPlusFunctor (A := AddCommGrpCat.{max w a}) E ⋙ CochainComplex.Plus.ι _)
      infer_instance
    have : PreservesFiniteColimits
        (K ⋙ ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{max w a}) := by
      change PreservesFiniteColimits
        (cechComplexPlusFunctor (A := AddCommGrpCat.{max w a}) E ⋙ CochainComplex.Plus.ι _)
      infer_instance
    let :=
      (ComplexShape.embeddingUpNat.fullyFaithfulExtendFunctor AddCommGrpCat.{max w a}).full
    let :=
      (ComplexShape.embeddingUpNat.fullyFaithfulExtendFunctor AddCommGrpCat.{max w a}).faithful
    exact ⟨preservesFiniteLimits_of_reflects_of_preserves K
        (ComplexShape.embeddingUpNat.extendFunctor _),
      preservesFiniteColimits_of_reflects_of_preserves K
        (ComplexShape.embeddingUpNat.extendFunctor _)⟩
  rw [exactFunctor_iff] at hK
  letI := hK.1
  letI := hK.2
  letI : K.Additive := (exactFunctor_le_additiveFunctor _ _) K hK
  refine ⟨{
    functor n := K ⋙ HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) n
    additive n := by dsimp [K]; infer_instance
    δ hS n := (hS.map_of_exact K).δ n (n + 1) (by simp)
    map_g_δ hS n := (hS.map_of_exact K).comp_δ n (n + 1) (by simp)
    δ_map_f hS n := (hS.map_of_exact K).δ_comp n (n + 1) (by simp)
    mono_map_f {S} hS := by
      have := (hS.map_of_exact K).mono_f
      exact HomologicalComplex.mono_homologyMap_of_mono_of_not_rel (S.map K).f 0 (by simp)
    exact_map hS n := (hS.map_of_exact K).homology_exact₂ n
    exact_δ₁ hS n := (hS.map_of_exact K).homology_exact₃ n (n + 1) (by simp)
    exact_δ₂ hS n := (hS.map_of_exact K).homology_exact₁ n (n + 1) (by simp)
    δ_naturality {S T} hS hT φ n := by
      change HomologicalComplex.homologyMap (K.map φ.τ₃) n ≫ _ =
        _ ≫ HomologicalComplex.homologyMap (K.map φ.τ₁) (n + 1)
      exact (HomologicalComplex.HomologySequence.δ_naturality
        (K.mapShortComplex.map φ) (hS.map_of_exact K) (hT.map_of_exact K)
        n (n + 1) (by simp)).symm
  }, by intro n; dsimp [K]⟩

end Stacks.CechSite

end
