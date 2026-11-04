module

public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedFullyFaithful
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorFullyFaithful
public import StacksFrontier.Algebra.DifferentialGraded.Module.EvaluationAtOne
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerived
public import StacksCore.Tactic.StacksAttribute
import all StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedFullyFaithful

/-!
# Additions to `StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedFullyFaithful`

Declarations extending
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedFullyFaithful`, kept in their own
module.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open DifferentialGradedModule

namespace CategoryTheory.Adjunction

universe w v₁ v₂ u₁ u₂

section Devissage

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [HasZeroObject C] [HasZeroObject D] [Preadditive C] [Preadditive D]
  [HasShift C ℤ] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated C] [Pretriangulated D]
  [HasCoproducts.{w} D] {F : D ⥤ C} {G : C ⥤ D}

/-- **The unit of an adjunction is invertible when the source admits a dévissage to the shifts of
a weak generator on which the left adjoint is bijective on morphisms.** Let `F ⊣ G` be an
adjunction of exact functors compatible with the translation between pretriangulated categories,
let `E` be a weak generator of the source of `F`, and assume

* `G` preserves the direct sums, indexed by types in the universe `w`, of objects in the image of
  `F`;
* `F` is bijective from `Hom(E, E[n])` onto `Hom(F E, F (E[n]))` for every `n : ℤ`;
* every property of objects of the source which holds of the shifts of `E`, passes to direct
  sums indexed by types in the universe `w`, and satisfies two-out-of-three in a distinguished
  triangle, holds of every object.

Then the unit of the adjunction is an isomorphism.

The three clauses of the dévissage are exactly
`CategoryTheory.Adjunction.isIso_unit_app_sigma_of_preservesColimit`,
`CategoryTheory.Adjunction.isIso_unit_app_of_mem_distTriang` and
`CategoryTheory.Adjunction.isIso_unit_app_shift_of_bijective_map` for the property "the unit is
invertible at this object". -/
theorem isIso_unit_of_devissage_of_preservesColimit (adj : F ⊣ G)
    [F.CommShift ℤ] [G.CommShift ℤ] [adj.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
    (hG : ∀ {ι : Type w} (Z : ι → D), PreservesColimit (Discrete.functor fun i => F.obj (Z i)) G)
    {E : D} (hgen : (ObjectProperty.singleton E).IsWeakTriangulatedGenerator)
    (hbij : ∀ n : ℤ, Function.Bijective (fun f : E ⟶ E⟦n⟧ => F.map f))
    (hdev : ∀ T : D → Prop,
      (∀ {ι : Type w} (Z : ι → D), (∀ i, T (Z i)) → T (∐ Z)) →
      (∀ Δ : Triangle D, Δ ∈ distTriang D →
        (T Δ.obj₁ → T Δ.obj₂ → T Δ.obj₃) ∧ (T Δ.obj₁ → T Δ.obj₃ → T Δ.obj₂) ∧
          (T Δ.obj₂ → T Δ.obj₃ → T Δ.obj₁)) →
      (∀ k : ℤ, T (E⟦k⟧)) → ∀ M : D, T M) :
    IsIso adj.unit := by
  have key : ∀ M : D, IsIso (adj.unit.app M) :=
    hdev (fun M => IsIso (adj.unit.app M)) (fun {_} Z hZ => have := hG Z
      adj.isIso_unit_app_sigma_of_preservesColimit Z hZ)
      (fun Δ hΔ => adj.isIso_unit_app_of_mem_distTriang Δ hΔ)
      (fun k => adj.isIso_unit_app_shift_of_bijective_map hgen hbij k)
  exact NatIso.isIso_of_isIso_app _

/-- **A left adjoint is fully faithful when the source admits a dévissage to the shifts of a weak
generator on which it is bijective on morphisms.** This is Tag 07RB — a left adjoint whose unit
is invertible is fully faithful — applied to
`CategoryTheory.Adjunction.isIso_unit_of_devissage_of_preservesColimit`. Full faithfulness is
data, a chosen inverse to the action on morphism groups, so this is a definition. -/
def fullyFaithfulL_of_devissage_of_preservesColimit (adj : F ⊣ G)
    [F.CommShift ℤ] [G.CommShift ℤ] [adj.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
    (hG : ∀ {ι : Type w} (Z : ι → D), PreservesColimit (Discrete.functor fun i => F.obj (Z i)) G)
    {E : D} (hgen : (ObjectProperty.singleton E).IsWeakTriangulatedGenerator)
    (hbij : ∀ n : ℤ, Function.Bijective (fun f : E ⟶ E⟦n⟧ => F.map f))
    (hdev : ∀ T : D → Prop,
      (∀ {ι : Type w} (Z : ι → D), (∀ i, T (Z i)) → T (∐ Z)) →
      (∀ Δ : Triangle D, Δ ∈ distTriang D →
        (T Δ.obj₁ → T Δ.obj₂ → T Δ.obj₃) ∧ (T Δ.obj₁ → T Δ.obj₃ → T Δ.obj₂) ∧
          (T Δ.obj₂ → T Δ.obj₃ → T Δ.obj₁)) →
      (∀ k : ℤ, T (E⟦k⟧)) → ∀ M : D, T M) :
    F.FullyFaithful :=
  haveI := adj.isIso_unit_of_devissage_of_preservesColimit hG hgen hbij hdev
  adj.fullyFaithfulLOfIsIsoUnit

end Devissage

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.RingedSite

universe u v w t s

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})
  (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)

end AlgebraicGeometry.RingedSite

end
