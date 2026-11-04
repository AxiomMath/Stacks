module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.JacobianFrobenius
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.PicardDegreeZeroDivisible
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.ZPowFiniteLocallyFree

/-!
# The jacobian of a curve over an algebraically closed field has dimension the genus

Let `X` be a smooth proper curve over an algebraically closed field `k`. The degree-zero
component of the Picard scheme is an abelian variety `J` with `J(k) ≅ Pic⁰(X)`, smooth of
relative dimension `g = genus X` over `k`, so `dim J = g`. This packages the jacobian data used
by the proof of Tag 03VM, where `g ≥ 1` gives `J[n] ≅ (ℤ/n)^{2g} ≠ 0`.

## Main results

* `Stacks.Zeta.exists_jacobian_data_abelianVarietyDimension_eq_genus` — the jacobian, its points
  and its dimension.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Zeta

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k))
  [IsCurve k g] [Smooth g] [IsProper g] (hdim : topologicalKrullDim X ≤ 1)

/-- **The jacobian of a smooth proper curve over an algebraically closed field**: an abelian
variety `J` with `J(k) ≅ Pic⁰(X)` and `dim J = genus X`. -/
theorem exists_jacobian_data_abelianVarietyDimension_eq_genus :
    ∃ (A : Over (Spec (.of k))) (_ : GrpObj A) (_ : IsAbelianVariety k A)
      (_ : Additive (𝟙_ (Over (Spec (.of k))) ⟶ A) ≃+ picardDegreeZero k g hdim),
      Stacks.Groupoids.abelianVarietyDimension A = genus g := by
  let S₀ : Set Scheme.{u} := {X, Spec (.of k)}
  have : Small.{u} S₀ := by dsimp [S₀]; infer_instance
  obtain ⟨B, hB⟩ := BigFppfSite.exists_containing S₀
  have hX : B.Contains X := hB X (by simp [S₀])
  have hk : B.Contains (Spec (.of k)) := hB _ (by simp [S₀])
  let f : B.obj hX ⟶ B.obj hk := ObjectProperty.homMk g
  have : IsCurve k (B.inclusion.map f) := ‹IsCurve k g›
  have : Smooth (B.inclusion.map f) := ‹Smooth g›
  have : IsProper (B.inclusion.map f) := ‹IsProper g›
  have : IrreducibleSpace X := inferInstance
  have : GeometricallyIrreducible (B.inclusion.map f) :=
    geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k X g
  have hproj : IsProjective (B.inclusion.map f) :=
    (isProjectiveVariety_iff_isProjective k g).1
      ((isProjectiveVariety_iff_isProjectiveMorphism k g).2
        (isProjectiveMorphism_of_isProper_of_isCurve k g))
  have : IsProjectiveVariety k (B.inclusion.map f) :=
    (isProjectiveVariety_iff_isProjective k g).2 hproj
  have : Nonempty X := inferInstance
  obtain ⟨σ, hσ⟩ := Stacks.RigidifiedPicard.exists_section_of_smooth_of_isSepClosed k g
  have := Stacks.RigidifiedPicard.isRepresentable_picardFunctor_of_isSepClosed k B hX hk f
    (isProjectiveMorphism_of_isProper_of_isCurve k g)
  have := Stacks.PicardFunctor.isAbelianVariety_jacobian B hX hk f σ hσ
  set A := (Stacks.PicardFunctor.jacobianGrp B hX hk f σ hσ).X
  have : SmoothOfRelativeDimension (genus (B.inclusion.map f)) A.hom :=
    Stacks.PicardFunctor.smoothOfRelativeDimension_picardSchemeDegreeComponent B hX hk f σ hσ 0
  have : Nonempty A.left := ⟨(η[A]).left (IsLocalRing.closedPoint k)⟩
  have hdimA : Stacks.Groupoids.abelianVarietyDimension A = genus g := by
    have h1 := topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field
      (genus (B.inclusion.map f)) A.hom
    have h2 := Stacks.Groupoids.topologicalKrullDim_eq_abelianVarietyDimension A
    rw [h1] at h2
    exact_mod_cast h2.symm
  exact ⟨A, inferInstance, inferInstance,
    Stacks.PicardFunctor.jacobianPointsAddEquiv B hX hk f σ hσ hdim, hdimA⟩

end Stacks.Zeta

end
