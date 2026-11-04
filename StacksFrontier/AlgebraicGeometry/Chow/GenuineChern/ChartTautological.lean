module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.PullbackExt
public import StacksFrontier.AlgebraicGeometry.RelativeProjDegreeOne.Tautological

/-!
# The tautological map of a projective bundle, read on a chart

Let `ℰ` be a module on a scheme `X` with quasi-coherent symmetric powers, `π : 𝐏(ℰ) ⟶ X` its
projective bundle and `π^*ℰ ⟶ 𝒪(1)` the tautological map. Over an affine open `U` of `X`:

* the tautological map sends the pullback `π^*x` of a section `x ∈ Γ(U, ℰ)` to the value of the
  degree-one homogeneous-section map `ψ₁` at the degree-one element `x` of `Γ(U, Sym ℰ)`;
* under the chart identification of `𝒪(1)` on `Proj Γ(U, Sym ℰ)` with the twisting sheaf, that
  value is the global section of `𝒪(1)` attached to `x`.

## Main results

* `Stacks.Chow.GenuineChern.unitSection_pullback_map`: naturality of pulled-back sections.
* `Stacks.Chow.GenuineChern.tautologicalMap_unitSection`.
* `Stacks.Chow.GenuineChern.chartIso_inv_degreeSection`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.RelativeProjDegreeOne Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.ProjTwistSections Stacks.SymGraded

universe u

namespace Stacks.Chow.GenuineChern

/-- **Naturality of pulled-back sections.** -/
theorem unitSection_pullback_map {X Y : Scheme.{u}} (f : X ⟶ Y) {M N : Y.Modules} (φ : M ⟶ N)
    (U : Y.Opens) (x : Γ(M, U)) :
    ((Scheme.Modules.pullback f).map φ).val.app (op (f ⁻¹ᵁ U)) (unitSection f M U x) =
      unitSection f N U (φ.val.app (op U) x) :=
  congrArg
    (fun ρ : M ⟶ (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj N) =>
      ρ.val.app (op U) x)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality φ).symm

variable {X : Scheme.{u}} (E : X.Modules) (hqc : IsQuasicoherentPieces E)

/-- **The tautological map on a pulled-back section** is the degree-one homogeneous-section map
at the corresponding degree-one element of `Sym ℰ`. -/
theorem tautologicalMap_unitSection (U : X.Opens) (x : Γ(E, U)) :
    (Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc).val.app
        (op ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U))
        (unitSection (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase E U x) =
      ((projectiveBundleTwistData E hqc).ψ 1).val.app (op U)
        ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op U) x) :=
  (congrArg (fun w =>
      (Stacks.ProjectiveBundleSplitting.tautologicalTwistMap E hqc 1).val.app
        (op ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U)) w)
      (unitSection_pullback_map _ (Scheme.Modules.symmetricAlgebraGen X E) U x)).trans
    (app_homEquiv_symm _ _ U _)

variable {E hqc} in
/-- **The chart identification carries the global section of `𝒪(1)` attached to a degree-one
element to the restriction of the homogeneous-section map.** This is the field
`RelativeProjTwists.TwistData.ψ_chart` with the transport along `ChartData.chart_range`
discharged. -/
theorem chartIso_inv_degreeSection (U : X.Opens) (hU : IsAffineOpen U)
    (a : (schemeSheafGradedAlgebra E hqc).sectionPieces U 1)
    (h : (relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU ''ᵁ ⊤ ≤
      (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U) :
    letI := (projectiveBundleTwistData E hqc).chartData.chart_isOpenImmersion U hU
    ((projectiveBundleTwistData E hqc).chartData.chartIso U hU ((1 : ℕ) : ℤ)).inv.val.app (op ⊤)
        (degreeSection ((schemeSheafGradedAlgebra E hqc).grading U) 1
          ⟨DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces U) 1 a,
            (schemeSheafGradedAlgebra E hqc).of_mem_grading U a⟩) =
      ((projectiveBundleTwistData E hqc).algebra.piece ((1 : ℕ) : ℤ)).val.map (homOfLE h).op
        (((projectiveBundleTwistData E hqc).ψ 1).val.app (op U) a) := by
  let := (projectiveBundleTwistData E hqc).chartData.chart_isOpenImmersion U hU
  refine Eq.trans ?_ (map_eqRec ((projectiveBundleTwistData E hqc).chartData.chart_range U hU)
    (((projectiveBundleTwistData E hqc).ψ 1).val.app (op U) a) le_rfl h)
  refine Eq.trans ?_ (congrArg (fun w =>
    ((projectiveBundleTwistData E hqc).algebra.piece ((1 : ℕ) : ℤ)).val.map
      (homOfLE (le_refl ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU ''ᵁ ⊤))).op w)
    ((projectiveBundleTwistData E hqc).ψ_chart U hU 1 a))
  rw [show (homOfLE (le_refl ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU ''ᵁ ⊤)))
    = 𝟙 _ from rfl, op_id, PresheafOfModules.map_id]
  rfl

end Stacks.Chow.GenuineChern

end
