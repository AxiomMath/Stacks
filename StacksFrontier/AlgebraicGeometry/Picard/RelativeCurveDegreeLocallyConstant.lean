module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFibreEulerCharacteristicUnconditional
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatRankOpenUniversal
public import StacksFrontier.AlgebraicGeometry.Picard.RelativeCurveDegree
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.CohomologyOpenSubfunctor

/-!
# The degree on a flat proper relative curve is locally constant

Let `π : Y ⟶ T` be flat, proper and of finite presentation with fibres of dimension at most one.
The degree of an invertible module `ℒ` on the fibre over `t` is `χ(Y_t, ℒ_t) - χ(Y_t, 𝒪_{Y_t})`,
and both Euler characteristics are locally constant in `t` by [Stacks, Tag 0B9T]. So the degree
of a Picard class of `Y` is a locally constant function on `T`. This is the first step of the
proof of [Stacks, Tag 0BA0]: it cuts the Picard functor into open and closed pieces of fixed
degree.

## Main results

* `AlgebraicGeometry.isLocallyConstant_relativeInvertibleDegreeHom` — the degree of a Picard
  class is locally constant.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

universe u

namespace AlgebraicGeometry

variable {Y T : Scheme.{u}} (π : Y ⟶ T) [Flat π] (hfp : FinitePresentation π) [IsProper π]
  (hdim : ∀ t : T, topologicalKrullDim ↥(π.fiber t) ≤ 1)

include hfp in
/-- **The degree of a Picard class on a flat proper relative curve is locally constant on the
base**, by [Stacks, Tag 0B9T] applied to the class and to the structure sheaf. -/
theorem isLocallyConstant_relativeInvertibleDegreeHom (c : Stacks.Picard.ofScheme Y) :
    IsLocallyConstant (relativeInvertibleDegreeHom π hdim c) := by
  set L := (Stacks.Picard.picardRepresentative Y.toRingedSpace c).obj
  have hL := (Stacks.Picard.picardRepresentative Y.toRingedSpace c).property
  obtain ⟨hLfp, hLflat⟩ := isFinitePresentation_and_isFlatOver_of_isInvertible π L hL
  obtain ⟨hOfp, hOflat⟩ := isFinitePresentation_and_isFlatOver_of_isInvertible π
    (SheafOfModules.unit Y.ringCatSheaf) (Stacks.SheafOfModules.isInvertible_unit _ _)
  have h1 := isLocallyConstant_fibreEulerCharacteristic π hfp L hLfp hLflat
  have h2 := isLocallyConstant_fibreEulerCharacteristic π hfp _ hOfp hOflat
  have heq : relativeInvertibleDegreeHom π hdim c =
      fibreEulerCharacteristic π L -
        fibreEulerCharacteristic π (SheafOfModules.unit Y.ringCatSheaf) := by
    funext t
    rw [relativeInvertibleDegreeHom_apply, relativeInvertibleDegreeHomAt_apply,
      invertibleCurveDegreeHom_apply, Pi.sub_apply]
    obtain ⟨e₁⟩ := Stacks.RigidifiedPicard.nonempty_iso_pullback_picardRepresentative (π.fiberι t) c
    show _ = eulerSum (T.residueField t) (π.fiberToSpecResidueField t)
        ((Scheme.Modules.pullback (π.fiberι t)).obj L) -
      eulerSum (T.residueField t) (π.fiberToSpecResidueField t)
        ((Scheme.Modules.pullback (π.fiberι t)).obj (SheafOfModules.unit Y.ringCatSheaf))
    have h₂ : eulerSum (T.residueField t) (π.fiberToSpecResidueField t)
        ((Scheme.Modules.pullback (π.fiberι t)).obj (SheafOfModules.unit Y.ringCatSheaf)) =
        eulerSum (T.residueField t) (π.fiberToSpecResidueField t)
          (SheafOfModules.unit (π.fiber t).ringCatSheaf) :=
      eulerSum_congr _ _ (Scheme.Modules.pullbackUnitIso (π.fiberι t))
    rw [eulerSum_congr _ _ e₁, h₂]
    rfl
  rw [heq]
  exact h1.sub h2

end AlgebraicGeometry

end
