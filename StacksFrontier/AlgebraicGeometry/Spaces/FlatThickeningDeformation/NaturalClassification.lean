module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatThickeningDeformation.Classification
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The natural structures on flat deformations of an algebraic space (Stacks 0D17)

Let `S` be a scheme, `Y ⊂ Y'` a first order thickening of algebraic spaces over `S` and
`f : X ⟶ Y` a flat morphism of algebraic spaces over `S` admitting a flat deformation
`(f' : X' ⟶ Y', a)`. This file states [Stacks Project, Tag 0D17] with its natural structures:

1. the action of `Ext¹_{𝒪_X}(NL_{X/Y}, f^*𝒞_{Y/Y'})` on the set `Classes f` of isomorphism classes
   of pairs `(f', a)` is the one of [Stacks 08UK]: `ξ` carries `[D₁]` to `[D₂]` exactly when the
   obstruction class `Deformation.obstruction D₁ D₂` of [Stacks 08UG] of the two solutions
   `0 → f^*𝒞_{Y/Y'} → i⁻¹𝒪_{X'ᵢ} → 𝒪_X → 0` is `ξ`;
2. the identification of `Aut D` with `Ext⁰_{𝒪_X}(NL_{X/Y}, f^*𝒞_{Y/Y'})` is the composite of
   `φ ↦ (φ^♯)⁻¹` (`Deformation.autMulEquivAmbientSolution`) with the identification of
   [Stacks 08UG] of the automorphisms of a solution with `Ext⁰` (`solutionAutMulEquivExtZero`).

## Main definitions

* `AlgebraicGeometry.Space.FlatThickeningDeformation.Deformation.obstruction`: the obstruction
  class in `Ext¹_{𝒪_X}(NL_{X/Y}, f^*𝒞_{Y/Y'})` of two flat deformations.

## Main results

* `AlgebraicGeometry.Space.FlatThickeningDeformation.classes_addTorsor_vadd_iff`: part (1).
* `AlgebraicGeometry.Space.FlatThickeningDeformation.classes_naturalAddTorsor_and_autMulEquiv`:
  [Stacks 0D17].

## References

* [Stacks Project, Tag 0D17](https://stacks.math.columbia.edu/tag/0D17)
* [Stacks Project, Tag 08UK](https://stacks.math.columbia.edu/tag/08UK)
* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG)
-/

@[expose] public noncomputable section

open CategoryTheory
open Deformation.ToposThickening Deformation.ToposThickening.RingedToposExtensionProblem

universe t u

namespace AlgebraicGeometry.Space.FlatThickeningDeformation

attribute [local instance 1] Sheaf.hasWeakSheafifyCommRingCat

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Y' : AlgebraicSpaces B S hS} {Z : ClosedSubspaces B S hS Y'.1}
  (hZ : IsFirstOrderThickening B S hS Y' Z.1) {X : AlgebraicSpaces B S hS}
  (f : X ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))

/-- The abelian structure of the `𝒪_X`-modules with sections in `Type (u + 1)`, named so that
instance search does not meet the universe constraint posed by competing instances stated at a
maximum of universes. -/
local instance (priority := high) naturalClassificationAbelianLargeModules :
    Abelian (_root_.SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u} (smallEtaleRingedTopos B S hS X).O)) :=
  SheafOfModules.instAbelian _

variable [HasDerivedCategory.{t} (_root_.SheafOfModules.{u + 1}
  (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u} (smallEtaleRingedTopos B S hS X).O))]

variable {f} in
/-- **The obstruction class of two flat deformations** `D₁, D₂` of `f`, in
`Ext¹_{𝒪_X}(NL_{X/Y}, f^*𝒞_{Y/Y'})`: the obstruction class `o(𝒪'₁, 𝒪'₂)` of [Stacks 08UG] of
their solutions `0 → f^*𝒞_{Y/Y'} → i⁻¹𝒪_{X'ᵢ} → 𝒪_X → 0` (`Deformation.ambientSolution`),
computed on the `Type u` model of the small étale site of `X` and carried back to `Ext` out of
`NL_{X/Y}` by `modelExtAddEquiv`. -/
def Deformation.obstruction (D₁ D₂ : Deformation f) :
    DerivedCategory.Ext (DerivedCategory.Q.obj (naiveCotangentComplex B S hS f))
      ((DerivedCategory.singleFunctor _ 0).obj (liftedPulledBackConormal hZ f)) 1 :=
  letI := HasDerivedCategory.standard (_root_.SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleModelRingRestriction (smallEtaleRingedTopos B S hS X).O)))
  (modelExtAddEquiv hZ f 1).symm
    (modelObstruction hZ f (D₁.ambientSolution hZ) (D₂.ambientSolution hZ))

/-- **Part (1) of [Stacks Project, Tag 0D17], with its natural action**: for flat `f` admitting a
flat deformation, `Classes f` is principal homogeneous under `Ext¹_{𝒪_X}(NL_{X/Y}, f^*𝒞_{Y/Y'})`
for an action under which `ξ` carries the class of `D₁` to the class of `D₂` exactly when the
obstruction class `Deformation.obstruction D₁ D₂` of [Stacks 08UG] is `ξ` (the action of
[Stacks 08UK] on the solutions of the extension problem, read through `classesEquiv`). -/
theorem classes_addTorsor_vadd_iff (hf : IsFlat B S hS f.hom) (hD : Nonempty (Deformation f)) :
    ∃ T : AddTorsor
        (DerivedCategory.Ext (DerivedCategory.Q.obj (naiveCotangentComplex B S hS f))
          ((DerivedCategory.singleFunctor _ 0).obj (liftedPulledBackConormal hZ f)) 1)
        (Classes f),
      ∀ (ξ : DerivedCategory.Ext (DerivedCategory.Q.obj (naiveCotangentComplex B S hS f))
          ((DerivedCategory.singleFunctor _ 0).obj (liftedPulledBackConormal hZ f)) 1)
        (D₁ D₂ : Deformation f),
        T.vadd ξ (Quotient.mk (setoid f) D₁) = Quotient.mk (setoid f) D₂ ↔
          D₁.obstruction hZ D₂ = ξ := by
  let hM := HasDerivedCategory.standard (_root_.SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleModelRingRestriction (smallEtaleRingedTopos B S hS X).O)))
  obtain ⟨T, hT⟩ := solutionClasses_addTorsor_vadd_iff (hD := hM) hZ f
    ⟨hD.some.ambientSolution hZ⟩
  refine ⟨addTorsorTransfer T (classesEquiv hZ f hf) (AddEquiv.refl _), fun ξ D₁ D₂ => ?_⟩
  rw [addTorsorTransfer_vadd, Equiv.symm_apply_eq]
  refine (hT ξ (D₁.ambientSolution hZ) (D₂.ambientSolution hZ)).trans ?_
  unfold Deformation.obstruction
  rw [← AddEquiv.symm_apply_eq]

/-- **[Stacks Project, Tag 0D17]**, with its natural structures. Let `S` be a scheme, `Y ⊂ Y'` a
first order thickening of algebraic spaces over `S` (`hZ`) and `f : X ⟶ Y` a flat morphism of
algebraic spaces over `S` (`hf`). If there exists a flat `f' : X' ⟶ Y'` with an isomorphism
`a : X ≅ X' ×_{Y'} Y` over `Y` (`hD`; a `Deformation f` is exactly such a pair, see
`Deformation.ofPair`, `Deformation.pairIso`), then
1. the set `Classes f` of isomorphism classes of pairs `(f', a)` is principal homogeneous under
   `Ext¹_{𝒪_X}(NL_{X/Y}, f^*𝒞_{Y/Y'})`, for the action of [Stacks 08UK]: `ξ` carries `[D₁]` to
   `[D₂]` exactly when the obstruction class `Deformation.obstruction D₁ D₂` of [Stacks 08UG] of
   the two deformations is `ξ`; and
2. for every such pair `D`, the group `Aut D` of automorphisms `φ : X' ⟶ X'` over `Y'` reducing to
   the identity on `X' ×_{Y'} Y` is `Ext⁰_{𝒪_X}(NL_{X/Y}, f^*𝒞_{Y/Y'})`, by the group isomorphism
   sending `φ` to the class in `Ext⁰` of [Stacks 08UG] of the automorphism `(φ^♯)⁻¹` of the
   solution `0 → f^*𝒞_{Y/Y'} → i⁻¹𝒪_{X'} → 𝒪_X → 0` (`Deformation.autMulEquivAmbientSolution`
   followed by `solutionAutMulEquivExtZero`).

`NL_{X/Y}` is the canonical naive cotangent complex `naiveCotangentComplex B S hS f`; the module
`f^*𝒞_{Y/Y'}` is `liftedPulledBackConormal hZ f`; the `Ext` groups are those of any model of the
derived category of `𝒪_X`-modules. -/
@[stacks 0D17 "both parts, with the action on isomorphism classes characterised by the \
obstruction class of 08UG as in 08UK, and the isomorphism Aut = Ext^0 given explicitly through \
the automorphism (phi^#)^(-1) of the solution and 08UG"]
theorem classes_naturalAddTorsor_and_autMulEquiv (hf : IsFlat B S hS f.hom)
    (hD : Nonempty (Deformation f)) :
    (∃ T : AddTorsor
        (DerivedCategory.Ext (DerivedCategory.Q.obj (naiveCotangentComplex B S hS f))
          ((DerivedCategory.singleFunctor _ 0).obj (liftedPulledBackConormal hZ f)) 1)
        (Classes f),
      ∀ (ξ : DerivedCategory.Ext (DerivedCategory.Q.obj (naiveCotangentComplex B S hS f))
          ((DerivedCategory.singleFunctor _ 0).obj (liftedPulledBackConormal hZ f)) 1)
        (D₁ D₂ : Deformation f),
        T.vadd ξ (Quotient.mk (setoid f) D₁) = Quotient.mk (setoid f) D₂ ↔
          D₁.obstruction hZ D₂ = ξ) ∧
      ∀ D : Deformation f, ∃ e : Aut D ≃* Multiplicative (DerivedCategory.Ext
        (DerivedCategory.Q.obj (naiveCotangentComplex B S hS f))
        ((DerivedCategory.singleFunctor _ 0).obj (liftedPulledBackConormal hZ f)) 0),
        ∀ φ : Aut D, e φ = solutionAutMulEquivExtZero hZ f (D.ambientSolution hZ)
          (Deformation.autMulEquivAmbientSolution hZ D φ) :=
  ⟨classes_addTorsor_vadd_iff hZ f hf hD,
    fun D => ⟨D.autMulEquivNaiveCotangentExtZero hZ, fun _ => rfl⟩⟩

end AlgebraicGeometry.Space.FlatThickeningDeformation

end
