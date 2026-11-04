module

public import StacksFrontier.AlgebraicGeometry.Stacks.TensorFunctors.TildeUnit
public import StacksFrontier.AlgebraicGeometry.Stacks.TensorFunctors.TensorFunctorAlgebra

/-!
# Multiplication by a global function on `g_*𝒪_U` is `g_*𝒪_U`-linear

Let `g : U ⟶ 𝒳` be an affine 1-morphism from a scheme `U` to an algebraic stack, with ring of
global functions `A = Γ(U, 𝒪_U)`.  For `a ∈ A`, multiplication by `a` on `𝒪_U` has direct image
`κ(a) : g_*𝒪_U ⟶ g_*𝒪_U`, and the square of the proof of Stacks 0GRK commutes:
`(κ(a) ⊗ 1) ≫ μ = μ ≫ κ(a)` for the multiplication `μ` of the commutative monoid `g_*𝒪_U`.

## Main results

* `AlgebraicGeometry.Stack.affinePushforward_map_globalMul_whiskerRight_mul`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

universe u w

namespace AlgebraicGeometry.Stack

attribute [local instance] FibredSite.hasWeakSheafify_associatedTopology
  FibredSite.wEqualsLocallyBijective_associatedTopology
  AlgebraicStacks.modulesMonoidalCategory AlgebraicStacks.modulesSymmetricCategory

local notation "𝒪[" Y "]" => AlgebraicStacks.fppfStructureRingSheaf _ _ _ Y
local notation "𝒪c[" Y "]" => AlgebraicStacks.fppfStructureSheaf _ _ _ Y

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U : BigFppfOver B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
  (g : schemeStack.{u, w} B S hS U ⟶ 𝒳) (hg : AlgebraicStacks.IsAffineHom B S hS g)

/-- The global function `a ∈ A`, pulled back to `r x = U ×_𝒳 x` for every object `x` of `𝒳`. -/
noncomputable abbrev pushforwardGlobalSection (a : schemeGlobalRing U)
    (x : 𝒳.val.val.objᵒᵖ) :
    ((affineRightAdjoint g hg).op ⋙ (𝒪c[schemeStack.{u, w} B S hS U]).obj).obj x :=
  globalSection.{u, w} U a ((affineRightAdjoint g hg).op.obj x)

/-- The direct image of multiplication by `a` on `𝒪_U` is multiplication by the section `a` of
the presheaf of algebras `x ↦ 𝒪_U(r x)`. -/
theorem affinePushforward_map_globalMul_val (a : schemeGlobalRing U) :
    ((affinePushforward.{u, w, u} g hg).map (globalMul.{u, w} U a)).val =
      PresheafOfModules.algebraPresheafMulBy (pushforwardCommRingHom g hg)
        (pushforwardGlobalSection g hg a)
        (fun f => globalSection_map.{u, w} U a ((affineRightAdjoint g hg).op.map f)) :=
  rfl

/-- **Multiplication by a global function `a` on `g_*𝒪_U` commutes with the multiplication**:
`(κ(a) ⊗ 1) ≫ μ = μ ≫ κ(a)`.  On the presheaf of algebras `x ↦ 𝒪_U(r x)` this is associativity of
the multiplication; sheafification, being monoidal, carries it to the sheafified algebra, and the
multiplication of `g_*𝒪_U` is the sheafified one transported along the counit. -/
theorem affinePushforward_map_globalMul_whiskerRight_mul (a : schemeGlobalRing U) :
    letI := monObjAffinePushforwardStructureSheaf g hg
    (affinePushforward.{u, w, u} g hg).map (globalMul.{u, w} U a) ▷
        affinePushforwardStructureSheaf g hg ≫ MonObj.mul =
      MonObj.mul ≫ (affinePushforward.{u, w, u} g hg).map (globalMul.{u, w} U a) := by
  let := Stacks.SheafOfModules.monoidalCategory (𝒪c[𝒳]).obj
    (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS 𝒳)
  let := Stacks.SheafOfModules.sheafifyMonoidal (𝒪c[𝒳]).obj
    (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS 𝒳)
  let M : MonObj ((Stacks.SheafOfModules.sheafifyFunctor (𝒪c[𝒳]).obj
      (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS 𝒳)).obj
        (affinePushforwardStructureSheaf g hg).val) :=
    Functor.monObjObj (F := Stacks.SheafOfModules.sheafifyFunctor (𝒪c[𝒳]).obj
      (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS 𝒳))
      (X := PresheafOfModules.algebraPresheaf (pushforwardCommRingHom g hg))
  have h₁ := Functor.map_whiskerRight_mul (Stacks.SheafOfModules.sheafifyFunctor (𝒪c[𝒳]).obj
      (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS 𝒳))
    (M := PresheafOfModules.algebraPresheaf (pushforwardCommRingHom g hg))
    (PresheafOfModules.algebraPresheafMulBy (pushforwardCommRingHom g hg)
      (pushforwardGlobalSection g hg a)
      (fun f => globalSection_map.{u, w} U a ((affineRightAdjoint g hg).op.map f)))
    (PresheafOfModules.algebraPresheafMulBy_whiskerRight_mul _ _ _)
  have h₂ := @MonObj.ofIso_whiskerRight_mul _ _ (AlgebraicStacks.modulesMonoidalCategory B S hS 𝒳)
    _ _ M (Stacks.SheafOfModules.sheafifyValIso (𝒪c[𝒳]).obj
      (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS 𝒳)
      (affinePushforwardStructureSheaf g hg)) _ h₁
  have hn := Stacks.SheafOfModules.sheafifyValIso_hom_naturality (𝒪c[𝒳]).obj
    (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS 𝒳)
    ((affinePushforward.{u, w, u} g hg).map (globalMul.{u, w} U a))
  have h₃ := (Iso.eq_inv_comp _).mpr hn
  rw [h₃]
  exact h₂

end AlgebraicGeometry.Stack
