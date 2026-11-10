module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.FiniteDimensionalExtOne
import StacksCore.Tactic.EgaSgaAttribute

/-! # `Ext¹` as a quotient of the maps out of the relation object

Let `𝒜` be an abelian category which is linear over a field `k`, and let

`0 ⟶ K ⟶ P ⟶ M ⟶ 0`

be a short exact sequence in `𝒜` with `P` projective. Composition with the class of the
sequence sends a map `K ⟶ Y` to a class in `Ext¹(M, Y)`; it is surjective because `Ext¹(P, Y)`
vanishes, and its kernel is exactly the maps `K ⟶ Y` which extend to `P`. So

`Ext¹(M, Y) ≅ (K ⟶ Y) / {restrictions of maps P ⟶ Y}`

as `k`-modules.

## Main results

* `CategoryTheory.Abelian.Ext.ker_extClassComp`: the kernel of composition with the class of
  the sequence is the image of restriction along `K ⟶ P`.
* `CategoryTheory.Abelian.Ext.extOneQuotientEquiv`: hence `Ext¹(M, Y)` is the quotient of
  `K ⟶ Y` by the restrictions of the maps `P ⟶ Y`.
-/

@[expose] public noncomputable section

universe t w v u

namespace CategoryTheory.Abelian.Ext

variable {k : Type t} [Field k] {C : Type u} [Category.{v} C] [Abelian C] [Linear k C]
  [HasExt.{w} C] {S : ShortComplex C} (hS : S.ShortExact) (Y : C)

/-- Restriction along the monomorphism of a short exact sequence, as a `k`-linear map from the
maps out of its middle object to the maps out of its left-hand object. Its image is the set of
maps `S.X₁ ⟶ Y` which extend over `S.X₂`. -/
abbrev restrictHom : (S.X₂ ⟶ Y) →ₗ[k] (S.X₁ ⟶ Y) := Linear.leftComp k Y S.f

/-- **The kernel of composition with the class of a short exact sequence.** A map `S.X₁ ⟶ Y` has
vanishing class in `Ext¹(S.X₃, Y)` exactly when it extends over `S.X₂`. -/
@[sga "4 V 2.1.1" "partial"]
theorem ker_extClassComp :
    LinearMap.ker (extClassComp (k := k) hS Y) =
      LinearMap.range (restrictHom (k := k) (S := S) Y) := by
  apply le_antisymm
  · intro f hf
    rw [LinearMap.mem_ker, extClassComp_apply] at hf
    obtain ⟨x₂, hx₂⟩ :=
      contravariant_sequence_exact₁ hS Y (mk₀ f) (n₀ := 0) (n₁ := 1) (add_zero 1) hf
    refine ⟨linearEquiv₀ (R := k) x₂, ?_⟩
    have : mk₀ (S.f ≫ linearEquiv₀ (R := k) x₂) = mk₀ f := by
      rw [← mk₀_comp_mk₀, mk₀_linearEquiv₀_apply]
      exact hx₂
    exact Function.Bijective.injective (mk₀_bijective S.X₁ Y) this
  · rintro f ⟨ψ, rfl⟩
    rw [LinearMap.mem_ker, extClassComp_apply]
    change hS.extClass.comp (mk₀ (S.f ≫ ψ)) (add_zero 1) = 0
    rw [← mk₀_comp_mk₀]
    exact hS.extClass_comp_assoc (mk₀ ψ)

/-- **`Ext¹` of a projective presentation is a quotient of the maps out of the relation
object.** If `0 ⟶ K ⟶ P ⟶ M ⟶ 0` is short exact with `P` projective, then `Ext¹(M, Y)` is the
quotient of the `k`-module `K ⟶ Y` by the submodule of maps which extend over `P`. -/
def extOneQuotientEquiv [Projective S.X₂] :
    ((S.X₁ ⟶ Y) ⧸ LinearMap.range (restrictHom (k := k) (S := S) Y)) ≃ₗ[k] Ext.{w} S.X₃ Y 1 :=
  (Submodule.quotEquivOfEq _ _ (ker_extClassComp (k := k) hS Y).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (surjective_extClassComp (k := k) hS Y))

end CategoryTheory.Abelian.Ext

end
