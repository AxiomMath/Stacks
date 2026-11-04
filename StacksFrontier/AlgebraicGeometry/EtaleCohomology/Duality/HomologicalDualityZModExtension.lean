module

public import StacksFrontier.CategoryTheory.Triangulated.HomologicalDualityPairing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LocallyConstantDevissage

/-!
# The extension property for `ℤ/ℓ`-valued traces

The five lemma for duality pairings (`Stacks.HomologicalDuality.isPerfect_obj₂`) asks that the
target `A` of the trace have the extension property for subgroups of the groups `Hom(M, D[j])`.
For `A = ℤ/ℓ` with `ℓ` prime this holds as soon as `ℓ` kills the dualizing object `D`: then every
`Hom(M, D[j])` is a vector space over the field `ℤ/ℓ`
(`Stacks.HomologicalDuality.exists_extend_zmod_of_nsmul_id_eq_zero`). This is the case for
sheaves of `ℤ/ℓ`-modules on the small étale site
(`Stacks.EtaleCohomology.nsmul_id_etaleModules_zmod`), in the fibration step of Poincaré
duality in the proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.HomologicalDuality.exists_extend_zmod_of_nsmul_id_eq_zero`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v u

namespace Stacks.HomologicalDuality

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] (ℓ : ℕ) [Fact ℓ.Prime] {D : C}

omit [Fact ℓ.Prime] in
/-- If `ℓ` kills `D`, it kills every morphism into a shift of `D`. -/
theorem nsmul_eq_zero_of_nsmul_id_eq_zero (h : ℓ • 𝟙 D = 0) {M : C} {j : ℤ} (y : M ⟶ D⟦j⟧) :
    ℓ • y = 0 := by
  have h' : ℓ • 𝟙 (D⟦j⟧) = 0 := by
    rw [← (shiftFunctor C j).map_id, ← Functor.map_nsmul, h, Functor.map_zero]
  rw [← Category.comp_id y, ← Preadditive.comp_nsmul, h', Limits.comp_zero]

/-- **`ℤ/ℓ` has the extension property for subgroups of `Hom(M, D[j])` when `ℓ` kills `D`**: these
groups are vector spaces over the field `ℤ/ℓ`. -/
theorem exists_extend_zmod_of_nsmul_id_eq_zero (h : ℓ • 𝟙 D = 0) (M : C) (j : ℤ)
    (Hs : AddSubgroup (M ⟶ D⟦j⟧)) (φ : Hs →+ ZMod ℓ) :
    ∃ ψ : (M ⟶ D⟦j⟧) →+ ZMod ℓ, ∀ x : Hs, ψ x = φ x :=
  let : Module (ZMod ℓ) (M ⟶ D⟦j⟧) :=
    AddCommGroup.zmodModule (fun y => nsmul_eq_zero_of_nsmul_id_eq_zero ℓ h y)
  Stacks.EtaleCohomology.exists_extend_zmod Hs φ

end Stacks.HomologicalDuality

end
