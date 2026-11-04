module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Torsion exponents in distinguished triangles

In a pretriangulated category, say that an object `X` is *killed by `n : ℤ`* when `n • 𝟙 X = 0`.

* If `A ⟶ B ⟶ C ⟶ A⟦1⟧` is distinguished and `A`, `C` are killed by `a`, `b`, then `B` is killed by
  `a * b` (`Stacks.Triangulated.mul_zsmul_id_eq_zero_of_distTriang`).
* If `X₁ ⟶ X ⟶ X₂ ⟶` and `Y₁ ⟶ Y ⟶ Y₂ ⟶` are distinguished, `X₁` is killed by `a`, `Y₂` by `b`, and
  there is no nonzero morphism `X₂ ⟶ Y₁`, then every morphism `X ⟶ Y` is killed by `a * b`
  (`Stacks.Triangulated.mul_zsmul_eq_zero_of_distTriang`).

These are the estimates of the finite-level form of Laumon's argument that the Fourier transform
of an irreducible lisse sheaf is irreducible: at level `n` the identities of the rational argument
hold up to `ℓ^c`-torsion with `c` independent of `n`, and the second statement, applied to the
truncation triangles, bounds the torsion exponent of a morphism between complexes concentrated, up
to bounded torsion, in disjoint ranges of degrees.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace Stacks.Triangulated

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **The middle vertex of a triangle is killed by the product of the exponents of the outer
ones**: `b • 𝟙_B` dies in `C`, so it factors through `A`, where `a` kills it. -/
theorem mul_zsmul_id_eq_zero_of_distTriang (T : Triangle C) (hT : T ∈ distTriang C) {a b : ℤ}
    (ha : a • 𝟙 T.obj₁ = 0) (hb : b • 𝟙 T.obj₃ = 0) : (a * b) • 𝟙 T.obj₂ = 0 := by
  have h1 : (b • 𝟙 T.obj₂) ≫ T.mor₂ = 0 := by
    rw [show (b • 𝟙 T.obj₂) ≫ T.mor₂ = T.mor₂ ≫ (b • 𝟙 T.obj₃) by simp, hb, comp_zero]
  obtain ⟨h, hh⟩ := Triangle.coyoneda_exact₂ T hT _ h1
  calc (a * b) • 𝟙 T.obj₂ = a • (b • 𝟙 T.obj₂) := mul_smul a b _
    _ = a • (h ≫ T.mor₁) := by rw [hh]
    _ = h ≫ (a • 𝟙 T.obj₁) ≫ T.mor₁ := by simp
    _ = 0 := by rw [ha, zero_comp, comp_zero]

/-- **A morphism between objects whose bad parts are disjoint is killed by the product of the
exponents.** For distinguished `X₁ ⟶ X ⟶ X₂ ⟶` and `Y₁ ⟶ Y ⟶ Y₂ ⟶` with `a` killing `X₁`, `b`
killing `Y₂` and no nonzero morphism `X₂ ⟶ Y₁`, every `φ : X ⟶ Y` satisfies `(a * b) • φ = 0`:
`a • φ` factors through `X₂`, and `b` times that factorization factors through `Y₁`. -/
theorem mul_zsmul_eq_zero_of_distTriang (T : Triangle C) (hT : T ∈ distTriang C)
    (S : Triangle C) (hS : S ∈ distTriang C) {a b : ℤ} (ha : a • 𝟙 T.obj₁ = 0)
    (hb : b • 𝟙 S.obj₃ = 0) (h0 : ∀ g : T.obj₃ ⟶ S.obj₁, g = 0) (φ : T.obj₂ ⟶ S.obj₂) :
    (a * b) • φ = 0 := by
  have h1 : T.mor₁ ≫ (a • φ) = 0 := by
    rw [show T.mor₁ ≫ (a • φ) = (a • 𝟙 T.obj₁) ≫ T.mor₁ ≫ φ by simp, ha, zero_comp]
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ T hT _ h1
  have h2 : (b • g) ≫ S.mor₂ = 0 := by
    rw [show (b • g) ≫ S.mor₂ = g ≫ S.mor₂ ≫ (b • 𝟙 S.obj₃) by simp, hb, comp_zero, comp_zero]
  obtain ⟨g', hg'⟩ := Triangle.coyoneda_exact₂ S hS _ h2
  calc (a * b) • φ = b • (a • φ) := by rw [mul_comm, mul_smul]
    _ = b • (T.mor₂ ≫ g) := by rw [hg]
    _ = T.mor₂ ≫ (b • g) := by simp
    _ = 0 := by rw [hg', h0 g', zero_comp, comp_zero]

end Stacks.Triangulated
