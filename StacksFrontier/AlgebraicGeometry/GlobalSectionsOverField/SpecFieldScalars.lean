module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.TransformedDiagonal.SituationBoxPairing

/-!
# Endomorphisms of the structure sheaf of the spectrum of a field are scalars

Let `k` be a field and `S = Spec k`, viewed as a `k`-scheme by the identity. Every endomorphism of
`𝒪_S` is multiplication by an element of `k`, for the `k`-linear structure
`AlgebraicGeometry.modulesLinear`, and the same holds for `𝒪_S[0]` in the derived category.

## Main definitions

* `AlgebraicGeometry.specFieldOver`: `Spec k` as a scheme over `Spec k`.

## Main results

* `AlgebraicGeometry.exists_eq_smul_id_specFieldOver_unit`: endomorphisms of `𝒪_{Spec k}` are
  scalars.
* `AlgebraicGeometry.exists_eq_smul_id_specFieldOver_single`: the same for `𝒪_{Spec k}[0]`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe u

namespace AlgebraicGeometry

open AlgebraicGeometry.VectorBundleKZero in
attribute [local instance] onSpaceModulesMonoidal

variable (k : Type u) [Field k]

/-- `Spec k` as a scheme over `Spec k`, by the identity. -/
abbrev specFieldOver : Over (Spec (.of k)) := Over.mk (𝟙 (Spec (.of k)))

/-- The ring map `k ⟶ Γ(Spec k, ⊤)` through which `k` acts on global sections is surjective. -/
theorem surjective_specFieldOver_globalScalar :
    Function.Surjective ((Scheme.ΓSpecIso (.of k)).inv ≫
      (specFieldOver k).hom.appLE ⊤ ⊤ (by simp)).hom := by
  have : (specFieldOver k).hom.appLE ⊤ ⊤ (by simp) = 𝟙 _ := by
    simp only [Scheme.Hom.appLE, Over.mk_hom, Scheme.Hom.id_app]
    exact (Spec (CommRingCat.of k)).presheaf.map_id _
  rw [this, Category.comp_id]
  exact ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv)).2

/-- **Endomorphisms of `𝒪_{Spec k}` are scalars.** -/
theorem exists_eq_smul_id_specFieldOver_unit
    (ψ : 𝟙_ (specFieldOver k).left.Modules ⟶ 𝟙_ (specFieldOver k).left.Modules) :
    letI := modulesLinear k (specFieldOver k)
    ∃ r : k, ψ = r • 𝟙 _ := by
  let := modulesLinear k (specFieldOver k)
  let e := unitHomLinearEquiv k (specFieldOver k) (𝟙_ (specFieldOver k).left.Modules)
  obtain ⟨r, hr⟩ := surjective_specFieldOver_globalScalar k (e ψ)
  refine ⟨r, e.injective ?_⟩
  rw [map_smul, ← hr]
  show _ = ((Scheme.ΓSpecIso (.of k)).inv ≫
    (specFieldOver k).hom.appLE ⊤ ⊤ (by simp)).hom r * (1 : Γ((specFieldOver k).left, ⊤))
  exact (mul_one _).symm

attribute [local instance 100000] HasDerivedCategory.standard

/-- **Endomorphisms of `𝒪_{Spec k}[0]` in the derived category are scalars.** -/
theorem exists_eq_smul_id_specFieldOver_single
    (φ : (DerivedCategory.singleFunctor (specFieldOver k).left.Modules 0).obj
        (𝟙_ (specFieldOver k).left.Modules) ⟶
      (DerivedCategory.singleFunctor (specFieldOver k).left.Modules 0).obj
        (𝟙_ (specFieldOver k).left.Modules)) :
    letI := modulesLinear k (specFieldOver k)
    ∃ r : k, φ = r • 𝟙 _ := by
  let := modulesLinear k (specFieldOver k)
  obtain ⟨ψ, rfl⟩ :=
    (DerivedCategory.singleFunctor (specFieldOver k).left.Modules 0).map_surjective φ
  obtain ⟨r, rfl⟩ := exists_eq_smul_id_specFieldOver_unit k ψ
  exact ⟨r, by rw [Functor.map_smul, CategoryTheory.Functor.map_id]⟩

end AlgebraicGeometry
