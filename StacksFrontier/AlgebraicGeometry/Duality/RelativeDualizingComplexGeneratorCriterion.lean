module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexDiagonalRigidity
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexChartConverse
public import StacksFrontier.RingTheory.Dualizing.RelativeGeneratorUniversal

/-!
# The diagonal condition through generators

Let `W` be a diagonal open of `f : X ⟶ S` with diagonal `Δ : X ⟶ W`, `K` an object of `D(𝒪_X)`
and `ξ : Δ_*𝒪_X ⟶ L pr₁^*K|_W`. Write `Φ(ζ)` for the map
`Δ_*𝒪_X ⟶ R SheafHom(Δ_*𝒪_X, L pr₁^*K|_W)` defined by `ζ` (Stacks 0E2T).

* If `Φ(ξ)` is an isomorphism, every `ζ : Δ_*𝒪_X ⟶ L pr₁^*K|_W` factors as `x ≫ ξ`: writing
  `Φ(ζ) = (a • 𝟙) ≫ Φ(ξ)` (every endomorphism of `Δ_*𝒪_X` is a scalar), the `Γ(X, 𝒪_X)`-linear left
  inverse of `Φ` gives `ζ = a • ξ`.
* Conversely, if `R ℰom(𝒪_X, L pr₁^*K|_W) ≅ 𝒪_X[0]` and every `ζ` factors through `ξ`, then `Φ(ξ)`
  is an isomorphism: `Hom(Δ_*𝒪_X, L pr₁^*K|_W)` is free of rank one over `End(Δ_*𝒪_X)`, so a
  generator is a basis, and rigidity applies.

## Main results

* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.isPostcompGenerator_of_isIso_diagonalAction`
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.isIso_diagonalAction_of_isPostcompGenerator`

## References

* [Stacks Project, Definition 48.28.1 (Tag 0E2T)](https://stacks.math.columbia.edu/tag/0E2T)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite StrictlyPerfect

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace AlgebraicGeometry.Scheme.Hom.DiagonalOpen

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

variable {X S : Scheme.{u}} {f : X ⟶ S} (D : DiagonalOpen f)

/-- **A map defining an isomorphism is a generator.** If `ξ` defines an isomorphism
`Δ_*𝒪_X ⟶ R SheafHom(Δ_*𝒪_X, L pr₁^*K|_W)`, every `ζ : Δ_*𝒪_X ⟶ L pr₁^*K|_W` is `x ≫ ξ` for some
endomorphism `x` of `Δ_*𝒪_X`. -/
theorem isPostcompGenerator_of_isIso_diagonalAction
    (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (ξ : D.diagonalObject ⟶ D.derivedPullbackProj K) (h : IsIso (D.diagonalAction K ξ)) :
    Dualizing.IsPostcompGenerator ξ := by
  let := D.proj.linearStructureSheafModules
  intro ζ
  obtain ⟨a, ha, -⟩ := D.existsUnique_eq_smul_of_isIso_diagonalAction h ζ
  refine ⟨a • 𝟙 _, ?_⟩
  show (a • 𝟙 D.diagonalObject) ≫ ξ = ζ
  rw [Linear.smul_comp, Category.id_comp]
  exact ha.symm

/-- **A generator defines an isomorphism**, as soon as `R ℰom(𝒪_X, L pr₁^*K|_W) ≅ 𝒪_X[0]`. -/
theorem isIso_diagonalAction_of_isPostcompGenerator
    (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (h : Nonempty (D.diagonalExactSupport K ≅ structureSingle X))
    (ξ : D.diagonalObject ⟶ D.derivedPullbackProj K) (hξ : Dualizing.IsPostcompGenerator ξ) :
    IsIso (D.diagonalAction K ξ) := by
  let := D.proj.linearStructureSheafModules
  obtain ⟨τ⟩ := D.nonempty_diagonalObject_iso_derivedSheafHom K h
  obtain ⟨ζ₁, hgen₁, huniq₁⟩ := D.exists_diagonalObject_generator K h
  refine D.isIso_diagonalAction_of_iso_of_generator K τ ξ (fun ζ => ?_) ?_
  · obtain ⟨x, hx⟩ := hξ ζ
    exact ⟨x, hx.symm⟩
  · intro u v huv
    obtain ⟨x, hx⟩ := hξ ζ₁
    obtain ⟨y, hy⟩ := hgen₁ ξ
    change x ≫ ξ = ζ₁ at hx
    have hxy : x ≫ y = 𝟙 _ :=
      huniq₁ _ _ (by rw [Category.assoc, ← hy, Category.id_comp, hx])
    have hyx : y ≫ x = 𝟙 _ := by
      obtain ⟨a, rfl⟩ := D.exists_eq_smul_id_diagonalObject x
      obtain ⟨b, rfl⟩ := D.exists_eq_smul_id_diagonalObject y
      refine Eq.trans ?_ hxy
      simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul, mul_comm]
    have h₂ : (u ≫ y) ≫ ζ₁ = (v ≫ y) ≫ ζ₁ := by
      simpa only [Category.assoc, ← hy] using huv
    calc u = (u ≫ y) ≫ x := by rw [Category.assoc, hyx, Category.comp_id]
      _ = (v ≫ y) ≫ x := by rw [huniq₁ _ _ h₂]
      _ = v := by rw [Category.assoc, hyx, Category.comp_id]

end AlgebraicGeometry.Scheme.Hom.DiagonalOpen

end
