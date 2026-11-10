module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Automorphisms
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Formula
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Comparison.Formula

/-!
# Invariance of periodic determinants

Two consequences of the comparison formula for periodic determinants: equal connecting
isomorphisms give equal periodic determinants, and an isomorphism of exact periodic complexes
preserves the periodic determinant.

## Main results

* `AlgebraicGeometry.periodicDeterminant_eq_of_connecting_eq` is the equal-boundaries case of
  the comparison formula.
* `AlgebraicGeometry.periodicDeterminant_eq_of_linearEquiv` is its isomorphism case: an
  isomorphism of exact periodic complexes preserves the periodic determinant.

## References

* [Stacks Project, Tag 02PV](https://stacks.math.columbia.edu/tag/02PV)
-/

@[expose] public section

noncomputable section

open CategoryTheory

open scoped TensorProduct

open Module.FiniteLength

namespace AlgebraicGeometry

universe u v w

/-- The determinant of the identity automorphism is one. -/
private theorem determinantAutomorphism_refl
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M) :
    determinantAutomorphism (LinearEquiv.refl R M) hM = 1 := by
  classical
  let F := determinantFunctor.{u, v} R
  let O : FiniteLengthModuleIso.{u, v} R := ⟨⟨ModuleCat.of R M, hM⟩⟩
  let f : O ⟶ O := 𝟙 O
  have hfun : F.toFunctor.map f = 𝟙 (F.toFunctor.obj O) := by simp [f]
  have hmap := F.map_iso f
  rw [hfun] at hmap
  have hcat : ModuleCat.ofHom (F.mapLinearEquiv f).toLinearMap = 𝟙 _ := by
    simpa using hmap.symm
  have hlin : (F.mapLinearEquiv f).toLinearMap = LinearMap.id := by
    simpa using congrArg (fun g => g.hom) hcat
  have heq : F.mapLinearEquiv f = LinearEquiv.refl _ _ :=
    LinearEquiv.ext fun x ↦ congrArg (fun g : _ →ₗ[IsLocalRing.ResidueField R] _ => g x) hlin
  change LinearEquiv.det (F.mapLinearEquiv f) = 1
  rw [heq]
  simp

/-- **Stacks Project, Tag 02PV.** Equal connecting isomorphisms give equal periodic
determinants. -/
@[stacks 02PV "equal connecting isomorphisms"]
theorem periodicDeterminant_eq_of_connecting_eq
    {R : Type u} {M : Type v} {M' : Type w}
    [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (φ ψ : M →ₗ[R] M) (φ' ψ' : M' →ₗ[R] M') (α : M →ₗ[R] M')
    (hM : IsFiniteLength R M) (hM' : IsFiniteLength R M')
    (hφψ : Function.Exact φ ψ) (hψφ : Function.Exact ψ φ)
    (hφ'ψ' : Function.Exact φ' ψ') (hψ'φ' : Function.Exact ψ' φ')
    (hαφ : α.comp φ = φ'.comp α) (hαψ : α.comp ψ = ψ'.comp α)
    (hKφ : LinearMap.ker α ≤ LinearMap.ker φ)
    (hKψ : LinearMap.ker α ≤ LinearMap.ker ψ)
    (hQφ : LinearMap.range φ' ≤ LinearMap.range α)
    (hQψ : LinearMap.range ψ' ≤ LinearMap.range α)
    (heq : (connectingEquivs φ ψ φ' ψ' α hφψ hψφ hφ'ψ' hψ'φ'
      hαφ hαψ hKφ hKψ hQφ hQψ).1.1 =
      (connectingEquivs φ ψ φ' ψ' α hφψ hψφ hφ'ψ' hψ'φ'
        hαφ hαψ hKφ hKψ hQφ hQψ).1.2) :
    periodicDeterminant φ ψ hφψ hψφ hM =
      periodicDeterminant φ' ψ' hφ'ψ' hψ'φ' hM' := by
  rw [periodicDeterminant_eq_det_connecting_mul
    φ ψ φ' ψ' α hM hM' hφψ hψφ hφ'ψ' hψ'φ'
    hαφ hαψ hKφ hKψ hQφ hQψ]
  have heid :
      (connectingEquivs φ ψ φ' ψ' α hφψ hψφ hφ'ψ' hψ'φ'
        hαφ hαψ hKφ hKψ hQφ hQψ).1.2.trans
        (connectingEquivs φ ψ φ' ψ' α hφψ hψφ hφ'ψ' hψ'φ'
          hαφ hαψ hKφ hKψ hQφ hQψ).1.1.symm =
        LinearEquiv.refl R (M' ⧸ LinearMap.range α) := by
    apply LinearEquiv.ext
    intro x
    simp [heq]
  rw [heid, determinantAutomorphism_refl]
  simp

/-- Isomorphic exact periodic complexes have the same periodic determinant.

If `e : M ≃ₗ[R] M'` intertwines a pair of differentials `φ, ψ` on `M` with a pair `φ', ψ'` on
`M'`, then the two periodic determinants agree. This is the transport lemma used to compute a
periodic determinant on whichever presentation of the module is convenient. -/
theorem periodicDeterminant_eq_of_linearEquiv
    {R : Type u} {M : Type v} {M' : Type w}
    [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (φ ψ : M →ₗ[R] M) (hφψ : Function.Exact φ ψ) (hψφ : Function.Exact ψ φ)
    (φ' ψ' : M' →ₗ[R] M') (hφ'ψ' : Function.Exact φ' ψ')
    (hψ'φ' : Function.Exact ψ' φ') (e : M ≃ₗ[R] M')
    (hφ : e.toLinearMap.comp φ = φ'.comp e.toLinearMap)
    (hψ : e.toLinearMap.comp ψ = ψ'.comp e.toLinearMap)
    (hM : IsFiniteLength R M) (hM' : IsFiniteLength R M') :
    periodicDeterminant φ ψ hφψ hψφ hM =
      periodicDeterminant φ' ψ' hφ'ψ' hψ'φ' hM' := by
  let α := e.toLinearMap
  have hker : LinearMap.ker α = ⊥ := LinearMap.ker_eq_bot.mpr e.injective
  have hK : ∀ (f : M →ₗ[R] M) (f' : M' →ₗ[R] M'), α.comp f = f'.comp α →
      LinearMap.ker α ≤ LinearMap.ker f := by
    intro f f' h x hx
    have hval : α (f x) = f' (α x) := LinearMap.congr_fun h x
    rw [LinearMap.mem_ker.mp hx, map_zero] at hval
    exact e.injective (by simpa [α] using hval)
  have hQ : ∀ (f : M →ₗ[R] M) (f' : M' →ₗ[R] M'), α.comp f = f'.comp α →
      LinearMap.range f' ≤ LinearMap.range α := by
    rintro f f' h _ ⟨z, rfl⟩
    obtain ⟨x, rfl⟩ := e.surjective z
    exact ⟨f x, LinearMap.congr_fun h x⟩
  have hKφ := hK φ φ' hφ
  have hKψ := hK ψ ψ' hψ
  have hQφ := hQ φ φ' hφ
  have hQψ := hQ ψ ψ' hψ
  have _instKer : Subsingleton (LinearMap.ker α) := by
    rw [hker]
    infer_instance
  let : Subsingleton (LinearMap.ker α) := _instKer
  have hconn :
      (connectingEquivs φ ψ φ' ψ' α hφψ hψφ hφ'ψ' hψ'φ'
        hφ hψ hKφ hKψ hQφ hQψ).1.1 =
      (connectingEquivs φ ψ φ' ψ' α hφψ hψφ hφ'ψ' hψ'φ'
        hφ hψ hKφ hKψ hQφ hQψ).1.2 := by
    apply LinearEquiv.ext
    intro x
    exact Subsingleton.elim _ _
  exact periodicDeterminant_eq_of_connecting_eq
    φ ψ φ' ψ' α hM hM' hφψ hψφ hφ'ψ' hψ'φ' hφ hψ hKφ hKψ hQφ hQψ hconn

end AlgebraicGeometry
