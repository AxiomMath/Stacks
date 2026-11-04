module

public import StacksFrontier.AlgebraicGeometry.Stacks.VersalRing
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalSituationFiniteDimensional
import StacksCore.Tactic.StacksAttribute

/-!
# Existence of versal rings (Stacks 0DQX, first assertion)

In Situation 0DQU — `𝒳` an algebraic stack locally of finite type over a locally Noetherian
scheme `S` — let `x₀ : Spec k ⟶ 𝒳` be a morphism with `k` a field of finite type over `S`. Then a
versal ring to `𝒳` at `x₀` (Stacks 0DQV) exists.

The proof is the source's: `𝓕_{𝒳,k,x₀}` is a deformation category with finite-dimensional
tangent space by Stacks 0DQW
(`AlgebraicGeometry.Stack.isFiniteDimensionalDeformationCategory_of_versalSituation`), so
Schlessinger's theorem (Stacks 06J7, 06IW) produces a versal formal object
(`AlgebraicGeometry.Stack.exists_isVersalRingAt_of_deformationCategory`). The second assertion
of Stacks 0DQX is `AlgebraicGeometry.Stack.versalRing_powerSeries_comparison`.

## Main results

* `AlgebraicGeometry.Stack.exists_isVersalRingAt`: **Stacks 0DQX**, existence.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u w

namespace AlgebraicGeometry.Stack

/-- **Stacks 0DQX**, first assertion. In Situation 0DQU, let `x₀` be an object of `𝒳` over
`Spec k` for a field `k` of finite type over `S`, and let `Spec Λ ⊆ S` be an affine open through
which `Spec k ⟶ S` factors. Then a versal ring to `𝒳` at `x₀` exists, presented over `Λ`. -/
@[stacks 0DQX "existence of a versal ring to 𝒳 at x₀"]
theorem exists_isVersalRingAt
    (D : VersalSituation.{u, w}) {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    ∃ A : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k,
      IsVersalRingAt D iΛ hiΛ x₀ hx₀ hfinite A :=
  exists_isVersalRingAt_of_deformationCategory D iΛ hiΛ x₀ hx₀ hfinite
    fun iΛ' hiΛ' hx₀' hfinite' => by
      obtain ⟨hp, hT, -⟩ :=
        isFiniteDimensionalDeformationCategory_of_versalSituation D iΛ' hiΛ' x₀ hx₀' hfinite'
      exact ⟨hp, hT⟩

end AlgebraicGeometry.Stack
