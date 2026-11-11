module

public import StacksFrontier.AlgebraicGeometry.Surfaces.NegativeCurveAlgebraization
public import StacksFrontier.AlgebraicGeometry.Surfaces.NegativeCurveAlgebraizationLocalRingsStalk

/-!
# Global functions inject into the ring of formal functions

Let `X` be an integral locally Noetherian scheme and `D` a quasi-coherent ideal sheaf on `X`
cutting out a nonempty closed subscheme `C`, with thickenings `Cₙ = V(Dⁿ⁺¹)` and ring of formal
functions `A = lim Γ(Cₙ, 𝒪)`. The restriction map `Γ(X, 𝒪) ⟶ A` is injective: a global
function restricting to zero on every `Cₙ` has germ at a point `x` of `C` in
`⋂ₙ 𝔪ₓⁿ⁺¹ = 0` (Krull's intersection theorem in the Noetherian local ring `𝒪_{X, x}`), hence
vanishes since `X` is integral.

## Main results

* `Scheme.IdealSheafData.germ_mem_maximalIdeal_pow_of_globalToFormalNeighborhood_eq_zero`:
  the germ of such a function lies in every power of the maximal ideal.
* `AlgebraicGeometry.Scheme.IdealSheafData.injective_globalToFormalNeighborhood`: the
  restriction `Γ(X, 𝒪) ⟶ A` is injective.
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (D : X.IdealSheafData)

/-- A global function restricting to zero on every thickening `Cₙ = V(Dⁿ⁺¹)` has germ at any
point of `C = V(D)` in every power `𝔪ⁿ⁺¹` of the maximal ideal of the local ring. -/
theorem germ_mem_maximalIdeal_pow_of_globalToFormalNeighborhood_eq_zero {a : Γ(X, ⊤)}
    (ha : globalToFormalNeighborhood D a = 0) {x : X} (hx : x ∈ (D.support : Set X)) (n : ℕ) :
    X.presheaf.germ ⊤ x (show x ∈ (⊤ : X.Opens) from trivial) a ∈
      maximalIdeal (X.presheaf.stalk x) ^ (n + 1) := by
  obtain ⟨w, rfl⟩ : x ∈ Set.range (D ^ (n + 1)).subschemeι := by
    rw [range_subschemeι, support_pow_succ]
    exact hx
  apply ker_stalkMap_subschemeι_pow_le_maximalIdeal_pow D n w
  have h0 : (D ^ (n + 1)).subschemeι.appTop a = 0 := by
    rw [← formalNeighborhoodProjection_globalToFormalNeighborhood, ha, map_zero]
  rw [RingHom.mem_ker, Scheme.Hom.germ_stalkMap_apply,
    show (D ^ (n + 1)).subschemeι.app ⊤ a = 0 from h0, map_zero]

/-- **Global functions inject into the ring of formal functions.** On an integral locally
Noetherian scheme `X`, for an ideal sheaf `D` with nonempty support `C`, the restriction
`Γ(X, 𝒪) ⟶ lim Γ(Cₙ, 𝒪)` is injective: the germ at a point of `C` of a function in the kernel
lies in `⋂ₙ 𝔪ⁿ⁺¹ = 0` by Krull's intersection theorem, and germs are injective on an integral
scheme. -/
theorem injective_globalToFormalNeighborhood [IsIntegral X] [IsLocallyNoetherian X]
    (hD : (D.support : Set X).Nonempty) :
    Function.Injective (globalToFormalNeighborhood D) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨x, hx⟩ := hD
  have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal (X.presheaf.stalk x))
    (maximalIdeal.isMaximal _).ne_top
  have hmem : X.presheaf.germ ⊤ x (show x ∈ (⊤ : X.Opens) from trivial) a ∈
      ⨅ i : ℕ, maximalIdeal (X.presheaf.stalk x) ^ i :=
    Ideal.mem_iInf.2 fun i => Ideal.pow_le_pow_right (Nat.le_succ i)
      (germ_mem_maximalIdeal_pow_of_globalToFormalNeighborhood_eq_zero D ha hx i)
  rw [hbot, Ideal.mem_bot] at hmem
  exact germ_injective_of_isIntegral X x (show x ∈ (⊤ : X.Opens) from trivial)
    (hmem.trans (map_zero _).symm)

end AlgebraicGeometry.Scheme.IdealSheafData

end
