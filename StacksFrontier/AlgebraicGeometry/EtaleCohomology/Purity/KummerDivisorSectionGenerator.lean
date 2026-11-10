module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.KummerSectionTransportOpens
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.RelativeCurveFirstBaseChangeAb

/-!
# The fundamental class of an étale divisor of a smooth relative curve generates `R¹ j_* μ_N`

Let `W` be smooth over a field `k`, `g : U ⟶ W` smooth of relative dimension one, `i : Z ⟶ U` a
closed immersion with `Z ⟶ W` étale, `j : U₀ ⟶ U` the open complement and `N` invertible in `k`.
The fundamental class `s` of `Z` in `R¹ j_* μ_N`
(`Stacks.EtaleCohomology.Purity.kummerDivisorSection`) generates the stalk of `R¹ j_* μ_N`
freely over `ℤ/N` at every geometric point over `Z`: `σ_s : ℤ/N ⟶ R¹ j_* μ_N` is invertible on
these stalks (`isIsoStalksOver_torsionSectionSheafHom_kummerDivisorSection_standard`).

Near a point of `Z`, a chart `V ⊆ U` with a smooth `φ : V ⟶ 𝔸¹_k` cuts out `Z ∩ V` by
`t = φ^* x` (`Stacks.EtaleCohomology.Purity.exists_smooth_affineLine_chart`). On `V` the class
`s` is the Kummer class of `t` (`Stacks.EtaleCohomology.Purity.kummerDivisorSection_restrict`),
and the degree-one base change map along the open immersion `V ⊆ U` carries it to the Kummer
class of `t` on `V`
(`Stacks.EtaleCohomology.Purity.map_homEquiv_kummerBaseChangeMap_localKummerClass`), which
generates by the Kummer generator of a smooth chart
(`Stacks.EtaleCohomology.Purity.isIsoStalksOver_torsionSectionSheafHom_of_isPullback_affineLine`).
This file works in the standard model of the derived categories, in which the base change maps
are defined.

## Main results

* `Stacks.EtaleCohomology.Purity.nsmul_kummerDivisorSection`: `N` kills the fundamental class.
* `isIsoStalksOver_torsionSectionSheafHom_kummerDivisorSection_standard`: `σ_s` is invertible
  on the stalks at geometric points over `Z`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

universe w u

namespace Stacks.EtaleCohomology.Purity

open Stacks.Kummer

section Torsion

variable {U₀ U : Scheme.{u}} (j : U₀ ⟶ U) {N : ℕ}

/-- `N` kills the sections of `R¹ j_* μ_N`. -/
theorem nsmul_kummerTarget_section {T : U.Etale}
    (x : ToType ((kummerTarget j N).obj.obj (op T))) : N • x = 0 := by
  have hm : ((smallEtalePushforwardAb j).rightDerived 1).map
        (N • 𝟙 (rootsOfUnitySheaf.{u, 0} U₀ N)) =
      N • ((smallEtalePushforwardAb j).rightDerived 1).map (𝟙 (rootsOfUnitySheaf.{u, 0} U₀ N)) :=
    Functor.map_nsmul _
  rw [CategoryTheory.Functor.map_id, nsmul_id_rootsOfUnitySheaf_univ, Functor.map_zero] at hm
  have h := sheaf_nsmul_hom_app_apply.{u, 0} U (𝟙 (kummerTarget j N)) N (op T) x
  have h1 : N • 𝟙 (kummerTarget j N) = 0 := hm.symm
  rw [h1] at h
  exact h.symm.trans rfl

variable [HasDerivedCategory.{w} (Sheaf (smallEtaleTopology U₀) Ab.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallEtaleTopology U) Ab.{u + 1})]

/-- `N` kills the fundamental class. -/
theorem nsmul_kummerDivisorSection (hN0 : N ≠ 0) (hN : IsUnit ((N : ℕ) : Γ(U₀, ⊤)))
    (hNU : IsUnit ((N : ℕ) : Γ(U, ⊤))) {Z : Scheme.{u}} (i : Z ⟶ U) [IsClosedImmersion i]
    (hj : Set.range j.base ⊆ (Set.range i.base)ᶜ)
    (hcov : ∀ x : U, ∃ (V : U.Opens) (t : Γ(U, V)), x ∈ V ∧ IsLocalEquation i V t) :
    N • kummerDivisorSection j hN0 hN hNU i hj hcov = 0 :=
  nsmul_kummerTarget_section j _

end Torsion

/-- The function on an open `V`, read on the open subscheme `V` and back. -/
theorem appLE_ι_topIso_hom {X : Scheme.{u}} (V : X.Opens) (hO : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V)
    (r : Γ(V.toScheme, ⊤)) : V.ι.appLE V ⊤ hO (V.topIso.hom r) = r := by
  rw [← CommRingCat.comp_apply]
  have e : V.topIso.hom ≫ V.ι.appLE V ⊤ hO = 𝟙 _ := by
    rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_hom]
    exact (X.presheaf.map_comp _ _).symm.trans ((congrArg X.presheaf.map
      (Quiver.Hom.unop_inj (Subsingleton.elim _ _))).trans (X.presheaf.map_id _))
  rw [e]
  rfl

end Stacks.EtaleCohomology.Purity

end
