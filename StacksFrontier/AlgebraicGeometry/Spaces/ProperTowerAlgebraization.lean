module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumOfAdicCompletion
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence

/-!
# Algebraization of compatible morphisms on the thickenings of a proper algebraic space

Let `V` be an affine object of the big fppf site of `S` whose ring of global sections `A` is
Noetherian and `I`-adically complete for an ideal `I ⊆ A`, and let `p : Y ⟶ V` be a proper
morphism of algebraic spaces. The thickenings of `Y` along `I` are the base changes
`Y_n = Y ×_V Spec(A/Iⁿ⁺¹)`. A target `X` has *proper tower algebraization* when every compatible
family of morphisms `g_n : Y_n ⟶ X` is the restriction of a morphism `Y ⟶ X`. This is the
existence part of Stacks 0A4Z (Grothendieck's algebraization of morphisms, for algebraic spaces),
which holds for `X` separated and locally of finite type over `S`.

## Main definitions

* `AlgebraicGeometry.Space.properThickeningTransition`: the transition `Y_n ⟶ Y_{n+1}`.
* `AlgebraicGeometry.Space.HasProperTowerAlgebraization`.

## References

* [Stacks Project, Tag 0A4Z](https://stacks.math.columbia.edu/tag/0A4Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The closed immersions `Spec(A/Iⁿ⁺¹) ⟶ Spec(A/Iⁿ⁺²)` lie over `V`. -/
theorem adicCompletionQuotientObjTransition_comp_hom (V : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) {m n : ℕ} (hmn : m ≤ n) :
    adicCompletionQuotientObjTransition B S hS V I hmn ≫ adicCompletionQuotientObjHom B S hS V I n =
      adicCompletionQuotientObjHom B S hS V I m :=
  (BigFppfOver.toScheme B S hS).map_injective
    ((Functor.map_comp _ _ _).trans (specMap_factorPow_comp_specMap_mk_assoc B S hS V I hmn _))

/-- The transition `Y ×_V Spec(A/Iⁿ⁺¹) ⟶ Y ×_V Spec(A/Iⁿ⁺²)` between the thickenings of
`p : Y ⟶ V` along `I`. -/
def properThickeningTransition {V : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : Y ⟶ yoneda.obj V) (n : ℕ) :
    pullback p (yoneda.map (adicCompletionQuotientObjHom B S hS V I (n + 1))) ⟶
      pullback p (yoneda.map (adicCompletionQuotientObjHom B S hS V I (n + 1 + 1))) :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ yoneda.map (adicCompletionQuotientObjTransition B S hS V I
      (Nat.le_add_right (n + 1) 1)))
    (by
      rw [pullback.condition, Category.assoc, ← Functor.map_comp,
        adicCompletionQuotientObjTransition_comp_hom])

/-- **Algebraization of compatible morphisms on the thickenings of a proper algebraic space**
(the existence part of Stacks 0A4Z). For every affine `V` with Noetherian `I`-adically complete
ring of global sections `A`, every proper `p : Y ⟶ V` of algebraic spaces and every family of
morphisms `g_n : Y ×_V Spec(A/Iⁿ⁺¹) ⟶ X` compatible with the transitions, there is `y : Y ⟶ X`
restricting to every `g_n`. -/
def HasProperTowerAlgebraization (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∀ (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)),
    IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) →
    IsAdicComplete I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) →
    ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS Y →
    ∀ (p : Y ⟶ yoneda.obj V), IsProper B S hS p →
    ∀ (g : ∀ n : ℕ, pullback p (yoneda.map (adicCompletionQuotientObjHom B S hS V I (n + 1))) ⟶ X),
      (∀ n, properThickeningTransition I p n ≫ g (n + 1) = g n) →
      ∃ y : Y ⟶ X, ∀ n, pullback.fst _ _ ≫ y = g n

end AlgebraicGeometry.Space

end
