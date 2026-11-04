module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.InducedHomInnerConjugate
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TorsorCharacter

/-!
# Induced homomorphisms to two base points differ by a change of base point

Two homomorphisms `Φ : π₁(Y, ȳ) → π₁(X, x̄)` and `Φ' : π₁(Y, ȳ) → π₁(X, x̄')` induced by the same
functor `H : FÉt_X ⥤ FÉt_Y` (`AlgebraicGeometry.IsEtaleFundamentalGroupHomInducedBy`) differ by
the transport along an isomorphism `F_x̄ ≅ F_x̄'` of fibre functors
(`AlgebraicGeometry.IsEtaleFundamentalGroupHomInducedBy.exists_mulEquiv`). Since the character of a
torsor cover is invariant under such transport, the characters of a torsor cover of `X` composed
with `Φ` and with `Φ'` agree
(`AlgebraicGeometry.IsEtaleFundamentalGroupHomInducedBy.character_eq_of_eq`).

## Main results

* `AlgebraicGeometry.IsEtaleFundamentalGroupHomInducedBy.exists_mulEquiv`.
* `AlgebraicGeometry.IsEtaleFundamentalGroupHomInducedBy.character_eq`,
  `AlgebraicGeometry.IsEtaleFundamentalGroupHomInducedBy.character_eq_of_eq`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IsEtaleFundamentalGroupHomInducedBy

variable {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y] {y : GeometricPoint Y}
  {x x' : GeometricPoint X}

/-- **Homomorphisms to two base points induced by the same functor differ by a change of base
point**: `Φ' = s ∘ Φ ∘ s⁻¹`-transport for `s = T' ∘ T⁻¹ : F_x̄ ≅ F_x̄'`. -/
public theorem exists_mulEquiv {H : FiniteEtaleOver X ⥤ FiniteEtaleOver Y}
    {Φ : EtaleFundamentalGroup Y y →* EtaleFundamentalGroup X x}
    {Φ' : EtaleFundamentalGroup Y y →* EtaleFundamentalGroup X x'}
    (h : IsEtaleFundamentalGroupHomInducedBy H Φ) (h' : IsEtaleFundamentalGroupHomInducedBy H Φ') :
    ∃ s : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor x',
      ∀ γ, Φ' γ = etaleFundamentalGroupMulEquiv s (Φ γ) := by
  obtain ⟨T, hT⟩ := h
  obtain ⟨T', hT'⟩ := h'
  refine ⟨T.symm ≪≫ T', fun γ => Aut.ext ?_⟩
  ext V w
  have h1 := Stacks.FundamentalGroup.conjAut_app_apply_inv (T.symm ≪≫ T') (Φ γ) V w
  refine (hT' γ V w).trans (Eq.trans ?_ h1.symm)
  show _ = T'.hom.app V (T.inv.app V (((Φ γ).app V).hom (T.hom.app V (T'.inv.app V w))))
  rw [hT, Iso.hom_inv_id_app_apply, Iso.hom_inv_id_app_apply]

/-- **The character of a torsor cover composed with homomorphisms induced by the same functor
does not depend on the base point.** -/
public theorem character_eq {K : Type*} [AddCommGroup K] (T : TorsorCover X K)
    {H : FiniteEtaleOver X ⥤ FiniteEtaleOver Y}
    {Φ : EtaleFundamentalGroup Y y →* EtaleFundamentalGroup X x}
    {Φ' : EtaleFundamentalGroup Y y →* EtaleFundamentalGroup X x'}
    (h : IsEtaleFundamentalGroupHomInducedBy H Φ) (h' : IsEtaleFundamentalGroupHomInducedBy H Φ')
    (p : (finiteEtaleFiberFunctor x).obj T.cover) (p' : (finiteEtaleFiberFunctor x').obj T.cover)
    (γ : EtaleFundamentalGroup Y y) :
    T.character x' p' (Φ' γ) = T.character x p (Φ γ) := by
  obtain ⟨s, hs⟩ := h.exists_mulEquiv h'
  rw [hs]
  exact T.character_etaleFundamentalGroupMulEquiv s p p' (Φ γ)

/-- **The character of a torsor cover composed with homomorphisms induced by base changes along
equal morphisms does not depend on the base point.** -/
public theorem character_eq_of_eq {K : Type*} [AddCommGroup K] (T : TorsorCover X K)
    {f f' : Y ⟶ X} {Φ : EtaleFundamentalGroup Y y →* EtaleFundamentalGroup X x}
    {Φ' : EtaleFundamentalGroup Y y →* EtaleFundamentalGroup X x'}
    (h : IsEtaleFundamentalGroupHomInducedBy (finiteEtaleBaseChange f) Φ)
    (h' : IsEtaleFundamentalGroupHomInducedBy (finiteEtaleBaseChange f') Φ') (hf : f = f')
    (p : (finiteEtaleFiberFunctor x).obj T.cover) (p' : (finiteEtaleFiberFunctor x').obj T.cover)
    (γ : EtaleFundamentalGroup Y y) :
    T.character x' p' (Φ' γ) = T.character x p (Φ γ) := by
  subst hf
  exact character_eq T h h' p p' γ

end AlgebraicGeometry.IsEtaleFundamentalGroupHomInducedBy

end
