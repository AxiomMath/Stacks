module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomology
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.EnvelopeDescent
public import StacksCore.Tactic.StacksAttribute

/-!
# The composition and identity laws for restriction on Chow cohomology

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, Stacks 02QL. For a
morphism `f : X' ⟶ X` of schemes locally of finite type over the base,
`Stacks.Chow.chowCohomologyRestriction` is the restriction map `f^* : A^p(X) ⟶ A^p(X')` of
Stacks 0B7F. It makes `A^p(-)` a contravariant functor:

  `(a ≫ f)^* = a^* ∘ f^*`  and  `(𝟙 X)^* = id`.

## Main results

* `Stacks.Chow.chowCohomologyRestriction_comp`: restricting along `f : Y ⟶ X` and then along
  `a : W ⟶ Y` is restricting along `a ≫ f`.
* `Stacks.Chow.chowCohomologyRestriction_id`: restricting along the identity is the identity.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section Functoriality

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y W : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (f : Y ⟶ X) [LocallyOfFiniteType f] (a : W ⟶ Y)
  [LocallyOfFiniteType a] (p : ℤ) (hgys : G.IsNaturalUnderBaseChangeIso)

/-- The restriction map of Stacks 0B7F is compatible with composition: restricting a class on `X`
along `f : Y ⟶ X` and then along `a : W ⟶ Y` gives the restriction along `a ≫ f`,

  `a^*(f^*(c)) = (a ≫ f)^*(c)`. -/
@[stacks 0F9Z "compatibility with compositions, for the restriction map on Chow cohomology of \
Tag 0B7F"]
theorem chowCohomologyRestriction_comp (c : chowCohomologyComponent C G sX p) :
    chowCohomologyRestriction C G (f ≫ sX) a p hgys
        (chowCohomologyRestriction C G sX f p hgys c) =
      chowCohomologyRestriction C G sX (a ≫ f) p hgys c := by
  ext T t _ k α
  refine chowPushforwardOfIso_injective C (pullback.fst (𝟙 W) t ≫ (a ≫ (f ≫ sX)))
    (t ≫ (a ≫ (f ≫ sX))) (identityBaseChangeIso t).hom
    (identityBaseChangeIso_hom_comp_base C (a ≫ (f ≫ sX)) t) (k - p) ?_
  exact (chowCohomologyRestriction_cap C G (f ≫ sX) a p hgys
      (chowCohomologyRestriction C G sX f p hgys c) t k α).trans
    ((chowCohomologyRestriction_cap C G sX f p hgys c (t ≫ a) k α).trans
      (chowCohomologyRestriction_cap C G sX (a ≫ f) p hgys c t k α).symm)

/-- The restriction map of Stacks 0B7F along an identity is the identity: `(𝟙 X)^* = id`. -/
theorem chowCohomologyRestriction_id (c : chowCohomologyComponent C G sX p) :
    chowCohomologyRestriction C G sX (𝟙 X) p hgys c = c := by
  ext T t _ k α
  refine chowPushforwardOfIso_injective C (pullback.fst (𝟙 X) t ≫ sX) (t ≫ sX)
    (identityBaseChangeIso t).hom (identityBaseChangeIso_hom_comp_base C sX t) (k - p) ?_
  exact chowCohomologyRestriction_cap C G sX (𝟙 X) p hgys c t k α

end Functoriality

end Stacks.Chow

end
