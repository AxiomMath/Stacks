module

public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Iso

/-!
# A pasted base change isomorphism, read as a pointwise cocycle

A base change isomorphism `ρ : Φ ⋙ G ≅ E₁ ⋙ Φ'` and a second one `σ : Φ' ⋙ H ≅ E₂ ⋙ Φ''` paste,
along contractions `c : G ⋙ H ≅ K` and `δ : E₁ ⋙ E₂ ≅ E` of the two composites, to an
isomorphism `Φ ⋙ K ≅ E ⋙ Φ''`. If the pasting equals a given isomorphism `k`, then at every
object the four factors compose to the component of `k`.

## Main results

* `Stacks.CategoryTheory.BaseChange.pastedBaseChangeIso_hom_app_of_eq`: the pasting of two base
  change isomorphisms, read at an object, given as an equation of isomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Stacks.CategoryTheory.BaseChange

variable {M M' M'' A B C : Type*} [Category* M] [Category* M'] [Category* M''] [Category* A]
  [Category* B] [Category* C] {Φ : M ⥤ A} {Φ' : M' ⥤ B} {Φ'' : M'' ⥤ C} {E₁ : M ⥤ M'}
  {E₂ : M' ⥤ M''} {E : M ⥤ M''} {G : A ⥤ B} {H : B ⥤ C} {K : A ⥤ C}

/-- **Two pasted base change isomorphisms, read at an object.** If the pasting of `ρ` and `σ`
along the contractions `c` and `δ` is the isomorphism `k`, then at every object `X` the
contraction `c`, the component of `ρ` pushed along `H`, the component of `σ` and the image of the
component of `δ` compose to the component of `k`. -/
theorem pastedBaseChangeIso_hom_app_of_eq (c : G ⋙ H ≅ K) (δ : E₁ ⋙ E₂ ≅ E)
    (ρ : Φ ⋙ G ≅ E₁ ⋙ Φ') (σ : Φ' ⋙ H ≅ E₂ ⋙ Φ'') (k : Φ ⋙ K ≅ E ⋙ Φ'')
    (hk : Functor.isoWhiskerLeft Φ c.symm ≪≫ (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight ρ H ≪≫ Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft E₁ σ ≪≫ (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight δ Φ'' = k)
    (X : M) :
    c.inv.app (Φ.obj X) ≫ H.map (ρ.hom.app X) ≫ σ.hom.app (E₁.obj X) ≫
        Φ''.map (δ.hom.app X) =
      k.hom.app X := by
  subst hk
  simp

end Stacks.CategoryTheory.BaseChange

end
