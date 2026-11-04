module

public import Mathlib.CategoryTheory.Adjunction.Parametrized
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Whiskering

/-!
# Uniqueness and composition of adjunctions with a parameter

Mathlib's `CategoryTheory.ParametrizedAdjunction F G`, written `F ⊣₂ G`, is a family of
adjunctions `F.obj X ⊣ G.obj (op X)` indexed by a parameter `X`, together with the naturality
of the units in `X`. This file supplies the three things that family is missing and that a
caller needs in order to *identify* two such right bifunctors:

* uniqueness — two parametrized right adjoints of one bifunctor are isomorphic **as
  bifunctors**, so the comparison is natural in the parameter as well as in the remaining
  variable;
* transport of a parametrized adjunction along an isomorphism of left bifunctors, which is
  what lets two right adjoints be compared when their left adjoints agree only up to the
  associator;
* three ways of composing a parametrized adjunction with an ordinary one — precomposing the
  parameter, and composing on either of the two remaining variables.

The point of doing this at the level of bifunctors is naturality in the *contravariant*
variable of an internal hom. `CategoryTheory.Adjunction.rightAdjointUniq` identifies two right
adjoints of one functor, which gives naturality in the covariant variable only; the parameter
of a `⊣₂` is exactly the contravariant one.

## Main definitions

All in the namespace `Stacks.Duality`.

* `parametrizedOfNatIsoLeft` — transport along `F ≅ F'`.
* `parametrizedRightAdjointUniq` — `(F ⊣₂ G) → (F ⊣₂ G') → (G ≅ G')`.
* `parametrizedCompParam` — precompose the parameter by a functor.
* `parametrizedCompTarget`, `parametrizedCompSource` — compose with an ordinary adjunction on
  the third, resp. the second, variable.

## Main results

* `Stacks.Duality.rightAdjointUniq_hom_app_eq` — the component of
  `CategoryTheory.Adjunction.rightAdjointUniq` is the adjunct of the counit. This is the only
  thing used about it, and it is what makes the naturality in the parameter come out of
  `CategoryTheory.ParametrizedAdjunction.whiskerLeft_map_counit`.

## Implementation notes

Everything is built through `CategoryTheory.ParametrizedAdjunction.mk'`, whose compatibility is
stated in terms of `Adjunction.homEquiv`; for each of the three composition lemmas the
verification is two rewrites, one naturality of the ordinary adjunction's bijection and one
naturality of the parametrized one.

## References

* [nLab, two-variable adjunction](https://ncatlab.org/nlab/show/two-variable+adjunction)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe v₀ v₁ v₂ v₃ v₄ v₅ u₀ u₁ u₂ u₃ u₄ u₅

namespace Stacks.Duality

variable {C₀ : Type u₀} {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
  {C₅ : Type u₅}
  [Category.{v₀} C₀] [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  [Category.{v₄} C₄] [Category.{v₅} C₅]

/-! ### The component of `rightAdjointUniq` -/

/-- The component of `CategoryTheory.Adjunction.rightAdjointUniq` at an object is the adjunct,
under the second adjunction, of the counit of the first. -/
theorem rightAdjointUniq_hom_app_eq {D : Type u₂} {E : Type u₃} [Category.{v₂} D]
    [Category.{v₃} E] {F : D ⥤ E} {G G' : E ⥤ D} (adj : F ⊣ G) (adj' : F ⊣ G') (x : E) :
    (Adjunction.rightAdjointUniq adj adj').hom.app x =
      (adj'.homEquiv _ _) (adj.counit.app x) :=
  (Equiv.symm_apply_eq _).mp (adj.homEquiv_symm_rightAdjointUniq_hom_app adj' x)

/-! ### Transport along an isomorphism of left bifunctors -/

/-- A parametrized adjunction transported along an isomorphism of its left bifunctors. -/
def parametrizedOfNatIsoLeft {F F' : C₁ ⥤ C₂ ⥤ C₃} {G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂}
    (a : F ⊣₂ G) (e : F ≅ F') : F' ⊣₂ G :=
  ParametrizedAdjunction.mk' (fun X => (a.adj X).ofNatIsoLeft (e.app X)) (by
    intro X₁ Y₁ f X₂ X₃ g
    simp only [Adjunction.homEquiv_ofNatIsoLeft_apply]
    rw [← ParametrizedAdjunction.homEquiv_eq, ← ParametrizedAdjunction.homEquiv_eq,
      ← a.homEquiv_naturality_one]
    congr 1
    have hn := NatTrans.congr_app (e.hom.naturality f) X₂
    simp only [Iso.app_hom, NatTrans.comp_app] at hn ⊢
    rw [← Category.assoc, ← Category.assoc, hn])

/-! ### Uniqueness of the parametrized right adjoint -/

/-- **Two parametrized right adjoints of one bifunctor are isomorphic as bifunctors.** The
comparison at each parameter is `CategoryTheory.Adjunction.rightAdjointUniq`; naturality in the
parameter is the compatibility of the counits recorded by
`CategoryTheory.ParametrizedAdjunction.whiskerLeft_map_counit`. -/
def parametrizedRightAdjointUniq {F : C₁ ⥤ C₂ ⥤ C₃} {G G' : C₁ᵒᵖ ⥤ C₃ ⥤ C₂}
    (a : F ⊣₂ G) (a' : F ⊣₂ G') : G ≅ G' :=
  NatIso.ofComponents (fun X => Adjunction.rightAdjointUniq (a.adj X.unop) (a'.adj X.unop))
    (by
      intro X Y φ
      ext W
      dsimp
      have key : a'.homEquiv
            ((F.map φ.unop).app ((G.obj X).obj W) ≫ (a.adj X.unop).counit.app W) =
          a'.homEquiv ((a.adj X.unop).counit.app W) ≫ (G'.map φ).app W :=
        a'.homEquiv_naturality_one φ.unop _
      rw [rightAdjointUniq_hom_app_eq, rightAdjointUniq_hom_app_eq,
        ← ParametrizedAdjunction.homEquiv_eq, ← ParametrizedAdjunction.homEquiv_eq,
        ← a'.homEquiv_naturality_two (f₂ := (G.map φ).app W), ← key]
      congr 1
      exact (NatTrans.congr_app (a.whiskerLeft_map_counit φ.unop) W).symm)

/-! ### Composing a parametrized adjunction with an ordinary one -/

/-- Precomposing the parameter of a parametrized adjunction by a functor. -/
def parametrizedCompParam {F : C₁ ⥤ C₂ ⥤ C₃} {G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂} (a : F ⊣₂ G)
    (H : C₀ ⥤ C₁) : (H ⋙ F) ⊣₂ (H.op ⋙ G) :=
  ParametrizedAdjunction.mk' (fun X => a.adj (H.obj X)) fun f _ _ g =>
    a.homEquiv_naturality_one (H.map f) g

/-- Composing a parametrized adjunction with an ordinary adjunction on the third variable: the
left bifunctor is postcomposed by the left adjoint, the right bifunctor precomposed by the
right adjoint. -/
def parametrizedCompTarget {F : C₁ ⥤ C₂ ⥤ C₃} {G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂} (a : F ⊣₂ G)
    {P : C₃ ⥤ C₄} {Q : C₄ ⥤ C₃} (adj : P ⊣ Q) :
    (F ⋙ (Functor.whiskeringRight C₂ C₃ C₄).obj P) ⊣₂
      (G ⋙ (Functor.whiskeringLeft C₄ C₃ C₂).obj Q) :=
  ParametrizedAdjunction.mk' (fun X => (a.adj X).comp adj) (by
    intro X₁ Y₁ f X₂ X₃ g
    simp only [Adjunction.comp_homEquiv, Equiv.trans_apply]
    change (a.adj X₁).homEquiv X₂ (Q.obj X₃)
        ((adj.homEquiv ((F.obj X₁).obj X₂) X₃) (P.map ((F.map f).app X₂) ≫ g)) =
      (a.adj Y₁).homEquiv X₂ (Q.obj X₃)
        ((adj.homEquiv ((F.obj Y₁).obj X₂) X₃) g) ≫ (G.map f.op).app (Q.obj X₃)
    rw [adj.homEquiv_naturality_left]
    exact a.homEquiv_naturality_one f _)

/-- Composing a parametrized adjunction with an ordinary adjunction on the second variable: the
left bifunctor is precomposed by the left adjoint, the right bifunctor postcomposed by the
right adjoint. -/
def parametrizedCompSource {F : C₁ ⥤ C₂ ⥤ C₃} {G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂} (a : F ⊣₂ G)
    {P : C₅ ⥤ C₂} {Q : C₂ ⥤ C₅} (adj : P ⊣ Q) :
    (F ⋙ (Functor.whiskeringLeft C₅ C₂ C₃).obj P) ⊣₂
      (G ⋙ (Functor.whiskeringRight C₃ C₂ C₅).obj Q) :=
  ParametrizedAdjunction.mk' (fun X => adj.comp (a.adj X)) (by
    intro X₁ Y₁ f X₂ X₃ g
    simp only [Adjunction.comp_homEquiv, Equiv.trans_apply]
    change (adj.homEquiv X₂ ((G.obj (Opposite.op X₁)).obj X₃))
        ((a.adj X₁).homEquiv (P.obj X₂) X₃ ((F.map f).app (P.obj X₂) ≫ g)) =
      (adj.homEquiv X₂ ((G.obj (Opposite.op Y₁)).obj X₃))
        ((a.adj Y₁).homEquiv (P.obj X₂) X₃ g) ≫ Q.map ((G.map f.op).app X₃)
    have hh : (a.adj X₁).homEquiv (P.obj X₂) X₃ ((F.map f).app (P.obj X₂) ≫ g) =
        (a.adj Y₁).homEquiv (P.obj X₂) X₃ g ≫ (G.map f.op).app X₃ :=
      a.homEquiv_naturality_one f g
    rw [hh, adj.homEquiv_naturality_right])

end Stacks.Duality

end
