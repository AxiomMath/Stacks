module

public import Mathlib.CategoryTheory.Sites.Subcanonical

/-!
# Natural endomorphisms of the identity of the topos of a subcanonical site

Let `J` be a subcanonical Grothendieck topology on a category `C` and let
`τ : 𝟭 ⟶ 𝟭` be a natural endomorphism of the identity functor of the category of sheaves of
types on `(C, J)`. Its component on the sheaf `h_U` represented by an object `U` is, by Yoneda,
postcomposition with an endomorphism `α_U : U ⟶ U`, and these form a natural endomorphism of the
identity of `C` (`g ≫ α_U = α_V ≫ g` for `g : V ⟶ U`). Its component on any sheaf `F` is
restriction along these endomorphisms: `τ_F(x) = F(α_U)(x)` for `x ∈ F(U)`.

So `τ` is the identity as soon as every `α_U` is. Because each `h_U` is separated, it suffices
that `α_V = 𝟙` for the sources `V` of a family of arrows generating a covering sieve of each `U`.
This is the rigidity input in the proof of [Stacks Project, Tag 0D17], part (2), where `C` is the
small étale site of an algebraic space and the `V` are the affine étale charts.

## Main definitions
* `CategoryTheory.GrothendieckTopology.identityEndRepresenting`: the endomorphism `α_U`.

## Main results
* `CategoryTheory.GrothendieckTopology.identityEnd_app_apply`: `τ_F(x) = F(α_U)(x)`.
* `CategoryTheory.GrothendieckTopology.comp_identityEndRepresenting`: naturality of `α`.
* `CategoryTheory.GrothendieckTopology.identityEnd_eq_id_of_generate`: `τ = 𝟙` once `α_V = 𝟙`
  for the sources of generating families of covering sieves.
-/

@[expose] public section

open CategoryTheory Opposite

universe v u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [J.Subcanonical]
  (τ : 𝟭 (Sheaf J (Type v)) ⟶ 𝟭 (Sheaf J (Type v)))

/-- The endomorphism `α_U : U ⟶ U` by which a natural endomorphism `τ` of the identity of the
sheaves of types acts on the sheaf represented by `U`, read through Yoneda. -/
def identityEndRepresenting (U : C) : U ⟶ U :=
  J.yonedaEquiv (τ.app (J.yoneda.obj U))

/-- **A natural endomorphism of the identity of a subcanonical topos is restriction along the
endomorphisms `α_U`**: `τ_F(x) = F(α_U)(x)` for every sheaf `F` and `x ∈ F(U)`. -/
theorem identityEnd_app_apply (F : Sheaf J (Type v)) (U : C) (x : F.obj.obj (op U)) :
    (τ.app F).hom.app (op U) x = F.obj.map (J.identityEndRepresenting τ U).op x := by
  have h := congrArg J.yonedaEquiv (τ.naturality (J.yonedaEquiv.symm x))
  simp only [Functor.id_map, yonedaEquiv_comp, Equiv.apply_symm_apply] at h
  exact h

/-- **The endomorphisms `α_U` are natural**: `g ≫ α_U = α_V ≫ g` for `g : V ⟶ U`. -/
theorem comp_identityEndRepresenting {U V : C} (g : V ⟶ U) :
    g ≫ J.identityEndRepresenting τ U = J.identityEndRepresenting τ V ≫ g := by
  have h₁ := J.identityEnd_app_apply τ (J.yoneda.obj U) V g
  have h₂ := NatTrans.naturality_apply (τ.app (J.yoneda.obj U)).hom g.op (𝟙 U)
  exact h₂.symm.trans ((congrArg _ (Category.comp_id g)).trans h₁)

/-- **Rigidity of the identity of a subcanonical topos**: a natural endomorphism `τ` of the
identity of the sheaves of types is the identity once `α_V = 𝟙` for the source `V` of every
arrow of a family `R U` generating a covering sieve of each object `U`. -/
theorem identityEnd_eq_id_of_generate (R : ∀ U : C, Presieve U)
    (hR : ∀ U, Sieve.generate (R U) ∈ J U)
    (h : ∀ ⦃U V : C⦄ (g : V ⟶ U), R U g → J.identityEndRepresenting τ V = 𝟙 V) :
    τ = 𝟙 _ := by
  have hα : ∀ U, J.identityEndRepresenting τ U = 𝟙 U := by
    intro U
    have hsh := (isSheaf_iff_isSheaf_of_type J _).1 (J.yoneda.obj U).cond
    refine (hsh.isSeparated _ (hR U)).ext fun W f hf => ?_
    obtain ⟨V, f', g, hg, rfl⟩ := hf
    change (f' ≫ g) ≫ J.identityEndRepresenting τ U = (f' ≫ g) ≫ 𝟙 U
    rw [Category.assoc, comp_identityEndRepresenting, h g hg, Category.id_comp,
      Category.comp_id]
  ext F U x
  change (τ.app F).hom.app U x = x
  rw [identityEnd_app_apply, hα, op_id, F.obj.map_id]
  rfl

end CategoryTheory.GrothendieckTopology
