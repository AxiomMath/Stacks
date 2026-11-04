module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.CategoryTheory.Adjunction.LeftAdjointCompIsoHomEquiv

/-!
# Transposes along a composite of morphisms of schemes

For morphisms `q : X'' ⟶ X'` and `g : X' ⟶ X` of schemes and morphisms of sheaves of modules
`c : g^*A ⟶ B`, `c' : q^*B ⟶ C` and `c'' : (q ≫ g)^*A ⟶ C`, the morphism `c''` factors as
`(q ≫ g)^*A ≅ q^*g^*A ⟶ q^*B ⟶ C` exactly when its adjoint transpose `A ⟶ (q ≫ g)_*C` is the
composite of the transposes of `c` and `c'`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.eq_pullbackComp_inv_comp`: the factorization, from the
  equation between transposes.
* `AlgebraicGeometry.Scheme.Modules.eq_pullbackComp_inv_comp_of_sections`: the same, with the
  equation between transposes checked on local sections.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

universe u

/-- **A morphism out of the inverse image along a composite factors through the composition
law** as soon as its transpose is the composite of the two transposes. -/
theorem AlgebraicGeometry.Scheme.Modules.eq_pullbackComp_inv_comp {X X' X'' : Scheme.{u}}
    (q : X'' ⟶ X') (g : X' ⟶ X) {A : X.Modules} {B : X'.Modules} {C : X''.Modules}
    (c : (Scheme.Modules.pullback g).obj A ⟶ B) (c' : (Scheme.Modules.pullback q).obj B ⟶ C)
    (c'' : (Scheme.Modules.pullback (q ≫ g)).obj A ⟶ C)
    (h : (Scheme.Modules.pullbackPushforwardAdjunction (q ≫ g)).homEquiv A C c'' =
      (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv A B c ≫
        (Scheme.Modules.pushforward g).map
          ((Scheme.Modules.pullbackPushforwardAdjunction q).homEquiv B C c')) :
    c'' = (Scheme.Modules.pullbackComp q g).inv.app A ≫ (Scheme.Modules.pullback q).map c ≫ c' := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (q ≫ g)).homEquiv A C).injective
  rw [h]
  have := Adjunction.homEquiv_leftAdjointCompIso_inv_app
    (Scheme.Modules.pullbackPushforwardAdjunction g)
    (Scheme.Modules.pullbackPushforwardAdjunction q)
    (Scheme.Modules.pullbackPushforwardAdjunction (q ≫ g)) (Scheme.Modules.pushforwardComp q g)
    c c'
  refine Eq.symm (this.trans ?_)
  congr 1

/-- The factorization through the composition law, with the equation between the transposes
checked on local sections. -/
theorem AlgebraicGeometry.Scheme.Modules.eq_pullbackComp_inv_comp_of_sections
    {X X' X'' : Scheme.{u}} (q : X'' ⟶ X') (g : X' ⟶ X)
    {A : X.Modules} {B : X'.Modules} {C : X''.Modules}
    (c : (Scheme.Modules.pullback g).obj A ⟶ B) (c' : (Scheme.Modules.pullback q).obj B ⟶ C)
    (c'' : (Scheme.Modules.pullback (q ≫ g)).obj A ⟶ C)
    (h : ∀ (O : X.Opens) (x : A.val.obj (op O)),
      ((Scheme.Modules.pullbackPushforwardAdjunction (q ≫ g)).homEquiv A C c'').val.app (op O) x =
        ((Scheme.Modules.pullbackPushforwardAdjunction q).homEquiv B C c').val.app (op (g ⁻¹ᵁ O))
          (((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv A B c).val.app (op O) x)) :
    c'' = (Scheme.Modules.pullbackComp q g).inv.app A ≫ (Scheme.Modules.pullback q).map c ≫ c' :=
  Scheme.Modules.eq_pullbackComp_inv_comp q g c c' c''
    (SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun O =>
      ModuleCat.hom_ext (LinearMap.ext fun x => h O.unop x)))

