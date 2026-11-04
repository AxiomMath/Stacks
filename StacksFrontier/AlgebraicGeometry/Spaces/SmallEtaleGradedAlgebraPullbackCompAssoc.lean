module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraSquareMap
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.EtaleCoherence
public import StacksFrontier.CategoryTheory.Functor.CompIsoCube

/-!
# Associativity of the composition comparison for pullbacks of sheaves of graded algebras

For morphisms of algebraic spaces `f`, `g`, `h`,
`AlgebraicGeometry.Space.gradedAlgebraPullbackCompIso` compares `(f ≫ g)^*` with `g^* ∘ f^*` on
sheaves of graded algebras.  This file proves that the comparison is **associative**: the two
ways of comparing `(f ≫ g ≫ h)^*` with `h^* ∘ g^* ∘ f^*` agree.  It is the coherence of a
pseudofunctor, and it is the transpose of the associativity of
the comparison of direct images, `AlgebraicGeometry.Space.gradedAlgebraPushforwardCompIso_assoc`.

The comparison along a morphism which only *equals* a composite,
`AlgebraicGeometry.Space.gradedAlgebraPullbackCompIsoOfEq`, inherits the coherence, with every
composite given as a separate morphism and an equation; that is the form in which squares of
algebraic spaces are pasted.

## Main results

* `AlgebraicGeometry.Space.gradedAlgebraPullbackCompIso_eq_leftAdjointCompIso`: the comparison is
  the comparison of left adjoints induced by the comparison of direct images.
* `AlgebraicGeometry.Space.gradedAlgebraPullbackCompIso_assoc`: **the associativity coherence.**
* `AlgebraicGeometry.Space.gradedAlgebraPullbackCompIsoOfEq_assoc`: the same for the
  comparisons along morphisms equal to composites, and
  `AlgebraicGeometry.Space.isAssoc_gradedAlgebraPullbackCompIsoOfEq`, the same in the form of
  `CategoryTheory.CompIsoCube.IsAssoc`.

## References

* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull gradedPush gradedAdj
  gradedPullbackCompIso)

namespace CategoryTheory.Adjunction

variable {C₀ C₁ C₂ C₃ : Type*} [Category* C₀] [Category* C₁] [Category* C₂] [Category* C₃]
  {F₀₁ : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂} {F₂₃ : C₂ ⥤ C₃} {F₀₂ : C₀ ⥤ C₂} {F₁₃ : C₁ ⥤ C₃} {F₀₃ : C₀ ⥤ C₃}
  {G₁₀ : C₁ ⥤ C₀} {G₂₁ : C₂ ⥤ C₁} {G₃₂ : C₃ ⥤ C₂} {G₂₀ : C₂ ⥤ C₀} {G₃₁ : C₃ ⥤ C₁} {G₃₀ : C₃ ⥤ C₀}

/-- `CategoryTheory.Adjunction.leftAdjointCompIso_assoc` for comparisons of left adjoints which
are only *equal* to the inverses of the induced ones, given as variables.  Stating it this way
lets a consumer instantiate it without rewriting inside its own comparisons. -/
theorem leftAdjointCompIso_assoc_of_eq (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₁₂ : F₁₂ ⊣ G₂₁)
    (adj₂₃ : F₂₃ ⊣ G₃₂) (adj₀₂ : F₀₂ ⊣ G₂₀) (adj₁₃ : F₁₃ ⊣ G₃₁) (adj₀₃ : F₀₃ ⊣ G₃₀)
    (e₀₁₂ : G₂₁ ⋙ G₁₀ ≅ G₂₀) (e₁₂₃ : G₃₂ ⋙ G₂₁ ≅ G₃₁)
    (e₀₁₃ : G₃₁ ⋙ G₁₀ ≅ G₃₀) (e₀₂₃ : G₃₂ ⋙ G₂₀ ≅ G₃₀)
    (h : isoWhiskerLeft G₃₂ e₀₁₂ ≪≫ e₀₂₃ =
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight e₁₂₃ _ ≪≫ e₀₁₃)
    (P₀₁₂ : F₀₂ ≅ F₀₁ ⋙ F₁₂) (P₁₂₃ : F₁₃ ≅ F₁₂ ⋙ F₂₃) (P₀₁₃ : F₀₃ ≅ F₀₁ ⋙ F₁₃)
    (P₀₂₃ : F₀₃ ≅ F₀₂ ⋙ F₂₃)
    (h₀₁₂ : P₀₁₂ = (leftAdjointCompIso adj₀₁ adj₁₂ adj₀₂ e₀₁₂).symm)
    (h₁₂₃ : P₁₂₃ = (leftAdjointCompIso adj₁₂ adj₂₃ adj₁₃ e₁₂₃).symm)
    (h₀₁₃ : P₀₁₃ = (leftAdjointCompIso adj₀₁ adj₁₃ adj₀₃ e₀₁₃).symm)
    (h₀₂₃ : P₀₂₃ = (leftAdjointCompIso adj₀₂ adj₂₃ adj₀₃ e₀₂₃).symm) :
    isoWhiskerLeft F₀₁ P₁₂₃.symm ≪≫ P₀₁₃.symm =
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight P₀₁₂.symm F₂₃ ≪≫ P₀₂₃.symm := by
  subst h₀₁₂ h₁₂₃ h₀₁₃ h₀₂₃
  simp only [Iso.symm_symm_eq]
  exact leftAdjointCompIso_assoc adj₀₁ adj₁₂ adj₂₃ adj₀₂ adj₁₃ adj₀₃ e₀₁₂ e₁₂₃ e₀₁₃ e₀₂₃ h

end CategoryTheory.Adjunction

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {W X Y Z : AlgebraicSpaces B S hS}

/-- The pullback comparison built from an isomorphism of direct images is the comparison of left
adjoints induced by it. -/
private theorem gradedPullbackCompIso_eq_leftAdjointCompIso_aux (f : X ⟶ Y) (g : Y ⟶ Z)
    (j : X ⟶ Z)
    (e : gradedPush (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
        (smallEtaleRingedToposHom B S hS f) ⋙
      gradedPush (X := smallEtaleRingedTopos B S hS Y) (Y := smallEtaleRingedTopos B S hS Z)
        (smallEtaleRingedToposHom B S hS g) ≅
      gradedPush (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Z)
        (smallEtaleRingedToposHom B S hS j)) :
    gradedPullbackCompIso (smallEtaleRingedToposHom B S hS f) (smallEtaleRingedToposHom B S hS g)
        (smallEtaleRingedToposHom B S hS j) e =
      (Adjunction.leftAdjointCompIso
        (gradedAdj (X := smallEtaleRingedTopos B S hS Y) (Y := smallEtaleRingedTopos B S hS Z)
          (smallEtaleRingedToposHom B S hS g))
        (gradedAdj (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
          (smallEtaleRingedToposHom B S hS f))
        (gradedAdj (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Z)
          (smallEtaleRingedToposHom B S hS j)) e).symm := by
  refine Iso.ext ((conjugateEquiv
    ((gradedAdj (X := smallEtaleRingedTopos B S hS Y) (Y := smallEtaleRingedTopos B S hS Z)
      (smallEtaleRingedToposHom B S hS g)).comp
      (gradedAdj (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
        (smallEtaleRingedToposHom B S hS f)))
    (gradedAdj (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Z)
      (smallEtaleRingedToposHom B S hS j))).injective ?_)
  refine (Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom _ e.symm
    _).trans ?_
  exact (Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _).symm

/-- **The graded composition comparison is the comparison of left adjoints induced by the
comparison of direct images**, in the form `CategoryTheory.Adjunction.leftAdjointCompIso` for
which Mathlib proves the pseudofunctor coherences. -/
theorem gradedAlgebraPullbackCompIso_eq_leftAdjointCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    gradedAlgebraPullbackCompIso B S hS f g =
      (Adjunction.leftAdjointCompIso
        (gradedAdj (X := smallEtaleRingedTopos B S hS Y) (Y := smallEtaleRingedTopos B S hS Z)
          (smallEtaleRingedToposHom B S hS g))
        (gradedAdj (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
          (smallEtaleRingedToposHom B S hS f))
        (gradedAdj (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Z)
          (smallEtaleRingedToposHom B S hS (f ≫ g)))
        (gradedAlgebraPushforwardCompIso B S hS f g)).symm :=
  gradedPullbackCompIso_eq_leftAdjointCompIso_aux B S hS f g (f ≫ g)
    (gradedAlgebraPushforwardCompIso B S hS f g)

/-- **Associativity of the composition comparison for pullbacks of sheaves of graded
algebras.**  For `f : W ⟶ X`, `g : X ⟶ Y`, `h : Y ⟶ Z` the two ways of comparing
`(f ≫ g ≫ h)^*` with `h^* ∘ g^* ∘ f^*` agree. -/
theorem gradedAlgebraPullbackCompIso_assoc (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    isoWhiskerLeft (gradedPull (X := smallEtaleRingedTopos B S hS Y)
        (Y := smallEtaleRingedTopos B S hS Z) (smallEtaleRingedToposHom B S hS h))
        (gradedAlgebraPullbackCompIso B S hS f g).symm ≪≫
      (gradedAlgebraPullbackCompIso B S hS (f ≫ g) h).symm =
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (gradedAlgebraPullbackCompIso B S hS g h).symm
        (gradedPull (X := smallEtaleRingedTopos B S hS W) (Y := smallEtaleRingedTopos B S hS X)
          (smallEtaleRingedToposHom B S hS f)) ≪≫
      (gradedAlgebraPullbackCompIso B S hS f (g ≫ h)).symm :=
  Adjunction.leftAdjointCompIso_assoc_of_eq _ _ _ _ _ _ _ _ _ _
    (gradedAlgebraPushforwardCompIso_assoc B S hS f g h) _ _ _ _
    (gradedAlgebraPullbackCompIso_eq_leftAdjointCompIso B S hS g h)
    (gradedAlgebraPullbackCompIso_eq_leftAdjointCompIso B S hS f g)
    (gradedAlgebraPullbackCompIso_eq_leftAdjointCompIso B S hS (f ≫ g) h)
    (gradedAlgebraPullbackCompIso_eq_leftAdjointCompIso B S hS f (g ≫ h))

/-- The associativity coherence at a single sheaf of graded algebras. -/
theorem gradedAlgebraPullbackCompIso_assoc_app (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (𝒜 : SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Z).O)) :
    (gradedAlgebraPullbackCompIso B S hS f (g ≫ h)).hom.app 𝒜 ≫
        (gradedPull (X := smallEtaleRingedTopos B S hS W) (Y := smallEtaleRingedTopos B S hS X)
          (smallEtaleRingedToposHom B S hS f)).map
          ((gradedAlgebraPullbackCompIso B S hS g h).hom.app 𝒜) =
      (gradedAlgebraPullbackCompIso B S hS (f ≫ g) h).hom.app 𝒜 ≫
        (gradedAlgebraPullbackCompIso B S hS f g).hom.app
          ((gradedPull (X := smallEtaleRingedTopos B S hS Y) (Y := smallEtaleRingedTopos B S hS Z)
            (smallEtaleRingedToposHom B S hS h)).obj 𝒜) := by
  have e := congrArg (fun i => i.inv.app 𝒜) (gradedAlgebraPullbackCompIso_assoc B S hS f g h)
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, associator_hom_app,
    Category.comp_id, Functor.comp_obj] at e
  exact e.symm

/-- The comparison along a morphism equal to the composite, at the composite itself and an
arbitrary proof of the equation, is the comparison along the composite. -/
theorem gradedAlgebraPullbackCompIsoOfEq_self (f : X ⟶ Y) (g : Y ⟶ Z) (hfg : f ≫ g = f ≫ g) :
    gradedAlgebraPullbackCompIsoOfEq B S hS f g (f ≫ g) hfg =
      gradedAlgebraPullbackCompIso B S hS f g :=
  gradedAlgebraPullbackCompIsoOfEq_rfl B S hS f g

/-- **The graded composition comparison along a morphism equal to a composite is the comparison
of left adjoints induced by the comparison of direct images**, as
`AlgebraicGeometry.Space.gradedAlgebraPullbackCompIso_eq_leftAdjointCompIso` is for the
composite itself. -/
theorem gradedAlgebraPullbackCompIsoOfEq_eq_leftAdjointCompIso (f : X ⟶ Y) (g : Y ⟶ Z)
    (j : X ⟶ Z) (hj : j = f ≫ g) :
    gradedAlgebraPullbackCompIsoOfEq B S hS f g j hj =
      (Adjunction.leftAdjointCompIso
        (gradedAdj (X := smallEtaleRingedTopos B S hS Y) (Y := smallEtaleRingedTopos B S hS Z)
          (smallEtaleRingedToposHom B S hS g))
        (gradedAdj (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
          (smallEtaleRingedToposHom B S hS f))
        (gradedAdj (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Z)
          (smallEtaleRingedToposHom B S hS j))
        (gradedAlgebraPushforwardCompIsoOfEq B S hS f g j hj)).symm :=
  gradedPullbackCompIso_eq_leftAdjointCompIso_aux B S hS f g j
    (gradedAlgebraPushforwardCompIsoOfEq B S hS f g j hj)

/-- **Associativity of the comparison of direct images along morphisms equal to composites.** -/
theorem gradedAlgebraPushforwardCompIsoOfEq_assoc (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z)
    (ab : W ⟶ Y) (bc : X ⟶ Z) (t : W ⟶ Z) (hab : ab = a ≫ b) (hbc : bc = b ≫ c)
    (h₁ : t = a ≫ bc) (h₂ : t = ab ≫ c) :
    isoWhiskerLeft (gradedPush (X := smallEtaleRingedTopos B S hS W)
        (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposHom B S hS a))
        (gradedAlgebraPushforwardCompIsoOfEq B S hS b c bc hbc) ≪≫
      gradedAlgebraPushforwardCompIsoOfEq B S hS a bc t h₁ =
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (gradedAlgebraPushforwardCompIsoOfEq B S hS a b ab hab)
        (gradedPush (X := smallEtaleRingedTopos B S hS Y) (Y := smallEtaleRingedTopos B S hS Z)
          (smallEtaleRingedToposHom B S hS c)) ≪≫
      gradedAlgebraPushforwardCompIsoOfEq B S hS ab c t h₂ := by
  subst hab hbc h₁
  simp only [gradedAlgebraPushforwardCompIsoOfEq, eqToIso_refl, Iso.trans_refl]
  exact gradedAlgebraPushforwardCompIso_assoc B S hS a b c

/-- **Associativity of the composition comparison along morphisms equal to composites.**  For
`a : W ⟶ X`, `b : X ⟶ Y`, `c : Y ⟶ Z` and morphisms `ab`, `bc` and `t` equal to `a ≫ b`, `b ≫ c`
and to both `a ≫ bc` and `ab ≫ c`, the two ways of comparing `t^*` with `a^* ∘ b^* ∘ c^*` on
sheaves of graded algebras agree. -/
theorem gradedAlgebraPullbackCompIsoOfEq_assoc (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z)
    (ab : W ⟶ Y) (bc : X ⟶ Z) (t : W ⟶ Z) (hab : ab = a ≫ b) (hbc : bc = b ≫ c)
    (h₁ : t = a ≫ bc) (h₂ : t = ab ≫ c) :
    isoWhiskerLeft (gradedPull (X := smallEtaleRingedTopos B S hS Y)
        (Y := smallEtaleRingedTopos B S hS Z) (smallEtaleRingedToposHom B S hS c))
        (gradedAlgebraPullbackCompIsoOfEq B S hS a b ab hab).symm ≪≫
      (gradedAlgebraPullbackCompIsoOfEq B S hS ab c t h₂).symm =
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (gradedAlgebraPullbackCompIsoOfEq B S hS b c bc hbc).symm
        (gradedPull (X := smallEtaleRingedTopos B S hS W) (Y := smallEtaleRingedTopos B S hS X)
          (smallEtaleRingedToposHom B S hS a)) ≪≫
      (gradedAlgebraPullbackCompIsoOfEq B S hS a bc t h₁).symm :=
  Adjunction.leftAdjointCompIso_assoc_of_eq _ _ _ _ _ _ _ _ _ _
    (gradedAlgebraPushforwardCompIsoOfEq_assoc B S hS a b c ab bc t hab hbc h₁ h₂) _ _ _ _
    (gradedAlgebraPullbackCompIsoOfEq_eq_leftAdjointCompIso B S hS b c bc hbc)
    (gradedAlgebraPullbackCompIsoOfEq_eq_leftAdjointCompIso B S hS a b ab hab)
    (gradedAlgebraPullbackCompIsoOfEq_eq_leftAdjointCompIso B S hS ab c t h₂)
    (gradedAlgebraPullbackCompIsoOfEq_eq_leftAdjointCompIso B S hS a bc t h₁)

/-- The comparisons along morphisms equal to composites satisfy the associativity coherence of
`CategoryTheory.CompIsoCube.IsAssoc`, for the inverse images of sheaves of graded algebras along
morphisms of algebraic spaces. -/
theorem isAssoc_gradedAlgebraPullbackCompIsoOfEq :
    CategoryTheory.CompIsoCube.IsAssoc
      (GA := fun A : AlgebraicSpaces B S hS => SheafOfModules.GradedAlgebra.{u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS A).O))
      (fun {A B'} (f : A ⟶ B') => gradedPull (X := smallEtaleRingedTopos B S hS A)
        (Y := smallEtaleRingedTopos B S hS B') (smallEtaleRingedToposHom B S hS f))
      (fun a b t h => gradedAlgebraPullbackCompIsoOfEq B S hS a b t h) :=
  fun a b c ab bc t hab hbc h₁ h₂ =>
    gradedAlgebraPullbackCompIsoOfEq_assoc B S hS a b c ab bc t hab hbc h₁ h₂

end AlgebraicGeometry.Space

end
