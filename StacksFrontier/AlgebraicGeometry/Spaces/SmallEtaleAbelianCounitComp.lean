module

public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsWithSupportInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAbelianPushforwardComp

/-!
# The counit of the inverse-image/direct-image adjunction at a composite

Let `a : W ⟶ Y` and `b : Y ⟶ X` be morphisms of algebraic spaces over a scheme `S` with
representable underlying morphisms and let `c = a ≫ b`. The direct images compose,
`a_* ⋙ b_* ≅ c_*`, and uniqueness of left adjoints turns that isomorphism into a comparison
`c^{-1} ≅ b^{-1} ⋙ a^{-1}` of inverse images. This file records how the counit of the
adjunction `c^{-1} ⊣ c_*` factors through the counits of the adjunctions of `a` and `b`, and
reads off the two "two out of three" consequences.

## Main definitions

* `CategoryTheory.Adjunction.compLeftAdjointIso` is the comparison of left adjoints attached to
  a factorisation `Ra ⋙ Rb ≅ Rc` of a right adjoint through a composite, for arbitrary
  adjunctions.
* `AlgebraicGeometry.Space.smallEtaleAbelianInverseImageCompIso` is that comparison for the
  inverse image of abelian sheaves on small étale sites: `c^{-1} ≅ b^{-1} ⋙ a^{-1}`.

## Main results

* `CategoryTheory.Adjunction.counit_app_eq_compLeftAdjointIso` and
  `AlgebraicGeometry.Space.counit_app_smallEtaleAbelianInverseImageAdjunction_comp` factor the
  counit of the composite through the counits of the two factors.
* `CategoryTheory.Adjunction.isIso_counit_app_of_comp` and
  `AlgebraicGeometry.Space.isIso_counit_app_smallEtaleAbelianInverseImageAdjunction_comp`:
  invertibility of the two factors' counits gives invertibility of the composite's counit.
* `CategoryTheory.Adjunction.isIso_map_counit_app_of_comp` and
  `AlgebraicGeometry.Space.isIso_map_counit_app_smallEtaleAbelianInverseImageAdjunction_comp`:
  conversely, invertibility of the composite's counit and of the outer factor's counit makes
  the inner factor's counit invertible after applying the outer inverse image.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Adjunction

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {Lb : C ⥤ D} {Rb : D ⥤ C} {La : D ⥤ E} {Ra : E ⥤ D}
  {Lc : C ⥤ E} {Rc : E ⥤ C}

/-- **The comparison of left adjoints attached to a factorisation of a right adjoint through a
composite.** Given adjunctions `Lb ⊣ Rb`, `La ⊣ Ra` and `Lc ⊣ Rc` together with an isomorphism
`Ra ⋙ Rb ≅ Rc`, the left adjoint `Lc` is the composite `Lb ⋙ La`, by uniqueness of left
adjoints. -/
def compLeftAdjointIso (adjb : Lb ⊣ Rb) (adja : La ⊣ Ra) (adjc : Lc ⊣ Rc)
    (μ : Ra ⋙ Rb ≅ Rc) : Lc ≅ Lb ⋙ La :=
  leftAdjointUniq adjc ((adjb.comp adja).ofNatIsoRight μ)

/-- **The counit at a composite factors through the counits of the two factors.** Read through
the comparison `CategoryTheory.Adjunction.compLeftAdjointIso` of left adjoints and the given
factorisation `μ : Ra ⋙ Rb ≅ Rc`, the counit of `Lc ⊣ Rc` at an object is the counit of
`Lb ⊣ Rb` at `Ra`-image, pushed along `La`, followed by the counit of `La ⊣ Ra`. -/
theorem counit_app_eq_compLeftAdjointIso (adjb : Lb ⊣ Rb) (adja : La ⊣ Ra) (adjc : Lc ⊣ Rc)
    (μ : Ra ⋙ Rb ≅ Rc) (X : E) :
    adjc.counit.app X =
      (compLeftAdjointIso adjb adja adjc μ).hom.app (Rc.obj X) ≫
        La.map (Lb.map (μ.inv.app X)) ≫ La.map (adjb.counit.app (Ra.obj X)) ≫
          adja.counit.app X := by
  rw [← leftAdjointUniq_hom_app_counit adjc ((adjb.comp adja).ofNatIsoRight μ) X]
  simp [compLeftAdjointIso]

/-- **Two out of three, forwards.** If the counits of the two factors are invertible at the
relevant objects then so is the counit of the composite. -/
theorem isIso_counit_app_of_comp (adjb : Lb ⊣ Rb) (adja : La ⊣ Ra) (adjc : Lc ⊣ Rc)
    (μ : Ra ⋙ Rb ≅ Rc) (X : E) [IsIso (adjb.counit.app (Ra.obj X))]
    [IsIso (adja.counit.app X)] : IsIso (adjc.counit.app X) := by
  rw [counit_app_eq_compLeftAdjointIso adjb adja adjc μ X]
  infer_instance

/-- **Two out of three, backwards.** If the counit of the composite and the counit of the outer
factor are invertible, then the inner factor's counit becomes invertible after applying the
outer left adjoint `La`. -/
theorem isIso_map_counit_app_of_comp (adjb : Lb ⊣ Rb) (adja : La ⊣ Ra) (adjc : Lc ⊣ Rc)
    (μ : Ra ⋙ Rb ≅ Rc) (X : E) [IsIso (adjc.counit.app X)] [IsIso (adja.counit.app X)] :
    IsIso (La.map (adjb.counit.app (Ra.obj X))) := by
  have h : IsIso ((compLeftAdjointIso adjb adja adjc μ).hom.app (Rc.obj X) ≫
      La.map (Lb.map (μ.inv.app X)) ≫ La.map (adjb.counit.app (Ra.obj X)) ≫
        adja.counit.app X) := by
    rw [← counit_app_eq_compLeftAdjointIso adjb adja adjc μ X]
    infer_instance
  have h₁ : IsIso (La.map (Lb.map (μ.inv.app X)) ≫ La.map (adjb.counit.app (Ra.obj X)) ≫
      adja.counit.app X) :=
    IsIso.of_isIso_comp_left ((compLeftAdjointIso adjb adja adjc μ).hom.app (Rc.obj X)) _
  have h₂ : IsIso (La.map (adjb.counit.app (Ra.obj X)) ≫ adja.counit.app X) :=
    IsIso.of_isIso_comp_left (La.map (Lb.map (μ.inv.app X))) _
  exact IsIso.of_isIso_comp_right (La.map (adjb.counit.app (Ra.obj X))) (adja.counit.app X)

end CategoryTheory.Adjunction

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {W Y X : AlgebraicSpaces B S hS}

/-- **The inverse image of abelian sheaves at a composite.** For morphisms `a : W ⟶ Y` and
`b : Y ⟶ X` of algebraic spaces over `S` with representable underlying morphisms and a
morphism `c : W ⟶ X` with `a ≫ b = c`, the inverse image along `c` is `b^{-1}` followed by
`a^{-1}`.

It is the adjoint comparison of the composition isomorphism
`AlgebraicGeometry.Space.smallEtaleAbelianPushforwardCompIsoOfEq` of direct images, so it is not
an independent choice. -/
def smallEtaleAbelianInverseImageCompIso (a : W ⟶ Y) (b : Y ⟶ X) (c : W ⟶ X)
    (ha : yoneda.relativelyRepresentable a.hom) (hb : yoneda.relativelyRepresentable b.hom)
    (hc : yoneda.relativelyRepresentable c.hom) (h : a ≫ b = c) :
    smallEtaleAbelianInverseImage B S hS c hc ≅
      smallEtaleAbelianInverseImage B S hS b hb ⋙ smallEtaleAbelianInverseImage B S hS a ha :=
  Adjunction.compLeftAdjointIso (smallEtaleAbelianInverseImageAdjunction B S hS b hb)
    (smallEtaleAbelianInverseImageAdjunction B S hS a ha)
    (smallEtaleAbelianInverseImageAdjunction B S hS c hc)
    (smallEtaleAbelianPushforwardCompIsoOfEq B S hS a b c ha hb hc h)

/-- **The counit of the inverse-image/direct-image adjunction at a composite.** For `a ≫ b = c`
the counit `c^{-1}c_*G ⟶ G` is, through the comparison
`AlgebraicGeometry.Space.smallEtaleAbelianInverseImageCompIso` and the composition isomorphism
of direct images, the inverse image along `a` of the counit of `b` at `a_*G`, followed by the
counit of `a` at `G`. -/
theorem counit_app_smallEtaleAbelianInverseImageAdjunction_comp (a : W ⟶ Y) (b : Y ⟶ X)
    (c : W ⟶ X) (ha : yoneda.relativelyRepresentable a.hom)
    (hb : yoneda.relativelyRepresentable b.hom) (hc : yoneda.relativelyRepresentable c.hom)
    (h : a ≫ b = c) (G : Sheaf (SmallEtale.topology B S hS W.1) AddCommGrpCat.{u + 1}) :
    (smallEtaleAbelianInverseImageAdjunction B S hS c hc).counit.app G =
      (smallEtaleAbelianInverseImageCompIso B S hS a b c ha hb hc h).hom.app
          ((smallEtaleAbelianPushforward.{u + 1} B S hS c hc).obj G) ≫
        (smallEtaleAbelianInverseImage B S hS a ha).map
          ((smallEtaleAbelianInverseImage B S hS b hb).map
            ((smallEtaleAbelianPushforwardCompIsoOfEq B S hS a b c ha hb hc h).inv.app G)) ≫
        (smallEtaleAbelianInverseImage B S hS a ha).map
          ((smallEtaleAbelianInverseImageAdjunction B S hS b hb).counit.app
            ((smallEtaleAbelianPushforward.{u + 1} B S hS a ha).obj G)) ≫
        (smallEtaleAbelianInverseImageAdjunction B S hS a ha).counit.app G :=
  Adjunction.counit_app_eq_compLeftAdjointIso _ _ _ _ G

/-- **Two out of three, forwards, for small étale inverse images.** If the counit of `b` at
`a_*G` and the counit of `a` at `G` are invertible, then so is the counit of `c = a ≫ b`
at `G`. -/
theorem isIso_counit_app_smallEtaleAbelianInverseImageAdjunction_comp (a : W ⟶ Y) (b : Y ⟶ X)
    (c : W ⟶ X) (ha : yoneda.relativelyRepresentable a.hom)
    (hb : yoneda.relativelyRepresentable b.hom) (hc : yoneda.relativelyRepresentable c.hom)
    (h : a ≫ b = c) (G : Sheaf (SmallEtale.topology B S hS W.1) AddCommGrpCat.{u + 1})
    (hcb : IsIso ((smallEtaleAbelianInverseImageAdjunction B S hS b hb).counit.app
      ((smallEtaleAbelianPushforward.{u + 1} B S hS a ha).obj G)))
    (hca : IsIso ((smallEtaleAbelianInverseImageAdjunction B S hS a ha).counit.app G)) :
    IsIso ((smallEtaleAbelianInverseImageAdjunction B S hS c hc).counit.app G) :=
  Adjunction.isIso_counit_app_of_comp
    (smallEtaleAbelianInverseImageAdjunction B S hS b hb)
    (smallEtaleAbelianInverseImageAdjunction B S hS a ha)
    (smallEtaleAbelianInverseImageAdjunction B S hS c hc)
    (smallEtaleAbelianPushforwardCompIsoOfEq B S hS a b c ha hb hc h) G

/-- **Two out of three, backwards, for small étale inverse images.** If the counit of
`c = a ≫ b` at `G` and the counit of `a` at `G` are invertible, then the counit of `b` at
`a_*G` is invertible after applying `a^{-1}`. -/
theorem isIso_map_counit_app_smallEtaleAbelianInverseImageAdjunction_comp (a : W ⟶ Y)
    (b : Y ⟶ X) (c : W ⟶ X) (ha : yoneda.relativelyRepresentable a.hom)
    (hb : yoneda.relativelyRepresentable b.hom) (hc : yoneda.relativelyRepresentable c.hom)
    (h : a ≫ b = c) (G : Sheaf (SmallEtale.topology B S hS W.1) AddCommGrpCat.{u + 1})
    (hcc : IsIso ((smallEtaleAbelianInverseImageAdjunction B S hS c hc).counit.app G))
    (hca : IsIso ((smallEtaleAbelianInverseImageAdjunction B S hS a ha).counit.app G)) :
    IsIso ((smallEtaleAbelianInverseImage B S hS a ha).map
      ((smallEtaleAbelianInverseImageAdjunction B S hS b hb).counit.app
        ((smallEtaleAbelianPushforward.{u + 1} B S hS a ha).obj G))) :=
  Adjunction.isIso_map_counit_app_of_comp
    (smallEtaleAbelianInverseImageAdjunction B S hS b hb)
    (smallEtaleAbelianInverseImageAdjunction B S hS a ha)
    (smallEtaleAbelianInverseImageAdjunction B S hS c hc)
    (smallEtaleAbelianPushforwardCompIsoOfEq B S hS a b c ha hb hc h) G

end AlgebraicGeometry.Space

end
