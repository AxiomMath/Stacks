module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.DerivedSystem

/-!
# The compositor of derived functors is natural in each of its two functors

`CategoryTheory.derivedCompIso` identifies the derived functor of a composite of exact functors
with the composite of their derived functors. This file proves that the identification is
natural in each factor: a transformation of the outer factor, respectively of the inner one,
induces the same map on either side of the comparison.

These are the two squares that carry a degreewise statement about a conjugated functor
`F ⋙ G ⋙ H` past the comparison, which is what the derived form of the projection formula of
Stacks 0D9E needs: the endofunctor `g_{n!}ℤ ⊗_ℤ -` of abelian sheaves is a tensor product of
sheaves of modules conjugated by the equivalence with modules over the constant sheaf `ℤ`, and a
map `g_{n!}ℤ ⟶ g_{m!}ℤ` acts in the middle of that conjugation.

## Main results

* `CategoryTheory.derivedCompIso_refl_hom_app_Q`: the value of the compositor at the identity
  comparison, on the image of a complex.
* `CategoryTheory.derivedCompIso_refl_hom_whiskerLeft`: naturality in the outer factor.
* `CategoryTheory.derivedCompIso_refl_hom_whiskerRight`: naturality in the inner factor.

## References

* [Stacks Project, Tag 0D9E](https://stacks.math.columbia.edu/tag/0D9E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃ w₁ w₂ w₃

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  {D : Type u₃} [Category.{v₃} D] [Abelian D] [HasDerivedCategory.{w₃} D]

section

variable (F : A ⥤ B) (G : B ⥤ D) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- **The compositor of derived functors at the identity comparison, on the image of a
complex.** The complex-level comparison is the identity, so only the two factorisations of the
derived functors remain. -/
theorem derivedCompIso_refl_hom_app_Q (X : CochainComplex A ℤ) :
    (derivedCompIso F G (F ⋙ G) (Iso.refl _)).hom.app (DerivedCategory.Q.obj X) =
      (F ⋙ G).mapDerivedCategoryFactors.hom.app X ≫
        G.mapDerivedCategoryFactors.inv.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫
          G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app X) := by
  have hrefl : (NatIso.mapHomologicalComplex (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).hom.app X =
      𝟙 _ := HomologicalComplex.hom_ext _ _ fun _ => rfl
  rw [derivedCompIso_hom_app_Q, hrefl, CategoryTheory.Functor.map_id]
  exact congrArg (fun k => (F ⋙ G).mapDerivedCategoryFactors.hom.app X ≫ k)
    (Category.id_comp (G.mapDerivedCategoryFactors.inv.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app X)))

end

section WhiskerLeft

variable (F : A ⥤ B) (G G' : B ⥤ D) [F.Additive] [G.Additive] [G'.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']

omit [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G'] in
/-- The transformation of complexes induced by whiskering on the left is the one induced by the
transformation itself, at the complex obtained by applying the inner factor degreewise. -/
theorem mapHomologicalComplex_whiskerLeft_app (α : G ⟶ G') (X : CochainComplex A ℤ) :
    (NatTrans.mapHomologicalComplex (Functor.whiskerLeft F α) (ComplexShape.up ℤ)).app X =
      (NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) :=
  HomologicalComplex.hom_ext _ _ fun _ => rfl

/-- **The compositor of derived functors is natural in the outer factor.** A transformation
`α : G ⟶ G'` of the outer factor induces, on the one hand, the derived transformation of
`F ⋙ α` and, on the other, the derived transformation of `α` whiskered with the derived functor
of `F`; the compositor carries one to the other. -/
theorem derivedCompIso_refl_hom_whiskerLeft (α : G ⟶ G') :
    derivedNatTrans (F ⋙ G) (F ⋙ G') (Functor.whiskerLeft F α) ≫
        (derivedCompIso F G' (F ⋙ G') (Iso.refl _)).hom =
      (derivedCompIso F G (F ⋙ G) (Iso.refl _)).hom ≫
        Functor.whiskerLeft F.mapDerivedCategory (derivedNatTrans G G' α) := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) fun X => ?_
  have hnat : G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app X) ≫
        (derivedNatTrans G G' α).app
          (F.mapDerivedCategory.obj (DerivedCategory.Q.obj X)) =
      (derivedNatTrans G G' α).app
          (DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X)) ≫
        G'.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app X) :=
    (derivedNatTrans G G' α).naturality (F.mapDerivedCategoryFactors.inv.app X)
  have hmid : G.mapDerivedCategoryFactors.inv.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫
        (derivedNatTrans G G' α).app
          (DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X)) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X)) ≫
        G'.mapDerivedCategoryFactors.inv.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) := by
    rw [derivedNatTrans_app G G' α ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X),
      ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  rw [NatTrans.comp_app, NatTrans.comp_app, derivedNatTrans_app, derivedCompIso_refl_hom_app_Q,
    derivedCompIso_refl_hom_app_Q, Functor.whiskerLeft_app,
    mapHomologicalComplex_whiskerLeft_app]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_app_assoc, hnat, reassoc_of% hmid]

end WhiskerLeft

section WhiskerRight

variable (F F' : A ⥤ B) (G : B ⥤ D) [F.Additive] [F'.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

omit [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
  [PreservesFiniteLimits G] [PreservesFiniteColimits G] in
/-- The transformation of complexes induced by whiskering on the right is the outer factor,
applied degreewise, of the transformation itself. -/
theorem mapHomologicalComplex_whiskerRight_app (α : F ⟶ F') (X : CochainComplex A ℤ) :
    (NatTrans.mapHomologicalComplex (Functor.whiskerRight α G) (ComplexShape.up ℤ)).app X =
      (G.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app X) :=
  HomologicalComplex.hom_ext _ _ fun _ => rfl

/-- **The compositor of derived functors is natural in the inner factor.** -/
theorem derivedCompIso_refl_hom_whiskerRight (α : F ⟶ F') :
    derivedNatTrans (F ⋙ G) (F' ⋙ G) (Functor.whiskerRight α G) ≫
        (derivedCompIso F' G (F' ⋙ G) (Iso.refl _)).hom =
      (derivedCompIso F G (F ⋙ G) (Iso.refl _)).hom ≫
        Functor.whiskerRight (derivedNatTrans F F' α) G.mapDerivedCategory := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) fun X => ?_
  have hfac : G.mapDerivedCategoryFactors.inv.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫
        G.mapDerivedCategory.map (DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app X)) =
      DerivedCategory.Q.map ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map
            ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app X)) ≫
        G.mapDerivedCategoryFactors.inv.app
          ((F'.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) :=
    (G.mapDerivedCategoryFactors.inv.naturality
      ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app X)).symm
  rw [NatTrans.comp_app, NatTrans.comp_app, derivedNatTrans_app, derivedCompIso_refl_hom_app_Q,
    derivedCompIso_refl_hom_app_Q, Functor.whiskerRight_app, derivedNatTrans_app,
    mapHomologicalComplex_whiskerRight_app]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_app_assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app_assoc,
    CategoryTheory.Functor.map_comp, reassoc_of% hfac]

end WhiskerRight

end CategoryTheory

end
