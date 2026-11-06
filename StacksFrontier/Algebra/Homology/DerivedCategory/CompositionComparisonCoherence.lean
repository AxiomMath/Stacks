module

public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionComparisonIso
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.HomotopyCategory.InducedCommShift
public import StacksFrontier.CategoryTheory.Triangulated.ConnectingMorphismNatTrans
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionComparisonAssoc
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusNatIsoGlue

/-!
# Coherence of the composition comparison of right derived functors

For additive functors `F : 𝒜 ⥤ ℬ` and `G : ℬ ⥤ 𝒞` let `t : R(G ∘ F) ⟶ RF ⋙ RG` be the canonical
comparison of [Stacks, Tag 05T2] on bounded below derived categories. This file records three
properties of `t` used to paste derived comparison maps:

* `t` is compatible with the commutation of both sides with the shift: it is the descent along
  the unit of `R(G ∘ F)` of a transformation compatible with the shift;
* `t` is natural in its second factor, with respect to the invariance comparison
  `CategoryTheory.Functor.rightDerivedFunctorPlusNatIso` (the first factor is
  `CategoryTheory.Functor.rightDerivedFunctorPlusComp_natIso_whiskerRight`);
* the comparisons attached to an associative system of isomorphisms of underived functors paste.

## Main results

* `CategoryTheory.Functor.natTransCommShift_rightDerivedFunctorPlusComp`.
* `CategoryTheory.Functor.rightDerivedFunctorPlusComp_natIso_whiskerLeft`.
* `CategoryTheory.Functor.rightDerivedFunctorPlusComp_paste`.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
  [EnoughInjectives C] [EnoughInjectives D]

attribute [local instance] commShiftRightDerivedFunctorPlus
  natTransCommShiftRightDerivedFunctorPlusUnit

/-- The transformation `G(F(K)) ⟶ RG(F(K)) ⟶ RG(RF(K))` commutes with the shift. -/
theorem natTransCommShift_rightComparisonUnit :
    NatTrans.CommShift (rightComparisonUnit F G) ℤ := by
  have e : rightComparisonUnit F G =
      Functor.whiskerRight (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).inv
          DerivedCategory.Plus.Qh ≫ (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft F.mapHomotopyCategoryPlus G.rightDerivedFunctorPlusUnith ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight F.rightDerivedFunctorPlusUnith G.rightDerivedFunctorPlus ≫
        (Functor.associator _ _ _).hom := by
    ext K
    simp [rightComparisonUnit]
  rw [e]
  infer_instance

/-- **The comparison `t : R(G ∘ F) ⟶ RF ⋙ RG` commutes with the shift.** -/
theorem natTransCommShift_rightDerivedFunctorPlusComp :
    NatTrans.CommShift (rightDerivedFunctorPlusComp F G) ℤ := by
  have := natTransCommShift_rightComparisonUnit F G
  exact Stacks.Triangulated.natTransCommShift_rightDerivedDesc _ _
    (HomotopyCategory.Plus.quasiIso C) ℤ _ _

section Coherence

variable {C D E E' : Type*} [Category* C] [Category* D] [Category* E] [Category* E']
  [Abelian C] [Abelian D] [Abelian E] [Abelian E']
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory E']
  [EnoughInjectives C] [EnoughInjectives D] [EnoughInjectives E]

omit [EnoughInjectives E] in
/-- **The comparison of [Stacks, Tag 05T2] is natural in its second factor.** For an isomorphism
`e : H ≅ H'` of additive functors `ℬ ⥤ 𝒞`, the invariance comparison for `F` whiskered with `e`,
followed by the composition comparison for `(F, H')`, is the composition comparison for
`(F, H)` followed by `RF` whiskered with the invariance comparison for `e`. -/
theorem rightDerivedFunctorPlusComp_natIso_whiskerLeft (F : C ⥤ D) {H H' : D ⥤ E}
    [F.Additive] [H.Additive] [H'.Additive] (e : H ≅ H') :
    (rightDerivedFunctorPlusNatIso (Functor.isoWhiskerLeft F e)).hom ≫
        rightDerivedFunctorPlusComp F H' =
      rightDerivedFunctorPlusComp F H ≫
        Functor.whiskerLeft F.rightDerivedFunctorPlus (rightDerivedFunctorPlusNatIso e).hom := by
  refine (F ⋙ H).rightDerivedFunctorPlus.rightDerived_ext (F ⋙ H).rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso C) _ _ _ (NatTrans.ext (funext fun K ↦ ?_))
  have hl : (F ⋙ H).rightDerivedFunctorPlusUnith.app K ≫
      (rightDerivedFunctorPlusNatIso (Functor.isoWhiskerLeft F e)).hom.app
          (DerivedCategory.Plus.Qh.obj K) ≫
        (rightDerivedFunctorPlusComp F H').app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusNatIso e).hom.app
          (F.mapHomotopyCategoryPlus.obj K)) ≫
        H'.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj K) ≫
          H'.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app K) :=
    (Category.assoc _ _ _).symm.trans
      ((CategoryTheory.eq_whisker
          (rightDerivedFunctorPlusNatIso_hom_fac_app (Functor.isoWhiskerLeft F e) K)
          ((rightDerivedFunctorPlusComp F H').app (DerivedCategory.Plus.Qh.obj K))).trans
        ((Category.assoc _ _ _).trans
          (CategoryTheory.whisker_eq _ (unit_comp_rightDerivedFunctorPlusComp_app F H' K))))
  have hr : (F ⋙ H).rightDerivedFunctorPlusUnith.app K ≫
      (rightDerivedFunctorPlusComp F H).app (DerivedCategory.Plus.Qh.obj K) ≫
        (rightDerivedFunctorPlusNatIso e).hom.app
          (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj K)) =
      DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusNatIso e).hom.app
          (F.mapHomotopyCategoryPlus.obj K)) ≫
        H'.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj K) ≫
          H'.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app K) :=
    (Category.assoc _ _ _).symm.trans
      ((CategoryTheory.eq_whisker (unit_comp_rightDerivedFunctorPlusComp_app F H K)
          ((rightDerivedFunctorPlusNatIso e).hom.app
            (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj K)))).trans
        ((Category.assoc _ _ _).trans
          ((CategoryTheory.whisker_eq _
              ((rightDerivedFunctorPlusNatIso e).hom.naturality
                (F.rightDerivedFunctorPlusUnith.app K))).trans
            ((Category.assoc _ _ _).symm.trans
              ((CategoryTheory.eq_whisker
                  (rightDerivedFunctorPlusNatIso_hom_fac_app e (F.mapHomotopyCategoryPlus.obj K))
                  (H'.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app K))).trans
                (Category.assoc _ _ _))))))
  exact hl.trans hr.symm

/-- **Pasting of composition comparisons.** Let `F₁ : 𝒜 ⥤ ℬ`, `G₁ : ℬ ⥤ 𝒞`, `H₁ : 𝒞 ⥤ 𝒟`,
and let `a : F₂ ≅ F₁ ⋙ G₁`, `b : F₃ ≅ F₂ ⋙ H₁`, `c : F₃ ≅ F₁ ⋙ G₂` and `d : G₁ ⋙ H₁ ≅ G₂` be
isomorphisms of additive functors with `b ≫ a H₁ = c ≫ F₁ d⁻¹`. Then the derived comparisons
`RF₃ ⟶ RF₁ ⋙ RG₁ ⋙ RH₁` obtained by taking `F₃` apart along `b` and then `a`, or along `c` and
then `d`, agree. -/
theorem rightDerivedFunctorPlusComp_paste {F₁ : C ⥤ D} {G₁ : D ⥤ E} {H₁ : E ⥤ E'}
    {F₂ : C ⥤ E} {F₃ : C ⥤ E'} {G₂ : D ⥤ E'} [F₁.Additive] [G₁.Additive] [H₁.Additive]
    [F₂.Additive] [F₃.Additive] [G₂.Additive]
    (a : F₂ ≅ F₁ ⋙ G₁) (b : F₃ ≅ F₂ ⋙ H₁) (c : F₃ ≅ F₁ ⋙ G₂) (d : G₁ ⋙ H₁ ≅ G₂)
    [EnoughInjectives E']
    (h : b.hom ≫ Functor.whiskerRight a.hom H₁ = c.hom ≫ Functor.whiskerLeft F₁ d.inv) :
    (rightDerivedFunctorPlusNatIso b).hom ≫ rightDerivedFunctorPlusComp F₂ H₁ ≫
        Functor.whiskerRight ((rightDerivedFunctorPlusNatIso a).hom ≫
          rightDerivedFunctorPlusComp F₁ G₁) H₁.rightDerivedFunctorPlus =
      (rightDerivedFunctorPlusNatIso c).hom ≫ rightDerivedFunctorPlusComp F₁ G₂ ≫
        Functor.whiskerLeft F₁.rightDerivedFunctorPlus
          ((rightDerivedFunctorPlusNatIso d).inv ≫ rightDerivedFunctorPlusComp G₁ H₁) := by
  have h₁ := rightDerivedFunctorPlusComp_natIso_whiskerRight a H₁
  have h₂ := rightDerivedFunctorPlusComp_assoc F₁ G₁ H₁
  have h₃ := rightDerivedFunctorPlusComp_natIso_whiskerLeft F₁ d.symm
  have h₄ : b ≪≫ Functor.isoWhiskerRight a H₁ = c ≪≫ Functor.isoWhiskerLeft F₁ d.symm :=
    Iso.ext h
  have h₅ := congrArg Iso.hom (congrArg rightDerivedFunctorPlusNatIso h₄)
  rw [rightDerivedFunctorPlusNatIso_trans, rightDerivedFunctorPlusNatIso_trans] at h₅
  rw [rightDerivedFunctorPlusNatIso_symm] at h₃
  simp only [Iso.trans_hom] at h₅
  simp only [Iso.symm_hom] at h₃
  rw [Functor.whiskerRight_comp, Functor.whiskerLeft_comp, ← reassoc_of% h₁, h₂,
    reassoc_of% h₅, reassoc_of% h₃]

end Coherence

end CategoryTheory.Functor
