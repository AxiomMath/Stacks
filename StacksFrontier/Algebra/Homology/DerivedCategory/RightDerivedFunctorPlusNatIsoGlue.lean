module

public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionComparisonAssoc
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusComparisons
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# The invariance comparison `RF ≅ RG` is functorial, and natural in the composition comparison

`CategoryTheory.Functor.rightDerivedFunctorPlusNatIso` turns an isomorphism `e : F ≅ G` of
additive functors `𝒜 ⥤ ℬ` into an isomorphism `RF ≅ RG` of their bounded below right derived
functors.  This module proves that this construction preserves identities, composites and
inverses, and that it is compatible with the composition comparison of [Stacks, Tag 05T2].

## Main results

All in the namespace `CategoryTheory.Functor`.

* `rightDerivedFunctorPlusNatIso_refl`, `rightDerivedFunctorPlusNatIso_trans`,
  `rightDerivedFunctorPlusNatIso_symm` — the construction takes the identity to the identity,
  a composite to the composite and an inverse to the inverse.
* `rightDerivedFunctorPlusComp_natIso_whiskerRight` — **the comparison of [Stacks, Tag 05T2] is
  natural in its first factor**: for `e : F ≅ F'` of functors `𝒜 ⥤ ℬ` and `H : ℬ ⥤ 𝒞`, the
  invariance comparison for `e` whiskered by `H`, followed by the composition comparison for
  `(F', H)`, is the composition comparison for `(F, H)` followed by `RH` of the invariance
  comparison for `e`.
* `unit_comp_rightDerivedFunctorPlusComp_app` — the factorization of the composition comparison
  with the coherence isomorphism cancelled.
* `rightDerivedFunctorPlusNatIso_hom_fac_app`, `rightDerivedFunctorPlusNatIso_inv_fac_app` —
  the factorizations characterising the invariance comparison.

## Implementation notes

The identities in `D⁺(𝒞)` are proved in term mode: the source of the two sides of
`rightDerivedFunctorPlusComp_natIso_whiskerRight` has the two spellings
`(F ⋙ H).mapHomotopyCategoryPlus.obj K` and
`H.mapHomotopyCategoryPlus.obj (F.mapHomotopyCategoryPlus.obj K)`, and `rw` re-checks the goal
it builds at a transparency that will not unfold `DerivedCategory.Plus.Qh`.

## References

* [Stacks, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2), the comparison transformation
* [Stacks, Tag 015M](https://stacks.math.columbia.edu/tag/015M), when it is an isomorphism
-/

@[expose] public section

universe w w₁ w₂ v v₁ v₂ u u₁ u₂

open CategoryTheory Limits

namespace CategoryTheory.Functor

-- Pointwise right derivability is found from `EnoughInjectives` before any other instance.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### The action on bounded below homotopy categories -/

section Degreewise

variable {A : Type u} {B : Type u₁} {C : Type u₂}
  [Category.{v} A] [Category.{v₁} B] [Category.{v₂} C]
  [Preadditive A] [Preadditive B] [Preadditive C]

/-- The action on bounded below homotopy categories of the identity isomorphism is the
identity. -/
lemma mapHomotopyCategoryPlusNatIso_refl_hom_app (F : A ⥤ B) [F.Additive]
    (K : HomotopyCategory.Plus A) :
    (mapHomotopyCategoryPlusNatIso (Iso.refl F)).hom.app K =
      𝟙 (F.mapHomotopyCategoryPlus.obj K) := by
  apply (HomotopyCategory.Plus.ι B).map_injective
  change (NatTrans.mapHomotopyCategory (Iso.refl F).hom (ComplexShape.up ℤ)).app K.obj = _
  rw [Iso.refl_hom, NatTrans.mapHomotopyCategory_id]
  rfl

/-- The action on bounded below homotopy categories of a composite of isomorphisms is the
composite of the actions. -/
lemma mapHomotopyCategoryPlusNatIso_trans_hom_app {F G H : A ⥤ B} [F.Additive] [G.Additive]
    [H.Additive] (e : F ≅ G) (e' : G ≅ H) (K : HomotopyCategory.Plus A) :
    (mapHomotopyCategoryPlusNatIso (e ≪≫ e')).hom.app K =
      (mapHomotopyCategoryPlusNatIso e).hom.app K ≫
        (mapHomotopyCategoryPlusNatIso e').hom.app K := by
  apply (HomotopyCategory.Plus.ι B).map_injective
  change (NatTrans.mapHomotopyCategory (e ≪≫ e').hom (ComplexShape.up ℤ)).app K.obj = _
  rw [Iso.trans_hom, NatTrans.mapHomotopyCategory_comp]
  rfl

/-- The action on bounded below homotopy categories of the inverse of an isomorphism is the
inverse of the action. -/
lemma mapHomotopyCategoryPlusNatIso_symm_hom_app {F G : A ⥤ B} [F.Additive] [G.Additive]
    (e : F ≅ G) (K : HomotopyCategory.Plus A) :
    (mapHomotopyCategoryPlusNatIso e.symm).hom.app K =
      (mapHomotopyCategoryPlusNatIso e).inv.app K := rfl

/-- **The action on bounded below homotopy categories is compatible with whiskering.**  The
induced action of `e` whiskered by `H` is `H` applied to the induced action of `e`. -/
lemma mapHomotopyCategoryPlusNatIso_isoWhiskerRight_hom_app {F G : A ⥤ B} [F.Additive]
    [G.Additive] (e : F ≅ G) (H : B ⥤ C) [H.Additive] (K : HomotopyCategory.Plus A) :
    (mapHomotopyCategoryPlusNatIso (Functor.isoWhiskerRight e H)).hom.app K =
      H.mapHomotopyCategoryPlus.map ((mapHomotopyCategoryPlusNatIso e).hom.app K) := rfl

end Degreewise

/-! ### The factorizations characterising the two comparisons -/

section Factorizations

variable {A : Type u} {B : Type u₁} {C : Type u₂}
  [Category.{v} A] [Category.{v₁} B] [Category.{v₂} C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w₁} B] [HasDerivedCategory.{w₂} C]
  [EnoughInjectives A]

/-- **The factorization characterising `rightDerivedFunctorPlusNatIso`**: composed with the
derived-functor unit of `RF` at a bounded below complex `K`, its forward half is the degreewise
action of `e` followed by the unit of `RG`. -/
lemma rightDerivedFunctorPlusNatIso_hom_fac_app {F G : A ⥤ B} [F.Additive] [G.Additive]
    (e : F ≅ G) (K : HomotopyCategory.Plus A) :
    F.rightDerivedFunctorPlusUnith.app K ≫
        (rightDerivedFunctorPlusNatIso e).hom.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusNatIso e).hom.app K) ≫
        G.rightDerivedFunctorPlusUnith.app K :=
  rightDerivedNatTrans_app F.rightDerivedFunctorPlus G.rightDerivedFunctorPlus
    F.rightDerivedFunctorPlusUnith G.rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso A)
    (Functor.isoWhiskerRight (mapHomotopyCategoryPlusNatIso e) DerivedCategory.Plus.Qh).hom K

/-- The inverse half of `rightDerivedFunctorPlusNatIso_hom_fac_app`. -/
lemma rightDerivedFunctorPlusNatIso_inv_fac_app {F G : A ⥤ B} [F.Additive] [G.Additive]
    (e : F ≅ G) (K : HomotopyCategory.Plus A) :
    G.rightDerivedFunctorPlusUnith.app K ≫
        (rightDerivedFunctorPlusNatIso e).inv.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusNatIso e).inv.app K) ≫
        F.rightDerivedFunctorPlusUnith.app K :=
  rightDerivedNatTrans_app G.rightDerivedFunctorPlus F.rightDerivedFunctorPlus
    G.rightDerivedFunctorPlusUnith F.rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso A)
    (Functor.isoWhiskerRight (mapHomotopyCategoryPlusNatIso e) DerivedCategory.Plus.Qh).inv K

/-- Two natural transformations out of `RF` are equal when they agree after the derived-functor
unit of `RF` at every bounded below complex. -/
private lemma rightDerivedFunctorPlus_hom_ext {F : A ⥤ B} [F.Additive]
    {G : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B} {γ₁ γ₂ : F.rightDerivedFunctorPlus ⟶ G}
    (h : ∀ K : HomotopyCategory.Plus A, F.rightDerivedFunctorPlusUnith.app K ≫
      γ₁.app (DerivedCategory.Plus.Qh.obj K) =
        F.rightDerivedFunctorPlusUnith.app K ≫ γ₂.app (DerivedCategory.Plus.Qh.obj K)) :
    γ₁ = γ₂ :=
  Functor.rightDerived_ext F.rightDerivedFunctorPlus
    F.rightDerivedFunctorPlusUnith (HomotopyCategory.Plus.quasiIso A) _ _ _
    (NatTrans.ext (funext h))

variable [EnoughInjectives B]

/-- **The factorization of the comparison of [Stacks, Tag 05T2], with its coherence isomorphism
cancelled**: composed with the derived-functor unit of `R(H ∘ F)` at `K`, it is the unit of `RH`
at `F(K)` followed by `RH` of the unit of `RF` at `K`. -/
lemma unit_comp_rightDerivedFunctorPlusComp_app (F : A ⥤ B) (H : B ⥤ C) [F.Additive]
    [H.Additive] (K : HomotopyCategory.Plus A) :
    (F ⋙ H).rightDerivedFunctorPlusUnith.app K ≫
        (rightDerivedFunctorPlusComp F H).app (DerivedCategory.Plus.Qh.obj K) =
      H.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj K) ≫
        H.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app K) :=
  (rightDerivedFunctorPlusComp_fac_app F H K).trans
    (qhMapCompIsoReflInv_comp F H K
      (H.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj K) ≫
        H.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app K)))

end Factorizations

/-! ### The invariance comparison is functorial -/

section Functoriality

variable {A : Type u} {B : Type u₁}
  [Category.{v} A] [Category.{v₁} B] [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w₁} B] [EnoughInjectives A]

/-- **The invariance comparison of the identity isomorphism is the identity.** -/
theorem rightDerivedFunctorPlusNatIso_refl (F : A ⥤ B) [F.Additive] :
    rightDerivedFunctorPlusNatIso (Iso.refl F) = Iso.refl F.rightDerivedFunctorPlus :=
  Iso.ext (rightDerivedFunctorPlus_hom_ext fun K ↦ by
    refine (rightDerivedFunctorPlusNatIso_hom_fac_app (Iso.refl F) K).trans ?_
    rw [mapHomotopyCategoryPlusNatIso_refl_hom_app, CategoryTheory.Functor.map_id,
      Category.id_comp]
    exact (Category.comp_id _).symm)

/-- The composite of the derived-functor unit of `RF` with the two invariance comparisons in
succession. -/
private lemma trans_fac_app {F G H : A ⥤ B} [F.Additive] [G.Additive] [H.Additive] (e : F ≅ G)
    (e' : G ≅ H) (K : HomotopyCategory.Plus A) :
    F.rightDerivedFunctorPlusUnith.app K ≫
        (rightDerivedFunctorPlusNatIso e).hom.app (DerivedCategory.Plus.Qh.obj K) ≫
          (rightDerivedFunctorPlusNatIso e').hom.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusNatIso e).hom.app K) ≫
        DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusNatIso e').hom.app K) ≫
          H.rightDerivedFunctorPlusUnith.app K := by
  rw [← Category.assoc, rightDerivedFunctorPlusNatIso_hom_fac_app e K, Category.assoc,
    rightDerivedFunctorPlusNatIso_hom_fac_app e' K]

/-- The composite of the derived-functor unit of `RF` with the invariance comparison of the
composite isomorphism. -/
private lemma trans_fac_app' {F G H : A ⥤ B} [F.Additive] [G.Additive] [H.Additive] (e : F ≅ G)
    (e' : G ≅ H) (K : HomotopyCategory.Plus A) :
    F.rightDerivedFunctorPlusUnith.app K ≫
        (rightDerivedFunctorPlusNatIso (e ≪≫ e')).hom.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusNatIso e).hom.app K) ≫
        DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusNatIso e').hom.app K) ≫
          H.rightDerivedFunctorPlusUnith.app K := by
  rw [rightDerivedFunctorPlusNatIso_hom_fac_app (e ≪≫ e') K,
    mapHomotopyCategoryPlusNatIso_trans_hom_app, CategoryTheory.Functor.map_comp,
    Category.assoc]

/-- **The invariance comparison of a composite is the composite of the comparisons.** -/
theorem rightDerivedFunctorPlusNatIso_trans {F G H : A ⥤ B} [F.Additive] [G.Additive]
    [H.Additive] (e : F ≅ G) (e' : G ≅ H) :
    rightDerivedFunctorPlusNatIso (e ≪≫ e') =
      rightDerivedFunctorPlusNatIso e ≪≫ rightDerivedFunctorPlusNatIso e' :=
  Iso.ext (rightDerivedFunctorPlus_hom_ext fun K ↦
    (trans_fac_app' e e' K).trans (trans_fac_app e e' K).symm)

/-- **The invariance comparison of an inverse is the inverse of the comparison.** -/
theorem rightDerivedFunctorPlusNatIso_symm {F G : A ⥤ B} [F.Additive] [G.Additive] (e : F ≅ G) :
    rightDerivedFunctorPlusNatIso e.symm = (rightDerivedFunctorPlusNatIso e).symm :=
  Iso.ext (rightDerivedFunctorPlus_hom_ext fun K ↦
    (rightDerivedFunctorPlusNatIso_hom_fac_app e.symm K).trans
      (rightDerivedFunctorPlusNatIso_inv_fac_app e K).symm)

end Functoriality

/-! ### Naturality of the composition comparison in its first factor -/

section WhiskerRight

variable {A : Type u} {B : Type u₁} {C : Type u₂}
  [Category.{v} A] [Category.{v₁} B] [Category.{v₂} C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w₁} B] [HasDerivedCategory.{w₂} C]
  [EnoughInjectives A] [EnoughInjectives B]
  {F F' : A ⥤ B} [F.Additive] [F'.Additive] (e : F ≅ F') (H : B ⥤ C) [H.Additive]

/-- The left hand route of `rightDerivedFunctorPlusComp_natIso_whiskerRight`, computed after the
derived-functor unit of `R(H ∘ F)`. -/
private lemma natIsoWhiskerRight_leftRoute (K : HomotopyCategory.Plus A) :
    (F ⋙ H).rightDerivedFunctorPlusUnith.app K ≫
        (rightDerivedFunctorPlusNatIso (Functor.isoWhiskerRight e H)).hom.app
            (DerivedCategory.Plus.Qh.obj K) ≫
          (rightDerivedFunctorPlusComp F' H).app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map
          (H.mapHomotopyCategoryPlus.map ((mapHomotopyCategoryPlusNatIso e).hom.app K)) ≫
        H.rightDerivedFunctorPlusUnith.app (F'.mapHomotopyCategoryPlus.obj K) ≫
          H.rightDerivedFunctorPlus.map (F'.rightDerivedFunctorPlusUnith.app K) :=
  (Category.assoc _ _ _).symm.trans
    ((CategoryTheory.eq_whisker
          ((rightDerivedFunctorPlusNatIso_hom_fac_app (Functor.isoWhiskerRight e H) K).trans
            (CategoryTheory.eq_whisker
              (congrArg DerivedCategory.Plus.Qh.map
                (mapHomotopyCategoryPlusNatIso_isoWhiskerRight_hom_app e H K))
              ((F' ⋙ H).rightDerivedFunctorPlusUnith.app K)))
          ((rightDerivedFunctorPlusComp F' H).app (DerivedCategory.Plus.Qh.obj K))).trans
      ((Category.assoc _ _ _).trans
        (CategoryTheory.whisker_eq _ (unit_comp_rightDerivedFunctorPlusComp_app F' H K))))

/-- The right hand route of `rightDerivedFunctorPlusComp_natIso_whiskerRight`, computed after
the derived-functor unit of `R(H ∘ F)`. -/
private lemma natIsoWhiskerRight_rightRoute (K : HomotopyCategory.Plus A) :
    (F ⋙ H).rightDerivedFunctorPlusUnith.app K ≫
        (rightDerivedFunctorPlusComp F H).app (DerivedCategory.Plus.Qh.obj K) ≫
          H.rightDerivedFunctorPlus.map
            ((rightDerivedFunctorPlusNatIso e).hom.app (DerivedCategory.Plus.Qh.obj K)) =
      DerivedCategory.Plus.Qh.map
          (H.mapHomotopyCategoryPlus.map ((mapHomotopyCategoryPlusNatIso e).hom.app K)) ≫
        H.rightDerivedFunctorPlusUnith.app (F'.mapHomotopyCategoryPlus.obj K) ≫
          H.rightDerivedFunctorPlus.map (F'.rightDerivedFunctorPlusUnith.app K) :=
  have hmap : H.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app K) ≫
      H.rightDerivedFunctorPlus.map
        ((rightDerivedFunctorPlusNatIso e).hom.app (DerivedCategory.Plus.Qh.obj K)) =
      H.rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusNatIso e).hom.app K)) ≫
        H.rightDerivedFunctorPlus.map (F'.rightDerivedFunctorPlusUnith.app K) := by
    rw [← CategoryTheory.Functor.map_comp, rightDerivedFunctorPlusNatIso_hom_fac_app e K,
      CategoryTheory.Functor.map_comp]
  have hnat : H.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj K) ≫
      H.rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusNatIso e).hom.app K)) =
      DerivedCategory.Plus.Qh.map
          (H.mapHomotopyCategoryPlus.map ((mapHomotopyCategoryPlusNatIso e).hom.app K)) ≫
        H.rightDerivedFunctorPlusUnith.app (F'.mapHomotopyCategoryPlus.obj K) :=
    (H.rightDerivedFunctorPlusUnith.naturality
      ((mapHomotopyCategoryPlusNatIso e).hom.app K)).symm
  (Category.assoc _ _ _).symm.trans
    ((CategoryTheory.eq_whisker (unit_comp_rightDerivedFunctorPlusComp_app F H K)
          (H.rightDerivedFunctorPlus.map
            ((rightDerivedFunctorPlusNatIso e).hom.app
              (DerivedCategory.Plus.Qh.obj K)))).trans
      ((Category.assoc _ _ _).trans
        ((CategoryTheory.whisker_eq _ hmap).trans
          ((Category.assoc _ _ _).symm.trans
            ((CategoryTheory.eq_whisker hnat
                  (H.rightDerivedFunctorPlus.map
                    (F'.rightDerivedFunctorPlusUnith.app K))).trans
              (Category.assoc _ _ _))))))

/-- **The comparison of [Stacks, Tag 05T2] is natural in its first factor.**  For an isomorphism
`e : F ≅ F'` of additive functors `𝒜 ⥤ ℬ` and an additive `H : ℬ ⥤ 𝒞`, the invariance
comparison for `e` whiskered by `H`, followed by the composition comparison for `(F', H)`, is
the composition comparison for `(F, H)` followed by `RH` of the invariance comparison for `e`. -/
theorem rightDerivedFunctorPlusComp_natIso_whiskerRight :
    (rightDerivedFunctorPlusNatIso (Functor.isoWhiskerRight e H)).hom ≫
        rightDerivedFunctorPlusComp F' H =
      rightDerivedFunctorPlusComp F H ≫
        Functor.whiskerRight (rightDerivedFunctorPlusNatIso e).hom
          H.rightDerivedFunctorPlus :=
  rightDerivedFunctorPlus_hom_ext fun K ↦
    (natIsoWhiskerRight_leftRoute e H K).trans (natIsoWhiskerRight_rightRoute e H K).symm

/-- `rightDerivedFunctorPlusComp_natIso_whiskerRight` read at an object of `D⁺(𝒜)`. -/
theorem rightDerivedFunctorPlusComp_natIso_whiskerRight_app (K : DerivedCategory.Plus A) :
    (rightDerivedFunctorPlusNatIso (Functor.isoWhiskerRight e H)).hom.app K ≫
        (rightDerivedFunctorPlusComp F' H).app K =
      (rightDerivedFunctorPlusComp F H).app K ≫
        H.rightDerivedFunctorPlus.map ((rightDerivedFunctorPlusNatIso e).hom.app K) :=
  NatTrans.congr_app (rightDerivedFunctorPlusComp_natIso_whiskerRight e H) K

end WhiskerRight

end CategoryTheory.Functor

end
