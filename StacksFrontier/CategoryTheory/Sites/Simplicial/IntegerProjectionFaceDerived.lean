module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerProjectionFaceLeg
public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerProjectionRealization
public import StacksFrontier.CategoryTheory.Sites.Simplicial.DerivedRightUnitor

/-!
# The face identity of Stacks 0D9K, transported into the derived category

All names are in the namespace `CategoryTheory.SimplicialSiteSituation`.

Let `S` be a simplicial-site situation and `K` an object of the derived category of abelian sheaves
on the total site. The face identity the proof of Stacks 0D9K needs is

  `integerProjection K q ≫ (- ⊗^L integerFace φ) = realizationTermMap φ ≫ integerProjection K p`

at `φ : p ⟶ q`, and `integerProjection_comp_derivedTensorFace_eq_realizationTermMap_of_comp`
reduces it, for a cartesian `K`, to the same identity composed with `g_{q!}` of the derived
transition of Stacks 07TF, in which no inverse of the transition appears. This file identifies the
left-hand side of that reduced identity with the derived functor of the sheaf-level face identity.

The sheaf-level identity is
`whiskerRight_abelianTransitionOfFiber_comp_integerProjectionSheaf_comp_integerTensorFace`, an
identity of transformations `(g_p^{-1} ⋙ f_φ^{-1}) ⋙ g_{q!} ⟶ g_{p!}ℤ ⊗_ℤ -`.

## Main results

* `derivedTransition_comp_integerProjection_comp_derivedTensorFace`: **the left-hand side of the
  reduced face identity is the derived functor of the left-hand side of the sheaf-level face
  identity**, read through the compositor of the derived restriction and the derived inverse image
  and through `integerTensorAbDerivedIso`.
* `derivedTransition_comp_integerProjection_comp_derivedTensorFace_eq_leg`: the same, with the
  sheaf-level face identity applied, so that the derived functor is taken of the transpose of the
  `φ`-labelled leg of the sum formula of Stacks 09WG followed by the comparison in degree `p`.

## References

* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 09WI](https://stacks.math.columbia.edu/tag/09WI)
* [Stacks Project, Tag 0D9E](https://stacks.math.columbia.edu/tag/0D9E)
* [Stacks Project, Tag 0D9K](https://stacks.math.columbia.edu/tag/0D9K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.DerivedTensor.AbelianSheaves
open scoped Simplicial

universe v u

namespace CategoryTheory.SimplicialSiteSituation

/-- A naturality square carried to the inverses of its two vertical isomorphisms. -/
private theorem comp_inv_eq_inv_comp {C : Type*} [Category C] {A₁ A₂ B₁ B₂ : C}
    (a : A₁ ⟶ A₂) (b : B₁ ⟶ B₂) (hp : A₁ ⟶ B₁) (hpi : B₁ ⟶ A₁) (hq : A₂ ⟶ B₂) (hqi : B₂ ⟶ A₂)
    (hp₁ : hpi ≫ hp = 𝟙 B₁) (hq₁ : hq ≫ hqi = 𝟙 A₂) (h : a ≫ hq = hp ≫ b) :
    b ≫ hqi = hpi ≫ a := by
  have e₁ : b ≫ hqi = hpi ≫ hp ≫ b ≫ hqi := by
    rw [← Category.assoc hpi hp, hp₁, Category.id_comp]
  have e₂ : hpi ≫ hp ≫ b ≫ hqi = hpi ≫ a ≫ hq ≫ hqi := by
    rw [← Category.assoc hp b hqi, ← h, Category.assoc]
  rw [e₁, e₂, hq₁, Category.comp_id]

/-- Regrouping a fivefold composite past a naturality square and a splitting of one of its
factors. -/
private theorem comp_regroup {C : Type*} [Category C] {X Y Y' Y'' Z W V : C}
    (x : X ⟶ Y) (y : Y ⟶ Y') (c : Y' ⟶ Z) (n₁ : Z ⟶ W) (t : W ⟶ V)
    (cp : Y ⟶ Y'') (n₀ : Y'' ⟶ Z) (n : Y'' ⟶ W)
    (hmove : y ≫ c = cp ≫ n₀) (hn : n = n₀ ≫ n₁) :
    (x ≫ y) ≫ c ≫ n₁ ≫ t = x ≫ cp ≫ n ≫ t := by
  rw [hn]
  simp only [Category.assoc]
  rw [← Category.assoc y c, hmove, Category.assoc]

section Standard

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] CategoryTheory.SimplicialSiteSituation.abelianComponent

variable (S : SimplicialSiteSituation.{u})

/-- **The left-hand side of the reduced face identity of Stacks 0D9K is the derived functor of the
left-hand side of the sheaf-level face identity.** The derived transition of Stacks 07TF, extended
by `g_{q!}`, followed by the comparison of Stacks 0D9E in degree `q` and the derived tensor product
with the structure map of the integral resolution at `φ : p ⟶ q`, is the derived functor of the
sheaf-level composite of `Functor.whiskerRight (abelianTransitionOfFiber' φ) g_{q!}`,
`integerProjectionSheaf q` and `integerTensorFace φ`, read through the compositor of the derived
restriction with the derived inverse image, the compositor of that composite with `g_{q!}`, and
`integerTensorAbDerivedIso`. -/
theorem derivedTransition_comp_integerProjection_comp_derivedTensorFace
    (K : DerivedCategory (Sheaf S.totalTopology Ab.{u}))
    {p q : SimplexCategory} (φ : p ⟶ q) :
    (S.componentLowerShriekDerived q).map ((derivedTransition S φ).app K) ≫
        S.integerProjection K q ≫
          ((derivedTensor S.totalTopology).map
            ((DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).map
              (integerFace S φ))).app K =
      (S.componentLowerShriekDerived q).map
          ((derivedComponentCompIso' S φ).inv.app K) ≫
        (derivedCompIso (restrictAb S p ⋙ abelianTransition S φ)
            (componentLowerShriekAb S q)
            ((restrictAb S p ⋙ abelianTransition S φ) ⋙ componentLowerShriekAb S q)
            (Iso.refl _)).inv.app K ≫
          (derivedNatTrans
            ((restrictAb S p ⋙ abelianTransition S φ) ⋙ componentLowerShriekAb S q)
            (integerTensorAb S p)
            (Functor.whiskerRight (S.abelianTransitionOfFiber' φ)
                (componentLowerShriekAb S q) ≫
              integerProjectionSheaf S q ≫ integerTensorFace S φ)).app K ≫
            (S.integerTensorAbDerivedIso p).hom.app K := by
  have hwhisker := congr_app (derivedCompIso_refl_hom_whiskerRight
    (restrictAb S p ⋙ abelianTransition S φ) (restrictAb S q) (componentLowerShriekAb S q)
    (S.abelianTransitionOfFiber' φ)) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hwhisker
  have hmove : (S.componentLowerShriekDerived q).map
        ((derivedNatTrans (restrictAb S p ⋙ abelianTransition S φ) (restrictAb S q)
          (S.abelianTransitionOfFiber' φ)).app K) ≫
      (derivedCompIso (restrictAb S q) (componentLowerShriekAb S q)
        (restrictAb S q ⋙ componentLowerShriekAb S q) (Iso.refl _)).inv.app K =
    (derivedCompIso (restrictAb S p ⋙ abelianTransition S φ) (componentLowerShriekAb S q)
          ((restrictAb S p ⋙ abelianTransition S φ) ⋙ componentLowerShriekAb S q)
          (Iso.refl _)).inv.app K ≫
      (derivedNatTrans
        ((restrictAb S p ⋙ abelianTransition S φ) ⋙ componentLowerShriekAb S q)
        (restrictAb S q ⋙ componentLowerShriekAb S q)
        (Functor.whiskerRight (S.abelianTransitionOfFiber' φ)
          (componentLowerShriekAb S q))).app K :=
    comp_inv_eq_inv_comp _ _ _ _ _ _ (Iso.inv_hom_id_app _ _) (Iso.hom_inv_id_app _ _) hwhisker
  have hn := congr_app (derivedNatTrans_comp
    ((restrictAb S p ⋙ abelianTransition S φ) ⋙ componentLowerShriekAb S q)
    (restrictAb S q ⋙ componentLowerShriekAb S q) (integerTensorAb S p)
    (Functor.whiskerRight (S.abelianTransitionOfFiber' φ) (componentLowerShriekAb S q))
    (integerProjectionSheaf S q ≫ integerTensorFace S φ)) K
  simp only [NatTrans.comp_app] at hn
  rw [integerProjection_comp_derivedTensorFace, derivedTransition_eq',
    derivedTransitionOfAbelian', NatTrans.comp_app, CategoryTheory.Functor.map_comp]
  exact comp_regroup _ _ _ _ _ _ _ _ hmove hn

/-- **The left-hand side of the reduced face identity of Stacks 0D9K is the derived functor of the
transpose of the `φ`-labelled leg of the sum formula of Stacks 09WG followed by the comparison of
Stacks 0D9E in degree `p`.** The transpose is spelled out as `g_{q!}` of the leg followed by the
counit of `g_{q!} ⊣ g_q^{-1}` and the right unitor of `g_p^{-1} ⋙ g_{p!}`. -/
theorem derivedTransition_comp_integerProjection_comp_derivedTensorFace_eq_leg
    (K : DerivedCategory (Sheaf S.totalTopology Ab.{u}))
    {p q : SimplexCategory} (φ : p ⟶ q) :
    (S.componentLowerShriekDerived q).map ((derivedTransition S φ).app K) ≫
        S.integerProjection K q ≫
          ((derivedTensor S.totalTopology).map
            ((DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).map
              (integerFace S φ))).app K =
      (S.componentLowerShriekDerived q).map
          ((derivedComponentCompIso' S φ).inv.app K) ≫
        (derivedCompIso (restrictAb S p ⋙ abelianTransition S φ)
            (componentLowerShriekAb S q)
            ((restrictAb S p ⋙ abelianTransition S φ) ⋙ componentLowerShriekAb S q)
            (Iso.refl _)).inv.app K ≫
          (derivedNatTrans
            ((restrictAb S p ⋙ abelianTransition S φ) ⋙ componentLowerShriekAb S q)
            (integerTensorAb S p)
            (Functor.whiskerRight
                (Functor.whiskerLeft (S.restrictAb p)
                  (Functor.whiskerRight (S.componentLowerShriekAbAdjunction' p).unit
                      (abelianTransition S φ) ≫
                    Functor.whiskerLeft (componentLowerShriekAb S p)
                      (S.abelianTransitionOfFiber' φ)))
                (componentLowerShriekAb S q) ≫
              Functor.whiskerLeft (S.restrictAb p ⋙ componentLowerShriekAb S p)
                  (S.componentLowerShriekAbAdjunction' q).counit ≫
                (Functor.rightUnitor (S.restrictAb p ⋙ componentLowerShriekAb S p)).hom ≫
                  integerProjectionSheaf S p)).app K ≫
            (S.integerTensorAbDerivedIso p).hom.app K := by
  rw [derivedTransition_comp_integerProjection_comp_derivedTensorFace,
    whiskerRight_abelianTransitionOfFiber_comp_integerProjectionSheaf_comp_integerTensorFace]

end Standard

end CategoryTheory.SimplicialSiteSituation

end
