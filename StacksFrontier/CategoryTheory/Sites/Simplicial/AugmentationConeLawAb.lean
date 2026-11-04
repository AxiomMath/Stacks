module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationCartesian
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationComponentInverseImageAb
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationComponentPushforwardAbForget
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationResolutionFace
public import StacksFrontier.CategoryTheory.Sites.Topos.AbelianAdjunctionForget

/-!
# The cone law of Stacks 0D70 on abelian sheaves

Let `S` be a simplicial-site situation and `a` an augmentation of `S` towards a site `(D, K)`.
Stacks 0D70 builds the direct image along the total augmentation as the limit of the cosimplicial
sheaf of the degreewise direct images, and the law that makes that work is the one
`CategoryTheory.SimplicialSiteSituation.Augmentation`
`.homEquiv_componentPushforwardTransition_iff` records: a family of morphisms out of the inverse
images `a_n⁻¹𝒢` transposes to a cone on that cosimplicial sheaf exactly when it is compatible
with the inverse-image transitions of Stacks 09WF. That law is stated for sheaves of sets.

This file supplies the abelian form.

## Main results

* `CategoryTheory.SimplicialSiteSituation.Augmentation`
  `.homEquiv_componentPushforwardTransition_iff'`: the cone law of Stacks 0D70 for two degrees
  at a time, with the two morphisms independent instead of a family indexed by all degrees.
* `CategoryTheory.SimplicialSiteSituation.Augmentation`
  `.transitionInverseImageIso_hom_app_comp_componentRestrictionIso_inv`: the inverse-image
  comparison of Stacks 0D70, compatibility (1), as the inverse-image transition of `a⁻¹𝒢` read
  through the restriction comparisons of compatibility (b).
* `CategoryTheory.SimplicialSiteSituation.Augmentation`
  `.homEquiv_componentPushforwardTransition_iff''`: the cone law with those restriction
  comparisons absorbed, so that both sides speak only of the restrictions of `a⁻¹𝒢`.
* `CategoryTheory.SimplicialSiteSituation.Augmentation`
  `.forget_abelianComponentPushforwardIso_inv_comp_map`: the Stacks 04DB correction followed by
  a cosimplicial transition of the complex of Stacks 0D79 forgets to the direct-image transition
  of Stacks 0D70, compatibility (c).
* `CategoryTheory.SimplicialSiteSituation.Augmentation`
  `.abelianHomEquiv_abelianCosimplicialPushforward_iff`: **the cone law of Stacks 0D70 on
  abelian sheaves.**

## References

* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 0D79](https://stacks.math.columbia.edu/tag/0D79)
* [Stacks Project, Tag 04DB](https://stacks.math.columbia.edu/tag/04DB)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Topos.AbelianPushforward
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation.Augmentation

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K)

/-- **The cone law of Stacks 0D70, for two degrees.** -/
theorem homEquiv_componentPushforwardTransition_iff'
    (G : Sheaf K (Type u)) (F : Sheaf S.totalTopology (Type u))
    {m n : SimplexCategory} (φ : m ⟶ n)
    (γm : (componentAugmentation S D K a m).inverseImage.obj G ⟶ (S.restrict m).obj F)
    (γn : (componentAugmentation S D K a n).inverseImage.obj G ⟶ (S.restrict n).obj F) :
    (componentAugmentation S D K a m).adj.homEquiv G _ γm ≫
          (componentPushforwardTransition S D K a φ).app F =
        (componentAugmentation S D K a n).adj.homEquiv G _ γn ↔
      (S.transitionMorphism φ).inverseImage.map γm ≫ (S.fiberTransition φ).app F =
        (transitionInverseImageIso S D K a φ).hom.app G ≫ γn := by
  have hkey := homEquiv_transitionInverseImageIso S D K a φ G ((S.restrict n).obj F) γn
  rw [Adjunction.comp_homEquiv, Equiv.trans_apply] at hkey
  change (componentAugmentation S D K a m).adj.homEquiv G _ γm ≫
      (componentAugmentation S D K a m).pushforward.map ((S.restrictTransition φ).app F) ≫
        (transitionPushforwardIso S D K a φ).hom.app ((S.restrict n).obj F) = _ ↔ _
  rw [← hkey, ← Category.assoc, ← Adjunction.homEquiv_naturality_right]
  refine Iff.trans (Iso.cancel_iso_hom_right _ _
    ((transitionPushforwardIso S D K a φ).app ((S.restrict n).obj F))) ?_
  refine Iff.trans (Equiv.apply_eq_iff_eq _) ?_
  refine Iff.trans (Equiv.apply_eq_iff_eq
    ((S.transitionMorphism φ).adj.homEquiv _ _).symm).symm ?_
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_naturality_left_symm]
  rfl

variable {m n : SimplexCategory}

/-- The inverse-image comparison of Stacks 0D70, compatibility (1), rewritten as the
inverse-image transition of `a⁻¹𝒢` read through the restriction comparisons. -/
theorem transitionInverseImageIso_hom_app_comp_componentRestrictionIso_inv
    (φ : m ⟶ n) (G : Sheaf K (Type u)) :
    (S.transitionMorphism φ).inverseImage.map (componentRestrictionIso S D K a G m).inv ≫
        (S.fiberTransition φ).app (inverseImageSheaf S D K a G) =
      (transitionInverseImageIso S D K a φ).hom.app G ≫
        (componentRestrictionIso S D K a G n).inv := by
  rw [fiberTransition_inverseImageSheaf, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The cone law of Stacks 0D70, with the restriction comparisons absorbed.** A pair of
morphisms out of the restrictions of `a⁻¹𝒢` transposes to a compatible pair exactly when it is
compatible with the inverse-image transitions of Stacks 09WF. -/
theorem homEquiv_componentPushforwardTransition_iff''
    (G : Sheaf K (Type u)) (F : Sheaf S.totalTopology (Type u)) (φ : m ⟶ n)
    (δm : (S.restrict m).obj (inverseImageSheaf S D K a G) ⟶ (S.restrict m).obj F)
    (δn : (S.restrict n).obj (inverseImageSheaf S D K a G) ⟶ (S.restrict n).obj F) :
    (componentAugmentation S D K a m).adj.homEquiv G _
            ((componentRestrictionIso S D K a G m).inv ≫ δm) ≫
          (componentPushforwardTransition S D K a φ).app F =
        (componentAugmentation S D K a n).adj.homEquiv G _
          ((componentRestrictionIso S D K a G n).inv ≫ δn) ↔
      (S.transitionMorphism φ).inverseImage.map δm ≫ (S.fiberTransition φ).app F =
        (S.fiberTransition φ).app (inverseImageSheaf S D K a G) ≫ δn := by
  refine Iff.trans (homEquiv_componentPushforwardTransition_iff' S D K a G F φ _ _) ?_
  rw [CategoryTheory.Functor.map_comp, Category.assoc,
    ← Category.assoc ((transitionInverseImageIso S D K a φ).hom.app G),
    ← transitionInverseImageIso_hom_app_comp_componentRestrictionIso_inv S D K a φ G,
    Category.assoc]
  exact Iso.cancel_iso_hom_left
    ((S.transitionMorphism φ).inverseImage.mapIso
      (componentRestrictionIso S D K a G m).symm) _ _

/-- The abelian inverse image along a simplicial transition has the inverse image of sheaves of
sets as its underlying functor, on morphisms. -/
theorem forget_abelianTransition_map (φ : m ⟶ n)
    {A B : Sheaf (S.componentTopology m) Ab.{u}} (g : A ⟶ B) :
    (sheafCompose (S.componentTopology n) (forget Ab.{u})).map ((abelianTransition S φ).map g) =
      (S.transitionMorphism φ).inverseImage.map
        ((sheafCompose (S.componentTopology m) (forget Ab.{u})).map g) :=
  rfl

variable [HasSheafify K AddCommGrpCat.{u}]

omit [HasSheafify K AddCommGrpCat] in
/-- Forgetting the group operations of a transpose along the abelian adjunction of the
augmentation of degree `k`, precomposed with the restriction comparison. -/
theorem forget_abelianHomEquiv_comp (G : Sheaf K Ab.{u}) (F : Sheaf S.totalTopology Ab.{u})
    (k : SimplexCategory)
    (δ : (S.abelianComponent k).obj ((totalInverseImageAb S D K a).obj G) ⟶
      (S.abelianComponent k).obj F) :
    (sheafCompose K (forget Ab.{u})).map
        ((abelianInverseImageAdjPushforward (S.componentTopology k)
            (componentAugmentation S D K a k)).homEquiv G _
          ((componentRestrictionAbInverseImageIso S D K a G k).inv ≫ δ)) =
      (componentAugmentation S D K a k).adj.homEquiv ((sheafCompose K (forget Ab.{u})).obj G) _
        ((componentRestrictionIso S D K a ((sheafCompose K (forget Ab.{u})).obj G) k).inv ≫
          (sheafCompose (S.componentTopology k) (forget Ab.{u})).map δ) := by
  refine Eq.trans (abelianInverseImageAdjPushforward_homEquiv_forget
    (S.componentTopology k) (componentAugmentation S D K a k) G _ _) ?_
  exact congrArg ((componentAugmentation S D K a k).adj.homEquiv
      ((sheafCompose K (forget Ab.{u})).obj G) _)
    ((sheafCompose (S.componentTopology k) (forget Ab.{u})).map_comp _ _)

omit [HasSheafify K AddCommGrpCat] in
/-- Forgetting the group operations of a transpose along the abelian adjunction of the
augmentation of degree `k`, precomposed with the restriction comparison. -/
theorem forget_abelianHomEquiv_comp' (G : Sheaf K Ab.{u}) (F : Sheaf S.totalTopology Ab.{u})
    (k : SimplexCategory)
    (δ : (S.restrictAb k).obj ((totalInverseImageAb S D K a).obj G) ⟶
      (S.restrictAb k).obj F) :
    (sheafCompose K (forget Ab.{u})).map
        ((abelianInverseImageAdjPushforward (S.componentTopology k)
            (componentAugmentation S D K a k)).homEquiv G _
          ((componentRestrictionAbInverseImageIso' S D K a G k).inv ≫ δ)) =
      (componentAugmentation S D K a k).adj.homEquiv ((sheafCompose K (forget Ab.{u})).obj G) _
        ((componentRestrictionIso S D K a ((sheafCompose K (forget Ab.{u})).obj G) k).inv ≫
          (sheafCompose (S.componentTopology k) (forget Ab.{u})).map δ) := by
  refine Eq.trans (abelianInverseImageAdjPushforward_homEquiv_forget
    (S.componentTopology k) (componentAugmentation S D K a k) G _ _) ?_
  exact congrArg ((componentAugmentation S D K a k).adj.homEquiv
      ((sheafCompose K (forget Ab.{u})).obj G) _)
    ((sheafCompose (S.componentTopology k) (forget Ab.{u})).map_comp _ _)

/-- Forgetting the Stacks 04DB correction followed by a cosimplicial transition of the complex
of Stacks 0D79 gives the direct-image transition of Stacks 0D70, compatibility (c). -/
theorem forget_abelianComponentPushforwardIso_inv_comp_map
    (F : Sheaf S.totalTopology Ab.{u}) (φ : m ⟶ n) :
    (sheafCompose K (forget Ab.{u})).map
        ((abelianComponentPushforwardIso S D K a m).inv.app F ≫
          ((abelianCosimplicialPushforward S D K a).map φ).app F) =
      (componentPushforwardTransition S D K a φ).app
        ((sheafCompose S.totalTopology (forget Ab.{u})).obj F) := by
  refine Eq.trans ((sheafCompose K (forget Ab.{u})).map_comp _ _) ?_
  refine Eq.trans (congrArg (fun t => t ≫ (sheafCompose K (forget Ab.{u})).map
      (((abelianCosimplicialPushforward S D K a).map φ).app F))
    (abelianComponentPushforwardIso_inv_forget S D K a m F)) ?_
  exact (Category.id_comp _).trans (abelianCosimplicialPushforward_map_forget S D K a φ F)

/-- The cone law on abelian sheaves, for any family of restriction comparisons and abelian
transitions compatible with forgetting the group operations. -/
private theorem abelianHomEquiv_abelianCosimplicialPushforward_iff_aux
    (G : Sheaf K Ab.{u}) (F : Sheaf S.totalTopology Ab.{u})
    (e : ∀ k, (S.abelianComponent k).obj ((totalInverseImageAb S D K a).obj G) ≅
      (componentInverseImageAb S D K a k).obj G)
    (τ : ∀ {k l : SimplexCategory} (φ : k ⟶ l),
      S.abelianComponent k ⋙ abelianTransition S φ ⟶ S.abelianComponent l)
    (he : ∀ k (δ : (S.abelianComponent k).obj ((totalInverseImageAb S D K a).obj G) ⟶
        (S.abelianComponent k).obj F),
      (sheafCompose K (forget Ab.{u})).map
          ((abelianInverseImageAdjPushforward (S.componentTopology k)
              (componentAugmentation S D K a k)).homEquiv G _ ((e k).inv ≫ δ)) =
        (componentAugmentation S D K a k).adj.homEquiv ((sheafCompose K (forget Ab.{u})).obj G) _
          ((componentRestrictionIso S D K a ((sheafCompose K (forget Ab.{u})).obj G) k).inv ≫
            (sheafCompose (S.componentTopology k) (forget Ab.{u})).map δ))
    (hτ : ∀ {k l : SimplexCategory} (φ : k ⟶ l) (A : Sheaf S.totalTopology Ab.{u}),
      (sheafCompose (S.componentTopology l) (forget Ab.{u})).map ((τ φ).app A) =
        (S.fiberTransition φ).app ((sheafCompose S.totalTopology (forget Ab.{u})).obj A))
    (φ : m ⟶ n)
    (δm : (S.abelianComponent m).obj ((totalInverseImageAb S D K a).obj G) ⟶
      (S.abelianComponent m).obj F)
    (δn : (S.abelianComponent n).obj ((totalInverseImageAb S D K a).obj G) ⟶
      (S.abelianComponent n).obj F) :
    (abelianInverseImageAdjPushforward (S.componentTopology m)
              (componentAugmentation S D K a m)).homEquiv G _ ((e m).inv ≫ δm) ≫
          (abelianComponentPushforwardIso S D K a m).inv.app F ≫
            ((abelianCosimplicialPushforward S D K a).map φ).app F =
        (abelianInverseImageAdjPushforward (S.componentTopology n)
              (componentAugmentation S D K a n)).homEquiv G _ ((e n).inv ≫ δn) ≫
          (abelianComponentPushforwardIso S D K a n).inv.app F ↔
      (abelianTransition S φ).map δm ≫ (τ φ).app F =
        (τ φ).app ((totalInverseImageAb S D K a).obj G) ≫ δn := by
  have hX : (sheafCompose K (forget Ab.{u})).map
        ((abelianInverseImageAdjPushforward (S.componentTopology m)
                (componentAugmentation S D K a m)).homEquiv G _
              ((e m).inv ≫ δm) ≫
            (abelianComponentPushforwardIso S D K a m).inv.app F ≫
              ((abelianCosimplicialPushforward S D K a).map φ).app F) =
      (componentAugmentation S D K a m).adj.homEquiv ((sheafCompose K (forget Ab.{u})).obj G) _
          ((componentRestrictionIso S D K a ((sheafCompose K (forget Ab.{u})).obj G) m).inv ≫
            (sheafCompose (S.componentTopology m) (forget Ab.{u})).map δm) ≫
        (componentPushforwardTransition S D K a φ).app
          ((sheafCompose S.totalTopology (forget Ab.{u})).obj F) :=
    (((sheafCompose K (forget Ab.{u})).map_comp _ _).trans
        (congrArg (fun t => (sheafCompose K (forget Ab.{u})).map
            ((abelianInverseImageAdjPushforward (S.componentTopology m)
                  (componentAugmentation S D K a m)).homEquiv G _
              ((e m).inv ≫ δm)) ≫ t)
          (forget_abelianComponentPushforwardIso_inv_comp_map S D K a F φ))).trans
      (congrArg (fun t => t ≫ (componentPushforwardTransition S D K a φ).app
          ((sheafCompose S.totalTopology (forget Ab.{u})).obj F))
        (he m δm))
  have hY : (sheafCompose K (forget Ab.{u})).map
        ((abelianInverseImageAdjPushforward (S.componentTopology n)
                (componentAugmentation S D K a n)).homEquiv G _
              ((e n).inv ≫ δn) ≫
            (abelianComponentPushforwardIso S D K a n).inv.app F) =
      (componentAugmentation S D K a n).adj.homEquiv ((sheafCompose K (forget Ab.{u})).obj G) _
        ((componentRestrictionIso S D K a ((sheafCompose K (forget Ab.{u})).obj G) n).inv ≫
          (sheafCompose (S.componentTopology n) (forget Ab.{u})).map δn) :=
    (((sheafCompose K (forget Ab.{u})).map_comp _ _).trans
        (congrArg (fun t => (sheafCompose K (forget Ab.{u})).map
            ((abelianInverseImageAdjPushforward (S.componentTopology n)
                  (componentAugmentation S D K a n)).homEquiv G _
              ((e n).inv ≫ δn)) ≫ t)
          (abelianComponentPushforwardIso_inv_forget S D K a n F))).trans
      ((Category.comp_id _).trans (he n δn))
  have hR : ((abelianTransition S φ).map δm ≫ (τ φ).app F =
        (τ φ).app ((totalInverseImageAb S D K a).obj G) ≫ δn) ↔
      ((S.transitionMorphism φ).inverseImage.map
            ((sheafCompose (S.componentTopology m) (forget Ab.{u})).map δm) ≫
          (S.fiberTransition φ).app
            ((sheafCompose S.totalTopology (forget Ab.{u})).obj F) =
        (S.fiberTransition φ).app
            ((sheafCompose S.totalTopology (forget Ab.{u})).obj
              ((totalInverseImageAb S D K a).obj G)) ≫
          (sheafCompose (S.componentTopology n) (forget Ab.{u})).map δn) := by
    refine Iff.trans
      ((Functor.map_injective (sheafCompose (S.componentTopology n) (forget Ab.{u}))).eq_iff).symm
      ?_
    refine Iff.of_eq (congrArg₂ Eq ?_ ?_)
    · exact ((sheafCompose (S.componentTopology n) (forget Ab.{u})).map_comp _ _).trans
        (congrArg (fun t => (sheafCompose (S.componentTopology n) (forget Ab.{u})).map
            ((abelianTransition S φ).map δm) ≫ t)
          (hτ φ F))
    · exact ((sheafCompose (S.componentTopology n) (forget Ab.{u})).map_comp _ _).trans
        (congrArg (fun t => t ≫ (sheafCompose (S.componentTopology n) (forget Ab.{u})).map δn)
          (hτ φ ((totalInverseImageAb S D K a).obj G)))
  constructor
  · intro h
    refine hR.mpr ((homEquiv_componentPushforwardTransition_iff'' S D K a _ _ φ _ _).mp ?_)
    exact hX.symm.trans ((congrArg (sheafCompose K (forget Ab.{u})).map h).trans hY)
  · intro h
    exact Functor.map_injective (sheafCompose K (forget Ab.{u}))
      (hX.trans
        (((homEquiv_componentPushforwardTransition_iff'' S D K a _ _ φ _ _).mpr
          (hR.mp h)).trans hY.symm))


/-- **The cone law of Stacks 0D70 on abelian sheaves.** A pair of morphisms out of the
restrictions of `a⁻¹𝒢` transposes, through the comparison of Stacks 04DB, to a pair compatible
with the cosimplicial transitions of the complex of Stacks 0D79 exactly when it is compatible
with the abelian inverse-image transitions of Stacks 09WF. -/
theorem abelianHomEquiv_abelianCosimplicialPushforward_iff
    (G : Sheaf K Ab.{u}) (F : Sheaf S.totalTopology Ab.{u}) (φ : m ⟶ n)
    (δm : (S.abelianComponent m).obj ((totalInverseImageAb S D K a).obj G) ⟶
      (S.abelianComponent m).obj F)
    (δn : (S.abelianComponent n).obj ((totalInverseImageAb S D K a).obj G) ⟶
      (S.abelianComponent n).obj F) :
    (abelianInverseImageAdjPushforward (S.componentTopology m)
              (componentAugmentation S D K a m)).homEquiv G _
            ((componentRestrictionAbInverseImageIso S D K a G m).inv ≫ δm) ≫
          (abelianComponentPushforwardIso S D K a m).inv.app F ≫
            ((abelianCosimplicialPushforward S D K a).map φ).app F =
        (abelianInverseImageAdjPushforward (S.componentTopology n)
              (componentAugmentation S D K a n)).homEquiv G _
            ((componentRestrictionAbInverseImageIso S D K a G n).inv ≫ δn) ≫
          (abelianComponentPushforwardIso S D K a n).inv.app F ↔
      (abelianTransition S φ).map δm ≫ (abelianTransitionOfFiber S φ).app F =
        (abelianTransitionOfFiber S φ).app ((totalInverseImageAb S D K a).obj G) ≫ δn := by
  exact abelianHomEquiv_abelianCosimplicialPushforward_iff_aux S D K a G F
    (componentRestrictionAbInverseImageIso S D K a G)
    (fun φ => abelianTransitionOfFiber S φ)
    (fun k δ => forget_abelianHomEquiv_comp S D K a G F k δ)
    (fun φ A => abelianTransitionOfFiber_forget S φ A) φ δm δn

/-- **The cone law of Stacks 0D70 on abelian sheaves.** A pair of morphisms out of the
restrictions of `a⁻¹𝒢` transposes, through the comparison of Stacks 04DB, to a pair compatible
with the cosimplicial transitions of the complex of Stacks 0D79 exactly when it is compatible
with the abelian inverse-image transitions of Stacks 09WF. -/
theorem abelianHomEquiv_abelianCosimplicialPushforward_iff'
    (G : Sheaf K Ab.{u}) (F : Sheaf S.totalTopology Ab.{u}) (φ : m ⟶ n)
    (δm : (S.restrictAb m).obj ((totalInverseImageAb S D K a).obj G) ⟶
      (S.restrictAb m).obj F)
    (δn : (S.restrictAb n).obj ((totalInverseImageAb S D K a).obj G) ⟶
      (S.restrictAb n).obj F) :
    (abelianInverseImageAdjPushforward (S.componentTopology m)
              (componentAugmentation S D K a m)).homEquiv G _
            ((componentRestrictionAbInverseImageIso' S D K a G m).inv ≫ δm) ≫
          (abelianComponentPushforwardIso S D K a m).inv.app F ≫
            ((abelianCosimplicialPushforward S D K a).map φ).app F =
        (abelianInverseImageAdjPushforward (S.componentTopology n)
              (componentAugmentation S D K a n)).homEquiv G _
            ((componentRestrictionAbInverseImageIso' S D K a G n).inv ≫ δn) ≫
          (abelianComponentPushforwardIso S D K a n).inv.app F ↔
      (abelianTransition S φ).map δm ≫ (abelianTransitionOfFiber' S φ).app F =
        (abelianTransitionOfFiber' S φ).app ((totalInverseImageAb S D K a).obj G) ≫ δn := by
  exact abelianHomEquiv_abelianCosimplicialPushforward_iff_aux S D K a G F
    (componentRestrictionAbInverseImageIso' S D K a G)
    (fun φ => abelianTransitionOfFiber' S φ)
    (fun k δ => forget_abelianHomEquiv_comp' S D K a G F k δ)
    (fun φ A => abelianTransitionOfFiber_forget' S φ A) φ δm δn

/-- **The cone law of Stacks 0D70 on abelian sheaves, in the spelling of Stacks 09WG.** The same
statement with the inverse-image transition written as the summand transformation
`CategoryTheory.SimplicialSiteSituation.fiberTransitionAb` of the direct-sum formula of
Stacks 09WG rather than as the inverse image of Stacks 04JC; the two differ by the comparison
`CategoryTheory.SimplicialSiteSituation.transitionInverseImageAbIso`. -/
theorem abelianHomEquiv_abelianCosimplicialPushforward_iff_fiberTransitionAb
    (G : Sheaf K Ab.{u}) (F : Sheaf S.totalTopology Ab.{u}) (φ : m ⟶ n)
    (δm : (S.abelianComponent m).obj ((totalInverseImageAb S D K a).obj G) ⟶
      (S.abelianComponent m).obj F)
    (δn : (S.abelianComponent n).obj ((totalInverseImageAb S D K a).obj G) ⟶
      (S.abelianComponent n).obj F) :
    (abelianInverseImageAdjPushforward (S.componentTopology m)
              (componentAugmentation S D K a m)).homEquiv G _
            ((componentRestrictionAbInverseImageIso S D K a G m).inv ≫ δm) ≫
          (abelianComponentPushforwardIso S D K a m).inv.app F ≫
            ((abelianCosimplicialPushforward S D K a).map φ).app F =
        (abelianInverseImageAdjPushforward (S.componentTopology n)
              (componentAugmentation S D K a n)).homEquiv G _
            ((componentRestrictionAbInverseImageIso S D K a G n).inv ≫ δn) ≫
          (abelianComponentPushforwardIso S D K a n).inv.app F ↔
      (S.transitionInverseImageAb φ).map δm ≫ (S.fiberTransitionAb φ).app F =
        (S.fiberTransitionAb φ).app ((totalInverseImageAb S D K a).obj G) ≫ δn := by
  refine Iff.trans (abelianHomEquiv_abelianCosimplicialPushforward_iff S D K a G F φ δm δn) ?_
  have he (A : Sheaf S.totalTopology Ab.{u}) :
      (S.fiberTransitionAb φ).app A =
        (S.transitionInverseImageAbIso φ).hom.app ((S.abelianComponent m).obj A) ≫
          (abelianTransitionOfFiber S φ).app A :=
    congr_app (S.fiberTransitionAb_eq φ) A
  rw [he F, he ((totalInverseImageAb S D K a).obj G), ← Category.assoc,
    (S.transitionInverseImageAbIso φ).hom.naturality δm, Category.assoc]
  exact (Iso.cancel_iso_hom_left
    ((S.transitionInverseImageAbIso φ).app
      ((S.abelianComponent m).obj ((totalInverseImageAb S D K a).obj G))) _ _).symm

/-- **The cone law of Stacks 0D70 on abelian sheaves, in the spelling of Stacks 09WG.** The same
statement with the inverse-image transition written as the summand transformation
`CategoryTheory.SimplicialSiteSituation.fiberTransitionAb'` of the direct-sum formula of
Stacks 09WG rather than as the inverse image of Stacks 04JC; the two differ by the comparison
`CategoryTheory.SimplicialSiteSituation.transitionInverseImageAbIso`. -/
theorem abelianHomEquiv_abelianCosimplicialPushforward_iff_fiberTransitionAb'
    (G : Sheaf K Ab.{u}) (F : Sheaf S.totalTopology Ab.{u}) (φ : m ⟶ n)
    (δm : (S.restrictAb m).obj ((totalInverseImageAb S D K a).obj G) ⟶
      (S.restrictAb m).obj F)
    (δn : (S.restrictAb n).obj ((totalInverseImageAb S D K a).obj G) ⟶
      (S.restrictAb n).obj F) :
    (abelianInverseImageAdjPushforward (S.componentTopology m)
              (componentAugmentation S D K a m)).homEquiv G _
            ((componentRestrictionAbInverseImageIso' S D K a G m).inv ≫ δm) ≫
          (abelianComponentPushforwardIso S D K a m).inv.app F ≫
            ((abelianCosimplicialPushforward S D K a).map φ).app F =
        (abelianInverseImageAdjPushforward (S.componentTopology n)
              (componentAugmentation S D K a n)).homEquiv G _
            ((componentRestrictionAbInverseImageIso' S D K a G n).inv ≫ δn) ≫
          (abelianComponentPushforwardIso S D K a n).inv.app F ↔
      (S.transitionInverseImageAb φ).map δm ≫ (S.fiberTransitionAb' φ).app F =
        (S.fiberTransitionAb' φ).app ((totalInverseImageAb S D K a).obj G) ≫ δn := by
  refine Iff.trans (abelianHomEquiv_abelianCosimplicialPushforward_iff' S D K a G F φ δm δn) ?_
  have he (A : Sheaf S.totalTopology Ab.{u}) :
      (S.fiberTransitionAb' φ).app A =
        (S.transitionInverseImageAbIso φ).hom.app ((S.restrictAb m).obj A) ≫
          (abelianTransitionOfFiber' S φ).app A :=
    congr_app (S.fiberTransitionAb_eq' φ) A
  rw [he F, he ((totalInverseImageAb S D K a).obj G), ← Category.assoc,
    (S.transitionInverseImageAbIso φ).hom.naturality δm, Category.assoc]
  exact (Iso.cancel_iso_hom_left
    ((S.transitionInverseImageAbIso φ).app
      ((S.restrictAb m).obj ((totalInverseImageAb S D K a).obj G))) _ _).symm

end CategoryTheory.SimplicialSiteSituation.Augmentation

end
