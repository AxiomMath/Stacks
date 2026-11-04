module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationResolutionDegIsoSimplicial
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SliceComponentTransitionRestriction

/-!
# The simplex maps of the resolution of Stacks 0D78, read through the restrictions along `j_p`

Let `(C, J)` be a site with fibre products and `K` a simplicial semi-representable object, with
`a` the augmentation of Stacks 0D8B and `𝒢` an abelian sheaf on `(C, J)`. The resolution of
Stacks 0D78 of `a^{-1}𝒢` has degree-`p` term `g_{p!}(a_p^{-1}𝒢)`, and
`CategoryTheory.SimplicialSemiRepresentable.situationComponentInverseImageSliceIso` identifies
`a_p^{-1}𝒢` with the restriction `j_p^{-1}𝒢` along the localization functor of the simplicial
degree. This module computes the simplex maps of the resolution in that spelling.

The computation is one identity, `componentSheafSummand_comp_restrictAb_map_degIso_slice`, and its
two sides are the two descriptions of the `φ`-labelled summand of Stacks 09WG after the
identifications: on the left the summand of the simplex-coefficient resolution followed by the
degreewise identification of Stacks 0D78 and the unit of `a_! ⊣ a^{-1}`, on the right the
comparison of restrictions `j_m^{-1}r_φ^{-1} ≅ j_n^{-1}` followed by the unit of
`j_{m!} ⊣ j_m^{-1}` and the comparison `a^{-1}g_m^{-1}r_φ^{-1} ≅ a^{-1}g_n^{-1}` of the
restrictions along the two factorizations of `j_n` through the total site.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable`
  `.fiberTransitionAb_comp_restrictAb_map_augmentationUnit`: the transition of the restrictions of
  an abelian sheaf of the form `a_!W` is the comparison of restrictions, against the unit of
  `a_! ⊣ a^{-1}`. This is
  `.fiberTransitionAb_augmentationTransitionRestrictionIso` composed with one naturality.
* `CategoryTheory.SimplicialSemiRepresentable`
  `.componentSheafSummand_comp_restrictAb_map_degIso_slice`: the `φ`-labelled summand of
  Stacks 09WG through the restrictions along the localization functors.
* `CategoryTheory.SimplicialSemiRepresentable`
  `.map_degIso_inv_comp_barSimplicial_map_comp_degIso_hom_slice`: **the simplex maps of the
  resolution of Stacks 0D78 after `a_!`, as the shriek restriction transitions of Stacks 0D87.**

## Implementation notes

The transition `CategoryTheory.SimplicialSiteSituation.fiberTransitionAb'` of the restrictions of
`a^{-1}𝒢` is invertible, that sheaf being cartesian
(`CategoryTheory.SimplicialSiteSituation.Augmentation.isCartesianAbSheaf_totalInverseImageAb`), so
the identity may be proved after composing with it. That is what makes it reachable: composed with
the transition, its left side is the `φ`-labelled leg of the direct-sum formula of Stacks 09WG
(`CategoryTheory.SimplicialSiteSituation`
`.componentSumFormulaLeg_comp_restrictAb_map_componentLowerShriekMap`) and its right side is
`CategoryTheory.SimplicialSemiRepresentable`
`.fiberTransitionAb_situationComponentInverseImageSliceIso`,
and the two meet in `fiberTransitionAb_comp_restrictAb_map_augmentationUnit`.

The passage from the summand identity to the statement about the simplex maps is a transposition
along `j_{n!} ⊣ j_n^{-1}`, spelled as the composite of `g_{n!} ⊣ g_n^{-1}` with `a_! ⊣ a^{-1}`.
It is cut into four top-level lemmas because the whole of it in one declaration exceeds the
heartbeat budget of a single declaration, and the budget is per declaration; the generic steps of
the transposition are isolated in the `Stacks.CategoryTheory` namespace with the categories as
variables, which is also what keeps them clear of the two spellings of the category of abelian
sheaves on the total site.

Every reassociation is by `reassoc_of%` on a named naturality rather than by `rw [Category.assoc]`:
the goals here carry two spellings of the category of abelian sheaves on the total site, and a
`rw` whose motive abstracts over an object of it is rejected at the transparency `rw` checks its
motive at.

## References

* [Stacks Project, Tag 0D78](https://stacks.math.columbia.edu/tag/0D78)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 09WM](https://stacks.math.columbia.edu/tag/09WM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SimplicialSiteSituation
open scoped Simplicial

universe u

namespace Stacks.CategoryTheory

open CategoryTheory

variable {A : Type*} {B : Type*} [Category A] [Category B] {L : A ⥤ B} {R : B ⥤ A}

/-- The transpose of the image of a morphism under a left adjoint is that morphism followed by
the unit. -/
theorem homEquiv_left_adjoint_map (adj : L ⊣ R) {X Y : A} (f : X ⟶ Y) :
    adj.homEquiv X (L.obj Y) (L.map f) = f ≫ adj.unit.app Y :=
  (adj.homEquiv_unit X (L.obj Y) (L.map f)).trans (adj.unit.naturality f).symm

/-- The transpose of the counit followed by a morphism is the right adjoint's image of that
morphism. -/
theorem homEquiv_counit_app_comp (adj : L ⊣ R) {W Y : B} (h : W ⟶ Y) :
    adj.homEquiv (R.obj W) Y (adj.counit.app W ≫ h) = R.map h := by
  rw [adj.homEquiv_unit, R.map_comp, ← Category.assoc, adj.right_triangle_components,
    Category.id_comp]

variable {E : Type*} [Category E] {H : B ⥤ E} {I : E ⥤ B}

/-- The transpose along a composite adjunction, as the two transposes it is. -/
theorem homEquiv_comp_apply (adj₁ : L ⊣ R) (adj₂ : H ⊣ I) {X : A} {Y : E}
    (f : H.obj (L.obj X) ⟶ Y) :
    (adj₁.comp adj₂).homEquiv X Y f =
      adj₁.homEquiv X (I.obj Y) (adj₂.homEquiv (L.obj X) Y f) := by
  rw [Adjunction.comp_homEquiv]
  rfl

/-- Naturality of the transpose along a composite adjunction in the source, with the left adjoint
of the composite spelled as the two functors it is composed of. -/
theorem homEquiv_comp_naturality_left (adj₁ : L ⊣ R) (adj₂ : H ⊣ I) {X X' : A} (t : X ⟶ X')
    {Y : E} (w : H.obj (L.obj X') ⟶ Y) :
    (adj₁.comp adj₂).homEquiv X Y (H.map (L.map t) ≫ w) =
      t ≫ (adj₁.comp adj₂).homEquiv X' Y w :=
  Adjunction.homEquiv_naturality_left (adj₁.comp adj₂) t w

/-- **The transpose along a composite adjunction of a transpose of the first factor, pushed
forward.** This is the shape the simplex map of a resolution has after the second left adjoint is
applied to it: the first factor's transpose of a morphism on the inner category, followed by the
second left adjoint's image of a morphism there. -/
theorem homEquiv_comp_map_homEquiv_symm (adj₁ : L ⊣ R) (adj₂ : H ⊣ I)
    {X : A} {W Z : B} (u : X ⟶ R.obj W) (s : W ⟶ Z) :
    (adj₁.comp adj₂).homEquiv X (H.obj Z)
        (H.map ((adj₁.homEquiv X W).symm u) ≫ H.map s) =
      u ≫ R.map (s ≫ adj₂.unit.app Z) := by
  rw [homEquiv_comp_apply, Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_left, homEquiv_left_adjoint_map, homEquiv_counit_app_comp]

/-- `homEquiv_comp_map_homEquiv_symm` with the transpose of the first factor written out as the
left adjoint's image followed by the counit. -/
theorem homEquiv_comp_map_counit_comp (adj₁ : L ⊣ R) (adj₂ : H ⊣ I)
    {X : A} {W Z : B} (u : X ⟶ R.obj W) (s : W ⟶ Z) :
    (adj₁.comp adj₂).homEquiv X (H.obj Z)
        (H.map (L.map u ≫ adj₁.counit.app W) ≫ H.map s) =
      u ≫ R.map (s ≫ adj₂.unit.app Z) :=
  Eq.trans
    (congrArg (fun g => (adj₁.comp adj₂).homEquiv X (H.obj Z) (H.map g ≫ H.map s))
      (adj₁.homEquiv_counit X W u).symm)
    (homEquiv_comp_map_homEquiv_symm adj₁ adj₂ u s)

end Stacks.CategoryTheory

namespace CategoryTheory.SimplicialSemiRepresentable

open SemiRepresentable

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (K : SimplicialObject (FormalCoproduct.{u} C)) [J.toCoverage.HasPullbacks]

/-- **The transition of the restrictions of an abelian sheaf of the form `a_!W`, against the unit
of `a_! ⊣ a^{-1}`.** -/
theorem fiberTransitionAb_comp_restrictAb_map_augmentationUnit {m n : SimplexCategory}
    (φ : m ⟶ n) (W : Sheaf (situation J K).totalTopology Ab.{u}) :
    ((situation J K).fiberTransitionAb' φ).app W ≫
        ((situation J K).restrictAb n).map
          ((augmentationAbelianLowerShriekAdjunction J K).unit.app W) =
      ((situation J K).transitionInverseImageAb φ).map
          (((situation J K).restrictAb m).map
            ((augmentationAbelianLowerShriekAdjunction J K).unit.app W)) ≫
        (situationTransitionInverseImageAbIso J K φ).hom.app
            (((situation J K).restrictAb m).obj
              (((totalForget K).sheafPushforwardContinuous AddCommGrpCat.{u}
                ((situation J K).totalTopology) J).obj
                ((augmentationAbelianLowerShriek J K).obj W))) ≫
          (augmentationTransitionRestrictionIso J K φ).hom.app
            ((augmentationAbelianLowerShriek J K).obj W) := by
  refine Eq.trans (((situation J K).fiberTransitionAb' φ).naturality
    ((augmentationAbelianLowerShriekAdjunction J K).unit.app W)).symm ?_
  exact congrArg (fun g => ((situation J K).transitionInverseImageAb φ).map
      (((situation J K).restrictAb m).map
        ((augmentationAbelianLowerShriekAdjunction J K).unit.app W)) ≫ g)
    (fiberTransitionAb_augmentationTransitionRestrictionIso J K φ
      ((augmentationAbelianLowerShriek J K).obj W))


variable (G : Sheaf J Ab.{u})

section Goal

variable {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌)

/-- **The `φ`-labelled summand of the resolution of Stacks 0D78, read through the restrictions
along the localization functors.** -/
theorem componentSheafSummand_comp_restrictAb_map_degIso_slice :
    componentSheafSummand' (situation J K)
          ((Augmentation.totalInverseImageAb (situation J K) (Cat.of C) J
            (situationAugmentation J K)).obj G) φ ≫
        ((situation J K).restrictAb ⦋n⦌).map
          ((Augmentation.degIso' (situation J K) (Cat.of C) J (situationAugmentation J K) G m).hom ≫
            (SimplicialSiteSituation.componentLowerShriekAb (situation J K) ⦋m⦌).map
                ((componentRestrictionAbInverseImageIso' (situation J K) (Cat.of C) J
                    (situationAugmentation J K) G ⦋m⦌).inv ≫
                  (situationComponentInverseImageSliceIso J K ⦋m⦌).hom.app G) ≫
              (augmentationAbelianLowerShriekAdjunction J K).unit.app
                ((SimplicialSiteSituation.componentLowerShriekAb (situation J K) ⦋m⦌).obj
                  (((sliceForget K (op ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u}
                    ((situation J K).componentTopology ⦋m⦌) J).obj G))) =
      (situationComponentInverseImageSliceIso J K ⦋n⦌).hom.app G ≫
        (sliceAbelianRestrictionCompIso J K φ).inv.app G ≫
          ((componentTransitionFunctor J K φ).sheafPushforwardContinuous AddCommGrpCat.{u}
              ((situation J K).componentTopology ⦋n⦌)
              ((situation J K).componentTopology ⦋m⦌)).map
            ((((situation J K).componentLowerShriekAbAdjunction' ⦋m⦌).comp
                (augmentationAbelianLowerShriekAdjunction J K)).unit.app
              (((sliceForget K (op ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u}
                ((situation J K).componentTopology ⦋m⦌) J).obj G)) ≫
            (augmentationTransitionRestrictionIso J K φ).hom.app
              ((augmentationAbelianLowerShriek J K).obj
                ((SimplicialSiteSituation.componentLowerShriekAb (situation J K) ⦋m⦌).obj
                  (((sliceForget K (op ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u}
                    ((situation J K).componentTopology ⦋m⦌) J).obj G))) := by
  have : IsIso (((situation J K).fiberTransitionAb' φ).app
      ((Augmentation.totalInverseImageAb (situation J K) (Cat.of C) J
        (situationAugmentation J K)).obj G)) :=
    isIso_fiberTransitionAb_app_of_isCartesianAbSheaf' (situation J K) _
      (Augmentation.isCartesianAbSheaf_totalInverseImageAb (situation J K) (Cat.of C) J
        (situationAugmentation J K) G) φ
  have hu := ((situation J K).componentLowerShriekAbAdjunction' ⦋m⦌).unit.naturality
    ((situationComponentInverseImageSliceIso J K ⦋m⦌).hom.app G)
  simp only [CategoryTheory.Functor.id_map, Functor.comp_map] at hu
  have hnat := ((situation J K).fiberTransitionAb' φ).naturality
    ((SimplicialSiteSituation.componentLowerShriekAb (situation J K) ⦋m⦌).map
      ((situationComponentInverseImageSliceIso J K ⦋m⦌).hom.app G))
  simp only [Functor.comp_map] at hnat
  have hinner : ((situation J K).componentLowerShriekAbAdjunction' ⦋m⦌).unit.app
          (((situation J K).restrictAb ⦋m⦌).obj
            ((Augmentation.totalInverseImageAb (situation J K) (Cat.of C) J
              (situationAugmentation J K)).obj G)) ≫
        ((situation J K).restrictAb ⦋m⦌).map
            ((SimplicialSiteSituation.componentLowerShriekAb (situation J K) ⦋m⦌).map
              ((situationComponentInverseImageSliceIso J K ⦋m⦌).hom.app G)) ≫
          ((situation J K).restrictAb ⦋m⦌).map
            ((augmentationAbelianLowerShriekAdjunction J K).unit.app
              ((SimplicialSiteSituation.componentLowerShriekAb (situation J K) ⦋m⦌).obj
                (((sliceForget K (op ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u}
                  ((situation J K).componentTopology ⦋m⦌) J).obj G))) =
      (situationComponentInverseImageSliceIso J K ⦋m⦌).hom.app G ≫
        (((situation J K).componentLowerShriekAbAdjunction' ⦋m⦌).comp
            (augmentationAbelianLowerShriekAdjunction J K)).unit.app
          (((sliceForget K (op ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u}
            ((situation J K).componentTopology ⦋m⦌) J).obj G) := by
    have hcomp : (((situation J K).componentLowerShriekAbAdjunction' ⦋m⦌).comp
            (augmentationAbelianLowerShriekAdjunction J K)).unit.app
          (((sliceForget K (op ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u}
            ((situation J K).componentTopology ⦋m⦌) J).obj G) =
        ((situation J K).componentLowerShriekAbAdjunction' ⦋m⦌).unit.app
            (((sliceForget K (op ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u}
              ((situation J K).componentTopology ⦋m⦌) J).obj G) ≫
          ((situation J K).restrictAb ⦋m⦌).map
            ((augmentationAbelianLowerShriekAdjunction J K).unit.app
              ((SimplicialSiteSituation.componentLowerShriekAb (situation J K) ⦋m⦌).obj
                (((sliceForget K (op ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u}
                  ((situation J K).componentTopology ⦋m⦌) J).obj G))) :=
      Adjunction.comp_unit_app _ _ _
    rw [hcomp, ← reassoc_of% hu]
  rw [← cancel_epi (((situation J K).fiberTransitionAb' φ).app
    ((Augmentation.totalInverseImageAb (situation J K) (Cat.of C) J
      (situationAugmentation J K)).obj G))]
  refine Eq.trans (b :=
    ((situation J K).transitionInverseImageAb φ).map
        ((situationComponentInverseImageSliceIso J K ⦋m⦌).hom.app G ≫
          (((situation J K).componentLowerShriekAbAdjunction' ⦋m⦌).comp
              (augmentationAbelianLowerShriekAdjunction J K)).unit.app
            (((sliceForget K (op ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u}
              ((situation J K).componentTopology ⦋m⦌) J).obj G)) ≫
      (situationTransitionInverseImageAbIso J K φ).hom.app
          (((situation J K).restrictAb ⦋m⦌).obj
            (((totalForget K).sheafPushforwardContinuous AddCommGrpCat.{u}
              ((situation J K).totalTopology) J).obj
              ((augmentationAbelianLowerShriek J K).obj
                ((SimplicialSiteSituation.componentLowerShriekAb (situation J K) ⦋m⦌).obj
                  (((sliceForget K (op ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u}
                    ((situation J K).componentTopology ⦋m⦌) J).obj G))))) ≫
        (augmentationTransitionRestrictionIso J K φ).hom.app
          ((augmentationAbelianLowerShriek J K).obj
            ((SimplicialSiteSituation.componentLowerShriekAb (situation J K) ⦋m⦌).obj
              (((sliceForget K (op ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u}
                ((situation J K).componentTopology ⦋m⦌) J).obj G)))) ?_ ?_
  · rw [← Category.assoc,
      ← componentSumFormulaLeg_comp_restrictAb_map_componentLowerShriekMap (situation J K)
        ((Augmentation.totalInverseImageAb (situation J K) (Cat.of C) J
          (situationAugmentation J K)).obj G) φ,
      Category.assoc, ← Functor.map_comp, ← Category.assoc,
      Augmentation.componentLowerShriekMap_comp_degIso_hom', ← Category.assoc, ← Functor.map_comp,
      Iso.hom_inv_id_assoc, componentSumFormulaLeg_app', Functor.map_comp, Category.assoc,
      ← reassoc_of% hnat, fiberTransitionAb_comp_restrictAb_map_augmentationUnit,
      ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc, hinner]
  · refine Eq.symm ?_
    rw [reassoc_of% (fiberTransitionAb_situationComponentInverseImageSliceIso J K φ G),
      reassoc_of% ((sliceAbelianRestrictionCompIso J K φ).hom_inv_id_app G),
      ← Functor.map_comp_assoc,
      ← reassoc_of% ((situationTransitionInverseImageAbIso J K φ).hom.naturality
        ((situationComponentInverseImageSliceIso J K ⦋m⦌).hom.app G ≫
          (((situation J K).componentLowerShriekAbAdjunction' ⦋m⦌).comp
              (augmentationAbelianLowerShriekAdjunction J K)).unit.app
            (((sliceForget K (op ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u}
              ((situation J K).componentTopology ⦋m⦌) J).obj G)))]
    exact rfl

end Goal

section SimplexMap

variable {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌)

/-- **The comparison `r_{φ!}a_!g_{m!} ≅ a_!g_{n!}` is the conjugate of the comparison of the
restrictions along the two factorizations of `j_n` through the total site.** -/
theorem conjugateEquiv_symm_augmentationTransitionRestrictionIso :
    (conjugateEquiv ((transitionAbelianLowerShriekAdjunction J K φ).comp (((situation J
      K).componentLowerShriekAbAdjunction' ⦋m⦌).comp
        (augmentationAbelianLowerShriekAdjunction J K))) (((situation J
          K).componentLowerShriekAbAdjunction' ⦋n⦌).comp
        (augmentationAbelianLowerShriekAdjunction J K))).symm (augmentationTransitionRestrictionIso
          J K φ).hom = (augmentationTransitionAbelianLowerShriekIso J K φ).inv :=
  (Equiv.symm_apply_eq _).mpr
    (Adjunction.conjugateEquiv_leftAdjointCompIso_inv (transitionAbelianLowerShriekAdjunction J K φ)
      (((situation J K).componentLowerShriekAbAdjunction' ⦋m⦌).comp
        (augmentationAbelianLowerShriekAdjunction J K)) (((situation J
          K).componentLowerShriekAbAdjunction' ⦋n⦌).comp
        (augmentationAbelianLowerShriekAdjunction J K)) (augmentationTransitionRestrictionIso J K
          φ)).symm

/-- The transpose along `j_{n!} ⊣ j_n^{-1}` of the comparison `r_{φ!}a_!g_{m!} ≅ a_!g_{n!}`
followed by a morphism is the transpose along `r_{φ!}a_!g_{m!} ⊣ a^{-1}g_m^{-1}r_φ^{-1}` of that
morphism, corrected by the comparison of the restrictions. -/
theorem homEquiv_augmentationTransitionAbelianLowerShriekIso_inv_comp
    {Y : Sheaf J AddCommGrpCat.{u}}
    (f : (augmentationAbelianLowerShriek J K).obj ((SimplicialSiteSituation.componentLowerShriekAb
      (situation J K) ⦋m⦌).obj ((transitionAbelianLowerShriek J K φ).obj (((sliceForget K (op
      ⦋n⦌)).sheafPushforwardContinuous AddCommGrpCat.{u}
        ((situation J K).componentTopology ⦋n⦌) J).obj G))) ⟶ Y) :
    (((situation J K).componentLowerShriekAbAdjunction' ⦋n⦌).comp
        (augmentationAbelianLowerShriekAdjunction J K)).homEquiv (((sliceForget K (op
          ⦋n⦌)).sheafPushforwardContinuous AddCommGrpCat.{u}
        ((situation J K).componentTopology ⦋n⦌) J).obj G) Y
          ((augmentationTransitionAbelianLowerShriekIso J K φ).inv.app (((sliceForget K (op
          ⦋n⦌)).sheafPushforwardContinuous AddCommGrpCat.{u}
        ((situation J K).componentTopology ⦋n⦌) J).obj G) ≫ f) =
      ((transitionAbelianLowerShriekAdjunction J K φ).comp (((situation J
        K).componentLowerShriekAbAdjunction' ⦋m⦌).comp
        (augmentationAbelianLowerShriekAdjunction J K))).homEquiv (((sliceForget K (op
          ⦋n⦌)).sheafPushforwardContinuous AddCommGrpCat.{u}
        ((situation J K).componentTopology ⦋n⦌) J).obj G) Y f ≫
          (augmentationTransitionRestrictionIso J K φ).hom.app Y := by
  refine Eq.trans (congrArg (fun g => (((situation J K).componentLowerShriekAbAdjunction' ⦋n⦌).comp
        (augmentationAbelianLowerShriekAdjunction J K)).homEquiv (((sliceForget K (op
          ⦋n⦌)).sheafPushforwardContinuous AddCommGrpCat.{u}
        ((situation J K).componentTopology ⦋n⦌) J).obj G) Y (g ≫ f)) ?_)
    (Stacks.CategoryTheory.homEquiv_conjugate ((transitionAbelianLowerShriekAdjunction J K φ).comp
      (((situation J K).componentLowerShriekAbAdjunction' ⦋m⦌).comp
        (augmentationAbelianLowerShriekAdjunction J K))) (((situation J
          K).componentLowerShriekAbAdjunction' ⦋n⦌).comp
        (augmentationAbelianLowerShriekAdjunction J K)) (augmentationTransitionRestrictionIso J K
          φ).hom f)
  exact congrArg (fun t => NatTrans.app t (((sliceForget K (op ⦋n⦌)).sheafPushforwardContinuous
    AddCommGrpCat.{u}
        ((situation J K).componentTopology ⦋n⦌) J).obj G))
    (conjugateEquiv_symm_augmentationTransitionRestrictionIso J K φ).symm

/-- The transpose along `j_{n!} ⊣ j_n^{-1}` of the `a_!`-image of a transpose along
`g_{n!} ⊣ g_n^{-1}`, followed by the `a_!g_{m!}`-image of a morphism on the component of degree
`m`. -/
theorem homEquiv_map_lowerShriek_counit_comp :
    (((situation J K).componentLowerShriekAbAdjunction' ⦋n⦌).comp
        (augmentationAbelianLowerShriekAdjunction J K)).homEquiv _ _
        ((augmentationAbelianLowerShriek J K).map ((SimplicialSiteSituation.componentLowerShriekAb
          (situation J K) ⦋n⦌).map ((componentRestrictionAbInverseImageIso' (situation J K) (Cat.of
          C) J
        (situationAugmentation J K) G ⦋n⦌).inv ≫ componentSheafSummand' (situation J K)
          ((Augmentation.totalInverseImageAb (situation J K) (Cat.of C) J
        (situationAugmentation J K)).obj G) φ ≫ ((situation J K).restrictAb ⦋n⦌).map
          (Augmentation.degIso' (situation J K) (Cat.of C) J (situationAugmentation J K) G m).hom) ≫
          ((situation J K).componentLowerShriekAbAdjunction' ⦋n⦌).counit.app
          (Augmentation.resolutionTerm (situation J K) (Cat.of C) J (situationAugmentation J K) G
          m)) ≫ (augmentationAbelianLowerShriek J K).map
          ((SimplicialSiteSituation.componentLowerShriekAb (situation J K) ⦋m⦌).map
          ((componentRestrictionAbInverseImageIso' (situation J K) (Cat.of C) J
        (situationAugmentation J K) G ⦋m⦌).inv ≫ ((situationComponentInverseImageSliceIso J K
          ⦋m⦌).hom.app G)))) =
      ((componentRestrictionAbInverseImageIso' (situation J K) (Cat.of C) J
        (situationAugmentation J K) G ⦋n⦌).inv ≫ componentSheafSummand' (situation J K)
          ((Augmentation.totalInverseImageAb (situation J K) (Cat.of C) J
        (situationAugmentation J K)).obj G) φ ≫ ((situation J K).restrictAb ⦋n⦌).map
          (Augmentation.degIso' (situation J K) (Cat.of C) J (situationAugmentation J K) G m).hom) ≫
          ((situation J K).restrictAb ⦋n⦌).map ((SimplicialSiteSituation.componentLowerShriekAb
          (situation J K) ⦋m⦌).map ((componentRestrictionAbInverseImageIso' (situation J K) (Cat.of
          C) J
        (situationAugmentation J K) G ⦋m⦌).inv ≫ ((situationComponentInverseImageSliceIso J K
          ⦋m⦌).hom.app G)) ≫ (augmentationAbelianLowerShriekAdjunction J K).unit.app
          ((SimplicialSiteSituation.componentLowerShriekAb (situation J K) ⦋m⦌).obj (((sliceForget K
          (op ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u}
        ((situation J K).componentTopology ⦋m⦌) J).obj G))) :=
  Stacks.CategoryTheory.homEquiv_comp_map_counit_comp ((situation J
    K).componentLowerShriekAbAdjunction' ⦋n⦌) (augmentationAbelianLowerShriekAdjunction J K)
    ((componentRestrictionAbInverseImageIso' (situation J K) (Cat.of C) J
        (situationAugmentation J K) G ⦋n⦌).inv ≫ componentSheafSummand' (situation J K)
          ((Augmentation.totalInverseImageAb (situation J K) (Cat.of C) J
        (situationAugmentation J K)).obj G) φ ≫ ((situation J K).restrictAb ⦋n⦌).map
          (Augmentation.degIso' (situation J K) (Cat.of C) J (situationAugmentation J K) G m).hom)
          ((SimplicialSiteSituation.componentLowerShriekAb (situation J K) ⦋m⦌).map
          ((componentRestrictionAbInverseImageIso' (situation J K) (Cat.of C) J
        (situationAugmentation J K) G ⦋m⦌).inv ≫ ((situationComponentInverseImageSliceIso J K
          ⦋m⦌).hom.app G)))

/-- The transpose along `r_{φ!}a_!g_{m!} ⊣ a^{-1}g_m^{-1}r_φ^{-1}` of the `a_!g_{m!}`-image of the
reindexing of `j_n^{-1}𝒢` into `r_φ^{-1}j_m^{-1}𝒢` followed by the counit of
`r_{φ!} ⊣ r_φ^{-1}`. -/
theorem homEquiv_transitionComp_map_lowerShriek_transition :
    ((transitionAbelianLowerShriekAdjunction J K φ).comp (((situation J
      K).componentLowerShriekAbAdjunction' ⦋m⦌).comp
        (augmentationAbelianLowerShriekAdjunction J K))).homEquiv _ _
          ((augmentationAbelianLowerShriek J K).map ((SimplicialSiteSituation.componentLowerShriekAb
          (situation J K) ⦋m⦌).map ((transitionAbelianLowerShriek J K φ).map
          ((sliceAbelianRestrictionCompIso J K φ).inv.app G) ≫
          (transitionAbelianLowerShriekAdjunction J K φ).counit.app (((sliceForget K (op
          ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u}
        ((situation J K).componentTopology ⦋m⦌) J).obj G)))) =
      (sliceAbelianRestrictionCompIso J K φ).inv.app G ≫ ((componentTransitionFunctor J K
        φ).sheafPushforwardContinuous AddCommGrpCat.{u}
        ((situation J K).componentTopology ⦋n⦌) ((situation J K).componentTopology ⦋m⦌)).map
          ((((situation J K).componentLowerShriekAbAdjunction' ⦋m⦌).comp
        (augmentationAbelianLowerShriekAdjunction J K)).unit.app (((sliceForget K (op
          ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u}
        ((situation J K).componentTopology ⦋m⦌) J).obj G)) := by
  refine Eq.trans (Stacks.CategoryTheory.homEquiv_comp_apply (transitionAbelianLowerShriekAdjunction
    J K φ) (((situation J K).componentLowerShriekAbAdjunction' ⦋m⦌).comp
        (augmentationAbelianLowerShriekAdjunction J K))
    ((augmentationAbelianLowerShriek J K).map ((SimplicialSiteSituation.componentLowerShriekAb
      (situation J K) ⦋m⦌).map ((transitionAbelianLowerShriek J K φ).map
      ((sliceAbelianRestrictionCompIso J K φ).inv.app G) ≫ (transitionAbelianLowerShriekAdjunction J
      K φ).counit.app (((sliceForget K (op ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u}
        ((situation J K).componentTopology ⦋m⦌) J).obj G))))) ?_
  refine Eq.trans (congrArg ((transitionAbelianLowerShriekAdjunction J K φ).homEquiv _ _)
    (Stacks.CategoryTheory.homEquiv_left_adjoint_map (((situation J
      K).componentLowerShriekAbAdjunction' ⦋m⦌).comp
        (augmentationAbelianLowerShriekAdjunction J K)) ((transitionAbelianLowerShriek J K φ).map
          ((sliceAbelianRestrictionCompIso J K φ).inv.app G) ≫
          (transitionAbelianLowerShriekAdjunction J K φ).counit.app (((sliceForget K (op
          ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u}
        ((situation J K).componentTopology ⦋m⦌) J).obj G)))) ?_
  refine Eq.trans (congrArg ((transitionAbelianLowerShriekAdjunction J K φ).homEquiv _ _)
    (Category.assoc _ _ _)) ?_
  refine Eq.trans (Adjunction.homEquiv_naturality_left (transitionAbelianLowerShriekAdjunction J K
    φ) ((sliceAbelianRestrictionCompIso J K φ).inv.app G) _) ?_
  exact congrArg (fun g => (sliceAbelianRestrictionCompIso J K φ).inv.app G ≫ g)
    (Stacks.CategoryTheory.homEquiv_counit_app_comp (transitionAbelianLowerShriekAdjunction J K φ)
      ((((situation J K).componentLowerShriekAbAdjunction' ⦋m⦌).comp
        (augmentationAbelianLowerShriekAdjunction J K)).unit.app (((sliceForget K (op
          ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u}
        ((situation J K).componentTopology ⦋m⦌) J).obj G)))

/-- The transpose along `j_{n!} ⊣ j_n^{-1}` of the right-hand side of the simplex-map
comparison. -/
theorem homEquiv_map_lowerShriek_augmentationTransition :
    (((situation J K).componentLowerShriekAbAdjunction' ⦋n⦌).comp
        (augmentationAbelianLowerShriekAdjunction J K)).homEquiv
          ((Augmentation.componentInverseImageAb (situation J K) (Cat.of C) J
          (situationAugmentation J K) ⦋n⦌).obj G) ((augmentationAbelianLowerShriek J K).obj
            ((SimplicialSiteSituation.componentLowerShriekAb (situation J K) ⦋m⦌).obj (((sliceForget
            K (op ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u}
        ((situation J K).componentTopology ⦋m⦌) J).obj G)))
        ((augmentationAbelianLowerShriek J K).map ((SimplicialSiteSituation.componentLowerShriekAb
          (situation J K) ⦋n⦌).map ((componentRestrictionAbInverseImageIso' (situation J K) (Cat.of
          C) J
        (situationAugmentation J K) G ⦋n⦌).inv ≫ ((situationComponentInverseImageSliceIso J K
          ⦋n⦌).hom.app G))) ≫ (augmentationTransitionAbelianLowerShriekIso J K φ).inv.app
          (((sliceForget K (op ⦋n⦌)).sheafPushforwardContinuous AddCommGrpCat.{u}
        ((situation J K).componentTopology ⦋n⦌) J).obj G) ≫ (augmentationAbelianLowerShriek J K).map
          ((SimplicialSiteSituation.componentLowerShriekAb (situation J K) ⦋m⦌).map
          ((transitionAbelianLowerShriek J K φ).map ((sliceAbelianRestrictionCompIso J K φ).inv.app
          G) ≫ (transitionAbelianLowerShriekAdjunction J K φ).counit.app (((sliceForget K (op
          ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u}
        ((situation J K).componentTopology ⦋m⦌) J).obj G)))) =
      ((componentRestrictionAbInverseImageIso' (situation J K) (Cat.of C) J
        (situationAugmentation J K) G ⦋n⦌).inv ≫ ((situationComponentInverseImageSliceIso J K
          ⦋n⦌).hom.app G)) ≫ ((sliceAbelianRestrictionCompIso J K φ).inv.app G ≫
          ((componentTransitionFunctor J K φ).sheafPushforwardContinuous AddCommGrpCat.{u}
        ((situation J K).componentTopology ⦋n⦌) ((situation J K).componentTopology ⦋m⦌)).map
          ((((situation J K).componentLowerShriekAbAdjunction' ⦋m⦌).comp
        (augmentationAbelianLowerShriekAdjunction J K)).unit.app (((sliceForget K (op
          ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u}
        ((situation J K).componentTopology ⦋m⦌) J).obj G))) ≫
        (augmentationTransitionRestrictionIso J K φ).hom.app ((augmentationAbelianLowerShriek J
          K).obj ((SimplicialSiteSituation.componentLowerShriekAb (situation J K) ⦋m⦌).obj
          (((sliceForget K (op ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u}
        ((situation J K).componentTopology ⦋m⦌) J).obj G))) := by
  refine Eq.trans (Stacks.CategoryTheory.homEquiv_comp_naturality_left ((situation J
    K).componentLowerShriekAbAdjunction' ⦋n⦌) (augmentationAbelianLowerShriekAdjunction J K)
    ((componentRestrictionAbInverseImageIso' (situation J K) (Cat.of C) J
        (situationAugmentation J K) G ⦋n⦌).inv ≫ ((situationComponentInverseImageSliceIso J K
          ⦋n⦌).hom.app G))
    ((augmentationTransitionAbelianLowerShriekIso J K φ).inv.app (((sliceForget K (op
      ⦋n⦌)).sheafPushforwardContinuous AddCommGrpCat.{u}
        ((situation J K).componentTopology ⦋n⦌) J).obj G) ≫ (augmentationAbelianLowerShriek J K).map
          ((SimplicialSiteSituation.componentLowerShriekAb (situation J K) ⦋m⦌).map
          ((transitionAbelianLowerShriek J K φ).map ((sliceAbelianRestrictionCompIso J K φ).inv.app
          G) ≫ (transitionAbelianLowerShriekAdjunction J K φ).counit.app (((sliceForget K (op
          ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u}
        ((situation J K).componentTopology ⦋m⦌) J).obj G))))) ?_
  refine congrArg (fun g => ((componentRestrictionAbInverseImageIso' (situation J K) (Cat.of C) J
        (situationAugmentation J K) G ⦋n⦌).inv ≫ ((situationComponentInverseImageSliceIso J K
          ⦋n⦌).hom.app G)) ≫ g) ?_
  refine Eq.trans (homEquiv_augmentationTransitionAbelianLowerShriekIso_inv_comp J K G φ
    ((augmentationAbelianLowerShriek J K).map ((SimplicialSiteSituation.componentLowerShriekAb
      (situation J K) ⦋m⦌).map ((transitionAbelianLowerShriek J K φ).map
      ((sliceAbelianRestrictionCompIso J K φ).inv.app G) ≫ (transitionAbelianLowerShriekAdjunction J
      K φ).counit.app (((sliceForget K (op ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u}
        ((situation J K).componentTopology ⦋m⦌) J).obj G))))) ?_
  exact congrArg (fun g => g ≫ (augmentationTransitionRestrictionIso J K φ).hom.app
    ((augmentationAbelianLowerShriek J K).obj ((SimplicialSiteSituation.componentLowerShriekAb
    (situation J K) ⦋m⦌).obj (((sliceForget K (op ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u}
        ((situation J K).componentTopology ⦋m⦌) J).obj G))))
    (homEquiv_transitionComp_map_lowerShriek_transition J K G φ)

/-- **The simplex maps of the resolution of Stacks 0D78 after extension by zero along the
augmentation.** For a simplex map `φ : ⦋m⦌ ⟶ ⦋n⦌` the `a_!`-image of the structure map of the
resolution of `a^{-1}𝒢`, conjugated by the degreewise identifications of its terms and then by
the identification of `a_p^{-1}𝒢` with the restriction `j_p^{-1}𝒢`, is the comparison
`r_{φ!}a_!g_{m!} ≅ a_!g_{n!}` followed by the `a_!g_{m!}`-image of the reindexing of `j_n^{-1}𝒢`
into `r_φ^{-1}j_m^{-1}𝒢` and the counit of `r_{φ!} ⊣ r_φ^{-1}`.

The right-hand side is the shriek restriction transition of Stacks 0D87 at `φ`, read through the
comparison of `a_!g_{p!}` with `j_{p!}`: that is
`CategoryTheory.SimplicialSemiRepresentable`
`.shriekRestrictionTransition_app_sliceAbelianLowerShriekCompIso` together with
`CategoryTheory.SimplicialSemiRepresentable`
`.componentLowerShriekCompAugmentationAbelianIso_transition`.
So this is the naturality in the simplex map that the comparison of the resolution of Stacks 0D78
with the complex of Stacks 01GE needs.

Both sides are morphisms out of `a_!g_{n!}(a_n^{-1}𝒢)`, so they are equal as soon as their
transposes along `j_{n!} ⊣ j_n^{-1}` are, and those are
`homEquiv_map_lowerShriek_counit_comp` and `homEquiv_map_lowerShriek_augmentationTransition`. -/
theorem map_degIso_inv_comp_barSimplicial_map_comp_degIso_hom_slice :
    (augmentationAbelianLowerShriek J K).map
          ((Augmentation.degIso' (situation J K) (Cat.of C) J (situationAugmentation J K) G n).inv ≫
            ((barSimplicial' (situation J K)).obj ((Augmentation.totalInverseImageAb (situation J K)
              (Cat.of C) J
        (situationAugmentation J K)).obj G)).map φ.op ≫ (Augmentation.degIso' (situation J K)
          (Cat.of C) J (situationAugmentation J K) G m).hom) ≫
        (augmentationAbelianLowerShriek J K).map ((SimplicialSiteSituation.componentLowerShriekAb
          (situation J K) ⦋m⦌).map ((componentRestrictionAbInverseImageIso' (situation J K) (Cat.of
          C) J
        (situationAugmentation J K) G ⦋m⦌).inv ≫ ((situationComponentInverseImageSliceIso J K
          ⦋m⦌).hom.app G))) =
      (augmentationAbelianLowerShriek J K).map ((SimplicialSiteSituation.componentLowerShriekAb
        (situation J K) ⦋n⦌).map ((componentRestrictionAbInverseImageIso' (situation J K) (Cat.of C)
        J
        (situationAugmentation J K) G ⦋n⦌).inv ≫ ((situationComponentInverseImageSliceIso J K
          ⦋n⦌).hom.app G))) ≫
        (augmentationTransitionAbelianLowerShriekIso J K φ).inv.app (((sliceForget K (op
          ⦋n⦌)).sheafPushforwardContinuous AddCommGrpCat.{u}
        ((situation J K).componentTopology ⦋n⦌) J).obj G) ≫ (augmentationAbelianLowerShriek J K).map
          ((SimplicialSiteSituation.componentLowerShriekAb (situation J K) ⦋m⦌).map
          ((transitionAbelianLowerShriek J K φ).map ((sliceAbelianRestrictionCompIso J K φ).inv.app
          G) ≫ (transitionAbelianLowerShriekAdjunction J K φ).counit.app (((sliceForget K (op
          ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u}
        ((situation J K).componentTopology ⦋m⦌) J).obj G))) := by
  refine ((((situation J K).componentLowerShriekAbAdjunction' ⦋n⦌).comp
        (augmentationAbelianLowerShriekAdjunction J K)).homEquiv _ _).injective ?_
  rw [Augmentation.degIso_inv_comp_barSimplicial_map_comp_degIso_hom,
    homEquiv_map_lowerShriek_counit_comp, homEquiv_map_lowerShriek_augmentationTransition]
  have h := congrArg ((componentRestrictionAbInverseImageIso' (situation J K) (Cat.of C) J
    (situationAugmentation J K) G ⦋n⦌).inv ≫ ·)
    (componentSheafSummand_comp_restrictAb_map_degIso_slice J K G φ)
  simpa only [Category.assoc, Functor.map_comp] using h

end SimplexMap

end CategoryTheory.SimplicialSemiRepresentable

end
