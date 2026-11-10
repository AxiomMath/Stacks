module

public import
  StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationResolutionLowerShriekSimplexMap
public import
  StacksFrontier.CategoryTheory.Sites.Simplicial.SliceAbelianLowerShriekFreeYonedaSimplicial
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SliceFreeAbelianLowerShriekNaturalityOfEq
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SliceShriekRestrictionTransitionCompIso

/-!
# The `a_!`-image of the resolution of Stacks 0D78 at `ℤ_V^♯` is the complex of Stacks 01GE

Let `(C, J)` be a site with fibre products, `K` a simplicial semi-representable object with
augmentation `a` of Stacks 0D8B, and `V` an object of `C`. The resolution of Stacks 0D78 of
`a^{-1}ℤ_V^♯` has degree-`p` term `g_{p!}(a_p^{-1}ℤ_V^♯)`, and
`CategoryTheory.SimplicialSemiRepresentable.augmentationComponentFreeYonedaIso` identifies its
`a_!`-image with the free abelian sheaf `ℤ_{h_V × F(K_p)}^♯`. That identification is degreewise;
this module proves it natural in the simplex maps, which is the one thing the comparison of the
resolution of Stacks 0D78 with the complex of Stacks 01GE was missing.

The `a_!`-image of the simplex maps is computed by
`CategoryTheory.SimplicialSemiRepresentable`
`.map_degIso_inv_comp_barSimplicial_map_comp_degIso_hom_slice`, which gives them as the shriek
restriction transitions of Stacks 0D87 read through the comparison `a_!g_{p!} ≅ j_{p!}`; the
simplex maps of the carrier `p ↦ a_!g_{p!}j_p^{-1}ℤ_V^♯` are the transported ones of a
`CategoryTheory.Functor.copyObj`, and
`augmentationComponentFreeYonedaSimplicial_map_eq_augmentationTransition` identifies them with the
same transitions. The two computations meet in
`map_barSimplicial_map_comp_degIso_slice`, which is the naturality square.

## Main definitions

* `CategoryTheory.SimplicialSemiRepresentable.resolutionLowerShriekFreeYonedaIsoApp`: the
  degreewise comparison.
* `CategoryTheory.SimplicialSemiRepresentable.resolutionLowerShriekFreeYonedaIso`: **the
  `a_!`-image of the resolving simplicial object of Stacks 0D78 of `a^{-1}ℤ_V^♯` is
  `p ↦ a_!g_{p!}j_p^{-1}ℤ_V^♯`, as simplicial abelian sheaves.**
* `CategoryTheory.SimplicialSemiRepresentable.resolutionLowerShriekFreeYonedaSimplicialIso`: and
  hence it is `p ↦ ℤ_{h_V × F(K_p)}^♯`, the simplicial abelian sheaf the complex of Stacks 01GE
  for the hypercovering multiplied by `h_V` is built from.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable`
  `.augmentationComponentFreeYonedaSimplicial_map_eq_augmentationTransition`: the transported
  simplex maps of the carrier are the shriek restriction transitions.
* `CategoryTheory.SimplicialSemiRepresentable.map_barSimplicial_map_comp_degIso_slice`: the
  naturality square.

## Implementation notes

The topologies of the two simplicial degrees are only propositionally the componentwise localized
ones, so the shriek restriction transition cannot be written at them by instance search; it is
reached by `CategoryTheory.SemiRepresentable.hasWeakSheafifyComponentOver`, exactly as in
`StacksFrontier/CategoryTheory/Sites/Simplicial/SliceShriekRestrictionTransitionCompIso.lean`.

Three of the lemmas below are stated against a trailing morphism `h` rather than as plain
equalities. The reason: `reassoc_of%` and `simp only [Category.assoc]` do not reach
right-associated normal form in these goals -- the two spellings of the component site defeat the
`isDefEq` checks the normalisation needs -- so an equality of two-factor composites cannot be
rewritten inside a longer right-associated composite. Carrying the trailing morphism in the
statement removes the need for any reassociation at the point of use.

No `@[stacks]` attribute is placed: the degreewise identification carries the tags it realizes,
and what is added here is its naturality.

## References

* [Stacks Project, Tag 0D78](https://stacks.math.columbia.edu/tag/0D78)
* [Stacks Project, Tag 0D87](https://stacks.math.columbia.edu/tag/0D87)
* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
* [Stacks Project, Tag 09WM](https://stacks.math.columbia.edu/tag/09WM)
* [Stacks Project, Tag 01GE](https://stacks.math.columbia.edu/tag/01GE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SimplicialSiteSituation
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

open SemiRepresentable

attribute [local instance] GrothendieckTopology.hasSheafify_addCommGrpCat

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (K : SimplicialObject (FormalCoproduct.{u} C)) [J.toCoverage.HasPullbacks]
  [J.WEqualsLocallyBijective (Type u)] (V : C)

variable {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌)

/-- **Stacks 0D87 part (2) at `ℤ_V^♯` along a simplex map, at the topologies of the two simplicial
degrees.** The degreewise identification `j_{p!}j_p^{-1}ℤ_V^♯ ≅ ℤ_{h_V × F(K_p)}^♯` carries the
shriek restriction transition of `K_φ : K_n ⟶ K_m` to the map `ℤ_{h_V × F(K_n)}^♯ ⟶
ℤ_{h_V × F(K_m)}^♯` induced by `F(K_φ)`.

This is `CategoryTheory.SemiRepresentable`
`.shriekRestrictionTransition_comp_freeYonedaSheafPushforwardPullbackIsoOfEq` read at the
component topologies of the simplicial degrees, which is where
`CategoryTheory.SimplicialSemiRepresentable.sliceFreeYonedaLowerShriekIso` lives. -/
theorem shriekRestrictionTransition_freeYoneda_eq :
    haveI := hasWeakSheafifyComponentOver (L := K.obj (op ⦋n⦌))
      ((situation J K).componentTopology ⦋n⦌)
    haveI := hasWeakSheafifyComponentOver (L := K.obj (op ⦋m⦌))
      ((situation J K).componentTopology ⦋m⦌)
    haveI : (componentOverForget (K.obj (op ⦋n⦌))).IsContinuous
        ((situation J K).componentTopology ⦋n⦌) J := sliceForget_isContinuous J K ⦋n⦌
    haveI : (componentOverForget (K.obj (op ⦋m⦌))).IsContinuous
        ((situation J K).componentTopology ⦋m⦌) J := sliceForget_isContinuous J K ⦋m⦌
    (sliceFreeYonedaLowerShriekIso J K ⦋n⦌ V).hom ≫ (freeYonedaProd J V).map (K.map φ.op) =
      (shriekRestrictionTransition J (K.map φ.op) ((situation J K).componentTopology ⦋n⦌)
          ((situation J K).componentTopology ⦋m⦌) AddCommGrpCat.{u}).app
            (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V) ≫
        (sliceFreeYonedaLowerShriekIso J K ⦋m⦌ V).hom := by
  have := hasWeakSheafifyComponentOver (L := K.obj (op ⦋n⦌))
    ((situation J K).componentTopology ⦋n⦌)
  have := hasWeakSheafifyComponentOver (L := K.obj (op ⦋m⦌))
    ((situation J K).componentTopology ⦋m⦌)
  have : (componentOverForget (K.obj (op ⦋n⦌))).IsContinuous
      ((situation J K).componentTopology ⦋n⦌) J := sliceForget_isContinuous J K ⦋n⦌
  have : (componentOverForget (K.obj (op ⦋m⦌))).IsContinuous
      ((situation J K).componentTopology ⦋m⦌) J := sliceForget_isContinuous J K ⦋m⦌
  exact (shriekRestrictionTransition_comp_freeYonedaSheafPushforwardPullbackIsoOfEq J
    (K.map φ.op) (componentTopology_eq J K ⦋n⦌) (componentTopology_eq J K ⦋m⦌) V).symm


omit [J.WEqualsLocallyBijective (Type u)] in
/-- **The identification `a_!g_{p!} ≅ j_{p!}` turns the composition comparison of the `j_{p!}` into
the comparison of the composites through the total site.** This is
`componentLowerShriekCompAugmentationAbelianIso_transition` with the two isomorphisms moved to the
other side. -/
theorem componentLowerShriekCompAugmentationAbelianIso_hom_app_comp_sliceCompIso_inv
    (Y : Sheaf ((situation J K).componentTopology ⦋n⦌) AddCommGrpCat.{u}) :
    (componentLowerShriekCompAugmentationAbelianIso J K ⦋n⦌).hom.app Y ≫
      (sliceAbelianLowerShriekCompIso J K φ).inv.app Y =
      (augmentationTransitionAbelianLowerShriekIso J K φ).inv.app Y ≫
        (componentLowerShriekCompAugmentationAbelianIso J K ⦋m⦌).hom.app
        ((transitionAbelianLowerShriek J K φ).obj Y) := by
  have h : (componentLowerShriekCompAugmentationAbelianIso J K ⦋m⦌).hom.app
    ((transitionAbelianLowerShriek J K φ).obj Y) ≫ (sliceAbelianLowerShriekCompIso J K φ).hom.app Y
    =
      (augmentationTransitionAbelianLowerShriekIso J K φ).hom.app Y ≫
        (componentLowerShriekCompAugmentationAbelianIso J K ⦋n⦌).hom.app Y :=
    congrArg (fun e => NatTrans.app (Iso.hom e) Y)
      (componentLowerShriekCompAugmentationAbelianIso_transition J K φ)
  refine (Iso.comp_inv_eq ((sliceAbelianLowerShriekCompIso J K φ).app Y)).mpr ?_
  refine Eq.trans (((augmentationTransitionAbelianLowerShriekIso J K φ).app Y).inv_hom_id_assoc
    ((componentLowerShriekCompAugmentationAbelianIso J K ⦋n⦌).hom.app Y)).symm ?_
  refine Eq.trans (congrArg (fun g => (augmentationTransitionAbelianLowerShriekIso J K φ).inv.app Y
    ≫ g) h.symm) ?_
  exact (Category.assoc _ _ _).symm

/-- `shriekRestrictionTransition_freeYoneda_eq` followed by
`shriekRestrictionTransition_app_sliceAbelianLowerShriekCompIso`, stated against a trailing
morphism so that it applies in a right-associated composite. -/
theorem sliceFreeYonedaLowerShriekIso_hom_comp_freeYonedaProd_map_comp
    {W : Sheaf J AddCommGrpCat.{u}} (h : (freeYonedaProd J V).obj (K.obj (op ⦋m⦌)) ⟶ W) :
    (sliceFreeYonedaLowerShriekIso J K ⦋n⦌ V).hom ≫ (freeYonedaProd J V).map (K.map φ.op) ≫ h =
      (sliceAbelianLowerShriekCompIso J K φ).inv.app (((sliceForget K (op
        ⦋n⦌)).sheafPushforwardContinuous AddCommGrpCat.{u} ((situation J K).componentTopology ⦋n⦌)
        J).obj (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)) ≫
        (sliceAbelianLowerShriek J K ⦋m⦌).map ((transitionAbelianLowerShriek J K φ).map
        ((sliceAbelianRestrictionCompIso J K φ).inv.app
        (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)) ≫
        (transitionAbelianLowerShriekAdjunction J K φ).counit.app (((sliceForget K (op
        ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u} ((situation J K).componentTopology ⦋m⦌)
        J).obj (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V))) ≫
        (sliceFreeYonedaLowerShriekIso J K ⦋m⦌ V).hom ≫ h := by
  have hcomb : (sliceFreeYonedaLowerShriekIso J K ⦋n⦌ V).hom ≫ (freeYonedaProd J V).map (K.map φ.op)
    =
      ((sliceAbelianLowerShriekCompIso J K φ).inv.app (((sliceForget K (op
        ⦋n⦌)).sheafPushforwardContinuous AddCommGrpCat.{u} ((situation J K).componentTopology ⦋n⦌)
        J).obj (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)) ≫
        (sliceAbelianLowerShriek J K ⦋m⦌).map ((transitionAbelianLowerShriek J K φ).map
        ((sliceAbelianRestrictionCompIso J K φ).inv.app
        (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)) ≫
        (transitionAbelianLowerShriekAdjunction J K φ).counit.app (((sliceForget K (op
        ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u} ((situation J K).componentTopology ⦋m⦌)
        J).obj (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)))) ≫
        (sliceFreeYonedaLowerShriekIso J K ⦋m⦌ V).hom :=
    (shriekRestrictionTransition_freeYoneda_eq J K V φ).trans
      (congrArg (fun g => g ≫ (sliceFreeYonedaLowerShriekIso J K ⦋m⦌ V).hom)
        (shriekRestrictionTransition_app_sliceAbelianLowerShriekCompIso J K φ
          (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)))
  exact Eq.trans (Category.assoc _ _ _).symm
    (Eq.trans (congrArg (fun g => g ≫ h) hcomb)
      (Eq.trans (Category.assoc _ _ _) (Category.assoc _ _ _)))

omit [J.WEqualsLocallyBijective (Type u)] in
/-- `componentLowerShriekCompAugmentationAbelianIso_hom_app_comp_sliceCompIso_inv` against a
trailing morphism. -/
theorem componentLowerShriekCompAugmentationAbelianIso_hom_app_comp_sliceCompIso_inv_comp
    {W : Sheaf J AddCommGrpCat.{u}} (h : (sliceAbelianLowerShriek J K ⦋m⦌).obj
      ((transitionAbelianLowerShriek J K φ).obj (((sliceForget K (op
      ⦋n⦌)).sheafPushforwardContinuous AddCommGrpCat.{u} ((situation J K).componentTopology ⦋n⦌)
      J).obj (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V))) ⟶ W) :
    (componentLowerShriekCompAugmentationAbelianIso J K ⦋n⦌).hom.app (((sliceForget K (op
      ⦋n⦌)).sheafPushforwardContinuous AddCommGrpCat.{u} ((situation J K).componentTopology ⦋n⦌)
      J).obj (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)) ≫
      (sliceAbelianLowerShriekCompIso J K φ).inv.app (((sliceForget K (op
      ⦋n⦌)).sheafPushforwardContinuous AddCommGrpCat.{u} ((situation J K).componentTopology ⦋n⦌)
      J).obj (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)) ≫ h =
      (augmentationTransitionAbelianLowerShriekIso J K φ).inv.app (((sliceForget K (op
        ⦋n⦌)).sheafPushforwardContinuous AddCommGrpCat.{u} ((situation J K).componentTopology ⦋n⦌)
        J).obj (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)) ≫
        (componentLowerShriekCompAugmentationAbelianIso J K ⦋m⦌).hom.app
        ((transitionAbelianLowerShriek J K φ).obj (((sliceForget K (op
        ⦋n⦌)).sheafPushforwardContinuous AddCommGrpCat.{u} ((situation J K).componentTopology ⦋n⦌)
        J).obj (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V))) ≫ h :=
  Eq.trans (Category.assoc _ _ _).symm
    (Eq.trans
      (congrArg (fun g => g ≫ h)
        (componentLowerShriekCompAugmentationAbelianIso_hom_app_comp_sliceCompIso_inv J K φ
          (((sliceForget K (op ⦋n⦌)).sheafPushforwardContinuous AddCommGrpCat.{u} ((situation J
          K).componentTopology ⦋n⦌) J).obj (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J
          V))))
      (Category.assoc _ _ _))

omit [J.WEqualsLocallyBijective (Type u)] in
/-- The naturality of `a_!g_{m!} ≅ j_{m!}` read as a conjugation: the `j_{m!}`-image of a morphism
of the component of degree `m`, conjugated by the identification, is its `a_!g_{m!}`-image. -/
theorem componentLowerShriekCompAugmentationAbelianIso_hom_app_comp_map_comp_inv_app :
    (componentLowerShriekCompAugmentationAbelianIso J K ⦋m⦌).hom.app ((transitionAbelianLowerShriek
      J K φ).obj (((sliceForget K (op ⦋n⦌)).sheafPushforwardContinuous AddCommGrpCat.{u} ((situation
      J K).componentTopology ⦋n⦌) J).obj (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J
      V))) ≫ (sliceAbelianLowerShriek J K ⦋m⦌).map ((transitionAbelianLowerShriek J K φ).map
      ((sliceAbelianRestrictionCompIso J K φ).inv.app
      (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)) ≫
      (transitionAbelianLowerShriekAdjunction J K φ).counit.app (((sliceForget K (op
      ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u} ((situation J K).componentTopology ⦋m⦌)
      J).obj (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V))) ≫
      (componentLowerShriekCompAugmentationAbelianIso J K ⦋m⦌).inv.app (((sliceForget K (op
      ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u} ((situation J K).componentTopology ⦋m⦌)
      J).obj (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)) =
      (augmentationAbelianLowerShriek J K).map ((SimplicialSiteSituation.componentLowerShriekAb
        (situation J K) ⦋m⦌).map ((transitionAbelianLowerShriek J K φ).map
        ((sliceAbelianRestrictionCompIso J K φ).inv.app
        (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)) ≫
        (transitionAbelianLowerShriekAdjunction J K φ).counit.app (((sliceForget K (op
        ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u} ((situation J K).componentTopology ⦋m⦌)
        J).obj (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)))) :=
  Eq.trans (Category.assoc _ _ _).symm
    ((Iso.comp_inv_eq ((componentLowerShriekCompAugmentationAbelianIso J K ⦋m⦌).app (((sliceForget K
      (op ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u} ((situation J K).componentTopology ⦋m⦌)
      J).obj (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)))).mpr
      ((componentLowerShriekCompAugmentationAbelianIso J K ⦋m⦌).hom.naturality
      ((transitionAbelianLowerShriek J K φ).map ((sliceAbelianRestrictionCompIso J K φ).inv.app
      (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)) ≫
      (transitionAbelianLowerShriekAdjunction J K φ).counit.app (((sliceForget K (op
      ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u} ((situation J K).componentTopology ⦋m⦌)
      J).obj (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)))).symm)

/-- **The identification `a_!g_{p!}j_p^{-1}ℤ_V^♯ ≅ ℤ_{h_V × F(K_p)}^♯` carries the simplex map of
`p ↦ ℤ_{h_V × F(K_p)}^♯` to the comparison `r_{φ!}a_!g_{m!} ≅ a_!g_{n!}` followed by the
`a_!g_{m!}`-image of the reindexing and the counit of `r_{φ!} ⊣ r_φ^{-1}`.** -/
theorem augmentationComponentFreeYonedaIso_hom_comp_freeYonedaProd_map :
    (augmentationComponentFreeYonedaIso J K ⦋n⦌ V).hom ≫ (freeYonedaProd J V).map (K.map φ.op) ≫
      (augmentationComponentFreeYonedaIso J K ⦋m⦌ V).inv =
      (augmentationTransitionAbelianLowerShriekIso J K φ).inv.app (((sliceForget K (op
        ⦋n⦌)).sheafPushforwardContinuous AddCommGrpCat.{u} ((situation J K).componentTopology ⦋n⦌)
        J).obj (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)) ≫
        (augmentationAbelianLowerShriek J K).map ((SimplicialSiteSituation.componentLowerShriekAb
        (situation J K) ⦋m⦌).map ((transitionAbelianLowerShriek J K φ).map
        ((sliceAbelianRestrictionCompIso J K φ).inv.app
        (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)) ≫
        (transitionAbelianLowerShriekAdjunction J K φ).counit.app (((sliceForget K (op
        ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u} ((situation J K).componentTopology ⦋m⦌)
        J).obj (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)))) := by
  change ((componentLowerShriekCompAugmentationAbelianIso J K ⦋n⦌).hom.app (((sliceForget K (op
    ⦋n⦌)).sheafPushforwardContinuous AddCommGrpCat.{u} ((situation J K).componentTopology ⦋n⦌)
    J).obj (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)) ≫
    (sliceFreeYonedaLowerShriekIso J K ⦋n⦌ V).hom) ≫ (freeYonedaProd J V).map (K.map φ.op) ≫
      ((sliceFreeYonedaLowerShriekIso J K ⦋m⦌ V).inv ≫
        (componentLowerShriekCompAugmentationAbelianIso J K ⦋m⦌).inv.app (((sliceForget K (op
        ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u} ((situation J K).componentTopology ⦋m⦌)
        J).obj (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V))) =
    (augmentationTransitionAbelianLowerShriekIso J K φ).inv.app (((sliceForget K (op
      ⦋n⦌)).sheafPushforwardContinuous AddCommGrpCat.{u} ((situation J K).componentTopology ⦋n⦌)
      J).obj (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)) ≫
      (augmentationAbelianLowerShriek J K).map ((SimplicialSiteSituation.componentLowerShriekAb
      (situation J K) ⦋m⦌).map ((transitionAbelianLowerShriek J K φ).map
      ((sliceAbelianRestrictionCompIso J K φ).inv.app
      (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)) ≫
      (transitionAbelianLowerShriekAdjunction J K φ).counit.app (((sliceForget K (op
      ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u} ((situation J K).componentTopology ⦋m⦌)
      J).obj (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V))))
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun g => (componentLowerShriekCompAugmentationAbelianIso J K
    ⦋n⦌).hom.app (((sliceForget K (op ⦋n⦌)).sheafPushforwardContinuous AddCommGrpCat.{u} ((situation
    J K).componentTopology ⦋n⦌) J).obj (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)) ≫
    g)
    (sliceFreeYonedaLowerShriekIso_hom_comp_freeYonedaProd_map_comp J K V φ
      ((sliceFreeYonedaLowerShriekIso J K ⦋m⦌ V).inv ≫
        (componentLowerShriekCompAugmentationAbelianIso J K ⦋m⦌).inv.app (((sliceForget K (op
        ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u} ((situation J K).componentTopology ⦋m⦌)
        J).obj (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V))))) ?_
  refine Eq.trans (congrArg (fun g => (componentLowerShriekCompAugmentationAbelianIso J K
    ⦋n⦌).hom.app (((sliceForget K (op ⦋n⦌)).sheafPushforwardContinuous AddCommGrpCat.{u} ((situation
    J K).componentTopology ⦋n⦌) J).obj (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)) ≫
    (sliceAbelianLowerShriekCompIso J K φ).inv.app (((sliceForget K (op
    ⦋n⦌)).sheafPushforwardContinuous AddCommGrpCat.{u} ((situation J K).componentTopology ⦋n⦌)
    J).obj (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)) ≫
    (sliceAbelianLowerShriek J K ⦋m⦌).map ((transitionAbelianLowerShriek J K φ).map
      ((sliceAbelianRestrictionCompIso J K φ).inv.app
      (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)) ≫
      (transitionAbelianLowerShriekAdjunction J K φ).counit.app (((sliceForget K (op
      ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u} ((situation J K).componentTopology ⦋m⦌)
      J).obj (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V))) ≫ g)
      ((sliceFreeYonedaLowerShriekIso J K ⦋m⦌ V).hom_inv_id_assoc
      ((componentLowerShriekCompAugmentationAbelianIso J K ⦋m⦌).inv.app (((sliceForget K (op
      ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u} ((situation J K).componentTopology ⦋m⦌)
      J).obj (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V))))) ?_
  refine Eq.trans
    (componentLowerShriekCompAugmentationAbelianIso_hom_app_comp_sliceCompIso_inv_comp J K V φ
      ((sliceAbelianLowerShriek J K ⦋m⦌).map ((transitionAbelianLowerShriek J K φ).map
        ((sliceAbelianRestrictionCompIso J K φ).inv.app
        (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)) ≫
        (transitionAbelianLowerShriekAdjunction J K φ).counit.app (((sliceForget K (op
        ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u} ((situation J K).componentTopology ⦋m⦌)
        J).obj (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V))) ≫
        (componentLowerShriekCompAugmentationAbelianIso J K ⦋m⦌).inv.app (((sliceForget K (op
        ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u} ((situation J K).componentTopology ⦋m⦌)
        J).obj (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)))) ?_
  exact congrArg (fun g => (augmentationTransitionAbelianLowerShriekIso J K φ).inv.app
    (((sliceForget K (op ⦋n⦌)).sheafPushforwardContinuous AddCommGrpCat.{u} ((situation J
    K).componentTopology ⦋n⦌) J).obj (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)) ≫
    g)
    (componentLowerShriekCompAugmentationAbelianIso_hom_app_comp_map_comp_inv_app J K V φ)

/-- **The simplex maps of the carrier `p ↦ a_!g_{p!}j_p^{-1}ℤ_V^♯`.** Its simplex maps are
transported ones, this being a `CategoryTheory.Functor.copyObj`; this identifies them with the
shriek restriction transitions of Stacks 0D87 read through the comparison `a_!g_{p!} ≅ j_{p!}`,
which is the form `map_degIso_inv_comp_barSimplicial_map_comp_degIso_hom_slice` produces. -/
theorem augmentationComponentFreeYonedaSimplicial_map_eq_augmentationTransition :
    (augmentationComponentFreeYonedaSimplicial J K V).map φ.op =
      (augmentationTransitionAbelianLowerShriekIso J K φ).inv.app (((sliceForget K (op
        ⦋n⦌)).sheafPushforwardContinuous AddCommGrpCat.{u} ((situation J K).componentTopology ⦋n⦌)
        J).obj (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)) ≫
        (augmentationAbelianLowerShriek J K).map ((SimplicialSiteSituation.componentLowerShriekAb
        (situation J K) ⦋m⦌).map ((transitionAbelianLowerShriek J K φ).map
        ((sliceAbelianRestrictionCompIso J K φ).inv.app
        (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)) ≫
        (transitionAbelianLowerShriekAdjunction J K φ).counit.app (((sliceForget K (op
        ⦋m⦌)).sheafPushforwardContinuous AddCommGrpCat.{u} ((situation J K).componentTopology ⦋m⦌)
        J).obj (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)))) :=
  (augmentationComponentFreeYonedaSimplicial_map_eq J K V φ.op).trans
    (augmentationComponentFreeYonedaIso_hom_comp_freeYonedaProd_map J K V φ)


/-- **The naturality of the degreewise comparison of the `a_!`-image of the resolution of
Stacks 0D78 of `a^{-1}ℤ_V^♯` with `p ↦ a_!g_{p!}j_p^{-1}ℤ_V^♯`.** This is the naturality square of
`resolutionLowerShriekFreeYonedaIso`, and the whole content of it is the simplex-map comparison
`map_degIso_inv_comp_barSimplicial_map_comp_degIso_hom_slice` together with the computation
`augmentationComponentFreeYonedaSimplicial_map_eq_augmentationTransition` of the carrier's
transported simplex maps. -/
theorem map_barSimplicial_map_comp_degIso_slice :
    (augmentationAbelianLowerShriek J K).map (((barSimplicial' (situation J K)).obj
      ((Augmentation.totalInverseImageAb (situation J K) (Cat.of C) J (situationAugmentation J
      K)).obj (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V))).map φ.op) ≫
        (augmentationAbelianLowerShriek J K).map (Augmentation.degIso' (situation J K) (Cat.of C) J
          (situationAugmentation J K) (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)
          m).hom ≫ (augmentationAbelianLowerShriek J K).map
          ((SimplicialSiteSituation.componentLowerShriekAb (situation J K) ⦋m⦌).map
          ((componentRestrictionAbInverseImageIso' (situation J K) (Cat.of C) J
          (situationAugmentation J K) (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)
          ⦋m⦌).inv ≫ (situationComponentInverseImageSliceIso J K ⦋m⦌).hom.app
          (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V))) =
      ((augmentationAbelianLowerShriek J K).map (Augmentation.degIso' (situation J K) (Cat.of C) J
        (situationAugmentation J K) (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)
        n).hom ≫ (augmentationAbelianLowerShriek J K).map
        ((SimplicialSiteSituation.componentLowerShriekAb (situation J K) ⦋n⦌).map
        ((componentRestrictionAbInverseImageIso' (situation J K) (Cat.of C) J (situationAugmentation
        J K) (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V) ⦋n⦌).inv ≫
        (situationComponentInverseImageSliceIso J K ⦋n⦌).hom.app
        (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)))) ≫
        (augmentationComponentFreeYonedaSimplicial J K V).map φ.op := by
  have hmc : (augmentationAbelianLowerShriek J K).map ((Augmentation.degIso' (situation J K) (Cat.of
    C) J (situationAugmentation J K) (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)
    n).inv ≫
        ((barSimplicial' (situation J K)).obj ((Augmentation.totalInverseImageAb (situation J K)
          (Cat.of C) J (situationAugmentation J K)).obj
          (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V))).map φ.op ≫
          (Augmentation.degIso' (situation J K) (Cat.of C) J (situationAugmentation J K)
          (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V) m).hom) =
      (augmentationAbelianLowerShriek J K).map (Augmentation.degIso' (situation J K) (Cat.of C) J
        (situationAugmentation J K) (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)
        n).inv ≫ (augmentationAbelianLowerShriek J K).map (((barSimplicial' (situation J K)).obj
        ((Augmentation.totalInverseImageAb (situation J K) (Cat.of C) J (situationAugmentation J
        K)).obj (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V))).map φ.op) ≫
        (augmentationAbelianLowerShriek J K).map (Augmentation.degIso' (situation J K) (Cat.of C) J
          (situationAugmentation J K) (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)
          m).hom := by
    rw [Functor.map_comp, Functor.map_comp]
  have hchain : (augmentationAbelianLowerShriek J K).map (Augmentation.degIso' (situation J K)
    (Cat.of C) J (situationAugmentation J K) (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J
    V) n).inv ≫
        (augmentationAbelianLowerShriek J K).map (((barSimplicial' (situation J K)).obj
          ((Augmentation.totalInverseImageAb (situation J K) (Cat.of C) J (situationAugmentation J
          K)).obj (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V))).map φ.op) ≫
          (augmentationAbelianLowerShriek J K).map (Augmentation.degIso' (situation J K)
            (Cat.of C) J
            (situationAugmentation J K) (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)
            m).hom ≫ (augmentationAbelianLowerShriek J K).map
            ((SimplicialSiteSituation.componentLowerShriekAb (situation J K) ⦋m⦌).map
            ((componentRestrictionAbInverseImageIso' (situation J K) (Cat.of C) J
            (situationAugmentation J K) (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)
            ⦋m⦌).inv ≫ (situationComponentInverseImageSliceIso J K ⦋m⦌).hom.app
            (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V))) =
      (augmentationAbelianLowerShriek J K).map ((SimplicialSiteSituation.componentLowerShriekAb
        (situation J K) ⦋n⦌).map ((componentRestrictionAbInverseImageIso' (situation J K) (Cat.of C)
        J (situationAugmentation J K) (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)
        ⦋n⦌).inv ≫ (situationComponentInverseImageSliceIso J K ⦋n⦌).hom.app
        (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V))) ≫
        (augmentationComponentFreeYonedaSimplicial J K V).map φ.op := by
    refine Eq.trans
      (Eq.trans
        (congrArg (fun g => (augmentationAbelianLowerShriek J K).map
          (Augmentation.degIso' (situation J K) (Cat.of C) J (situationAugmentation J K)
          (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V) n).inv ≫ g)
          (Category.assoc ((augmentationAbelianLowerShriek J K).map (((barSimplicial' (situation J
            K)).obj ((Augmentation.totalInverseImageAb (situation J K) (Cat.of C) J
            (situationAugmentation J K)).obj (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J
            V))).map φ.op))
            ((augmentationAbelianLowerShriek J K).map (Augmentation.degIso' (situation J K) (Cat.of
              C) J (situationAugmentation J K) (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf
              J V) m).hom) ((augmentationAbelianLowerShriek J K).map
              ((SimplicialSiteSituation.componentLowerShriekAb (situation J K) ⦋m⦌).map
              ((componentRestrictionAbInverseImageIso' (situation J K) (Cat.of C) J
              (situationAugmentation J K) (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)
              ⦋m⦌).inv ≫ (situationComponentInverseImageSliceIso J K ⦋m⦌).hom.app
              (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V))))).symm)
        (Category.assoc ((augmentationAbelianLowerShriek J K).map (Augmentation.degIso' (situation J
          K) (Cat.of C) J (situationAugmentation J K)
          (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V) n).inv) _
          ((augmentationAbelianLowerShriek J K).map ((SimplicialSiteSituation.componentLowerShriekAb
          (situation J K) ⦋m⦌).map ((componentRestrictionAbInverseImageIso' (situation J K) (Cat.of
          C) J (situationAugmentation J K) (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J
          V) ⦋m⦌).inv ≫ (situationComponentInverseImageSliceIso J K ⦋m⦌).hom.app
          (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V))))).symm) ?_
    refine Eq.trans (congrArg (fun g => g ≫ (augmentationAbelianLowerShriek J K).map
      ((SimplicialSiteSituation.componentLowerShriekAb (situation J K) ⦋m⦌).map
      ((componentRestrictionAbInverseImageIso' (situation J K) (Cat.of C) J (situationAugmentation J
      K) (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V) ⦋m⦌).inv ≫
      (situationComponentInverseImageSliceIso J K ⦋m⦌).hom.app
      (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)))) hmc.symm) ?_
    refine Eq.trans
      (map_degIso_inv_comp_barSimplicial_map_comp_degIso_hom_slice J K
        (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V) φ) ?_
    exact congrArg (fun g => (augmentationAbelianLowerShriek J K).map
      ((SimplicialSiteSituation.componentLowerShriekAb (situation J K) ⦋n⦌).map
      ((componentRestrictionAbInverseImageIso' (situation J K) (Cat.of C) J (situationAugmentation J
      K) (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V) ⦋n⦌).inv ≫
      (situationComponentInverseImageSliceIso J K ⦋n⦌).hom.app
      (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V))) ≫ g)
      (augmentationComponentFreeYonedaSimplicial_map_eq_augmentationTransition J K V φ).symm
  refine Eq.trans ((((augmentationAbelianLowerShriek J K).mapIso (Augmentation.degIso' (situation J
    K) (Cat.of C) J (situationAugmentation J K)
    (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V) n)).hom_inv_id_assoc
    ((augmentationAbelianLowerShriek J K).map (((barSimplicial' (situation J K)).obj
      ((Augmentation.totalInverseImageAb (situation J K) (Cat.of C) J (situationAugmentation J
      K)).obj (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V))).map φ.op) ≫
      (augmentationAbelianLowerShriek J K).map (Augmentation.degIso' (situation J K) (Cat.of C) J
        (situationAugmentation J K) (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)
        m).hom ≫ (augmentationAbelianLowerShriek J K).map
        ((SimplicialSiteSituation.componentLowerShriekAb (situation J K) ⦋m⦌).map
        ((componentRestrictionAbInverseImageIso' (situation J K) (Cat.of C) J (situationAugmentation
        J K) (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V) ⦋m⦌).inv ≫
        (situationComponentInverseImageSliceIso J K ⦋m⦌).hom.app
        (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V))))).symm) ?_
  refine Eq.trans (congrArg (fun g => (augmentationAbelianLowerShriek J K).map (Augmentation.degIso'
    (situation J K) (Cat.of C) J (situationAugmentation J K)
    (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V) n).hom ≫ g) hchain) ?_
  exact (Category.assoc _ _ _).symm

/-- The degree-`p` comparison: the degreewise identification of the resolution of Stacks 0D78,
followed by the identification of `a_p^{-1}ℤ_V^♯` with the restriction `j_p^{-1}ℤ_V^♯`, both
pushed forward along the extension by zero `a_!`. -/
def resolutionLowerShriekFreeYonedaIsoApp (p : SimplexCategory) :
    (augmentationAbelianLowerShriek J K).obj (((barSimplicial' (situation J K)).obj
      ((Augmentation.totalInverseImageAb (situation J K) (Cat.of C) J (situationAugmentation J
      K)).obj (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V))).obj (op p)) ≅
      (augmentationComponentFreeYonedaSimplicial J K V).obj (op p) :=
  (augmentationAbelianLowerShriek J K).mapIso (Augmentation.degIso' (situation J K) (Cat.of C) J
    (situationAugmentation J K)
      (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V) p.len) ≪≫
    (augmentationAbelianLowerShriek J K).mapIso ((SimplicialSiteSituation.componentLowerShriekAb
      (situation J K) p).mapIso
      ((componentRestrictionAbInverseImageIso' (situation J K) (Cat.of C) J
            (situationAugmentation J K) (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)
              p).symm ≪≫
        (situationComponentInverseImageSliceIso J K p).app
          (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)))

/-- **The `a_!`-image of the resolving simplicial object of Stacks 0D78 of `a^{-1}ℤ_V^♯` is
`p ↦ a_!g_{p!}j_p^{-1}ℤ_V^♯`, as simplicial abelian sheaves.** The degreewise comparison is
`resolutionLowerShriekFreeYonedaIsoApp` and its naturality in the simplex maps is
`map_barSimplicial_map_comp_degIso_slice`.

This is the naturality in the simplex map of
`CategoryTheory.SimplicialSemiRepresentable.augmentationComponentFreeYonedaIso`. -/
def resolutionLowerShriekFreeYonedaIso :
    (barSimplicial' (situation J K)).obj ((Augmentation.totalInverseImageAb (situation J K) (Cat.of
      C) J (situationAugmentation J K)).obj (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J
      V)) ⋙ augmentationAbelianLowerShriek J K ≅
      augmentationComponentFreeYonedaSimplicial J K V :=
  NatIso.ofComponents (fun p => resolutionLowerShriekFreeYonedaIsoApp J K V p.unop)
    (fun {_ _} α => map_barSimplicial_map_comp_degIso_slice J K V α.unop)


/-- **The `a_!`-image of the resolving simplicial object of Stacks 0D78 of `a^{-1}ℤ_V^♯` is the
simplicial abelian sheaf `p ↦ ℤ_{h_V × F(K_p)}^♯`.** The carrier
`augmentationComponentFreeYonedaSimplicial` is a `CategoryTheory.Functor.copyObj` of
`freeYonedaSimplicial`, so its identification with `p ↦ ℤ_{h_V × F(K_p)}^♯` is free; all the
content is in `resolutionLowerShriekFreeYonedaIso`.

The right-hand side is the simplicial presheaf whose free abelian sheaves make up the complex of
Stacks 01GE for the hypercovering multiplied by `h_V`, by
`Stacks.CategoryTheory.Hypercovering.freeAbelianSheafComplexProdConstIsoYoneda_target_X`. -/
def resolutionLowerShriekFreeYonedaSimplicialIso :
    (barSimplicial' (situation J K)).obj ((Augmentation.totalInverseImageAb (situation J K) (Cat.of
      C) J (situationAugmentation J K)).obj (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J
      V)) ⋙ augmentationAbelianLowerShriek J K ≅
      freeYonedaSimplicial J K V :=
  resolutionLowerShriekFreeYonedaIso J K V ≪≫ augmentationComponentFreeYonedaSimplicialIso J K V

/-- In degree `p` the identification is `augmentationComponentFreeYonedaIso` after the degreewise
comparison. -/
theorem resolutionLowerShriekFreeYonedaSimplicialIso_app (p : SimplexCategoryᵒᵖ) :
    (resolutionLowerShriekFreeYonedaSimplicialIso J K V).hom.app p =
      (resolutionLowerShriekFreeYonedaIsoApp J K V p.unop).hom ≫
        (augmentationComponentFreeYonedaIso J K p.unop V).hom :=
  rfl

end CategoryTheory.SimplicialSemiRepresentable

end
