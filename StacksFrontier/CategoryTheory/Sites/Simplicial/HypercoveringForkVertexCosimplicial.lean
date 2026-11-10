module

public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.CocontinuousCompMate
public import StacksFrontier.CategoryTheory.Sites.Glueing.InternalHomFreeAbelian
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.AbelianPushPull
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.PushPullSheafHomNaturality
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianCechDiagramReading
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationCechTransitionInverseImage
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianSections
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringLocalizationTransition

/-!
# The fork vertices of a simplicial semi-representable object, cosimplicially

Let `(C, J)` be a small site and `K` a simplicial object of `SR(C)` whose localized topology
admits pullbacks of coverings, so that the simplicial site `n ↦ C/K_n` of Stacks 0D8B exists with
augmentation `a`. Stacks 0D86, in simplicial degree `k`, identifies the degree-`k` vertex
`a_{k,*}a_k^{-1}` of the fork of Stacks 0D70, part (3), with the internal hom
`SheafHom(F(K_k)^#, -)` out of the sheafified semi-representable presheaf; that is
`CategoryTheory.SimplicialSemiRepresentable.restrictForkVertexSheafHomIso`.

This module makes that identification cosimplicial: the two cosimplicial diagrams of endofunctors
of sheaves of sets — the fork vertices with the direct-image transitions of Stacks 0D70,
compatibility (c), and the internal homs with the maps induced by the face and degeneracy maps of
`K` — are isomorphic. Reading that isomorphism through the abelian conjugation identifies the
terms of the Čech complex of Stacks 0D79 with the abelian internal homs out of the free abelian
sheaves of `F(K)`, which is what Stacks 0D8F needs; so Stacks 0D8F itself is proved here.

## Main definitions

* `CategoryTheory.SimplicialSemiRepresentable.sheafHomCosimplicialFunctor`: the cosimplicial
  diagram `n ↦ SheafHom(F(K_n)^#, -)` of endofunctors of sheaves of sets.
* `CategoryTheory.Sites.AbelianSheaf.mapCommGrpDiagramIso` and `.abelianReadingDiagramIso`: the
  abelian reading of a cosimplicial diagram of endofunctors transports an isomorphism of
  diagrams.
* `CategoryTheory.SimplicialSemiRepresentable.forkVertexSheafHomCosimplicialIso`: **Stacks 0D86,
  cosimplicially.**
* `CategoryTheory.SimplicialSemiRepresentable.cechCosimplicialObjectIsoSheafHomCosimplicialObject`:
  the terms of the Čech complex of Stacks 0D79 are the abelian internal homs, cosimplicially.
* `CategoryTheory.SimplicialSemiRepresentable.cechComplexIsoSheafHomComplex`: **Stacks 0D8F.**

## Main results

* `CategoryTheory.SimplicialSemiRepresentable.pushPullTransition_componentPushPullSheafHomIso`:
  **Stacks 0D86 is compatible with the simplicial structure** — the push-pull transition of a
  simplex map corresponds to the internal hom of the sheafified transition.
* `CategoryTheory.SimplicialSemiRepresentable.restrictForkVertexSheafHomIso_naturality`: the
  fork-vertex identification commutes with the transitions — the Čech transition is the
  push-pull transition of the factorization of Stacks 0D70 (1), the Stacks 0D8B identifications
  carry it to the push-pull transition of the localization functors, and the previous item
  carries that to the map induced by the simplicial structure of `K`.

## Implementation notes

The diagram of internal homs is a composite of three functors, `K` followed by the
semi-representable presheaf, sheafification and the internal-hom bifunctor of Stacks 0BWQ, so it
needs no functoriality proof of its own.

Stacks 0D8F is proved in this module rather than in
`StacksFrontier/CategoryTheory/Sites/Simplicial/HypercoveringCechComplex.lean`, where the Čech
complex and the sheaf-Hom complex are defined: the identification of their terms is cosimplicial,
and that is only available here, while the Čech cosimplicial abelian sheaf is defined below. The
half of Stacks 0D8F that concerns the differentials is still
`CategoryTheory.SimplicialSemiRepresentable.sheafHomComplexIsoCofaceComplex` there.

`mapCommGrpDiagramIso` is built from `CategoryTheory.Functor.mapCommGrpNatTrans` rather than from
Mathlib's `Functor.mapCommGrpNatIso`, so that its `hom` and `inv` are transformations of the shape
the transitions of `CategoryTheory.Sites.AbelianSheaf.mapCommGrpDiagram` already have; the two
unit and composition laws for those transformations hold by `rfl`, which is what makes the
naturality square and the two inverse laws immediate.

## References

* [Stacks Project, Tag 0D8F](https://stacks.math.columbia.edu/tag/0D8F)
* [Stacks Project, Tag 0D86](https://stacks.math.columbia.edu/tag/0D86)
* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
* [Stacks Project, Tag 0D79](https://stacks.math.columbia.edu/tag/0D79)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 00XO](https://stacks.math.columbia.edu/tag/00XO)
* [Stacks Project, Tag 0BWQ](https://stacks.math.columbia.edu/tag/0BWQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ u₁ v₂ u₂ v₃ u₃ u

attribute [local instance] CategoryTheory.sheafTypeCartesian CategoryTheory.sheafTypeBraided

attribute [local instance] Functor.Braided.ofChosenFiniteProducts


namespace CategoryTheory.Sites.AbelianSheaf

variable {A₁ : Type u₁} [Category.{v₁} A₁] [CartesianMonoidalCategory A₁] [BraidedCategory A₁]
  {A₂ : Type u₂} [Category.{v₂} A₂] [CartesianMonoidalCategory A₂] [BraidedCategory A₂]
  {T : Type u₃} [Category.{v₃} T]

/-- **An isomorphism of diagrams of finite-product-preserving functors induces one of the
diagrams they define on commutative group objects.** -/
def mapCommGrpDiagramIso {P P' : T ⥤ (A₁ ⥤ A₂)} [∀ t, (P.obj t).Braided]
    [∀ t, (P'.obj t).Braided] (e : P ≅ P') :
    mapCommGrpDiagram P ≅ mapCommGrpDiagram P' where
  hom :=
    { app := fun t => Functor.mapCommGrpNatTrans (e.hom.app t)
      naturality := fun t t' f => by
        change Functor.mapCommGrpNatTrans (P.map f) ≫ Functor.mapCommGrpNatTrans (e.hom.app t') =
          Functor.mapCommGrpNatTrans (e.hom.app t) ≫ Functor.mapCommGrpNatTrans (P'.map f)
        rw [← mapCommGrpNatTrans_comp, ← mapCommGrpNatTrans_comp, e.hom.naturality f] }
  inv :=
    { app := fun t => Functor.mapCommGrpNatTrans (e.inv.app t)
      naturality := fun t t' f => by
        change Functor.mapCommGrpNatTrans (P'.map f) ≫ Functor.mapCommGrpNatTrans (e.inv.app t') =
          Functor.mapCommGrpNatTrans (e.inv.app t) ≫ Functor.mapCommGrpNatTrans (P.map f)
        rw [← mapCommGrpNatTrans_comp, ← mapCommGrpNatTrans_comp, e.inv.naturality f] }
  hom_inv_id := by
    apply NatTrans.ext
    funext t
    change Functor.mapCommGrpNatTrans (e.hom.app t) ≫ Functor.mapCommGrpNatTrans (e.inv.app t) =
      𝟙 _
    rw [← mapCommGrpNatTrans_comp, Iso.hom_inv_id_app, mapCommGrpNatTrans_id]
  inv_hom_id := by
    apply NatTrans.ext
    funext t
    change Functor.mapCommGrpNatTrans (e.inv.app t) ≫ Functor.mapCommGrpNatTrans (e.hom.app t) =
      𝟙 _
    rw [← mapCommGrpNatTrans_comp, Iso.inv_hom_id_app, mapCommGrpNatTrans_id]

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- **An isomorphism of diagrams of finite-product-preserving endofunctors of sheaves of sets
induces one of their abelian readings.** -/
def abelianReadingDiagramIso {P P' : T ⥤ (Sheaf J (Type u) ⥤ Sheaf J (Type u))}
    [∀ t, (P.obj t).Braided] [∀ t, (P'.obj t).Braided] (e : P ≅ P') :
    abelianReadingDiagram J P ≅ abelianReadingDiagram J P' :=
  Functor.isoWhiskerRight (mapCommGrpDiagramIso e) (abelianConjugationFunctor J J)

end CategoryTheory.Sites.AbelianSheaf

namespace CategoryTheory.SimplicialSemiRepresentable

open SemiRepresentable

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (K : SimplicialObject (FormalCoproduct.{u} C)) [J.toCoverage.HasPullbacks]

/-- **The cosimplicial diagram `n ↦ SheafHom(F(K_n)^#, -)`** of endofunctors of sheaves of sets on
`(C, J)`: the simplicial presheaf represented by `K`, sheafified, read through the internal-hom
bifunctor of Stacks 0BWQ, which is contravariant in its source. -/
def sheafHomCosimplicialFunctor :
    CosimplicialObject (Sheaf J (Type u) ⥤ Sheaf J (Type u)) :=
  (semiRepresentablePresheaf K ⋙ presheafToSheaf J (Type u)).rightOp ⋙
    SheafHomAdj.sheafHomBifunctor

omit [J.toCoverage.HasPullbacks] in
/-- In degree `n` the diagram of internal homs is `SheafHom(F(K_n)^#, -)`. -/
theorem sheafHomCosimplicialFunctor_obj (n : SimplexCategory) :
    (sheafHomCosimplicialFunctor J K).obj n =
      SheafHomAdj.sheafHomFunctor (formalCoproductSheafifiedYoneda J (K.obj (op n))) := rfl

omit [J.toCoverage.HasPullbacks] in
/-- The transitions of the diagram of internal homs are the maps induced by the simplicial
structure of `K`, sheafified. -/
theorem sheafHomCosimplicialFunctor_map {m n : SimplexCategory} (φ : m ⟶ n) :
    (sheafHomCosimplicialFunctor J K).map φ =
      SheafHomAdj.sheafHomContraMap (totSheafify J (K.map φ.op)) := rfl

/-- Every term of the diagram of internal homs is braided, preserving finite products by
Stacks 0BWQ. -/
instance preservesFiniteProducts_sheafHomCosimplicialFunctor_obj (n : SimplexCategory) :
    PreservesFiniteProducts ((sheafHomCosimplicialFunctor J K).obj n) :=
  inferInstanceAs (PreservesFiniteProducts (SheafHomAdj.sheafHomFunctor
    (formalCoproductSheafifiedYoneda J (K.obj (op n)))))

/-- Every term of the diagram of internal homs is braided, preserving finite products by
Stacks 0BWQ. -/
instance braided_sheafHomCosimplicialFunctor_obj (n : SimplexCategory) :
    ((sheafHomCosimplicialFunctor J K).obj n).Braided :=
  Functor.Braided.ofChosenFiniteProducts _

/-- The transition functor of a simplex map is continuous for the component topologies of the
simplicial site of `K`: the instance `componentOverMap_isContinuous'` of `CartesianSections.lean`,
under its former name here. -/
instance componentOverMap_isContinuous {m n : SimplexCategory} (φ : m ⟶ n) :
    (componentOverMap (K.map φ.op)).IsContinuous ((situation J K).componentTopology n)
      ((situation J K).componentTopology m) :=
  componentOverMap_isContinuous' J K φ


/-- The Stacks 0D8B identification of the inverse images is the one the Stacks 0D8B
identification of the direct images induces by uniqueness of a left adjoint. -/
theorem componentInverseImageIso_eq (k : SimplexCategory) :
    componentInverseImageIso J K k =
      MorphismOfTopoi.inverseImageIsoOfPushforwardIso
        (SimplicialSiteSituation.Augmentation.componentAugmentation (situation J K) (Cat.of C) J
          (situationAugmentation J K) k) (localizationMorphism J K k)
        (componentPushforwardIso J K k) := rfl

/-- **The push-pull transition of the Čech diagram is the push-pull transition of the
localization functors.** The Stacks 0D8B identifications carry the push-pull transition of the
factorization of the component augmentations to the push-pull transition of the factorization
`r_φ ⋙ j_m = j_n` of the localization functors; the compatibility of the two factorization
isomorphisms is `componentPushforwardIso_transitionPushforwardIso`. -/
theorem pushPullTransition_localizationMorphism {m n : SimplexCategory} (φ : m ⟶ n) :
    MorphismOfTopoi.pushPullTransition
          (SimplicialSiteSituation.Augmentation.componentAugmentation (situation J K) (Cat.of C) J
            (situationAugmentation J K) m)
          (SimplicialSiteSituation.Augmentation.componentAugmentation (situation J K) (Cat.of C) J
            (situationAugmentation J K) n)
          ((situation J K).transitionMorphism φ)
          (SimplicialSiteSituation.Augmentation.transitionPushforwardIso (situation J K)
            (Cat.of C) J (situationAugmentation J K) φ) ≫
        (Functor.isoWhiskerRight (componentInverseImageIso J K n)
            (SimplicialSiteSituation.Augmentation.componentAugmentation (situation J K)
              (Cat.of C) J (situationAugmentation J K) n).pushforward ≪≫
          Functor.isoWhiskerLeft (localizationMorphism J K n).inverseImage
            (componentPushforwardIso J K n)).hom =
      (Functor.isoWhiskerRight (componentInverseImageIso J K m)
            (SimplicialSiteSituation.Augmentation.componentAugmentation (situation J K)
              (Cat.of C) J (situationAugmentation J K) m).pushforward ≪≫
          Functor.isoWhiskerLeft (localizationMorphism J K m).inverseImage
            (componentPushforwardIso J K m)).hom ≫
        MorphismOfTopoi.pushPullTransition (localizationMorphism J K m)
          (localizationMorphism J K n) ((situation J K).transitionMorphism φ)
          (localizationPushforwardCompIso J K φ) := by
  rw [componentInverseImageIso_eq, componentInverseImageIso_eq]
  exact MorphismOfTopoi.pushPullTransition_congr _ _ _ _ _ _ _ _ _
    (componentPushforwardIso_transitionPushforwardIso J K φ)

/-- **The abelian reading of the cosimplicial diagram of internal homs is
`ℋom(s(ℤ_{F(K)}^#), F)` termwise.** Evaluating the abelian reading of
`n ↦ SheafHom(F(K_n)^#, -)` at `F` gives the cosimplicial abelian sheaf
`n ↦ ℋom(ℤ_{F(K_n)}^#, F)` whose alternating-coface complex is `SheafHom(s(ℤ_{F(K)}^#), F)`;
degreewise this is the comparison `internalHomFreeAbelianIso`, and it is cosimplicial because
that comparison is natural in the presheaf of sets. -/
def abelianReadingSheafHomCosimplicialIso (F : Sheaf J AddCommGrpCat.{u}) :
    Sites.AbelianSheaf.abelianReadingDiagram J (sheafHomCosimplicialFunctor J K) ⋙
        (evaluation _ _).obj F ≅
      sheafHomCosimplicialObject J K F :=
  Functor.isoWhiskerLeft (semiRepresentablePresheaf K).rightOp
    (internalHomFreeAbelianIso J F).symm

/-! ### The cosimplicial comparison and the terms of the Čech complex -/

/-- **Stacks 0D86 is compatible with the simplicial structure.** For a simplex map `φ : m ⟶ n`
the push-pull transition of the factorization `r_φ ⋙ j_m = j_n` of the localization functors is
carried by the two instances of Stacks 0D86 to the internal hom of the sheafified transition
`F(K_n)^# ⟶ F(K_m)^#`.

It is `CategoryTheory.SemiRepresentable.pushPullSheafHomIso_naturality` for the morphism
`K_n ⟶ K_m` of semi-representable objects, once the push-pull transition of the morphisms of
topoi is identified with
`CategoryTheory.SemiRepresentable.pushPullRestrictionTransition`. That identification has two
steps. The relocalization adjunction of a morphism of topoi is the one of Stacks 00XO, whose
inverse image is the sheafified restriction, whereas `pushPullRestrictionTransition` uses plain
restriction; the two are different left adjoints of the same direct image, so
`Stacks.CategoryTheory.restrictionTransition_congr_middle` and
`Stacks.CategoryTheory.leftAdjointCompIso_congr_middle` move between them. What is left is that
the comparison of restrictions which `localizationPushforwardCompIso` induces is the one
`CategoryTheory.Functor.sheafPushforwardContinuousComp'` builds from `r_φ ⋙ j_m = j_n`, which is
`CategoryTheory.leftAdjointCompIso_sheafPushforwardCocontinuousCompIso`. -/
theorem pushPullTransition_componentPushPullSheafHomIso {m n : SimplexCategory} (φ : m ⟶ n) :
    MorphismOfTopoi.pushPullTransition (localizationMorphism J K m)
          (localizationMorphism J K n) ((situation J K).transitionMorphism φ)
          (localizationPushforwardCompIso J K φ) ≫
        (componentPushPullSheafHomIso J K n).hom =
      (componentPushPullSheafHomIso J K m).hom ≫
        SheafHomAdj.sheafHomContraMap (totSheafify J (K.map φ.op)) := by
  let icm : (componentOverForget (K.obj (op m))).IsContinuous
      ((situation J K).componentTopology m) J := sliceForget_isContinuous J K m
  let iccm : (componentOverForget (K.obj (op m))).IsCocontinuous
      ((situation J K).componentTopology m) J := sliceForget_isCocontinuous J K m
  let icn : (componentOverForget (K.obj (op n))).IsContinuous
      ((situation J K).componentTopology n) J := sliceForget_isContinuous J K n
  let iccn : (componentOverForget (K.obj (op n))).IsCocontinuous
      ((situation J K).componentTopology n) J := sliceForget_isCocontinuous J K n
  let imcc : (componentOverMap (K.map φ.op)).IsCocontinuous
      ((situation J K).componentTopology n) ((situation J K).componentTopology m) :=
    componentOverMap_isCocontinuous J K φ
  let iuv : (componentOverMap (K.map φ.op) ⋙ componentOverForget (K.obj (op m))).IsCocontinuous
      ((situation J K).componentTopology n) J :=
    @CategoryTheory.isCocontinuous_comp _ _ _ _ _ _ _ _
      ((situation J K).componentTopology n) ((situation J K).componentTopology m) J imcc iccm
  have hiso : Adjunction.leftAdjointCompIso
        ((componentOverForget (K.obj (op m))).sheafAdjunctionCocontinuous (Type u)
          ((situation J K).componentTopology m) J)
        ((componentOverMap (K.map φ.op)).sheafAdjunctionCocontinuous (Type u)
          ((situation J K).componentTopology n) ((situation J K).componentTopology m))
        ((componentOverForget (K.obj (op n))).sheafAdjunctionCocontinuous (Type u)
          ((situation J K).componentTopology n) J)
        (localizationPushforwardCompIso J K φ) =
      relocalizationForgetPushforwardIso J (K.map φ.op)
        ((situation J K).componentTopology n) (componentTopology_eq J K n)
        ((situation J K).componentTopology m) (componentTopology_eq J K m) :=
    (@leftAdjointCompIso_sheafPushforwardCocontinuousCompIso
        (ComponentOver (K.obj (op n))) _ (ComponentOver (K.obj (op m))) _ C _
        ((situation J K).componentTopology n) ((situation J K).componentTopology m) J
        (componentOverMap (K.map φ.op)) (componentOverForget (K.obj (op m)))
        (componentOverForget (K.obj (op n)))
        (componentOverMap_isContinuous J K φ) imcc icm iccm icn iccn
        (componentOverMap_comp_componentOverForget (K.map φ.op))).trans
      (relocalizationForgetPushforwardIso_eq J (K.map φ.op)
        ((situation J K).componentTopology n) (componentTopology_eq J K n)
        ((situation J K).componentTopology m) (componentTopology_eq J K m)).symm
  have htrans : MorphismOfTopoi.pushPullTransition (localizationMorphism J K m)
        (localizationMorphism J K n) ((situation J K).transitionMorphism φ)
        (localizationPushforwardCompIso J K φ) =
      pushPullRestrictionTransition J (K.map φ.op)
        ((situation J K).componentTopology n) (componentTopology_eq J K n)
        ((situation J K).componentTopology m) (componentTopology_eq J K m) := by
    refine Stacks.CategoryTheory.restrictionTransition_congr_middle
      ((localizationMorphism J K m).adj) ((localizationMorphism J K n).adj)
      (((situation J K).transitionMorphism φ).adj)
      ((componentOverMap (K.map φ.op)).sheafAdjunctionCocontinuous (Type u)
        ((situation J K).componentTopology n) ((situation J K).componentTopology m))
      _ _
      (Adjunction.leftAdjointUniq (((situation J K).transitionMorphism φ).adj)
        ((componentOverMap (K.map φ.op)).sheafAdjunctionCocontinuous (Type u)
          ((situation J K).componentTopology n) ((situation J K).componentTopology m))) ?_
    exact (Stacks.CategoryTheory.leftAdjointCompIso_congr_middle
        ((localizationMorphism J K m).adj) (((situation J K).transitionMorphism φ).adj)
        ((componentOverMap (K.map φ.op)).sheafAdjunctionCocontinuous (Type u)
          ((situation J K).componentTopology n) ((situation J K).componentTopology m))
        ((localizationMorphism J K n).adj) (localizationPushforwardCompIso J K φ)).trans
      (congrArg
        (fun z : (componentOverForget (K.obj (op m))).sheafPushforwardContinuous (Type u)
              ((situation J K).componentTopology m) J ⋙
            (componentOverMap (K.map φ.op)).sheafPushforwardContinuous (Type u)
              ((situation J K).componentTopology n) ((situation J K).componentTopology m) ≅
            (componentOverForget (K.obj (op n))).sheafPushforwardContinuous (Type u)
              ((situation J K).componentTopology n) J =>
          Functor.isoWhiskerLeft (localizationMorphism J K m).inverseImage
              (Adjunction.leftAdjointUniq (((situation J K).transitionMorphism φ).adj)
                ((componentOverMap (K.map φ.op)).sheafAdjunctionCocontinuous (Type u)
                  ((situation J K).componentTopology n)
                  ((situation J K).componentTopology m))) ≪≫ z)
        hiso)
  rw [htrans]
  exact pushPullSheafHomIso_naturality J (K.map φ.op)
    ((situation J K).componentTopology n) (componentTopology_eq J K n)
    ((situation J K).componentTopology m) (componentTopology_eq J K m)

/-- The cosimplicial naturality of the fork-vertex identification, in the spelling in which its
three inputs are stated: the Čech transition is the push-pull transition of the factorization of
Stacks 0D70 (1), the Stacks 0D8B identifications carry it to the push-pull transition of the
localization functors, and `pushPullTransition_componentPushPullSheafHomIso` carries that to the
map induced by the simplicial structure of `K`. -/
private theorem restrictForkVertexSheafHomIso_naturality_aux
    {m n : SimplexCategory} (φ : m ⟶ n) :
    Functor.whiskerLeft (SimplicialSiteSituation.Augmentation.inverseImage (situation J K)
          (Cat.of C) J (situationAugmentation J K))
        (SimplicialSiteSituation.Augmentation.componentPushforwardTransition (situation J K)
          (Cat.of C) J (situationAugmentation J K) φ) ≫
      (Functor.isoWhiskerRight (SimplicialSiteSituation.Augmentation.restrictCompInverseImageIso
            (situation J K) (Cat.of C) J (situationAugmentation J K) n)
          (SimplicialSiteSituation.Augmentation.componentAugmentation (situation J K) (Cat.of C) J
            (situationAugmentation J K) n).pushforward).hom ≫
        (Functor.isoWhiskerRight (componentInverseImageIso J K n)
            (SimplicialSiteSituation.Augmentation.componentAugmentation (situation J K) (Cat.of C) J
              (situationAugmentation J K) n).pushforward ≪≫
          Functor.isoWhiskerLeft (localizationMorphism J K n).inverseImage
            (componentPushforwardIso J K n)).hom ≫
          (componentPushPullSheafHomIso J K n).hom =
      (Functor.isoWhiskerRight (SimplicialSiteSituation.Augmentation.restrictCompInverseImageIso
            (situation J K) (Cat.of C) J (situationAugmentation J K) m)
          (SimplicialSiteSituation.Augmentation.componentAugmentation (situation J K) (Cat.of C) J
            (situationAugmentation J K) m).pushforward).hom ≫
        (Functor.isoWhiskerRight (componentInverseImageIso J K m)
            (SimplicialSiteSituation.Augmentation.componentAugmentation (situation J K) (Cat.of C) J
              (situationAugmentation J K) m).pushforward ≪≫
          Functor.isoWhiskerLeft (localizationMorphism J K m).inverseImage
            (componentPushforwardIso J K m)).hom ≫
          (componentPushPullSheafHomIso J K m).hom ≫
            SheafHomAdj.sheafHomContraMap (totSheafify J (K.map φ.op)) := by
  have h1 :=
    SimplicialSiteSituation.Augmentation.restrictCompInverseImageIso_componentPushforwardTransition
      (situation J K) (Cat.of C) J (situationAugmentation J K) φ
  have h2 := (SimplicialSiteSituation.Augmentation.pushPullTransition_componentAugmentation
    (situation J K) (Cat.of C) J (situationAugmentation J K) φ).symm
  have h3 := pushPullTransition_localizationMorphism J K φ
  have h4 := pushPullTransition_componentPushPullSheafHomIso J K φ
  rw [h2] at h1
  rw [← Category.assoc, h1, Category.assoc]
  congr 1
  simp only [← Category.assoc] at h3 ⊢
  rw [h3]
  simp only [Category.assoc]
  rw [h4]

/-- **Stacks 0D86, cosimplicially, at the level of components.** The fork-vertex identification
`restrictForkVertexSheafHomIso` commutes with the transitions: the Čech transition of a simplex
map corresponds to the internal hom of the sheafified transition `F(K_n)^# ⟶ F(K_m)^#`. -/
theorem restrictForkVertexSheafHomIso_naturality {m n : SimplexCategory} (φ : m ⟶ n) :
    (forkVertexCosimplicialFunctor J K).map φ ≫ (restrictForkVertexSheafHomIso J K n).hom =
      (restrictForkVertexSheafHomIso J K m).hom ≫ (sheafHomCosimplicialFunctor J K).map φ :=
  restrictForkVertexSheafHomIso_naturality_aux J K φ

/-- **Stacks 0D86, cosimplicially.** The fork-vertex cosimplicial diagram of endofunctors of
sheaves of sets is the cosimplicial diagram of internal homs out of the sheafified
semi-representable presheaves of `K`.

Degreewise this is `restrictForkVertexSheafHomIso`, Stacks 0D8B followed by Stacks 0D86, and the
cosimplicial naturality is `restrictForkVertexSheafHomIso_naturality`. -/
def forkVertexSheafHomCosimplicialIso :
    forkVertexCosimplicialFunctor J K ≅ sheafHomCosimplicialFunctor J K :=
  NatIso.ofComponents (restrictForkVertexSheafHomIso J K)
    (fun {_ _} φ => restrictForkVertexSheafHomIso_naturality J K φ)

/-- **The terms of the Čech complex of Stacks 0D79 are the abelian internal homs, cosimplicially.**
For an abelian sheaf `F` the cosimplicial abelian sheaf `n ↦ a_{n,*}a_n⁻¹F` underlying the Čech
complex is `n ↦ ℋom(ℤ_{F(K_n)}^#, F)`.

The three factors are: the Čech cosimplicial abelian sheaf is the abelian reading of the
fork-vertex diagram (`cechCosimplicialObjectIso`), the abelian reading of
`forkVertexSheafHomCosimplicialIso` identifies that with the abelian reading of the diagram of
internal homs out of sheaves of sets, and the abelian reading of the latter is
`n ↦ ℋom(ℤ_{F(K_n)}^#, F)` (`abelianReadingSheafHomCosimplicialIso`). -/
def cechCosimplicialObjectIsoSheafHomCosimplicialObject (F : Sheaf J AddCommGrpCat.{u}) :
    cechCosimplicialObject J K F ≅ sheafHomCosimplicialObject J K F :=
  cechCosimplicialObjectIso J K F ≪≫
    Functor.isoWhiskerRight
        (Sites.AbelianSheaf.abelianReadingDiagramIso J (forkVertexSheafHomCosimplicialIso J K))
        ((evaluation _ _).obj F) ≪≫
      abelianReadingSheafHomCosimplicialIso J K F

/-- **Stacks 0D8F.** The Čech complex of Stacks 0D79 associated to `a⁻¹F`,

`a_{0,*}a_0⁻¹F ⟶ a_{1,*}a_1⁻¹F ⟶ a_{2,*}a_2⁻¹F ⟶ …`

is canonically isomorphic — the source says equal, and the comparison is indeed the identity in
every degree once the terms are identified — to the cochain complex
`SheafHom(s(ℤ_{F(K)}^#), F)` obtained by applying the abelian internal hom `ℋom(-, F)` to the
complex of free abelian sheaves of Stacks 01GB.

The differentials of both complexes are the alternating sums induced by the simplicial structure
of `K`, so a cosimplicial identification of the terms suffices; that is the whole of the source's
argument. The identification of the terms itself,
`a_{n,*}a_n⁻¹F = ℋom'(F(K_n)^#, F) = ℋom(ℤ_{F(K_n)}^#, F)`, is
`cechCosimplicialObjectIsoSheafHomCosimplicialObject`. -/
@[stacks 0D8F]
def cechComplexIsoSheafHomComplex (F : Sheaf J AddCommGrpCat.{u}) :
    cechComplex J K F ≅ sheafHomComplex J K F :=
  (AlgebraicTopology.alternatingCofaceMapComplex (Sheaf J AddCommGrpCat.{u})).mapIso
      (cechCosimplicialObjectIsoSheafHomCosimplicialObject J K F) ≪≫
    sheafHomComplexIsoCofaceComplex J K F

end CategoryTheory.SimplicialSemiRepresentable

end
