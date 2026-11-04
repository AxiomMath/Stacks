module

public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import StacksFrontier.CategoryTheory.Sites.Modules.InverseImage.AbelianSheaf
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringCechComplex

/-!
# The Čech cosimplicial abelian sheaf is the abelian reading of the fork-vertex diagram

Let `(C, J)` be a small site whose topology has pullbacks of coverings and let `K` be a
simplicial object of `SR(C)`. The simplicial site `n ↦ C/K_n` of Stacks 0D8B carries the
augmentation given by the degree-zero localization functor, with component augmentations `a_n`
and total augmentation `a`; for an abelian sheaf `F` on `(C, J)` the Čech cosimplicial abelian
sheaf of Stacks 0D79 at `a⁻¹F` is `n ↦ a_{n,*}(a⁻¹F)_n`, which is
`CategoryTheory.SimplicialSemiRepresentable.cechCosimplicialObject`.

On sheaves of *sets* the same recipe is a cosimplicial diagram of endofunctors of `Sh(C, J)`,
namely `n ↦ a⁻¹ ⋙ (-)_n ⋙ a_{n,*}`: these are the vertices of the fork of Stacks 0D70, part (3),
read as functors of the sheaf on the augmentation site. Each of them preserves finite products,
being the composite of the left exact inverse image of a morphism of topoi with two right
adjoints, so each of them acts on commutative group objects; the passage of Stacks 04DB therefore
turns the whole diagram into a cosimplicial diagram of endofunctors of abelian sheaves. This file
builds that passage for an arbitrary diagram of finite-product-preserving endofunctors and shows
that the Čech cosimplicial abelian sheaf of Stacks 0D79 is the value at `F` of the abelian
reading of the fork-vertex diagram.

## Main definitions

* `CategoryTheory.mapCommGrpDiagram`: a diagram of finite-product-preserving functors, taken to
  commutative group objects degreewise.
* `CategoryTheory.Sites.AbelianSheaf.abelianConjugationFunctor`: the passage of Stacks 04DB as a
  functor, from functors of commutative group objects to functors of abelian sheaves.
* `CategoryTheory.Sites.AbelianSheaf.abelianReadingDiagram`: **the abelian reading of a diagram
  of endofunctors of sheaves of sets.**
* `CategoryTheory.SimplicialSemiRepresentable.forkVertexCosimplicialFunctor`: **the fork-vertex
  cosimplicial diagram of endofunctors of sheaves of sets** `n ↦ a⁻¹ ⋙ (-)_n ⋙ a_{n,*}`.
* `CategoryTheory.SimplicialSemiRepresentable.grpCosimplicialPushforward`: the cosimplicial
  diagram of the degreewise direct images, on commutative group objects.
* `CategoryTheory.SimplicialSemiRepresentable.cechReadingDiagram`: the Čech cosimplicial abelian
  sheaf of Stacks 0D79, before evaluation, as a diagram of endofunctors of abelian sheaves.

## Main results

* `CategoryTheory.whiskerLeft_mapCommGrpNatTrans_comp_mapCommGrpCompIso_inv`: splitting a
  composite into commutative group objects is natural in the second factor.
* `CategoryTheory.SimplicialSemiRepresentable.cechReadingDiagramIso`: the Čech diagram of
  endofunctors of abelian sheaves is the abelian reading of the fork-vertex diagram.
* `CategoryTheory.SimplicialSemiRepresentable.cechCosimplicialObjectIso`: **the Čech cosimplicial
  abelian sheaf of Stacks 0D79 at `a⁻¹F` is the abelian reading of the fork-vertex diagram,
  evaluated at `F`.**

## Implementation notes

There are two constructions of the morphism of topoi of a total augmentation in this repository,
and they are not identified here: the one built from the cocontinuous functor out of the total
category, and the uniform one of Stacks 0D70, part (2), whose inverse image descends the inverse
images along the component augmentations. The abelian inverse image `totalInverseImageAb`, hence
`cechCosimplicialObject`, is built from the *uniform* one, so that is the inverse image used
throughout this file; the two are compared by
`CategoryTheory.CocontinuousSimplicialSite.Augmentation.totalInverseImageIso`.

The comparison is assembled so that cosimplicial naturality has to be checked only once. Both
sides factor through `grpCosimplicialPushforward`, the diagram of degreewise direct images on
commutative group objects: the Čech side is that diagram conjugated by the equivalence of
Stacks 04DB and then precomposed with the abelian inverse image, and the fork-vertex side is the
same diagram with the inverse image on commutative group objects moved inside. Cancelling the
equivalence in the middle is `Sites.AbelianSheaf.externalInternalIso`, which enters only through
`Functor.mapIso` of the whiskering functors, so its cosimplicial naturality is the functoriality
of whiskering; moving the inverse image inside is `Functor.mapCommGrpCompIso`, whose cosimplicial
naturality is the one square proved by hand,
`CategoryTheory.whiskerLeft_mapCommGrpNatTrans_comp_mapCommGrpCompIso_inv`. That square holds on
the nose, because both legs of `Functor.mapCommGrpCompIso` are the identity on underlying
objects.

Two shapes are load-bearing for the definitional equalities that glue the three steps together.
`grpCosimplicialPushforward` is written out as a functor rather than as `mapCommGrpDiagram` of
`cosimplicialPushforward`, because the instance `∀ n, ((cosimplicialPushforward …).obj n).Braided`
that the latter needs is not found while the diagram is still being unified. And the abelian
inverse image is kept *folded* in the intermediate diagrams: unfolding it there and cancelling
`externalSheaf ⋙ internalSheaf` inside the unfolded form makes the glue equality exceed the
`whnf` heartbeat budget, whereas with it folded every step is cheap.

The braided structures must be the same terms as the ones the Čech diagram was elaborated with,
which is why `Functor.Braided.ofChosenFiniteProducts` is activated as a local instance exactly as
where `CategoryTheory.SimplicialSiteSituation.Augmentation.abelianCosimplicialPushforward` is
defined.

## References

* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 0D79](https://stacks.math.columbia.edu/tag/0D79)
* [Stacks Project, Tag 04DB](https://stacks.math.columbia.edu/tag/04DB)
* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄ u

namespace CategoryTheory

attribute [local instance] CategoryTheory.sheafTypeCartesian CategoryTheory.sheafTypeBraided

attribute [local instance] Functor.Braided.ofChosenFiniteProducts

section CommGrpDiagram

variable {A₁ : Type u₁} [Category.{v₁} A₁] [CartesianMonoidalCategory A₁] [BraidedCategory A₁]
  {A₂ : Type u₂} [Category.{v₂} A₂] [CartesianMonoidalCategory A₂] [BraidedCategory A₂]
  {A₃ : Type u₃} [Category.{v₃} A₃] [CartesianMonoidalCategory A₃] [BraidedCategory A₃]
  {T : Type u₄} [Category.{v₄} T]

/-- **A diagram of finite-product-preserving functors, taken to commutative group objects.** In
degree `t` it is `Functor.mapCommGrp` of the functor in degree `t`, and its transitions are the
transitions of the diagram applied to commutative group objects. -/
def mapCommGrpDiagram (P : T ⥤ (A₁ ⥤ A₂)) [∀ t, (P.obj t).Braided] :
    T ⥤ (CommGrp A₁ ⥤ CommGrp A₂) where
  obj t := (P.obj t).mapCommGrp
  map f := Functor.mapCommGrpNatTrans (P.map f)
  map_id t := by rw [P.map_id]; exact mapCommGrpNatTrans_id _
  map_comp f g := by rw [P.map_comp]; exact mapCommGrpNatTrans_comp _ _

/-- In degree `t` the diagram of commutative group objects is `Functor.mapCommGrp` of the functor
in degree `t`. -/
theorem mapCommGrpDiagram_obj (P : T ⥤ (A₁ ⥤ A₂)) [∀ t, (P.obj t).Braided] (t : T) :
    (mapCommGrpDiagram P).obj t = (P.obj t).mapCommGrp := rfl

/-- The transitions of the diagram of commutative group objects are the transitions of the
original diagram, applied to commutative group objects. -/
theorem mapCommGrpDiagram_map (P : T ⥤ (A₁ ⥤ A₂)) [∀ t, (P.obj t).Braided] {t t' : T}
    (f : t ⟶ t') :
    (mapCommGrpDiagram P).map f = Functor.mapCommGrpNatTrans (P.map f) := rfl

/-- **Splitting a composite into commutative group objects is natural in the second factor.** -/
theorem whiskerLeft_mapCommGrpNatTrans_comp_mapCommGrpCompIso_inv (R : A₁ ⥤ A₂) [R.Braided]
    {G G' : A₂ ⥤ A₃} [G.Braided] [G'.Braided] (α : G ⟶ G') :
    Functor.whiskerLeft R.mapCommGrp (Functor.mapCommGrpNatTrans α) ≫
        (Functor.mapCommGrpCompIso (F := R) (G := G')).inv =
      (Functor.mapCommGrpCompIso (F := R) (G := G)).inv ≫
        Functor.mapCommGrpNatTrans (Functor.whiskerLeft R α) := by
  apply NatTrans.ext
  funext X
  apply CommGrp.hom_ext
  exact (Category.comp_id _).trans (Category.id_comp _).symm

end CommGrpDiagram

section AbelianReading

namespace Sites.AbelianSheaf

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)

/-- **The passage of Stacks 04DB, as a functor.** A functor from the commutative group objects of
sheaves of sets on one site to those on another is read as a functor of abelian sheaves by
internalizing the group operations, applying the functor, and reading the resulting operations
off on sections again. This is the single construction of which
`CategoryTheory.SimplicialSiteSituation.Augmentation.abelianConjugation` is the case of a total
site over its augmentation site. -/
def abelianConjugationFunctor :
    (CommGrp (Sheaf J (Type u)) ⥤ CommGrp (Sheaf K (Type u))) ⥤
      (Sheaf J AddCommGrpCat.{u} ⥤ Sheaf K AddCommGrpCat.{u}) :=
  (Functor.whiskeringLeft _ _ _).obj (internalSheaf J) ⋙
    (Functor.whiskeringRight _ _ _).obj (externalSheaf K)

/-- The abelian reading of a functor of commutative group objects is that functor conjugated by
the equivalence of Stacks 04DB between abelian sheaves and commutative group objects. -/
theorem abelianConjugationFunctor_obj
    (Q : CommGrp (Sheaf J (Type u)) ⥤ CommGrp (Sheaf K (Type u))) :
    (abelianConjugationFunctor J K).obj Q = internalSheaf J ⋙ Q ⋙ externalSheaf K := rfl

variable {T : Type u₄} [Category.{v₄} T]

/-- **The abelian reading of a diagram of endofunctors of sheaves of sets.** Each endofunctor in
the diagram preserves finite products, hence acts on commutative group objects; taking
commutative group objects degreewise and conjugating by the equivalence of Stacks 04DB turns the
diagram into a diagram of endofunctors of abelian sheaves, whose transitions are the abelian
readings of the original transitions. -/
def abelianReadingDiagram (P : T ⥤ (Sheaf J (Type u) ⥤ Sheaf J (Type u)))
    [∀ t, (P.obj t).Braided] :
    T ⥤ (Sheaf J AddCommGrpCat.{u} ⥤ Sheaf J AddCommGrpCat.{u}) :=
  mapCommGrpDiagram P ⋙ abelianConjugationFunctor J J

/-- In degree `t` the abelian reading of a diagram of endofunctors of sheaves of sets is the
abelian reading of the endofunctor in degree `t`. -/
theorem abelianReadingDiagram_obj (P : T ⥤ (Sheaf J (Type u) ⥤ Sheaf J (Type u)))
    [∀ t, (P.obj t).Braided] (t : T) :
    (abelianReadingDiagram J P).obj t =
      internalSheaf J ⋙ (P.obj t).mapCommGrp ⋙ externalSheaf J := rfl

/-- The transitions of the abelian reading of a diagram of endofunctors of sheaves of sets are
the abelian readings of the transitions of the diagram. -/
theorem abelianReadingDiagram_map (P : T ⥤ (Sheaf J (Type u) ⥤ Sheaf J (Type u)))
    [∀ t, (P.obj t).Braided] {t t' : T} (f : t ⟶ t') :
    (abelianReadingDiagram J P).map f =
      Functor.whiskerLeft (internalSheaf J)
        (Functor.whiskerRight (Functor.mapCommGrpNatTrans (P.map f)) (externalSheaf J)) := rfl

end Sites.AbelianSheaf

end AbelianReading

section SemiRepresentable

namespace SimplicialSemiRepresentable

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (K : SimplicialObject (FormalCoproduct.{u} C)) [J.toCoverage.HasPullbacks]

/-- The inverse image `a⁻¹` of sheaves of sets along the total augmentation of the simplicial
site of Stacks 0D8B. This is the uniform construction of Stacks 0D70, part (2). -/
abbrev totalInverseImageSets :
    Sheaf J (Type u) ⥤ Sheaf (situation J K).totalTopology (Type u) :=
  (SimplicialSiteSituation.Augmentation.totalMorphismOfTopoi (situation J K) (Cat.of C) J
    (situationAugmentation J K)).inverseImage

/-- The inverse image along the total augmentation preserves finite limits, being the inverse
image of a morphism of topoi. -/
instance preservesFiniteLimits_totalInverseImageSets :
    PreservesFiniteLimits (totalInverseImageSets J K) :=
  (SimplicialSiteSituation.Augmentation.totalMorphismOfTopoi (situation J K) (Cat.of C) J
    (situationAugmentation J K)).preservesFiniteLimits

/-- **The fork-vertex cosimplicial diagram of endofunctors of sheaves of sets.** In degree `n` it
is `a⁻¹ ⋙ (-)_n ⋙ a_{n,*}`, the degree-`n` vertex of the fork of Stacks 0D70, part (3), read as a
functor of the sheaf on the augmentation site; its transitions are the direct-image transitions
of Stacks 0D70, compatibility (c), precomposed with `a⁻¹`. -/
def forkVertexCosimplicialFunctor :
    SimplexCategory ⥤ (Sheaf J (Type u) ⥤ Sheaf J (Type u)) :=
  SimplicialSiteSituation.Augmentation.cosimplicialPushforward (situation J K) (Cat.of C) J
      (situationAugmentation J K) ⋙
    (Functor.whiskeringLeft _ _ _).obj (totalInverseImageSets J K)

/-- In degree `n` the fork-vertex diagram is the inverse image along the total augmentation
followed by the direct image along the augmentation of degree `n` of the restriction to that
degree. -/
theorem forkVertexCosimplicialFunctor_obj (n : SimplexCategory) :
    (forkVertexCosimplicialFunctor J K).obj n =
      totalInverseImageSets J K ⋙ SimplicialSiteSituation.Augmentation.componentPushforward
        (situation J K) (Cat.of C) J (situationAugmentation J K) n := rfl

/-- The transitions of the fork-vertex diagram are the direct-image transitions of Stacks 0D70,
compatibility (c), precomposed with the inverse image along the total augmentation. -/
theorem forkVertexCosimplicialFunctor_map {m n : SimplexCategory} (φ : m ⟶ n) :
    (forkVertexCosimplicialFunctor J K).map φ =
      Functor.whiskerLeft (totalInverseImageSets J K)
        (SimplicialSiteSituation.Augmentation.componentPushforwardTransition (situation J K)
          (Cat.of C) J (situationAugmentation J K) φ) := rfl

/-- Every term of the fork-vertex diagram preserves finite products: the inverse image along the
total augmentation preserves finite limits, and restriction to a simplicial component and the
direct image along the augmentation of that component are right adjoints. -/
instance preservesFiniteProducts_forkVertexCosimplicialFunctor_obj (n : SimplexCategory) :
    PreservesFiniteProducts ((forkVertexCosimplicialFunctor J K).obj n) :=
  inferInstanceAs (PreservesFiniteProducts (totalInverseImageSets J K ⋙
    SimplicialSiteSituation.Augmentation.componentPushforward (situation J K) (Cat.of C) J
      (situationAugmentation J K) n))

/-- Every term of the fork-vertex diagram is braided, preserving finite products. -/
instance braided_forkVertexCosimplicialFunctor_obj (n : SimplexCategory) :
    ((forkVertexCosimplicialFunctor J K).obj n).Braided :=
  inferInstanceAs ((totalInverseImageSets J K ⋙
    SimplicialSiteSituation.Augmentation.componentPushforward (situation J K) (Cat.of C) J
      (situationAugmentation J K) n).Braided)

/-- **The cosimplicial diagram of the degreewise direct images, on commutative group objects.**
In degree `n` it is `Functor.mapCommGrp` of the direct image along the augmentation of degree `n`
of the restriction to that degree, and its transitions are those of Stacks 0D70, compatibility
(c), applied to commutative group objects. -/
def grpCosimplicialPushforward :
    SimplexCategory ⥤ (CommGrp (Sheaf (situation J K).totalTopology (Type u)) ⥤
      CommGrp (Sheaf J (Type u))) where
  obj n := (SimplicialSiteSituation.Augmentation.componentPushforward (situation J K)
    (Cat.of C) J (situationAugmentation J K) n).mapCommGrp
  map φ := Functor.mapCommGrpNatTrans
    (SimplicialSiteSituation.Augmentation.componentPushforwardTransition (situation J K)
      (Cat.of C) J (situationAugmentation J K) φ)
  map_id n := by
    rw [SimplicialSiteSituation.Augmentation.componentPushforwardTransition_id]
    exact mapCommGrpNatTrans_id _
  map_comp χ φ := by
    rw [SimplicialSiteSituation.Augmentation.componentPushforwardTransition_comp]
    exact mapCommGrpNatTrans_comp _ _

/-- The Čech cosimplicial abelian sheaf of Stacks 0D79 at `a⁻¹F`, before evaluation at `F`: the
cosimplicial diagram of the degreewise direct images of abelian sheaves, precomposed with the
inverse image of abelian sheaves along the total augmentation. -/
def cechReadingDiagram :
    SimplexCategory ⥤ (Sheaf J AddCommGrpCat.{u} ⥤ Sheaf J AddCommGrpCat.{u}) :=
  SimplicialSiteSituation.Augmentation.abelianCosimplicialPushforward (situation J K)
      (Cat.of C) J (situationAugmentation J K) ⋙
    (Functor.whiskeringLeft _ _ _).obj
      (SimplicialSiteSituation.Augmentation.totalInverseImageAb (situation J K) (Cat.of C) J
        (situationAugmentation J K))

/-- The Čech cosimplicial abelian sheaf of Stacks 0D79 at `a⁻¹F` is the evaluation at `F` of the
diagram of endofunctors `cechReadingDiagram`. -/
theorem cechCosimplicialObject_eq (F : Sheaf J AddCommGrpCat.{u}) :
    cechCosimplicialObject J K F = cechReadingDiagram J K ⋙ (evaluation _ _).obj F := rfl

/-- **The equivalence of Stacks 04DB, cancelled on the abelian inverse image.** Internalizing the
inverse image `a⁻¹F` of abelian sheaves is applying the inverse image of sheaves of sets to the
internalization of `F`, naturally in `F`. -/
def internalTotalInverseImageAbIso :
    SimplicialSiteSituation.Augmentation.totalInverseImageAb (situation J K) (Cat.of C) J
          (situationAugmentation J K) ⋙
        Sites.AbelianSheaf.internalSheaf (situation J K).totalTopology ≅
      Sites.AbelianSheaf.internalSheaf J ⋙ (totalInverseImageSets J K).mapCommGrp :=
  Functor.isoWhiskerLeft
      (Sites.AbelianSheaf.internalSheaf J ⋙ (totalInverseImageSets J K).mapCommGrp)
      (Sites.AbelianSheaf.externalInternalIso (situation J K).totalTopology) ≪≫
    (Sites.AbelianSheaf.internalSheaf J ⋙ (totalInverseImageSets J K).mapCommGrp).rightUnitor

/-- **Moving the inverse image inside, on commutative group objects.** The diagram of degreewise
direct images on commutative group objects, precomposed with the inverse image on commutative
group objects, is the fork-vertex diagram taken to commutative group objects. The comparison is
`Functor.mapCommGrpCompIso` in every degree, and it is cosimplicial by
`CategoryTheory.whiskerLeft_mapCommGrpNatTrans_comp_mapCommGrpCompIso_inv`. -/
def forkVertexGrpDiagramIso :
    grpCosimplicialPushforward J K ⋙
        (Functor.whiskeringLeft _ _ _).obj (totalInverseImageSets J K).mapCommGrp ≅
      mapCommGrpDiagram (forkVertexCosimplicialFunctor J K) :=
  NatIso.ofComponents
    (fun n => (Functor.mapCommGrpCompIso (F := totalInverseImageSets J K)
      (G := SimplicialSiteSituation.Augmentation.componentPushforward (situation J K)
        (Cat.of C) J (situationAugmentation J K) n)).symm)
    fun _ => whiskerLeft_mapCommGrpNatTrans_comp_mapCommGrpCompIso_inv _ _

/-- **The Čech diagram of endofunctors of abelian sheaves is the abelian reading of the
fork-vertex diagram of endofunctors of sheaves of sets.** Cancelling the equivalence of
Stacks 04DB in the middle leaves the degreewise direct images on commutative group objects
precomposed with the inverse image, and moving the inverse image inside turns that into the
fork-vertex diagram on commutative group objects. -/
def cechReadingDiagramIso :
    cechReadingDiagram J K ≅
      Sites.AbelianSheaf.abelianReadingDiagram J (forkVertexCosimplicialFunctor J K) :=
  Functor.isoWhiskerLeft (grpCosimplicialPushforward J K)
      (Functor.isoWhiskerRight
        ((Functor.whiskeringLeft _ _ _).mapIso (internalTotalInverseImageAbIso J K))
        ((Functor.whiskeringRight _ _ _).obj (Sites.AbelianSheaf.externalSheaf J))) ≪≫
    Functor.isoWhiskerRight (forkVertexGrpDiagramIso J K)
      (Sites.AbelianSheaf.abelianConjugationFunctor J J)

/-- **The Čech cosimplicial abelian sheaf of Stacks 0D79 at `a⁻¹F` is the abelian reading of the
fork-vertex diagram of Stacks 0D70, part (3), evaluated at `F`.** In degree `n` it is the abelian
reading of `a⁻¹ ⋙ (-)_n ⋙ a_{n,*}` applied to `F`, and its cosimplicial transitions are the
abelian readings of the set-level transitions. -/
def cechCosimplicialObjectIso (F : Sheaf J AddCommGrpCat.{u}) :
    cechCosimplicialObject J K F ≅
      Sites.AbelianSheaf.abelianReadingDiagram J (forkVertexCosimplicialFunctor J K) ⋙
        (evaluation _ _).obj F :=
  Functor.isoWhiskerRight (cechReadingDiagramIso J K) ((evaluation _ _).obj F)

end SimplicialSemiRepresentable

end SemiRepresentable

end CategoryTheory

end
