module
import StacksCore.Tactic.StacksAttribute

public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentationForkConeLaw

/-!
# The total direct image is the equalizer of the two vertex transitions

Let `C` be a simplicial family of sites whose transition functors are cocontinuous and let `a` be
an augmentation of `C` towards a site `(D, K)`. For a sheaf `F` on the total site the total direct
image `a_*F` carries, in every simplicial degree, a canonical map to the direct image of the
augmentation of that degree, and those maps form a cone over the transitions of the component
direct images. Stacks 0D70 (3) asserts more: the total direct image *is* the equalizer of the two
transitions attached to the two maps of the zero-simplex into the one-simplex. This file proves
that universal property.

## Main definitions

* `CategoryTheory.CocontinuousSimplicialSite.Augmentation.restrictForkLeg` and
  `.restrictForkMap`: the leg and the transition of the fork, read through the identification of
  the inverse image along a component inclusion with restriction to that component.
* `CategoryTheory.CocontinuousSimplicialSite.Augmentation.restrictForkTranspose`: the transpose of
  a map into the direct image of a component augmentation, across the adjunctions of the total
  augmentation and of the component inclusion.
* `CategoryTheory.CocontinuousSimplicialSite.Augmentation.vertexRestrictMap`: the map of the
  restrictions in a simplicial degree determined by a map of the degree-zero restrictions and a
  map of the zero-simplex into that degree.
* `CategoryTheory.CocontinuousSimplicialSite.Augmentation.totalDirectImageFork`: **Stacks 0D70
  (3).** The fork of the total direct image over the two vertex transitions.
* `CategoryTheory.CosimplicialObject.coneOfFork`: the cone over a cosimplicial object attached to
  a fork over its two maps in degrees `0 ⇉ 1`.

## Main results

* `CategoryTheory.Adjunction.homEquiv_comp_conjugateEquiv`: precomposing with a transformation of
  left adjoints and then transposing is transposing and then postcomposing with the conjugate
  transformation.
* `MorphismOfTopoi.forkLeg_transpose_restrict` and
  `MorphismOfTopoi.restrictForkMap_transpose`: the transposes of a leg and of a transition of the
  fork of a direct image. The first says that a leg transposes to the restriction of the transpose;
  the second that the transition transposes to the unique completion of a map of the restrictions
  across the transition of the simplicial site.
* `CategoryTheory.CocontinuousSimplicialSite.Augmentation.isIso_fiberTransition_app_inverseImage`:
  the transitions of the inverse image of a sheaf on the augmentation site are invertible.
* `CategoryTheory.CocontinuousSimplicialSite.Augmentation.existsUnique_hom_restrict`: a map of
  sheaves on the total site out of such an inverse image is determined by its degree-zero
  restriction, and every degree-zero map satisfying the one-simplex condition comes from one.
* `CategoryTheory.CocontinuousSimplicialSite.Augmentation.restrictFork_existsUnique` and
  `.totalForkLeg_existsUnique`: the universal property, in restriction form and in the form of
  `totalForkLeg` and `totalForkTransition`.
* `CategoryTheory.CocontinuousSimplicialSite.Augmentation.totalDirectImageForkIsLimit`:
  **Stacks 0D70 (3).** The fork is a limit: the total direct image is the equalizer of the two
  transitions of the direct images of the components attached to the two maps `[0] ⟶ [1]`.
* `CategoryTheory.CosimplicialObject.isLimitForkOfIsLimit`: for a cosimplicial object in any
  category, a limit cone over the whole simplex category has its degree-zero leg as a limit fork of
  the two maps in degrees `0 ⇉ 1`. This is the dual of Simplicial, Lemma 14.20.2.

## References

* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u v' u' v'' u'' v₃ u₃

namespace CategoryTheory

/-! ### A conjugate transformation, read on hom-sets -/

/-- **Precomposition with a transformation of left adjoints, transposed.** For `α : L₂ ⟶ L₁` and
`z : L₁ X ⟶ Y`, transposing `α.app X ≫ z` along the second adjunction is transposing `z` along the
first and then postcomposing with the conjugate of `α`. -/
theorem Adjunction.homEquiv_comp_conjugateEquiv {A : Type u} [Category.{v} A] {B : Type u'}
    [Category.{v'} B] {L₁ L₂ : A ⥤ B} {R₁ R₂ : B ⥤ A} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : L₂ ⟶ L₁) (X : A) (Y : B) (z : L₁.obj X ⟶ Y) :
    adj₂.homEquiv X Y (α.app X ≫ z) =
      adj₁.homEquiv X Y z ≫ (conjugateEquiv adj₁ adj₂ α).app Y := by
  have hu := unit_conjugateEquiv adj₁ adj₂ α X
  have hn := (conjugateEquiv adj₁ adj₂ α).naturality z
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp,
    ← Category.assoc, ← hu, Category.assoc, ← hn, ← Category.assoc]

/-- **A middle factor of a composite of isomorphisms is an isomorphism.** If a threefold composite
is equal to an isomorphism and its first two factors are isomorphisms, so is the third. -/
theorem isIso_of_comp_comp_eq {A : Type u} [Category.{v} A] {W X Y Z : A}
    {c : W ⟶ X} {d : X ⟶ Y} (e : Y ⟶ Z) {q : W ⟶ Z} [IsIso c] [IsIso d] [IsIso q]
    (h : c ≫ d ≫ e = q) : IsIso e := by
  subst h
  have := IsIso.of_isIso_comp_left c (d ≫ e)
  exact IsIso.of_isIso_comp_left d e

end CategoryTheory

/-! ### The transposes of the legs and of the transitions of a fork of direct images -/

namespace MorphismOfTopoi

variable {T : Type u} [Category.{v} T] {Dd : Type u'} [Category.{v'} Dd]
  {Cm : Type u''} [Category.{v''} Cm] {Cn : Type u₃} [Category.{v₃} Cn]

/-- **A leg of the fork, transposed.** The transpose, along the composite of the adjunction of the
direct image and the adjunction of a restriction, of the restriction of a map `A^{-1}G ⟶ F` is the
transpose of that map followed by the direct image of the unit of the restriction. Composed with
the comparison of the direct images, the right-hand side is the leg of the fork precomposed with
the transpose, so this says that a leg acts on transposes as restriction. -/
theorem forkLeg_transpose_restrict {Ai : Dd ⥤ T} {As : T ⥤ Dd} (adjA : Ai ⊣ As)
    {Rm : T ⥤ Cm} {Gm : Cm ⥤ T} (adjm : Rm ⊣ Gm) (F : T) (G : Dd) (s : Ai.obj G ⟶ F) :
    (adjA.comp adjm).homEquiv G (Rm.obj F) (Rm.map s) =
      adjA.homEquiv G F s ≫ As.map (adjm.unit.app F) := by
  have hinner : adjm.homEquiv (Ai.obj G) (Rm.obj F) (Rm.map s) = s ≫ adjm.unit.app F := by
    rw [Adjunction.homEquiv_unit]
    exact (adjm.unit.naturality s).symm
  rw [Adjunction.comp_homEquiv, Equiv.trans_apply, hinner,
    Adjunction.homEquiv_naturality_right]

/-- **A transition of the fork, transposed.** Let `pm`, `pn` compare the composites of the direct
images with two given functors, let `t` compare the transition of those functors with the second
one, and let `ν` be the transition of the restrictions. If the three comparisons and `ν` are
compatible — the hypothesis `hH`, which is the equation between direct images of Stacks 0D70 (3) —
then the transpose of a map `x` into the direct image of the first functor, pushed along the
transition of the restrictions, is the transpose of `x` followed by the transition built from `ν`
and `t`. -/
theorem restrictForkMap_transpose {Ai : Dd ⥤ T} {As : T ⥤ Dd} (adjA : Ai ⊣ As)
    {Rm : T ⥤ Cm} {Gm : Cm ⥤ T} (adjm : Rm ⊣ Gm)
    {Rn : T ⥤ Cn} {Gn : Cn ⥤ T} (adjn : Rn ⊣ Gn)
    {Rf : Cm ⥤ Cn} {Gf : Cn ⥤ Cm} (adjf : Rf ⊣ Gf)
    {Bms : Cm ⥤ Dd} {Bns : Cn ⥤ Dd}
    (pm : Gm ⋙ As ≅ Bms) (pn : Gn ⋙ As ≅ Bns) (t : Gf ⋙ Bms ≅ Bns) (ν : Rm ⋙ Rf ⟶ Rn)
    (hH : Functor.whiskerRight (conjugateEquiv adjn (adjm.comp adjf) ν) As ≫
      Functor.whiskerLeft Gf pm.hom ≫ t.hom = pn.hom)
    (F : T) (G : Dd) (x : G ⟶ Bms.obj (Rm.obj F)) :
    Rf.map (((adjA.comp adjm).homEquiv G (Rm.obj F)).symm
          (x ≫ pm.inv.app (Rm.obj F))) ≫ ν.app F =
      ν.app (Ai.obj G) ≫ ((adjA.comp adjn).homEquiv G (Rn.obj F)).symm
        ((x ≫ Bms.map (adjf.homEquiv (Rm.obj F) (Rn.obj F) (ν.app F)) ≫
          t.hom.app (Rn.obj F)) ≫ pn.inv.app (Rn.obj F)) := by
  set W := adjf.homEquiv (Rm.obj F) (Rn.obj F) (ν.app F) with hW
  set ξ := ((adjA.comp adjm).homEquiv G (Rm.obj F)).symm (x ≫ pm.inv.app (Rm.obj F)) with hξ
  set z := ((adjA.comp adjn).homEquiv G (Rn.obj F)).symm
    ((x ≫ Bms.map W ≫ t.hom.app (Rn.obj F)) ≫ pn.inv.app (Rn.obj F)) with hz
  have hξ' : (adjA.comp adjm).homEquiv G (Rm.obj F) ξ = x ≫ pm.inv.app (Rm.obj F) := by
    rw [hξ, Equiv.apply_symm_apply]
  have hz' : (adjA.comp adjn).homEquiv G (Rn.obj F) z =
      (x ≫ Bms.map W ≫ t.hom.app (Rn.obj F)) ≫ pn.inv.app (Rn.obj F) := by
    rw [hz, Equiv.apply_symm_apply]
  have hξ'' : adjA.homEquiv G (Gm.obj (Rm.obj F))
      (adjm.homEquiv (Ai.obj G) (Rm.obj F) ξ) = x ≫ pm.inv.app (Rm.obj F) := by
    rw [← hξ', Adjunction.comp_homEquiv, Equiv.trans_apply]
  have hz'' : adjA.homEquiv G (Gn.obj (Rn.obj F))
      (adjn.homEquiv (Ai.obj G) (Rn.obj F) z) =
      (x ≫ Bms.map W ≫ t.hom.app (Rn.obj F)) ≫ pn.inv.app (Rn.obj F) := by
    rw [← hz', Adjunction.comp_homEquiv, Equiv.trans_apply]
  have hHc := congrFun (congrArg NatTrans.app hH) (Rn.obj F)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hHc
  have hconj : As.map ((conjugateEquiv adjn (adjm.comp adjf) ν).app (Rn.obj F)) =
      pn.hom.app (Rn.obj F) ≫ t.inv.app (Rn.obj F) ≫ pm.inv.app (Gf.obj (Rn.obj F)) := by
    rw [← hHc]
    simp
  have hkey : pm.inv.app (Rm.obj F) ≫ As.map (Gm.map W) =
      Bms.map W ≫ t.hom.app (Rn.obj F) ≫ pn.inv.app (Rn.obj F) ≫
        As.map ((conjugateEquiv adjn (adjm.comp adjf) ν).app (Rn.obj F)) := by
    have hnat := pm.hom.naturality W
    simp only [Functor.comp_map] at hnat
    have h2 : pm.inv.app (Rm.obj F) ≫ As.map (Gm.map W) ≫
        pm.hom.app (Gf.obj (Rn.obj F)) = Bms.map W := by
      rw [hnat]
      simp
    rw [hconj]
    rw [show Bms.map W ≫ t.hom.app (Rn.obj F) ≫ pn.inv.app (Rn.obj F) ≫
        (pn.hom.app (Rn.obj F) ≫ t.inv.app (Rn.obj F) ≫ pm.inv.app (Gf.obj (Rn.obj F))) =
      Bms.map W ≫ pm.inv.app (Gf.obj (Rn.obj F)) from by simp]
    rw [← h2]
    simp
  have hL : (adjm.comp adjf).homEquiv (Ai.obj G) (Rn.obj F) (Rf.map ξ ≫ ν.app F) =
      adjm.homEquiv (Ai.obj G) (Rm.obj F) ξ ≫ Gm.map W := by
    rw [Adjunction.comp_homEquiv, Equiv.trans_apply, Adjunction.homEquiv_naturality_left,
      ← hW, Adjunction.homEquiv_naturality_right]
  have hR : (adjm.comp adjf).homEquiv (Ai.obj G) (Rn.obj F) (ν.app (Ai.obj G) ≫ z) =
      adjn.homEquiv (Ai.obj G) (Rn.obj F) z ≫
        (conjugateEquiv adjn (adjm.comp adjf) ν).app (Rn.obj F) :=
    Adjunction.homEquiv_comp_conjugateEquiv adjn (adjm.comp adjf) ν (Ai.obj G) (Rn.obj F) z
  refine ((adjm.comp adjf).homEquiv (Ai.obj G) (Rn.obj F)).injective ?_
  rw [hL, hR]
  refine (adjA.homEquiv G (Gm.obj (Gf.obj (Rn.obj F)))).injective ?_
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right, hξ'', hz'']
  simp only [Category.assoc]
  rw [hkey]

end MorphismOfTopoi

/-! ### Limits of a cosimplicial object -/

namespace CategoryTheory.CosimplicialObject

variable {A : Type u} [Category.{v} A] (X : SimplexCategory ⥤ A)

/-- The two vertices of the one-simplex map to the vertices `0` and `i` under the edge from `0`
to `i`. -/
private theorem const_comp_mkOfLe (n : SimplexCategory) (i : Fin (n.len + 1)) :
    SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 0 ≫
        SimplexCategory.mkOfLe 0 i (Fin.zero_le i) =
      SimplexCategory.const (SimplexCategory.mk 0) n 0 ∧
    SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 1 ≫
        SimplexCategory.mkOfLe 0 i (Fin.zero_le i) =
      SimplexCategory.const (SimplexCategory.mk 0) n i := by
  constructor <;> (rw [SimplexCategory.const_comp]; rfl)

/-- **Two vertices of a simplex are the two ends of an edge.** A map out of a cone point which
equalises the two maps of the one-simplex equalises the maps of any two vertices of any simplex:
the two vertices `0` and `i` of `⦋n⦌` are the images of the two vertices of `⦋1⦌` under the edge
joining them. -/
theorem vertex_eq_of_edge_eq {W : A} (e : W ⟶ X.obj (SimplexCategory.mk 0))
    (h : e ≫ X.map (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 0) =
      e ≫ X.map (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 1))
    (n : SimplexCategory) (i : Fin (n.len + 1)) :
    e ≫ X.map (SimplexCategory.const (SimplexCategory.mk 0) n 0) =
      e ≫ X.map (SimplexCategory.const (SimplexCategory.mk 0) n i) := by
  obtain ⟨h0, h1⟩ := const_comp_mkOfLe n i
  rw [← h0, ← h1]
  simpa only [Category.assoc, ← X.map_comp] using
    congrArg (fun k => k ≫ X.map (SimplexCategory.mkOfLe 0 i (Fin.zero_le i))) h

/-- The degree-zero leg of a cone over a cosimplicial object equalises the two maps of the
one-simplex. -/
theorem cone_condition (c : Cone X) :
    c.π.app (SimplexCategory.mk 0) ≫
        X.map (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 0) =
      c.π.app (SimplexCategory.mk 0) ≫
        X.map (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 1) := by
  rw [c.w (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 0),
    c.w (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 1)]

/-- The cone over a cosimplicial object attached to a fork over its two maps in degrees `0 ⇉ 1`:
its leg in simplicial degree `n` is the map of the fork followed by the first vertex of that
degree. -/
def coneOfFork
    (s : Fork (X.map (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 0))
      (X.map (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 1))) :
    Cone X where
  pt := s.pt
  π :=
    { app := fun n => s.ι ≫ X.map (SimplexCategory.const (SimplexCategory.mk 0) n 0)
      naturality := fun n m φ => by
        dsimp only [Functor.const_obj_map, Functor.const_obj_obj]
        rw [Category.id_comp, Category.assoc, ← X.map_comp, SimplexCategory.const_comp]
        exact vertex_eq_of_edge_eq X s.ι (Fork.condition s) m (φ.toOrderHom 0) }

/-- **The limit of a cosimplicial object is the equalizer of its two maps in degrees `0 ⇉ 1`.**
The degree-zero leg of a limit cone over a cosimplicial object is a limit fork of the two maps
induced by the two vertices of the one-simplex. This is the dual of Simplicial, Lemma 14.20.2. -/
def isLimitForkOfIsLimit (c : Cone X) (hc : IsLimit c) :
    IsLimit (Fork.ofι (c.π.app (SimplexCategory.mk 0)) (cone_condition X c)) := by
  refine Fork.IsLimit.mk _ (fun s => hc.lift (coneOfFork X s)) (fun s => ?_) (fun s m hm => ?_)
  · refine Eq.trans (hc.fac (coneOfFork X s) (SimplexCategory.mk 0)) ?_
    change s.ι ≫ X.map (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 0) 0) = _
    rw [SimplexCategory.const_eq_id, X.map_id, Category.comp_id]
  · refine hc.uniq (coneOfFork X s) m (fun n => ?_)
    change m ≫ c.π.app n = s.ι ≫ X.map (SimplexCategory.const (SimplexCategory.mk 0) n 0)
    rw [← hm, Category.assoc]
    exact congrArg (fun k => m ≫ k)
      (c.w (SimplexCategory.const (SimplexCategory.mk 0) n 0)).symm

end CategoryTheory.CosimplicialObject

/-! ### The fork of the total augmentation -/

namespace CategoryTheory

namespace CocontinuousSimplicialSite

namespace Augmentation

open CategoryTheory.SimplicialSiteSituation

variable {C : CocontinuousSimplicialSite.{u}} {D : Cat.{u, u}} {K : GrothendieckTopology D}

/-! #### The augmentation data, spelled through the situation -/

/-- The total augmentation as a morphism of topoi, with its source topos spelled through the total
topology of the situation. -/
def totalMorphism (a : C.Augmentation D K) :
    MorphismOfTopoi (Sheaf (situation C).totalTopology (Type u)) (Sheaf K (Type u)) :=
  totalMorphismOfTopoi a

/-- The augmentation of the component in simplicial degree `k` as a morphism of topoi, with its
source topos spelled through the component topology of the situation. -/
def componentAug (a : C.Augmentation D K) (k : SimplexCategory) :
    MorphismOfTopoi (Sheaf ((situation C).componentTopology k) (Type u)) (Sheaf K (Type u)) :=
  SimplicialSiteSituation.Augmentation.componentAugmentation (situation C) D K a k

/-- **Stacks 0D70, compatibility (2).** Composing the inclusion of a component with the total
augmentation gives the augmentation of that component. -/
def componentCompIso (a : C.Augmentation D K) (k : SimplexCategory) :
    (SimplicialSiteSituation.componentMorphism (situation C) k).pushforward ⋙
        (totalMorphism a).pushforward ≅
      (componentAug a k).pushforward :=
  componentInclusionCompPushforwardIso a k

/-- **Stacks 0D70, compatibility (1).** The comparison of the direct images of the component
augmentations along a map of simplices. -/
def transitionAugIso (a : C.Augmentation D K) {m n : SimplexCategory} (φ : m ⟶ n) :
    ((situation C).transitionMorphism φ).pushforward ⋙ (componentAug a m).pushforward ≅
      (componentAug a n).pushforward :=
  SimplicialSiteSituation.Augmentation.transitionPushforwardIso (situation C) D K a φ

/-- The leg of the fork of Stacks 0D70 (3) in simplicial degree `k`. -/
def totalForkLeg (a : C.Augmentation D K) (F : Sheaf (situation C).totalTopology (Type u))
    (k : SimplexCategory) :
    (totalMorphism a).pushforward.obj F ⟶
      (componentAug a k).pushforward.obj
        ((SimplicialSiteSituation.componentMorphism (situation C) k).inverseImage.obj F) :=
  totalComponentUnitMap a F k

/-- The transition of the fork of Stacks 0D70 (3) attached to a map of simplices. -/
def totalForkTransition (a : C.Augmentation D K)
    (F : Sheaf (situation C).totalTopology (Type u)) {m n : SimplexCategory} (φ : m ⟶ n) :
    (componentAug a m).pushforward.obj
        ((SimplicialSiteSituation.componentMorphism (situation C) m).inverseImage.obj F) ⟶
      (componentAug a n).pushforward.obj
        ((SimplicialSiteSituation.componentMorphism (situation C) n).inverseImage.obj F) :=
  componentDirectImageTransitionMap a F φ

/-! #### The fork read through restriction to the components -/

/-- The leg of the fork in simplicial degree `k`, read through the identification of the inverse
image along the component inclusion with restriction to that component: the direct image of the
unit of the adjunction between restriction and the direct image along the inclusion, followed by
the comparison of the total augmentation with the augmentation of that component. -/
def restrictForkLeg (a : C.Augmentation D K) (F : Sheaf (situation C).totalTopology (Type u))
    (k : SimplexCategory) :
    (totalMorphism a).pushforward.obj F ⟶
      (componentAug a k).pushforward.obj (((situation C).restrict k).obj F) :=
  (totalMorphism a).pushforward.map ((componentRestrictAdj k).unit.app F) ≫
    (componentCompIso a k).hom.app (((situation C).restrict k).obj F)

/-- The transition of the fork attached to a map of simplices, in the same reading: the direct
image of the direct-image transition of the restrictions, followed by the comparison of the
component augmentations. -/
def restrictForkMap (a : C.Augmentation D K) (F : Sheaf (situation C).totalTopology (Type u))
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (componentAug a m).pushforward.obj (((situation C).restrict m).obj F) ⟶
      (componentAug a n).pushforward.obj (((situation C).restrict n).obj F) :=
  (componentAug a m).pushforward.map (((situation C).restrictTransition φ).app F) ≫
    (transitionAugIso a φ).hom.app (((situation C).restrict n).obj F)

/-- The isomorphism comparing the two readings of the fork in simplicial degree `k`: the direct
image of the augmentation of that component, applied to the identification of the inverse image
along the component inclusion with restriction to the component. -/
def restrictForkIso (a : C.Augmentation D K) (F : Sheaf (situation C).totalTopology (Type u))
    (k : SimplexCategory) :
    (componentAug a k).pushforward.obj (((situation C).restrict k).obj F) ≅
      (componentAug a k).pushforward.obj
        ((SimplicialSiteSituation.componentMorphism (situation C) k).inverseImage.obj F) :=
  (componentAug a k).pushforward.mapIso ((componentInverseImageRestrictIso (C := C) k).app F).symm

/-- The comparison of the two readings of the fork, as a morphism. -/
theorem restrictForkIso_hom (a : C.Augmentation D K)
    (F : Sheaf (situation C).totalTopology (Type u)) (k : SimplexCategory) :
    (restrictForkIso a F k).hom =
      (componentAug a k).pushforward.map
        ((componentInverseImageRestrictIso (C := C) k).inv.app F) := rfl

/-- The leg of the fork of Stacks 0D70 (3) is the leg in restriction form, followed by the
comparison of the two readings. -/
theorem totalForkLeg_eq (a : C.Augmentation D K)
    (F : Sheaf (situation C).totalTopology (Type u)) (k : SimplexCategory) :
    totalForkLeg a F k = restrictForkLeg a F k ≫ (restrictForkIso a F k).hom := by
  have h0 : totalForkLeg a F k =
      MorphismOfTopoi.forkLeg (totalMorphism a)
        (SimplicialSiteSituation.componentMorphism (situation C) k)
        (componentAug a k).pushforward (componentCompIso a k)
        (SimplicialSiteSituation.componentMorphism (situation C) k).adj F := rfl
  have hu : MorphismOfTopoi.forkLegOfRestriction (totalMorphism a)
        (SimplicialSiteSituation.componentMorphism (situation C) k)
        (componentAug a k).pushforward (componentCompIso a k)
        (componentInverseImageRestrictIso (C := C) k)
        (SimplicialSiteSituation.componentMorphism (situation C) k).adj F =
      restrictForkLeg a F k :=
    congrArg (fun g => (totalMorphism a).pushforward.map g ≫
        (componentCompIso a k).hom.app (((situation C).restrict k).obj F))
      (componentRestrictAdj_unit k F)
  rw [h0, MorphismOfTopoi.forkLeg_eq_forkLegOfRestriction (totalMorphism a)
      (SimplicialSiteSituation.componentMorphism (situation C) k)
      (componentAug a k).pushforward (componentCompIso a k)
      (componentInverseImageRestrictIso (C := C) k)
      (SimplicialSiteSituation.componentMorphism (situation C) k).adj F, hu, restrictForkIso_hom]

/-- The transition of the fork of Stacks 0D70 (3) is the transition in restriction form,
conjugated by the comparisons of the two readings. -/
theorem restrictForkIso_comp_totalForkTransition (a : C.Augmentation D K)
    (F : Sheaf (situation C).totalTopology (Type u)) {m n : SimplexCategory} (φ : m ⟶ n) :
    (restrictForkIso a F m).hom ≫ totalForkTransition a F φ =
      restrictForkMap a F φ ≫ (restrictForkIso a F n).hom := by
  have hnat := (transitionAugIso a φ).hom.naturality
    ((componentInverseImageRestrictIso (C := C) n).inv.app F)
  simp only [Functor.comp_map] at hnat
  have hmap : totalForkTransition a F φ =
      (componentAug a m).pushforward.map
          ((componentInverseImageRestrictIso (C := C) m).hom.app F ≫
            ((situation C).restrictTransition φ).app F ≫
              ((situation C).transitionMorphism φ).pushforward.map
                ((componentInverseImageRestrictIso (C := C) n).inv.app F)) ≫
        (transitionAugIso a φ).hom.app
          ((SimplicialSiteSituation.componentMorphism (situation C) n).inverseImage.obj F) :=
    componentDirectImageTransitionMap_eq a F φ
  rw [hmap, restrictForkIso_hom, restrictForkIso_hom, restrictForkMap]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, hnat]

/-! #### The universal property -/

/-- The transpose of a map from a sheaf on the augmentation site into the direct image of the
augmentation of the component in simplicial degree `k`: the comparison of the direct images
followed by the transpose along the composite of the adjunction of the total augmentation with the
adjunction between restriction and the direct image along the component inclusion. -/
def restrictForkTranspose (a : C.Augmentation D K)
    (F : Sheaf (situation C).totalTopology (Type u)) {G : Sheaf K (Type u)} (k : SimplexCategory)
    (x : G ⟶ (componentAug a k).pushforward.obj (((situation C).restrict k).obj F)) :
    ((situation C).restrict k).obj ((totalMorphism a).inverseImage.obj G) ⟶
      ((situation C).restrict k).obj F :=
  (((totalMorphism a).adj.comp (componentRestrictAdj k)).homEquiv G
      (((situation C).restrict k).obj F)).symm
    (x ≫ (componentCompIso a k).inv.app (((situation C).restrict k).obj F))

/-- A map into the total direct image, followed by a leg of the fork in restriction form,
transposes to the restriction of its own transpose. -/
theorem restrictForkTranspose_comp_restrictForkLeg (a : C.Augmentation D K)
    (F : Sheaf (situation C).totalTopology (Type u)) {G : Sheaf K (Type u)} (k : SimplexCategory)
    (l : G ⟶ (totalMorphism a).pushforward.obj F) :
    restrictForkTranspose a F k (l ≫ restrictForkLeg a F k) =
      ((situation C).restrict k).map (((totalMorphism a).adj.homEquiv G F).symm l) := by
  refine (((totalMorphism a).adj.comp (componentRestrictAdj k)).homEquiv G
    (((situation C).restrict k).obj F)).injective ?_
  rw [restrictForkTranspose, Equiv.apply_symm_apply,
    MorphismOfTopoi.forkLeg_transpose_restrict (totalMorphism a).adj
      (componentRestrictAdj k) F G (((totalMorphism a).adj.homEquiv G F).symm l),
    Equiv.apply_symm_apply, restrictForkLeg, Category.assoc, Category.assoc,
    Iso.hom_inv_id_app]
  exact congrArg (fun g => l ≫ g) (Category.comp_id _)

/-- The transpose `restrictForkTranspose` is injective. -/
theorem restrictForkTranspose_injective (a : C.Augmentation D K)
    (F : Sheaf (situation C).totalTopology (Type u)) (G : Sheaf K (Type u))
    (k : SimplexCategory) :
    Function.Injective (restrictForkTranspose a F (G := G) k) := by
  intro y y' h
  have h2 := congrArg (((totalMorphism a).adj.comp (componentRestrictAdj k)).homEquiv G
    (((situation C).restrict k).obj F)) h
  rw [restrictForkTranspose, restrictForkTranspose, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply] at h2
  exact (cancel_mono ((componentCompIso a k).inv.app (((situation C).restrict k).obj F))).mp h2

/-- **The transitions of the inverse image of a sheaf on the augmentation site are invertible.** -/
instance isIso_fiberTransition_app_inverseImage (a : C.Augmentation D K)
    {m n : SimplexCategory} (φ : m ⟶ n) (G : Sheaf K (Type u)) :
    IsIso (((situation C).fiberTransition φ).app ((totalMorphism a).inverseImage.obj G)) := by
  have h : (conjugateEquiv ((componentAug a m).adj.comp
            ((situation C).transitionMorphism φ).adj)
          (componentAug a n).adj).symm (transitionAugIso a φ).hom ≫
        Functor.whiskerRight
            ((conjugateEquiv ((totalMorphism a).adj.comp (componentRestrictAdj m))
                (componentAug a m).adj).symm (componentCompIso a m).hom)
            ((situation C).transitionMorphism φ).inverseImage ≫
          Functor.whiskerLeft (totalMorphism a).inverseImage
            ((situation C).fiberTransition φ) =
      (conjugateEquiv ((totalMorphism a).adj.comp (componentRestrictAdj n))
          (componentAug a n).adj).symm (componentCompIso a n).hom :=
    inverseImageCompatibility a φ
  have h2 : IsIso (Functor.whiskerLeft (totalMorphism a).inverseImage
      ((situation C).fiberTransition φ)) := isIso_of_comp_comp_eq _ h
  exact NatIso.isIso_app_of_isIso (Functor.whiskerLeft (totalMorphism a).inverseImage
    ((situation C).fiberTransition φ)) G

/-- The map of the restrictions in simplicial degree `n` determined by a map `s` of the
degree-zero restrictions and a map of the zero-simplex into that degree: the inverse of the
transition of the inverse image of the sheaf on the augmentation site, the inverse image of `s`,
and the transition of the sheaf on the total site. -/
def vertexRestrictMap (a : C.Augmentation D K) (F : Sheaf (situation C).totalTopology (Type u))
    (G : Sheaf K (Type u))
    (s : ((situation C).restrict (SimplexCategory.mk 0)).obj
        ((totalMorphism a).inverseImage.obj G) ⟶
      ((situation C).restrict (SimplexCategory.mk 0)).obj F)
    {n : SimplexCategory} (φ : SimplexCategory.mk 0 ⟶ n) :
    ((situation C).restrict n).obj ((totalMorphism a).inverseImage.obj G) ⟶
      ((situation C).restrict n).obj F :=
  inv (((situation C).fiberTransition φ).app ((totalMorphism a).inverseImage.obj G)) ≫
    ((situation C).transitionMorphism φ).inverseImage.map s ≫
      ((situation C).fiberTransition φ).app F

/-- The defining square of `vertexRestrictMap`: it completes the inverse image of `s` across the
transitions attached to the given map of simplices. -/
theorem vertexRestrictMap_spec (a : C.Augmentation D K)
    (F : Sheaf (situation C).totalTopology (Type u)) (G : Sheaf K (Type u))
    (s : ((situation C).restrict (SimplexCategory.mk 0)).obj
        ((totalMorphism a).inverseImage.obj G) ⟶
      ((situation C).restrict (SimplexCategory.mk 0)).obj F)
    {n : SimplexCategory} (φ : SimplexCategory.mk 0 ⟶ n) :
    ((situation C).fiberTransition φ).app ((totalMorphism a).inverseImage.obj G) ≫
        vertexRestrictMap a F G s φ =
      ((situation C).transitionMorphism φ).inverseImage.map s ≫
        ((situation C).fiberTransition φ).app F := by
  rw [vertexRestrictMap, IsIso.hom_inv_id_assoc]

/-- The square of `vertexRestrictMap_spec` determines the map: the transition of the inverse image
of the sheaf on the augmentation site is invertible. -/
theorem eq_vertexRestrictMap (a : C.Augmentation D K)
    (F : Sheaf (situation C).totalTopology (Type u)) (G : Sheaf K (Type u))
    (s : ((situation C).restrict (SimplexCategory.mk 0)).obj
        ((totalMorphism a).inverseImage.obj G) ⟶
      ((situation C).restrict (SimplexCategory.mk 0)).obj F)
    {n : SimplexCategory} (φ : SimplexCategory.mk 0 ⟶ n)
    (y : ((situation C).restrict n).obj ((totalMorphism a).inverseImage.obj G) ⟶
      ((situation C).restrict n).obj F)
    (hy : ((situation C).fiberTransition φ).app ((totalMorphism a).inverseImage.obj G) ≫ y =
      ((situation C).transitionMorphism φ).inverseImage.map s ≫
        ((situation C).fiberTransition φ).app F) :
    y = vertexRestrictMap a F G s φ :=
  (cancel_epi (((situation C).fiberTransition φ).app
    ((totalMorphism a).inverseImage.obj G))).mp
      (hy.trans (vertexRestrictMap_spec a F G s φ).symm)

/-- The map determined by the identity vertex of the zero-simplex is the given map. -/
theorem vertexRestrictMap_id (a : C.Augmentation D K)
    (F : Sheaf (situation C).totalTopology (Type u)) (G : Sheaf K (Type u))
    (s : ((situation C).restrict (SimplexCategory.mk 0)).obj
        ((totalMorphism a).inverseImage.obj G) ⟶
      ((situation C).restrict (SimplexCategory.mk 0)).obj F) :
    vertexRestrictMap a F G s (𝟙 (SimplexCategory.mk 0)) = s := by
  refine (eq_vertexRestrictMap a F G s (𝟙 (SimplexCategory.mk 0)) s ?_).symm
  rw [fiberTransition_id, fiberTransition_id]
  exact ((canonicalIdentityComparison (situation C) (SimplexCategory.mk 0)).hom.naturality s).symm

/-- **The composition law of the determined maps.** Completing the map determined by a vertex of
an intermediate degree across a further map of simplices gives the map determined by the composite
vertex. -/
theorem vertexRestrictMap_comp (a : C.Augmentation D K)
    (F : Sheaf (situation C).totalTopology (Type u)) (G : Sheaf K (Type u))
    (s : ((situation C).restrict (SimplexCategory.mk 0)).obj
        ((totalMorphism a).inverseImage.obj G) ⟶
      ((situation C).restrict (SimplexCategory.mk 0)).obj F)
    {m n : SimplexCategory} (ψ : SimplexCategory.mk 0 ⟶ m) (φ : m ⟶ n) :
    inv (((situation C).fiberTransition φ).app ((totalMorphism a).inverseImage.obj G)) ≫
        ((situation C).transitionMorphism φ).inverseImage.map
            (vertexRestrictMap a F G s ψ) ≫
          ((situation C).fiberTransition φ).app F =
      vertexRestrictMap a F G s (ψ ≫ φ) := by
  refine eq_vertexRestrictMap a F G s (ψ ≫ φ) _ ?_
  have hnat := (canonicalCompositionComparison (situation C) ψ φ).hom.naturality s
  simp only [Functor.comp_map] at hnat
  rw [fiberTransition_comp, fiberTransition_comp, Category.assoc, Category.assoc,
    IsIso.hom_inv_id_assoc, ← CategoryTheory.Functor.map_comp_assoc,
    vertexRestrictMap_spec a F G s ψ, CategoryTheory.Functor.map_comp, Category.assoc,
    ← Category.assoc _ _ (((situation C).transitionMorphism φ).inverseImage.map
      (((situation C).fiberTransition ψ).app F) ≫ ((situation C).fiberTransition φ).app F),
    ← hnat, Category.assoc]

/-- **Two vertices of a simplex determine the same map.** If the two vertices of the one-simplex
determine the same map, then so do any two vertices of any simplex. -/
theorem vertexRestrictMap_const (a : C.Augmentation D K)
    (F : Sheaf (situation C).totalTopology (Type u)) (G : Sheaf K (Type u))
    (s : ((situation C).restrict (SimplexCategory.mk 0)).obj
        ((totalMorphism a).inverseImage.obj G) ⟶
      ((situation C).restrict (SimplexCategory.mk 0)).obj F)
    (hs : vertexRestrictMap a F G s
          (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 0) =
        vertexRestrictMap a F G s
          (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 1))
    (n : SimplexCategory) (i : Fin (n.len + 1)) :
    vertexRestrictMap a F G s (SimplexCategory.const (SimplexCategory.mk 0) n i) =
      vertexRestrictMap a F G s (SimplexCategory.const (SimplexCategory.mk 0) n 0) := by
  obtain ⟨h0, h1⟩ := CosimplicialObject.const_comp_mkOfLe n i
  rw [← h0, ← h1, ← vertexRestrictMap_comp, ← vertexRestrictMap_comp, hs]

/-- **The determined family is compatible with every transition, in inverse-image form.** For
every map of simplices, the inverse image of the map determined by the first vertex of its source
degree, followed by the transition of the sheaf on the total site, is the transition of the inverse
image followed by the map determined by the first vertex of its target degree. -/
theorem vertexRestrictMap_compatible (a : C.Augmentation D K)
    (F : Sheaf (situation C).totalTopology (Type u)) (G : Sheaf K (Type u))
    (s : ((situation C).restrict (SimplexCategory.mk 0)).obj
        ((totalMorphism a).inverseImage.obj G) ⟶
      ((situation C).restrict (SimplexCategory.mk 0)).obj F)
    (hs : vertexRestrictMap a F G s
          (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 0) =
        vertexRestrictMap a F G s
          (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 1))
    {m n : SimplexCategory} (φ : m ⟶ n) :
    ((situation C).transitionMorphism φ).inverseImage.map
          (vertexRestrictMap a F G s (SimplexCategory.const (SimplexCategory.mk 0) m 0)) ≫
        ((situation C).fiberTransition φ).app F =
      ((situation C).fiberTransition φ).app ((totalMorphism a).inverseImage.obj G) ≫
        vertexRestrictMap a F G s (SimplexCategory.const (SimplexCategory.mk 0) n 0) := by
  have hcomp := vertexRestrictMap_comp a F G s
    (SimplexCategory.const (SimplexCategory.mk 0) m 0) φ
  rw [SimplexCategory.const_comp, vertexRestrictMap_const a F G s hs n (φ.toOrderHom 0)] at hcomp
  rw [← hcomp, IsIso.hom_inv_id_assoc]

/-- A map of sheaves on the total site out of the inverse image of a sheaf on the augmentation
site restricts, in every simplicial degree, to the map determined by its own degree-zero
restriction and the first vertex of that degree. -/
theorem restrict_map_eq_vertexRestrictMap (a : C.Augmentation D K)
    (F : Sheaf (situation C).totalTopology (Type u)) (G : Sheaf K (Type u))
    (σ : (totalMorphism a).inverseImage.obj G ⟶ F) (n : SimplexCategory) :
    ((situation C).restrict n).map σ =
      vertexRestrictMap a F G (((situation C).restrict (SimplexCategory.mk 0)).map σ)
        (SimplexCategory.const (SimplexCategory.mk 0) n 0) := by
  refine eq_vertexRestrictMap a F G _ _ _ ?_
  exact (((situation C).fiberTransition
    (SimplexCategory.const (SimplexCategory.mk 0) n 0)).naturality σ).symm

/-- **The descent of Stacks 09WF at an inverse image.** A map of sheaves on the total site out of
the inverse image of a sheaf on the augmentation site is uniquely determined by its degree-zero
restriction, and a map of the degree-zero restrictions is the degree-zero restriction of exactly
one such map as soon as the two vertices of the one-simplex determine the same map. -/
theorem existsUnique_hom_restrict (a : C.Augmentation D K)
    (F : Sheaf (situation C).totalTopology (Type u)) (G : Sheaf K (Type u))
    (s : ((situation C).restrict (SimplexCategory.mk 0)).obj
        ((totalMorphism a).inverseImage.obj G) ⟶
      ((situation C).restrict (SimplexCategory.mk 0)).obj F)
    (hs : vertexRestrictMap a F G s
          (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 0) =
        vertexRestrictMap a F G s
          (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 1)) :
    ∃! σ : (totalMorphism a).inverseImage.obj G ⟶ F,
      ((situation C).restrict (SimplexCategory.mk 0)).map σ = s := by
  have hβ : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      vertexRestrictMap a F G s (SimplexCategory.const (SimplexCategory.mk 0) m 0) ≫
          ((situation C).restrictTransition φ).app F =
        ((situation C).restrictTransition φ).app ((totalMorphism a).inverseImage.obj G) ≫
          ((situation C).transitionMorphism φ).pushforward.map
            (vertexRestrictMap a F G s
              (SimplexCategory.const (SimplexCategory.mk 0) n 0)) := by
    intro m n φ
    rw [← fiberTransition_adj, ← fiberTransition_adj]
    exact Adjunction.homEquiv_naturality_left_square _ _ _ _ _
      (vertexRestrictMap_compatible a F G s hs φ)
  have h1 : ((situation C).restrict (SimplexCategory.mk 0)).map
      ((situation C).totalHomOfFamily
        (fun n => vertexRestrictMap a F G s
          (SimplexCategory.const (SimplexCategory.mk 0) n 0)) hβ) = s := by
    rw [(situation C).restrict_map_totalHomOfFamily _ hβ (SimplexCategory.mk 0),
      SimplexCategory.const_eq_id, vertexRestrictMap_id]
  refine ⟨_, h1, fun σ hσ => ?_⟩
  have hσ' : ((situation C).restrict (SimplexCategory.mk 0)).map σ = s := hσ
  refine (situation C).total_hom_ext (fun n => ?_)
  rw [restrict_map_eq_vertexRestrictMap a F G σ n, hσ',
    (situation C).restrict_map_totalHomOfFamily _ hβ n]

/-- **The universal property of the fork, in restriction form.** Every map from a sheaf on the
augmentation site into the direct image of the degree-zero component augmentation which equalises
the two transitions attached to the two vertices of the one-simplex factors uniquely through the
total direct image. -/
theorem restrictFork_existsUnique (a : C.Augmentation D K)
    (F : Sheaf (situation C).totalTopology (Type u)) (G : Sheaf K (Type u))
    (x : G ⟶ (componentAug a (SimplexCategory.mk 0)).pushforward.obj
      (((situation C).restrict (SimplexCategory.mk 0)).obj F))
    (hx : x ≫ restrictForkMap a F
          (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 0) =
        x ≫ restrictForkMap a F
          (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 1)) :
    ∃! l : G ⟶ (totalMorphism a).pushforward.obj F,
      l ≫ restrictForkLeg a F (SimplexCategory.mk 0) = x := by
  have htr : ∀ i : Fin 2,
      restrictForkTranspose a F (SimplexCategory.mk 1)
          (x ≫ restrictForkMap a F
            (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) i)) =
        vertexRestrictMap a F G (restrictForkTranspose a F (SimplexCategory.mk 0) x)
          (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) i) := by
    intro i
    refine eq_vertexRestrictMap a F G _ _ _ ?_
    have key := MorphismOfTopoi.restrictForkMap_transpose (totalMorphism a).adj
      (componentRestrictAdj (C := C) (SimplexCategory.mk 0))
      (componentRestrictAdj (C := C) (SimplexCategory.mk 1))
      ((situation C).transitionMorphism
        (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) i)).adj
      (componentCompIso a (SimplexCategory.mk 0)) (componentCompIso a (SimplexCategory.mk 1))
      (transitionAugIso a
        (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) i))
      ((situation C).fiberTransition
        (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) i))
      (directImageCompatibility a
        (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) i)) F G x
    rw [fiberTransition_adj] at key
    exact key.symm
  have hs : vertexRestrictMap a F G (restrictForkTranspose a F (SimplexCategory.mk 0) x)
        (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 0) =
      vertexRestrictMap a F G (restrictForkTranspose a F (SimplexCategory.mk 0) x)
        (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 1) := by
    rw [← htr 0, ← htr 1, hx]
  obtain ⟨σ, hσ, hσuniq⟩ := existsUnique_hom_restrict a F G
    (restrictForkTranspose a F (SimplexCategory.mk 0) x) hs
  have hres : ∀ l : G ⟶ (totalMorphism a).pushforward.obj F,
      restrictForkTranspose a F (SimplexCategory.mk 0)
          (l ≫ restrictForkLeg a F (SimplexCategory.mk 0)) =
        ((situation C).restrict (SimplexCategory.mk 0)).map
          (((totalMorphism a).adj.homEquiv G F).symm l) := fun l =>
    restrictForkTranspose_comp_restrictForkLeg a F (SimplexCategory.mk 0) l
  have hfac : (totalMorphism a).adj.homEquiv G F σ ≫
      restrictForkLeg a F (SimplexCategory.mk 0) = x := by
    refine restrictForkTranspose_injective a F G (SimplexCategory.mk 0) ?_
    rw [hres, Equiv.symm_apply_apply, hσ]
  have huniq : ∀ l : G ⟶ (totalMorphism a).pushforward.obj F,
      l ≫ restrictForkLeg a F (SimplexCategory.mk 0) = x →
        l = (totalMorphism a).adj.homEquiv G F σ := by
    intro l hl
    refine ((totalMorphism a).adj.homEquiv G F).symm.injective ?_
    rw [Equiv.symm_apply_apply]
    exact hσuniq _ ((hres l).symm.trans
      (congrArg (restrictForkTranspose a F (SimplexCategory.mk 0)) hl))
  exact ⟨_, hfac, huniq⟩

/-- **The universal property of the fork of Stacks 0D70 (3).** Every map from a sheaf on the
augmentation site into the direct image of the degree-zero component augmentation which equalises
the two vertex transitions factors uniquely through the total direct image. -/
theorem totalForkLeg_existsUnique (a : C.Augmentation D K)
    (F : Sheaf (situation C).totalTopology (Type u)) (G : Sheaf K (Type u))
    (x : G ⟶ (componentAug a (SimplexCategory.mk 0)).pushforward.obj
      ((SimplicialSiteSituation.componentMorphism (situation C)
        (SimplexCategory.mk 0)).inverseImage.obj F))
    (hx : x ≫ totalForkTransition a F
          (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 0) =
        x ≫ totalForkTransition a F
          (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 1)) :
    ∃! l : G ⟶ (totalMorphism a).pushforward.obj F,
      l ≫ totalForkLeg a F (SimplexCategory.mk 0) = x := by
  have hmap : ∀ i : Fin 2,
      (restrictForkIso a F (SimplexCategory.mk 0)).hom ≫ totalForkTransition a F
          (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) i) =
        restrictForkMap a F
            (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) i) ≫
          (restrictForkIso a F (SimplexCategory.mk 1)).hom := fun i =>
    restrictForkIso_comp_totalForkTransition a F _
  have hx' : (x ≫ (restrictForkIso a F (SimplexCategory.mk 0)).inv) ≫ restrictForkMap a F
        (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 0) =
      (x ≫ (restrictForkIso a F (SimplexCategory.mk 0)).inv) ≫ restrictForkMap a F
        (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 1) := by
    rw [← cancel_mono (restrictForkIso a F (SimplexCategory.mk 1)).hom]
    simp only [Category.assoc, ← hmap 0, ← hmap 1, Iso.inv_hom_id_assoc]
    exact hx
  obtain ⟨l, hl, huniq⟩ := restrictFork_existsUnique a F G
    (x ≫ (restrictForkIso a F (SimplexCategory.mk 0)).inv) hx'
  have hfac : l ≫ totalForkLeg a F (SimplexCategory.mk 0) = x := by
    rw [totalForkLeg_eq, ← Category.assoc, hl]
    simp
  refine ⟨l, hfac, fun l' hl' => ?_⟩
  have hl'' : l' ≫ totalForkLeg a F (SimplexCategory.mk 0) = x := hl'
  refine huniq l' ?_
  rw [← hl'', totalForkLeg_eq]
  simp

/-- **Stacks 0D70 (3).** The fork of the total direct image over the two transitions of the direct
images of the components attached to the two maps `[0] ⟶ [1]`. -/
def totalDirectImageFork (a : C.Augmentation D K)
    (F : Sheaf (situation C).totalTopology (Type u)) :
    Fork (vertexDirectImageMap a F 0) (vertexDirectImageMap a F 1) :=
  Fork.ofι (totalComponentUnitMap a F (SimplexCategory.mk 0))
    ((coneLaw a F (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 0)).trans
      (coneLaw a F
        (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 1)).symm)

/-- **Stacks 0D70 (3).** The total direct image *is* the equalizer of the two transitions of the
direct images of the components attached to the two maps `[0] ⟶ [1]`: the fork built from the
degree-zero leg is a limit. -/
def totalDirectImageForkIsLimit (a : C.Augmentation D K)
    (F : Sheaf (situation C).totalTopology (Type u)) :
    IsLimit (totalDirectImageFork a F) :=
  Fork.IsLimit.mk _
    (fun s => (totalForkLeg_existsUnique a F s.pt s.ι (Fork.condition s)).choose)
    (fun s => (totalForkLeg_existsUnique a F s.pt s.ι (Fork.condition s)).choose_spec.1)
    (fun s m hm =>
      (totalForkLeg_existsUnique a F s.pt s.ι (Fork.condition s)).choose_spec.2 m hm)

end Augmentation

end CocontinuousSimplicialSite

end CategoryTheory

end
