module

public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.TopologicalComparison
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi
public import StacksFrontier.Topology.Simplicial.ComponentSite

/-!
# The morphism of topoi associated to an augmented simplicial space

An augmentation of a simplicial topological space gives a morphism from the topos of
sheaves on its simplicial site to the topos of sheaves on the target. Its inverse image
is computed degreewise, and its direct image is the equalizer of the two degree-one
transition maps applied to the direct image in degree zero.

## Main definitions

* `Stacks.Topology.Simplicial.AugmentationMorphismData`: the morphism together with its
  coherent component identifications.
* `Stacks.Topology.Simplicial.augmentationMorphism`: the canonical morphism of topoi.
* `Stacks.Topology.Simplicial.augmentationPullbackTransition`: the canonical map between
  component pullbacks.
* `Stacks.Topology.Simplicial.augmentationFaceMap`: the map of direct images induced by a vertex
  of the one-simplex.
* `Stacks.Topology.Simplicial.componentSheaf`: the component of a sheaf on the simplicial site in
  one simplicial degree.

## Main results

* `Stacks.Topology.Simplicial.augmentationMorphism_inverseImage_component`: inverse images are
  computed degreewise.
* `Stacks.Topology.Simplicial.augmentationMorphism_inverseImage_transition`: a characterization
  of every transition map.
* `CategoryTheory.Limits.Cocone.w`: the compatibility of the augmentation maps.
* `Stacks.Topology.Simplicial.augmentationMorphism_comp_component`: a comparison of the
  composite morphism on a component.
* `Stacks.Topology.Simplicial.augmentationMorphism_pushforwardEqualizer`: direct images are
  computed as an equalizer.

## Implementation notes

The two equalizer arrows are the maps induced by the two simplex maps from degree one to
degree zero. The component composite is expressed by a natural isomorphism of inverse-image
functors; the second functor is the inverse image of the component morphism from Tag 09W0.
The degreewise description uses the sheaf-system equivalence of Tag 09VM.
The component identifications and their transition compatibility are part of the same
construction. The canonical transition is the adjoint of the pullback unit, transported
along the augmentation equation; this is the pullback comparison used in the source proof.
Part (2) is the cocone naturality equation, so we register Mathlib's general
`CategoryTheory.Limits.Cocone.w` rather than restating it for topological spaces.

## References

* [Stacks Project, Tag 09W4](https://stacks.math.columbia.edu/tag/09W4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Simplicial

universe u

namespace Stacks.Topology.Simplicial

add_to_stacks 09W4 "part (2): compatibility of augmentation maps"
  CategoryTheory.Limits.Cocone.w

variable (Y : SimplicialObject TopCat.{u}) (X : TopCat.{u})
  (a : Y ⟶ (SimplicialObject.const TopCat).obj X)

/-- The canonical `Y.map φ`-map between the pullbacks of a sheaf along the augmentation.
It is adjoint to the unit for `a.app n`, using `Y.map φ ≫ a.app m = a.app n`
to identify the composite pushforward. -/
noncomputable def augmentationPullbackTransition (F : TopCat.Sheaf (Type u) X)
    {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) :
    StacksFMap (Y.map φ)
      ((TopCat.Sheaf.pullback (Type u) (a.app n)).obj F).obj
      ((TopCat.Sheaf.pullback (Type u) (a.app m)).obj F).obj := by
  refine (StacksFMap.equivSheafHom _ _ _).symm ?_
  refine ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (a.app m)).homEquiv _ _).symm ?_
  refine (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (a.app n)).unit.app F ≫
    eqToHom ?_
  have h : Y.map φ ≫ a.app m = a.app n :=
    (show Cocone Y from { pt := X, ι := a }).w φ
  rw [← h]
  rfl

namespace Augmentation

/-- Sheaves of sets on a topological space. -/
abbrev sh (X : TopCat.{u}) := TopCat.Sheaf (Type u) X

/-- Inverse image of sheaves of sets along a continuous map. -/
@[sga "4 IV 9.8.1"]
abbrev pb {X Z : TopCat.{u}} (f : X ⟶ Z) := TopCat.Sheaf.pullback (Type u) f

/-- Direct image of sheaves of sets along a continuous map. -/
@[sga "4 IV 4.1.1"]
abbrev pf {X Z : TopCat.{u}} (f : X ⟶ Z) := TopCat.Sheaf.pushforward (Type u) f

/-- The inverse-image/direct-image adjunction of a continuous map, on sheaves of sets. -/
abbrev adj {X Z : TopCat.{u}} (f : X ⟶ Z) :=
  TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f

/-- The canonical comparison from the pullback along `c` to the direct image along `f` of the
pullback along `b`, for a triangle `f ≫ c = b`. It is the adjoint of the unit for `b`. -/
def pullTransition {B C Z : TopCat.{u}}
    (f : B ⟶ C) (b : B ⟶ Z) (c : C ⟶ Z) (h : f ≫ c = b) (F : sh Z) :
    (pb c).obj F ⟶ (pf f).obj ((pb b).obj F) :=
  ((adj c).homEquiv _ _).symm ((adj b).unit.app F ≫ eqToHom (by rw [← h]; rfl))

/-- `pullTransition` is the map whose adjoint is the unit for the lower leg of the triangle. -/
lemma pullTransition_unit {B C Z : TopCat.{u}}
    (f : B ⟶ C) (b : B ⟶ Z) (c : C ⟶ Z) (h : f ≫ c = b) (F : sh Z) :
    (adj c).unit.app F ≫ (pf c).map (pullTransition f b c h F) =
      (adj b).unit.app F ≫ eqToHom (by rw [← h]; rfl) :=
  ((adj c).homEquiv _ _).apply_symm_apply _

/-- The comparison along an identity is the identity. -/
lemma pullTransition_id {B Z : TopCat.{u}}
    (b : B ⟶ Z) (F : sh Z) :
    pullTransition (𝟙 B) b b (Category.id_comp _) F =
      eqToHom (show (pb b).obj F = (pf (𝟙 B)).obj ((pb b).obj F) from rfl) := by
  apply ((adj b).homEquiv _ _).injective
  show ((adj b).homEquiv _ _) (((adj b).homEquiv _ _).symm
    ((adj b).unit.app F ≫ 𝟙 _)) = (adj b).unit.app F ≫ (pf b).map (𝟙 _)
  simp [Adjunction.homEquiv_id]

/-- The comparisons along two composable triangles compose to the comparison along the
composite. -/
lemma pullTransition_comp {B C D Z : TopCat.{u}}
    (f : B ⟶ C) (g : C ⟶ D) (b : B ⟶ Z) (c : C ⟶ Z) (d : D ⟶ Z)
    (h : f ≫ c = b) (k : g ≫ d = c) (F : sh Z) :
    pullTransition g c d k F ≫ (pf g).map (pullTransition f b c h F) =
      pullTransition (f ≫ g) b d (by rw [Category.assoc, k, h]) F := by
  subst b
  subst c
  apply ((adj d).homEquiv _ _).injective
  show (adj d).unit.app F ≫ (pf d).map
    (pullTransition g (g ≫ d) d rfl F ≫
      (pf g).map (pullTransition f (f ≫ g ≫ d) (g ≫ d) rfl F)) =
    (adj d).unit.app F ≫ (pf d).map
      (pullTransition (f ≫ g) (f ≫ g ≫ d) d _ F)
  rw [Functor.map_comp]
  rw [← Category.assoc ((adj d).unit.app F), pullTransition_unit, pullTransition_unit]
  show ((adj (g ≫ d)).unit.app F ≫ 𝟙 _) ≫
      (pf (g ≫ d)).map (pullTransition f (f ≫ g ≫ d) (g ≫ d) rfl F) =
    (adj (f ≫ g ≫ d)).unit.app F ≫ 𝟙 _
  rw [Category.comp_id]
  exact pullTransition_unit f (f ≫ g ≫ d) (g ≫ d) rfl F

/-- The comparison is natural in the sheaf. -/
lemma pullTransition_naturality {B C Z : TopCat.{u}}
    (f : B ⟶ C) (b : B ⟶ Z) (c : C ⟶ Z) (h : f ≫ c = b)
    {F G : sh Z} (α : F ⟶ G) :
    (pb c).map α ≫ pullTransition f b c h G =
      pullTransition f b c h F ≫ (pf f).map ((pb b).map α) := by
  subst b
  apply ((adj c).homEquiv _ _).injective
  show (adj c).unit.app F ≫ (pf c).map ((pb c).map α ≫ _) =
    (adj c).unit.app F ≫ (pf c).map (_ ≫ _)
  have hn := (adj c).unit.naturality α
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  rw [Functor.map_comp, ← Category.assoc ((adj c).unit.app F), ← hn]
  rw [Category.assoc α, pullTransition_unit, Functor.map_comp,
    ← Category.assoc ((adj c).unit.app F),
    pullTransition_unit]
  show α ≫ ((adj (f ≫ c)).unit.app G ≫ 𝟙 _) =
    ((adj (f ≫ c)).unit.app F ≫ 𝟙 _) ≫ (pf (f ≫ c)).map ((pb (f ≫ c)).map α)
  simpa only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map,
    Category.comp_id] using (adj (f ≫ c)).unit.naturality α

/-- An augmentation of a simplicial space is a cocone, hence compatible with the simplex maps. -/
lemma augmentation_w {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) :
    Y.map φ ≫ a.app m = a.app n :=
  (show Cocone Y from { pt := X, ι := a }).w φ

/-- On sections, the comparison along a map that is the identity is the identity. -/
lemma pullTransition_id_app {B Z : TopCat.{u}}
    (f : B ⟶ B) (hf : f = 𝟙 B) (b : B ⟶ Z) (h : f ≫ b = b)
    (F : sh Z) (V : (Opens B)ᵒᵖ) :
    HEq ((pullTransition f b b h F).hom.app V) (𝟙 (((pb b).obj F).obj.obj V)) := by
  subst f
  rw [pullTransition_id]
  rfl

/-- On sections, the comparisons along two composable triangles compose. -/
lemma pullTransition_comp_app {B C D Z : TopCat.{u}}
    (f : B ⟶ C) (g : C ⟶ D) (fg : B ⟶ D) (hfg : fg = f ≫ g)
    (b : B ⟶ Z) (c : C ⟶ Z) (d : D ⟶ Z)
    (h : f ≫ c = b) (k : g ≫ d = c) (hk : fg ≫ d = b)
    (F : sh Z) (V : (Opens D)ᵒᵖ) :
    HEq ((pullTransition g c d k F ≫ (pf g).map (pullTransition f b c h F)).hom.app V)
      ((pullTransition fg b d hk F).hom.app V) := by
  subst fg
  rw [pullTransition_comp]
  exact HEq.rfl

/-- The system of degreewise pullbacks of a sheaf along an augmentation, with the canonical
comparisons as its transition maps. -/
def pullbackSystem (F : sh X) : SimplicialSheafSystem Y (Type u) where
  component n := (pb (a.app n)).obj F
  transition φ := augmentationPullbackTransition Y X a F φ
  transition_id n V :=
    pullTransition_id_app (Y.map (𝟙 n)) (Y.map_id n) (a.app n)
      (augmentation_w Y X a _) F V
  transition_comp φ ψ V :=
    pullTransition_comp_app (Y.map φ) (Y.map ψ) (Y.map (φ ≫ ψ)) (Y.map_comp φ ψ)
      _ _ _ (augmentation_w Y X a _) (augmentation_w Y X a _)
      (augmentation_w Y X a _) F V

/-- `pullbackSystem`, as a functor from sheaves on the augmentation target. -/
def pullbackSystemFunctor : sh X ⥤ SimplicialSheafSystem Y (Type u) where
  obj := pullbackSystem Y X a
  map α :=
    { componentHom := fun n => (pb (a.app n)).map α
      naturality := by
        intro n m φ V
        exact congrArg (fun t => t.hom.app V)
          (pullTransition_naturality (Y.map φ) (a.app n) (a.app m)
            (augmentation_w Y X a φ) α).symm }
  map_id F := by
    apply SimplicialSheafSystem.Hom.ext
    intro n
    exact (pb (a.app n)).map_id F
  map_comp α β := by
    apply SimplicialSheafSystem.Hom.ext
    intro n
    exact (pb (a.app n)).map_comp α β

/-- A map of direct images: given a triangle `f ≫ c = b` and an `f`-map `t`, the induced map from
the direct image along `c` to the direct image along `b`. -/
def pushTransition {B C Z : TopCat.{u}}
    (f : B ⟶ C) (b : B ⟶ Z) (c : C ⟶ Z) (h : f ≫ c = b)
    {F : sh B} {G : sh C} (t : G ⟶ (pf f).obj F) :
    (pf c).obj G ⟶ (pf b).obj F := by
  rw [← h]
  exact (pf c).map t

/-- The direct-image map attached to an identity triangle and the identity `f`-map is the
identity. -/
lemma pushTransition_id {B Z : TopCat.{u}}
    (b : B ⟶ Z) (F : sh B) :
    pushTransition (𝟙 B) b b (Category.id_comp _)
        (eqToHom (show F = (pf (𝟙 B)).obj F from rfl)) =
      𝟙 ((pf b).obj F) := by
  show (pf b).map (𝟙 F) ≫ 𝟙 _ = _
  simp

/-- The direct-image maps attached to two composable triangles compose. -/
lemma pushTransition_comp {B C D Z : TopCat.{u}}
    (f : B ⟶ C) (g : C ⟶ D) (b : B ⟶ Z) (c : C ⟶ Z) (d : D ⟶ Z)
    (h : f ≫ c = b) (k : g ≫ d = c)
    {F : sh B} {G : sh C} {H : sh D}
    (t : G ⟶ (pf f).obj F) (s : H ⟶ (pf g).obj G) :
    pushTransition g c d k s ≫ pushTransition f b c h t =
      pushTransition (f ≫ g) b d (by rw [Category.assoc, k, h]) (s ≫ (pf g).map t) := by
  subst b
  subst c
  show ((pf d).map s ≫ 𝟙 _) ≫ ((pf (g ≫ d)).map t ≫ 𝟙 _) =
    (pf d).map (s ≫ (pf g).map t) ≫ 𝟙 _
  simp only [Category.comp_id, Functor.map_comp]
  rfl

/-- The mate correspondence: a square for `pullTransition` is equivalent to a square for
`pushTransition` under the adjunctions. -/
lemma mate_transition_iff {B C Z : TopCat.{u}}
    (f : B ⟶ C) (b : B ⟶ Z) (c : C ⟶ Z) (h : f ≫ c = b)
    {F : sh Z} {G : sh B} {H : sh C}
    (t : H ⟶ (pf f).obj G) (α : (pb b).obj F ⟶ G) (β : (pb c).obj F ⟶ H) :
    pullTransition f b c h F ≫ (pf f).map α = β ≫ t ↔
      ((adj c).homEquiv _ _) β ≫ pushTransition f b c h t =
        ((adj b).homEquiv _ _) α := by
  subst b
  rw [← Equiv.apply_eq_iff_eq ((adj c).homEquiv F ((pf f).obj G))]
  show ((adj c).unit.app F ≫ (pf c).map (pullTransition f (f ≫ c) c rfl F ≫
      (pf f).map α) = (adj c).unit.app F ≫ (pf c).map (β ≫ t)) ↔ _
  simp only [Functor.map_comp]
  rw [← Category.assoc ((adj c).unit.app F), pullTransition_unit]
  show (((adj (f ≫ c)).unit.app F ≫ 𝟙 _) ≫ (pf (f ≫ c)).map α =
    (adj c).unit.app F ≫ (pf c).map β ≫ (pf c).map t) ↔
    ((adj c).unit.app F ≫ (pf c).map β) ≫ ((pf c).map t ≫ 𝟙 _) =
      (adj (f ≫ c)).unit.app F ≫ (pf (f ≫ c)).map α
  simp only [Category.comp_id, Category.assoc]
  exact eq_comm

/-- A direct-image map attached to an identity triangle is the identity as soon as its `f`-map is
sectionwise the identity. -/
lemma pushTransition_id_of_app {B Z : TopCat.{u}}
    (f : B ⟶ B) (hf : f = 𝟙 B) (b : B ⟶ Z) (h : f ≫ b = b)
    {F : sh B} (t : F ⟶ (pf f).obj F)
    (ht : ∀ V, HEq (t.hom.app V) (𝟙 (F.obj.obj V))) :
    pushTransition f b b h t = 𝟙 _ := by
  subst f
  have ht' : t = eqToHom (show F = (pf (𝟙 B)).obj F from rfl) := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    exact eq_of_heq (ht V)
  rw [ht', pushTransition_id]

/-- Composition of direct-image maps, with the composite `f`-map identified sectionwise. -/
lemma pushTransition_comp_of_app {B C D Z : TopCat.{u}}
    (f : B ⟶ C) (g : C ⟶ D) (fg : B ⟶ D) (hfg : fg = f ≫ g)
    (b : B ⟶ Z) (c : C ⟶ Z) (d : D ⟶ Z)
    (h : f ≫ c = b) (k : g ≫ d = c) (hk : fg ≫ d = b)
    {F : sh B} {G : sh C} {H : sh D}
    (t : G ⟶ (pf f).obj F) (s : H ⟶ (pf g).obj G) (r : H ⟶ (pf fg).obj F)
    (hr : ∀ V, HEq ((s ≫ (pf g).map t).hom.app V) (r.hom.app V)) :
    pushTransition g c d k s ≫ pushTransition f b c h t = pushTransition fg b d hk r := by
  subst fg
  have hr' : s ≫ (pf g).map t = r := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    exact eq_of_heq (hr V)
  cases hr'
  exact pushTransition_comp f g b c d h k t s

/-- The transition map of a simplicial sheaf system, read as a morphism to a direct image. -/
def systemTransition (S : SimplicialSheafSystem Y (Type u))
    {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) :
    S.component m ⟶ (pf (Y.map φ)).obj (S.component n) :=
  (StacksFMap.equivSheafHom _ _ _) (S.transition φ)

/-- The cosimplicial diagram of direct images of the components of a simplicial sheaf system. -/
def pushforwardDiagram (S : SimplicialSheafSystem Y (Type u)) :
    SimplexCategory ⥤ sh X where
  obj n := (pf (a.app (op n))).obj (S.component (op n))
  map φ := pushTransition (Y.map φ.op) (a.app _) (a.app _)
    (augmentation_w Y X a _) (systemTransition Y S φ.op)
  map_id n := pushTransition_id_of_app (Y.map (𝟙 (op n))) (Y.map_id _)
    _ (augmentation_w Y X a _) _ (S.transition_id _)
  map_comp φ ψ := (pushTransition_comp_of_app (Y.map ψ.op) (Y.map φ.op)
    (Y.map (ψ.op ≫ φ.op)) (Y.map_comp _ _) _ _ _
    (augmentation_w Y X a _) (augmentation_w Y X a _) (augmentation_w Y X a _)
    (systemTransition Y S ψ.op) (systemTransition Y S φ.op)
    (systemTransition Y S (ψ.op ≫ φ.op)) (S.transition_comp ψ.op φ.op)).symm

/-- Naturality of the direct-image maps in the two sheaves and their `f`-maps. -/
lemma pushTransition_naturality {B C Z : TopCat.{u}}
    (f : B ⟶ C) (b : B ⟶ Z) (c : C ⟶ Z) (h : f ≫ c = b)
    {F F' : sh B} {G G' : sh C} (α : F ⟶ F') (β : G ⟶ G')
    (t : G ⟶ (pf f).obj F) (t' : G' ⟶ (pf f).obj F')
    (ht : t ≫ (pf f).map α = β ≫ t') :
    (pf c).map β ≫ pushTransition f b c h t' =
      pushTransition f b c h t ≫ (pf b).map α := by
  subst b
  show (pf c).map β ≫ ((pf c).map t' ≫ 𝟙 _) =
    ((pf c).map t ≫ 𝟙 _) ≫ (pf (f ≫ c)).map α
  simp only [Category.comp_id]
  show (pf c).map β ≫ (pf c).map t' = (pf c).map t ≫ (pf c).map ((pf f).map α)
  rw [← Functor.map_comp, ← Functor.map_comp, ht]

/-- `pushforwardDiagram`, as a functor on simplicial sheaf systems. -/
def pushforwardDiagramFunctor : SimplicialSheafSystem Y (Type u) ⥤
    (SimplexCategory ⥤ sh X) where
  obj := pushforwardDiagram Y X a
  map α :=
    { app := fun n => (pf (a.app (op n))).map (α.componentHom (op n))
      naturality := by
        intro n m φ
        symm
        apply pushTransition_naturality (Y.map φ.op) _ _ (augmentation_w Y X a _)
        apply Sheaf.hom_ext
        apply NatTrans.ext
        funext V
        exact α.naturality φ.op V }
  map_id S := by
    ext n : 1
    exact (pf (a.app (op n))).map_id _
  map_comp α β := by
    ext n : 1
    exact (pf (a.app (op n))).map_comp _ _

/-- Morphisms out of the pullback system correspond to cones over the cosimplicial diagram of
direct images. -/
def systemConeEquiv (F : sh X) (S : SimplicialSheafSystem Y (Type u)) :
    ((pullbackSystemFunctor Y X a).obj F ⟶ S) ≃
      ((Functor.const SimplexCategory).obj F ⟶ pushforwardDiagram Y X a S) where
  toFun α :=
    { app := fun n => ((adj (a.app (op n))).homEquiv _ _) (α.componentHom (op n))
      naturality := by
        intro n m φ
        have h : pullTransition (Y.map φ.op) (a.app (op m)) (a.app (op n))
            (augmentation_w Y X a _) F ≫ (pf (Y.map φ.op)).map (α.componentHom (op m)) =
            α.componentHom (op n) ≫ systemTransition Y S φ.op := by
          apply Sheaf.hom_ext
          apply NatTrans.ext
          funext V
          exact α.naturality φ.op V
        simpa only [pushforwardDiagram, Functor.const_obj_obj, Functor.const_obj_map,
          Category.id_comp] using ((mate_transition_iff _ _ _ _ _ _ _).mp h).symm }
  invFun β :=
    { componentHom := fun n => ((adj (a.app n)).homEquiv _ _).symm (β.app n.unop)
      naturality := by
        intro n m φ V
        have h : ((adj (a.app m)).homEquiv _ _)
            (((adj (a.app m)).homEquiv _ _).symm (β.app m.unop)) ≫
            pushTransition (Y.map φ) (a.app n) (a.app m) (augmentation_w Y X a _)
              (systemTransition Y S φ) =
            ((adj (a.app n)).homEquiv _ _)
              (((adj (a.app n)).homEquiv _ _).symm (β.app n.unop)) := by
          simpa only [pushforwardDiagram, Functor.const_obj_obj, Functor.const_obj_map,
            Category.id_comp,
            Quiver.Hom.op_unop, Opposite.op_unop, Equiv.apply_symm_apply] using
              (β.naturality φ.unop).symm
        exact congrArg (fun t => t.hom.app V) ((mate_transition_iff _ _ _ _ _ _ _).mpr h) }
  left_inv α := by
    apply SimplicialSheafSystem.Hom.ext
    intro n
    exact ((adj (a.app n)).homEquiv _ _).symm_apply_apply _
  right_inv β := by
    ext n : 1
    exact ((adj (a.app (op n))).homEquiv _ _).apply_symm_apply _

/-- `systemConeEquiv` is natural in the target system. -/
lemma systemConeEquiv_comp {F : sh X} {S T : SimplicialSheafSystem Y (Type u)}
    (α : (pullbackSystemFunctor Y X a).obj F ⟶ S) (β : S ⟶ T) :
    systemConeEquiv Y X a F T (α ≫ β) = systemConeEquiv Y X a F S α ≫
      (pushforwardDiagramFunctor Y X a).map β := by
  ext n : 1
  exact (adj (a.app (op n))).homEquiv_naturality_right _ _

/-- `systemConeEquiv` is natural in the source sheaf. -/
lemma systemConeEquiv_map_comp {F G : sh X} {S : SimplicialSheafSystem Y (Type u)}
    (f : F ⟶ G) (α : (pullbackSystemFunctor Y X a).obj G ⟶ S) :
    systemConeEquiv Y X a F S ((pullbackSystemFunctor Y X a).map f ≫ α) =
      (Functor.const SimplexCategory).map f ≫ systemConeEquiv Y X a G S α := by
  ext n : 1
  exact (adj (a.app (op n))).homEquiv_naturality_left _ _

/-- The pullback system is left adjoint to the limit of the cosimplicial diagram of direct
images. -/
def systemAdjunction : pullbackSystemFunctor Y X a ⊣
    pushforwardDiagramFunctor Y X a ⋙ lim :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun F S => (systemConeEquiv Y X a F S).trans (constLimAdj.homEquiv _ _)
      homEquiv_naturality_left_symm := by
        intro F G S f α
        apply (systemConeEquiv Y X a F S).injective
        change systemConeEquiv Y X a F S
          ((systemConeEquiv Y X a F S).symm ((constLimAdj.homEquiv _ _).symm (f ≫ α))) =
          systemConeEquiv Y X a F S ((pullbackSystemFunctor Y X a).map f ≫
            (systemConeEquiv Y X a G S).symm ((constLimAdj.homEquiv _ _).symm α))
        rw [Equiv.apply_symm_apply, systemConeEquiv_map_comp, Equiv.apply_symm_apply]
        exact constLimAdj.homEquiv_naturality_left_symm f α
      homEquiv_naturality_right := by
        intro F S T α β
        change (constLimAdj.homEquiv _ _) (systemConeEquiv Y X a F T (α ≫ β)) =
          (constLimAdj.homEquiv _ _) (systemConeEquiv Y X a F S α) ≫
            (pushforwardDiagramFunctor Y X a ⋙ lim).map β
        rw [systemConeEquiv_comp]
        exact constLimAdj.homEquiv_naturality_right _ _ }

/-- The sheaf-system description of sheaves on the simplicial site of `Y`. -/
abbrev presentation := sheafEquivalenceSimplicialSheafSystem Y (Type u)

/-- The inverse image of the augmentation morphism of topoi: the pullback system, transported
through the sheaf-system equivalence. -/
def inverseImageFunctor :
    sh X ⥤ Sheaf (SimplicialOpen.grothendieckTopology Y) (Type u) :=
  pullbackSystemFunctor Y X a ⋙ (presentation Y).toEquivalence.inverse

/-- The components of the inverse image are the degreewise pullbacks along the augmentation. -/
def inverseImageComponentIso (n : SimplexCategoryᵒᵖ) :
    inverseImageFunctor Y X a ⋙ (presentation Y).toEquivalence.functor ⋙
      SimplicialSheafSystem.componentFunctor Y (Type u) n ≅ pb (a.app n) :=
  NatIso.ofComponents
    (fun F => (SimplicialSheafSystem.componentFunctor Y (Type u) n).mapIso
      ((presentation Y).toEquivalence.counitIso.app ((pullbackSystemFunctor Y X a).obj F)))
    (by
      intro F G α
      exact congrArg (fun t => t.componentHom n)
        ((presentation Y).toEquivalence.counitIso.hom.naturality
          ((pullbackSystemFunctor Y X a).map α)))

/-- The presheaf underlying the inverse image is the one reconstructed from the pullback system. -/
def inverseImagePresheafIso :
    inverseImageFunctor Y X a ⋙
        sheafToPresheaf (SimplicialOpen.grothendieckTopology Y) (Type u) ≅
      pullbackSystemFunctor Y X a ⋙ (presentation Y).toPresheaf :=
  Functor.isoWhiskerLeft (pullbackSystemFunctor Y X a)
    (Functor.isoWhiskerLeft (presentation Y).toEquivalence.inverse
      (presentation Y).underlyingPresheafIso.symm ≪≫
      Functor.isoWhiskerRight (presentation Y).toEquivalence.counitIso
        (presentation Y).toPresheaf ≪≫ (presentation Y).toPresheaf.leftUnitor)

/-- The inverse image is left exact, since it is so degreewise and limits of sheaves on the
simplicial site are computed degreewise. -/
lemma inverseImage_preservesFiniteLimits :
    PreservesFiniteLimits (inverseImageFunctor Y X a) := by
  let E := presentation Y
  let L := inverseImageFunctor Y X a
  let Q := sheafToPresheaf (SimplicialOpen.grothendieckTopology Y) (Type u)
  have : PreservesFiniteLimits (L ⋙ Q) := by
    apply preservesFiniteLimits_of_evaluation
    intro U
    let n := U.unop.degree
    let V := op U.unop.toOpens
    let ev := (evaluation (Opens (Y.obj n))ᵒᵖ (Type u)).obj V
    let e : (L ⋙ Q) ⋙ (evaluation (SimplicialOpen Y)ᵒᵖ (Type u)).obj U ≅
        pb (a.app n) ⋙ TopCat.Sheaf.forget (Type u) (Y.obj n) ⋙ ev :=
      Functor.isoWhiskerRight (inverseImagePresheafIso Y X a) _ ≪≫
        Functor.isoWhiskerLeft (pullbackSystemFunctor Y X a)
          (Functor.isoWhiskerRight (E.componentIso n) ev)
    have : PreservesFiniteLimits (pb (a.app n)) :=
      (StacksZariskiSite.isMorphismOfSites_opensMap (a.app n)).preservesFiniteLimits
    have : PreservesLimits (TopCat.Sheaf.forget (Type u) (Y.obj n)) := by
      show PreservesLimits (sheafToPresheaf (Opens.grothendieckTopology (Y.obj n)) (Type u))
      infer_instance
    have : PreservesFiniteLimits ev := by
      dsimp only [ev]
      infer_instance
    have : PreservesFiniteLimits (TopCat.Sheaf.forget (Type u) (Y.obj n)) := inferInstance
    have : PreservesFiniteLimits (TopCat.Sheaf.forget (Type u) (Y.obj n) ⋙ ev) :=
      comp_preservesFiniteLimits _ _
    have : PreservesFiniteLimits
        (pb (a.app n) ⋙ TopCat.Sheaf.forget (Type u) (Y.obj n) ⋙ ev) :=
      comp_preservesFiniteLimits _ _
    exact preservesFiniteLimits_of_natIso e.symm
  exact preservesFiniteLimits_of_reflects_of_preserves L Q

/-- In a cosimplicial object, a map out of degree zero that is equalized by the two vertices of the
one-simplex is equalized by all vertices of every simplex. -/
lemma cosimplicial_vertex_eq {C : Type*} [Category C]
    (D : SimplexCategory ⥤ C) {T : C} (e : T ⟶ D.obj ⦋0⦌)
    (h : e ≫ D.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0) =
      e ≫ D.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1))
    (n : SimplexCategory) (i : Fin (n.len + 1)) :
    e ≫ D.map (SimplexCategory.const ⦋0⦌ n 0) =
      e ≫ D.map (SimplexCategory.const ⦋0⦌ n i) := by
  let edge := SimplexCategory.mkOfLe 0 i (Fin.zero_le i)
  have := congrArg (fun t => t ≫ D.map edge) h
  simp only [Category.assoc, ← D.map_comp, SimplexCategory.const_comp] at this
  exact this

/-- The cone over a cosimplicial object with vertex the equalizer of the two maps induced by the
vertices of the one-simplex. -/
def cosimplicialEqualizerCone {C : Type*} [Category C] [HasEqualizers C]
    (D : SimplexCategory ⥤ C) : Cone D where
  pt := equalizer (D.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0))
    (D.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1))
  π :=
    { app := fun n => equalizer.ι _ _ ≫ D.map (SimplexCategory.const ⦋0⦌ n 0)
      naturality := by
        intro n m φ
        dsimp only [Functor.const_obj_map, Functor.const_obj_obj]
        rw [Category.id_comp, Category.assoc, ← D.map_comp, SimplexCategory.const_comp]
        exact cosimplicial_vertex_eq D _ (equalizer.condition _ _) m (φ.toOrderHom 0) }

/-- The degree-zero leg of `cosimplicialEqualizerCone` is the equalizer inclusion. -/
lemma cosimplicialEqualizerCone_pi_zero {C : Type*} [Category C] [HasEqualizers C]
    (D : SimplexCategory ⥤ C) :
    (cosimplicialEqualizerCone D).π.app ⦋0⦌ =
      equalizer.ι (D.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0))
        (D.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1)) := by
  show equalizer.ι _ _ ≫ D.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0) = _
  rw [SimplexCategory.const_eq_id, D.map_id, Category.comp_id]

/-- `cosimplicialEqualizerCone` is a limit cone. -/
def cosimplicialEqualizerCone_isLimit {C : Type*} [Category C] [HasEqualizers C]
    (D : SimplexCategory ⥤ C) : IsLimit (cosimplicialEqualizerCone D) where
  lift s := equalizer.lift (s.π.app ⦋0⦌) (by
    rw [s.w (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0), s.w (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1)])
  fac s n := by
    change equalizer.lift _ _ ≫ (equalizer.ι _ _ ≫ _) = _
    rw [equalizer.lift_ι_assoc]
    exact s.w (SimplexCategory.const ⦋0⦌ n 0)
  uniq s f hf := by
    apply equalizer.hom_ext
    rw [equalizer.lift_ι, ← cosimplicialEqualizerCone_pi_zero D]
    exact hf ⦋0⦌

/-- The limit of a cosimplicial object is the equalizer of the two maps induced by the vertices of
the one-simplex. -/
def cosimplicialLimitIsoEqualizer {C : Type*} [Category C] [HasEqualizers C]
    (D : SimplexCategory ⥤ C) [HasLimit D] :
    limit D ≅ equalizer (D.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0))
      (D.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1)) :=
  (limit.isLimit D).conePointUniqueUpToIso (cosimplicialEqualizerCone_isLimit D)

end Augmentation

open Augmentation

/-- The canonical geometric morphism together with the coherent degreewise
identification of its inverse image. The transition field records the construction
in the proof of Tag 09W4, not just separate isomorphisms in each degree. -/
structure AugmentationMorphismData extends
    MorphismOfTopoi
      (Sheaf (SimplicialOpen.grothendieckTopology Y) (Type u))
      (TopCat.Sheaf (Type u) X) where
  /-- Inverse image restricts to pullback by the augmentation in each degree. -/
  inverseImageComponent (n : SimplexCategoryᵒᵖ) :
    inverseImage ⋙
      (sheafEquivalenceSimplicialSheafSystem Y (Type u)).toEquivalence.functor ⋙
        SimplicialSheafSystem.componentFunctor Y (Type u) n ≅
      TopCat.Sheaf.pullback (Type u) (a.app n)
  /-- These identifications intertwine transitions with the canonical pullback maps. -/
  inverseImage_transition (F : TopCat.Sheaf (Type u) X)
      {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) (V : (Opens (Y.obj m))ᵒᵖ) :
    let S := (sheafEquivalenceSimplicialSheafSystem Y (Type u)).toEquivalence.functor.obj
      (inverseImage.obj F)
    (S.transition φ).app V ≫
        ((TopCat.Sheaf.forget (Type u) (Y.obj n)).map
          ((inverseImageComponent n).app F).hom).app
            (op ((Opens.map (Y.map φ)).obj V.unop)) =
      ((TopCat.Sheaf.forget (Type u) (Y.obj m)).map
        ((inverseImageComponent m).app F).hom).app V ≫
          (augmentationPullbackTransition Y X a F φ).app V

/-- The morphism from the topos of a simplicial space to that of its augmentation target,
with the coherent component identifications from the construction in the source proof. -/
@[stacks 09W4 "the canonical morphism of topoi"]
noncomputable def augmentationMorphism
    (a : Y ⟶ (SimplicialObject.const TopCat).obj X) :
    AugmentationMorphismData Y X a := by
  refine
    { pushforward := (presentation Y).toEquivalence.functor ⋙
        pushforwardDiagramFunctor Y X a ⋙ lim
      inverseImage := inverseImageFunctor Y X a
      adj := (systemAdjunction Y X a).comp (presentation Y).toEquivalence.symm.toAdjunction
      preservesFiniteLimits := inverseImage_preservesFiniteLimits Y X a
      inverseImageComponent := inverseImageComponentIso Y X a
      inverseImage_transition := ?_ }
  intro F n m φ V
  exact ((presentation Y).toEquivalence.counitIso.hom.app
    ((pullbackSystemFunctor Y X a).obj F)).naturality φ V

/-- The component of a sheaf on the simplicial site in one simplicial degree. -/
abbrev componentSheaf
    (G : Sheaf (SimplicialOpen.grothendieckTopology Y) (Type u))
    (n : SimplexCategoryᵒᵖ) : TopCat.Sheaf (Type u) (Y.obj n) :=
  ((sheafEquivalenceSimplicialSheafSystem Y (Type u)).toEquivalence.functor.obj G).component n

/-- **Stacks 09W4 (1).** Inverse image along the augmentation restricts in degree `n`
to inverse image along the component map `a_n`. -/
@[stacks 09W4 "part (1): inverse image on components"]
noncomputable def augmentationMorphism_inverseImage_component
    (n : SimplexCategoryᵒᵖ) :
    (augmentationMorphism Y X a).inverseImage ⋙
      (sheafEquivalenceSimplicialSheafSystem Y (Type u)).toEquivalence.functor ⋙
        SimplicialSheafSystem.componentFunctor Y (Type u) n ≅
      TopCat.Sheaf.pullback (Type u) (a.app n) :=
  (augmentationMorphism Y X a).inverseImageComponent n

/-- The inverse-image component isomorphisms intertwine every system transition with
the canonical map between pullbacks induced by the augmentation equation. -/
@[stacks 09W4 "part (1): compatibility of inverse-image transitions"]
theorem augmentationMorphism_inverseImage_transition (F : TopCat.Sheaf (Type u) X)
    {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) (V : (Opens (Y.obj m))ᵒᵖ) :
    let S := (sheafEquivalenceSimplicialSheafSystem Y (Type u)).toEquivalence.functor.obj
      ((augmentationMorphism Y X a).inverseImage.obj F)
    (S.transition φ).app V ≫
        ((TopCat.Sheaf.forget (Type u) (Y.obj n)).map
          ((augmentationMorphism_inverseImage_component Y X a n).app F).hom).app
            (op ((Opens.map (Y.map φ)).obj V.unop)) =
      ((TopCat.Sheaf.forget (Type u) (Y.obj m)).map
        ((augmentationMorphism_inverseImage_component Y X a m).app F).hom).app V ≫
          (augmentationPullbackTransition Y X a F φ).app V :=
  (augmentationMorphism Y X a).inverseImage_transition F φ V

/-- **Stacks 09W4 (3).** The composite of the component inclusion and the augmentation
agrees with the topological morphism induced by `a_n`. -/
@[stacks 09W4 "part (3): composition with a component inclusion"]
noncomputable def augmentationMorphism_comp_component (n : SimplexCategoryᵒᵖ) :
    (augmentationMorphism Y X a).inverseImage ⋙
      (levelFunctor Y n).sheafPullbackCocontinuous (Type u)
        (Opens.grothendieckTopology (Y.obj n))
        (SimplicialOpen.grothendieckTopology Y) ≅
      TopCat.Sheaf.pullback (Type u) (a.app n) :=
  Functor.isoWhiskerLeft (augmentationMorphism Y X a).inverseImage
      (inverseImageIsoComponent Y n.unop.len) ≪≫
    (augmentationMorphism Y X a).inverseImageComponent n

/-- The map on direct images induced by a vertex of the one-simplex and the transition
map of a sheaf on the simplicial site. -/
noncomputable def augmentationFaceMap
    (G : Sheaf (SimplicialOpen.grothendieckTopology Y) (Type u)) (i : Fin 2) :
    (TopCat.Sheaf.pushforward (Type u) (a.app (op ⦋0⦌))).obj
        (componentSheaf Y G (op ⦋0⦌)) ⟶
      (TopCat.Sheaf.pushforward (Type u) (a.app (op ⦋1⦌))).obj
        (componentSheaf Y G (op ⦋1⦌)) := by
  let φ : (op ⦋1⦌ : SimplexCategoryᵒᵖ) ⟶ op ⦋0⦌ :=
    (SimplexCategory.const ⦋0⦌ ⦋1⦌ i).op
  let S := (sheafEquivalenceSimplicialSheafSystem Y (Type u)).toEquivalence.functor.obj G
  let t := (StacksFMap.equivSheafHom (Y.map φ) (S.component (op ⦋1⦌))
    (S.component (op ⦋0⦌))).toFun (S.transition φ)
  have h : Y.map φ ≫ a.app (op ⦋0⦌) = a.app (op ⦋1⦌) :=
    (show Cocone Y from { pt := X, ι := a }).w φ
  rw [← h]
  exact (TopCat.Sheaf.pushforward (Type u) (a.app (op ⦋0⦌))).map t

/-- **Stacks 09W4 (4).** The direct image of a sheaf on the simplicial site is the
equalizer of the two degree-one transition maps on direct images. -/
@[stacks 09W4 "part (4): direct image as an equalizer"]
noncomputable def augmentationMorphism_pushforwardEqualizer
    (G : Sheaf (SimplicialOpen.grothendieckTopology Y) (Type u)) :
    (augmentationMorphism Y X a).pushforward.obj G ≅
      equalizer (augmentationFaceMap Y X a G 0) (augmentationFaceMap Y X a G 1) :=
  cosimplicialLimitIsoEqualizer
    (pushforwardDiagram Y X a ((presentation Y).toEquivalence.functor.obj G))

end Stacks.Topology.Simplicial

end
