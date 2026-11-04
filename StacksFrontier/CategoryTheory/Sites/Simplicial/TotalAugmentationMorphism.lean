module
import StacksCore.Tactic.StacksAttribute

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationPushforwardCocycle
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentSheafSumFormula
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ContinuousAugmentationSiteFunctors
public import StacksFrontier.CategoryTheory.Sites.Simplicial.Descent

/-!
# The augmentation of the total site of a simplicial-site situation

Let `S` be a simplicial-site situation and `a` an augmentation of `S` towards a site `(D, K)`.
Every simplicial degree `n` carries a morphism of topoi `a_n` from the sheaves on the component
of degree `n` to the sheaves on `(D, K)`, and those morphisms are coherently compatible with the
simplicial transitions. This file builds out of them a morphism of topoi `a` from the sheaves on
the total site to the sheaves on `(D, K)`.

Neither half of `a` is the image of a single site functor. Its inverse image is built from the
components: a sheaf `G` on the augmentation site goes to the sheaf on the total site whose
restriction to the component of degree `n` is `a_n^{-1} G` and whose transitions are the
canonical identifications, which is a sheaf on the total site because the sheaves on that site
are exactly such systems. Its direct image is a limit: the restrictions of a sheaf `F` on the
total site, pushed forward along the augmentations of the degrees, form a cosimplicial sheaf on
the augmentation site, and `a_* F` is its limit over the simplex category. The two are adjoint
because a morphism `a^{-1} G ⟶ F` is, degree by degree, a family of morphisms
`a_n^{-1} G ⟶ F_n` compatible with the transitions, hence by the adjunctions of the degrees a
cosimplicial morphism from the constant cosimplicial sheaf `G` into that cosimplicial sheaf,
hence a morphism `G ⟶ a_* F`. Finally `a^{-1}` is exact, because a sheaf on the total site is
evaluated at an object through its restriction to the degree of that object, where `a^{-1}` is
the exact functor `a_n^{-1}`.

The construction and all of its proofs are uniform in the two cases of the situation, and in
particular settle case (A), where the total category is the contravariant Grothendieck
construction and no cocontinuous functor out of it represents `a`.

## Main definitions

Unless stated otherwise, all names are in the namespace
`CategoryTheory.SimplicialSiteSituation.Augmentation`.

* `inverseImageSystem`: the system on the components attached to a sheaf on the augmentation site.
* `inverseImage`: the inverse image of the total augmentation.
* `cosimplicialPushforward`: the cosimplicial sheaf of direct images along the augmentations of the
  degrees.
* `pushforward`: the direct image of the total augmentation, the limit of that cosimplicial sheaf.
* `homEquiv` and `adjunction`: the hom-set bijection and the adjunction between them.
* `totalMorphismOfTopoi`: the resulting morphism of topoi.
* `CategoryTheory.SimplicialSite.ContinuousAugmentation.totalMorphismOfTopoi`: the same in
  case (A), with the total site of a simplicial site spelled as its own.

## Main results

* `transitionInverseImageIso_hom_app_id` and `transitionInverseImageIso_hom_app_comp`: the unit
  and cocycle laws which make the identifications of the inverse images a system.
* `restrictCompInverseImageIso`: **Stacks 0D70, compatibility (2)**, in inverse images: the
  inverse image of the total augmentation followed by restriction to a simplicial degree is the
  inverse image of the augmentation of that degree.
* `totalMorphismOfTopoi_componentMorphism_iso`: the same, phrased through the inverse image of the
  morphism of topoi of Stacks 09WG.
* `homEquiv_transitionInverseImageIso`: the identification of the inverse images of two degrees
  is the mate of the identification of their direct images, read on hom-sets.
* `homEquiv_componentPushforwardTransition_iff`: a family of morphisms out of the inverse images
  of the degrees is compatible with the transitions exactly when its transposes form a cone on the
  cosimplicial sheaf.
* `inverseImage_preservesFiniteLimits`: the inverse image of the total augmentation is exact.

## Implementation notes

The inverse image is not constructed as a functor into a category of systems and then
transported along the equivalence of Stacks 09WF: on objects it is the descent of a system, but
on morphisms it is assembled directly from the restrictions by
`CategoryTheory.SimplicialSiteSituation.totalHomOfFamily`, and its functoriality is then
`CategoryTheory.SimplicialSiteSituation.total_hom_ext`. That avoids building a modification of
lax transformations for every morphism of sheaves, and it is also what makes the component
identifications available as a natural isomorphism rather than only objectwise.

Compatibility of a family of morphisms with the transitions is needed in three different
shapes — for the restrictions of a sheaf on the total site, for the inverse images of the
degrees, and as a cone on the cosimplicial sheaf — and the two translations between them are
`restrictTransition_componentRestrictionIso_iff` and
`homEquiv_componentPushforwardTransition_iff`. Both are stated as iffs with the family as a
parameter.

The limit is taken over the whole simplex category rather than as the equalizer of the two
cofaces in degrees zero and one. The two agree by the dual of Simplicial, Lemma 14.20.2, which
is exactly the statement that a cone on a cosimplicial object is determined by its two lowest
legs; with the limit over the simplex category the universal property needed for the adjunction
is the definition of that limit, and no reduction to the equalizer is required.

## References

* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 0D6Z](https://stacks.math.columbia.edu/tag/0D6Z)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory

namespace SimplicialSiteSituation

namespace Augmentation

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K)

/-! ### The system of inverse images along the component augmentations -/

/-- The unit law for the inverse-image comparison of the component augmentations, read at a
sheaf on the augmentation site: in degree `n` it is the canonical identification of the inverse
image of the identity transition with the identity functor. -/
theorem transitionInverseImageIso_hom_app_id (n : SimplexCategory) (G : Sheaf K (Type u)) :
    (transitionInverseImageIso S D K a (𝟙 n)).hom.app G =
      (canonicalIdentityComparison S n).hom.app
        ((componentAugmentation S D K a n).inverseImage.obj G) := by
  rw [transitionInverseImageIso_id, canonicalIdentityComparison_eq_leftAdjointIdIso]
  simp

/-- The cocycle law for the inverse-image comparison of the component augmentations, read at a
sheaf on the augmentation site and solved for the comparison at the composite. -/
theorem transitionInverseImageIso_hom_app_comp {m n p : SimplexCategory} (φ : m ⟶ n)
    (ψ : n ⟶ p) (G : Sheaf K (Type u)) :
    (canonicalCompositionComparison S φ ψ).inv.app
          ((componentAugmentation S D K a m).inverseImage.obj G) ≫
        (transitionInverseImageIso S D K a (φ ≫ ψ)).hom.app G =
      (S.transitionMorphism ψ).inverseImage.map
          ((transitionInverseImageIso S D K a φ).hom.app G) ≫
        (transitionInverseImageIso S D K a ψ).hom.app G := by
  have h := NatTrans.congr_app
    (congrArg Iso.hom (transitionInverseImageIso_comp S D K a φ ψ)) G
  rw [canonicalCompositionComparison_eq_leftAdjointCompIso]
  simpa using h

/-- **Stacks 0D70, part (2), the inverse image.** The system on the simplicial components
attached to a sheaf on the augmentation site: in degree `n` its component is the inverse image
of that sheaf along the augmentation of degree `n`, and its transitions are the canonical
identifications of those inverse images. -/
def inverseImageSystem (G : Sheaf K (Type u)) :
    SimplicialSheafSystem (componentPseudofunctor S) where
  app n := ((Functor.const _).obj (AsSmall.up.obj
    ((componentAugmentation S D K a n.as).inverseImage.obj G))).toCatHom
  naturality f :=
    { toNatTrans :=
        { app := fun _ => AsSmall.up.map
            ((transitionInverseImageIso S D K a f.as).hom.app G)
          naturality := fun _ _ _ => by
            change AsSmall.up.map ((S.transitionMorphism f.as).inverseImage.map (𝟙 _)) ≫ _
              = _ ≫ 𝟙 _
            rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
            exact (Category.id_comp _).trans (Category.comp_id _).symm } }
  naturality_naturality η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    obtain rfl : η = 𝟙 _ := Subsingleton.elim _ _
    cat_disch
  naturality_id b := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext _
    change AsSmall.up.{u, u + 1, u + 1}.map
          ((canonicalIdentityComparison S b.as).inv.app
            ((componentAugmentation S D K a b.as).inverseImage.obj G)) ≫
        AsSmall.up.{u, u + 1, u + 1}.map
          ((transitionInverseImageIso S D K a (𝟙 b.as)).hom.app G) =
      𝟙 (AsSmall.up.{u, u + 1, u + 1}.obj
        ((componentAugmentation S D K a b.as).inverseImage.obj G))
    rw [← CategoryTheory.Functor.map_comp, transitionInverseImageIso_hom_app_id,
      Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
    rfl
  naturality_comp := by
    intro b _ _ f g
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext _
    change AsSmall.up.{u, u + 1, u + 1}.map
          ((canonicalCompositionComparison S f.as g.as).inv.app
            ((componentAugmentation S D K a b.as).inverseImage.obj G)) ≫
        AsSmall.up.{u, u + 1, u + 1}.map
          ((transitionInverseImageIso S D K a (f.as ≫ g.as)).hom.app G) =
      AsSmall.up.{u, u + 1, u + 1}.map
          ((S.transitionMorphism g.as).inverseImage.map
            ((transitionInverseImageIso S D K a f.as).hom.app G)) ≫
        AsSmall.up.{u, u + 1, u + 1}.map
          ((transitionInverseImageIso S D K a g.as).hom.app G)
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      transitionInverseImageIso_hom_app_comp]

/-- The component in degree `n` of the system attached to a sheaf on the augmentation site is
the inverse image of that sheaf along the augmentation of that degree. -/
theorem systemSheaf_inverseImageSystem (G : Sheaf K (Type u)) (n : SimplexCategory) :
    S.systemSheaf (inverseImageSystem S D K a G) n =
      (componentAugmentation S D K a n).inverseImage.obj G := rfl

/-- The inverse-image transition of the system attached to a sheaf on the augmentation site is
the inverse-image comparison of the component augmentations. -/
theorem systemFibreTransition_inverseImageSystem (G : Sheaf K (Type u))
    {m n : SimplexCategory} (φ : m ⟶ n) :
    S.systemFibreTransition (inverseImageSystem S D K a G) φ =
      (transitionInverseImageIso S D K a φ).hom.app G := rfl

/-- The direct-image form of the inverse-image comparison of the component augmentations: the
mate, under the topos adjunction of a simplicial transition, of the comparison of the inverse
images, natural in the sheaf on the augmentation site. -/
def transitionDirectInverseImageTrans {m n : SimplexCategory} (φ : m ⟶ n) :
    (componentAugmentation S D K a m).inverseImage ⟶
      (componentAugmentation S D K a n).inverseImage ⋙
        (S.transitionMorphism φ).pushforward where
  app G := (S.transitionMorphism φ).adj.homEquiv _ _
    ((transitionInverseImageIso S D K a φ).hom.app G)
  naturality G G' f := by
    have hnat := (transitionInverseImageIso S D K a φ).hom.naturality f
    dsimp only [Functor.comp_map] at hnat ⊢
    rw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_right]
    exact congrArg ((S.transitionMorphism φ).adj.homEquiv _ _) hnat

/-- The direct-image transition of the system attached to a sheaf on the augmentation site is
the direct-image form of the inverse-image comparison of the component augmentations. -/
theorem systemDirectTransition_inverseImageSystem (G : Sheaf K (Type u))
    {m n : SimplexCategory} (φ : m ⟶ n) :
    S.systemDirectTransition (inverseImageSystem S D K a G) φ =
      (transitionDirectInverseImageTrans S D K a φ).app G := rfl

/-! ### The inverse image of the total augmentation -/

/-- **Stacks 0D70, part (2), the inverse image on objects.** The sheaf on the total site
attached to a sheaf on the augmentation site: the descent of the system whose component in
degree `n` is the inverse image along the augmentation of that degree. -/
def inverseImageSheaf (G : Sheaf K (Type u)) : Sheaf S.totalTopology (Type u) :=
  S.systemTotalSheaf (inverseImageSystem S D K a G)

/-- **Stacks 0D70, compatibility (2), in inverse images.** The restriction to the simplicial
component of degree `n` of the sheaf attached to a sheaf on the augmentation site is the
inverse image of that sheaf along the augmentation of degree `n`. -/
def componentRestrictionIso (G : Sheaf K (Type u)) (n : SimplexCategory) :
    (S.restrict n).obj (inverseImageSheaf S D K a G) ≅
      (componentAugmentation S D K a n).inverseImage.obj G :=
  S.restrictIso (inverseImageSystem S D K a G) n

/-- The component identifications carry the direct-image transitions of the restrictions to the
direct-image comparisons of the inverse images along the component augmentations. -/
theorem componentRestrictionIso_restrictTransition (G : Sheaf K (Type u))
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (componentRestrictionIso S D K a G m).hom ≫
        (transitionDirectInverseImageTrans S D K a φ).app G =
      (S.restrictTransition φ).app (inverseImageSheaf S D K a G) ≫
        (S.transitionMorphism φ).pushforward.map
          (componentRestrictionIso S D K a G n).hom :=
  S.restrictIso_systemDirectTransition (inverseImageSystem S D K a G) φ

/-- Compatibility with the direct-image transitions of the restrictions, for a family of
morphisms out of the sheaf attached to a sheaf on the augmentation site, is compatibility with
the direct-image comparisons of the inverse images along the component augmentations. -/
theorem restrictTransition_componentRestrictionIso_iff (G : Sheaf K (Type u))
    (F : Sheaf S.totalTopology (Type u))
    (γ : ∀ n, (componentAugmentation S D K a n).inverseImage.obj G ⟶ (S.restrict n).obj F)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    ((componentRestrictionIso S D K a G m).hom ≫ γ m) ≫ (S.restrictTransition φ).app F =
          (S.restrictTransition φ).app (inverseImageSheaf S D K a G) ≫
            (S.transitionMorphism φ).pushforward.map
              ((componentRestrictionIso S D K a G n).hom ≫ γ n) ↔
        γ m ≫ (S.restrictTransition φ).app F =
          (transitionDirectInverseImageTrans S D K a φ).app G ≫
            (S.transitionMorphism φ).pushforward.map (γ n) := by
  rw [CategoryTheory.Functor.map_comp, ← Category.assoc,
    ← componentRestrictionIso_restrictTransition S D K a G φ, Category.assoc, Category.assoc]
  exact cancel_epi _

/-- The morphism from the inverse image along the augmentation of a simplicial degree to the
restriction of the sheaf attached to a second sheaf on the augmentation site, induced by a
morphism of sheaves on the augmentation site. -/
def inverseImageFamilyCore (G G' : Sheaf K (Type u)) (f : G ⟶ G') (n : SimplexCategory) :
    (componentAugmentation S D K a n).inverseImage.obj G ⟶
      (S.restrict n).obj (inverseImageSheaf S D K a G') :=
  (componentAugmentation S D K a n).inverseImage.map f ≫
    (componentRestrictionIso S D K a G' n).inv

/-- The family of morphisms of inverse images induced by a morphism of sheaves on the
augmentation site is compatible with the direct-image comparisons of the inverse images along
the component augmentations. -/
theorem inverseImageFamilyCore_compat (G G' : Sheaf K (Type u)) (f : G ⟶ G')
    {m n : SimplexCategory} (φ : m ⟶ n) :
    inverseImageFamilyCore S D K a G G' f m ≫
        (S.restrictTransition φ).app (inverseImageSheaf S D K a G') =
      (transitionDirectInverseImageTrans S D K a φ).app G ≫
        (S.transitionMorphism φ).pushforward.map
          (inverseImageFamilyCore S D K a G G' f n) := by
  dsimp only [inverseImageFamilyCore]
  have hG' := componentRestrictionIso_restrictTransition S D K a G' φ
  have hnat := (transitionDirectInverseImageTrans S D K a φ).naturality f
  dsimp only [Functor.comp_map] at hnat
  have hinv : (componentRestrictionIso S D K a G' m).inv ≫
      (S.restrictTransition φ).app (inverseImageSheaf S D K a G') =
      (transitionDirectInverseImageTrans S D K a φ).app G' ≫
        (S.transitionMorphism φ).pushforward.map
          (componentRestrictionIso S D K a G' n).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, hG', Category.assoc,
      ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
    exact (Category.comp_id _).symm
  rw [Category.assoc, hinv, ← Category.assoc, hnat, Category.assoc,
    ← CategoryTheory.Functor.map_comp]

/-- The family of morphisms of restrictions induced by a morphism of sheaves on the
augmentation site is compatible with the direct-image transitions of the restrictions. -/
theorem inverseImageFamily_restrictTransition (G G' : Sheaf K (Type u)) (f : G ⟶ G')
    {m n : SimplexCategory} (φ : m ⟶ n) :
    ((componentRestrictionIso S D K a G m).hom ≫ inverseImageFamilyCore S D K a G G' f m) ≫
        (S.restrictTransition φ).app (inverseImageSheaf S D K a G') =
      (S.restrictTransition φ).app (inverseImageSheaf S D K a G) ≫
        (S.transitionMorphism φ).pushforward.map
          ((componentRestrictionIso S D K a G n).hom ≫
            inverseImageFamilyCore S D K a G G' f n) :=
  (restrictTransition_componentRestrictionIso_iff S D K a G
    (inverseImageSheaf S D K a G') (inverseImageFamilyCore S D K a G G' f) φ).mpr
      (inverseImageFamilyCore_compat S D K a G G' f φ)

/-- The morphism of sheaves on the total site induced by a morphism of sheaves on the
augmentation site: the unique one whose restriction to each simplicial degree is the inverse
image of that morphism along the augmentation of that degree. -/
def inverseImageMap (G G' : Sheaf K (Type u)) (f : G ⟶ G') :
    inverseImageSheaf S D K a G ⟶ inverseImageSheaf S D K a G' :=
  S.totalHomOfFamily
    (fun n => (componentRestrictionIso S D K a G n).hom ≫
      inverseImageFamilyCore S D K a G G' f n)
    (fun {_ _} φ => inverseImageFamily_restrictTransition S D K a G G' f φ)

/-- The restriction to a simplicial degree of the morphism induced by a morphism of sheaves on
the augmentation site is, under the component identifications, the inverse image of that
morphism along the augmentation of that degree. -/
theorem restrict_map_inverseImageMap (G G' : Sheaf K (Type u)) (f : G ⟶ G')
    (n : SimplexCategory) :
    (S.restrict n).map (inverseImageMap S D K a G G' f) =
      (componentRestrictionIso S D K a G n).hom ≫
        (componentAugmentation S D K a n).inverseImage.map f ≫
          (componentRestrictionIso S D K a G' n).inv := by
  dsimp only [inverseImageMap, inverseImageFamilyCore]
  apply S.restrict_map_totalHomOfFamily

/-- **Stacks 0D70, part (2), the inverse image.** The inverse image of the total augmentation:
a sheaf on the augmentation site goes to the descent of the system of its inverse images along
the component augmentations, and a morphism of sheaves to the unique morphism whose restriction
to each simplicial degree is the inverse image of that morphism along the augmentation of that
degree. -/
def inverseImage : Sheaf K (Type u) ⥤ Sheaf S.totalTopology (Type u) where
  obj G := inverseImageSheaf S D K a G
  map {G G'} f := inverseImageMap S D K a G G' f
  map_id G := S.total_hom_ext fun n => by
    rw [restrict_map_inverseImageMap,
      CategoryTheory.Functor.map_id (componentAugmentation S D K a n).inverseImage G,
      Category.id_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  map_comp {G G' G''} f g := S.total_hom_ext fun n => by
    rw [restrict_map_inverseImageMap, CategoryTheory.Functor.map_comp (S.restrict n),
      restrict_map_inverseImageMap, restrict_map_inverseImageMap,
      CategoryTheory.Functor.map_comp (componentAugmentation S D K a n).inverseImage f g]
    simp

/-- The restriction to a simplicial degree of the inverse image of a morphism of sheaves on the
augmentation site is, under the component identifications, the inverse image of that morphism
along the augmentation of that degree. -/
theorem restrict_map_inverseImage_map (G G' : Sheaf K (Type u)) (f : G ⟶ G')
    (n : SimplexCategory) :
    (S.restrict n).map ((inverseImage S D K a).map f) =
      (componentRestrictionIso S D K a G n).hom ≫
        (componentAugmentation S D K a n).inverseImage.map f ≫
          (componentRestrictionIso S D K a G' n).inv :=
  restrict_map_inverseImageMap S D K a G G' f n

/-- The component identifications are natural in the sheaf on the augmentation site. -/
theorem componentRestrictionIso_naturality (G G' : Sheaf K (Type u)) (f : G ⟶ G')
    (n : SimplexCategory) :
    (S.restrict n).map (inverseImageMap S D K a G G' f) ≫
        (componentRestrictionIso S D K a G' n).hom =
      (componentRestrictionIso S D K a G n).hom ≫
        (componentAugmentation S D K a n).inverseImage.map f := by
  rw [restrict_map_inverseImageMap]
  simp

/-- **Stacks 0D70, compatibility (2), in inverse images.** The inverse image of the total
augmentation followed by restriction to the simplicial component of degree `n` is the inverse
image along the augmentation of that degree. -/
def restrictCompInverseImageIso (n : SimplexCategory) :
    inverseImage S D K a ⋙ S.restrict n ≅ (componentAugmentation S D K a n).inverseImage :=
  NatIso.ofComponents (fun G => componentRestrictionIso S D K a G n) fun {G G'} f =>
    componentRestrictionIso_naturality S D K a G G' f n

/-! ### The direct image of the total augmentation -/

/-- The direct image along the augmentation of the simplicial degree `n` of the restriction to
that degree: the degree-`n` term of the cosimplicial sheaf of Stacks 0D70, compatibility (3). -/
abbrev componentPushforward (n : SimplexCategory) :
    Sheaf S.totalTopology (Type u) ⥤ Sheaf K (Type u) :=
  S.restrict n ⋙ (componentAugmentation S D K a n).pushforward

/-- The cosimplicial structure of the direct images along the component augmentations: the
direct-image transition of the restrictions, pushed forward along the augmentation of the source
degree and compared with the augmentation of the target degree. -/
def componentPushforwardTransition {m n : SimplexCategory} (φ : m ⟶ n) :
    componentPushforward S D K a m ⟶ componentPushforward S D K a n where
  app F := (componentAugmentation S D K a m).pushforward.map
      ((S.restrictTransition φ).app F) ≫
    (transitionPushforwardIso S D K a φ).hom.app ((S.restrict n).obj F)
  naturality F F' α := by
    have hrT := (S.restrictTransition φ).naturality α
    have hP := (transitionPushforwardIso S D K a φ).hom.naturality
      ((S.restrict n).map α)
    dsimp only [Functor.comp_map] at hrT hP
    dsimp only [componentPushforward, Functor.comp_map]
    rw [← CategoryTheory.Functor.map_comp_assoc, hrT,
      CategoryTheory.Functor.map_comp_assoc, hP, Category.assoc]

/-- **Stacks 0D70, compatibility (3).** The cosimplicial sheaf on the augmentation site attached
to a sheaf on the total site: in degree `n` the direct image along the augmentation of degree `n`
of the restriction to that degree. -/
def cosimplicialPushforward :
    SimplexCategory ⥤ Sheaf S.totalTopology (Type u) ⥤ Sheaf K (Type u) where
  obj n := componentPushforward S D K a n
  map φ := componentPushforwardTransition S D K a φ
  map_id n := by
    apply NatTrans.ext
    funext F
    have hcomp : (componentAugmentation S D K a n).pushforward.map
          ((S.pushforwardId n).inv.app ((S.restrict n).obj F)) ≫
        (componentAugmentation S D K a n).pushforward.map
          ((S.pushforwardId n).hom.app ((S.restrict n).obj F)) =
        𝟙 ((componentAugmentation S D K a n).pushforward.obj ((S.restrict n).obj F)) := by
      rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app,
        CategoryTheory.Functor.map_id]
      rfl
    change (componentAugmentation S D K a n).pushforward.map
          ((S.restrictTransition (𝟙 n)).app F) ≫
        (transitionPushforwardIso S D K a (𝟙 n)).hom.app ((S.restrict n).obj F) = 𝟙 _
    rw [restrictTransition_id' S n F, transitionPushforwardIso_id S D K a n]
    simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.leftUnitor_hom_app]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ 𝟙 ((componentAugmentation S D K a n).pushforward.obj
        ((S.restrict n).obj F))) hcomp).trans (Category.id_comp _))
  map_comp {l m n} χ φ := by
    apply NatTrans.ext
    funext F
    have hnat := (transitionPushforwardIso S D K a χ).hom.naturality
      ((S.restrictTransition φ).app F)
    have hwl := NatTrans.congr_app (congrArg Iso.hom
      (transitionPushforwardIso_whiskerLeft S D K a χ φ)) ((S.restrict n).obj F)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hnat
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_inv_app, Category.id_comp] at hwl
    change (componentAugmentation S D K a l).pushforward.map
          ((S.restrictTransition (χ ≫ φ)).app F) ≫
        (transitionPushforwardIso S D K a (χ ≫ φ)).hom.app ((S.restrict n).obj F) =
      ((componentAugmentation S D K a l).pushforward.map ((S.restrictTransition χ).app F) ≫
          (transitionPushforwardIso S D K a χ).hom.app ((S.restrict m).obj F)) ≫
        ((componentAugmentation S D K a m).pushforward.map ((S.restrictTransition φ).app F) ≫
          (transitionPushforwardIso S D K a φ).hom.app ((S.restrict n).obj F))
    rw [restrictTransition_comp' S χ φ F, CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.map_comp, Category.assoc, Category.assoc, ← hwl,
      reassoc_of% hnat, Category.assoc]

/-- **Stacks 0D70, part (2), the direct image.** The direct image of the total augmentation: the
limit over the simplex category of the cosimplicial sheaf whose degree-`n` term is the direct
image along the augmentation of degree `n` of the restriction to that degree. -/
def pushforward : Sheaf S.totalTopology (Type u) ⥤ Sheaf K (Type u) :=
  (cosimplicialPushforward S D K a).flip ⋙ lim

/-- The cosimplicial sheaf on the augmentation site whose limit is the direct image of a sheaf
on the total site. -/
abbrev pushforwardDiagram (F : Sheaf S.totalTopology (Type u)) :
    SimplexCategory ⥤ Sheaf K (Type u) :=
  (cosimplicialPushforward S D K a).flip.obj F

/-- The direct image of a sheaf on the total site is the limit of its cosimplicial sheaf. -/
theorem pushforward_obj (F : Sheaf S.totalTopology (Type u)) :
    (pushforward S D K a).obj F = limit (pushforwardDiagram S D K a F) := rfl

/-- The leg of the limit in simplicial degree `n`: the direct image of the total augmentation
maps to the direct image along the augmentation of degree `n` of the restriction to that
degree. -/
def pushforwardProjection (F : Sheaf S.totalTopology (Type u)) (n : SimplexCategory) :
    (pushforward S D K a).obj F ⟶ (componentPushforward S D K a n).obj F :=
  limit.π (pushforwardDiagram S D K a F) n

/-- The legs of the limit are compatible with the cosimplicial structure. -/
theorem pushforwardProjection_comp (F : Sheaf S.totalTopology (Type u))
    {m n : SimplexCategory} (φ : m ⟶ n) :
    pushforwardProjection S D K a F m ≫ (componentPushforwardTransition S D K a φ).app F =
      pushforwardProjection S D K a F n :=
  limit.w (pushforwardDiagram S D K a F) φ

/-- The direct image of a morphism of sheaves on the total site is compatible with the legs of
the limit. -/
theorem pushforward_map_comp_projection {F F' : Sheaf S.totalTopology (Type u)} (α : F ⟶ F')
    (n : SimplexCategory) :
    (pushforward S D K a).map α ≫ pushforwardProjection S D K a F' n =
      pushforwardProjection S D K a F n ≫ (componentPushforward S D K a n).map α :=
  limMap_π ((cosimplicialPushforward S D K a).flip.map α) n

/-! ### The adjunction between the two -/

/-- The direct-image form of the inverse-image comparison, on a sheaf on the augmentation
site. -/
theorem transitionDirectInverseImageTrans_app {m n : SimplexCategory} (φ : m ⟶ n)
    (G : Sheaf K (Type u)) :
    (transitionDirectInverseImageTrans S D K a φ).app G =
      (S.transitionMorphism φ).adj.homEquiv _ _
        ((transitionInverseImageIso S D K a φ).hom.app G) := rfl

/-- **Stacks 0D70, part (2), the hom-set bijection in one degree.** The inverse-image comparison
of the component augmentations is the mate of the direct-image comparison: transposing a morphism
out of the inverse image of a simplicial degree along the composite of the augmentation of that
degree with a transition, and then comparing with the augmentation of the target degree, is
transposing it along the augmentation of the target degree. -/
theorem homEquiv_transitionInverseImageIso {m n : SimplexCategory} (φ : m ⟶ n)
    (G : Sheaf K (Type u)) (Y : Sheaf (S.componentTopology n) (Type u))
    (γ : (componentAugmentation S D K a n).inverseImage.obj G ⟶ Y) :
    ((componentAugmentation S D K a m).adj.comp (S.transitionMorphism φ).adj).homEquiv G Y
          ((transitionInverseImageIso S D K a φ).hom.app G ≫ γ) ≫
        (transitionPushforwardIso S D K a φ).hom.app Y =
      (componentAugmentation S D K a n).adj.homEquiv G Y γ := by
  have hconj : conjugateEquiv
        ((componentAugmentation S D K a m).adj.comp (S.transitionMorphism φ).adj)
        (componentAugmentation S D K a n).adj
        (transitionInverseImageIso S D K a φ).inv =
      (transitionPushforwardIso S D K a φ).hom :=
    Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _
  have hu := unit_conjugateEquiv
    ((componentAugmentation S D K a m).adj.comp (S.transitionMorphism φ).adj)
    (componentAugmentation S D K a n).adj (transitionInverseImageIso S D K a φ).inv G
  rw [hconj] at hu
  have hnatP := (transitionPushforwardIso S D K a φ).hom.naturality
    ((transitionInverseImageIso S D K a φ).hom.app G ≫ γ)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnatP hu
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Category.assoc]
  dsimp only [Functor.comp_map]
  rw [hnatP, ← Category.assoc, hu, Category.assoc, ← CategoryTheory.Functor.map_comp,
    ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

/-- **Stacks 0D70, the cone law.** A family of morphisms out of the inverse images along the
component augmentations is compatible with the direct-image comparisons of those inverse images
exactly when its transposes form a cone on the cosimplicial sheaf of direct images. -/
theorem homEquiv_componentPushforwardTransition_iff (G : Sheaf K (Type u))
    (F : Sheaf S.totalTopology (Type u))
    (γ : ∀ n, (componentAugmentation S D K a n).inverseImage.obj G ⟶ (S.restrict n).obj F)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (componentAugmentation S D K a m).adj.homEquiv G ((S.restrict m).obj F) (γ m) ≫
            (componentPushforwardTransition S D K a φ).app F =
          (componentAugmentation S D K a n).adj.homEquiv G ((S.restrict n).obj F) (γ n) ↔
        γ m ≫ (S.restrictTransition φ).app F =
          (transitionDirectInverseImageTrans S D K a φ).app G ≫
            (S.transitionMorphism φ).pushforward.map (γ n) := by
  have hkey := homEquiv_transitionInverseImageIso S D K a φ G ((S.restrict n).obj F) (γ n)
  rw [Adjunction.comp_homEquiv, Equiv.trans_apply, Adjunction.homEquiv_naturality_right,
    ← transitionDirectInverseImageTrans_app] at hkey
  show (componentAugmentation S D K a m).adj.homEquiv G ((S.restrict m).obj F) (γ m) ≫
          (componentAugmentation S D K a m).pushforward.map
              ((S.restrictTransition φ).app F) ≫
            (transitionPushforwardIso S D K a φ).hom.app ((S.restrict n).obj F) =
        (componentAugmentation S D K a n).adj.homEquiv G ((S.restrict n).obj F) (γ n) ↔ _
  rw [← hkey, ← Category.assoc, ← Adjunction.homEquiv_naturality_right]
  exact Iff.trans
    (Iso.cancel_iso_hom_right _ _
      ((transitionPushforwardIso S D K a φ).app ((S.restrict n).obj F)))
    (Equiv.apply_eq_iff_eq _)

/-- The transposes of the restrictions of a morphism out of the sheaf attached to a sheaf on the
augmentation site: a cone on the cosimplicial sheaf of direct images. -/
def pushforwardCone {G : Sheaf K (Type u)} {F : Sheaf S.totalTopology (Type u)}
    (α : inverseImageSheaf S D K a G ⟶ F) : Cone (pushforwardDiagram S D K a F) where
  pt := G
  π :=
    { app := fun n => (componentAugmentation S D K a n).adj.homEquiv G ((S.restrict n).obj F)
        ((componentRestrictionIso S D K a G n).inv ≫ (S.restrict n).map α)
      naturality := fun m n φ => by
        have hβ : ∀ k : SimplexCategory, (componentRestrictionIso S D K a G k).hom ≫
            ((componentRestrictionIso S D K a G k).inv ≫ (S.restrict k).map α) =
            (S.restrict k).map α := fun k => by
          rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
        have hnat := (S.restrictTransition φ).naturality α
        dsimp only [Functor.comp_map] at hnat
        have hcompat := (restrictTransition_componentRestrictionIso_iff S D K a G F
          (fun k => (componentRestrictionIso S D K a G k).inv ≫ (S.restrict k).map α) φ).mp
            (by rw [hβ m, hβ n]; exact hnat)
        exact (Category.id_comp _).trans
          ((homEquiv_componentPushforwardTransition_iff S D K a G F
            (fun k => (componentRestrictionIso S D K a G k).inv ≫ (S.restrict k).map α)
            φ).mpr hcompat).symm }

/-- Two morphisms into the direct image of the total augmentation which agree on every leg of
the limit are equal. -/
theorem pushforward_hom_ext {G : Sheaf K (Type u)} {F : Sheaf S.totalTopology (Type u)}
    {u v : G ⟶ (pushforward S D K a).obj F}
    (h : ∀ n, u ≫ pushforwardProjection S D K a F n =
      v ≫ pushforwardProjection S D K a F n) : u = v :=
  limit.hom_ext h

/-- The morphism into the direct image of the total augmentation determined by a cone on the
cosimplicial sheaf of direct images. -/
def pushforwardLiftCone {F : Sheaf S.totalTopology (Type u)}
    (c : Cone (pushforwardDiagram S D K a F)) : c.pt ⟶ (pushforward S D K a).obj F :=
  limit.lift (pushforwardDiagram S D K a F) c

/-- The morphism determined by a cone recovers the legs of that cone. -/
theorem pushforwardLiftCone_comp_projection {F : Sheaf S.totalTopology (Type u)}
    (c : Cone (pushforwardDiagram S D K a F)) (n : SimplexCategory) :
    pushforwardLiftCone S D K a c ≫ pushforwardProjection S D K a F n = c.π.app n :=
  limit.lift_π c n

/-- The morphism out of the sheaf attached to a sheaf on the augmentation site obtained from a
morphism into the direct image of the total augmentation: in each simplicial degree the
transpose of the corresponding leg of the limit. -/
def pushforwardLift {G : Sheaf K (Type u)} {F : Sheaf S.totalTopology (Type u)}
    (δ : G ⟶ (pushforward S D K a).obj F) : inverseImageSheaf S D K a G ⟶ F :=
  S.totalHomOfFamily
    (fun n => (componentRestrictionIso S D K a G n).hom ≫
      ((componentAugmentation S D K a n).adj.homEquiv G ((S.restrict n).obj F)).symm
        (δ ≫ pushforwardProjection S D K a F n))
    (fun {_ _} φ => by
      refine (restrictTransition_componentRestrictionIso_iff S D K a G F
        (fun k => ((componentAugmentation S D K a k).adj.homEquiv G
          ((S.restrict k).obj F)).symm (δ ≫ pushforwardProjection S D K a F k)) φ).mpr ?_
      refine (homEquiv_componentPushforwardTransition_iff S D K a G F
        (fun k => ((componentAugmentation S D K a k).adj.homEquiv G
          ((S.restrict k).obj F)).symm (δ ≫ pushforwardProjection S D K a F k)) φ).mp ?_
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Category.assoc,
        pushforwardProjection_comp])

/-- The restriction to a simplicial degree of the morphism obtained from a morphism into the
direct image of the total augmentation. -/
theorem restrict_map_pushforwardLift {G : Sheaf K (Type u)}
    {F : Sheaf S.totalTopology (Type u)} (δ : G ⟶ (pushforward S D K a).obj F)
    (n : SimplexCategory) :
    (S.restrict n).map (pushforwardLift S D K a δ) =
      (componentRestrictionIso S D K a G n).hom ≫
        ((componentAugmentation S D K a n).adj.homEquiv G ((S.restrict n).obj F)).symm
          (δ ≫ pushforwardProjection S D K a F n) := by
  dsimp only [pushforwardLift]
  apply S.restrict_map_totalHomOfFamily

/-- The morphism into the direct image of the total augmentation attached to a morphism out of
the inverse image: the transposes of its restrictions, assembled through the limit. -/
def inverseImageTranspose {G : Sheaf K (Type u)} {F : Sheaf S.totalTopology (Type u)}
    (α : inverseImageSheaf S D K a G ⟶ F) : G ⟶ (pushforward S D K a).obj F :=
  pushforwardLiftCone S D K a (pushforwardCone S D K a α)

/-- The legs of the morphism attached to a morphism out of the inverse image are the transposes
of its restrictions. -/
theorem inverseImageTranspose_comp_projection {G : Sheaf K (Type u)}
    {F : Sheaf S.totalTopology (Type u)} (α : inverseImageSheaf S D K a G ⟶ F)
    (n : SimplexCategory) :
    inverseImageTranspose S D K a α ≫ pushforwardProjection S D K a F n =
      (componentAugmentation S D K a n).adj.homEquiv G ((S.restrict n).obj F)
        ((componentRestrictionIso S D K a G n).inv ≫ (S.restrict n).map α) :=
  pushforwardLiftCone_comp_projection S D K a (pushforwardCone S D K a α) n

/-- **Stacks 0D70, part (2).** The hom-set bijection of the total augmentation: a morphism out of
the inverse image of a sheaf on the augmentation site is, degree by degree, a cosimplicial
morphism from the constant cosimplicial sheaf, hence a morphism into the limit which is the
direct image. -/
def homEquiv (G : Sheaf K (Type u)) (F : Sheaf S.totalTopology (Type u)) :
    (inverseImageSheaf S D K a G ⟶ F) ≃ (G ⟶ (pushforward S D K a).obj F) where
  toFun α := inverseImageTranspose S D K a α
  invFun δ := pushforwardLift S D K a δ
  left_inv α := S.total_hom_ext fun n => by
    change (S.restrict n).map (pushforwardLift S D K a (inverseImageTranspose S D K a α)) =
      (S.restrict n).map α
    rw [restrict_map_pushforwardLift, inverseImageTranspose_comp_projection,
      Equiv.symm_apply_apply, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  right_inv δ := pushforward_hom_ext S D K a fun n => by
    change inverseImageTranspose S D K a (pushforwardLift S D K a δ) ≫
      pushforwardProjection S D K a F n = δ ≫ pushforwardProjection S D K a F n
    rw [inverseImageTranspose_comp_projection, restrict_map_pushforwardLift, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp, Equiv.apply_symm_apply]

/-- The hom-set bijection is natural in the sheaf on the augmentation site. -/
theorem homEquiv_naturality_left_symm_aux (G' G : Sheaf K (Type u))
    (F : Sheaf S.totalTopology (Type u)) (f : G' ⟶ G)
    (g : G ⟶ (pushforward S D K a).obj F) :
    pushforwardLift S D K a (f ≫ g) =
      inverseImageMap S D K a G' G f ≫ pushforwardLift S D K a g := by
  refine S.total_hom_ext fun n => ?_
  rw [restrict_map_pushforwardLift, Category.assoc f g (pushforwardProjection S D K a F n),
    Adjunction.homEquiv_naturality_left_symm, CategoryTheory.Functor.map_comp (S.restrict n),
    restrict_map_inverseImageMap, restrict_map_pushforwardLift]
  simp

/-- The hom-set bijection is natural in the sheaf on the total site. -/
theorem homEquiv_naturality_right_aux (G : Sheaf K (Type u))
    (F F' : Sheaf S.totalTopology (Type u)) (α : inverseImageSheaf S D K a G ⟶ F)
    (g : F ⟶ F') :
    inverseImageTranspose S D K a (α ≫ g) =
      inverseImageTranspose S D K a α ≫ (pushforward S D K a).map g := by
  refine pushforward_hom_ext S D K a fun n => ?_
  rw [inverseImageTranspose_comp_projection, Category.assoc, pushforward_map_comp_projection,
    ← Category.assoc, inverseImageTranspose_comp_projection]
  dsimp only [componentPushforward, Functor.comp_map]
  rw [← Adjunction.homEquiv_naturality_right, CategoryTheory.Functor.map_comp (S.restrict n),
    Category.assoc]

/-- **Stacks 0D70, part (2).** The inverse image of the total augmentation is left adjoint to its
direct image. -/
def adjunction : inverseImage S D K a ⊣ pushforward S D K a :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv S D K a
      homEquiv_naturality_left_symm := fun {G' G F} f g =>
        homEquiv_naturality_left_symm_aux S D K a G' G F f g
      homEquiv_naturality_right := fun {G F F'} α g =>
        homEquiv_naturality_right_aux S D K a G F F' α g }

/-! ### Exactness of the inverse image, and the morphism of topoi -/

/-- Restriction to a simplicial degree followed by evaluation at an object of that degree is
evaluation of the total sheaf at the image of that object. -/
theorem restrict_comp_evaluation (n : SimplexCategory) (V : S.component n) :
    S.restrict n ⋙ sheafToPresheaf (S.componentTopology n) (Type u) ⋙
        (evaluation (S.component n)ᵒᵖ (Type u)).obj (Opposite.op V) =
      sheafToPresheaf S.totalTopology (Type u) ⋙
        (evaluation (S.totalCategory)ᵒᵖ (Type u)).obj
          (Opposite.op ((S.inclusion n).obj V)) := rfl

/-- Evaluation of a sheaf on the total site at an object is evaluation, at the fibre of that
object, of its restriction to the simplicial degree of that object. -/
theorem evaluation_eq_restrict_comp_evaluation (X : (S.totalCategory)ᵒᵖ) :
    sheafToPresheaf S.totalTopology (Type u) ⋙
        (evaluation (S.totalCategory)ᵒᵖ (Type u)).obj X =
      S.restrict (S.totalObjDegree X.unop) ⋙
        sheafToPresheaf (S.componentTopology (S.totalObjDegree X.unop)) (Type u) ⋙
          (evaluation (S.component (S.totalObjDegree X.unop))ᵒᵖ (Type u)).obj
            (Opposite.op (S.totalObjFibre X.unop)) := by
  rw [restrict_comp_evaluation, S.inclusion_obj_totalObjFibre]

/-- **Stacks 0D70, part (2).** The inverse image of the total augmentation is exact. A sheaf on
the total site is evaluated at an object of the total category through its restriction to the
simplicial degree of that object, and in each degree the inverse image of the total augmentation
is the inverse image of the augmentation of that degree, which is exact. -/
instance inverseImage_preservesFiniteLimits :
    PreservesFiniteLimits (inverseImage S D K a) where
  preservesFiniteLimits E _ _ := by
    have hcomp : PreservesLimitsOfShape E
        (inverseImage S D K a ⋙ sheafToPresheaf S.totalTopology (Type u)) := by
      refine preservesLimitsOfShape_of_evaluation _ E fun X => ?_
      have hpres :=
        (componentAugmentation S D K a (S.totalObjDegree X.unop)).preservesFiniteLimits
      have heq : (inverseImage S D K a ⋙ sheafToPresheaf S.totalTopology (Type u)) ⋙
            (evaluation (S.totalCategory)ᵒᵖ (Type u)).obj X =
          (inverseImage S D K a ⋙ S.restrict (S.totalObjDegree X.unop)) ⋙
            (sheafToPresheaf (S.componentTopology (S.totalObjDegree X.unop)) (Type u) ⋙
              (evaluation (S.component (S.totalObjDegree X.unop))ᵒᵖ (Type u)).obj
                (Opposite.op (S.totalObjFibre X.unop))) := by
        rw [Functor.assoc, evaluation_eq_restrict_comp_evaluation]
        exact (Functor.assoc _ _ _).symm
      rw [heq]
      exact preservesLimitsOfShape_of_natIso (Functor.isoWhiskerRight
        (restrictCompInverseImageIso S D K a (S.totalObjDegree X.unop)) _).symm
    exact ⟨fun {_} => preservesLimit_of_reflects_of_preserves (inverseImage S D K a)
      (sheafToPresheaf S.totalTopology (Type u))⟩

/-- **Stacks 0D70, part (2).** The morphism of topoi from the sheaves on the total site to the
sheaves on the augmentation site induced by an augmentation: its inverse image is the descent of
the inverse images along the component augmentations, its direct image is the limit of the
cosimplicial sheaf of their direct images, and the two are adjoint. -/
@[stacks 0D70 "part (2): the morphism of topoi of the total site"]
def totalMorphismOfTopoi :
    MorphismOfTopoi (Sheaf S.totalTopology (Type u)) (Sheaf K (Type u)) where
  pushforward := pushforward S D K a
  inverseImage := inverseImage S D K a
  adj := adjunction S D K a
  preservesFiniteLimits := inverseImage_preservesFiniteLimits S D K a

/-- **Stacks 0D70, compatibility (2), in inverse images.** The inverse image of the total
augmentation followed by restriction to the simplicial component of degree `n` is the inverse
image of the augmentation of that degree. Restriction is the inverse image of the morphism of
topoi which Stacks 09WG attaches to that degree, so this says that the augmentation of a
simplicial degree is the total augmentation composed with that morphism. -/
def totalMorphismOfTopoi_restrict_iso (n : SimplexCategory) :
    (totalMorphismOfTopoi S D K a).inverseImage ⋙ S.restrict n ≅
      (componentAugmentation S D K a n).inverseImage :=
  restrictCompInverseImageIso S D K a n

/-- **Stacks 0D70, compatibility (2), in inverse images.** The inverse image of the total
augmentation followed by the inverse image of the morphism of topoi which Stacks 09WG attaches
to the simplicial degree `n` is the inverse image of the augmentation of that degree: the
augmentation of a simplicial degree is the total augmentation composed with that morphism. -/
@[stacks 0D70 "compatibility (2): composition with a component inclusion"]
def totalMorphismOfTopoi_componentMorphism_iso (n : SimplexCategory) :
    (totalMorphismOfTopoi S D K a).inverseImage ⋙ (componentMorphism S n).inverseImage ≅
      (componentAugmentation S D K a n).inverseImage :=
  Functor.isoWhiskerLeft (totalMorphismOfTopoi S D K a).inverseImage
      (componentInverseImageIsoPushforward S n) ≪≫
    restrictCompInverseImageIso S D K a n

end Augmentation

end SimplicialSiteSituation

namespace SimplicialSite

namespace ContinuousAugmentation

variable {C : SimplicialSite.{u}} {D : Cat.{u, u}} {K : GrothendieckTopology D}
  (a : C.ContinuousAugmentation D K)

/-- **Stacks 0D70, part (2), case (A), the inverse image.** The inverse image of the
augmentation of the total site of a simplicial site: a sheaf on the augmentation site goes to
the sheaf on the total site whose component in simplicial degree `n` is its inverse image along
the augmentation of that degree. -/
def totalInverseImage : Sheaf K (Type u) ⥤ Sheaf C.totalTopology (Type u) :=
  SimplicialSiteSituation.Augmentation.inverseImage C.situation D K a

/-- **Stacks 0D70, part (2), case (A), the direct image.** The direct image of the augmentation
of the total site of a simplicial site: the limit over the simplex category of the cosimplicial
sheaf whose degree-`n` term is the direct image along the augmentation of degree `n` of the
restriction to that degree. -/
def totalPushforward : Sheaf C.totalTopology (Type u) ⥤ Sheaf K (Type u) :=
  SimplicialSiteSituation.Augmentation.pushforward C.situation D K a

/-- **Stacks 0D70, part (2), case (A).** The two are adjoint. -/
def totalAdjunction : totalInverseImage a ⊣ totalPushforward a :=
  SimplicialSiteSituation.Augmentation.adjunction C.situation D K a

/-- **Stacks 0D70, part (2), case (A).** The morphism of topoi from the sheaves on the total
site of a simplicial site to the sheaves on the augmentation site. -/
def totalMorphismOfTopoi :
    MorphismOfTopoi (Sheaf C.totalTopology (Type u)) (Sheaf K (Type u)) :=
  SimplicialSiteSituation.Augmentation.totalMorphismOfTopoi C.situation D K a

/-- **Stacks 0D70, compatibility (2), case (A), in inverse images.** The inverse image of the
total augmentation followed by restriction to the simplicial component of degree `n` is the
inverse image of the augmentation of that degree. -/
def totalInverseImage_restrict_iso (n : SimplexCategory) :
    totalInverseImage a ⋙ C.situation.restrict n ≅
      (SimplicialSiteSituation.Augmentation.componentAugmentation C.situation D K a
        n).inverseImage :=
  SimplicialSiteSituation.Augmentation.restrictCompInverseImageIso C.situation D K a n

end ContinuousAugmentation

end SimplicialSite

end CategoryTheory

end
