module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.Pullback

/-!
# Subgroupoids of a groupoid scheme cut out by a pair of monomorphisms

A *subgroupoid presentation* of a groupoid scheme `G` is a pair of monomorphisms `V ⟶ U` and
`W ⟶ R` into its object and arrow schemes, together with source, target, composition, identity
and inverse morphisms for `(V, W)` which the two monomorphisms carry to those of `G`.  Any such
presentation is already a groupoid scheme: each groupoid axiom is an equality of morphisms into
`V` or into `W`, so it may be tested after composing with the corresponding monomorphism, where
it becomes the corresponding axiom of `G`.

The two monomorphisms are not required to be immersions, open or closed; only that they be
monomorphisms and that they intertwine the five structure morphisms.

## Main definitions

* `Stacks.Groupoids.GroupoidScheme.MonoSubgroupoid` is the data above.
* `Stacks.Groupoids.GroupoidScheme.MonoSubgroupoid.toGroupoidScheme` is **the groupoid scheme it
  presents**, with the given schemes and structure morphisms.
* `Stacks.Groupoids.GroupoidScheme.MonoSubgroupoid.hom` is **the morphism of groupoid schemes**
  from it to `G`, given by the two monomorphisms.

## Main results

* `Stacks.Groupoids.GroupoidScheme.MonoSubgroupoid.lift_comp_comp_ιArrows`: a composite of two
  composable generalized arrows of the subgroupoid is carried by the monomorphism of arrow
  schemes to the composite of their images.
* `Stacks.Groupoids.GroupoidScheme.MonoSubgroupoid.comp_ιArrows_condition`: composability of a
  pair of generalized arrows is inherited by their images.

## Implementation notes

The monomorphism hypotheses are stated in `CategoryTheory.Over S`, where the groupoid axioms
live.  `CategoryTheory.Over.mono_of_mono_left` reduces them to monomorphy of the underlying
morphisms of schemes.

The axioms of `Stacks.Groupoids.GroupoidScheme` which are stated on generalized points are
proved here by transporting the generalized point along the monomorphism of arrow schemes.
`Stacks.Groupoids.GroupoidScheme.MonoSubgroupoid.lift_comp_comp_ιArrows` takes the transported
arrows as separate arguments together with equations identifying them, in the manner of
`AlgebraicGeometry.GroupoidScheme.stabilizerLift`; this avoids rewriting underneath the
composability witness of `CategoryTheory.Limits.pullback.lift`, which is a dependent position.

## References

* [Stacks Project, Tag 0231](https://stacks.math.columbia.edu/tag/0231)
* [Stacks Project, Tag 03BC](https://stacks.math.columbia.edu/tag/03BC)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Groupoids

namespace GroupoidScheme

/-- A presentation of a subgroupoid of a groupoid scheme `G`: schemes of objects and arrows
mapping to those of `G` by monomorphisms, with source, target, composition, identity and inverse
morphisms which the two monomorphisms intertwine with those of `G`. -/
structure MonoSubgroupoid {S : Scheme.{u}} (G : GroupoidScheme S) where
  /-- The scheme of objects of the subgroupoid. -/
  objects : Over S
  /-- The scheme of arrows of the subgroupoid. -/
  arrows : Over S
  /-- The monomorphism onto the objects of `G`. -/
  ιObjects : objects ⟶ G.objects
  /-- The monomorphism onto the arrows of `G`. -/
  ιArrows : arrows ⟶ G.arrows
  /-- The morphism `ιObjects` is a monomorphism. -/
  mono_ιObjects : Mono ιObjects
  /-- The morphism `ιArrows` is a monomorphism. -/
  mono_ιArrows : Mono ιArrows
  /-- The source morphism of the subgroupoid. -/
  source : arrows ⟶ objects
  /-- The target morphism of the subgroupoid. -/
  target : arrows ⟶ objects
  /-- The composition morphism of the subgroupoid. -/
  comp : pullback source target ⟶ arrows
  /-- The identity morphism of the subgroupoid. -/
  identity : objects ⟶ arrows
  /-- The inverse morphism of the subgroupoid. -/
  inverse : arrows ⟶ arrows
  /-- The monomorphisms intertwine the source morphisms. -/
  source_ι : source ≫ ιObjects = ιArrows ≫ G.source
  /-- The monomorphisms intertwine the target morphisms. -/
  target_ι : target ≫ ιObjects = ιArrows ≫ G.target
  /-- The monomorphisms intertwine the identity morphisms. -/
  identity_ι : identity ≫ ιArrows = ιObjects ≫ G.identity
  /-- The monomorphism of arrow schemes intertwines the inverse morphisms. -/
  inverse_ι : inverse ≫ ιArrows = ιArrows ≫ G.inverse
  /-- The monomorphisms intertwine the composition morphisms. -/
  comp_ι : comp ≫ ιArrows =
    pullback.map source target G.source G.target ιArrows ιArrows ιObjects source_ι target_ι ≫
      G.comp

namespace MonoSubgroupoid

variable {S : Scheme.{u}} {G : GroupoidScheme S} (M : MonoSubgroupoid G)

attribute [instance] mono_ιObjects mono_ιArrows

/-! ### Transporting the structure morphisms -/

/-- The source of the image of an arrow is the image of its source. -/
@[reassoc]
theorem ιArrows_comp_source : M.ιArrows ≫ G.source = M.source ≫ M.ιObjects := M.source_ι.symm

/-- The target of the image of an arrow is the image of its target. -/
@[reassoc]
theorem ιArrows_comp_target : M.ιArrows ≫ G.target = M.target ≫ M.ιObjects := M.target_ι.symm

/-- The identity at the image of an object is the image of its identity. -/
@[reassoc]
theorem ιObjects_comp_identity : M.ιObjects ≫ G.identity = M.identity ≫ M.ιArrows :=
  M.identity_ι.symm

/-- The inverse of the image of an arrow is the image of its inverse. -/
@[reassoc]
theorem ιArrows_comp_inverse : M.ιArrows ≫ G.inverse = M.inverse ≫ M.ιArrows := M.inverse_ι.symm

/-- **Composability of generalized arrows is inherited by their images.** -/
theorem comp_ιArrows_condition {T : Over S} {a b : T ⟶ M.arrows}
    (h : a ≫ M.source = b ≫ M.target) :
    (a ≫ M.ιArrows) ≫ G.source = (b ≫ M.ιArrows) ≫ G.target := by
  simp only [Category.assoc, ιArrows_comp_source, ιArrows_comp_target]
  simp only [← Category.assoc, h]

/-- Composability of generalized arrows transfers to any pair of arrows equal to their images. -/
private theorem condition_of_comp_ιArrows_eq {T : Over S} {a b : T ⟶ M.arrows}
    (h : a ≫ M.source = b ≫ M.target) {a' b' : T ⟶ G.arrows}
    (ha : a ≫ M.ιArrows = a') (hb : b ≫ M.ιArrows = b') : a' ≫ G.source = b' ≫ G.target := by
  subst ha hb
  exact M.comp_ιArrows_condition h

/-! ### Composable arrows -/

/-- The morphism on schemes of composable arrows induced by a subgroupoid presentation. -/
noncomputable def composables :
    pullback M.source M.target ⟶ pullback G.source G.target :=
  pullback.map _ _ _ _ M.ιArrows M.ιArrows M.ιObjects M.source_ι M.target_ι

/-- The morphism `composables` is compatible with the first projections. -/
@[reassoc (attr := simp)]
theorem composables_fst :
    M.composables ≫ pullback.fst G.source G.target =
      pullback.fst M.source M.target ≫ M.ιArrows :=
  pullback.lift_fst _ _ _

/-- The morphism `composables` is compatible with the second projections. -/
@[reassoc (attr := simp)]
theorem composables_snd :
    M.composables ≫ pullback.snd G.source G.target =
      pullback.snd M.source M.target ≫ M.ιArrows :=
  pullback.lift_snd _ _ _

/-- The composition morphism of the subgroupoid, read through the monomorphism of arrow
schemes. -/
@[reassoc]
theorem comp_comp_ιArrows : M.comp ≫ M.ιArrows = M.composables ≫ G.comp := M.comp_ι

/-- Transporting a pair of composable generalized arrows along the monomorphism of arrow schemes
commutes with the comparison of composable arrows. -/
theorem lift_comp_composables {T : Over S} (a b : T ⟶ M.arrows)
    (w : a ≫ M.source = b ≫ M.target) (a' b' : T ⟶ G.arrows)
    (ha : a ≫ M.ιArrows = a') (hb : b ≫ M.ιArrows = b')
    (w' : a' ≫ G.source = b' ≫ G.target) :
    pullback.lift a b w ≫ M.composables = pullback.lift a' b' w' := by
  subst ha
  subst hb
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, composables_fst, ← Category.assoc, pullback.lift_fst, pullback.lift_fst]
  · rw [Category.assoc, composables_snd, ← Category.assoc, pullback.lift_snd, pullback.lift_snd]

/-- **A composite of two composable generalized arrows of the subgroupoid is carried by the
monomorphism of arrow schemes to the composite of their images.** -/
theorem lift_comp_comp_ιArrows {T : Over S} (a b : T ⟶ M.arrows)
    (w : a ≫ M.source = b ≫ M.target) (a' b' : T ⟶ G.arrows)
    (ha : a ≫ M.ιArrows = a') (hb : b ≫ M.ιArrows = b')
    (w' : a' ≫ G.source = b' ≫ G.target) :
    (pullback.lift a b w ≫ M.comp) ≫ M.ιArrows = pullback.lift a' b' w' ≫ G.comp := by
  rw [Category.assoc, comp_comp_ιArrows, ← Category.assoc,
    M.lift_comp_composables a b w a' b' ha hb w']

/-! ### The groupoid axioms -/

/-- The source of the identity at an object is that object. -/
theorem source_identity : M.identity ≫ M.source = 𝟙 M.objects := by
  rw [← cancel_mono M.ιObjects, Category.id_comp, Category.assoc, M.source_ι,
    ← Category.assoc, M.identity_ι, Category.assoc, G.source_identity, Category.comp_id]

/-- The target of the identity at an object is that object. -/
theorem target_identity : M.identity ≫ M.target = 𝟙 M.objects := by
  rw [← cancel_mono M.ιObjects, Category.id_comp, Category.assoc, M.target_ι,
    ← Category.assoc, M.identity_ι, Category.assoc, G.target_identity, Category.comp_id]

/-- The source of the inverse of an arrow is its target. -/
theorem source_inverse : M.inverse ≫ M.source = M.target := by
  rw [← cancel_mono M.ιObjects, Category.assoc, M.source_ι, ← Category.assoc, M.inverse_ι,
    Category.assoc, G.source_inverse, M.target_ι]

/-- The target of the inverse of an arrow is its source. -/
theorem target_inverse : M.inverse ≫ M.target = M.source := by
  rw [← cancel_mono M.ιObjects, Category.assoc, M.target_ι, ← Category.assoc, M.inverse_ι,
    Category.assoc, G.target_inverse, M.source_ι]

/-- The source of a composite is the source of its second factor. -/
theorem source_comp :
    M.comp ≫ M.source = pullback.snd M.source M.target ≫ M.source := by
  rw [← cancel_mono M.ιObjects]
  simp only [Category.assoc, M.source_ι]
  rw [comp_comp_ιArrows_assoc, G.source_comp, composables_snd_assoc]

/-- The target of a composite is the target of its first factor. -/
theorem target_comp :
    M.comp ≫ M.target = pullback.fst M.source M.target ≫ M.target := by
  rw [← cancel_mono M.ιObjects]
  simp only [Category.assoc, M.target_ι]
  rw [comp_comp_ιArrows_assoc, G.target_comp, composables_fst_assoc]

/-- Composing a generalized arrow with the identity at its target gives the arrow back. -/
theorem left_identity (T : Over S) (f : T ⟶ M.arrows)
    (w : (f ≫ M.target ≫ M.identity) ≫ M.source = f ≫ M.target) :
    pullback.lift (f ≫ M.target ≫ M.identity) f w ≫ M.comp = f := by
  have key : (f ≫ M.target ≫ M.identity) ≫ M.ιArrows =
      (f ≫ M.ιArrows) ≫ G.target ≫ G.identity := by
    simp only [Category.assoc, ιArrows_comp_target_assoc, ιObjects_comp_identity]
  have w' := M.condition_of_comp_ιArrows_eq w key rfl
  rw [← cancel_mono M.ιArrows, M.lift_comp_comp_ιArrows _ f w _ _ key rfl w']
  exact G.left_identity T (f ≫ M.ιArrows) w'

/-- Composing a generalized arrow with the identity at its source gives the arrow back. -/
theorem right_identity (T : Over S) (f : T ⟶ M.arrows)
    (w : f ≫ M.source = (f ≫ M.source ≫ M.identity) ≫ M.target) :
    pullback.lift f (f ≫ M.source ≫ M.identity) w ≫ M.comp = f := by
  have key : (f ≫ M.source ≫ M.identity) ≫ M.ιArrows =
      (f ≫ M.ιArrows) ≫ G.source ≫ G.identity := by
    simp only [Category.assoc, ιArrows_comp_source_assoc, ιObjects_comp_identity]
  have w' := M.condition_of_comp_ιArrows_eq w rfl key
  rw [← cancel_mono M.ιArrows, M.lift_comp_comp_ιArrows f _ w _ _ rfl key w']
  exact G.right_identity T (f ≫ M.ιArrows) w'

/-- The composite of the inverse of a generalized arrow `f` with `f` is the identity at the
source of `f`. -/
theorem left_inverse (T : Over S) (f : T ⟶ M.arrows)
    (w : (f ≫ M.inverse) ≫ M.source = f ≫ M.target) :
    pullback.lift (f ≫ M.inverse) f w ≫ M.comp = f ≫ M.source ≫ M.identity := by
  have key : (f ≫ M.inverse) ≫ M.ιArrows = (f ≫ M.ιArrows) ≫ G.inverse := by
    simp only [Category.assoc, ιArrows_comp_inverse]
  have w' := M.condition_of_comp_ιArrows_eq w key rfl
  rw [← cancel_mono M.ιArrows, M.lift_comp_comp_ιArrows _ f w _ _ key rfl w',
    G.left_inverse T (f ≫ M.ιArrows) w']
  simp only [Category.assoc, ιArrows_comp_source_assoc, ιObjects_comp_identity]

/-- The composite of a generalized arrow `f` with its inverse is the identity at the target of
`f`. -/
theorem right_inverse (T : Over S) (f : T ⟶ M.arrows)
    (w : f ≫ M.source = (f ≫ M.inverse) ≫ M.target) :
    pullback.lift f (f ≫ M.inverse) w ≫ M.comp = f ≫ M.target ≫ M.identity := by
  have key : (f ≫ M.inverse) ≫ M.ιArrows = (f ≫ M.ιArrows) ≫ G.inverse := by
    simp only [Category.assoc, ιArrows_comp_inverse]
  have w' := M.condition_of_comp_ιArrows_eq w rfl key
  rw [← cancel_mono M.ιArrows, M.lift_comp_comp_ιArrows f _ w _ _ rfl key w',
    G.right_inverse T (f ≫ M.ιArrows) w']
  simp only [Category.assoc, ιArrows_comp_target_assoc, ιObjects_comp_identity]

/-- Composition of generalized arrows of the subgroupoid is associative. -/
theorem assoc (T : Over S) (f g h : T ⟶ M.arrows)
    (wfg : f ≫ M.source = g ≫ M.target) (wgh : g ≫ M.source = h ≫ M.target)
    (w₁ : (pullback.lift f g wfg ≫ M.comp) ≫ M.source = h ≫ M.target)
    (w₂ : f ≫ M.source = (pullback.lift g h wgh ≫ M.comp) ≫ M.target) :
    pullback.lift (pullback.lift f g wfg ≫ M.comp) h w₁ ≫ M.comp =
      pullback.lift f (pullback.lift g h wgh ≫ M.comp) w₂ ≫ M.comp := by
  have wfg' := M.comp_ιArrows_condition wfg
  have wgh' := M.comp_ιArrows_condition wgh
  have kfg : (pullback.lift f g wfg ≫ M.comp) ≫ M.ιArrows =
      pullback.lift (f ≫ M.ιArrows) (g ≫ M.ιArrows) wfg' ≫ G.comp :=
    M.lift_comp_comp_ιArrows f g wfg _ _ rfl rfl wfg'
  have kgh : (pullback.lift g h wgh ≫ M.comp) ≫ M.ιArrows =
      pullback.lift (g ≫ M.ιArrows) (h ≫ M.ιArrows) wgh' ≫ G.comp :=
    M.lift_comp_comp_ιArrows g h wgh _ _ rfl rfl wgh'
  have w₁' := M.condition_of_comp_ιArrows_eq w₁ kfg rfl
  have w₂' := M.condition_of_comp_ιArrows_eq w₂ rfl kgh
  rw [← cancel_mono M.ιArrows, M.lift_comp_comp_ιArrows _ h w₁ _ _ kfg rfl w₁',
    M.lift_comp_comp_ιArrows f _ w₂ _ _ rfl kgh w₂']
  exact G.assoc T (f ≫ M.ιArrows) (g ≫ M.ιArrows) (h ≫ M.ιArrows) wfg' wgh' w₁' w₂'

/-! ### The groupoid scheme and the morphism to `G` -/

/-- **The groupoid scheme presented by a subgroupoid presentation**, with the given schemes of
objects and arrows and the given structure morphisms. -/
noncomputable def toGroupoidScheme : GroupoidScheme S where
  objects := M.objects
  arrows := M.arrows
  source := M.source
  target := M.target
  comp := M.comp
  identity := M.identity
  inverse := M.inverse
  source_identity := M.source_identity
  target_identity := M.target_identity
  source_inverse := M.source_inverse
  target_inverse := M.target_inverse
  source_comp := M.source_comp
  target_comp := M.target_comp
  left_identity := M.left_identity
  right_identity := M.right_identity
  left_inverse := M.left_inverse
  right_inverse := M.right_inverse
  assoc := M.assoc

/-- The scheme of objects of `M.toGroupoidScheme` is `M.objects`. -/
@[simp] theorem toGroupoidScheme_objects : M.toGroupoidScheme.objects = M.objects := rfl

/-- The scheme of arrows of `M.toGroupoidScheme` is `M.arrows`. -/
@[simp] theorem toGroupoidScheme_arrows : M.toGroupoidScheme.arrows = M.arrows := rfl

/-- The source morphism of `M.toGroupoidScheme` is `M.source`. -/
@[simp] theorem toGroupoidScheme_source : M.toGroupoidScheme.source = M.source := rfl

/-- The target morphism of `M.toGroupoidScheme` is `M.target`. -/
@[simp] theorem toGroupoidScheme_target : M.toGroupoidScheme.target = M.target := rfl

/-- The identity morphism of `M.toGroupoidScheme` is `M.identity`. -/
@[simp] theorem toGroupoidScheme_identity : M.toGroupoidScheme.identity = M.identity := rfl

/-- The inverse morphism of `M.toGroupoidScheme` is `M.inverse`. -/
@[simp] theorem toGroupoidScheme_inverse : M.toGroupoidScheme.inverse = M.inverse := rfl

/-- **The morphism of groupoid schemes from the presented subgroupoid to `G`**, given by the two
monomorphisms. -/
noncomputable def hom : GroupoidScheme.Hom M.toGroupoidScheme G where
  mapObjects := M.ιObjects
  mapArrows := M.ιArrows
  map_source := M.source_ι.symm
  map_target := M.target_ι.symm
  map_identity := M.identity_ι.symm
  map_comp := fun _ a b w w' => M.lift_comp_comp_ιArrows a b w _ _ rfl rfl w'

/-- The morphism of object schemes underlying `M.hom` is `M.ιObjects`. -/
@[simp] theorem hom_mapObjects : M.hom.mapObjects = M.ιObjects := rfl

/-- The morphism of arrow schemes underlying `M.hom` is `M.ιArrows`. -/
@[simp] theorem hom_mapArrows : M.hom.mapArrows = M.ιArrows := rfl

end MonoSubgroupoid

end GroupoidScheme

end Stacks.Groupoids

end
