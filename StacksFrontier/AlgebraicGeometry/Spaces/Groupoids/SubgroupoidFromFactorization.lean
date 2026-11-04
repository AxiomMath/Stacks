module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SchemeSplittings

/-!
# A subgroupoid of a groupoid scheme from three factorizations

Let `(U, R, s, t, c, e, i)` be a groupoid scheme over `S` and let `ι : P ⟶ R` be a
monomorphism of schemes over `S`.  Then `(U, P, s ∘ ι, t ∘ ι, …)` is a groupoid scheme on the
same object scheme, and `ι` a morphism of groupoid schemes, as soon as three morphisms factor
through `ι`: the composition of two arrows of `P` composable for the restricted source and
target, the identity `e : U ⟶ R`, and the composite `ι ≫ i`.  Nothing else is needed — every
groupoid axiom for `P` follows from the corresponding axiom for `R` by cancelling the
monomorphism `ι`.

This is the conditions-(a)-and-(b) half of Stacks 04RK built from data rather than assumed:
together with openness of `ι` and finiteness of `s ∘ ι` and `t ∘ ι` it produces a
`Stacks.Groupoids.GroupoidScheme.OpenFiniteSubgroupoid`, hence by the footnote to part (3) of
that tag a quasi-splitting at every point of `U`.

## Main definitions

* `Stacks.Groupoids.GroupoidScheme.subComposable`: the comparison morphism
  `P ×_{s∘ι, U, t∘ι} P ⟶ R ×_{s, U, t} R`.
* `Stacks.Groupoids.GroupoidScheme.SubgroupoidData`: the three factorizations, as data.
* `Stacks.Groupoids.GroupoidScheme.SubgroupoidData.groupoid` and
  `Stacks.Groupoids.GroupoidScheme.SubgroupoidData.inclusionHom`: the subgroupoid they define
  and its morphism into the ambient groupoid.
* `Stacks.Groupoids.GroupoidScheme.SubgroupoidData.openFiniteSubgroupoid`: conditions (a) and
  (b) of Stacks 04RK, for an open `ι` with finite `s ∘ ι` and `t ∘ ι`.

## Main results

* `Stacks.Groupoids.GroupoidScheme.mono_of_isOpenImmersion_left`: a morphism of schemes over
  `S` whose underlying morphism is an open immersion is a monomorphism of `CategoryTheory.Over S`.
* `Stacks.Groupoids.GroupoidScheme.lift_comp_subComposable`: the comparison morphism carries
  the lift of a composable pair of arrows of `P` to the lift of the pair of their images.

## Implementation notes

The composability condition is phrased through `subComposable`, which is written as an explicit
`CategoryTheory.Limits.pullback.lift` rather than as `CategoryTheory.Limits.pullback.map` so
that its two projection formulas are `pullback.lift_fst` and `pullback.lift_snd` on the nose.

Both `lift_comp_subComposable` and `SubgroupoidData.comp_lift` take the images of the two
arrows as implicit arguments constrained by equations rather than as the literal composites with
`ι`.  That is what makes them usable in the associativity axiom, where the outer composable pair
has an inner composition in its first slot: the equation supplied there is the lemma itself,
applied to the inner pair.

Every axiom of `Stacks.Groupoids.GroupoidScheme` quantified over test schemes is proved by
cancelling `ι` and invoking the corresponding ambient axiom at the test arrow `f ≫ ι`; the two
unquantified compatibilities `source_comp` and `target_comp` have no mono to cancel and are
computed directly from the ambient ones through the projection formulas for `subComposable`.

## References

* [Stacks Project, Tag 0231](https://stacks.math.columbia.edu/tag/0231)
* [Stacks Project, Tag 04RK](https://stacks.math.columbia.edu/tag/04RK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace Stacks.Groupoids.GroupoidScheme

variable {S : Scheme.{u}}

/-- A morphism of schemes over `S` whose underlying morphism of schemes is an open immersion is
a monomorphism of `CategoryTheory.Over S`: an open immersion is a monomorphism of schemes, and
the forgetful functor is faithful, so it reflects monomorphisms. -/
theorem mono_of_isOpenImmersion_left {X Y : Over S} (f : X ⟶ Y)
    (hf : IsOpenImmersion f.left) : Mono f := by
  have : Mono f.left := hf.mono
  exact (Over.forget S).mono_of_mono_map (show Mono ((Over.forget S).map f) from this)

variable (H : GroupoidScheme S) {P : Over S} (ι : P ⟶ H.arrows)

/-- The comparison morphism from the scheme of pairs of arrows of `P` composable for the
restricted source and target to the scheme of composable pairs of the ambient groupoid. -/
def subComposable : pullback (ι ≫ H.source) (ι ≫ H.target) ⟶ pullback H.source H.target :=
  pullback.lift (pullback.fst (ι ≫ H.source) (ι ≫ H.target) ≫ ι)
    (pullback.snd (ι ≫ H.source) (ι ≫ H.target) ≫ ι)
    (by rw [Category.assoc, Category.assoc]; exact pullback.condition)

/-- The first projection of `subComposable` is the first projection followed by `ι`. -/
@[simp]
theorem subComposable_fst :
    subComposable H ι ≫ pullback.fst H.source H.target =
      pullback.fst (ι ≫ H.source) (ι ≫ H.target) ≫ ι :=
  pullback.lift_fst _ _ _

/-- The second projection of `subComposable` is the second projection followed by `ι`. -/
@[simp]
theorem subComposable_snd :
    subComposable H ι ≫ pullback.snd H.source H.target =
      pullback.snd (ι ≫ H.source) (ι ≫ H.target) ≫ ι :=
  pullback.lift_snd _ _ _

/-- The comparison morphism carries the lift of a composable pair of arrows of `P` to the lift
of the pair of their images. -/
theorem lift_comp_subComposable {T : Over S} (a b : T ⟶ P) {a' b' : T ⟶ H.arrows}
    (ha : a ≫ ι = a') (hb : b ≫ ι = b')
    (w : a ≫ ι ≫ H.source = b ≫ ι ≫ H.target)
    (w' : a' ≫ H.source = b' ≫ H.target) :
    pullback.lift a b w ≫ subComposable H ι = pullback.lift a' b' w' := by
  subst ha
  subst hb
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, subComposable_fst, ← Category.assoc, pullback.lift_fst,
      pullback.lift_fst]
  · rw [Category.assoc, subComposable_snd, ← Category.assoc, pullback.lift_snd,
      pullback.lift_snd]

/-- The source of a composition of two composable generalized arrows is the source of the
arrow applied first. -/
theorem lift_comp_comp_source {T : Over S} (a b : T ⟶ H.arrows)
    (w : a ≫ H.source = b ≫ H.target) :
    (pullback.lift a b w ≫ H.comp) ≫ H.source = b ≫ H.source := by
  rw [Category.assoc, H.source_comp, ← Category.assoc, pullback.lift_snd]

/-- The target of a composition of two composable generalized arrows is the target of the arrow
applied last. -/
theorem lift_comp_comp_target {T : Over S} (a b : T ⟶ H.arrows)
    (w : a ≫ H.source = b ≫ H.target) :
    (pullback.lift a b w ≫ H.comp) ≫ H.target = a ≫ H.target := by
  rw [Category.assoc, H.target_comp, ← Category.assoc, pullback.lift_fst]

/-- The data exhibiting a monomorphism into the arrow scheme of a groupoid scheme as a
subgroupoid on the same object scheme: the composition of composable arrows, the identity and
the inverse all factor through it. -/
structure SubgroupoidData (H : GroupoidScheme S) where
  /-- The scheme of arrows of the subgroupoid. -/
  arrows : Over S
  /-- Its inclusion into the ambient scheme of arrows. -/
  inclusion : arrows ⟶ H.arrows
  /-- The inclusion is a monomorphism. -/
  mono_inclusion : Mono inclusion
  /-- The composition of two arrows of the subgroupoid, composable for the restricted source
  and target. -/
  comp : pullback (inclusion ≫ H.source) (inclusion ≫ H.target) ⟶ arrows
  /-- Composition in the subgroupoid is the ambient composition. -/
  comp_spec : comp ≫ inclusion = subComposable H inclusion ≫ H.comp
  /-- The identity arrow of the subgroupoid. -/
  identity : H.objects ⟶ arrows
  /-- It is the ambient identity. -/
  identity_spec : identity ≫ inclusion = H.identity
  /-- The inverse of an arrow of the subgroupoid. -/
  inverse : arrows ⟶ arrows
  /-- It is the ambient inverse. -/
  inverse_spec : inverse ≫ inclusion = inclusion ≫ H.inverse

namespace SubgroupoidData

attribute [instance] mono_inclusion

variable {H} (D : SubgroupoidData H)

/-- The source of the identity arrow of the subgroupoid is the identity of the objects. -/
theorem identity_comp_source : D.identity ≫ D.inclusion ≫ H.source = 𝟙 H.objects := by
  rw [← Category.assoc, D.identity_spec, H.source_identity]

/-- The target of the identity arrow of the subgroupoid is the identity of the objects. -/
theorem identity_comp_target : D.identity ≫ D.inclusion ≫ H.target = 𝟙 H.objects := by
  rw [← Category.assoc, D.identity_spec, H.target_identity]

/-- The source of the inverse of an arrow of the subgroupoid is the target of the arrow. -/
theorem inverse_comp_source :
    D.inverse ≫ D.inclusion ≫ H.source = D.inclusion ≫ H.target := by
  rw [← Category.assoc, D.inverse_spec, Category.assoc, H.source_inverse]

/-- The target of the inverse of an arrow of the subgroupoid is the source of the arrow. -/
theorem inverse_comp_target :
    D.inverse ≫ D.inclusion ≫ H.target = D.inclusion ≫ H.source := by
  rw [← Category.assoc, D.inverse_spec, Category.assoc, H.target_inverse]

/-- The source of a composition in the subgroupoid is the source of the arrow applied first. -/
theorem comp_comp_source :
    D.comp ≫ D.inclusion ≫ H.source =
      pullback.snd (D.inclusion ≫ H.source) (D.inclusion ≫ H.target) ≫
        D.inclusion ≫ H.source := by
  rw [← Category.assoc, D.comp_spec, Category.assoc, H.source_comp, ← Category.assoc,
      subComposable_snd, Category.assoc]

/-- The target of a composition in the subgroupoid is the target of the arrow applied last. -/
theorem comp_comp_target :
    D.comp ≫ D.inclusion ≫ H.target =
      pullback.fst (D.inclusion ≫ H.source) (D.inclusion ≫ H.target) ≫
        D.inclusion ≫ H.target := by
  rw [← Category.assoc, D.comp_spec, Category.assoc, H.target_comp, ← Category.assoc,
      subComposable_fst, Category.assoc]

/-- The composition of a composable pair of arrows of the subgroupoid, read in the ambient
groupoid, is the ambient composition of the pair of their images. -/
theorem comp_lift {T : Over S} (a b : T ⟶ D.arrows) {a' b' : T ⟶ H.arrows}
    (ha : a ≫ D.inclusion = a') (hb : b ≫ D.inclusion = b')
    (w : a ≫ D.inclusion ≫ H.source = b ≫ D.inclusion ≫ H.target)
    (w' : a' ≫ H.source = b' ≫ H.target) :
    (pullback.lift a b w ≫ D.comp) ≫ D.inclusion = pullback.lift a' b' w' ≫ H.comp := by
  rw [Category.assoc, D.comp_spec, ← Category.assoc,
    lift_comp_subComposable H D.inclusion a b ha hb w w']

/-- The subgroupoid defined by the three factorizations. -/
def groupoid : GroupoidScheme S where
  objects := H.objects
  arrows := D.arrows
  source := D.inclusion ≫ H.source
  target := D.inclusion ≫ H.target
  comp := D.comp
  identity := D.identity
  inverse := D.inverse
  source_identity := D.identity_comp_source
  target_identity := D.identity_comp_target
  source_inverse := D.inverse_comp_source
  target_inverse := D.inverse_comp_target
  source_comp := D.comp_comp_source
  target_comp := D.comp_comp_target
  left_identity := by
    intro T f w
    have ha : (f ≫ (D.inclusion ≫ H.target) ≫ D.identity) ≫ D.inclusion =
        (f ≫ D.inclusion) ≫ H.target ≫ H.identity := by
      simp only [Category.assoc, D.identity_spec]
    have w' : ((f ≫ D.inclusion) ≫ H.target ≫ H.identity) ≫ H.source =
        (f ≫ D.inclusion) ≫ H.target := by
      simp only [Category.assoc, H.source_identity, Category.comp_id]
    refine (cancel_mono D.inclusion).1 ?_
    rw [D.comp_lift _ f ha rfl w w']
    exact H.left_identity T (f ≫ D.inclusion) w'
  right_identity := by
    intro T f w
    have hb : (f ≫ (D.inclusion ≫ H.source) ≫ D.identity) ≫ D.inclusion =
        (f ≫ D.inclusion) ≫ H.source ≫ H.identity := by
      simp only [Category.assoc, D.identity_spec]
    have w' : (f ≫ D.inclusion) ≫ H.source =
        ((f ≫ D.inclusion) ≫ H.source ≫ H.identity) ≫ H.target := by
      simp only [Category.assoc, H.target_identity, Category.comp_id]
    refine (cancel_mono D.inclusion).1 ?_
    rw [D.comp_lift f _ rfl hb w w']
    exact H.right_identity T (f ≫ D.inclusion) w'
  left_inverse := by
    intro T f w
    have ha : (f ≫ D.inverse) ≫ D.inclusion = (f ≫ D.inclusion) ≫ H.inverse := by
      rw [Category.assoc, D.inverse_spec, Category.assoc]
    have w' : ((f ≫ D.inclusion) ≫ H.inverse) ≫ H.source = (f ≫ D.inclusion) ≫ H.target := by
      simp only [Category.assoc, H.source_inverse]
    refine (cancel_mono D.inclusion).1 ?_
    rw [D.comp_lift _ f ha rfl w w', H.left_inverse T (f ≫ D.inclusion) w']
    simp only [Category.assoc, D.identity_spec]
  right_inverse := by
    intro T f w
    have hb : (f ≫ D.inverse) ≫ D.inclusion = (f ≫ D.inclusion) ≫ H.inverse := by
      rw [Category.assoc, D.inverse_spec, Category.assoc]
    have w' : (f ≫ D.inclusion) ≫ H.source = ((f ≫ D.inclusion) ≫ H.inverse) ≫ H.target := by
      simp only [Category.assoc, H.target_inverse]
    refine (cancel_mono D.inclusion).1 ?_
    rw [D.comp_lift f _ rfl hb w w', H.right_inverse T (f ≫ D.inclusion) w']
    simp only [Category.assoc, D.identity_spec]
  assoc := by
    intro T f g h wfg wgh w₁ w₂
    have wfg' : (f ≫ D.inclusion) ≫ H.source = (g ≫ D.inclusion) ≫ H.target := by
      simpa only [Category.assoc] using wfg
    have wgh' : (g ≫ D.inclusion) ≫ H.source = (h ≫ D.inclusion) ≫ H.target := by
      simpa only [Category.assoc] using wgh
    have w₁' : (pullback.lift (f ≫ D.inclusion) (g ≫ D.inclusion) wfg' ≫ H.comp) ≫ H.source =
        (h ≫ D.inclusion) ≫ H.target := by
      rw [lift_comp_comp_source]
      exact wgh'
    have w₂' : (f ≫ D.inclusion) ≫ H.source =
        (pullback.lift (g ≫ D.inclusion) (h ≫ D.inclusion) wgh' ≫ H.comp) ≫ H.target := by
      rw [lift_comp_comp_target]
      exact wfg'
    refine (cancel_mono D.inclusion).1 ?_
    rw [D.comp_lift _ h (D.comp_lift f g rfl rfl wfg wfg') rfl w₁ w₁',
      D.comp_lift f _ rfl (D.comp_lift g h rfl rfl wgh wgh') w₂ w₂']
    exact H.assoc T (f ≫ D.inclusion) (g ≫ D.inclusion) (h ≫ D.inclusion) wfg' wgh' w₁' w₂'

/-- The object scheme of the subgroupoid is that of the ambient groupoid. -/
@[simp] theorem groupoid_objects : D.groupoid.objects = H.objects := rfl

/-- The arrow scheme of the subgroupoid is `D.arrows`. -/
@[simp] theorem groupoid_arrows : D.groupoid.arrows = D.arrows := rfl

/-- The source of the subgroupoid is the ambient source restricted along the inclusion. -/
@[simp] theorem groupoid_source : D.groupoid.source = D.inclusion ≫ H.source := rfl

/-- The target of the subgroupoid is the ambient target restricted along the inclusion. -/
@[simp] theorem groupoid_target : D.groupoid.target = D.inclusion ≫ H.target := rfl

/-- The inclusion of the subgroupoid into the ambient groupoid, as a morphism of groupoid
schemes which is the identity on objects. -/
def inclusionHom : Hom D.groupoid H where
  mapObjects := 𝟙 H.objects
  mapArrows := D.inclusion
  map_source := (Category.comp_id (D.inclusion ≫ H.source)).symm
  map_target := (Category.comp_id (D.inclusion ≫ H.target)).symm
  map_identity := (Category.id_comp H.identity).trans D.identity_spec.symm
  map_comp := fun _ f g w w' => D.comp_lift f g rfl rfl w w'

/-- The inclusion of the subgroupoid is the identity on objects. -/
@[simp] theorem inclusionHom_mapObjects : D.inclusionHom.mapObjects = 𝟙 H.objects := rfl

/-- On arrows, the inclusion of the subgroupoid is `D.inclusion`. -/
@[simp] theorem inclusionHom_mapArrows : D.inclusionHom.mapArrows = D.inclusion := rfl

/-- **Conditions (a) and (b) of Stacks 04RK** from the three factorizations: an open
monomorphism into the arrow scheme through which the composition, the identity and the inverse
factor, and whose restricted source and target are finite, is an open finite subgroupoid. -/
def openFiniteSubgroupoid (hopen : IsOpenImmersion D.inclusion.left)
    (hs : IsFinite (D.inclusion ≫ H.source).left)
    (ht : IsFinite (D.inclusion ≫ H.target).left) :
    OpenFiniteSubgroupoid H where
  subgroupoid := D.groupoid
  objects_eq := rfl
  inclusion := D.inclusionHom
  mapObjects_eq := rfl
  arrows_open := hopen
  source_finite := hs
  target_finite := ht

end SubgroupoidData

end Stacks.Groupoids.GroupoidScheme

end

end
