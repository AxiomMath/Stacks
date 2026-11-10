module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpaces

/-!
# The stabilizer of a groupoid in algebraic spaces

Let `G` be a groupoid in algebraic spaces over `B`, with object space `U` and arrow space `R`.
The morphism `(t, s) : R ⟶ U ×_B U` and the diagonal `U ⟶ U ×_B U` have a fibre product, the
*stabilizer* `S` of `G`: an arrow whose source and target coincide. It is an algebraic space
over `U`, and this file builds it together with the projection of a stabilizer element to its
arrow in `G` and the basic calculus of generalized points of the stabilizer.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.objectPairs`: the square `U ×_B U`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.sourceTarget`: the morphism `(t, s)`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.diagonal`: the diagonal of `U` over `B`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.stabilizerOverBase`: the stabilizer as an
  algebraic space over `S`, and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.stabilizer` the same object read in the slice
  over the object space.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.stabilizerArrow`: the arrow of `G` underlying a
  stabilizer element, and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.stabilizerArrowHom` the arrow underlying a
  generalized point of the stabilizer.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.stabilizerArrow_source` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.stabilizerArrow_target`: the underlying arrow of
  a stabilizer element has both endpoints equal to the point of `U` it lies over.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.stabilizerArrow_condition`: conversely an arrow
  whose two endpoints agree factors through the stabilizer.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.stabilizer_hom_ext`: a generalized point of the
  stabilizer is determined by its underlying arrow.

## Implementation notes

The fibre product is taken in presheaves, where it is again an algebraic space by
**Stacks 02X2**, so the same object serves as an algebraic space over `S` and as an object of
the slice of presheaves over the object presheaf; the two readings are `stabilizerOverBase` and
`stabilizer` and have the same underlying presheaf by definition. Working in the slice is what
makes the group-object API of
`AlgebraicGeometry.Space.overCartesianMonoidalCategory` available, which is how the group
structure of **Stacks 0447** is stated.

`objectPairsSource` and `objectPairsTarget` are the two projections of the square; they are
named rather than inlined because the pullback square of the stabilizer is detected by
composing with them, and the orientation `(t, s)` of `sourceTarget` matters: the first
projection is the target and the second is the source.

## References

* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 043H](https://stacks.math.columbia.edu/tag/043H)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 0447](https://stacks.math.columbia.edu/tag/0447)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- The square of the object space of a groupoid in algebraic spaces over the base. -/
noncomputable abbrev objectPairs (G : GroupoidInAlgebraicSpaces C S hS B) :
    AlgebraicSpaces C S hS :=
  AlgebraicSpaces.fiberProduct C S hS G.objectsToBase G.objectsToBase

/-- The morphism `(t, s)` from the arrow space to the square of the object space. -/
noncomputable def sourceTarget (G : GroupoidInAlgebraicSpaces C S hS B) :
    G.arrows ⟶ objectPairs G :=
  ObjectProperty.homMk (pullback.lift G.target.hom G.source.hom
    (congrArg (fun f : G.arrows ⟶ B => f.hom) (G.target_over.trans G.source_over.symm)))

/-- The diagonal of the object space of a groupoid in algebraic spaces over the base. -/
noncomputable def diagonal (G : GroupoidInAlgebraicSpaces C S hS B) :
    G.objects ⟶ objectPairs G :=
  ObjectProperty.homMk (pullback.lift (𝟙 G.objects.obj) (𝟙 G.objects.obj) (by simp))

/-- The stabilizer of a groupoid in algebraic spaces, as an algebraic space over `S`: the
fibre product of `(t, s)` with the diagonal of the object space. -/
noncomputable abbrev stabilizerOverBase (G : GroupoidInAlgebraicSpaces C S hS B) :
    AlgebraicSpaces C S hS :=
  AlgebraicSpaces.fiberProduct C S hS (sourceTarget G) (diagonal G)

/-- The stabilizer of a groupoid in algebraic spaces, read in the slice over the object
space. -/
noncomputable abbrev stabilizer (G : GroupoidInAlgebraicSpaces C S hS B) :
    Over G.objects.obj :=
  Over.mk (pullback.snd (sourceTarget G).hom (diagonal G).hom)

/-- The arrow of the groupoid underlying a stabilizer element. -/
noncomputable abbrev stabilizerArrow (G : GroupoidInAlgebraicSpaces C S hS B) :
    (stabilizer G).left ⟶ G.arrows.obj :=
  pullback.fst (sourceTarget G).hom (diagonal G).hom

/-- The second projection of the square of the object space, which is the source component. -/
noncomputable def objectPairsSource (G : GroupoidInAlgebraicSpaces C S hS B) :
    objectPairs G ⟶ G.objects :=
  ObjectProperty.homMk (pullback.snd G.objectsToBase.hom G.objectsToBase.hom :
    (AlgebraicSpaces.fiberProduct C S hS G.objectsToBase G.objectsToBase).obj ⟶
      G.objects.obj)

/-- The first projection of the square of the object space, which is the target component. -/
noncomputable def objectPairsTarget (G : GroupoidInAlgebraicSpaces C S hS B) :
    objectPairs G ⟶ G.objects :=
  ObjectProperty.homMk (pullback.fst G.objectsToBase.hom G.objectsToBase.hom :
    (AlgebraicSpaces.fiberProduct C S hS G.objectsToBase G.objectsToBase).obj ⟶
      G.objects.obj)

/-- The source component of `(t, s)` is the source. -/
theorem sourceTarget_source_projection (G : GroupoidInAlgebraicSpaces C S hS B) :
    (sourceTarget G).hom ≫ (objectPairsSource G).hom = G.source.hom := by
  change pullback.lift G.target.hom G.source.hom _ ≫
    pullback.snd G.objectsToBase.hom G.objectsToBase.hom = G.source.hom
  exact pullback.lift_snd G.target.hom G.source.hom _

/-- The target component of `(t, s)` is the target. -/
theorem sourceTarget_target_projection (G : GroupoidInAlgebraicSpaces C S hS B) :
    (sourceTarget G).hom ≫ (objectPairsTarget G).hom = G.target.hom := by
  change pullback.lift G.target.hom G.source.hom _ ≫
    pullback.fst G.objectsToBase.hom G.objectsToBase.hom = G.target.hom
  exact pullback.lift_fst G.target.hom G.source.hom _

/-- Both components of the diagonal are the identity. -/
theorem diagonal_source_projection (G : GroupoidInAlgebraicSpaces C S hS B) :
    (diagonal G).hom ≫ (objectPairsSource G).hom = 𝟙 G.objects.obj := by
  change pullback.lift (𝟙 G.objects.obj) (𝟙 G.objects.obj) _ ≫
    pullback.snd G.objectsToBase.hom G.objectsToBase.hom = 𝟙 G.objects.obj
  exact pullback.lift_snd (𝟙 G.objects.obj) (𝟙 G.objects.obj) _

/-- Both components of the diagonal are the identity. -/
theorem diagonal_target_projection (G : GroupoidInAlgebraicSpaces C S hS B) :
    (diagonal G).hom ≫ (objectPairsTarget G).hom = 𝟙 G.objects.obj := by
  change pullback.lift (𝟙 G.objects.obj) (𝟙 G.objects.obj) _ ≫
    pullback.fst G.objectsToBase.hom G.objectsToBase.hom = 𝟙 G.objects.obj
  exact pullback.lift_fst (𝟙 G.objects.obj) (𝟙 G.objects.obj) _

/-- Composing the underlying arrow of a stabilizer element with `(t, s)` and a component of the
square, whose composite with the diagonal is the identity, gives the point it lies over. -/
private theorem stabilizerArrow_comp_sourceTarget_comp
    (G : GroupoidInAlgebraicSpaces C S hS B) (p : objectPairs G ⟶ G.objects)
    (h : (diagonal G).hom ≫ p.hom = 𝟙 G.objects.obj) :
    stabilizerArrow G ≫ (sourceTarget G).hom ≫ p.hom = (stabilizer G).hom := by
  rw [← Category.assoc, pullback.condition, Category.assoc, h, Category.comp_id]
  rfl

/-- The underlying arrow of a stabilizer element has source the point it lies over. -/
theorem stabilizerArrow_source (G : GroupoidInAlgebraicSpaces C S hS B) :
    stabilizerArrow G ≫ G.source.hom = (stabilizer G).hom := by
  simpa only [sourceTarget_source_projection] using
    stabilizerArrow_comp_sourceTarget_comp G _ (diagonal_source_projection G)

/-- The underlying arrow of a stabilizer element has target the point it lies over. -/
theorem stabilizerArrow_target (G : GroupoidInAlgebraicSpaces C S hS B) :
    stabilizerArrow G ≫ G.target.hom = (stabilizer G).hom := by
  simpa only [sourceTarget_target_projection] using
    stabilizerArrow_comp_sourceTarget_comp G _ (diagonal_target_projection G)

/-- The arrow of the groupoid underlying a generalized point of the stabilizer. -/
noncomputable abbrev stabilizerArrowHom (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : Over G.objects.obj} (f : T ⟶ stabilizer G) : T.left ⟶ G.arrows.obj :=
  f.left ≫ stabilizerArrow G

/-- The arrow underlying a generalized point of the stabilizer has source the structure
morphism of the test object. -/
theorem stabilizerArrowHom_source (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : Over G.objects.obj} (f : T ⟶ stabilizer G) :
    stabilizerArrowHom G f ≫ G.source.hom = T.hom := by
  rw [stabilizerArrowHom, Category.assoc, stabilizerArrow_source, f.w]

/-- The arrow underlying a generalized point of the stabilizer has target the structure
morphism of the test object. -/
theorem stabilizerArrowHom_target (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : Over G.objects.obj} (f : T ⟶ stabilizer G) :
    stabilizerArrowHom G f ≫ G.target.hom = T.hom := by
  rw [stabilizerArrowHom, Category.assoc, stabilizerArrow_target, f.w]

/-- Any two generalized points of the stabilizer over the same test object have composable
underlying arrows. -/
theorem stabilizerArrowHom_composable (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : Over G.objects.obj} (f g : T ⟶ stabilizer G) :
    stabilizerArrowHom G f ≫ G.source.hom = stabilizerArrowHom G g ≫ G.target.hom :=
  (stabilizerArrowHom_source G f).trans (stabilizerArrowHom_target G g).symm

/-- An arrow of the groupoid whose source and target are both a given point of the object
space satisfies the equation defining the stabilizer. -/
theorem stabilizerArrow_condition (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (a : T ⟶ G.arrows.obj)
    (v : T ⟶ G.objects.obj) (hs : a ≫ G.source.hom = v) (ht : a ≫ G.target.hom = v) :
    a ≫ (sourceTarget G).hom = v ≫ (diagonal G).hom := by
  apply pullback.hom_ext
  · change (a ≫ (sourceTarget G).hom) ≫ (objectPairsTarget G).hom =
      (v ≫ (diagonal G).hom) ≫ (objectPairsTarget G).hom
    simpa only [Category.assoc, sourceTarget_target_projection,
      diagonal_target_projection, Category.comp_id] using ht
  · change (a ≫ (sourceTarget G).hom) ≫ (objectPairsSource G).hom =
      (v ≫ (diagonal G).hom) ≫ (objectPairsSource G).hom
    simpa only [Category.assoc, sourceTarget_source_projection,
      diagonal_source_projection, Category.comp_id] using hs

/-- A generalized point of the stabilizer is determined by its underlying arrow. -/
theorem stabilizer_hom_ext (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : Over G.objects.obj} (f g : T ⟶ stabilizer G)
    (h : stabilizerArrowHom G f = stabilizerArrowHom G g) : f = g :=
  Over.OverMorphism.ext (pullback.hom_ext h (f.w.trans g.w.symm))

end AlgebraicGeometry.GroupoidInAlgebraicSpaces
