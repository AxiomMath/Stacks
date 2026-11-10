module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.FamilyPullbackFunctor

/-!
# Independence of the morphism of families in the pullback of descent data

Two morphisms of families of algebraic spaces with the same map of targets induce canonically
isomorphic functors on descent data, even when their maps of index types differ.

## Main definitions

* `AlgebraicGeometry.Space.Descent.PullbackFunctorIso` specifies the canonical comparison by
  the gluing isomorphism of the original datum on every component.

## Main results

* `AlgebraicGeometry.Space.Descent.pullbackFunctorIso` constructs the comparison.

## Implementation notes

The comparison on a component is the unique lift, through the second component pullback square,
of the point obtained by moving the first component projection to the image prescribed by the
second morphism of families. That is what the `component` field of the specification says: the
comparison followed by the second component projection is the gluing isomorphism of the
original datum applied to the first projection, followed by the projection to its second
factor.

## References

* [Stacks Project, Tag 0ADN](https://stacks.math.columbia.edu/tag/0ADN)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Space.Descent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {ι : Type v} {ι' : Type w}
variable {X : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
variable {X' : ι' → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
variable (f : ∀ i, X i ⟶ T) (f' : ∀ i, X' i ⟶ T')
variable (hT : IsAlgebraicSpace B S hS T)
variable (hX : ∀ i, IsAlgebraicSpace B S hS (X i))
variable (hT' : IsAlgebraicSpace B S hS T')
variable (hX' : ∀ i, IsAlgebraicSpace B S hS (X' i))
variable (α β : ι' → ι) (g : T' ⟶ T)
variable (gᵢ : ∀ i, X' i ⟶ X (α i)) (hᵢ : ∀ i, X' i ⟶ X (β i))
variable (commα : ∀ i, gᵢ i ≫ f (α i) = f' i ≫ g)
variable (commβ : ∀ i, hᵢ i ≫ f (β i) = f' i ≫ g)

/-- The natural isomorphism comparing the two pullback functors induced by two morphisms of
families with the same map of targets, specified componentwise by the gluing isomorphism of the
original datum. -/
public structure PullbackFunctorIso
    (Pα : PullbackFunctor f f' hT hX hT' hX' α g gᵢ commα)
    (Pβ : PullbackFunctor f f' hT hX hT' hX' β g hᵢ commβ) where
  /-- The natural isomorphism between the two pullback functors. -/
  iso : Pα.functor ≅ Pβ.functor
  /-- The map comparing a component of the first pulled-back datum with the source of the
  gluing isomorphism of the original datum. -/
  sourceMap (D : DescentData f hT hX) (i : ι') :
    ((pullbackDatum f f' hT hX hT' hX' α gᵢ D g commα).datum.obj i).left ⟶
      (Over.mk (prod.map (structureMap (f (α i)) (D.obj (α i)))
        (𝟙 (Over.mk (f (β i)))))).left.left
  /-- The source of that gluing isomorphism is the pairwise fibre product. -/
  source_eq (D : DescentData f hT hX) (i : ι') :
    (Over.mk (prod.map (structureMap (f (α i)) (D.obj (α i)))
      (𝟙 (Over.mk (f (β i)))))).left.left =
      ((Over.map (f (α i))).obj (D.obj (α i)) ⨯ Over.mk (f (β i))).left
  /-- The target of that gluing isomorphism is the pairwise fibre product. -/
  target_eq (D : DescentData f hT hX) (i : ι') :
    (Over.mk (prod.map (𝟙 (Over.mk (f (α i))))
      (structureMap (f (β i)) (D.obj (β i))))).left.left =
      (Over.mk (f (α i)) ⨯ (Over.map (f (β i))).obj (D.obj (β i))).left
  /-- The first projection of the comparison map is the first component projection. -/
  source_fst (D : DescentData f hT hX) (i : ι') :
    sourceMap D i ≫ eqToHom (source_eq D i) ≫
        ((prod.fst : (Over.map (f (α i))).obj (D.obj (α i)) ⨯
          Over.mk (f (β i)) ⟶ _)).left =
      (pullbackDatum f f' hT hX hT' hX' α gᵢ D g commα).objMap i
  /-- The second projection of the comparison map is the second morphism of families. -/
  source_snd (D : DescentData f hT hX) (i : ι') :
    sourceMap D i ≫ eqToHom (source_eq D i) ≫
        ((prod.snd : (Over.map (f (α i))).obj (D.obj (α i)) ⨯
          Over.mk (f (β i)) ⟶ _)).left =
      ((pullbackDatum f f' hT hX hT' hX' α gᵢ D g commα).datum.obj i).hom ≫ hᵢ i
  /-- On each component the comparison is the gluing isomorphism of the original datum followed
  by the projection to its second factor. -/
  component (D : DescentData f hT hX) (i : ι') :
    ((eqToHom (Pα.obj_eq D).symm).hom i).left ≫
        ((iso.hom.app D).hom i).left ≫
        ((eqToHom (Pβ.obj_eq D)).hom i).left ≫
        (pullbackDatum f f' hT hX hT' hX' β hᵢ D g commβ).objMap i =
      sourceMap D i ≫ (D.gluing (α i) (β i)).hom.left.left ≫
        eqToHom (target_eq D i) ≫
        ((prod.snd : Over.mk (f (α i)) ⨯
          (Over.map (f (β i))).obj (D.obj (β i)) ⟶ _)).left

/-- The `i`-th member of the family of spaces over `T` attached to a descent datum. -/
private abbrev component (D : DescentData f hT hX) (i : ι) : Over T :=
  (Over.map (f i)).obj (D.obj i)

/-- The projection of a pulled-back component onto the original component, as a map of spaces
over `T`. -/
private def componentProjection (D : DescentData f hT hX)
    (P : PulledBackDatum f f' hT hX hT' hX' α gᵢ D) (i : ι') :
    (Over.map g).obj (component f' hT' hX' P.datum i) ⟶ component f hT hX D (α i) :=
  overStructureProjection (f (α i)) (f' i) g (gᵢ i) (commα i) (D.obj (α i)) (P.datum.obj i)
    (P.objMap i) (P.obj_isPullback i)

/-- The component pullback square, as a base-change square for the structure maps. -/
private def componentLift (D : DescentData f hT hX)
    (P : PulledBackDatum f f' hT hX hT' hX' α gᵢ D) (i : ι') :
    BaseChangeSquare (Over.map g) (structureMap (f (α i)) (D.obj (α i)))
      (structureMap (f' i) (P.datum.obj i))
      (componentProjection f f' hT hX hT' hX' α g gᵢ commα D P i)
      (baseProjection f f' α g gᵢ commα i) :=
  overBaseChangeSquare (f (α i)) (f' i) g (gᵢ i) (commα i) (D.obj (α i)) (P.datum.obj i)
    (P.objMap i) (P.obj_isPullback i)

/-- The move operation of a pulled-back datum is the base change of the move operation of the
original datum along the component projections. -/
private lemma projection_move (D : DescentData f hT hX)
    (P : PulledBackDatum f f' hT hX hT' hX' α gᵢ D) {i j : ι'} {Z : Over T'}
    (v : Z ⟶ component f' hT' hX' P.datum i) (y : Z ⟶ Over.mk (f' j)) :
    (Over.map g).map (P.datum.transport.move v y) ≫
        componentProjection f f' hT hX hT' hX' α g gᵢ commα D P j =
      D.transport.move
        ((Over.map g).map v ≫ componentProjection f f' hT hX hT' hX' α g gᵢ commα D P i)
        ((Over.map g).map y ≫ baseProjection f f' α g gᵢ commα j) := by
  have hs : (prod.lift
        ((Over.map g).map v ≫ componentProjection f f' hT hX hT' hX' α g gᵢ commα D P i)
        ((Over.map g).map y ≫ baseProjection f f' α g gᵢ commα j)).left =
      (prod.lift v y).left ≫ P.gluingSourceMap i j := by
    apply Over.prod_left_ext
    · rw [Category.assoc, P.gluingSource_fst, ← Over.comp_left, prod.lift_fst]
      simp only [Over.comp_left, Over.map_map_left, componentProjection,
        overStructureProjection_left]
      rw [← Category.assoc, ← Over.comp_left, prod.lift_fst]
    · rw [Category.assoc, P.gluingSource_snd, ← Over.comp_left, prod.lift_snd]
      simp only [Over.comp_left, Over.map_map_left, baseProjection, overStructureBase_left]
      rw [← Category.assoc, ← Over.comp_left, prod.lift_snd]
  have hg := P.gluing_comm i j
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hg
  apply Over.OverMorphism.ext
  change ((prod.lift v y).left ≫ (P.datum.gluing i j).hom.left.left ≫
      (prod.snd : Over.mk (f' i) ⨯ component f' hT' hX' P.datum j ⟶ _).left) ≫
    P.objMap j = _
  simp only [DescentData.transport_move, Over.comp_left, Category.assoc]
  rw [hs, Category.assoc, reassoc_of% hg, P.gluingTarget_snd]

/-- The comparison map on the `i`-th component, as a map of spaces over `T'`. -/
private def componentComparison (D : DescentData f hT hX)
    (P : PulledBackDatum f f' hT hX hT' hX' α gᵢ D)
    (Q : PulledBackDatum f f' hT hX hT' hX' β hᵢ D) (i : ι') :
    component f' hT' hX' P.datum i ⟶ component f' hT' hX' Q.datum i :=
  (componentLift f f' hT hX hT' hX' β g hᵢ commβ D Q i).lift
    (D.transport.move (componentProjection f f' hT hX hT' hX' α g gᵢ commα D P i)
      ((Over.map g).map (structureMap (f' i) (P.datum.obj i)) ≫
        baseProjection f f' β g hᵢ commβ i))
    (structureMap (f' i) (P.datum.obj i)) (D.transport.move_base _ _)

/-- The comparison map on the `i`-th component, as a map of spaces over `X' i`. -/
private def comparison (D : DescentData f hT hX)
    (P : PulledBackDatum f f' hT hX hT' hX' α gᵢ D)
    (Q : PulledBackDatum f f' hT hX hT' hX' β hᵢ D) (i : ι') :
    P.datum.obj i ⟶ Q.datum.obj i :=
  Over.homMk (componentComparison f f' hT hX hT' hX' α β g gᵢ hᵢ commα commβ D P Q i).left
    (congrArg Over.Hom.left
      ((componentLift f f' hT hX hT' hX' β g hᵢ commβ D Q i).lift_p _ _
        (D.transport.move_base _ _)))

private lemma componentComparison_structureMap (D : DescentData f hT hX)
    (P : PulledBackDatum f f' hT hX hT' hX' α gᵢ D)
    (Q : PulledBackDatum f f' hT hX hT' hX' β hᵢ D) (i : ι') :
    componentComparison f f' hT hX hT' hX' α β g gᵢ hᵢ commα commβ D P Q i ≫
        structureMap (f' i) (Q.datum.obj i) = structureMap (f' i) (P.datum.obj i) :=
  (componentLift f f' hT hX hT' hX' β g hᵢ commβ D Q i).lift_p _ _
    (D.transport.move_base _ _)

private lemma map_comparison (D : DescentData f hT hX)
    (P : PulledBackDatum f f' hT hX hT' hX' α gᵢ D)
    (Q : PulledBackDatum f f' hT hX hT' hX' β hᵢ D) (i : ι') :
    (Over.map (f' i)).map (comparison f f' hT hX hT' hX' α β g gᵢ hᵢ commα commβ D P Q i) =
      componentComparison f f' hT hX hT' hX' α β g gᵢ hᵢ commα commβ D P Q i := by
  apply Over.OverMorphism.ext
  rfl

private lemma comparison_projection (D : DescentData f hT hX)
    (P : PulledBackDatum f f' hT hX hT' hX' α gᵢ D)
    (Q : PulledBackDatum f f' hT hX hT' hX' β hᵢ D) (i : ι') :
    (Over.map g).map ((Over.map (f' i)).map
        (comparison f f' hT hX hT' hX' α β g gᵢ hᵢ commα commβ D P Q i)) ≫
        componentProjection f f' hT hX hT' hX' β g hᵢ commβ D Q i =
      D.transport.move (componentProjection f f' hT hX hT' hX' α g gᵢ commα D P i)
        ((Over.map g).map (structureMap (f' i) (P.datum.obj i)) ≫
          baseProjection f f' β g hᵢ commβ i) := by
  rw [map_comparison]
  exact (componentLift f f' hT hX hT' hX' β g hᵢ commβ D Q i).lift_q _ _
    (D.transport.move_base _ _)

private lemma comp_comparison_projection (D : DescentData f hT hX)
    (P : PulledBackDatum f f' hT hX hT' hX' α gᵢ D)
    (Q : PulledBackDatum f f' hT hX hT' hX' β hᵢ D) {i : ι'} {Z : Over T'}
    (v : Z ⟶ component f' hT' hX' P.datum i) :
    (Over.map g).map (v ≫ (Over.map (f' i)).map
        (comparison f f' hT hX hT' hX' α β g gᵢ hᵢ commα commβ D P Q i)) ≫
        componentProjection f f' hT hX hT' hX' β g hᵢ commβ D Q i =
      D.transport.move
        ((Over.map g).map v ≫ componentProjection f f' hT hX hT' hX' α g gᵢ commα D P i)
        ((Over.map g).map (v ≫ structureMap (f' i) (P.datum.obj i)) ≫
          baseProjection f f' β g hᵢ commβ i) := by
  simp only [Functor.map_comp, Category.assoc, comparison_projection, D.transport.comp_move]

private lemma comparison_move (D : DescentData f hT hX)
    (P : PulledBackDatum f f' hT hX hT' hX' α gᵢ D)
    (Q : PulledBackDatum f f' hT hX hT' hX' β hᵢ D) {i j : ι'} {Z : Over T'}
    (v : Z ⟶ component f' hT' hX' P.datum i) (y : Z ⟶ Over.mk (f' j)) :
    Q.datum.transport.move (v ≫ (Over.map (f' i)).map
        (comparison f f' hT hX hT' hX' α β g gᵢ hᵢ commα commβ D P Q i)) y =
      P.datum.transport.move v y ≫ (Over.map (f' j)).map
        (comparison f f' hT hX hT' hX' α β g gᵢ hᵢ commα commβ D P Q j) := by
  refine (componentLift f f' hT hX hT' hX' β g hᵢ commβ D Q j).hom_ext _ _ ?_ ?_
  · rw [projection_move, comp_comparison_projection, comp_comparison_projection,
      projection_move, P.datum.transport.move_base, D.transport.move_comp,
      D.transport.move_comp]
  · rw [Q.datum.transport.move_base, Category.assoc, map_comparison,
      componentComparison_structureMap, P.datum.transport.move_base]

/-- The comparison morphism of descent data. -/
private def comparisonHom (D : DescentData f hT hX)
    (P : PulledBackDatum f f' hT hX hT' hX' α gᵢ D)
    (Q : PulledBackDatum f f' hT hX hT' hX' β hᵢ D) : P.datum ⟶ Q.datum :=
  DescentData.homOfMove
    (fun i ↦ comparison f f' hT hX hT' hX' α β g gᵢ hᵢ commα commβ D P Q i)
    (fun v y ↦ (comparison_move f f' hT hX hT' hX' α β g gᵢ hᵢ commα commβ D P Q v y).symm)

private lemma comparison_comp (D : DescentData f hT hX)
    (P : PulledBackDatum f f' hT hX hT' hX' α gᵢ D)
    (Q : PulledBackDatum f f' hT hX hT' hX' β hᵢ D) (i : ι') :
    comparison f f' hT hX hT' hX' α β g gᵢ hᵢ commα commβ D P Q i ≫
      comparison f f' hT hX hT' hX' β α g hᵢ gᵢ commβ commα D Q P i = 𝟙 _ := by
  refine Over.map_injective (f' i) ?_
  rw [Functor.map_comp, CategoryTheory.Functor.map_id]
  refine (componentLift f f' hT hX hT' hX' α g gᵢ commα D P i).hom_ext _ _ ?_ ?_
  · rw [comp_comparison_projection, comparison_projection, structureMap_naturality,
      D.transport.move_comp,
      ← (componentLift f f' hT hX hT' hX' α g gᵢ commα D P i).square,
      D.transport.move_self]
    simp
  · simp [structureMap_naturality]

/-- The comparison isomorphism of descent data. -/
private def comparisonIso (D : DescentData f hT hX)
    (P : PulledBackDatum f f' hT hX hT' hX' α gᵢ D)
    (Q : PulledBackDatum f f' hT hX hT' hX' β hᵢ D) : P.datum ≅ Q.datum where
  hom := comparisonHom f f' hT hX hT' hX' α β g gᵢ hᵢ commα commβ D P Q
  inv := comparisonHom f f' hT hX hT' hX' β α g hᵢ gᵢ commβ commα D Q P
  hom_inv_id := DescentData.Hom.ext
    (funext (comparison_comp f f' hT hX hT' hX' α β g gᵢ hᵢ commα commβ D P Q))
  inv_hom_id := DescentData.Hom.ext
    (funext (comparison_comp f f' hT hX hT' hX' β α g hᵢ gᵢ commβ commα D Q P))

private lemma comparison_naturality {D E : DescentData f hT hX} (φ : D ⟶ E)
    (P : PulledBackDatum f f' hT hX hT' hX' α gᵢ D)
    (Q : PulledBackDatum f f' hT hX hT' hX' β hᵢ D)
    (R : PulledBackDatum f f' hT hX hT' hX' α gᵢ E)
    (U : PulledBackDatum f f' hT hX hT' hX' β hᵢ E)
    (m : P.datum ⟶ R.datum) (n : Q.datum ⟶ U.datum)
    (hm : ∀ i, (Over.map g).map ((Over.map (f' i)).map (m.hom i)) ≫
      componentProjection f f' hT hX hT' hX' α g gᵢ commα E R i =
      componentProjection f f' hT hX hT' hX' α g gᵢ commα D P i ≫
        (Over.map (f (α i))).map (φ.hom (α i)))
    (hn : ∀ i, (Over.map g).map ((Over.map (f' i)).map (n.hom i)) ≫
      componentProjection f f' hT hX hT' hX' β g hᵢ commβ E U i =
      componentProjection f f' hT hX hT' hX' β g hᵢ commβ D Q i ≫
        (Over.map (f (β i))).map (φ.hom (β i))) :
    m ≫ comparisonHom f f' hT hX hT' hX' α β g gᵢ hᵢ commα commβ E R U =
      comparisonHom f f' hT hX hT' hX' α β g gᵢ hᵢ commα commβ D P Q ≫ n := by
  apply DescentData.Hom.ext
  funext i
  refine Over.map_injective (f' i) ?_
  change (Over.map (f' i)).map (m.hom i ≫
      comparison f f' hT hX hT' hX' α β g gᵢ hᵢ commα commβ E R U i) =
    (Over.map (f' i)).map (
      comparison f f' hT hX hT' hX' α β g gᵢ hᵢ commα commβ D P Q i ≫ n.hom i)
  rw [Functor.map_comp, Functor.map_comp]
  refine (componentLift f f' hT hX hT' hX' β g hᵢ commβ E U i).hom_ext _ _ ?_ ?_
  · rw [comp_comparison_projection, hm, structureMap_naturality,
      ← DescentData.move_naturality φ]
    simp only [Functor.map_comp, Category.assoc, hn]
    rw [← Category.assoc, comparison_projection]
  · simp [structureMap_naturality]

/-- The canonical natural isomorphism between the pullback functors induced by two morphisms of
families with the same map of targets. -/
@[stacks 0ADN "family_map_independence"]
public def pullbackFunctorIso :
    PullbackFunctorIso f f' hT hX hT' hX' α β g gᵢ hᵢ commα commβ
      (pullbackFunctor f f' hT hX hT' hX' α g gᵢ commα)
      (pullbackFunctor f f' hT hX hT' hX' β g hᵢ commβ) := private_decl% (by
  refine
    { iso := NatIso.ofComponents
        (fun D ↦ comparisonIso f f' hT hX hT' hX' α β g gᵢ hᵢ commα commβ D
          (pullbackDatum f f' hT hX hT' hX' α gᵢ D g commα)
          (pullbackDatum f f' hT hX hT' hX' β hᵢ D g commβ)) ?_
      sourceMap := fun D i ↦ (prod.lift
        (componentProjection f f' hT hX hT' hX' α g gᵢ commα D
          (pullbackDatum f f' hT hX hT' hX' α gᵢ D g commα) i)
        ((Over.map g).map (structureMap (f' i)
            ((pullbackDatum f f' hT hX hT' hX' α gᵢ D g commα).datum.obj i)) ≫
          baseProjection f f' β g hᵢ commβ i)).left
      source_eq := fun _ _ ↦ rfl
      target_eq := fun _ _ ↦ rfl
      source_fst := ?_
      source_snd := ?_
      component := ?_ }
  · intro D E φ
    exact comparison_naturality f f' hT hX hT' hX' α β g gᵢ hᵢ commα commβ φ _ _ _ _
      ((pullbackFunctor f f' hT hX hT' hX' α g gᵢ commα).functor.map φ)
      ((pullbackFunctor f f' hT hX hT' hX' β g hᵢ commβ).functor.map φ)
      (fun i ↦ Over.OverMorphism.ext
        ((pullbackFunctor f f' hT hX hT' hX' α g gᵢ commα).map D E φ i).symm)
      (fun i ↦ Over.OverMorphism.ext
        ((pullbackFunctor f f' hT hX hT' hX' β g hᵢ commβ).map D E φ i).symm)
  · intro D i
    simp only [eqToHom_refl, Category.id_comp]
    rw [← Over.comp_left, prod.lift_fst]
    rfl
  · intro D i
    simp only [eqToHom_refl, Category.id_comp]
    rw [← Over.comp_left, prod.lift_snd]
    rfl
  · intro D i
    have hc := congrArg Over.Hom.left
      (comparison_projection f f' hT hX hT' hX' α β g gᵢ hᵢ commα commβ D
        (pullbackDatum f f' hT hX hT' hX' α gᵢ D g commα)
        (pullbackDatum f f' hT hX hT' hX' β hᵢ D g commβ) i)
    change (comparison f f' hT hX hT' hX' α β g gᵢ hᵢ commα commβ D
      (pullbackDatum f f' hT hX hT' hX' α gᵢ D g commα)
      (pullbackDatum f f' hT hX hT' hX' β hᵢ D g commβ) i).left ≫
      (pullbackDatum f f' hT hX hT' hX' β hᵢ D g commβ).objMap i = _
    simpa only [DescentData.transport_move, Over.comp_left, Over.map_map_left,
      componentProjection, overStructureProjection_left, Over.homMk_left, eqToHom_refl,
      Category.id_comp] using hc)

end AlgebraicGeometry.Space.Descent

end
