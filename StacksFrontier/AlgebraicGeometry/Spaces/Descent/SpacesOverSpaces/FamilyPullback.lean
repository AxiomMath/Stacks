module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.DescentTransport

/-!
# Pulling a descent datum back along a morphism of families

A morphism of families of algebraic spaces with fixed targets pulls a descent datum back to a
descent datum. Its components are the fibre products of the original components with the new
family members, and its gluing isomorphisms are the base changes of the original ones.

## Main definitions

* `AlgebraicGeometry.Space.Descent.PulledBackDatum` specifies the component pullback squares
  and the induced comparison maps on pairwise fibre products.
* `AlgebraicGeometry.Space.Descent.pullbackDatum` supplies the pulled-back datum.

## Implementation notes

The gluing specification uses the two maps from a pairwise fibre product to its factors, so
`gluingSourceMap` and `gluingTargetMap` are uniquely the maps induced by the component
pullback projections and the component maps of the morphism of families. The equation
`gluing_comm` says that the new gluing isomorphism is the base change of the old one. The
component pullback squares make the objects canonically isomorphic to the chosen pullbacks.

The gluing isomorphisms of the given datum form a move operation
(`CategoryTheory.FamilyTransport`), whose base change along the component
pullback squares gives gluing isomorphisms satisfying the cocycle condition.

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
variable (α : ι' → ι) (g : T' ⟶ T) (gᵢ : ∀ i, X' i ⟶ X (α i))
variable (comm : ∀ i, gᵢ i ≫ f (α i) = f' i ≫ g)
variable (D : DescentData f hT hX)

/-- The component of the pulled-back datum: the fibre product of the original component with
the new family member. -/
private def pulledComponent (α : ι' → ι) (gᵢ : ∀ i, X' i ⟶ X (α i)) (D : DescentData f hT hX)
    (i : ι') : Over (X' i) :=
  (Over.pullback (gᵢ i)).obj (D.obj (α i))

private abbrev oldComponent (i : ι') : Over T := (Over.map (f (α i))).obj (D.obj (α i))

private abbrev newComponent : ι' → Over T' := fun i ↦
  (Over.map (f' i)).obj (pulledComponent f hT hX α gᵢ D i)

private abbrev oldBase (i : ι') : Over T := Over.mk (f (α i))

private abbrev newBase (i : ι') : Over T' := Over.mk (f' i)

private abbrev oldStructure (i : ι') :
    oldComponent f hT hX α D i ⟶ oldBase f α i :=
  structureMap (f (α i)) (D.obj (α i))

private abbrev newStructure (i : ι') :
    newComponent f f' hT hX α gᵢ D i ⟶ newBase f' i :=
  structureMap (f' i) (pulledComponent f hT hX α gᵢ D i)

/-- The projection of a pulled-back component onto the original component, as a map of spaces
over `T`. -/
private def componentProjection (i : ι') :
    (Over.map g).obj (newComponent f f' hT hX α gᵢ D i) ⟶ oldComponent f hT hX α D i :=
  overStructureProjection (f (α i)) (f' i) g (gᵢ i) (comm i) (D.obj (α i))
    (pulledComponent f hT hX α gᵢ D i) (pullback.fst (D.obj (α i)).hom (gᵢ i))
    (IsPullback.of_hasPullback (D.obj (α i)).hom (gᵢ i)).flip

/-- The component of the morphism of families, as a map of spaces over `T`. -/
def baseProjection (i : ι') :
    (Over.map g).obj (Over.mk (f' i)) ⟶ Over.mk (f (α i)) :=
  overStructureBase (f (α i)) (f' i) g (gᵢ i) (comm i)

/-- The component pullback square, as a base-change square for the structure maps. -/
private def componentLift (i : ι') :
    BaseChangeSquare (Over.map g) (oldStructure f hT hX α D i)
      (newStructure f f' hT hX α gᵢ D i)
      (componentProjection f f' hT hX α g gᵢ comm D i) (baseProjection f f' α g gᵢ comm i) :=
  overBaseChangeSquare (f (α i)) (f' i) g (gᵢ i) (comm i) (D.obj (α i))
    (pulledComponent f hT hX α gᵢ D i) (pullback.fst (D.obj (α i)).hom (gᵢ i))
    (IsPullback.of_hasPullback (D.obj (α i)).hom (gᵢ i)).flip

/-- The move operation of the pulled-back datum: the base change of the move operation of the
original datum, reindexed along the map of index types. -/
private def pulledTransport :
    FamilyTransport (newComponent f f' hT hX α gᵢ D) (newBase f')
      (newStructure f f' hT hX α gᵢ D) :=
  FamilyTransport.baseChange (componentLift f f' hT hX α g gᵢ comm D) (D.transport.comap α)

/-- The comparison of the source of the new gluing isomorphism with the source of the old
one. -/
private def sourceMapCore (i j : ι') :
    (Over.map g).obj (newComponent f f' hT hX α gᵢ D i ⨯ newBase f' j) ⟶
      oldComponent f hT hX α D i ⨯ oldBase f α j :=
  prod.lift
    ((Over.map g).map (prod.fst : newComponent f f' hT hX α gᵢ D i ⨯ newBase f' j ⟶ _) ≫
      componentProjection f f' hT hX α g gᵢ comm D i)
    ((Over.map g).map (prod.snd : newComponent f f' hT hX α gᵢ D i ⨯ newBase f' j ⟶ _) ≫
      baseProjection f f' α g gᵢ comm j)

/-- The comparison of the target of the new gluing isomorphism with the target of the old
one. -/
private def targetMapCore (i j : ι') :
    (Over.map g).obj (newBase f' i ⨯ newComponent f f' hT hX α gᵢ D j) ⟶
      oldBase f α i ⨯ oldComponent f hT hX α D j :=
  prod.lift
    ((Over.map g).map (prod.fst : newBase f' i ⨯ newComponent f f' hT hX α gᵢ D j ⟶ _) ≫
      baseProjection f f' α g gᵢ comm i)
    ((Over.map g).map (prod.snd : newBase f' i ⨯ newComponent f f' hT hX α gᵢ D j ⟶ _) ≫
      componentProjection f f' hT hX α g gᵢ comm D j)

/-- The pulled-back descent datum. -/
private def pulledDatum : DescentData f' hT' hX' where
  obj i := pulledComponent f hT hX α gᵢ D i
  obj_isAlgebraicSpace i := isAlgebraicSpace_pullback B S hS (D.obj (α i)).hom (gᵢ i)
    (D.obj_isAlgebraicSpace (α i)) (hX' i) (hX (α i))
  gluing i j := (pulledTransport f f' hT hX α g gᵢ comm D).gluing i j
  cocycle i j k :=
    FamilyTransport.gluing_cocycle (pulledTransport f f' hT hX α g gᵢ comm D) i j k

/-- A descent datum whose components and gluing isomorphisms are the pullbacks of those of `D`
along a morphism of families of algebraic spaces. -/
public structure PulledBackDatum {ι : Type v} {ι' : Type w}
    {X : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {X' : ι' → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : ∀ i, X i ⟶ T) (f' : ∀ i, X' i ⟶ T') (hT : IsAlgebraicSpace B S hS T)
    (hX : ∀ i, IsAlgebraicSpace B S hS (X i)) (hT' : IsAlgebraicSpace B S hS T')
    (hX' : ∀ i, IsAlgebraicSpace B S hS (X' i)) (α : ι' → ι) (gᵢ : ∀ i, X' i ⟶ X (α i))
    (D : DescentData f hT hX) where
  /-- The pulled-back descent datum. -/
  datum : DescentData f' hT' hX'
  /-- The projection of each component onto the corresponding original component. -/
  objMap (i : ι') : (datum.obj i).left ⟶ (D.obj (α i)).left
  /-- Each component sits in a pullback square over the morphism of families. -/
  obj_isPullback (i : ι') :
    IsPullback (datum.obj i).hom (objMap i) (gᵢ i) (D.obj (α i)).hom
  /-- The source of the new gluing isomorphism is the new pairwise fibre product. -/
  source_eq_new (i j : ι') :
    (Over.mk (prod.map (structureMap (f' i) (datum.obj i))
      (𝟙 (Over.mk (f' j))))).left.left =
      ((Over.map (f' i)).obj (datum.obj i) ⨯ Over.mk (f' j)).left
  /-- The source of the old gluing isomorphism is the old pairwise fibre product. -/
  source_eq_old (i j : ι') :
    (Over.mk (prod.map (structureMap (f (α i)) (D.obj (α i)))
      (𝟙 (Over.mk (f (α j)))))).left.left =
      ((Over.map (f (α i))).obj (D.obj (α i)) ⨯ Over.mk (f (α j))).left
  /-- The target of the new gluing isomorphism is the new pairwise fibre product. -/
  target_eq_new (i j : ι') :
    (Over.mk (prod.map (𝟙 (Over.mk (f' i)))
      (structureMap (f' j) (datum.obj j)))).left.left =
      (Over.mk (f' i) ⨯ (Over.map (f' j)).obj (datum.obj j)).left
  /-- The target of the old gluing isomorphism is the old pairwise fibre product. -/
  target_eq_old (i j : ι') :
    (Over.mk (prod.map (𝟙 (Over.mk (f (α i))))
      (structureMap (f (α j)) (D.obj (α j))))).left.left =
      (Over.mk (f (α i)) ⨯ (Over.map (f (α j))).obj (D.obj (α j))).left
  /-- The comparison map on sources of gluing isomorphisms. -/
  gluingSourceMap (i j : ι') :
    ((Over.map (f' i)).obj (datum.obj i) ⨯ Over.mk (f' j)).left ⟶
      ((Over.map (f (α i))).obj (D.obj (α i)) ⨯ Over.mk (f (α j))).left
  /-- The first projection of the source comparison map is the component projection. -/
  gluingSource_fst : ∀ i j : ι',
    gluingSourceMap i j ≫
        ((prod.fst : (Over.map (f (α i))).obj (D.obj (α i)) ⨯
          Over.mk (f (α j)) ⟶ _)).left =
      ((prod.fst : (Over.map (f' i)).obj (datum.obj i) ⨯ Over.mk (f' j) ⟶ _)).left ≫
        objMap i
  /-- The second projection of the source comparison map is the morphism of families. -/
  gluingSource_snd (i j : ι') :
    gluingSourceMap i j ≫
        ((prod.snd : (Over.map (f (α i))).obj (D.obj (α i)) ⨯
          Over.mk (f (α j)) ⟶ _)).left =
      ((prod.snd : (Over.map (f' i)).obj (datum.obj i) ⨯ Over.mk (f' j) ⟶ _)).left ≫
        gᵢ j
  /-- The comparison map on targets of gluing isomorphisms. -/
  gluingTargetMap (i j : ι') :
    (Over.mk (f' i) ⨯ (Over.map (f' j)).obj (datum.obj j)).left ⟶
      (Over.mk (f (α i)) ⨯ (Over.map (f (α j))).obj (D.obj (α j))).left
  /-- The first projection of the target comparison map is the morphism of families. -/
  gluingTarget_fst (i j : ι') :
    gluingTargetMap i j ≫
        ((prod.fst : Over.mk (f (α i)) ⨯
          (Over.map (f (α j))).obj (D.obj (α j)) ⟶ _)).left =
      ((prod.fst : Over.mk (f' i) ⨯ (Over.map (f' j)).obj (datum.obj j) ⟶ _)).left ≫
        gᵢ i
  /-- The second projection of the target comparison map is the component projection. -/
  gluingTarget_snd (i j : ι') :
    gluingTargetMap i j ≫
        ((prod.snd : Over.mk (f (α i)) ⨯
          (Over.map (f (α j))).obj (D.obj (α j)) ⟶ _)).left =
      ((prod.snd : Over.mk (f' i) ⨯ (Over.map (f' j)).obj (datum.obj j) ⟶ _)).left ≫
        objMap j
  /-- The new gluing isomorphism is the base change of the old one. -/
  gluing_comm (i j : ι') :
    eqToHom (source_eq_new i j) ≫ gluingSourceMap i j ≫
        eqToHom (source_eq_old i j).symm ≫ (D.gluing (α i) (α j)).hom.left.left =
      (datum.gluing i j).hom.left.left ≫ eqToHom (target_eq_new i j) ≫
        gluingTargetMap i j ≫ eqToHom (target_eq_old i j).symm

/-- Pullback of a descent datum along a morphism of families of algebraic spaces. -/
@[stacks 0ADN "family_pullback_datum"]
public def pullbackDatum (g : T' ⟶ T) (comm : ∀ i, gᵢ i ≫ f (α i) = f' i ≫ g) :
    PulledBackDatum f f' hT hX hT' hX' α gᵢ D := private_decl% (by
  refine ⟨pulledDatum f f' hT hX hT' hX' α g gᵢ comm D, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · exact fun i ↦ pullback.fst (D.obj (α i)).hom (gᵢ i)
  · exact fun i ↦ (IsPullback.of_hasPullback (D.obj (α i)).hom (gᵢ i)).flip
  · exact fun _ _ ↦ rfl
  · exact fun _ _ ↦ rfl
  · exact fun _ _ ↦ rfl
  · exact fun _ _ ↦ rfl
  · exact fun i j ↦ (sourceMapCore f f' hT hX α g gᵢ comm D i j).left
  · intro i j
    change ((sourceMapCore f f' hT hX α g gᵢ comm D i j) ≫
        (prod.fst : oldComponent f hT hX α D i ⨯ oldBase f α j ⟶ _)).left =
      (((Over.map g).map (prod.fst :
        newComponent f f' hT hX α gᵢ D i ⨯ newBase f' j ⟶ _) ≫
          componentProjection f f' hT hX α g gᵢ comm D i).left)
    simp [sourceMapCore]
  · intro i j
    change ((sourceMapCore f f' hT hX α g gᵢ comm D i j) ≫
        (prod.snd : oldComponent f hT hX α D i ⨯ oldBase f α j ⟶ _)).left =
      (((Over.map g).map (prod.snd :
        newComponent f f' hT hX α gᵢ D i ⨯ newBase f' j ⟶ _) ≫
          baseProjection f f' α g gᵢ comm j).left)
    simp [sourceMapCore]
  · exact fun i j ↦ (targetMapCore f f' hT hX α g gᵢ comm D i j).left
  · intro i j
    change ((targetMapCore f f' hT hX α g gᵢ comm D i j) ≫
        (prod.fst : oldBase f α i ⨯ oldComponent f hT hX α D j ⟶ _)).left =
      (((Over.map g).map (prod.fst :
        newBase f' i ⨯ newComponent f f' hT hX α gᵢ D j ⟶ _) ≫
          baseProjection f f' α g gᵢ comm i).left)
    simp [targetMapCore]
  · intro i j
    change ((targetMapCore f f' hT hX α g gᵢ comm D i j) ≫
        (prod.snd : oldBase f α i ⨯ oldComponent f hT hX α D j ⟶ _)).left =
      (((Over.map g).map (prod.snd :
        newBase f' i ⨯ newComponent f f' hT hX α gᵢ D j ⟶ _) ≫
          componentProjection f f' hT hX α g gᵢ comm D j).left)
    simp [targetMapCore]
  · intro i j
    change eqToHom rfl ≫ (sourceMapCore f f' hT hX α g gᵢ comm D i j).left ≫
        eqToHom rfl ≫ (D.gluing (α i) (α j)).hom.left.left =
      ((pulledDatum f f' hT hX hT' hX' α g gᵢ comm D).gluing i j).hom.left.left ≫
        eqToHom rfl ≫ (targetMapCore f f' hT hX α g gᵢ comm D i j).left ≫ eqToHom rfl
    simp only [eqToHom_refl, Category.id_comp]
    have h := FamilyTransport.baseChange_gluing
      (componentLift f f' hT hX α g gᵢ comm D) (D.transport.comap α) i j
    rw [FamilyTransport.comap_gluing, DescentData.transport_gluing] at h
    have h' := congrArg Over.Hom.left h.symm
    simpa only [sourceMapCore, targetMapCore, pulledDatum, pulledTransport, newComponent,
      newBase, oldComponent, oldBase, Over.comp_left, Over.map_map_left, Category.id_comp,
      Category.comp_id] using h')

end AlgebraicGeometry.Space.Descent

end
