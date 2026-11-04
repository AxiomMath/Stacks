module

public import Mathlib.CategoryTheory.Comma.Arrow
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.ActionGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite

/-!
# Flatness and universal openness of the group law of a group algebraic space over a field

Let `S` be a scheme, let `k` be a field over `S`, and let `G` be a group algebraic space over
`Spec k`, in the category of algebraic spaces over `S`. Then the multiplication
`G ×_k G ⟶ G` is flat and universally open.

The group law is the composition of a groupoid in algebraic spaces: `G` acts on the base
`Spec k`, necessarily trivially, and the arrow space of the resulting action groupoid is
`G ×_k Spec k`, which is `G` again, while its composition is multiplication in `G`. The
object space of that groupoid is the spectrum of a field, so its composition is flat and
universally open.

## Main results

* `AlgebraicGeometry.Space.isFlat_mul`: **Stacks 06E0**, second assertion: the multiplication
  of a group algebraic space over a field is flat and universally open.

## Implementation notes

Flatness and universal openness of the composition of a groupoid in algebraic spaces over a
field spectrum are
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.isFlat_comp_of_objects_eq_spec_field`, which this
file only has to transport along the identifications supplied by the action groupoid. Both
properties depend only on the isomorphism class of an arrow (for universal openness this is
`AlgebraicGeometry.Space.universallyOpen_of_arrowIso`), and the transport is written once for
any such property.

A group algebraic space over `Spec k` is a group object in the slice of presheaves over the
algebraic space `AlgebraicGeometry.schemeSpace` of `Spec k`, and the final object of that
slice is its monoidal unit. So the object on which `G` acts is taken to be the monoidal unit,
whose underlying presheaf is the base itself; the action is then the trivial one, and the
arrow space `G ⊗ 𝟙_` of the action groupoid is identified with `G` by the first projection.
The two resulting identifications, of `G ⊗ 𝟙_` with `G` and of the fibre product of the source
and the target with `G ⊗ G`, assemble into an isomorphism of arrows carrying the composition of
the action groupoid to the multiplication of `G`, along which both properties transport.

The identifications of the structure maps of the action groupoid are heterogeneous equalities,
because the construction names the chosen object and arrow spaces rather than replacing them by
isomorphic ones. They are turned into equations by substituting the equalities of the object and
arrow spaces first, after which the two sides of each heterogeneous equality have the same type.

## References

* [Stacks Project, Tag 0444](https://stacks.math.columbia.edu/tag/0444)
* [Stacks Project, Tag 043H](https://stacks.math.columbia.edu/tag/043H)
* [Stacks Project, Tag 06E0](https://stacks.math.columbia.edu/tag/06E0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe v w u

namespace AlgebraicGeometry.Space

/-! ### Products over a terminal object -/

/-- A product with a terminal object is the first factor, through the first projection. -/
private noncomputable def tensorIsoOfIsTerminal {D : Type w} [Category.{v} D]
    [CartesianMonoidalCategory D] {A T : D} (hT : IsTerminal T) : A ⊗ T ≅ A where
  hom := fst A T
  inv := lift (𝟙 A) (hT.from A)
  hom_inv_id := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ (hT.hom_ext _ _)
    simp
  inv_hom_id := by simp

/-- A fibre product over a terminal object is the product. -/
private noncomputable def pullbackIsoTensorOfIsTerminal {D : Type w} [Category.{v} D]
    [CartesianMonoidalCategory D] {A A' T : D} (hT : IsTerminal T) (f : A ⟶ T) (g : A' ⟶ T)
    [HasPullback f g] : pullback f g ≅ A ⊗ A' where
  hom := lift (pullback.fst f g) (pullback.snd f g)
  inv := pullback.lift (fst A A') (snd A A') (hT.hom_ext _ _)
  hom_inv_id := by
    refine pullback.hom_ext ?_ ?_ <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, lift_fst, lift_snd,
        Category.id_comp]
  inv_hom_id := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_ <;>
      simp only [Category.assoc, lift_fst, lift_snd, pullback.lift_fst, pullback.lift_snd,
        Category.id_comp]

/-! ### Transport along an isomorphism of arrows -/

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

/-- Flatness of a morphism of presheaves depends only on the isomorphism class of its arrow:
an isomorphism of arrows turns one commuting square of étale charts into another with the same
underlying morphism of schemes. -/
private theorem isFlat_of_arrowIso {F F' G G' : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    {g : F' ⟶ G'} (e : Arrow.mk f ≅ Arrow.mk g) (hf : IsFlat C S hS f) : IsFlat C S hS g := by
  have hw : e.inv.left ≫ f = g ≫ e.inv.right := Arrow.w e.inv
  intro U V a b h ha hb hab
  refine hf U V (a ≫ e.inv.left) (b ≫ e.inv.right) h
    (MorphismProperty.RespectsIso.postcomp _ e.inv.left a ha)
    (MorphismProperty.RespectsIso.postcomp _ e.inv.right b hb) ?_
  rw [← Category.assoc, hab, Category.assoc, Category.assoc, ← hw]

/-! ### The action groupoid of a group acting on a terminal object -/

/-- The first component of the composition of an action groupoid is multiplication in the
acting group, read along the two projections of the fibre product of composable arrows. -/
private theorem actionComposition_comp_fst (B : AlgebraicSpaces C S hS) (G X : Over B.obj)
    [GrpObj G] [ModObj G X] :
    Stacks.Groupoids.ActionGroupoid.composition G X ≫ fst G X =
      lift (pullback.fst (snd G X) γ[G,X] ≫ fst G X)
        (pullback.snd (snd G X) γ[G,X] ≫ fst G X) ≫ μ[G] :=
  Stacks.Groupoids.ActionGroupoid.composition_fst G X

/-- When a group object acts on a terminal object, the composition of the action groupoid is the
multiplication of the group: the arrow space is the group itself and the fibre product of
composable arrows is the square of the group. -/
private noncomputable def actionCompositionArrowIso (B : AlgebraicSpaces C S hS)
    (G X : Over B.obj) [GrpObj G] [ModObj G X] (hX : IsTerminal X) :
    Arrow.mk (Stacks.Groupoids.ActionGroupoid.composition G X) ≅ Arrow.mk μ[G] :=
  Arrow.isoMk
    (pullbackIsoTensorOfIsTerminal hX (snd G X) γ[G,X] ≪≫
      tensorIso (tensorIsoOfIsTerminal hX) (tensorIsoOfIsTerminal hX))
    (tensorIsoOfIsTerminal hX)
    (by
      dsimp only [Arrow.mk_hom]
      rw [Iso.trans_hom, tensorIso_hom]
      simp only [pullbackIsoTensorOfIsTerminal, tensorIsoOfIsTerminal, lift_map]
      exact (actionComposition_comp_fst B G X).symm)

/-- A property of the composition of an action groupoid, read on the composition morphism of the
action itself. This is where the heterogeneous identifications of the structure maps of
`AlgebraicGeometry.Space.ActionGroupoidConstruction` are discharged: substituting the equalities
of the object and the arrow space makes the two sides of each of them have the same type. -/
private theorem actionComposition_of_comp (P : MorphismProperty ((BigFppfOver C S hS)ᵒᵖ ⥤ Type u))
    (B : AlgebraicSpaces C S hS) (G X : Over B.obj)
    [GrpObj G] [ModObj G X] (hG : IsAlgebraicSpace C S hS G.left)
    (hX : IsAlgebraicSpace C S hS X.left) (R : GroupoidInAlgebraicSpaces C S hS B)
    (iso : pullback (snd G X).left γ[G,X].left ≅ (pullback (snd G X) γ[G,X]).left)
    (objects_eq : R.objects = ⟨X.left, hX⟩)
    (arrows_eq : R.arrows = AlgebraicSpaces.fiberProduct C S hS
      (ObjectProperty.homMk G.hom : (⟨G.left, hG⟩ : AlgebraicSpaces C S hS) ⟶ B)
      (ObjectProperty.homMk X.hom : (⟨X.left, hX⟩ : AlgebraicSpaces C S hS) ⟶ B))
    (source_eq : HEq R.source.hom (snd G X).left)
    (target_eq : HEq R.target.hom γ[G,X].left)
    (comp_eq : HEq R.comp.hom (iso.hom ≫ (Stacks.Groupoids.ActionGroupoid.composition G X).left))
    (hflat : P R.comp.hom) :
    P (iso.hom ≫ (Stacks.Groupoids.ActionGroupoid.composition G X).left) := by
  obtain ⟨objects, arrows, objectsToBase, arrowsToBase, source, target, _hsb, _htb, comp,
    _hcb, _hpg⟩ := R
  subst objects_eq arrows_eq
  obtain ⟨sourceHom⟩ := source
  obtain ⟨targetHom⟩ := target
  obtain rfl : sourceHom = (snd G X).left := eq_of_heq source_eq
  obtain rfl : targetHom = γ[G,X].left := eq_of_heq target_eq
  rwa [← eq_of_heq comp_eq]

/-- The multiplication of a group object in the slice over an algebraic space has a property of
morphisms depending only on the isomorphism class of an arrow as soon as the composition of the
groupoid of its action on a terminal object has it. -/
private theorem mul_of_comp (P : MorphismProperty ((BigFppfOver C S hS)ᵒᵖ ⥤ Type u))
    (hP : ∀ {F F' K K' : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ K} {g : F' ⟶ K'},
      (Arrow.mk f ≅ Arrow.mk g) → P f → P g)
    (B : AlgebraicSpaces C S hS) (G X : Over B.obj)
    [GrpObj G] [ModObj G X] (hXterm : IsTerminal X) (hG : IsAlgebraicSpace C S hS G.left)
    (hX : IsAlgebraicSpace C S hS X.left) (H : ActionGroupoidConstruction B G X hG hX)
    (hflat : P H.groupoid.comp.hom) :
    P μ[G].left := by
  have e₁ : Arrow.mk (H.compositionDomainIso.hom ≫
        (Stacks.Groupoids.ActionGroupoid.composition G X).left) ≅
      Arrow.mk (Stacks.Groupoids.ActionGroupoid.composition G X).left :=
    Arrow.isoMk H.compositionDomainIso (Iso.refl _) (by simp)
  have e₂ : Arrow.mk (Stacks.Groupoids.ActionGroupoid.composition G X).left ≅ Arrow.mk μ[G].left :=
    (Over.forget B.obj).mapArrow.mapIso (actionCompositionArrowIso B G X hXterm)
  exact hP (e₁ ≪≫ e₂)
    (actionComposition_of_comp P B G X hG hX H.groupoid H.compositionDomainIso H.objects_eq
      H.arrows_eq H.source_eq H.target_eq H.comp_eq hflat)

/-! ### The group law over a field -/

/-- **Stacks 06E0**, second assertion. For a field `k` over the scheme `S`, the multiplication
of a group algebraic space over `Spec k` is flat and universally open.

The first assertion of the same tag, for the composition of a groupoid in algebraic spaces whose
object space is the spectrum of a field, is
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.isFlat_comp_of_objects_eq_spec_field`. -/
@[stacks 06E0 "second assertion: the group law of a group space over a field",
  sga "3 XVIII 2.2" "special case"]
theorem isFlat_mul {k : Type u} [Field k] (C : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : C.Contains S) (structureMap : Spec (.of k) ⟶ S) (hk : C.Contains (Spec (.of k)))
    (G : GroupAlgebraicSpace C S hS
      (schemeSpace (Over.mk (⟨structureMap⟩ : C.obj hk ⟶ C.obj hS))).obj
      (schemeSpace (Over.mk (⟨structureMap⟩ : C.obj hk ⟶ C.obj hS))).property) :
    IsFlat C S hS μ[G.obj.X].left ∧ UniversallyOpen C S hS μ[G.obj.X].left := by
  let K := schemeSpace (Over.mk (⟨structureMap⟩ : C.obj hk ⟶ C.obj hS))
  let _ : ModObj G.obj.X (𝟙_ (Over K.obj)) := ModObj.trivialAction _ _
  let H := groupoidOfAction K G.obj.X (𝟙_ (Over K.obj)) G.property K.property
  have hcomp := GroupoidInAlgebraicSpaces.isFlat_comp_of_objects_eq_spec_field C S hS
    structureMap hk K H.groupoid H.objects_eq
  exact ⟨mul_of_comp (fun _ _ f ↦ IsFlat C S hS f) isFlat_of_arrowIso K G.obj.X _
      isTerminalTensorUnit G.property K.property H hcomp.1,
    mul_of_comp (fun _ _ f ↦ UniversallyOpen C S hS f) (universallyOpen_of_arrowIso C S hS) K
      G.obj.X _ isTerminalTensorUnit G.property K.property H hcomp.2⟩

end AlgebraicGeometry.Space

end
