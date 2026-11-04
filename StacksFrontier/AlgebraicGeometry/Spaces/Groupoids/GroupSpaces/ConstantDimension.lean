module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ResidueField
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRespectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.ConstantDimensionOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.ActionGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.LocalRingDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite
public import StacksFrontier.AlgebraicGeometry.Spaces.TranscendenceDegreeChart
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ClosedPoint

/-!
# Constant dimension of a group algebraic space over a field

Let `k` be a field and let `G` be a group algebraic space over `Spec k` which is locally of
finite type. Then `G` has the same dimension at every one of its points, so that its dimension
is that common value; and at a point whose transcendence degree over `k` is zero that common
value is the dimension of the local ring there.

A group over a field is the arrow space of a groupoid in algebraic spaces whose object space is
`Spec k`: the group acts on `Spec k`, necessarily trivially, and the arrow space of the
resulting action groupoid is `G ×_k Spec k`, which is `G` again, while the source and the target
of that groupoid are both the structure morphism of `G`. Over the spectrum of a field the arrow
space of such a groupoid has constant dimension.

## Main results

* `AlgebraicGeometry.Space.dimension_eq_dimensionAtPoint_of_groupAlgebraicSpace`: the dimension
  of a group algebraic space locally of finite type over a field is its dimension at every one
  of its points.
* `AlgebraicGeometry.Space.dimension_eq_localRingDimension_of_groupAlgebraicSpace`: at a point
  of transcendence degree zero over the field that dimension is the dimension of the local
  ring.

## Implementation notes

Constant dimension of the arrow space of a groupoid in algebraic spaces over a field spectrum is
`AlgebraicGeometry.Space.dimension_eq_dimensionAtPoint`, which this file only has to transport
along the identifications supplied by the action groupoid.

A group algebraic space over `Spec k` is a group object in the slice of presheaves over the
final algebraic space `AlgebraicGeometry.Space.terminalSpace`, and the final object of that
slice is its monoidal unit. So the object on which `G` acts is taken to be the monoidal unit,
whose underlying presheaf is the base itself; the action is then the trivial one, and the arrow
space `G ⊗ 𝟙_` of the action groupoid is the fibre product of the structure morphism of `G` with
an identity, identified with `G` by the first projection. Both the source and the target of the
action groupoid become the structure morphism of `G` read through that identification, so each
is locally of finite type as soon as the structure morphism is; and the dimension and the
dimension at a point are invariant under an isomorphism of algebraic spaces, the one being
`AlgebraicGeometry.Space.dimension_eq_of_iso` and the other a case of étale invariance.

The identifications of the structure maps of the action groupoid are heterogeneous equalities,
because the construction names the chosen object and arrow spaces rather than replacing them by
isomorphic ones. They are turned into equations by substituting the equalities of the object and
arrow spaces first, after which the two sides of each heterogeneous equality have the same type.

The dimension of the local ring at a point, Stacks 04NA, is the Krull dimension of the local
ring of an étale scheme chart at a point above it, which is what the source writes
`dim 𝒪_{G, ḡ}`. The second statement is the case of a group of the identification of the
dimension at a point of transcendence degree zero with the dimension of the local ring there,
`AlgebraicGeometry.Space.dimensionAtPoint_eq_localRingDimension_of_hasTranscendenceDegreeAt_zero`,
which holds for an arbitrary algebraic space locally of finite type over the spectrum of a
field.

## References

* [Stacks Project, Tag 06FE](https://stacks.math.columbia.edu/tag/06FE)
* [Stacks Project, Tag 06FD](https://stacks.math.columbia.edu/tag/06FD)
* [Stacks Project, Tag 06DZ](https://stacks.math.columbia.edu/tag/06DZ)
* [Stacks Project, Tag 06DX](https://stacks.math.columbia.edu/tag/06DX)
* [Stacks Project, Tag 04NA](https://stacks.math.columbia.edu/tag/04NA)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
* [Stacks Project, Tag 01TE](https://stacks.math.columbia.edu/tag/01TE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe v w u

namespace AlgebraicGeometry.Space

/-! ### Fibre products along an identity -/

/-- A fibre product along an identity is the other factor, through the first projection. -/
private noncomputable def pullbackIdIso {D : Type w} [Category.{v} D] {A T : D} (f : A ⟶ T)
    [HasPullback f (𝟙 T)] : pullback f (𝟙 T) ≅ A where
  hom := pullback.fst f (𝟙 T)
  inv := pullback.lift (𝟙 A) f (by simp)
  hom_inv_id := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp]
      exact pullback.condition.trans (Category.comp_id _)
  inv_hom_id := by rw [pullback.lift_fst]

/-! ### Transport along the identifications of the action groupoid -/

section Transport

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

/-- Being locally of finite type is preserved by precomposition with an isomorphism of the
source. -/
private theorem isLocallyOfFiniteType_iso_comp
    {F F' G : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (e : F ≅ F') (f : F' ⟶ G)
    (hf : IsLocallyOfFiniteType C S hS f) :
    IsLocallyOfFiniteType C S hS (e.hom ≫ f) :=
  let : MorphismProperty.RespectsIso
      (fun ⦃X Y : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u⦄ (φ : X ⟶ Y) =>
        IsLocallyOfFiniteType C S hS φ) :=
    isLocallyOfFiniteType_respectsIso C S hS
  MorphismProperty.RespectsIso.precomp
    (fun ⦃X Y : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u⦄ (φ : X ⟶ Y) =>
      IsLocallyOfFiniteType C S hS φ) e.hom f hf

/-- A morphism of presheaves heterogeneously equal to one locally of finite type, between
presheaves equal to its source and its target, is itself locally of finite type.

Substituting the two equalities of presheaves makes the heterogeneous equality an equation
between morphisms of the same type. -/
private theorem isLocallyOfFiniteType_of_heq
    {F G F' G' : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) (g : F' ⟶ G')
    (hsource : F' = F) (htarget : G' = G) (h : HEq f g)
    (hg : IsLocallyOfFiniteType C S hS g) :
    IsLocallyOfFiniteType C S hS f := by
  subst hsource htarget
  rwa [eq_of_heq h]

/-- Having dimension equal to the dimension at every point transports along an equality of
presheaves. -/
private theorem dimension_eq_dimensionAtPoint_of_eq
    {F F' : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace C S hS F)
    (hF' : IsAlgebraicSpace C S hS F') (h : F = F')
    (hd : ∀ r : points C S hS F,
      dimension C S hS F hF = dimensionAtPoint C S hS F hF r)
    (r : points C S hS F') :
    dimension C S hS F' hF' = dimensionAtPoint C S hS F' hF' r := by
  subst h
  exact hd r

end Transport

/-! ### The dimension of a group over a field -/

/-- **Stacks 06FE, part (1).** A group algebraic space over a field which is locally of finite
type has the same dimension at every one of its points, namely its dimension.

Constant dimension of the arrow space of a groupoid in algebraic spaces whose object space is
the spectrum of a field is `AlgebraicGeometry.Space.dimension_eq_dimensionAtPoint`. -/
@[stacks 06FE "part (1): dimension at every point"]
theorem dimension_eq_dimensionAtPoint_of_groupAlgebraicSpace {k : Type u} [Field k]
    (C : BigFppfSite.{u}) (hk : C.Contains (Spec (.of k)))
    (G : GroupAlgebraicSpace C (Spec (.of k)) hk (terminalSpace C (Spec (.of k)) hk).obj
      (terminalSpace C (Spec (.of k)) hk).property)
    (hG : IsLocallyOfFiniteType C (Spec (.of k)) hk G.obj.X.hom)
    (g : points C (Spec (.of k)) hk G.obj.X.left) :
    dimension C (Spec (.of k)) hk G.obj.X.left G.property =
      dimensionAtPoint C (Spec (.of k)) hk G.obj.X.left G.property g := by
  let B := terminalSpace C (Spec (.of k)) hk
  let X : Over B.obj := 𝟙_ (Over B.obj)
  let _ : ModObj G.obj.X X := ModObj.trivialAction _ _
  let H := groupoidOfAction B G.obj.X X G.property B.property
  -- the arrow space of the action groupoid, and its identification with the group
  have harr : IsAlgebraicSpace C (Spec (.of k)) hk (pullback G.obj.X.hom (𝟙 B.obj)) :=
    isAlgebraicSpace_pullback C (Spec (.of k)) hk G.obj.X.hom (𝟙 B.obj) G.property
      B.property B.property
  let ε := pullbackIdIso G.obj.X.hom
  -- both structure maps of the action groupoid are the structure map of the group
  have hsnd : (snd G.obj.X X).left = ε.hom ≫ G.obj.X.hom :=
    (Category.comp_id (pullback.snd G.obj.X.hom (𝟙 B.obj))).symm.trans
      (pullback.condition (f := G.obj.X.hom) (g := 𝟙 B.obj)).symm
  have hs : IsLocallyOfFiniteType C (Spec (.of k)) hk (snd G.obj.X X).left := by
    rw [hsnd]
    exact isLocallyOfFiniteType_iso_comp ε G.obj.X.hom hG
  have hobj : X.left = H.groupoid.objects.obj :=
    (congrArg (fun Z => Z.obj) H.objects_eq).symm
  have hars : pullback G.obj.X.hom (𝟙 B.obj) = H.groupoid.arrows.obj :=
    (congrArg (fun Z => Z.obj) H.arrows_eq).symm
  have hsrc : IsLocallyOfFiniteType C (Spec (.of k)) hk H.groupoid.source.hom :=
    isLocallyOfFiniteType_of_heq H.groupoid.source.hom (snd G.obj.X X).left hars hobj
      H.source_eq hs
  have htgt : IsLocallyOfFiniteType C (Spec (.of k)) hk H.groupoid.target.hom :=
    isLocallyOfFiniteType_of_heq H.groupoid.target.hom γ[G.obj.X, X].left hars hobj
      H.target_eq hs
  -- constant dimension of the arrow space, read on the group
  calc dimension C (Spec (.of k)) hk G.obj.X.left G.property
      = dimension C (Spec (.of k)) hk (pullback G.obj.X.hom (𝟙 B.obj)) harr :=
        (dimension_eq_of_iso C (Spec (.of k)) hk harr G.property ε).symm
    _ = dimensionAtPoint C (Spec (.of k)) hk (pullback G.obj.X.hom (𝟙 B.obj)) harr
          (pointsMap C (Spec (.of k)) hk G.obj.X.left ε.inv g) :=
        dimension_eq_dimensionAtPoint_of_eq H.groupoid.arrows.property harr hars.symm
          (dimension_eq_dimensionAtPoint C (Spec (.of k)) hk hk (𝟙 (Spec (.of k)))
            H.groupoid H.objects_eq hsrc htgt) _
    _ = dimensionAtPoint C (Spec (.of k)) hk G.obj.X.left G.property g :=
        (dimensionAtPoint_eq_of_isEtale C (Spec (.of k)) hk G.property harr ε.inv
          (isEtale_of_iso C (Spec (.of k)) hk ε.symm) g).symm

/-- **Stacks 06FE, part (2).** At a point of a group algebraic space locally of finite type over
a field whose transcendence degree over that field is zero, the dimension of the group is the
dimension of the local ring. -/
@[stacks 06FE "part (2): dimension of the local ring at a point of transcendence degree zero"]
theorem dimension_eq_localRingDimension_of_groupAlgebraicSpace {k : Type u} [Field k]
    (C : BigFppfSite.{u}) (hk : C.Contains (Spec (.of k)))
    (G : GroupAlgebraicSpace C (Spec (.of k)) hk (terminalSpace C (Spec (.of k)) hk).obj
      (terminalSpace C (Spec (.of k)) hk).property)
    (hG : IsLocallyOfFiniteType C (Spec (.of k)) hk G.obj.X.hom)
    (g : points C (Spec (.of k)) hk G.obj.X.left)
    (htr : HasTranscendenceDegreeAt C (Spec (.of k)) hk G.obj.X.hom g 0) :
    dimension C (Spec (.of k)) hk G.obj.X.left G.property =
      (localRingDimension C (Spec (.of k)) hk g : WithBot ℕ∞) :=
  (dimension_eq_dimensionAtPoint_of_groupAlgebraicSpace C hk G hG g).trans
    (dimensionAtPoint_eq_localRingDimension_of_hasTranscendenceDegreeAt_zero C (Spec (.of k)) hk
      hk (𝟙 (Spec (.of k))) G.property G.obj.X.hom hG g htr)

end AlgebraicGeometry.Space

end
