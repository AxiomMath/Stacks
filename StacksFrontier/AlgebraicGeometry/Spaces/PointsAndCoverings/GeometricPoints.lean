module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite

/-!
# Geometric points of an algebraic space and their étale neighbourhoods

A *geometric point* of an algebraic space over `S` is a field-valued point whose field is
algebraically closed; it lies over the point of the space which is its equivalence class.
An *étale neighbourhood* of a geometric point is an étale algebraic space over the space
together with a lift of that very geometric point, and a morphism of étale neighbourhoods
is a morphism over the space preserving the lift. Every étale neighbourhood is refined by
one whose underlying algebraic space is a scheme.

## Main definitions

* `AlgebraicGeometry.Space.GeometricPoint` is a geometric point, with
  `AlgebraicGeometry.Space.GeometricPoint.image` its point of the space and
  `AlgebraicGeometry.Space.GeometricPoint.LiesOver` the condition of lying over a given
  point.
* `AlgebraicGeometry.Space.EtaleNeighborhood` is an étale neighbourhood of a geometric
  point and `AlgebraicGeometry.Space.EtaleNeighborhood.Hom` a morphism of such.

## Main results

* Étale neighbourhoods of a fixed geometric point form a category, with identity and
  composition induced by the corresponding morphisms of algebraic spaces.
* `AlgebraicGeometry.Space.exists_scheme_refinement`: every étale neighbourhood receives a
  morphism from one whose underlying algebraic space is representable.

## Implementation notes

The definitions are made for an arbitrary presheaf on the big fppf site over `S`, and so in
particular for an algebraic space. A field-valued point already carries the structure
morphism to the base and the section defining the morphism to the space, so a geometric
point is a transparent subtype of `AlgebraicGeometry.Space.FieldValuedPoint` and the
quotient API for points applies to it unchanged; its image and the lying-over condition are
likewise abbreviations.

The lift carried by an étale neighbourhood is a section over the object of the site
underlying the fixed geometric point, hence has exactly the same source as that point, and
the field `point_comp` is the commuting triangle of the source definition.

The refinement is produced from an atlas of the neighbourhood: because the geometric
point's field is algebraically closed, the base change of a surjective étale atlas along
the lift has a section, and that section exhibits the atlas object as a representable étale
neighbourhood mapping to the given one. Composing the atlas with the structure morphism
stays étale by `AlgebraicGeometry.Space.isEtale_comp`, and its source is an algebraic space
by `AlgebraicGeometry.isAlgebraicSpace_yoneda`.

## References

* [Stacks Project, Tag 0486](https://stacks.math.columbia.edu/tag/0486)
* [Stacks Project, Tag 04JV](https://stacks.math.columbia.edu/tag/04JV)
* [Stacks Project, Tag 04JW](https://stacks.math.columbia.edu/tag/04JW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- A morphism from the spectrum of an algebraically closed field to a presheaf over a scheme.
For an algebraic space this is a geometric point. -/
@[stacks 0486 "part (1): geometric point"]
abbrev GeometricPoint (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Type (u + 1) :=
  {p : FieldValuedPoint B S hS F // IsAlgClosed p.carrier}

/-- The point of the algebraic space represented by a geometric point. -/
@[stacks 0486 "part (2): image point"]
abbrev GeometricPoint.image {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : GeometricPoint B S hS F) :
    points B S hS F := p.val.class B S hS F

/-- A geometric point lies over its image point in the underlying point set. -/
@[stacks 0486 "part (2): lying over a point"]
abbrev GeometricPoint.LiesOver {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : GeometricPoint B S hS F)
    (x : points B S hS F) : Prop := p.image = x

/-- An étale neighbourhood of a geometric point of an algebraic space, with a chosen lift from
the same field spectrum as the given geometric point. -/
@[stacks 04JV "part (1): étale neighborhoods", sga "4½ Arcata 2.3.1" "étale neighbourhood"]
structure EtaleNeighborhood (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (_hF : IsAlgebraicSpace B S hS F)
    (x : GeometricPoint B S hS F) where
  /-- The algebraic space underlying the neighborhood. -/
  space : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- The source is an algebraic space. -/
  isAlgebraicSpace : IsAlgebraicSpace B S hS space
  /-- The structure map to the fixed algebraic space. -/
  toBase : space ⟶ F
  /-- The structure map is étale. -/
  etale_toBase : IsEtale B S hS toBase
  /-- The lift of the geometric point from its fixed field spectrum. -/
  point : space.obj (Opposite.op x.val.siteObject)
  /-- The lift maps to the original geometric point. -/
  point_comp : toBase.app (Opposite.op x.val.siteObject) point = x.val.value

namespace EtaleNeighborhood

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {hF : IsAlgebraicSpace B S hS F} {x : GeometricPoint B S hS F}

/-- A map of étale neighbourhoods over the fixed algebraic space which carries the chosen lift
to the chosen lift. -/
@[ext, stacks 04JV "part (2): morphisms of étale neighborhoods"]
structure Hom (U V : EtaleNeighborhood B S hS F hF x) where
  /-- The underlying morphism of algebraic spaces. -/
  hom : U.space ⟶ V.space
  /-- The map is over the fixed algebraic space. -/
  over : hom ≫ V.toBase = U.toBase
  /-- The map preserves the chosen geometric point. -/
  point_comp : hom.app (Opposite.op x.val.siteObject) U.point = V.point

/-- Étale neighbourhoods of a geometric point form a category, with morphisms the maps of
étale neighbourhoods. -/
instance : Category (EtaleNeighborhood B S hS F hF x) where
  Hom := Hom
  id U := { hom := 𝟙 U.space, over := by simp, point_comp := by simp }
  comp f g :=
    { hom := f.hom ≫ g.hom
      over := by simp only [Category.assoc, g.over, f.over]
      point_comp := by
        simp only [NatTrans.comp_app, types_comp_apply, f.point_comp, g.point_comp] }
  id_comp f := by ext; simp
  comp_id f := by ext; simp
  assoc f g h := by ext; simp

/-- The underlying morphism of the identity of an étale neighbourhood is the identity of its
algebraic space. -/
@[simp] theorem id_hom (U : EtaleNeighborhood B S hS F hF x) :
    Hom.hom (𝟙 U) = 𝟙 U.space := rfl

/-- The underlying morphism of a composite of maps of étale neighbourhoods is the composite of
the underlying morphisms. -/
@[simp] theorem comp_hom {U V W : EtaleNeighborhood B S hS F hF x}
    (f : U ⟶ V) (g : V ⟶ W) : Hom.hom (f ≫ g) = f.hom ≫ g.hom := rfl

end EtaleNeighborhood

/-- A surjective étale morphism to the spectrum of an algebraically closed field has a
section: the fibre over the unique point is nonempty, and an étale morphism of schemes factors
through any point of its source lying over a separably closed field. -/
theorem exists_section_of_surjective_etale_spec
    (k : Type u) [Field k] [IsAlgClosed k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) [Etale f] [Surjective f] :
    ∃ s : Spec (.of k) ⟶ Y, s ≫ f = 𝟙 _ := by
  obtain ⟨y, _⟩ := f.surjective (IsLocalRing.closedPoint k)
  obtain ⟨s, hs, _⟩ := Scheme.exists_fac_of_etale_of_isSepClosed f (𝟙 _) y (by subsingleton)
  exact ⟨s, by simpa using hs⟩

/-- Every étale neighbourhood of a geometric point admits a refinement by a scheme. -/
@[stacks 04JW "scheme_refinement"]
theorem exists_scheme_refinement (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F)
    (x : GeometricPoint B S hS F)
    (U : EtaleNeighborhood B S hS F hF x) :
    ∃ (U' : EtaleNeighborhood B S hS F hF x),
      ∃ (_f : U' ⟶ U), U'.space.IsRepresentable := by
  obtain ⟨V, atlas, hatlas_surjective, hatlas_etale⟩ := U.isAlgebraicSpace.exists_atlas
  let P := x.val.siteObject B S hS F
  let g : yoneda.obj P ⟶ U.space := yonedaEquiv.symm U.point
  let hrep := hatlas_surjective.1
  let snd := hrep.snd g
  let fst := hrep.fst g
  have hpb : IsPullback fst (yoneda.map snd) atlas g := hrep.isPullback g
  have _ : Surjective ((BigFppfOver.toScheme B S hS).map snd) :=
    hatlas_surjective.property_snd g
  have _ : Etale ((BigFppfOver.toScheme B S hS).map snd) :=
    hatlas_etale.property g fst snd hpb
  have _ : IsAlgClosed x.val.carrier := x.property
  obtain ⟨sec, hsec⟩ := exists_section_of_surjective_etale_spec x.val.carrier
    ((BigFppfOver.toScheme B S hS).map snd)
  let secInclusion : B.inclusion.obj P.left ⟶ B.inclusion.obj (hrep.pullback g).left := sec
  change secInclusion ≫ B.inclusion.map snd.left = 𝟙 _ at hsec
  have hleft : B.inclusion.preimage secInclusion ≫ snd.left = 𝟙 P.left := by
    apply B.inclusion.map_injective
    simpa only [Functor.map_comp, B.inclusion.map_preimage, B.inclusion.map_id] using hsec
  let secOver : P ⟶ hrep.pullback g :=
    Over.homMk (B.inclusion.preimage secInclusion) (by
      rw [← Over.w snd, ← Category.assoc, hleft, Category.id_comp])
  have hsecOver : secOver ≫ snd = 𝟙 P := by
    apply Over.OverMorphism.ext
    simpa [secOver] using hleft
  let toV : P ⟶ V := secOver ≫ yoneda.preimage fst
  let pointV : (yoneda.obj V).obj (Opposite.op P) := yonedaEquiv (yoneda.map toV)
  have hpointV : atlas.app (Opposite.op P) pointV = U.point := by
    have hcomp : yoneda.map toV ≫ atlas = g := by
      calc
        yoneda.map toV ≫ atlas = yoneda.map secOver ≫ fst ≫ atlas := by
          simp [toV, Category.assoc]
        _ = yoneda.map secOver ≫ yoneda.map snd ≫ g := by rw [hpb.w]
        _ = yoneda.map (secOver ≫ snd) ≫ g := by simp [Functor.map_comp, Category.assoc]
        _ = g := by simp [hsecOver]
    rw [← yonedaEquiv_comp, hcomp]
    simp [g]
  have hatlas_isEtale : IsEtale B S hS atlas :=
    isEtale_of_presheaf_etale B S hS hatlas_etale
  let U' : EtaleNeighborhood B S hS F hF x :=
    { space := yoneda.obj V
      isAlgebraicSpace := isAlgebraicSpace_yoneda B S hS V
      toBase := atlas ≫ U.toBase
      etale_toBase := isEtale_comp B S hS hatlas_isEtale U.etale_toBase
      point := pointV
      point_comp := by
        show U.toBase.app (Opposite.op P) (atlas.app (Opposite.op P) pointV) = _
        rw [hpointV]
        exact U.point_comp }
  refine ⟨U', ⟨?_, ?_⟩⟩
  · exact { hom := atlas, over := rfl, point_comp := hpointV }
  · infer_instance

end AlgebraicGeometry.Space

end
