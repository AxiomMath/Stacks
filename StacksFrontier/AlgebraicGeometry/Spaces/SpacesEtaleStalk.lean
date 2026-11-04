module

public import Mathlib.CategoryTheory.Limits.Final.Type
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleComparison

/-!
# Stalks of presheaves on the spaces-étale site

Let `x` be a geometric point of an algebraic space `X` over `S`. The stalk at `x` of a
presheaf on the *small* étale site of `X` is the colimit of its sections over the small étale
neighbourhoods of `x` (Stacks 04JY). A presheaf on the *spaces*-étale site of `X` has a
larger diagram available: its sections over all étale neighbourhoods of `x`, in the sense of
Stacks 04JV, where the neighbourhood may be any algebraic space étale over `X`. The two
colimits agree, because the small étale neighbourhoods are initial among all of them.

## Main definitions

* `AlgebraicGeometry.Space.spacesNeighborhoodFunctor` reads an étale neighbourhood of `x` as
  an object of the spaces-étale site of `X`.
* `AlgebraicGeometry.Space.spacesNeighborhoodSections` is the diagram of sections of a
  presheaf on the spaces-étale site over the étale neighbourhoods of `x`, and
  `AlgebraicGeometry.Space.spacesStalkSet` is its set-valued colimit;
  `AlgebraicGeometry.Space.spacesStalkSetFunctor` makes that colimit functorial.

## Main results

* `AlgebraicGeometry.Space.stalkSpacesEtaleEquiv` and
  `AlgebraicGeometry.Space.stalkSpacesEtaleIso`: the stalk at `x` of the restriction of a
  presheaf along the comparison functor of Stacks 03G1 is the colimit of its sections over
  all étale neighbourhoods of `x`, naturally in the presheaf.

## Implementation notes

The identification is stated as a natural isomorphism of set-valued functors on presheaves,
which keeps its compatibility with maps of sheaves and needs no sheaf condition: it holds
already for presheaves on the spaces-étale site, and restriction along the comparison functor
turns a sheaf on the spaces-étale site into one on the small étale site.

Everything rests on one definitional coincidence: composing
`AlgebraicGeometry.Space.EtaleNeighborhood.ofSmallEtale`, which reads a small étale
neighbourhood as an étale neighbourhood, with
`AlgebraicGeometry.Space.spacesNeighborhoodFunctor` gives literally the comparison functor of
Stacks 03G1 applied to the underlying chart — both are the Yoneda algebraic space of the
chart with the chart as its structure morphism. So the two diagrams of sections are the same
functor, and the comparison of the colimits is
`CategoryTheory.Functor.colimitTypePrecomp` along
`AlgebraicGeometry.Space.EtaleNeighborhood.ofSmallEtale`, bijective because that functor is
initial.

## References

* [Stacks Project, Tag 04JZ](https://stacks.math.columbia.edu/tag/04JZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} (x : GeometricPoint B S hS X.1)

/-- A morphism of étale neighbourhoods of `x`, read as a morphism of the spaces-étale site of
`X` between the objects underlying its source and target. -/
def spacesNeighborhoodMap {U V : EtaleNeighborhood B S hS X.1 X.2 x} (f : U ⟶ V) :
    etaleSiteObjectOfNeighborhood B S hS X x U ⟶
      etaleSiteObjectOfNeighborhood B S hS X x V :=
  ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk f.hom)
    (ObjectProperty.hom_ext _ f.over))

/-- The étale neighbourhoods of `x` as a subcategory of the spaces-étale site of `X`: an
étale neighbourhood is an algebraic space étale over `X`, and a morphism of neighbourhoods is
a morphism over `X`. -/
def spacesNeighborhoodFunctor :
    EtaleNeighborhood B S hS X.1 X.2 x ⥤ SpacesEtale B S hS X where
  obj U := etaleSiteObjectOfNeighborhood B S hS X x U
  map f := spacesNeighborhoodMap x f
  map_id := fun _ ↦ ObjectProperty.hom_ext _ rfl
  map_comp := fun _ _ ↦ ObjectProperty.hom_ext _ rfl

/-- Sections of a presheaf on the spaces-étale site of `X` over the étale neighbourhoods of
`x`, directed by restriction to refinements. This is the diagram whose colimit is the stalk
at `x`, and it is the restriction of the presheaf along
`AlgebraicGeometry.Space.spacesNeighborhoodFunctor`. -/
@[implicit_reducible]
def spacesNeighborhoodSections (P : (SpacesEtale B S hS X)ᵒᵖ ⥤ Type w) :
    (EtaleNeighborhood B S hS X.1 X.2 x)ᵒᵖ ⥤ Type w where
  obj U := P.obj (Opposite.op (etaleSiteObjectOfNeighborhood B S hS X x U.unop))
  map f := P.map (spacesNeighborhoodMap x f.unop).op
  map_id U := by
    have h : spacesNeighborhoodMap x (𝟙 U.unop) = 𝟙 _ := ObjectProperty.hom_ext _ rfl
    simp [h]
  map_comp f g := by
    have h : spacesNeighborhoodMap x (g.unop ≫ f.unop) =
        spacesNeighborhoodMap x g.unop ≫ spacesNeighborhoodMap x f.unop :=
      ObjectProperty.hom_ext _ rfl
    simp [h]

/-- The set-valued stalk at `x` of a presheaf on the spaces-étale site of `X`, formed as a
quotient colimit so that no smallness assumption on the category of étale neighbourhoods is
needed. -/
abbrev spacesStalkSet (P : (SpacesEtale B S hS X)ᵒᵖ ⥤ Type w) : Type _ :=
  (spacesNeighborhoodSections x P).ColimitType

/-- The map on spaces-étale stalks induced by a morphism of presheaves. -/
def spacesStalkSetMap {P Q : (SpacesEtale B S hS X)ᵒᵖ ⥤ Type w} (α : P ⟶ Q) :
    spacesStalkSet x P → spacesStalkSet x Q :=
  Quot.map
    (fun p ↦ ⟨p.1, α.app (Opposite.op (etaleSiteObjectOfNeighborhood B S hS X x p.1.unop)) p.2⟩)
    (by
      rintro ⟨j, a⟩ ⟨k, b⟩ ⟨f, h⟩
      refine ⟨f, ?_⟩
      dsimp [spacesNeighborhoodSections] at h ⊢
      rw [h]
      simpa only [types_comp_apply] using
        congrArg (fun g ↦ g a) (α.naturality (spacesNeighborhoodMap x f.unop).op))

/-- The map on spaces-étale stalks sends a germ to the germ of its image. -/
@[simp]
theorem spacesStalkSetMap_ι {P Q : (SpacesEtale B S hS X)ᵒᵖ ⥤ Type w} (α : P ⟶ Q)
    (U : (EtaleNeighborhood B S hS X.1 X.2 x)ᵒᵖ)
    (a : P.obj (Opposite.op (etaleSiteObjectOfNeighborhood B S hS X x U.unop))) :
    spacesStalkSetMap x α ((spacesNeighborhoodSections x P).ιColimitType U a) =
      (spacesNeighborhoodSections x Q).ιColimitType U
        (α.app (Opposite.op (etaleSiteObjectOfNeighborhood B S hS X x U.unop)) a) := rfl

/-- The set-valued spaces-étale stalk at `x` is functorial in the presheaf, without requiring
the category of étale neighbourhoods to be small at the universe of the values. -/
@[implicit_reducible]
def spacesStalkSetFunctor :
    ((SpacesEtale B S hS X)ᵒᵖ ⥤ Type w) ⥤ Type (max (u + 1) w) where
  obj P := spacesStalkSet x P
  map α := TypeCat.ofHom (spacesStalkSetMap x α)
  map_id P := by
    ext z
    induction z using Quot.inductionOn with
    | _ p => rfl
  map_comp α β := by
    ext z
    induction z using Quot.inductionOn with
    | _ p => rfl

/-- The object of the spaces-étale site underlying the étale neighbourhood of a small étale
neighbourhood `U` is the comparison functor of Stacks 03G1 applied to the chart of `U`: both
are the Yoneda algebraic space of the chart, with the chart as its structure morphism. -/
theorem small_neighborhood_site_obj (U : SmallEtaleNeighborhood x) :
    (spacesNeighborhoodFunctor x).obj ((EtaleNeighborhood.ofSmallEtale X.2 x).obj U) =
      (comparisonFunctor B S hS X).obj U.chart := rfl

/-- **Stacks 04JZ.** The stalk at `x` of a presheaf on the spaces-étale site of `X`,
restricted along the comparison functor of Stacks 03G1, is its colimit over all étale
neighbourhoods of `x`.

The two diagrams of sections are the same functor, by
`AlgebraicGeometry.Space.small_neighborhood_site_obj`, and the comparison of the colimits is
bijective because `AlgebraicGeometry.Space.EtaleNeighborhood.ofSmallEtale` is initial. -/
noncomputable def stalkSpacesEtaleEquiv (P : (SpacesEtale B S hS X)ᵒᵖ ⥤ Type w) :
    stalkSet x ((comparisonFunctor B S hS X).op ⋙ P) ≃ spacesStalkSet x P :=
  Equiv.ofBijective
    (Functor.colimitTypePrecomp (EtaleNeighborhood.ofSmallEtale X.2 x).op
      (P := spacesNeighborhoodSections x P))
    (Functor.bijective_colimitTypePrecomp _ _)

/-- The identification of the two stalks carries the germ of a section over a small étale
neighbourhood to its germ over the corresponding étale neighbourhood. -/
@[simp]
theorem stalkSpacesEtaleEquiv_ι (P : (SpacesEtale B S hS X)ᵒᵖ ⥤ Type w)
    (U : (SmallEtaleNeighborhood x)ᵒᵖ)
    (a : P.obj (Opposite.op ((comparisonFunctor B S hS X).obj U.unop.chart))) :
    stalkSpacesEtaleEquiv x P
        ((SmallEtaleNeighborhood.sections (x := x)
          ((comparisonFunctor B S hS X).op ⋙ P)).ιColimitType U a) =
      (spacesNeighborhoodSections x P).ιColimitType
        (Opposite.op ((EtaleNeighborhood.ofSmallEtale X.2 x).obj U.unop)) a := rfl

/-- **Stacks 04JZ.** The small-site stalk at a geometric point is the colimit of sections
over all étale algebraic-space neighbourhoods of that point, naturally in the presheaf on the
spaces-étale site. -/
@[stacks 04JZ]
noncomputable def stalkSpacesEtaleIso :
    ((Functor.whiskeringLeft (SmallEtale B S hS X.1)ᵒᵖ (SpacesEtale B S hS X)ᵒᵖ
        (Type w)).obj (comparisonFunctor B S hS X).op ⋙ stalkSetFunctor x) ≅
      spacesStalkSetFunctor x :=
  NatIso.ofComponents (fun P ↦ (stalkSpacesEtaleEquiv x P).toIso) <| by
    intro P Q α
    ext z
    obtain ⟨j, a, rfl⟩ :=
      (SmallEtaleNeighborhood.sections (x := x)
        ((comparisonFunctor B S hS X).op ⋙ P)).ιColimitType_jointly_surjective z
    rfl

end AlgebraicGeometry.Space

end
