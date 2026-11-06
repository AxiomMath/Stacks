module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSitePoint
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleStalk

/-!
# A geometric point as a point of the spaces-étale site

A geometric point `x` of an algebraic space `X` over `S` has, on the small étale site of
scheme charts, the functor of lifts `AlgebraicGeometry.Space.geometricFiber`, which is a point
of that site (Stacks 04K0). On the spaces-étale site of `X`, whose objects are the algebraic
spaces étale over `X`, the same prescription gives the functor of lifts
`AlgebraicGeometry.Space.spacesGeometricFiber`, and it too is a point of the site. Its stalk is
the colimit of sections over all étale neighbourhoods of `x` in the sense of Stacks 04JV.

## Main definitions

* `AlgebraicGeometry.Space.spacesGeometricFiber`: the functor of lifts of a geometric point into
  the algebraic spaces étale over `X`.
* `AlgebraicGeometry.Space.spacesFiberElementsEquiv`: its category of elements is the category of
  étale neighbourhoods of the point.
* `AlgebraicGeometry.Space.spacesEtaleSitePoint`: the resulting point of the spaces-étale site.
* `AlgebraicGeometry.Space.spacesEtaleSitePointStalkIso`: its stalk functor is the spaces-étale
  stalk of Stacks 04JZ.

## Main results

* `AlgebraicGeometry.Space.spacesGeometricFiber_jointly_surjective`: a lift of the geometric
  point into an étale algebraic space lifts through every jointly point-surjective family over
  it.

## References

* [Stacks Project, Tag 04K0](https://stacks.math.columbia.edu/tag/04K0)
* [Stacks Project, Tag 04JX](https://stacks.math.columbia.edu/tag/04JX)
* [Stacks Project, Tag 04JZ](https://stacks.math.columbia.edu/tag/04JZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} (x : GeometricPoint B S hS X.1)

/-- The functor of lifts of a geometric point of `X` into the algebraic spaces étale over `X`:
a lift is a section over the field spectrum of `x` whose composite with the structure morphism
is `x` itself. -/
noncomputable def spacesGeometricFiber : SpacesEtale B S hS X ⥤ Type u where
  obj V := {v : ((SpacesEtale.toSpaces B S hS X).obj V).1.obj (Opposite.op x.val.siteObject) //
    ((SpacesEtale.inclusion B S hS X).obj V).hom.hom.app
      (Opposite.op x.val.siteObject) v = x.val.value}
  map {V W} g := TypeCat.ofHom fun v =>
    ⟨((SpacesEtale.toSpaces B S hS X).map g).hom.app (Opposite.op x.val.siteObject) v.1,
      (congrArg (fun k => k.hom.app (Opposite.op x.val.siteObject) v.1)
        (Over.w ((SpacesEtale.inclusion B S hS X).map g))).trans v.2⟩
  map_id V := by ext v; rfl
  map_comp g h := by ext v; rfl

/-- The elements of the fibre functor on the spaces-étale site are the étale neighbourhoods of
the geometric point: an object étale over `X` together with a lift of `x` into it is precisely
an étale neighbourhood in the sense of Stacks 04JV. -/
noncomputable def spacesFiberElementsEquiv :
    (spacesGeometricFiber x).Elements ≌ EtaleNeighborhood B S hS X.1 X.2 x where
  functor :=
    { obj p := etaleNeighborhoodOfSitePoint B S hS X x p.1 p.2.1 p.2.2
      map {p q} g :=
        { hom := ((SpacesEtale.toSpaces B S hS X).map g.1).hom
          over := congrArg (fun k => k.hom) (Over.w ((SpacesEtale.inclusion B S hS X).map g.1))
          point_comp := congrArg Subtype.val g.2 }
      map_id p := EtaleNeighborhood.Hom.ext rfl
      map_comp g h := EtaleNeighborhood.Hom.ext rfl }
  inverse :=
    { obj U := (spacesGeometricFiber x).elementsMk (etaleSiteObjectOfNeighborhood B S hS X x U)
        ⟨U.point, U.point_comp⟩
      map f := Functor.Elements.homMk (spacesNeighborhoodMap x f) (Subtype.ext f.point_comp)
      map_id U := by apply Functor.Elements.hom_ext; rfl
      map_comp f g := by apply Functor.Elements.hom_ext; rfl }
  unitIso := NatIso.ofComponents (fun p => Iso.refl p) (fun g => by
    apply Functor.Elements.hom_ext
    simp only [Functor.id_map, Functor.comp_map, Iso.refl_hom]
    rfl)
  counitIso := NatIso.ofComponents (fun U => Iso.refl U) (fun f => by
    simp only [Functor.id_map, Functor.comp_map, Iso.refl_hom]
    exact EtaleNeighborhood.Hom.ext rfl)

/-- The elements of the fibre functor on the spaces-étale site are cofiltered. -/
instance isCofiltered_spacesGeometricFiber_elements :
    IsCofiltered (spacesGeometricFiber x).Elements :=
  IsCofiltered.of_equivalence (spacesFiberElementsEquiv x).symm

/-- The étale neighbourhoods of a geometric point have a weakly initial family in the universe
of the schemes. -/
theorem initiallySmall_etaleNeighborhood :
    InitiallySmall.{u} (EtaleNeighborhood B S hS X.1 X.2 x) :=
  have : InitiallySmall.{u} (geometricFiber B S hS X.1 x).Elements :=
    initiallySmall_geometricFiber_elements B S hS X.1 X.2 x
  have : InitiallySmall.{u} (SmallEtaleNeighborhood x) :=
    initiallySmall_of_initial_of_initiallySmall
      (neighborhoodFiberElementsEquiv B S hS X.1 x).inverse
  initiallySmall_of_initial_of_initiallySmall (EtaleNeighborhood.ofSmallEtale X.2 x)

/-- The elements of the fibre functor on the spaces-étale site have a weakly initial family in
the universe of the schemes. -/
instance initiallySmall_spacesGeometricFiber_elements :
    InitiallySmall.{u} (spacesGeometricFiber x).Elements :=
  have := initiallySmall_etaleNeighborhood x
  initiallySmall_of_initial_of_initiallySmall (spacesFiberElementsEquiv x).inverse

/-- The spaces-étale form of Stacks 04JX: a lift of a geometric point into an algebraic space
`V` étale over `X` lifts through every jointly point-surjective family over `V`. -/
theorem spacesGeometricFiber_jointly_surjective {V : SpacesEtale B S hS X} (R : Presieve V)
    (hR : R ∈ SpacesEtale.precoverage B S hS X V) (v : (spacesGeometricFiber x).obj V) :
    ∃ (W : SpacesEtale B S hS X) (g : W ⟶ V) (_ : R g) (w : (spacesGeometricFiber x).obj W),
      (spacesGeometricFiber x).map g w = v := by
  obtain ⟨E, rfl, hE⟩ := hR
  obtain ⟨i, wval, hwval, φ, hφ⟩ :=
    exists_lift_to_etaleCovering B S hS X x
      (etaleNeighborhoodOfSitePoint B S hS X x V v.1 v.2) E hE
  exact ⟨E.X i, E.f i, Presieve.ofArrows.mk i, ⟨wval, hwval⟩, Subtype.ext <|
    (congrArg (fun k => k.app (Opposite.op x.val.siteObject) wval) hφ).symm.trans φ.point_comp⟩

/-- The spaces-étale analogue of the point of Stacks 04K0: the point of the spaces-étale site
of `X` determined by a geometric point of `X`. Its fibre functor is the functor of lifts of the
geometric point into the algebraic spaces étale over `X`. -/
noncomputable def spacesEtaleSitePoint : (SpacesEtale.topology B S hS X).Point.{u} :=
  GrothendieckTopology.Point.ofPrecoverage (spacesGeometricFiber x)
    (fun R hR v => spacesGeometricFiber_jointly_surjective x R hR v)

/-- The fibre functor of the point of the spaces-étale site is the functor of lifts, on the
nose. -/
@[simp]
theorem spacesEtaleSitePoint_fiber :
    (spacesEtaleSitePoint x).fiber = spacesGeometricFiber x := rfl

/-- The diagram of sections of a presheaf on the spaces-étale site over the elements of the
fibre functor is its diagram of sections over the étale neighbourhoods, read along
`AlgebraicGeometry.Space.spacesFiberElementsEquiv`. -/
theorem spacesNeighborhoodSections_comp (P : (SpacesEtale B S hS X)ᵒᵖ ⥤ Type (u + 1)) :
    (spacesFiberElementsEquiv x).functor.op ⋙ spacesNeighborhoodSections x P =
      (Functor.Elements.π (spacesGeometricFiber x)).op ⋙ P := rfl

/-- The stalk at the point of the spaces-étale site of one presheaf of sets is the spaces-étale
stalk of Stacks 04JZ. -/
noncomputable def spacesEtaleSitePointStalkIsoComponent
    (P : (SpacesEtale B S hS X)ᵒᵖ ⥤ Type (u + 1)) :
    ((spacesEtaleSitePoint x).presheafFiber (A := Type (u + 1))).obj P ≅ spacesStalkSet x P :=
  Equiv.toIso ((Types.colimitEquivColimitType
    ((Functor.Elements.π (spacesGeometricFiber x)).op ⋙ P)).trans
      (Equiv.ofBijective
        (show ((Functor.Elements.π (spacesGeometricFiber x)).op ⋙ P).ColimitType →
            spacesStalkSet x P from
          Functor.colimitTypePrecomp (spacesFiberElementsEquiv x).functor.op
            (spacesNeighborhoodSections x P))
        (Functor.bijective_colimitTypePrecomp _ _)))

/-- The stalk comparison on the spaces-étale site sends the germ at a lift of the geometric
point of a section over an étale algebraic space to the germ of that section over the
corresponding étale neighbourhood. -/
theorem spacesEtaleSitePointStalkIsoComponent_toPresheafFiber
    (P : (SpacesEtale B S hS X)ᵒᵖ ⥤ Type (u + 1)) (V : SpacesEtale B S hS X)
    (v : (spacesGeometricFiber x).obj V) (a : P.obj (Opposite.op V)) :
    (spacesEtaleSitePointStalkIsoComponent x P).hom
        ((spacesEtaleSitePoint x).toPresheafFiber V v P a) =
      (spacesNeighborhoodSections x P).ιColimitType
        (Opposite.op (etaleNeighborhoodOfSitePoint B S hS X x V v.1 v.2)) a := by
  let D := (Functor.Elements.π (spacesGeometricFiber x)).op ⋙ P
  show (show D.ColimitType → spacesStalkSet x P from
      Functor.colimitTypePrecomp (spacesFiberElementsEquiv x).functor.op
        (spacesNeighborhoodSections x P))
      ((Types.colimitEquivColimitType D) (colimit.ι D (Opposite.op ((spacesGeometricFiber x).elementsMk V v)) a)) = _
  rw [Types.colimitEquivColimitType_apply]
  rfl

/-- The stalk at the point of the spaces-étale site is the spaces-étale stalk of Stacks 04JZ,
naturally in the presheaf. -/
noncomputable def spacesEtaleSitePointStalkIso :
    (spacesEtaleSitePoint x).presheafFiber (A := Type (u + 1)) ≅ spacesStalkSetFunctor x :=
  NatIso.ofComponents (fun P => spacesEtaleSitePointStalkIsoComponent x P) (by
    intro P Q α
    apply (spacesEtaleSitePoint x).presheafFiber_hom_ext
    intro V v
    apply ConcreteCategory.hom_ext
    intro a
    have hnat := ConcreteCategory.congr_hom
      ((spacesEtaleSitePoint x).toPresheafFiber_naturality α V v) a
    simp only [types_comp_apply] at hnat
    change (spacesEtaleSitePointStalkIsoComponent x Q).hom
        ((spacesEtaleSitePoint x).presheafFiber.map α
          ((spacesEtaleSitePoint x).toPresheafFiber V v P a)) =
      (spacesStalkSetFunctor x).map α
        ((spacesEtaleSitePointStalkIsoComponent x P).hom
          ((spacesEtaleSitePoint x).toPresheafFiber V v P a))
    rw [hnat, spacesEtaleSitePointStalkIsoComponent_toPresheafFiber x Q V v,
      spacesEtaleSitePointStalkIsoComponent_toPresheafFiber x P V v]
    rfl)

end AlgebraicGeometry.Space

end
