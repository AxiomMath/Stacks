module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.SubcanonicalYoneda
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Reduction
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleToposMorphism
public import StacksFrontier.CategoryTheory.Sites.SubcanonicalSheafifiedYoneda

/-!
# The étale sites of a formal algebraic space, and their functoriality

Let `S` be a scheme contained in a big fppf site `B`. The three étale sites of a formal
algebraic space `X` over `S` are, by definition, the three étale sites of its reduction
`X_red`: the small étale site of étale scheme charts, the spaces-étale site of algebraic
spaces étale over it, and the affine étale site of étale charts with affine source. A
morphism `f : X ⟶ Y` of formal algebraic spaces induces a morphism of reductions
`X_red ⟶ Y_red`, hence a base-change morphism of spaces-étale sites and a morphism of small
étale topoi, both compatible with composition.

## Main definitions

* `AlgebraicGeometry.FormalSpace.Reduction`: the reduction of a formal algebraic space, as data.
* `AlgebraicGeometry.FormalSpace.Reduction.map`: the morphism of reductions induced by a morphism
  of formal algebraic spaces.
* `AlgebraicGeometry.FormalSpace.Reduction.SmallEtale`,
  `AlgebraicGeometry.FormalSpace.Reduction.SpacesEtale` and
  `AlgebraicGeometry.FormalSpace.Reduction.AffineEtale`, with their topologies: the small étale,
  spaces-étale and affine étale sites of a formal algebraic space.
* `AlgebraicGeometry.FormalSpace.Reduction.spacesBaseChange` and
  `AlgebraicGeometry.FormalSpace.Reduction.smallToposMorphism`: the base-change functor of
  spaces-étale sites and the morphism of small étale topoi induced by a morphism.
* `AlgebraicGeometry.FormalSpace.liftSheafFunctor`: the universe lift of algebraic spaces, as a
  functor into the fppf sheaves, with `AlgebraicGeometry.FormalSpace.liftSheafFunctorFullyFaithful`
  its full faithfulness.
* `AlgebraicGeometry.FormalSpace.yonedaSpaceCompLiftSheafFunctorIsoUliftYoneda` and
  `AlgebraicGeometry.FormalSpace.yonedaSpaceCompLiftSheafFunctorIsoSheafifiedYoneda`: the universe
  lift of a representable algebraic space is the Yoneda embedding into fppf sheaves, and the
  sheafified Yoneda embedding;
  `AlgebraicGeometry.FormalSpace.liftSheafYonedaSpaceIsoSheafifiedYoneda` is the latter at a
  single object of the site.

## Main results

* `AlgebraicGeometry.FormalSpace.Reduction.map_comp` and
  `AlgebraicGeometry.FormalSpace.Reduction.map_id`: the morphism of reductions is functorial.
* `AlgebraicGeometry.FormalSpace.Reduction.iso`: two reductions of one formal algebraic space are
  canonically isomorphic.
* `AlgebraicGeometry.FormalSpace.Reduction.isContinuous_spacesBaseChange` and
  `AlgebraicGeometry.FormalSpace.Reduction.spacesBaseChange_isMorphismOfSites`: the base-change
  functor is continuous and induces a morphism of sites.
* `AlgebraicGeometry.FormalSpace.Reduction.spacesBaseChangeComp`,
  `AlgebraicGeometry.FormalSpace.Reduction.spacesBaseChangeComp_projection` and
  `AlgebraicGeometry.FormalSpace.Reduction.smallToposMorphismComp`: compatibility with
  composition.

## Implementation notes

Every declaration takes a reduction `AlgebraicGeometry.FormalSpace.Reduction` as an argument
rather than choosing one; one exists for every formal algebraic space by
`AlgebraicGeometry.FormalSpace.exists_isReduction_of_isFormalAlgebraicSpace` (Stacks 0AIN).

A formal algebraic space is a sheaf of `Type (u + 1)` while an algebraic space is a presheaf of
`Type u`, so the reduction enters through its universe lift
`AlgebraicGeometry.FormalSpace.liftSheaf`.

Compatibility with composition cannot be obtained by rewriting with
`AlgebraicGeometry.FormalSpace.Reduction.map_comp`, because the composition isomorphisms of
Stacks 03G2 have types depending on the morphism; the three `*OfEq` declarations restate them for
a morphism equal to a composite.

## References

* [Stacks Project, Tag 0DEA](https://stacks.math.columbia.edu/tag/0DEA)
* [Stacks Project, Tag 0DEC](https://stacks.math.columbia.edu/tag/0DEC)
* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The universe lift of an algebraic space -/

/-- An algebraic space over `S`, read as an fppf sheaf of `Type (u + 1)` by lifting the
universe of its values. -/
noncomputable def liftSheaf (X : AlgebraicSpaces B S hS) : FppfSheaf B S hS :=
  ⟨X.obj ⋙ uliftFunctor.{u + 1}, by
    rw [isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_comp_uliftFunctor_iff]
    exact (isSheaf_iff_isSheaf_of_type _ _).mp X.property.isSheaf⟩

/-- Lifting the universe of the values of a presheaf is fully faithful. -/
def liftFullyFaithful :
    ((Functor.whiskeringRight ((BigFppfOver B S hS)ᵒᵖ) (Type u) (Type (u + 1))).obj
      uliftFunctor.{u + 1}).FullyFaithful :=
  Functor.FullyFaithful.whiskeringRight fullyFaithfulULiftFunctor.{u + 1, u} _

/-- A morphism of algebraic spaces over `S`, read as a morphism of the universe-lifted
sheaves. -/
def liftSheafMap {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    liftSheaf B S hS X ⟶ liftSheaf B S hS Y :=
  ⟨Functor.whiskerRight f.hom uliftFunctor.{u + 1}⟩

/-- The universe lift of the identity is the identity. -/
@[simp]
theorem liftSheafMap_id (X : AlgebraicSpaces B S hS) :
    liftSheafMap B S hS (𝟙 X) = 𝟙 (liftSheaf B S hS X) :=
  rfl

/-- The universe lift of a composite is the composite of the lifts. -/
@[simp]
theorem liftSheafMap_comp {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) :
    liftSheafMap B S hS (f ≫ g) = liftSheafMap B S hS f ≫ liftSheafMap B S hS g :=
  rfl

/-- The morphism of algebraic spaces whose universe lift is a given morphism of the lifted
sheaves. -/
noncomputable def liftSheafPreimage {X Y : AlgebraicSpaces B S hS}
    (g : liftSheaf B S hS X ⟶ liftSheaf B S hS Y) : X ⟶ Y :=
  ObjectProperty.homMk ((liftFullyFaithful B S hS).preimage g.hom)

/-- The universe lift of `AlgebraicGeometry.FormalSpace.liftSheafPreimage g` is `g`. -/
@[simp]
theorem liftSheafMap_liftSheafPreimage {X Y : AlgebraicSpaces B S hS}
    (g : liftSheaf B S hS X ⟶ liftSheaf B S hS Y) :
    liftSheafMap B S hS (liftSheafPreimage B S hS g) = g :=
  Sheaf.hom_ext ((liftFullyFaithful B S hS).map_preimage g.hom)

/-- The universe lift of morphisms of algebraic spaces is injective. -/
theorem liftSheafMap_injective {X Y : AlgebraicSpaces B S hS} :
    Function.Injective (liftSheafMap B S hS (X := X) (Y := Y)) := by
  intro a b h
  apply ObjectProperty.hom_ext
  apply (liftFullyFaithful B S hS).map_injective
  exact congrArg (fun k : liftSheaf B S hS X ⟶ liftSheaf B S hS Y => k.hom) h

/-! ### The reduction as a hypothesis -/

/-- The reduction of a formal algebraic space `X` over `S`, as data: a reduced algebraic space
`space` over `S`, an inclusion of its universe lift into `X`, and the witness that this
inclusion is representable, a thickening, and universal among morphisms from reduced algebraic
spaces. -/
structure Reduction (X : FppfSheaf B S hS) where
  /-- The reduced algebraic space underlying the formal algebraic space. -/
  space : AlgebraicSpaces B S hS
  /-- The inclusion of the reduction, as a morphism of fppf sheaves. -/
  inclusion : liftSheaf B S hS space ⟶ X
  /-- The inclusion exhibits `space` as the reduction, in the sense of Stacks 0AIN. -/
  isReduction : IsReduction B S hS X (liftSheaf B S hS space) inclusion

namespace Reduction

variable {B S hS} {X Y Z : FppfSheaf B S hS}

/-! ### The morphism of reductions induced by a morphism of formal algebraic spaces -/

/-- A morphism `f : X ⟶ Y` of formal algebraic spaces induces a unique morphism of reductions
commuting with the two inclusions. -/
theorem existsUnique_liftSheafMap (RX : Reduction B S hS X) (RY : Reduction B S hS Y)
    (f : X ⟶ Y) :
    ∃! g : RX.space ⟶ RY.space,
      liftSheafMap B S hS g ≫ RY.inclusion = RX.inclusion ≫ f := by
  obtain ⟨h, hh, hu⟩ := RY.isReduction.universal (liftSheaf B S hS RX.space)
    RX.isReduction.algebraic RX.isReduction.reduced (RX.inclusion ≫ f)
  refine ⟨liftSheafPreimage B S hS h, ?_, ?_⟩
  · exact (congrArg (· ≫ RY.inclusion) (liftSheafMap_liftSheafPreimage B S hS h)).trans hh
  · exact fun g hg => liftSheafMap_injective B S hS
      ((hu _ hg).trans (liftSheafMap_liftSheafPreimage B S hS h).symm)

/-- The morphism of reductions `X_red ⟶ Y_red` induced by a morphism `f : X ⟶ Y` of formal
algebraic spaces. -/
noncomputable def map (RX : Reduction B S hS X) (RY : Reduction B S hS Y) (f : X ⟶ Y) :
    RX.space ⟶ RY.space :=
  (RX.existsUnique_liftSheafMap RY f).choose

/-- The induced morphism of reductions commutes with the two inclusions. -/
theorem liftSheafMap_map (RX : Reduction B S hS X) (RY : Reduction B S hS Y) (f : X ⟶ Y) :
    liftSheafMap B S hS (RX.map RY f) ≫ RY.inclusion = RX.inclusion ≫ f :=
  (RX.existsUnique_liftSheafMap RY f).choose_spec.1

/-- Any morphism of reductions commuting with the two inclusions is the induced one. -/
theorem eq_map (RX : Reduction B S hS X) (RY : Reduction B S hS Y) (f : X ⟶ Y)
    (g : RX.space ⟶ RY.space)
    (hg : liftSheafMap B S hS g ≫ RY.inclusion = RX.inclusion ≫ f) :
    g = RX.map RY f :=
  (RX.existsUnique_liftSheafMap RY f).unique hg (RX.liftSheafMap_map RY f)

/-- The induced morphism of reductions is compatible with composition. -/
theorem map_comp (RX : Reduction B S hS X) (RY : Reduction B S hS Y) (RZ : Reduction B S hS Z)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    RX.map RY f ≫ RY.map RZ g = RX.map RZ (f ≫ g) := by
  apply eq_map
  rw [liftSheafMap_comp, Category.assoc, RY.liftSheafMap_map RZ g, ← Category.assoc,
    RX.liftSheafMap_map RY f, Category.assoc]

/-- The induced morphism of reductions sends the identity to the identity. -/
theorem map_id (RX : Reduction B S hS X) : RX.map RX (𝟙 X) = 𝟙 RX.space :=
  (eq_map RX RX (𝟙 X) (𝟙 RX.space) (by
    rw [liftSheafMap_id, Category.id_comp, Category.comp_id])).symm

/-- Two reductions of one formal algebraic space are canonically isomorphic, by the morphisms
of reductions induced by the identity in both directions. -/
noncomputable def iso (R R' : Reduction B S hS X) : R.space ≅ R'.space where
  hom := R.map R' (𝟙 X)
  inv := R'.map R (𝟙 X)
  hom_inv_id := by rw [map_comp, Category.comp_id, map_id]
  inv_hom_id := by rw [map_comp, Category.comp_id, map_id]

/-! ### Stacks 0DEA: the three étale sites of a formal algebraic space -/

/-- The *small étale site* `X_étale` of a formal algebraic space `X`
with reduction `X_red`, as a category: the small étale site `X_{red, étale}` of the reduction,
in the sense of Stacks 03ED, whose objects are the étale scheme charts of `X_red`. -/
@[stacks 0DEA "(1) the small étale site, as a category; read against a given reduction, which
  Stacks 0AIN supplies"]
abbrev SmallEtale (R : Reduction B S hS X) := Space.SmallEtale B S hS R.space.obj

/-- The topology of the small étale site of `X`: that of
`X_{red, étale}`. -/
@[stacks 0DEA "(1) the topology of the small étale site; read against a given reduction, which
  Stacks 0AIN supplies"]
abbrev smallEtaleTopology (R : Reduction B S hS X) : GrothendieckTopology R.SmallEtale :=
  Space.SmallEtale.topology B S hS R.space.obj

/-- The site `X_{spaces, étale}` of a formal algebraic space `X`
with reduction `X_red`, as a category: the spaces-étale site `X_{red, spaces, étale}` of the
reduction, in the sense of Stacks 03G0, whose objects are the algebraic spaces étale over
`X_red`. -/
@[stacks 0DEA "(2) the spaces-étale site, as a category; read against a given reduction, which
  Stacks 0AIN supplies"]
abbrev SpacesEtale (R : Reduction B S hS X) := Space.SpacesEtale B S hS R.space

/-- The topology of `X_{spaces, étale}`: that of
`X_{red, spaces, étale}`. -/
@[stacks 0DEA "(2) the topology of the spaces-étale site; read against a given reduction, which
  Stacks 0AIN supplies"]
abbrev spacesEtaleTopology (R : Reduction B S hS X) : GrothendieckTopology R.SpacesEtale :=
  Space.SpacesEtale.topology B S hS R.space

/-- The site `X_{affine, étale}` of a formal algebraic space `X`
with reduction `X_red`, as a category: the affine étale site `X_{red, affine, étale}` of the
reduction, whose objects are the étale charts of `X_red` with affine source. -/
@[stacks 0DEA "(3) the affine étale site, as a category; read against a given reduction, which
  Stacks 0AIN supplies"]
abbrev AffineEtale (R : Reduction B S hS X) := Space.AffineEtale B S hS R.space.obj

/-- The topology of `X_{affine, étale}`: that of
`X_{red, affine, étale}`. -/
@[stacks 0DEA "(3) the topology of the affine étale site; read against a given reduction, which
  Stacks 0AIN supplies"]
abbrev affineEtaleTopology (R : Reduction B S hS X) : GrothendieckTopology R.AffineEtale :=
  Space.AffineEtale.topology B S hS R.space.obj

end Reduction

/-! ### Transport of the composition isomorphisms of Stacks 03G2 along an equality -/

/-- The composition isomorphism of Stacks 03G2, part (2), for a morphism merely *equal* to a
composite. -/
noncomputable def spacesBaseChangeCompOfEq {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k) :
    (Space.spacesBaseChange B S hS g).functor ⋙ (Space.spacesBaseChange B S hS f).functor ≅
      (Space.spacesBaseChange B S hS k).functor := by
  cases h
  exact Space.spacesBaseChange_comp B S hS f g

/-- `AlgebraicGeometry.FormalSpace.spacesBaseChangeCompOfEq` is compatible with the cartesian
projections. -/
theorem spacesBaseChangeCompOfEq_projection {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k) (V : Space.SpacesEtale B S hS Z) :
    ((spacesBaseChangeCompOfEq B S hS f g k h).hom.app V).hom.left ≫
        (Space.spacesBaseChange B S hS k).projection.app V =
      (Space.spacesBaseChange B S hS f).projection.app
          ((Space.spacesBaseChange B S hS g).functor.obj V) ≫
        (Space.spacesBaseChange B S hS g).projection.app V := by
  cases h
  exact Space.spacesBaseChange_comp_projection B S hS f g V

/-- The composition isomorphism of small étale direct images of Stacks 03G2, part (3), for a
morphism merely *equal* to a composite. -/
noncomputable def smallToposMorphismCompOfEq {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k) :
    (MorphismOfTopoi.comp (Space.smallToposMorphism B S hS g)
        (Space.smallToposMorphism B S hS f)).pushforward ≅
      (Space.smallToposMorphism B S hS k).pushforward := by
  cases h
  exact Space.smallToposMorphism_comp B S hS f g

namespace Reduction

variable {B S hS} {X Y Z : FppfSheaf B S hS}

/-! ### Stacks 0DEC: functoriality of the étale sites -/

/-- The functor `Y_{spaces, étale} ⟶ X_{spaces, étale}` induced by a
morphism `f : X ⟶ Y` of formal algebraic spaces: base change along the induced morphism of
reductions, together with its cartesian projection, by Stacks 03G2, part (1). -/
@[stacks 0DEC "(1) the base-change functor `Y_spaces,étale ⟶ X_spaces,étale`; read against
  given reductions, which Stacks 0AIN supplies"]
noncomputable def spacesBaseChange (RX : Reduction B S hS X) (RY : Reduction B S hS Y)
    (f : X ⟶ Y) : Space.SpacesBaseChange B S hS (RX.map RY f) :=
  Space.spacesBaseChange B S hS (RX.map RY f)

/-- The functor `Y_{spaces, étale} ⟶ X_{spaces, étale}` is
continuous. -/
@[stacks 0DEC "(1) continuity of the functor; read against given reductions, which Stacks
  0AIN supplies"]
theorem isContinuous_spacesBaseChange (RX : Reduction B S hS X) (RY : Reduction B S hS Y)
    (f : X ⟶ Y) :
    (RX.spacesBaseChange RY f).functor.IsContinuous RY.spacesEtaleTopology
      RX.spacesEtaleTopology :=
  Space.isContinuous_spacesBaseChange B S hS (RX.map RY f)

/-- The continuous functor `Y_{spaces, étale} ⟶ X_{spaces, étale}`
induces a morphism of sites
`f_{spaces, étale} : X_{spaces, étale} ⟶ Y_{spaces, étale}`, in the sense of Stacks 00X1. -/
@[stacks 0DEC "(1) the induced morphism of sites `f_spaces,étale`; read against given
  reductions, which Stacks 0AIN supplies"]
theorem spacesBaseChange_isMorphismOfSites (RX : Reduction B S hS X)
    (RY : Reduction B S hS Y) (f : X ⟶ Y) :
    (RX.spacesBaseChange RY f).functor.IsMorphismOfSites RY.spacesEtaleTopology
      RX.spacesEtaleTopology :=
  Space.spacesBaseChange_isMorphismOfSites B S hS (RX.map RY f)

/-- The rule `f ↦ f_{spaces, étale}` is compatible with composition:
the underlying functor of `(f ≫ g)_{spaces, étale}` is canonically isomorphic to the composite
of those of `g_{spaces, étale}` and `f_{spaces, étale}`, which is the composition of morphisms
of sites of Stacks 03CC. -/
@[stacks 0DEC "(2) compatibility with composition, as a canonical isomorphism of the
  underlying functors; read against given reductions, which Stacks 0AIN supplies"]
noncomputable def spacesBaseChangeComp (RX : Reduction B S hS X) (RY : Reduction B S hS Y)
    (RZ : Reduction B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z) :
    (RY.spacesBaseChange RZ g).functor ⋙ (RX.spacesBaseChange RY f).functor ≅
      (RX.spacesBaseChange RZ (f ≫ g)).functor :=
  spacesBaseChangeCompOfEq B S hS (RX.map RY f) (RY.map RZ g) (RX.map RZ (f ≫ g))
    (map_comp RX RY RZ f g)

/-- The composition isomorphism is compatible with the cartesian
projections to the original object of `Z_{spaces, étale}`. -/
@[stacks 0DEC "(2) the composition isomorphism is compatible with the cartesian projections,
  which pins it down; read against given reductions, which Stacks 0AIN supplies"]
theorem spacesBaseChangeComp_projection (RX : Reduction B S hS X) (RY : Reduction B S hS Y)
    (RZ : Reduction B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z) (V : RZ.SpacesEtale) :
    ((RX.spacesBaseChangeComp RY RZ f g).hom.app V).hom.left ≫
        (RX.spacesBaseChange RZ (f ≫ g)).projection.app V =
      (RX.spacesBaseChange RY f).projection.app
          ((RY.spacesBaseChange RZ g).functor.obj V) ≫
        (RY.spacesBaseChange RZ g).projection.app V :=
  spacesBaseChangeCompOfEq_projection B S hS (RX.map RY f) (RY.map RZ g)
    (RX.map RZ (f ≫ g)) (map_comp RX RY RZ f g) V

/-- The morphism of topoi
`f_small : Sh(X_étale) ⟶ Sh(Y_étale)` associated to `f_{spaces, étale}`, via the
identification (0DEB) of the small étale topos with the spaces-étale topos. It is the morphism
of small étale topoi of Stacks 03G2, part (3), at the induced morphism of reductions. -/
@[stacks 0DEC "(3) the morphism of small étale topoi `f_small`, through the identification
  (0DEB); read against given reductions, which Stacks 0AIN supplies"]
noncomputable def smallToposMorphism (RX : Reduction B S hS X) (RY : Reduction B S hS Y)
    (f : X ⟶ Y) :
    MorphismOfTopoi (Sheaf RX.smallEtaleTopology (Type (u + 1)))
      (Sheaf RY.smallEtaleTopology (Type (u + 1))) :=
  Space.smallToposMorphism B S hS (RX.map RY f)

/-- The construction of `f_small` is compatible with composition:
the direct image of the composite of `g_small` and `f_small` is canonically isomorphic to the
direct image of `(f ≫ g)_small`. -/
@[stacks 0DEC "(3) compatibility with composition of the morphisms of small étale topoi, on
  direct images; read against given reductions, which Stacks 0AIN supplies"]
noncomputable def smallToposMorphismComp (RX : Reduction B S hS X) (RY : Reduction B S hS Y)
    (RZ : Reduction B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z) :
    (MorphismOfTopoi.comp (RY.smallToposMorphism RZ g)
        (RX.smallToposMorphism RY f)).pushforward ≅
      (RX.smallToposMorphism RZ (f ≫ g)).pushforward :=
  smallToposMorphismCompOfEq B S hS (RX.map RY f) (RY.map RZ g) (RX.map RZ (f ≫ g))
    (map_comp RX RY RZ f g)

end Reduction

/-! ### The universe lift as a functor, and the Yoneda route -/

/-- The universe lift of algebraic spaces, as a functor: an algebraic space over `S` is sent to
the fppf sheaf of `Type (u + 1)` obtained by lifting the universe of its values, and a morphism
of algebraic spaces to its lift. -/
noncomputable def liftSheafFunctor : AlgebraicSpaces B S hS ⥤ FppfSheaf B S hS where
  obj := liftSheaf B S hS
  map := liftSheafMap B S hS
  map_id := liftSheafMap_id B S hS
  map_comp := liftSheafMap_comp B S hS

/-- On objects the universe-lift functor is `AlgebraicGeometry.FormalSpace.liftSheaf`. -/
@[simp]
theorem liftSheafFunctor_obj (X : AlgebraicSpaces B S hS) :
    (liftSheafFunctor B S hS).obj X = liftSheaf B S hS X :=
  rfl

/-- On morphisms the universe-lift functor is `AlgebraicGeometry.FormalSpace.liftSheafMap`. -/
@[simp]
theorem liftSheafFunctor_map {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    (liftSheafFunctor B S hS).map f = liftSheafMap B S hS f :=
  rfl

/-- The universe-lift functor is fully faithful: every morphism between the lifts of two
algebraic spaces is the lift of a unique morphism of algebraic spaces. -/
noncomputable def liftSheafFunctorFullyFaithful : (liftSheafFunctor B S hS).FullyFaithful where
  preimage f := liftSheafPreimage B S hS f
  map_preimage f := liftSheafMap_liftSheafPreimage B S hS f
  preimage_map f :=
    liftSheafMap_injective B S hS
      (liftSheafMap_liftSheafPreimage B S hS (liftSheafMap B S hS f))

/-- The universe-lift functor is full. -/
instance liftSheafFunctor_full : (liftSheafFunctor B S hS).Full :=
  (liftSheafFunctorFullyFaithful B S hS).full

/-- The universe-lift functor is faithful. -/
instance liftSheafFunctor_faithful : (liftSheafFunctor B S hS).Faithful :=
  (liftSheafFunctorFullyFaithful B S hS).faithful

/-- The universe lift of the algebraic space represented by an object of the big fppf site of
`S` is the Yoneda embedding into fppf sheaves of `Type (u + 1)`. -/
noncomputable def yonedaSpaceCompLiftSheafFunctorIsoUliftYoneda :
    schemeSpaceFunctor B S hS ⋙ liftSheafFunctor B S hS ≅
      GrothendieckTopology.uliftYoneda.{u + 1} (BigFppfOver.topology B S hS) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by
    apply Sheaf.hom_ext
    ext T x
    rfl)

/-- The universe lift of the algebraic space represented by an object `U` of the big fppf site
of `S` is the sheafified Yoneda embedding `U ↦ h_U^#`, naturally in `U`. -/
noncomputable def yonedaSpaceCompLiftSheafFunctorIsoSheafifiedYoneda :
    schemeSpaceFunctor B S hS ⋙ liftSheafFunctor B S hS ≅
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS) :=
  yonedaSpaceCompLiftSheafFunctorIsoUliftYoneda B S hS ≪≫
    (Sheaf.sheafifiedYonedaIsoUliftYoneda' (BigFppfOver.topology B S hS)).symm

/-- The universe lift of the algebraic space represented by `U` is the sheafified representable
`h_U^#`. -/
noncomputable def liftSheafYonedaSpaceIsoSheafifiedYoneda (U : BigFppfOver B S hS) :
    liftSheaf B S hS ((schemeSpaceFunctor B S hS).obj U) ≅
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U :=
  (yonedaSpaceCompLiftSheafFunctorIsoSheafifiedYoneda B S hS).app U

end AlgebraicGeometry.FormalSpace

end
