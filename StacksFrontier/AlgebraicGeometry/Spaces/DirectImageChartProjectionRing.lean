module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjection
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStructureMapComp

/-!
# The chart projections of a direct image of a sheaf of rings are ring homomorphisms

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`.  The sections of the
direct image `f_*𝒪_X` over an étale scheme chart `V` of `Y` carry the ring structure
*transported* along the direct image, in the sense of `CategoryTheory.Sheaf.ringObjRing`, and
`AlgebraicGeometry.Space.directImageChartProjection` — the projection to one of the étale
scheme charts of `X` above `X ×_Y V` — is only a natural transformation of the *set*-valued
sections functors.  This file upgrades it to a homomorphism of sheaves of rings' sections.

## Main definitions

* `Stacks.Sheaves.ToposPullback.pullbackRingSectionsHom`: for a finite-product-preserving
  functor `Φ` of sheaves of sets and a natural transformation `θ : Φ ⋙ Γ(X, -) ⟶ Γ(Z, -)` of
  sections functors, the map `θ` on the sections of `O` **is a ring homomorphism** from the
  sections of the inverse-image sheaf of rings `pullbackRingSheaf J Φ O` over `X` to the
  sections of `O` over `Z`.
* `AlgebraicGeometry.Space.directImageChartProjectionRingHom`: that homomorphism at the chart
  projection of the direct image of the structure sheaf.

## Main results

* `AlgebraicGeometry.Space.directImageChartProjectionRingHom_apply`: on sections the ring
  homomorphism is the chart projection, so nothing is changed but the recorded structure.
* `AlgebraicGeometry.Space.hom_structureSharp_comp_directImageChartProjectionRingHom`: the
  structure map followed by the chart projection is pullback of regular functions along the
  induced morphism of charts, as a homomorphism of rings.
* `AlgebraicGeometry.Space.directImageChartProjectionRingHom_pullbackRingSheafMap`: the ring
  homomorphism commutes with the direct image of a morphism of sheaves of rings.

## Implementation notes

**Why a lemma and not an exposure attribute.**  The sections of `f_*𝒪_X` over `V` are the
object `RingCat.of ((f_* ⋙ Γ(V, -)).obj 𝒪_X)` whose ring structure is
`CategoryTheory.Sheaf.ringObjRing`, whereas the sections of `𝒪_X` over a chart of `X` carry
their own, direct ring structure; those two are *not* the same structure on one type, so no
amount of unfolding identifies them.  The one-line `CategoryTheory.Sheaf.ringObjHom` applied to
`AlgebraicGeometry.Space.directImageChartProjection` produces a homomorphism between the two
*transported* structures, and its target is not the ring of sections of `𝒪_X`.  What identifies
the transported structure on the sections of a sheaf of rings with the direct one are the four
computation rules `CategoryTheory.Sheaf.sectionsFunctor_map_ringAddHom`, `..._ringMulHom`,
`..._ringZeroHom` and `..._ringOneHom`; composing them with
`CategoryTheory.Sheaf.ringAddObj_naturality` and its siblings is exactly
`Stacks.Sheaves.ToposPullback.pullbackRingSectionsHom`.  So the honest fix is a lemma through
the API of `Stacks.Sheaves.ToposPullback.pullbackRingSheaf`, and the exposure question never
arises: the only definitional identification used is the one `RingCat.ofHom` performs against
the stated type, which is the same one
`Stacks.Sheaves.ToposPullback.restrictionRingHom` performs.

That definition is the special case in which the transporting functor `Φ` is restriction
along a continuous functor of sites, where `Φ ⋙ Γ(X, -)` is *definitionally* a sections functor
and `θ` is the identity.  The direct image is not of that shape, so the transformation `θ` has
to be carried along; everything else is the same proof, and the four field proofs below are the
four of `Stacks.Sheaves.ToposPullback.restrictionRingHom` precomposed with the naturality of
`θ`.

The homomorphism is stated as a morphism of `RingCat` rather than as a bundled `RingHom`
between the two section types: in that form the transported ring structure is carried by the
object `RingCat.of …` itself, so a consumer reading `.hom` gets a `RingHom` for the ring
structures `RingCat` records, with no instance argument to supply and no transported structure
mentioned in its type.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map and
  its chart projections.
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2), the transported ring
  structure on an inverse image.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open Stacks.Sheaves.ToposPullback

namespace Stacks.Sheaves.ToposPullback

universe ww vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww})]
  (Φ : Sheaf K (Type ww) ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
  (O : Sheaf K RingCat.{ww})

/-- **A natural transformation from the transporting functor to a sections functor is a ring
homomorphism on sections.**  If `θ` carries the sections over `X` of the inverse image of a
sheaf of sets along `Φ` to its sections over `Z`, then `θ` carries the sections over `X` of the
inverse-image sheaf of rings `pullbackRingSheaf J Φ O` — whose ring structure is the one
transported along `Φ ⋙ Γ(X, -)` — to the sections of `O` over `Z` with their own ring
structure, and does so as a ring homomorphism.

`Stacks.Sheaves.ToposPullback.restrictionRingHom` is the case where `Φ` is restriction along a
continuous functor of sites and `θ` is the identity. -/
noncomputable def pullbackRingSectionsHom (X : Cᵒᵖ) (Z : Dᵒᵖ)
    (θ : Φ ⋙ sectionsFunctor J X ⟶ sectionsFunctor K Z) :
    (pullbackRingSheaf J Φ O).obj.obj X ⟶ O.obj.obj Z :=
  letI := ringObjRing O (Φ ⋙ sectionsFunctor J X)
  RingCat.ofHom
    { toFun := θ.app (Sheaf.ringSheaf O)
      map_add' := fun x y ↦ (ringAddObj_naturality O θ x y).trans
        (sectionsFunctor_map_ringAddHom O Z _ _)
      map_mul' := fun x y ↦ (ringMulObj_naturality O θ x y).trans
        (sectionsFunctor_map_ringMulHom O Z _ _)
      map_zero' := (ringZeroObj_naturality O θ).trans
        (sectionsFunctor_map_ringZeroHom O Z default)
      map_one' := (ringOneObj_naturality O θ).trans
        (sectionsFunctor_map_ringOneHom O Z default) }

omit [J.HasSheafCompose (forget RingCat.{ww})] in
/-- On sections the ring homomorphism is the given natural transformation. -/
@[simp]
lemma pullbackRingSectionsHom_apply (X : Cᵒᵖ) (Z : Dᵒᵖ)
    (θ : Φ ⋙ sectionsFunctor J X ⟶ sectionsFunctor K Z)
    (a : ToType ((pullbackRingSheaf J Φ O).obj.obj X)) :
    (pullbackRingSectionsHom J K Φ O X Z θ).hom a = θ.app (Sheaf.ringSheaf O) a := rfl

end Stacks.Sheaves.ToposPullback

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- **The chart projection of the direct image of the structure sheaf is a ring
homomorphism.**  The sections of `f_*𝒪_X` over an étale scheme chart `V` of `Y` form a ring by
transport along the direct image; this is the projection to the regular functions on an étale
scheme chart of `X` above `X ×_Y V`, recorded as a homomorphism of rings. -/
noncomputable def directImageChartProjectionRingHom (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op) :
    (structureRingSheafDirectImage B S hS f).obj.obj (op V) ⟶
      (structureRingSheaf B S hS X).obj.obj j.right :=
  pullbackRingSectionsHom (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)
    (smallEtaleDirectImage B S hS f) (structureRingSheaf B S hS X) (op V) j.right
    (directImageChartProjection B S hS f V j)

/-- On sections the ring homomorphism is the chart projection. -/
@[simp]
theorem directImageChartProjectionRingHom_apply (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (a : ToType ((structureRingSheafDirectImage B S hS f).obj.obj (op V))) :
    (directImageChartProjectionRingHom B S hS f V j).hom a =
      (directImageChartProjection B S hS f V j).app (structureSetSheaf B S hS X) a := rfl

/-- **The structure map followed by a chart projection is pullback of regular functions along
the induced morphism of charts**, as a homomorphism of rings: the ring-level form of
`AlgebraicGeometry.Space.directImageChartProjection_structureSharpSet`. -/
theorem hom_structureSharp_comp_directImageChartProjectionRingHom (f : X ⟶ Y)
    (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op) :
    ((structureSharp B S hS f).hom.app (op V) ≫
        directImageChartProjectionRingHom B S hS f V j).hom =
      chartPullbackRingHom B S hS f V j :=
  RingHom.ext fun b ↦ directImageChartProjection_structureSharpSet B S hS f V j b

/-- **The ring homomorphism commutes with the direct image of a morphism of sheaves of
rings**: the ring-level form of
`AlgebraicGeometry.Space.directImageChartProjection_ringSheafMap`. -/
theorem directImageChartProjectionRingHom_pullbackRingSheafMap (f : X ⟶ Y)
    (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    {O : Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u}}
    (φ : structureRingSheaf B S hS X ⟶ O) :
    (pullbackRingSheafMap (SmallEtale.topology B S hS Y.1)
          (smallEtaleDirectImage B S hS f) φ).hom.app (op V) ≫
        pullbackRingSectionsHom (SmallEtale.topology B S hS Y.1)
          (SmallEtale.topology B S hS X.1) (smallEtaleDirectImage B S hS f) O (op V) j.right
          (directImageChartProjection B S hS f V j) =
      directImageChartProjectionRingHom B S hS f V j ≫ φ.hom.app j.right :=
  RingCat.hom_ext (RingHom.ext fun a ↦
    directImageChartProjection_ringSheafMap B S hS f V j φ a)

end AlgebraicGeometry.Space

end
