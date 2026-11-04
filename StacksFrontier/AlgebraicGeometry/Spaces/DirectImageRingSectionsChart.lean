module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionExt
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionRing
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartProjectionComp

/-!
# The sections of the direct image of a sheaf of rings over a chart

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B` and let `O` be a sheaf of rings on the small étale site of `X`.  The sections over an
étale scheme chart `V` of `Y` of the direct image `f_*O` are a limit over the étale scheme
charts of `X` above the algebraic space `X ×_Y V`
(`AlgebraicGeometry.Space.ranChartIsLimit`), and the ring structure on them is the one
*transported* along the direct image.  `AlgebraicGeometry.Space.directImageChartProjection` is
the projection of that limit to one of the charts, as a map of sets.

The projection is a homomorphism of rings for an arbitrary sheaf of rings `O`, and it is
bijective whenever the index it projects to has an invertible structure morphism, that is,
whenever the chart it names identifies the algebraic space `X ×_Y V`.  For a relatively
representable `f`, in particular for an affine one, the sections of `f_*O` over `V` are
therefore the sections of `O` over the base-changed chart `V ×_Y X`, as rings.

## Main definitions

* `AlgebraicGeometry.Space.directImageRingSectionsHom`: the chart projection of the sections of
  `f_*O` over an étale scheme chart of `Y`, as a homomorphism of rings, for an arbitrary sheaf
  of rings `O` on the small étale site of `X`.
* `AlgebraicGeometry.Space.directImageRingSectionsRingEquiv`: for a relatively representable
  `f`, that homomorphism at the base-changed chart, as an isomorphism of rings
  `(f_*O)(V) ≅ O(V ×_Y X)`.

## Main results

* `AlgebraicGeometry.Space.bijective_directImageChartProjection_of_isIso_hom`: the chart
  projection of a direct image of sheaves of sets is bijective at an index whose structure
  morphism is invertible.
* `AlgebraicGeometry.Space.bijective_directImageRingSectionsHom_of_isIso_hom` and
  `AlgebraicGeometry.Space.isIso_directImageRingSectionsHom_of_isIso_hom`: the same for the
  ring homomorphism, and as an isomorphism of `RingCat`.
* `AlgebraicGeometry.Space.directImageRingSectionsHom_pullbackRingSheafMap`: the ring
  homomorphism commutes with the direct image of a morphism of sheaves of rings.

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G4](https://stacks.math.columbia.edu/tag/03G4)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-! ### The chart projection for an arbitrary sheaf of rings -/

/-- The chart projection of the direct image of a sheaf of rings, as a homomorphism of rings: the
sections of `f_*O` over an étale scheme chart `V` of `Y` carry the ring structure transported
along the direct image, and this is the projection to the sections of `O` over an étale scheme
chart of `X` above `X ×_Y V`. -/
noncomputable def directImageRingSectionsHom (f : X ⟶ Y)
    (O : Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u}) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op) :
    (pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS Y.1)
        (smallEtaleDirectImage B S hS f) O).obj.obj (op V) ⟶ O.obj.obj j.right :=
  pullbackRingSectionsHom (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)
    (smallEtaleDirectImage B S hS f) O (op V) j.right
    (directImageChartProjection B S hS f V j)

/-- On sections the ring homomorphism is the chart projection. -/
@[simp]
theorem directImageRingSectionsHom_apply (f : X ⟶ Y)
    (O : Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u}) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (a : ToType ((pullbackRingSheaf.{u, u, u, u + 1, u, u + 1}
      (SmallEtale.topology B S hS Y.1) (smallEtaleDirectImage B S hS f) O).obj.obj (op V))) :
    (directImageRingSectionsHom B S hS f O V j).hom a =
      (directImageChartProjection B S hS f V j).app
        ((sheafCompose (SmallEtale.topology B S hS X.1)
          (CategoryTheory.forget RingCat.{u})).obj O) a := rfl

/-- At the structure sheaf of `X`, `AlgebraicGeometry.Space.directImageRingSectionsHom` is
`AlgebraicGeometry.Space.directImageChartProjectionRingHom`. -/
theorem directImageRingSectionsHom_structureRingSheaf (f : X ⟶ Y)
    (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op) :
    directImageRingSectionsHom B S hS f (structureRingSheaf B S hS X) V j =
      directImageChartProjectionRingHom B S hS f V j := rfl

/-- The ring homomorphism commutes with the direct image of a morphism of sheaves of rings. -/
theorem directImageRingSectionsHom_pullbackRingSheafMap (f : X ⟶ Y)
    {O O' : Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u}} (φ : O ⟶ O')
    (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op) :
    (pullbackRingSheafMap (SmallEtale.topology B S hS Y.1)
          (smallEtaleDirectImage B S hS f) φ).hom.app (op V) ≫
        directImageRingSectionsHom B S hS f O' V j =
      directImageRingSectionsHom B S hS f O V j ≫ φ.hom.app j.right :=
  RingCat.hom_ext (RingHom.ext fun a ↦
    directImageChartProjection_ringSheafMap B S hS f V j φ a)

/-! ### The collapse at an index naming the base change -/

/-- The chart projection of a direct image is bijective at an index whose structure morphism is
invertible. -/
theorem bijective_directImageChartProjection_of_isIso_hom (f : X ⟶ Y)
    (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (hj : IsIso j.hom.unop) (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    Function.Bijective ((directImageChartProjection B S hS f V j).app F) := by
  have hπ : Function.Bijective
      ((ranChartCone B S hS X F.obj (chartBaseChange B S hS f V)).π.app j) :=
    (isIso_iff_bijective _).1
      (IsLimit.isIso_π_app_of_isInitial
        (ranChartIsLimit B S hS X F.obj (chartBaseChange B S hS f V)) j
        (isInitial_of_isIso_hom B S hS X j hj))
  have hcmp : Function.Bijective
      (fun a ↦ ((smallEtaleDirectImageRanIso B S hS f).hom.app F).hom.app (op V) a) :=
    Function.bijective_iff_has_inverse.2
      ⟨fun b ↦ ((smallEtaleDirectImageRanIso B S hS f).inv.app F).hom.app (op V) b,
        fun a ↦ Sheaf.hom_congr_app_apply
          (((smallEtaleDirectImageRanIso B S hS f).app F).hom_inv_id) (op V) a,
        fun b ↦ Sheaf.hom_congr_app_apply
          (((smallEtaleDirectImageRanIso B S hS f).app F).inv_hom_id) (op V) b⟩
  have hstep : ∀ a, (directImageChartProjection B S hS f V j).app F a =
      (ranChartCone B S hS X F.obj (chartBaseChange B S hS f V)).π.app j
        (((smallEtaleDirectImageRanIso B S hS f).hom.app F).hom.app (op V) a) := fun a ↦
    (directImageChartProjection_app_apply B S hS f V j F a).trans
      (chartProjection_app_eq_ranChartCone_π B S hS f V j F _)
  refine ⟨fun a b hab ↦ hcmp.1 (hπ.1 ((hstep a).symm.trans (hab.trans (hstep b)))), fun y ↦ ?_⟩
  obtain ⟨c, hc⟩ := hπ.2 y
  obtain ⟨a, ha⟩ := hcmp.2 c
  exact ⟨a, (hstep a).trans ((congrArg
    (fun z ↦ (ranChartCone B S hS X F.obj (chartBaseChange B S hS f V)).π.app j z) ha).trans hc)⟩

/-- At an index whose structure morphism is invertible, the chart projection from the sections of
`f_*O` over `V` to the sections of `O` over the chart naming `X ×_Y V` is bijective. -/
theorem bijective_directImageRingSectionsHom_of_isIso_hom (f : X ⟶ Y)
    (O : Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u}) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (hj : IsIso j.hom.unop) :
    Function.Bijective (directImageRingSectionsHom B S hS f O V j).hom := by
  have h := bijective_directImageChartProjection_of_isIso_hom B S hS f V j hj
    ((sheafCompose (SmallEtale.topology B S hS X.1)
      (CategoryTheory.forget RingCat.{u})).obj O)
  refine ⟨fun a b hab ↦ h.1 ?_, fun y ↦ ?_⟩
  · exact (directImageRingSectionsHom_apply B S hS f O V j a).symm.trans
      (hab.trans (directImageRingSectionsHom_apply B S hS f O V j b))
  · obtain ⟨a, ha⟩ := h.2 y
    exact ⟨a, (directImageRingSectionsHom_apply B S hS f O V j a).trans ha⟩

/-- The same as an isomorphism of `RingCat`. -/
theorem isIso_directImageRingSectionsHom_of_isIso_hom (f : X ⟶ Y)
    (O : Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u}) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (hj : IsIso j.hom.unop) :
    IsIso (directImageRingSectionsHom B S hS f O V j) :=
  (ConcreteCategory.isIso_iff_bijective _).2
    (bijective_directImageRingSectionsHom_of_isIso_hom B S hS f O V j hj)

/-! ### The identification for a relatively representable morphism -/

/-- For a relatively representable morphism, the sections of `f_*O` over an étale scheme chart `V`
of `Y` are the sections of `O` over the base-changed chart `V ×_Y X`, as an isomorphism of
rings. -/
noncomputable def directImageRingSectionsRingEquiv (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom)
    (O : Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u}) (V : SmallEtale B S hS Y.1) :
    ToType ((pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS Y.1)
        (smallEtaleDirectImage B S hS f) O).obj.obj (op V)) ≃+*
      ToType (O.obj.obj (op ((smallBaseChange B S hS f hf).obj V))) :=
  RingEquiv.ofBijective
    (directImageRingSectionsHom B S hS f O V (smallBaseChangeIndex B S hS f hf V)).hom
    (bijective_directImageRingSectionsHom_of_isIso_hom B S hS f O V
      (smallBaseChangeIndex B S hS f hf V)
      (isIso_smallBaseChangeIndex_hom_unop B S hS f hf V))

/-- On sections the isomorphism of rings is the chart projection to the base-changed chart. -/
@[simp]
theorem directImageRingSectionsRingEquiv_apply (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom)
    (O : Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u}) (V : SmallEtale B S hS Y.1)
    (a : ToType ((pullbackRingSheaf.{u, u, u, u + 1, u, u + 1}
      (SmallEtale.topology B S hS Y.1) (smallEtaleDirectImage B S hS f) O).obj.obj (op V))) :
    directImageRingSectionsRingEquiv B S hS f hf O V a =
      (directImageChartProjection B S hS f V
          (smallBaseChangeIndex B S hS f hf V)).app
        ((sheafCompose (SmallEtale.topology B S hS X.1)
          (CategoryTheory.forget RingCat.{u})).obj O) a := rfl

end AlgebraicGeometry.Space

end
