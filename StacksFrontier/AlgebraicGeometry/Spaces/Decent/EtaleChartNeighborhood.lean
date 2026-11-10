module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.MonomorphismPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibers

/-!
# Recognizing an étale chart as an elementary étale neighborhood

Let `c : U ⟶ F` be an étale chart of an algebraic space and let `t` be a field-valued point of
the representable presheaf of `U` whose composite with `c` is a monomorphism. Then `U`, pointed
at the scheme point underlying `t`, is an elementary étale neighborhood of the point of `F`
represented by `t`: the residue-field point at that scheme point represents the same point of
`U`, and does so monomorphically, so the two field-valued points differ by an isomorphism of
field spectra and the composite of the residue-field point with `c` inherits the monomorphy.

## Main definitions

* `AlgebraicGeometry.Space.elementaryEtaleNeighborhoodOfMono`: the elementary étale
  neighborhood carried by such a chart.

## Main results

* `AlgebraicGeometry.Space.mono_of_eq_of_mono`: monicity transports along an equality of
  morphisms.
* `AlgebraicGeometry.Space.pointsToScheme_presheafPoint`: the scheme point underlying the
  point of a representable presheaf given by a point of the representing scheme is that point.
* `AlgebraicGeometry.Space.mono_yoneda_map_residueFieldMap`: the residue-field point of a
  scheme of the site is a monomorphism into the represented presheaf.

## References

* [Stacks Project, Tag 0BGU](https://stacks.math.columbia.edu/tag/0BGU)
* [Stacks Project, Tag 03E1](https://stacks.math.columbia.edu/tag/03E1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- Monicity transports along an equality of morphisms. -/
theorem mono_of_eq_of_mono {C : Type*} [Category C] {A P : C} {u v : A ⟶ P}
    (h : u = v) (hv : Mono v) : Mono u := by rw [h]; exact hv

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The residue-field point of a scheme of the site -/

/-- The canonical morphism from the residue-field point of a scheme of the site into that
scheme is a monomorphism of presheaves: it is one on underlying schemes, the inclusion of the
site is faithful, and Yoneda preserves monomorphisms. -/
theorem mono_yoneda_map_residueFieldMap (U : BigFppfOver B S hS) (u : U.left.1)
    (hu : B.Contains (Spec (.of (U.left.1.residueField u)))) :
    Mono (yoneda.map (residueFieldMap B S hS U u hu)) := by
  have hscheme : Mono ((BigFppfOver.toScheme B S hS).map (residueFieldMap B S hS U u hu)) := by
    change Mono (U.left.1.fromSpecResidueField u)
    infer_instance
  have : Mono (residueFieldMap B S hS U u hu) :=
    Functor.mono_of_mono_map (BigFppfOver.toScheme B S hS) hscheme
  exact inferInstanceAs (Mono (yoneda.map _))

/-- The scheme point underlying the point of a represented presheaf attached to a point of the
representing scheme is that point. -/
theorem pointsToScheme_presheafPoint (U : BigFppfOver B S hS) (u : U.left.1)
    (hu : B.Contains (Spec (.of (U.left.1.residueField u)))) :
    pointsToScheme B S hS U (presheafPoint B S hS U u hu) = u := by
  change U.left.1.fromSpecResidueField u (IsLocalRing.closedPoint _) = u
  exact Scheme.fromSpecResidueField_apply u _

/-- The point of a represented presheaf attached to the scheme point underlying a field-valued
point is the class of that field-valued point. -/
theorem presheafPoint_pointsToScheme (U : BigFppfOver B S hS)
    (t : FieldValuedPoint B S hS (yoneda.obj U))
    (hu : B.Contains (Spec (.of (U.left.1.residueField
      (pointsToScheme B S hS U (t.class B S hS (yoneda.obj U))))))) :
    presheafPoint B S hS U (pointsToScheme B S hS U (t.class B S hS (yoneda.obj U))) hu =
      t.class B S hS (yoneda.obj U) :=
  injective_pointsToScheme B S hS U (pointsToScheme_presheafPoint B S hS U _ hu)

/-! ### Charts pointed by a monomorphic field-valued point -/

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
variable (U : BigFppfOver B S hS) (c : yoneda.obj U ⟶ F)

/-- A field-valued point of an étale chart whose composite with the chart is a monomorphism
presents the residue-field point at its underlying scheme point monomorphically. -/
theorem mono_yoneda_map_residueFieldMap_comp
    (t : FieldValuedPoint B S hS (yoneda.obj U))
    (hmono : Mono (fieldMorphism B S hS (yoneda.obj U) t ≫ c))
    (hu : B.Contains (Spec (.of (U.left.1.residueField
      (pointsToScheme B S hS U (t.class B S hS (yoneda.obj U))))))) :
    Mono (yoneda.map (residueFieldMap B S hS U
      (pointsToScheme B S hS U (t.class B S hS (yoneda.obj U))) hu) ≫ c) := by
  have htmono : Mono (yonedaEquiv.symm t.value) :=
    mono_of_mono (fieldMorphism B S hS (yoneda.obj U) t) c
  -- The residue-field point at the scheme point underlying `t`. This is the very field-valued
  -- point whose class `AlgebraicGeometry.Space.presheafPoint` is, so that its class is
  -- `presheafPoint` by definition and its presenting morphism is the Yoneda image of
  -- `AlgebraicGeometry.Space.residueFieldMap`.
  let v : FieldValuedPoint B S hS (yoneda.obj U) :=
    ⟨U.left.1.residueField (pointsToScheme B S hS U (t.class B S hS (yoneda.obj U))), hu,
      U.left.1.fromSpecResidueField
        (pointsToScheme B S hS U (t.class B S hS (yoneda.obj U))) ≫ U.hom.1,
      residueFieldMap B S hS U
        (pointsToScheme B S hS U (t.class B S hS (yoneda.obj U))) hu⟩
  have hvfield : fieldMorphism B S hS (yoneda.obj U) v =
      yoneda.map (residueFieldMap B S hS U
        (pointsToScheme B S hS U (t.class B S hS (yoneda.obj U))) hu) :=
    fieldMorphism_yoneda B S hS v
  have hvmono : Mono (yonedaEquiv.symm v.value) := by
    rw [show yonedaEquiv.symm v.value = yoneda.map (residueFieldMap B S hS U
      (pointsToScheme B S hS U (t.class B S hS (yoneda.obj U))) hu) from hvfield]
    exact mono_yoneda_map_residueFieldMap B S hS U _ hu
  obtain ⟨e, he⟩ := iso_of_mono_of_point_eq B S hS (yoneda.obj U)
    (isAlgebraicSpace_yoneda B S hS U) v t
    (presheafPoint_pointsToScheme B S hS U t hu)
  have hfac : yoneda.map e.hom ≫ fieldMorphism B S hS (yoneda.obj U) t =
      yoneda.map (residueFieldMap B S hS U
        (pointsToScheme B S hS U (t.class B S hS (yoneda.obj U))) hu) := by
    rw [← hvfield]
    change yoneda.map e.hom ≫ yonedaEquiv.symm t.value = yonedaEquiv.symm _
    rw [yonedaEquiv_symm_naturality_left e.hom (yoneda.obj U) t.value, he]
  exact mono_of_eq_of_mono
    ((congrArg (fun k ↦ k ≫ c) hfac).symm.trans (Category.assoc _ _ _))
    (mono_comp' (IsIso.mono_of_iso (yoneda.map e.hom)) hmono)

/-- **An étale chart pointed by a monomorphic field-valued point is an elementary étale
neighborhood.** The chart is étale, the residue-field point at the scheme point underlying the
given field-valued point represents the same point of the chart, and the two representatives
differ by an isomorphism of field spectra, so the residue-field point maps monomorphically
into the space. -/
def elementaryEtaleNeighborhoodOfMono
    (hc : IsEtale B S hS c) (t : FieldValuedPoint B S hS (yoneda.obj U))
    (hmono : Mono (fieldMorphism B S hS (yoneda.obj U) t ≫ c)) (x : points B S hS F)
    (hx : pointsMap B S hS (yoneda.obj U) c (t.class B S hS (yoneda.obj U)) = x) :
    ElementaryEtaleNeighborhood B S hS F hF x where
  scheme := U
  point := pointsToScheme B S hS U (t.class B S hS (yoneda.obj U))
  residueField_contained := B.residueField_spec_contains U.left.property _
  toSpace := c
  etale_toSpace := hc
  map_point := by rwa [presheafPoint_pointsToScheme B S hS U t]
  mono_residueField := mono_yoneda_map_residueFieldMap_comp B S hS U c t hmono _

end AlgebraicGeometry.Space

end
