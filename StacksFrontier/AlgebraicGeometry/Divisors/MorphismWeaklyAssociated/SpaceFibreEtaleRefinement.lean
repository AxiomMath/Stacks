module

public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceFieldBaseChange
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceFibreRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibreFieldRepresentative
import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization

/-!
# Weak association across a refinement of a field-valued point of the target

Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`, let `q` refine `p` as a
field-valued point of `Y` through `κ : q.siteObject ⟶ p.siteObject`, and let `F` be an
`𝒪_X`-module. The fibre of `f` over `q` is then the base change of the fibre of `f` over `p`
along the morphism of field spectra `κ` presents, by
`AlgebraicGeometry.Space.exists_fibreMap_isPullback_of_refines`, and the restriction of `F` to
the one fibre is the pullback of its restriction to the other. Weak association therefore
transfers across the comparison morphism of fibres in each of the two ways such a base change
permits:

* it *descends*, from a point of the fibre over `q` to its image in the fibre over `p`, by
  Stacks 0CUS, the refinement being a field extension; and
* it transfers *in both directions* when the morphism of field spectra is étale, by
  Stacks 0CUU.

## Main definitions

* `AlgebraicGeometry.Space.refinementRingHom` and
  `AlgebraicGeometry.Space.refinementAlgebra`: the morphism of fields, and the algebra
  structure, underlying a morphism of the objects of the site two field-valued points are
  defined on.
* `AlgebraicGeometry.Space.fieldValuedPointSpace` and
  `AlgebraicGeometry.Space.fibreAtFieldValuedPointStructure`: the algebraic space represented
  by the object of the site a field-valued point is defined on, and the structure morphism to
  it from the fibre over that point.

## Main results

* `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_fibre_of_refines`: **Stacks 0CUS at a
  refinement of field-valued points**, the pointwise descent of weak association along the
  comparison of fibres.
* `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_fibre_refines_iff_of_isEtale`:
  **Stacks 0CUU at an étale refinement of field-valued points**, the two-way transfer.
* `AlgebraicGeometry.Space.exists_fieldValuedPoint_fibre_isEtale_siteHom`: a point of the fibre
  of an étale morphism of the target over a field-valued point has a field-valued
  representative whose morphism of field spectra to that point is étale.

## References

* [Stacks Project, Tag 0CUZ](https://stacks.math.columbia.edu/tag/0CUZ)
* [Stacks Project, Tag 0CUS](https://stacks.math.columbia.edu/tag/0CUS)
* [Stacks Project, Tag 0CUU](https://stacks.math.columbia.edu/tag/0CUU)
* [Stacks Project, Tag 02GL](https://stacks.math.columbia.edu/tag/02GL)
* [Stacks Project, Tag 03DP](https://stacks.math.columbia.edu/tag/03DP)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The field extension underlying a refinement -/

section Refinement

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The morphism of fields underlying a morphism between the objects of the site two
field-valued points are defined on: the global sections of the morphism of field spectra it
induces, read through the identification of the global sections of an affine scheme with its
ring. -/
noncomputable def refinementRingHom {p q : FieldValuedPoint B S hS F}
    (κ : q.siteObject ⟶ p.siteObject) :
    CommRingCat.of p.carrier ⟶ CommRingCat.of q.carrier :=
  (Scheme.ΓSpecIso (CommRingCat.of p.carrier)).inv ≫
    (show Spec (CommRingCat.of q.carrier) ⟶ Spec (CommRingCat.of p.carrier) from
      (BigFppfOver.toScheme B S hS).map κ).appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of q.carrier)).hom

/-- The morphism of field spectra underlying a morphism of the objects of the site is the
spectrum of the morphism of fields underlying it. -/
theorem specMap_refinementRingHom {p q : FieldValuedPoint B S hS F}
    (κ : q.siteObject ⟶ p.siteObject) :
    Spec.map (refinementRingHom B S hS κ) =
      (show Spec (CommRingCat.of q.carrier) ⟶ Spec (CommRingCat.of p.carrier) from
        (BigFppfOver.toScheme B S hS).map κ) := by
  rw [refinementRingHom, Spec.map_comp, Spec.map_comp, ← Scheme.isoSpec_Spec_hom,
    ← Scheme.isoSpec_Spec_inv, Category.assoc, Scheme.isoSpec_hom_naturality_assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- The algebra structure on the field of a field-valued point over the field of a point it
refines, induced by a morphism of the objects of the site. -/
@[instance_reducible] noncomputable def refinementAlgebra
    {p q : FieldValuedPoint B S hS F}
    (κ : q.siteObject ⟶ p.siteObject) : Algebra p.carrier q.carrier :=
  (refinementRingHom B S hS κ).hom.toAlgebra

/-- The morphism of field spectra underlying a morphism of the objects of the site is the
spectrum of the structure morphism of the algebra it induces. -/
theorem specMap_algebraMap_refinementAlgebra {p q : FieldValuedPoint B S hS F}
    (κ : q.siteObject ⟶ p.siteObject) :
    letI := refinementAlgebra B S hS κ
    Spec.map (CommRingCat.ofHom (algebraMap p.carrier q.carrier)) =
      (show Spec (CommRingCat.of q.carrier) ⟶ Spec (CommRingCat.of p.carrier) from
        (BigFppfOver.toScheme B S hS).map κ) :=
  specMap_refinementRingHom B S hS κ

end Refinement

/-! ### The fibre over a field-valued point and its structure morphism -/

variable {X Y : AlgebraicSpaces B S hS}

/-- The algebraic space represented by the object of the site a field-valued point is defined
on: the spectrum of its field, as an object over `S`. -/
noncomputable abbrev fieldValuedPointSpace {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : FieldValuedPoint B S hS F) : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj p.siteObject, isAlgebraicSpace_yoneda B S hS p.siteObject⟩

/-- The structure morphism of the fibre of `f` over a field-valued point `p` of the target to
the spectrum of the field of `p`. -/
noncomputable abbrev fibreAtFieldValuedPointStructure (f : X ⟶ Y)
    (p : FieldValuedPoint B S hS Y.1) :
    fibreAtFieldValuedPoint B S hS f p ⟶ fieldValuedPointSpace B S hS p :=
  ObjectProperty.homMk (pullback.snd f.hom (fieldMorphism B S hS Y.1 p))

/-- The morphism of algebraic spaces presented by a morphism of the objects of the site two
field-valued points are defined on. -/
noncomputable abbrev fieldValuedPointSpaceMap {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p q : FieldValuedPoint B S hS F} (κ : q.siteObject ⟶ p.siteObject) :
    fieldValuedPointSpace B S hS q ⟶ fieldValuedPointSpace B S hS p :=
  ObjectProperty.homMk (yoneda.map κ)

/-! ### Descent along a refinement -/

/-- **Weak association descends along a refinement of field-valued points.** Let `f : X ⟶ Y`
be a morphism of algebraic spaces over `S`, let `F` be a quasi-coherent `𝒪_X`-module, let `q`
refine `p` as a field-valued point of `Y` through `κ : q.siteObject ⟶ p.siteObject`, and let `π`
be the comparison morphism of the fibre of `f` over `q` with the fibre of `f` over `p`,
compatible with the projections to `X` and presenting the one fibre as the base change of the
other along `κ`. If a point of the fibre over `q` is weakly associated to the restriction of `F`
there, then its image in the fibre over `p` is weakly associated to the restriction of `F`
there. -/
@[stacks 0CUS "at a refinement of field-valued points of the target, read on the comparison of \
the two fibres"]
theorem isWeaklyAssociatedPoint_fibre_of_refines (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    {p q : FieldValuedPoint B S hS Y.1} (κ : q.siteObject ⟶ p.siteObject)
    {π : fibreAtFieldValuedPoint B S hS f q ⟶ fibreAtFieldValuedPoint B S hS f p}
    (hπ : π ≫ fibreAtFieldValuedPointProjection B S hS f p =
      fibreAtFieldValuedPointProjection B S hS f q)
    (sq : IsPullback π.hom (pullback.snd f.hom (fieldMorphism B S hS Y.1 q))
      (pullback.snd f.hom (fieldMorphism B S hS Y.1 p)) (yoneda.map κ))
    {ζ : points B S hS (fibreAtFieldValuedPoint B S hS f q).1}
    (h : IsWeaklyAssociatedPoint B S hS (fibreAtFieldValuedPoint B S hS f q)
      ((modulePullback B S hS (fibreAtFieldValuedPointProjection B S hS f q)).obj F) ζ) :
    IsWeaklyAssociatedPoint B S hS (fibreAtFieldValuedPoint B S hS f p)
      ((modulePullback B S hS (fibreAtFieldValuedPointProjection B S hS f p)).obj F)
      (pointsMap B S hS (fibreAtFieldValuedPoint B S hS f q).1 π.hom ζ) := by
  let := refinementAlgebra B S hS κ
  have hFp : ((modulePullback B S hS
      (fibreAtFieldValuedPointProjection B S hS f p)).obj F).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      (fibreAtFieldValuedPointProjection B S hS f p) F hF
  have sq' : IsPullback π (fibreAtFieldValuedPointStructure B S hS f q)
      (fibreAtFieldValuedPointStructure B S hS f p)
      (fieldValuedPointSpaceMap B S hS κ) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι fun G ↦ IsAlgebraicSpace B S hS G) sq
  refine isWeaklyAssociatedPoint_of_fieldBaseChange B S hS p.carrier q.carrier
    p.siteObject q.siteObject κ (fibreAtFieldValuedPointStructure B S hS f p)
    (fibreAtFieldValuedPointStructure B S hS f q) (fieldValuedPointSpaceMap B S hS κ) π sq'
    (Iso.refl _) (Iso.refl _) ?_ (Iso.refl _) (Iso.refl _) (by simp) _ ζ ?_
  · simp only [Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.comp_id]
    exact (specMap_algebraMap_refinementAlgebra B S hS κ).symm
  · exact (isWeaklyAssociatedPoint_congr B S hS
      ((modulePullbackCompIso B S hS π
            (fibreAtFieldValuedPointProjection B S hS f p)).app F ≪≫
        eqToIso (congrArg (fun k ↦ (modulePullback B S hS k).obj F) hπ)) ζ).2 h

/-! ### Transfer along an étale refinement -/

/-- **Weak association transfers along an étale refinement of field-valued points.** In the
situation of `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_fibre_of_refines`, with `F` an
arbitrary `𝒪_X`-module, if the morphism of field spectra the refinement presents is étale, then a
point of the fibre over `q` is weakly associated to the restriction of `F` exactly when its image
in the fibre over `p` is. -/
@[stacks 0CUU "at an etale refinement of field-valued points of the target, read on the \
comparison of the two fibres"]
theorem isWeaklyAssociatedPoint_fibre_refines_iff_of_isEtale (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2)
    {p q : FieldValuedPoint B S hS Y.1} (κ : q.siteObject ⟶ p.siteObject)
    (hκ : IsEtale B S hS (yoneda.map κ))
    {π : fibreAtFieldValuedPoint B S hS f q ⟶ fibreAtFieldValuedPoint B S hS f p}
    (hπ : π ≫ fibreAtFieldValuedPointProjection B S hS f p =
      fibreAtFieldValuedPointProjection B S hS f q)
    (sq : IsPullback π.hom (pullback.snd f.hom (fieldMorphism B S hS Y.1 q))
      (pullback.snd f.hom (fieldMorphism B S hS Y.1 p)) (yoneda.map κ))
    (ζ : points B S hS (fibreAtFieldValuedPoint B S hS f q).1) :
    IsWeaklyAssociatedPoint B S hS (fibreAtFieldValuedPoint B S hS f q)
        ((modulePullback B S hS (fibreAtFieldValuedPointProjection B S hS f q)).obj F) ζ ↔
      IsWeaklyAssociatedPoint B S hS (fibreAtFieldValuedPoint B S hS f p)
        ((modulePullback B S hS (fibreAtFieldValuedPointProjection B S hS f p)).obj F)
        (pointsMap B S hS (fibreAtFieldValuedPoint B S hS f q).1 π.hom ζ) := by
  have sq' : IsPullback π (fibreAtFieldValuedPointStructure B S hS f q)
      (fibreAtFieldValuedPointStructure B S hS f p)
      (fieldValuedPointSpaceMap B S hS κ) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι fun G ↦ IsAlgebraicSpace B S hS G) sq
  have hπe : IsEtale B S hS π.hom :=
    isEtale_of_isPullback B S hS (fibreAtFieldValuedPointStructure B S hS f q) π
      (fieldValuedPointSpaceMap B S hS κ) (fibreAtFieldValuedPointStructure B S hS f p)
      sq'.flip hκ
  refine (isWeaklyAssociatedPoint_congr B S hS
      ((modulePullbackCompIso B S hS π
            (fibreAtFieldValuedPointProjection B S hS f p)).app F ≪≫
        eqToIso (congrArg (fun k ↦ (modulePullback B S hS k).obj F) hπ)) ζ).symm.trans
    (isWeaklyAssociatedPoint_modulePullback_iff B S hS π hπe _ ζ)

/-! ### An étale refinement through an étale morphism of the target -/

variable {Y' : AlgebraicSpaces B S hS}

/-- **An étale refinement of a field-valued point, read off a point of the fibre of an étale
morphism of the target.** Let `g : Y' ⟶ Y` be an étale morphism of algebraic spaces over `S`,
let `p` be a field-valued point of `Y` and let `η` be a point of the fibre of `g` over `p`.
Then `η` has a field-valued representative whose field is, over the field of `p`, the residue
field of a point of a scheme étale over its spectrum: the morphism of field spectra from the
representative to `p` is étale. -/
theorem exists_fieldValuedPoint_fibre_isEtale_siteHom (g : Y' ⟶ Y)
    (hg : IsEtale B S hS g.hom) (p : FieldValuedPoint B S hS Y.1)
    (η : points B S hS (fibreAtFieldValuedPoint B S hS g p).1) :
    ∃ n : FieldValuedPoint B S hS (fibreAtFieldValuedPoint B S hS g p).1,
      n.class B S hS (fibreAtFieldValuedPoint B S hS g p).1 = η ∧
        IsEtale B S hS (yoneda.map (FieldValuedPoint.map B S hS
          (fibreAtFieldValuedPoint B S hS g p).1
          (pullback.snd g.hom (fieldMorphism B S hS Y.1 p)) n).siteHom) := by
  have hsn : IsEtale B S hS (pullback.snd g.hom (fieldMorphism B S hS Y.1 p)) :=
    isEtale_of_isPullback B S hS (fibreAtFieldValuedPointProjection B S hS g p)
      (fibreAtFieldValuedPointStructure B S hS g p) g
      (ObjectProperty.homMk (fieldMorphism B S hS Y.1 p) :
        fieldValuedPointSpace B S hS p ⟶ Y)
      (IsPullback.of_map_of_faithful (ObjectProperty.ι fun G ↦ IsAlgebraicSpace B S hS G)
        (IsPullback.of_hasPullback g.hom (fieldMorphism B S hS Y.1 p))) hg
  obtain ⟨U, α, ω, hα, hαω, -, -⟩ := exists_etale_scheme_chart_through_point B S hS
    (fibreAtFieldValuedPoint B S hS g p).2 (𝟙 (fibreAtFieldValuedPoint B S hS g p).1)
    (isEtale_id B S hS (fibreAtFieldValuedPoint B S hS g p).1) η
  set ρ := schemePointRepresentative B S hS U (pointsToScheme B S hS U ω) with hρ
  refine ⟨FieldValuedPoint.map B S hS (yoneda.obj U) α ρ, ?_, ?_⟩
  · rwa [← pointsMap_class, hρ, class_schemePointRepresentative_pointsToScheme]
  set β := yoneda.preimage (α ≫ pullback.snd g.hom (fieldMorphism B S hS Y.1 p)) with hβ
  have hβmap : yoneda.map β = α ≫ pullback.snd g.hom (fieldMorphism B S hS Y.1 p) :=
    yoneda.map_preimage _
  have hβetale : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map β) :=
    (presheaf_yoneda_map_etale_iff B S hS β).1
      ((isEtale_iff_presheaf_of_yoneda B S hS (yoneda.map β)).1
        (hβmap ▸ isEtale_comp B S hS hα hsn))
  have hκ : (FieldValuedPoint.map B S hS (fibreAtFieldValuedPoint B S hS g p).1
      (pullback.snd g.hom (fieldMorphism B S hS Y.1 p))
      (FieldValuedPoint.map B S hS (yoneda.obj U) α ρ)).siteHom = ρ.siteHom ≫ β := by
    show (α ≫ pullback.snd g.hom (fieldMorphism B S hS Y.1 p)).app
      (Opposite.op ρ.siteObject) ρ.value = ρ.siteHom ≫ β
    rw [← hβmap]
    rfl
  rw [hκ]
  refine (isEtale_iff_presheaf_of_yoneda B S hS _).2
    ((presheaf_yoneda_map_etale_iff B S hS (ρ.siteHom ≫ β)).2 ?_)
  rw [Functor.map_comp, hρ, toScheme_map_siteHom_schemePointRepresentative]
  exact etale_comp_of_mono_of_etale_to_spec_field p.carrier
    (((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField
      (pointsToScheme B S hS U ω))
    inferInstance
    (show (BigFppfOver.toScheme B S hS).obj U ⟶ Spec (CommRingCat.of p.carrier) from
      (BigFppfOver.toScheme B S hS).map β)
    hβetale

end AlgebraicGeometry.Space

end
