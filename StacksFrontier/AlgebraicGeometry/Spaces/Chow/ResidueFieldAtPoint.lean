module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.Decency
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidueField
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Monomorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations

/-!
# The residue field at a point of a good algebraic space

Let `X` be a good algebraic space over the base of a `BaseSpaceDimensionSituation`. Every point
of `|X|` is then represented by a monomorphism from the spectrum of a field, unique up to unique
isomorphism over `X`; the field is the *residue field* `κ(x)` of `X` at `x`. The space `X` has a
dense open subspace which is a scheme, and at a point lying on such an open subspace the residue
field is the residue field of the corresponding point of that scheme.

## Main definitions

* `AlgebraicGeometry.Space.BaseSpaceDimensionSituation.residueFieldRepresentative` is the
  monomorphic field-valued representative of a point of a good algebraic space,
  `AlgebraicGeometry.Space.BaseSpaceDimensionSituation.residueField` is the residue field
  `κ(x)` it defines and
  `AlgebraicGeometry.Space.BaseSpaceDimensionSituation.residueFieldMorphism` is the
  monomorphism `Spec κ(x) ⟶ X`.

## Main results

* `AlgebraicGeometry.Space.exists_ringEquiv_residueField_of_mono`: the field of an arbitrary
  monomorphic field-valued representative of a point of a decent algebraic space is the
  residue field there, by an isomorphism whose spectrum is the comparison morphism over the
  space.
* `AlgebraicGeometry.Space.exists_ringEquiv_residueField_schemeResidueField_of_mono`: for a
  monomorphism from a representable presheaf into a decent algebraic space, the residue field
  of the space at the image of a point of the representing scheme is the residue field of that
  scheme at the point.
* `AlgebraicGeometry.Space.BaseSpaceDimensionSituation.residueFieldMorphism_spec` and
  `AlgebraicGeometry.Space.BaseSpaceDimensionSituation.residueFieldRepresentative_unique`:
  a point of a good algebraic space is represented by a monomorphism from the spectrum of its
  residue field, and that monomorphism is unique up to unique isomorphism over the space.
* `BaseSpaceDimensionSituation.exists_denseRange_isRepresentable_isOpenSubspace_of_isGood`:
  a good algebraic space has a dense open subspace which is a scheme.
* `BaseSpaceDimensionSituation.exists_ringEquiv_residueField_schemeResidueField`:
  at a point of an open subspace of a good algebraic space which is a scheme, the residue field
  of the space agrees with the residue field of that scheme at the corresponding point.

## References

* [Stacks Project, Tag 0ENW](https://stacks.math.columbia.edu/tag/0ENW)
* [Stacks Project, Tag 03K4](https://stacks.math.columbia.edu/tag/03K4)
* [Stacks Project, Tag 06NH](https://stacks.math.columbia.edu/tag/06NH)
* [Stacks Project, Tag 086U](https://stacks.math.columbia.edu/tag/086U)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EMW](https://stacks.math.columbia.edu/tag/0EMW)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section General

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The field of a monomorphic field-valued representative of a point of a decent algebraic
space is the residue field there, by an isomorphism whose spectrum is a morphism of the site
fitting in the square over the space. -/
theorem exists_ringEquiv_residueField_of_mono (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (x : points B S hS X) (q : FieldValuedPoint B S hS X)
    (hq : q.class B S hS X = x) (hmono : Mono (fieldMorphism B S hS X q)) :
    ∃ (φ : residueField B S hS X hdec x ≃+* q.carrier)
      (g : q.siteObject B S hS X ⟶
        (residueFieldRepresentative B S hS X hdec x).1.siteObject B S hS X),
      B.inclusion.map g.left = Spec.map (CommRingCat.ofHom φ.toRingHom) ∧
        yoneda.map g ≫ residueFieldMorphism B S hS X hdec x = fieldMorphism B S hS X q := by
  classical
  obtain ⟨e, he, -⟩ := residueFieldRepresentative_unique B S hS X hX hdec x q hq hmono
  set g := yoneda.preimage e.inv
  have hg : yoneda.map g = e.inv := yoneda.map_preimage _
  have hgIsoMap : IsIso (yoneda.map g) := by rw [hg]; infer_instance
  have hgIso : IsIso g := isIso_of_reflects_iso g yoneda
  set φ₀ := ((Spec.fullyFaithful.preimage (B.inclusion.map g.left)).unop).hom with hφDef
  have hspec : B.inclusion.map g.left = Spec.map (CommRingCat.ofHom φ₀) := by simp [hφDef]
  have hleftIso : IsIso (B.inclusion.map g.left) := by
    show IsIso ((BigFppfOver.toScheme B S hS).map g)
    infer_instance
  have hφiso : IsIso (Spec.map (CommRingCat.ofHom φ₀)) := by rw [← hspec]; infer_instance
  have hSpecIso : IsIso (Scheme.Spec.map (CommRingCat.ofHom φ₀).op) := hφiso
  have hopIso : IsIso (CommRingCat.ofHom φ₀).op := Spec.fullyFaithful.isIso_of_isIso_map _
  have hofIso : IsIso (CommRingCat.ofHom φ₀) := isIso_of_op _
  refine ⟨RingEquiv.ofBijective φ₀ (ConcreteCategory.bijective_of_isIso (CommRingCat.ofHom φ₀)),
    g, hspec, ?_⟩
  rw [hg, ← he, Iso.inv_hom_id_assoc]

/-- The residue field of a decent algebraic space at the image of a point `u` of a scheme
mapping to it by a monomorphism out of the presheaf the scheme represents is the residue field
of that scheme at `u`. -/
theorem exists_ringEquiv_residueField_schemeResidueField_of_mono
    (hX : IsAlgebraicSpace B S hS X) (hdec : IsDecentSpace B S hS X)
    (T : BigFppfOver B S hS) (j : yoneda.obj T ⟶ X) (hj : Mono j)
    (u : (BigFppfOver.toScheme B S hS).obj T) (x : points B S hS X)
    (hu : pointsMap B S hS (yoneda.obj T) j
      ((schemePointRepresentative B S hS T u).class B S hS (yoneda.obj T)) = x) :
    ∃ (φ : residueField B S hS X hdec x ≃+*
        ((BigFppfOver.toScheme B S hS).obj T).residueField u)
      (g : (schemePointRepresentative B S hS T u).siteObject B S hS (yoneda.obj T) ⟶
        (residueFieldRepresentative B S hS X hdec x).1.siteObject B S hS X),
      B.inclusion.map g.left = Spec.map (CommRingCat.ofHom φ.toRingHom) ∧
        yoneda.map g ≫ residueFieldMorphism B S hS X hdec x =
          yoneda.map (schemePointRepresentative B S hS T u).siteHom ≫ j := by
  classical
  have hmonorep : Mono (yoneda.map (schemePointRepresentative B S hS T u).siteHom) := by
    rw [← fieldMorphism_yoneda B S hS (schemePointRepresentative B S hS T u)]
    exact mono_fieldMorphism_schemePointRepresentative B S hS T u
  have hqmor : fieldMorphism B S hS X (FieldValuedPoint.map B S hS (yoneda.obj T) j
        (schemePointRepresentative B S hS T u)) =
      yoneda.map (schemePointRepresentative B S hS T u).siteHom ≫ j :=
    fieldMorphism_map_yoneda B S hS X j (schemePointRepresentative B S hS T u)
  have hmonoq : Mono (fieldMorphism B S hS X (FieldValuedPoint.map B S hS (yoneda.obj T) j
      (schemePointRepresentative B S hS T u))) := by
    rw [hqmor]; exact mono_comp' hmonorep hj
  have hqclass : (FieldValuedPoint.map B S hS (yoneda.obj T) j
      (schemePointRepresentative B S hS T u)).class B S hS X = x := by
    rwa [← pointsMap_class]
  obtain ⟨φ, g, hgspec, hgsq⟩ :=
    exists_ringEquiv_residueField_of_mono B S hS hX hdec x _ hqclass hmonoq
  exact ⟨φ, g, hgspec, hgsq.trans hqmor⟩

end General

section Situation

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- The monomorphic field-valued representative of a point of a good algebraic space over the
base of a `BaseSpaceDimensionSituation`, together with the two properties characterizing it:
that it represents the point, and that its morphism to the space is a monomorphism. -/
noncomputable abbrev BaseSpaceDimensionSituation.residueFieldRepresentative (f : X ⟶ D.space)
    (hf : D.IsGood f) (x : points D.site D.base D.base_mem X) :
    {p : FieldValuedPoint D.site D.base D.base_mem X //
      p.class D.site D.base D.base_mem X = x ∧
        Mono (fieldMorphism D.site D.base D.base_mem X p)} :=
  _root_.AlgebraicGeometry.Space.residueFieldRepresentative D.site D.base D.base_mem X
    (D.isDecentSpace_of_isGood f hf) x

/-- The residue field `κ(x)` of a good algebraic space over the base of a
`BaseSpaceDimensionSituation` at a point `x` of `|X|`: the field of the monomorphism from a field
spectrum representing `x`. -/
@[stacks 0ENW]
noncomputable abbrev BaseSpaceDimensionSituation.residueField (f : X ⟶ D.space)
    (hf : D.IsGood f) (x : points D.site D.base D.base_mem X) : Type u :=
  (D.residueFieldRepresentative f hf x).1.carrier

/-- The monomorphism `Spec κ(x) ⟶ X` representing a point `x` of a good algebraic space over
the base of a `BaseSpaceDimensionSituation`. -/
noncomputable abbrev BaseSpaceDimensionSituation.residueFieldMorphism (f : X ⟶ D.space)
    (hf : D.IsGood f) (x : points D.site D.base D.base_mem X) :
    yoneda.obj ((D.residueFieldRepresentative f hf x).1.siteObject
      D.site D.base D.base_mem X) ⟶ X :=
  fieldMorphism D.site D.base D.base_mem X (D.residueFieldRepresentative f hf x).1

/-- A point `x` of a good algebraic space over the base of a `BaseSpaceDimensionSituation` is
represented by the morphism `Spec κ(x) ⟶ X` out of the spectrum of its residue field, and that
morphism is a monomorphism. -/
@[stacks 0ENW "a point is represented by a monomorphism from the spectrum of its residue \
  field"]
theorem BaseSpaceDimensionSituation.residueFieldMorphism_spec (f : X ⟶ D.space)
    (hf : D.IsGood f) (x : points D.site D.base D.base_mem X) :
    (D.residueFieldRepresentative f hf x).1.class D.site D.base D.base_mem X = x ∧
      Mono (D.residueFieldMorphism f hf x) :=
  (D.residueFieldRepresentative f hf x).2

/-- The monomorphism from a field spectrum representing a point `x` of a good algebraic space
over the base of a `BaseSpaceDimensionSituation` is unique: any monomorphic field-valued
representative of `x` is uniquely isomorphic, over the space, to `Spec κ(x) ⟶ X`. -/
@[stacks 0ENW "the monomorphism from a field spectrum representing a point is unique up to \
  unique isomorphism over the space"]
theorem BaseSpaceDimensionSituation.residueFieldRepresentative_unique (f : X ⟶ D.space)
    (hf : D.IsGood f) (x : points D.site D.base D.base_mem X)
    (q : FieldValuedPoint D.site D.base D.base_mem X)
    (hq : q.class D.site D.base D.base_mem X = x)
    (hmq : Mono (fieldMorphism D.site D.base D.base_mem X q)) :
    ∃! e : yoneda.obj ((D.residueFieldRepresentative f hf x).1.siteObject
        D.site D.base D.base_mem X) ≅
        yoneda.obj (q.siteObject D.site D.base D.base_mem X),
      e.hom ≫ fieldMorphism D.site D.base D.base_mem X q = D.residueFieldMorphism f hf x :=
  _root_.AlgebraicGeometry.Space.residueFieldRepresentative_unique D.site D.base D.base_mem X
    hf.1 (D.isDecentSpace_of_isGood f hf) x q hq hmq

/-- A good algebraic space over the base of a `BaseSpaceDimensionSituation` has a dense open
subspace which is a scheme. -/
@[stacks 0ENW "a good algebraic space has a dense open subspace which is a scheme"]
theorem BaseSpaceDimensionSituation.exists_denseRange_isRepresentable_isOpenSubspace_of_isGood
    (f : X ⟶ D.space) (hf : D.IsGood f) :
    ∃ G : Subfunctor X, IsOpenSubspace D.site D.base D.base_mem G ∧
      G.toFunctor.IsRepresentable ∧
      DenseRange (pointsMap D.site D.base D.base_mem G.toFunctor G.ι) :=
  exists_denseRange_isRepresentable_isOpenSubspace_of_isDecentSpace D.site D.base D.base_mem
    hf.1 (D.isDecentSpace_of_isGood f hf)

/-- Let `X/B` be good over the base of a `BaseSpaceDimensionSituation` and let `U ⊆ X` be an
open subspace which is a scheme, presented by an open immersion out of the presheaf
represented by an object of the site. At a point `x` of `|X|` coming from a point `u` of that
scheme, the residue field `κ(x)` agrees with the residue field of `u` on `U` as a scheme: they
are isomorphic by an isomorphism whose spectrum is the comparison morphism over `X`. -/
@[stacks 0ENW "at a point of an open subspace which is a scheme the residue field agrees \
  with the residue field of the corresponding point on that scheme"]
theorem BaseSpaceDimensionSituation.exists_ringEquiv_residueField_schemeResidueField
    (f : X ⟶ D.space) (hf : D.IsGood f) (T : BigFppfOver D.site D.base D.base_mem)
    (j : yoneda.obj T ⟶ X) (hj : IsOpenImmersion D.site D.base D.base_mem j)
    (u : (BigFppfOver.toScheme D.site D.base D.base_mem).obj T)
    (x : points D.site D.base D.base_mem X)
    (hu : pointsMap D.site D.base D.base_mem (yoneda.obj T) j
      ((schemePointRepresentative D.site D.base D.base_mem T u).class
        D.site D.base D.base_mem (yoneda.obj T)) = x) :
    ∃ (φ : D.residueField f hf x ≃+*
        ((BigFppfOver.toScheme D.site D.base D.base_mem).obj T).residueField u)
      (g : (schemePointRepresentative D.site D.base D.base_mem T u).siteObject
          D.site D.base D.base_mem (yoneda.obj T) ⟶
        (D.residueFieldRepresentative f hf x).1.siteObject D.site D.base D.base_mem X),
      D.site.inclusion.map g.left = Spec.map (CommRingCat.ofHom φ.toRingHom) ∧
        yoneda.map g ≫ D.residueFieldMorphism f hf x =
          yoneda.map (schemePointRepresentative D.site D.base D.base_mem T u).siteHom ≫ j :=
  exists_ringEquiv_residueField_schemeResidueField_of_mono D.site D.base D.base_mem hf.1
    (D.isDecentSpace_of_isGood f hf) T j
    (mono_of_isImmersion D.site D.base D.base_mem
      (isImmersion_of_isOpenImmersion D.site D.base D.base_mem hj))
    u x hu

end Situation

end AlgebraicGeometry.Space

end
