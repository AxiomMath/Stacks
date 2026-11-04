module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.MonomorphismPoints

/-!
# Residue fields of a decent algebraic space

A point of an algebraic space over `S` is represented by at most one monomorphism from the
spectrum of a field, up to unique isomorphism over the space, and a decent algebraic space
has such a representative at every point. The field of a chosen representative is the
*residue field* of the space at the point.

A morphism of decent algebraic spaces induces a homomorphism of residue fields at every
point: the spectrum of the residue field of the source maps to the target, hence factors
uniquely through the monomorphic representative of the image point. That homomorphism is an
isomorphism exactly when the composite morphism from the spectrum of the source residue
field to the target space is itself a monomorphism.

## Main definitions

* `AlgebraicGeometry.Space.residueFieldRepresentative` is the chosen monomorphic field-valued
  representative of a point of a decent algebraic space, `AlgebraicGeometry.Space.residueField`
  is its field and `AlgebraicGeometry.Space.residueFieldMorphism` its morphism to the space.
* `AlgebraicGeometry.Space.IsInducedResidueFieldHom` says that a homomorphism of residue
  fields fits in the square over the target cut out by a morphism of decent spaces, and
  `AlgebraicGeometry.Space.residueFieldHom` is the homomorphism a morphism induces.

## Main results

* `AlgebraicGeometry.Space.residueFieldRepresentative_unique`: a monomorphic field-valued
  representative of a point is unique up to unique isomorphism over the space.
* `AlgebraicGeometry.Space.existsUnique_isInducedResidueFieldHom`: the square over the target
  determines the induced homomorphism of residue fields uniquely, and
  `AlgebraicGeometry.Space.residueFieldHom_spec` is that square for the chosen one.
* `AlgebraicGeometry.Space.isIso_residueFieldHom_iff_mono`: the induced homomorphism is an
  isomorphism exactly when the composite morphism out of the spectrum of the source residue
  field is a monomorphism.

## References

* [Stacks Project, Tag 03K4](https://stacks.math.columbia.edu/tag/03K4)
* [Stacks Project, Tag 0EMW](https://stacks.math.columbia.edu/tag/0EMW)
* [Stacks Project, Tag 0EMX](https://stacks.math.columbia.edu/tag/0EMX)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

add_to_stacks 03K4 "injectivity" AlgebraicGeometry.Space.iso_of_mono_of_point_eq
add_to_stacks 03K4 "surjectivity"
  AlgebraicGeometry.Space.IsDecentSpace.hasMonomorphicFieldRepresentative

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-! ### The residue field at a point -/

/-- The chosen field-valued representative of a point of a decent algebraic space whose morphism
to the space is a monomorphism. -/
@[stacks 0EMW "field-valued monomorphism"]
noncomputable def residueFieldRepresentative (hDecent : IsDecentSpace B S hS X)
    (x : points B S hS X) :
    {p : FieldValuedPoint B S hS X //
      p.class B S hS X = x ∧ Mono (fieldMorphism B S hS X p)} :=
  Classical.indefiniteDescription _
    (IsDecentSpace.hasMonomorphicFieldRepresentative B S hS X hDecent x)

/-- The residue field of a decent algebraic space at a point: the field of the monomorphism from
a field spectrum representing that point. -/
@[stacks 0EMW "residue field"]
noncomputable abbrev residueField (hDecent : IsDecentSpace B S hS X)
    (x : points B S hS X) : Type u :=
  (residueFieldRepresentative B S hS X hDecent x).1.carrier

/-- The monomorphism from the spectrum of the residue field at `x` to the space. -/
noncomputable abbrev residueFieldMorphism (hDecent : IsDecentSpace B S hS X)
    (x : points B S hS X) :
    yoneda.obj ((residueFieldRepresentative B S hS X hDecent x).1.siteObject B S hS X) ⟶ X :=
  fieldMorphism B S hS X (residueFieldRepresentative B S hS X hDecent x).1

/-- A monomorphic field-valued representative of a point of a decent algebraic space is uniquely
isomorphic, over the space, to the chosen one: the residue field is unique up to unique
isomorphism. -/
@[stacks 0EMW "uniqueness"]
theorem residueFieldRepresentative_unique (hX : IsAlgebraicSpace B S hS X)
    (hDecent : IsDecentSpace B S hS X) (x : points B S hS X)
    (q : FieldValuedPoint B S hS X) (hq : q.class B S hS X = x)
    (hmq : Mono (fieldMorphism B S hS X q)) :
    ∃! e : yoneda.obj ((residueFieldRepresentative B S hS X hDecent x).1.siteObject B S hS X) ≅
        yoneda.obj (q.siteObject B S hS X),
      e.hom ≫ fieldMorphism B S hS X q = residueFieldMorphism B S hS X hDecent x := by
  let p := (residueFieldRepresentative B S hS X hDecent x).1
  have := (residueFieldRepresentative B S hS X hDecent x).2.2
  obtain ⟨e, he⟩ := iso_of_mono_of_point_eq B S hS X hX p q
    ((residueFieldRepresentative B S hS X hDecent x).2.1.trans hq.symm)
  have hrel : yoneda.map e.hom ≫ fieldMorphism B S hS X q = fieldMorphism B S hS X p := by
    show yoneda.map e.hom ≫ yonedaEquiv.symm q.value = yonedaEquiv.symm p.value
    rw [yonedaEquiv_symm_naturality_left e.hom X q.value, he]
  refine ⟨yoneda.mapIso e, hrel, fun e' he' ↦ ?_⟩
  exact Iso.ext ((cancel_mono (fieldMorphism B S hS X q)).1 (he'.trans hrel.symm))

/-! ### The homomorphism induced by a morphism of decent algebraic spaces -/

variable (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- A homomorphism of residue fields is induced by `f` at `x` when the morphism of field
spectra it defines fits in the square over `Y` formed by the chosen monomorphic
representatives of `x` and of its image. -/
def IsInducedResidueFieldHom (hDecentX : IsDecentSpace B S hS X)
    (hDecentY : IsDecentSpace B S hS Y) (f : X ⟶ Y) (x : points B S hS X)
    (φ : residueField B S hS Y hDecentY (pointsMap B S hS X f x) →+*
      residueField B S hS X hDecentX x) : Prop :=
  let px := (residueFieldRepresentative B S hS X hDecentX x).1
  let py := (residueFieldRepresentative B S hS Y hDecentY (pointsMap B S hS X f x)).1
  ∃ g : px.siteObject B S hS X ⟶ py.siteObject B S hS Y,
    B.inclusion.map g.left = Spec.map (CommRingCat.ofHom φ) ∧
      yoneda.map g ≫ residueFieldMorphism B S hS Y hDecentY (pointsMap B S hS X f x) =
        residueFieldMorphism B S hS X hDecentX x ≫ f

/-- The square over `Y` determines a unique homomorphism of residue fields. -/
theorem existsUnique_isInducedResidueFieldHom (hY : IsAlgebraicSpace B S hS Y)
    (hDecentX : IsDecentSpace B S hS X) (hDecentY : IsDecentSpace B S hS Y)
    (f : X ⟶ Y) (x : points B S hS X) :
    ∃! φ : residueField B S hS Y hDecentY (pointsMap B S hS X f x) →+*
        residueField B S hS X hDecentX x,
      IsInducedResidueFieldHom B S hS X Y hDecentX hDecentY f x φ := by
  classical
  let px := (residueFieldRepresentative B S hS X hDecentX x).1
  let py := (residueFieldRepresentative B S hS Y hDecentY (pointsMap B S hS X f x)).1
  let qx := FieldValuedPoint.map B S hS X f px
  have hclass : py.class B S hS Y = qx.class B S hS Y := by
    rw [(residueFieldRepresentative B S hS Y hDecentY _).2.1,
      ← (residueFieldRepresentative B S hS X hDecentX x).2.1, pointsMap_class]
  have := (residueFieldRepresentative B S hS Y hDecentY (pointsMap B S hS X f x)).2.2
  obtain ⟨g, hg, -⟩ :=
    FieldValuedPoint.existsUnique_factor_of_class_eq_of_mono B S hS Y hY py qx hclass
  dsimp only [qx, FieldValuedPoint.map] at g hg
  let φ : py.carrier →+* px.carrier :=
    ((Spec.fullyFaithful.preimage (B.inclusion.map g.left)).unop).hom
  have hspec : B.inclusion.map g.left = Spec.map (CommRingCat.ofHom φ) := by dsimp [φ]; simp
  have hg' : Y.map g.op py.value = f.app (Opposite.op (px.siteObject B S hS X)) px.value := hg
  have hsquare : yoneda.map g ≫ fieldMorphism B S hS Y py =
      fieldMorphism B S hS X px ≫ f := by
    show yoneda.map g ≫ yonedaEquiv.symm py.value = yonedaEquiv.symm px.value ≫ f
    rw [yonedaEquiv_symm_naturality_left g Y py.value, hg']
    exact (yonedaEquiv_symm_naturality_right (px.siteObject B S hS X) f px.value).symm
  refine ⟨φ, ⟨g, hspec, hsquare⟩, ?_⟩
  rintro φ' ⟨g', hspec', hsquare'⟩
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective
    (hspec'.symm.trans ((congrArg (fun k ↦ B.inclusion.map k.left)
      (yoneda.map_injective ((cancel_mono (fieldMorphism B S hS Y py)).1
        (hsquare'.trans hsquare.symm)))).trans hspec)))

/-- The homomorphism of residue fields induced by a morphism of decent algebraic spaces,
together with the square over `Y` that characterizes it. -/
noncomputable def residueFieldHomData (hY : IsAlgebraicSpace B S hS Y)
    (hDecentX : IsDecentSpace B S hS X) (hDecentY : IsDecentSpace B S hS Y)
    (f : X ⟶ Y) (x : points B S hS X) :
    {φ : residueField B S hS Y hDecentY (pointsMap B S hS X f x) →+*
        residueField B S hS X hDecentX x //
      IsInducedResidueFieldHom B S hS X Y hDecentX hDecentY f x φ} :=
  Classical.indefiniteDescription _
    (existsUnique_isInducedResidueFieldHom B S hS X Y hY hDecentX hDecentY f x).exists

/-- The homomorphism of residue fields induced by a morphism of decent algebraic spaces. -/
noncomputable abbrev residueFieldHom (hY : IsAlgebraicSpace B S hS Y)
    (hDecentX : IsDecentSpace B S hS X) (hDecentY : IsDecentSpace B S hS Y)
    (f : X ⟶ Y) (x : points B S hS X) :
    residueField B S hS Y hDecentY (pointsMap B S hS X f x) →+*
      residueField B S hS X hDecentX x :=
  (residueFieldHomData B S hS X Y hY hDecentX hDecentY f x).1

/-- The induced homomorphism of residue fields sits in the square over `Y`. -/
theorem residueFieldHom_spec (hY : IsAlgebraicSpace B S hS Y)
    (hDecentX : IsDecentSpace B S hS X) (hDecentY : IsDecentSpace B S hS Y)
    (f : X ⟶ Y) (x : points B S hS X) :
    IsInducedResidueFieldHom B S hS X Y hDecentX hDecentY f x
      (residueFieldHom B S hS X Y hY hDecentX hDecentY f x) :=
  (residueFieldHomData B S hS X Y hY hDecentX hDecentY f x).2

/-! ### When a morphism identifies residue fields -/

/-- A morphism of decent algebraic spaces induces an isomorphism of residue fields at a point
exactly when the morphism from the spectrum of the residue field at that point to the target
space is a monomorphism. -/
@[stacks 0EMX]
theorem isIso_residueFieldHom_iff_mono (hY : IsAlgebraicSpace B S hS Y)
    (hDecentX : IsDecentSpace B S hS X) (hDecentY : IsDecentSpace B S hS Y)
    (f : X ⟶ Y) (x : points B S hS X) :
    IsIso (CommRingCat.ofHom (residueFieldHom B S hS X Y hY hDecentX hDecentY f x)) ↔
      Mono (residueFieldMorphism B S hS X hDecentX x ≫ f) := by
  classical
  let φ := residueFieldHom B S hS X Y hY hDecentX hDecentY f x
  let pX := (residueFieldRepresentative B S hS X hDecentX x).1
  let pY := (residueFieldRepresentative B S hS Y hDecentY (pointsMap B S hS X f x)).1
  let q : FieldValuedPoint B S hS Y :=
    { carrier := pX.carrier
      field := pX.field
      contained := pX.contained
      toBase := pX.toBase
      value := f.app (Opposite.op (pX.siteObject B S hS X)) pX.value }
  have hspec := residueFieldHom_spec B S hS X Y hY hDecentX hDecentY f x
  change ∃ g : _, _ ∧ _ at hspec
  obtain ⟨g, hgSpec, hgComm⟩ := hspec
  have hmapSquare : fieldMorphism B S hS Y q = fieldMorphism B S hS X pX ≫ f := by
    show yonedaEquiv.symm q.value = yonedaEquiv.symm pX.value ≫ f
    exact (yonedaEquiv_symm_naturality_right _ f pX.value).symm
  have hpyMono : Mono (fieldMorphism B S hS Y pY) :=
    (residueFieldRepresentative B S hS Y hDecentY (pointsMap B S hS X f x)).2.2
  refine ⟨fun hφ ↦ ?_, fun hmono ↦ ?_⟩
  · have : IsIso (CommRingCat.ofHom φ) := hφ
    have hleftIso : IsIso (B.inclusion.map g.left) := by rw [hgSpec]; infer_instance
    have hgLeftIso : IsIso g.left :=
      (Functor.FullyFaithful.ofFullyFaithful B.inclusion).isIso_of_isIso_map g.left
    have : IsIso ((Over.forget (B.obj hS)).map g) := hgLeftIso
    have : IsIso g := isIso_of_reflects_iso g (Over.forget (B.obj hS))
    have hcomp : Mono (yoneda.map g ≫ fieldMorphism B S hS Y pY) := inferInstance
    rwa [hgComm] at hcomp
  · have hqClass : q.class B S hS Y = (FieldValuedPoint.map B S hS X f pX).class B S hS Y := by
      refine FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS Y ⟨q, ?_, ?_⟩
      · exact ⟨𝟙 (q.siteObject B S hS Y), by simp⟩
      · refine ⟨𝟙 (q.siteObject B S hS Y), ?_⟩
        show Y.map (𝟙 (q.siteObject B S hS Y)).op q.value = q.value
        simp
    have hclass : q.class B S hS Y = pointsMap B S hS X f x := by
      rw [hqClass, ← pointsMap_class, (residueFieldRepresentative B S hS X hDecentX x).2.1]
    have hqmono : Mono (fieldMorphism B S hS Y q) := by rw [hmapSquare]; exact hmono
    obtain ⟨e, he, -⟩ := residueFieldRepresentative_unique B S hS Y hY hDecentY
      (pointsMap B S hS X f x) q hclass hqmono
    have hge : yoneda.map g ≫ e.hom = 𝟙 _ := by
      rw [← cancel_mono (fieldMorphism B S hS Y q), Category.assoc, he, Category.id_comp, hgComm,
        hmapSquare]
    have : IsIso (yoneda.map g) := by rw [(Iso.comp_hom_eq_id e).1 hge]; infer_instance
    have : IsIso g := isIso_of_reflects_iso g yoneda
    have : IsIso g.left := by
      show IsIso ((Over.forget (B.obj hS)).map g)
      infer_instance
    have hleftIso : IsIso (B.inclusion.map g.left) := inferInstance
    rw [hgSpec] at hleftIso
    have : IsIso (Scheme.Spec.map (CommRingCat.ofHom φ).op) := by
      simpa [Scheme.Spec, φ] using hleftIso
    exact (isIso_op_iff _).mp
      ((Functor.FullyFaithful.ofFullyFaithful Scheme.Spec).isIso_of_isIso_map _)

end AlgebraicGeometry.Space

end
