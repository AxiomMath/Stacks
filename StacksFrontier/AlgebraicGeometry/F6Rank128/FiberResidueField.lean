module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.FinTrdeg

/-!
# Residue fields along a morphism surjective on stalks, and on a scheme-theoretic fibre

A morphism of schemes which is surjective on stalks induces a surjection of residue fields, and
a homomorphism of fields is injective, so the induced map on residue fields is an isomorphism.
The scheme-theoretic fibre `X_y = X ×_Y Spec κ(y)` is the main example: its projection
`f.fiberι y` to `X` is a base change of `Spec κ(y) ⟶ Y`, hence a preimmersion, so a point `x`
of `X` and the corresponding point `f.asFiber x` of the fibre over `f x` have canonically
isomorphic residue fields.

That isomorphism is one of `κ(f x)`-algebras, where the fibre is a `κ(f x)`-scheme through
`Scheme.Hom.fiberToSpecResidueField` and `κ(x)` is a `κ(f x)`-algebra through
`Scheme.Hom.residueFieldMap`. Consequently the two residue fields have the same transcendence
degree over `κ(f x)`. This is what lets the dimension formula for a scheme over a field be read
on a fibre: the transcendence degree appearing in the formula for the fibre over `f x`, taken
at `f.asFiber x`, is the transcendence degree of `κ(x)` over `κ(f x)`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.bijective_residueFieldMap`: the residue field map of a morphism
  surjective on stalks is bijective.
* `AlgebraicGeometry.SpecMap_algebraMap_residueField`: the algebra structure a morphism to
  `Spec A` puts on a residue field is characterised geometrically by
  `Scheme.fromSpecResidueField`.
* `AlgebraicGeometry.Scheme.Hom.fiberResidueFieldHom`: the comparison map from `κ(x)` to the
  residue field of the fibre over `f x` at `f.asFiber x`, shown bijective by
  `AlgebraicGeometry.Scheme.Hom.bijective_fiberResidueFieldHom` and characterised geometrically
  by `AlgebraicGeometry.Scheme.Hom.SpecMap_fiberResidueFieldHom`.
* `AlgebraicGeometry.Scheme.Hom.fiberResidueFieldHom_algebraMap`: the comparison map is one of
  `κ(f x)`-algebras.
* `AlgebraicGeometry.Scheme.Hom.trdeg_residueField_fiber`: the two residue fields have equal
  transcendence degree over `κ(f x)`.

## Implementation notes

The `κ(f x)`-algebra structure on a residue field is not an instance; as everywhere else in the
dimension theory of this library, each statement introduces it in its own `let` binding. On the
fibre the canonical choice is the one induced by `Scheme.Hom.fiberToSpecResidueField`, written
through global sections and evaluation so that it matches the form the dimension formula
`AlgebraicGeometry.topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk` uses; on `κ(x)` it is
`Scheme.Hom.residueFieldMap`, which is definitionally the algebra map.

The comparison is packaged as a morphism of `CommRingCat` rather than a `RingEquiv`, because
`κ(x)` carries both a `Field` and a `CommRing` instance path and `CommRingCat.ofHom` applied to
a `RingEquiv.toRingHom` picks the former, which then does not match the composites appearing in
the geometric lemmas. The `RingEquiv` and the `AlgEquiv` are assembled where they are used.

The compatibility of the two algebra structures is proved geometrically rather than by
unfolding: both `Spec.map`s agree after composing with the monomorphism
`Y.fromSpecResidueField (f x)`, and `Spec` is faithful.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- A morphism which is surjective on stalks induces a bijection of residue fields: the induced
map is surjective because the stalk map is, and injective because it is a homomorphism of
fields. -/
theorem Scheme.Hom.bijective_residueFieldMap (i : Y ⟶ X) [SurjectiveOnStalks i] (y : Y) :
    Function.Bijective (i.residueFieldMap y).hom := by
  refine ⟨(i.residueFieldMap y).hom.injective, ?_⟩
  have h := (Y.residue_surjective y).comp (i.stalkMap_surjective y)
  change Function.Surjective (i.stalkMap y ≫ Y.residue y).hom at h
  rw [← Scheme.residue_residueFieldMap i y, CommRingCat.hom_comp, RingHom.coe_comp] at h
  exact h.of_comp

/-- The `A`-algebra structure that a morphism `g : Z ⟶ Spec A` puts on a residue field of `Z`
is characterised geometrically: `Spec` of its algebra map is `Z.fromSpecResidueField z ≫ g`. -/
theorem SpecMap_algebraMap_residueField {Z : Scheme.{u}} {A : CommRingCat.{u}} (g : Z ⟶ Spec A)
    (z : Z) :
    letI : Algebra A (Z.residueField z) :=
      ((Scheme.ΓSpecIso A).inv ≫ g.appTop ≫ Z.Γevaluation z).hom.toAlgebra
    Spec.map (CommRingCat.ofHom (algebraMap A (Z.residueField z))) =
      Z.fromSpecResidueField z ≫ g := by
  let _ : Algebra A (Z.residueField z) :=
    ((Scheme.ΓSpecIso A).inv ≫ g.appTop ≫ Z.Γevaluation z).hom.toAlgebra
  rw [← cancel_mono (Spec A).isoSpec.hom]
  change _ ≫ (Spec _).toSpecΓ = _ ≫ (Spec _).toSpecΓ
  conv_rhs => rw [Category.assoc, Scheme.toSpecΓ_naturality]
  simp only [Scheme.fromSpecResidueField, Category.assoc,
    Scheme.fromSpecStalk_toSpecΓ_assoc, ← AlgebraicGeometry.Spec.map_comp]
  rw [← SpecMap_ΓSpecIso_hom, ← AlgebraicGeometry.Spec.map_comp, Spec.map_inj]
  change (((Scheme.ΓSpecIso A).hom ≫ (Scheme.ΓSpecIso A).inv) ≫ g.appTop) ≫
      Z.Γevaluation z = _
  rw [Iso.hom_inv_id, Category.id_comp]
  rfl

section Fiber

variable (f : X ⟶ Y) (x : X)

/-- The comparison map from the residue field of `X` at `x` to the residue field of the
scheme-theoretic fibre over `f x` at the corresponding point `f.asFiber x`. -/
def Scheme.Hom.fiberResidueFieldHom :
    X.residueField x ⟶ (f.fiber (f x)).residueField (f.asFiber x) :=
  (X.residueFieldCongr (f.fiberι_asFiber x).symm).hom ≫
    (f.fiberι (f x)).residueFieldMap (f.asFiber x)

/-- The comparison map of residue fields along a fibre is bijective: the fibre projection is a
base change of `Spec κ(f x) ⟶ Y`, hence a preimmersion, so it is surjective on stalks. -/
theorem Scheme.Hom.bijective_fiberResidueFieldHom :
    Function.Bijective (f.fiberResidueFieldHom x).hom := by
  rw [Scheme.Hom.fiberResidueFieldHom, CommRingCat.hom_comp]
  exact ((f.fiberι (f x)).bijective_residueFieldMap (f.asFiber x)).comp
    (ConcreteCategory.bijective_of_isIso (X.residueFieldCongr (f.fiberι_asFiber x).symm).hom)

/-- Geometric characterisation of `Scheme.Hom.fiberResidueFieldHom`: it intertwines the
canonical map from the spectrum of a residue field on `X` with the one on the fibre. -/
theorem Scheme.Hom.SpecMap_fiberResidueFieldHom :
    Spec.map (f.fiberResidueFieldHom x) ≫ X.fromSpecResidueField x =
      (f.fiber (f x)).fromSpecResidueField (f.asFiber x) ≫ f.fiberι (f x) := by
  rw [Scheme.Hom.fiberResidueFieldHom, Spec.map_comp, Category.assoc,
    Scheme.residueFieldCongr_fromSpecResidueField]
  exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField (f.fiberι (f x)) (f.asFiber x)

/-- The `κ(f x)`-algebra structure on the residue field of the fibre at `f.asFiber x`. -/
private abbrev fiberAlgebra :
    Algebra (Y.residueField (f x)) ((f.fiber (f x)).residueField (f.asFiber x)) :=
  ((Scheme.ΓSpecIso (Y.residueField (f x))).inv ≫
    (f.fiberToSpecResidueField (f x)).appTop ≫
      (f.fiber (f x)).Γevaluation (f.asFiber x)).hom.toAlgebra

/-- `Scheme.Hom.fiberResidueFieldHom` is a map of `κ(f x)`-algebras. On `κ(x)` the structure is
`Scheme.Hom.residueFieldMap`, and on the residue field of the fibre it is the one induced by
`Scheme.Hom.fiberToSpecResidueField`. -/
theorem Scheme.Hom.fiberResidueFieldHom_algebraMap :
    letI : Algebra (Y.residueField (f x)) ((f.fiber (f x)).residueField (f.asFiber x)) :=
      ((Scheme.ΓSpecIso (Y.residueField (f x))).inv ≫
        (f.fiberToSpecResidueField (f x)).appTop ≫
          (f.fiber (f x)).Γevaluation (f.asFiber x)).hom.toAlgebra
    CommRingCat.ofHom
        (algebraMap (Y.residueField (f x)) ((f.fiber (f x)).residueField (f.asFiber x))) =
      f.residueFieldMap x ≫ f.fiberResidueFieldHom x := by
  let _ := fiberAlgebra f x
  apply Spec.map_injective
  rw [Spec.map_comp, ← cancel_mono (Y.fromSpecResidueField (f x)),
    SpecMap_algebraMap_residueField (f.fiberToSpecResidueField (f x)) (f.asFiber x)]
  conv_rhs => rw [Category.assoc,
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f x, ← Category.assoc,
    f.SpecMap_fiberResidueFieldHom x, Category.assoc, Scheme.Hom.fiber_fac]
  rw [Category.assoc]

/-- The residue field of a scheme-theoretic fibre at `f.asFiber x` has the same transcendence
degree over `κ(f x)` as `κ(x)` does. -/
theorem Scheme.Hom.trdeg_residueField_fiber :
    letI : Algebra (Y.residueField (f x)) ((f.fiber (f x)).residueField (f.asFiber x)) :=
      ((Scheme.ΓSpecIso (Y.residueField (f x))).inv ≫
        (f.fiberToSpecResidueField (f x)).appTop ≫
          (f.fiber (f x)).Γevaluation (f.asFiber x)).hom.toAlgebra
    letI : Algebra (Y.residueField (f x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    Algebra.trdeg (Y.residueField (f x)) ((f.fiber (f x)).residueField (f.asFiber x)) =
      Algebra.trdeg (Y.residueField (f x)) (X.residueField x) := by
  let _ := fiberAlgebra f x
  let _ : Algebra (Y.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  let e : (X.residueField x : Type u) ≃ₐ[Y.residueField (f x)]
      ((f.fiber (f x)).residueField (f.asFiber x) : Type u) :=
    AlgEquiv.ofRingEquiv
      (f := RingEquiv.ofBijective (f.fiberResidueFieldHom x).hom
        (f.bijective_fiberResidueFieldHom x)) (fun a => by
      have h := DFunLike.congr_fun
        (congrArg CommRingCat.Hom.hom (f.fiberResidueFieldHom_algebraMap x)) a
      simp only [CommRingCat.hom_ofHom, CommRingCat.hom_comp, RingHom.coe_comp,
        Function.comp_apply] at h
      exact h.symm)
  exact e.symm.trdeg_eq

end Fiber

end AlgebraicGeometry

end
