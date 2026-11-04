module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.ResidueField
public import StacksFrontier.AlgebraicGeometry.Varieties.FunctionFieldEquivalence.Basic

/-!
# The extension of function fields attached to a dominant morphism

A dominant morphism `f : X ⟶ Y` of integral schemes carries the generic point of `X` to the
generic point of `Y`, so its stalk map there is a homomorphism of the function field of `Y`
into the function field of `X`. This file constructs that homomorphism, identifies it with the
residue-field map of `f` at the generic point, and records what is needed to compare degrees:
residue degrees multiply along a composition, and a morphism whose residue degree at the
generic point is one induces a bijection of function fields.

## Main definitions

* `AlgebraicGeometry.stalkResidueEquiv` — the residue map of a stalk which happens to be a
  field, as an isomorphism onto the residue field at that point.
* `AlgebraicGeometry.genericResidueEquiv` — the function field of an integral scheme, as the
  residue field at its generic point.
* `AlgebraicGeometry.genericResidueEquivOfDominant` — the function field of the target of a
  dominant morphism, as the residue field at the image of the generic point of the source.
* `AlgebraicGeometry.functionFieldMap` — the extension of function fields induced by a
  dominant morphism of integral schemes.

## Main results

* `AlgebraicGeometry.residueFieldMap_comp_genericResidueEquivOfDominant` — the extension of
  function fields agrees with the residue-field map at the generic point.
* `AlgebraicGeometry.functionFieldMap_fromSpecStalk` — the extension of function fields is
  compatible with the canonical morphisms out of the spectra of the generic stalks.
* `AlgebraicGeometry.isDominant_fromSpecStalk_genericPoint` — the canonical morphism from the
  spectrum of the function field is dominant.
* `AlgebraicGeometry.residueDegree_comp` — the residue degree of a composition is the product
  of the residue degrees.
* `AlgebraicGeometry.functionFieldMap_bijective_of_residueDegree_eq_one` — residue degree one
  at the generic point means the extension of function fields is a bijection.

## Implementation notes

The function field of an integral scheme is by definition the stalk at the generic point, so
the homomorphism of function fields is literally the stalk map of `f`, transported along the
isomorphism of stalks coming from the equality of points. The residue-field formulation is the
one in which degrees are expressed, since `AlgebraicGeometry.Scheme.Hom.residueDegree` is a
degree of residue fields, and the comparison between the two is recorded once and for all.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The residue map of a stalk which is a field, as an isomorphism onto the residue field. -/
def stalkResidueEquiv (X : Scheme.{u}) (x : X) (hfield : IsField (X.presheaf.stalk x)) :
    X.presheaf.stalk x ≃+* X.residueField x :=
  let _ : Field (X.presheaf.stalk x) := hfield.toField
  .ofBijective (X.residue x).hom ⟨(X.residue x).hom.injective, X.residue_surjective x⟩

/-- The isomorphism of a field-valued stalk with the residue field is the residue map. -/
theorem stalkResidueEquiv_toRingHom (X : Scheme.{u}) (x : X)
    (hfield : IsField (X.presheaf.stalk x)) :
    (stalkResidueEquiv X x hfield).toRingHom = (X.residue x).hom := rfl

/-- The ring equivalence underlying an isomorphism of commutative rings is its forward map. -/
theorem commRingCatIsoToRingEquiv_toRingHom {R S : CommRingCat.{u}} (e : R ≅ S) :
    e.commRingCatIsoToRingEquiv.toRingHom = e.hom.hom := rfl

/-- The function field of an integral scheme is its residue field at the generic point: the
stalk there is already a field. -/
def genericResidueEquiv (X : Scheme.{u}) [IsIntegral X] :
    X.functionField ≃+* X.residueField (genericPoint X) :=
  stalkResidueEquiv X (genericPoint X) (Field.toIsField _)

/-- The stalk of the target of a dominant morphism at the image of the generic point of the
source is a field, because that image is the generic point of the target. -/
theorem isField_stalk_map_genericPoint {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsDominant f] :
    IsField (Y.presheaf.stalk (f (genericPoint X))) := by
  rw [map_genericPoint_of_isDominant f]
  exact Field.toIsField _

/-- The function field of the target of a dominant morphism, as the residue field at the image
of the generic point of the source. -/
def genericResidueEquivOfDominant {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsDominant f] :
    Y.functionField ≃+* Y.residueField (f (genericPoint X)) :=
  (Y.presheaf.stalkCongr
        (Inseparable.of_eq (map_genericPoint_of_isDominant f).symm)).commRingCatIsoToRingEquiv.trans
    (stalkResidueEquiv Y (f (genericPoint X)) (isField_stalk_map_genericPoint f))

/-- The extension of function fields induced by a dominant morphism of integral schemes: the
stalk map at the generic point, read through the equality of the image of the generic point of
the source with the generic point of the target. -/
def functionFieldMap {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [IsDominant f] : Y.functionField →+* X.functionField :=
  ((Y.presheaf.stalkCongr (Inseparable.of_eq (map_genericPoint_of_isDominant f).symm)).hom ≫
    f.stalkMap (genericPoint X)).hom

/-- The extension of function fields of a dominant morphism is the residue-field map at the
generic point, read through the identifications of function fields with residue fields. -/
theorem residueFieldMap_comp_genericResidueEquivOfDominant {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsDominant f] :
    (f.residueFieldMap (genericPoint X)).hom.comp
        (genericResidueEquivOfDominant f).toRingHom =
      (genericResidueEquiv X).toRingHom.comp (functionFieldMap f) := by
  have hnatural := congrArg CommRingCat.Hom.hom
    (Scheme.residue_residueFieldMap f (genericPoint X))
  change (f.residueFieldMap (genericPoint X)).hom.comp
      (Y.residue (f (genericPoint X))).hom =
    (X.residue (genericPoint X)).hom.comp
      (f.stalkMap (genericPoint X)).hom at hnatural
  simpa only [genericResidueEquivOfDominant, RingEquiv.toRingHom_trans,
    genericResidueEquiv, functionFieldMap, stalkResidueEquiv_toRingHom,
    TopCat.Presheaf.stalkCongr_hom, commRingCatIsoToRingEquiv_toRingHom,
    CategoryTheory.Iso.commRingCatIsoToRingEquiv_toRingHom,
    ← CommRingCat.hom_comp, Category.assoc, RingHom.comp_assoc,
    RingHom.comp_apply] using
      congrArg (fun g => g.comp
        (Y.presheaf.stalkCongr
          (Inseparable.of_eq (map_genericPoint_of_isDominant f).symm)).hom.hom) hnatural

/-- The extension of function fields of a dominant morphism is compatible with the canonical
morphisms from the spectra of the stalks at the generic points. -/
theorem functionFieldMap_fromSpecStalk {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsDominant f] :
    Spec.map (CommRingCat.ofHom (functionFieldMap f)) ≫
        Y.fromSpecStalk (genericPoint Y) =
      X.fromSpecStalk (genericPoint X) ≫ f := by
  simp only [functionFieldMap, CommRingCat.ofHom_hom, Spec.map_comp,
    Category.assoc, TopCat.Presheaf.stalkCongr_hom]
  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk]
  congr 1
  exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk _

/-- The canonical morphism from the spectrum of the function field of an integral scheme is
dominant: its image is the generic point, which is dense. -/
theorem isDominant_fromSpecStalk_genericPoint (X : Scheme.{u}) [IsIntegral X] :
    IsDominant (X.fromSpecStalk (genericPoint X)) :=
  ⟨Dense.mono (s₁ := {genericPoint X})
    (Set.singleton_subset_iff.mpr
      ⟨IsLocalRing.closedPoint X.functionField, X.fromSpecStalk_closedPoint⟩)
    (dense_iff_closure_eq.mpr (genericPoint_spec X))⟩

/-- The spectrum of a homomorphism of fields is surjective: both spectra are single points. -/
theorem surjective_specMap_of_field {K L : Type u} [Field K] [Field L] (φ : K →+* L) :
    Surjective (Spec.map (CommRingCat.ofHom φ)) :=
  ⟨Function.surjective_to_subsingleton _⟩

/-- Residue degrees multiply along a composition of morphisms of schemes. -/
theorem residueDegree_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g).residueDegree x = g.residueDegree (f x) * f.residueDegree x := by
  let A := Z.residueField (g (f x))
  let B := Y.residueField (f x)
  let C := X.residueField x
  let _ : Algebra A B := (g.residueFieldMap (f x)).hom.toAlgebra
  let _ : Algebra B C := (f.residueFieldMap x).hom.toAlgebra
  let _ : Algebra A C :=
    ((f.residueFieldMap x).hom.comp (g.residueFieldMap (f x)).hom).toAlgebra
  have : IsScalarTower A B C := .of_algebraMap_eq' rfl
  dsimp only [Scheme.Hom.residueDegree]
  rw [Scheme.residueFieldMap_comp]
  exact (Module.finrank_mul_finrank A B C).symm

/-- A dominant morphism of integral schemes whose residue degree at the generic point is one
induces a bijection of function fields. -/
theorem functionFieldMap_bijective_of_residueDegree_eq_one {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsDominant f]
    (hdegree : f.residueDegree (genericPoint X) = 1) :
    Function.Bijective (functionFieldMap f) := by
  let _ : Algebra (Y.residueField (f (genericPoint X))) (X.residueField (genericPoint X)) :=
    (f.residueFieldMap (genericPoint X)).hom.toAlgebra
  refine ((genericResidueEquiv X).bijective.of_comp_iff' _).mp ?_
  rw [← RingEquiv.coe_toRingHom, ← RingHom.coe_comp, ← RingEquiv.toRingHom_eq_coe,
    ← residueFieldMap_comp_genericResidueEquivOfDominant f]
  exact (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hdegree).comp
    (genericResidueEquivOfDominant f).bijective

end AlgebraicGeometry

end
