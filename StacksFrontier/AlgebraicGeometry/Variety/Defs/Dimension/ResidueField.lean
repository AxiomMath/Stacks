module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.FinTrdeg
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NoetherianFibre
public import StacksFrontier.RingTheory.KrullDimension.Defs

/-!
# Residue fields of a scheme over a field

Let `f : X ⟶ Spec k` be a scheme over a field. Each residue field `κ(x)` is a `k`-algebra
through the composite of global sections with evaluation at `x`, and when `f` is locally of
finite type that extension is finitely generated, hence of finite transcendence degree. A
morphism which is surjective on stalks induces an isomorphism of residue fields, so it does not
change the transcendence degree.

## Main results

* `AlgebraicGeometry.spec_residueField_essFiniteType`: the residue field of `Spec k` at a point
  is a finitely generated extension of `k`.
* `AlgebraicGeometry.residueField_isScalarTower`: the `k`-algebra structure on `κ(x)` factors
  through the residue field of the base at `f x`.
* `AlgebraicGeometry.residueField_essFiniteType` and
  `AlgebraicGeometry.residueField_finTrdeg`: for `f` locally of finite type, `κ(x)` is a
  finitely generated extension of `k`, and so has finite transcendence degree.
* `AlgebraicGeometry.trdeg_residueField_of_surjectiveOnStalks`: a morphism surjective on stalks
  preserves the transcendence degree of residue fields.
* `AlgebraicGeometry.IsAffineOpen.ringKrullDim_stalk_eq_height`: on an affine open the Krull
  dimension of a stalk is the height of the corresponding prime.

## Implementation notes

The `k`-algebra structure on a residue field is not an instance; every statement therefore
introduces it in its own `letI` binding, which is the canonical composite from `k` through
global sections and evaluation at the point. Transcendence degree is Mathlib's cardinal-valued
`Algebra.trdeg`.

## References

* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public section

open CategoryTheory CommRingCat

universe u

namespace AlgebraicGeometry

/-- The residue field of `Spec k` at a point is a finitely generated extension of `k`. -/
theorem spec_residueField_essFiniteType (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X) :
    letI : Algebra k ((Spec (.of k)).residueField (f x)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).Γevaluation (f x)).hom.toAlgebra
    Algebra.EssFiniteType k ((Spec (.of k)).residueField (f x)) := by
  let : Algebra k ((Spec (.of k)).residueField (f x)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).Γevaluation (f x)).hom.toAlgebra
  let q := (f x).asIdeal
  let e := Scheme.Spec.residueFieldIso (.of k) (f x)
  let : q.IsPrime := (f x).isPrime
  let : q.IsMaximal := by
    simpa [q.eq_bot_of_prime] using (Ideal.bot_isMaximal : (⊥ : Ideal k).IsMaximal)
  have hq' : (algebraMap k q.ResidueField).EssFiniteType :=
    (RingHom.FiniteType.of_surjective _ q.algebraMap_residueField_surjective).essFiniteType
  have h := RingHom.EssFiniteType.respectsIso.1
    (algebraMap k q.ResidueField) e.symm.commRingCatIsoToRingEquiv hq'
  rw [← RingHom.essFiniteType_algebraMap]
  convert h
  show ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).Γevaluation (f x)).hom =
    e.inv.hom.comp (algebraMap k q.ResidueField)
  simpa [e, q, Scheme.Γevaluation, Scheme.evaluation, RingHom.comp_assoc] using
    (congrArg CommRingCat.Hom.hom
      (Scheme.Spec.algebraMap_residueFieldIso_inv (.of k) (f x))).symm

/-- Evaluating sections at `g y` and then mapping residue fields is evaluating the pulled-back
sections at `y`. -/
private theorem comp_Γevaluation_comp_residueFieldMap {X Y : Scheme.{u}} (g : Y ⟶ X) (y : Y)
    {R : CommRingCat.{u}} (φ : R ⟶ Γ(X, ⊤)) :
    φ ≫ X.Γevaluation (g y) ≫ g.residueFieldMap y = φ ≫ g.appTop ≫ Y.Γevaluation y := by
  rw [Scheme.Γevaluation_naturality g y]

/-- The `k`-algebra structure on the residue field of `X` at `x` factors through the residue
field of `Spec k` at `f x`. -/
theorem residueField_isScalarTower (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X) :
    letI : Algebra k ((Spec (.of k)).residueField (f x)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).Γevaluation (f x)).hom.toAlgebra
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
    letI : Algebra ((Spec (.of k)).residueField (f x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    IsScalarTower k ((Spec (.of k)).residueField (f x)) (X.residueField x) := by
  let : Algebra k ((Spec (.of k)).residueField (f x)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).Γevaluation (f x)).hom.toAlgebra
  let : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
  let : Algebra ((Spec (.of k)).residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  exact (congrArg CommRingCat.Hom.hom
    (comp_Γevaluation_comp_residueFieldMap f x (Scheme.ΓSpecIso (.of k)).inv)).symm

/-- For a morphism locally of finite type to the spectrum of a field, every residue field is a
finitely generated extension of that field. -/
theorem residueField_essFiniteType (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : X) :
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
    Algebra.EssFiniteType k (X.residueField x) := by
  let : Algebra k ((Spec (.of k)).residueField (f x)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).Γevaluation (f x)).hom.toAlgebra
  let : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
  let : Algebra.EssFiniteType k ((Spec (.of k)).residueField (f x)) :=
    spec_residueField_essFiniteType k f x
  let : Algebra ((Spec (.of k)).residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  let : IsScalarTower k ((Spec (.of k)).residueField (f x)) (X.residueField x) :=
    residueField_isScalarTower k f x
  let : Algebra.EssFiniteType ((Spec (.of k)).residueField (f x)) (X.residueField x) :=
    residueField_essFiniteType_of_locallyOfFiniteType f x
  exact Algebra.EssFiniteType.comp k ((Spec (.of k)).residueField (f x)) _

/-- For a morphism locally of finite type to the spectrum of a field, every residue field has
finite transcendence degree over that field. -/
theorem residueField_finTrdeg (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : X) :
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
    FinTrdeg k (X.residueField x) := by
  let : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
  let : Algebra.EssFiniteType k (X.residueField x) := residueField_essFiniteType k f x
  infer_instance

/-- A morphism which is surjective on stalks induces an isomorphism of residue fields, so the
transcendence degrees of the residue fields at a point and at its image agree. -/
theorem trdeg_residueField_of_surjectiveOnStalks
    (k : Type u) [Field k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (i : Y ⟶ X) [SurjectiveOnStalks i] (y : Y) :
    letI : Algebra k (X.residueField (i y)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation (i y)).hom.toAlgebra
    letI : Algebra k (Y.residueField y) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (i ≫ f).appTop ≫ Y.Γevaluation y).hom.toAlgebra
    Algebra.trdeg k (X.residueField (i y)) = Algebra.trdeg k (Y.residueField y) := by
  let : Algebra k (X.residueField (i y)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation (i y)).hom.toAlgebra
  let : Algebra k (Y.residueField y) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (i ≫ f).appTop ≫ Y.Γevaluation y).hom.toAlgebra
  have hs : Function.Surjective (i.residueFieldMap y).hom := by
    have h := (Y.residue_surjective y).comp (i.stalkMap_surjective y)
    change Function.Surjective (i.stalkMap y ≫ Y.residue y).hom at h
    rw [← Scheme.residue_residueFieldMap i y] at h
    exact Function.Surjective.of_comp (g := (X.residue (i y)).hom) h
  let e : X.residueField (i y) ≃ₐ[k] Y.residueField y :=
    { RingEquiv.ofBijective (i.residueFieldMap y).hom
        ⟨(i.residueFieldMap y).hom.injective, hs⟩ with
      commutes' := fun a ↦ by
        have := congrArg CommRingCat.Hom.hom (comp_Γevaluation_comp_residueFieldMap i y
          ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop))
        change (i.residueFieldMap y).hom
          (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation (i y)).hom a) =
          ((Scheme.ΓSpecIso (.of k)).inv ≫ (i ≫ f).appTop ≫ Y.Γevaluation y).hom a
        rw [Scheme.Hom.comp_appTop]
        exact congr($this a) }
  exact e.trdeg_eq

/-- On an affine open neighbourhood of `x`, the Krull dimension of the stalk at `x` is the
height of the prime of the section ring corresponding to `x`. -/
theorem IsAffineOpen.ringKrullDim_stalk_eq_height
    {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) :
    ringKrullDim (X.presheaf.stalk x) = (hU.primeIdealOf ⟨x, hx⟩).asIdeal.height :=
  let _ := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  (hU.isLocalization_stalk ⟨x, hx⟩).ringKrullDim_eq_height

end AlgebraicGeometry

end
