module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.FieldTheory.SeparableDegree
public import StacksFrontier.AlgebraicGeometry.Variety.ClosedPointResidueField

/-!
# The base field and the residue field of the base

Let `X` be a scheme over a field `k`, with structure morphism `f : X ⟶ Spec k`. The residue field
`κ(x)` at a point `x` of `X` carries two algebra structures that are in practice used
interchangeably: the one over `k` itself, attached to the ring homomorphism
`k ⟶ Γ(X, ⊤) ⟶ 𝒪_{X,x} ⟶ κ(x)` built from the structure morphism, and the one over the residue
field of `Spec k` at `f x`, attached to the residue field map of `f`. Since `Spec k` has a single
point whose residue field is canonically `k`, the two structures agree, and properties of the
residue field extension may be read off from either.

## Main results

* `AlgebraicGeometry.bijective_algebraMap_residueField_spec_self`: the canonical map from `k` to
  the residue field of `Spec k` at its unique point is bijective.
* `AlgebraicGeometry.isSeparable_residueField_base_iff`: the residue field at `x` is separable
  over the residue field of the base if and only if it is separable over the base field.
* `AlgebraicGeometry.finite_residueField_base_iff`: the residue field at `x` is a finite module
  over the residue field of the base if and only if it is finite over the base field.

## Implementation notes

Neither algebra structure is an instance, so each statement introduces the ones it needs by a
`letI`. The comparison rests on the scalar tower `k ⟶ κ(f x) ⟶ κ(x)`, which is the naturality of
global evaluation along `f` (`AlgebraicGeometry.Scheme.Γevaluation_naturality`) written out in
terms of germs and residue maps.

The identification of `k` with the residue field of `Spec k` uses that the underlying space of
`Spec k` is a subsingleton, so the given point is the closed point of the local ring `k`, where
`AlgebraicGeometry.stalkClosedPointIso` identifies the stalk with `k`.
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

/-- The map from `k` to the stalk of `Spec k` at the closed point, presented as the inverse of
`AlgebraicGeometry.Scheme.ΓSpecIso` followed by the germ at the closed point, is the inverse of
`AlgebraicGeometry.stalkClosedPointIso`. -/
private lemma ΓSpecIso_inv_germ_closedPoint (k : Type u) [Field k]
    (h : closedPoint (CommRingCat.of k) ∈ (⊤ : (Spec (.of k)).Opens)) :
    (Scheme.ΓSpecIso (.of k)).inv ≫
        (Spec (.of k)).presheaf.germ ⊤ (closedPoint (CommRingCat.of k)) h =
      (stalkClosedPointIso (CommRingCat.of k)).inv := by
  rw [← ΓSpecIso_hom_stalkClosedPointIso_inv, Iso.inv_hom_id_assoc]

/-- The map from `k` to the stalk of `Spec k` at any point is bijective: the space `Spec k` has a
single point, which is the closed point of the local ring `k`. -/
private lemma bijective_ΓSpecIso_inv_germ (k : Type u) [Field k] (s : Spec (.of k))
    (h : s ∈ (⊤ : (Spec (.of k)).Opens)) :
    Function.Bijective
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).presheaf.germ ⊤ s h).hom := by
  have : Subsingleton (Spec (.of k)) := by
    show Subsingleton (PrimeSpectrum k)
    infer_instance
  obtain rfl : s = closedPoint (CommRingCat.of k) := Subsingleton.elim _ _
  rw [ΓSpecIso_inv_germ_closedPoint]
  exact ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (CommRingCat.of k)).inv

/-- The identification of `k` with the residue field of `Spec k` at its unique point is
bijective. -/
public theorem bijective_algebraMap_residueField_spec_self
    (k : Type u) [Field k] (s : Spec (.of k)) :
    letI : Algebra k ((Spec (.of k)).residueField s) :=
      (((Spec (.of k)).residue s).hom.comp
        ((Scheme.ΓSpecIso (.of k)).inv ≫
          (Spec (.of k)).presheaf.germ ⊤ s (by simp)).hom).toAlgebra
    Function.Bijective (algebraMap k ((Spec (.of k)).residueField s)) := by
  let : Algebra k ((Spec (.of k)).residueField s) :=
    (((Spec (.of k)).residue s).hom.comp
      ((Scheme.ΓSpecIso (.of k)).inv ≫
        (Spec (.of k)).presheaf.germ ⊤ s (by simp)).hom).toAlgebra
  refine ⟨RingHom.injective _, ?_⟩
  rw [RingHom.algebraMap_toAlgebra]
  simp only [RingHom.coe_comp]
  exact ((Spec (.of k)).residue_surjective s).comp
    (bijective_ΓSpecIso_inv_germ k s (by simp)).surjective

/-- Global evaluation at `x` of the pullback of a global function on `Spec k` is the image under
the residue field map of `f` of its evaluation at `f x`, written out in terms of germs and
residue maps. -/
private lemma residue_germ_appTop_eq (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X) :
    (X.residue x).hom.comp
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
          X.presheaf.germ ⊤ x (by simp)).hom =
      (f.residueFieldMap x).hom.comp
        ((((Spec (.of k)).residue (f.base x)).hom.comp
          ((Scheme.ΓSpecIso (.of k)).inv ≫
            (Spec (.of k)).presheaf.germ ⊤ (f.base x) (by simp)).hom)) := by
  have key : (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
        X.presheaf.germ ⊤ x (by simp) ≫ X.residue x =
      (Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).presheaf.germ ⊤ (f.base x) (by simp) ≫
        (Spec (.of k)).residue (f.base x) ≫ f.residueFieldMap x := by
    rw [Scheme.germ_residue, Scheme.germ_residue_assoc, Scheme.Γevaluation_naturality]
  simpa only [CommRingCat.hom_comp, RingHom.comp_assoc] using congrArg CommRingCat.Hom.hom key

/-- The algebra structure of the residue field of `Spec k` at `s` over `k`, through the germ. -/
private abbrev baseResidueFieldAlgebra (k : Type u) [Field k] (s : Spec (.of k)) :
    Algebra k ((Spec (.of k)).residueField s) :=
  (((Spec (.of k)).residue s).hom.comp
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).presheaf.germ ⊤ s (by simp)).hom).toAlgebra

/-- The algebra structure of the residue field of `X` at `x` over `k`, through global sections. -/
private abbrev residueFieldAlgebra (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (x : X) : Algebra k (X.residueField x) :=
  ((X.residue x).hom.comp ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
    X.presheaf.germ ⊤ x (by simp)).hom).toAlgebra

/-- The base field, the residue field of the base at `f x` and the residue field at `x` form a
scalar tower. -/
private lemma isScalarTower_base_residueField (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X) :
    letI := baseResidueFieldAlgebra k (f.base x)
    letI := residueFieldAlgebra k f x
    letI : Algebra ((Spec (.of k)).residueField (f.base x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    IsScalarTower k ((Spec (.of k)).residueField (f.base x)) (X.residueField x) := by
  let := baseResidueFieldAlgebra k (f.base x)
  let := residueFieldAlgebra k f x
  let := (f.residueFieldMap x).hom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq' ?_
  simp only [RingHom.algebraMap_toAlgebra]
  exact residue_germ_appTop_eq k f x

/-- **The residue field at a point of a `k`-scheme is separable over the residue field of the base
if and only if it is separable over `k`**, the two residue field extensions being the same. -/
public theorem isSeparable_residueField_base_iff
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X) :
    letI instk : Algebra k (X.residueField x) :=
      ((X.residue x).hom.comp ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
        X.presheaf.germ ⊤ x (by simp)).hom).toAlgebra
    letI instR : Algebra ((Spec (.of k)).residueField (f.base x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    (Algebra.IsSeparable ((Spec (.of k)).residueField (f.base x)) (X.residueField x) ↔
      Algebra.IsSeparable k (X.residueField x)) := by
  let := baseResidueFieldAlgebra k (f.base x)
  let := residueFieldAlgebra k f x
  let := (f.residueFieldMap x).hom.toAlgebra
  have : IsScalarTower k ((Spec (.of k)).residueField (f.base x)) (X.residueField x) :=
    isScalarTower_base_residueField k f x
  have hbij : Function.Bijective
      (algebraMap k ((Spec (.of k)).residueField (f.base x))) :=
    bijective_algebraMap_residueField_spec_self k (f.base x)
  have : Algebra.IsSeparable k ((Spec (.of k)).residueField (f.base x)) :=
    Algebra.IsSeparable.of_bijective_algebraMap hbij
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · exact Algebra.IsSeparable.trans k ((Spec (.of k)).residueField (f.base x)) (X.residueField x)
  · exact Algebra.isSeparable_tower_top_of_isSeparable k
      ((Spec (.of k)).residueField (f.base x)) (X.residueField x)

/-- **The residue field at a point of a `k`-scheme is a finite module over the residue field of
the base if and only if it is finite over `k`**, the two residue field extensions being the
same. -/
public theorem finite_residueField_base_iff
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X) :
    letI instk : Algebra k (X.residueField x) :=
      ((X.residue x).hom.comp ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
        X.presheaf.germ ⊤ x (by simp)).hom).toAlgebra
    letI instR : Algebra ((Spec (.of k)).residueField (f.base x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    (Module.Finite ((Spec (.of k)).residueField (f.base x)) (X.residueField x) ↔
      Module.Finite k (X.residueField x)) := by
  let := baseResidueFieldAlgebra k (f.base x)
  let := residueFieldAlgebra k f x
  let := (f.residueFieldMap x).hom.toAlgebra
  have : IsScalarTower k ((Spec (.of k)).residueField (f.base x)) (X.residueField x) :=
    isScalarTower_base_residueField k f x
  have hbij : Function.Bijective
      (algebraMap k ((Spec (.of k)).residueField (f.base x))) :=
    bijective_algebraMap_residueField_spec_self k (f.base x)
  have : Module.Finite k ((Spec (.of k)).residueField (f.base x)) :=
    Module.Finite.of_surjective
      (Algebra.linearMap k ((Spec (.of k)).residueField (f.base x))) hbij.surjective
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · exact Module.Finite.trans ((Spec (.of k)).residueField (f.base x)) (X.residueField x)
  · exact Module.Finite.of_restrictScalars_finite k
      ((Spec (.of k)).residueField (f.base x)) (X.residueField x)

end AlgebraicGeometry

end
