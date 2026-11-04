module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.RingTheory.Ideal.Cotangent

/-!
# Degrees at a closed point over an algebraically closed field

Let `k` be an algebraically closed field and let `X` be a scheme locally of finite type over `k`.
At a closed point `x` the structure morphism identifies `k` with the residue field `κ(x)`, so
`κ(x)` has degree one over `k`, and the cotangent space `𝔪_x / 𝔪_x²` of the local ring at `x` has
the same dimension over `k` as it has over `κ(x)`.

## Main results

* `AlgebraicGeometry.Scheme.fromSpecResidueField_toSpecΓ`: the canonical morphism
  `Spec κ(x) ⟶ X` followed by `X ⟶ Spec Γ(X, ⊤)` is the spectrum of evaluation at `x`.
* `AlgebraicGeometry.residueFieldIsoBase_inv_eq`: the inverse of the isomorphism `κ(x) ≅ k` at a
  closed point is the homomorphism `k ⟶ Γ(X, ⊤) ⟶ κ(x)` built from the structure morphism and
  evaluation at `x`.
* `AlgebraicGeometry.finrank_residueField_of_isClosed`: the residue field at a closed point has
  degree one over the base field.
* `AlgebraicGeometry.finrank_cotangentSpace_base_eq_of_isClosed`: the cotangent space of the
  local ring at a closed point has the same dimension over the base field as over the residue
  field.

## Implementation notes

The `k`-algebra structure on `κ(x)` is not an instance: it is the one attached to the ring
homomorphism `k ⟶ Γ(X, ⊤) ⟶ κ(x)` obtained from the structure morphism and evaluation at `x`,
and each statement introduces it by a `let`. The `k`-module structure on the cotangent space is
restriction of scalars along that homomorphism.

## References

* [Stacks Project, Tag 00FV](https://stacks.math.columbia.edu/tag/00FV)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

/-- The canonical morphism `Spec κ(x) ⟶ X`, followed by the unit `X ⟶ Spec Γ(X, ⊤)`, is the
spectrum of evaluation at `x`. -/
public theorem Scheme.fromSpecResidueField_toSpecΓ {X : Scheme.{u}} (x : X) :
    X.fromSpecResidueField x ≫ X.toSpecΓ = Spec.map (X.Γevaluation x) := by
  rw [Scheme.fromSpecResidueField, Category.assoc, Scheme.fromSpecStalk_toSpecΓ,
    ← Spec.map_comp]
  rfl

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}

/-- The identification of the base field with the residue field at a closed point is evaluation
at that point, precomposed with the structure morphism on global sections. -/
public theorem residueFieldIsoBase_inv_eq (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    (residueFieldIsoBase p x hx).inv =
      (Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ X.Γevaluation x := by
  apply Spec.map_injective
  rw [SpecMap_residueFieldIsoBase_inv, Spec.map_comp, Spec.map_comp,
    ← Scheme.fromSpecResidueField_toSpecΓ, Category.assoc, Category.assoc,
    ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- The structure map of the residue field at a closed point over an algebraically closed field
is bijective. -/
public theorem bijective_algebraMap_residueField_of_isClosed (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] (x : X) (hx : IsClosed ({x} : Set X)) :
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ X.Γevaluation x).hom.toAlgebra
    Function.Bijective (algebraMap k (X.residueField x)) := by
  let : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ X.Γevaluation x).hom.toAlgebra
  rw [RingHom.algebraMap_toAlgebra, ← residueFieldIsoBase_inv_eq p x hx]
  exact ConcreteCategory.bijective_of_isIso (residueFieldIsoBase p x hx).inv

/-- **The residue field at a closed point of a scheme locally of finite type over an
algebraically closed field has degree one over the base field.** -/
public theorem finrank_residueField_of_isClosed (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] (x : X) (hx : IsClosed ({x} : Set X)) :
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ X.Γevaluation x).hom.toAlgebra
    Module.finrank k (X.residueField x) = 1 := by
  let : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ X.Γevaluation x).hom.toAlgebra
  have e : k ≃ₐ[k] X.residueField x :=
    AlgEquiv.ofBijective (Algebra.ofId k _)
      (bijective_algebraMap_residueField_of_isClosed p x hx)
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

/-- **At a closed point of a scheme locally of finite type over an algebraically closed field the
cotangent space has the same dimension over the base field as over the residue field**, the
residue field having degree one over the base field. -/
public theorem finrank_cotangentSpace_base_eq_of_isClosed (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] (x : X) (hx : IsClosed ({x} : Set X)) :
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ X.Γevaluation x).hom.toAlgebra
    letI : Module (X.residueField x) (CotangentSpace (X.presheaf.stalk x)) :=
      inferInstanceAs (Module (ResidueField (X.presheaf.stalk x)) _)
    letI : Module k (CotangentSpace (X.presheaf.stalk x)) :=
      Module.compHom _ (algebraMap k (X.residueField x))
    Module.finrank k (CotangentSpace (X.presheaf.stalk x)) =
      Module.finrank (X.residueField x) (CotangentSpace (X.presheaf.stalk x)) := by
  let : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ X.Γevaluation x).hom.toAlgebra
  let : Module (X.residueField x) (CotangentSpace (X.presheaf.stalk x)) :=
    inferInstanceAs (Module (ResidueField (X.presheaf.stalk x)) _)
  let : Module k (CotangentSpace (X.presheaf.stalk x)) :=
    Module.compHom _ (algebraMap k (X.residueField x))
  let : IsScalarTower k (X.residueField x) (CotangentSpace (X.presheaf.stalk x)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have h := Module.finrank_mul_finrank k (X.residueField x) (CotangentSpace (X.presheaf.stalk x))
  rw [finrank_residueField_of_isClosed p x hx, one_mul] at h
  exact h.symm

end AlgebraicGeometry

end
