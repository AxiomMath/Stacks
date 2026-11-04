module

public import StacksFrontier.AlgebraicGeometry.Scheme.ClosedPointRationalPoint
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldOverLocalRing

/-!
# Evaluating global functions in the residue field at a point

For a scheme `X` and a point `x`, the ring map `Γ(X, ⊤) ⟶ κ(x)` adjoint to
`X.fromSpecResidueField x ≫ X.toSpecΓ` evaluates a global function at `x`. This file records its
three basic properties: its kernel is the prime of `Γ(X, ⊤)` cut out by `x`, it is natural in
morphisms of schemes, and — the consequence the rest of the file is for — together with
surjectivity of a residue field map it lets every global function upstairs be matched, modulo the
prime at the point, by one pulled back from downstairs.

That last statement is the hypothesis which
`RingHom.bijective_quotientMap_of_bijective_comapRestrict` takes about the fibre, phrased so that
it can be supplied by `AlgebraicGeometry.Scheme.Hom.bijective_residueFieldMap_of_etale` — a fact
about *scheme* residue fields — rather than by a statement about `Ideal.ResidueField`. It also
gives maximality of the prime at `x` for free: if the evaluation map at `x` is surjective then
`Γ(X, ⊤)` modulo that prime is a field.

## Main definitions

* `AlgebraicGeometry.Scheme.globalEvaluation`: the evaluation map `Γ(X, ⊤) ⟶ κ(x)`.

## Main results

* `AlgebraicGeometry.Scheme.ker_globalEvaluation`: its kernel is the prime at `x`.
* `AlgebraicGeometry.Scheme.globalEvaluation_naturality`: naturality in `X`.
* `AlgebraicGeometry.Scheme.surjective_globalEvaluation`: it is surjective at a point whose prime
  is maximal, for an affine scheme.
* `AlgebraicGeometry.globalEvaluation_naturality_apply`: naturality, applied to an element.
* `AlgebraicGeometry.surjective_globalEvaluation_comp`: the evaluation map upstairs is surjective
  as soon as the one downstairs is and the residue field map is.
* `AlgebraicGeometry.isMaximal_asIdeal_toSpecΓ_base`: a point at which the evaluation map is
  surjective cuts out a maximal ideal.
* `AlgebraicGeometry.exists_sub_mem_asIdeal_of_surjective_residueFieldMap`: **every global
  function upstairs agrees, modulo the prime at `x`, with one pulled back from downstairs.**

## Implementation notes

The evaluation map is *defined* as `Spec.preimage (X.fromSpecResidueField x ≫ X.toSpecΓ)` rather
than as `AlgebraicGeometry.Scheme.Γevaluation`, because that is the spelling in which
`AlgebraicGeometry.Spec.preimage_fromSpecResidueField_comp` computes it and in which
`AlgebraicGeometry.surjective_preimage_fromSpecResidueField_comp_toSpecΓ` already proves it
surjective. Naturality then comes from
`AlgebraicGeometry.Spec.preimage_fromSpecResidueField_comp_comp` together with naturality of
`AlgebraicGeometry.Scheme.toSpecΓ`, with no affineness needed.

The prime at `x` is written `(X.toSpecΓ.base x).asIdeal`, which for an affine `X` is
`AlgebraicGeometry.Scheme.carrierEquivPrimeSpectrum` by definition.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

namespace Scheme

/-- **Evaluation of global functions in the residue field at a point**, as the ring map adjoint
to `X.fromSpecResidueField x ≫ X.toSpecΓ`. -/
def globalEvaluation (X : Scheme.{u}) (x : X) : Γ(X, ⊤) ⟶ X.residueField x :=
  Spec.preimage (X.fromSpecResidueField x ≫ X.toSpecΓ)

/-- **The kernel of the evaluation map at `x` is the prime of `Γ(X, ⊤)` cut out by `x`.** -/
theorem ker_globalEvaluation (X : Scheme.{u}) (x : X) :
    RingHom.ker (X.globalEvaluation x).hom = (X.toSpecΓ.base x).asIdeal := by
  let _ : (X.toSpecΓ.base x).asIdeal.IsPrime := (X.toSpecΓ.base x).isPrime
  have h : (X.globalEvaluation x).hom =
      (((Spec.residueFieldIso Γ(X, ⊤) (X.toSpecΓ.base x)).inv ≫
        X.toSpecΓ.residueFieldMap x).hom).comp
        (algebraMap Γ(X, ⊤) (X.toSpecΓ.base x).asIdeal.ResidueField) := by
    rw [globalEvaluation, Spec.preimage_fromSpecResidueField_comp X.toSpecΓ x]
    rfl
  rw [h, RingHom.ker_comp_of_injective _ (RingHom.injective _),
    Ideal.ker_algebraMap_residueField]

/-- **Naturality of the evaluation map**: pulling a global function back along a morphism and
evaluating it at a point is evaluating it at the image point and mapping the value along the
residue field map. -/
@[reassoc]
theorem globalEvaluation_naturality {X Y : Scheme.{u}} (e : X ⟶ Y) (x : X) :
    e.appTop ≫ X.globalEvaluation x =
      Y.globalEvaluation (e.base x) ≫ e.residueFieldMap x := by
  have h := Spec.preimage_fromSpecResidueField_comp_comp e Y.toSpecΓ x
  rw [Scheme.toSpecΓ_naturality, ← Category.assoc, Spec.preimage_comp, Spec.preimage_map] at h
  exact h

/-- **The evaluation map of an affine scheme at a point whose prime is maximal is surjective.**
-/
theorem surjective_globalEvaluation (X : Scheme.{u}) [IsAffine X] (x : X)
    (hx : (X.toSpecΓ.base x).asIdeal.IsMaximal) :
    Function.Surjective (X.globalEvaluation x).hom :=
  surjective_preimage_fromSpecResidueField_comp_toSpecΓ x hx

end Scheme

/-- **Naturality of the evaluation map, applied to a global function.** -/
theorem globalEvaluation_naturality_apply {X Y : Scheme.{u}} (e : X ⟶ Y) (x : X)
    (a : Γ(Y, ⊤)) :
    (X.globalEvaluation x).hom (e.appTop.hom a) =
      (e.residueFieldMap x).hom ((Y.globalEvaluation (e.base x)).hom a) := by
  have h := ConcreteCategory.congr_hom (Scheme.globalEvaluation_naturality e x) a
  simpa using h

/-- **The evaluation map upstairs is surjective as soon as the one downstairs is and the residue
field map is.** -/
theorem surjective_globalEvaluation_comp {X Y : Scheme.{u}} (e : X ⟶ Y) (x : X)
    (hY : Function.Surjective (Y.globalEvaluation (e.base x)).hom)
    (hres : Function.Surjective (e.residueFieldMap x).hom) :
    Function.Surjective (X.globalEvaluation x).hom := by
  intro ξ
  obtain ⟨η, rfl⟩ := hres ξ
  obtain ⟨a, rfl⟩ := hY η
  exact ⟨e.appTop.hom a, globalEvaluation_naturality_apply e x a⟩

/-- **A point at which the evaluation map is surjective cuts out a maximal ideal.** The quotient
of `Γ(X, ⊤)` by that prime is then isomorphic to the residue field at the point. -/
theorem isMaximal_asIdeal_toSpecΓ_base {X : Scheme.{u}} (x : X)
    (hsurj : Function.Surjective (X.globalEvaluation x).hom) :
    (X.toSpecΓ.base x).asIdeal.IsMaximal := by
  have e : (Γ(X, ⊤) ⧸ RingHom.ker (X.globalEvaluation x).hom) ≃+* X.residueField x :=
    RingHom.quotientKerEquivOfSurjective hsurj
  rw [← X.ker_globalEvaluation x]
  exact Ideal.Quotient.maximal_of_isField _
    (MulEquiv.isField (Field.toIsField (X.residueField x)) e.toMulEquiv)

/-- **Every global function upstairs agrees, modulo the prime at a point, with one pulled back
from downstairs**, as soon as the residue field map at that point is surjective and the
evaluation map at its image is.

This is the matching statement that `RingHom.bijective_quotientMap_of_bijective_comapRestrict`
asks for on the fibre, supplied from the *scheme* residue fields rather than from
`Ideal.ResidueField`. -/
theorem exists_sub_mem_asIdeal_of_surjective_residueFieldMap {X Y : Scheme.{u}} (e : X ⟶ Y)
    (x : X) (hY : Function.Surjective (Y.globalEvaluation (e.base x)).hom)
    (hres : Function.Surjective (e.residueFieldMap x).hom) (y : Γ(X, ⊤)) :
    ∃ a : Γ(Y, ⊤), y - e.appTop.hom a ∈ (X.toSpecΓ.base x).asIdeal := by
  obtain ⟨η, hη⟩ := hres ((X.globalEvaluation x).hom y)
  obtain ⟨a, rfl⟩ := hY η
  refine ⟨a, ?_⟩
  rw [← X.ker_globalEvaluation x, RingHom.mem_ker, map_sub, sub_eq_zero]
  exact hη.symm.trans (globalEvaluation_naturality_apply e x a).symm

end AlgebraicGeometry

end

end
