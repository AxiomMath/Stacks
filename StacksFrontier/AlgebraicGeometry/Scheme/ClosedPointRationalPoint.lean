module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# Residue fields over a base ring, and rational points at closed points

For a morphism `f : X ⟶ Spec R`, the ring map adjoint to `X.fromSpecResidueField x ≫ f` is the
canonical map from `R` to the residue field of `X` at `x`.  Working with that adjoint rather
than with the composite built from `Scheme.Spec.residueFieldIso` makes the whole theory
mechanical: functoriality is `Spec.map_preimage`, and the affine case is an instance of it.

On top of this we prove that over an algebraically closed field `K`, a point whose residue
field is algebraic over `K` is the image of a section of the structure morphism.  Mathlib's
`AlgebraicGeometry.Scheme.pointOfClosedPoint` proves the same thing for `f` locally of finite
type, where algebraicity is automatic; here algebraicity is a hypothesis instead, which is
what makes the statement usable over a very large base field.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Spec.preimage_fromSpecResidueField_comp` identifies the adjoint ring map
  with the canonical composite built from `Scheme.Spec.residueFieldIso`.
* `AlgebraicGeometry.Spec.preimage_fromSpecResidueField_comp_comp` is its functoriality.
* `AlgebraicGeometry.isAlgebraic_residueField_comp_iff` transports algebraicity of the residue
  field along a morphism over the base inducing an isomorphism of residue fields.
* `AlgebraicGeometry.isAlgebraic_residueField_specMap` is the affine case.
* `AlgebraicGeometry.exists_isSection_of_isAlgebraic_residueField` produces the section of `f`
  through `x`.

## Implementation notes

The section is `Spec.map` of the inverse of the adjoint ring map, followed by
`X.fromSpecResidueField x`; the identity `Spec.map (Spec.preimage g) = g` then makes the
section property a one-line computation, with no residue-field bookkeeping at all.  The
inverse is introduced as an opaque variable together with its defining equation, because the
`IsIso` instance argument of `inv` makes the motive of a rewrite in the adjoint map ill-typed.

Algebraicity statements carry the algebra structure as a `let`-bound
`RingHom.toAlgebra` of the adjoint ring map rather than as an instance argument, so that the
statements say which structure they are about; the two spellings are propositionally equal, so
`AlgebraicGeometry.isAlgebraic_residueField_iff` converts between them.

## References

* [Stacks Project, Tag 0479](https://stacks.math.columbia.edu/tag/0479)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The ring map adjoint to `X.fromSpecResidueField x ≫ f` is the canonical map from the base
ring to the residue field of the image point, transported to the residue field of `x`. -/
theorem Spec.preimage_fromSpecResidueField_comp {X : Scheme.{u}} {R : CommRingCat.{u}}
    (f : X ⟶ Spec R) (x : X) :
    letI : (f x).asIdeal.IsPrime := (f x).isPrime
    Spec.preimage (X.fromSpecResidueField x ≫ f) =
      CommRingCat.ofHom (algebraMap R (f x).asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso R (f x)).inv ≫ f.residueFieldMap x := by
  let _ : (f x).asIdeal.IsPrime := (f x).isPrime
  apply Spec.map_injective
  simp only [Spec.map_preimage, Spec.map_comp, Category.assoc,
    Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField,
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]

/-- Functoriality of the adjoint ring map in the first factor. -/
theorem Spec.preimage_fromSpecResidueField_comp_comp {X Y : Scheme.{u}} {R : CommRingCat.{u}}
    (e : X ⟶ Y) (g : Y ⟶ Spec R) (x : X) :
    Spec.preimage (X.fromSpecResidueField x ≫ e ≫ g) =
      Spec.preimage (Y.fromSpecResidueField (e x) ≫ g) ≫ e.residueFieldMap x := by
  apply Spec.map_injective
  rw [Spec.map_preimage, Spec.map_comp, Spec.map_preimage]
  simp only [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc]

/-- The adjoint ring map of an affine scheme over a field, at a point of its spectrum. -/
theorem Spec.preimage_fromSpecResidueField_comp_specMap {K A : Type u} [Field K] [CommRing A]
    [Algebra K A] (q : Spec (.of A)) :
    letI : q.asIdeal.IsPrime := q.isPrime
    Spec.preimage ((Spec (.of A)).fromSpecResidueField q ≫
        Spec.map (CommRingCat.ofHom (algebraMap K A))) =
      CommRingCat.ofHom (algebraMap K q.asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso (.of A) q).inv := by
  let _ : q.asIdeal.IsPrime := q.isPrime
  apply Spec.map_injective
  rw [Spec.map_preimage, Spec.map_comp,
    show (CommRingCat.ofHom (algebraMap K q.asIdeal.ResidueField) :
        CommRingCat.of K ⟶ CommRingCat.of q.asIdeal.ResidueField) =
      CommRingCat.ofHom (algebraMap K A) ≫
        CommRingCat.ofHom (algebraMap A q.asIdeal.ResidueField) from by
      rw [← CommRingCat.ofHom_comp]
      congr 1,
    Spec.map_comp, ← Category.assoc,
    Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]

/-- Algebraicity over a base field transports along an isomorphism of commutative rings
compatible with the maps from the base field. -/
theorem isAlgebraic_of_commRingCatIso {K : Type u} [Field K] {E F : CommRingCat.{u}}
    [Algebra K E] [Algebra K F] (ρ : E ≅ F)
    (h : CommRingCat.ofHom (algebraMap K E) ≫ ρ.hom = CommRingCat.ofHom (algebraMap K F))
    [Algebra.IsAlgebraic K E] : Algebra.IsAlgebraic K F :=
  (AlgEquiv.ofRingEquiv (f := ρ.commRingCatIsoToRingEquiv)
    fun a => congrArg (fun φ : CommRingCat.of K ⟶ F => φ.hom a) h).isAlgebraic_iff.mp
    inferInstance

section OverBase

variable {X Y : Scheme.{u}} {K : Type u} [Field K]

/-- The two spellings of the canonical algebra structure on a residue field over the base
agree, so the corresponding algebraicity statements are equivalent. -/
theorem isAlgebraic_residueField_iff (f : X ⟶ Spec (.of K)) (x : X) :
    (letI := (Spec.preimage (X.fromSpecResidueField x ≫ f)).hom.toAlgebra;
      Algebra.IsAlgebraic K (X.residueField x)) ↔
      (letI : (f x).asIdeal.IsPrime := (f x).isPrime;
        letI := (CommRingCat.ofHom (algebraMap K (f x).asIdeal.ResidueField) ≫
          (Scheme.Spec.residueFieldIso (.of K) (f x)).inv ≫
            f.residueFieldMap x).hom.toAlgebra;
        Algebra.IsAlgebraic K (X.residueField x)) := by
  rw [Spec.preimage_fromSpecResidueField_comp f x]

/-- Algebraicity of the residue field over the base is invariant under a morphism over the
base whose induced map of residue fields is an isomorphism. -/
theorem isAlgebraic_residueField_comp_iff (e : X ⟶ Y) (g : Y ⟶ Spec (.of K)) (x : X)
    [IsIso (e.residueFieldMap x)] :
    (letI := (Spec.preimage (X.fromSpecResidueField x ≫ e ≫ g)).hom.toAlgebra;
      Algebra.IsAlgebraic K (X.residueField x)) ↔
      (letI := (Spec.preimage (Y.fromSpecResidueField (e x) ≫ g)).hom.toAlgebra;
        Algebra.IsAlgebraic K (Y.residueField (e x))) := by
  let _ : Algebra K (Y.residueField (e x)) :=
    (Spec.preimage (Y.fromSpecResidueField (e x) ≫ g)).hom.toAlgebra
  let _ : Algebra K (X.residueField x) :=
    (Spec.preimage (X.fromSpecResidueField x ≫ e ≫ g)).hom.toAlgebra
  have hcomp := Spec.preimage_fromSpecResidueField_comp_comp e g x
  refine ⟨fun h => ?_, fun h => ?_⟩
  · let _ : Algebra.IsAlgebraic K (X.residueField x) := h
    exact isAlgebraic_of_commRingCatIso (asIso (e.residueFieldMap x)).symm
      ((asIso (e.residueFieldMap x)).comp_inv_eq.mpr hcomp)
  · let _ : Algebra.IsAlgebraic K (Y.residueField (e x)) := h
    exact isAlgebraic_of_commRingCatIso (asIso (e.residueFieldMap x)) hcomp.symm

end OverBase

/-- For an affine scheme over a field, algebraicity of the residue field of a prime implies
algebraicity of the scheme-theoretic residue field over the base. -/
theorem isAlgebraic_residueField_specMap {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    (q : Spec (.of A))
    (h : letI : q.asIdeal.IsPrime := q.isPrime
      Algebra.IsAlgebraic K q.asIdeal.ResidueField) :
    letI := (Spec.preimage ((Spec (.of A)).fromSpecResidueField q ≫
      Spec.map (CommRingCat.ofHom (algebraMap K A)))).hom.toAlgebra
    Algebra.IsAlgebraic K ((Spec (.of A)).residueField q) := by
  let _ : q.asIdeal.IsPrime := q.isPrime
  let _ : Algebra K ((Spec (.of A)).residueField q) :=
    (Spec.preimage ((Spec (.of A)).fromSpecResidueField q ≫
      Spec.map (CommRingCat.ofHom (algebraMap K A)))).hom.toAlgebra
  let _ : Algebra.IsAlgebraic K (CommRingCat.of q.asIdeal.ResidueField) := h
  exact isAlgebraic_of_commRingCatIso (Scheme.Spec.residueFieldIso (.of A) q).symm
    (Spec.preimage_fromSpecResidueField_comp_specMap q).symm

/-- Over an algebraically closed field, a point whose residue field is algebraic over the base
is the image of a section of the structure morphism. -/
theorem exists_isSection_of_isAlgebraic_residueField
    {X : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K] (f : X ⟶ Spec (.of K)) (x : X)
    [Algebra K (X.residueField x)]
    (halg : CommRingCat.ofHom (algebraMap K (X.residueField x)) =
      Spec.preimage (X.fromSpecResidueField x ≫ f))
    [Algebra.IsAlgebraic K (X.residueField x)] :
    ∃ q : Spec (.of K) ⟶ X, q ≫ f = 𝟙 _ ∧ ∀ s, q s = x := by
  have : Algebra.IsIntegral K (X.residueField x) := Algebra.IsAlgebraic.isIntegral
  have hbij : Function.Bijective
      (Spec.preimage (X.fromSpecResidueField x ≫ f)).hom := by
    rw [← halg]
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral
  obtain ⟨φ, hφ, hiso⟩ : ∃ φ : CommRingCat.of K ⟶ X.residueField x,
      Spec.map φ = X.fromSpecResidueField x ≫ f ∧ IsIso φ :=
    ⟨_, Spec.map_preimage _, (ConcreteCategory.isIso_iff_bijective _).mpr hbij⟩
  refine ⟨Spec.map (inv φ) ≫ X.fromSpecResidueField x, ?_, fun s => by simp⟩
  rw [Category.assoc, ← hφ, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id]

/-- The form of `AlgebraicGeometry.exists_isSection_of_isAlgebraic_residueField` in which the
algebra structure on the residue field is spelled out as the composite coming from the
structure morphism. -/
theorem exists_isSection_of_isAlgebraic_residueField'
    {X : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K] (f : X ⟶ Spec (.of K)) (x : X)
    (hAlg : letI : (f x).asIdeal.IsPrime := (f x).isPrime
      letI := (CommRingCat.ofHom (algebraMap K (f x).asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso (.of K) (f x)).inv ≫
          f.residueFieldMap x).hom.toAlgebra
      Algebra.IsAlgebraic K (X.residueField x)) :
    ∃ q : Spec (.of K) ⟶ X, q ≫ f = 𝟙 _ ∧ ∀ s, q s = x := by
  let _ : (f x).asIdeal.IsPrime := (f x).isPrime
  let _ : Algebra K (X.residueField x) :=
    (CommRingCat.ofHom (algebraMap K (f x).asIdeal.ResidueField) ≫
      (Scheme.Spec.residueFieldIso (.of K) (f x)).inv ≫ f.residueFieldMap x).hom.toAlgebra
  let _ : Algebra.IsAlgebraic K (X.residueField x) := hAlg
  exact exists_isSection_of_isAlgebraic_residueField f x
    (Spec.preimage_fromSpecResidueField_comp f x).symm

end AlgebraicGeometry

end
