module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.FunctionFieldMap

/-!
# The residue field of a finite type scheme is essentially of finite type over the base

Let `f : X ⟶ Spec R` be locally of finite type and let `x` be a point of `X`. The residue field
`κ(x)`, an `R`-algebra through the composite `R ⟶ Γ(X, ⊤) ⟶ κ(x)`, is essentially of finite type
over `R`, and over the residue field `κ(s)` of `Spec R` at `s = f x`.

## Main results

* `AlgebraicGeometry.finiteType_appLE_top`: the sections of `X` over an affine open form a finite
  type `R`-algebra.
* `AlgebraicGeometry.isScalarTower_sections_stalk`: the tower `R ⟶ Γ(X, U) ⟶ 𝒪_{X,x}`.
* `AlgebraicGeometry.isScalarTower_stalk_residueField`: the tower `R ⟶ 𝒪_{X,x} ⟶ κ(x)`.
* `AlgebraicGeometry.essFiniteType_residueField`: `κ(x)` is essentially of finite type over `R`.
* `AlgebraicGeometry.essFiniteType_specResidueField_residueField`: `κ(x)` is essentially of
  finite type over `κ(s)`.

## References

* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559), Step B of the first
  proof
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- For a morphism to an affine scheme which is locally of finite type, the sections over an
affine open of the source form a finite type algebra over the base ring. -/
theorem finiteType_appLE_top (R : CommRingCat.{u}) {X : Scheme.{u}} (f : X ⟶ Spec R)
    [LocallyOfFiniteType f] {U : X.Opens} (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ ⊤) :
    ((Scheme.ΓSpecIso R).inv ≫ f.appLE ⊤ U e).hom.FiniteType := by
  have hsurj : Function.Surjective (Scheme.ΓSpecIso R).inv.hom :=
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv.surjective
  exact RingHom.finiteType_stableUnderComposition _ _
    (RingHom.FiniteType.of_surjective _ hsurj)
    (f.finiteType_appLE (isAffineOpen_top (Spec R)) hU e)

/-- The tower `R ⟶ Γ(X, U) ⟶ 𝒪_{X,x}` for a point `x` of an open `U` of a scheme over
`Spec R`. -/
theorem isScalarTower_sections_stalk (R : CommRingCat.{u}) {X : Scheme.{u}} (f : X ⟶ Spec R)
    (x : X) (U : X.Opens) (hxU : x ∈ U) (e : U ≤ f ⁻¹ᵁ ⊤) :
    letI : Algebra R Γ(X, U) := ((Scheme.ΓSpecIso R).inv ≫ f.appLE ⊤ U e).hom.toAlgebra
    letI : Algebra R (X.presheaf.stalk x) :=
      ((Scheme.ΓSpecIso R).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial).hom.toAlgebra
    letI : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
    IsScalarTower R Γ(X, U) (X.presheaf.stalk x) := by
  let : Algebra R Γ(X, U) := ((Scheme.ΓSpecIso R).inv ≫ f.appLE ⊤ U e).hom.toAlgebra
  let : Algebra R (X.presheaf.stalk x) :=
    ((Scheme.ΓSpecIso R).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial).hom.toAlgebra
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq' (RingHom.ext fun a ↦ ?_)
  change X.presheaf.germ ⊤ x trivial (f.appTop ((Scheme.ΓSpecIso R).inv.hom a)) =
    X.presheaf.germ U x hxU (f.appLE ⊤ U e ((Scheme.ΓSpecIso R).inv.hom a))
  exact (X.presheaf.germ_res_apply (homOfLE (show U ≤ ⊤ from le_top)) x hxU
    (f.appTop ((Scheme.ΓSpecIso R).inv.hom a))).symm

/-- The tower `R ⟶ 𝒪_{X,x} ⟶ κ(x)` for a point `x` of a scheme over `Spec R`. -/
theorem isScalarTower_stalk_residueField (R : CommRingCat.{u}) {X : Scheme.{u}} (f : X ⟶ Spec R)
    (x : X) :
    letI : Algebra R (X.presheaf.stalk x) :=
      ((Scheme.ΓSpecIso R).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial).hom.toAlgebra
    letI : Algebra R (X.residueField x) :=
      ((Scheme.ΓSpecIso R).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
    letI : Algebra (X.presheaf.stalk x) (X.residueField x) := (X.residue x).hom.toAlgebra
    IsScalarTower R (X.presheaf.stalk x) (X.residueField x) := by
  let : Algebra R (X.presheaf.stalk x) :=
    ((Scheme.ΓSpecIso R).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial).hom.toAlgebra
  let : Algebra R (X.residueField x) :=
    ((Scheme.ΓSpecIso R).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
  let : Algebra (X.presheaf.stalk x) (X.residueField x) := (X.residue x).hom.toAlgebra
  exact IsScalarTower.of_algebraMap_eq' (RingHom.ext fun _ ↦ rfl)

/-- The residue field of a scheme locally of finite type over `Spec R` at any point is
essentially of finite type over `R`. -/
theorem essFiniteType_residueField (R : CommRingCat.{u}) {X : Scheme.{u}} (f : X ⟶ Spec R)
    [LocallyOfFiniteType f] (x : X) :
    letI : Algebra R (X.residueField x) :=
      ((Scheme.ΓSpecIso R).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
    Algebra.EssFiniteType R (X.residueField x) := by
  let U : X.Opens := (X.affineCover.f (X.affineCover.idx x)).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange _
  have hxU : x ∈ U := X.affineCover.covers x
  have e : U ≤ f ⁻¹ᵁ ⊤ := le_top
  let : Algebra R Γ(X, U) := ((Scheme.ΓSpecIso R).inv ≫ f.appLE ⊤ U e).hom.toAlgebra
  let : Algebra R (X.presheaf.stalk x) :=
    ((Scheme.ΓSpecIso R).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial).hom.toAlgebra
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
  let : Algebra R (X.residueField x) :=
    ((Scheme.ΓSpecIso R).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
  let : Algebra (X.presheaf.stalk x) (X.residueField x) := (X.residue x).hom.toAlgebra
  have : IsScalarTower R Γ(X, U) (X.presheaf.stalk x) :=
    isScalarTower_sections_stalk R f x U hxU e
  have : IsScalarTower R (X.presheaf.stalk x) (X.residueField x) :=
    isScalarTower_stalk_residueField R f x
  have hft : Algebra.FiniteType R Γ(X, U) := finiteType_appLE_top R f hU e
  have : IsLocalization (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
      (X.presheaf.stalk x) := hU.isLocalization_stalk ⟨x, hxU⟩
  have : Algebra.EssFiniteType Γ(X, U) (X.presheaf.stalk x) :=
    Algebra.EssFiniteType.of_isLocalization _ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  have : Algebra.EssFiniteType R (X.presheaf.stalk x) :=
    Algebra.EssFiniteType.comp R Γ(X, U) (X.presheaf.stalk x)
  exact Algebra.EssFiniteType.of_surjective
    (IsScalarTower.toAlgHom R (X.presheaf.stalk x) (X.residueField x)) (X.residue_surjective x)

/-- For `f : X ⟶ Spec R` locally of finite type, a point `x` of `X` and a point `s` of `Spec R`
equal to `f x`, the residue field of `X` at `x` is essentially of finite type over the residue
field of `Spec R` at `s`. -/
theorem essFiniteType_specResidueField_residueField (R : CommRingCat.{u}) {X : Scheme.{u}}
    (f : X ⟶ Spec R) [LocallyOfFiniteType f] {x : X} {s : Spec R} (hs : f x = s) :
    letI := specResidueFieldAlgebra R s
    letI := residueFieldAlgebraOfEq f hs
    Algebra.EssFiniteType ((Spec R).residueField s) (X.residueField x) := by
  let := specResidueFieldAlgebra R s
  let := residueFieldAlgebraOfEq f hs
  let : Algebra R (X.residueField x) :=
    ((Scheme.ΓSpecIso R).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
  have : IsScalarTower R ((Spec R).residueField s) (X.residueField x) :=
    isScalarTower_specResidueField R f hs
  have : Algebra.EssFiniteType R (X.residueField x) := essFiniteType_residueField R f x
  exact Algebra.EssFiniteType.of_comp R ((Spec R).residueField s) (X.residueField x)

end AlgebraicGeometry

end
