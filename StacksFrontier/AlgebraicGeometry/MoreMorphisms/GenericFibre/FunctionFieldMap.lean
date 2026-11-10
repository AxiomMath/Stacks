module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GenericResidueFieldOfSpec
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The residue field of a scheme at a point as an extension of the residue field below

Part of Step B of the proof of Stacks Tag 0559. The proof of Tag 0559 over a domain base `R`
compares the residue field `κ(ξ)` of `X` at its generic point with the residue field
`κ(η) = Frac R` of `Spec R` at its generic point, and feeds the extension `κ(η) ⟶ κ(ξ)` to the
construction of the standard hypersurface model
(`Algebra.exists_mvPolynomial_model_of_isDomain_tensor`). This module supplies that extension
and the one compatibility it has to satisfy.

The extension is `AlgebraicGeometry.Scheme.Hom.residueFieldMapOfEq`, the residue field map of
`f` at `ξ` read off at a point `s` of the target presented as `f ξ`; the hypothesis `f ξ = s` is
taken as an argument rather than substituted, because the consumer meets `s` as
`genericPoint (Spec R)` and the equality as a separate fact.

The compatibility is
`AlgebraicGeometry.algebraMap_comp_residueFieldMapOfEq`: the composite
`R ⟶ κ(s) ⟶ κ(ξ)` of the canonical map of `R` into the residue field of its spectrum
(`AlgebraicGeometry.specResidueFieldAlgebra`) with this extension is the canonical map
`R ⟶ Γ(X, ⊤) ⟶ κ(ξ)`. It is `AlgebraicGeometry.Scheme.Hom.Γevaluation_naturality` after the
equality is substituted, and it is what makes `κ(s) ⟶ κ(ξ)` a map of `R`-algebras.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.residueFieldMapOfEq`: the residue field map of `f` at `x`, with
  the point of the target presented as an arbitrary `y` equal to `f x`.
* `AlgebraicGeometry.residueFieldAlgebraOfEq`: the algebra structure it defines.

## Main results

* `AlgebraicGeometry.algebraMap_comp_residueFieldMapOfEq`: the compatibility square over the
  base ring.
* `AlgebraicGeometry.isScalarTower_specResidueField`: the resulting tower
  `R ⟶ κ(s) ⟶ κ(x)`.

## Implementation notes

`AlgebraicGeometry.Scheme.residueFieldCongr` is `eqToIso`, so every statement here is proved by
substituting the equality and reducing to the corresponding statement of Mathlib at `f x`
itself.

No Stacks tag is attached: Step B is not itself a tag of the source.

## References

* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559), Step B of the first
  proof
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The residue field map of `f` at `x`, with the point of the target presented as a point `y`
equal to `f x`. -/
@[sga "1 I 5.4"]
noncomputable def Scheme.Hom.residueFieldMapOfEq {X Y : Scheme.{u}} (f : X ⟶ Y) {x : X} {y : Y}
    (hy : f x = y) : Y.residueField y ⟶ X.residueField x :=
  (Y.residueFieldCongr hy).inv ≫ f.residueFieldMap x

/-- For the equality `f x = f x`, `residueFieldMapOfEq` is the residue field map of `f` at `x`. -/
@[simp]
theorem Scheme.Hom.residueFieldMapOfEq_rfl {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    f.residueFieldMapOfEq (rfl : f x = f x) = f.residueFieldMap x := by
  simp [Scheme.Hom.residueFieldMapOfEq]

/-- The algebra structure on the residue field of `X` at `x` over the residue field of `Y` at a
point `y` equal to `f x`. -/
noncomputable abbrev residueFieldAlgebraOfEq {X Y : Scheme.{u}} (f : X ⟶ Y) {x : X} {y : Y}
    (hy : f x = y) : Algebra (Y.residueField y) (X.residueField x) :=
  (f.residueFieldMapOfEq hy).hom.toAlgebra

/-- **The compatibility square of Step B of Stacks Tag 0559.** The canonical map of `R` into the
residue field of `Spec R` at a point `s`, followed by the residue field map of `f : X ⟶ Spec R`
at a point `x` with `f x = s`, is the canonical map of `R` into the residue field of `X` at
`x`. -/
theorem algebraMap_comp_residueFieldMapOfEq (R : CommRingCat.{u}) {X : Scheme.{u}}
    (f : X ⟶ Spec R) {x : X} {s : Spec R} (hs : f x = s) :
    letI := specResidueFieldAlgebra R s
    CommRingCat.ofHom (algebraMap R ((Spec R).residueField s)) ≫ f.residueFieldMapOfEq hs =
      (Scheme.ΓSpecIso R).inv ≫ f.appTop ≫ X.Γevaluation x := by
  subst hs
  change ((Scheme.ΓSpecIso R).inv ≫ (Spec R).Γevaluation (f x)) ≫ f.residueFieldMapOfEq rfl = _
  rw [Scheme.Hom.residueFieldMapOfEq_rfl, Category.assoc, Scheme.Γevaluation_naturality f x]

/-- The tower `R ⟶ κ(s) ⟶ κ(x)` defined by the canonical maps, for `f : X ⟶ Spec R` and a point
`s` of `Spec R` equal to `f x`. -/
theorem isScalarTower_specResidueField (R : CommRingCat.{u}) {X : Scheme.{u}} (f : X ⟶ Spec R)
    {x : X} {s : Spec R} (hs : f x = s) :
    letI := specResidueFieldAlgebra R s
    letI := residueFieldAlgebraOfEq f hs
    letI : Algebra R (X.residueField x) :=
      ((Scheme.ΓSpecIso R).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
    IsScalarTower R ((Spec R).residueField s) (X.residueField x) := by
  let := specResidueFieldAlgebra R s
  let := residueFieldAlgebraOfEq f hs
  let : Algebra R (X.residueField x) :=
    ((Scheme.ΓSpecIso R).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq' (RingHom.ext fun r ↦ ?_)
  exact congrArg (fun φ : R ⟶ X.residueField x ↦ φ.hom r)
    (algebraMap_comp_residueFieldMapOfEq R f hs).symm

end AlgebraicGeometry

end
