module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GenericResidueField
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.IntegralSource
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.IrreducibleOfDominant
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.IsoTransport
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Geometric irreducibility of the generic fibre, tested on the residue field above

Let `f : X ⟶ Y` be a morphism of schemes with `X` irreducible carrying the generic point of `X`
to the generic point `η` of `Y`. The generic fibre `X_η` is then irreducible, and the inclusion
`X_η → X` carries the generic point of `X_η` to the generic point of `X` and induces an
isomorphism on residue fields there. Testing geometric irreducibility of `X_η` over `κ(η)` on
that residue field — which is [Stacks, Tag 054Q] — therefore turns into a statement about the
residue field of `X` itself at its generic point:

`X_η` is geometrically irreducible over `κ(η)` if and only if `κ(ξ)` is geometrically irreducible
over `κ(η)`, for `ξ` the generic point of `X`.

Neither side asks `X` to be reduced. This is what makes the criterion usable in the proof of
[Stacks, Tag 0G4F], where the universal divisor `H_univ` is irreducible but, under the tag's own
hypotheses, not reduced.

## Main results

* `AlgebraicGeometry.geometricallyIrreducible_fiber_iff_isGeometricallyIrreducible_residueField`:
  the criterion, over the spectrum of a domain.
* `AlgebraicGeometry.isoSpec_genericPoint`: the canonical isomorphism of an affine scheme with
  the spectrum of its ring of functions carries the generic point to the generic point.
* `AlgebraicGeometry.geometricallyIrreducible_fiber_genericPoint_iff_residueField_of_isAffine`:
  the criterion over an integral affine base, with the residue field of the base written on the
  ring of functions, which is the form in which an affine space over a field supplies it.

## Implementation notes

The comparison of the residue field of `X` at its generic point with that of the generic fibre is
`AlgebraicGeometry.genericFiberResidueFieldMap`, an isomorphism of `κ(η)`-algebras by
`AlgebraicGeometry.residueFieldMapOfEq_comp_genericFiberResidueFieldMap`. Those are stated for a
base of the form `Spec R` with `R` a domain, because the `κ(η)`-linearity is checked by comparing
two ring maps out of `κ(η)` on the image of `R`, so the criterion is proved there first and then
transported to an affine base along `AlgebraicGeometry.Scheme.isoSpec` with
`AlgebraicGeometry.prop_fiberToSpecResidueField_comp_iso_iff`.

The algebra structure of `κ(ξ)` over `κ(η)` is `AlgebraicGeometry.residueFieldAlgebraOfEq`, the
residue field map of `f` itself, rather than a structure read off global sections; this is the
shape in which a client holding a morphism of schemes has it.

## References

* [Stacks Project, Tag 054Q](https://stacks.math.columbia.edu/tag/054Q)
* [Stacks Project, Tag 0G4F](https://stacks.math.columbia.edu/tag/0G4F)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

section SpecBase

variable {R : CommRingCat.{u}} [IsDomain R] {X : Scheme.{u}} [IrreducibleSpace X]
  (f : X ⟶ Spec R) (hgen : f (genericPoint X) = genericPoint (Spec R))

include hgen in
/-- **The generic fibre is geometrically irreducible exactly when the residue field at the
generic point is.** Let `R` be a domain and let `f : X ⟶ Spec R` carry the generic point of an
irreducible `X` to the generic point `η` of `Spec R`. Then the generic fibre of `f` is
geometrically irreducible over `κ(η)` if and only if the residue field of `X` at its generic
point is geometrically irreducible over `κ(η)`.

This is [Stacks, Tag 054Q] applied to the generic fibre, which is irreducible by
`AlgebraicGeometry.Scheme.Hom.irreducibleSpace_fiber_of_genericPoint`, followed by the
identification `AlgebraicGeometry.genericFiberResidueFieldMap` of its residue field at its
generic point with that of `X`. `X` is not assumed reduced. -/
@[stacks 054Q "the generic fibre, read on the residue field of the source",
  ega "IV 4.5.12" "more general"]
theorem geometricallyIrreducible_fiber_iff_isGeometricallyIrreducible_residueField :
    letI := residueFieldAlgebraOfEq f hgen
    GeometricallyIrreducible (f.fiberToSpecResidueField (genericPoint (Spec R))) ↔
      Algebra.IsGeometricallyIrreducible
        ↥((Spec R).residueField (genericPoint (Spec R))) ↥(X.residueField (genericPoint X)) := by
  have : IrreducibleSpace (f.fiber (genericPoint (Spec R))) :=
    f.irreducibleSpace_fiber_of_genericPoint hgen
  let algFib : Algebra ↥((Spec R).residueField (genericPoint (Spec R)))
      ↥((f.fiber (genericPoint (Spec R))).residueField
        (genericPoint (f.fiber (genericPoint (Spec R))))) :=
    ((Scheme.ΓSpecIso ((Spec R).residueField (genericPoint (Spec R)))).inv ≫
      (f.fiberToSpecResidueField (genericPoint (Spec R))).appTop ≫
      (f.fiber (genericPoint (Spec R))).Γevaluation
        (genericPoint (f.fiber (genericPoint (Spec R))))).hom.toAlgebra
  let := residueFieldAlgebraOfEq f hgen
  let e : ↥(X.residueField (genericPoint X)) ≃ₐ[↥((Spec R).residueField
        (genericPoint (Spec R)))]
      ↥((f.fiber (genericPoint (Spec R))).residueField
        (genericPoint (f.fiber (genericPoint (Spec R))))) :=
    AlgEquiv.ofRingEquiv
      (f := (asIso (genericFiberResidueFieldMap f hgen)).commRingCatIsoToRingEquiv)
      fun r ↦ congrArg
        (fun φ : (Spec R).residueField (genericPoint (Spec R)) ⟶
          (f.fiber (genericPoint (Spec R))).residueField
            (genericPoint (f.fiber (genericPoint (Spec R)))) ↦ φ.hom r)
        (residueFieldMapOfEq_comp_genericFiberResidueFieldMap f hgen)
  exact ((geometricallyIrreducible_tfae_functionField
      ↥((Spec R).residueField (genericPoint (Spec R))) (f.fiber (genericPoint (Spec R)))
      (f.fiberToSpecResidueField (genericPoint (Spec R)))
      (genericPoint (f.fiber (genericPoint (Spec R))))
      (genericPoint_spec (f.fiber (genericPoint (Spec R))))).out 1 2).trans
    (isGeometricallyIrreducible_iff_of_algEquiv _ _ _ e).symm

end SpecBase

section AffineBase

variable {Y : Scheme.{u}} [IsAffine Y] [IsIntegral Y] {X : Scheme.{u}} [IrreducibleSpace X]
  (f : X ⟶ Y)

/-- **The canonical isomorphism of an affine scheme with the spectrum of its ring of functions
carries the generic point to the generic point.** -/
theorem isoSpec_genericPoint (Y : Scheme.{u}) [IsAffine Y] [IsIntegral Y] :
    Y.isoSpec.hom (genericPoint Y) = genericPoint (Spec Γ(Y, ⊤)) := by
  have hsur : Set.range Y.isoSpec.hom = Set.univ :=
    Y.isoSpec.hom.homeomorph.surjective.range_eq
  exact (isGenericPoint_apply_of_denseRange Y.isoSpec.hom
      (by rw [hsur]; exact dense_univ) (by simpa using genericPoint_spec Y)).eq
    (by simpa using genericPoint_spec (Spec Γ(Y, ⊤)))

/-- A dominant morphism onto an integral affine scheme is dominant onto the spectrum of its ring
of functions. -/
theorem comp_isoSpec_genericPoint_eq (hgen : f (genericPoint X) = genericPoint Y) :
    (f ≫ Y.isoSpec.hom) (genericPoint X) = genericPoint (Spec Γ(Y, ⊤)) := by
  show Y.isoSpec.hom.base (f.base (genericPoint X)) = _
  rw [hgen, isoSpec_genericPoint]

/-- **The generic fibre over an integral affine base is geometrically irreducible exactly when
the residue field at the generic point is.** The criterion
`AlgebraicGeometry.geometricallyIrreducible_fiber_iff_isGeometricallyIrreducible_residueField`
for a base presented as an integral affine scheme rather than literally as the spectrum of a
domain; the residue field of the base is then written at the generic point of
`Spec Γ(Y, ⊤)`, which is where a fraction-field presentation of it is available. -/
@[stacks 054Q "the generic fibre over an affine base, read on the residue field of the source",
  ega "IV 4.5.12" "more general"]
theorem geometricallyIrreducible_fiber_genericPoint_iff_residueField_of_isAffine
    (hgen : f (genericPoint X) = genericPoint Y) :
    letI := residueFieldAlgebraOfEq (f ≫ Y.isoSpec.hom) (comp_isoSpec_genericPoint_eq f hgen)
    GeometricallyIrreducible (f.fiberToSpecResidueField (genericPoint Y)) ↔
      Algebra.IsGeometricallyIrreducible
        ↥((Spec Γ(Y, ⊤)).residueField (genericPoint (Spec Γ(Y, ⊤))))
        ↥(X.residueField (genericPoint X)) := by
  have : MorphismProperty.RespectsIso @GeometricallyIrreducible.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine Iff.trans ?_ (geometricallyIrreducible_fiber_iff_isGeometricallyIrreducible_residueField
    (f ≫ Y.isoSpec.hom) (comp_isoSpec_genericPoint_eq f hgen))
  rw [← isoSpec_genericPoint Y]
  exact (prop_fiberToSpecResidueField_comp_iso_iff (P := @GeometricallyIrreducible) f
    Y.isoSpec (genericPoint Y)).symm

end AffineBase

end AlgebraicGeometry

end
