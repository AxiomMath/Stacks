module

public import StacksFrontier.AlgebraicGeometry.Properties.Unibranch
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local rings with normal reduction are geometrically unibranch

A local ring `R` whose reduction `R ⧸ nilradical R` is a normal domain is geometrically
unibranch: the normalization of the reduction is the reduction itself, a local ring with the
same residue field as `R`.

## Main results

* `AlgebraicGeometry.isGeometricallyUnibranchRing_of_isIntegrallyClosed_quotient_nilradical`.

## Implementation notes

-/

@[expose] public section

open IsLocalRing

universe u

namespace AlgebraicGeometry


/-- A local ring whose reduction is a normal domain is geometrically unibranch: the
normalization of the reduction is the reduction itself, a local ring with the same residue
field. -/
@[ega "0 23.2.1" "more general", ega "III 4.3.6" "more general"]
public theorem isGeometricallyUnibranchRing_of_isIntegrallyClosed_quotient_nilradical
    {R : Type u} [CommRing R] [IsLocalRing R] [IsDomain (R ⧸ nilradical R)]
    (hR : IsIntegrallyClosed (R ⧸ nilradical R)) : IsGeometricallyUnibranchRing R := by
  let q : R →+* R ⧸ nilradical R := Ideal.Quotient.mk _
  have : IsLocalRing (R ⧸ nilradical R) :=
    IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
  have : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  have := hR
  let C := integralClosure (R ⧸ nilradical R) (FractionRing (R ⧸ nilradical R))
  have hCsurj : Function.Surjective (algebraMap (R ⧸ nilradical R) C) := by
    intro z
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral z.2
    exact ⟨r, Subtype.ext hr⟩
  have : IsLocalRing C :=
    IsLocalRing.of_surjective' (algebraMap (R ⧸ nilradical R) C) hCsurj
  let f : R →+* C := (algebraMap (R ⧸ nilradical R) C).comp q
  let : Algebra R C := f.toAlgebra
  have : IsLocalHom f := RingHom.isLocalHom_comp _ _
  unfold IsGeometricallyUnibranchRing
  refine ⟨inferInstance, inferInstance, ?_⟩
  have hAlgSurj : Function.Surjective
      (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField C)) := by
    intro y
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨r, rfl⟩ := hCsurj.comp Ideal.Quotient.mk_surjective z
    exact ⟨IsLocalRing.residue R r, IsLocalRing.ResidueField.algebraMap_residue r⟩
  refine ⟨Algebra.isIntegral_def.mpr fun z => ?_, fun z _ => hAlgSurj z⟩
  obtain ⟨r, rfl⟩ := hAlgSurj z
  exact isIntegral_algebraMap

end AlgebraicGeometry

end
