module

public import StacksFrontier.AlgebraicGeometry.Divisors.SectionContraction
public import StacksFrontier.AlgebraicGeometry.Spaces.CanonicalSectionRegular
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceFromQuasicoherentIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels

/-!
# A regular section of an invertible module cuts out an effective Cartier divisor

Let `X` be an algebraic space over a scheme `S`.  For an effective Cartier divisor `D ⊆ X` the
canonical section `1_D` of `𝒪_X(D)` is a regular section, which is part (1) of Stacks 0847 and
is `AlgebraicGeometry.Space.canonicalSection_isRegular`.  This file proves the converse
direction: an invertible `𝒪_X`-module `L` with a regular global section `s` is `𝒪_X(D)` for an
effective Cartier divisor `D ⊆ X`.

## Main results

* `AlgebraicGeometry.Space.exists_isEffectiveCartierDivisor_associatedInvertibleSheaf_iso` is the
  existence assertion of **Stacks 0847, part (2)**.

## Implementation notes

Contracting the inverse `L^{⊗ -1}` with `s` gives a morphism `L^{⊗ -1} ⟶ 𝒪_X`, and it is a
monomorphism exactly because `s` is regular: tensoring by the invertible module `L^{⊗ -1}` is an
autoequivalence of `𝒪_X`-modules, and it carries multiplication by `s` to this contraction up to
the unit and braiding constraints.  This is
`Stacks.SheafOfModules.Invertible.mono_sectionContraction`, and no local trivialization of `L`
enters, exactly as none enters in the proof of part (1).

A monomorphism of sheaves of modules is an isomorphism onto its image subsheaf, so the image of
the contraction is a sheaf of ideals of `𝒪_X` isomorphic to `L^{⊗ -1}`.  It is therefore
invertible, hence finite locally free of rank one, hence quasi-coherent, and so by the
surjectivity half of Stacks 03MB it is the defining ideal sheaf `𝓘_D` of a closed subspace
`D ⊆ X`.  Invertibility of `𝓘_D` is precisely the assertion that `D` is an effective Cartier
divisor, and `𝒪_X(D) ≅ L` because `𝒪_X(D)` and `L` are both inverse to `𝓘_D` for the tensor
product, two inverses of one object being isomorphic by
`Stacks.SheafOfModules.Invertible.isoOfTensorUnit`.

What is proved here is the existence assertion of part (2): the effective Cartier divisor and
the isomorphism exist.  The source states two further clauses, that the divisor is the zero
scheme `Z(s)` of Stacks 0845 and that the divisor and the isomorphism carrying `1_D` to `s` are
unique; they are not proved here, and the attribute's label records which assertion is carried.

The statement lives in its own module rather than beside part (1) in
`StacksFrontier.AlgebraicGeometry.Spaces.CanonicalSectionRegular` because the proof needs the
import closure of Stacks 03MB, which part (1) does not.

## References

* [Stacks Project, Tag 0847](https://stacks.math.columbia.edu/tag/0847)
* [Stacks Project, Tag 0841](https://stacks.math.columbia.edu/tag/0841)
* [Stacks Project, Tag 0843](https://stacks.math.columbia.edu/tag/0843)
* [Stacks Project, Tag 083B](https://stacks.math.columbia.edu/tag/083B)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite
open Stacks.SheafOfModules.Invertible
open Stacks.SheafOfModules.TensorSheafification

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **Stacks 0847, part (2), existence.**  Let `X` be an algebraic space over a scheme `S` and
let `L` be an invertible `𝒪_X`-module with a regular global section `s`.  Then there is an
effective Cartier divisor `D ⊆ X` and an isomorphism `𝒪_X(D) ≅ L`.

Contraction with `s` is a monomorphism `L^{⊗ -1} ⟶ 𝒪_X` whose image is a quasi-coherent sheaf of
ideals isomorphic to `L^{⊗ -1}`; by Stacks 03MB that sheaf of ideals is the defining ideal sheaf
`𝓘_D` of a closed subspace `D`, which is therefore an effective Cartier divisor, and
`𝒪_X(D) ≅ L` because both are inverse to `𝓘_D`. -/
@[stacks 0847 "part (2), existence: a regular global section of an invertible module cuts out \
an effective Cartier divisor whose associated invertible sheaf it is"]
theorem exists_isEffectiveCartierDivisor_associatedInvertibleSheaf_iso
    (L : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property L)
    (s : L.sections)
    (hs : AlgebraicGeometry.IsRegularSection (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property s) :
    ∃ (D : ClosedSubspaces B S hS X.1) (hD : IsEffectiveCartierDivisor B S hS X D),
      Nonempty (associatedInvertibleSheaf B S hS X D hD ≅ L) := by
  have := hL
  have hinvinv : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property (inverseSheaf (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property L) :=
    inverseSheaf_isInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property L
  have := hinvinv
  have hmono : Mono (L.unitHomEquiv.symm s) := hs
  have hiso : inverseSheaf (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property L ≅
      (sectionIdealSubmodule (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property L s).toSheafOfModules :=
    inverseSheafIsoSectionIdeal (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property L s hmono
  have hqcinv : (inverseSheaf (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property L).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_of_isInvertible B S hS X _ hinvinv
  have hqc : (sectionIdealSubmodule (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property L s).toSheafOfModules.IsQuasicoherentOnSite :=
    SheafOfModules.IsQuasicoherentOnSite.of_iso hiso hqcinv
  obtain ⟨D, hDN⟩ := exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite B S hS X
    (sectionIdealSubmodule (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property L s) hqc
  have h0 : idealSheafOfModules B S hS X D ≅ inverseSheaf (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property L :=
    eqToIso (congrArg (fun T => T.toSheafOfModules) hDN) ≪≫ hiso.symm
  have hD : IsEffectiveCartierDivisor B S hS X D :=
    isInvertible_of_iso (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
      h0.symm
  refine ⟨D, hD, ⟨?_⟩⟩
  have eM : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
        ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
        ((structureRingSheaf B S hS X).property)⟩).obj
          ((idealSheafOfModules B S hS X D))).obj (L)) ≅
      SheafOfModules.unit (structureRingSheaf B S hS X) :=
    tensorProductIso (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
        h0 (Iso.refl L) ≪≫
      inverseSheafEvaluation (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property L
  exact isoOfTensorUnit (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
    eM (associatedInvertibleSheafEvaluation B S hS X D hD)

end AlgebraicGeometry.Space

end
