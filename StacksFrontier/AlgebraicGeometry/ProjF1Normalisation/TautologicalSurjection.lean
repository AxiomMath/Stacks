module

public import StacksFrontier.AlgebraicGeometry.ProjF1Normalisation.Basic
public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.GenerationNecessary

/-!
# The tautological surjection onto the degree-one twist

The universal pair of a bundle is an invertible sheaf on the relative `Proj` together with a
graded map out of the pulled-back algebra whose degree-one part is surjective. When the pair is the
canonical twist pair of a normalisation datum, that invertible sheaf is identified with the
degree-one twist `𝒪(1)`, so the degree-one part of the graded map becomes a surjection

  `π⁎𝒜₁ ⟶ 𝒪(1)`

on the relative `Proj`. For `𝒜 = Sym(ℰ)` the degree-one piece is `ℰ`, and the surjection is the
tautological quotient `π⁎ℰ ⟶ 𝒪_{𝐏(ℰ)}(1)`.

## Main results

* `Stacks.AlgebraicGeometry.ProjF1Normalisation.exists_epi_to_twistPieceOne`: a bundle whose
  universal pair is canonical for a normalisation datum has an epimorphism from the pullback of
  the degree-one piece of the algebra onto the degree-one piece of the datum's graded algebra.
* `Stacks.AlgebraicGeometry.ProjF1Normalisation.exists_epi_to_twistPieceOne_twistData`: the same
  at a twist datum.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ProjRepresentsF1
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

namespace Stacks.AlgebraicGeometry.ProjF1Normalisation

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {S : Scheme.{u}} (A : SheafGradedAlgebra.{u} S) (TA : TensorAlgebras.{u})
  {ι : TensorAlgebraPullbackIsos.{u} TA}

/-- **The tautological surjection onto the degree-one twist.** A bundle whose universal pair is
the canonical twist pair of a normalisation datum carries an epimorphism from the pullback of the
degree-one piece of the algebra onto the degree-one piece of the datum's graded algebra. -/
public theorem exists_epi_to_twistPieceOne (B : F1Bundle A TA ι) (N : TwistNormalisation A)
    (hB : IsCanonicalTwistPairOf A TA N B.universal) :
    ∃ q : (Scheme.Modules.pullback (relativeProj A).toBase).obj (A.piece 1) ⟶
      N.algebra.piece 1, Epi q := by
  obtain ⟨β, -, -, -, -, -⟩ := hB
  have h₁ : Epi (pairDegreeOneMap A TA B.universal) := epi_pairDegreeOneMap A TA B.universal
  have hiso : IsIso β.hom := ⟨β.inv, β.hom_inv_id, β.inv_hom_id⟩
  have h₂ : Epi β.hom := IsIso.epi_of_iso β.hom
  exact ⟨pairDegreeOneMap A TA B.universal ≫ β.hom, epi_comp _ _⟩

/-- The tautological surjection at a twist datum: a bundle whose universal pair is the canonical
twist pair of a twist datum `D` carries an epimorphism from the pullback of the degree-one piece of
the algebra onto the degree-one piece of the graded algebra of `D`. -/
public theorem exists_epi_to_twistPieceOne_twistData (B : F1Bundle A TA ι) (D : TwistData A)
    (hB : IsCanonicalTwistPair A TA D B.universal) :
    ∃ q : (Scheme.Modules.pullback (relativeProj A).toBase).obj (A.piece 1) ⟶
      D.algebra.piece 1, Epi q :=
  exists_epi_to_twistPieceOne A TA B (ofTwistData A D) hB

end Stacks.AlgebraicGeometry.ProjF1Normalisation

end
