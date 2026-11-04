module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Characterization of formally smooth algebras by a formally smooth presentation

Let `R → S` be a ring map, let `P` be a formally smooth `R`-algebra and let `P → S` be a
surjection with kernel `J`. Then the four conditions

1. `S` is formally smooth over `R`,
2. the surjection `P ⧸ J² → S` admits an `R`-algebra section,
3. the sequence `0 → J/J² → S ⊗[P] Ω[P⁄R] → Ω[S⁄R] → 0` is split short exact, that is,
   `J/J² → S ⊗[P] Ω[P⁄R]` is injective and `S ⊗[P] Ω[P⁄R] → Ω[S⁄R]` admits an `S`-linear section,
4. `Ω[S⁄R]` is a projective `S`-module and `H₁(L_{S⁄R}) = 0`

are equivalent.

The presentation `P` is a variable of the statement, so it gives both the "for some `P`" and the
"for all `P`" forms of the second and third conditions; such a `P` always exists, for instance
`Algebra.Generators.self R S`. The map `P ⧸ J² → S` is `AlgHom.kerSquareLift` of
`IsScalarTower.toAlgHom R P S`, and the two maps of the sequence are
`KaehlerDifferential.kerCotangentToTensor R P S` and `KaehlerDifferential.mapBaseChange R P S`.

## Main results

* `Stacks.FormallySmooth.PresentationTFAE.solution`: the four conditions above are equivalent.
* `Algebra.FormallySmooth.tfae_of_surjective`: the same statement.

## References

* [StacksProject 031J](https://stacks.math.columbia.edu/tag/031J)
* [StacksProject 00RU](https://stacks.math.columbia.edu/tag/00RU)

## Tags

formally smooth, naive cotangent complex, Kaehler differentials, split exact sequence
-/

@[expose] public section

@[expose] public section

open scoped TensorProduct

open KaehlerDifferential

namespace Stacks.FormallySmooth.PresentationTFAE

/-- For a formally smooth `R`-algebra `P` with a surjection `P → S` of kernel `J`, the following
are equivalent: `S` is formally smooth over `R`; `P ⧸ J² → S` admits an `R`-algebra section;
`J/J² → S ⊗[P] Ω[P⁄R]` is injective and `S ⊗[P] Ω[P⁄R] → Ω[S⁄R]` admits an `S`-linear section;
`Ω[S⁄R]` is a projective `S`-module and `H₁(L_{S⁄R}) = 0`. -/
public theorem solution
    {R : Type*} {S : Type*} {P : Type*} [CommRing R] [CommRing S] [CommRing P]
    [Algebra R S] [Algebra R P] [Algebra P S] [IsScalarTower R P S]
    [Algebra.FormallySmooth R P] (hf : Function.Surjective (algebraMap P S)) :
    List.TFAE
      [ Algebra.FormallySmooth R S,
        ∃ g, (IsScalarTower.toAlgHom R P S).kerSquareLift.comp g = AlgHom.id R S,
        Function.Injective (kerCotangentToTensor R P S) ∧
          ∃ σ : Ω[S⁄R] →ₗ[S] S ⊗[P] Ω[P⁄R], mapBaseChange R P S ∘ₗ σ = LinearMap.id,
        Module.Projective S Ω[S⁄R] ∧ Subsingleton (Algebra.H1Cotangent R S) ] := by
  tfae_have 1 ↔ 2 :=
    Algebra.FormallySmooth.iff_split_surjection (IsScalarTower.toAlgHom R P S) hf
  tfae_have 1 ↔ 4 := Algebra.formallySmooth_iff R S
  tfae_have 4 ↔ 3 := by
    rw [and_comm, Algebra.FormallySmooth.kerCotangentToTensor_injective_iff hf,
      Module.Projective.iff_split_of_projective (mapBaseChange R P S)
        (mapBaseChange_surjective R P S hf)]
  tfae_finish

end Stacks.FormallySmooth.PresentationTFAE

end

@[expose] public section

open scoped TensorProduct

open KaehlerDifferential

/-- Let `R → S` be a ring map, let `P` be a formally smooth `R`-algebra and let `P → S` be a
surjection with kernel `J`. The following are equivalent:

1. `S` is formally smooth over `R`;
2. the surjection `P ⧸ J² → S` admits an `R`-algebra section;
3. the sequence `0 → J/J² → S ⊗[P] Ω[P⁄R] → Ω[S⁄R] → 0` is split short exact, i.e. its first map
   is injective and its second map admits an `S`-linear section;
4. `Ω[S⁄R]` is a projective `S`-module and `H₁(NL_{S/R}) = 0`. -/
@[stacks 031J "Stated for a variable formally smooth presentation, giving the source's `for some
P` and `for all P` forms at once; see the module docstring.",
  ega "0 20.4.9" "discrete case",
  ega "IV 17.2.3" "(i), affine case"]
public theorem Algebra.FormallySmooth.tfae_of_surjective
    {R : Type*} {S : Type*} {P : Type*} [CommRing R] [CommRing S] [CommRing P]
    [Algebra R S] [Algebra R P] [Algebra P S] [IsScalarTower R P S]
    [Algebra.FormallySmooth R P] (hf : Function.Surjective (algebraMap P S)) :
    List.TFAE
      [ Algebra.FormallySmooth R S,
        ∃ g, (IsScalarTower.toAlgHom R P S).kerSquareLift.comp g = AlgHom.id R S,
        Function.Injective (kerCotangentToTensor R P S) ∧
          ∃ σ : Ω[S⁄R] →ₗ[S] S ⊗[P] Ω[P⁄R], mapBaseChange R P S ∘ₗ σ = LinearMap.id,
        Module.Projective S Ω[S⁄R] ∧ Subsingleton (Algebra.H1Cotangent R S) ] :=
  Stacks.FormallySmooth.PresentationTFAE.solution hf

end
