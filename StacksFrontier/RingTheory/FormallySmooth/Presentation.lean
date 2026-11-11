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
* `Algebra.FormallySmooth.tfae_lifting_of_surjective`: Stacks 031J in full, adding the lifting
  property of Stacks 00TI as a condition; in the four conditions above the first is Mathlib's
  `Algebra.FormallySmooth`, which is by definition the fourth.

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
4. `Ω[S⁄R]` is a projective `S`-module and `H₁(NL_{S/R}) = 0`.

Mathlib's `Algebra.FormallySmooth R S` is defined as condition 4, so the first item here is Stacks'
condition (6), not the lifting property of Stacks 00TI. The complete Stacks statement, with the
lifting property as a separate condition, is `Algebra.FormallySmooth.tfae_lifting_of_surjective`. -/
@[ega "0 20.4.9" "discrete case",
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

/-- **Stacks 031J.** Let `R → S` be a ring map, let `P` be a formally smooth `R`-algebra and let
`P → S` be a surjection with kernel `J`. The following are equivalent:

1. `S` is formally smooth over `R` in the sense of Stacks 00TI: for every `R`-algebra `B` and every
   ideal `I ⊆ B` of square zero, every `R`-algebra map `S → B ⧸ I` lifts to an `R`-algebra map
   `S → B`;
2. the surjection `P ⧸ J² → S` admits an `R`-algebra section;
3. the sequence `0 → J/J² → S ⊗[P] Ω[P⁄R] → Ω[S⁄R] → 0` is split short exact, i.e. its first map
   is injective and its second map admits an `S`-linear section;
4. `Ω[S⁄R]` is a projective `S`-module and `H₁(NL_{S/R}) = 0`;
5. `S` is an `Algebra.FormallySmooth R`-algebra (Mathlib's definition, which is condition 4).

The lifting condition quantifies over `R`-algebras `B` in the universe `max u v`, where `R : Type u`
and `S : Type v`, the universe in which Mathlib proves the lifting criterion. -/
@[stacks 031J "The presentation `P` is a variable, so conditions 2 and 3 hold for some `P` iff they
hold for every `P` (each is equivalent to condition 1); Stacks' conditions (2)/(3) are item 2,
(4)/(5) are item 3 and (6) is item 4. Item 5 is Mathlib's `Algebra.FormallySmooth`, which is (6)
by definition."]
public theorem Algebra.FormallySmooth.tfae_lifting_of_surjective.{u, v, w}
    {R : Type u} {S : Type v} {P : Type w} [CommRing R] [CommRing S] [CommRing P]
    [Algebra R S] [Algebra R P] [Algebra P S] [IsScalarTower R P S]
    [Algebra.FormallySmooth R P] (hf : Function.Surjective (algebraMap P S)) :
    List.TFAE
      [ ∀ ⦃B : Type (max u v)⦄ [CommRing B] [Algebra R B] (I : Ideal B), I ^ 2 = ⊥ →
          Function.Surjective ((Ideal.Quotient.mkₐ R I).comp : (S →ₐ[R] B) → S →ₐ[R] B ⧸ I),
        ∃ g, (IsScalarTower.toAlgHom R P S).kerSquareLift.comp g = AlgHom.id R S,
        Function.Injective (kerCotangentToTensor R P S) ∧
          ∃ σ : Ω[S⁄R] →ₗ[S] S ⊗[P] Ω[P⁄R], mapBaseChange R P S ∘ₗ σ = LinearMap.id,
        Module.Projective S Ω[S⁄R] ∧ Subsingleton (Algebra.H1Cotangent R S),
        Algebra.FormallySmooth R S ] := by
  have h := Algebra.FormallySmooth.tfae_of_surjective (R := R) hf
  tfae_have 1 ↔ 5 := (Algebra.FormallySmooth.iff_comp_surjective (R := R) (A := S)).symm
  tfae_have 5 ↔ 2 := h.out 1 2
  tfae_have 5 ↔ 3 := h.out 1 3
  tfae_have 5 ↔ 4 := h.out 1 4
  tfae_finish

end
