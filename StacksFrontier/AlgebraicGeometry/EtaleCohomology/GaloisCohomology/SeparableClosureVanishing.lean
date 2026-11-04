module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.MultiplicativeGroupVanishingAllDegrees
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 03R8 in full: both parts of the vanishing proposition at the separable closure

Let `K` be a field with separable algebraic closure `Kˢᵉᵖ`, and assume that `Br(K') = 0` for
every finite extension `K'/K`. Then

1. `H^q(Gal(Kˢᵉᵖ/K), (Kˢᵉᵖ)ˣ) = 0` for every `q ≥ 1`, and
2. `H^q(Gal(Kˢᵉᵖ/K), M) = 0` for every torsion discrete `Gal(Kˢᵉᵖ/K)`-module `M` and every
   `q ≥ 2`,

the groups being this library's continuous group cohomology of Stacks 04JR.

## Main results

* `Stacks.GaloisCohomology.isZero_continuousGroupCohomology_units_and_torsion_of_forall_brauer`:
  the proposition of the tag, both parts in one statement, under the source's hypothesis.

## Implementation notes

Both conjuncts are already proved in this chapter, each in full, so this is an assembly.

The first conjunct is `…GaloisCohomology.isZero_continuousGroupCohomology_units_of_forall_brauer`
read at `Ω = Kˢᵉᵖ`, which takes the same Brauer hypothesis verbatim.

The second conjunct is `…GaloisCohomology.isZero_continuousGroupCohomology_of_isAddTorsion` read
at `Ω = Kˢᵉᵖ`. Its hypothesis asks for `Br(L) = 0` only for the intermediate fields `L` of
`Kˢᵉᵖ/K` that are finite over `K`, i.e. for the finite *separable* extensions of `K`; each such
`L` is a finite extension of `K`, so the source's hypothesis supplies it at `K' = ↥L`.

The second conjunct is stated at the coefficient universe `max u v` of the source statement,
which is the shape the étale comparison of Stacks 03QU consumes; the first is at the universe of
the carrier `Additive (Kˢᵉᵖ)ˣ`, which is `u`.

## References

* [Stacks Project, Tag 03R8](https://stacks.math.columbia.edu/tag/03R8): the proposition, both
  parts of which are stated here.
* [Stacks Project, Tag 04JP](https://stacks.math.columbia.edu/tag/04JP): the category of
  discrete `G`-modules.
* [Stacks Project, Tag 04JR](https://stacks.math.columbia.edu/tag/04JR): the cohomology groups.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace Stacks.GaloisCohomology

/-- **Stacks Project, Tag 03R8.** Let `K` be a field with separable algebraic closure `Kˢᵉᵖ`,
and assume that `Br(K') = 0` for every finite extension `K'/K`. Then

1. `H ^q(Gal(Kˢᵉᵖ/K), (Kˢᵉᵖ)ˣ) = 0` for every `q ≥ 1`, and
2. `H ^q(Gal(Kˢᵉᵖ/K), M) = 0` for every torsion discrete `Gal(Kˢᵉᵖ/K)`-module `M` and every
   `q ≥ 2`,

the groups being this library's continuous group cohomology of Stacks 04JR, and the module of
the first conjunct being the discrete Galois module
`Stacks.GaloisCohomology.unitsContinuousGModule`. -/
@[stacks 03R8 "the WHOLE proposition at Ω = K^sep: part (1) and part (2) together, as one
statement, under exactly the source's hypothesis -- Br(K') = 0 for every finite extension K'/K.
The first conjunct is H^q(Gal(K^sep/K), (K^sep)ˣ) = 0 for every q ≥ 1, at the discrete Galois
module unitsContinuousGModule; the second is H^q(Gal(K^sep/K), M) = 0 for every torsion discrete
Galois module M and every q ≥ 2. Both are values of the derived-functor groups
continuousGroupCohomology of Stacks 04JR. This is an assembly of the two theorems of this chapter
that each prove one part in full: isZero_continuousGroupCohomology_units_of_forall_brauer, in
StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.MultiplicativeGroupVanishingAllDegrees,
which takes the same Brauer hypothesis verbatim and gives every degree q ≥ 1; and
isZero_continuousGroupCohomology_of_isAddTorsion, in
StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.TorsionGaloisVanishing, which
gives every degree q ≥ 2 for every torsion discrete module, and whose hypothesis -- Br(L) = 0 for
the intermediate fields L of K^sep/K finite over K -- is an instance of the source's at K' = ↥L,
every such L being a finite extension of K. Every clause of the proposition is established here.
The per-part registrations elsewhere in the chapter are retained: part (1) in every degree in
MultiplicativeGroupVanishingAllDegrees, part (2) in TorsionGaloisVanishing, and the degree-one
and degree-two statements of part (1) in MultiplicativeGroupVanishingCriterion",
  sga "4½ Arcata 3.1.6"]
theorem isZero_continuousGroupCohomology_units_and_torsion_of_forall_brauer (K : Type u)
    [Field K]
    (hBr : ∀ (K' : Type u) [Field K'] [Algebra K K'] [Module.Finite K K']
      (y : BrauerGroup K'), y = 1) :
    (∀ q : ℕ, 1 ≤ q → IsZero (continuousGroupCohomology.{u, u} Gal(SeparableClosure K/K) q
        (unitsContinuousGModule K (SeparableClosure K)))) ∧
      ∀ (M : ContinuousGModule.{u, max u v} Gal(SeparableClosure K/K)),
        IsAddTorsion M.obj.obj.V → ∀ q : ℕ, 2 ≤ q →
          IsZero (continuousGroupCohomology.{u, v} Gal(SeparableClosure K/K) q M) :=
  ⟨fun q hq ↦ isZero_continuousGroupCohomology_units_of_forall_brauer K (SeparableClosure K)
      hBr q hq,
    fun M hM q hq ↦ isZero_continuousGroupCohomology_of_isAddTorsion.{u, v} K
      (SeparableClosure K) (fun L hL y ↦ by have := hL; exact hBr ↥L y) M hM q hq⟩

end Stacks.GaloisCohomology

end
