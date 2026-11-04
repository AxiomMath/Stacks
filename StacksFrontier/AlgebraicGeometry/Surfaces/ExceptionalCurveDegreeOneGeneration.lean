module

public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveDegreewiseSymbol
public import StacksFrontier.AlgebraicGeometry.Surfaces.ThickeningKernelFiltration

/-!
# The whole remaining gap of Stacks 0C2K, as one inequality

`AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData.ofExceptionalCurve` produces
the five geometric inputs of [Stacks, Tag 0C2K] for an exceptional curve of the first kind from
the single statement that the associated graded ring of the projection-kernel filtration is
generated in degree one,

`Iₙ₊₁ ⊆ I₁ Iₙ + Iₙ₊₂`,

a statement about the inverse limit `A = lim Γ(Eₙ, 𝒪)`. This file restates that input without
the inverse limit. By
`AlgebraicGeometry.Scheme.IdealSheafData`
`.formalNeighborhoodFiltration_le_mul_sup_of_thickeningKernel_le` and the surjectivity of the
transition maps of an exceptional curve of the first kind, it suffices that

`K_{p+1} ⊆ K₀ · K_p`  inside  `Γ(E_{p+2}, 𝒪)`,

where `Kⱼ` is the ideal of functions on the thickening `E_{p+2}` vanishing on the smaller
thickening `Eⱼ`. That is a statement about one ring of global functions on one scheme: no
inverse limit, no symbol, no twist, no cohomology in the statement.

That inequality is now proved, so for 0C2K nothing is left conditional; the implication is still
worth having isolated under a name, as the shape in which the geometric input enters.

The inequality in turn needs no thickening at all. By
`AlgebraicGeometry.Scheme.IdealSheafData.thickeningKernel_le_mul_of_mem_closure` it suffices
that every global section of `𝒪_X(-D ^ (p + 2))|_E` be a finite sum of symbols of products —
members of `AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsDegreeOneProducts`, a set of
sections of a twist on `E` and nothing else. That spelling of the hypothesis is
`AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData`
`.ofGradedSectionsDegreeOneGeneration`.

## What the inequality needed, and where it is

Affine-locally on `X` it is the triviality `I^{p+1} = I · I^p + I^{p+2}`. Globally it says that
a *global* function on `E_{p+2}` vanishing on `E_{p+1}` is a finite sum of products of global
functions, and that is where the projective line enters: it is the surjectivity of
`H⁰(𝐏¹, 𝒪(1)) ⊗ H⁰(𝐏¹, 𝒪(p + 1)) ⟶ H⁰(𝐏¹, 𝒪(p + 2))`, once the graded pieces
`Kⱼ / Kⱼ₊₁ ≅ Γ(E, i^*ℐ_{D ^ (j + 1)})` of
`AlgebraicGeometry.Scheme.IdealSheafData.exists_gradedSectionsHom_eq_of_mem_thickeningKernel`
are identified with those spaces *compatibly with multiplication*. Of that identification the
half naming the pairing is
`AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsHomOfEq_restrictedIdealMulSections` in
`StacksFrontier/AlgebraicGeometry/Surfaces/GradedSectionsLocal.lean`, and the half crossing to `𝐏¹`
is
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.prodTwistSection_restrictedIdealMulSections` in
`StacksFrontier/AlgebraicGeometry/Surfaces/ExceptionalCurveTwistMultiplicative.lean`. The two
spellings of the inequality below are therefore both discharged for an exceptional curve of the
first kind, by
`AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData`
`.ofIsExceptionalCurveOfFirstKind` in
`StacksFrontier/AlgebraicGeometry/Surfaces/ExceptionalCurveMonomialData.lean`.

Nothing here carries a `@[stacks]` attribute: this is a step in the proof of Tag 0C2K, not one
of its assertions, and the tag sits on the four clauses in
`StacksFrontier/AlgebraicGeometry/Surfaces/ExceptionalCurveFormalNeighborhood.lean`.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData.ofThickeningKernelGeneration`
  — the five geometric inputs of [Stacks, Tag 0C2K] from `K_{p+1} ⊆ K₀ · K_p` alone.
* `AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData`
  `.ofGradedSectionsDegreeOneGeneration` — the same five inputs from degree-one generation of
  the symbols, a statement about the sections of the twists `i^*ℐ_{D ^ m}` on `E` alone.

## References

* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} {D : X.IdealSheafData} {k : Type u} [Field k]
  {e : projectiveLineProj k ≅ D.subscheme}

namespace ExceptionalMonomialData

/-- **The five geometric inputs of [Stacks, Tag 0C2K] from one inequality between ideals of
functions on one thickening.**

`hgenK` says that a global function on `E_{p+2}` vanishing on `E_{p+1}` is a sum of products of
a global function vanishing on `E` with a global function vanishing on `Eₚ`. The reverse
inclusion is `AlgebraicGeometry.Scheme.IdealSheafData.thickeningKernel_mul_le`, proved
unconditionally, so `hgenK` is the assertion that that containment is an equality.

Everything else [Stacks, Tag 0C2K] needs for an exceptional curve of the first kind is already
proved: multiplicativity of the filtration, the residue quotient being a field, the degreewise
symbol system, and the passage from degree-one generation to the three monomial statements. -/
public def ofThickeningKernelGeneration (hE : IsExceptionalCurveOfFirstKind D k e)
    (hgenK : ∀ p : ℕ, thickeningKernel D (Nat.le_succ (p + 1)) ≤
      thickeningKernel D (Nat.zero_le (p + 2)) * thickeningKernel D (Nat.le_add_right p 2)) :
    ExceptionalMonomialData D :=
  ofExceptionalCurve hE
    (formalNeighborhoodFiltration_le_mul_sup_of_thickeningKernel_le D
      hE.surjective_thickeningRestriction hgenK)

/-- **The five geometric inputs of [Stacks, Tag 0C2K] from degree-one generation of the symbols
alone.**

`ofThickeningKernelGeneration` still speaks of the ring of functions on a thickening and of a
product of two ideals of it. This spelling does not: `hgen` says that every global section of
`𝒪_X(-D ^ (p + 2))|_E` is a finite sum of members of
`AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsDegreeOneProducts` — symbols of products
of a lift of a degree-one symbol with a lift of a degree-`p + 1` one. Nothing but the global
sections of the twists `i^*ℐ_{D ^ m}` and the pairing they carry appears in it.

That is the form in which the projective line finishes the proof: under an identification of
those sections with `H⁰(𝐏¹_k, 𝒪(m))` *compatible with the two multiplications*, `hgen` is
`Stacks.ProjectiveSpace.Cohomology.mem_closure_degreeOneProducts`. Which members of
`gradedSectionsDegreeOneProducts` the products are is settled —
`AlgebraicGeometry.Scheme.IdealSheafData`
`.mem_gradedSectionsDegreeOneProducts_of_gradedSectionsHom_eq`
puts the restricted product `Stacks.Divisors.restrictedIdealMulSections a b` there — and the
multiplicative identification with `H⁰(𝐏¹_k, 𝒪(m))` is
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.prodTwistSection_restrictedIdealMulSections`, so `hgen` itself is
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.mem_closure_gradedSectionsDegreeOneProducts`.

The effective Cartier instance is redundant — it is `hE.1` — but `hgen` mentions
`gradedSectionsDegreeOneProducts`, which needs it to be stated at all. -/
public def ofGradedSectionsDegreeOneGeneration
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (hE : IsExceptionalCurveOfFirstKind D k e)
    (hgen : ∀ (p : ℕ) (x : Γ((Scheme.Modules.pullback D.subschemeι).obj
        (Stacks.Divisors.negativeTwist (D ^ (p + 1 + 1))), (⊤ : D.subscheme.Opens))),
      x ∈ AddSubgroup.closure (gradedSectionsDegreeOneProducts D p)) :
    ExceptionalMonomialData D :=
  ofThickeningKernelGeneration hE
    (thickeningKernel_le_mul_of_mem_closure D hE.surjective_thickeningRestriction hgen)

end ExceptionalMonomialData

end AlgebraicGeometry.Scheme.IdealSheafData

end
