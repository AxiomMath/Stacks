module

public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.EmptySupport

/-!
# Tag 0BEM from its two geometric inputs, with no case left out

[Stacks, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM) says that the Euler
characteristics of the twists `ℱ ⊗ 𝓛_1^{⊗ n_1} ⊗ ⋯ ⊗ 𝓛_r^{⊗ n_r}` of a coherent sheaf on a
proper scheme over a field are the values of a rational polynomial which is zero or of total
degree at most `dim Supp ℱ`.

Two disjoint cases of that conclusion are already in the library and are never joined:

* `AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_dimension_descent`
  (`TwistedSheaf/Polynomial.lean`) runs the source's induction, but its hypothesis `hdim`
  bounds a natural number by `topologicalKrullDim (Supp ℱ)` and so is unsatisfiable when the
  support is empty, where that dimension is `⊥`;
* `AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_supp_eq_empty`
  (`TwistedSheaf/EmptySupport.lean`) closes exactly that case, unconditionally.

This file joins them. The point is not the case split, which is one line, but that after it the
remaining debt of Tag 0BEM is *only* the source's own two geometric inputs: the result here has
the tag's conclusion for an arbitrary coherent sheaf, which makes visible that the empty-support
case is already covered.

## Main results

* `AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf`: Tag 0BEM's conclusion for **every**
  coherent sheaf, from the source's two geometric inputs `hbase` and `hstep`, with the
  dimension bound `hdim` required only on nonempty support.
* `AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_eulerCharacteristic_twist_eq`: the
  same with `hbase` replaced by the statement the source actually cites there, namely that on
  zero-dimensional support the Euler characteristic is unchanged by twisting — Tag 0AYT clause
  (5) at rank one.

## Implementation notes

**Why `hdim` is weakened rather than removed.** The induction descends on a natural number, so
it needs a `ℕ`-valued `dim` and a guarantee that `dim ℱ` really is bounded by the dimension of
the support; that guarantee is what makes the conclusion a statement about the support rather
than about the chosen `dim`. On empty support no such natural number exists, and the empty case
is proved by a different argument, so `hdim` is only ever used on nonempty support. Weakening
it to that is therefore free. `hdim` does **not** disappear: it still asks that the dimension
of a nonempty support be bounded by a natural number, which is a real input and is why the
statements here are not unconditional.

**Why `hbase` is restated.** `hbase` as the induction consumes it asks for a rational
polynomial of total degree `0`. The source does not produce one: it cites Tag 0AYT, whose
clause (5) says that twisting by a locally free sheaf of rank `n` multiplies the Euler
characteristic by `n`, so at rank one — which is what an invertible twist is — the Euler
characteristic is unchanged, and *that* is what makes the degree-zero polynomial available.
Stating the hypothesis as the equality means a caller discharges it with clause (5) alone;
`MvPolynomial.C` of the common value, whose total degree is zero, is supplied here.

**What Tag 0BEM still owes after this file.** `hdim`, `hbase` and `hstep`, and nothing else.
`hbase` is Tag 0AYT clause (5) at rank one in the restated form, clauses (4)+(5) in the
abstract one; of that tag only clause (1) is in the library, as
`AlgebraicGeometry.nonempty_generatingSections_of_support_dim_le_zero`. `hstep` is the source's
first-difference identity, which needs the regular meromorphic section and its ideal of
denominators (Tags 02OZ, 02P2), the reduction to a sheaf whose support is the whole scheme
(Tag 02OM), invariance of cohomology along a closed immersion (Tag 089W) and additivity of the
Euler characteristic (Tag 08AA, in the library as
`AlgebraicGeometry.eulerCharacteristic_add_of_shortExact_of_finiteDimensional_of_isZero` with
Tags 02O6 and 01XJ as hypotheses). Two of its inputs **are** in the library and a tag scan for
02OM or 02P2 will not surface either: the embedded-point sequence of Tag 02OL, in
`StacksFrontier/AlgebraicGeometry/CoherentSubquotients/NowhereDense.lean`, and the case `ℱ = 𝒪_X`
of Tag 02P2, which is Tag 02P0, in
`StacksFrontier/AlgebraicGeometry/Meromorphic/DenominatorSupport.lean` and
`StacksFrontier/AlgebraicGeometry/Divisors/Meromorphic/`.

No attribute for Tag 0BEM is attached: the tag sits on the unconditional
Euler-characteristic theorem of the tagged statement, and the results here are conditional on the
two inputs above.

## References

* [Stacks Project, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM)
* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
* [Stacks Project, Tag 0BEJ](https://stacks.math.columbia.edu/tag/0BEJ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] {r : ℕ}
  (L : Fin r → X.Modules)
  [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)]

/-- **[Stacks, Tag 0BEM] from its two geometric inputs, for every coherent sheaf.** This is
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_dimension_descent` with the
empty-support case folded in from
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_supp_eq_empty`, so the dimension
bound `hdim` is asked for only where the induction can use it.

The hypotheses `hbase` and `hstep` are the source's own two geometric inputs, one per paragraph
of its proof: `hbase` is Tag 0AYT on zero-dimensional support, and `hstep` is the
first-difference identity obtained there from a regular meromorphic section of `𝓛_i` and its
ideal of denominators. Everything else in Tag 0BEM is now discharged. -/
theorem exists_eulerPolynomial_twistedSheaf (dim : X.Modules → ℕ)
    (hbase : ∀ (G : X.Modules) (hG : SheafOfModules.IsCoherent G), dim G = 0 →
      ∃ P : MvPolynomial (Fin r) ℚ, P.totalDegree ≤ 0 ∧
        ∀ n : Fin r → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P
          = (@eulerCharacteristic k _ X f _ (twistedSheaf G L n)
              (@twistedSheaf_isCoherent X r G L _ hG n) : ℚ))
    (hstep : ∀ (G : X.Modules) (hG : SheafOfModules.IsCoherent G), dim G ≠ 0 → ∀ i : Fin r,
      ∃ (G₁ G₂ : X.Modules) (hG₁ : SheafOfModules.IsCoherent G₁)
        (hG₂ : SheafOfModules.IsCoherent G₂), dim G₁ < dim G ∧ dim G₂ < dim G ∧
        ∀ n : Fin r → ℤ,
          (@eulerCharacteristic k _ X f _ (twistedSheaf G L (Function.update n i (n i + 1)))
              (@twistedSheaf_isCoherent X r G L _ hG _) : ℚ)
            - (@eulerCharacteristic k _ X f _ (twistedSheaf G L n)
                (@twistedSheaf_isCoherent X r G L _ hG n) : ℚ)
            = (@eulerCharacteristic k _ X f _ (twistedSheaf G₁ L n)
                (@twistedSheaf_isCoherent X r G₁ L _ hG₁ n) : ℚ)
              - (@eulerCharacteristic k _ X f _ (twistedSheaf G₂ L n)
                  (@twistedSheaf_isCoherent X r G₂ L _ hG₂ n) : ℚ))
    (F : X.Modules) (hF : SheafOfModules.IsCoherent F)
    (hdim : SheafOfModules.supp F ≠ ∅ →
      ((dim F : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim (SheafOfModules.supp F)) :
    ∃ P : MvPolynomial (Fin r) ℚ,
      (P = 0 ∨ (P.totalDegree : WithBot ℕ∞) ≤
        topologicalKrullDim (SheafOfModules.supp F)) ∧
      ∀ n : Fin r → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P
        = (@eulerCharacteristic k _ X f _ (twistedSheaf F L n)
            (@twistedSheaf_isCoherent X r F L _ hF n) : ℚ) := by
  by_cases hsupp : SheafOfModules.supp F = ∅
  · exact exists_eulerPolynomial_twistedSheaf_of_supp_eq_empty k f L F hF hsupp
  · exact exists_eulerPolynomial_twistedSheaf_of_dimension_descent k f L dim hbase hstep F hF
      (hdim hsupp)

/-- **[Stacks, Tag 0BEM] with its base case stated as the source states it.** On
zero-dimensional support Tag 0AYT gives not a degree-zero polynomial but an equality: twisting
by an invertible sheaf does not change the Euler characteristic, which is clause (5) of that tag
at rank one. This is `AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf` with `hbase`
replaced by that equality, the constant polynomial being supplied here. -/
theorem exists_eulerPolynomial_twistedSheaf_of_eulerCharacteristic_twist_eq
    (dim : X.Modules → ℕ)
    (hbase : ∀ (G : X.Modules) (hG : SheafOfModules.IsCoherent G), dim G = 0 →
      ∀ n : Fin r → ℤ, @eulerCharacteristic k _ X f _ (twistedSheaf G L n)
          (@twistedSheaf_isCoherent X r G L _ hG n)
        = @eulerCharacteristic k _ X f _ G hG)
    (hstep : ∀ (G : X.Modules) (hG : SheafOfModules.IsCoherent G), dim G ≠ 0 → ∀ i : Fin r,
      ∃ (G₁ G₂ : X.Modules) (hG₁ : SheafOfModules.IsCoherent G₁)
        (hG₂ : SheafOfModules.IsCoherent G₂), dim G₁ < dim G ∧ dim G₂ < dim G ∧
        ∀ n : Fin r → ℤ,
          (@eulerCharacteristic k _ X f _ (twistedSheaf G L (Function.update n i (n i + 1)))
              (@twistedSheaf_isCoherent X r G L _ hG _) : ℚ)
            - (@eulerCharacteristic k _ X f _ (twistedSheaf G L n)
                (@twistedSheaf_isCoherent X r G L _ hG n) : ℚ)
            = (@eulerCharacteristic k _ X f _ (twistedSheaf G₁ L n)
                (@twistedSheaf_isCoherent X r G₁ L _ hG₁ n) : ℚ)
              - (@eulerCharacteristic k _ X f _ (twistedSheaf G₂ L n)
                  (@twistedSheaf_isCoherent X r G₂ L _ hG₂ n) : ℚ))
    (F : X.Modules) (hF : SheafOfModules.IsCoherent F)
    (hdim : SheafOfModules.supp F ≠ ∅ →
      ((dim F : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim (SheafOfModules.supp F)) :
    ∃ P : MvPolynomial (Fin r) ℚ,
      (P = 0 ∨ (P.totalDegree : WithBot ℕ∞) ≤
        topologicalKrullDim (SheafOfModules.supp F)) ∧
      ∀ n : Fin r → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P
        = (@eulerCharacteristic k _ X f _ (twistedSheaf F L n)
            (@twistedSheaf_isCoherent X r F L _ hF n) : ℚ) :=
  exists_eulerPolynomial_twistedSheaf k f L dim
    (fun G hG hG0 => ⟨MvPolynomial.C ((@eulerCharacteristic k _ X f _ G hG : ℤ) : ℚ),
      le_of_eq (MvPolynomial.totalDegree_C _), fun n => by
        rw [MvPolynomial.eval_C, hbase G hG hG0 n]⟩)
    hstep F hF hdim

end AlgebraicGeometry

end
