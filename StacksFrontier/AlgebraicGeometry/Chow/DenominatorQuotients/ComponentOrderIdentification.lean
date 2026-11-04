module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.ComponentOrder
public import StacksFrontier.AlgebraicGeometry.Chow.LocalEquationMultiplicity
public import StacksFrontier.AlgebraicGeometry.Chow.StalkLocalSituation.ComponentDimension
public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.ClosureSubscheme

/-!
# The order of vanishing at a minimal prime is the order of vanishing on the component

The length formula of [Stacks, Tag 02QH] produces, for each minimal prime `q` of the local ring
`A = 𝒪_{X, ξ}`, the order of vanishing `Ring.ord (A ⧸ q)` of the image of a germ; part (4) of
[Stacks, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW) states its right-hand side in terms
of the order of vanishing of a rational function *on the irreducible component* that `q` indexes.
`StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.ComponentOrder` identifies the two rings
in which those orders are taken and stops short of
`AlgebraicGeometry.Scheme.ord`, because the step to it — `Stacks.Chow.ord_eq_ringOrd_germ` — wants
`coheight ξ = 1` on the component. That hypothesis is now available, as
`Stacks.Chow.StalkLocalSituation.coheight_eq_one_of_ringEquiv_quotient_minimalPrime`, so this file
completes the identification: for `ξ` a point of delta-dimension `k` in a closed nowhere dense
subset of a scheme of delta-dimension at most `k + 1`, and `Z` the integral component through `ξ`
cut out by a minimal prime `q` of `A`,

  `ord_{A ⧸ q}(germ t) = ord_{Z}(t|_Z)`

for every section `t` of `𝒪_X` near `ξ` whose germ is a nonzerodivisor — which is exactly the
hypothesis the length formula already asks of the numerator and the denominator of a local ratio.

## Main results

* `Stacks.Chow.subschemeι_app_ne_zero_of_germ_notMem_stalkIdeal` — a section whose germ avoids the
  stalk of the ideal sheaf of `Z` does not restrict to zero on `Z`; the kernel of the stalk map of
  a closed immersion is that stalk,
  `AlgebraicGeometry.Scheme.IdealSheafData.ker_stalkMap_subschemeι`.
* `Stacks.Chow.coheight_eq_one_of_stalkIdeal_eq_minimalPrime` — the point of `Z` over `ξ` has
  coheight one in `Z`, with the identification of the stalk of the ideal sheaf passed as an
  equation.
* `Stacks.Chow.ord_quotient_minimalPrime_eq_ord_subscheme` — **the identification**: the order of
  vanishing of the image of a germ in `A ⧸ q` is the order of vanishing on the component of the
  rational function the section represents there.
* `Stacks.Chow.ord_quotient_minimalPrime_sub_eq_ord_subscheme_sub` — the same for the difference of
  the two orders of a ratio `a / b`, which is the factor appearing in the right-hand side of the
  coefficient identity of
  `StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.MultiplicityDifference`.

## Implementation notes

**Every statement here keeps `ξ`, the component `Z` and the ideal `q` independent**, tied together
only by the equations `hz : Z.subschemeι z = ξ` and `hI : Z.stalkIdeal ξ = q.asIdeal`. That is
forced: in the application `Z` is the integral component attached to `X.fromSpecStalk ξ q` and `q`
lives in `PrimeSpectrum (X.presheaf.stalk ξ)`, so both mention `ξ` and neither of the two
equations can be rewritten — the only way to use them is to generalize `ξ` and `q` and `subst`,
which is what the proofs do. `Stacks.Chow.StalkLocalSituation.ComponentDimension` documents the
same constraint and resolves it the other way, by phrasing everything at `Z.subschemeι z`; that
is not available here, because the ring `A ⧸ q` in the conclusion is a ring of germs at `ξ`.

**The nonvanishing of the restriction comes from the nonzerodivisor hypothesis**, through
Mathlib's `notMem_nonZeroDivisors_of_mem_mem_minimalPrimes`: an element of a minimal prime is a
zerodivisor, with no Noetherian hypothesis at all. So the germ of a nonzerodivisor section avoids
every minimal prime of the local ring, hence avoids the stalk of the ideal sheaf of the component
it cuts out, hence does not restrict to zero on that component. The two nonzerodivisor conditions
this consumes are the ones
`Stacks.Chow.StalkLocalSituation.lengthFormula_hypotheses` already produces for the germs of a
local ratio.

**What is still owed for the cycle form of part (4).** The right-hand side of part (4) is
`∑ᵢ mᵢ (Xᵢ → X)_* div_{ℒ|_{Xᵢ}}(sᵢ)`, whose coefficient at `ξ` is
`∑ᵢ mᵢ ord_{Xᵢ, ℒ|_{Xᵢ}}(sᵢ)`. What this file supplies is `ord_{Xᵢ}` of the *rational functions*
that the numerator and the denominator of a local ratio of `s` represent on `Xᵢ`. The remaining
inch is that their quotient is a coordinate of `sᵢ` with respect to the restricted trivializing
basis, which needs `sᵢ` to exist and to be a regular meromorphic section of `ℒ|_{Xᵢ}` —
[Stacks, Tag 02OU] for the pullback of meromorphic functions along `Xᵢ → X` being defined, and
[Stacks, Tag 02OY] parts (1) and (2) for the pullback of `s` and its regularity. Neither is in
this library.

## References

* [Stacks Project, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW)
* [Stacks Project, Tag 02QH](https://stacks.math.columbia.edu/tag/02QH)
* [Stacks Project, Tag 02MD](https://stacks.math.columbia.edu/tag/02MD)
* [Stacks Project, Tag 02OY](https://stacks.math.columbia.edu/tag/02OY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order Topology TopologicalSpace

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}}

/-! ### The restriction of a section to the component is nonzero -/

/-- **A section whose germ at a point of a closed subscheme avoids the stalk of its ideal sheaf
does not restrict to zero on that subscheme.** The kernel of the stalk map of the closed immersion
is exactly that stalk, by
`AlgebraicGeometry.Scheme.IdealSheafData.ker_stalkMap_subschemeι`, and the germ of the restriction
is the image of the germ under the stalk map. -/
theorem subschemeι_app_ne_zero_of_germ_notMem_stalkIdeal (Z : X.IdealSheafData)
    (z : Z.subscheme) {V : X.Opens} (hzV : Z.subschemeι z ∈ V) {t : Γ(X, V)}
    (ht : (X.presheaf.germ V (Z.subschemeι z) hzV).hom t ∉
      Z.stalkIdeal (Z.subschemeι z)) :
    (Z.subschemeι.app V).hom t ≠ 0 := by
  intro h0
  refine ht ?_
  rw [← Z.ker_stalkMap_subschemeι z, RingHom.mem_ker, Scheme.Hom.germ_stalkMap_apply, h0,
    map_zero]

/-! ### The coheight on the component -/

/-- **The point of the component over `ξ` has coheight one in the component.** This is
`Stacks.Chow.StalkLocalSituation.coheight_eq_one_of_mem_minimalPrimes_idealStalk` with the two
identifications `Z.subschemeι z = ξ` and `Z.stalkIdeal ξ = I` passed as equations rather than
built into the statement; see the implementation notes. -/
theorem coheight_eq_one_of_stalkIdeal_eq_minimalPrime (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian X] {k : ℤ}
    (hdim : schemeDeltaDimension C f ≤ ((k + 1 : ℤ) : EInt)) {T : Set X} (hT : IsClosed T)
    (hT' : IsNowhereDense T) (Z : X.IdealSheafData) (z : Z.subscheme) {ξ : X}
    (hz : Z.subschemeι z = ξ) (hξT : ξ ∈ T)
    (hδ : relativeDimension C.dimensionFunction f ξ = k)
    {I : Ideal (X.presheaf.stalk ξ)} (hI : Z.stalkIdeal ξ = I)
    (hq : I ∈ minimalPrimes (X.presheaf.stalk ξ)) :
    coheight z = 1 := by
  subst hz
  subst hI
  refine StalkLocalSituation.coheight_eq_one_of_mem_minimalPrimes_idealStalk C f hdim hT hT' Z z
    hξT hδ ?_
  rw [← Scheme.IdealSheafData.stalkIdeal_eq_stalk]
  exact hq

/-! ### The identification of the two orders of vanishing -/

/-- **The order of vanishing at a minimal prime of `𝒪_{X, ξ}` is the order of vanishing on the
component that prime cuts out.** This is the second of the two identifications part (4) of
[Stacks, Tag 02SW] needs: the sum the length formula of [Stacks, Tag 02QH] produces has, at each
minimal prime `q`, the factor `Ring.ord (𝒪_{X, ξ} ⧸ q)` of the image of a germ, and part (4) has
in its place an order of vanishing along the irreducible component indexed by `q`.

The component is an arbitrary closed subscheme `Z` which is integral and whose ideal sheaf has `q`
as its stalk at `ξ`; the hypotheses on `ξ` are those of [Stacks, Tag 02SW], namely
`dim_δ(X) ≤ k + 1`, delta-dimension `k` at `ξ` and membership of a closed nowhere dense subset,
and they enter only through the coheight of the component at `ξ`. The section is arbitrary with
nonzerodivisor germ, which is the hypothesis
`Stacks.Chow.StalkLocalSituation.lengthFormula_hypotheses` supplies for both the numerator and the
denominator of a local ratio. -/
theorem ord_quotient_minimalPrime_eq_ord_subscheme (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian X] {k : ℤ}
    (hdim : schemeDeltaDimension C f ≤ ((k + 1 : ℤ) : EInt)) {T : Set X} (hT : IsClosed T)
    (hT' : IsNowhereDense T) (Z : X.IdealSheafData) [IsIntegral Z.subscheme]
    [IsLocallyNoetherian Z.subscheme] (z : Z.subscheme) {ξ : X} (hz : Z.subschemeι z = ξ)
    (hξT : ξ ∈ T) (hδ : relativeDimension C.dimensionFunction f ξ = k)
    {q : Ideal (X.presheaf.stalk ξ)} (hq : q ∈ minimalPrimes (X.presheaf.stalk ξ))
    (hI : Z.stalkIdeal ξ = q) {V : X.Opens} [Nonempty (Z.subschemeι ⁻¹ᵁ V : Z.subscheme.Opens)]
    (hξV : ξ ∈ V) {t : Γ(X, V)}
    (ht : (X.presheaf.germ V ξ hξV).hom t ∈ nonZeroDivisors (X.presheaf.stalk ξ)) :
    ((Ring.ord (X.presheaf.stalk ξ ⧸ q)
        (Ideal.Quotient.mk q ((X.presheaf.germ V ξ hξV).hom t))).toNat : ℤ) =
      Z.subscheme.ord
        (Z.subscheme.germToFunctionField (Z.subschemeι ⁻¹ᵁ V) ((Z.subschemeι.app V).hom t)) z := by
  have hco : coheight z = 1 :=
    coheight_eq_one_of_stalkIdeal_eq_minimalPrime C f hdim hT hT' Z z hz hξT hδ hI hq
  subst hz
  subst hI
  have hzV : z ∈ (Z.subschemeι ⁻¹ᵁ V : Z.subscheme.Opens) := hξV
  have hnotMem : (X.presheaf.germ V (Z.subschemeι z) hξV).hom t ∉
      Z.stalkIdeal (Z.subschemeι z) := fun hmem =>
    notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hmem hq ht
  have ht0 : (Z.subschemeι.app V).hom t ≠ 0 :=
    subschemeι_app_ne_zero_of_germ_notMem_stalkIdeal Z z hξV hnotMem
  have hgermZ : (Z.subscheme.presheaf.germ (Z.subschemeι ⁻¹ᵁ V) z hzV).hom
      ((Z.subschemeι.app V).hom t) ≠ 0 := fun h =>
    ht0 (germ_injective_of_isIntegral Z.subscheme z hzV (by simpa using h))
  have hKrull : Ring.KrullDimLE 1 (Z.subscheme.presheaf.stalk z) :=
    krullDimLE_of_coheight_le hco.le
  have htop : Ring.ord (Z.subscheme.presheaf.stalk z)
      ((Z.subscheme.presheaf.germ (Z.subschemeι ⁻¹ᵁ V) z hzV).hom
        ((Z.subschemeι.app V).hom t)) ≠ ⊤ :=
    Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hgermZ)
  have hgerm : (Z.subschemeι.stalkMap z).hom ((X.presheaf.germ V (Z.subschemeι z) hξV).hom t) =
      (Z.subscheme.presheaf.germ (Z.subschemeι ⁻¹ᵁ V) z hzV).hom ((Z.subschemeι.app V).hom t) :=
    Scheme.Hom.germ_stalkMap_apply Z.subschemeι V z hξV t
  have hord : Ring.ord (X.presheaf.stalk (Z.subschemeι z) ⧸ Z.stalkIdeal (Z.subschemeι z))
        (Ideal.Quotient.mk (Z.stalkIdeal (Z.subschemeι z))
          ((X.presheaf.germ V (Z.subschemeι z) hξV).hom t)) =
      Ring.ord (Z.subscheme.presheaf.stalk z)
        ((Z.subscheme.presheaf.germ (Z.subschemeι ⁻¹ᵁ V) z hzV).hom
          ((Z.subschemeι.app V).hom t)) :=
    (ord_subschemeStalk Z z _).trans
      (congrArg (Ring.ord (Z.subscheme.presheaf.stalk z)) hgerm)
  rw [hord]
  exact (ord_eq_ringOrd_germ hco hzV ((Z.subschemeι.app V).hom t) ht0
    (ENat.natCast_toNat htop).symm).symm

/-- **The difference of the two orders at a minimal prime is the difference of the two orders on
the component.** This is `Stacks.Chow.ord_quotient_minimalPrime_eq_ord_subscheme` applied to the
numerator and to the denominator of a local ratio; the left-hand side is the factor appearing in
the right-hand side of
`Stacks.Chow.exists_affineOpen_sheafMultiplicity_denominatorQuotients_sub_eq`. -/
theorem ord_quotient_minimalPrime_sub_eq_ord_subscheme_sub (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian X] {k : ℤ}
    (hdim : schemeDeltaDimension C f ≤ ((k + 1 : ℤ) : EInt)) {T : Set X} (hT : IsClosed T)
    (hT' : IsNowhereDense T) (Z : X.IdealSheafData) [IsIntegral Z.subscheme]
    [IsLocallyNoetherian Z.subscheme] (z : Z.subscheme) {ξ : X} (hz : Z.subschemeι z = ξ)
    (hξT : ξ ∈ T) (hδ : relativeDimension C.dimensionFunction f ξ = k)
    {q : Ideal (X.presheaf.stalk ξ)} (hq : q ∈ minimalPrimes (X.presheaf.stalk ξ))
    (hI : Z.stalkIdeal ξ = q) {V : X.Opens} [Nonempty (Z.subschemeι ⁻¹ᵁ V : Z.subscheme.Opens)]
    (hξV : ξ ∈ V) {a b : Γ(X, V)}
    (ha : (X.presheaf.germ V ξ hξV).hom a ∈ nonZeroDivisors (X.presheaf.stalk ξ))
    (hb : (X.presheaf.germ V ξ hξV).hom b ∈ nonZeroDivisors (X.presheaf.stalk ξ)) :
    ((Ring.ord (X.presheaf.stalk ξ ⧸ q)
          (Ideal.Quotient.mk q ((X.presheaf.germ V ξ hξV).hom a))).toNat : ℤ) -
        ((Ring.ord (X.presheaf.stalk ξ ⧸ q)
          (Ideal.Quotient.mk q ((X.presheaf.germ V ξ hξV).hom b))).toNat : ℤ) =
      Z.subscheme.ord
          (Z.subscheme.germToFunctionField (Z.subschemeι ⁻¹ᵁ V)
            ((Z.subschemeι.app V).hom a)) z -
        Z.subscheme.ord
          (Z.subscheme.germToFunctionField (Z.subschemeι ⁻¹ᵁ V)
            ((Z.subschemeι.app V).hom b)) z :=
  congrArg₂ (fun u v : ℤ => u - v)
    (ord_quotient_minimalPrime_eq_ord_subscheme C f hdim hT hT' Z z hz hξT hδ hq hI hξV ha)
    (ord_quotient_minimalPrime_eq_ord_subscheme C f hdim hT hT' Z z hz hξT hδ hq hI hξV hb)

end Stacks.Chow

end
