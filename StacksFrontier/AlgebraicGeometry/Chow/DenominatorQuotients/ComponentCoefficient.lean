module

public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.ComponentIndexDimension
public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.ComponentOrderIdentification
public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.ComponentSum
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent

/-!
# The coefficient of part (4) as a sum over the components of delta-dimension `k + 1`

The coefficient identity of
`StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.MultiplicityDifference` reads

  `mult(𝒬₂, ξ) - mult(𝒬₁, ξ)
     = ∑_q length(ℱ_ξ at q) · (ord_q(a) - ord_q(b))`,

a sum over the minimal primes of `𝒪_{X, ξ}`, which is the shape the length formula of
[Stacks, Tag 02QH] produces. Part (4) of
[Stacks, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW) states its right-hand side as a sum
over the irreducible components `Xᵢ` of `X` of delta-dimension `k + 1`, with coefficients the
multiplicities `mᵢ` of `[ℱ]_{k+1} = ∑ᵢ mᵢ [Xᵢ]` and factors the orders of vanishing along those
components. This file performs that change of shape, using the two identifications that were
missing:

* the index moves along
  `Stacks.Chow.bijOn_fromSpecStalk_minimalPrimes_topDimensional` — the minimal primes of
  `𝒪_{X, ξ}` are the generic points of the components of delta-dimension `k + 1` through `ξ`;
* each factor becomes an order of vanishing *on* the corresponding component, by
  `Stacks.Chow.ord_quotient_minimalPrime_eq_ord_subscheme`.

The result is

  `mult(𝒬₂, ξ) - mult(𝒬₁, ξ)
     = ∑_{η} mult(ℱ, η) · (ord_{Xη}(a) - ord_{Xη}(b))`,

the sum being over the generic points `η` of the irreducible components of `X` of
delta-dimension `k + 1` through `ξ`, and `X_η` the integral closed subscheme supported on the
closure of `η`. That is the coefficient of part (4) at `ξ` with the right-hand side indexed and
weighted exactly as part (4) indexes and weights it.

## Main definitions

* `Stacks.Chow.componentOrdAt` — `ord_{Xη, ξ}(t)`, the order of vanishing at `ξ` along the
  component through `η` of the rational function a section `t` of `𝒪_X` represents there. Like
  `AlgebraicGeometry.Scheme.ord` itself it has a junk value: `0` when `ξ` is not a point of that
  component.

## Main results

* `Stacks.Chow.componentOrdAt_eq` — the characterization of `Stacks.Chow.componentOrdAt`, which
  is what should be used in place of the definition.
* `Stacks.Chow.finsum_minimalPrimes_eq_finsum_componentOrd` — **the change of shape**: for an
  arbitrary coefficient function, a sum over the minimal primes of `𝒪_{X, ξ}` of the orders at
  those primes is the sum over the components of delta-dimension `k + 1` through `ξ` of the
  orders along them.
* `Stacks.Chow.exists_affineOpen_nonZeroDivisors_sheafMultiplicity_denominatorQuotients_sub_eq` —
  the coefficient identity of `MultiplicityDifference` with the two nonzerodivisor clauses of the
  chart retained; see the implementation notes.
* `Stacks.Chow.exists_affineOpen_sheafMultiplicity_sub_eq_finsum_componentOrd` — the displayed
  identity.

## Implementation notes

**Why the chart statement is re-proved.** `Stacks.Chow.exists_affineOpen_sheafMultiplicity_sub_eq_
finsum_sheafMultiplicity` and the statement it rests on produce an affine open and a ratio `a / b`
but discard the two clauses `a, b ∈ nonZeroDivisors Γ(X, V)` that
`Stacks.Chow.DenominatorStalk.exists_affineOpen_length_denominatorQuotientStalk_eq` had produced.
Those clauses are exactly what the order identification needs: an element of a minimal prime is a
zerodivisor, so a nonzerodivisor germ has nonzero image in the residue ring of every minimal
prime, which is what makes its restriction to the component nonzero. Since an existential cannot
be strengthened after the fact, the chart is re-obtained and the two short proofs — the one of
`MultiplicityDifference` and the coefficient rewrite of `ComponentSum` — are re-run with the two
clauses carried along. Both of those statements are left unchanged.

**The junk value and the chosen point.** The order of vanishing along a component is taken at a
*point of that component*, so naming it requires the point of `X_η` over `ξ`. It exists exactly
when `ξ` lies on the component, and it is unique, but uniqueness is not needed: the definition
takes `Exists.choose` of that existence statement, and by proof irrelevance the chosen point does
not depend on which proof of existence is supplied — so the characterization
`Stacks.Chow.componentOrdAt_eq` can be stated at `Exists.choose` and still be applied with a
point obtained from `Stacks.Chow.exists_subschemeι_vanishingIdeal_closure_eq`. The `dite` is
factored through `Stacks.Chow.componentOrdAux` so that the characterization is one `dite_eq_left`
on a definition whose body is a single branch, rather than a rewrite underneath three `let`s.

**The three instances of the component** — integrality, local Noetherianity and the nonemptiness
of the chart it meets — are `Prop`s, so the ones the definition builds and the ones a consumer
supplies are interchangeable by proof irrelevance; that is why the characterization may take the
nonemptiness as an instance binder while the definition builds its own.

**What is still owed for the cycle form of part (4).** The factor above is the order of vanishing
along `Xᵢ` of the rational functions that `a` and `b` represent there, not yet
`ord_{Xᵢ, ℒ|_{Xᵢ}}(sᵢ)`. The missing step is that `a|_{Xᵢ} / b|_{Xᵢ}` is a coordinate of the
restricted section, which needs the restriction `sᵢ` to exist and be a regular meromorphic
section of `ℒ|_{Xᵢ}`: [Stacks, Tag 02OU] for the pullback of meromorphic functions along
`Xᵢ → X` being defined, and [Stacks, Tag 02OY] parts (1) and (2) for the pullback of `s` and its
regularity. Beyond that, the cycle identity itself needs the pushforward of
`div_{ℒ|_{Xᵢ}}(sᵢ)` along `Xᵢ → X` and the coefficientwise comparison at points *outside* the
exceptional locus, where both sides vanish.

## References

* [Stacks Project, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW)
* [Stacks Project, Tag 02QH](https://stacks.math.columbia.edu/tag/02QH)
* [Stacks Project, Tag 02QX](https://stacks.math.columbia.edu/tag/02QX)
* [Stacks Project, Tag 02OY](https://stacks.math.columbia.edu/tag/02OY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order Topology TopologicalSpace

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}}

/-! ### The order of vanishing along the component through a point -/

/-- The order of vanishing at `ξ`, along the integral component supported on the closure of `η`,
of the rational function that a section `t` of `𝒪_X` represents on that component. The hypothesis
`h` provides the point of the component lying over `ξ`, at which the order is taken. -/
def componentOrdAux [IsLocallyNoetherian X] (ξ η : X) {V : X.Opens} (hξV : ξ ∈ V) (t : Γ(X, V))
    (h : ∃ z : (integralComponentAt η).subscheme,
      (integralComponentAt η).subschemeι z = ξ) : ℤ :=
  let _ := isIntegral_integralComponentAt η
  let _ := (integralComponentAt η).isLocallyNoetherian_subscheme
  let _ : Nonempty ((integralComponentAt η).subschemeι ⁻¹ᵁ V :
      (integralComponentAt η).subscheme.Opens) :=
    ⟨⟨h.choose, show (integralComponentAt η).subschemeι h.choose ∈ V by
      rw [h.choose_spec]; exact hξV⟩⟩
  (integralComponentAt η).subscheme.ord
    ((integralComponentAt η).subscheme.germToFunctionField
      ((integralComponentAt η).subschemeι ⁻¹ᵁ V)
      (((integralComponentAt η).subschemeι.app V).hom t)) h.choose

open scoped Classical in
/-- **The order of vanishing at `ξ` along the component through `η`.** `ord_{Xη, ξ}(t)` for `X_η`
the integral closed subscheme of `X` supported on the closure of `η` and `t` a section of `𝒪_X`
on an open neighbourhood of `ξ`: the order of vanishing, at the point of `X_η` over `ξ`, of the
rational function `t` represents on `X_η`.

As with `AlgebraicGeometry.Scheme.ord` itself the value is junk — here `0` — outside the range in
which it means anything, namely when `ξ` is not a point of `X_η`.
`Stacks.Chow.componentOrdAt_eq` is the characterization and is what should be used. -/
def componentOrdAt [IsLocallyNoetherian X] (ξ η : X) {V : X.Opens} (hξV : ξ ∈ V)
    (t : Γ(X, V)) : ℤ :=
  if h : ∃ z : (integralComponentAt η).subscheme,
      (integralComponentAt η).subschemeι z = ξ then
    componentOrdAux ξ η hξV t h
  else 0

/-- **The characterization of `Stacks.Chow.componentOrdAt`**: at a point `ξ` of the component
through `η` it is the order of vanishing, at the point of the component over `ξ`, of the
restriction of `t`.

The three instances of the component are `Prop`s, so the ones supplied here and the ones the
definition builds are interchangeable; see the implementation notes. -/
theorem componentOrdAt_eq [IsLocallyNoetherian X] (ξ η : X) {V : X.Opens} (hξV : ξ ∈ V)
    (t : Γ(X, V))
    (h : ∃ z : (integralComponentAt η).subscheme,
      (integralComponentAt η).subschemeι z = ξ)
    [IsIntegral (integralComponentAt η).subscheme]
    [IsLocallyNoetherian (integralComponentAt η).subscheme]
    [Nonempty ((integralComponentAt η).subschemeι ⁻¹ᵁ V :
      (integralComponentAt η).subscheme.Opens)] :
    componentOrdAt ξ η hξV t =
      (integralComponentAt η).subscheme.ord
        ((integralComponentAt η).subscheme.germToFunctionField
          ((integralComponentAt η).subschemeι ⁻¹ᵁ V)
          (((integralComponentAt η).subschemeι.app V).hom t)) h.choose := by
  unfold componentOrdAt
  exact dite_eq_left h

/-! ### The change of shape of the right-hand side -/

/-- **A sum over the minimal primes of `𝒪_{X, ξ}` of orders of vanishing at those primes is the
sum over the components of delta-dimension `k + 1` through `ξ` of the orders of vanishing along
them.** This is the composition of the two identifications part (4) of [Stacks, Tag 02SW] needs:
`Stacks.Chow.bijOn_fromSpecStalk_minimalPrimes_topDimensional` on the index and
`Stacks.Chow.ord_quotient_minimalPrime_eq_ord_subscheme` on the factor.

The coefficient function `g` is arbitrary: nothing about the change of shape depends on it, and in
the application it is `Stacks.Chow.sheafMultiplicity ℱ`. The two hypotheses on the germs of `a`
and `b` are the nonzerodivisor clauses that
`Stacks.Chow.StalkLocalSituation.lengthFormula_hypotheses` produces. -/
theorem finsum_minimalPrimes_eq_finsum_componentOrd (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian X] {k : ℤ}
    (hdim : schemeDeltaDimension C f ≤ ((k + 1 : ℤ) : EInt)) {T : Set X} (hT : IsClosed T)
    (hT' : IsNowhereDense T) {ξ : X} (hξT : ξ ∈ T)
    (hδ : relativeDimension C.dimensionFunction f ξ = k) (g : X → ℤ)
    {V : X.Opens} (hξV : ξ ∈ V) {a b : Γ(X, V)}
    (ha : (X.presheaf.germ V ξ hξV).hom a ∈ nonZeroDivisors (X.presheaf.stalk ξ))
    (hb : (X.presheaf.germ V ξ hξV).hom b ∈ nonZeroDivisors (X.presheaf.stalk ξ)) :
    ∑ᶠ q ∈ {q : PrimeSpectrum (X.presheaf.stalk ξ) |
        q.asIdeal ∈ minimalPrimes (X.presheaf.stalk ξ)},
      g (X.fromSpecStalk ξ q) *
          (((Ring.ord (X.presheaf.stalk ξ ⧸ q.asIdeal)
              (Ideal.Quotient.mk q.asIdeal (X.presheaf.germ V ξ hξV a))).toNat : ℤ) -
            ((Ring.ord (X.presheaf.stalk ξ ⧸ q.asIdeal)
              (Ideal.Quotient.mk q.asIdeal (X.presheaf.germ V ξ hξV b))).toNat : ℤ)) =
      ∑ᶠ η ∈ {η : X | η ∈ genericPoints X ∧ η ⤳ ξ ∧
          relativeDimension C.dimensionFunction f η = k + 1},
        g η * (componentOrdAt ξ η hξV a - componentOrdAt ξ η hξV b) := by
  rw [finsum_topDimensionalComponentGenericPoints_eq C f hdim hT hT' hξT hδ
    (fun η => g η * (componentOrdAt ξ η hξV a - componentOrdAt ξ η hξV b))]
  refine finsum_mem_congr rfl fun q hq => ?_
  refine congrArg (fun z : ℤ => g (X.fromSpecStalk ξ q) * z) ?_
  have hex : ∃ z : (integralComponentAt (X.fromSpecStalk ξ q)).subscheme,
      (integralComponentAt (X.fromSpecStalk ξ q)).subschemeι z = ξ :=
    exists_subschemeι_vanishingIdeal_closure_eq ξ q
  have hstalk : (integralComponentAt (X.fromSpecStalk ξ q)).stalkIdeal ξ = q.asIdeal :=
    stalkIdeal_vanishingIdeal_closure_fromSpecStalk ξ q
  let _ := isIntegral_integralComponentAt (X.fromSpecStalk ξ q)
  let _ := (integralComponentAt (X.fromSpecStalk ξ q)).isLocallyNoetherian_subscheme
  let _ : Nonempty ((integralComponentAt (X.fromSpecStalk ξ q)).subschemeι ⁻¹ᵁ V :
      (integralComponentAt (X.fromSpecStalk ξ q)).subscheme.Opens) :=
    ⟨⟨hex.choose, show (integralComponentAt (X.fromSpecStalk ξ q)).subschemeι hex.choose ∈ V by
      rw [hex.choose_spec]; exact hξV⟩⟩
  rw [componentOrdAt_eq ξ (X.fromSpecStalk ξ q) hξV a hex,
    componentOrdAt_eq ξ (X.fromSpecStalk ξ q) hξV b hex]
  refine congrArg₂ (fun u v : ℤ => u - v) ?_ ?_ <;>
    exact ord_quotient_minimalPrime_eq_ord_subscheme C f hdim hT hT'
      (integralComponentAt (X.fromSpecStalk ξ q)) hex.choose hex.choose_spec hξT hδ hq hstalk
      hξV (by assumption)

/-! ### The coefficient identity -/

/-- **The coefficient identity of part (4) of [Stacks, Tag 02SW], with the chart's nonzerodivisor
clauses retained.** This is
`Stacks.Chow.exists_affineOpen_sheafMultiplicity_sub_eq_finsum_sheafMultiplicity` with the two
clauses saying that the germs of the local ratio are nonzerodivisors in `𝒪_{X, ξ}` added to the
conclusion. They are produced by
`Stacks.Chow.StalkLocalSituation.lengthFormula_hypotheses` along the way and discarded there; the
order identification needs them, and an existential cannot be strengthened after the fact. The
hypotheses are exactly those of Tag 02SW together with the point data of part (4). -/
theorem exists_affineOpen_nonZeroDivisors_sheafMultiplicity_denominatorQuotients_sub_eq
    (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (L F : X.Modules) (s : AlgebraicGeometry.MeromorphicSection X.sheaf L)
    [F.IsCoherent] {k : ℤ}
    (hdim : schemeDeltaDimension C f ≤ ((k + 1 : ℤ) : EInt))
    (_hX : HasNoEmbeddedPoints X)
    (hF : HasNoEmbeddedAssociatedPoints F)
    (hSupp : (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F).supp = Set.univ)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (hs : IsRegularMeromorphicSection X.sheaf L s)
    {ξ : X} (hξ : ξ ∈ denominatorBadLocus X L s)
    (hδ : relativeDimension C.dimensionFunction f ξ = k) :
    ∃ (V : X.Opens) (hξV : ξ ∈ V), IsAffineOpen V ∧ ∃ a b : Γ(X, V),
      X.presheaf.germ V ξ hξV a ∈ nonZeroDivisors (X.presheaf.stalk ξ) ∧
      X.presheaf.germ V ξ hξV b ∈ nonZeroDivisors (X.presheaf.stalk ξ) ∧
      sheafMultiplicity
            (@DenominatorStalk.denominatorSectionQuotientDecl X L F s
              (LocallyOfFiniteType.isLocallyNoetherian f) hL hs inferInstance hF hSupp) ξ -
          sheafMultiplicity (denominatorQuotientDecl L F s) ξ =
        ∑ᶠ q ∈ {q : PrimeSpectrum (X.presheaf.stalk ξ) |
            q.asIdeal ∈ minimalPrimes (X.presheaf.stalk ξ)},
          sheafMultiplicity F (X.fromSpecStalk ξ q) *
            (((Ring.ord ((X.presheaf.stalk ξ) ⧸ q.asIdeal)
                (Ideal.Quotient.mk q.asIdeal (X.presheaf.germ V ξ hξV a))).toNat : ℤ) -
              ((Ring.ord ((X.presheaf.stalk ξ) ⧸ q.asIdeal)
                (Ideal.Quotient.mk q.asIdeal (X.presheaf.germ V ξ hξV b))).toNat : ℤ)) := by
  have hNoeth := LocallyOfFiniteType.isLocallyNoetherian f
  have hFq : F.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F).1
  obtain ⟨V, hξV, hVaff, a, b, ha, hb, hQ₁, hQ₂⟩ :=
    DenominatorStalk.exists_affineOpen_length_denominatorQuotientStalk_eq hL hs hF hSupp ξ
  obtain ⟨hfin, ha', hb', hdim1, hemb, hsupp, -⟩ :=
    StalkLocalSituation.lengthFormula_hypotheses C f F hdim hF hSupp
      (denominatorBadLocus_isClosed X L s hL hs)
      (denominatorBadLocus_isNowhereDense X L s hL hs) hVaff hξV hξ hδ ha hb
  refine ⟨V, hξV, hVaff, a, b, ha', hb', ?_⟩
  have : Module.Finite (X.presheaf.stalk ξ) (F.presheaf.stalk ξ) := hfin
  have h₂ : sheafMultiplicity
        (@DenominatorStalk.denominatorSectionQuotientDecl X L F s
          (LocallyOfFiniteType.isLocallyNoetherian f) hL hs inferInstance hF hSupp) ξ =
      ((Module.length (X.presheaf.stalk ξ)
        (F.presheaf.stalk ξ ⧸
          (Ideal.fractionalProductIdeal (X.presheaf.germ V ξ hξV a)
              (X.presheaf.germ V ξ hξV b) •
            (⊤ : Submodule (X.presheaf.stalk ξ) (F.presheaf.stalk ξ))))).toNat : ℤ) :=
    congrArg (fun z : ℕ∞ => (z.toNat : ℤ)) hQ₂
  have h₁ : sheafMultiplicity (denominatorQuotientDecl L F s) ξ =
      ((Module.length (X.presheaf.stalk ξ)
        (F.presheaf.stalk ξ ⧸
          (Ideal.denominatorIdeal (X.presheaf.germ V ξ hξV a) (X.presheaf.germ V ξ hξV b) •
            (⊤ : Submodule (X.presheaf.stalk ξ) (F.presheaf.stalk ξ))))).toNat : ℤ) :=
    congrArg (fun z : ℕ∞ => (z.toNat : ℤ)) hQ₁
  refine Eq.trans (congrArg₂ (fun u v : ℤ => u - v) h₂ h₁) ?_
  refine Eq.trans (Ideal.length_fractionalProduct_quotient_sub_length_denominator_quotient
    (X.presheaf.germ V ξ hξV a) (X.presheaf.germ V ξ hξV b) ha' hb' hdim1 hemb hsupp) ?_
  refine finsum_mem_congr rfl fun q _ => ?_
  exact congrArg
    (fun z : ℤ => z *
      (((Ring.ord ((X.presheaf.stalk ξ) ⧸ q.asIdeal)
          (Ideal.Quotient.mk q.asIdeal (X.presheaf.germ V ξ hξV a))).toNat : ℤ) -
        ((Ring.ord ((X.presheaf.stalk ξ) ⧸ q.asIdeal)
          (Ideal.Quotient.mk q.asIdeal (X.presheaf.germ V ξ hξV b))).toNat : ℤ)))
    (length_localizedModule_stalk_eq_sheafMultiplicity F q)

/-- **The coefficient of part (4) of [Stacks, Tag 02SW] at a point of delta-dimension `k` of the
exceptional locus, as a sum over the irreducible components of `X` of delta-dimension `k + 1`
through that point.** In the situation of Tag 02SW some affine open `V ∋ ξ` carries a local ratio
`a / b` of `s` with

  `mult(𝒬₂, ξ) - mult(𝒬₁, ξ)
     = ∑_η mult(ℱ, η) · (ord_{Xη, ξ}(a) - ord_{Xη, ξ}(b))`,

the sum being over the generic points `η` of the irreducible components of `X` of
delta-dimension `k + 1` through `ξ` — which are the `Xᵢ` of part (4) — with coefficients the
multiplicities `mᵢ = mult(ℱ, η)` of `[ℱ]_{k+1} = ∑ᵢ mᵢ [Xᵢ]` and factors the orders of vanishing
at `ξ` *along* those components.

This is the coefficient identity of
`Stacks.Chow.exists_affineOpen_sheafMultiplicity_denominatorQuotients_sub_eq` with both of the
identifications that statement was missing carried out. It is not part (4), which is an equality
of cycles; the remaining step is recorded in the implementation notes, and no `@[stacks]`
attribute is attached. -/
theorem exists_affineOpen_sheafMultiplicity_sub_eq_finsum_componentOrd
    (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (L F : X.Modules) (s : AlgebraicGeometry.MeromorphicSection X.sheaf L)
    [F.IsCoherent] {k : ℤ}
    (hdim : schemeDeltaDimension C f ≤ ((k + 1 : ℤ) : EInt))
    (_hX : HasNoEmbeddedPoints X)
    (hF : HasNoEmbeddedAssociatedPoints F)
    (hSupp : (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F).supp = Set.univ)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (hs : IsRegularMeromorphicSection X.sheaf L s)
    {ξ : X} (hξ : ξ ∈ denominatorBadLocus X L s)
    (hδ : relativeDimension C.dimensionFunction f ξ = k) :
    ∃ (V : X.Opens) (hξV : ξ ∈ V), IsAffineOpen V ∧ ∃ a b : Γ(X, V),
      sheafMultiplicity
            (@DenominatorStalk.denominatorSectionQuotientDecl X L F s
              (LocallyOfFiniteType.isLocallyNoetherian f) hL hs inferInstance hF hSupp) ξ -
          sheafMultiplicity (denominatorQuotientDecl L F s) ξ =
        ∑ᶠ η ∈ {η : X | η ∈ genericPoints X ∧ η ⤳ ξ ∧
            relativeDimension C.dimensionFunction f η = k + 1},
          sheafMultiplicity F η *
            (@componentOrdAt X (LocallyOfFiniteType.isLocallyNoetherian f) ξ η V hξV a -
              @componentOrdAt X (LocallyOfFiniteType.isLocallyNoetherian f) ξ η V hξV b) := by
  have hNoeth := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨V, hξV, hVaff, a, b, ha, hb, hid⟩ :=
    exists_affineOpen_nonZeroDivisors_sheafMultiplicity_denominatorQuotients_sub_eq C f L F s
      hdim _hX hF hSupp hL hs hξ hδ
  refine ⟨V, hξV, hVaff, a, b, hid.trans ?_⟩
  exact finsum_minimalPrimes_eq_finsum_componentOrd C f hdim
    (denominatorBadLocus_isClosed X L s hL hs)
    (denominatorBadLocus_isNowhereDense X L s hL hs) hξ hδ (sheafMultiplicity F) hξV ha hb

end Stacks.Chow

end
