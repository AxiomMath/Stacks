module

public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.SectionQuotientStalk
public import StacksFrontier.AlgebraicGeometry.Chow.StalkLocalSituation.Basic

/-!
# The difference of the multiplicities of the two denominator quotients

Let `X` be locally of finite type over the base of a Chow situation with `dim_δ(X) ≤ k + 1`, let
`L` be an invertible `𝒪_X`-module, let `F` be coherent with full support and no embedded
associated points, and let `s` be a regular meromorphic section of `L`. Part (1) of
[Stacks, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW) puts the two canonical maps of
[Stacks, Tag 02P2](https://stacks.math.columbia.edu/tag/02P2) in two short exact sequences with
cokernels `Q₁ = F / I F` and `Q₂ = (F ⊗ L) / s(I F)`, and part (2) bounds their
delta-dimension by `k`. Part (4) compares the two `k`-cycles `[Q₁]_k` and `[Q₂]_k`.

This file proves the **coefficientwise** statement that comparison rests on. The coefficient of
`[Qᵢ]_k` at a point is `Stacks.Chow.sheafMultiplicity Qᵢ`, the length of the stalk there, and at
a point `ξ` of delta-dimension `k` in the closed nowhere dense exceptional subset of Tag 02P2
there is an affine open carrying a local ratio `a / b` of `s` with

  `mult(Q₂, ξ) - mult(Q₁, ξ)
     = ∑_q length(F_ξ localized at q) · (ord_q(germ a) - ord_q(germ b))`,

the sum being over the minimal primes of the local ring `𝒪_{X, ξ}`. That is exactly the
right-hand side of the length formula of
[Stacks, Tag 02QH](https://stacks.math.columbia.edu/tag/02QH),
`Ideal.length_fractionalProduct_quotient_sub_length_denominator_quotient`, and the identity is
that formula read through the two stalk identifications
`(Q₁)_ξ ≅ F_ξ / (I a b) F_ξ` and `(Q₂)_ξ ≅ F_ξ / (J a b) F_ξ` of
`StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.SectionQuotientStalk`.

## Main results

* `Stacks.Chow.exists_affineOpen_sheafMultiplicity_denominatorQuotients_sub_eq` — the displayed
  identity. Its hypotheses are exactly those of Tag 02SW together with the point data of part
  (4): a point of delta-dimension `k` in the exceptional subset.

## Implementation notes

**What is proved and what is not.** Part (4) of Tag 02SW is an equality of `k`-cycles,
`[Q₂]_k - [Q₁]_k = ∑ mᵢ (Xᵢ → X)_* div(sᵢ)`. What is proved here is its coefficient at a point,
with the right-hand side still in the local form the length formula produces — a sum over the
minimal primes of `𝒪_{X, ξ}` of orders of vanishing of the germs of the ratio. Turning that into
`∑ mᵢ (Xᵢ → X)_* div(sᵢ)` needs two further identifications that this development does not have:
the minimal primes of `𝒪_{X, ξ}` have to be matched with the irreducible components of `X` of
delta-dimension `k + 1` through `ξ`, and the order of vanishing of the germs of `a / b` along
such a component has to be matched with the order of vanishing of `s` there. Neither is a
restatement of anything in the library, so this file carries **no** `@[stacks]` attribute: the tag's
part (4) is the cycle equality, and the attribute belongs on that statement when it exists, not on a
step toward it.

**Where the one-dimensionality comes from.** Not from `HasNoEmbeddedPoints X`: on a disjoint
union of a `k`-dimensional and a `(k+1)`-dimensional integral scheme there are no embedded
points, `dim_δ(X) = k + 1`, and the generic point of the first component has `δ = k` and a field
as local ring, so Krull dimension zero. The hypothesis that does the work is that `ξ` lies in a
closed nowhere dense subset, which for the two quotients of Tag 02SW it does: their supports lie
in `AlgebraicGeometry.denominatorBadLocus`, closed and nowhere dense by
`AlgebraicGeometry.denominatorBadLocus_isClosed` and
`AlgebraicGeometry.denominatorBadLocus_isNowhereDense`. That is the hypothesis `hξ` below, and it
is supplied to `Stacks.Chow.StalkLocalSituation.lengthFormula_hypotheses` as the subset `T`.
`HasNoEmbeddedPoints X` is nevertheless carried, as `_hX`, so that the hypothesis list is
literally that of Tag 02SW, exactly as the six results of
`StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.Basic` carry it.

**Why the attribute is not in that file.** `Chow/DenominatorQuotients/Basic.lean` is where the six
other 02SW attributes live, but the declaration below cannot go there: it consumes
`StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.SectionQuotientStalk`, whose import
closure contains `Basic` itself —
`SectionQuotientStalk → DenominatorActionStalk → Stalks → Basic` — so an import of it from
`Basic` is a cycle. The attribute therefore sits here, downstream, and `Basic` is untouched.

**The local Noetherianity instance** is introduced by hand from `LocallyOfFiniteType f`, and the
quotient `Q₂` is formed with that instance supplied explicitly, as in the frozen
`Stacks.Chow.denominatorSectionQuotientShortComplex_shortExact`: the instance is not found from
the hypothesis list by search. The passage from the two length identities to the two
multiplicities is `congrArg` of `ENat.toNat` composed with the integer coercion, not a `rewrite`:
`Stacks.Chow.sheafMultiplicity` is a `def`, and two definitionally equal module structures on the
stalk are in the import closure, which makes `rewrite` inside a statement about
`Submodule (X.presheaf.stalk ξ) (F.presheaf.stalk ξ)` unreliable.

Finiteness of the stalk is **re-stated** rather than used from the destructured conjunction: the
package returns it, but instance search does not pick the hypothesis up at the spelling the
length formula asks for, and restating it with the ascribed type forces the one definitional
check that makes it visible. This is the spelling gap the package documents, met at the
one place it bites.

## References

* [Stacks Project, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW)
* [Stacks Project, Tag 02QH](https://stacks.math.columbia.edu/tag/02QH)
* [Stacks Project, Tag 02QX](https://stacks.math.columbia.edu/tag/02QX)
* [Stacks Project, Tag 02P2](https://stacks.math.columbia.edu/tag/02P2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Topology TopologicalSpace

universe u

namespace Stacks.Chow

/-- **Stacks 02SW (4), the coefficient identity.** In the situation of Tag 02SW, let `ξ` be a
point of delta-dimension `k` lying in the closed nowhere dense exceptional subset of Tag 02P2.
Then some affine open `V ∋ ξ` carries a local ratio `a / b` of `s` for which the difference of
the multiplicities of the two denominator quotients at `ξ` is the sum, over the minimal primes
of the local ring at `ξ`, of the generic lengths of `F` weighted by the difference of the orders
of vanishing of the germs of `a` and of `b`.

This is the coefficient at `ξ` of the cycle identity of part (4): the coefficients of `[Qᵢ]_k`
are the multiplicities on the left, and the right-hand side is the local form the length formula
of Tag 02QH produces, before the minimal primes are matched with the irreducible components of
delta-dimension `k + 1` and the orders with the order of vanishing of `s` along them. -/
theorem exists_affineOpen_sheafMultiplicity_denominatorQuotients_sub_eq
    (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
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
        ∑ᶠ q ∈ {q : PrimeSpectrum (X.presheaf.stalk ξ) |
            q.asIdeal ∈ minimalPrimes (X.presheaf.stalk ξ)},
          ((Module.length (Localization.AtPrime q.asIdeal)
              (LocalizedModule q.asIdeal.primeCompl (F.presheaf.stalk ξ))).toNat : ℤ) *
            (((Ring.ord ((X.presheaf.stalk ξ) ⧸ q.asIdeal)
                (Ideal.Quotient.mk q.asIdeal (X.presheaf.germ V ξ hξV a))).toNat : ℤ) -
              ((Ring.ord ((X.presheaf.stalk ξ) ⧸ q.asIdeal)
                (Ideal.Quotient.mk q.asIdeal (X.presheaf.germ V ξ hξV b))).toNat : ℤ)) := by
  have hNoeth := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨V, hξV, hVaff, a, b, ha, hb, hQ₁, hQ₂⟩ :=
    DenominatorStalk.exists_affineOpen_length_denominatorQuotientStalk_eq hL hs hF hSupp ξ
  refine ⟨V, hξV, hVaff, a, b, ?_⟩
  obtain ⟨hfin, ha', hb', hdim1, hemb, hsupp, -⟩ :=
    StalkLocalSituation.lengthFormula_hypotheses C f F hdim hF hSupp
      (denominatorBadLocus_isClosed X L s hL)
      (denominatorBadLocus_isNowhereDense X L s hL hs) hVaff hξV hξ hδ ha hb
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
  exact Ideal.length_fractionalProduct_quotient_sub_length_denominator_quotient
    (X.presheaf.germ V ξ hξV a) (X.presheaf.germ V ξ hξV b) ha' hb' hdim1 hemb hsupp

end Stacks.Chow

end
