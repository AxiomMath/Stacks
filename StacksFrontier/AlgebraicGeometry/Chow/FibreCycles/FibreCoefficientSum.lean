module

public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.AssociatedPointsStalk
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.DisjointSections
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.LocalMultiplicity
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor

/-!
# The coefficient of a fibre cycle as a sum over the minimal primes at the point

Let `Z ⊆ X ×_S 𝐏¹_S` be a closed subscheme satisfying the hypotheses of Stacks Tag 02S5, and let
`ξ` be the point of the zero section (or of the infinity section) above a generic point of the
corresponding fibre of `Z` at which `X` has relative dimension `k`. Write `A = 𝒪_{X ×_S 𝐏¹_S, ξ}`,
`I ⊆ A` for the stalk of the ideal sheaf of `Z` and `t ∈ A` for a local equation of the section.
The coefficient of `[Z₀]_k` (resp. `[Z_∞]_k`) at that point is the sum, over the minimal primes `q`
of `I`, of the colength of `(t, q)` times the length of `A/I` localised at `q`.

## Main results

* `Stacks.Chow.exists_subschemeι_eq_zeroSection` and
  `Stacks.Chow.exists_subschemeι_eq_infinitySection` — a point of a fibre of `Z` is the image of
  a point of `Z`.
* `Stacks.Chow.relativeDimension_familyBase_eq_of_zeroSection` and its infinity twin — the
  relative dimension of `Z` over the base at such a point is the relative dimension of `X` over
  the base at the point of the fibre.
* `Stacks.Chow.notMem_schemeAssociatedPoints_of_relativeDimension_eq` — a point of `Z` on either
  distinguished section whose relative dimension is `k` is not an associated point of `Z`.
* `Stacks.Chow.exists_localEquation_cycleAssociatedToZeroFiber_apply_eq_sum_minimalPrimes` and
  `Stacks.Chow.exists_localEquation_cycleAssociatedToInfinityFiber_apply_eq_sum_minimalPrimes` —
  the coefficient of the fibre cycle as the sum over minimal primes.

## References

* [Stacks Project, Tag 02S5](https://stacks.math.columbia.edu/tag/02S5)
* [Stacks Project, Tag 02QG](https://stacks.math.columbia.edu/tag/02QG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing

universe u

namespace Stacks.Chow

/-! ### The point of `Z` above a point of a fibre -/

/-- A point of the zero fibre of `Z` is the image, under the zero section, of a point of `Z`:
the support of the zero fibre is the preimage of the support of `Z`. -/
theorem exists_subschemeι_eq_zeroSection {X S : Scheme.{u}} (f : X ⟶ S)
    (Z : (projectiveLineProduct f).IdealSheafData) (y : (zeroFiber f Z).subscheme) :
    ∃ w : Z.subscheme, Z.subschemeι w = zeroSection f ((zeroFiber f Z).subschemeι y) := by
  have h1 : (zeroFiber f Z).subschemeι y ∈ ((zeroFiber f Z).support : Set X) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨y, rfl⟩
  rw [coe_support_zeroFiber] at h1
  have h2 : zeroSection f ((zeroFiber f Z).subschemeι y) ∈ (Z.support : Set _) := h1
  rw [← Scheme.IdealSheafData.range_subschemeι] at h2
  exact h2

/-- A point of the infinity fibre of `Z` is the image, under the infinity section, of a point of
`Z`. -/
theorem exists_subschemeι_eq_infinitySection {X S : Scheme.{u}} (f : X ⟶ S)
    (Z : (projectiveLineProduct f).IdealSheafData) (y : (infinityFiber f Z).subscheme) :
    ∃ w : Z.subscheme, Z.subschemeι w = infinitySection f ((infinityFiber f Z).subschemeι y) := by
  have h1 : (infinityFiber f Z).subschemeι y ∈ ((infinityFiber f Z).support : Set X) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨y, rfl⟩
  rw [coe_support_infinityFiber] at h1
  have h2 : infinitySection f ((infinityFiber f Z).subschemeι y) ∈ (Z.support : Set _) := h1
  rw [← Scheme.IdealSheafData.range_subschemeι] at h2
  exact h2

/-! ### Relative dimension at such a point -/

/-- At a point of `Z` lying on the zero section, the relative dimension of `Z` over the base is the
relative dimension of `X` over the base at the corresponding point of `X`. -/
theorem relativeDimension_familyBase_eq_of_zeroSection (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (Z : (projectiveLineProduct f).IdealSheafData)
    (w : Z.subscheme) (x : X) (hw : Z.subschemeι w = zeroSection f x) :
    relativeDimension C.dimensionFunction (familyBase f Z) w =
      relativeDimension C.dimensionFunction f x := by
  rw [familyBase, relativeDimension_comp_closedImmersion C.dimensionFunction Z.subschemeι
    (pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f) w, hw,
    ← relativeDimension_comp_closedImmersion C.dimensionFunction (zeroSection f)
      (pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f) x]
  congr 1
  rw [← Category.assoc, zeroSection_comp_fst, Category.id_comp]

/-- At a point of `Z` lying on the infinity section, the relative dimension of `Z` over the base
is the relative dimension of `X` over the base at the corresponding point of `X`. -/
theorem relativeDimension_familyBase_eq_of_infinitySection (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (Z : (projectiveLineProduct f).IdealSheafData)
    (w : Z.subscheme) (x : X) (hw : Z.subschemeι w = infinitySection f x) :
    relativeDimension C.dimensionFunction (familyBase f Z) w =
      relativeDimension C.dimensionFunction f x := by
  rw [familyBase, relativeDimension_comp_closedImmersion C.dimensionFunction Z.subschemeι
    (pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f) w, hw,
    ← relativeDimension_comp_closedImmersion C.dimensionFunction (infinitySection f)
      (pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f) x]
  congr 1
  rw [← Category.assoc, infinitySection_comp_fst, Category.id_comp]

/-! ### The associated-points hypothesis, read at such a point -/

/-- Under the hypothesis of Stacks Tag 02S5 on associated points, a point of `Z` which lies on one
of the two distinguished sections and has relative dimension exactly `k` is not an associated point
of `Z`. -/
theorem notMem_schemeAssociatedPoints_of_relativeDimension_eq (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (Z : (projectiveLineProduct f).IdealSheafData) (k : ℤ) (w : Z.subscheme)
    (hrange : Z.subschemeι w ∈ Set.range (zeroSection f) ∨
      Z.subschemeι w ∈ Set.range (infinitySection f))
    (hw : relativeDimension C.dimensionFunction (familyBase f Z) w = k)
    (hAssociated : w ∈ Stacks.Divisors.schemeAssociatedPoints Z.subscheme →
      ((Z.subschemeι w ∉ Set.range (zeroSection f) ∧
          Z.subschemeι w ∉ Set.range (infinitySection f)) ∨
        relativeDimension C.dimensionFunction (familyBase f Z) w < k)) :
    w ∉ Stacks.Divisors.schemeAssociatedPoints Z.subscheme := by
  intro hmem
  rcases hAssociated hmem with ⟨h₀, hInf⟩ | hlt
  · exact hrange.elim h₀ hInf
  · omega

/-! ### The coefficient of the fibre cycle as a sum over minimal primes -/

/-- The shared argument for the two sections: for a closed immersion `g : X ⟶ X ×_S 𝐏¹_S` whose
stalk-map kernels are principal, the coefficient of the cycle of `Z.comap g` at a generic point of
relative dimension `k` is the sum over the minimal primes of the stalk of `Z`, given a point `w` of
`Z` above the image point which has relative dimension `k` and lies on a distinguished section. -/
private theorem exists_localEquation_cycleAssociatedToComap_apply_eq_sum_minimalPrimes
    (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (Z : (projectiveLineProduct f).IdealSheafData) (k : ℤ) (g : X ⟶ projectiveLineProduct f)
    [IsClosedImmersion g]
    (hg : ∀ x : X, ∃ t : (projectiveLineProduct f).presheaf.stalk (g x),
      RingHom.ker (g.stalkMap x).hom = Ideal.span {t})
    (ξ : genericPoints (Z.comap g).subscheme)
    (hξ : relativeDimension C.dimensionFunction f ((Z.comap g).subschemeι ξ.1) = k)
    (hZ : ∀ ζ : Z.subscheme,
      relativeDimension C.dimensionFunction (familyBase f Z) ζ ≤ k + 1)
    (hAssociated : ∀ ζ : Z.subscheme,
      ζ ∈ Stacks.Divisors.schemeAssociatedPoints Z.subscheme →
      ((Z.subschemeι ζ ∉ Set.range (zeroSection f) ∧
          Z.subschemeι ζ ∉ Set.range (infinitySection f)) ∨
        relativeDimension C.dimensionFunction (familyBase f Z) ζ < k))
    (w : Z.subscheme) (hw : Z.subschemeι w = g ((Z.comap g).subschemeι ξ.1))
    (hrange : Z.subschemeι w ∈ Set.range (zeroSection f) ∨
      Z.subschemeι w ∈ Set.range (infinitySection f))
    (hwdim : relativeDimension C.dimensionFunction (familyBase f Z) w = k) :
    ∃ t : (projectiveLineProduct f).presheaf.stalk (g ((Z.comap g).subschemeι ξ.1)),
      (cycleAssociatedToClosedSubscheme C f (Z.comap g).subschemeι k).1
          ((Z.comap g).subschemeι ξ.1) =
        ((∑ᶠ q ∈ {q : PrimeSpectrum ((projectiveLineProduct f).presheaf.stalk
              (g ((Z.comap g).subschemeι ξ.1))) |
              q.asIdeal ∈ (AlgebraicGeometry.IdealSheafData.stalk Z
                (g ((Z.comap g).subschemeι ξ.1))).minimalPrimes},
            Module.length
                ((projectiveLineProduct f).presheaf.stalk (g ((Z.comap g).subschemeι ξ.1)))
                ((projectiveLineProduct f).presheaf.stalk (g ((Z.comap g).subschemeι ξ.1)) ⧸
                  (Ideal.span {t} ⊔ q.asIdeal)) *
              Module.length (Localization.AtPrime q.asIdeal)
                (LocalizedModule q.asIdeal.primeCompl
                  ((projectiveLineProduct f).presheaf.stalk (g ((Z.comap g).subschemeι ξ.1)) ⧸
                    AlgebraicGeometry.IdealSheafData.stalk Z
                      (g ((Z.comap g).subschemeι ξ.1))))).toNat : ℤ) := by
  have _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have _ : IsLocallyNoetherian (projectiveLineProduct f) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.fst f (relativeProjectiveLine C.S ↘ C.S))
  have hass : w ∉ Stacks.Divisors.schemeAssociatedPoints Z.subscheme :=
    notMem_schemeAssociatedPoints_of_relativeDimension_eq C f Z k w hrange hwdim
      (hAssociated w)
  obtain ⟨t, ht⟩ := hg ((Z.comap g).subschemeι ξ.1)
  refine ⟨t, ?_⟩
  have hcoeff := cycleAssociatedToComap_apply_eq_length C f g Z k ξ hξ
  rw [ht] at hcoeff
  rw [hcoeff]
  refine congrArg (fun n : ℕ∞ ↦ (n.toNat : ℤ)) ?_
  have hI := notMem_associatedPrimes_idealStalk_of_notMem_schemeAssociatedPoints Z w hass
  rw [hw] at hI
  have hdim := ringKrullDim_quotient_idealStalk_eq_one C f Z k hZ hwdim hrange (hAssociated w)
  rw [hw] at hdim
  have hx := (ringKrullDim_quotient_stalk_comap_eq g Z ((Z.comap g).subschemeι ξ.1)).trans
    (ringKrullDim_quotient_idealStalk_eq (Z.comap g) ξ.1)
  rw [ht, ringKrullDim_stalk_eq_zero_of_mem_genericPoints ξ] at hx
  exact length_quotient_span_sup_eq_sum_minimalPrimes_of_notMem_associatedPrimes t _ hI hdim
    hx.le

/-- **The local content of Stacks Tag 02S5, at the zero section.** Under the hypotheses of the tag,
the coefficient of `[Z₀]_k` at a generic point of the zero fibre of relative dimension `k` is the
sum, over the minimal primes `q` of the stalk `I` of the ideal sheaf of `Z` at the corresponding
point `ξ` of the zero section, of the colength of `(t, q)` in `A = 𝒪_{X ×_S 𝐏¹_S, ξ}` times the
length of `A/I` localised at `q`, where `t` is a local equation of the zero section. -/
theorem exists_localEquation_cycleAssociatedToZeroFiber_apply_eq_sum_minimalPrimes
    (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (Z : (projectiveLineProduct f).IdealSheafData) (k : ℤ)
    (ξ : genericPoints (zeroFiber f Z).subscheme)
    (hξ : relativeDimension C.dimensionFunction f ((zeroFiber f Z).subschemeι ξ.1) = k)
    (hZ : ∀ ζ : Z.subscheme,
      relativeDimension C.dimensionFunction (familyBase f Z) ζ ≤ k + 1)
    (hAssociated : ∀ ζ : Z.subscheme,
      ζ ∈ Stacks.Divisors.schemeAssociatedPoints Z.subscheme →
      ((Z.subschemeι ζ ∉ Set.range (zeroSection f) ∧
          Z.subschemeι ζ ∉ Set.range (infinitySection f)) ∨
        relativeDimension C.dimensionFunction (familyBase f Z) ζ < k)) :
    ∃ t : (projectiveLineProduct f).presheaf.stalk
        (zeroSection f ((zeroFiber f Z).subschemeι ξ.1)),
      (cycleAssociatedToClosedSubscheme C f (zeroFiber f Z).subschemeι k).1
          ((zeroFiber f Z).subschemeι ξ.1) =
        ((∑ᶠ q ∈ {q : PrimeSpectrum ((projectiveLineProduct f).presheaf.stalk
              (zeroSection f ((zeroFiber f Z).subschemeι ξ.1))) |
              q.asIdeal ∈ (AlgebraicGeometry.IdealSheafData.stalk Z
                (zeroSection f ((zeroFiber f Z).subschemeι ξ.1))).minimalPrimes},
            Module.length
                ((projectiveLineProduct f).presheaf.stalk
                  (zeroSection f ((zeroFiber f Z).subschemeι ξ.1)))
                ((projectiveLineProduct f).presheaf.stalk
                    (zeroSection f ((zeroFiber f Z).subschemeι ξ.1)) ⧸
                  (Ideal.span {t} ⊔ q.asIdeal)) *
              Module.length (Localization.AtPrime q.asIdeal)
                (LocalizedModule q.asIdeal.primeCompl
                  ((projectiveLineProduct f).presheaf.stalk
                      (zeroSection f ((zeroFiber f Z).subschemeι ξ.1)) ⧸
                    AlgebraicGeometry.IdealSheafData.stalk Z
                      (zeroSection f ((zeroFiber f Z).subschemeι ξ.1))))).toNat : ℤ) := by
  obtain ⟨w, hw⟩ := exists_subschemeι_eq_zeroSection f Z ξ.1
  exact exists_localEquation_cycleAssociatedToComap_apply_eq_sum_minimalPrimes C f Z k
    (zeroSection f) (exists_span_eq_ker_stalkMap_zeroSection f) ξ hξ hZ hAssociated w hw
    (Or.inl ⟨_, hw.symm⟩)
    ((relativeDimension_familyBase_eq_of_zeroSection C f Z w _ hw).trans hξ)

/-- **The local content of Stacks Tag 02S5, at the infinity section.** The coefficient of
`[Z_∞]_k` at a generic point of the infinity fibre of relative dimension `k` is the same sum
over the minimal primes of the stalk of the ideal sheaf of `Z`, with `t` a local equation of the
infinity section. -/
theorem exists_localEquation_cycleAssociatedToInfinityFiber_apply_eq_sum_minimalPrimes
    (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (Z : (projectiveLineProduct f).IdealSheafData) (k : ℤ)
    (ξ : genericPoints (infinityFiber f Z).subscheme)
    (hξ : relativeDimension C.dimensionFunction f ((infinityFiber f Z).subschemeι ξ.1) = k)
    (hZ : ∀ ζ : Z.subscheme,
      relativeDimension C.dimensionFunction (familyBase f Z) ζ ≤ k + 1)
    (hAssociated : ∀ ζ : Z.subscheme,
      ζ ∈ Stacks.Divisors.schemeAssociatedPoints Z.subscheme →
      ((Z.subschemeι ζ ∉ Set.range (zeroSection f) ∧
          Z.subschemeι ζ ∉ Set.range (infinitySection f)) ∨
        relativeDimension C.dimensionFunction (familyBase f Z) ζ < k)) :
    ∃ t : (projectiveLineProduct f).presheaf.stalk
        (infinitySection f ((infinityFiber f Z).subschemeι ξ.1)),
      (cycleAssociatedToClosedSubscheme C f (infinityFiber f Z).subschemeι k).1
          ((infinityFiber f Z).subschemeι ξ.1) =
        ((∑ᶠ q ∈ {q : PrimeSpectrum ((projectiveLineProduct f).presheaf.stalk
              (infinitySection f ((infinityFiber f Z).subschemeι ξ.1))) |
              q.asIdeal ∈ (AlgebraicGeometry.IdealSheafData.stalk Z
                (infinitySection f ((infinityFiber f Z).subschemeι ξ.1))).minimalPrimes},
            Module.length
                ((projectiveLineProduct f).presheaf.stalk
                  (infinitySection f ((infinityFiber f Z).subschemeι ξ.1)))
                ((projectiveLineProduct f).presheaf.stalk
                    (infinitySection f ((infinityFiber f Z).subschemeι ξ.1)) ⧸
                  (Ideal.span {t} ⊔ q.asIdeal)) *
              Module.length (Localization.AtPrime q.asIdeal)
                (LocalizedModule q.asIdeal.primeCompl
                  ((projectiveLineProduct f).presheaf.stalk
                      (infinitySection f ((infinityFiber f Z).subschemeι ξ.1)) ⧸
                    AlgebraicGeometry.IdealSheafData.stalk Z
                      (infinitySection f ((infinityFiber f Z).subschemeι ξ.1))))).toNat : ℤ) := by
  obtain ⟨w, hw⟩ := exists_subschemeι_eq_infinitySection f Z ξ.1
  exact exists_localEquation_cycleAssociatedToComap_apply_eq_sum_minimalPrimes C f Z k
    (infinitySection f) (exists_span_eq_ker_stalkMap_infinitySection f) ξ hξ hZ hAssociated w hw
    (Or.inr ⟨_, hw.symm⟩)
    ((relativeDimension_familyBase_eq_of_infinitySection C f Z w _ hw).trans hξ)

end Stacks.Chow

end
