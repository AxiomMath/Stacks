module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.CoherentComponentDecomposition
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FibreComparison
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.DimensionDropApplications
public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints

/-!
# Rational equivalence of the two fibres of a coherent sheaf on the projective line

Let `f : X ⟶ S` be locally of finite type over the base scheme of chapter 42 and let `F` be a
coherent sheaf on `X ×_S 𝐏¹_S`. Writing `i₀, i_∞ : X ⟶ X ×_S 𝐏¹_S` for the zero and the
infinity section and `F₀ = i₀^* F`, `F_∞ = i_∞^* F`, Stacks Tag 02S6 asserts that `[F₀]_k` and
`[F_∞]_k` are rationally equivalent `k`-cycles on `X`, under a bound on the delta-dimension of
the support of `F` and of the two fibres and a condition on the associated points of `F`.

The source proves it in two steps. The first is a *claim*: writing `[F]_{k+1} = ∑ nᵢ [Wᵢ]` over
the irreducible components of `Supp(F)` of delta-dimension `k + 1`, one has
`[F₀]_k = ∑ nᵢ [(Wᵢ)₀]_k` and likewise at infinity. That is a coefficientwise computation in the
local ring `A = 𝒪_{X ×_S 𝐏¹_S, ξ}` at a point `ξ = (ξ', 0)` of the zero section: the coefficient
on the left is `length_A(M / tM)` for `M = F_ξ` and `t` a local equation of the zero section, the
coefficient on the right is `∑ length_A(A/(t, 𝔮ᵢ)) · length_{A_{𝔮ᵢ}}(M_{𝔮ᵢ})`, and the two agree
because `M` is a one-dimensional Cohen--Macaulay module on which `t` is a nonzerodivisor. The
second step feeds the resulting locally finite family of integral closed subschemes to Tag 02S4
part (3).

This file carries out both steps. Tag 02S4 part (3) is
`Stacks.Chow.familyFibreDifferencesRationallyEquivalentToZero`, and the claim is
`Stacks.Chow.coherentFibreCycleDecompositionRule`, proved here from the family of components of
`Supp(F)` built in
`StacksFrontier/AlgebraicGeometry/Chow/FibreCycles/CoherentComponentDecomposition.lean`. So the
statement of the tag below has exactly the tag's own three hypotheses.

The coefficient identity the claim needs is the module form of Stacks Tag 02QG, formalized as
`AlgebraicGeometry.length_quotSMulTop_eq_sum_minimal_support`, together with the identification
of the coefficient of `[F₀]_k` at a point of relative dimension `k` with `length_A(M / tM)`.
That identification is the sheaf counterpart of
`Stacks.Chow.cycleAssociatedToComap_apply_eq_length`, and it is
`Stacks.Chow.sheafMultiplicity_pullback_eq_toNat_length_quotSMulTop`, read off the stalk formula
for a pullback of modules.

## Main definitions

* `Stacks.Chow.productBase` — the structure morphism `X ×_S 𝐏¹_S ⟶ S`.
* `Stacks.Chow.zeroFibreModule`, `Stacks.Chow.infinityFibreModule` — the two fibres `F₀` and
  `F_∞` of a module on `X ×_S 𝐏¹_S`.
* `Stacks.Chow.CoherentFibreCycleDecomposition` — the claim in the proof of Tag 02S6, for a
  single coherent sheaf.
* `Stacks.Chow.CoherentFibreCycleDecompositionRule` — the claim as an implication from the
  hypotheses of Tag 02S6.

## Main results

* `Stacks.Chow.isCoherent_zeroFibreModule`, `Stacks.Chow.isCoherent_infinityFibreModule` — the
  two fibres of a coherent sheaf are coherent, so both cycles are defined.
* `Stacks.Chow.coherentFibreCycleDecomposition_of_apply_of_relativeDimension_eq` — the
  decomposition only has to be checked at points of relative dimension `k`.
* `Stacks.Chow.cycleAssociatedToCoherentFibres_rationallyEquivalent_of_decomposition` — the
  cycles of the two fibres of `F` are rationally equivalent, given the decomposition.
* `Stacks.Chow.coherentFibreCycleDecompositionRule` — the claim in the proof of Tag 02S6.
* `Stacks.Chow.cycleAssociatedToCoherentFibres_rationallyEquivalent_of_decompositionRule` — Tag
  02S6, with all three of that tag's hypotheses.

## Implementation notes

Hypothesis (3) is stated here for *associated* points of `F`, as in
`Stacks.Chow.FibreCycleComponentDecompositionRule` for the closed-subscheme case Tag 02S5, and
not for embedded ones. The published form of the tag quantifies (3) over the *embedded*
associated points, but that form is false, and the source's own proof does not use it: it reads
hypothesis (3) off as "`ξ` is not an associated point of `F`". For `S = X = Spec k` with the
zero dimension function, `k = 0` and `F` the structure sheaf of the zero section of `𝐏¹`, the
sheaf `F` has no embedded associated point at all and hypotheses (1) and (2) hold, while
`[F₀]_0 = [Spec k]` and `[F_∞]_0 = 0`, so the conclusion would read `[Spec k] ∼ 0` in
`A₀(Spec k) = ℤ`.

Both halves of `Ass(F)` are load-bearing, at different steps, so neither can be dropped:

* the *non-embedded* half — the maximal points of `Supp(F)` — is what
  `Stacks.Chow.relativeDimension_of_mem_componentGenericPointsThrough` consumes, to know that a
  component generic point of `Supp(F)` through `ξ` is a proper generalization of `ξ`; that is
  the source's step `dim(Supp(M)) = 1`, and it is exactly the half the embedded reading drops;
* the *embedded* half is what
  `Stacks.Chow.sheafMultiplicity_pullback_eq_toNat_finsum_minimal_support` consumes, through
  `Stacks.Chow.length_quotSMulTop_eq_finsum_minimal_support_of_notMem_associatedPrimes`: the
  maximal ideal must not be an associated prime of `M`, which once `dim(Supp(M)) = 1` is known
  says exactly that `ξ` is not an embedded associated point, and it is what makes `t` a
  nonzerodivisor on `M`, the hypothesis Tag 02QG is applied under.

The coherence of the two fibres is Tag 0EBF, `AlgebraicGeometry.isCoherent_pullback`, applied to
a section of the family; it is recorded as a theorem rather than an instance because the local
Noetherianity of `X` it needs is read off the morphism `f`, which the conclusion does not
mention. The statements below therefore take it as an instance argument, and the two theorems
above discharge it.

The coefficient function of a family difference is
`Stacks.Chow.familyFibreDifferenceCoefficient`, already the shape Tag 02S4 part (3) concludes
with, so the second step is an extensionality argument: a `k`-cycle is determined by its
coefficient function, and `Stacks.Chow.RationallyEquivalent` is membership of a difference in
the subgroup `Stacks.Chow.rationalEquivalences`.

## References

* [Stacks Project, Tag 02S6](https://stacks.math.columbia.edu/tag/02S6)
* [Stacks Project, Tag 02S4](https://stacks.math.columbia.edu/tag/02S4)
* [Stacks Project, Tag 02QG](https://stacks.math.columbia.edu/tag/02QG)
* [Stacks Project, Tag 02QW](https://stacks.math.columbia.edu/tag/02QW)
* [Stacks Project, Tag 02QX](https://stacks.math.columbia.edu/tag/02QX)
* [Stacks Project, Tag 0EBF](https://stacks.math.columbia.edu/tag/0EBF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The family of projective lines and the two fibres of a module on it -/

section Fibres

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The structure morphism `X ×_S 𝐏¹_S ⟶ S` of the family of projective lines over `X`. The
relative dimension of a point of the family is measured along it, and restricting it to a closed
subscheme gives `Stacks.Chow.familyBase`. -/
abbrev productBase : projectiveLineProduct f ⟶ S :=
  pullback.fst f (relativeProjectiveLine S ↘ S) ≫ f

/-- The zero fibre `F₀ = i₀^* F` of a module on `X ×_S 𝐏¹_S`: its pullback along the zero
section. -/
abbrev zeroFibreModule (F : (projectiveLineProduct f).Modules) : X.Modules :=
  (Scheme.Modules.pullback (zeroSection f)).obj F

/-- The infinity fibre `F_∞ = i_∞^* F` of a module on `X ×_S 𝐏¹_S`: its pullback along the
infinity section. -/
abbrev infinityFibreModule (F : (projectiveLineProduct f).Modules) : X.Modules :=
  (Scheme.Modules.pullback (infinitySection f)).obj F

end Fibres

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)

/-- **Stacks Tag 0EBF for the zero section.** The zero fibre of a coherent sheaf on
`X ×_S 𝐏¹_S` is a coherent sheaf on `X`, so its cycle is defined. -/
theorem isCoherent_zeroFibreModule (F : (projectiveLineProduct f).Modules) [F.IsCoherent] :
    (zeroFibreModule f F).IsCoherent :=
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  isCoherent_pullback (zeroSection f) F

/-- **Stacks Tag 0EBF for the infinity section.** The infinity fibre of a coherent sheaf on
`X ×_S 𝐏¹_S` is a coherent sheaf on `X`, so its cycle is defined. -/
theorem isCoherent_infinityFibreModule (F : (projectiveLineProduct f).Modules) [F.IsCoherent] :
    (infinityFibreModule f F).IsCoherent :=
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  isCoherent_pullback (infinitySection f) F

variable (F : (projectiveLineProduct f).Modules)
  [(zeroFibreModule f F).IsCoherent] [(infinityFibreModule f F).IsCoherent]

/-! ### The claim in the proof of the tag -/

/-- The claim in the proof of Stacks Tag 02S6: the difference of the cycles of the two fibres of
`F` is, coefficientwise, the difference of the cycles of the two fibres of a locally finite
family of integral closed subschemes of `X ×_S 𝐏¹_S` of relative dimension `k + 1`, each
contained in neither distinguished section.

In the source the family is the family of irreducible components of `Supp(F)` of delta-dimension
`k + 1`, each repeated as often as its multiplicity in `[F]_{k + 1}`; the statement here does
not prescribe the family, only that one exists, which is all Tag 02S4 part (3) consumes. -/
def CoherentFibreCycleDecomposition
    (h₀ : schemeDeltaDimension C ((reducedSupport (zeroFibreModule f F)).subschemeι ≫ f)
      ≤ (k : EInt))
    (hInf : schemeDeltaDimension C ((reducedSupport (infinityFibreModule f F)).subschemeι ≫ f)
      ≤ (k : EInt)) : Prop :=
  ∃ (J : Type u) (W : J → (projectiveLineProduct f).IdealSheafData),
    (∀ j, IsIntegral (W j).subscheme) ∧
    (∀ j, ∀ ξ : genericPoints (W j).subscheme,
      relativeDimension C.dimensionFunction (familyBase f (W j)) ξ.1 = k + 1) ∧
    (∀ j, ¬ Set.range (W j).subschemeι ⊆ Set.range (zeroSection f)) ∧
    (∀ j, ¬ Set.range (W j).subschemeι ⊆ Set.range (infinitySection f)) ∧
    LocallyFinite (fun j ↦ ((W j).support : Set (projectiveLineProduct f))) ∧
    ∀ x : X,
      (cycleAssociatedToCoherentSheaf C f (zeroFibreModule f F) k h₀).1 x -
          (cycleAssociatedToCoherentSheaf C f (infinityFibreModule f F) k hInf).1 x =
        familyFibreDifferenceCoefficient C f k W x

/-- The decomposition only has to be checked at points of relative dimension `k`: everywhere
else both sides vanish term by term.

The coefficient of the cycle of a coherent sheaf in degree `k` vanishes at a point whose
relative dimension is not `k`, by
`Stacks.Chow.cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_ne`, and the coefficient
of the cycle of a closed subscheme likewise, so the family's difference coefficient is a locally
finite sum of zeros. This is what reduces the decomposition from an identity at every point of
`X` to the coefficientwise computation in the local ring at a point of relative dimension `k`
that the source's proof performs. -/
theorem coherentFibreCycleDecomposition_of_apply_of_relativeDimension_eq
    (h₀ : schemeDeltaDimension C ((reducedSupport (zeroFibreModule f F)).subschemeι ≫ f)
      ≤ (k : EInt))
    (hInf : schemeDeltaDimension C ((reducedSupport (infinityFibreModule f F)).subschemeι ≫ f)
      ≤ (k : EInt))
    {J : Type u} (W : J → (projectiveLineProduct f).IdealSheafData)
    (hInt : ∀ j, IsIntegral (W j).subscheme)
    (hDim : ∀ j, ∀ ξ : genericPoints (W j).subscheme,
      relativeDimension C.dimensionFunction (familyBase f (W j)) ξ.1 = k + 1)
    (hz : ∀ j, ¬ Set.range (W j).subschemeι ⊆ Set.range (zeroSection f))
    (hi : ∀ j, ¬ Set.range (W j).subschemeι ⊆ Set.range (infinitySection f))
    (hLoc : LocallyFinite (fun j ↦ ((W j).support : Set (projectiveLineProduct f))))
    (hpt : ∀ x : X, relativeDimension C.dimensionFunction f x = k →
      (cycleAssociatedToCoherentSheaf C f (zeroFibreModule f F) k h₀).1 x -
          (cycleAssociatedToCoherentSheaf C f (infinityFibreModule f F) k hInf).1 x =
        familyFibreDifferenceCoefficient C f k W x) :
    CoherentFibreCycleDecomposition C f k F h₀ hInf := by
  refine ⟨J, W, hInt, hDim, hz, hi, hLoc, fun x ↦ ?_⟩
  by_cases hx : relativeDimension C.dimensionFunction f x = k
  · exact hpt x hx
  · rw [cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_ne C f
      (zeroFibreModule f F) k h₀ hx,
      cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_ne C f
        (infinityFibreModule f F) k hInf hx, sub_zero, familyFibreDifferenceCoefficient]
    refine ((finsum_congr fun j ↦ ?_).trans (finsum_zero (M := ℤ) (α := J))).symm
    rw [cycleAssociatedToClosedSubscheme_apply_eq_zero_of_relativeDimension_ne C f
      (zeroFiber f (W j)).subschemeι k hx,
      cycleAssociatedToClosedSubscheme_apply_eq_zero_of_relativeDimension_ne C f
        (infinityFiber f (W j)).subschemeι k hx, sub_zero]

/-- The claim in the proof of Stacks Tag 02S6, as an implication from that tag's hypotheses: for
every coherent sheaf on `X ×_S 𝐏¹_S` whose support has relative dimension at most `k + 1`, whose
two fibres have delta-dimension at most `k`, and each of whose associated points either misses
both distinguished sections or has relative dimension below `k`, the fibre cycles decompose over
a family of integral closed subschemes.

The hypotheses are those of the tag; in particular the condition is on *associated* points, not
on embedded ones, for the reason recorded in the module documentation. -/
def CoherentFibreCycleDecompositionRule : Prop :=
  ∀ (G : (projectiveLineProduct f).Modules) (_ : G.IsCoherent)
    (_ : (zeroFibreModule f G).IsCoherent) (_ : (infinityFibreModule f G).IsCoherent)
    (h₀ : schemeDeltaDimension C ((reducedSupport (zeroFibreModule f G)).subschemeι ≫ f)
      ≤ (k : EInt))
    (hInf : schemeDeltaDimension C ((reducedSupport (infinityFibreModule f G)).subschemeι ≫ f)
      ≤ (k : EInt)),
    (∀ ξ : projectiveLineProduct f, ξ ∈ SheafOfModules.supp G →
      relativeDimension C.dimensionFunction (productBase f) ξ ≤ k + 1) →
    (∀ ξ : projectiveLineProduct f, ξ ∈ Stacks.Divisors.associatedPoints G →
      ((ξ ∉ Set.range (zeroSection f) ∧ ξ ∉ Set.range (infinitySection f)) ∨
        relativeDimension C.dimensionFunction (productBase f) ξ < k)) →
    CoherentFibreCycleDecomposition C f k G h₀ hInf

/-- **The claim in the proof of Stacks Tag 02S6.** For every coherent sheaf on `X ×_S 𝐏¹_S`
satisfying the hypotheses of the tag, the fibre cycles decompose over the family of the
irreducible components of its support of relative dimension `k + 1`, each repeated as often as
the multiplicity of the sheaf there.

The family is `Stacks.Chow.coherentComponentFamily`, and the coefficient identity at either
section is
`Stacks.Chow.cycleAssociatedToCoherentPullback_apply_eq_finsum_coherentComponentFamily`; the
decomposition only has to be checked at points of relative dimension `k`, which is what reduces
it to that identity. -/
theorem coherentFibreCycleDecompositionRule : CoherentFibreCycleDecompositionRule C f k := by
  intro G _ _ _ h₀ hInf hSupp hAssociated
  have hgf₀ : zeroSection f ≫ pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f = f := by
    rw [← Category.assoc, zeroSection_comp_fst, Category.id_comp]
  have hgfInf :
      infinitySection f ≫ pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f = f := by
    rw [← Category.assoc, infinitySection_comp_fst, Category.id_comp]
  refine coherentFibreCycleDecomposition_of_apply_of_relativeDimension_eq C f k G h₀ hInf
    (coherentComponentFamily C f k G) (isIntegral_coherentComponentFamily C f k G)
    (relativeDimension_coherentComponentFamily C f k G)
    (not_range_coherentComponentFamily_subset_range C f k G (zeroSection f) hgf₀
      fun _ hy => relativeDimension_le_of_schemeDeltaDimension_reducedSupport_le C f k h₀ hy)
    (not_range_coherentComponentFamily_subset_range C f k G (infinitySection f) hgfInf
      fun _ hy => relativeDimension_le_of_schemeDeltaDimension_reducedSupport_le C f k hInf hy)
    (locallyFinite_support_coherentComponentFamily C f k G) fun x hx => ?_
  have hassoc : ∀ (s : X ⟶ projectiveLineProduct f) [IsClosedImmersion s],
      s ≫ pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f = f →
      (∀ ξ ∈ Stacks.Divisors.associatedPoints G, ξ ∉ Set.range s ∨
        relativeDimension C.dimensionFunction (productBase f) ξ < k) →
      s x ∉ Stacks.Divisors.associatedPoints G := fun s _ hs hA h => by
    rcases hA _ h with hn | hlt
    · exact hn ⟨x, rfl⟩
    · rw [relativeDimension_apply_of_section C f s hs x, hx] at hlt
      omega
  have hassoc₀ := hassoc _ hgf₀ fun ξ h => (hAssociated ξ h).imp (·.1) id
  have hassocInf := hassoc _ hgfInf fun ξ h => (hAssociated ξ h).imp (·.2) id
  rw [cycleAssociatedToCoherentPullback_apply_eq_finsum_coherentComponentFamily C f k G
      (zeroSection f) hgf₀ (exists_span_eq_ker_stalkMap_zeroSection f) hSupp h₀ hx hassoc₀,
    cycleAssociatedToCoherentPullback_apply_eq_finsum_coherentComponentFamily C f k G
      (infinitySection f) hgfInf (exists_span_eq_ker_stalkMap_infinitySection f) hSupp hInf hx
      hassocInf, familyFibreDifferenceCoefficient]
  exact (finsum_sub_distrib
    (hasFiniteSupport_cycleAssociatedToComap_coherentComponentFamily C f k G (zeroSection f) x)
    (hasFiniteSupport_cycleAssociatedToComap_coherentComponentFamily C f k G
      (infinitySection f) x)).symm

/-! ### The conclusion of the tag from the claim -/

/-- Given the decomposition of the fibre cycles of `F` over a family of integral closed
subschemes, the cycles of the zero and infinity fibres of `F` are rationally equivalent — the
conclusion of Stacks Tag 02S6.

Tag 02S4 part (3) is
`Stacks.Chow.familyFibreDifferencesRationallyEquivalentToZero`, so the decomposition is the only
input. A `k`-cycle is determined by its coefficient function, so the decomposition identifies
the difference of the two fibre cycles with the cycle that part (3) produces, and rational
equivalence is membership of that difference in the subgroup of cycles rationally equivalent to
zero. -/
theorem cycleAssociatedToCoherentFibres_rationallyEquivalent_of_decomposition
    (h₀ : schemeDeltaDimension C ((reducedSupport (zeroFibreModule f F)).subschemeι ≫ f)
      ≤ (k : EInt))
    (hInf : schemeDeltaDimension C ((reducedSupport (infinityFibreModule f F)).subschemeι ≫ f)
      ≤ (k : EInt))
    (hdec : CoherentFibreCycleDecomposition C f k F h₀ hInf) :
    RationallyEquivalent C f k
      (cycleAssociatedToCoherentSheaf C f (zeroFibreModule f F) k h₀)
      (cycleAssociatedToCoherentSheaf C f (infinityFibreModule f F) k hInf) := by
  obtain ⟨J, W, hInt, hDim, hz, hi, hLoc, hcoeff⟩ := hdec
  obtain ⟨α, hα, hαcoeff⟩ :=
    familyFibreDifferencesRationallyEquivalentToZero C f k W hInt hDim hz hi hLoc
  have heq : cycleAssociatedToCoherentSheaf C f (zeroFibreModule f F) k h₀ -
      cycleAssociatedToCoherentSheaf C f (infinityFibreModule f F) k hInf = α := by
    refine Subtype.ext (DFunLike.ext _ _ fun x ↦ ?_)
    rw [hαcoeff x, ← hcoeff x]
    rfl
  rw [RationallyEquivalent, heq]
  exact hα

/-- **Stacks Tag 02S6.** For a coherent sheaf `F` on `X ×_S 𝐏¹_S` whose support has relative
dimension at most `k + 1`, whose two fibres have delta-dimension at most `k`, and each of whose
associated points either misses both distinguished sections or has relative dimension below `k`,
the cycles `[F₀]_k` and `[F_∞]_k` of the two fibres are rationally equivalent.

The two inputs are `Stacks.Chow.coherentFibreCycleDecompositionRule`, the claim in the source's
proof, and `Stacks.Chow.familyFibreDifferencesRationallyEquivalentToZero`, Tag 02S4 part (3). -/
@[stacks 02S6 "all three hypotheses and the conclusion, with hypothesis (3) quantified over \
every associated point of F, as the source's own \
proof of this lemma uses it ('since ξ is not an associated point of F by assumption (3)'). The \
published statement of the tag quantifies (3) over the embedded associated points only; that \
reading is false, by the counterexample in the module documentation, so it is not what is \
registered here"]
theorem cycleAssociatedToCoherentFibres_rationallyEquivalent_of_decompositionRule
    [F.IsCoherent]
    (hSupp : ∀ ξ : projectiveLineProduct f, ξ ∈ SheafOfModules.supp F →
      relativeDimension C.dimensionFunction (productBase f) ξ ≤ k + 1)
    (h₀ : schemeDeltaDimension C ((reducedSupport (zeroFibreModule f F)).subschemeι ≫ f)
      ≤ (k : EInt))
    (hInf : schemeDeltaDimension C ((reducedSupport (infinityFibreModule f F)).subschemeι ≫ f)
      ≤ (k : EInt))
    (hAssociated : ∀ ξ : projectiveLineProduct f, ξ ∈ Stacks.Divisors.associatedPoints F →
      ((ξ ∉ Set.range (zeroSection f) ∧ ξ ∉ Set.range (infinitySection f)) ∨
        relativeDimension C.dimensionFunction (productBase f) ξ < k)) :
    RationallyEquivalent C f k
      (cycleAssociatedToCoherentSheaf C f (zeroFibreModule f F) k h₀)
      (cycleAssociatedToCoherentSheaf C f (infinityFibreModule f F) k hInf) :=
  cycleAssociatedToCoherentFibres_rationallyEquivalent_of_decomposition C f k F h₀ hInf
    (coherentFibreCycleDecompositionRule C f k F ‹F.IsCoherent›
      ‹(zeroFibreModule f F).IsCoherent› ‹(infinityFibreModule f F).IsCoherent› h₀ hInf hSupp
      hAssociated)

end Stacks.Chow

end
