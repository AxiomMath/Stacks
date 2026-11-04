module

public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToDiagonal.DiagonalLocalMultiplicity
public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToDiagonal.DiagonalSubvarietyProduct
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormulaMultiplicities.TransversalCycleMultiplicity

/-!
# The coefficient of the diagonal pair, point by point

Let `X` be a nonsingular variety over an algebraically closed field `k`, let `V`, `W` be the
reduced closures of two points `a`, `b` of `X`, and write `Δ` for the diagonal of `X` in
`X ×_k X` and `V ×_k W` for the product of the two subvarieties. This file proves the
coefficientwise form of part (2) of [Stacks, Tag 0B0U] for a single pair of subvarieties:

`(Δ · V ×_k W) (Δ(z)) = (V · W) (z)` for every point `z` of `X`,

and that `Δ · V ×_k W` vanishes off the image of the diagonal. Both products are the Section
43.14 product `AlgebraicGeometry.TorFormula.torSubvarietyProductOfBound`, the alternating sum
`∑ᵢ (-1)ⁱ [Torᵢ(𝒪_·, 𝒪_·)]_n` of the cycles of the `Tor` sheaves.

The two coefficients are local invariants of the pair of ideals in the local ring at the point, by
`AlgebraicGeometry.TorFormula.torSubvarietyProductOfBound_apply_eq_localIntersectionMultiplicity`,
and the equality of those invariants is the reduction to the diagonal at a point,
`Stacks.Intersection.Diagonal.localIntersectionMultiplicity_stalk_comap_diagonal_eq`. What this
file adds is the geometry on both sides: the local ideal of the diagonal at `Δ(z)` is the kernel
of the local ring map of `Δ`, the local ideal of `V ×_k W` is the stalk of `pr₁^* I_V ⊔ pr₂^* I_W`,
the intersection `Δ ∩ (V ×_k W)` is `Δ(V ∩ W)`, and `Δ` preserves relative dimension.

## Main results

* `Stacks.Intersection.ReductionToDiagonal.relativeDimension_diagonal` — the diagonal preserves
  relative dimension over the base.
* `Stacks.Intersection.ReductionToDiagonal.closure_diagonal_genericPoint` — the closure of
  `Δ(η)` is the image of the diagonal.
* `Stacks.Intersection.ReductionToDiagonal.mem_closure_productPointAt_iff` — a point lies in
  `V ×_k W` exactly when its two projections lie in `V` and in `W`.
* `Stacks.Intersection.ReductionToDiagonal.torSubvarietyProductOfBound_diagonal_apply` —
  **the equality of coefficients**: `(Δ · V ×_k W)(Δ(z)) = (V · W)(z)`.
* `Stacks.Intersection.ReductionToDiagonal.torSubvarietyProductOfBound_diagonal_apply_eq_zero` —
  `Δ · V ×_k W` vanishes off the image of the diagonal.

## Implementation notes

The delta-dimension bounds that the Section 43.14 product needs are hypotheses, one for each of
the two pairs; in the application they come from proper intersection of the two cycles through
`AlgebraicGeometry.TorFormula.torSupportBound_of_mem_support_of_intersectProperly`. Since the
bound is a proposition the value of the product does not depend on which proof is supplied.

## References

* [Stacks Project, Lemma 43.19.2 (Tag 0B0U)](https://stacks.math.columbia.edu/tag/0B0U)
* [Stacks Project, Tag 0AZR](https://stacks.math.columbia.edu/tag/0AZR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.TorFormula
open Stacks.Chow

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Intersection.ReductionToDiagonal

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-! ### The geometry of the diagonal -/

/-- The diagonal is a morphism over the base: composed with the structure morphism of `X ×_Y X`
it is the structure morphism of `X`. -/
theorem diagonal_comp_fst_comp {Y : Scheme.{u}} (f : X ⟶ Y) :
    pullback.diagonal f ≫ (pullback.fst f f ≫ f) = f := by
  rw [← Category.assoc, pullback.diagonal_fst, Category.id_comp]

/-- **The diagonal preserves relative dimension.** A closed immersion does not change the
relative dimension of a point over the base, and the diagonal composed with the structure
morphism of `X ×_Y X` is the structure morphism of `X`. -/
theorem relativeDimension_diagonal {Y : Scheme.{u}} (δ : DimensionFunction Y) (f : X ⟶ Y)
    [IsSeparated f] (z : X) :
    relativeDimension δ (pullback.fst f f ≫ f) ((pullback.diagonal f).base z) =
      relativeDimension δ f z := by
  have : IsClosedImmersion (pullback.diagonal f) := IsSeparated.isClosedImmersion_diagonal
  rw [← relativeDimension_comp_closedImmersion δ (pullback.diagonal f)
    (pullback.fst f f ≫ f) z, diagonal_comp_fst_comp f]

/-- **The closure of `Δ(η)` is the image of the diagonal.** For `X` integral with generic point
`η` and `f` separated, the diagonal is a closed embedding, so the closure of the image of the
generic point is the whole image. -/
theorem closure_diagonal_genericPoint {Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f]
    [IsIntegral X] :
    closure ({(pullback.diagonal f).base (genericPoint X)} :
        Set (pullback f f : Scheme.{u})) =
      Set.range (pullback.diagonal f).base := by
  have : IsClosedImmersion (pullback.diagonal f) := IsSeparated.isClosedImmersion_diagonal
  have h := (genericPoint_spec X).image (pullback.diagonal f).continuous
  rw [Set.image_univ] at h
  exact h.trans (pullback.diagonal f).isClosedEmbedding.isClosed_range.closure_eq

/-- Every point of the diagonal lies in the closure of `Δ(η)`. -/
theorem mem_closure_diagonal_genericPoint {Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f]
    [IsIntegral X] (z : X) :
    (pullback.diagonal f).base z ∈
      closure ({(pullback.diagonal f).base (genericPoint X)} :
        Set (pullback f f : Scheme.{u})) := by
  rw [closure_diagonal_genericPoint f]
  exact Set.mem_range_self z

/-! ### The support of the product of two point closures -/

/-- **A point lies in the product of two reduced point closures exactly when its two projections
lie in them.** -/
theorem mem_closure_productPointAt_iff [IsAlgClosed k] (f : X ⟶ Spec (CommRingCat.of k))
    [IsVariety k f] (a b : X) (p : (pullback f f : Scheme.{u})) :
    p ∈ closure ({productPointAt f a b} : Set (pullback f f : Scheme.{u})) ↔
      (pullback.fst f f).base p ∈ closure ({a} : Set X) ∧
        (pullback.snd f f).base p ∈ closure ({b} : Set X) := by
  rw [productPointAt_eq_genericPointOf, ← support_eq_closure_genericPointOf,
    Scheme.IdealSheafData.support_sup, Closeds.coe_inf,
    Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_comap,
    Closeds.coe_preimage, Closeds.coe_preimage, coe_support_integralComponentAt,
    coe_support_integralComponentAt]
  exact Iff.rfl

/-- The diagonal image of `z` lies in the product of two point closures exactly when `z` lies in
both closures. -/
private theorem diagonal_mem_closure_productPointAt_iff [IsAlgClosed k]
    (f : X ⟶ Spec (CommRingCat.of k)) [IsVariety k f] (a b z : X) :
    (pullback.diagonal f).base z ∈
        closure ({productPointAt f a b} : Set (pullback f f : Scheme.{u})) ↔
      z ∈ closure ({a} : Set X) ∩ closure ({b} : Set X) := by
  rw [mem_closure_productPointAt_iff, Diagonal.pullback_fst_diagonal_apply,
    Diagonal.pullback_snd_diagonal_apply]
  exact Iff.rfl

/-! ### The equality of coefficients -/

/-- **The coefficientwise form of part (2) of [Stacks, Tag 0B0U] for one pair of closed
subvarieties.** Let `X` be a nonsingular variety over an algebraically closed field, let `V`, `W`
be the reduced closures of two points `a`, `b` of `X`, and let `Δ` be the diagonal of `X` inside
`X ×_k X`. Then for every point `z` of `X` the coefficient of the Section 43.14 product
`Δ · V ×_k W` at `Δ(z)` equals the coefficient of `V · W` at `z`.

Both coefficients are Tor-formula local intersection multiplicities of two ideals in the local
ring at the point, and the two multiplicities agree by the reduction to the diagonal,
`Stacks.Intersection.Diagonal.localIntersectionMultiplicity_stalk_comap_diagonal_eq`. -/
theorem torSubvarietyProductOfBound_diagonal_apply [IsAlgClosed k]
    (f : X ⟶ Spec (CommRingCat.of k)) [IsVariety k f] [IsLocallyNoetherian X]
    [IsLocallyNoetherian (pullback f f : Scheme.{u})] (hX : IsRegular X)
    (hP : IsRegular (pullback f f : Scheme.{u})) (n : ℤ) (a b : X)
    (dX : ℕ) (hdX : topologicalKrullDim X ≤ (dX : WithBot ℕ∞))
    (dP : ℕ) (hdP : topologicalKrullDim (pullback f f : Scheme.{u}) ≤ (dP : WithBot ℕ∞))
    (h : TorSupportBound (fieldChowSituation k) f hX n a b)
    (h' : TorSupportBound (fieldChowSituation k) (pullback.fst f f ≫ f) hP n
      ((pullback.diagonal f).base (genericPoint X)) (productPointAt f a b))
    (z : X) :
    torSubvarietyProductOfBound (fieldChowSituation k) (pullback.fst f f ≫ f) hP n h'
        ((pullback.diagonal f).base z) =
      torSubvarietyProductOfBound (fieldChowSituation k) f hX n h z := by
  by_cases hdim : relativeDimension (fieldChowSituation k).dimensionFunction f z = n
  · by_cases hmem : z ∈ closure ({a} : Set X) ∩ closure ({b} : Set X)
    · have hdimP : relativeDimension (fieldChowSituation k).dimensionFunction
          (pullback.fst f f ≫ f) ((pullback.diagonal f).base z) = n := by
        rw [relativeDimension_diagonal]; exact hdim
      have hL := torSubvarietyProductOfBound_apply_eq_localIntersectionMultiplicity
        (fieldChowSituation k) (pullback.fst f f ≫ f) hP n h' dP hdP hdimP
        (mem_closure_diagonal_genericPoint f z)
        ((diagonal_mem_closure_productPointAt_iff f a b z).2 hmem)
      have hR := torSubvarietyProductOfBound_apply_eq_localIntersectionMultiplicity
        (fieldChowSituation k) f hX n h dX hdX hdim hmem.1 hmem.2
      rw [localIdealAt, localIdealAt, localIdealAt_diagonal_eq_ker_stalkMap,
        integralComponentAt_productPointAt] at hL
      have hkey := Diagonal.localIntersectionMultiplicity_stalk_comap_diagonal_eq k f
        (integralComponentAt a) (integralComponentAt b) z
      have hQ : ((torSubvarietyProductOfBound (fieldChowSituation k) (pullback.fst f f ≫ f) hP n h'
            ((pullback.diagonal f).base z) : ℤ) : ℚ) =
          ((torSubvarietyProductOfBound (fieldChowSituation k) f hX n h z : ℤ) : ℚ) := by
        rw [hL, hR]; exact hkey
      exact_mod_cast hQ
    · rw [torSubvarietyProductOfBound_apply_eq_zero_of_notMem_inter
        (fieldChowSituation k) f hX n h dX hdX hmem]
      refine torSubvarietyProductOfBound_apply_eq_zero_of_notMem_inter
        (fieldChowSituation k) (pullback.fst f f ≫ f) hP n h' dP hdP ?_
      exact fun hc => hmem ((diagonal_mem_closure_productPointAt_iff f a b z).1 hc.2)
  · rw [torSubvarietyProductOfBound_apply_eq_zero_of_relativeDimension_ne
      (fieldChowSituation k) f hX n h dX hdX hdim]
    refine torSubvarietyProductOfBound_apply_eq_zero_of_relativeDimension_ne
      (fieldChowSituation k) (pullback.fst f f ≫ f) hP n h' dP hdP ?_
    rwa [relativeDimension_diagonal]

/-- **A Section 43.14 product with the diagonal is carried by the diagonal.** Off the image of
`Δ` every coefficient of `Δ · Z` vanishes, for `Z` the reduced closure of any point, because `Δ`
is the reduced closure of `Δ(η)` and the product is supported on the intersection of the two
factors. -/
theorem torSubvarietyProductOfBound_diagonal_apply_eq_zero
    (f : X ⟶ Spec (CommRingCat.of k)) [IsVariety k f]
    [IsLocallyNoetherian (pullback f f : Scheme.{u})]
    (hP : IsRegular (pullback f f : Scheme.{u})) (n : ℤ) (w : (pullback f f : Scheme.{u}))
    (dP : ℕ) (hdP : topologicalKrullDim (pullback f f : Scheme.{u}) ≤ (dP : WithBot ℕ∞))
    (h' : TorSupportBound (fieldChowSituation k) (pullback.fst f f ≫ f) hP n
      ((pullback.diagonal f).base (genericPoint X)) w)
    {p : (pullback f f : Scheme.{u})} (hp : p ∉ Set.range (pullback.diagonal f).base) :
    torSubvarietyProductOfBound (fieldChowSituation k) (pullback.fst f f ≫ f) hP n h' p = 0 := by
  refine torSubvarietyProductOfBound_apply_eq_zero_of_notMem_inter
    (fieldChowSituation k) (pullback.fst f f ≫ f) hP n h' dP hdP ?_
  intro hc
  exact hp (by rw [← closure_diagonal_genericPoint f]; exact hc.1)

end Stacks.Intersection.ReductionToDiagonal

end
