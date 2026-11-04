module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.RationalEquivalenceCoproduct
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.RationalEquivalenceReduction

/-!
# Vanishing in the wide dimension layer along a decomposition into open and closed pieces

Let `(S, δ)` be a base situation with a dimension function and let `V` be a quasi-compact scheme
locally of finite type over `S`, decomposed into open and closed pieces `V = ∐_j O_j`. This file
shows that the class in the wide dimension layer `K₀(Coh_{≤k+1}(V)/Coh_{≤k-1}(V))` of a
`k`-cycle on `V` vanishes as soon as the class of its restriction to each piece vanishes.

It follows that on a quasi-compact scheme `X` locally of finite type over `S` the class in the
wide dimension layer of a `k`-cycle rationally equivalent to zero vanishes, provided the class of
the principal divisor of a rational function vanishes on every quasi-compact integral scheme of
delta-dimension `k + 1` over `S`.

## Main definitions

* `Stacks.Chow.cycleCoeffHom` — the coefficient of a `k`-cycle at a point of the scheme, as a
  homomorphism `Z_k(X) ⟶ ℤ`.

## Main results

* `Stacks.Chow.exists_finset_mem_of_isClopenDecomposition` — on a quasi-compact scheme only
  finitely many pieces of a decomposition into open and closed subschemes are nonempty.
* `Stacks.Chow.cycle_eq_sum_properPushforward_opensRestrict` — on a quasi-compact scheme a cycle
  is the finite sum of the pushforwards of its restrictions to the pieces.
* `Stacks.Chow.cycleDimensionLayerWideHom_eq_zero_of_isClopenDecomposition` — the vanishing
  statement above.
* `Stacks.Chow.cycleDimensionLayerWideHom_eq_zero_of_isClopenDecomposition_of_properPushforward` —
  the same with each piece identified with a scheme of its own.
* `Stacks.Chow.cycleDimensionLayerWideHom_eq_zero_of_isRationallyEquivalentToZero` and
  `Stacks.Chow.cycleDimensionLayerWideHom_eq_zero_of_mem_rationalEquivalences` — a cycle
  rationally equivalent to zero on a quasi-compact `X` has vanishing class in the wide layer,
  provided the class of the principal divisor of a rational function vanishes on a quasi-compact
  integral scheme of delta-dimension `k + 1`.

## References

* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 02S9](https://stacks.math.columbia.edu/tag/02S9)
* [Stacks Project, Tag 0FDR](https://stacks.math.columbia.edu/tag/0FDR)
* [Stacks Project, Tag 0FDS](https://stacks.math.columbia.edu/tag/0FDS)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {V X : Scheme.{u}}

/-! ### The coefficient of a cycle as a homomorphism -/

/-- The coefficient of a `k`-cycle at a point of the scheme, as a homomorphism `Z_k(X) ⟶ ℤ`. -/
def cycleCoeffHom (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)
    (x : X) : CycleGroup C f k →+ ℤ where
  toFun c := c.1 x
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The value of `Stacks.Chow.cycleCoeffHom` on a cycle `c` at `x` is the coefficient of `c`
at `x`. -/
@[simp]
theorem cycleCoeffHom_apply (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)
    (x : X) (c : CycleGroup C f k) : cycleCoeffHom C f k x c = c.1 x :=
  rfl

/-! ### A decomposition of a quasi-compact scheme has finitely many nonempty pieces -/

/-- Only finitely many pieces of a decomposition of a quasi-compact scheme into open and closed
subschemes are nonempty. -/
theorem exists_finset_mem_of_isClopenDecomposition {J : Type u} {O : J → V.Opens}
    (hO : IsClopenDecomposition O) [CompactSpace V] :
    ∃ t : Finset J, ∀ j, (O j : Set V).Nonempty → j ∈ t := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun j ↦ (O j : Set V))
    (fun j ↦ (O j).2) fun x _ ↦ Set.mem_iUnion.2 (hO.exists_mem x)
  refine ⟨t, fun j ⟨x, hx⟩ ↦ ?_⟩
  obtain ⟨i, hit, hxi⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact hO.eq_of_mem hxi hx ▸ hit

/-- On a quasi-compact scheme a cycle is the finite sum of the pushforwards of its restrictions
to the pieces of a decomposition into open and closed subschemes, the sum running over any finite
set of indices containing every index of a nonempty piece. -/
theorem cycle_eq_sum_properPushforward_opensRestrict (C : ChowSituation.{u}) (sV : V ⟶ C.S)
    [LocallyOfFiniteType sV] {J : Type u} {O : J → V.Opens} (hO : IsClopenDecomposition O)
    [∀ j, IsProper (O j).ι] (k : ℤ) (c : CycleGroup C sV k) {t : Finset J}
    (ht : ∀ j, (O j : Set V).Nonempty → j ∈ t) :
    c = ∑ j ∈ t, properPushforwardHom C ((O j).ι ≫ sV) sV (O j).ι rfl k
      (cycleGroupOpensRestrict C sV (O j) k c) := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
  have hsupp : Function.support (fun j ↦ (properPushforward C ((O j).ι ≫ sV) sV (O j).ι rfl k
      (cycleGroupOpensRestrict C sV (O j) k c)).1 x) ⊆ (t : Set J) := by
    intro j hj
    obtain ⟨y, -⟩ := support_properPushforward_subset C ((O j).ι ≫ sV) sV (O j).ι rfl k _ hj
    exact ht j ⟨y.1, y.2⟩
  rw [cycle_eq_finsum_properPushforward_opensRestrict C sV hO k c x,
    finsum_eq_sum_of_support_subset _ hsupp]
  exact (map_sum (cycleCoeffHom C sV k x)
    (fun j ↦ properPushforwardHom C ((O j).ι ≫ sV) sV (O j).ι rfl k
      (cycleGroupOpensRestrict C sV (O j) k c)) t).symm

/-! ### Vanishing in the wide layer along a decomposition -/

/-- A quasi-compact scheme locally of finite type over the base is Noetherian. -/
private theorem isNoetherian_of_locallyOfFiniteType (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] [CompactSpace X] : IsNoetherian X :=
  { __ := LocallyOfFiniteType.isLocallyNoetherian f }

/-- The class in the wide dimension layer of a cycle on a quasi-compact scheme vanishes as soon as
the class of its restriction to every piece of a decomposition into open and closed subschemes
vanishes. -/
theorem cycleDimensionLayerWideHom_eq_zero_of_isClopenDecomposition (C : ChowSituation.{u})
    (sV : V ⟶ C.S) [LocallyOfFiniteType sV] [CompactSpace V] (k : ℤ) {J : Type u}
    {O : J → V.Opens} (hO : IsClopenDecomposition O) (c : CycleGroup C sV k)
    (hvan : ∀ j, cycleDimensionLayerWideHom C ((O j).ι ≫ sV) k
      (cycleGroupOpensRestrict C sV (O j) k c) = 0) :
    cycleDimensionLayerWideHom C sV k c = 0 := by
  have := isNoetherian_of_locallyOfFiniteType C sV
  have hprop : ∀ j, IsProper (O j).ι := hO.isProper_ι
  obtain ⟨t, ht⟩ := exists_finset_mem_of_isClopenDecomposition hO
  rw [cycle_eq_sum_properPushforward_opensRestrict C sV hO k c ht, map_sum]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  have := hO.isClosedImmersion_ι j
  exact cycleDimensionLayerWideHom_eq_zero_of_properPushforwardHom_eq C ((O j).ι ≫ sV) sV
    (O j).ι rfl k rfl (hvan j)

/-- The class in the wide dimension layer of a cycle `c` on a quasi-compact scheme vanishes,
given schemes `Z j` with isomorphisms `e j : Z j ⟶ O j` onto the pieces of a decomposition into
open and closed subschemes, cycles `a j` on `Z j` whose classes vanish, and an identification of
the restriction of `c` to `O j` with the pushforward of `a j`. -/
theorem cycleDimensionLayerWideHom_eq_zero_of_isClopenDecomposition_of_properPushforward
    (C : ChowSituation.{u}) (sV : V ⟶ C.S) [LocallyOfFiniteType sV] [CompactSpace V] (k : ℤ)
    {J : Type u} {O : J → V.Opens} (hO : IsClopenDecomposition O) {Z : J → Scheme.{u}}
    {sZ : ∀ j, Z j ⟶ C.S} [∀ j, LocallyOfFiniteType (sZ j)]
    (e : ∀ j, Z j ⟶ (O j : Scheme.{u})) [∀ j, IsIso (e j)]
    (he : ∀ j, e j ≫ (O j).ι ≫ sV = sZ j) (a : ∀ j, CycleGroup C (sZ j) k)
    (c : CycleGroup C sV k)
    (hres : ∀ j, cycleGroupOpensRestrict C sV (O j) k c =
      properPushforward C (sZ j) ((O j).ι ≫ sV) (e j) (he j) k (a j))
    (hvan : ∀ j, cycleDimensionLayerWideHom C (sZ j) k (a j) = 0) :
    cycleDimensionLayerWideHom C sV k c = 0 := by
  refine cycleDimensionLayerWideHom_eq_zero_of_isClopenDecomposition C sV k hO c fun j ↦ ?_
  have := hO.isClosedImmersion_ι j
  have : CompactSpace (O j : Scheme.{u}) := QuasiCompact.compactSpace_of_compactSpace (O j).ι
  have := isNoetherian_of_locallyOfFiniteType C ((O j).ι ≫ sV)
  exact cycleDimensionLayerWideHom_eq_zero_of_properPushforwardHom_eq C (sZ j)
    ((O j).ι ≫ sV) (e j) (he j) k (hres j).symm (hvan j)

/-! ### Cycles rationally equivalent to zero -/

/-- On a quasi-compact scheme `X` locally of finite type over the base, a `k`-cycle rationally
equivalent to zero has vanishing class in the wide dimension layer
`K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))`, granted the hypothesis `hint`: for a quasi-compact integral
scheme of delta-dimension `k + 1` over the base and a unit `g` of its rational functions, the
class of a `k`-cycle with coefficients the principal divisor `div(g)` vanishes. -/
theorem cycleDimensionLayerWideHom_eq_zero_of_isRationallyEquivalentToZero (C : ChowSituation.{u})
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [CompactSpace X] (k : ℤ)
    (hint : ∀ (Y : Scheme.{u}) (q : Y ⟶ C.S) [LocallyOfFiniteType q] [CompactSpace Y]
      [IsIntegral Y] [IsLocallyNoetherian Y],
      schemeDeltaDimension C q = ((k + 1 : ℤ) : EInt) → ∀ (g : (rationalFunctions Y)ˣ)
        (b : CycleGroup C q k),
        b.1 = principalCycle Y
          ((rationalFunctionsEquivFunctionField Y).1 (g : rationalFunctions Y)) →
        cycleDimensionLayerWideHom C q k b = 0)
    {α : CycleGroup C sX k} (hα : IsRationallyEquivalentToZero C sX k α) :
    cycleDimensionLayerWideHom C sX k α = 0 := by
  obtain ⟨J, W, hW, hDim, hLocal, g, hg⟩ := hα
  have := isNoetherian_of_locallyOfFiniteType C sX
  have hfin : IsFinite (Sigma.desc fun j ↦ (W j).subschemeι) :=
    isFinite_sigmaDesc_of_locallyFinite _
      (by simpa only [Scheme.IdealSheafData.range_subschemeι] using hLocal)
  have he : ∀ j, (Sigma.ι (fun j ↦ (W j).subscheme) j).isoOpensRange.hom ≫
      (Sigma.ι (fun j ↦ (W j).subscheme) j).opensRange.ι ≫
        (Sigma.desc fun j ↦ (W j).subschemeι) = (W j).subschemeι := fun j ↦ by
    rw [← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, Sigma.ι_desc]
  obtain ⟨c, hc, hres⟩ := exists_properPushforward_eq_of_isClopenDecomposition C sX
    (Sigma.desc fun j ↦ (W j).subschemeι) k
    (isClopenDecomposition_opensRange_sigmaι fun j ↦ (W j).subscheme)
    (fun j ↦ (W j).subschemeι)
    (fun j ↦ (Sigma.ι (fun j ↦ (W j).subscheme) j).isoOpensRange.hom) he
    (fun j ↦ subschemePrincipalDivisorCycle C sX k (W j) (hW j) (hDim j) (g j))
    (α := α) fun x ↦ by
      rw [hg x]
      exact finsum_congr fun j ↦ by
        rw [← properPushforward_subschemePrincipalDivisorCycle C sX k (W j) (hW j) (hDim j) (g j)]
  have := QuasiCompact.compactSpace_of_compactSpace (Sigma.desc fun j ↦ (W j).subschemeι)
  refine cycleDimensionLayerWideHom_eq_zero_of_properPushforwardHom_eq C _ sX
    (Sigma.desc fun j ↦ (W j).subschemeι) rfl k hc ?_
  refine cycleDimensionLayerWideHom_eq_zero_of_isClopenDecomposition_of_properPushforward C _ k
    (isClopenDecomposition_opensRange_sigmaι fun j ↦ (W j).subscheme)
    (fun j ↦ (Sigma.ι (fun j ↦ (W j).subscheme) j).isoOpensRange.hom)
    (fun j ↦ by rw [← he j, Category.assoc, Category.assoc])
    (fun j ↦ subschemePrincipalDivisorCycle C sX k (W j) (hW j) (hDim j) (g j)) c hres fun j ↦ ?_
  have := hW j
  have : CompactSpace (W j).subscheme := QuasiCompact.compactSpace_of_compactSpace (W j).subschemeι
  have := isNoetherian_of_locallyOfFiniteType C ((W j).subschemeι ≫ sX)
  exact hint (W j).subscheme ((W j).subschemeι ≫ sX) (hDim j) _ _ rfl

/-- Granted the hypothesis `hint` on quasi-compact integral schemes of delta-dimension `k + 1`,
the composite `Z_k(X) → K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))` vanishes on the subgroup of cycles
rationally equivalent to zero. -/
theorem cycleDimensionLayerWideHom_eq_zero_of_mem_rationalEquivalences (C : ChowSituation.{u})
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [CompactSpace X] (k : ℤ)
    (hint : ∀ (Y : Scheme.{u}) (q : Y ⟶ C.S) [LocallyOfFiniteType q] [CompactSpace Y]
      [IsIntegral Y] [IsLocallyNoetherian Y],
      schemeDeltaDimension C q = ((k + 1 : ℤ) : EInt) → ∀ (g : (rationalFunctions Y)ˣ)
        (b : CycleGroup C q k),
        b.1 = principalCycle Y
          ((rationalFunctionsEquivFunctionField Y).1 (g : rationalFunctions Y)) →
        cycleDimensionLayerWideHom C q k b = 0)
    (α : CycleGroup C sX k) (hα : α ∈ rationalEquivalences C sX k) :
    cycleDimensionLayerWideHom C sX k α = 0 :=
  cycleDimensionLayerWideHom_eq_zero_of_isRationallyEquivalentToZero C sX k hint hα

end Stacks.Chow

end
