module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.RationalEquivalenceFinsum
public import StacksFrontier.AlgebraicGeometry.Chow.DimensionFunction.PrincipalDivisorFamily
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction
public import StacksFrontier.AlgebraicGeometry.Limits.SigmaFiniteHom
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.Coproduct

/-!
# A cycle rationally equivalent to zero as a pushforward from a disjoint union

Let `(S, δ)` be a base situation with a dimension function and let `X` be a scheme locally of
finite type over `S`. A `k`-cycle `α` on `X` rationally equivalent to zero is, by
[Stacks, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW), a locally finite sum

  `α = ∑_j (i_j)_* div(f_j)`

over a locally finite family of integral closed subschemes `i_j : W_j ⟶ X` of delta-dimension
`k + 1` carrying nonzero rational functions `f_j`. The first step of the proof of
[Stacks, Tag 0FDS](https://stacks.math.columbia.edu/tag/0FDS) replaces this family by the single
finite morphism `π = ⨿ i_j : ⨿ W_j ⟶ X` and the single cycle `∑_j div(f_j)` on `⨿ W_j`. This file
carries out that replacement.

## Main definitions

* `Stacks.Chow.subschemePrincipalDivisorCycle` — the principal divisor of a nonzero rational
  function on an integral closed subscheme of delta-dimension `k + 1`, as a `k`-cycle on that
  subscheme.

## Main results

* `Stacks.Chow.exists_properPushforward_eq_of_isClopenDecomposition` — given a proper
  `π : V ⟶ X`, a decomposition of `V` into open and closed pieces `O j`, and identifications of
  those pieces with schemes `Z j` mapping to `X`, a cycle on `X` which is the locally finite sum of
  the pushforwards of cycles `a j` on the `Z j` is the pushforward along `π` of a single cycle on
  `V`, namely the one restricting to `a j` on `O j`.
* `Stacks.Chow.properPushforward_subschemePrincipalDivisorCycle` — the pushforward of
  `Stacks.Chow.subschemePrincipalDivisorCycle` along the inclusion of the subscheme is
  `Stacks.Chow.principalDivisorPushforward`.
* `Stacks.Chow.exists_isFinite_properPushforward_eq_of_isRationallyEquivalentToZero` — a
  `k`-cycle rationally equivalent to zero is the proper pushforward, along a finite morphism, of a
  `k`-cycle on the disjoint union of the integral closed subschemes of Tag 02RW.

## References

* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
* [Stacks Project, Tag 02R5](https://stacks.math.columbia.edu/tag/02R5)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 0FDS](https://stacks.math.columbia.edu/tag/0FDS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-! ### Assembling a cycle on a scheme decomposed into open and closed pieces -/

/-- Let `π : V ⟶ X` be proper, let `O` be a decomposition of `V` into open and closed subschemes,
and identify each piece `O j` with a scheme `Z j` carrying a proper morphism `ι j` to `X`,
compatibly with `π`. Then a `k`-cycle `α` on `X` whose coefficients are the locally finite sum of
the coefficients of the pushforwards along the `ι j` of `k`-cycles `a j` on the `Z j` is itself
the pushforward along `π` of a single `k`-cycle on `V` — the one whose restriction to the piece
`O j` is `a j`. -/
theorem exists_properPushforward_eq_of_isClopenDecomposition {V : Scheme.{u}} (π : V ⟶ X)
    [IsProper π] (k : ℤ) {J : Type u} {O : J → V.Opens} (hO : IsClopenDecomposition O)
    {Z : J → Scheme.{u}} (ι : ∀ j, Z j ⟶ X) [∀ j, IsProper (ι j)]
    (e : ∀ j, Z j ⟶ (O j : Scheme.{u})) [∀ j, IsIso (e j)]
    (he : ∀ j, e j ≫ (O j).ι ≫ π = ι j) (a : ∀ j, CycleGroup C (ι j ≫ sX) k)
    {α : CycleGroup C sX k}
    (hα : ∀ x : X, α.1 x =
      ∑ᶠ j : J, (properPushforward C (ι j ≫ sX) sX (ι j) rfl k (a j)).1 x) :
    ∃ c : CycleGroup C (π ≫ sX) k,
      properPushforward C (π ≫ sX) sX π rfl k c = α ∧
        ∀ j, cycleGroupOpensRestrict C (π ≫ sX) (O j) k c =
          properPushforward C (ι j ≫ sX) ((O j).ι ≫ π ≫ sX) (e j)
            (by simp [← he j]) k (a j) := by
  have hproper : ∀ j, IsProper (O j).ι := hO.isProper_ι
  set b : ∀ j, CycleGroup C ((O j).ι ≫ π ≫ sX) k := fun j ↦
    properPushforward C (ι j ≫ sX) ((O j).ι ≫ π ≫ sX) (e j)
      (by simp [← he j]) k (a j) with hb
  set c := (cycleGroupClopenEquiv C (π ≫ sX) hO k).symm b
  have hres : ∀ j, cycleGroupOpensRestrict C (π ≫ sX) (O j) k c = b j := fun j ↦
    congrFun ((cycleGroupClopenEquiv C (π ≫ sX) hO k).apply_symm_apply b) j
  refine ⟨c, ?_, hres⟩
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
  have hsum : ∀ z : V, c.1 z = ∑ᶠ j : J,
      (properPushforward C ((O j).ι ≫ π ≫ sX) (π ≫ sX) (O j).ι rfl k (b j)).1 z := fun z ↦ by
    rw [cycle_eq_finsum_properPushforward_opensRestrict C (π ≫ sX) hO k c z]
    exact finsum_congr fun j ↦ by rw [hres j]
  have hsupp : ∀ j, Function.support
      (properPushforward C ((O j).ι ≫ π ≫ sX) (π ≫ sX) (O j).ι rfl k (b j)).1 ⊆
        Set.range (O j).ι :=
    fun j ↦ support_properPushforward_subset C ((O j).ι ≫ π ≫ sX) (π ≫ sX) (O j).ι rfl k (b j)
  have hpush : (properPushforward C (π ≫ sX) sX π rfl k c).1 x = ∑ᶠ j : J,
      (properPushforward C (π ≫ sX) sX π rfl k
        (properPushforward C ((O j).ι ≫ π ≫ sX) (π ≫ sX) (O j).ι rfl k (b j))).1 x :=
    algebraicCycle_map_finsum_apply π _ _ (fun j ↦ Set.range (O j).ι)
      hO.locallyFinite_range_ι
      (fun j ↦ (properPushforward C ((O j).ι ≫ π ≫ sX) (π ≫ sX) (O j).ι rfl k (b j)).1)
      hsupp c.1 hsum x
  rw [hpush, hα x]
  refine finsum_congr fun j ↦ ?_
  rw [properPushforward_properPushforward C ((O j).ι ≫ π ≫ sX) (π ≫ sX) sX (O j).ι π rfl rfl k,
    hb, properPushforward_properPushforward C (ι j ≫ sX) ((O j).ι ≫ π ≫ sX) sX (e j)
      ((O j).ι ≫ π) (by simp [← he j]) rfl k,
    properPushforward_congr C (ι j ≫ sX) sX (e j ≫ (O j).ι ≫ π) (ι j) (he j)
      (by rw [he j]) rfl k]

/-! ### The principal divisor of a rational function as a cycle on the subscheme -/

/-- The principal divisor of a nonzero rational function on an integral closed subscheme `V ⊆ X`
of delta-dimension `k + 1`, as a `k`-cycle on `V`. -/
def subschemePrincipalDivisorCycle (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (k : ℤ) (V : X.IdealSheafData) (hV : IsIntegral V.subscheme)
    (hDim : schemeDeltaDimension C (V.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (g : (rationalFunctions V.subscheme)ˣ) : CycleGroup C (V.subschemeι ≫ p) k :=
  letI := hV
  letI : IsLocallyNoetherian V.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (V.subschemeι ≫ p)
  ⟨principalCycle V.subscheme
      ((rationalFunctionsEquivFunctionField V.subscheme).1 (g : rationalFunctions V.subscheme)),
    by
      simpa only [add_sub_cancel_right] using
        principalCycle_mem_cyclesOfDimension C (V.subschemeι ≫ p) hDim _⟩

/-- The pushforward of `Stacks.Chow.subschemePrincipalDivisorCycle` along the inclusion of the
closed subscheme is `Stacks.Chow.principalDivisorPushforward`. -/
theorem properPushforward_subschemePrincipalDivisorCycle (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) (V : X.IdealSheafData)
    (hV : IsIntegral V.subscheme)
    (hDim : schemeDeltaDimension C (V.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (g : (rationalFunctions V.subscheme)ˣ) :
    (properPushforward C (V.subschemeι ≫ p) p V.subschemeι rfl k
        (subschemePrincipalDivisorCycle C p k V hV hDim g)).1 =
      principalDivisorPushforward C p V hV g :=
  rfl

/-! ### The first step of the proof of Stacks 0FDS -/

/-- A `k`-cycle `α` on `X` rationally equivalent to zero is the proper pushforward, along a
finite morphism `π : V ⟶ X`, of a single `k`-cycle on `V`. Here `V` is the disjoint union `⨿ W_j`
of the integral closed subschemes of Tag 02RW, `π` is `⨿ i_j`, and the cycle on `V` restricts to
`div(f_j)` on the component `W_j`. -/
theorem exists_isFinite_properPushforward_eq_of_isRationallyEquivalentToZero (k : ℤ)
    {α : CycleGroup C sX k} (hα : IsRationallyEquivalentToZero C sX k α) :
    ∃ (V : Scheme.{u}) (π : V ⟶ X) (_ : IsFinite π) (c : CycleGroup C (π ≫ sX) k),
      properPushforwardHom C (π ≫ sX) sX π rfl k c = α := by
  obtain ⟨J, W, hW, hDim, hLocal, g, hg⟩ := hα
  have hfin : IsFinite (Sigma.desc fun j ↦ (W j).subschemeι) :=
    isFinite_sigmaDesc_of_locallyFinite _
      (by simpa only [Scheme.IdealSheafData.range_subschemeι] using hLocal)
  refine ⟨∐ fun j ↦ (W j).subscheme, Sigma.desc fun j ↦ (W j).subschemeι, hfin, ?_⟩
  have he : ∀ j, (Sigma.ι (fun j ↦ (W j).subscheme) j).isoOpensRange.hom ≫
      (Sigma.ι (fun j ↦ (W j).subscheme) j).opensRange.ι ≫
        (Sigma.desc fun j ↦ (W j).subschemeι) = (W j).subschemeι := by
    intro j
    rw [← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
    exact Sigma.ι_comp_desc _ j
  obtain ⟨c, hc, -⟩ := exists_properPushforward_eq_of_isClopenDecomposition C sX
    (Sigma.desc fun j ↦ (W j).subschemeι) k
    (isClopenDecomposition_opensRange_sigmaι fun j ↦ (W j).subscheme)
    (fun j ↦ (W j).subschemeι)
    (fun j ↦ (Sigma.ι (fun j ↦ (W j).subscheme) j).isoOpensRange.hom) he
    (fun j ↦ subschemePrincipalDivisorCycle C sX k (W j) (hW j) (hDim j) (g j))
    (α := α) fun x ↦ by
      rw [hg x]
      exact finsum_congr fun j ↦ by
        rw [← properPushforward_subschemePrincipalDivisorCycle C sX k (W j) (hW j) (hDim j) (g j)]
  exact ⟨c, hc⟩

end Stacks.Chow

end
