module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.Continuous
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupHomology.NormalSubgroupAction
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.Trace
public import StacksFrontier.NumberTheory.TraceFormula.CommutativeExample

/-!
# The abstract trace formula

Let `1 → G → Γ → Ẑ → 1` be an extension of profinite groups, given by a continuous surjective
homomorphism `deg : Γ → Ẑ` with kernel `G`. Following [Stacks, Section 03VO], `Γ` *has an
abstract trace formula* if there exist

1. an integer `q ≥ 1`, and
2. for every `d ≥ 1` a finite set `S_d` and for each `x ∈ S_d` a conjugacy class `F_x` of `Γ`
   with `deg(F_x) = d`,

such that

1. for all primes `ℓ` not dividing `q`, `cd_ℓ(G) < ∞`, and
2. for all finite rings `Λ` with `q ∈ Λ^*`, all finite projective `Λ`-modules `M` with
   continuous `Γ`-action and all `n > 0`,
   `∑_{d ∣ n} d (∑_{x ∈ S_d} Tr(F_x^{n/d} | M)) = q^n Tr(F^n | M ⊗^L_{Λ[[G]]} Λ)` in `Λ^♮`,

where `M ⊗^L_{Λ[[G]]} Λ = LH₀(G, M)` is the derived homology and `F` is an element of degree `1`.

## Main definitions

* `Stacks.TraceFormula.HasFiniteCohomologicalDimensionAt`: `cd_ℓ(G) < ∞`.
* `Stacks.TraceFormula.AbstractTraceFormula`: the data `q`, `S_d`, `F_x` and the two conditions.
* `Stacks.TraceFormula.HasAbstractTraceFormula`: the existence of such data.

## Implementation notes

`Ẑ` is `Stacks.TraceFormula.ProfiniteIntegers = ∏_ℓ ℤ_ℓ`, written multiplicatively as the
target of the degree map.

The derived homology `LH₀(G, M) = M ⊗^L_{Λ[[G]]} Λ` is `Stacks.GroupHomology.derivedCoinvariants`
of `M` regarded as a module over the completed group algebra `Λ[[G]]`, an object of `D(Λ)`, and
the action of `γ ∈ Γ` on it is `Stacks.GroupHomology.derivedCoinvariantsAction`. The right hand
side of the trace formula is the trace `CategoryTheory.FilteredDerived.perfectDerivedTrace` of
[Stacks, Tag 03TI] of the action of `F^n`, which is defined for a perfect object; perfectness of
`LH₀(G, M)` is therefore part of condition (2), as it is implicit in the source's formula. The left
hand side is the trace `Stacks.Trace.projectiveModuleTrace` of [Stacks, Tag 03U6]; both take
values in `Λ^♮ = Λ / [Λ, Λ]`, the ring `Λ` not being assumed commutative.

A conjugacy class has a well-defined degree, and its trace on `M` does not depend on the chosen
representative; the identity is required for **every** choice of representatives of the classes
`F_x` and **every** element `F` of degree `1`, which is the source's formula.

A continuous action on the finite module `M` is one whose point stabilizers are open. Finiteness
of `cd_ℓ(G)` is the vanishing of the continuous cohomology `H^i(G, A)` of [Stacks, Tag 04JR] in
all large degrees, for all `ℓ`-primary torsion discrete `G`-modules `A`.

The group `Γ`, the coefficient rings and the modules live in one universe; the sets `S_d` are
finite types.

## References

* [Stacks Project, Tag 03VO](https://stacks.math.columbia.edu/tag/03VO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupHomology CategoryTheory.FilteredDerived

universe u

namespace Stacks.TraceFormula

attribute [local instance] HasDerivedCategory.standard

/-- A profinite group `G` has finite `ℓ`-cohomological dimension when its continuous cohomology
with coefficients in every `ℓ`-primary torsion discrete `G`-module vanishes in all large
degrees. -/
public def HasFiniteCohomologicalDimensionAt (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (ℓ : ℕ) : Prop :=
  ∃ N : ℕ, ∀ i : ℕ, N < i → ∀ A : ContinuousGModule.{u, u} G,
    (∀ a : A.obj.obj.V, ∃ k : ℕ, (ℓ ^ k) • a = 0) →
      IsZero (continuousGroupCohomology.{u, u} G i A)

section Setting

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
  [TotallyDisconnectedSpace Γ]

omit [IsTopologicalGroup Γ] [TotallyDisconnectedSpace Γ] in
/-- The kernel of a continuous homomorphism from a compact group to `Ẑ` is compact. -/
public theorem compactSpace_ker (deg : Γ →* Multiplicative ProfiniteIntegers)
    (hdeg : Continuous deg) : CompactSpace deg.ker := by
  have hclosed : IsClosed (deg.ker : Set Γ) := by
    have : (deg.ker : Set Γ) = deg ⁻¹' {1} := by ext; simp [MonoidHom.mem_ker]
    rw [this]
    exact isClosed_singleton.preimage hdeg
  exact isCompact_iff_compactSpace.mp hclosed.isCompact

omit [TotallyDisconnectedSpace Γ] in
/-- A finite module with a continuous action of `Γ` is acted on trivially by an open normal
subgroup of the kernel of a continuous homomorphism `Γ → Ẑ`. -/
public theorem isSmoothFor_ker (deg : Γ →* Multiplicative ProfiniteIntegers)
    (hdeg : Continuous deg) (M : Type u) [AddCommGroup M] [DistribMulAction Γ M] [Finite M]
    (hM : ∀ m : M, IsOpen {γ : Γ | γ • m = m}) :
    ∃ U : OpenNormalSubgroup deg.ker, ∀ g ∈ U, ∀ m : M, g • m = m := by
  have := compactSpace_ker deg hdeg
  exact exists_openNormalSubgroup_smul_eq M fun m =>
    (hM m).preimage continuous_subtype_val

end Setting

/-- **Stacks Project, Section 03VO.** An *abstract trace formula* for an extension of profinite
groups `1 → G → Γ → Ẑ → 1`, given by a continuous surjective degree map `deg : Γ → Ẑ` with kernel
`G`: an integer `q ≥ 1`, for every `d` a finite set `S_d` and for each `x ∈ S_d` a conjugacy class
`F_x` of degree `d` (for `d ≥ 1`), such that `cd_ℓ(G) < ∞` for all primes `ℓ ∤ q` and such that
for all finite rings `Λ` with `q ∈ Λ^*`, all finite projective `Λ`-modules `M` with continuous
`Γ`-action and all `n > 0`, the derived homology `LH₀(G, M) = M ⊗^L_{Λ[[G]]} Λ` is perfect and
`∑_{d ∣ n} d ∑_{x ∈ S_d} Tr(F_x^{n/d} | M) = q^n Tr(F^n | LH₀(G, M))` in `Λ^♮`, for every element
`F` of degree one and all representatives of the classes `F_x`. -/
@[stacks 03VO "an extension 1 → G → Γ → Ẑ → 1 of profinite groups has an abstract trace formula"]
public structure AbstractTraceFormula (Γ : Type u) [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    (deg : Γ →* Multiplicative ProfiniteIntegers) (hdeg : Continuous deg)
    (hsurj : Function.Surjective deg) where
  /-- The integer `q`. -/
  q : ℕ
  /-- `q ≥ 1`. -/
  one_le_q : 1 ≤ q
  /-- The finite set `S_d`. -/
  S : ℕ → Type
  /-- `S_d` is finite. -/
  [fintypeS : ∀ d, Fintype (S d)]
  /-- The conjugacy class `F_x` attached to `x ∈ S_d`. -/
  F : ∀ d, S d → ConjClasses Γ
  /-- The class `F_x` has degree `d`. -/
  deg_F : ∀ d, 1 ≤ d → ∀ (x : S d) (g : Γ), ConjClasses.mk g = F d x →
    deg g = Multiplicative.ofAdd (d : ProfiniteIntegers)
  /-- `cd_ℓ(G) < ∞` for every prime `ℓ` not dividing `q`. -/
  finite_cohomologicalDimension : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ q →
    HasFiniteCohomologicalDimensionAt deg.ker ℓ
  /-- The trace formula. -/
  trace_formula : ∀ (Λ : Type u) [Ring Λ] [Finite Λ], IsUnit (q : Λ) →
    ∀ (M : Type u) [AddCommGroup M] [Module Λ M] [Module.Finite Λ M] [Module.Projective Λ M]
      [DistribMulAction Γ M] [SMulCommClass Γ Λ M] (hM : ∀ m : M, IsOpen {γ : Γ | γ • m = m})
      (n : ℕ), 0 < n →
      ∃ hperf : StacksDraft.Perfect.IsPerfect (derivedCoinvariants
          (toCompletedGroupAlgebraModuleCat Λ (G := deg.ker) (V := M)
            (haveI := Module.finite_of_finite Λ (M := M); isSmoothFor_ker deg hdeg M hM))),
        ∀ (g : ∀ d, S d → Γ), (∀ d x, ConjClasses.mk (g d x) = F d x) →
        ∀ Φ : Γ, deg Φ = Multiplicative.ofAdd (1 : ProfiniteIntegers) →
          ∑ d ∈ n.divisors, d • ∑ x : S d,
              Stacks.Trace.projectiveModuleTrace Λ M
                (DistribMulAction.toModuleEnd Λ M (g d x ^ (n / d))) =
            (q ^ n) • perfectDerivedTrace Λ ⟨_, hperf⟩
              (derivedCoinvariantsAction Λ
                (haveI := Module.finite_of_finite Λ (M := M); isSmoothFor_ker deg hdeg M hM)
                (Φ ^ n))

attribute [instance] AbstractTraceFormula.fintypeS

/-- **Stacks Project, Section 03VO.** The extension `1 → G → Γ → Ẑ → 1` *has an abstract trace
formula* if the data of `Stacks.TraceFormula.AbstractTraceFormula` exist. -/
@[stacks 03VO "has an abstract trace formula"]
public def HasAbstractTraceFormula (Γ : Type u) [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    (deg : Γ →* Multiplicative ProfiniteIntegers) (hdeg : Continuous deg)
    (hsurj : Function.Surjective deg) : Prop :=
  Nonempty (AbstractTraceFormula Γ deg hdeg hsurj)

end Stacks.TraceFormula

end
