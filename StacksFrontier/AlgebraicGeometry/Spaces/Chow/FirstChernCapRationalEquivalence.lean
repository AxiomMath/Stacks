module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChowGroupDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackRationalEquivalence

/-!
# The cap product with the first Chern class against rational equivalence

In Situation 0EDT let `X/B` be good and let `𝒩` be an invertible `𝒪_X`-module.  Stacks 0EQY is
the assertion that the cap product `c₁(𝒩) ∩ - : Z_{k+1}(X) ⟶ CH_k(X)` of Stacks 0EQJ *factors
through rational equivalence*, so that it descends to

`c₁(𝒩) ∩ - : CH_{k+1}(X) ⟶ CH_k(X)`.

By `AlgebraicGeometry.Space.chowGroupLift` the descent is exactly the statement that the cap
product kills every `(k+1)`-cycle rationally equivalent to zero, and by Stacks 0EQ6, part (2),
such a cycle is a locally finite sum `∑_j (i_j)_* div(f_j)` over integral closed subspaces
`W_j ⊆ X` of δ-dimension `k + 2`.

This file shows that the cap product of such a sum is the locally finite sum of the cap products
of its summands, and deduces the descent under the hypothesis `hdiv` that the cap product of
each summand `(i_W)_* div(f)` is a locally finite sum of principal divisors on integral closed
subspaces of `X` of δ-dimension `k + 1` whose point sets lie in `|W|`.

## Main results

* `firstChernCapCycleMap_cycleFamilySum_apply`: the cap product of Stacks 0EQJ of the cycle
  `∑_j (i_j)_* c_j` of Stacks 0EQ6, part (1), is coefficientwise the locally finite sum of the
  cap products of the summands.
* `isRationallyEquivalentToZero_firstChernCapCycleMap_of_pushforwardDivisor`: the cap product
  of a cycle rationally equivalent to zero is rationally equivalent to zero, **given** the
  hypothesis `hdiv`.
* `canonicalFirstChernCapChowMap_of_pushforwardDivisor`: the descended operation
  `CH_{k+1}(X) ⟶ CH_k(X)` at the canonical choices of Stacks 0EQJ, given the same hypothesis.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EQY](https://stacks.math.columbia.edu/tag/0EQY)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ)
    (chern : FirstChernComponentCycleRule D sX k)

/-! ### The cap product of a locally finite sum of pushforwards -/

/-- Let `{W_j ⊆ X}` be a locally finite family of integral closed subspaces and `c_j` a cycle on
`W_j`.  At a fixed integral closed subspace `T ⊆ X` only finitely many pairs `(V, j)` have both
the coefficient of `(i_j)_* c_j` at `V` and the coefficient at `T` of the component cycle of `V`
nonzero, so only finitely many contribute to the coefficient of `c₁(𝒩) ∩ ∑_j (i_j)_* c_j`. -/
theorem finite_support_firstChernComponentCycle_mul_pushforward {J : Type v}
    (W : J → IntegralClosedSubspace D.site D.base D.base_mem X)
    (hWfin : LocallyFinite fun j : J =>
      subspacePointSet D.site D.base D.base_mem X (W j).subspace)
    (c : ∀ j, CycleGroup D ((W j).subspace.ι ≫ sX) (k + 1))
    (T : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (Function.support fun s : IntegralClosedSubspace D.site D.base D.base_mem X × J =>
      (integralClosedSubspacePushforward D sX hX (W s.2) (k + 1) (c s.2)).1 s.1 *
        (firstChernComponentCycle D sX hX k chern s.1).1 T).Finite := by
  classical
  set ξ : points D.site D.base D.base_mem X :=
    pointsMap D.site D.base D.base_mem T.subspace.toFunctor T.subspace.ι
      (T.genericPoint D.site D.base D.base_mem) with hξ
  have hξT : ξ ∈ subspacePointSet D.site D.base D.base_mem X T.subspace := ⟨_, rfl⟩
  obtain ⟨V₀, hV₀, hV₀fin⟩ := hWfin ξ
  choose U hU hUfin using fun j : J =>
    locallyFinite_pushforward_support D sX hX (W j) (k + 1) (c j) ξ
  refine (hV₀fin.biUnion fun j _ => (hUfin j).image fun V =>
    ((V, j) : IntegralClosedSubspace D.site D.base D.base_mem X × J)).subset ?_
  rintro ⟨V, j⟩ hVj
  have hterm : (integralClosedSubspacePushforward D sX hX (W j) (k + 1) (c j)).1 V *
      (firstChernComponentCycle D sX hX k chern V).1 T ≠ 0 := hVj
  have hpj : (integralClosedSubspacePushforward D sX hX (W j) (k + 1) (c j)).1 V ≠ 0 :=
    left_ne_zero_of_mul hterm
  have hmV : (firstChernComponentCycle D sX hX k chern V).1 T ≠ 0 := right_ne_zero_of_mul hterm
  have hξV : ξ ∈ subspacePointSet D.site D.base D.base_mem X V.subspace :=
    subspacePointSet_subset_of_firstChernComponentCycle_ne_zero D sX hX k chern V T hmV hξT
  have hξW : ξ ∈ subspacePointSet D.site D.base D.base_mem X (W j).subspace :=
    subspacePointSet_subset_of_pushforward_ne_zero D sX hX (W j) (k + 1) (c j) V hpj hξV
  have hjf : j ∈ {j : J |
      (subspacePointSet D.site D.base D.base_mem X (W j).subspace ∩ V₀).Nonempty} :=
    ⟨_, hξW, mem_of_mem_nhds hV₀⟩
  refine Set.mem_biUnion hjf ⟨V, ⟨_, ?_, mem_of_mem_nhds (hU j)⟩, rfl⟩
  simp only [Set.mem_ite_empty_left]
  exact ⟨hpj, hξV⟩

/-- The cap product with the first Chern class of the cycle `∑_j (i_j)_* c_j` attached to a
locally finite family `{W_j ⊆ X}` of integral closed subspaces is, coefficientwise, the locally
finite sum of the cap products `c₁(𝒩) ∩ (i_j)_* c_j` of the summands. -/
theorem firstChernCapCycleMap_cycleFamilySum_apply {J : Type v}
    (W : J → IntegralClosedSubspace D.site D.base D.base_mem X)
    (hWfin : LocallyFinite fun j : J =>
      subspacePointSet D.site D.base D.base_mem X (W j).subspace)
    (c : ∀ j, CycleGroup D ((W j).subspace.ι ≫ sX) (k + 1))
    (T : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (firstChernCapCycleMap D sX hX k chern
        (cycleFamilySum D sX hX W hWfin (k + 1) c)).1 T =
      ∑ᶠ j : J, (firstChernCapCycleMap D sX hX k chern
        (integralClosedSubspacePushforward D sX hX (W j) (k + 1) (c j))).1 T := by
  have hstep : ∀ V : IntegralClosedSubspace D.site D.base D.base_mem X,
      (cycleFamilySum D sX hX W hWfin (k + 1) c).1 V *
          (firstChernComponentCycle D sX hX k chern V).1 T =
        ∑ᶠ j : J, (integralClosedSubspacePushforward D sX hX (W j) (k + 1) (c j)).1 V *
          (firstChernComponentCycle D sX hX k chern V).1 T := by
    intro V
    rw [cycleFamilySum_apply, finsum_mul]
  calc (firstChernCapCycleMap D sX hX k chern (cycleFamilySum D sX hX W hWfin (k + 1) c)).1 T
      = ∑ᶠ V : IntegralClosedSubspace D.site D.base D.base_mem X,
          (cycleFamilySum D sX hX W hWfin (k + 1) c).1 V *
            (firstChernComponentCycle D sX hX k chern V).1 T := rfl
    _ = ∑ᶠ V : IntegralClosedSubspace D.site D.base D.base_mem X, ∑ᶠ j : J,
          (integralClosedSubspacePushforward D sX hX (W j) (k + 1) (c j)).1 V *
            (firstChernComponentCycle D sX hX k chern V).1 T := finsum_congr hstep
    _ = ∑ᶠ j : J, ∑ᶠ V : IntegralClosedSubspace D.site D.base D.base_mem X,
          (integralClosedSubspacePushforward D sX hX (W j) (k + 1) (c j)).1 V *
            (firstChernComponentCycle D sX hX k chern V).1 T :=
        Stacks.Chow.finsum_finsum_comm_of_finite_support _
          (finite_support_firstChernComponentCycle_mul_pushforward D sX hX k chern W hWfin c T)
    _ = ∑ᶠ j : J, (firstChernCapCycleMap D sX hX k chern
          (integralClosedSubspacePushforward D sX hX (W j) (k + 1) (c j))).1 T := rfl

/-! ### Stacks 0EQY, given the cap product of a pushed-forward principal divisor -/

/-- The cap product with the first Chern class of a `(k+1)`-cycle rationally equivalent to zero
is rationally equivalent to zero, **given** that the cap product of the pushforward
`(i_V)_* div(g)` of a principal divisor from an integral closed subspace `V ⊆ X` of
δ-dimension `k + 2` is presented as a sum of principal divisors over a locally finite family of
integral closed subspaces of `X` of δ-dimension `k + 1` whose point sets lie in `|V|`. -/
theorem isRationallyEquivalentToZero_firstChernCapCycleMap_of_pushforwardDivisor
    (hdiv : ∀ V : IntegralClosedSubspace D.site D.base D.base_mem X,
      deltaDimension D sX V = k + 1 + 1 →
      ∀ d : CycleGroup D (V.subspace.ι ≫ sX) (k + 1),
        IsPrincipalDivisorCycle D (V.subspace.ι ≫ sX) (k + 1) d →
          ∃ (K : Type v) (U : K → IntegralClosedSubspace D.site D.base D.base_mem X)
            (hUfin : LocallyFinite fun l : K =>
              subspacePointSet D.site D.base D.base_mem X (U l).subspace)
            (e : ∀ l, CycleGroup D ((U l).subspace.ι ≫ sX) k),
            (∀ l, subspacePointSet D.site D.base D.base_mem X (U l).subspace ⊆
                subspacePointSet D.site D.base D.base_mem X V.subspace) ∧
              (∀ l, deltaDimension D sX (U l) = k + 1) ∧
                (∀ l, IsPrincipalDivisorCycle D ((U l).subspace.ι ≫ sX) k (e l)) ∧
                  firstChernCapCycleMap D sX hX k chern
                      (integralClosedSubspacePushforward D sX hX V (k + 1) d) =
                    cycleFamilySum D sX hX U hUfin k e)
    {α : CycleGroup D sX (k + 1)}
    (hα : IsRationallyEquivalentToZero.{v} D sX hX (k + 1) α) :
    IsRationallyEquivalentToZero.{v} D sX hX k (firstChernCapCycleMap D sX hX k chern α) := by
  obtain ⟨J, W, hWfin, c, hdim, hprin, hsum⟩ := hα
  choose K U hUfin e hsub hUdim hUprin heq using
    fun j : J => hdiv (W j) (hdim j) (c j) (hprin j)
  have hVfin : LocallyFinite fun s : (j : J) × K j =>
      subspacePointSet D.site D.base D.base_mem X (U s.1 s.2).subspace :=
    locallyFinite_sigma_of_subset hWfin hUfin hsub
  refine ⟨(j : J) × K j, fun s => U s.1 s.2, hVfin, fun s => e s.1 s.2,
    fun s => hUdim s.1 s.2, fun s => hUprin s.1 s.2, Subtype.ext (funext fun T => ?_)⟩
  have hterm : ∀ j : J, (firstChernCapCycleMap D sX hX k chern
      (integralClosedSubspacePushforward D sX hX (W j) (k + 1) (c j))).1 T =
        ∑ᶠ l : K j,
          (integralClosedSubspacePushforward D sX hX (U j l) k (e j l)).1 T := fun j => by
    rw [heq j]
    exact cycleFamilySum_apply D sX hX (U j) (hUfin j) k (e j) T
  rw [hsum, firstChernCapCycleMap_cycleFamilySum_apply D sX hX k chern W hWfin c T,
    finsum_congr hterm]
  exact (Stacks.Chow.finsum_sigma (fun s : (j : J) × K j =>
    (integralClosedSubspacePushforward D sX hX (U s.1 s.2) k (e s.1 s.2)).1 T)
    (finite_support_cycleFamilyCoeff D sX hX (fun s : (j : J) × K j => U s.1 s.2) hVfin k
      (fun s => e s.1 s.2) T)).symm

/-- The class in `CH_k(X)` of the cap product of a `(k+1)`-cycle rationally equivalent to zero
vanishes, **given the summand hypothesis** of
`AlgebraicGeometry.Space.isRationallyEquivalentToZero_firstChernCapCycleMap_of_pushforwardDivisor`.
-/
theorem chowClass_firstChernCapCycleMap_eq_zero_of_pushforwardDivisor
    (hdiv : ∀ V : IntegralClosedSubspace D.site D.base D.base_mem X,
      deltaDimension D sX V = k + 1 + 1 →
      ∀ d : CycleGroup D (V.subspace.ι ≫ sX) (k + 1),
        IsPrincipalDivisorCycle D (V.subspace.ι ≫ sX) (k + 1) d →
          ∃ (K : Type v) (U : K → IntegralClosedSubspace D.site D.base D.base_mem X)
            (hUfin : LocallyFinite fun l : K =>
              subspacePointSet D.site D.base D.base_mem X (U l).subspace)
            (e : ∀ l, CycleGroup D ((U l).subspace.ι ≫ sX) k),
            (∀ l, subspacePointSet D.site D.base D.base_mem X (U l).subspace ⊆
                subspacePointSet D.site D.base D.base_mem X V.subspace) ∧
              (∀ l, deltaDimension D sX (U l) = k + 1) ∧
                (∀ l, IsPrincipalDivisorCycle D ((U l).subspace.ι ≫ sX) k (e l)) ∧
                  firstChernCapCycleMap D sX hX k chern
                      (integralClosedSubspacePushforward D sX hX V (k + 1) d) =
                    cycleFamilySum D sX hX U hUfin k e)
    (α : CycleGroup D sX (k + 1))
    (hα : IsRationallyEquivalentToZero.{v} D sX hX (k + 1) α) :
    chowClass.{v} D sX hX k (firstChernCapCycleMap D sX hX k chern α) = 0 :=
  (chowClass_eq_zero_iff.{v} D sX hX k _).2
    (isRationallyEquivalentToZero_firstChernCapCycleMap_of_pushforwardDivisor.{v} D sX hX k chern
      hdiv hα)

/-! ### The descent at the canonical choices of Stacks 0EQJ -/

section Canonical

variable (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)

/-- The cap product `c₁(𝒩) ∩ - : Z_{k+1}(X) ⟶ CH_k(X)` of Stacks 0EQJ at the canonical choices
(`AlgebraicGeometry.Space.canonicalFirstChernCap`) descends to

`c₁(𝒩) ∩ - : CH_{k+1}(X) ⟶ CH_k(X)`,

**given** that the cap product of the pushforward of a principal divisor from an integral closed
subspace of δ-dimension `k + 2` is a locally finite sum of principal divisors carried by that
subspace.  It is `AlgebraicGeometry.Space.chowGroupLift` applied to that cap product. -/
def canonicalFirstChernCapChowMap_of_pushforwardDivisor
    (hdiv : ∀ V : IntegralClosedSubspace D.site D.base D.base_mem X,
      deltaDimension D sX V = k + 1 + 1 →
      ∀ d : CycleGroup D (V.subspace.ι ≫ sX) (k + 1),
        IsPrincipalDivisorCycle D (V.subspace.ι ≫ sX) (k + 1) d →
          ∃ (K : Type v) (U : K → IntegralClosedSubspace D.site D.base D.base_mem X)
            (hUfin : LocallyFinite fun l : K =>
              subspacePointSet D.site D.base D.base_mem X (U l).subspace)
            (e : ∀ l, CycleGroup D ((U l).subspace.ι ≫ sX) k),
            (∀ l, subspacePointSet D.site D.base D.base_mem X (U l).subspace ⊆
                subspacePointSet D.site D.base D.base_mem X V.subspace) ∧
              (∀ l, deltaDimension D sX (U l) = k + 1) ∧
                (∀ l, IsPrincipalDivisorCycle D ((U l).subspace.ι ≫ sX) k (e l)) ∧
                  firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX N hN k)
                      (integralClosedSubspacePushforward D sX hX V (k + 1) d) =
                    cycleFamilySum D sX hX U hUfin k e) :
    chowGroup.{v} D sX hX (k + 1) →+ chowGroup.{v} D sX hX k :=
  chowGroupLift D sX hX (k + 1) (canonicalFirstChernCap.{u, v} D sX hX N hN k)
    (chowClass_firstChernCapCycleMap_eq_zero_of_pushforwardDivisor.{v} D sX hX k
      (canonicalFirstChernRule D sX hX N hN k) hdiv)

/-- The descended operation agrees with the cap product of Stacks 0EQJ on the class of a
cycle. -/
theorem canonicalFirstChernCapChowMap_of_pushforwardDivisor_chowClass
    (hdiv : ∀ V : IntegralClosedSubspace D.site D.base D.base_mem X,
      deltaDimension D sX V = k + 1 + 1 →
      ∀ d : CycleGroup D (V.subspace.ι ≫ sX) (k + 1),
        IsPrincipalDivisorCycle D (V.subspace.ι ≫ sX) (k + 1) d →
          ∃ (K : Type v) (U : K → IntegralClosedSubspace D.site D.base D.base_mem X)
            (hUfin : LocallyFinite fun l : K =>
              subspacePointSet D.site D.base D.base_mem X (U l).subspace)
            (e : ∀ l, CycleGroup D ((U l).subspace.ι ≫ sX) k),
            (∀ l, subspacePointSet D.site D.base D.base_mem X (U l).subspace ⊆
                subspacePointSet D.site D.base D.base_mem X V.subspace) ∧
              (∀ l, deltaDimension D sX (U l) = k + 1) ∧
                (∀ l, IsPrincipalDivisorCycle D ((U l).subspace.ι ≫ sX) k (e l)) ∧
                  firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX N hN k)
                      (integralClosedSubspacePushforward D sX hX V (k + 1) d) =
                    cycleFamilySum D sX hX U hUfin k e)
    (α : CycleGroup D sX (k + 1)) :
    canonicalFirstChernCapChowMap_of_pushforwardDivisor.{v} D sX hX k N hN hdiv
        (chowClass.{v} D sX hX (k + 1) α) =
      canonicalFirstChernCap.{u, v} D sX hX N hN k α :=
  rfl

end Canonical

end AlgebraicGeometry.Space

end
