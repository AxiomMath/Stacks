module

public import StacksFrontier.AlgebraicGeometry.Chow.CycleAdditivity
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChowGroupDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackOfCycles
public import StacksFrontier.Topology.LocallyFinite.Sigma

/-!
# Flat pullback and rational equivalence

In Situation 0EDT let `X, Y/B` be good and let `f : X ⟶ Y` be a morphism over the base which is
flat of relative dimension `r`. This file shows that if `α ∼_rat β` as `m`-cycles on `Y` then
`f^*α ∼_rat f^*β` as `n`-cycles on `X`, where `m + r = n`, given that for every integral closed
subspace `V ⊆ Y` of δ-dimension `m + 1` the flat pullback of the pushforward of a principal
divisor on `V` is a locally finite sum of pushforwards of principal divisors on integral closed
subspaces of `X` of δ-dimension `n + 1` lying in `f^{-1}(|V|)`.

## Main definitions

* `AlgebraicGeometry.Space.flatPullbackChowMap_of_pushforwardDivisor`: under this hypothesis, the
  flat pullback `CH_m(Y) → CH_n(X)` on Chow groups.

## Main results

* `Stacks.Chow.finsum_finsum_comm_of_finite_support`: a double `finsum` whose terms vanish
  outside a finite set of pairs may be taken in either order.
* `AlgebraicGeometry.Space.flatPullbackMap_cycleFamilySum_apply`: the flat pullback of the cycle
  `∑_j (i_j)_* c_j` attached to a locally finite family of integral closed subspaces is
  coefficientwise the locally finite sum of the flat pullbacks of the summands.
* `AlgebraicGeometry.Space.isRationallyEquivalentToZero_flatPullbackMap_of_pushforwardDivisor`:
  under this hypothesis, the flat pullback of a cycle rationally equivalent to zero is rationally
  equivalent to zero.
* `AlgebraicGeometry.Space.rationallyEquivalent_flatPullbackMap_of_pushforwardDivisor`: under
  this hypothesis, flat pullback preserves rational equivalence.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EE2](https://stacks.math.columbia.edu/tag/0EE2)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0EP6](https://stacks.math.columbia.edu/tag/0EP6)
* [Stacks Project, Tag 0EP8](https://stacks.math.columbia.edu/tag/0EP8)
* [Stacks Project, Tag 0EPD](https://stacks.math.columbia.edu/tag/0EPD)
* [Stacks Project, Tag 0EQ2](https://stacks.math.columbia.edu/tag/0EQ2)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQ8](https://stacks.math.columbia.edu/tag/0EQ8)
* [Stacks Project, Tag 0EQA](https://stacks.math.columbia.edu/tag/0EQA)
* [Stacks Project, Tag 0EQB](https://stacks.math.columbia.edu/tag/0EQB)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace Stacks.Chow

/-! ### Exchanging two locally finite sums over index types in different universes -/

/-- A double `finsum` whose terms vanish outside a finite set of pairs may be taken in either
order. -/
theorem finsum_finsum_comm_of_finite_support {A B M : Type*} [AddCommMonoid M] (G : A → B → M)
    (h : (Function.support fun s : A × B => G s.1 s.2).Finite) :
    (∑ᶠ a : A, ∑ᶠ b : B, G a b) = ∑ᶠ b : B, ∑ᶠ a : A, G a b := by
  have h' : (Function.support fun s : B × A => G s.2 s.1).Finite :=
    by simpa [Function.support] using h.preimage Prod.swap_injective.injOn
  rw [← finsum_curry (fun s : A × B => G s.1 s.2) h,
    ← finsum_curry (fun s : B × A => G s.2 s.1) h']
  exact (finsum_comp_equiv (Equiv.prodComm B A) (f := fun s : A × B => G s.1 s.2)).symm

end Stacks.Chow

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)

/-! ### The flat pullback of a locally finite sum of pushforwards -/

/-- At a fixed integral closed subspace `T ⊆ X` only finitely many pairs `(V, j)` contribute to
the coefficient of `f^*(∑_j (i_j)_* c_j)` at `T`: the products of the coefficient of
`(i_j)_* c_j` at `V` with the multiplicity of `T` in `f^{-1}(V)` have finite support. -/
theorem finite_support_flatPullbackMult_mul_pushforward {J : Type v}
    (W : J → IntegralClosedSubspace D.site D.base D.base_mem Y)
    (hWfin : LocallyFinite fun j : J =>
      subspacePointSet D.site D.base D.base_mem Y (W j).subspace)
    (m : ℤ) (c : ∀ j, CycleGroup D ((W j).subspace.ι ≫ sY) m)
    (T : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (Function.support fun s : IntegralClosedSubspace D.site D.base D.base_mem Y × J =>
      (integralClosedSubspacePushforward D sY hY (W s.2) m (c s.2)).1 s.1 *
        flatPullbackMult D sX hX sY hY f hbase r hflat hr s.1 T).Finite := by
  classical
  obtain ⟨V₀, hV₀, hV₀fin⟩ := hWfin (pointsMap D.site D.base D.base_mem X f
    (T.ambientGenericPoint D.site D.base D.base_mem))
  choose U hU hUfin using fun j : J => locallyFinite_pushforward_support D sY hY (W j) m (c j)
    (pointsMap D.site D.base D.base_mem X f (T.ambientGenericPoint D.site D.base D.base_mem))
  refine (hV₀fin.biUnion fun j _ => (hUfin j).image fun V =>
    ((V, j) : IntegralClosedSubspace D.site D.base D.base_mem Y × J)).subset ?_
  rintro ⟨V, j⟩ hVj
  have hterm : (integralClosedSubspacePushforward D sY hY (W j) m (c j)).1 V *
      flatPullbackMult D sX hX sY hY f hbase r hflat hr V T ≠ 0 := hVj
  have hpj : (integralClosedSubspacePushforward D sY hY (W j) m (c j)).1 V ≠ 0 :=
    left_ne_zero_of_mul hterm
  have hmV : flatPullbackMult D sX hX sY hY f hbase r hflat hr V T ≠ 0 :=
    right_ne_zero_of_mul hterm
  have hξV : pointsMap D.site D.base D.base_mem X f
      (T.ambientGenericPoint D.site D.base D.base_mem) ∈
      subspacePointSet D.site D.base D.base_mem Y V.subspace :=
    mem_subspacePointSet_of_flatPullbackMult_ne_zero D sX hX sY hY f hbase r hflat hr V T hmV
  have hξW : pointsMap D.site D.base D.base_mem X f
      (T.ambientGenericPoint D.site D.base D.base_mem) ∈
      subspacePointSet D.site D.base D.base_mem Y (W j).subspace :=
    subspacePointSet_subset_of_pushforward_ne_zero D sY hY (W j) m (c j) V hpj hξV
  have hjf : j ∈ {j : J |
      (subspacePointSet D.site D.base D.base_mem Y (W j).subspace ∩ V₀).Nonempty} :=
    ⟨_, hξW, mem_of_mem_nhds hV₀⟩
  refine Set.mem_biUnion hjf ⟨V, ⟨_, ?_, mem_of_mem_nhds (hU j)⟩, rfl⟩
  simp only [Set.mem_ite_empty_left]
  exact ⟨hpj, hξV⟩

/-- The flat pullback of the cycle `∑_j (i_j)_* c_j` attached to a locally finite family
`{W_j ⊆ Y}` of integral closed subspaces is, coefficientwise, the locally finite sum of the flat
pullbacks `f^*((i_j)_* c_j)` of the summands. -/
theorem flatPullbackMap_cycleFamilySum_apply {J : Type v}
    (W : J → IntegralClosedSubspace D.site D.base D.base_mem Y)
    (hWfin : LocallyFinite fun j : J =>
      subspacePointSet D.site D.base D.base_mem Y (W j).subspace)
    (m n : ℤ) (hmn : m + (r : ℤ) = n) (c : ∀ j, CycleGroup D ((W j).subspace.ι ≫ sY) m)
    (T : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn
        (cycleFamilySum D sY hY W hWfin m c)).1 T =
      ∑ᶠ j : J, (flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn
        (integralClosedSubspacePushforward D sY hY (W j) m (c j))).1 T := by
  calc (flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn
        (cycleFamilySum D sY hY W hWfin m c)).1 T
      = ∑ᶠ V : IntegralClosedSubspace D.site D.base D.base_mem Y,
          (cycleFamilySum D sY hY W hWfin m c).1 V *
            flatPullbackMult D sX hX sY hY f hbase r hflat hr V T := rfl
    _ = ∑ᶠ V : IntegralClosedSubspace D.site D.base D.base_mem Y, ∑ᶠ j : J,
          (integralClosedSubspacePushforward D sY hY (W j) m (c j)).1 V *
            flatPullbackMult D sX hX sY hY f hbase r hflat hr V T := finsum_congr fun V => by
          rw [cycleFamilySum_apply, finsum_mul]
    _ = ∑ᶠ j : J, ∑ᶠ V : IntegralClosedSubspace D.site D.base D.base_mem Y,
          (integralClosedSubspacePushforward D sY hY (W j) m (c j)).1 V *
            flatPullbackMult D sX hX sY hY f hbase r hflat hr V T :=
        Stacks.Chow.finsum_finsum_comm_of_finite_support _
          (finite_support_flatPullbackMult_mul_pushforward D sX hX sY hY f hbase r hflat hr
            W hWfin m c T)
    _ = ∑ᶠ j : J, (flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn
          (integralClosedSubspacePushforward D sY hY (W j) m (c j))).1 T := rfl

/-! ### Flat pullback and rational equivalence -/

/-- The flat pullback of an `m`-cycle rationally equivalent to zero is rationally equivalent to
zero, **given** that the flat pullback of the pushforward `(i_V)_* div(g)` of a principal divisor
from an integral closed subspace `V ⊆ Y` of δ-dimension `m + 1` is presented as a sum of
principal divisors over a locally finite family of integral closed subspaces of `X` of
δ-dimension `n + 1` whose point sets lie in `f^{-1}(|V|)`. -/
theorem isRationallyEquivalentToZero_flatPullbackMap_of_pushforwardDivisor (m n : ℤ)
    (hmn : m + (r : ℤ) = n)
    (hdiv : ∀ V : IntegralClosedSubspace D.site D.base D.base_mem Y,
      deltaDimension D sY V = m + 1 →
      ∀ d : CycleGroup D (V.subspace.ι ≫ sY) m,
        IsPrincipalDivisorCycle D (V.subspace.ι ≫ sY) m d →
          ∃ (K : Type v) (U : K → IntegralClosedSubspace D.site D.base D.base_mem X)
            (hUfin : LocallyFinite fun l : K =>
              subspacePointSet D.site D.base D.base_mem X (U l).subspace)
            (e : ∀ l, CycleGroup D ((U l).subspace.ι ≫ sX) n),
            (∀ l, subspacePointSet D.site D.base D.base_mem X (U l).subspace ⊆
                pointsMap D.site D.base D.base_mem X f ⁻¹'
                  subspacePointSet D.site D.base D.base_mem Y V.subspace) ∧
              (∀ l, deltaDimension D sX (U l) = n + 1) ∧
                (∀ l, IsPrincipalDivisorCycle D ((U l).subspace.ι ≫ sX) n (e l)) ∧
                  flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn
                      (integralClosedSubspacePushforward D sY hY V m d) =
                    cycleFamilySum D sX hX U hUfin n e)
    {α : CycleGroup D sY m} (hα : IsRationallyEquivalentToZero.{v} D sY hY m α) :
    IsRationallyEquivalentToZero.{v} D sX hX n
      (flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn α) := by
  obtain ⟨J, W, hWfin, c, hdim, hprin, hsum⟩ := hα
  choose K U hUfin e hsub hUdim hUprin heq using
    fun j : J => hdiv (W j) (hdim j) (c j) (hprin j)
  have hVfin : LocallyFinite fun s : (j : J) × K j =>
      subspacePointSet D.site D.base D.base_mem X (U s.1 s.2).subspace :=
    locallyFinite_sigma_of_subset
      (locallyFinite_preimage_pointsMap D.site D.base D.base_mem hX.1 hY.1 f
        (fun j => subspacePointSet D.site D.base D.base_mem Y (W j).subspace) hWfin)
      hUfin hsub
  refine ⟨(j : J) × K j, fun s => U s.1 s.2, hVfin, fun s => e s.1 s.2,
    fun s => hUdim s.1 s.2, fun s => hUprin s.1 s.2, Subtype.ext (funext fun T => ?_)⟩
  have hterm : ∀ j : J, (flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn
      (integralClosedSubspacePushforward D sY hY (W j) m (c j))).1 T =
        ∑ᶠ l : K j,
          (integralClosedSubspacePushforward D sX hX (U j l) n (e j l)).1 T := fun j => by
    rw [heq j]
    exact cycleFamilySum_apply D sX hX (U j) (hUfin j) n (e j) T
  rw [hsum, flatPullbackMap_cycleFamilySum_apply D sX hX sY hY f hbase r hflat hr W hWfin m n hmn
    c T, finsum_congr hterm]
  exact (Stacks.Chow.finsum_sigma (fun s : (j : J) × K j =>
    (integralClosedSubspacePushforward D sX hX (U s.1 s.2) n (e s.1 s.2)).1 T)
    (finite_support_cycleFamilyCoeff D sX hX (fun s : (j : J) × K j => U s.1 s.2) hVfin n
      (fun s => e s.1 s.2) T)).symm

/-- The class in `CH_n(X)` of the flat pullback of a cycle rationally equivalent to zero
vanishes, given the hypothesis `hdiv` of
`AlgebraicGeometry.Space.isRationallyEquivalentToZero_flatPullbackMap_of_pushforwardDivisor`. -/
theorem chowClass_flatPullbackMap_eq_zero_of_pushforwardDivisor (m n : ℤ)
    (hmn : m + (r : ℤ) = n)
    (hdiv : ∀ V : IntegralClosedSubspace D.site D.base D.base_mem Y,
      deltaDimension D sY V = m + 1 →
      ∀ d : CycleGroup D (V.subspace.ι ≫ sY) m,
        IsPrincipalDivisorCycle D (V.subspace.ι ≫ sY) m d →
          ∃ (K : Type v) (U : K → IntegralClosedSubspace D.site D.base D.base_mem X)
            (hUfin : LocallyFinite fun l : K =>
              subspacePointSet D.site D.base D.base_mem X (U l).subspace)
            (e : ∀ l, CycleGroup D ((U l).subspace.ι ≫ sX) n),
            (∀ l, subspacePointSet D.site D.base D.base_mem X (U l).subspace ⊆
                pointsMap D.site D.base D.base_mem X f ⁻¹'
                  subspacePointSet D.site D.base D.base_mem Y V.subspace) ∧
              (∀ l, deltaDimension D sX (U l) = n + 1) ∧
                (∀ l, IsPrincipalDivisorCycle D ((U l).subspace.ι ≫ sX) n (e l)) ∧
                  flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn
                      (integralClosedSubspacePushforward D sY hY V m d) =
                    cycleFamilySum D sX hX U hUfin n e)
    (α : CycleGroup D sY m) (hα : IsRationallyEquivalentToZero.{v} D sY hY m α) :
    ((chowClass.{v} D sX hX n).comp
        (flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn)) α = 0 :=
  (chowClass_eq_zero_iff.{v} D sX hX n _).2
    (isRationallyEquivalentToZero_flatPullbackMap_of_pushforwardDivisor.{v} D sX hX sY hY f hbase
      r hflat hr m n hmn hdiv hα)

/-- In Situation 0EDT let `X, Y/B` be good, let `f : X ⟶ Y` be flat of relative dimension `r`,
and let `α ∼_rat β` be rationally equivalent `m`-cycles on `Y`. Then `f^*α ∼_rat f^*β` as
`n`-cycles on `X`, where `m + r = n`, given the hypothesis `hdiv` of
`AlgebraicGeometry.Space.isRationallyEquivalentToZero_flatPullbackMap_of_pushforwardDivisor`. -/
theorem rationallyEquivalent_flatPullbackMap_of_pushforwardDivisor (m n : ℤ)
    (hmn : m + (r : ℤ) = n)
    (hdiv : ∀ V : IntegralClosedSubspace D.site D.base D.base_mem Y,
      deltaDimension D sY V = m + 1 →
      ∀ d : CycleGroup D (V.subspace.ι ≫ sY) m,
        IsPrincipalDivisorCycle D (V.subspace.ι ≫ sY) m d →
          ∃ (K : Type v) (U : K → IntegralClosedSubspace D.site D.base D.base_mem X)
            (hUfin : LocallyFinite fun l : K =>
              subspacePointSet D.site D.base D.base_mem X (U l).subspace)
            (e : ∀ l, CycleGroup D ((U l).subspace.ι ≫ sX) n),
            (∀ l, subspacePointSet D.site D.base D.base_mem X (U l).subspace ⊆
                pointsMap D.site D.base D.base_mem X f ⁻¹'
                  subspacePointSet D.site D.base D.base_mem Y V.subspace) ∧
              (∀ l, deltaDimension D sX (U l) = n + 1) ∧
                (∀ l, IsPrincipalDivisorCycle D ((U l).subspace.ι ≫ sX) n (e l)) ∧
                  flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn
                      (integralClosedSubspacePushforward D sY hY V m d) =
                    cycleFamilySum D sX hX U hUfin n e)
    {α β : CycleGroup D sY m} (h : RationallyEquivalent.{v} D sY hY m α β) :
    RationallyEquivalent.{v} D sX hX n
      (flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn α)
      (flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn β) :=
  (chowClass_eq_iff_rationallyEquivalent.{v} D sX hX n _ _).1
    (map_eq_of_rationallyEquivalent.{u, v} D sY hY m
      ((chowClass.{v} D sX hX n).comp
        (flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn))
      (chowClass_flatPullbackMap_eq_zero_of_pushforwardDivisor.{v} D sX hX sY hY f hbase r hflat
        hr m n hmn hdiv) h)

/-- The flat pullback `f^* : CH_m(Y) → CH_n(X)` on Chow groups, for `m + r = n`, given the
hypothesis `hdiv` of
`AlgebraicGeometry.Space.isRationallyEquivalentToZero_flatPullbackMap_of_pushforwardDivisor`. -/
def flatPullbackChowMap_of_pushforwardDivisor (m n : ℤ) (hmn : m + (r : ℤ) = n)
    (hdiv : ∀ V : IntegralClosedSubspace D.site D.base D.base_mem Y,
      deltaDimension D sY V = m + 1 →
      ∀ d : CycleGroup D (V.subspace.ι ≫ sY) m,
        IsPrincipalDivisorCycle D (V.subspace.ι ≫ sY) m d →
          ∃ (K : Type v) (U : K → IntegralClosedSubspace D.site D.base D.base_mem X)
            (hUfin : LocallyFinite fun l : K =>
              subspacePointSet D.site D.base D.base_mem X (U l).subspace)
            (e : ∀ l, CycleGroup D ((U l).subspace.ι ≫ sX) n),
            (∀ l, subspacePointSet D.site D.base D.base_mem X (U l).subspace ⊆
                pointsMap D.site D.base D.base_mem X f ⁻¹'
                  subspacePointSet D.site D.base D.base_mem Y V.subspace) ∧
              (∀ l, deltaDimension D sX (U l) = n + 1) ∧
                (∀ l, IsPrincipalDivisorCycle D ((U l).subspace.ι ≫ sX) n (e l)) ∧
                  flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn
                      (integralClosedSubspacePushforward D sY hY V m d) =
                    cycleFamilySum D sX hX U hUfin n e) :
    chowGroup.{v} D sY hY m →+ chowGroup.{v} D sX hX n :=
  chowGroupLift.{u, v} D sY hY m
    ((chowClass.{v} D sX hX n).comp
      (flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn))
    (chowClass_flatPullbackMap_eq_zero_of_pushforwardDivisor.{v} D sX hX sY hY f hbase r hflat hr
      m n hmn hdiv)

end AlgebraicGeometry.Space

end
