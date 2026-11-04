module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullback

/-!
# Cycles under a change of the base scheme

Let `B` be a flat base change of Chow situations with dimension shift `c`, that is a flat
morphism `g : S' ⟶ S` of the two bases whose dimension functions differ by `c` on the generic
points of the fibres of `g`. For `X` locally of finite type over `S` the base change
`X' = X ×_S S'` is locally of finite type over `S'`, and the first projection `q : X' ⟶ X` is
flat; this file builds the induced homomorphism `Z_k(X) ⟶ Z_{k+c}(X')` on cycle groups.

The coefficient at a point `x'` of `X'` is the coefficient of the cycle at `q x'` times the
multiplicity of `x'` in the inverse image of the reduced closure of `q x'`, as for a flat
pullback over a fixed base.

## Main definitions

* `Stacks.Chow.baseChangeCycleCoeff` — the coefficient of the base change of a cycle.
* `Stacks.Chow.baseChangeCyclePullback` — the homomorphism `Z_k(X) ⟶ Z_{k+c}(X')`.

## Main results

* `Stacks.Chow.baseChangeCycleCoeff_locallyFiniteSupport`,
  `Stacks.Chow.baseChangeCycleCoeff_mem_cyclesOfDimension` — the coefficient function is a cycle
  of delta-dimension `k + c`.

## References

* [Stacks Project, Tag 0FVG](https://stacks.math.columbia.edu/tag/0FVG)
* [Stacks Project, Tag 0FVI](https://stacks.math.columbia.edu/tag/0FVI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped Topology

universe u

namespace Stacks.Chow

/-- A coefficient function of the shape "coefficient of a cycle at the image point, times the
multiplicity of the point in the inverse image of the reduced closure of that image" has locally
finite support, for any morphism `q : X' ⟶ X` and any cycle on `X`. -/
private theorem locallyFiniteSupport_mul_flatPullbackWeight (C : ChowSituation.{u})
    {X' X : Scheme.{u}} (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (q : X' ⟶ X) (j : ℤ)
    (c : AlgebraicCycle X ℤ) :
    LocallyFiniteSupport (fun x' ↦ c (q.base x') * flatPullbackWeight C sX' q j x') := by
  classical
  intro x'
  obtain ⟨V, hV, hVfinite⟩ := Function.locallyFinsupp.locallyFiniteSupport c (q.base x')
  set I : Finset X := hVfinite.toFinset with hI
  set a : X → X' → ℤ := fun y z ↦ closedSubschemeCycleCoeff C sX'
    (((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({y} : Set X))).comap q).subschemeι) j z with ha
  have hloc : ∀ y ∈ I, ∃ t ∈ 𝓝 x', (t ∩ Function.support (a y)).Finite := fun y _ ↦
    closedSubschemeCycleCoeff_locallyFiniteSupport C sX'
      (((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({y} : Set X))).comap q).subschemeι) j x'
  choose! t ht hfin using hloc
  refine ⟨q.base ⁻¹' V ∩ ⋂ y ∈ I, t y,
    Filter.inter_mem (q.continuous.continuousAt hV)
      ((Filter.biInter_finset_mem I).2 ht), ?_⟩
  refine (Set.Finite.biUnion I.finite_toSet fun y hy ↦ hfin y hy).subset ?_
  intro z hz
  have hprod := mul_ne_zero_iff.1 (Function.mem_support.1 hz.2)
  have hmemI : q.base z ∈ I := (Set.Finite.mem_toFinset hVfinite).2 ⟨hz.1.1, hprod.1⟩
  exact Set.mem_biUnion hmemI ⟨Set.mem_iInter₂.1 hz.1.2 _ hmemI,
    Function.mem_support.2 hprod.2⟩

/-- The coefficient at `x'` of the base change of a cycle along a flat change of the base
scheme: the coefficient of the cycle at the image of `x'` in `X`, times the multiplicity of `x'`
in the inverse image of the reduced closure of that image. -/
def baseChangeCycleCoeff (B : FlatBaseChangeSituation.{u}) {X : Scheme.{u}} (f : X ⟶ B.base.S)
    [LocallyOfFiniteType f] (k : ℤ) (z : CycleGroup B.base f k)
    (x : (pullback f B.g : Scheme.{u})) : ℤ :=
  z.1 ((pullback.fst f B.g).base x) *
    flatPullbackWeight B.baseChange (pullback.snd f B.g) (pullback.fst f B.g) (k + B.c) x

/-- The coefficient function of the base change of a cycle has locally finite support. -/
theorem baseChangeCycleCoeff_locallyFiniteSupport (B : FlatBaseChangeSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ B.base.S) [LocallyOfFiniteType f] (k : ℤ)
    (z : CycleGroup B.base f k) :
    LocallyFiniteSupport (baseChangeCycleCoeff B f k z) :=
  locallyFiniteSupport_mul_flatPullbackWeight B.baseChange (pullback.snd f B.g)
    (pullback.fst f B.g) (k + B.c) z.1

/-- The base change of a `k`-cycle is a cycle of delta-dimension `k + c`. -/
theorem baseChangeCycleCoeff_mem_cyclesOfDimension (B : FlatBaseChangeSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ B.base.S) [LocallyOfFiniteType f] (k : ℤ)
    (z : CycleGroup B.base f k) :
    (⟨baseChangeCycleCoeff B f k z, fun _ _ ↦ trivial, fun x _ ↦
      baseChangeCycleCoeff_locallyFiniteSupport B f k z x⟩ :
        AlgebraicCycle (pullback f B.g : Scheme.{u}) ℤ) ∈
      cyclesOfDimension B.baseChange (pullback.snd f B.g) (k + B.c) := by
  rw [mem_cyclesOfDimension]
  intro Z hZ
  change baseChangeCycleCoeff B f k z Z.isIrreducible.genericPoint ≠ 0 at hZ
  have hcoeff := (mul_ne_zero_iff.1 hZ).2
  rw [deltaDimension_eq_of_isGenericPoint B.baseChange (pullback.snd f B.g) Z
    Z.isIrreducible.genericPoint (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed)]
  unfold flatPullbackWeight closedSubschemeCycleCoeff at hcoeff
  split at hcoeff
  next h => exact h.choose_spec.2
  next => contradiction

/-- The homomorphism `Z_k(X) ⟶ Z_{k+c}(X ×_S S')` of cycle groups induced by a flat change of
the base scheme with dimension shift `c`. -/
def baseChangeCyclePullback (B : FlatBaseChangeSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ B.base.S) [LocallyOfFiniteType f] (k : ℤ) :
    CycleGroup B.base f k →+ CycleGroup B.baseChange (pullback.snd f B.g) (k + B.c) where
  toFun z := ⟨⟨baseChangeCycleCoeff B f k z, fun _ _ ↦ trivial, fun x _ ↦
      baseChangeCycleCoeff_locallyFiniteSupport B f k z x⟩,
      baseChangeCycleCoeff_mem_cyclesOfDimension B f k z⟩
  map_zero' := by
    apply Subtype.ext
    ext x
    change baseChangeCycleCoeff B f k 0 x = 0
    simp [baseChangeCycleCoeff]
  map_add' z z' := by
    apply Subtype.ext
    ext x
    change baseChangeCycleCoeff B f k (z + z') x =
      baseChangeCycleCoeff B f k z x + baseChangeCycleCoeff B f k z' x
    simp [baseChangeCycleCoeff, add_mul]

/-- The coefficient formula for the base change of a cycle. -/
@[simp]
theorem baseChangeCyclePullback_apply (B : FlatBaseChangeSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ B.base.S) [LocallyOfFiniteType f] (k : ℤ) (z : CycleGroup B.base f k)
    (x : (pullback f B.g : Scheme.{u})) :
    (baseChangeCyclePullback B f k z).1 x =
      z.1 ((pullback.fst f B.g).base x) *
        flatPullbackWeight B.baseChange (pullback.snd f B.g) (pullback.fst f B.g) (k + B.c) x :=
  rfl

end Stacks.Chow

end
