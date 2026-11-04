module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.ChowGroups
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.ClosedSubschemeCycleRules
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.Dimension
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductAssociativity
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.Cycles
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.GeneralRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InverseImageDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.BaseChange
public import StacksCore.Tactic.StacksAttribute

/-!
# Flat pullback commutes with a change of the base scheme

Let `B` be a flat base change of Chow situations with dimension shift `c`, that is a flat
morphism `g : S' ⟶ S` of the two bases whose dimension functions differ by `c` on the generic
points of the fibres of `g`. Let `Y ⟶ X ⟶ S` be locally of finite type with `f : Y ⟶ X` flat of
relative dimension `r`, and let `X' = X ×_S S'`, `Y' = Y ×_S S'` and `f' : Y' ⟶ X'` be the base
changes. Stacks 0FVK says that `f'` is again flat of relative dimension `r` and that the two
squares

```
Z_{k+r}(Y) --g^*--> Z_{k+c+r}(Y')        A_{k+r}(Y) --g^*--> A_{k+c+r}(Y')
    ^ f^*               ^ (f')^*              ^ f^*              ^ (f')^*
Z_k(X)     --g^*--> Z_{k+c}(X')          A_k(X)     --g^*--> A_{k+c}(X')
```

commute. As the source says, it suffices to treat the first square; the second is its image
under the quotient maps.

## Main definitions

* `Stacks.Chow.FlatPullbackClosedSubschemeCycleRule` — Stacks 02RE, part (1), cycle identity, as
  a predicate; it holds, by
  `Stacks.Chow.flatPullbackClosedSubschemeCycleRule_holds`.
* `Stacks.Chow.BaseChangeClosedSubschemeCycleRule` — Stacks 0FVI, part (1), cycle identity, as a
  predicate; it holds, by `Stacks.Chow.baseChangeClosedSubschemeCycleRule_holds`.

## Main results

* `Stacks.Chow.flat_relativeDimension_baseChange` — **Stacks 0FVK**, the base change of a flat
  morphism of relative dimension `r` is again flat of relative dimension `r`.
* `Stacks.Chow.baseChangeCyclePullback_flatPullback_apply` — the two paths around the square of
  cycle groups have the same coefficient at every point of `Y'`.
* `Stacks.Chow.baseChange_flatPullback_cycles` — **Stacks 0FVK**, the square of cycle groups
  commutes.
* `Stacks.Chow.baseChange_flatPullback_chow` — **Stacks 0FVK**, the square of Chow groups
  commutes.

## Implementation notes

### The parameters threaded, and why

* The base-changed morphism is taken as a parameter `f' : Y' ⟶ X'` subject only to the two
  compatibilities `pullback.fst sY B.g ≫ f = f' ≫ pullback.fst sX B.g` and
  `f' ≫ pullback.snd sX B.g = pullback.snd sY B.g`, together with its flatness, its local
  finite type and its relative dimension. This is a generalization of the source, which takes
  `f'` to be the base change: the cartesian square is never used, only its commutativity, and
  the three properties of `f'` are exactly what
  `Stacks.Chow.flat_relativeDimension_baseChange` supplies for the base change itself. The same
  device is used for the morphism `g` of Stacks 0B6Y in
  `StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullback`.
* Stacks 02RE, part (1), cycle identity — that the flat pullback of the fundamental cycle of a
  closed subscheme of delta-dimension at most `k` is the fundamental cycle of its
  scheme-theoretic inverse image — is needed below for the base change of an integral closed
  subscheme, which is neither integral nor of exactly the expected delta-dimension, so
  `Stacks.Chow.flatPullback_cycleAssociatedToClosedSubscheme` does not apply directly.
  The general statement is
  `Stacks.Chow.flatPullback_cycleAssociatedToClosedSubscheme_of_le`, proved from the flat base
  change `f^*(i_* 𝒪_Z) ≅ (pullback.snd i f)_* 𝒪_{Z ×_X X'}` of
  `Stacks.Chow.pullbackPushforwardStructureSheafIso_of_flat` together with Stacks 02QY and
  Stacks 02RE part (2); no decomposition into components is needed.
* Stacks 0FVI, part (1), cycle identity, is
  `Stacks.Chow.baseChangeCyclePullback_cycleAssociatedToClosedSubscheme`, and
  `Stacks.Chow.baseChangeCyclePullback_cycleAssociatedToClosedSubscheme_fst` is that statement
  read through the symmetry of the pullback, in the presentation the squares below use.
* For the square of Chow groups, Stacks 02S1 along `f` and along `f'` is
  `Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general`, and Stacks 0FVJ over `X`
  and over `Y` is `Stacks.Chow.baseChangeFactorsThroughRationalEquivalence`. Those four facts
  *are* the existence of the four maps in the square, and all four are proved, so both squares
  below are unconditional.

### Why the two squares are stated with `HEq`

The two paths around the square land in cycle groups of degree `(k + r) + c` and `(k + c) + r`.
These integers are equal but not syntactically so, hence the two composites have equal but not
syntactically equal types, and their equality is heterogeneous. The content is the coefficient
identity `Stacks.Chow.baseChangeCyclePullback_flatPullback_apply`, which is homogeneous because
a coefficient is an integer; the `HEq` statements transport it.

### The reduction to an integral closed subscheme

A coefficient of either composite is the coefficient of the cycle at a point `y` of `X` times a
product of two multiplicities, and the multiplicities do not depend on the cycle. So it suffices
to compare the two paths on the fundamental cycle of the reduced closure of `y`, whose
coefficient at `y` is one; that cycle is integral of delta-dimension `k` whenever `y` carries a
nonzero coefficient of a `k`-cycle. On it, each path is computed by one of the two hypotheses
above together with one dimension bound, and the two answers are the fundamental cycles of two
presentations `Y' ×_{X'} (X' ×_X Z)` and `(Y ×_X Z) ×_Y Y'` of one closed subscheme of `Y'`,
identified by `CategoryTheory.Limits.pullbackRightPullbackFstIso` twice and the commutativity of
the square.

## References

* [Stacks Project, Tag 0FVK](https://stacks.math.columbia.edu/tag/0FVK)
* [Stacks Project, Tag 0FVG](https://stacks.math.columbia.edu/tag/0FVG)
* [Stacks Project, Tag 0FVI](https://stacks.math.columbia.edu/tag/0FVI)
* [Stacks Project, Tag 0FVJ](https://stacks.math.columbia.edu/tag/0FVJ)
* [Stacks Project, Tag 02NK](https://stacks.math.columbia.edu/tag/02NK)
* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
* [Stacks Project, Tag 02RE](https://stacks.math.columbia.edu/tag/02RE)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The base-changed morphism -/

/-- **Stacks 0FVK.** In a flat base-change situation, the base change of a morphism locally of
finite type and flat of relative dimension `r` is again locally of finite type and flat of
relative dimension `r`.

Flatness and local finite type are stable under base change, and the relative dimension is
Stacks 02NK. -/
@[stacks 0FVK "flatness and relative dimension of the base-changed morphism"]
theorem flat_relativeDimension_baseChange (B : FlatBaseChangeSituation.{u}) {Y X : Scheme.{u}}
    (sY : Y ⟶ B.base.S) (sX : X ⟶ B.base.S) (f : Y ⟶ X) [LocallyOfFiniteType f] [Flat f]
    (f' : (pullback sY B.g : Scheme.{u}) ⟶ (pullback sX B.g : Scheme.{u}))
    (hsq : IsPullback (pullback.fst sY B.g) f' f (pullback.fst sX B.g))
    (r : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r) :
    letI : LocallyOfFiniteType f' :=
      MorphismProperty.of_isPullback hsq (P := @LocallyOfFiniteType) inferInstance
    Flat f' ∧ AlgebraicGeometry.RelativeDimension f' r :=
  have : LocallyOfFiniteType f' :=
    MorphismProperty.of_isPullback hsq (P := @LocallyOfFiniteType) inferInstance
  ⟨MorphismProperty.of_isPullback hsq (P := @Flat) inferInstance,
    AlgebraicGeometry.RelativeDimension.of_isPullback hsq hf⟩

/-! ### The two closed-subscheme cycle identities -/

/-- **Stacks 02RE, part (1), cycle identity.** The assertion that the flat pullback of the
fundamental `k`-cycle of a closed subscheme `Z ⊆ X` of delta-dimension at most `k` is the
fundamental `(k+r)`-cycle of the scheme-theoretic inverse image `X' ×_X Z`.

This is named as a predicate so that the two cycle squares below can be stated once and applied
at each delta-dimension, and it holds: `Stacks.Chow.flatPullbackClosedSubschemeCycleRule_holds`
proves it, from the tagged statement of the identity,
`Stacks.Chow.flatPullback_cycleAssociatedToClosedSubscheme_of_le`. -/
def FlatPullbackClosedSubschemeCycleRule (C : ChowSituation.{u}) {X' X : Scheme.{u}}
    (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (f : X' ⟶ X) [LocallyOfFiniteType f] [Flat f] (hbase : f ≫ sX = sX') (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ) : Prop :=
  ∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i],
    schemeDeltaDimension C (i ≫ sX) ≤ (k : EInt) →
      flatPullback C sX' sX f hbase r hf k (cycleAssociatedToClosedSubscheme C sX i k) =
        cycleAssociatedToClosedSubscheme C sX' (pullback.fst f i) (k + (r : ℤ))

/-- **Stacks 0FVI, part (1), cycle identity.** The assertion that the base change of the
fundamental `k`-cycle of a closed subscheme `Z ⊆ X` of delta-dimension at most `k` is the
fundamental `(k+c)`-cycle of the base change `Z ×_X X'`.

This is named as a predicate so that the cycle squares below can be stated once, and it holds:
`Stacks.Chow.baseChangeClosedSubschemeCycleRule_holds` proves it, from the dimension bound
`Stacks.Chow.schemeDeltaDimension_baseChange_closedSubscheme_le` together with the
identification of the base-changed structure sheaf. -/
def BaseChangeClosedSubschemeCycleRule (B : FlatBaseChangeSituation.{u}) : Prop :=
  ∀ {X Z : Scheme.{u}} (f : X ⟶ B.base.S) [LocallyOfFiniteType f] (i : Z ⟶ X)
      [IsClosedImmersion i] (k : ℤ),
    schemeDeltaDimension B.base (i ≫ f) ≤ (k : EInt) →
      baseChangeCyclePullback B f k (cycleAssociatedToClosedSubscheme B.base f i k) =
        cycleAssociatedToClosedSubscheme B.baseChange (pullback.snd f B.g)
          (pullback.fst (pullback.fst f B.g) i) (k + B.c)

/-- **Stacks 02RE, part (1), cycle identity.** The flat pullback of the fundamental `k`-cycle of
a closed subscheme of delta-dimension at most `k` is the fundamental `(k+r)`-cycle of its
scheme-theoretic inverse image.

This inhabits `Stacks.Chow.FlatPullbackClosedSubschemeCycleRule`, so that predicate is a
theorem rather than a hypothesis; it is
`Stacks.Chow.flatPullback_cycleAssociatedToClosedSubscheme_of_le`. -/
theorem flatPullbackClosedSubschemeCycleRule_holds (C : ChowSituation.{u}) {X' X : Scheme.{u}}
    (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (f : X' ⟶ X) [LocallyOfFiniteType f] [Flat f] (hbase : f ≫ sX = sX') (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ) :
    FlatPullbackClosedSubschemeCycleRule C sX' sX f hbase r hf k := by
  intro Z i _ hZ
  exact flatPullback_cycleAssociatedToClosedSubscheme_of_le C sX' sX f hbase r hf i k hZ

/-- **Stacks 0FVI, part (1), cycle identity.** The base change of the fundamental `k`-cycle of a
closed subscheme of delta-dimension at most `k` is the fundamental `(k+c)`-cycle of its base
change.

This inhabits `Stacks.Chow.BaseChangeClosedSubschemeCycleRule`, so that predicate is a theorem
rather than a hypothesis; it is
`Stacks.Chow.baseChangeCyclePullback_cycleAssociatedToClosedSubscheme_fst`. -/
theorem baseChangeClosedSubschemeCycleRule_holds (B : FlatBaseChangeSituation.{u}) :
    BaseChangeClosedSubschemeCycleRule B := by
  intro X Z f _ i _ k hZ
  exact baseChangeCyclePullback_cycleAssociatedToClosedSubscheme_fst B f i k hZ

/-! ### The square on the fundamental cycle of an integral closed subscheme -/

/-- The two closed subschemes `(Y ×_X Z) ×_Y Y'` and `Y' ×_{X'} (X' ×_X Z)` of `Y'` have the same
cycle coefficients: pasting pullbacks identifies each of them with `Y' ×_X Z`, and the
commutativity of the square relating `f` and `f'` matches the two identifications. -/
private theorem closedSubschemeCycleCoeff_baseChange_flatPullback_comm
    (B : FlatBaseChangeSituation.{u}) {Y X Z : Scheme.{u}}
    (sY : Y ⟶ B.base.S) [LocallyOfFiniteType sY] (sX : X ⟶ B.base.S) [LocallyOfFiniteType sX]
    (f : Y ⟶ X) (f' : (pullback sY B.g : Scheme.{u}) ⟶ (pullback sX B.g : Scheme.{u}))
    (hcomm : pullback.fst sY B.g ≫ f = f' ≫ pullback.fst sX B.g)
    (i : Z ⟶ X) [IsClosedImmersion i] (j : ℤ) (x : (pullback sY B.g : Scheme.{u})) :
    closedSubschemeCycleCoeff B.baseChange (pullback.snd sY B.g)
        (pullback.fst (pullback.fst sY B.g) (pullback.fst f i)) j x =
      closedSubschemeCycleCoeff B.baseChange (pullback.snd sY B.g)
        (pullback.fst f' (pullback.fst (pullback.fst sX B.g) i)) j x := by
  let eQ := pullbackRightPullbackFstIso f i (pullback.fst sY B.g)
  let eP := pullbackRightPullbackFstIso (pullback.fst sX B.g) i f'
  let eC : pullback (pullback.fst sY B.g ≫ f) i ≅ pullback (f' ≫ pullback.fst sX B.g) i :=
    pullback.congrHom hcomm rfl
  let e : pullback f' (pullback.fst (pullback.fst sX B.g) i) ≅
      pullback (pullback.fst sY B.g) (pullback.fst f i) := eP.trans (eC.symm.trans eQ.symm)
  have heC : eC.inv ≫ pullback.fst (pullback.fst sY B.g ≫ f) i =
      pullback.fst (f' ≫ pullback.fst sX B.g) i := by
    dsimp [eC]
    rw [pullback.congrHom_inv, pullback.lift_fst]
    rfl
  have hecomp : e.hom ≫ pullback.fst (pullback.fst sY B.g) (pullback.fst f i) =
      pullback.fst f' (pullback.fst (pullback.fst sX B.g) i) := by
    calc
      e.hom ≫ pullback.fst (pullback.fst sY B.g) (pullback.fst f i) =
          eP.hom ≫ eC.inv ≫ eQ.inv ≫
            pullback.fst (pullback.fst sY B.g) (pullback.fst f i) := by
            simp [e, Category.assoc]
      _ = eP.hom ≫ eC.inv ≫ pullback.fst (pullback.fst sY B.g ≫ f) i := by
            rw [pullbackRightPullbackFstIso_inv_fst]
      _ = eP.hom ≫ pullback.fst (f' ≫ pullback.fst sX B.g) i := by rw [heC]
      _ = pullback.fst f' (pullback.fst (pullback.fst sX B.g) i) := by simp [eP]
  exact (closedSubschemeCycleCoeff_eq_of_iso B.baseChange (pullback.snd sY B.g)
    (pullback.fst f' (pullback.fst (pullback.fst sX B.g) i))
    (pullback.fst (pullback.fst sY B.g) (pullback.fst f i)) e hecomp j x).symm

/-- The square of cycle groups commutes on the fundamental cycle of an integral closed subscheme
`Z ⊆ X` of delta-dimension `k`: each path turns it into the fundamental cycle of a presentation
of `Y' ×_X Z`. -/
private theorem baseChangeCyclePullback_flatPullback_integral
    (B : FlatBaseChangeSituation.{u}) {Y X Z : Scheme.{u}}
    (sY : Y ⟶ B.base.S) [LocallyOfFiniteType sY] (sX : X ⟶ B.base.S) [LocallyOfFiniteType sX]
    (f : Y ⟶ X) [LocallyOfFiniteType f] [Flat f] (hbase : f ≫ sX = sY)
    (f' : (pullback sY B.g : Scheme.{u}) ⟶ (pullback sX B.g : Scheme.{u}))
    [LocallyOfFiniteType f'] [Flat f']
    (hbase' : f' ≫ pullback.snd sX B.g = pullback.snd sY B.g)
    (hcomm : pullback.fst sY B.g ≫ f = f' ≫ pullback.fst sX B.g)
    (r : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r)
    (hf' : AlgebraicGeometry.RelativeDimension f' r) (k : ℤ)
    (hbc : BaseChangeClosedSubschemeCycleRule B)
    (hfp : FlatPullbackClosedSubschemeCycleRule B.baseChange (pullback.snd sY B.g)
      (pullback.snd sX B.g) f' hbase' r hf' (k + B.c))
    (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (hZ : schemeDeltaDimension B.base (i ≫ sX) = (k : EInt))
    (x : (pullback sY B.g : Scheme.{u})) :
    (baseChangeCyclePullback B sY (k + (r : ℤ))
        (flatPullback B.base sY sX f hbase r hf k
          (cycleAssociatedToClosedSubscheme B.base sX i k))).1 x =
      (flatPullback B.baseChange (pullback.snd sY B.g) (pullback.snd sX B.g) f' hbase' r hf'
        (k + B.c) (baseChangeCyclePullback B sX k
          (cycleAssociatedToClosedSubscheme B.base sX i k))).1 x := by
  have hidx : k + (r : ℤ) + B.c = k + B.c + (r : ℤ) := by omega
  rw [flatPullback_cycleAssociatedToClosedSubscheme B.base sY sX f hbase r hf k i hZ,
    hbc sY (pullback.fst f i) (k + (r : ℤ))
      (schemeDeltaDimension_pullback_le B.base sY sX f hbase r hf i k (le_of_eq hZ)),
    hbc sX i k (le_of_eq hZ),
    hfp (pullback.fst (pullback.fst sX B.g) i)
      (schemeDeltaDimension_baseChange_closedSubscheme_fst_le B sX i (le_of_eq hZ)),
    hidx]
  exact closedSubschemeCycleCoeff_baseChange_flatPullback_comm B sY sX f f' hcomm i _ x

/-! ### The square of cycle groups -/

/-- The two paths around the square of cycle groups have the same coefficient at every point of
`Y'`: both are the coefficient of the cycle at the image point of `X`, times the flat-pullback
multiplicity along `f` or `f'`, times the one along the projection of a base change. Those
multiplicities do not involve the cycle, so the identity follows from its case on the
fundamental cycle of the reduced closure of the image point. -/
theorem baseChangeCyclePullback_flatPullback_apply
    (B : FlatBaseChangeSituation.{u}) {Y X : Scheme.{u}}
    (sY : Y ⟶ B.base.S) [LocallyOfFiniteType sY] (sX : X ⟶ B.base.S) [LocallyOfFiniteType sX]
    (f : Y ⟶ X) [LocallyOfFiniteType f] [Flat f] (hbase : f ≫ sX = sY)
    (f' : (pullback sY B.g : Scheme.{u}) ⟶ (pullback sX B.g : Scheme.{u}))
    [LocallyOfFiniteType f'] [Flat f']
    (hbase' : f' ≫ pullback.snd sX B.g = pullback.snd sY B.g)
    (hcomm : pullback.fst sY B.g ≫ f = f' ≫ pullback.fst sX B.g)
    (r : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r)
    (hf' : AlgebraicGeometry.RelativeDimension f' r) (k : ℤ)
    (hbc : BaseChangeClosedSubschemeCycleRule B)
    (hfp : FlatPullbackClosedSubschemeCycleRule B.baseChange (pullback.snd sY B.g)
      (pullback.snd sX B.g) f' hbase' r hf' (k + B.c))
    (z : CycleGroup B.base sX k) (x : (pullback sY B.g : Scheme.{u})) :
    (baseChangeCyclePullback B sY (k + (r : ℤ))
        (flatPullback B.base sY sX f hbase r hf k z)).1 x =
      (flatPullback B.baseChange (pullback.snd sY B.g) (pullback.snd sX B.g) f' hbase' r hf'
        (k + B.c) (baseChangeCyclePullback B sX k z)).1 x := by
  have hxy : f ((pullback.fst sY B.g) x) = (pullback.fst sX B.g) (f' x) :=
    congrArg (fun m : (pullback sY B.g : Scheme.{u}) ⟶ X ↦ m x) hcomm
  simp only [baseChangeCyclePullback_apply, flatPullback_apply]
  by_cases hz : z.1 (f ((pullback.fst sY B.g) x)) = 0
  · rw [← hxy, hz]
    ring
  · let _ : IsIntegral (integralComponentAt (f ((pullback.fst sY B.g) x))).subscheme :=
      isIntegral_integralComponentAt _
    have hZ : schemeDeltaDimension B.base
        ((integralComponentAt (f ((pullback.fst sY B.g) x))).subschemeι ≫ sX) = (k : EInt) := by
      rw [schemeDeltaDimension_integralComponentAt B.base sX]
      exact congrArg (fun n : ℤ ↦ (n : EInt))
        ((mem_cyclesOfDimension_iff_forall_point B.base sX k z.1).1 z.2 _ hz)
    have hone : (cycleAssociatedToClosedSubscheme B.base sX
        (integralComponentAt (f ((pullback.fst sY B.g) x))).subschemeι k).1
          (f ((pullback.fst sY B.g) x)) = 1 := by
      have h := cycleAssociatedToClosedSubscheme_integral_apply B.base sX
        (integralComponentAt (f ((pullback.fst sY B.g) x)))
        (isIntegral_integralComponentAt _) hZ
      rwa [genericPointOf_integralComponentAt] at h
    have hsq := baseChangeCyclePullback_flatPullback_integral B sY sX f hbase f' hbase' hcomm
      r hf hf' k hbc hfp (integralComponentAt (f ((pullback.fst sY B.g) x))).subschemeι hZ x
    simp only [baseChangeCyclePullback_apply, flatPullback_apply] at hsq
    rw [← hxy, hone] at hsq
    simp only [one_mul] at hsq
    rw [← hxy]
    calc
      z.1 (f ((pullback.fst sY B.g) x)) *
            flatPullbackWeight B.base sY f (k + (r : ℤ)) ((pullback.fst sY B.g) x) *
            flatPullbackWeight B.baseChange (pullback.snd sY B.g) (pullback.fst sY B.g)
              (k + (r : ℤ) + B.c) x =
          z.1 (f ((pullback.fst sY B.g) x)) *
            (flatPullbackWeight B.base sY f (k + (r : ℤ)) ((pullback.fst sY B.g) x) *
              flatPullbackWeight B.baseChange (pullback.snd sY B.g) (pullback.fst sY B.g)
                (k + (r : ℤ) + B.c) x) := by ring
      _ = z.1 (f ((pullback.fst sY B.g) x)) *
            (flatPullbackWeight B.baseChange (pullback.snd sX B.g) (pullback.fst sX B.g)
                (k + B.c) (f' x) *
              flatPullbackWeight B.baseChange (pullback.snd sY B.g) f'
                (k + B.c + (r : ℤ)) x) := by rw [hsq]
      _ = _ := by ring

/-! ### Transporting along the equality `(k + r) + c = (k + c) + r` -/

/-- A homomorphism transported along an equality of target degrees acts by transporting its
values. -/
private theorem castAddMonoidHom_apply {A : Type u} {M : ℤ → Type u} [AddCommGroup A]
    [∀ n, AddCommGroup (M n)] {i j : ℤ} (h : i = j) (φ : A →+ M i) (a : A) :
    (cast (congrArg (fun n ↦ A →+ M n) h) φ) a = cast (congrArg M h) (φ a) := by
  cases h
  rfl

/-- The coefficient function of a cycle is unchanged by transport along an equality of
degrees. -/
private theorem castCycleGroup_apply (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] {i j : ℤ} (h : i = j) (α : CycleGroup C p i) (x : X) :
    (cast (congrArg (fun n ↦ CycleGroup C p n) h) α).1 x = α.1 x := by
  cases h
  rfl

/-- Two cycles of equal degrees with the same coefficients are identified by the transport along
that equality. -/
private theorem cast_cycleGroup_eq (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] {i j : ℤ} (h : i = j) (α : CycleGroup C p i) (β : CycleGroup C p j)
    (hab : ∀ x : X, α.1 x = β.1 x) :
    cast (congrArg (fun n ↦ CycleGroup C p n) h) α = β :=
  Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦
    (castCycleGroup_apply C p h α x).trans (hab x))

/-- Transport along an equality of degrees commutes with passing to a quotient. -/
private theorem castQuotientMk {A : ℤ → Type u} [∀ n, AddCommGroup (A n)]
    (N : ∀ n, AddSubgroup (A n)) {i j : ℤ} (h : i = j) (α : A i) :
    cast (congrArg (fun n ↦ A n ⧸ N n) h) (QuotientAddGroup.mk α) =
      QuotientAddGroup.mk (cast (congrArg A h) α) := by
  cases h
  rfl

/-! ### The two commuting squares -/

/-- The coefficient identity of `Stacks.Chow.baseChangeCyclePullback_flatPullback_apply`, with the
two cycle-rule hypotheses discharged. -/
private theorem baseChangeCyclePullback_flatPullback_coeff
    (B : FlatBaseChangeSituation.{u}) {Y X : Scheme.{u}}
    (sY : Y ⟶ B.base.S) [LocallyOfFiniteType sY] (sX : X ⟶ B.base.S) [LocallyOfFiniteType sX]
    (f : Y ⟶ X) [LocallyOfFiniteType f] [Flat f] (hbase : f ≫ sX = sY)
    (f' : (pullback sY B.g : Scheme.{u}) ⟶ (pullback sX B.g : Scheme.{u}))
    [LocallyOfFiniteType f'] [Flat f']
    (hbase' : f' ≫ pullback.snd sX B.g = pullback.snd sY B.g)
    (hcomm : pullback.fst sY B.g ≫ f = f' ≫ pullback.fst sX B.g)
    (r : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r)
    (hf' : AlgebraicGeometry.RelativeDimension f' r) (k : ℤ)
    (z : CycleGroup B.base sX k) (x : (pullback sY B.g : Scheme.{u})) :
    (baseChangeCyclePullback B sY (k + (r : ℤ))
        (flatPullback B.base sY sX f hbase r hf k z)).1 x =
      (flatPullback B.baseChange (pullback.snd sY B.g) (pullback.snd sX B.g) f' hbase' r hf'
        (k + B.c) (baseChangeCyclePullback B sX k z)).1 x :=
  baseChangeCyclePullback_flatPullback_apply B sY sX f hbase f' hbase' hcomm r hf hf' k
    (baseChangeClosedSubschemeCycleRule_holds B)
    (flatPullbackClosedSubschemeCycleRule_holds B.baseChange (pullback.snd sY B.g)
      (pullback.snd sX B.g) f' hbase' r hf' (k + B.c)) z x

/-- **Stacks 0FVK.** The square of cycle groups commutes: base change after flat pullback is
flat pullback after base change, as homomorphisms `Z_k(X) ⟶ Z_{k+c+r}(Y')`.

The two composites land in cycle groups of degree `(k + r) + c` and `(k + c) + r`, so the
statement is heterogeneous; its content is the coefficient identity
`Stacks.Chow.baseChangeCyclePullback_flatPullback_apply`. -/
@[stacks 0FVK "commuting diagram of cycle groups"]
theorem baseChange_flatPullback_cycles
    (B : FlatBaseChangeSituation.{u}) {Y X : Scheme.{u}}
    (sY : Y ⟶ B.base.S) [LocallyOfFiniteType sY] (sX : X ⟶ B.base.S) [LocallyOfFiniteType sX]
    (f : Y ⟶ X) [LocallyOfFiniteType f] [Flat f] (hbase : f ≫ sX = sY)
    (f' : (pullback sY B.g : Scheme.{u}) ⟶ (pullback sX B.g : Scheme.{u}))
    [LocallyOfFiniteType f'] [Flat f']
    (hbase' : f' ≫ pullback.snd sX B.g = pullback.snd sY B.g)
    (hcomm : pullback.fst sY B.g ≫ f = f' ≫ pullback.fst sX B.g)
    (r : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r)
    (hf' : AlgebraicGeometry.RelativeDimension f' r) (k : ℤ) :
    HEq ((baseChangeCyclePullback B sY (k + (r : ℤ))).comp
          (flatPullback B.base sY sX f hbase r hf k))
      ((flatPullback B.baseChange (pullback.snd sY B.g) (pullback.snd sX B.g) f' hbase' r hf'
          (k + B.c)).comp (baseChangeCyclePullback B sX k)) := by
  have hidx : k + (r : ℤ) + B.c = k + B.c + (r : ℤ) := by omega
  refine heq_iff_exists_cast_eq.2 ⟨congrArg (fun n : ℤ ↦ CycleGroup B.base sX k →+
    CycleGroup B.baseChange (pullback.snd sY B.g) n) hidx, ?_⟩
  ext z x
  rw [castAddMonoidHom_apply hidx, castCycleGroup_apply _ _ hidx]
  exact baseChangeCyclePullback_flatPullback_coeff B sY sX f hbase f' hbase' hcomm r hf hf' k z x

/-- **Stacks 0FVK.** The square of Chow groups commutes: base change after flat pullback is flat
pullback after base change, as homomorphisms `A_k(X) ⟶ A_{k+c+r}(Y')`.

This is the image of `Stacks.Chow.baseChange_flatPullback_cycles` under the quotient maps, which
is why the source says it suffices to prove the square of cycle groups. -/
@[stacks 0FVK "commuting diagram of Chow groups"]
theorem baseChange_flatPullback_chow
    (B : FlatBaseChangeSituation.{u}) {Y X : Scheme.{u}}
    (sY : Y ⟶ B.base.S) [LocallyOfFiniteType sY] (sX : X ⟶ B.base.S) [LocallyOfFiniteType sX]
    (f : Y ⟶ X) [LocallyOfFiniteType f] [Flat f] (hbase : f ≫ sX = sY)
    (f' : (pullback sY B.g : Scheme.{u}) ⟶ (pullback sX B.g : Scheme.{u}))
    [LocallyOfFiniteType f'] [Flat f']
    (hbase' : f' ≫ pullback.snd sX B.g = pullback.snd sY B.g)
    (hcomm : pullback.fst sY B.g ≫ f = f' ≫ pullback.fst sX B.g)
    (r : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r)
    (hf' : AlgebraicGeometry.RelativeDimension f' r) (k : ℤ) :
    HEq ((flatBaseChangeChowPullback B sY (k + (r : ℤ))
            (baseChangeFactorsThroughRationalEquivalence B sY (k + (r : ℤ)))).comp
          (flatPullbackChow B.base sY sX f hbase r hf k
            (flatPullbackFactorsThroughRationalEquivalence_general B.base sY sX f hbase r hf k)))
      ((flatPullbackChow B.baseChange (pullback.snd sY B.g) (pullback.snd sX B.g) f' hbase' r hf'
          (k + B.c)
          (flatPullbackFactorsThroughRationalEquivalence_general B.baseChange
            (pullback.snd sY B.g) (pullback.snd sX B.g) f' hbase' r hf' (k + B.c))).comp
        (flatBaseChangeChowPullback B sX k
          (baseChangeFactorsThroughRationalEquivalence B sX k))) := by
  have hidx : k + (r : ℤ) + B.c = k + B.c + (r : ℤ) := by omega
  refine heq_iff_exists_cast_eq.2 ⟨congrArg (fun n : ℤ ↦ chowGroup B.base sX k →+
    chowGroup B.baseChange (pullback.snd sY B.g) n) hidx, ?_⟩
  ext z
  simp only [AddMonoidHom.comp_apply]
  rw [castAddMonoidHom_apply hidx]
  show cast (congrArg (fun n ↦ chowGroup B.baseChange (pullback.snd sY B.g) n) hidx)
      (QuotientAddGroup.mk ((baseChangeCyclePullback B sY (k + (r : ℤ)))
        (flatPullback B.base sY sX f hbase r hf k z))) =
    QuotientAddGroup.mk ((flatPullback B.baseChange (pullback.snd sY B.g)
      (pullback.snd sX B.g) f' hbase' r hf' (k + B.c)) ((baseChangeCyclePullback B sX k) z))
  rw [castQuotientMk (fun n ↦ rationalEquivalences B.baseChange (pullback.snd sY B.g) n) hidx,
    cast_cycleGroup_eq B.baseChange (pullback.snd sY B.g) hidx _ _
      (baseChangeCyclePullback_flatPullback_coeff B sY sX f hbase f' hbase' hcomm r hf hf' k z)]

end Stacks.Chow

end
