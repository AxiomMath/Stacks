module

public import StacksFrontier.AlgebraicGeometry.Crystalline.FiniteLevelTower
public import StacksFrontier.CategoryTheory.Sites.AbelianRestrictionExact

/-!
# Restriction of abelian sheaves to a finite crystalline level is exact

Continuing `StacksFrontier/AlgebraicGeometry/Crystalline/FiniteLevelTower.lean`, which builds the
restrictions `Crystalline.pAdicLevelSheafRestriction` of an abelian sheaf on `Cris(X/S)` to a
finite divided power level and `Crystalline.pAdicLevelStepSheafRestriction` between two finite
levels, this file records that both are **exact**.

Exactness is what lets a restriction functor be applied to a bounded below derived category at
all, so it is a structural prerequisite for the derived transition maps
`RΓ(Cris(X/S_e), F_e) ⟶ RΓ(Cris(X/S_m), F_m)` of [Stacks, Tag 07MV].  It is not the hard
ingredient of those maps; see "What is and is not proved".

Neither half is formal.  Left exactness holds for any continuous functor of sites, because limits
of sheaves are computed in presheaves and so pointwise.  Right exactness is where *co*continuity
enters: restriction along a cocontinuous functor commutes with sheafification, so it preserves
all colimits.  Both halves are
`CategoryTheory.Functor.exactFunctor_sheafPushforwardContinuous_of_isCocontinuous` of
`StacksFrontier/CategoryTheory/Sites/AbelianRestrictionExact.lean`; what this file supplies is the
cocontinuity of the two functors of levels, which is
`Crystalline.GlobalCrystallineSituation.smallChangeBase_isCocontinuous` in each case, exactly as
their continuity is `smallChangeBase_isContinuous`.

## Main results

* `Crystalline.pAdicLevelExtend_isCocontinuous` and
  `Crystalline.pAdicLevelStepExtend_isCocontinuous` — the two functors of finite levels are
  cocontinuous, the companions of `Crystalline.pAdicLevelExtend_isContinuous` and
  `Crystalline.pAdicLevelStepExtend_isContinuous`.
* `Crystalline.exactFunctor_pAdicLevelSheafRestriction` and
  `Crystalline.exactFunctor_pAdicLevelStepSheafRestriction` — **restriction of abelian sheaves to
  a finite level, and between two finite levels, is exact**, with
  `preservesFiniteLimits_*` and `preservesFiniteColimits_*` as the two halves in instance form.

## What is and is not proved

**No tag attribute is placed in this file**, and nothing here is [Stacks, Tag 07MV].

Nothing below proves the ingredient the derived transition maps of that remark really turn on:
that restriction to a finite level carries an *injective* abelian sheaf to one with acyclic
global sections.  That is the acyclicity hypothesis of
`Crystalline.GlobalCrystallineSituation.SmallSite.derivedGlobalSectionsCompIso`
([Stacks, Tag 015M]), it is the first half of the remark's own hint, and exactness does not give
it: exactness bounds the higher derived functors of the restriction itself, whereas the
hypothesis is about the higher *cohomology on the smaller site* of the restricted sheaf, which
exactness says nothing about.  Nothing below weakens or stands in for that hypothesis.

That ingredient is proved separately, in
`StacksFrontier/AlgebraicGeometry/Crystalline/FiniteLevelRestrictionInjectives.lean`, by a route
that does not pass through exactness of the restriction at all: both functors of levels are
change of divided power base, so the abelian lower shriek left adjoint to the restriction is
exact by [Stacks, Tag 00X4], and the restriction therefore preserves injectives outright.  The
tower's *arrows* are still missing; see that file for what remains.

## References

* [Stacks Project, Tag 07MV](https://stacks.math.columbia.edu/tag/07MV)
* [Stacks Project, Tag 07KL](https://stacks.math.columbia.edu/tag/07KL)
* [Stacks Project, Tag 04J4](https://stacks.math.columbia.edu/tag/04J4)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Crystalline

section Level

variable {A : Type u} [CommRing A] (I : Ideal A) (γ : DividedPowers I) (p : ℕ)
  [Fact p.Prime] [Algebra (DividedPowers.IntegersAtPrime p) A]

/-- **The functor `Cris(X/S_e) ⥤ Cris(X/S)` is cocontinuous.**  This is
`Crystalline.GlobalCrystallineSituation.smallChangeBase_isCocontinuous`, [Stacks, Tag 07KL], at
the pair `(S_e ⟶ S, 𝟙 X)`; it is the companion of
`Crystalline.pAdicLevelExtend_isContinuous`, and together with it makes restriction of abelian
sheaves to the level exact. -/
instance pAdicLevelExtend_isCocontinuous {e : ℕ} (he : IsPAdicLevel I γ p e) (X : Scheme.{u})
    (toCF : X ⟶ DividedPowerScheme.closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x)) :
    (pAdicLevelExtend I γ p he X toCF hX).IsCocontinuous
      (GlobalCrystallineSituation.smallTopology (pAdicLevelSituation I γ p he X toCF hX))
      (GlobalCrystallineSituation.smallTopology (specSituation I γ p X toCF hX)) :=
  GlobalCrystallineSituation.smallChangeBase_isCocontinuous

/-- **The transition functor `Cris(X/S_m) ⥤ Cris(X/S_e)` of the tower of finite levels is
cocontinuous**, the companion of `Crystalline.pAdicLevelStepExtend_isContinuous`. -/
instance pAdicLevelStepExtend_isCocontinuous {m e : ℕ} (hm : IsPAdicLevel I γ p m)
    (he : IsPAdicLevel I γ p e) (hme : m ≤ e) (X : Scheme.{u})
    (toCF : X ⟶ DividedPowerScheme.closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x)) :
    (pAdicLevelStepExtend I γ p hm he hme X toCF hX).IsCocontinuous
      (GlobalCrystallineSituation.smallTopology (pAdicLevelSituation I γ p hm X toCF hX))
      (GlobalCrystallineSituation.smallTopology (pAdicLevelSituation I γ p he X toCF hX)) :=
  GlobalCrystallineSituation.smallChangeBase_isCocontinuous

/-- **Restriction of abelian sheaves from `Cris(X/S)` to a finite level `Cris(X/S_e)` is
exact.**  Left exactness is continuity of `Crystalline.pAdicLevelExtend`, right exactness its
cocontinuity. -/
theorem exactFunctor_pAdicLevelSheafRestriction {e : ℕ} (he : IsPAdicLevel I γ p e)
    (X : Scheme.{u}) (toCF : X ⟶ DividedPowerScheme.closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x)) :
    exactFunctor _ _ (pAdicLevelSheafRestriction I γ p he X toCF hX) :=
  Functor.exactFunctor_sheafPushforwardContinuous_of_isCocontinuous _ _ _

/-- **Restriction of abelian sheaves between two finite levels `Cris(X/S_e) ⟶ Cris(X/S_m)` is
exact**, for `m ≤ e`.  This is the arrow of the tower of [Stacks, Tag 07MV] at the level of
abelian sheaves; exactness is what would let it act on bounded below derived categories. -/
theorem exactFunctor_pAdicLevelStepSheafRestriction {m e : ℕ} (hm : IsPAdicLevel I γ p m)
    (he : IsPAdicLevel I γ p e) (hme : m ≤ e) (X : Scheme.{u})
    (toCF : X ⟶ DividedPowerScheme.closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x)) :
    exactFunctor _ _ (pAdicLevelStepSheafRestriction I γ p hm he hme X toCF hX) :=
  Functor.exactFunctor_sheafPushforwardContinuous_of_isCocontinuous _ _ _

/-- Restriction of abelian sheaves to a finite level preserves finite limits. -/
instance preservesFiniteLimits_pAdicLevelSheafRestriction {e : ℕ} (he : IsPAdicLevel I γ p e)
    (X : Scheme.{u}) (toCF : X ⟶ DividedPowerScheme.closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x)) :
    PreservesFiniteLimits (pAdicLevelSheafRestriction I γ p he X toCF hX) :=
  ((exactFunctor_iff _).mp (exactFunctor_pAdicLevelSheafRestriction I γ p he X toCF hX)).1

/-- Restriction of abelian sheaves to a finite level preserves finite colimits. -/
instance preservesFiniteColimits_pAdicLevelSheafRestriction {e : ℕ} (he : IsPAdicLevel I γ p e)
    (X : Scheme.{u}) (toCF : X ⟶ DividedPowerScheme.closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x)) :
    PreservesFiniteColimits (pAdicLevelSheafRestriction I γ p he X toCF hX) :=
  ((exactFunctor_iff _).mp (exactFunctor_pAdicLevelSheafRestriction I γ p he X toCF hX)).2

/-- Restriction of abelian sheaves between two finite levels preserves finite limits. -/
instance preservesFiniteLimits_pAdicLevelStepSheafRestriction {m e : ℕ}
    (hm : IsPAdicLevel I γ p m) (he : IsPAdicLevel I γ p e) (hme : m ≤ e) (X : Scheme.{u})
    (toCF : X ⟶ DividedPowerScheme.closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x)) :
    PreservesFiniteLimits (pAdicLevelStepSheafRestriction I γ p hm he hme X toCF hX) :=
  ((exactFunctor_iff _).mp
    (exactFunctor_pAdicLevelStepSheafRestriction I γ p hm he hme X toCF hX)).1

/-- Restriction of abelian sheaves between two finite levels preserves finite colimits. -/
instance preservesFiniteColimits_pAdicLevelStepSheafRestriction {m e : ℕ}
    (hm : IsPAdicLevel I γ p m) (he : IsPAdicLevel I γ p e) (hme : m ≤ e) (X : Scheme.{u})
    (toCF : X ⟶ DividedPowerScheme.closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x)) :
    PreservesFiniteColimits (pAdicLevelStepSheafRestriction I γ p hm he hme X toCF hX) :=
  ((exactFunctor_iff _).mp
    (exactFunctor_pAdicLevelStepSheafRestriction I γ p hm he hme X toCF hX)).2

end Level

end Crystalline

end
