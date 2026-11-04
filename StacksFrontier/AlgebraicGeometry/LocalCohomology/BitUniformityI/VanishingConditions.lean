module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Seven vanishing conditions for a map of modules

Let `alpha : M ⟶ M'` be a map of modules, with chosen projective resolutions `p : P ⟶ M` and
`p' : P' ⟶ M'`. Fixing a degree `e`, there are seven conditions one may impose: that some lift
of `alpha` to the resolutions vanishes in all homological degrees above `e`, or only in degree
`e + 1`; that the maps `alpha` induces on `Ext` vanish above `e`, or only in degree `e + 1`;
that a canonical `Ext` class pulls back to zero; and the two corresponding `Tor` conditions.
This module records the conditions themselves.

## Main definitions

* `singleComplex`: a module viewed as a cochain complex in degree `0`.
* `IsResolutionLift`: a map of resolutions lifting a map of the resolved modules.
* `HasLiftVanishingAbove`, `HasLiftVanishingAtSucc`: conditions (1) and (2).
* `ExtMapVanishesAbove`, `ExtMapVanishesAtSucc`: conditions (3) and (4).
* `CanonicalExtClassPullbackVanishes`: condition (5).
* `TorMapVanishesAbove`, `TorMapVanishesAtSucc`: conditions (6) and (7).

## Implementation notes

Homological degree `i` in the source is cohomological degree `-i` in the chosen cochain
resolutions. Condition (5) is written using its canonical cocycle: the factorization of the
differential through its image. Saying that its pullback is a coboundary is precisely saying
that the canonical `Ext` class pulls back to zero. `Tor` is represented by Mathlib's `Tor'`,
which derives the first argument of the tensor product.

## References

* [Stacks Project, Tag 0G9V](https://stacks.math.columbia.edu/tag/0G9V)
-/

@[expose] public section

open CategoryTheory Limits

universe u

variable {R : Type u} [CommRing R]

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- A module viewed as a cochain complex concentrated in degree `0`. -/
noncomputable abbrev singleComplex (M : ModuleCat.{u} R) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M

/-- A map of resolutions lifts a given map of the resolved modules. -/
def IsResolutionLift {M M' : ModuleCat.{u} R}
    {P P' : CochainComplex (ModuleCat.{u} R) ℤ}
    (p : P ⟶ singleComplex M) (p' : P' ⟶ singleComplex M') (alpha : M ⟶ M')
    (a : P ⟶ P') : Prop :=
  a ≫ p' = p ≫ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map alpha

/-- Condition (1): there is a lift whose components in homological degrees above `e` vanish. -/
def HasLiftVanishingAbove {M M' : ModuleCat.{u} R}
    {P P' : CochainComplex (ModuleCat.{u} R) ℤ}
    (p : P ⟶ singleComplex M) (p' : P' ⟶ singleComplex M')
    (alpha : M ⟶ M') (e : ℕ) : Prop :=
  ∃ a : P ⟶ P', IsResolutionLift p p' alpha a ∧
    ∀ i : ℕ, e < i → a.f (-(i : ℤ)) = 0

/-- Condition (2): there is a lift whose component in homological degree `e + 1` vanishes. -/
def HasLiftVanishingAtSucc {M M' : ModuleCat.{u} R}
    {P P' : CochainComplex (ModuleCat.{u} R) ℤ}
    (p : P ⟶ singleComplex M) (p' : P' ⟶ singleComplex M')
    (alpha : M ⟶ M') (e : ℕ) : Prop :=
  ∃ a : P ⟶ P', IsResolutionLift p p' alpha a ∧
    a.f (-((e + 1 : ℕ) : ℤ)) = 0

/-- Condition (3): every map on Ext induced contravariantly by `alpha` vanishes above `e`. -/
def ExtMapVanishesAbove {M M' : ModuleCat.{u} R}
    (alpha : M ⟶ M') (e : ℕ) : Prop :=
  ∀ (N : ModuleCat.{u} R) (i : ℕ), e < i →
    ∀ x : Abelian.zExt M' N (i : ℤ),
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map alpha ≫ x = 0

/-- Condition (4): the map on Ext in degree `e + 1` induced by `alpha` vanishes. -/
def ExtMapVanishesAtSucc {M M' : ModuleCat.{u} R}
    (alpha : M ⟶ M') (e : ℕ) : Prop :=
  ∀ (N : ModuleCat.{u} R) (x : Abelian.zExt M' N ((e + 1 : ℕ) : ℤ)),
    (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map alpha ≫ x = 0

/-- Condition (5): the pullback of the canonical Ext class defined by the image of
`P'_{e+1} → P'_e` is zero. The displayed equality says that the pullback of its canonical
cocycle is a coboundary. -/
def CanonicalExtClassPullbackVanishes {M M' : ModuleCat.{u} R}
    {P P' : CochainComplex (ModuleCat.{u} R) ℤ}
    (p : P ⟶ singleComplex M) (p' : P' ⟶ singleComplex M')
    (alpha : M ⟶ M') (e : ℕ) : Prop :=
  ∃ (a : P ⟶ P')
      (phi : P.X (-(e : ℤ)) ⟶
        image (P'.d (-((e + 1 : ℕ) : ℤ)) (-(e : ℤ)))),
    IsResolutionLift p p' alpha a ∧
      a.f (-((e + 1 : ℕ) : ℤ)) ≫
          factorThruImage (P'.d (-((e + 1 : ℕ) : ℤ)) (-(e : ℤ))) =
        P.d (-((e + 1 : ℕ) : ℤ)) (-(e : ℤ)) ≫ phi

/-- Condition (6): every map on Tor induced covariantly by `alpha` vanishes above `e`. -/
def TorMapVanishesAbove {M M' : ModuleCat.{u} R}
    (alpha : M ⟶ M') (e : ℕ) : Prop :=
  ∀ (N : ModuleCat.{u} R) (i : ℕ), e < i →
    ((Tor' (ModuleCat.{u} R) i).map alpha).app N = 0

/-- Condition (7): the map on Tor in degree `e + 1` induced by `alpha` vanishes. -/
def TorMapVanishesAtSucc {M M' : ModuleCat.{u} R}
    (alpha : M ⟶ M') (e : ℕ) : Prop :=
  ∀ N : ModuleCat.{u} R, ((Tor' (ModuleCat.{u} R) (e + 1)).map alpha).app N = 0

end
