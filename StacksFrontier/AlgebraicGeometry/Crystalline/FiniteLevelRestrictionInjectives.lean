module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import StacksFrontier.AlgebraicGeometry.Crystalline.FiniteLevelRestrictionExact
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Formula07MKInjectives

/-!
# Restriction to a finite crystalline level carries injectives to acyclic sheaves

Continuing `StacksFrontier/AlgebraicGeometry/Crystalline/FiniteLevelRestrictionExact.lean`, which
proved that the restrictions `Crystalline.pAdicLevelSheafRestriction` and
`Crystalline.pAdicLevelStepSheafRestriction` of abelian sheaves to a finite divided power level
are exact, this file supplies the ingredient that file explicitly did **not** have, and which
exactness does not give: that these restrictions carry an *injective* abelian sheaf to one whose
global sections are acyclic.

This is the first half of the hint of [Stacks, Tag 07MV], and it is the hypothesis `hg` of
`Crystalline.GlobalCrystallineSituation.SmallSite.derivedGlobalSectionsCompIso`
([Stacks, Tag 015M]).

## Why exactness is not enough, and what replaces it

Exactness of a restriction functor `ρ` bounds the higher derived functors of `ρ` itself; the
hypothesis here is about the higher cohomology, on the *smaller* site, of the sheaf `ρ F`, which
exactness says nothing about.  The route the source takes — `ρ` preserves injectives because its
left adjoint is exact — needs the left adjoint `Functor.sheafPullback` to preserve
monomorphisms, and Mathlib supplies that only under `[RepresentablyFlat]` together with
`[PreservesFiniteLimits _.op.lan]`, neither of which is available for `pAdicLevelExtend`.

**At abelian coefficients neither is needed.**  The lower shriek along any continuous functor of
sites is exact on sheaves of abelian groups as soon as the source site has fibre products and
equalizers which the functor preserves — [Stacks, Tag 00X4], formalized as
`Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits`.  Both finite level functors are change
of divided power base, `Crystalline.GlobalCrystallineSituation.smallChangeBase` at the pairs
`(S_e ⟶ S, 𝟙 X)` and `(S_m ⟶ S_e, 𝟙 X)`, and that criterion has already been discharged for
change of base in full generality:
`...SmallSite.preservesFiniteLimits_smallChangeBaseAbelianLowerShriek` and
`...SmallSite.preservesInjectiveObjects_smallChangeBaseAbelianRestriction` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/Formula07MKInjectives.lean`.  So the two
restrictions of levels preserve injectives *on the nose*, not merely up to acyclicity, and the
acyclicity hypothesis follows because an injective object is right acyclic for every additive
functor.

The hypothesis `[IsOpenImmersion g]` that change of base carries is satisfied with nothing to
prove: the `g` of both finite level functors is the identity of `X`.

## Main results

Everything lives in the namespace `Crystalline`.

* `preservesInjectiveObjects_pAdicLevelSheafRestriction` and
  `preservesInjectiveObjects_pAdicLevelStepSheafRestriction` — **restriction of abelian sheaves
  to a finite level, and between two finite levels, carries injective abelian sheaves to
  injective abelian sheaves**, unconditionally.
* `subsingleton_cohomology_pAdicLevelSheafRestriction_of_injective` and
  `subsingleton_cohomology_pAdicLevelStepSheafRestriction_of_injective` — hence
  `H^{j+1}(Cris(X/S_e), F_e) = 0` for `F` injective, the concrete cohomological form of
  acyclicity.
* `rightAcyclic_globalSections_pAdicLevelSheafRestriction_of_injective` and
  `rightAcyclic_globalSections_pAdicLevelStepSheafRestriction_of_injective` — the same statement
  in the shape `Crystalline.GlobalCrystallineSituation.SmallSite.derivedGlobalSectionsCompIso`
  consumes it, `CategoryTheory.Functor.rightAcyclic` of the global sections of the smaller site.
* `pAdicLevelDerivedGlobalSectionsCompIso` and `pAdicLevelStepDerivedGlobalSectionsCompIso` —
  the payoff, [Stacks, Tag 015M] for the two restrictions:
  `R(Γ(Cris(X/S_e), -) ∘ ρ) ≅ Rρ ⋙ RΓ(Cris(X/S_e), -)`.

## What is and is not proved

What is proved is exactly the first half of the hint of [Stacks, Tag 07MV]: restriction to a
finite level is a functor to which [Stacks, Tag 015M] applies.  The tag is placed on the two
injectivity statements and the two `rightAcyclic` statements, which are that assertion of the
remark and nothing more; the strings record what each one says.

What is **not** proved, and what the remark still needs:

* The *arrows* of the tower `e ↦ RΓ(Cris(X/S_e), F_e)`.  Those need the underived comparison
  `Γ(Cris(X/S_e), -) ⟹ ρ ⋙ Γ(Cris(X/S_m), -)` of global sections along the transition, which
  does not exist in the library for `CategoryTheory.Sheaf.Γ` — only the module-valued
  `...SmallSite.smallChangeBaseGlobalSectionsTrans` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/BaseChangeMap.lean` — and then the
  change-of-base composition coherence that
  `StacksFrontier/AlgebraicGeometry/Crystalline/FiniteLevelTower.lean` deliberately omits.  Nothing
  below supplies either.
* The conclusion of [Stacks, Tag 07MV], that `RΓ(Cris(X/S), F)` is the derived inverse limit of
  that tower.  No `R lim` appears below.
* Nothing here changes the residual recorded in
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CompleteComparison.lean`, that
  `...SmallSite.DeRhamComparison07MZ` drops the mod-`p^e` conjunct of its clause (1): that
  residual is about the *statement* of the comparison, and this file adds an input to one of its
  three hypotheses without touching it.

## References

* [Stacks Project, Tag 07MV](https://stacks.math.columbia.edu/tag/07MV)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 00X4](https://stacks.math.columbia.edu/tag/00X4)
* [Stacks Project, Tag 07KL](https://stacks.math.columbia.edu/tag/07KL)
* [Stacks Project, Tag 0157](https://stacks.math.columbia.edu/tag/0157)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe w w' w'' u

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace Crystalline

section Level

variable {A : Type u} [CommRing A] (I : Ideal A) (γ : DividedPowers I) (p : ℕ)
  [Fact p.Prime] [Algebra (DividedPowers.IntegersAtPrime p) A]

/-! ### Additivity

`Crystalline.pAdicLevelSheafRestriction` and `Crystalline.pAdicLevelStepSheafRestriction` are
definitions wrapping `CategoryTheory.Functor.sheafPushforwardContinuous`, so instance search does
not see through them to
`CategoryTheory.Functor.additive_sheafPushforwardContinuous`; these two instances are that
unfolding, and are what lets the restrictions act degreewise on complexes. -/

/-- Restriction of abelian sheaves to a finite level is additive: on underlying presheaves it is
restriction along the functor of levels, which only reindexes the components of a natural
transformation. -/
instance additive_pAdicLevelSheafRestriction {e : ℕ} (he : IsPAdicLevel I γ p e) (X : Scheme.{u})
    (toCF : X ⟶ DividedPowerScheme.closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x)) :
    (pAdicLevelSheafRestriction I γ p he X toCF hX).Additive :=
  inferInstanceAs ((pAdicLevelExtend I γ p he X toCF hX).sheafPushforwardContinuous
    AddCommGrpCat.{u + 1} _ _).Additive

/-- Restriction of abelian sheaves between two finite levels is additive. -/
instance additive_pAdicLevelStepSheafRestriction {m e : ℕ} (hm : IsPAdicLevel I γ p m)
    (he : IsPAdicLevel I γ p e) (hme : m ≤ e) (X : Scheme.{u})
    (toCF : X ⟶ DividedPowerScheme.closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x)) :
    (pAdicLevelStepSheafRestriction I γ p hm he hme X toCF hX).Additive :=
  inferInstanceAs ((pAdicLevelStepExtend I γ p hm he hme X toCF hX).sheafPushforwardContinuous
    AddCommGrpCat.{u + 1} _ _).Additive

/-! ### Preservation of injectives -/

/-- **Stacks Project, Tag 07MV.**  Restriction of abelian sheaves from `Cris(X/S)` to a finite
divided power level `Cris(X/S_e)` carries injective abelian sheaves to injective abelian sheaves.

This is the first half of the hint of the remark.  The functor of levels is change of divided
power base at the pair `(S_e ⟶ S, 𝟙 X)`, so this is
`...SmallSite.preservesInjectiveObjects_smallChangeBaseAbelianRestriction`:
the left adjoint of restriction is the abelian lower shriek, which is exact by
[Stacks, Tag 00X4] because `Cris(X/S_e)` has fibre products and equalizers and change of base
preserves them, hence preserves monomorphisms, and a right adjoint of a
monomorphism-preserving functor preserves injective objects, [Stacks, Tag 015Z]. -/
@[stacks 07MV
  "restriction of abelian sheaves to a finite level carries injectives to injectives, \
   the first half of the remark's hint"]
instance preservesInjectiveObjects_pAdicLevelSheafRestriction {e : ℕ}
    (he : IsPAdicLevel I γ p e) (X : Scheme.{u})
    (toCF : X ⟶ DividedPowerScheme.closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x)) :
    (pAdicLevelSheafRestriction I γ p he X toCF hX).PreservesInjectiveObjects :=
  GlobalCrystallineSituation.SmallSite.preservesInjectiveObjects_smallChangeBaseAbelianRestriction
    (pAdicLevelSituation I γ p he X toCF hX) (specSituation I γ p X toCF hX)
    (pAdicLevelSchemeProj I γ p he) (𝟙 X)
    (pAdicLevelSituation_changeBase_condition I γ p he X toCF hX)

/-- **Stacks Project, Tag 07MV.**  Restriction of abelian sheaves between two finite divided
power levels `Cris(X/S_e) ⟶ Cris(X/S_m)`, for `m ≤ e`, carries injective abelian sheaves to
injective abelian sheaves.  This is the same argument as
`Crystalline.preservesInjectiveObjects_pAdicLevelSheafRestriction` at the pair
`(S_m ⟶ S_e, 𝟙 X)`. -/
@[stacks 07MV
  "restriction of abelian sheaves between two finite levels carries injectives to injectives"]
instance preservesInjectiveObjects_pAdicLevelStepSheafRestriction {m e : ℕ}
    (hm : IsPAdicLevel I γ p m) (he : IsPAdicLevel I γ p e) (hme : m ≤ e) (X : Scheme.{u})
    (toCF : X ⟶ DividedPowerScheme.closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x)) :
    (pAdicLevelStepSheafRestriction I γ p hm he hme X toCF hX).PreservesInjectiveObjects :=
  GlobalCrystallineSituation.SmallSite.preservesInjectiveObjects_smallChangeBaseAbelianRestriction
    (pAdicLevelSituation I γ p hm X toCF hX) (pAdicLevelSituation I γ p he X toCF hX)
    (pAdicLevelTransitionScheme I γ p hm he hme) (𝟙 X)
    (pAdicLevelStep_changeBase_condition I γ p hm he hme X toCF hX)

/-! ### The cohomological form of acyclicity -/

/-- `H^{j+1}(Cris(X/S_e), F_e) = 0` for an injective abelian sheaf `F` on `Cris(X/S)`: the
restriction `F_e` is again injective, and the higher cohomology of an injective sheaf
vanishes. -/
theorem subsingleton_cohomology_pAdicLevelSheafRestriction_of_injective {e : ℕ}
    (he : IsPAdicLevel I γ p e) (X : Scheme.{u})
    (toCF : X ⟶ DividedPowerScheme.closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x))
    (F : Sheaf (GlobalCrystallineSituation.smallTopology (specSituation I γ p X toCF hX))
      AddCommGrpCat.{u + 1}) [Injective F] (j : ℕ) :
    Subsingleton (GlobalCrystallineSituation.SmallSite.cohomology
      (pAdicLevelSituation I γ p he X toCF hX)
      ((pAdicLevelSheafRestriction I γ p he X toCF hX).obj F) (j + 1)) :=
  inferInstance

/-- `H^{j+1}(Cris(X/S_m), F_m) = 0` for an injective abelian sheaf `F` on `Cris(X/S_e)` and
`m ≤ e`, the transition-functor form of
`Crystalline.subsingleton_cohomology_pAdicLevelSheafRestriction_of_injective`. -/
theorem subsingleton_cohomology_pAdicLevelStepSheafRestriction_of_injective {m e : ℕ}
    (hm : IsPAdicLevel I γ p m) (he : IsPAdicLevel I γ p e) (hme : m ≤ e) (X : Scheme.{u})
    (toCF : X ⟶ DividedPowerScheme.closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x))
    (F : Sheaf (GlobalCrystallineSituation.smallTopology
      (pAdicLevelSituation I γ p he X toCF hX)) AddCommGrpCat.{u + 1}) [Injective F] (j : ℕ) :
    Subsingleton (GlobalCrystallineSituation.SmallSite.cohomology
      (pAdicLevelSituation I γ p hm X toCF hX)
      ((pAdicLevelStepSheafRestriction I γ p hm he hme X toCF hX).obj F) (j + 1)) :=
  inferInstance

/-! ### The hypothesis of [Stacks, Tag 015M], and the resulting comparison -/

section Derived

open GlobalCrystallineSituation GlobalCrystallineSituation.SmallSite

/-- **Stacks Project, Tag 07MV.**  Restriction to a finite divided power level carries an
injective abelian sheaf to one with **acyclic global sections**: this is
`Crystalline.preservesInjectiveObjects_pAdicLevelSheafRestriction` followed by
`CategoryTheory.Functor.rightAcyclic_of_injective`, an injective object being right acyclic for
every additive functor whose bounded below right derived functor exists.

This is verbatim the hypothesis `hg` of
`Crystalline.GlobalCrystallineSituation.SmallSite.derivedGlobalSectionsCompIso`, and so the
first half of the hint of the remark. -/
@[stacks 07MV
  "restriction to a finite level carries an injective abelian sheaf to one with acyclic global \
   sections, the acyclicity hypothesis of (015M); NOT the tower and NOT the remark's conclusion"]
theorem rightAcyclic_globalSections_pAdicLevelSheafRestriction_of_injective {e : ℕ}
    (he : IsPAdicLevel I γ p e) (X : Scheme.{u})
    (toCF : X ⟶ DividedPowerScheme.closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x))
    [HasDerivedCategory.{w'} (Sheaf (smallTopology (pAdicLevelSituation I γ p he X toCF hX))
      AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}] :
    ∀ F : Sheaf (smallTopology (specSituation I γ p X toCF hX)) AddCommGrpCat.{u + 1},
      Injective F → (globalSections (pAdicLevelSituation I γ p he X toCF hX)).rightAcyclic
        ((pAdicLevelSheafRestriction I γ p he X toCF hX).obj F) := fun _ _ =>
  Functor.rightAcyclic_of_injective _ _

/-- **Stacks Project, Tag 07MV.**  The transition-functor form of
`Crystalline.rightAcyclic_globalSections_pAdicLevelSheafRestriction_of_injective`: restriction
from `Cris(X/S_e)` to `Cris(X/S_m)`, `m ≤ e`, carries an injective abelian sheaf to one with
acyclic global sections. -/
@[stacks 07MV
  "restriction between two finite levels carries an injective abelian sheaf to one with acyclic \
   global sections, the acyclicity hypothesis of (015M) for the tower's arrows"]
theorem rightAcyclic_globalSections_pAdicLevelStepSheafRestriction_of_injective {m e : ℕ}
    (hm : IsPAdicLevel I γ p m) (he : IsPAdicLevel I γ p e) (hme : m ≤ e) (X : Scheme.{u})
    (toCF : X ⟶ DividedPowerScheme.closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x))
    [HasDerivedCategory.{w'} (Sheaf (smallTopology (pAdicLevelSituation I γ p hm X toCF hX))
      AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}] :
    ∀ F : Sheaf (smallTopology (pAdicLevelSituation I γ p he X toCF hX)) AddCommGrpCat.{u + 1},
      Injective F → (globalSections (pAdicLevelSituation I γ p hm X toCF hX)).rightAcyclic
        ((pAdicLevelStepSheafRestriction I γ p hm he hme X toCF hX).obj F) := fun _ _ =>
  Functor.rightAcyclic_of_injective _ _

/-- **Stacks Project, Tag 015M for restriction to a finite crystalline level.**
`R(Γ(Cris(X/S_e), -) ∘ ρ) ≅ Rρ ⋙ RΓ(Cris(X/S_e), -)`, where `ρ` is the restriction
`Crystalline.pAdicLevelSheafRestriction` of abelian sheaves to the level `e`.  The acyclicity
hypothesis is
`Crystalline.rightAcyclic_globalSections_pAdicLevelSheafRestriction_of_injective`, so nothing is
assumed. -/
def pAdicLevelDerivedGlobalSectionsCompIso {e : ℕ} (he : IsPAdicLevel I γ p e) (X : Scheme.{u})
    (toCF : X ⟶ DividedPowerScheme.closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x))
    [HasDerivedCategory.{w} (Sheaf (smallTopology (specSituation I γ p X toCF hX))
      AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{w'} (Sheaf (smallTopology (pAdicLevelSituation I γ p he X toCF hX))
      AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}] :
    (pAdicLevelSheafRestriction I γ p he X toCF hX ⋙
        globalSections (pAdicLevelSituation I γ p he X toCF hX)).rightDerivedFunctorPlus ≅
      (pAdicLevelSheafRestriction I γ p he X toCF hX).rightDerivedFunctorPlus ⋙
        derivedGlobalSectionsFunctor (pAdicLevelSituation I γ p he X toCF hX) :=
  derivedGlobalSectionsCompIso _ _ (pAdicLevelSheafRestriction I γ p he X toCF hX)
    (rightAcyclic_globalSections_pAdicLevelSheafRestriction_of_injective I γ p he X toCF hX)

/-- **Stacks Project, Tag 015M for the transition functor of the tower of finite levels.**
`R(Γ(Cris(X/S_m), -) ∘ ρ) ≅ Rρ ⋙ RΓ(Cris(X/S_m), -)` for the restriction `ρ` of abelian sheaves
from `Cris(X/S_e)` to `Cris(X/S_m)`, `m ≤ e`.  Unconditional, by
`Crystalline.rightAcyclic_globalSections_pAdicLevelStepSheafRestriction_of_injective`. -/
def pAdicLevelStepDerivedGlobalSectionsCompIso {m e : ℕ} (hm : IsPAdicLevel I γ p m)
    (he : IsPAdicLevel I γ p e) (hme : m ≤ e) (X : Scheme.{u})
    (toCF : X ⟶ DividedPowerScheme.closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x))
    [HasDerivedCategory.{w} (Sheaf (smallTopology (pAdicLevelSituation I γ p he X toCF hX))
      AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{w'} (Sheaf (smallTopology (pAdicLevelSituation I γ p hm X toCF hX))
      AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}] :
    (pAdicLevelStepSheafRestriction I γ p hm he hme X toCF hX ⋙
        globalSections (pAdicLevelSituation I γ p hm X toCF hX)).rightDerivedFunctorPlus ≅
      (pAdicLevelStepSheafRestriction I γ p hm he hme X toCF hX).rightDerivedFunctorPlus ⋙
        derivedGlobalSectionsFunctor (pAdicLevelSituation I γ p hm X toCF hX) :=
  derivedGlobalSectionsCompIso _ _ (pAdicLevelStepSheafRestriction I γ p hm he hme X toCF hX)
    (rightAcyclic_globalSections_pAdicLevelStepSheafRestriction_of_injective
      I γ p hm he hme X toCF hX)

end Derived

end Level

end Crystalline

end
