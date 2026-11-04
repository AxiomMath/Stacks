module

public import StacksFrontier.AlgebraicGeometry.Crystalline.FiniteLevelTowerArrows
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ContinuousGlobalSectionsComp

/-!
# The cone of `RΓ(Cris(X/S), F)` over the tower of finite crystalline levels

`StacksFrontier/AlgebraicGeometry/Crystalline/FiniteLevelTowerArrows.lean` assembled the tower

`n ↦ RΓ(Cris(X/S_{N+n}), F_{N+n}) : ℕᵒᵖ ⥤ D⁺(Ab)`

of [Stacks, Tag 07MV] and recorded that a derived limit of it exists.  **The conclusion of that
remark is that `RΓ(Cris(X/S), F)` is the derived limit**, and for that the tower has to be
compared with `RΓ(Cris(X/S), F)` at all.  This file builds that comparison:

* the arrow `RΓ(Cris(X/S), F) ⟶ RΓ(Cris(X/S_e), F_e)` for every level `e`, by the same four
  inputs that `Crystalline.pAdicLevelStepDerivedGlobalSectionsMap` is built from, and
* its underived shadow, assembled into an honest `CategoryTheory.Limits.Cone` over the underived
  tower, which needs the **cone condition** — that restricting a global section to level `e` and
  then to level `m` is restricting it to level `m`.

The cone condition is proved at the generality of an arbitrary chain of two continuous functors
of sites, as `Stacks.Sites.globalSectionsAlongContinuousApp_comp` of
`StacksFrontier/CategoryTheory/Sites/GlobalSections/ContinuousGlobalSectionsComp.lean`: both sides
are maps into a limit whose legs are the restriction maps, and each leg of each side is a single
restriction map of `F`.

## Main definitions

* `Crystalline.pAdicLevelDerivedGlobalSectionsConeMap` — **the arrow
  `RΓ(Cris(X/S), F) ⟶ RΓ(Cris(X/S_e), F_e)`**, with no hypothesis.
* `Crystalline.pAdicLevelGlobalSectionsCone` — **the cone over the underived tower
  `Crystalline.pAdicLevelGlobalSectionsTower` with vertex `Γ(Cris(X/S), F)`**, whose legs are the
  restriction maps `Crystalline.pAdicLevelGlobalSectionsTrans`.

## Main results

* `Crystalline.pAdicLevelGlobalSectionsTrans_comp` — **the cone condition on global sections**:
  for `m ≤ e`, restricting along `Cris(X/S_e) ⥤ Cris(X/S)` and then along
  `Cris(X/S_m) ⥤ Cris(X/S_e)` is restricting along `Cris(X/S_m) ⥤ Cris(X/S)`, once `ρ(F_e)` is
  identified with `F_m` by `Crystalline.pAdicLevelStepSheafRestrictionCompIso`.

## What is and is not proved

**The conclusion of [Stacks, Tag 07MV] is still not proved**, and no tag attribute marking it is
placed anywhere.  What this file adds is the comparison the conclusion is *about*; what the
conclusion needs beyond it is

1. that the cone `Crystalline.pAdicLevelGlobalSectionsCone` is a **limit** cone, which is the
   remark's second hint `Γ(Cris(X/S), F) = lim_e Γ(Cris(X/S_e), F_e)`.  That rests on the
   assertion that any object of `Cris(X/S)` is locally an object of some `Cris(X/S_e)`.  Of that
   assertion the library has the local nilpotence of `p` on the ambient scheme of an object,
   `Crystalline.GlobalCrystallineSituation.Thickening.exists_isAffineOpen_mem_and_pow_eq_zero` of
   `StacksFrontier/AlgebraicGeometry/Crystalline/ThickeningNilpotence.lean`, and **not** the passage
   from it to a covering family, which is recorded as missing in that file's own
   "What is and is not proved";
2. that the transition maps of the underived tower are **surjective** on an injective sheaf,
   the remark's first hint, of which the library has only the injectivity of the restrictions
   (`Crystalline.preservesInjectiveObjects_pAdicLevelStepSheafRestriction`) and not the
   surjectivity;
3. the derived-category step itself: that 1 and 2 at an injective resolution of `F` give
   `IsDerivedLimit`.  Its ingredient is now in hand for the right category:
   `DerivedCategory.isDerivedLimit_of_limit_cone_of_epi_addCommGrpCat` of
   `StacksFrontier/Homology/DerivedCategory/InverseSystem/AbEpiTowerLimit.lean` says that a tower
   of complexes of **abelian groups** with epimorphic transition maps has `Q` of its ordinary
   inverse limit for a derived inverse limit.  (It was previously available only for
   `ModuleCat A`.)  What still has to be built around it is the injective resolution `F → I`
   and the identification of each `RΓ(Cris(X/S_e), F_e)` with `Q(Γ(Cris(X/S_e), ρ_e I))`, for
   which `Crystalline.preservesInjectiveObjects_pAdicLevelSheafRestriction` is the input; the
   two hypotheses of that theorem at `Γ(Cris(X/S_•), ρ_• I)` are exactly 1 and 2 above.

In particular nothing here is any part of [Stacks, Tag 07MZ]: the tower above is 07MV's tower of
abelian sheaves, whereas the left tower of
`...SmallSite.DerivedLimitPresentation07MZ` is an existentially quantified datum in `D(Mod_A)`.
Nothing here touches the residual recorded in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CompleteComparison.lean`, that
`...SmallSite.DeRhamComparison07MZ` drops the mod-`p^e` conjunct of its clause (1).

## References

* [Stacks Project, Tag 07MV](https://stacks.math.columbia.edu/tag/07MV)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 08TC](https://stacks.math.columbia.edu/tag/08TC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w w' w'' u

namespace Crystalline

section Level

variable {A : Type u} [CommRing A] (I : Ideal A) (γ : DividedPowers I) (p : ℕ)
  [Fact p.Prime] [Algebra (DividedPowers.IntegersAtPrime p) A]

open GlobalCrystallineSituation GlobalCrystallineSituation.SmallSite

/-! ### The cone condition on global sections -/

/-- **The restriction maps on global sections of the tower of finite levels form a cone.**  For
`m ≤ e`, restricting a global section of `F` to `Cris(X/S_e)` and then to `Cris(X/S_m)` is
restricting it to `Cris(X/S_m)`, once the two readings of the restricted sheaf are identified by
`Crystalline.pAdicLevelStepSheafRestrictionCompIso`.

This is `Stacks.Sites.globalSectionsAlongContinuousApp_comp` at the chain
`Cris(X/S_m) ⥤ Cris(X/S_e) ⥤ Cris(X/S)`, whose comparison with `Cris(X/S_m) ⥤ Cris(X/S)` is
`Crystalline.pAdicLevelStepExtendCompIso`; nothing of the crystalline sites is used beyond the
continuity already recorded for those functors. -/
theorem pAdicLevelGlobalSectionsTrans_comp {m e : ℕ} (hm : IsPAdicLevel I γ p m)
    (he : IsPAdicLevel I γ p e) (hme : m ≤ e) (X : Scheme.{u})
    (toCF : X ⟶ DividedPowerScheme.closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x))
    (F : Sheaf (smallTopology (specSituation I γ p X toCF hX)) AddCommGrpCat.{u + 1}) :
    (pAdicLevelGlobalSectionsTrans I γ p he X toCF hX).app F ≫
        (pAdicLevelStepGlobalSectionsTrans I γ p hm he hme X toCF hX).app
          ((pAdicLevelSheafRestriction I γ p he X toCF hX).obj F) ≫
        (globalSections (pAdicLevelSituation I γ p hm X toCF hX)).map
          ((pAdicLevelStepSheafRestrictionCompIso I γ p hm he hme X toCF hX).hom.app F) =
      (pAdicLevelGlobalSectionsTrans I γ p hm X toCF hX).app F :=
  Stacks.Sites.globalSectionsAlongContinuousApp_comp
    (pAdicLevelStepExtendCompIso I γ p hm he hme X toCF hX)
    (smallTopology (pAdicLevelSituation I γ p hm X toCF hX))
    (smallTopology (pAdicLevelSituation I γ p he X toCF hX))
    (smallTopology (specSituation I γ p X toCF hX)) AddCommGrpCat.{u + 1} F

/-! ### The cone over the underived tower -/

/-- **The cone over the underived tower of global sections with vertex `Γ(Cris(X/S), F)`.**  Its
leg at `n` is the restriction `Γ(Cris(X/S), F) ⟶ Γ(Cris(X/S_{N+n}), F_{N+n})` of
`Crystalline.pAdicLevelGlobalSectionsTrans`, and the cone condition is
`Crystalline.pAdicLevelGlobalSectionsTrans_comp`.

**That this cone is a limit is not proved**: it is the second hint of [Stacks, Tag 07MV],
`Γ(Cris(X/S), F) = lim_e Γ(Cris(X/S_e), F_e)`, which rests on the assertion that any object of
`Cris(X/S)` is locally an object of some `Cris(X/S_e)`. -/
def pAdicLevelGlobalSectionsCone {N : ℕ}
    (hN : ∀ e, N ≤ e → IsPAdicLevel I γ p e) (X : Scheme.{u})
    (toCF : X ⟶ DividedPowerScheme.closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x))
    (F : Sheaf (smallTopology (specSituation I γ p X toCF hX)) AddCommGrpCat.{u + 1}) :
    Cone (pAdicLevelGlobalSectionsTower I γ p hN X toCF hX F) where
  pt := (globalSections (specSituation I γ p X toCF hX)).obj F
  π :=
    NatTrans.ofOpSequence
      (fun n => (pAdicLevelGlobalSectionsTrans I γ p
        (hN (N + n) (Nat.le_add_right N n)) X toCF hX).app F)
      (fun n => by
        have hmap : (pAdicLevelGlobalSectionsTower I γ p hN X toCF hX F).map
              (homOfLE (Nat.le_add_right n 1)).op =
            (pAdicLevelStepGlobalSectionsTrans I γ p (hN (N + n) (Nat.le_add_right N n))
                  (hN (N + (n + 1)) (Nat.le_add_right N (n + 1))) (by omega) X toCF hX).app
                ((pAdicLevelSheafRestriction I γ p
                  (hN (N + (n + 1)) (Nat.le_add_right N (n + 1))) X toCF hX).obj F) ≫
              (globalSections (pAdicLevelSituation I γ p
                  (hN (N + n) (Nat.le_add_right N n)) X toCF hX)).map
                ((pAdicLevelStepSheafRestrictionCompIso I γ p
                  (hN (N + n) (Nat.le_add_right N n))
                  (hN (N + (n + 1)) (Nat.le_add_right N (n + 1))) (by omega)
                  X toCF hX).hom.app F) :=
          Functor.ofOpSequence_map_homOfLE_succ _ n
        refine (Category.id_comp _).trans (Eq.trans ?_ (congrArg
          (fun z => (pAdicLevelGlobalSectionsTrans I γ p
            (hN (N + (n + 1)) (Nat.le_add_right N (n + 1))) X toCF hX).app F ≫ z) hmap.symm))
        exact (pAdicLevelGlobalSectionsTrans_comp I γ p (hN (N + n) (Nat.le_add_right N n))
          (hN (N + (n + 1)) (Nat.le_add_right N (n + 1))) (by omega) X toCF hX F).symm)

/-! ### The derived arrow out of `RΓ(Cris(X/S), F)` -/

section Derived

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **Stacks Project, Tag 07MV.**  **The arrow `RΓ(Cris(X/S), F) ⟶ RΓ(Cris(X/S_e), F_e)`** from
derived global sections on `Cris(X/S)` to the term of the remark's tower at the finite divided
power level `e`.

It is assembled exactly as `Crystalline.pAdicLevelStepDerivedGlobalSectionsMap` is, from four
proved inputs and no hypothesis.  The underived restriction
`Crystalline.pAdicLevelGlobalSectionsTrans` is derived by
`Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans`; its target, the derived functor of the
composite `ρ_e ⋙ Γ(Cris(X/S_e), -)`, is split by
`Crystalline.pAdicLevelDerivedGlobalSectionsCompIso`, which is [Stacks, Tag 015M] and is
unconditional because restriction to a level preserves injectives; and
`CategoryTheory.Functor.rightDerivedFunctorPlusObjSingleIso` replaces `Rρ_e(F[0])` by `F_e[0]`,
restriction to a level being exact.  Unlike the step map no further identification is needed:
the sheaf being restricted is `F` itself.

**This is the comparison whose being a derived limit presentation is the conclusion of the
remark; that it is one is not proved.** -/
@[stacks 07MV
  "the arrow RΓ(Cris(X/S), F) ⟶ RΓ(Cris(X/S_e), F_e) comparing derived global sections with the \
   remark's tower; NOT the remark's conclusion, that RΓ(Cris(X/S), F) is the derived limit"]
def pAdicLevelDerivedGlobalSectionsConeMap {e : ℕ} (he : IsPAdicLevel I γ p e) (X : Scheme.{u})
    (toCF : X ⟶ DividedPowerScheme.closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x))
    [HasDerivedCategory.{w} (Sheaf (smallTopology (specSituation I γ p X toCF hX))
      AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{w'} (Sheaf (smallTopology (pAdicLevelSituation I γ p he X toCF hX))
      AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
    (F : Sheaf (smallTopology (specSituation I γ p X toCF hX)) AddCommGrpCat.{u + 1}) :
    (derivedGlobalSections (specSituation I γ p X toCF hX)).obj F ⟶
      pAdicLevelDerivedGlobalSections I γ p he X toCF hX F :=
  (Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans
        (pAdicLevelGlobalSectionsTrans I γ p he X toCF hX)).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
    (pAdicLevelDerivedGlobalSectionsCompIso I γ p he X toCF hX).hom.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
    (derivedGlobalSectionsFunctor (pAdicLevelSituation I γ p he X toCF hX)).map
      (Functor.rightDerivedFunctorPlusObjSingleIso
        (pAdicLevelSheafRestriction I γ p he X toCF hX) F).hom

end Derived

end Level

end Crystalline

end
