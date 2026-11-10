module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquareTransComposition
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.FrobeniusTwistArrows

/-!
# The map of [Stacks, Tag 07N5] is the composite of the arrows of its proof

The proof of [Stacks, Tag 07N5] says: "the map of the theorem is the composition of the three maps
(60.26.4.1), (60.26.4.2) and (60.26.4.3)".  The library builds the map of the theorem,
`...SmallSite.frobeniusMap07N5Canonical`, from the derived comparison of global sections for the
Frobenius square taken in one step (`...SmallSite.frobeniusBaseChangeArrows07N5`), and the first
two arrows of the proof, `...SmallSite.baseChangeArrow07QC` and
`...SmallSite.relativeFrobeniusArrow07N6`, from the comparisons for the two halves of that
square.  **This file proves that the two agree**,
`frobeniusBaseChangeArrows07N5_eq_comp`.

## How

The comparison along a change of divided power base is an instance of the general construction
`CategoryTheory.Functor.derivedSquareMap` of
`StacksFrontier/Algebra/Homology/DerivedCategory/DerivedSquareTransComposition.lean`
(`derivedChangeBaseBigGlobalSectionsMap_eq_derivedSquareMap`), and that construction is compatible
with pasting squares (`CategoryTheory.Functor.derivedSquareMap_comp`) — the compatibility of the
canonical transformation of [Stacks, Tag 05T2] with composition.  What is left is underived:

* the pullbacks compose, `F_{X/S₀}^* E^{(1)} = (F_X)^*_cris E`, at the module universe of the
  cohomology (`...SmallSite.frobeniusBigModulePullbackIso`);
* the restrictions of scalars compose, the one along `𝟙 S` being the identity;
* restricting a global section in two steps is restricting it in one
  (`changeBaseBigBaseGlobalSectionsTrans_paste`), by the compatibility of the section with the
  comparison isomorphism `...twistChangeBaseCompIso` of the two changes of base.

## Main results

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `derivedChangeBaseBigGlobalSectionsMap_comp` — the derived comparisons along two changes of
  divided power base paste, for an arbitrary pair of composable squares.
* `derivedChangeBaseBigGlobalSectionsMap_frobenius_eq` — the derived comparison for the Frobenius
  square is the pasting of those for its two halves, on the big crystalline site.
* `derivedFrobeniusRestrictGlobalSectionsMap_eq` — the same on the small crystalline site.
* `frobeniusBaseChangeArrows07N5_eq_comp` — **the composite of arrows 1 and 2
  of the proof of [Stacks, Tag 07N5] is the first factor of the map of the theorem.**

## References

* [Stacks Project, Tag 07N5](https://stacks.math.columbia.edu/tag/07N5)
* [Stacks Project, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u wS wB wA

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section ChangeBase

variable {S S' : GlobalCrystallineSituation.{u}}
  [HasDerivedCategory.{wB} (BigModuleSheaf S)] [HasDerivedCategory.{wB} (BigModuleSheaf S')]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S'.S.scheme, ⊤))]

/-- **The derived comparison on global sections along a change of divided power base is the
derived comparison of its square**, `CategoryTheory.Functor.derivedSquareMap`, at the underived
comparison `changeBaseBigBaseGlobalSectionsTrans`. -/
theorem derivedChangeBaseBigGlobalSectionsMap_eq_derivedSquareMap (f : S.S ⟶ S'.S)
    (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
    (N : BigModuleSheaf S') :
    derivedChangeBaseBigGlobalSectionsMap f g h N =
      Functor.derivedSquareMap (changeBaseBigBaseGlobalSectionsTrans f g h) N := by
  rw [Functor.derivedSquareMap_eq]
  rfl

variable {S₁ S₂ : GlobalCrystallineSituation.{u}}
  [HasDerivedCategory.{wB} (BigModuleSheaf S₁)] [HasDerivedCategory.{wB} (BigModuleSheaf S₂)]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S₁.S.scheme, ⊤))]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S₂.S.scheme, ⊤))]

/-- **The derived comparison along a pasted pair of changes of divided power base is the pasting
of the derived comparisons**, at a single sheaf of modules: for squares `(f₂₁, g₂₁)` from `S₂` to
`S₁` and `(f₁₂, g₁₂)` from `S₁` to `S₂`, a third square `(f, g)` from `S₁` to itself, an
isomorphism `e` from the composite of the two pullbacks to the third, and transformations
`ρ₀`, `ρ` comparing the restrictions of scalars, the comparison for `(f, g)` followed by `e⁻¹`
is the comparison for `(f₂₁, g₂₁)` followed by that for `(f₁₂, g₁₂)` and `ρ` — provided the
underived comparisons paste (`hα`) and `ρ` is compatible with `ρ₀` (`hρ`).

This is `CategoryTheory.Functor.derivedSquareMap_comp` at the squares of change of base. -/
theorem derivedChangeBaseBigGlobalSectionsMap_comp
    (f₂₁ : S₂.S ⟶ S₁.S) (g₂₁ : S₂.X ⟶ S₁.X)
    (h₂₁ : S₂.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f₂₁ = g₂₁ ≫ S₁.toClosedFiber)
    (f₁₂ : S₁.S ⟶ S₂.S) (g₁₂ : S₁.X ⟶ S₂.X)
    (h₁₂ : S₁.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f₁₂ = g₁₂ ≫ S₂.toClosedFiber)
    (f : S₁.S ⟶ S₁.S) (g : S₁.X ⟶ S₁.X)
    (h : S₁.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S₁.toClosedFiber)
    (e : changeBaseBigModulePullback S₂ S₁ f₂₁ g₂₁ h₂₁ ⋙
        changeBaseBigModulePullback S₁ S₂ f₁₂ g₁₂ h₁₂ ≅ changeBaseBigModulePullback S₁ S₁ f g h)
    (ρ₀ : ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom f₁₂) ⋙
        ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom f₂₁) ⟶
      ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom f))
    (ρ : (ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom f₁₂)).mapDerivedCategoryPlus ⋙
        (ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom f₂₁)).mapDerivedCategoryPlus ⟶
      (ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom f)).mapDerivedCategoryPlus)
    (hρ : ∀ L : HomotopyCategory.Plus (ModuleCat.{u + 1} Γ(S₁.S.scheme, ⊤)),
      (ModuleCat.restrictScalars.{u + 1}
          (baseChangeRingHom f₂₁)).mapDerivedCategoryPlusFactorsh.inv.app
          ((ModuleCat.restrictScalars.{u + 1}
            (baseChangeRingHom f₁₂)).mapHomotopyCategoryPlus.obj L) ≫
        (ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom f₂₁)).mapDerivedCategoryPlus.map
          ((ModuleCat.restrictScalars.{u + 1}
            (baseChangeRingHom f₁₂)).mapDerivedCategoryPlusFactorsh.inv.app L) ≫
          ρ.app (DerivedCategory.Plus.Qh.obj L) =
        DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatTrans ρ₀).app L) ≫
          (ModuleCat.restrictScalars.{u + 1}
            (baseChangeRingHom f)).mapDerivedCategoryPlusFactorsh.inv.app L)
    (hα : ∀ M : BigModuleSheaf S₁,
      (changeBaseBigBaseGlobalSectionsTrans f₂₁ g₂₁ h₂₁).app M ≫
          (ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom f₂₁)).map
            ((changeBaseBigBaseGlobalSectionsTrans f₁₂ g₁₂ h₁₂).app
              ((changeBaseBigModulePullback S₂ S₁ f₂₁ g₂₁ h₂₁).obj M)) ≫
          ρ₀.app _ =
        (changeBaseBigBaseGlobalSectionsTrans f g h).app M ≫
          (ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom f)).map
            ((bigBaseModuleGlobalSections S₁).map (e.inv.app M)))
    (N : BigModuleSheaf S₁) :
    derivedChangeBaseBigGlobalSectionsMap f₂₁ g₂₁ h₂₁ N ≫
        (ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom f₂₁)).mapDerivedCategoryPlus.map
          (derivedChangeBaseBigGlobalSectionsMap f₁₂ g₁₂ h₁₂
            ((changeBaseBigModulePullback S₂ S₁ f₂₁ g₂₁ h₂₁).obj N)) ≫
        ρ.app _ =
      derivedChangeBaseBigGlobalSectionsMap f g h N ≫
        (ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom f)).mapDerivedCategoryPlus.map
          ((derivedBigModuleGlobalSections S₁).map (e.inv.app N)) := by
  rw [derivedChangeBaseBigGlobalSectionsMap_eq_derivedSquareMap,
    derivedChangeBaseBigGlobalSectionsMap_eq_derivedSquareMap,
    derivedChangeBaseBigGlobalSectionsMap_eq_derivedSquareMap]
  exact Functor.derivedSquareMap_comp _ _ _ e.inv ρ₀ ρ hρ hα N

end ChangeBase

section Bookkeeping

variable {𝒦 𝒦' : Type*} [Category* 𝒦] [Category* 𝒦'] (σ : 𝒦' ⥤ 𝒦)

private lemma book1 {B : 𝒦} {C' G' H' F' E' : 𝒦'} (d : B ⟶ σ.obj C') (a : C' ⟶ G') (b : G' ⟶ H')
    (c : H' ⟶ F') (j : F' ⟶ E') :
    (d ≫ σ.map (a ≫ b ≫ c)) ≫ σ.map j = d ≫ σ.map (a ≫ b ≫ c ≫ j) := by
  simp only [Functor.map_comp, Category.assoc]

private lemma book2 {B : 𝒦} {C' D' E' : 𝒦'} (d : B ⟶ σ.obj C') (t : C' ⟶ D') (t' : D' ⟶ C')
    (htt : t ≫ t' = 𝟙 C') (R : C' ⟶ E') :
    d ≫ σ.map R = d ≫ σ.map t ≫ σ.map (t' ≫ R) := by
  rw [← Functor.map_comp, reassoc_of% htt]

private lemma book3 {A B : 𝒦} {C' D' E' : 𝒦'} (i : A ⟶ B) (d : B ⟶ σ.obj C') (t : C' ⟶ D')
    (R : D' ⟶ E') : i ≫ d ≫ σ.map t ≫ σ.map R = (i ≫ d ≫ σ.map t) ≫ σ.map R := by
  simp only [Category.assoc]

end Bookkeeping


section Frobenius

variable (T : Crystalline.FCrystalSituation.{u})
  [HasDerivedCategory.{wB} (BigModuleSheaf T.global)]
  [HasDerivedCategory.{wB} (BigModuleSheaf T.frobeniusTwistSituation)]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(T.global.S.scheme, ⊤))]

omit [HasDerivedCategory.{wB} (BigModuleSheaf T.global)]
  [HasDerivedCategory.{wB} (BigModuleSheaf T.frobeniusTwistSituation)]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(T.global.S.scheme, ⊤))] in
/-- **The underived comparisons of the two halves of the Frobenius square paste to the comparison
of the Frobenius square**, through `F_{X/S₀}^* E^{(1)} = (F_X)^*_cris E`: restricting a global
section along `Spec(σ)` and `X^{(1)} ⟶ X`, then along `F_{X/S₀}`, is restricting it along
`Spec(σ)` and `F_X`. -/
theorem changeBaseBigBaseGlobalSectionsTrans_paste (M : BigModuleSheaf T.global) :
    (changeBaseBigBaseGlobalSectionsTrans (S := T.frobeniusTwistSituation) (S' := T.global)
        T.specSigma T.twistProjection T.twistToClosedFiber_comp_closedFiberMap_specSigma).app M ≫
      (ModuleCat.restrictScalars (baseChangeRingHom (S := T.frobeniusTwistSituation)
          (S' := T.global) T.specSigma)).map
        ((changeBaseBigBaseGlobalSectionsTrans (S := T.global) (S' := T.frobeniusTwistSituation)
          (𝟙 T.global.S) T.relativeFrobeniusToTwist T.toClosedFiber_comp_closedFiberMap_id).app
          ((sigmaBigModulePullback T).obj M)) ≫
      (Functor.whiskerRight (ModuleCat.restrictScalarsId'.{u + 1}
          (baseChangeRingHom (S := T.global) (S' := T.global) (𝟙 T.global.S))
          (baseChangeRingHom_id T.global)).hom
        (ModuleCat.restrictScalars (baseChangeRingHom (S := T.frobeniusTwistSituation)
          (S' := T.global) T.specSigma))).app _ =
    (changeBaseBigBaseGlobalSectionsTrans (S := T.global) (S' := T.global)
        T.specSigma T.frobenius T.toClosedFiber_comp_closedFiberMap_specSigma).app M ≫
      (ModuleCat.restrictScalars (baseChangeRingHom (S := T.frobeniusTwistSituation)
          (S' := T.global) T.specSigma)).map
        ((bigBaseModuleGlobalSections T.global).map
          ((frobeniusBigModulePullbackIso T).inv.app M)) := by
  ext x
  refine Subtype.ext (funext fun A => ?_)
  change x.val (op (T.sigmaChangeBase.obj (T.twistChangeBase.obj A.unop))) =
    M.val.map (T.twistChangeBaseCompIso.hom.app A.unop).op
      (x.val (op (T.frobeniusChangeBase.obj A.unop)))
  exact (x.2 (T.twistChangeBaseCompIso.hom.app A.unop).op).symm


/-- The bookkeeping of `derivedChangeBaseBigGlobalSectionsMap_frobenius_eq`. -/
private lemma pasteFinish {𝒦 𝒦' : Type*} [Category* 𝒦] [Category* 𝒦'] (σ : 𝒦' ⥤ 𝒦) {A : 𝒦}
    {B' C' D' E' : 𝒦'} (d13 M : A ⟶ σ.obj E') (d23 M₁ : A ⟶ σ.obj B') (d12 M₂ : B' ⟶ C')
    (ρY : C' ⟶ D') (h : D' ⟶ E') (g : E' ⟶ D') (e13 : d13 = M) (e23 : d23 = M₁)
    (e12 : d12 = M₂) (K : M₁ ≫ σ.map M₂ ≫ σ.map ρY = M ≫ σ.map g) (hg : g ≫ h = 𝟙 E') :
    d13 = d23 ≫ σ.map (d12 ≫ ρY ≫ h) := by
  subst e13 e23 e12
  rw [Functor.map_comp, Functor.map_comp, reassoc_of% K, ← Functor.map_comp, hg,
    CategoryTheory.Functor.map_id, Category.comp_id]

/-- **The derived comparison for the Frobenius square is the pasting of the derived comparisons
for its two halves**, on the big crystalline site and at a single sheaf of modules: arrow 1
followed by `σ_*` of arrow 2, read at `(F_X)^*_cris N` through
`F_{X/S₀}^* N^{(1)} = (F_X)^*_cris N`.

This is the compatibility of the canonical transformation of [Stacks, Tag 05T2] with the
composition of the two change-of-base squares, `CategoryTheory.Functor.derivedSquareMap_comp`, at
the underived pasting `changeBaseBigBaseGlobalSectionsTrans_paste`. -/
theorem derivedChangeBaseBigGlobalSectionsMap_frobenius_eq (N : BigModuleSheaf T.global) :
    derivedChangeBaseBigGlobalSectionsMap (S := T.global) (S' := T.global) T.specSigma T.frobenius
        T.toClosedFiber_comp_closedFiberMap_specSigma N =
      derivedChangeBaseBigGlobalSectionsMap (S := T.frobeniusTwistSituation) (S' := T.global)
          T.specSigma T.twistProjection T.twistToClosedFiber_comp_closedFiberMap_specSigma N ≫
        (frobeniusSigmaRestrictScalarsPlus T).map
          (derivedChangeBaseBigGlobalSectionsMap (S := T.global) (S' := T.frobeniusTwistSituation)
              (𝟙 T.global.S) T.relativeFrobeniusToTwist T.toClosedFiber_comp_closedFiberMap_id
              ((sigmaBigModulePullback T).obj N) ≫
            (restrictScalarsIdDerivedPlusIso T.global).hom.app _ ≫
            (derivedBigModuleGlobalSections T.global).map
              ((frobeniusBigModulePullbackIso T).hom.app N)) := by
  have hρ := fun L => Functor.idIso_compatible
      (hM₀ := (inferInstance : HasDerivedCategory.{wA}
        (ModuleCat.{u + 1} Γ(T.global.S.scheme, ⊤))))
      (hM₁ := (inferInstance : HasDerivedCategory.{wA}
        (ModuleCat.{u + 1} Γ(T.global.S.scheme, ⊤))))
      (ModuleCat.restrictScalars.{u + 1}
        (baseChangeRingHom (S := T.global) (S' := T.global) T.specSigma))
      (ModuleCat.restrictScalars.{u + 1}
        (baseChangeRingHom (S := T.global) (S' := T.global) (𝟙 T.global.S)))
      (ModuleCat.restrictScalarsId'.{u + 1}
          (baseChangeRingHom (S := T.global) (S' := T.global) (𝟙 T.global.S))
          (baseChangeRingHom_id T.global)) L
  have key := derivedChangeBaseBigGlobalSectionsMap_comp (S₁ := T.global)
    (S₂ := T.frobeniusTwistSituation)
    T.specSigma T.twistProjection T.twistToClosedFiber_comp_closedFiberMap_specSigma
    (𝟙 T.global.S) T.relativeFrobeniusToTwist T.toClosedFiber_comp_closedFiberMap_id
    T.specSigma T.frobenius T.toClosedFiber_comp_closedFiberMap_specSigma
    (frobeniusBigModulePullbackIso T)
    (Functor.whiskerRight (ModuleCat.restrictScalarsId'.{u + 1}
          (baseChangeRingHom (S := T.global) (S' := T.global) (𝟙 T.global.S))
          (baseChangeRingHom_id T.global)).hom
        (ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom (S := T.frobeniusTwistSituation)
          (S' := T.global) T.specSigma)))
    (Functor.whiskerRight (restrictScalarsIdDerivedPlusIso T.global).hom
      (frobeniusSigmaRestrictScalarsPlus T)) hρ (changeBaseBigBaseGlobalSectionsTrans_paste T) N
  exact pasteFinish (frobeniusSigmaRestrictScalarsPlus T) _ _ _ _ _ _ _ _
    ((derivedBigModuleGlobalSections T.global).map ((frobeniusBigModulePullbackIso T).inv.app N))
    rfl rfl rfl key
    (((derivedBigModuleGlobalSections T.global).map_comp _ _).symm.trans
      ((congrArg (derivedBigModuleGlobalSections T.global).map
        ((frobeniusBigModulePullbackIso T).inv_hom_id_app N)).trans
        ((derivedBigModuleGlobalSections T.global).map_id _)))

/-- `derivedChangeBaseBigGlobalSectionsMap_frobenius_eq` at the universe lift of a sheaf of
modules at the universe of the chapter's crystals, with the base change `N^{(1)}` read at that
universe. -/
theorem derivedChangeBaseBigGlobalSectionsMap_frobenius_eq_ulift
    (N : SheafOfModules.{u} (crystallineStructureSheaf T.global)) :
    derivedFrobeniusBigGlobalSectionsMap T N =
      derivedChangeBaseBigGlobalSectionsMap (S := T.frobeniusTwistSituation) (S' := T.global)
          T.specSigma T.twistProjection T.twistToClosedFiber_comp_closedFiberMap_specSigma
          ((bigModuleULift T.global).obj N) ≫
        (frobeniusSigmaRestrictScalarsPlus T).map
          (derivedChangeBaseBigGlobalSectionsMap (S := T.global) (S' := T.frobeniusTwistSituation)
              (𝟙 T.global.S) T.relativeFrobeniusToTwist T.toClosedFiber_comp_closedFiberMap_id
              ((bigModuleULift T.frobeniusTwistSituation).obj (T.sigmaModulePullback.obj N)) ≫
            (restrictScalarsIdDerivedPlusIso T.global).hom.app _ ≫
            (derivedBigModuleGlobalSections T.global).map
              ((frobeniusBigModulePullbackIso T).hom.app ((bigModuleULift T.global).obj N))) :=
  derivedChangeBaseBigGlobalSectionsMap_frobenius_eq T ((bigModuleULift T.global).obj N)

variable [HasDerivedCategory.{wS} (ModuleSheaf T.global)]
  [HasDerivedCategory.{wS} (ModuleSheaf T.frobeniusTwistSituation)]

omit [HasDerivedCategory.{wS} (ModuleSheaf T.frobeniusTwistSituation)] in
/-- `derivedChangeBaseBigGlobalSectionsMap_frobenius_eq_ulift` followed by the passage to the
small site at the target. -/
theorem derivedFrobeniusBigGlobalSectionsMap_comp_restrict
    (N : SheafOfModules.{u} (crystallineStructureSheaf T.global)) :
    derivedFrobeniusBigGlobalSectionsMap T N ≫ (frobeniusSigmaRestrictScalarsPlus T).map
        (derivedRestrictModuleGlobalSectionsULiftIso T.global
          (T.frobeniusModulePullback.obj N)).hom =
      derivedChangeBaseBigGlobalSectionsMap (S := T.frobeniusTwistSituation) (S' := T.global)
          T.specSigma T.twistProjection T.twistToClosedFiber_comp_closedFiberMap_specSigma
          ((bigModuleULift T.global).obj N) ≫
        (frobeniusSigmaRestrictScalarsPlus T).map
          (derivedChangeBaseBigGlobalSectionsMap (S := T.global) (S' := T.frobeniusTwistSituation)
              (𝟙 T.global.S) T.relativeFrobeniusToTwist T.toClosedFiber_comp_closedFiberMap_id
              ((bigModuleULift T.frobeniusTwistSituation).obj (T.sigmaModulePullback.obj N)) ≫
            (restrictScalarsIdDerivedPlusIso T.global).hom.app _ ≫
            (derivedBigModuleGlobalSections T.global).map
              ((frobeniusBigModulePullbackIso T).hom.app ((bigModuleULift T.global).obj N)) ≫
            (derivedRestrictModuleGlobalSectionsULiftIso T.global
              (T.frobeniusModulePullback.obj N)).hom) :=
  (congrArg (· ≫ _) (derivedChangeBaseBigGlobalSectionsMap_frobenius_eq_ulift T N)).trans
    (book1 _ _ _ _ _ _)

/-- The previous identity with the small-site comparison at `X^{(1)}` inserted and cancelled:
the big-site form of `derivedFrobeniusRestrictGlobalSectionsMap_eq`. -/
theorem derivedFrobeniusBigGlobalSectionsMap_comp_restrict'
    (N : SheafOfModules.{u} (crystallineStructureSheaf T.global)) :
    derivedFrobeniusBigGlobalSectionsMap T N ≫ (frobeniusSigmaRestrictScalarsPlus T).map
        (derivedRestrictModuleGlobalSectionsULiftIso T.global
          (T.frobeniusModulePullback.obj N)).hom =
      derivedChangeBaseBigGlobalSectionsMap (S := T.frobeniusTwistSituation) (S' := T.global)
          T.specSigma T.twistProjection T.twistToClosedFiber_comp_closedFiberMap_specSigma
          ((bigModuleULift T.global).obj N) ≫
        (frobeniusSigmaRestrictScalarsPlus T).map
          (derivedRestrictModuleGlobalSectionsULiftIso T.frobeniusTwistSituation
            (T.sigmaModulePullback.obj N)).hom ≫
        (frobeniusSigmaRestrictScalarsPlus T).map
          (derivedRelativeFrobeniusRestrictGlobalSectionsMap T N) :=
  (derivedFrobeniusBigGlobalSectionsMap_comp_restrict T N).trans
    (book2 _ _ _ _ ((derivedRestrictModuleGlobalSectionsULiftIso T.frobeniusTwistSituation
      (T.sigmaModulePullback.obj N)).hom_inv_id) _)

/-- **The derived comparison for the Frobenius, read on the small crystalline site, is the
pasting of the comparisons for the two halves of the Frobenius square**:
`derivedFrobeniusRestrictGlobalSectionsMap` is `derivedSigmaTwistRestrictGlobalSectionsMap`
followed by `σ_*` of `derivedRelativeFrobeniusRestrictGlobalSectionsMap`. -/
theorem derivedFrobeniusRestrictGlobalSectionsMap_eq
    (N : SheafOfModules.{u} (crystallineStructureSheaf T.global)) :
    derivedFrobeniusRestrictGlobalSectionsMap T N =
      derivedSigmaTwistRestrictGlobalSectionsMap T N ≫
        (frobeniusSigmaRestrictScalarsPlus T).map
          (derivedRelativeFrobeniusRestrictGlobalSectionsMap T N) :=
  (CategoryTheory.whisker_eq (derivedRestrictModuleGlobalSectionsULiftIso T.global N).inv
    (derivedFrobeniusBigGlobalSectionsMap_comp_restrict' T N)).trans
    (book3 _ _ _ _ _)

/-- **The source's factorization of the map of [Stacks, Tag 07N5]**: the composite of the first
two arrows of its proof — the base change map (07QC) followed by the
pullback (07N6) along the relative Frobenius — is the derived comparison for the Frobenius square
taken in one step, `frobeniusBaseChangeArrows07N5`. -/
theorem frobeniusBaseChangeArrows07N5_eq_comp
    (E : Crystalline.FCrystal T) :
    frobeniusBaseChangeArrows07N5 T E =
      baseChangeArrow07QC T E ≫ relativeFrobeniusArrow07N6 T E := by
  refine Eq.trans ?_ ((frobeniusDerivedBaseChangeAdjunction T).homEquiv_naturality_right_symm
    (sigmaTwistSemilinearArrow T E) (relativeFrobeniusArrow07N6 T E))
  exact congrArg ((frobeniusDerivedBaseChangeAdjunction T).homEquiv _ _).symm
    ((congrArg DerivedCategory.Plus.ι.map
      (derivedFrobeniusRestrictGlobalSectionsMap_eq T E.crystal)).trans
      (DerivedCategory.Plus.ι.map_comp _ _))

end Frobenius

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
