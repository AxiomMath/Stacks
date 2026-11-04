module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomStageComparison

/-!
# Bijectivity of the comparison of Stacks 08JY at a stage

The comparison `AlgebraicGeometry.Space.HomSituation.stageComparison` of the proof of Stacks 08JY
sends the sections `Hom(Lg^*𝒪, Lg^*K)`, `K = Rf_*R𝓗om(P, 𝒢[0])`, over a test scheme `g : T ⟶ Y`
to `Hom(h^*𝓕, h^*𝒢)`. This file computes the components of its first two steps and proves it
bijective at every test scheme at which the base change map of Stacks 08JQ is an isomorphism
(`AlgebraicGeometry.Space.HomSituation.bijective_stageComparison_app`): the comparison is
composition with that map, adjunction along `f_T`, the tensor-hom adjunction and degree-zero
cohomology through the approximation `α : P ⟶ 𝓕[0]`.

## Implementation notes

The terms of the different steps are elaborated in files with different local instances, so the
same object of a derived category occurs in several spellings that agree only after unfolding.
The elaborator compares such terms by unfolding projections first, which does not terminate in
time; the equations are therefore closed either by `congr!`, which compares arguments first, or
by `rfl` once the two sides have the same shape, and the generic bijectivity steps are
instantiated with their intermediate objects given explicitly in the spelling of the comparison.

No tag is placed: these are steps of the proof of Stacks 08JY.

## References

* [Stacks Project, Tag 08JY](https://stacks.math.columbia.edu/tag/08JY)
* [Stacks Project, Tag 08JQ](https://stacks.math.columbia.edu/tag/08JQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace HomSituation

variable (v : HomSituation B S hS) (Pm : toposDerived B S hS v.X)
/-- The component of the tensor pairing of a stage at a test scheme, through the map of
Stacks 08JF. -/
theorem stageTensorPairing_app (T : v.SchemesOver)
    (y : (toposDerivedPullbackData B S hS).relHomObj (baseChangeProjectionCone v.f)
      (structureDerived v.X) (((smallEtaleDerivedSheafHom B S hS v.X).obj (op Pm)).obj
        ((DerivedCategory.singleFunctor (toposModules B S hS v.X) 0).obj v.G)) T) :
    (v.stageTensorPairing Pm).app (op T) y =
      (smallEtaleDerivedTensorStructureIso ((baseChangeSpaces v.f).obj T)
          ((smallEtaleDerivedModulePullback B S hS
            ((baseChangeProjectionCone v.f).leg T)).obj Pm)).hom ≫
        ((smallEtaleDerivedTensorSheafHomAdjunction B S hS ((baseChangeSpaces v.f).obj T)
          ((smallEtaleDerivedModulePullback B S hS
            ((baseChangeProjectionCone v.f).leg T)).obj Pm)).homEquiv _ _).symm
          ((smallEtaleDerivedModulePullbackUnitIso ((baseChangeProjectionCone v.f).leg T)).inv ≫ y ≫
            smallEtaleDerivedPullbackSheafHomMap ((baseChangeProjectionCone v.f).leg T) Pm
              ((DerivedCategory.singleFunctor (toposModules B S hS v.X) 0).obj v.G)) := by
  have h := relHomTensorPairing_smallEtale_app (toposDerivedPullbackData_isCoherent B S hS)
    (baseChangeProjectionCone v.f) Pm
    ((DerivedCategory.singleFunctor (toposModules B S hS v.X) 0).obj v.G) T y
  refine Eq.trans ?_ (h.trans ?_)
  · unfold stageTensorPairing
    congr!
  · congr!

/-- The component of pullback along the projections followed by the unit and counit of
`Lf^* ⊣ Rf_*`, at a test scheme, through the two factorisations of `X_T ⟶ base`. -/
theorem stageBaseChangeCounit_app (T : v.SchemesOver) (h₁ : v.StageTriangle₁ T)
    (h₂ : v.StageTriangle₂ T)
    (x : (toposDerivedPullbackData B S hS).relHomObj (schemesOverCone v.base)
      (structureDerived v.base) ((smallEtaleDerivedModulePushforward B S hS v.f).obj
        (((smallEtaleDerivedSheafHom B S hS v.X).obj (op Pm)).obj
          ((DerivedCategory.singleFunctor (toposModules B S hS v.X) 0).obj v.G))) T) :
    (v.stageBaseChangeCounit Pm).app (op T) x =
      CategoryStruct.comp
        (Y := ((toposDerivedPullbackData B S hS).pull ((baseChangeProjectionCone v.f).leg T)).obj
          (((toposDerivedPullbackData B S hS).pull v.f).obj (structureDerived v.base)))
        (((toposDerivedPullbackData B S hS).pull ((baseChangeProjectionCone v.f).leg T)).map
          (smallEtaleDerivedModulePullbackUnitIso v.f).inv)
        (CategoryStruct.comp
          (Y := ((toposDerivedPullbackData B S hS).pull ((baseChangeProjectionCone v.f).leg T)).obj
            (((toposDerivedPullbackData B S hS).pull v.f).obj
              ((smallEtaleDerivedModulePushforward B S hS v.f).obj
                (((smallEtaleDerivedSheafHom B S hS v.X).obj (op Pm)).obj
                  ((DerivedCategory.singleFunctor (toposModules B S hS v.X) 0).obj v.G)))))
          (Functor.transportHom ((toposDerivedPullbackData B S hS).triangle h₂).symm
            (Functor.conjHom ((toposDerivedPullbackData B S hS).triangle h₁) x))
          (((toposDerivedPullbackData B S hS).pull ((baseChangeProjectionCone v.f).leg T)).map
            ((smallEtaleDerivedAdjunction B S hS v.f).counit.app
              (((smallEtaleDerivedSheafHom B S hS v.X).obj (op Pm)).obj
                ((DerivedCategory.singleFunctor (toposModules B S hS v.X) 0).obj v.G))))) := by
  have e₁ := (toposDerivedPullbackData B S hS).relHomBimap_app
    (toposDerivedPullbackData_isCoherent B S hS) (baseChangeProjectionCone v.f)
    (smallEtaleDerivedModulePullbackUnitIso v.f).inv
    ((smallEtaleDerivedAdjunction B S hS v.f).counit.app
      (((smallEtaleDerivedSheafHom B S hS v.X).obj (op Pm)).obj
        ((DerivedCategory.singleFunctor (toposModules B S hS v.X) 0).obj v.G))) T
    ((relHomBaseChange v.f (toposDerivedPullbackData B S hS)
      (toposDerivedPullbackData_isCoherent B S hS) (structureDerived v.base)
      ((smallEtaleDerivedModulePushforward B S hS v.f).obj
        (((smallEtaleDerivedSheafHom B S hS v.X).obj (op Pm)).obj
          ((DerivedCategory.singleFunctor (toposModules B S hS v.X) 0).obj v.G)))).app (op T) x)
  have e₂ := relHomBaseChange_app v.f (toposDerivedPullbackData B S hS)
    (toposDerivedPullbackData_isCoherent B S hS) (structureDerived v.base)
    ((smallEtaleDerivedModulePushforward B S hS v.f).obj
      (((smallEtaleDerivedSheafHom B S hS v.X).obj (op Pm)).obj
        ((DerivedCategory.singleFunctor (toposModules B S hS v.X) 0).obj v.G))) T x
  refine Eq.trans ?_ (e₁.trans ?_)
  · unfold stageBaseChangeCounit
    rfl
  · rw [e₂]
    exact rfl

variable {Pm} (α : Pm ⟶ (DerivedCategory.singleFunctor (toposModules B S hS v.X) 0).obj v.F)
  (hiso : ∀ i : ℤ, -1 < i →
    IsIso ((DerivedCategory.homologyFunctor (toposModules B S hS v.X) i).map α))
  (hepi : Epi ((DerivedCategory.homologyFunctor (toposModules B S hS v.X) (-1)).map α))

/-- **The comparison of Stacks 08JY is bijective at every test scheme**, as soon as the base
change map of Stacks 08JQ there is an isomorphism: it is the composite of degree-zero cohomology
through `α`, the tensor-hom adjunction, adjunction along `f_T` and composition with the base
change map. -/
theorem bijective_stageComparison_app (T : v.SchemesOver) (h₁ : v.StageTriangle₁ T)
    (h₂ : v.StageTriangle₂ T) (hβ : IsIso (v.stageBaseChangeMap Pm T h₁ h₂)) :
    Function.Bijective ((v.stageComparison α hiso hepi).app (op T)) := by
  have hθ := Functor.bijective_transportHom_conjHom
    ((toposDerivedPullbackData B S hS).triangle h₁)
    ((toposDerivedPullbackData B S hS).triangle h₂).symm
    (smallEtaleDerivedAdjunction B S hS ((baseChangeSpacesInclusion v.f).app T))
    (smallEtaleDerivedModulePullbackUnitIso ((baseChangeProjectionCone v.f).leg T)).inv
    (smallEtaleDerivedModulePullbackUnitIso v.f).inv
    ((smallEtaleDerivedAdjunction B S hS v.f).counit.app
      (((smallEtaleDerivedSheafHom B S hS v.X).obj (op Pm)).obj
        ((DerivedCategory.singleFunctor (toposModules B S hS v.X) 0).obj v.G)))
    (smallEtaleDerivedPullbackSheafHomMap ((baseChangeProjectionCone v.f).leg T) Pm
      ((DerivedCategory.singleFunctor (toposModules B S hS v.X) 0).obj v.G))
    (((smallEtaleDerivedSheafHom B S hS ((baseChangeSpaces v.f).obj T)).obj
        (op ((smallEtaleDerivedModulePullback B S hS
          ((baseChangeProjectionCone v.f).leg T)).obj Pm))).map
      (smallEtaleDerivedModulePullbackQComparison ((baseChangeProjectionCone v.f).leg T)
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj v.G)))
    (v.stageBaseChangeMap Pm T h₁ h₂) (hβ := hβ) (v.homEquiv_symm_stageBaseChangeMap Pm T h₁ h₂)
  have h2 := Adjunction.bijective_comp_homEquiv_symm_comp
    (smallEtaleDerivedTensorSheafHomAdjunction B S hS ((baseChangeSpaces v.f).obj T)
      ((smallEtaleDerivedModulePullback B S hS ((baseChangeProjectionCone v.f).leg T)).obj Pm))
    (smallEtaleDerivedTensorStructureIso ((baseChangeSpaces v.f).obj T)
      ((smallEtaleDerivedModulePullback B S hS
        ((baseChangeProjectionCone v.f).leg T)).obj Pm)).hom
    (smallEtaleDerivedModulePullbackQComparison ((baseChangeProjectionCone v.f).leg T)
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj v.G))
    (smallEtaleDegreeZeroTargetIso ((baseChangeProjectionCone v.f).leg T) v.G).hom
    (hτ := (smallEtaleDegreeZeroTargetIso ((baseChangeProjectionCone v.f).leg T) v.G).isIso_hom)
    (B := (smallEtaleDerivedModulePullback B S hS ((baseChangeProjectionCone v.f).leg T)).obj
      ((DerivedCategory.singleFunctor (toposModules B S hS v.X) 0).obj v.G))
    (fun x => (smallEtaleDerivedModulePullbackUnitIso ((baseChangeProjectionCone v.f).leg T)).inv ≫
      (CategoryStruct.comp
        (Y := ((toposDerivedPullbackData B S hS).pull ((baseChangeProjectionCone v.f).leg T)).obj
          (((toposDerivedPullbackData B S hS).pull v.f).obj (structureDerived v.base)))
        (((toposDerivedPullbackData B S hS).pull ((baseChangeProjectionCone v.f).leg T)).map
          (smallEtaleDerivedModulePullbackUnitIso v.f).inv)
        (CategoryStruct.comp
          (Y := ((toposDerivedPullbackData B S hS).pull ((baseChangeProjectionCone v.f).leg T)).obj
            (((toposDerivedPullbackData B S hS).pull v.f).obj
              ((smallEtaleDerivedModulePushforward B S hS v.f).obj
                (((smallEtaleDerivedSheafHom B S hS v.X).obj (op Pm)).obj
                  ((DerivedCategory.singleFunctor (toposModules B S hS v.X) 0).obj v.G)))))
          (Functor.transportHom ((toposDerivedPullbackData B S hS).triangle h₂).symm
            (Functor.conjHom ((toposDerivedPullbackData B S hS).triangle h₁) x))
          (((toposDerivedPullbackData B S hS).pull ((baseChangeProjectionCone v.f).leg T)).map
            ((smallEtaleDerivedAdjunction B S hS v.f).counit.app
              (((smallEtaleDerivedSheafHom B S hS v.X).obj (op Pm)).obj
                ((DerivedCategory.singleFunctor (toposModules B S hS v.X) 0).obj v.G)))))) ≫
      smallEtaleDerivedPullbackSheafHomMap ((baseChangeProjectionCone v.f).leg T) Pm
        ((DerivedCategory.singleFunctor (toposModules B S hS v.X) 0).obj v.G)) hθ
  have h45 := fun ψ => relHomDegreeZero_toposPullbackData_app_apply
    (hZ := fun j => isLE_smallEtaleDerivedModulePullback_leg_of_approximation
      (baseChangeProjectionCone v.f) α hiso j)
    (hθ := fun j => isIso_degreeZeroCompare_toposPullbackData_of_approximation
      (baseChangeProjectionCone v.f) α hiso hepi j)
    (baseChangeProjectionCone v.f) Pm α v.G T ψ
  obtain ⟨dZ, hdZ⟩ : ∃ dZ : _ ≃ _, ∀ ψ, (v.stageDegreeZero α hiso hepi).app (op T) ψ =
      dZ (ψ ≫ (smallEtaleDerivedModulePullbackQComparison ((baseChangeProjectionCone v.f).leg T)
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj v.G)) ≫
          (smallEtaleDegreeZeroTargetIso ((baseChangeProjectionCone v.f).leg T) v.G).hom) :=
    ⟨_, h45⟩
  refine (congrArg Function.Bijective ?_).mpr (dZ.bijective.comp h2)
  funext x
  refine (v.stageComparison_app α hiso hepi T x).trans
    ((hdZ _).trans (congrArg dZ (congrArg (· ≫ _) ?_)))
  refine (v.stageTensorPairing_app Pm T _).trans ?_
  erw [v.stageBaseChangeCounit_app Pm T h₁ h₂ x]

/-- The degreewise hypotheses of Stacks 08JQ for `𝒢[0]`: quasi-coherent and flat over the base in
every degree. -/
theorem single_X_isQuasicoherentOnSite_and_isFlatOver
    (hGfl : IsFlatOver B S hS v.X.2 v.f.hom v.G) (n : ℤ) :
    (((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj v.G).X n).IsQuasicoherentOnSite ∧
      IsFlatOver B S hS v.X.2 v.f.hom
        (((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj v.G).X n) := by
  by_cases hn : n = 0
  · subst hn
    exact ⟨SheafOfModules.IsQuasicoherentOnSite.of_iso
        (HomologicalComplex.singleObjXSelf _ _ v.G).symm v.quasicoherent_G,
      IsFlatOver.of_iso B S hS v.X.2 (HomologicalComplex.singleObjXSelf _ _ v.G).symm hGfl⟩
  · exact ⟨SheafOfModules.IsQuasicoherentOnSite.of_isZero
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn),
      isFlatOver_of_isZero B S hS v.f (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)⟩

/-- **The comparison of Stacks 08JY is an isomorphism** for `P` perfect, `f` quasi-compact and
quasi-separated and `𝒢` flat over the base: at every test scheme it is bijective, the base change
map of Stacks 08JQ there being an isomorphism by Stacks 08JQ, part (1). -/
theorem isIso_stageComparison
    (hPm : (smallEtaleRingedSite B S hS v.X.1 v.X.2).IsPerfect Pm)
    (hfqc : IsQuasiCompact B S hS v.f.hom) (hfqs : IsQuasiSeparated B S hS v.f.hom)
    (hGfl : IsFlatOver B S hS v.X.2 v.f.hom v.G) :
    IsIso (v.stageComparison α hiso hepi) := by
  have h : ∀ T : v.SchemesOverᵒᵖ, IsIso ((v.stageComparison α hiso hepi).app T) := fun T => by
    refine (isIso_iff_bijective _).2 (v.bijective_stageComparison_app α hiso hepi T.unop
      (baseChangeInclusion_comp_hom v.f T.unop) rfl ?_)
    refine cast (congrArg IsIso (v.stageBaseChangeMap_eq Pm T.unop _ _
      (v.isPullback_baseChangeSquare T.unop).w).symm) ?_
    exact (isIso_smallEtaleDerivedSheafHomBaseChangeMap_tag v.f hfqc hfqs Pm _
      (fun n => (v.single_X_isQuasicoherentOnSite_and_isFlatOver hGfl n).1)
      (fun n => (v.single_X_isQuasicoherentOnSite_and_isFlatOver hGfl n).2)).1 hPm
      ⟨0, fun i hi => HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)⟩ _ _ _
      (v.isPullback_baseChangeSquare T.unop)
  exact NatIso.isIso_of_isIso_app _

end HomSituation

end AlgebraicGeometry.Space

end
