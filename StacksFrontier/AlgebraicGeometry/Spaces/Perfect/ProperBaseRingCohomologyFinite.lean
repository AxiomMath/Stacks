module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperCohomologyFiniteOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperHigherDirectImageCoherenceWitness
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingGlobalSectionsTerminalChart
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSpacePresentedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.InjectivePushforwardAcyclicity
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiDirectImageAcyclicity
public import StacksFrontier.Algebra.Homology.DerivedFunctorOfAnAcyclicComplex

/-!
# The cohomology of a coherent module on a space proper over an affine object is finite

Let `T` be an affine object of the big fppf site of a scheme `S`, with `R = Γ(T, 𝒪_T)`
Noetherian, let `f : X ⟶ T` be a proper morphism of algebraic spaces over `S` and `𝓕` a coherent
`𝒪_X`-module. Then every `Hⁱ(X, 𝓕)` is a finite `R`-module, the cohomology being the right derived
functors of global sections read as `R`-modules along `f`
(`AlgebraicGeometry.Space.baseRingGlobalSectionsModule` for
`AlgebraicGeometry.Space.baseRingHomOfMap f`).

This is Stacks 08AS with the base `Spec A` replaced by an affine object `T` of the site over an
arbitrary base scheme `S`; it is the form the proof of Stacks 0CTM uses, where the cohomology of
`X` is read on the spaces-étale model as the derived direct image to the point `(pt, R)`. The
proof is the source's: global sections over `X` are global sections over `T` of the direct image
(`AlgebraicGeometry.Space.pushforwardGlobalSectionsIso`); the higher direct images `Rⁱf_*𝓕` are
coherent (Stacks 08AR), so they have no higher cohomology on the affine `T` (Stacks 03DW), and the
direct image of an injective is acyclic (Stacks 072Z), so the Leray spectral sequence degenerates:
`Hⁱ(X, 𝓕) = Γ(T, Rⁱf_*𝓕)`. Global sections on `T` are the sections over the identity chart, a
terminal object of the small étale site, and those of a coherent module are finite over `R`.

## Main results

* `AlgebraicGeometry.Space.terminalChartSectionsIso`: global sections on `T`, read as abelian
  groups, are the sections over the identity chart.
* `AlgebraicGeometry.Space.terminalChartSectionsSemilinearMap`: the same identification is
  semilinear along `R ≅ 𝒪_T(T)`.
* `AlgebraicGeometry.Space.rightDerivedPushforwardTerminalGlobalSectionsIso`: the degeneration of
  the Leray spectral sequence at an acyclic target, for global sections read as `R`-modules.
* `AlgebraicGeometry.Space.moduleFinite_rightDerived_baseRingGlobalSectionsModule_of_isProper`:
  the finiteness statement.

## References

* [Stacks Project, Tag 08AS](https://stacks.math.columbia.edu/tag/08AS)
* [Stacks Project, Tag 08AR](https://stacks.math.columbia.edu/tag/08AR)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 072Z](https://stacks.math.columbia.edu/tag/072Z)
* [Stacks Project, Tag 0CTM](https://stacks.math.columbia.edu/tag/0CTM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.SiteModules

universe u

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X : AlgebraicSpaces B S hS}
  {T : BigFppfOver B S hS}

/-! ### Global sections on `T` are the sections over the identity chart -/

section Terminal

variable (T) in
/-- Global sections of an `𝒪_T`-module, read as `Γ(T, 𝒪_T)`-modules on the model of the small
étale site. -/
abbrev terminalGlobalSections :
    Modules.{u, u} B S hS (schemeSpace T).1 (schemeSpace T).2 ⥤ ModuleCat.{u} (baseRing B S hS T) :=
  baseRingGlobalSectionsModule B S hS (schemeSpace T) (baseRingHomOfMap (𝟙 (schemeSpace T)))

/-- A global section of an `𝒪_T`-module is its value at the identity chart of `T`, the unit
function being sent along the corresponding morphism `𝒪_T ⟶ M`. -/
def terminalChartSectionsEquiv (M : Modules.{u, u} B S hS (schemeSpace T).1 (schemeSpace T).2) :
    (terminalGlobalSections B S hS T).obj M ≃ M.val.obj (op (idEtaleChart B S hS T)) :=
  (modelSectionsHomEquiv B S hS (schemeSpace T) (baseRingHomOfMap (𝟙 (schemeSpace T))) M).trans
    ((SheafOfModules.unitHomEquiv M).trans
      (Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal M
        (isTerminalIdEtaleChart B S hS T)))

/-- `terminalChartSectionsEquiv` sends a global section to the value at the unit function of the
corresponding morphism `𝒪_T ⟶ M` over the identity chart. -/
theorem terminalChartSectionsEquiv_apply
    (M : Modules.{u, u} B S hS (schemeSpace T).1 (schemeSpace T).2)
    (s : (terminalGlobalSections B S hS T).obj M) :
    terminalChartSectionsEquiv B S hS M s =
      (modelSectionsHomEquiv B S hS (schemeSpace T) (baseRingHomOfMap (𝟙 (schemeSpace T))) M
        s).val.app (op (idEtaleChart B S hS T))
          (1 : chartRing B S hS (schemeSpace T).1 (schemeSpace T).2 (idEtaleChart B S hS T)) :=
  rfl

/-- `terminalChartSectionsEquiv` is additive. -/
theorem terminalChartSectionsEquiv_add
    (M : Modules.{u, u} B S hS (schemeSpace T).1 (schemeSpace T).2)
    (s t : (terminalGlobalSections B S hS T).obj M) :
    terminalChartSectionsEquiv B S hS M (s + t) =
      terminalChartSectionsEquiv B S hS M s + terminalChartSectionsEquiv B S hS M t := by
  rw [terminalChartSectionsEquiv_apply, terminalChartSectionsEquiv_apply,
    terminalChartSectionsEquiv_apply, modelSectionsHomEquiv_add]
  rfl

/-- **Global sections on `T` are the sections over the identity chart**, as abelian groups,
naturally in the module. -/
def terminalChartSectionsIso :
    terminalGlobalSections B S hS T ⋙
        forget₂ (ModuleCat.{u} (baseRing B S hS T)) AddCommGrpCat.{u} ≅
      Stacks.Cohomology.SiteInverseLimits.sectionsFunctor
        (smallEtaleRingedSite B S hS (schemeSpace T).1 (schemeSpace T).2) (idEtaleChart B S hS T) :=
  NatIso.ofComponents
    (fun M => (AddEquiv.mk (terminalChartSectionsEquiv B S hS M)
      (terminalChartSectionsEquiv_add B S hS M)).toAddCommGrpIso)
    (fun {M M'} g => by
      ext s
      change terminalChartSectionsEquiv B S hS M' ((terminalGlobalSections B S hS T).map g s) =
        (g.val.app (op (idEtaleChart B S hS T))).hom (terminalChartSectionsEquiv B S hS M s)
      rw [terminalChartSectionsEquiv_apply, terminalChartSectionsEquiv_apply,
        modelSectionsHomEquiv_naturality]
      rfl)

/-- The morphism `T ⟶ T` that the identity of `T` induces on the identity chart is the identity. -/
theorem chartToBaseOfMap_id_idEtaleChart :
    chartToBaseOfMap (𝟙 (schemeSpace T)) (idEtaleChart B S hS T) = 𝟙 T :=
  yoneda.map_injective ((yoneda_map_chartToBaseOfMap (𝟙 (schemeSpace T))
    (idEtaleChart B S hS T)).trans
      (by exact (Category.comp_id (𝟙 (yoneda.obj T))).trans (yoneda.map_id T).symm))

variable (T) in
/-- The ring map `Γ(T, 𝒪_T) ⟶ 𝒪_T(T)` to the functions at the identity chart: the pullback of
global functions along the identity of `T`. It is the identity. -/
def terminalChartRingHom :
    baseRing B S hS T →+* chartRing B S hS (schemeSpace T).1 (schemeSpace T).2
      (idEtaleChart B S hS T) where
  toFun r := (globalFunctionsOfMap (𝟙 (schemeSpace T)) r).1 (op (idEtaleChart B S hS T))
  map_one' := congrArg (fun a => a.1 (op (idEtaleChart B S hS T)))
    (map_one (globalFunctionsOfMap (𝟙 (schemeSpace T))))
  map_mul' r s := congrArg (fun a => a.1 (op (idEtaleChart B S hS T)))
    (map_mul (globalFunctionsOfMap (𝟙 (schemeSpace T))) r s)
  map_zero' := congrArg (fun a => a.1 (op (idEtaleChart B S hS T)))
    (map_zero (globalFunctionsOfMap (𝟙 (schemeSpace T))))
  map_add' r s := congrArg (fun a => a.1 (op (idEtaleChart B S hS T)))
    (map_add (globalFunctionsOfMap (𝟙 (schemeSpace T))) r s)

/-- `terminalChartRingHom` is the identity of `Γ(T, 𝒪_T)`. -/
theorem terminalChartRingHom_apply (r : baseRing B S hS T) :
    terminalChartRingHom B S hS T r = r := by
  change (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
    (chartToBaseOfMap (𝟙 (schemeSpace T)) (idEtaleChart B S hS T))).op).hom r = r
  have h2 : (BigFppfOver.toScheme B S hS).map
      (chartToBaseOfMap (𝟙 (schemeSpace T)) (idEtaleChart B S hS T)) = 𝟙 _ :=
    (congrArg (BigFppfOver.toScheme B S hS).map (chartToBaseOfMap_id_idEtaleChart B S hS)).trans
      ((BigFppfOver.toScheme B S hS).map_id T)
  rw [h2]
  exact congrArg (fun φ => φ.hom r) ((congrArg Scheme.Γ.map op_id).trans (Scheme.Γ.map_id _))

/-- `terminalChartRingHom` is surjective. -/
theorem surjective_terminalChartRingHom : Function.Surjective (terminalChartRingHom B S hS T) :=
  fun r => ⟨r, terminalChartRingHom_apply B S hS r⟩

/-- Multiplication by a global function `a`, followed by `g : 𝒪_X ⟶ M`, sends the unit function
at a chart `W` to `a(W)` times the value of `g` there. -/
theorem unitModuleMul_comp_val_app_one (a : GlobalFunctionRing (structureSheaf B S hS X.1 X.2))
    {M : Modules.{u, u} B S hS X.1 X.2} (g : unitModule B S hS X.2 ⟶ M)
    (W : SmallEtale B S hS X.1) :
    (unitModuleMul B S hS X a ≫ g).val.app (op W) (1 : chartRing B S hS X.1 X.2 W) =
      (show chartRing B S hS X.1 X.2 W from a.1 (op W)) •
        g.val.app (op W) (1 : chartRing B S hS X.1 X.2 W) := by
  change (g.val.app (op W)).hom ((unitModuleMul B S hS X a).val.app (op W)
    (1 : chartRing B S hS X.1 X.2 W)) = _
  rw [unitModuleMul_val_app_one]
  refine (congrArg (g.val.app (op W)).hom (mul_one
    (show chartRing B S hS X.1 X.2 W from a.1 (op W))).symm).trans ?_
  exact (g.val.app (op W)).hom.map_smul _ _

/-- **Global sections on `T` are the sections over the identity chart**, semilinearly along
`Γ(T, 𝒪_T) ⟶ 𝒪_T(T)`: multiplication by `r` is precomposition with multiplication by `r` on
`𝒪_T`, which at the identity chart is multiplication by `r`. -/
def terminalChartSectionsSemilinearMap
    (M : Modules.{u, u} B S hS (schemeSpace T).1 (schemeSpace T).2) :
    (terminalGlobalSections B S hS T).obj M →ₛₗ[terminalChartRingHom B S hS T]
      M.val.obj (op (idEtaleChart B S hS T)) where
  toFun := terminalChartSectionsEquiv B S hS M
  map_add' := terminalChartSectionsEquiv_add B S hS M
  map_smul' r s := by
    rw [terminalChartSectionsEquiv_apply, terminalChartSectionsEquiv_apply,
      modelSectionsHomEquiv_smul]
    exact unitModuleMul_comp_val_app_one B S hS (X := schemeSpace T) _ _ (idEtaleChart B S hS T)

/-- `terminalChartSectionsSemilinearMap` is bijective. -/
theorem bijective_terminalChartSectionsSemilinearMap
    (M : Modules.{u, u} B S hS (schemeSpace T).1 (schemeSpace T).2) :
    Function.Bijective (terminalChartSectionsSemilinearMap B S hS M) :=
  (terminalChartSectionsEquiv B S hS M).bijective

/-- **Global sections on `T` of a module are finite over `Γ(T, 𝒪_T)`** as soon as its sections
over the identity chart are finite over the functions there. -/
theorem moduleFinite_terminalGlobalSections
    (M : Modules.{u, u} B S hS (schemeSpace T).1 (schemeSpace T).2)
    (hM : Module.Finite (chartRing B S hS (schemeSpace T).1 (schemeSpace T).2
      (idEtaleChart B S hS T)) (M.val.obj (op (idEtaleChart B S hS T)))) :
    Module.Finite (baseRing B S hS T) ((terminalGlobalSections B S hS T).obj M) := by
  have : RingHomSurjective (terminalChartRingHom B S hS T) :=
    ⟨surjective_terminalChartRingHom B S hS⟩
  exact ((terminalChartSectionsSemilinearMap B S hS M).finite_iff_of_bijective
    (bijective_terminalChartSectionsSemilinearMap B S hS M)).2 hM

/-- **Acyclicity for global sections on `T` read as `R`-modules** follows from acyclicity for the
sections over the identity chart: the two agree as abelian groups, and forgetting the module
structure is exact and detects zero objects. -/
theorem isZero_rightDerived_terminalGlobalSections
    [EnoughInjectives (Modules.{u, u} B S hS (schemeSpace T).1 (schemeSpace T).2)]
    (M : Modules.{u, u} B S hS (schemeSpace T).1 (schemeSpace T).2) (p : ℕ)
    (h : IsZero (((Stacks.Cohomology.SiteInverseLimits.sectionsFunctor
      (smallEtaleRingedSite B S hS (schemeSpace T).1 (schemeSpace T).2)
        (idEtaleChart B S hS T)).rightDerived p).obj M)) :
    IsZero (((terminalGlobalSections B S hS T).rightDerived p).obj M) := by
  let e := terminalChartSectionsIso B S hS (T := T)
  obtain ⟨e'⟩ := Stacks.Cohomology.rightDerived_comp_iso_of_preservesHomology
    (terminalGlobalSections B S hS T)
    (forget₂ (ModuleCat.{u} (baseRing B S hS T)) AddCommGrpCat.{u})
    p M
  have h' : IsZero ((forget₂ (ModuleCat.{u} (baseRing B S hS T)) AddCommGrpCat.{u}).obj
      (((terminalGlobalSections B S hS T).rightDerived p).obj M)) :=
    h.of_iso (e' ≪≫
      { hom := (NatTrans.rightDerived e.hom p).app M
        inv := (NatTrans.rightDerived e.inv p).app M
        hom_inv_id := by
          rw [← NatTrans.comp_app, ← NatTrans.rightDerived_comp, e.hom_inv_id,
            NatTrans.rightDerived_id, NatTrans.id_app]
        inv_hom_id := by
          rw [← NatTrans.comp_app, ← NatTrans.rightDerived_comp, e.inv_hom_id,
            NatTrans.rightDerived_id, NatTrans.id_app] })
  rw [ModuleCat.isZero_iff_subsingleton]
  exact AddCommGrpCat.isZero_iff_subsingleton.1 h'

end Terminal

/-! ### The two acyclicity inputs -/

section Acyclic

/-- **A quasi-coherent module on an affine `T` is acyclic for global sections read as
`R`-modules** (Stacks 03DW): the sections over the affine identity chart have no higher derived
functors on quasi-coherent modules. -/
theorem acyclic_terminalGlobalSections_of_isQuasicoherentOnSite
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (M : Modules.{u, u} B S hS (schemeSpace T).1 (schemeSpace T).2)
    (hM : M.IsQuasicoherentOnSite) :
    have := enoughInjectives_modules B S hS (schemeSpace T).1 (schemeSpace T).2
    Stacks.RightDerivedComp.acyclic (terminalGlobalSections B S hS T) M := by
  intro _ p hp
  exact @isZero_rightDerived_terminalGlobalSections B S hS T
    (enoughInjectives_modules B S hS _ _) M p
    (isZero_rightDerived_sectionsFunctor_of_isAffineChart B S hS _ _ M hM
      (idEtaleChart B S hS T) hT p hp)

/-- **The direct image of an injective module is acyclic for global sections on `T` read as
`R`-modules** (Stacks 072Z): its underlying abelian sheaf is totally acyclic, so it has no higher
cohomology over the identity chart. -/
theorem acyclic_terminalGlobalSections_modulePushforward_of_injective (f : X ⟶ schemeSpace T)
    (I : Modules.{u, u} B S hS X.1 X.2) (hI : Injective I) :
    have := enoughInjectives_modules B S hS (schemeSpace T).1 (schemeSpace T).2
    Stacks.RightDerivedComp.acyclic (terminalGlobalSections B S hS T)
      ((modulePushforward B S hS f).obj I) := by
  intro _ p hp
  refine @isZero_rightDerived_terminalGlobalSections B S hS T
    (enoughInjectives_modules B S hS _ _) _ p ?_
  have : HasWeakSheafify (smallEtaleRingedSite B S hS (yoneda.obj T)
      (isAlgebraicSpace_yoneda B S hS T)).J (Type u) :=
    inferInstanceAs (HasWeakSheafify (SmallEtale.topology B S hS (yoneda.obj T)) (Type u))
  have := enoughInjectives_modules B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)
  have : HasExt.{u + 1} (Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) :=
    HasExt.standard _
  have := enoughInjectives_sheaf_smallEtale B S hS (yoneda.obj T)
  have := hasExt_sheaf_smallEtale B S hS (yoneda.obj T)
  have := enoughInjectives_sheaf_smallEtaleRingedSite B S hS (yoneda.obj T)
    (isAlgebraicSpace_yoneda B S hS T)
  have := hasExt_sheaf_smallEtaleRingedSite B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)
  have : EnoughInjectives (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)).O)) :=
    enoughInjectives_modules B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)
  have h0 := Stacks.Cohomology.isZero_rightDerived_evaluation_of_isTotallyAcyclic.{u, u + 1}
    (smallEtaleRingedSite B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)).J
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)).O) _
    (isTotallyAcyclic_modulePushforward_of_injective (hZ := hI) B S hS f I)
    (idEtaleChart B S hS T) p hp
  obtain ⟨e⟩ := Stacks.Cohomology.rightDerived_comp_iso_of_preservesHomology
    (SheafOfModules.evaluation
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (schemeSpace T).1
        (schemeSpace T).2).O)) (op (idEtaleChart B S hS T)))
    (forget₂ (ModuleCat.{u, u}
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (schemeSpace T).1
        (schemeSpace T).2).O)).obj.obj (op (idEtaleChart B S hS T)))) AddCommGrpCat.{u}) p
    ((modulePushforward B S hS f).obj I)
  exact (@AddCommGrpCat.isZero_of_subsingleton _ (ModuleCat.isZero_iff_subsingleton.1 h0)).of_iso
    e.symm

end Acyclic

/-! ### The degeneration of the Leray spectral sequence and Stacks 08AS over `T` -/

section Leray

/-- **The degeneration of the Leray spectral sequence of `f : X ⟶ T` at an affine target**, for
global sections read as `Γ(T, 𝒪_T)`-modules: if every higher direct image `R^q f_*𝓕` is acyclic
for global sections on `T`, then `Rⁿ(Γ(T, f_* −))(𝓕) = Γ(T, Rⁿf_*𝓕)`. The direct image of an
injective resolution of `𝓕` is a complex of acyclic objects (Stacks 072Z) whose cohomology is the
higher direct images. -/
def rightDerivedPushforwardTerminalGlobalSectionsIso (f : X ⟶ schemeSpace T)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (hcoh : ∀ q : ℕ,
      have := hasInjectiveResolutions_modules B S hS X.1 X.2
      have := enoughInjectives_modules B S hS (schemeSpace T).1 (schemeSpace T).2
      Stacks.RightDerivedComp.acyclic (terminalGlobalSections B S hS T)
        (((modulePushforward B S hS f).rightDerived q).obj F)) (n : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    ((modulePushforward B S hS f ⋙ terminalGlobalSections B S hS T).rightDerived n).obj F ≅
      (terminalGlobalSections B S hS T).obj (((modulePushforward B S hS f).rightDerived n).obj F) :=
  have := enoughInjectives_modules B S hS X.1 X.2
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := enoughInjectives_modules B S hS (schemeSpace T).1 (schemeSpace T).2
  have := (baseRingTensorModuleAdjunction B S hS (schemeSpace T)
    (baseRingHomOfMap (𝟙 (schemeSpace T)))).isRightAdjoint
  (injectiveResolution F).isoRightDerivedObj
      (modulePushforward B S hS f ⋙ terminalGlobalSections B S hS T) n ≪≫
    Stacks.Cohomology.RightDerivedCoEdge.homologyIsoMapHomologyOfAcyclic
      (terminalGlobalSections B S hS T)
      (Stacks.RightDerivedComp.mapCocomplex (modulePushforward B S hS f)
        (injectiveResolution F))
      (fun q => acyclic_terminalGlobalSections_modulePushforward_of_injective B S hS f _
        ((injectiveResolution F).injective q))
      (fun q => Stacks.Cohomology.RightDerivedCoEdge.acyclic_of_iso _
        ((injectiveResolution F).isoRightDerivedObj (modulePushforward B S hS f) q) (hcoh q)) n ≪≫
    (terminalGlobalSections B S hS T).mapIso
      ((injectiveResolution F).isoRightDerivedObj (modulePushforward B S hS f) n).symm

/-- An affine object `T` of the site with `Γ(T, 𝒪_T)` Noetherian is locally Noetherian, read as an
algebraic space through its étale charts. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_schemeSpace
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) [IsNoetherianRing (baseRing B S hS T)] :
    HasEtaleLocalProperty B S hS (schemeSpace T).1
      (fun V : Scheme.{u} ↦ IsLocallyNoetherian V) := by
  have hTN : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T) := by
    have : IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
      inferInstanceAs (IsNoetherianRing (baseRing B S hS T))
    have : IsLocallyNoetherian (Spec Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) :=
      isLocallyNoetherian_Spec.mpr inferInstance
    exact isLocallyNoetherian_of_isOpenImmersion ((BigFppfOver.toScheme B S hS).obj T).isoSpec.hom
  exact (exists_atlas_iff_of_representable B S hS (yoneda.obj T)
    (fun V : Scheme.{u} ↦ IsLocallyNoetherian V) T (Iso.refl _)).2 hTN

/-- **Stacks 08AS over an affine object of the site.** Let `T` be affine with `R = Γ(T, 𝒪_T)`
Noetherian, `f : X ⟶ T` a proper morphism of algebraic spaces and `𝓕` a coherent `𝒪_X`-module.
Then `Hⁿ(X, 𝓕)` is a finite `R`-module for every `n`, the cohomology being the right derived
functors of global sections read as `R`-modules along `f`.

`Hⁿ(X, 𝓕) = Hⁿ(Γ(T, f_* −))(𝓕) = Γ(T, Rⁿf_*𝓕)`, the higher direct images being coherent
(Stacks 08AR) hence acyclic on the affine `T` (Stacks 03DW); and the global sections of a
coherent module on `T` are its sections over the affine identity chart, which are finite. -/
theorem moduleFinite_rightDerived_baseRingGlobalSectionsModule_of_isProper
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) [IsNoetherianRing (baseRing B S hS T)]
    (f : X ⟶ schemeSpace T) (hf : IsProper B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F) (n : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    Module.Finite (baseRing B S hS T)
      (((baseRingGlobalSectionsModule B S hS X (baseRingHomOfMap f)).rightDerived n).obj F) := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := enoughInjectives_modules B S hS (schemeSpace T).1 (schemeSpace T).2
  have := modulePushforward_additive B S hS f
  have hY := hasEtaleLocalProperty_isLocallyNoetherian_schemeSpace B S hS hT
  have hcohR : ∀ q, IsCoherent B S hS (schemeSpace T).1 (schemeSpace T).2
      (((modulePushforward B S hS f).rightDerived q).obj F) :=
    fun q => isCoherent_rightDerived_of_isProper B S hS f hf hY F hF q
  have e :=
    (Functor.rightDerivedIsoOfNatIso (pushforwardGlobalSectionsIso B S hS f).symm n).app F ≪≫
    rightDerivedPushforwardTerminalGlobalSectionsIso B S hS f F
      (fun q => acyclic_terminalGlobalSections_of_isQuasicoherentOnSite B S hS hT _
        (hcohR q).toIsQuasicoherentOnSite) n
  have hfin := moduleFinite_terminalGlobalSections B S hS
    (((modulePushforward B S hS f).rightDerived n).obj F)
    (moduleFinite_sections_of_isCoherent B S hS _ _ _ (hcohR n) (V := idEtaleChart B S hS T) hT)
  exact Module.Finite.equiv e.symm.toLinearEquiv

end Leray

end AlgebraicGeometry.Space

end
