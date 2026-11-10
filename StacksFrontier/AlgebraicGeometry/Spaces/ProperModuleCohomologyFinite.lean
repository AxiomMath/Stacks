module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.RightDerivedModuleFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowTwistWitness
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissageUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardBaseScalars
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperCohomologyFinite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsInitialForget

/-!
# Finite cohomology of a coherent module on a proper algebraic space over an affine base

[Stacks, Tag 08AS] asserts that for a Noetherian ring `A`, a proper morphism of algebraic spaces
`f : X ⟶ Spec A` and a coherent `𝒪_X`-module `F`, every cohomology module `H^i(X, F)` is a finite
`A`-module.  This file proves it, for `𝒪_X`-modules whose sections lie in the universe of the
structure rings, with nothing carried.

The proof is the source's.  The right derived functors of `Γ(V, f_* −)`, for `f : X ⟶ V` proper
with `V` affine and Noetherian, are finite over the functions on `V` at every coherent module
(`AlgebraicGeometry.Space.hasFiniteCohomologyOver_of_isProper`): this is the dévissage of
Stacks 08AN on the Noetherian algebraic space `X`, its two-out-of-three condition being the long
exact sequence of the right derived functors over the Noetherian ring of functions on `V`, and its
witness at a reduced closed subspace with irreducible space of points being built from Chow's
lemma and Serre's vanishing theorem
(`AlgebraicGeometry.Space.hasCoherentWitnessOnIntegralSubspaces_hasFiniteCohomologyOver`).  Then
`Γ(Spec A, f_* −)` is `Γ(X, −)` as a functor to `A`-modules
(`AlgebraicGeometry.Space.globalSectionsOverBaseIso`), and restriction of scalars and the universe
lift are exact, so they pass through the right derived functors.

## Main results

* `AlgebraicGeometry.Space.hasFiniteCohomologyOver_of_isProper`: the cohomology modules of a
  coherent module along a proper morphism to an affine Noetherian scheme are finite.
* `AlgebraicGeometry.Space.moduleFinite_cohomology_of_isProper`: **[Stacks, Tag 08AS]** for
  modules in the universe of the structure rings.

## Implementation notes

**Universes.**  The statements here are about `Modules.{u, u}`, the universe at which the direct
image `AlgebraicGeometry.Space.modulePushforward` exists.  Cohomology is the right derived functors
of `Stacks.Cohomology.SiteModules.globalSectionsFunctor`, valued in modules over the global
functions in the universe `u + 1` of the small étale site.
`AlgebraicGeometry.Space.cohomologyOverBase`, at a module universe containing `u + 1`, is not
reached; see `StacksFrontier.AlgebraicGeometry.Spaces.ProperCohomologyFinite`.

## References

* [Stacks Project, Tag 08AS](https://stacks.math.columbia.edu/tag/08AS)
* [Stacks Project, Tag 08AR](https://stacks.math.columbia.edu/tag/08AR)
* [Stacks Project, Tag 08AN](https://stacks.math.columbia.edu/tag/08AN)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u})
    (hA : B.Contains (Spec (.of A)))

section Finite

open CategoryTheory.Limits Opposite

attribute [local instance 5000] SheafOfModules.instAbelian

variable (S : Scheme.{u}) (hS : B.Contains S)

/-- The `𝒪`-modules on the small étale site of an algebraic space, at the universe of the
structure rings, have enough injectives. -/
local instance (priority := 5000) enoughInjectives_modules_proper
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    EnoughInjectives (Modules.{u, u} B S hS F hF) :=
  enoughInjectives_modules B S hS F hF

/-- **The cohomology of a coherent module along a proper morphism to an affine Noetherian
scheme is finite.**  Let `f : X ⟶ yoneda.obj V` be proper, with `V` affine and Noetherian, and let
`𝓕` be a coherent `𝒪_X`-module.  Then every right derived functor of `Γ(V, f_* −)` takes a finite
value at `𝓕` over the functions on `V`.

This is the dévissage of Stacks 08AN on the Noetherian algebraic space `X`
(`AlgebraicGeometry.Space.property_of_integralWitness_and_twoOutOfThree`) for the property
`AlgebraicGeometry.Space.HasFiniteCohomologyOver`: it holds on zero modules; two-out-of-three is
the long exact sequence of the right derived functors over the Noetherian ring of functions on
`V`; a retract of a module with the property has it; and the witness is
`AlgebraicGeometry.Space.hasCoherentWitnessOnIntegralSubspaces_hasFiniteCohomologyOver`. -/
theorem hasFiniteCohomologyOver_of_isProper (V : BigFppfOver B S hS)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)] {X : AlgebraicSpaces B S hS}
    (f : X ⟶ (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS))
    (hf : IsProper B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : IsCoherent B S hS X.1 X.2 F) : HasFiniteCohomologyOver B S hS V f F := by
  have : IsNoetherianRing (chartRing B S hS (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V)
      (idEtaleChart B S hS V)) :=
    have := hV
    have h : IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
      IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
    h
  have := modulePushforward_additive B S hS f
  have : (SheafOfModules.evaluation ((Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite B S hS (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V)).O))
      (op (idEtaleChart B S hS V))).Additive :=
    ⟨fun {_ _ _ _} => rfl⟩
  let Q := modulePushforward B S hS f ⋙ SheafOfModules.evaluation
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj V)
      (isAlgebraicSpace_yoneda B S hS V)).O)) (op (idEtaleChart B S hS V))
  refine property_of_isCoherent_of_devissage B S hS B.contains_terminal
    X
    (isNoetherian_of_isProper_toAffine B S hS V hV f hf) (HasFiniteCohomologyOver B S hS V f)
    (fun M hM p => ?_) (fun E hE _ _ _ => ⟨fun h₁ h₃ n => ?_, fun h₂ h₃ n => ?_,
      fun h₁ h₂ n => ?_⟩) (fun M r hr hP p => ?_)
    (hasCoherentWitnessOnIntegralSubspaces_hasFiniteCohomologyOver B S hS V hV f hf) F hF
  · have := ModuleCat.isZero_iff_subsingleton.1 (Functor.map_isZero (Q.rightDerived p) hM)
    have : Finite ((Q.rightDerived p).obj M) := Finite.of_subsingleton
    infer_instance
  · exact Stacks.Cohomology.RightDerivedDelta.moduleFinite_rightDerived_X₂ Q hE n (h₁ n) (h₃ n)
  · rcases n with _ | n
    · exact Stacks.Cohomology.RightDerivedDelta.moduleFinite_rightDerived_zero_X₁ Q hE (h₂ 0)
    · exact Stacks.Cohomology.RightDerivedDelta.moduleFinite_rightDerived_succ_X₁ Q hE n
        (h₃ n) (h₂ (n + 1))
  · exact Stacks.Cohomology.RightDerivedDelta.moduleFinite_rightDerived_X₃ Q hE n (h₂ n)
      (h₁ (n + 1))
  · exact Stacks.Cohomology.RightDerivedDelta.moduleFinite_rightDerived_of_retract Q
      (biproduct.ι (fun _ : Fin r => M) ⟨0, hr⟩) (biproduct.π (fun _ : Fin r => M) ⟨0, hr⟩)
      (biproduct.ι_π_self _ _) p (hP p)

end Finite

section General

open CategoryTheory.Limits Opposite Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

variable {B} {S : Scheme.{u}} {hS : B.Contains S} (V : BigFppfOver B S hS)

/-- The direct image of sections of modules along a morphism of algebraic spaces is natural in
the module, in its inverse form. -/
theorem modulePushforwardSectionsEquiv_symm_sectionsMap
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) {M M' : Modules.{u, u} B S hS X.1 X.2}
    (φ : M ⟶ M') (s : M.sections) :
    (modulePushforwardSectionsEquiv B S hS f M').symm (SheafOfModules.sectionsMap φ s) =
      SheafOfModules.sectionsMap ((modulePushforward B S hS f).map φ)
        ((modulePushforwardSectionsEquiv B S hS f M).symm s) := by
  apply (modulePushforwardSectionsEquiv B S hS f M').injective
  rw [Equiv.apply_symm_apply, modulePushforwardSectionsEquiv_naturality, Equiv.apply_symm_apply]

/-- The global sections of an `𝒪_X`-module are the sections of its direct image along
`f : X ⟶ V` over `V`, lifted to the universe of global sections: `Γ(X, M) = Γ(V, f_*M)`,
followed by evaluation at the identity chart of `V`, which is terminal. -/
def globalSectionsEquivPushforwardSections {X : AlgebraicSpaces B S hS}
    (f : X ⟶ (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ :
      AlgebraicSpaces B S hS)) (M : Modules.{u, u} B S hS X.1 X.2) :
    M.sections ≃ ULift.{u + 1}
      (((modulePushforward B S hS f).obj M).val.obj
        (op (idEtaleChart B S hS V))) :=
  ((modulePushforwardSectionsEquiv B S hS f M).symm.trans
    (Stacks.Cohomology.SiteModules.globalSectionsEquivOfIsInitial _ _ _
      (isTerminalIdEtaleChart B S hS V).op)).trans
    Equiv.ulift.symm

/-- `AlgebraicGeometry.Space.globalSectionsEquivPushforwardSections` sends a global section `s`
to the value at the identity chart of `V` of the corresponding section of the direct image. -/
theorem globalSectionsEquivPushforwardSections_apply {X : AlgebraicSpaces B S hS}
    (f : X ⟶ (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ :
      AlgebraicSpaces B S hS)) (M : Modules.{u, u} B S hS X.1 X.2)
    (s : M.sections) :
    globalSectionsEquivPushforwardSections V f M s =
      ULift.up (((modulePushforwardSectionsEquiv B S hS f M).symm s).eval
        (op (idEtaleChart B S hS V))) :=
  rfl

/-- `AlgebraicGeometry.Space.globalSectionsEquivPushforwardSections` is natural in the module. -/
theorem globalSectionsEquivPushforwardSections_sectionsMap
    {X : AlgebraicSpaces B S hS}
    (f : X ⟶ (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ :
      AlgebraicSpaces B S hS)) {M M' : Modules.{u, u} B S hS X.1 X.2}
    (φ : M ⟶ M') (s : M.sections) :
    globalSectionsEquivPushforwardSections V f M' (SheafOfModules.sectionsMap φ s) =
      ULift.up (((modulePushforward B S hS f).map φ).val.app
        (op (idEtaleChart B S hS V))
        (globalSectionsEquivPushforwardSections V f M s).down) := by
  rw [globalSectionsEquivPushforwardSections_apply,
    modulePushforwardSectionsEquiv_symm_sectionsMap]
  rfl

end General

/-! ### Stacks 08AS -/

section ProperFinite

open CategoryTheory.Limits Opposite Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

variable {A B hA} (V : BigFppfOver B (Spec (.of A)) hA)

/-- The ring map from `A` to the functions on an object `V` of the site, read on the identity
chart of `V`. -/
abbrev idEtaleChartBaseRingHom :
    A →+* ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA
      (yoneda.obj V) (isAlgebraicSpace_yoneda B (Spec (.of A)) hA V)).O)).obj.obj
      (op (idEtaleChart B (Spec (.of A)) hA V)) :=
  (globalSectionEval _ (op (idEtaleChart B (Spec (.of A)) hA V))).comp
    (baseRingHom A B hA (yoneda.obj V) (isAlgebraicSpace_yoneda B (Spec (.of A)) hA V))

/-- On `Spec A` itself, the functions on the identity chart are `A`. -/
theorem bijective_baseChartRingHom_baseObject :
    Function.Bijective (idEtaleChartBaseRingHom (baseObject A B hA)) := by
  change Function.Bijective ((Scheme.ΓSpecIso (.of A)).inv ≫ Scheme.Γ.map (B.inclusion.map
    (𝟙 (B.obj hA))).op).hom
  exact (ConcreteCategory.bijective_of_isIso (Scheme.Γ.map (B.inclusion.map
    (𝟙 (B.obj hA))).op)).comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).inv)

/-- The global sections of an `𝒪_X`-module, read as an `A`-module. -/
abbrev globalSectionsOverBase (X : AlgebraicSpaces B (Spec (.of A)) hA) :
    Modules.{u, u} B (Spec (.of A)) hA X.1 X.2 ⥤ ModuleCat.{u + 1} A :=
  globalSectionsFunctor.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).O)) ⋙
    ModuleCat.restrictScalars (baseRingHom A B hA X.1 X.2)

/-- The sections over `V` of the direct image along `f : X ⟶ V`, read as an `A`-module and
lifted to the universe of global sections. -/
abbrev pushforwardSectionsOverBase {X : AlgebraicSpaces B (Spec (.of A)) hA}
    (f : X ⟶ (⟨yoneda.obj V, isAlgebraicSpace_yoneda B (Spec (.of A)) hA V⟩ :
      AlgebraicSpaces B (Spec (.of A)) hA)) :
    Modules.{u, u} B (Spec (.of A)) hA X.1 X.2 ⥤ ModuleCat.{u + 1} A :=
  (modulePushforward B (Spec (.of A)) hA f ⋙
    SheafOfModules.evaluation.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B (Spec (.of A)) hA (yoneda.obj V)
        (isAlgebraicSpace_yoneda B (Spec (.of A)) hA V)).O))
      (op (idEtaleChart B (Spec (.of A)) hA V))) ⋙
    (ModuleCat.restrictScalars.{u} (idEtaleChartBaseRingHom V) ⋙ ModuleCat.uliftFunctor.{u + 1} A)

/-- **The global sections of an `𝒪_X`-module are the sections of its direct image over `V`**,
`A`-linearly, for a morphism `f : X ⟶ V`.  This is
`AlgebraicGeometry.Space.globalSectionsEquivPushforwardSections`; it is `A`-linear because `f_*`
carries multiplication by `a ∈ A` to multiplication by `a`
(`AlgebraicGeometry.Space.modulePushforward_map_globalSmul_baseRingHom`). -/
def globalSectionsLinearEquivPushforwardSections {X : AlgebraicSpaces B (Spec (.of A)) hA}
    (f : X ⟶ (⟨yoneda.obj V, isAlgebraicSpace_yoneda B (Spec (.of A)) hA V⟩ :
      AlgebraicSpaces B (Spec (.of A)) hA)) (M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) :
    (globalSectionsOverBase X).obj M ≃ₗ[A] (pushforwardSectionsOverBase V f).obj M where
  toEquiv := globalSectionsEquivPushforwardSections V f M
  map_add' s t := by
    have h := (((globalSectionsModulePushforwardIso B (Spec (.of A)) hA f).app M).inv.hom).map_add
      s t
    exact congrArg ULift.up (congrArg (fun z : ((modulePushforward B (Spec (.of A)) hA f).obj
      M).sections => z.eval (op (idEtaleChart B (Spec (.of A)) hA V))) h)
  map_smul' a s := by
    have hs : (a • s : (globalSectionsOverBase X).obj M) =
        SheafOfModules.sectionsMap (globalSmul _ (baseRingHom A B hA X.1 X.2 a) M) s :=
      Subtype.ext (funext fun _ => rfl)
    refine (congrArg (globalSectionsEquivPushforwardSections V f M) hs).trans ?_
    refine (globalSectionsEquivPushforwardSections_sectionsMap V f _ s).trans ?_
    rw [modulePushforward_map_globalSmul_baseRingHom]
    rfl

/-- `AlgebraicGeometry.Space.globalSectionsLinearEquivPushforwardSections`, natural in the
module. -/
def globalSectionsOverBaseIso {X : AlgebraicSpaces B (Spec (.of A)) hA}
    (f : X ⟶ (⟨yoneda.obj V, isAlgebraicSpace_yoneda B (Spec (.of A)) hA V⟩ :
      AlgebraicSpaces B (Spec (.of A)) hA)) :
    globalSectionsOverBase X ≅ pushforwardSectionsOverBase V f :=
  NatIso.ofComponents
    (fun M => (globalSectionsLinearEquivPushforwardSections V f M).toModuleIso)
    (fun {M M'} φ => by
      ext s
      exact globalSectionsEquivPushforwardSections_sectionsMap V f φ s)

/-- Restriction of scalars along a ring map preserves finite limits and finite colimits. -/
private theorem restrictScalars_preservesFinite.{v, w, w'} {R : Type w} {S : Type w'}
    [CommRing R] [CommRing S] (f : R →+* S) :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{v} f) ∧
      PreservesFiniteColimits (ModuleCat.restrictScalars.{v} f) :=
  ⟨⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩, ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩⟩

attribute [local instance] hasInjectiveResolutions_modules in
/-- **Stacks 08AS.**  Let `A` be a Noetherian ring, `f : X ⟶ Spec A` a proper morphism of
algebraic spaces and `F` a coherent `𝒪_X`-module.  Then `Hⁱ(X, F)` is a finite `A`-module for
every `i ≥ 0`.

The right derived functors of `Γ(Spec A, f_* −)` are finite over the functions on `Spec A` at
a coherent module (`AlgebraicGeometry.Space.hasFiniteCohomologyOver_of_isProper`, the core of
Stacks 08AR), and `Γ(Spec A, f_* −)` is `Γ(X, −)` as a functor to `A`-modules
(`AlgebraicGeometry.Space.globalSectionsOverBaseIso`); restriction of scalars and the universe
lift are exact, so they pass through the right derived functors. -/
@[stacks 08AS]
theorem moduleFinite_cohomology_of_isProper [IsNoetherianRing A]
    (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
    (f : X ⟶ yoneda.obj (baseObject A B hA)) (hf : IsProper B (Spec (.of A)) hA f)
    (F : Modules.{u, u} B (Spec (.of A)) hA X hX) [IsCoherent B (Spec (.of A)) hA X hX F]
    (i : ℕ) :
    Module.Finite A ((ModuleCat.restrictScalars (baseRingHom A B hA X hX)).obj
      (((globalSectionsFunctor.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)).rightDerived
          i).obj F)) := by
  let V := baseObject A B hA
  let g : (⟨X, hX⟩ : AlgebraicSpaces B (Spec (.of A)) hA) ⟶
      (⟨yoneda.obj V, isAlgebraicSpace_yoneda B (Spec (.of A)) hA V⟩ :
        AlgebraicSpaces B (Spec (.of A)) hA) := ObjectProperty.homMk f
  have hV : IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj V) := by
    change IsAffine (Spec (.of A))
    infer_instance
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj V) := by
    change IsLocallyNoetherian (Spec (.of A))
    infer_instance
  have hfin := hasFiniteCohomologyOver_of_isProper B (Spec (.of A)) hA V hV g hf F inferInstance i
  have := modulePushforward_additive B (Spec (.of A)) hA g
  let O := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA
    (yoneda.obj V) (isAlgebraicSpace_yoneda B (Spec (.of A)) hA V)).O)
  have : (SheafOfModules.evaluation.{u} O (op (idEtaleChart B (Spec (.of A)) hA V))).Additive :=
    ⟨fun {_ _ _ _} => rfl⟩
  obtain ⟨_, _⟩ := restrictScalars_preservesFinite.{u + 1} (baseRingHom A B hA X hX)
  have : (ModuleCat.restrictScalars.{u + 1} (baseRingHom A B hA X hX)).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  let E := ModuleCat.restrictScalars.{u} (idEtaleChartBaseRingHom V) ⋙
    ModuleCat.uliftFunctor.{u + 1} A
  obtain ⟨_, _⟩ := restrictScalars_preservesFinite.{u} (idEtaleChartBaseRingHom V)
  have : PreservesFiniteLimits E := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits E := comp_preservesFiniteColimits _ _
  have : E.PreservesHomology := Functor.preservesHomologyOfExact _
  let Q := modulePushforward B (Spec (.of A)) hA g ⋙
    SheafOfModules.evaluation.{u} O (op (idEtaleChart B (Spec (.of A)) hA V))
  let Γ := globalSectionsFunctor.{u + 1, u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)
  have e₁ := (Functor.rightDerivedCompIso Γ
    (ModuleCat.restrictScalars.{u + 1} (baseRingHom A B hA X hX)) i).app F
  have e₂ := (Functor.rightDerivedIsoOfNatIso
    (F := Γ ⋙ ModuleCat.restrictScalars.{u + 1} (baseRingHom A B hA X hX)) (G := Q ⋙ E)
    (globalSectionsOverBaseIso V g) i).app F
  have e₃ := (Functor.rightDerivedCompIso Q E i).app F
  have h₁ : Module.Finite A ((ModuleCat.restrictScalars.{u} (idEtaleChartBaseRingHom V)).obj
      ((Q.rightDerived i).obj F)) := by
    let l : ((ModuleCat.restrictScalars.{u} (idEtaleChartBaseRingHom V)).obj
        ((Q.rightDerived i).obj F)) →ₛₗ[idEtaleChartBaseRingHom V] ((Q.rightDerived i).obj F) :=
      { toFun := id
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have : RingHomSurjective (idEtaleChartBaseRingHom V) :=
      ⟨(bijective_baseChartRingHom_baseObject (A := A) (B := B) (hA := hA)).2⟩
    exact (l.finite_iff_of_bijective Function.bijective_id).2 hfin
  have h₂ : Module.Finite A ((Q.rightDerived i ⋙ E).obj F) :=
    Module.Finite.equiv ULift.moduleEquiv.symm
  have h₃ : Module.Finite A (((Q ⋙ E).rightDerived i).obj F) :=
    Module.Finite.equiv e₃.symm.toLinearEquiv
  have h₄ : Module.Finite A (((Γ ⋙ ModuleCat.restrictScalars.{u + 1}
      (baseRingHom A B hA X hX)).rightDerived i).obj F) :=
    Module.Finite.equiv e₂.symm.toLinearEquiv
  exact Module.Finite.equiv e₁.toLinearEquiv

end ProperFinite

end AlgebraicGeometry.Space

end
