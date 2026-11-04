module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperCohomologyFiniteDevissage
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceModuleCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsTerminalChart
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatGlobalSectionsRingHom
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSpacePresentedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOpenRestriction
public import StacksFrontier.AlgebraicGeometry.ProperFiniteness.GlobalSectionsFinite
public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.ClosedImmersionCoherence

/-!
# Finite cohomology of a coherent module on a scheme proper over an affine Noetherian scheme,
read on the small étale site

Let `g : Z ⟶ W` be a morphism of the big fppf site whose morphism of schemes is proper, with `W`
affine and locally Noetherian, and let `M` be a coherent module on the small étale site of the
algebraic space `h_Z`.  Then every cohomology module `H^n(h_Z, M)`, read over `Γ(h_W, 𝒪)` along
the ring map of [Stacks, Tag 0732], is finite.

This is the scheme-level [Stacks, Tag 02O6] carried to the small étale site: the cohomology of
`h_Z` is the cohomology over the terminal chart `u(⊤)`
(`AlgebraicGeometry.Space.rightDerivedGlobalSectionsIsoEvaluationChart`), which is the Zariski
cohomology of the restriction of `M` to `Z`, finite over `Γ(W, 𝒪_W)` by
`AlgebraicGeometry.Space.moduleFinite_rightDerived_evaluation_selfOpensTop`.  The ring through
which `Γ(h_W, 𝒪)` acts on the chart is `Γ` of a proper morphism of schemes to `W`
(`AlgebraicGeometry.Space.globalSectionsChartEval_globalSectionsRingHomSite`), hence finite by
[Stacks, Tag 02O6] in degree zero, `AlgebraicGeometry.finiteGlobalSectionsOfProper`.

## Main results

* `AlgebraicGeometry.finite_appTop_of_isProper_of_isAffine`: `Γ(W) ⟶ Γ(T)` is finite for a
  proper `T ⟶ W` with `W` affine and locally Noetherian.
* `AlgebraicGeometry.Space.hasFiniteGlobalCohomologyOver_schemeSpaceMap_of_isProper`: the
  finiteness above.

## References

* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry

/-- **The ring map on global sections of a proper morphism to an affine locally Noetherian scheme
is finite.**  This is `AlgebraicGeometry.finiteGlobalSectionsOfProper` after composing with the
isomorphism `W ≅ Spec Γ(W, ⊤)`. -/
theorem finite_appTop_of_isProper_of_isAffine {T W : Scheme.{u}} (g : T ⟶ W) [IsProper g]
    [IsAffine W] [IsLocallyNoetherian W] : g.appTop.hom.Finite := by
  have : IsNoetherianRing Γ(W, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top W⟩
  have h := finiteGlobalSectionsOfProper Γ(W, ⊤) inferInstance (g ≫ W.isoSpec.hom) inferInstance
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] at h
  exact RingHom.Finite.of_comp_finite h

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

/-- Finiteness of a module through a finite ring map, at independent universes of the two rings:
a finite module over `S` is finite over `R` along a finite `R →+* S`. -/
theorem moduleFinite_restrictScalars_of_finite_ringHom {R : Type*} {S : Type*} [CommRing R]
    [CommRing S] (f : R →+* S) (hf : f.Finite) (M : ModuleCat.{u} S) [Module.Finite S M] :
    Module.Finite R ((ModuleCat.restrictScalars f).obj M) := by
  let _ : Algebra R S := f.toAlgebra
  have : Module.Finite R S := hf
  show @Module.Finite R (M : Type u) _ _ (Module.compHom (M : Type u) f)
  let _ : Module R (M : Type u) := Module.compHom (M : Type u) f
  have : IsScalarTower R S (M : Type u) := ⟨fun r s m => mul_smul (f r) s m⟩
  exact Module.Finite.trans S (M : Type u)

/-- A module whose restriction of scalars along a ring map is finite is finite: a generating
family over the source generates over the target, the source acting through the map. -/
theorem moduleFinite_of_moduleFinite_restrictScalars {R : Type*} {S : Type*} [Ring R] [Ring S]
    (f : R →+* S) (M : ModuleCat.{u} S)
    (h : Module.Finite R ((ModuleCat.restrictScalars f).obj M)) : Module.Finite S M := by
  let : SMul R S := ⟨fun r s => f r * s⟩
  let : Module R M := Module.compHom M f
  have : IsScalarTower R S M := ⟨fun r s m => mul_smul (f r) s m⟩
  have : Module.Finite R M := h
  exact Module.Finite.of_restrictScalars_finite R S M

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The cohomology of a coherent module on a scheme proper over an affine Noetherian scheme is
finite over the functions on the base**, on the small étale site: for `g : Z ⟶ W` with proper
morphism of schemes, `W` affine and locally Noetherian, and `M` coherent on `h_Z`, every
`H^n(h_Z, M)` is a finite `Γ(h_W, 𝒪)`-module along the ring map of `h_g`. -/
theorem hasFiniteGlobalCohomologyOver_schemeSpaceMap_of_isProper {Z W : BigFppfOver B S hS}
    (g : Z ⟶ W) [_root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map g)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    [_root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj W)]
    (M : Modules.{u, u} B S hS (schemeSpace Z).1 (schemeSpace Z).2)
    (hM : IsCoherent B S hS (yoneda.obj Z) (isAlgebraicSpace_yoneda B S hS Z) M) :
    HasFiniteGlobalCohomologyOver B S hS (schemeSpaceMap g) M := by
  unfold HasFiniteGlobalCohomologyOver
  intro _ n
  have := hasInjectiveResolutions_representedModules B S hS Z
  set V := (selfOpensFunctor B S hS Z).obj ⊤
  have hV : IsTerminal V := isTerminalSelfOpensFunctorTop B S hS Z
  set N := ((SheafOfModules.evaluation.{u} (representedStructureRingSheaf B S hS Z)
    (op V)).rightDerived n).obj M
  -- `N` is finite over the ring of the chart
  have h1 := @moduleFinite_rightDerived_evaluation_selfOpensTop B S hS Z _
    ((BigFppfOver.toScheme B S hS).map g) ‹_› ‹_› ‹_› M hM n
  have h2 : Module.Finite _ N := moduleFinite_of_moduleFinite_restrictScalars _ N h1
  let : CommRing ((representedStructureRingSheaf B S hS Z).obj.obj (op V)) :=
    inferInstanceAs (CommRing Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS (yoneda.obj Z)).obj V), ⊤))
  -- the chart diagram `u(⊤) ⟶ Z ⟶ W`
  let e : V ≅ idEtaleChart B S hS Z := hV.uniqueUpToIso (isTerminalIdEtaleChart B S hS Z)
  let d : ChartDiagram B S hS (schemeSpace Z).1 (schemeSpace W).1
      (schemeSpaceMap g).hom :=
    { U := V
      V := idEtaleChart B S hS W
      g := (SmallEtale.toOver B S hS (yoneda.obj Z)).map e.hom ≫ g
      comm := by
        show V.obj.hom ≫ yoneda.map g =
          yoneda.map ((SmallEtale.toOver B S hS (yoneda.obj Z)).map e.hom ≫ g) ≫ 𝟙 _
        rw [Category.comp_id, ← yoneda_map_toOver_map_comp_hom e.hom]
        exact (congrArg (· ≫ yoneda.map g) (Category.comp_id _)).trans
          (yoneda.map_comp _ _).symm }
  have hdg : (BigFppfOver.toScheme B S hS).map d.g =
      (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS (yoneda.obj Z)).map e.hom) ≫
        (BigFppfOver.toScheme B S hS).map g :=
    Functor.map_comp _ _ _
  have hdprop : _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map d.g) := by
    rw [hdg]
    exact (@MorphismProperty.cancel_left_of_respectsIso _ _ @_root_.AlgebraicGeometry.IsProper _
      _ _ _ _ ((BigFppfOver.toScheme B S hS).map g) ((BigFppfOver.toScheme B S hS).mapIso
        ((SmallEtale.toOver B S hS (yoneda.obj Z)).mapIso e)).isIso_hom).2
        ‹_root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map g)›
  -- the ring map through which `Γ(h_W)` acts on `N`
  set ψ := (globalSectionEval (ringSheaf (smallEtaleRingedSite B S hS (schemeSpace Z).1
      (schemeSpace Z).2).O) (op V)).comp
    (globalSectionsRingHomSite B S hS (schemeSpaceMap g))
  have hψ : ψ = ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map d.g).op).hom).comp
      (globalSectionsChartRingEquiv B S hS (schemeSpace W)
        (isTerminalIdEtaleChart B S hS W)).toRingHom := by
    ext a
    exact globalSectionsChartEval_globalSectionsRingHomSite B S hS (schemeSpaceMap g) d a
  have hψfin : ψ.Finite := by
    rw [hψ]
    refine RingHom.Finite.comp ?_ (RingHom.Finite.of_surjective _
      (globalSectionsChartRingEquiv B S hS (schemeSpace W)
        (isTerminalIdEtaleChart B S hS W)).surjective)
    exact @finite_appTop_of_isProper_of_isAffine _ _ ((BigFppfOver.toScheme B S hS).map d.g) hdprop
      (inferInstanceAs (IsAffine ((BigFppfOver.toScheme B S hS).obj W)))
      (inferInstanceAs (_root_.AlgebraicGeometry.IsLocallyNoetherian
        ((BigFppfOver.toScheme B S hS).obj W)))
  have h3 := @moduleFinite_restrictScalars_of_finite_ringHom _ _ _ _ ψ hψfin N h2
  -- transport along the comparison with the sections over the terminal chart
  have iso := (globalSectionsRestrictScalars B S hS (schemeSpaceMap g)).mapIso
    ((rightDerivedGlobalSectionsIsoEvaluationChart B S hS (schemeSpace Z) hV n).app M)
  have key := Module.Finite.equiv
    (R := RingCat.sectionsSubring
      (ringSheaf (smallEtaleRingedSite B S hS (schemeSpace W).1 (schemeSpace W).2).O).obj)
    (M := (ModuleCat.restrictScalars ψ).obj N)
    (N := (globalSectionsRestrictScalars B S hS (schemeSpaceMap g)).obj
      (((SheafOfModules.evaluation
          (ringSheaf (smallEtaleRingedSite B S hS (schemeSpace Z).1 (schemeSpace Z).2).O)
          (op V)).rightDerived n ⋙
        ModuleCat.restrictScalars (globalSectionEval
          (ringSheaf (smallEtaleRingedSite B S hS (schemeSpace Z).1 (schemeSpace Z).2).O)
          (op V)) ⋙
        ModuleCat.uliftFunctor.{u + 1} _).obj M))
    { toFun := ULift.up
      invFun := ULift.down
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Module.Finite.equiv iso.symm.toLinearEquiv

end AlgebraicGeometry.Space

end
