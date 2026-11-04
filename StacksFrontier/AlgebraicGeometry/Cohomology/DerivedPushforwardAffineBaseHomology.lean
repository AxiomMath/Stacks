module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.AlgebraicGeometry.Cohomology.AffineBase
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.Qcqs
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineIsoCriterion
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.PullbackPushforwardAdjunction
public import StacksFrontier.AlgebraicGeometry.AffineMorphismCohomology.Normalized
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
public import StacksFrontier.Algebra.Homology.RightDerivedDelta

/-!
# Cohomology sheaves of a derived direct image to an affine base, read on global cohomology

Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes with `S` affine, and
let `u : F ⟶ G` be a morphism of quasi-coherent `𝒪_X`-modules. This file proves that the map
`H^q(Rf_* F) ⟶ H^q(Rf_* G)` of cohomology sheaves of the unbounded derived direct images is an
isomorphism as soon as the map `H^q(X, F) ⟶ H^q(X, G)` of cohomology modules is, in every model of
the two derived categories.

The argument has three steps, each an available identification.

* The degree-`q` cohomology sheaf of `Rf_*` applied to a module placed in degree `0` is the
  classical higher direct image `R^qf_*`, naturally in the module and at an arbitrary model of the
  derived categories: `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived`.
* `R^qf_*F` and `R^qf_*G` are quasi-coherent ([Stacks, Tag 01XJ]), so on the affine `S` a morphism
  between them is invertible once it is invertible on global sections:
  `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_app_top`.
* On global sections it is the map `H^q(X, F) ⟶ H^q(X, G)`, scalars restricted along
  `Γ(S, 𝒪_S) ⟶ Γ(X, 𝒪_X)`, naturally in the module ([Stacks, Tag 01XK]):
  `Stacks.Cohomology.AffineBase.sectionsRightDerivedPushforwardIso`.

## Main results

* `Stacks.Cohomology.AffineBase.isIso_rightDerived_pushforward_map_of_isIso`: a morphism of
  quasi-coherent modules inducing an isomorphism on `H^q(X, -)` induces one on `R^qf_*`.
* `Stacks.Cohomology.AffineBase.isIso_homology_derivedPushforward_map_single_iff`: the cohomology
  sheaf `H^q(Rf_*(-))` of a morphism of modules placed in degree `0` is invertible exactly when
  `R^qf_*` of it is, in any model of the derived categories.
* `Stacks.Cohomology.AffineBase.isIso_homology_derivedPushforward_map_single_of_isIso`: the
  combination of the two.

## References

* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace Stacks.Cohomology.AffineBase

variable {X S : Scheme.{u}} (f : X ⟶ S)

section Classical

variable [QuasiCompact f] [QuasiSeparated f] [IsAffine S]

/-- A natural isomorphism of functors on quasi-coherent modules identifies the invertibility of
their values at the same morphism of quasi-coherent modules. -/
private theorem isIso_map_iff_of_isQuasicoherent {D : Type*} [Category D]
    {Φ Ψ : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤ D} (e : Φ ≅ Ψ)
    {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent] (u : F ⟶ G) :
    IsIso (Φ.map (ObjectProperty.homMk u : (⟨F, ‹_›⟩ : (SheafOfModules.isQuasicoherent
      X.ringCatSheaf).FullSubcategory) ⟶ ⟨G, ‹_›⟩)) ↔
    IsIso (Ψ.map (ObjectProperty.homMk u : (⟨F, ‹_›⟩ : (SheafOfModules.isQuasicoherent
      X.ringCatSheaf).FullSubcategory) ⟶ ⟨G, ‹_›⟩)) :=
  NatIso.isIso_map_iff e _

/-- **A morphism of quasi-coherent modules inducing an isomorphism on `H^q(X, -)` induces an
isomorphism on `R^qf_*`**, for `f` quasi-compact and quasi-separated with affine target. Both
higher direct images are quasi-coherent ([Stacks, Tag 01XJ]), so it suffices to look at global
sections over `S`, which are the cohomology modules of `X` by [Stacks, Tag 01XK]. -/
theorem isIso_rightDerived_pushforward_map_of_isIso {F G : X.Modules} [F.IsQuasicoherent]
    [G.IsQuasicoherent] (u : F ⟶ G) (q : ℕ)
    (h : IsIso (((sectionsFunctor X ⊤).rightDerived q).map u)) :
    IsIso (((Scheme.Modules.pushforward f).rightDerived q).map u) := by
  have h₁ : IsIso ((ModuleCat.restrictScalars f.appTop.hom).map
      (((sectionsFunctor X ⊤).rightDerived q).map u)) := inferInstance
  have h₂ := (isIso_map_iff_of_isQuasicoherent (sectionsRightDerivedPushforwardIso f q) u).1 h₁
  have h₃ : IsIso ((sectionsFunctor S ⊤).map
      (((Scheme.Modules.pushforward f).rightDerived q).map u)) := h₂
  refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_app_top _ ?_
  exact Functor.map_isIso (F := forget₂ (ModuleCat.{u} Γ(S, ⊤)) AddCommGrpCat.{u})
    (f := (sectionsFunctor S ⊤).map (((Scheme.Modules.pushforward f).rightDerived q).map u))

end Classical

section Derived

variable [HasDerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))]
  [HasDerivedCategory (SheafOfModules.{u} (structureSheafRing S.toRingedSpace))]

attribute [local instance] IsGrothendieckAbelian.enoughInjectives in
/-- **The cohomology sheaves of `Rf_*` at a morphism of modules placed in degree `0` are the
classical higher direct images**: `H^q(Rf_*(u[0]))` is invertible exactly when `R^qf_*u` is, in
any model of the two derived categories. -/
theorem isIso_homology_derivedPushforward_map_single_iff {F G : X.Modules} (u : F ⟶ G)
    (q : ℕ) :
    IsIso ((DerivedCategory.homologyFunctor _ (q : ℤ)).map
        ((derivedPushforward f.toLRSHom.toShHom).map
          (DerivedCategory.Q.map ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map u)))) ↔
      IsIso (((Scheme.Modules.pushforward f).rightDerived q).map u) := by
  have := SheafOfModules.isGrothendieckAbelianU (structureSheafRing X.toRingedSpace)
  let E := Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
    (modulePushforward f.toLRSHom.toShHom) (derivedPushforward f.toLRSHom.toShHom)
    (derivedPushforwardUnit f.toLRSHom.toShHom)
    (exists_quasiIso_isKInjective X.toRingedSpace) q
  let E' := Functor.isoWhiskerRight
    (DerivedCategory.singleFunctorIsoCompQ (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      0) (derivedPushforward f.toLRSHom.toShHom ⋙ DerivedCategory.homologyFunctor _ (q : ℤ))
  exact ((NatIso.isIso_map_iff E' u).symm.trans (NatIso.isIso_map_iff E u) :)

/-- **A morphism of quasi-coherent modules inducing an isomorphism on `H^q(X, -)` induces an
isomorphism on the degree-`q` cohomology sheaves of the derived direct images**, for `f`
quasi-compact and quasi-separated with affine target, in any model of the derived categories. -/
theorem isIso_homology_derivedPushforward_map_single_of_isIso [QuasiCompact f]
    [QuasiSeparated f] [IsAffine S] {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (u : F ⟶ G) (q : ℕ) (h : IsIso (((sectionsFunctor X ⊤).rightDerived q).map u)) :
    IsIso ((DerivedCategory.homologyFunctor _ (q : ℤ)).map
        ((derivedPushforward f.toLRSHom.toShHom).map
          (DerivedCategory.Q.map ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map u)))) :=
  (isIso_homology_derivedPushforward_map_single_iff f u q).2
    (isIso_rightDerived_pushforward_map_of_isIso f u q h)

end Derived

section Affine

/-- **On `Γ(X, 𝒪_X)`-modules and on abelian groups the cohomology of a morphism of modules is
invertible at the same time**: the comparison of [Stacks, Tag 01F1] part (1) identifies the
module-valued `H^q(X, -)` with the group-valued one after forgetting the scalars, and an
`R`-linear map is invertible exactly when its underlying additive map is. -/
theorem isIso_rightDerived_sections_map_iff_Hfunctor {F G : X.Modules} (u : F ⟶ G) (q : ℕ) :
    IsIso (((sectionsFunctor X ⊤).rightDerived q).map u) ↔
      IsIso ((Hfunctor X.ringCatSheaf ⊤ q).map u) := by
  have e := Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso X.ringCatSheaf
    (⊤ : X.Opens) q
  have h := NatIso.isIso_map_iff e u
  refine Iff.trans ?_ h
  change IsIso
      (((_root_.SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).rightDerived q).map u)
    ↔ IsIso ((forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}).map
      (((_root_.SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).rightDerived q).map u))
  constructor <;> intro hi <;> rw [ConcreteCategory.isIso_iff_bijective] at hi ⊢ <;> exact hi

/-- **Cohomology of a morphism of quasi-coherent modules is unchanged by pushing it forward along
an affine morphism**: `H^q(X, u)` is invertible exactly when `H^q(S, f_*u)` is. This is the
naturality of the isomorphism `H^q(X, -) ≅ H^q(S, f_*(-))` of [Stacks, Tag 089W]. -/
theorem isIso_rightDerived_sections_map_iff_of_isAffineHom [IsAffineHom f] {F G : X.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (u : F ⟶ G) (q : ℕ) :
    IsIso (((sectionsFunctor X ⊤).rightDerived q).map u) ↔
      IsIso
        (((sectionsFunctor S ⊤).rightDerived q).map ((Scheme.Modules.pushforward f).map u)) := by
  rw [isIso_rightDerived_sections_map_iff_Hfunctor, isIso_rightDerived_sections_map_iff_Hfunctor]
  exact isIso_map_iff_of_isQuasicoherent (Stacks.AffineCohomologyResolution.cohomologyPushforwardIso
    f q) u

end Affine

/-- **A morphism with vanishing kernel cohomology is invertible on cohomology**: if `g` is an
epimorphism of `𝒪_X`-modules and `H^q(X, ker g)` and `H^{q+1}(X, ker g)` vanish, then
`H^q(X, g)` is an isomorphism, by the long exact cohomology sequence of
`0 ⟶ ker g ⟶ M ⟶ N ⟶ 0`. -/
theorem isIso_rightDerived_sections_map_of_epi {M N : X.Modules} (g : M ⟶ N) [Epi g] (q : ℕ)
    (h : IsZero (((sectionsFunctor X ⊤).rightDerived q).obj (kernel g)))
    (h' : IsZero (((sectionsFunctor X ⊤).rightDerived (q + 1)).obj (kernel g))) :
    IsIso (((sectionsFunctor X ⊤).rightDerived q).map g) := by
  have hS : (ShortComplex.mk (kernel.ι g) g (kernel.condition g)).ShortExact :=
    { exact := ShortComplex.exact_kernel g
      mono_f := inferInstance
      epi_g := inferInstance }
  exact Stacks.Cohomology.RightDerivedDelta.isIso_rightDerived_map_g hS
    (sectionsFunctor X ⊤) q h h'

end Stacks.Cohomology.AffineBase

end
