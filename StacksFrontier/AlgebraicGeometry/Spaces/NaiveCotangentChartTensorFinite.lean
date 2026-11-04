module

public import StacksFrontier.AlgebraicGeometry.Spaces.NaiveCotangentChartFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackGlobalPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation

/-!
# Finiteness of `N ⊗_A 𝒪` on an affine chart

Let `(C, J)` be a site with a final object, `O` a sheaf of commutative rings on it and
`Γ = Γ(C, O)` its ring of global functions.  For a finitely presented `Γ`-module `M` the sheaf
`M ⊗_Γ 𝒪` of `Stacks.Cohomology.SiteModules.sectionTensorSheafFunctor` has a *finite* global
presentation, and for a finite `Γ`-module it has finite global generators: the functor
`M ↦ M ⊗_Γ 𝒪` is a left adjoint, so it carries a presentation `Γ^k → Γ^n → M → 0` to a cokernel
diagram, and it carries the free module `Γ^n` to a coproduct of `n` copies of the structure sheaf
(`Stacks.Cohomology.SiteModules.isColimitSectionTensorFreeCofan`).

Let then `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and `d` a diagram of
étale scheme charts over `f` with affine charts `V = Spec A` of `X` and `W = Spec R` of `Y`.
Evaluation at the final object identifies `Γ` of the slice of the small étale site of `X` at `V`
with `A`, so the above applies to the functor `N ↦ N ⊗_A 𝒪` of
`AlgebraicGeometry.Space.chartTensorFunctor`: for `N` of finite presentation (resp. finite) over
`A`, the sheaf `N ⊗_A 𝒪` is of finite presentation (resp. of finite type) on the slice, and it is
quasi-coherent for every `N`.  When `f` is locally of finite presentation, `A` is of finite
presentation over `R`.

## Main results

* `Stacks.Cohomology.SiteModules.hasFiniteGlobalPresentation_sectionTensor_of_isTerminal`:
  `M ⊗_Γ 𝒪` has a finite global presentation for `M` of finite presentation.
* `Stacks.Cohomology.SiteModules.hasFiniteGlobalGenerators_sectionTensor_of_isTerminal`:
  `M ⊗_Γ 𝒪` has finite global generators for `M` finite.
* `AlgebraicGeometry.Space.hasFiniteGlobalPresentation_chartTensorFunctor_obj`,
  `AlgebraicGeometry.Space.hasFiniteGlobalGenerators_chartTensorFunctor_obj`,
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_chartTensorFunctor_obj`,
  `AlgebraicGeometry.Space.isFinitePresentationOnSite_chartTensorFunctor_obj` and
  `AlgebraicGeometry.Space.isFiniteTypeOnSite_chartTensorFunctor_obj`: the corresponding
  statements for `N ⊗_A 𝒪` on the slice at an affine chart.
* `AlgebraicGeometry.Space.algebraFinitePresentation_chartDiagram`: the ring of an affine chart
  is of finite presentation over the ring of the chart below it, for `f` locally of finite
  presentation.

## References

* [Stacks Project, Tag 0D0Z](https://stacks.math.columbia.edu/tag/0D0Z)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.SiteModules

namespace Stacks.Cohomology.SiteModules

universe u v r

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  {O : Sheaf J CommRingCat.{r}}

/-- The free module `⨁_{Fin n} Γ`, indexed by the lift of `Fin n`, as the module of functions
`Fin n → Γ`. -/
def freeSectionModuleFinEquiv (n : ℕ) :
    freeSectionModule O (ULift.{max u v r} (Fin n)) ≃ₗ[GlobalFunctionRing O]
      (Fin n → GlobalFunctionRing O) :=
  (Finsupp.domLCongr Equiv.ulift).trans (Finsupp.linearEquivFunOnFinite _ _ _)

variable [HasWeakSheafify J AddCommGrpCat.{max u r v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u r v}] {Z : C} (hZ : IsTerminal Z)

/-- **`(⨁_{Fin n} Γ) ⊗_Γ 𝒪` is a coproduct of `n` copies of the universe lift of the structure
sheaf**, indexed by `Fin n` itself: `Stacks.Cohomology.SiteModules.isColimitSectionTensorFreeCofan`
reindexed along `Equiv.ulift`. -/
def isColimitSectionTensorFreeFinCofan (n : ℕ) :
    IsColimit (Cofan.mk ((sectionTensorSheafFunctor.{u, v, r, v} O).obj
        (freeSectionModule O (ULift.{max u v r} (Fin n))))
      (fun i : Fin n => sectionTensorFreeCofanInj hZ _ (ULift.up i))) :=
  Cofan.isColimitEquivOfEquiv Equiv.ulift.symm _ (isColimitSectionTensorFreeCofan hZ _)

/-- The surjection `⨁_{Fin n} Γ ⟶ M` attached to a linear map `Γ^n → M`. -/
def freeSectionModuleFinHom {n : ℕ} {M : ModuleCat.{max u r v} (GlobalFunctionRing O)}
    (p : (Fin n → GlobalFunctionRing O) →ₗ[GlobalFunctionRing O] M) :
    freeSectionModule O (ULift.{max u v r} (Fin n)) ⟶ M :=
  ModuleCat.ofHom (p ∘ₗ (freeSectionModuleFinEquiv n).toLinearMap)

omit [HasWeakSheafify J AddCommGrpCat.{max u r v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u r v}] in
/-- The map `⨁_{Fin n} Γ ⟶ M` attached to a surjection `Γ^n → M` is an epimorphism. -/
theorem epi_freeSectionModuleFinHom {n : ℕ} {M : ModuleCat.{max u r v} (GlobalFunctionRing O)}
    (p : (Fin n → GlobalFunctionRing O) →ₗ[GlobalFunctionRing O] M)
    (hp : Function.Surjective p) : Epi (freeSectionModuleFinHom (O := O) p) :=
  (ModuleCat.epi_iff_surjective _).2 fun y =>
    ⟨(freeSectionModuleFinEquiv n).symm (hp y).choose,
      (congrArg p ((freeSectionModuleFinEquiv n).apply_symm_apply _)).trans (hp y).choose_spec⟩

include hZ in
/-- **`M ⊗_Γ 𝒪` has a finite global presentation** for `M` of finite presentation over the ring
`Γ` of global functions, on a site with a final object.  A presentation `Γ^k → Γ^n → M → 0` is
carried by the left adjoint `M ↦ M ⊗_Γ 𝒪` to a cokernel diagram whose two free terms are
coproducts of `n` and `k` copies of the structure sheaf
(`Stacks.Cohomology.SiteModules.isColimitSectionTensorFreeFinCofan`). -/
theorem hasFiniteGlobalPresentation_sectionTensor_of_isTerminal
    (M : ModuleCat.{max u r v} (GlobalFunctionRing O))
    [Module.FinitePresentation (GlobalFunctionRing O) M] :
    ((sectionTensorSheafFunctor.{u, v, r, v} O).obj M).HasFiniteGlobalPresentation := by
  obtain ⟨n, k, p, q, hp, hpq⟩ := Module.FinitePresentation.exists_fin' (GlobalFunctionRing O) M
  let eN := freeSectionModuleFinEquiv (O := O) n
  let eK := freeSectionModuleFinEquiv (O := O) k
  let π : freeSectionModule O (ULift.{max u v r} (Fin n)) ⟶ M := freeSectionModuleFinHom p
  let ρ : freeSectionModule O (ULift.{max u v r} (Fin k)) ⟶
      freeSectionModule O (ULift.{max u v r} (Fin n)) :=
    ModuleCat.ofHom (eN.symm.toLinearMap ∘ₗ q ∘ₗ eK.toLinearMap)
  have hρπ : ρ ≫ π = 0 := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    change p (eN (eN.symm (q (eK x)))) = 0
    rw [LinearEquiv.apply_symm_apply]
    exact (hpq (q (eK x))).2 ⟨eK x, rfl⟩
  have hepi : Epi π := epi_freeSectionModuleFinHom p hp
  have hexact : (ShortComplex.mk ρ π hρπ).Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    obtain ⟨z, hz⟩ := (hpq (eN x)).1 hx
    refine ⟨eK.symm z, ?_⟩
    change eN.symm (q (eK (eK.symm z))) = x
    rw [LinearEquiv.apply_symm_apply, hz, LinearEquiv.symm_apply_apply]
  let F := sectionTensorSheafFunctor.{u, v, r, v} O
  have hadd : F.Additive := (sectionTensorSheafAdjunction.{u, v, r, v} O).left_adjoint_additive
  have : PreservesColimit (parallelPair ρ 0) F :=
    (sectionTensorSheafAdjunction.{u, v, r, v} O).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape.preservesColimit
  let e := Stacks.SheafOfModules.uliftForPresentationIsoSelf.{u, v, r, v} (F.obj M)
  have hc := isColimitCoforkMapOfIsColimit' F hρπ hexact.gIsCokernel
  refine ⟨n, k, _, _, _, _, ⟨isColimitSectionTensorFreeFinCofan hZ n⟩,
    ⟨isColimitSectionTensorFreeFinCofan hZ k⟩, F.map ρ, F.map π ≫ e.hom, ?_, ?_⟩
  · rw [← Category.assoc, ← F.map_comp, hρπ, F.map_zero, zero_comp]
  · exact ⟨Cofork.isColimitOfIsos _ hc _ (Iso.refl _) (Iso.refl _) e (by simp) (by simp)
      (Category.id_comp _)⟩

include hZ in
/-- **`M ⊗_Γ 𝒪` has finite global generators** for `M` finite over the ring `Γ` of global
functions, on a site with a final object: a surjection `Γ^n → M` is carried by the left adjoint
`M ↦ M ⊗_Γ 𝒪` to an epimorphism out of a coproduct of `n` copies of the structure sheaf. -/
theorem hasFiniteGlobalGenerators_sectionTensor_of_isTerminal
    (M : ModuleCat.{max u r v} (GlobalFunctionRing O))
    [Module.Finite (GlobalFunctionRing O) M] :
    ((sectionTensorSheafFunctor.{u, v, r, v} O).obj M).HasFiniteGlobalGenerators := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' (GlobalFunctionRing O) M
  have hepi : Epi (freeSectionModuleFinHom (O := O) p) := epi_freeSectionModuleFinHom p hp
  let F := sectionTensorSheafFunctor.{u, v, r, v} O
  have : F.PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction (sectionTensorSheafAdjunction.{u, v, r, v} O)
  exact ⟨n, _, _, ⟨isColimitSectionTensorFreeFinCofan hZ n⟩, F.map (freeSectionModuleFinHom p) ≫
    (Stacks.SheafOfModules.uliftForPresentationIsoSelf.{u, v, r, v} (F.obj M)).hom, inferInstance⟩

end Stacks.Cohomology.SiteModules

universe u

attribute [local instance 1]
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Sheaf.hasWeakSheafifyCommRingCat
  Sheaf.hasSheafifyAddCommGrpCat
  Sheaf.wEqualsLocallyBijectiveAddCommGrpCat

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-! ### The chart rings of a diagram -/

/-- **The ring of an affine chart is of finite presentation over the ring of the chart below
it**, for `f` locally of finite presentation. -/
theorem algebraFinitePresentation_chartDiagram (hf : IsLocallyOfFinitePresentation B S hS f.hom)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (hW : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V)) :
    letI := chartDiagramAlgebraInst B S hS f d
    Algebra.FinitePresentation (ToType ((smallEtaleRingedTopos B S hS Y).O.obj.obj (op d.V)))
      (ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U))) := by
  have hloc : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map d.g) :=
    hf d.U.1.left d.V.1.left d.U.1.hom d.V.1.hom d.g d.U.2 d.V.2 d.comm.symm
  have : IsAffine (Opposite.unop ((SmallEtale.toOver B S hS X.1 ⋙
      BigFppfOver.toScheme B S hS).op.obj (op d.U))) := hU
  have : IsAffine (Opposite.unop ((SmallEtale.toOver B S hS Y.1 ⋙
      BigFppfOver.toScheme B S hS).op.obj (op d.V))) := hW
  exact HasRingHomProperty.appTop (P := @LocallyOfFinitePresentation) _ hloc

variable (d : ChartDiagram B S hS X.1 Y.1 f.hom)

/-! ### Finiteness of `A`-modules read over `Γ` -/

/-- A module over `A`, restricted along a bijective ring map `Γ → A`, is finite (resp. of finite
presentation) over `Γ` whenever it is so over `A`. -/
private theorem finite_and_finitePresentation_compHom {Γ A N : Type*} [CommRing Γ] [CommRing A]
    [AddCommGroup N] [Module A N] (e : Γ →+* A) (he : Function.Bijective e) :
    letI := Module.compHom N e
    (Module.Finite A N → Module.Finite Γ N) ∧
      (Module.FinitePresentation A N → Module.FinitePresentation Γ N) := by
  let := e.toAlgebra
  let := Module.compHom N e
  have : IsScalarTower Γ A N := ⟨fun γ a n => mul_smul (e γ) a n⟩
  have hfin : Module.Finite Γ A := Module.Finite.of_surjective (Algebra.linearMap _ _) he.2
  have hfp : Module.FinitePresentation Γ A :=
    Module.finitePresentation_of_surjective (Algebra.linearMap _ _) he.2 (by
      rw [LinearMap.ker_eq_bot.2 he.1]
      exact Submodule.fg_bot)
  exact ⟨fun _ => Module.Finite.trans A N, fun _ => Module.FinitePresentation.trans _ N A⟩

/-- **An `A`-module of finite presentation is of finite presentation over `Γ`**, through the
identification `Γ ≅ A` of evaluation at the final object of the slice. -/
theorem moduleFinitePresentation_chartModuleLift (N : ModuleCat.{u} (chartSourceRing B S hS f d))
    [Module.FinitePresentation (chartSourceRing B S hS f d) N] :
    Module.FinitePresentation (chartGlobalRing B S hS f d)
      ((chartModuleLift B S hS f d).obj N) :=
  letI := Module.compHom N (chartEvalTop B S hS f d)
  have := (finite_and_finitePresentation_compHom _ (bijective_chartEvalTop B S hS f d)).2 ‹_›
  Module.FinitePresentation.of_equiv
    (ULift.moduleEquiv (R := chartGlobalRing B S hS f d) (M := N)).symm

/-- **A finite `A`-module is finite over `Γ`**, through the identification `Γ ≅ A` of evaluation
at the final object of the slice. -/
theorem moduleFinite_chartModuleLift (N : ModuleCat.{u} (chartSourceRing B S hS f d))
    [Module.Finite (chartSourceRing B S hS f d) N] :
    Module.Finite (chartGlobalRing B S hS f d) ((chartModuleLift B S hS f d).obj N) :=
  letI := Module.compHom N (chartEvalTop B S hS f d)
  have := (finite_and_finitePresentation_compHom _ (bijective_chartEvalTop B S hS f d)).1 ‹_›
  Module.Finite.equiv (ULift.moduleEquiv (R := chartGlobalRing B S hS f d) (M := N)).symm

/-! ### Finiteness of `N ⊗_A 𝒪` -/

/-- **`N ⊗_A 𝒪` has a finite global presentation** on the slice at `V`, for `N` of finite
presentation over `A`. -/
theorem hasFiniteGlobalPresentation_chartTensorFunctor_obj
    (N : ModuleCat.{u} (chartSourceRing B S hS f d))
    [Module.FinitePresentation (chartSourceRing B S hS f d) N] :
    ((chartTensorFunctor B S hS f d).obj N).HasFiniteGlobalPresentation :=
  have := moduleFinitePresentation_chartModuleLift B S hS f d N
  hasFiniteGlobalPresentation_sectionTensor_of_isTerminal (chartTopIsTerminal B S hS f d)
    ((chartModuleLift B S hS f d).obj N)

/-- **`N ⊗_A 𝒪` has finite global generators** on the slice at `V`, for `N` finite over `A`. -/
theorem hasFiniteGlobalGenerators_chartTensorFunctor_obj
    (N : ModuleCat.{u} (chartSourceRing B S hS f d))
    [Module.Finite (chartSourceRing B S hS f d) N] :
    ((chartTensorFunctor B S hS f d).obj N).HasFiniteGlobalGenerators :=
  have := moduleFinite_chartModuleLift B S hS f d N
  hasFiniteGlobalGenerators_sectionTensor_of_isTerminal (chartTopIsTerminal B S hS f d)
    ((chartModuleLift B S hS f d).obj N)

/-- **`N ⊗_A 𝒪` is quasi-coherent** on the slice at `V`, for every `A`-module `N`. -/
theorem isQuasicoherentOnSite_chartTensorFunctor_obj
    (N : ModuleCat.{u} (chartSourceRing B S hS f d)) :
    ((chartTensorFunctor B S hS f d).obj N).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_sectionTensor_of_isTerminal (chartTopIsTerminal B S hS f d)
    ((chartModuleLift B S hS f d).obj N)

/-- **`N ⊗_A 𝒪` is of finite presentation** on the slice at `V`, for `N` of finite presentation
over `A`. -/
theorem isFinitePresentationOnSite_chartTensorFunctor_obj
    (N : ModuleCat.{u} (chartSourceRing B S hS f d))
    [Module.FinitePresentation (chartSourceRing B S hS f d) N] :
    ((chartTensorFunctor B S hS f d).obj N).IsFinitePresentationOnSite :=
  Stacks.SheafOfModules.isFinitePresentationOnSite_of_hasFiniteGlobalPresentation _
    (hasFiniteGlobalPresentation_chartTensorFunctor_obj B S hS f d N)

/-- **`N ⊗_A 𝒪` is of finite type** on the slice at `V`, for `N` finite over `A`. -/
theorem isFiniteTypeOnSite_chartTensorFunctor_obj
    (N : ModuleCat.{u} (chartSourceRing B S hS f d))
    [Module.Finite (chartSourceRing B S hS f d) N] :
    ((chartTensorFunctor B S hS f d).obj N).IsFiniteTypeOnSite :=
  Stacks.SheafOfModules.isFiniteTypeOnSite_of_hasFiniteGlobalGenerators _
    (hasFiniteGlobalGenerators_chartTensorFunctor_obj B S hS f d N)

end AlgebraicGeometry.Space

end
