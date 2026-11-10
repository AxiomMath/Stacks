module

public import StacksFrontier.AlgebraicGeometry.Spaces.DisjointUnion.AffineEtaleCover
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDualizingComplexCechGluing
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDualizingComplexOfEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialQuasicoherentDerivedGluing
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialQuasicoherentSpectralSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfSpaceSiteExistence
public meta import StacksFrontier.Tactic.HEqCongr
import StacksCore.Tactic.StacksAttribute

/-!
# Existence of relative dualizing complexes (Stacks 0E61)

Let `f : X ⟶ Y` be a proper, flat morphism of algebraic spaces of finite presentation. Following
the source, choose an étale surjection `b₀ : V₀ ⟶ Y` from a disjoint union of affines and let
`U_n = V_n ×_Y X` over the Čech nerve `V` of `b₀`. The relative dualizing complex on `U_0/V_0`
(over the affine pieces) with the unique isomorphisms of pairs of its base changes is a descent
datum; it glues to `ω` on `X` (Stacks 0DLA, read on the spaces-étale sites), the trace `τ_0`
glues to `τ : Rf_* ω ⟶ 𝒪_Y` (Stacks 0DL9), and `(ω, τ)` is a relative dualizing complex by
Stacks 0E60.

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.exists_trace_cechOver`: the glued trace.
* `AlgebraicGeometry.BigFppfSpaceSite.nonempty_relativeDualizingComplex`: existence over the
  algebraic spaces of a big fppf site.
* `AlgebraicGeometry.Space.RelativeDualizingComplex.nonempty`: Stacks 0E61.

## References

* [Stacks Project, Tag 0E61](https://stacks.math.columbia.edu/tag/0E61)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
-- The universe-polymorphic sheafification instances of the cotangent complex (imported through
-- the small-étale duality files) leave universe constraints of the spaces-étale sites stuck.
attribute [-instance] CategoryTheory.Sheaf.hasSheafifyAddCommGrpCat
  CategoryTheory.Sheaf.wEqualsLocallyBijectiveAddCommGrpCat



namespace AlgebraicGeometry.BigFppfSpaceSite

attribute [local instance 5000] SheafOfModules.instAbelian
-- No global `HasDerivedCategory` instance applies to modules on the small étale sites; at low
-- priority the standard model chooses nothing where a global one exists.
attribute [local instance low] HasDerivedCategory.standard
attribute [local instance 5000] Space.SmallEtale.instHasSheafify
  Space.SmallEtale.instWEqualsLocallyBijective

open Space.SimplicialSpacesEtaleSite Stacks.Cohomology.DerivedPullbackOfToposHom
  Stacks.CategoryTheory.Hypercovering

variable {S : Scheme.{u}} {T : BigFppfSpaceSite S} {V₀ Y X : T.Spaces} (b₀ : V₀ ⟶ Y) (f : X ⟶ Y)


/-- Rewriting a composite through `κ₁ ≫ α = κ₀` and `F α ≫ t₀ = t₁`, in an arbitrary category. -/
theorem Functor.comp_map_comp_eq_of_comp_eq {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟]
    (F : 𝒞 ⥤ 𝒟) {P O O' : 𝒟} {A B₀ B₁ : 𝒞} (BC : P ⟶ F.obj A) {κ₀ : A ⟶ B₀} {κ₁ : A ⟶ B₁}
    {α : B₁ ⟶ B₀} {t₀ : F.obj B₀ ⟶ O} {t₁ : F.obj B₁ ⟶ O} (w : O ⟶ O') (hκ : κ₁ ≫ α = κ₀)
    (ht : F.map α ≫ t₀ = t₁) : BC ≫ F.map κ₀ ≫ t₀ ≫ w = BC ≫ F.map κ₁ ≫ t₁ ≫ w := by
  rw [← hκ, ← ht, F.map_comp, Category.assoc, Category.assoc]

/-- The two pullbacks to `V_1` of the map induced by `τ_0` agree. -/
theorem cechOverSmallEtaleTransitionIso_trace_eq (hZ : T.schemeSite.Contains (⊤_ Scheme.{u}))
    (hb₀ : etaleRepresentable T b₀)
    (hf : Space.IsProper T.schemeSite S T.scheme_mem f.hom)
    (hfl : Space.IsFlat T.schemeSite S T.scheme_mem f.hom)
    (hfp : Space.IsFinitePresentation T.schemeSite S T.scheme_mem f.hom)
    (D₀ : Space.RelativeDualizingComplex hZ (cechOverPullbackFst b₀ f (op ⦋0⦌))
      (isProper_cechOverPullbackFst b₀ f hf _) (isFlat_cechOverPullbackFst b₀ f hfl _)
      (isFinitePresentation_cechOverPullbackFst b₀ f hfp _))
    (α : (Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (1 : Fin 2)).op).left).obj D₀.ω ≅
        (Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (0 : Fin 2)).op).left).obj D₀.ω)
    (hτα : (Space.derivedModulePushforward T.schemeSite S T.scheme_mem
          (cechOverPullbackFst b₀ f (op ⦋1⦌))).map α.hom ≫
        (D₀.baseChange (isPullback_cechOverPullback_map b₀ f
          (SimplexCategory.δ (0 : Fin 2)).op)).τ =
        (D₀.baseChange (isPullback_cechOverPullback_map b₀ f
          (SimplexCategory.δ (1 : Fin 2)).op)).τ)
    (K : @DerivedCategory (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O)) _ _
        (HasDerivedCategory.standard _))
    (e : (derivedPullback (X := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f ⋙ Over.forget X).obj (op ⦋0⦌)))
        (Y := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
        (spacesEtaleRingedToposHom ((overAugmentation (cechOverPullback b₀ f)).app
          (op ⦋0⦌)))).obj K ≅
      (Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem
        ((cechOverPullback b₀ f ⋙ Over.forget X).obj (op ⦋0⦌))).obj D₀.ω)
    (he : (derivedPullback (spacesEtaleRingedToposHom ((cechOverPullback b₀ f ⋙ Over.forget X).map
          (SimplexCategory.δ (1 : Fin 2)).op))).map e.hom ≫
        (((smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T _
            (etaleRepresentable_cechOverPullback_delta b₀ f hb₀ 0 1).1).app D₀.ω).symm ≪≫
          (Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem
            ((cechOverPullback b₀ f ⋙ Over.forget X).obj (op ⦋1⦌))).mapIso α ≪≫
          (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T _
            (etaleRepresentable_cechOverPullback_delta b₀ f hb₀ 0 0).1).app D₀.ω).hom =
      ((augmentationTransitionDerivedIso (overAugmentation (cechOverPullback b₀ f))
          (SimplexCategory.δ (1 : Fin 2))).hom.app K ≫
        (augmentationTransitionDerivedIso (overAugmentation (cechOverPullback b₀ f))
          (SimplexCategory.δ (0 : Fin 2))).inv.app K) ≫
        (derivedPullback (spacesEtaleRingedToposHom ((cechOverPullback b₀ f ⋙ Over.forget X).map
          (SimplexCategory.δ (0 : Fin 2)).op))).map e.hom)
    (ω : DerivedCategory (Space.Modules.{u, u} T.schemeSite S T.scheme_mem X.1 X.2))
    (eω : (Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem X).obj ω ≅ K)
    (ε : (Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
      ((overAugmentation (cechOverPullback b₀ f)).app (op ⦋0⦌))).obj ω ≅ D₀.ω)
    (hε : (Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f ⋙ Over.forget X).obj (op ⦋0⦌))).map ε.hom =
        (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T _
          (etaleRepresentable_cechOverPullback_augmentation_zero b₀ f hb₀).1).hom.app ω ≫
        (derivedPullback (X := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem
            ((cechOverPullback b₀ f ⋙ Over.forget X).obj (op ⦋0⦌)))
          (Y := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
          (spacesEtaleRingedToposHom ((overAugmentation (cechOverPullback b₀ f)).app
            (op ⦋0⦌)))).map eω.hom ≫ e.hom) :
    (cechOverSmallEtaleTransitionIso b₀ 0).inv.app
          ((Space.derivedModulePushforward T.schemeSite S T.scheme_mem f).obj ω) ≫
        (Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
          ((cechOver b₀ ⋙ Over.forget Y).map (SimplexCategory.δ (0 : Fin 2)).op)).map
          (Space.smallEtaleDerivedModuleBaseChangeMap T.schemeSite S T.scheme_mem f
            ((overAugmentation (cechOver b₀)).app (op ⦋0⦌)) (cechOverPullbackFst b₀ f (op ⦋0⦌))
            ((overAugmentation (cechOverPullback b₀ f)).app (op ⦋0⦌))
            (isPullback_cechOverPullbackFst b₀ f (op ⦋0⦌)).w ω ≫
          (Space.derivedModulePushforward T.schemeSite S T.scheme_mem
            (cechOverPullbackFst b₀ f (op ⦋0⦌))).map ε.hom ≫ D₀.τ ≫
          (Space.smallEtaleDerivedModulePullbackUnitIso (B := T.schemeSite) (S := S)
            (hS := T.scheme_mem) ((overAugmentation (cechOver b₀)).app (op ⦋0⦌))).inv) ≫
        (cechOverSmallEtaleTransitionIso b₀ 0).hom.app
          (Space.derivedStructureSheaf T.schemeSite S T.scheme_mem Y.1 Y.2).obj =
      (cechOverSmallEtaleTransitionIso b₀ 1).inv.app
          ((Space.derivedModulePushforward T.schemeSite S T.scheme_mem f).obj ω) ≫
        (Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
          ((cechOver b₀ ⋙ Over.forget Y).map (SimplexCategory.δ (1 : Fin 2)).op)).map
          (Space.smallEtaleDerivedModuleBaseChangeMap T.schemeSite S T.scheme_mem f
            ((overAugmentation (cechOver b₀)).app (op ⦋0⦌)) (cechOverPullbackFst b₀ f (op ⦋0⦌))
            ((overAugmentation (cechOverPullback b₀ f)).app (op ⦋0⦌))
            (isPullback_cechOverPullbackFst b₀ f (op ⦋0⦌)).w ω ≫
          (Space.derivedModulePushforward T.schemeSite S T.scheme_mem
            (cechOverPullbackFst b₀ f (op ⦋0⦌))).map ε.hom ≫ D₀.τ ≫
          (Space.smallEtaleDerivedModulePullbackUnitIso (B := T.schemeSite) (S := S)
            (hS := T.scheme_mem) ((overAugmentation (cechOver b₀)).app (op ⦋0⦌))).inv) ≫
        (cechOverSmallEtaleTransitionIso b₀ 1).hom.app
          (Space.derivedStructureSheaf T.schemeSite S T.scheme_mem Y.1 Y.2).obj := by
  have hκ := cechOverPullbackSmallEtaleTransitionIso_inv_comp_map_comp b₀ f hZ hb₀ hf hfl hfp D₀ α
    K e he ω eω ε hε
  have g : ∀ i : Fin 2, (cechOverSmallEtaleTransitionIso b₀ i).inv.app
          ((Space.derivedModulePushforward T.schemeSite S T.scheme_mem f).obj ω) ≫
        (Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
          ((cechOver b₀ ⋙ Over.forget Y).map (SimplexCategory.δ i).op)).map
          (Space.smallEtaleDerivedModuleBaseChangeMap T.schemeSite S T.scheme_mem f
            ((overAugmentation (cechOver b₀)).app (op ⦋0⦌)) (cechOverPullbackFst b₀ f (op ⦋0⦌))
            ((overAugmentation (cechOverPullback b₀ f)).app (op ⦋0⦌))
            (isPullback_cechOverPullbackFst b₀ f (op ⦋0⦌)).w ω ≫
          (Space.derivedModulePushforward T.schemeSite S T.scheme_mem
            (cechOverPullbackFst b₀ f (op ⦋0⦌))).map ε.hom ≫ D₀.τ ≫
          (Space.smallEtaleDerivedModulePullbackUnitIso (B := T.schemeSite) (S := S)
            (hS := T.scheme_mem) ((overAugmentation (cechOver b₀)).app (op ⦋0⦌))).inv) ≫
        (cechOverSmallEtaleTransitionIso b₀ i).hom.app
          (Space.derivedStructureSheaf T.schemeSite S T.scheme_mem Y.1 Y.2).obj =
      Space.smallEtaleDerivedModuleBaseChangeMap T.schemeSite S T.scheme_mem f
          ((overAugmentation (cechOver b₀)).app (op ⦋1⦌)) (cechOverPullbackFst b₀ f (op ⦋1⦌))
          ((overAugmentation (cechOverPullback b₀ f)).app (op ⦋1⦌))
          (isPullback_cechOverPullbackFst b₀ f (op ⦋1⦌)).w ω ≫
        (Space.derivedModulePushforward T.schemeSite S T.scheme_mem
          (cechOverPullbackFst b₀ f (op ⦋1⦌))).map
          ((cechOverPullbackSmallEtaleTransitionIso b₀ f i).inv.app ω ≫
            (Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
              ((cechOverPullback b₀ f ⋙ Over.forget X).map
                (SimplexCategory.δ i).op)).map ε.hom) ≫
        (D₀.baseChange (isPullback_cechOverPullback_map b₀ f
          (SimplexCategory.δ i).op)).τ ≫
        (Space.smallEtaleDerivedModulePullbackUnitIso (B := T.schemeSite) (S := S)
          (hS := T.scheme_mem) ((overAugmentation (cechOver b₀)).app (op ⦋1⦌))).inv := by
    intro i
    have key := Space.RelativeDualizingPair.compIso_inv_app_comp_map_comp_eq
      D₀.toRelativeDualizingPair (isPullback_cechOverPullbackFst b₀ f (op ⦋0⦌))
      (isPullback_cechOverPullback_map b₀ f (SimplexCategory.δ i).op)
      (isPullback_cechOverPullbackFst b₀ f (op ⦋1⦌))
      (augmentation_map_comp_app (overAugmentation (cechOverPullback b₀ f)) (SimplexCategory.δ i))
      (augmentation_map_comp_app (overAugmentation (cechOver b₀)) (SimplexCategory.δ i)) ω ε
    unfold cechOverSmallEtaleTransitionIso cechOverPullbackSmallEtaleTransitionIso
    exact eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq key) (by heq_congr)))
  refine (g 0).trans (Eq.trans ?_ (g 1).symm)
  exact Functor.comp_map_comp_eq_of_comp_eq _ _ _ hκ hτα

/-- **The trace of the glued complex** (the last gluing step of the proof of Stacks 0E61). With
the data of the Čech gluing (`D₀`, the descent isomorphism `α` with its trace compatibility, the
output `(K, e)` of Stacks 0DLA and the descended `ω` with `ε : ω|_{U_0} ≅ ω_0`), the map
`L b_0^* Rf_* ω ⟶ L b_0^* 𝒪_Y` induced by `τ_0` through flat base change and `ε` is
`L b_0^* τ` for a map `τ : Rf_* ω ⟶ 𝒪_Y` (Stacks 0DL9). -/
theorem exists_trace_cechOver (hZ : T.schemeSite.Contains (⊤_ Scheme.{u}))
    (hb₀ : etaleRepresentable T b₀)
    (hb₀' : Presieve.singleton b₀ ∈ T.pretopologyBigFppfPretopology Y)
    (hf : Space.IsProper T.schemeSite S T.scheme_mem f.hom)
    (hfl : Space.IsFlat T.schemeSite S T.scheme_mem f.hom)
    (hfp : Space.IsFinitePresentation T.schemeSite S T.scheme_mem f.hom)
    (D₀ : Space.RelativeDualizingComplex hZ (cechOverPullbackFst b₀ f (op ⦋0⦌))
      (isProper_cechOverPullbackFst b₀ f hf _) (isFlat_cechOverPullbackFst b₀ f hfl _)
      (isFinitePresentation_cechOverPullbackFst b₀ f hfp _))
    (α : (Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (1 : Fin 2)).op).left).obj D₀.ω ≅
        (Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f).map (SimplexCategory.δ (0 : Fin 2)).op).left).obj D₀.ω)
    (hτα : (Space.derivedModulePushforward T.schemeSite S T.scheme_mem
          (cechOverPullbackFst b₀ f (op ⦋1⦌))).map α.hom ≫
        (D₀.baseChange (isPullback_cechOverPullback_map b₀ f
          (SimplexCategory.δ (0 : Fin 2)).op)).τ =
        (D₀.baseChange (isPullback_cechOverPullback_map b₀ f
          (SimplexCategory.δ (1 : Fin 2)).op)).τ)
    (K : @DerivedCategory (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O)) _ _
        (HasDerivedCategory.standard _))
    (e : (derivedPullback (X := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f ⋙ Over.forget X).obj (op ⦋0⦌)))
        (Y := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
        (spacesEtaleRingedToposHom ((overAugmentation (cechOverPullback b₀ f)).app
          (op ⦋0⦌)))).obj K ≅
      (Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem
        ((cechOverPullback b₀ f ⋙ Over.forget X).obj (op ⦋0⦌))).obj D₀.ω)
    (he : (derivedPullback (spacesEtaleRingedToposHom ((cechOverPullback b₀ f ⋙ Over.forget X).map
          (SimplexCategory.δ (1 : Fin 2)).op))).map e.hom ≫
        (((smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T _
            (etaleRepresentable_cechOverPullback_delta b₀ f hb₀ 0 1).1).app D₀.ω).symm ≪≫
          (Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem
            ((cechOverPullback b₀ f ⋙ Over.forget X).obj (op ⦋1⦌))).mapIso α ≪≫
          (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T _
            (etaleRepresentable_cechOverPullback_delta b₀ f hb₀ 0 0).1).app D₀.ω).hom =
      ((augmentationTransitionDerivedIso (overAugmentation (cechOverPullback b₀ f))
          (SimplexCategory.δ (1 : Fin 2))).hom.app K ≫
        (augmentationTransitionDerivedIso (overAugmentation (cechOverPullback b₀ f))
          (SimplexCategory.δ (0 : Fin 2))).inv.app K) ≫
        (derivedPullback (spacesEtaleRingedToposHom ((cechOverPullback b₀ f ⋙ Over.forget X).map
          (SimplexCategory.δ (0 : Fin 2)).op))).map e.hom)
    (ω : DerivedCategory (Space.Modules.{u, u} T.schemeSite S T.scheme_mem X.1 X.2))
    (hω : Space.QcohDerived T.schemeSite S T.scheme_mem X ω)
    (eω : (Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem X).obj ω ≅ K)
    (ε : (Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
      ((overAugmentation (cechOverPullback b₀ f)).app (op ⦋0⦌))).obj ω ≅ D₀.ω)
    (hε : (Space.toSpacesEtaleDerivedModules T.schemeSite S T.scheme_mem
          ((cechOverPullback b₀ f ⋙ Over.forget X).obj (op ⦋0⦌))).map ε.hom =
        (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T _
          (etaleRepresentable_cechOverPullback_augmentation_zero b₀ f hb₀).1).hom.app ω ≫
        (derivedPullback (X := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem
            ((cechOverPullback b₀ f ⋙ Over.forget X).obj (op ⦋0⦌)))
          (Y := Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X)
          (spacesEtaleRingedToposHom ((overAugmentation (cechOverPullback b₀ f)).app
            (op ⦋0⦌)))).map eω.hom ≫ e.hom) :
    ∃ τ : (Space.derivedModulePushforward T.schemeSite S T.scheme_mem f).obj ω ⟶
        (Space.derivedStructureSheaf T.schemeSite S T.scheme_mem Y.1 Y.2).obj,
      (Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
          ((overAugmentation (cechOver b₀)).app (op ⦋0⦌))).map τ =
        Space.smallEtaleDerivedModuleBaseChangeMap T.schemeSite S T.scheme_mem f
            ((overAugmentation (cechOver b₀)).app (op ⦋0⦌)) (cechOverPullbackFst b₀ f (op ⦋0⦌))
            ((overAugmentation (cechOverPullback b₀ f)).app (op ⦋0⦌))
            (isPullback_cechOverPullbackFst b₀ f (op ⦋0⦌)).w ω ≫
          (Space.derivedModulePushforward T.schemeSite S T.scheme_mem
            (cechOverPullbackFst b₀ f (op ⦋0⦌))).map ε.hom ≫ D₀.τ ≫
          (Space.smallEtaleDerivedModulePullbackUnitIso (B := T.schemeSite) (S := S)
            (hS := T.scheme_mem) ((overAugmentation (cechOver b₀)).app (op ⦋0⦌))).inv := by
  have hK' := (Space.qcohDerived_iff_toSpacesEtaleDerivedModules_obj T.schemeSite S T.scheme_mem Y
    _).1 (Space.qcohDerived_derivedModulePushforward_obj T.schemeSite S T.scheme_mem f hfp.2.1
      hfp.2.2 ω hω)
  have hE' := (Space.qcohDerived_iff_toSpacesEtaleDerivedModules_obj T.schemeSite S T.scheme_mem Y
    _).1 (Space.derivedStructureSheaf T.schemeSite S T.scheme_mem Y.1 Y.2).2
  have hex := exact_derivedPullback_map_augmentationFaceTransport
    (isHypercoveringAugmentation_cechOver T.pretopologyBigFppfPretopology b₀ hb₀') hK' hE'
    (fun n i hi g => hom_shift_eq_zero_derivedPullback_cechOver b₀ f hZ hb₀ hf hfl hfp D₀ ω hω ε
      n i hi g)
  exact exists_hom_smallEtaleDerivedModulePullback_cechOver_eq b₀ hb₀ _ _
    (Space.derivedStructureSheaf T.schemeSite S T.scheme_mem Y.1 Y.2).2
    (fun ψ hψ => (hex ψ).1 (sub_eq_zero.2 hψ)) _
    (cechOverSmallEtaleTransitionIso_trace_eq b₀ f hZ hb₀ hf hfl hfp D₀ α hτα K e he ω eω
      ε hε)

/-- The augmentation `V_0 ⟶ Y` of the Čech nerve of `b₀` is surjective when `b₀` is. -/
theorem isSurjective_cechOver_augmentation_zero
    (hsurj : Space.IsSurjective T.schemeSite S T.scheme_mem b₀.hom) :
    Space.IsSurjective T.schemeSite S T.scheme_mem
      ((overAugmentation (cechOver b₀)).app (op ⦋0⦌)).hom := by
  let e : (cechOver b₀).obj (op ⦋0⦌) ≅ Over.mk b₀ :=
    Limits.productUniqueIso (fun _ : Fin 1 => Over.mk b₀)
  have he : ((cechOver b₀).obj (op ⦋0⦌)).hom = e.hom.left ≫ b₀ := (Over.w e.hom).symm
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget Y).map e.hom))
  change Space.IsSurjective T.schemeSite S T.scheme_mem ((cechOver b₀).obj (op ⦋0⦌)).hom.hom
  rw [he]
  exact Space.isSurjective_comp T.schemeSite S T.scheme_mem
    (Space.isSurjective_of_isIso T.schemeSite S T.scheme_mem e.hom.left.hom) hsurj

/-- Reading back a map through an isomorphism and a unit, in an arbitrary category. -/
theorem inv_comp_comp_hom_eq_of_eq {𝒞 : Type*} [Category* 𝒞] {P Q Q' O O' : 𝒞} (BC : P ≅ Q)
    {Lτ : P ⟶ O'} {x₁ : Q ⟶ Q'} {x₂ : Q' ⟶ O} (u : O' ≅ O)
    (h : Lτ = BC.hom ≫ x₁ ≫ x₂ ≫ u.inv) : BC.inv ≫ Lτ ≫ u.hom = x₁ ≫ x₂ := by
  subst h
  simp

/-- **The glued pair is a relative dualizing complex** (the last step of the proof of
Stacks 0E61): `(ω, τ)` with `ω|_{U_0} ≅ ω_0` carrying `τ|_{V_0}` to `τ_0` is a relative dualizing
complex by Stacks 0E60, `V_0` being a disjoint union of affines. -/
theorem nonempty_relativeDualizingComplex_of_trace (hZ : T.schemeSite.Contains (⊤_ Scheme.{u}))
    (hb₀ : etaleRepresentable T b₀)
    (hbs : Space.IsSurjective T.schemeSite S T.scheme_mem b₀.hom)
    (hf : Space.IsProper T.schemeSite S T.scheme_mem f.hom)
    (hfl : Space.IsFlat T.schemeSite S T.scheme_mem f.hom)
    (hfp : Space.IsFinitePresentation T.schemeSite S T.scheme_mem f.hom)
    (D₀ : Space.RelativeDualizingComplex hZ (cechOverPullbackFst b₀ f (op ⦋0⦌))
      (isProper_cechOverPullbackFst b₀ f hf _) (isFlat_cechOverPullbackFst b₀ f hfl _)
      (isFinitePresentation_cechOverPullbackFst b₀ f hfp _))
    {ι : Type u} {Yi : ι → T.Spaces} {j : ∀ i, Yi i ⟶ V₀}
    (hc : IsColimit (Cofan.mk ((Space.algebraicSpacesToSheaf T.schemeSite S T.scheme_mem).obj V₀)
      fun i => (Space.algebraicSpacesToSheaf T.schemeSite S T.scheme_mem).map (j i)))
    (hYi : ∀ i, Space.IsAffineSpace T.schemeSite S T.scheme_mem (Yi i).1)
    (ω : DerivedCategory (Space.Modules.{u, u} T.schemeSite S T.scheme_mem X.1 X.2))
    (ε : (Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
      ((overAugmentation (cechOverPullback b₀ f)).app (op ⦋0⦌))).obj ω ≅ D₀.ω)
    (τ : (Space.derivedModulePushforward T.schemeSite S T.scheme_mem f).obj ω ⟶
        (Space.derivedStructureSheaf T.schemeSite S T.scheme_mem Y.1 Y.2).obj)
    (hτ : (Space.smallEtaleDerivedModulePullback T.schemeSite S T.scheme_mem
          ((overAugmentation (cechOver b₀)).app (op ⦋0⦌))).map τ =
        Space.smallEtaleDerivedModuleBaseChangeMap T.schemeSite S T.scheme_mem f
            ((overAugmentation (cechOver b₀)).app (op ⦋0⦌)) (cechOverPullbackFst b₀ f (op ⦋0⦌))
            ((overAugmentation (cechOverPullback b₀ f)).app (op ⦋0⦌))
            (isPullback_cechOverPullbackFst b₀ f (op ⦋0⦌)).w ω ≫
          (Space.derivedModulePushforward T.schemeSite S T.scheme_mem
            (cechOverPullbackFst b₀ f (op ⦋0⦌))).map ε.hom ≫ D₀.τ ≫
          (Space.smallEtaleDerivedModulePullbackUnitIso (B := T.schemeSite) (S := S)
            (hS := T.scheme_mem) ((overAugmentation (cechOver b₀)).app (op ⦋0⦌))).inv) :
    Nonempty (Space.RelativeDualizingComplex hZ f hf hfl hfp) := by
  have sq₀ : IsPullback ((overAugmentation (cechOverPullback b₀ f)).app (op ⦋0⦌))
      (cechOverPullbackFst b₀ f (op ⦋0⦌)) f ((overAugmentation (cechOver b₀)).app (op ⦋0⦌)) :=
    isPullback_cechOverPullbackFst b₀ f (op ⦋0⦌)
  have hg := (etaleRepresentable_cechOver_augmentation_zero b₀ hb₀).1
  have hgs := isSurjective_cechOver_augmentation_zero b₀ hbs
  let P : Space.RelativeDualizingPair f hfl hfp :=
    { ω := ω
      isPerfectRelativeTo := Space.isPerfectRelativeToCanonical_of_isPullback sq₀ hg hgs hfl hfp.1
        ω (Space.isPerfectRelativeToCanonical_of_iso _ _ _ ε.symm D₀.isPerfectRelativeTo)
      τ := τ }
  have hεP : (Space.derivedModulePushforward T.schemeSite S T.scheme_mem
      (cechOverPullbackFst b₀ f (op ⦋0⦌))).map ε.hom ≫ D₀.τ = P.baseChangeTrace sq₀ :=
    (inv_comp_comp_hom_eq_of_eq
      (@asIso _ _ _ _ (Space.smallEtaleDerivedModuleBaseChangeMap T.schemeSite S T.scheme_mem f
        ((overAugmentation (cechOver b₀)).app (op ⦋0⦌)) (cechOverPullbackFst b₀ f (op ⦋0⦌))
        ((overAugmentation (cechOverPullback b₀ f)).app (op ⦋0⦌)) sq₀.w ω)
        (P.isIso_smallEtaleDerivedBaseChangeMap sq₀))
      (Space.smallEtaleDerivedModulePullbackUnitIso (B := T.schemeSite) (S := S)
        (hS := T.scheme_mem) ((overAugmentation (cechOver b₀)).app (op ⦋0⦌))) hτ).symm
  let e := cechOverObjZeroIso b₀
  let A := Space.algebraicSpacesToSheaf T.schemeSite S T.scheme_mem
  have hc' : IsColimit (Cofan.mk (A.obj ((cechOver b₀).obj (op ⦋0⦌)).left)
      fun i => A.map (j i ≫ e.inv)) :=
    IsColimit.ofIsoColimit hc (Cofan.ext (A.mapIso e.symm) fun i =>
      (A.map_comp (j i) e.inv).symm)
  exact ⟨{ toRelativeDualizingPair := P
           isAffineBaseChangePair := fun _ _ f' g g' sq hY' =>
             P.isAffineBaseChangePair_of_baseChange_iso hZ hf sq₀ hg hgs D₀ ε hεP hc' hYi f' g g'
               sq hY' }⟩

/-- **Existence of relative dualizing complexes over the algebraic spaces of a big fppf site**
(the proof of Stacks 0E61). -/
theorem nonempty_relativeDualizingComplex (T : BigFppfSpaceSite S)
    (hZ : T.schemeSite.Contains (⊤_ Scheme.{u})) {X Y : T.Spaces} (f : X ⟶ Y)
    (hf : Space.IsProper T.schemeSite S T.scheme_mem f.hom)
    (hfl : Space.IsFlat T.schemeSite S T.scheme_mem f.hom)
    (hfp : Space.IsFinitePresentation T.schemeSite S T.scheme_mem f.hom) :
    Nonempty (Space.RelativeDualizingComplex hZ f hf hfl hfp) := by
  obtain ⟨ι, Yi, V₀, j, b₀, hYi, hbe, hbs, hbr, ⟨hc⟩⟩ :=
    Space.exists_isColimit_cofan_affine_etale_surjective T.schemeSite S T.scheme_mem Y
  have hb₀ : etaleRepresentable T b₀ := ⟨hbe, hbr⟩
  have hb₀' : Presieve.singleton b₀ ∈ T.pretopologyBigFppfPretopology Y :=
    T.singleton_mem_pretopology ⟨Space.isFlat_of_isEtale _ _ _ hbe,
      Space.isLocallyOfFinitePresentation_of_isEtale _ _ _ hbe, hbs⟩
  let D₀ := (nonempty_relativeDualizingComplex_cechOverPullbackFst_zero b₀ f hZ hc hYi hf hfl
    hfp).some
  obtain ⟨c, hc₁, hc₂⟩ :=
    exists_spacesEtaleDerivedCocycle_cechOverPullback hZ b₀ f hb₀ hf hfl hfp D₀
  have hK₀ := (Space.qcohDerived_iff_toSpacesEtaleDerivedModules_obj T.schemeSite S T.scheme_mem _
    D₀.ω).1 D₀.toRelativeDualizingPair.qcohDerived_ω
  obtain ⟨φ, hφ, ψ, hψ⟩ :=
    Space.SimplicialSpacesEtaleSite.exists_derivedPullback_degreeZero_iso_compatible
      (isHypercoveringAugmentation_cechOverPullback T.pretopologyBigFppfPretopology b₀ f hb₀') _
      hK₀ _ hc₂
      (fun n i hi g => hom_shift_eq_zero_cechOverPullback hZ b₀ f hb₀ hf hfl hfp D₀ n i hi g)
  obtain ⟨K, hK, e, eω, he⟩ := exists_iso_smallEtaleDerivedModulePullback_cechOverPullback b₀ f hZ
    hb₀ hbs hf hfl hfp D₀ φ hφ ψ
  obtain ⟨τ, hτ⟩ := exists_trace_cechOver b₀ f hZ hb₀ hb₀' hf hfl hfp D₀ c hc₁ φ ψ hψ K hK e eω he
  exact nonempty_relativeDualizingComplex_of_trace b₀ f hZ hb₀ hbs hf hfl hfp D₀ hc hYi K eω τ hτ

end AlgebraicGeometry.BigFppfSpaceSite

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0E61: existence of relative dualizing complexes.** Let `f : X ⟶ Y` be a proper,
flat morphism of algebraic spaces over `S` which is of finite presentation. Then there exists a
relative dualizing complex `(ω_{X/Y}, τ)` for `X/Y` (Stacks 0E5X). -/
@[stacks 0E61]
theorem RelativeDualizingComplex.nonempty (hZ : B.Contains (⊤_ Scheme.{u}))
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsProper B S hS f.hom)
    (hfl : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom) :
    Nonempty (RelativeDualizingComplex hZ f hf hfl hfp) :=
  BigFppfSpaceSite.of_forall B S hS
    (P := fun B hS => ∀ (hZ : B.Contains (⊤_ Scheme.{u})) {X Y : AlgebraicSpaces B S hS}
      (f : X ⟶ Y) (hf : IsProper B S hS f.hom) (hfl : IsFlat B S hS f.hom)
      (hfp : IsFinitePresentation B S hS f.hom),
        Nonempty (RelativeDualizingComplex hZ f hf hfl hfp))
    (fun T hZ _ _ f hf hfl hfp => BigFppfSpaceSite.nonempty_relativeDualizingComplex T hZ f hf hfl
      hfp) hZ f hf hfl hfp

end AlgebraicGeometry.Space

end
